#!/usr/bin/env python3
# Copyright (c) Microsoft Corporation.
# Licensed under the MIT License.
"""Regenerate typed head contracts with OPA 1.2.0.

Usage: python3 generate_partial_object_contracts.py SOURCE OPA OUTPUT WORK_DIR
SOURCE is partial_object_head_differential.rs; WORK_DIR is a dedicated,
persistent directory for generated policy/input files (never a system temp dir).
"""

import json
import re
import subprocess
import sys
from pathlib import Path

source, opa, output, work = map(Path, sys.argv[1:])
assert subprocess.check_output([str(opa.resolve()), "version"], text=True).splitlines()[0] == "Version: 1.2.0"
work.mkdir(parents=True, exist_ok=True)
templates = {
    name: json.loads('"' + rule + '"')
    for name, rule in re.findall(
        r'\(\s*"([^"]+)",\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)',
        source.read_text().split("const LOCAL_WRAPPERS")[0],
    )
}
assert len(templates) == 21
policies = [(name, [rule], False) for name, rule in templates.items()]
for first, rule in templates.items():
    for second, other in templates.items():
        if first != second:
            policies += [(first + "+" + second, [rule, other], False),
                         (first + "|" + second, [rule, other], True)]
inputs = {
    "populated": {"ks": ["a", "b"], "js": ["m", "n"], "vs": [20, 21], "keys": ["a", "c"]},
    "empty": {"ks": [], "js": [], "vs": [], "keys": []},
}
for name, value in inputs.items():
    (work / f"{name}.json").write_text(json.dumps(value) + "\n")
contracts = {}
for name, rules, split in policies:
    paths = []
    for index, group in enumerate([[rule] for rule in rules] if split else [rules]):
        path = work / f"policy_{index}.rego"
        path.write_text("package test\n" + "\n".join(group) + "\n")
        paths += ["--data", str(path)]
    entry = {"rules": rules}
    for input_name in inputs:
        result = subprocess.run(
            [str(opa.resolve()), "eval", "--format=json", *paths,
             "--input", str(work / f"{input_name}.json"),
             '[{"term": sprintf("%v", [v]), "value": v} | v := data.test.p]'],
            text=True, capture_output=True, check=False,
        )
        if not result.stdout and result.stderr.startswith("panic:"):
            assert "plain_set" in re.split(r"[+|]", name) and len(rules) == 2, (name, result.stderr)
            entry[input_name] = {
                "errors": ["opa_panic_mixed_rule_kinds"],
                "messages": ["unsupported mix of plain set and object rule heads"],
            }
            continue
        assert result.stdout, (name, result.returncode, result.stderr)
        value = json.loads(result.stdout)
        if "errors" in value:
            errors = value["errors"]
            codes = sorted({error["code"] for error in errors})
            assert set(codes) <= {"rego_type_error", "eval_conflict_error"}, (name, value)
            entry[input_name] = {"errors": codes,
                                 "messages": sorted({error["message"] for error in errors})}
        else:
            assert result.returncode == 0, (name, value)
            values = value["result"][0]["expressions"][0]["value"]
            entry[input_name] = values[0] if values else {"undefined": True}
    contracts[name] = entry
output.write_text('{"opa_version":"1.2.0","cases":{\n' + ",\n".join(
    json.dumps(name) + ":" + json.dumps(entry, sort_keys=True, separators=(",", ":"))
    for name, entry in sorted(contracts.items())
) + "\n}}\n")
print(f"Wrote {len(contracts)} policies x 2 inputs to {output}")
