// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::explain::{PathSegment, UnknownPath};
use alloc::vec::Vec;
use core::cmp::Ordering;

struct Node {
    path: usize,
    left: Option<usize>,
    right: Option<usize>,
    height: u8,
}

/// An AVL index of accepted, prefix-free paths. Only declaration indices are
/// retained; the arena also keeps destruction independent of path depth.
pub(super) struct UnknownIndex {
    nodes: Vec<Node>,
    root: Option<usize>,
    checked_bytes: bool,
}

#[allow(clippy::indexing_slicing)]
impl UnknownIndex {
    pub(super) const fn new(checked_bytes: bool) -> Self {
        Self {
            nodes: Vec::new(),
            root: None,
            checked_bytes,
        }
    }

    pub(super) fn overlap<E>(
        &self,
        paths: &[UnknownPath],
        path: usize,
        checkpoint: &mut impl FnMut() -> Result<(), E>,
    ) -> Result<Option<usize>, E> {
        let mut cursor = self.root;
        while let Some(index) = cursor {
            checkpoint()?;
            let node = &self.nodes[index];
            let (order, overlap) = compare(
                &paths[path],
                &paths[node.path],
                self.checked_bytes,
                checkpoint,
            )?;
            if overlap {
                if paths[path].segments.len() >= paths[node.path].segments.len() {
                    return Ok(Some(node.path));
                }
                // A new ancestor can cover several siblings. Scan once, only
                // on this terminating error, to retain declaration-order diagnostics.
                for candidate in &self.nodes {
                    checkpoint()?;
                    if compare(
                        &paths[path],
                        &paths[candidate.path],
                        self.checked_bytes,
                        checkpoint,
                    )?
                    .1
                    {
                        return Ok(Some(candidate.path));
                    }
                }
            }
            cursor = if order.is_lt() { node.left } else { node.right };
        }
        Ok(None)
    }

    pub(super) fn insert<E>(
        &mut self,
        paths: &[UnknownPath],
        path: usize,
        checkpoint: &mut impl FnMut() -> Result<(), E>,
    ) -> Result<(), E> {
        checkpoint()?;
        let index = self.nodes.len();
        self.nodes.push(Node {
            path,
            left: None,
            right: None,
            height: 1,
        });
        checkpoint()?;
        self.root = Some(self.insert_at(self.root, index, paths, checkpoint)?);
        Ok(())
    }

    fn insert_at<E>(
        &mut self,
        root: Option<usize>,
        index: usize,
        paths: &[UnknownPath],
        checkpoint: &mut impl FnMut() -> Result<(), E>,
    ) -> Result<usize, E> {
        checkpoint()?;
        let Some(root) = root else { return Ok(index) };
        let (order, _) = compare(
            &paths[self.nodes[index].path],
            &paths[self.nodes[root].path],
            self.checked_bytes,
            checkpoint,
        )?;
        if order.is_lt() {
            self.nodes[root].left =
                Some(self.insert_at(self.nodes[root].left, index, paths, checkpoint)?);
        } else {
            self.nodes[root].right =
                Some(self.insert_at(self.nodes[root].right, index, paths, checkpoint)?);
        }
        self.update_height(root);
        let left = self.nodes[root].left;
        let right = self.nodes[root].right;
        if self.height(left) > self.height(right).saturating_add(1) {
            if let Some(left) = left {
                if self.height(self.nodes[left].right) > self.height(self.nodes[left].left) {
                    self.nodes[root].left = Some(self.rotate_left(left));
                }
            }
            return Ok(self.rotate_right(root));
        }
        if self.height(right) > self.height(left).saturating_add(1) {
            if let Some(right) = right {
                if self.height(self.nodes[right].left) > self.height(self.nodes[right].right) {
                    self.nodes[root].right = Some(self.rotate_right(right));
                }
            }
            return Ok(self.rotate_left(root));
        }
        Ok(root)
    }

    fn height(&self, index: Option<usize>) -> u8 {
        index.map_or(0, |index| self.nodes[index].height)
    }

    fn update_height(&mut self, index: usize) {
        self.nodes[index].height = self
            .height(self.nodes[index].left)
            .max(self.height(self.nodes[index].right))
            .saturating_add(1);
    }

    fn rotate_left(&mut self, root: usize) -> usize {
        let Some(right) = self.nodes[root].right else {
            return root;
        };
        self.nodes[root].right = self.nodes[right].left;
        self.nodes[right].left = Some(root);
        self.update_height(root);
        self.update_height(right);
        right
    }

    fn rotate_right(&mut self, root: usize) -> usize {
        let Some(left) = self.nodes[root].left else {
            return root;
        };
        self.nodes[root].left = self.nodes[left].right;
        self.nodes[left].right = Some(root);
        self.update_height(root);
        self.update_height(left);
        left
    }
}

fn compare<E>(
    left: &UnknownPath,
    right: &UnknownPath,
    checked_bytes: bool,
    checkpoint: &mut impl FnMut() -> Result<(), E>,
) -> Result<(Ordering, bool), E> {
    checkpoint()?;
    let root = left.root.cmp(&right.root);
    if !root.is_eq() {
        return Ok((root, false));
    }
    for (left_segment, right_segment) in left.segments.iter().zip(&right.segments) {
        checkpoint()?;
        let order = match *left_segment {
            PathSegment::Index(left_index) => match *right_segment {
                PathSegment::Index(right_index) => left_index.cmp(&right_index),
                PathSegment::Key(_) => Ordering::Greater,
            },
            PathSegment::Key(ref left_key) => match *right_segment {
                PathSegment::Index(_) => Ordering::Less,
                PathSegment::Key(ref right_key) => {
                    if checked_bytes {
                        for (left_chunk, right_chunk) in left_key
                            .as_bytes()
                            .chunks(256)
                            .zip(right_key.as_bytes().chunks(256))
                        {
                            checkpoint()?;
                            let order = left_chunk.cmp(right_chunk);
                            if !order.is_eq() {
                                return Ok((order, false));
                            }
                        }
                        left_key.len().cmp(&right_key.len())
                    } else {
                        left_key.cmp(right_key)
                    }
                }
            },
        };
        if !order.is_eq() {
            return Ok((order, false));
        }
    }
    Ok((left.segments.len().cmp(&right.segments.len()), true))
}
