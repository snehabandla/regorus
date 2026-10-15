#if REGORUS_FFI_TEST_HOOKS
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using Regorus.Internal;

namespace Regorus.Internal
{
    internal static class PanicGuardTestHooks
    {
        public static unsafe void TriggerPanic()
        {
            var result = API.regorus_engine_test_trigger_panic();
            try
            {
                if (result.status == RegorusStatus.Ok)
                {
                    return;
                }

                throw result.status.CreateException(Utf8Marshaller.FromUtf8(result.error_message));
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        public static void ResetPoison()
        {
            API.regorus_engine_test_reset_poison();
        }
    }
}
#endif
