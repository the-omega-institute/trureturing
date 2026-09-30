#!/bin/bash
# Run the Lean inspector's Python test suites used by CI. The native suites
# share one staged inspector compiler; the remaining suites run without it.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
seed="$(mktemp -d)"
trap 'rm -rf "$seed"' EXIT
export STRATALINT_NATIVE_COMMAND_OBSERVATION=1

python3 -B test_native_support.py "$seed"

STRATALINT_NATIVE_COMPILER_SEED="$seed" python3 -B -m unittest -v \
  test_native.NativeArtifactTests \
  test_native.NativeCompilerTests \
  test_native.NativePackageTests \
  test_native.NativePublicationTests \
  test_native.NativeRecoveryTests \
  test_native.NativeRelocationTests.test_census_callers_in_relocated_package_with_spaces \
  test_native.NativeReportTests \
  test_native.NativeRoutingTests \
  test_native.NativeSemanticTests \
  test_native.NativeTests.test_coordinates_use_private_temporary_memo_and_clean_up_failures \
  test_native.NativeTests.test_imported_comment_warm_report_equals_fresh \
  test_native.NativeTests.test_interface_grammar_has_single_owner \
  test_native.NativeTests.test_interface_only_reports_missing_handler \
  test_native.NativeTests.test_interface_records_have_single_owner \
  test_native.NativeTests.test_interface_registered_build_inputs \
  test_native.NativeTests.test_interface_standalone_core_only \
  test_native.NativeTests.test_interface_store_cross_module_persistence \
  test_native.NativeTests.test_native_compatibility_preimage \
  test_native.NativeTests.test_native_compiler_seed_is_private \
  test_native.NativeTests.test_native_module_binding_scope \
  test_native.NativeTests.test_native_old_manifest_key_rejected \
  test_native.NativeTests.test_native_workload_rejects_nonfixture_before_writes \
  test_native.NativeTests.test_output_audit_follows_compiler_package_owners \
  test_native.NativeTests.test_reg_manifest_rejected_before_materialization \
  test_native.NativeTests.test_release_partition_preserves_semantic_and_selection_changes \
  test_native.NativeTests.test_snapshot_generation_preserves_mathlib_partition

python3 -B -m unittest -v test_native_support.GuardedCommandTests test_reuse test_streaming
