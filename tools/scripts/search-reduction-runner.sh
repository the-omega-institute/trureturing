#!/usr/bin/env bash
set -euo pipefail

# Resolve Lake's environment, then release its build graph before native work.
native_run() {
  python3 tools/scripts/search-reduction-probe-cache.py --native "$@"
}

case "${1:-}" in
  test)
    shift
    test "$#" -eq 0 || { echo 'search-reduction-runner test takes no arguments' >&2; exit 2; }
    make search-reduction-probe-cache-test
    modules=(GraphModel LookupModel CertificateModel CertificateTests CertificateScope
      ProbeCacheKernel ProbeCacheReplay ProbeCacheReplayCertificate ProbeCacheReplayVerdict
      LookupPruningTests LookupTests LookupRecallTests LookupColdTests LookupCacheTests LookupIsolationTests LookupTelemetry LookupScope NativeCertification GraphCalibration PublicationMutation
      Calibration FaultPaths SingleSourceModel VocabularyModel PresentationCoverage
      SingleSourceTests RawOriginsTests Faults RealNegative VocabularyTransport
      VocabularyTests InformationTests)
    for module in "${modules[@]}"; do
      search_test_start=$(date +%s)
      if make lean LEAN_SKIP_LOCK="${LEAN_SKIP_LOCK:-0}" \
          LEAN_TARGETS="LeanInformationAuditRegTests.SearchReduction.${module}"; then
        search_test_exit=0
      else
        search_test_exit=$?
      fi
      search_test_seconds=$(( $(date +%s) - search_test_start ))
      printf 'SEARCH_REDUCTION_TEST_TIMING module=%s seconds=%s exit=%s\n' \
        "$module" "$search_test_seconds" "$search_test_exit"
      test "$search_test_exit" -eq 0 || exit "$search_test_exit"
    done
    # Execute the shared-closure work regression even when Lake reuses its module.
    cache_kernel_test_dir=$(mktemp -d build/lean-inspector/cache-kernel-work.XXXXXX)
    SEARCH_REDUCTION_PROBE_CACHE=0 \
      SEARCH_REDUCTION_PROFILE="$cache_kernel_test_dir/phases.log" \
      make search-reduction-run \
        REQUESTS=tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/ProbeCacheKernel.lean
    make search-reduction-index-failure-test
    SEARCH_REDUCTION_TELEMETRY=1 make search-reduction-run \
      REQUESTS=tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/LookupTelemetry.lean
    ;;
  index-failure-test)
    lookup_test_dir=$(mktemp -d build/lean-inspector/index-open-failure.XXXXXX)
    cat > "$lookup_test_dir/request.lean" <<'LEAN'
import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.GraphCandidates
set_option maxHeartbeats 0
#search_reduction LeanInformationAudit.Tests.SearchReduction.GraphCandidates.squareVia at "b02b98342945a1a724a227db4fa38e376640e573" baseline [] using [] as indexFailureRegression
LEAN
    lookup_exit=0
    SEARCH_REDUCTION_INDEX="$lookup_test_dir/missing" make search-reduction-run \
      REQUESTS="$lookup_test_dir/request.lean" > "$lookup_test_dir/output.log" 2>&1 || lookup_exit=$?
    test "$lookup_exit" -ne 0 || {
      cat "$lookup_test_dir/output.log" >&2
      echo 'missing production index silently published an ordinary verdict' >&2; exit 1;
    }
    rg -q 'search.production_index_open_failed:.*missing' "$lookup_test_dir/output.log"
    if rg -q '"verdict"[[:space:]]*:' "$lookup_test_dir/output.log"; then
      cat "$lookup_test_dir/output.log" >&2
      echo 'index-open failure published an ordinary verdict' >&2; exit 1
    fi
    echo "LOOKUP_INDEX_FAILURE missing=nonzero reason=reported ordinary_verdict=absent log=$lookup_test_dir/output.log"
    ;;
  native)
    shift
    native_run "$@"
    ;;
  run)
    test -f "${SEARCH_REDUCTION_REQUESTS:-}" || {
      echo 'REQUESTS must name a Lean declaration list' >&2; exit 2;
    }
    case "$(uname -s)" in Darwin) lookup_ext=dylib ;; *) lookup_ext=so ;; esac
    lookup_lib=".lake/build/lean-inspector/reg/lib/libregInspector_LeanInformationAuditLookupDisk.$lookup_ext"
    test -f "$lookup_lib" || {
      echo 'Build SearchReduction.Commands before replaying requests' >&2; exit 2;
    }
    lookup_pickle_lib=".lake/packages/batteries/.lake/build/lib/libbatteries_Batteries.$lookup_ext"
    test -f "$lookup_pickle_lib" || {
      echo 'Build the Batteries native dependency before replaying requests' >&2; exit 2;
    }
    if test -z "${SEARCH_REDUCTION_RESUME+x}"; then
      lookup_request_hash=$(shasum -a 256 "$SEARCH_REDUCTION_REQUESTS")
      export SEARCH_REDUCTION_RESUME="build/lean-inspector/search-reduction-checkpoints/R_lookup-v19-checkpoint-v6/${lookup_request_hash%% *}"
    fi
    while :; do
      lookup_exit=0
      lookup_jobs="${SEARCH_REDUCTION_WORKERS:-8}"
      case "$lookup_jobs" in [1-8]) ;; *) echo 'SEARCH_REDUCTION_WORKERS must be 1..8' >&2; exit 2 ;; esac
      native_run python3 tools/scripts/search-reduction-probe-cache.py lean --load-dynlib="$lookup_pickle_lib" --load-dynlib="$lookup_lib" -j"$lookup_jobs" "$SEARCH_REDUCTION_REQUESTS" || lookup_exit=$?
      if test "$lookup_exit" -ne 75; then exit "$lookup_exit"; fi
    done
    ;;
  source-module)
    test "$#" -eq 4 && test -n "$2" && test -n "$3" && test -n "$4" || {
      echo 'SOURCE_ROOT, SOURCE_LIBRARY and SOURCE_MODULE are required' >&2; exit 2;
    }
    native_run python3 -c 'import os,pathlib,sys; root,library,module=sys.argv[1:]; relative=module.replace(".","/"); output=pathlib.Path(library)/(relative+".olean"); output.parent.mkdir(parents=True,exist_ok=True); os.environ["LEAN_PATH"]=library+os.pathsep+os.environ.get("LEAN_PATH",""); os.execvp("lean",["lean","-j1","--root="+root,"-o",str(output),str(pathlib.Path(root)/(relative+".lean"))])' "$2" "$3" "$4"
    ;;
  *) echo 'Expected native, run or source-module' >&2; exit 2 ;;
esac
