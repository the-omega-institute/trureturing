#!/usr/bin/env bash
set -euo pipefail

# Resolve Lake's environment, then release its build graph before native work.
native_run() {
  python3 -c 'import json, os, subprocess, sys; native_env = json.loads(subprocess.check_output(["lake", "-d", "tools/lean-inspector-reg", "env", "python3", "-c", "import json, os; print(json.dumps(dict(os.environ)))"], text=True)); os.execvpe(sys.argv[1], sys.argv[1:], native_env)' "$@"
}

case "${1:-}" in
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
      export SEARCH_REDUCTION_RESUME="build/lean-inspector/search-reduction-checkpoints/R_lookup-v15-checkpoint-v3/${lookup_request_hash%% *}"
    fi
    while :; do
      lookup_exit=0
      lookup_jobs="${SEARCH_REDUCTION_WORKERS:-8}"
      case "$lookup_jobs" in [1-8]) ;; *) echo 'SEARCH_REDUCTION_WORKERS must be 1..8' >&2; exit 2 ;; esac
      native_run lean --load-dynlib="$lookup_pickle_lib" --load-dynlib="$lookup_lib" -j"$lookup_jobs" "$SEARCH_REDUCTION_REQUESTS" || lookup_exit=$?
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
