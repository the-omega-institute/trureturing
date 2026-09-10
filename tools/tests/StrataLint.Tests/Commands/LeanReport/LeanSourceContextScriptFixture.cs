namespace StrataLint.Tests;

internal static class LeanSourceContextScriptFixture
{
    // Transport fixture only. Real Lean and strict admission composition has its
    // own compiler-backed fixtures; this stub makes bundle delivery observable.
    internal const string Script = """
        #!/usr/bin/env bash
        set -euo pipefail
        mode="$1"
        shift
        report=""
        base=""
        while [[ $# -gt 0 ]]; do
          case "$1" in
            --report) report="$2"; shift 2 ;;
            --base) base="$2"; shift 2 ;;
            *) shift ;;
          esac
        done
        if [[ "$mode" == prepare ]]; then
          printf '{"schema":"lean-source-context/1","files":[],"registrations":[],"fixtureBase":"%s"}\n' "$base" > "${report}.source-context.json"
        fi
        test -s "${report}.source-context.json"
        """;
}
