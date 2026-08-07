using System.Text;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    private sealed partial class ShepherdFixture
    {
        private void InstallStubs()
        {
            WriteExecutable(
                "gh",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                printf 'api|%s|%s|gh %s\n' \
                  "${PR_SHEPHERD_BOUND_STEP-}" \
                  "${PR_SHEPHERD_BOUND_TIMEOUT_SECONDS-}" "$*" \
                  >> "$PR_TEST_BOUNDED_CALLS"
                if [[ -n "${PR_TEST_FAIL_GH_OPERATION:-}" \
                    && "$*" == *"$PR_TEST_FAIL_GH_OPERATION"* ]]; then
                  exit 89
                fi
                if [[ "${1:-}" == pr && "${2:-}" == list ]]; then
                  [[ " $* " == *" --limit 1000 "* ]] || exit 97
                  if [[ "${PR_TEST_WATCH:-0}" == 1 && " $* " == *" --json autoMergeRequest "* ]]; then
                    count=0
                    [[ ! -f "$PR_TEST_WATCH_STATE" ]] || count="$(cat "$PR_TEST_WATCH_STATE")"
                    count=$((count + 1))
                    printf '%s' "$count" > "$PR_TEST_WATCH_STATE"
                    if [[ "$count" == 1 ]]; then printf '1\n'; else printf '0\n'; fi
                    exit 0
                  fi
                  head="$(git --git-dir "$PR_TEST_ORIGIN" rev-parse "refs/heads/$PR_TEST_HEAD")"
                  base="$PR_TEST_BASE_OID"
                  if [[ -n "${PR_TEST_STATUS_ROLLUP_COUNT:-}" ]]; then
                    row="1\tMERGEABLE\tBLOCKED\t${PR_TEST_HEAD}\t${head}\t${base}\t${PR_TEST_STATUS_ROLLUP_COUNT}\t-\t-"
                  elif [[ "${PR_TEST_NO_CHECKS:-0}" == 1 ]]; then
                    row="1	MERGEABLE	BLOCKED	${PR_TEST_HEAD}	${head}	${base}	0	-	-"
                  elif [[ "${PR_TEST_CONFLICTING:-0}" == 1 ]]; then
                    row="1	CONFLICTING	DIRTY	${PR_TEST_HEAD}	${head}	${base}	1	FAILURE	https://github.com/fixture/repository/actions/runs/123/job/456"
                  else
                    row="1	MERGEABLE	BEHIND	${PR_TEST_HEAD}	${head}	${base}	1	FAILURE	https://github.com/fixture/repository/actions/runs/123/job/456"
                  fi
                  if [[ "${PR_TEST_TWO_DERIVED:-0}" == 1 ]]; then
                    row2="2${row:1}"
                    printf '%b\n' "$row2"
                  fi
                  printf '%b\n' "$row"
                  [[ "$PR_TEST_DUPLICATE" != 1 ]] || printf '%b\n' "$row"
                  exit 0
                fi
                if [[ "${1:-}" == run && "${2:-}" == view ]]; then
                  if [[ "$PR_TEST_SPLIT" == 1 && " $* " != *" --job 456 "* ]]; then
                    printf '%s\n' \
                      'DIGEST_STATUS_INVALID stale Meta/StrataLint/Generated/scribe-emissions.v1.json' \
                      'ECHO_VERIFY_INFRASTRUCTURE residual derivation failed'
                    exit 0
                  fi
                  [[ " $* " == *" --job 456 "* ]] || exit 98
                  if [[ "$PR_TEST_SPLIT" == 1 ]]; then
                    printf '%s\n' 'DIGEST_STATUS_INVALID stale Meta/StrataLint/Generated/scribe-emissions.v1.json'
                    exit 0
                  fi
                  if [[ "$PR_TEST_EXPIRY" == 1 ]]; then
                    printf '%s\n' \
                      'DIGEST_STATUS_INVALID stale Meta/StrataLint/Generated/scribe-emissions.v1.json' \
                      'ECHO_VERIFY_INFRASTRUCTURE residual derivation failed'
                  else
                    printf '%s\n' 'SL-001 unrelated admission failure'
                  fi
                  exit 0
                fi
                if [[ "${1:-}" == pr && "${2:-}" == diff ]]; then
                  if [[ "${PR_TEST_DIFF_FAILURE:-0}" == 1 ]]; then
                    printf '%s\n' 'synthetic pr diff failure' >&2
                    exit 97
                  fi
                  if [[ "${PR_TEST_DERIVED:-1}" == 1 ]]; then
                    printf '%s\n' 'Generated/artifact.md'
                  else
                    printf '%s\n' 'Blueprint/input.scribe.cs'
                  fi
                  exit 0
                fi
                if [[ "${1:-}" == api && "${2:-}" == rate_limit ]]; then
                  [[ "${PR_TEST_GRAPHQL_REMAINING:-}" != unreadable ]] || exit 1
                  printf '%s\n' "${PR_TEST_GRAPHQL_REMAINING:-5000}"
                  exit 0
                fi
                if [[ "${1:-}" == api ]]; then
                  printf 'gh-api:%s\n' "${*:2}" >> "$PR_TEST_CALLS"
                  exit 0
                fi
                if [[ "${1:-}" == pr && "${2:-}" == create ]]; then
                  printf 'gh:%s|GH_TOKEN=%s\n' "$*" "${GH_TOKEN-<unset>}" >> "$PR_TEST_CALLS"
                  printf '%s\n' 'https://github.com/the-omega-institute/trureturing/pull/42'
                  exit 0
                fi
                if [[ "${1:-}" == pr && "${2:-}" == merge ]]; then
                  printf 'gh:%s|GH_TOKEN=%s\n' "$*" "${GH_TOKEN-<unset>}" >> "$PR_TEST_CALLS"
                  exit 0
                fi
                if [[ "${1:-}" == pr && ( "${2:-}" == close || "${2:-}" == reopen ) ]]; then
                  printf 'gh:%s\n' "$*" >> "$PR_TEST_CALLS"
                  exit 0
                fi
                printf 'gh:%s\n' "$*" >> "$PR_TEST_CALLS"
                exit 95
                """);
            WriteExecutable(
                "make",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "${1:-}" != -C || "${4:-}" != worktree ]]; then
                  [[ -z "${GH_TOKEN+x}" ]] || exit 91
                  [[ -z "${GITHUB_TOKEN+x}" ]] || exit 92
                fi
                root="$PWD"
                if [[ "${1:-}" == -C ]]; then root="$2"; shift 2; fi
                [[ "${1:-}" != --no-print-directory ]] || shift
                target="${1:-}"
                printf 'build|%s|%s|make %s\n' \
                  "${PR_SHEPHERD_BOUND_STEP-}" \
                  "${PR_SHEPHERD_BOUND_TIMEOUT_SECONDS-}" "$target" \
                  >> "$PR_TEST_BOUNDED_CALLS"
                if [[ "$target" == worktree ]]; then
                  [[ "$PR_TEST_PAUSE_WORKTREE" != 1 ]] || sleep 2
                  name=''; path=''; base=''
                  for argument in "$@"; do
                    case "$argument" in
                      NAME=*) name="${argument#NAME=}" ;;
                      PATH=*) path="${argument#PATH=}" ;;
                      BASE=*) base="${argument#BASE=}" ;;
                    esac
                  done
                  git -C "$root" worktree add -b "harness/$name" "$path" "$base" >/dev/null
                  printf 'worktree\n' >> "$PR_TEST_CALLS"
                  exit 0
                fi
                printf '%s\n' "$target" >> "$PR_TEST_CALLS"
                if [[ "$target" == "${PR_TEST_HANG_TARGET:-}" ]]; then
                  printf '%s\n' "$$" >> "$PR_TEST_HANGING_PIDS"
                  (
                    trap '' TERM
                    while :; do /bin/sleep 1; done
                  ) &
                  child=$!
                  printf '%s\n' "$child" >> "$PR_TEST_HANGING_PIDS"
                  trap '' TERM
                  while :; do wait "$child" || true; done
                fi
                if [[ "$target" == "$PR_TEST_FAIL_TARGET" \
                    && ( "${PR_TEST_FAIL_PR:-0}" == 0 \
                      || "${PR_SHEPHERD_CURRENT_PR:-0}" == "$PR_TEST_FAIL_PR" ) ]]; then
                  exit "$PR_TEST_FAIL_EXIT"
                fi
                case "$target" in
                  lean-report) mkdir -p "$root/.lake/build/stratalint" ;;
                  emit)
                    mkdir -p "$root/Generated"
                    printf 'derived artifact\n' > "$root/Generated/artifact.md"
                    ;;
                  ingest) ;;
                  emit-check)
                    if [[ "$PR_TEST_MOVE_HEAD" == 1 ]]; then
                      attacker="$(git --git-dir "$PR_TEST_ORIGIN" rev-parse refs/heads/attacker)"
                      git --git-dir "$PR_TEST_ORIGIN" update-ref refs/heads/feature "$attacker"
                    fi
                    ;;
                  *) exit 94 ;;
                esac
                """);
            WriteExecutable(
                "dotnet",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                printf 'build|%s|%s|dotnet %s\n' \
                  "${PR_SHEPHERD_BOUND_STEP-}" \
                  "${PR_SHEPHERD_BOUND_TIMEOUT_SECONDS-}" "$*" \
                  >> "$PR_TEST_BOUNDED_CALLS"
                [[ -z "${GH_TOKEN+x}" ]] || exit 91
                [[ -z "${GITHUB_TOKEN+x}" ]] || exit 92
                if [[ "$*" == *"ledger-append --candidate-lean-report"* ]]; then
                  printf 'ledger-append\n' >> "$PR_TEST_CALLS"
                  exit 0
                fi
                [[ "$*" == *"echo-verify --emit --base origin/dev"* ]] || exit 96
                temporary="$(find "$PWD" -type f -name '*.pr-shepherd.*' -print -quit)"; if [[ -n "$temporary" ]]; then printf 'inside-workspace:%s\n' "$temporary" > "$PR_TEST_CALLS.projection"; else printf 'outside-workspace\n' > "$PR_TEST_CALLS.projection"; fi
                printf 'echo-verify\n' >> "$PR_TEST_CALLS"
                printf '%s\n' '<!-- echo-residual-summary:v3 residual=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa -->' '# Echo Residual Summary'
                """);
            WriteExecutable(
                "git",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ " $* " == *" fetch "* || " $* " == *" push "* \
                    || " $* " == *" ls-remote "* ]]; then
                  printf 'git|%s|%s|git %s\n' \
                    "${PR_SHEPHERD_BOUND_STEP-}" \
                    "${PR_SHEPHERD_BOUND_TIMEOUT_SECONDS-}" "$*" \
                    >> "$PR_TEST_BOUNDED_CALLS"
                fi
                if [[ " $* " == *" fetch --no-tags "* ]]; then
                  if [[ "$PR_TEST_MOVE_HEAD_DURING_FETCH" == 1 ]]; then
                    attacker="$(/usr/bin/git --git-dir "$PR_TEST_ORIGIN" rev-parse refs/heads/attacker)"
                    /usr/bin/git --git-dir "$PR_TEST_ORIGIN" update-ref \
                      "refs/heads/$PR_TEST_HEAD" "$attacker"
                  fi
                  if [[ "$PR_TEST_MOVE_BASE_DURING_FETCH" == 1 ]]; then
                    /usr/bin/git --git-dir "$PR_TEST_ORIGIN" update-ref \
                      refs/heads/dev "$PR_TEST_MOVED_BASE"
                  fi
                fi
                if [[ "$PR_TEST_FAIL_MERGE" == 1 && " $* " == *" merge --no-commit "* ]]; then
                  exit 97
                fi
                if [[ "${PR_TEST_CONFLICTING:-0}" == 1 && " $* " == *" merge --no-commit "* ]]; then
                  printf 'local-merge\n' >> "$PR_TEST_CALLS"
                fi
                if [[ " $* " == *" push "* ]]; then
                  push_call=push
                  for argument in "$@"; do
                    case "$argument" in
                      -f|--force|--force=*|--force-with-lease*|--force-if-includes|+*)
                        push_call=force-push
                        ;;
                    esac
                  done
                  printf '%s\n' "$push_call" >> "$PR_TEST_CALLS"
                fi
                exec /usr/bin/git "$@"
                """);
            WriteExecutable(
                "cat",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "${PR_TEST_DELAY_LOCK_READ:-0}" == 1 && "${1:-}" == */lock-*/pid ]]; then
                  value="$(/bin/cat "$1")"
                  if mkdir "$PR_TEST_LOCK_READ_MARKER" 2>/dev/null; then sleep 1; fi
                  printf '%s' "$value"
                  exit 0
                fi
                exec /bin/cat "$@"
                """);
        }

        private void WriteExecutable(string name, string contents)
        {
            if (OperatingSystem.IsWindows()) return;
            var path = Path.Combine(bin, name);
            File.WriteAllText(path, contents + "\n", new UTF8Encoding(false));
            File.SetUnixFileMode(
                path,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }
    }
}
