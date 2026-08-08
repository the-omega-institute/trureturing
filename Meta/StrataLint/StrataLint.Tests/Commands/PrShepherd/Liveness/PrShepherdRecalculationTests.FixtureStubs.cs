using System.Text;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    private sealed partial class ShepherdFixture
    {
        private void InstallStubs()
        {
            WriteExecutable(
                "ps",
                """
                #!/usr/bin/env bash
                set -euo pipefail
                if /bin/ps "$@" 2>/dev/null; then
                  exit 0
                fi
                if [[ "${1:-}" == -p && "${3:-}" == -o && "${4:-}" == lstart= ]]; then
                  /bin/kill -0 "$2" 2>/dev/null || exit 1
                  printf 'fixture-process-%s\n' "$2"
                elif [[ "${1:-}" == -p && "${3:-}" == -o && "${4:-}" == pgid= ]]; then
                  /bin/kill -0 "$2" 2>/dev/null || exit 1
                  /usr/bin/ruby -e 'puts Process.getpgid(Integer(ARGV.fetch(0)))' "$2"
                elif [[ "${1:-}" == -axo && "${2:-}" == pid=,ppid= ]]; then
                  /usr/bin/ruby -rfiddle/import <<'RUBY'
                module LibProc
                  extend Fiddle::Importer
                  dlload '/usr/lib/libproc.dylib'
                  extern 'int proc_listpids(unsigned int, unsigned int, void*, int)'
                  extern 'int proc_pidinfo(int, int, unsigned long, void*, int)'
                end
                bytes = LibProc.proc_listpids(1, 0, nil, 0)
                buffer = Fiddle::Pointer.malloc(bytes)
                used = LibProc.proc_listpids(1, 0, buffer, bytes)
                buffer[0, used].unpack('l*').each do |pid|
                  next unless pid.positive?
                  info = Fiddle::Pointer.malloc(136)
                  next unless LibProc.proc_pidinfo(pid, 3, 0, info, 136) == 136
                  fields = info[0, 136].unpack('L*')
                  puts "#{fields[3]} #{fields[4]}"
                end
                RUBY
                else
                  exit 64
                fi
                """);
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
                if [[ -n "${PR_TEST_PAUSE_GH_OPERATION:-}" \
                    && "$*" == *"$PR_TEST_PAUSE_GH_OPERATION"* ]]; then
                  /bin/sleep 1
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
                    printf '%s/%s/%s\n' 'Evidence' 'D5' 'values.json'
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
                  lean-report)
                    mkdir -p "$root/.lake/build/stratalint"
                    cp "$root/Trureturing.lean" \
                      "$root/.lake/build/stratalint/raw-lean-report.json"
                    if [[ "${PR_TEST_LEDGER_CONFLICT:-0}" == 1 ]]; then
                      printf 'lean-report:%s\n' "$(cat "$root/Trureturing.lean")" \
                        >> "$PR_TEST_CALLS.ledger"
                    fi
                    ;;
                  emit)
                    count=0
                    [[ ! -f "$PR_TEST_CALLS.emit-count" ]] \
                      || count="$(cat "$PR_TEST_CALLS.emit-count")"
                    count=$((count + 1))
                    printf '%s' "$count" > "$PR_TEST_CALLS.emit-count"
                    round="$count"
                    if (( round > PR_TEST_TRUTH_GRAPH_DIRTY_ROUNDS )); then
                      round="$PR_TEST_TRUTH_GRAPH_DIRTY_ROUNDS"
                    fi
                    printf 'emit:%s:%s\n' "$count" "$(git -C "$root" rev-parse HEAD)" \
                      >> "$PR_TEST_CALLS.fixed-point"
                    if [[ "${PR_TEST_LEDGER_CONFLICT:-0}" == 1 ]]; then
                      if [[ "$count" == 1 ]]; then
                        cmp -s "$root/Generated/dev-choice.md" \
                          <(git -C "$root" show origin/dev:Generated/dev-choice.md) || exit 81
                        printf 'emit:dev-projection\n' >> "$PR_TEST_CALLS.ledger"
                      fi
                    fi
                    mkdir -p "$root/Generated"
                    printf 'truth graph round %s\n' "$round" > "$root/Generated/artifact.md"
                    if [[ -f "$root/Generated/dev-choice.md" ]]; then
                      printf 'reemitted choice\n' > "$root/Generated/dev-choice.md"
                    fi
                    ;;
                  ingest) ;;
                  emit-check)
                    if [[ "${PR_TEST_LEDGER_CONFLICT:-0}" == 1 ]]; then
                      ledger="$root/Meta/StrataLint/Golden/Frozen/events.jsonl"
                      grep -Fq 'dev-freeze' "$ledger" || exit 82
                      grep -Fq 'appended-under-base' "$ledger" || exit 83
                      grep -Fq 'reattested-candidate' "$ledger" || exit 84
                      ! grep -Eq 'feature-freeze|<<<<<<<|=======|>>>>>>>' "$ledger" || exit 85
                      [[ "$(cat "$root/Trureturing.lean")" == 'candidate trureturing' ]] || exit 86
                      printf 'emit-check:balanced\n' >> "$PR_TEST_CALLS.ledger"
                    fi
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
                  if [[ "${PR_TEST_LEDGER_CONFLICT:-0}" == 1 ]]; then
                    ledger=Meta/StrataLint/Golden/Frozen/events.jsonl
                    cmp -s Trureturing.lean <(git show origin/dev:Trureturing.lean) || exit 81
                    cmp -s Trureturing.lean .lake/build/stratalint/raw-lean-report.json || exit 82
                    cmp -s "$ledger" <(git show "origin/dev:$ledger") || exit 83
                    ! grep -Eq '<<<<<<<|=======|>>>>>>>' "$ledger" || exit 84
                    printf '{"event":"appended-under-base"}\n' >> "$ledger"
                    printf 'ledger-append:base-trureturing:new-report:dev-ledger\n' \
                      >> "$PR_TEST_CALLS.ledger"
                  fi
                  exit 0
                fi
                if [[ "$*" == *"ledger-reattest --candidate-lean-report"* ]]; then
                  printf 'ledger-reattest\n' >> "$PR_TEST_CALLS"
                  if [[ "${PR_TEST_LEDGER_CONFLICT:-0}" == 1 ]]; then
                    ledger=Meta/StrataLint/Golden/Frozen/events.jsonl
                    cmp -s Trureturing.lean <(git show HEAD:Trureturing.lean) || exit 85
                    cmp -s Trureturing.lean .lake/build/stratalint/raw-lean-report.json || exit 86
                    grep -Fq 'appended-under-base' "$ledger" || exit 87
                    printf '{"event":"reattested-candidate"}\n' >> "$ledger"
                    printf 'ledger-reattest:candidate-trureturing:new-report:appended-ledger\n' \
                      >> "$PR_TEST_CALLS.ledger"
                  fi
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
                if [[ -n "${PR_SHEPHERD_BOUND_STEP:-}" \
                    || " $* " == *" fetch "* || " $* " == *" push "* \
                    || " $* " == *" ls-remote "* || " $* " == *" reset --hard "* \
                    || " $* " == *" clean -fd "* || " $* " == *" checkout --detach "* \
                    || " $* " == *" merge --no-commit "* || " $* " == *" add -A "* \
                    || " $* " == *" commit -m "* \
                    || " $* " == *" rev-parse HEAD "* \
                    || "${PR_SHEPHERD_BOUND_STEP:-}" == ledger-* ]]; then
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
                if [[ -n "${PR_TEST_HANG_GIT_OPERATION:-}" \
                    && " $* " == *" ${PR_TEST_HANG_GIT_OPERATION} "* ]]; then
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
                  if [[ "${PR_TEST_FAIL_TARGET:-}" == push ]]; then
                    printf '%s\n' 'remote: pre-receive hook declined' >&2
                    exit "$PR_TEST_FAIL_EXIT"
                  fi
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
