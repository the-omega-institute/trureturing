#!/bin/bash
# Shared input, locking, process-table and state operations. Source from pipeline tools.
OP_PIPELINE_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
OP_REPO=$(cd "$OP_PIPELINE_DIR/../../../../.." && pwd -P)
op_fail() { printf 'PIPELINE_%s %s\n' "$2" "$3" >&2; exit "$1"; }
op_need() { local c; for c in "$@"; do command -v "$c" >/dev/null 2>&1 || op_fail 12 TOOL_MISSING "$c"; done; }
op_uint() { case "$2" in ''|*[!0-9]*) op_fail 13 INVALID_INPUT "$1 must be a nonnegative integer";; esac; }
op_name() { case "$1" in ''|*[!a-zA-Z0-9._-]*|.|..) op_fail 13 INVALID_NAME "$1";; esac; }
op_file() { [ -f "$1" ] && [ -r "$1" ] || op_fail 11 INPUT_MISSING "$1"; }
op_init() {
  op_need python3 git
  python3 -c 'import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)' || op_fail 12 TOOL_VERSION 'Python 3.9 or newer required'
  OP_STATE=$(python3 "$OP_PIPELINE_DIR/../briefgen/common.py" state-dir) || op_fail 16 IO_ERROR OP_STATE
  export OP_STATE
  OP_REFRESH_LOCK=$(python3 "$OP_PIPELINE_DIR/../briefgen/common.py" main-lean-lock) || op_fail 16 IO_ERROR OP_REFRESH_LOCK
  SSHX_HOME=${SSHX_HOME:-${HOME:?HOME or SSHX_HOME required}/.sshx}
  OP_NAME_PREFIX=${OP_NAME_PREFIX:-}
  SSHX_HOME=$(python3 -c 'import os,sys;print(os.path.abspath(sys.argv[1]))' "$SSHX_HOME")
  [ -z "$OP_NAME_PREFIX" ] || op_name "$OP_NAME_PREFIX"
  OP_POLL_SECONDS=${OP_POLL_SECONDS:-30}
  OP_LOCK_ROUNDS=${OP_LOCK_ROUNDS:-120}
  op_uint OP_POLL_SECONDS "$OP_POLL_SECONDS"; op_uint OP_LOCK_ROUNDS "$OP_LOCK_ROUNDS"
  export OP_STATE OP_REFRESH_LOCK SSHX_HOME OP_NAME_PREFIX
}
op_scratch() {
  [ -n "${OP_SCRATCH:-}" ] || op_fail 11 INPUT_MISSING OP_SCRATCH
  mkdir -p "$OP_SCRATCH/briefs" "$OP_SCRATCH/results" "$OP_SCRATCH/logs" "$OP_SCRATCH/preset" "$OP_SCRATCH/waiters" || op_fail 16 IO_ERROR OP_SCRATCH
  OP_SCRATCH=$(cd "$OP_SCRATCH" && pwd -P)
  export OP_SCRATCH
}
op_main() {
  OP_MAIN=$(git -C "$OP_REPO" worktree list --porcelain | op_data main) || op_fail 16 MAIN_CHECKOUT 'cannot read first worktree'
  [ -d "$OP_MAIN" ] && [ "$(git -C "$OP_MAIN" rev-parse --is-bare-repository)" = false ] || op_fail 11 MAIN_CHECKOUT 'first worktree is not a non-bare checkout'
}
op_snapshot() {
  OP_PS=$(ps -axo pid=,ppid=,command=) && [ -n "$OP_PS" ] || return 1
}
op_process() { printf '%s\n' "$OP_PS" | op_data "$@"; }
op_lock() {
  local lock=$1 rounds=${2:-$OP_LOCK_ROUNDS} i=0
  while [ "$i" -lt "$rounds" ]; do
    mkdir "$lock" 2>/dev/null && return 0
    i=$((i+1)); sleep "$OP_POLL_SECONDS"
  done
  return 1
}
op_latest_result() { op_data result "$1"; }
op_selftest() { bash "$OP_PIPELINE_DIR/selftest.sh" "$1"; }
op_data() {
  # Preserve stdin separately: Python source occupies the heredoc descriptor.
  python3 -c 'import sys; sys.path.insert(0, sys.argv.pop(1)); exec(sys.argv.pop(1))' "$OP_PIPELINE_DIR/../briefgen" "$(cat <<'PY'
import datetime, json, os, pathlib, re, shlex, sys, time
from common import main_warm_stamp
args = sys.argv[1:]
action = args.pop(0)
def die(message):
    print('PIPELINE_DATA_ERROR ' + message, file=sys.stderr)
    sys.exit(16)
def rows():
    out = []
    for line in sys.stdin:
        m = re.match(r'\s*(\d+)\s+(\d+)\s+(.*)', line.rstrip('\n'))
        if m:
            out.append((int(m[1]), int(m[2]), m[3]))
    return out
def runner(command):
    if ' -c ' in command:
        return None
    m = re.match(r'^(?:(?:\S*/)?bash\s+)?(?:.*?/)?run-codex-worker\.sh\s+', command)
    if not m:
        return None
    f = re.search(r'(?:^|\s)--flight-id ([0-9a-f]{24})(?:\s|$)', command)
    w = re.search(r'(?:^|\s)--work-target (.*?)(?= --[a-zA-Z]|$)', command)
    if not f:
        return None
    return f[1], os.path.realpath(w[1].strip("\"'")) if w else ''
def priority(name):
    prefix = os.environ.get('OP_NAME_PREFIX', '')
    if prefix and name.startswith(prefix):
        name = name[len(prefix):]
    if name.startswith(('review-', 'implb-', 'rework-', 'hotfix-')):
        return 0
    if name.startswith(('mirror-', 'impla-', 'fixa-', 'fixb-', 'fix-')):
        return 1
    return 2
def flights():
    result = {}
    p = pathlib.Path(os.environ['OP_SCRATCH']) / 'flights.txt'
    if p.exists():
        for line in p.read_text().splitlines():
            fields = line.split()
            if fields:
                result[fields[0]] = fields[1] if len(fields) > 1 else ''
    return result
def result_path(flight):
    if not re.fullmatch('[0-9a-f]{24}', flight):
        die('invalid flight id')
    candidates = []
    for p in (pathlib.Path(os.environ['SSHX_HOME']) / flight).glob('attempt-*/result.json'):
        m = re.fullmatch(r'attempt-(\d+)', p.parent.name)
        if m and p.is_file():
            candidates.append((int(m[1]), str(p)))
    return max(candidates, default=(0, 'NO_RESULT'))[1]
def waiter_records(procs):
    scratch = pathlib.Path(os.environ['OP_SCRATCH'])
    by_pid = {p: c for p, _, c in procs}
    records = {}
    for p in (scratch / 'waiters').glob('*.json'):
        try:
            data = json.loads(p.read_text())
            command = by_pid.get(data['pid'], '')
            if re.match(r'^(?:\S*/)?bash\s+.*(?:seat-wait|dispatch-when-free)\.(?:sh|new) ', command) and ' -c ' not in command:
                records[data['name']] = data
        except (OSError, ValueError, KeyError):
            die('invalid waiter record ' + str(p))
    latest = flights()
    for pid, _, command in procs:
        if ' -c ' in command:
            continue
        try:
            words = shlex.split(command)
        except ValueError:
            continue
        if len(words) >= 6 and os.path.basename(words[0]) == 'bash' and os.path.basename(words[1]) in ('dispatch-when-free.sh', 'dispatch-when-free.new', 'seat-wait.sh'):
            name = words[2]
            if latest.get(name) and name not in records:
                records[name] = dict(name=name, flight=latest[name], worktree=words[4], pid=pid)
    return list(records.values())
try:
    if action == 'main':
        listing = sys.stdin.read().splitlines()
        first = listing[0] if listing else ''
        if not first.startswith('worktree '):
            die('first worktree missing or bare')
        print(first[len('worktree '):])
    elif action == 'result':
        print(result_path(args[0]))
    elif action == 'register':
        name, flight, worktree, pid, since = args
        path = pathlib.Path(os.environ['OP_SCRATCH']) / 'waiters' / (name + '.json')
        tmp = path.with_suffix('.tmp')
        tmp.write_text(json.dumps(dict(name=name, flight=flight, worktree=worktree, pid=int(pid), since=int(since))))
        tmp.replace(path)
    elif action in ('gate', 'alive', 'busy', 'pro-busy', 'sweep', 'reap', 'migration'):
        procs = rows()
        if not procs:
            die('no readable process rows')
        running = {info[0]: info[1] for _, _, c in procs if (info := runner(c))}
        if action == 'pro-busy':
            active = any(re.match(r'^(?:\S*/)?(?:python[0-9.]*|bash)\s+.*(?:nyx\.py\s+ask|nyx-seat\.sh|run-oracle-worker\.sh)(?:\s|$)', c) and ' -c ' not in c for _, _, c in procs)
            sys.exit(0 if active else 1)
        elif action == 'alive':
            sys.exit(0 if args[0] in running else 1)
        elif action == 'busy':
            sys.exit(0 if os.path.realpath(args[0]) in running.values() else 1)
        elif action == 'gate':
            name, tree, cap, since = args
            tree = os.path.realpath(tree)
            if tree in running.values():
                print('worktree-busy'); sys.exit(1)
            if len(running) >= int(cap):
                print('seat-cap'); sys.exit(1)
            known = flights()
            aged = priority(name) == 2 and time.time() - int(since) >= 14400 and sum(priority(n) == 2 for n, f in known.items() if f in running) < 2
            if not aged:
                for record in waiter_records(procs):
                    if record['name'] != name and priority(record['name']) < priority(name) and record['flight'] not in running and os.path.realpath(record['worktree']) not in running.values():
                        print('higher-priority=' + record['name']); sys.exit(1)
            print('seats=' + str(len(running)) + ' prio=' + str(priority(name)))
        elif action == 'sweep':
            for name, flight in flights().items():
                if flight and (pathlib.Path(os.environ['SSHX_HOME']) / flight).is_dir() and flight not in running:
                    print(name + ' ' + flight)
        elif action == 'reap':
            flight = args[0]
            needle = str(pathlib.Path(os.environ['SSHX_HOME']) / flight) + '/attempt-'
            for pid, _, command in procs:
                if needle in command:
                    print(pid)
        else:
            pattern = re.compile(args[0])
            matches = [(p, c) for p, _, c in procs if pattern.search(c) and p not in (int(args[1]), os.getpid())]
            if len(matches) != 1:
                die('migration requires exactly one matching chain')
            pid, command = matches[0]
            # Only the chain shell may be signalled. Its descendants remain untouched.
            if not re.match(r'^(?:\S*/)?(?:bash|zsh)\s+(?!-c\s)', command) or any(x in command for x in ('codex', 'run-codex-worker.sh', 'dispatch')):
                die('protected or ambiguous migration process')
            print(pid)
    elif action == 'preset':
        name = args[0]
        scratch = pathlib.Path(os.environ['OP_SCRATCH'])
        path = scratch / 'preset' / name
        text = path.read_text().rstrip('\n')
        kind, sep, value = text.partition(' ')
        if not sep or not value or kind not in ('DONE', 'WAIT'):
            die('invalid preset ' + name)
        if kind == 'DONE' and not pathlib.Path(value).is_file():
            die('DONE result missing ' + value)
        if kind == 'WAIT' and not re.fullmatch('[0-9a-f]{24}', value):
            die('invalid WAIT flight')
        print(kind); print(value)
    elif action == 'recover':
        # STEP names have no prefix; log paths may contain whitespace.
        prefix = os.environ.get('OP_NAME_PREFIX', '')
        latest = flights()
        name = args[0]
        scratch = pathlib.Path(os.environ['OP_SCRATCH'])
        log = scratch / 'logs' / (name + '.log')
        text = log.read_text(errors='replace') if log.exists() else ''
        root = str(pathlib.Path(os.environ['SSHX_HOME']))
        paths = re.findall(re.escape(root) + r'/[0-9a-f]{24}/attempt-\d+/result\.json', text)
        for path in reversed(paths):
            if pathlib.Path(path).is_file():
                print('DONE ' + path); sys.exit(0)
        flight = latest.get(prefix + name, '')
        if flight:
            if flight in {r[0] for _, _, c in rows() if (r := runner(c))}:
                print('WAIT ' + flight); sys.exit(0)
            path = result_path(flight)
            if path != 'NO_RESULT':
                print('DONE ' + path); sys.exit(0)
        print('NONE')
    elif action == 'steps':
        # An explicit sidecar is preferred; canonical waiter calls can be recovered directly.
        command = pathlib.Path(args[0]).read_text()
        prefix = os.environ.get('OP_NAME_PREFIX', '')
        matches = list(re.finditer(r'(?:seat-wait|dispatch-when-free)\.(?:sh|new)\s+([A-Za-z0-9._-]+)', command))
        if not matches and re.search(r'chain-[A-Za-z0-9._-]+\.sh', command):
            die('compound chain requires running/NAME.steps metadata')
        for match in matches:
            name = match[1]
            print(name[len(prefix):] if prefix and name.startswith(prefix) else name)
    elif action == 'stale':
        main, tree, lag = map(str, args)
        stamp = main_warm_stamp(main)
        if not stamp.is_file():
            print('skip main-not-stamped'); sys.exit(0)
        sha, mtime = stamp.read_text().split()
        clone = pathlib.Path(tree) / '.lake/build/.main-cloned-at'
        oldtime = clone.read_text().split()[1] if clone.is_file() else ''
        version = 'none'
        import subprocess
        got = subprocess.run(['git', '-C', main, 'show', sha + ':lean-report-inputs.json'], capture_output=True, text=True)
        if got.returncode == 0:
            version = json.loads(got.stdout).get('report_cache_release_semantic_version', 'none')
        reuse = pathlib.Path(tree) / '.lake/build/stratalint/raw-lean-report.json.reuse.json'
        oldversion = json.loads(reuse.read_text()).get('inputs', {}).get('semantic_version') if reuse.is_file() else None
        parse = lambda s: datetime.datetime.fromisoformat(s.replace('Z', '+00:00'))
        stale = not oldtime or (parse(mtime) - parse(oldtime)).total_seconds() > float(lag)
        print(('refresh ' + sha + ' ' + mtime) if (version != 'none' and oldversion != version) or stale else 'skip tree-cloned-recently')
    else:
        die('unknown operation ' + action)
except (OSError, ValueError, KeyError, IndexError) as error:
    die(str(error))
PY
)" "$@"
}

if [ "${BASH_SOURCE[0]}" = "$0" ]; then
  [ "${1:-}" = --selftest ] || op_fail 10 USAGE 'source common.sh'
  op_selftest common
fi

op_presets() {
  local dry=$1 n preset kind flight log
  shift
  for n in "$@"; do
    op_name "$n"
    op_snapshot || op_fail 16 PROCESS_LIST_FAILED ps
    preset=$(op_process recover "$n") || exit $?
    [ "$preset" != NONE ] || break
    echo "preset $OP_NAME_PREFIX$n $preset"
    if [ "$dry" -eq 0 ]; then
      printf '%s\n' "$preset" > "$OP_SCRATCH/preset/$OP_NAME_PREFIX$n.tmp" && mv "$OP_SCRATCH/preset/$OP_NAME_PREFIX$n.tmp" "$OP_SCRATCH/preset/$OP_NAME_PREFIX$n" || op_fail 16 IO_ERROR preset
      kind=${preset%% *}; flight=${preset#* }; log=$OP_SCRATCH/logs/$n.log
      if [ "$kind" = WAIT ] && [ -f "$log" ]; then
        mkdir -p "$OP_SCRATCH/logs/archive" && mv "$log" "$OP_SCRATCH/logs/archive/$n.$flight.log" || op_fail 16 IO_ERROR archive
      fi
    fi
    [ "${preset%% *}" != WAIT ] || break
  done
}
op_spool() {
  local job=$1 command=$2
  op_name "$job"
  mkdir -p "$OP_STATE/spool" || op_fail 16 IO_ERROR spool
  [ ! -e "$OP_STATE/spool/$job.job" ] || op_fail 14 JOB_EXISTS "$job"
  printf '%s\n' "$command" > "$OP_STATE/spool/$job.job.tmp" && mv "$OP_STATE/spool/$job.job.tmp" "$OP_STATE/spool/$job.job" || op_fail 16 IO_ERROR spool
}

op_gptpro_ask() (
  local brief=$1 out=$2 rc lock=$OP_STATE/gptpro.lock n=0
  trap 'exit 130' INT
  trap 'exit 143' TERM
  op_file "$brief"; op_file "$OP_REPO/tools/scripts/agent/nyx/nyx.py"
  mkdir -p "$OP_STATE" || op_fail 16 IO_ERROR OP_STATE
  op_lock "$lock" || op_fail 15 LOCK_TIMEOUT gptpro.lock
  trap 'rmdir "$lock"' EXIT
  # Existing broker carriers must drain before a locked request starts.
  while :; do
    op_snapshot || op_fail 16 PROCESS_LIST_FAILED ps
    if op_process pro-busy; then
      n=$((n+1)); [ "$n" -lt "$OP_LOCK_ROUNDS" ] || op_fail 15 BROKER_BUSY 'active GPT Pro request'
      sleep "$OP_POLL_SECONDS"
    else
      rc=$?; [ "$rc" -eq 1 ] || exit "$rc"
      break
    fi
  done
  python3 "$OP_REPO/tools/scripts/agent/nyx/nyx.py" ask "$brief" "$out"; rc=$?
  exit "$rc"
)
