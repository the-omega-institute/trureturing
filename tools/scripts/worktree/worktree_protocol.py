#!/usr/bin/env python3
"""Git-owned worktree lifecycle protocol.

Lifetime is derived only from the current HEAD committer timestamp and the
native ``branch.<name>.worktreeStaleHead`` configuration value. There is no
occupancy lock, activity scan, allocation ledger, or process liveness probe.
"""
import argparse
from contextvars import ContextVar
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from urllib.parse import unquote, urlsplit

try:
    from maintenance_log import MaintenanceLog
except ImportError:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    try:
        from maintenance_log import MaintenanceLog
    except ImportError:
        MaintenanceLog = None

if __name__ == "__main__":
    sys.modules["worktree_protocol"] = sys.modules[__name__]

LOG = None
LOG_ACTION = None
LOG_LAST = {}
AUXILIARY_DEADLINE = ContextVar("worktree_auxiliary_deadline", default=None)
SCOPED_PROCESS_ENVIRONMENT = {
    "MSBUILDDISABLENODEREUSE": "1",
    "DOTNET_CLI_USE_MSBUILD_SERVER": "0",
    "UseSharedCompilation": "false",
    "UseRazorBuildServer": "false",
    "_RazorForceBuildServer": "false",
}


class Refused(RuntimeError):
    pass


class GitFailure(Refused):
    """A failed native Git command, distinct from a policy refusal."""


def inherited_environment():
    permitted = {
        "GIT_SSH", "GIT_SSH_COMMAND", "GIT_SSH_VARIANT", "GIT_ASKPASS",
        "GIT_TERMINAL_PROMPT", "GIT_AUTHOR_NAME", "GIT_AUTHOR_EMAIL",
        "GIT_AUTHOR_DATE", "GIT_COMMITTER_NAME", "GIT_COMMITTER_EMAIL",
        "GIT_COMMITTER_DATE",
    }
    return {key: val for key, val in os.environ.items()
            if not key.startswith("GIT_") or key in permitted}


def scoped_process_environment():
    return dict(SCOPED_PROCESS_ENVIRONMENT)


def git_environment(overrides=None):
    environment = inherited_environment()
    environment.update(overrides or {})
    environment.update(scoped_process_environment())
    return environment


def git(root, *args, env=None, input=None, check=True, timeout=300):
    deadline = AUXILIARY_DEADLINE.get()
    if deadline is not None:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError("agent_state_budget_exhausted")
        timeout = min(timeout, remaining)
    command = ["git", "-C", str(root), *map(str, args)]
    try:
        result = subprocess.run(command, input=input, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, env=git_environment(env),
                                timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        raise
    if check and result.returncode:
        raise GitFailure(result.stderr.decode(errors="replace").strip() or "git failed")
    return result


def value(root, *args):
    return os.fsdecode(git(root, *args).stdout).strip()


def common(root):
    return Path(value(root, "rev-parse", "--path-format=absolute", "--git-common-dir")).resolve()


def inventory(root):
    records = []
    for raw in git(root, "worktree", "list", "--porcelain", "-z").stdout.split(b"\0\0"):
        item = {}
        for field in raw.split(b"\0"):
            key, _, val = os.fsdecode(field).partition(" ")
            if key:
                item[key] = val
        if item:
            records.append(item)
    return records


def identity(source, path, snapshot=None, deadline=None):
    """Validate native registration and the linked checkout pointer."""
    del deadline
    path = Path(path).absolute()
    if path.is_symlink() or not path.is_dir():
        raise Refused("missing_or_linked_tree")
    path = path.resolve()
    rows = snapshot[0] if snapshot is not None else inventory(source)
    source_common = snapshot[1] if snapshot is not None else common(source)
    matches = [row for row in rows if Path(row["worktree"]).resolve() == path]
    if len(matches) != 1 or common(path) != source_common:
        raise Refused("repository_identity")
    if Path(value(path, "rev-parse", "--show-toplevel")).resolve() != path:
        raise Refused("tree_identity")
    metadata = Path(value(path, "rev-parse", "--absolute-git-dir")).resolve()
    if metadata != source_common:
        pointer = path / ".git"
        if pointer.is_symlink() or not pointer.is_file():
            raise Refused("git_pointer")
        text = pointer.read_text().strip()
        if not text.startswith("gitdir: ") or (path / text[8:]).resolve() != metadata:
            raise Refused("git_pointer_identity")
        backlink = (metadata / "gitdir").read_text().strip()
        if Path(backlink).resolve() != pointer.resolve():
            raise Refused("git_backlink")
    return matches[0], metadata


def branch_name(root):
    result = git(root, "symbolic-ref", "--quiet", "HEAD", check=False)
    if result.returncode == 1:
        return None
    if result.returncode:
        raise GitFailure(result.stderr.decode(errors="replace").strip() or "symbolic-ref failed")
    return os.fsdecode(result.stdout).strip()


def head_oid(root):
    return value(root, "rev-parse", "--verify", "HEAD^{commit}")


def head_committer_time(root):
    raw = value(root, "show", "-s", "--format=%ct", "HEAD")
    try:
        return int(raw)
    except ValueError as error:
        raise Refused("head_timestamp_unknown") from error


def branch_config_key(branch):
    short = branch.removeprefix("refs/heads/")
    if not short or not branch.startswith("refs/heads/"):
        raise Refused("current_branch_required")
    return "branch." + short + ".worktreeStaleHead"


def stale_head(source, branch):
    key = branch_config_key(branch)
    result = git(source, "config", "--local", "--get", key, check=False)
    if result.returncode == 1:
        return None
    if result.returncode:
        raise GitFailure(result.stderr.decode(errors="replace").strip() or "stale marker read failed")
    return os.fsdecode(result.stdout).strip() or None


def mark_stale(source, path):
    item, _ = identity(source, path)
    rows = inventory(source)
    if Path(rows[0]["worktree"]).resolve() == Path(path).resolve():
        raise Refused("main_worktree")
    branch = item.get("branch")
    if not branch or branch == "HEAD":
        raise Refused("current_branch_required")
    head = head_oid(path)
    git(source, "config", "--local", "--replace-all", branch_config_key(branch), head)
    return dict(event="worktree_stale", status="stale", path=str(Path(path).resolve()),
                branch=branch.removeprefix("refs/heads/"), head=head)


def clear_matching_stale(source, branch, head):
    full = branch if branch.startswith("refs/heads/") else "refs/heads/" + branch
    if stale_head(source, full) == head:
        git(source, "config", "--local", "--unset-all", branch_config_key(full))


def worktree_age(path, now=None):
    now = time.time() if now is None else now
    return now - head_committer_time(path)


def reusable(path, source, now=None):
    item, _ = identity(source, path)
    branch = item.get("branch")
    if not branch or branch == "HEAD":
        return False, "detached_head"
    age = worktree_age(path, now)
    if age > 6 * 60 * 60:
        return False, "head_older_than_6h"
    head = head_oid(path)
    if stale_head(source, branch) == head:
        return True, "stale"
    if age > 4 * 60 * 60:
        return True, "head_older_than_4h"
    return False, "head_recent"


def remote_endpoint(root, remote, push=False):
    flags = ["--push", "--all"] if push else []
    result = git(root, "remote", "get-url", *flags, "--", remote, check=False)
    endpoints = os.fsdecode(result.stdout).splitlines() if result.returncode == 0 else [remote]
    if len(endpoints) != 1 or not endpoints[0]:
        raise Refused("single_remote_endpoint_required")
    endpoint = endpoints[0]
    parsed = urlsplit(endpoint)
    if parsed.scheme == "file" or not parsed.scheme and ":" not in endpoint:
        path = Path(unquote(parsed.path) if parsed.scheme == "file" else endpoint)
        path = (Path(root) / path).resolve()
        if common(path) == common(root):
            raise Refused("remote_is_local_repository")
        return str(path)
    return endpoint


def read_input(source, file):
    del source
    return Path(file).resolve().read_bytes()


def _reason_code(raw):
    if raw is None:
        return None
    code = str(raw).strip().split(":", 1)[0].split(None, 1)[0]
    return re.sub(r"[^A-Za-z0-9_.-]", "_", code)[:96] or "unknown"


def _log_operation(action, *, status=None, outcome=None, reason=None, error=None, **fields):
    global LOG_LAST
    LOG_LAST = {"action": action, "operation": action, "status": status, "outcome": outcome,
                "reason_code": _reason_code(reason),
                "error_type": type(error).__name__ if error is not None else None, **fields}
    LOG_LAST = {key: value for key, value in LOG_LAST.items() if value is not None}
    if LOG is not None:
        LOG.emit("operation_finished", **LOG_LAST)


def _log_result(action, result):
    status = result.get("status") if isinstance(result, dict) else "failed"
    _log_operation(action, status=status, outcome=status,
                   reason=result.get("reason") if isinstance(result, dict) else "invalid_result")


def with_command(options):
    if not options.argv:
        raise Refused("missing_command")
    path = Path(options.path).resolve()
    identity(options.source, path)
    if not options.no_agent_summary:
        from worktree_agent_state import report
        report(options.source)
        options.no_agent_summary = True
    os.chdir(path)
    os.execvpe(options.argv[0], options.argv, git_environment())


def reuse(options, allow_recovered_base=False):
    del allow_recovered_base
    if options.path.is_symlink():
        raise Refused("linked_tree")
    item, _ = identity(options.source, options.path)
    expected_branch = "refs/heads/" + options.branch
    if item.get("branch") != expected_branch:
        raise Refused("incompatible_branch")
    base = value(options.source, "rev-parse", "--verify", options.base + "^{commit}")
    if git(options.path, "merge-base", "--is-ancestor", base, "HEAD", check=False).returncode:
        raise Refused("incompatible_base")
    for pin in ("lean-toolchain", "lake-manifest.json"):
        expected = git(options.source, "show", base + ":" + pin).stdout
        if (options.path / pin).read_bytes() != expected:
            raise Refused("incompatible_pin:" + pin)
    clear_matching_stale(options.source, expected_branch, head_oid(options.path))
    from worktree_agent_state import record
    record(options.source, options.path, branch=expected_branch)
    return dict(event="worktree_init", status="reused", path=str(options.path.resolve()),
                branch=options.branch, base_revision=base)


def _main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path.cwd())
    parser.add_argument("--no-agent-summary", action="store_true", help=argparse.SUPPRESS)
    commands = parser.add_subparsers(dest="action", required=True)
    commands.add_parser("pending", help="show current-agent pending worktrees (advisory)")
    registration = commands.add_parser("record-registration", help=argparse.SUPPRESS)
    registration.add_argument("--path", type=Path, required=True)
    registration.add_argument("--branch", required=True)
    command = commands.add_parser("with")
    command.add_argument("--path", type=Path, default=Path.cwd())
    command.add_argument("argv", nargs=argparse.REMAINDER)
    initializing = commands.add_parser("initialize", help=argparse.SUPPRESS)
    initializing.add_argument("--path", type=Path, required=True)
    initializing.add_argument("argv", nargs=argparse.REMAINDER)
    joined = commands.add_parser("reuse")
    joined.add_argument("--path", type=Path, required=True)
    joined.add_argument("--branch", required=True)
    joined.add_argument("--base", required=True)
    stale = commands.add_parser("stale")
    stale.add_argument("--path", type=Path, default=Path.cwd())
    returned = commands.add_parser("return")
    returned.add_argument("--path", type=Path, default=Path.cwd())
    returned.add_argument("--pr", type=int)
    returned.add_argument("--writers-joined", action="store_true")
    claimed = commands.add_parser("claim")
    claimed.add_argument("--path", type=Path)
    claimed.add_argument("--branch", required=True)
    claimed.add_argument("--base", required=True)
    claimed.add_argument("--skip-restore", action="store_true")
    pool = commands.add_parser("pool")
    pool.add_argument("--dev", required=True)
    pool.add_argument("--force", action="store_true")
    pool.add_argument("--exclude-path", type=Path, action="append", default=[])
    recovery = commands.add_parser("recover-init")
    recovery.add_argument("--path", type=Path, required=True)
    recovery.add_argument("--branch", required=True)
    recovery.add_argument("--base", required=True)
    recovery.add_argument("--skip-restore", action="store_true")
    removal = commands.add_parser("remove")
    removal.add_argument("--names", default="")
    removal.add_argument("--path", action="append", type=Path, default=[])
    removal.add_argument("--force", action="store_true")
    removal.add_argument("--preview", action="store_true")
    removal.add_argument("--expected", action="append", default=[])
    qualification = commands.add_parser("qualify")
    qualification.add_argument("--path", action="append", type=Path, required=True)
    qualification.add_argument("--stream", action="store_true")
    qualification.add_argument("--budget-seconds", type=float)
    for action in ("checkpoint", "publish", "finalize"):
        publication = commands.add_parser(action)
        publication.add_argument("--path", type=Path, default=Path.cwd())
        publication.add_argument("--message-file")
        publication.add_argument("--remote", default="origin")
        publication.add_argument("--branch")
        publication.add_argument("--commit", default="HEAD")
        publication.add_argument("--writers-joined", action="store_true")
    for action in ("prepare-mirror", "validate-mirror"):
        mirror = commands.add_parser(action)
        mirror.add_argument("--base", required=True)
        mirror.add_argument("--merge", required=True)
        mirror.add_argument("--message", required=True)
        if action == "prepare-mirror":
            mirror.add_argument("--path", type=Path, required=True)
            mirror.add_argument("--branch", required=True)
            mirror.add_argument("--remote", default="origin")
        else:
            mirror.add_argument("--commit", required=True)
    options = parser.parse_args(argv)
    global LOG, LOG_ACTION, LOG_LAST
    LOG_ACTION, LOG_LAST = options.action, {}
    LOG = MaintenanceLog("worktree-protocol", options.source) if MaintenanceLog else None
    summary_source = options.source
    # Anchor the final view before an operation can remove its invoking tree.
    from worktree_agent_state import budget, record, report
    if options.action not in ("qualify", "validate-mirror", "record-registration", "pending"):
        try:
            with budget():
                summary_source = Path(inventory(options.source)[0]["worktree"])
        except Exception:
            pass
    try:
        if options.action == "pending":
            print(json.dumps(report(options.source)), flush=True)
        elif options.action == "record-registration":
            record(options.source, options.path, created=True, branch="refs/heads/" + options.branch)
        elif options.action == "with":
            if options.argv[:1] == ["--"]:
                options.argv.pop(0)
            with_command(options)
        elif options.action == "initialize":
            from worktree_maintenance import initialization
            argv = options.argv[1:] if options.argv[:1] == ["--"] else options.argv
            with initialization(options.source, options.path):
                return subprocess.run(argv, env=git_environment()).returncode
        elif options.action == "stale":
            result = mark_stale(options.source, options.path)
            _log_result(options.action, result)
            print(json.dumps(result), flush=True)
        elif options.action == "reuse":
            result = reuse(options)
            _log_result(options.action, result)
            print(json.dumps(result), flush=True)
        elif options.action in ("return", "claim", "pool"):
            from worktree_pool import return_tree, claim, sweep
            result = (return_tree(options) if options.action == "return" else
                      claim(options) if options.action == "claim" else
                      sweep(options.source, options.dev, options.force, options.exclude_path))
            _log_result(options.action, result)
            print(json.dumps(result), flush=True)
            return 74 if result.get("status") == "failed" else 0
        elif options.action == "recover-init":
            result = reuse(options, allow_recovered_base=True)
            _log_result(options.action, result)
            print(json.dumps(result), flush=True)
        elif options.action == "qualify":
            from worktree_preservation import qualify_batch
            result = qualify_batch(options)
            print(json.dumps(result), flush=True)
            return 74 if result["status"] == "failed" else 0
        elif options.action == "remove":
            from worktree_preservation import remove
            result = remove(options)
            _log_result(options.action, result)
            print(json.dumps(result), flush=True)
            return 74 if result["status"] == "failed" else 73 if result["status"] == "refused" else 0
        elif options.action in ("prepare-mirror", "validate-mirror"):
            from worktree_publication import prepare_mirror, validate_mirror
            result = (prepare_mirror(options) if options.action == "prepare-mirror" else
                      validate_mirror(options.source, options.commit, options.base,
                                      options.merge, options.message))
            _log_result(options.action, result)
            print(json.dumps(result), flush=True)
        else:
            from worktree_publication import checkpoint, publish, finalize
            result = {"checkpoint": checkpoint, "publish": publish,
                      "finalize": finalize}[options.action](options)
            _log_result(options.action, result)
            print(json.dumps(result), flush=True)
        return 0
    except Exception as error:
        _log_operation(options.action,
                       status="refused" if isinstance(error, Refused) and not isinstance(error, GitFailure) else "failed",
                       outcome="refused" if isinstance(error, Refused) and not isinstance(error, GitFailure) else "failed",
                       reason=str(error) if isinstance(error, Refused) else "operation_failed", error=error)
        prefix = "WORKTREE_FAILED " if options.action == "claim" else "WORKTREE_RETAINED "
        print(prefix + str(error), file=sys.stderr, flush=True)
        return 73
    finally:
        if not options.no_agent_summary and options.action not in (
                "pending", "record-registration", "qualify", "validate-mirror"):
            report(summary_source)


def main(argv=None):
    global LOG
    LOG = None
    try:
        code = _main(argv)
    finally:
        if LOG is not None:
            LOG.finish(code if "code" in locals() else 1, action=LOG_ACTION,
                       operation=LOG_ACTION, status=LOG_LAST.get("status"),
                       outcome=LOG_LAST.get("outcome"), reason_code=LOG_LAST.get("reason_code"),
                       error_type=LOG_LAST.get("error_type"))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
