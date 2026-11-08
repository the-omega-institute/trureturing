"""Advisory, clone-local attribution for the current native registration."""
from contextlib import contextmanager
try:
    import fcntl
except ImportError:
    fcntl = None
import json
import os
from pathlib import Path
import re
import shlex
import sys
import time
import uuid

import worktree_protocol as native

STATE = "agent-state.json"
BUDGET_SECONDS = 4
MAX_BYTES = 16384
TOKEN = r"[A-Za-z0-9][A-Za-z0-9_.-]{0,159}"
AGENT = re.compile(r"[a-z][a-z0-9-]{0,31}:" + TOKEN + r"\Z")


def caller(environ=None):
    env = os.environ if environ is None else environ
    for key, namespace in (("WORKTREE_AGENT_ID", None), ("CODEX_THREAD_ID", "codex"),
                           ("CODEX_SESSION_ID", "codex"), ("CLAUDE_CODE_SESSION_ID", "claude")):
        if key in env:
            value = env[key] if namespace is None else namespace + ":" + env[key]
            return (value, None) if AGENT.fullmatch(value) else (None, "malformed:" + key)
    return None, "identity_absent"


@contextmanager
def budget():
    token = native.AUXILIARY_DEADLINE.set(time.monotonic() + BUDGET_SECONDS)
    try:
        yield
    finally:
        native.AUXILIARY_DEADLINE.reset(token)


def warning(error):
    print("WORKTREE_AGENT_WARNING " + json.dumps(str(error)[:512]), file=sys.stderr, flush=True)


def _stamp(stat):
    return [stat.st_dev, stat.st_ino]


@contextmanager
def registration(source, path, snapshot=None):
    if fcntl is None:
        raise ValueError("agent_metadata_coordination_unavailable")
    item, admin = native.identity(source, path, snapshot=snapshot)
    if admin == native.common(source):
        raise ValueError("main_worktree_has_no_agent_record")
    # An open directory pins the native registration even if Git removes and
    # recreates its pathname. All publication uses this descriptor, never mkdir.
    fd = os.open(admin, os.O_RDONLY | os.O_DIRECTORY)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        stamp = _stamp(os.fstat(fd))

        def verify():
            current, current_admin = native.identity(source, path)
            if current_admin != admin or _stamp(os.stat(admin)) != stamp:
                raise ValueError("registration_changed")
            return current

        verify()
        yield fd, stamp, item, verify
    finally:
        os.close(fd)


def _valid_agent(value):
    return value is None or isinstance(value, str) and AGENT.fullmatch(value) is not None


def read(fd, stamp):
    try:
        state_fd = os.open(STATE, os.O_RDONLY | os.O_NONBLOCK, dir_fd=fd)
    except FileNotFoundError:
        return None
    with os.fdopen(state_fd, "rb") as stream:
        raw = stream.read(MAX_BYTES + 1)
    if len(raw) > MAX_BYTES:
        raise ValueError("agent_state_too_large")
    state = json.loads(raw)
    if (not isinstance(state, dict) or set(state) != {"version", "registration", "creator", "allocation"}
            or state["version"] != 1 or state["registration"] != stamp
            or not _valid_agent(state["creator"])):
        raise ValueError("malformed_agent_state")
    allocation = state["allocation"]
    if allocation is not None and (not isinstance(allocation, dict)
            or set(allocation) != {"agent", "branch"} or not _valid_agent(allocation["agent"])
            or not isinstance(allocation["branch"], str)
            or not allocation["branch"].startswith("refs/heads/")):
        raise ValueError("malformed_agent_allocation")
    return state


def publish(fd, state, verify, branch=None):
    # This UUID names only an atomic-publication temporary, never an agent.
    temporary = ".agent-state-" + uuid.uuid4().hex
    try:
        file_fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600, dir_fd=fd)
        with os.fdopen(file_fd, "w") as stream:
            json.dump(state, stream, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        current = verify()
        if branch is not None and current.get("branch") != branch:
            raise ValueError("allocation_branch_changed")
        os.replace(temporary, STATE, src_dir_fd=fd, dst_dir_fd=fd)
    finally:
        try:
            os.unlink(temporary, dir_fd=fd)
        except FileNotFoundError:
            pass


def record(source, path, *, created=False, branch=None):
    """Capture immediately after add, or claim after successful explicit setup."""
    try:
        with budget(), registration(source, path) as (fd, stamp, item, verify):
            actual = item.get("branch")
            if not actual or branch is not None and actual != branch:
                raise ValueError("allocation_branch_mismatch")
            agent, reason = caller()
            if reason:
                warning(reason)
            state = read(fd, stamp)
            if state is None:
                state = dict(version=1, registration=stamp,
                             creator=agent if created else None, allocation=None)
            # Unknown callers cannot erase a known allocation for this branch.
            if agent is not None or state["allocation"] is None or state["allocation"]["branch"] != actual:
                state["allocation"] = dict(agent=agent, branch=actual)
            publish(fd, state, verify, actual)
    except Exception as error:
        warning(error)


def _observe(source, path, snapshot):
    with registration(source, path, snapshot) as (fd, stamp, item, verify):
        state = read(fd, stamp)
        branch = native.branch_name(path)
        if state and state["allocation"] and state["allocation"]["branch"] != branch:
            state["allocation"] = None
            publish(fd, state, verify, branch)
        row = dict(path=str(path), branch=branch, creator=state["creator"] if state else None,
                   allocation=state["allocation"] if state else None,
                   metadata="known" if state else "missing", status="unavailable", reason="native_read_failed")
        try:
            head = native.head_oid(path)
            marker = native.stale_head(source, branch) if branch else None
            if verify().get("branch") != branch or native.head_oid(path) != head:
                raise ValueError("native_state_changed")
            row.update(head=head, status="released" if branch and marker == head else "pending",
                       reason="matching_stale_head" if branch and marker == head else
                              "detached_head" if not branch else
                              "stale_head_mismatch" if marker else "no_stale_marker")
        except Exception as error:
            row["reason"] = str(error)[:256]
        return row


def summary(source):
    """One bounded, filtered view; incomplete data never establishes zero pending."""
    agent, reason = caller()
    result = dict(event="worktree_agent_pending", agent=agent, identity_reason=reason,
                  complete=agent is not None, pending=[], unknown=[])
    if agent is not None:
        try:
            with budget():
                rows = native.inventory(source)
                source = Path(rows[0]["worktree"]).resolve()
                snapshot = (rows, native.common(source))
                for item in rows[1:]:
                    path = Path(item["worktree"]).resolve()
                    try:
                        row = _observe(source, path, snapshot)
                        allocation = row["allocation"]
                        matches = (["creator"] if row["creator"] == agent else []) + (
                            ["allocation"] if allocation and allocation["agent"] == agent
                            and allocation["branch"] == row["branch"] else [])
                        if matches and row["status"] != "released":
                            result["pending"].append(row | {"matched_by": matches})
                        if row["creator"] is None or row["status"] == "unavailable":
                            result["unknown"].append(dict(path=str(path), reason="creator_unknown" if
                                row["creator"] is None else row["reason"]))
                    except Exception as error:
                        result["unknown"].append(dict(path=str(path), reason=str(error)[:256]))
        except Exception as error:
            result["unknown"].append(dict(reason=str(error)[:256]))
    result["complete"] &= not result["unknown"]
    print("WORKTREE_AGENT_PENDING " + json.dumps({key: value for key, value in result.items()
          if key not in ("pending", "unknown")} | {"pending": len(result["pending"]),
          "unknown": result["unknown"]}), file=sys.stderr, flush=True)
    for row in result["pending"]:
        print("WORKTREE_AGENT_TREE " + json.dumps(row), file=sys.stderr, flush=True)
        path = shlex.quote(row["path"])
        print("  maintain: cd " + path + "; make worktree-checkpoint MESSAGE=FILE; "
              "release: make worktree-stale WORKTREE_PATH=" + path + "; "
              "remove: make worktree-remove NAMES=" + shlex.quote(Path(row["path"]).name),
              file=sys.stderr, flush=True)
    return result


def report(source):
    try:
        return summary(source)
    except Exception as error:
        warning("pending_unavailable:" + str(error))
        return dict(event="worktree_agent_pending", complete=False, agent=None, pending=[],
                    unknown=[dict(reason="pending_unavailable")])
