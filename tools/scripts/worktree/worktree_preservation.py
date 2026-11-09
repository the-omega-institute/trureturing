"""Native worktree identity and forced removal.

Removal intentionally performs no snapshot, participation, activity, or lock
inspection. AI users own their committed branch history; Git preserves the
branch ref when a registered linked tree is removed.
"""
from pathlib import Path
import os
import subprocess
import time

from worktree_protocol import GitFailure, Refused, common, git, git_environment, identity, inventory


def finished_operations(metadata):
    # Kept as an inspection helper for callers that need to report unfinished
    # work. Removal itself does not use it as a veto.
    return [marker for marker in ("MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD",
                                  "rebase-merge", "rebase-apply", "sequencer")
            if (Path(metadata) / marker).exists()]


def qualify(source, path, stack=None, snapshot=None, deadline=None):
    del stack, deadline
    path = Path(path).absolute()
    if path.is_symlink() or (os.path.lexists(path) and not path.is_dir()):
        raise Refused("missing_or_linked_tree")
    path = path.resolve()
    rows = snapshot[0] if snapshot is not None else inventory(source)
    if not rows or path == Path(rows[0]["worktree"]).resolve():
        raise Refused("main_worktree")
    if any(path in Path(row["worktree"]).resolve().parents for row in rows):
        raise Refused("nested_worktree")
    if os.path.lexists(path / ".git"):
        item, _ = identity(source, path, snapshot=snapshot)
        return item
    return _missing_pointer_identity(source, path, rows, snapshot)[0]


def _missing_pointer_identity(source, path, rows, snapshot=None):
    # Cleanup alone can recover an absent checkout root or pointer. Require the native
    # administration entry's backlink, common directory and HEAD to agree;
    # ordinary reuse/with identity continues to require the checkout pointer.
    if all(os.path.lexists(path / name) for name in ("HEAD", "objects", "refs")):
        raise Refused("foreign_repository")
    matches = [row for row in rows if Path(row["worktree"]).resolve() == path]
    if len(matches) != 1:
        raise Refused("repository_identity")
    if path.is_dir() and path.stat().st_dev != path.parent.stat().st_dev:
        raise Refused("repository_identity")
    shared = snapshot[1] if snapshot is not None else common(source)
    administration = shared / "worktrees"
    entries = []
    for metadata in administration.iterdir():
        if metadata.is_symlink() or not metadata.is_dir():
            continue
        backlink = metadata / "gitdir"
        if backlink.is_symlink() or not backlink.is_file():
            continue
        if Path(backlink.read_text().rstrip("\n")) == path / ".git":
            entries.append(metadata)
    if len(entries) != 1:
        raise Refused("git_backlink")
    metadata = entries[0]
    if administration.resolve() != administration or metadata.resolve() != metadata:
        raise Refused("repository_identity")
    for name in ("commondir", "HEAD"):
        if (metadata / name).is_symlink() or not (metadata / name).is_file():
            raise Refused("repository_identity")
    if (metadata / (metadata / "commondir").read_text().strip()).resolve() != shared:
        raise Refused("repository_identity")
    head = git(source, "--git-dir=" + str(metadata), "rev-parse", "--verify", "HEAD^{commit}").stdout.strip()
    if os.fsdecode(head) != matches[0].get("HEAD"):
        raise Refused("registration_changed")
    return matches[0], metadata


def registered_committer_time(source, item):
    """Read the qualified registration's commit even when its pointer is absent."""
    raw = git(source, "show", "-s", "--format=%ct", item["HEAD"]).stdout.strip()
    try:
        return int(raw)
    except ValueError as error:
        raise Refused("head_timestamp_unknown") from error


def _removal_state(source, path):
    # Observe partial effects; never repair or delete an unregistered remnant.
    try:
        registered = any(Path(row["worktree"]).resolve() == path for row in inventory(source))
    except (Refused, OSError, subprocess.SubprocessError):
        registered = "unknown"
    return f"root={os.path.lexists(path)}, pointer={os.path.lexists(path / '.git')}, registered={registered}"


def remove_registered(source, path, timeout=1800):
    """Remove qualified payload first, then let Git remove its pointer/registration.

    Payload and final native removal share the caller's bound. None disables
    that bound for explicit FORCE and the unbounded allocation/sweep entrances.
    Payload failure leaves the root .git file available to ordinary retry; a
    final Git failure can have partial native effects, which are only observed.
    """
    path = Path(path).absolute()
    rows = inventory(source)
    item = qualify(source, path)
    path = path.resolve()
    source = Path(rows[0]["worktree"]).resolve()
    deadline = time.monotonic() + timeout if timeout is not None else None
    phase = "pointer-recovery"

    def remaining():
        if deadline is None:
            return None
        seconds = deadline - time.monotonic()
        if seconds <= 0:
            raise subprocess.TimeoutExpired("worktree removal " + phase, timeout)
        return seconds

    try:
        # An absent root has no payload or pointer to repair. Native Git can
        # remove its qualified registration directly, including a locked one.
        if os.path.lexists(path):
            qualify(source, path)
            if not os.path.lexists(path / ".git"):
                # Git validates a present root's pointer even with double force.
                # Recreate only this proven missing pointer, without overwriting
                # any entry or repairing/pruning other registrations.
                current_rows = inventory(source)
                _, metadata = _missing_pointer_identity(source, path, current_rows)
                with (path / ".git").open("x") as pointer:
                    pointer.write("gitdir: " + str(metadata) + "\n")
                identity(source, path)
            phase = "payload"
            # Bound argv even for a flat checkout. rm's physical traversal unlinks
            # symlinks, including .lake, without following their external targets.
            with os.scandir(path) as entries:
                arguments = ["./" + entry.name for entry in entries if entry.name != ".git"]
            batch, size = [], 0
            for argument in arguments:
                length = len(os.fsencode(argument)) + 1
                if batch and size + length > 32768:
                    _remove_payload(path, batch, remaining())
                    batch, size = [], 0
                batch.append(argument)
                size += length
            if batch:
                _remove_payload(path, batch, remaining())
            if any(entry.name != ".git" for entry in path.iterdir()):
                raise GitFailure("payload remains")
        phase = "final-native"
        qualify(source, path)
        result = git(source, "worktree", "remove", "--force", "--force", "--", str(path),
                     check=False, timeout=remaining())
        if result.returncode:
            raise subprocess.CalledProcessError(result.returncode, result.args,
                                                output=result.stdout, stderr=result.stderr)
        if os.path.lexists(path) or any(Path(row["worktree"]).resolve() == path
                                       for row in inventory(source)):
            raise GitFailure("native success left worktree material")
    except (OSError, subprocess.SubprocessError, GitFailure, KeyboardInterrupt) as error:
        diagnostic = getattr(error, "stderr", None) or b""
        if isinstance(diagnostic, bytes):
            diagnostic = diagnostic.decode(errors="replace")
        raise GitFailure(f"removal_{phase}_failed:{type(error).__name__}:"
                         f"exit={getattr(error, 'returncode', None)}, "
                         f"timeout={getattr(error, 'timeout', None)}; path={str(path)!r}; {str(error)[-4096:]}; "
                         f"stderr={diagnostic[-4096:]!r}; {_removal_state(source, path)}") from error
    return item


def _remove_payload(path, arguments, timeout):
    subprocess.run(["/bin/rm", "-rf", "--", *arguments], cwd=path,
                   env=git_environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                   timeout=timeout, check=True)


def qualify_batch(options, emit=None, emit_started=None):
    outcomes = []
    for path in list(dict.fromkeys(options.path)):
        try:
            if emit_started:
                emit_started(path)
            qualify(options.source, path)
            row = dict(path=str(path), outcome="qualified", reason=None)
        except Refused as error:
            row = dict(path=str(path), outcome="refused", reason=str(error))
        except Exception as error:
            row = dict(path=str(path), outcome="failed", reason=str(error))
        outcomes.append(row)
        if emit:
            emit(row)
    return dict(event="worktree_qualification", items=outcomes,
                status="failed" if any(row["outcome"] == "failed" for row in outcomes)
                else "succeeded")


def _resolve_targets(options, rows):
    names = list(dict.fromkeys(options.names.split()))
    if not names and not options.path:
        raise Refused("names_or_paths_required")
    targets = []
    for name in names:
        matches = [row for row in rows if Path(row["worktree"]).name == name]
        if len(matches) != 1:
            raise Refused("name_not_found_or_ambiguous:" + name)
        targets.append(Path(matches[0]["worktree"]))
    for path in options.path:
        path = Path(path)
        matches = [row for row in rows if Path(row["worktree"]).resolve() == path.resolve()]
        if len(matches) != 1:
            raise Refused("path_not_registered:" + str(path))
        targets.append(Path(matches[0]["worktree"]))
    return list(dict.fromkeys(targets))


def remove(options):
    rows = inventory(options.source)
    targets = _resolve_targets(options, rows)
    main = Path(rows[0]["worktree"]).resolve()
    outcomes = []
    for target in targets:
        try:
            if target.resolve() == main:
                raise Refused("main_worktree")
            item = qualify(main, target)
            if options.preview:
                outcomes.append(dict(path=str(target), outcome="would_remove",
                                     branch=item.get("branch"), head=item.get("HEAD")))
                continue
            remove_registered(main, target, timeout=None if getattr(options, "force", False) else 1800)
            outcomes.append(dict(path=str(target), outcome="removed",
                                 branch=item.get("branch"), head=item.get("HEAD")))
        except Refused as error:
            outcomes.append(dict(path=str(target),
                                 outcome="failed" if isinstance(error, GitFailure) else "refused",
                                 reason=str(error)))
        except Exception as error:
            outcomes.append(dict(path=str(target), outcome="failed", reason=str(error)))
    status = ("failed" if any(row["outcome"] == "failed" for row in outcomes)
              else "refused" if any(row["outcome"] == "refused" for row in outcomes)
              else "succeeded")
    return dict(event="worktree_removal", items=outcomes, status=status)
