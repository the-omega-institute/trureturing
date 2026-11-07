"""Native worktree identity and forced removal.

Removal intentionally performs no snapshot, participation, activity, or lock
inspection. AI users own their committed branch history; Git preserves the
branch ref when a registered linked tree is removed.
"""
from pathlib import Path

from worktree_protocol import Refused, git, identity, inventory


def finished_operations(metadata):
    # Kept as an inspection helper for callers that need to report unfinished
    # work. Removal itself does not use it as a veto.
    return [marker for marker in ("MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD",
                                  "rebase-merge", "rebase-apply", "sequencer")
            if (Path(metadata) / marker).exists()]


def qualify(source, path, stack=None, snapshot=None, deadline=None):
    del stack, deadline
    path = Path(path).resolve()
    rows = snapshot[0] if snapshot is not None else inventory(source)
    if path.is_symlink() or not path.is_dir():
        raise Refused("missing_or_linked_tree")
    if not rows or path == Path(rows[0]["worktree"]).resolve():
        raise Refused("main_worktree")
    if any(path in Path(row["worktree"]).resolve().parents for row in rows):
        raise Refused("nested_worktree")
    item, metadata = identity(source, path, snapshot=snapshot)
    return item


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
            item = qualify(options.source, target)
            if options.preview:
                outcomes.append(dict(path=str(target), outcome="would_remove",
                                     branch=item.get("branch"), head=item.get("HEAD")))
                continue
            # Native forced removal is intentionally immediate. It may discard
            # dirty or unfinished checkout bytes but never deletes the branch ref.
            git(options.source, "worktree", "remove", "--force", "--force", "--", str(target))
            outcomes.append(dict(path=str(target), outcome="removed",
                                 branch=item.get("branch"), head=item.get("HEAD")))
        except Refused as error:
            outcomes.append(dict(path=str(target), outcome="refused", reason=str(error)))
        except Exception as error:
            outcomes.append(dict(path=str(target), outcome="failed", reason=str(error)))
    status = ("failed" if any(row["outcome"] == "failed" for row in outcomes)
              else "refused" if any(row["outcome"] == "refused" for row in outcomes)
              else "succeeded")
    return dict(event="worktree_removal", items=outcomes, status=status)
