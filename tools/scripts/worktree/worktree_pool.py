"""Age/stale worktree allocation and release."""
import os
from pathlib import Path
import subprocess
import time

from worktree_protocol import (Refused, clear_matching_stale, git, git_environment,
                               head_committer_time, head_oid, identity, inventory,
                               mark_stale, stale_head, value)

FOUR_HOURS = 4 * 60 * 60
SIX_HOURS = 6 * 60 * 60
PINS = ("lean-toolchain", "lake-manifest.json")


def _main_path(rows):
    if not rows:
        raise Refused("worktree_inventory_empty")
    return Path(rows[0]["worktree"]).resolve()


def _same(path, other):
    return Path(path).resolve() == Path(other).resolve()


def _age(path, now=None):
    return (time.time() if now is None else now) - head_committer_time(path)


def _branch(item):
    return item.get("branch") or "HEAD"


def _expected_pins(source, base):
    return {pin: git(source, "show", base + ":" + pin).stdout for pin in PINS}


def _check_pins(path, expected):
    for pin, content in expected.items():
        target = Path(path) / pin
        if not target.is_file() or target.read_bytes() != content:
            raise Refused("incompatible_pin:" + pin)


def _remove_registered(source, path):
    rows = inventory(source)
    main = _main_path(rows)
    if _same(path, main):
        raise Refused("main_worktree")
    if not any(_same(path, row["worktree"]) for row in rows):
        raise Refused("path_not_registered")
    # Two native force flags make legacy Git lock markers irrelevant to the
    # lifecycle policy without adding an application lock or unlock stage.
    git(source, "worktree", "remove", "--force", "--force", "--", str(path))


def _make_scaffold(path):
    scaffold = Path(path) / ".gitignore"
    content = scaffold.read_text() if scaffold.exists() else ""
    missing = [pattern for pattern in (".caller-review-prompt.md", ".echo-review.md", ".sshx-*")
               if pattern not in content.splitlines()]
    if missing:
        with scaffold.open("a") as output:
            output.write(("\n" if content and not content.endswith("\n") else "")
                         + "\n".join(missing) + "\n")


def _allocate(source, path, options, base, expected, removed=False):
    branch = options.branch
    reference = "refs/heads/" + branch
    if git(source, "show-ref", "--verify", "--quiet", reference, check=False).returncode == 0:
        raise Refused("branch_already_exists:" + branch)
    git(source, "check-ref-format", "--branch", branch)
    if not removed:
        _remove_registered(source, path)
    git(source, "branch", "--", branch, base)
    try:
        git(source, "worktree", "add", "--no-checkout", "--", str(path), branch)
        git(path, "reset", "--hard", "--no-recurse-submodules", "HEAD", timeout=1200)
        _check_pins(path, expected)
        clear_matching_stale(source, branch, head_oid(path))
        _make_scaffold(path)
        if not options.skip_restore:
            result = subprocess.run(["dotnet", "restore", "tools/StrataLint.sln", "--locked-mode"],
                                    cwd=path, env=git_environment(), stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, timeout=1800, check=False)
            if result.returncode:
                raise Refused("claim_restore_failed:" + result.stderr.decode(errors="replace"))
    except Exception:
        # Keep the new branch ref and any registered tree for native recovery.
        raise
    return dict(event="worktree_init", status="claimed", path=str(Path(path).resolve()),
                branch=branch, base_revision=base,
                dotnet_restore="skipped" if options.skip_restore else "restored")


def _candidate_rows(source, requested):
    rows = inventory(source)
    main = _main_path(rows)
    if requested is not None:
        target = Path(requested).resolve()
        matches = [row for row in rows if _same(row["worktree"], target)]
        if not matches:
            return rows, main, []
        return rows, main, [matches[0]]
    return rows, main, [row for row in rows if not _same(row["worktree"], main)]


def claim(options):
    rows, main, candidates = _candidate_rows(options.source, options.path)
    base = value(options.source, "rev-parse", "--verify", options.base + "^{commit}")
    expected = _expected_pins(options.source, base)
    excluded = {Path(path).resolve() for path in getattr(options, "exclude_path", [])}
    now = time.time()
    refusals = []
    for item in candidates:
        path = Path(item["worktree"]).resolve()
        if path in excluded or _same(path, main):
            continue
        if path.is_symlink():
            refusals.append(dict(path=str(path), reason="linked_tree"))
            continue
        try:
            current, _ = identity(options.source, path)
            branch = _branch(current)
            head = head_oid(path)
            age = _age(path, now)
            marked = branch != "HEAD" and stale_head(options.source, branch) == head
            # Strict threshold: exactly six hours is retained. A future or
            # unknown timestamp is never treated as old.
            if age > SIX_HOURS:
                _remove_registered(options.source, path)
                # Removal is first in the allocation pass. The just-freed
                # directory is immediately eligible for the requested task.
                return _allocate(options.source, path, options, base, expected, removed=True) | {
                    "previous_branch": branch.removeprefix("refs/heads/"),
                    "previous_head": head,
                    "reuse_reason": "head_older_than_6h_removed",
                }
            if branch == "HEAD":
                raise Refused("detached_head")
            if not marked and age <= FOUR_HOURS:
                raise Refused("head_recent")
            _check_pins(path, expected)
            if branch == "refs/heads/" + options.branch:
                clear_matching_stale(options.source, branch, head)
                return dict(event="worktree_init", status="reused", path=str(path),
                            branch=options.branch, base_revision=base,
                            reuse_reason="stale" if marked else "head_older_than_4h")
            return _allocate(options.source, path, options, base, expected) | {
                "previous_branch": branch.removeprefix("refs/heads/"),
                "previous_head": head,
                "reuse_reason": "stale" if marked else "head_older_than_4h",
            }
        except (Refused, OSError, subprocess.SubprocessError) as error:
            refusals.append(dict(path=str(path), branch=branch if "branch" in locals() else None,
                                 reason=str(error)))
            if options.path is not None:
                raise
    result = dict(event="worktree_init", status="no_reusable")
    if refusals:
        result["candidate_refusals"] = refusals
    return result


def return_tree(options):
    # Release is a single native marker write. It deliberately has no PR,
    # remote, merge, join, clean-tree, or branch-switch prerequisite.
    return mark_stale(options.source, options.path)


def sweep(source, dev, force=False, exclude_paths=()):
    del dev
    rows = inventory(source)
    main = _main_path(rows)
    excluded = {Path(path).resolve() for path in exclude_paths}
    items = []
    status = "succeeded"
    now = time.time()
    for item in rows[1:]:
        path = Path(item["worktree"]).resolve()
        if path in excluded or _same(path, main):
            continue
        try:
            age = _age(path, now)
            if age > SIX_HOURS:
                if force:
                    _remove_registered(source, path)
                    items.append(dict(path=str(path), outcome="removed", reason="head_older_than_6h"))
                else:
                    items.append(dict(path=str(path), outcome="would_remove", reason="head_older_than_6h"))
            else:
                items.append(dict(path=str(path), outcome="retained", reason="head_not_older_than_6h"))
        except Exception as error:
            status = "failed"
            items.append(dict(path=str(path), outcome="failed", reason=str(error)))
    return dict(event="worktree_pool", status=status, items=items,
                thresholds=dict(reuse_seconds=FOUR_HOURS, remove_seconds=SIX_HOURS))
