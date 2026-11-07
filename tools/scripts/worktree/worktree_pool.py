"""Age/stale worktree allocation and release."""
from pathlib import Path
import subprocess
import time
from types import SimpleNamespace

from worktree_protocol import (GitFailure, Refused, clear_matching_stale, git, git_environment,
                               head_committer_time, head_oid, identity, inventory,
                               mark_stale, reuse, stale_head, value)
from worktree_preservation import remove_registered

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
    remove_registered(main, path)


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


def claim(options):
    rows = inventory(options.source)
    main = _main_path(rows)
    # The requested source may itself expire or be reassigned. Shared refs and
    # later native operations stay anchored to the protected main checkout.
    options = SimpleNamespace(**(vars(options) | {"source": main}))
    if options.path is not None and (options.path.exists() or options.path.is_symlink()):
        identity(options.source, options.path)
        if _same(options.path, main):
            raise Refused("main_worktree")
    base = value(options.source, "rev-parse", "--verify", options.base + "^{commit}")
    expected = _expected_pins(options.source, base)
    excluded = {Path(path).resolve() for path in getattr(options, "exclude_path", [])}
    now = time.time()
    refusals, candidates, removed, expiry_failures = [], [], [], []
    # Complete expiry for the whole inventory before returning any selection,
    # including a same-task continuation or an explicit destination.
    for item in rows[1:]:
        path = Path(item["worktree"]).absolute()
        if path.resolve() in excluded or _same(path, main):
            continue
        expired = False
        try:
            current, _ = identity(options.source, path)
            age = _age(path, now)
            head = head_oid(path)
            expired = age > SIX_HOURS
            if expired:
                _remove_registered(options.source, path)
                removed.append(str(path))
            candidates.append((path, _branch(current), head, age, expired))
        except (Refused, OSError, subprocess.SubprocessError) as error:
            refusals.append(dict(path=str(path), reason=str(error)))
            if expired:
                expiry_failures.append(dict(path=str(path), reason=str(error)))
            elif options.path is not None and _same(path, options.path):
                raise (GitFailure if isinstance(error, GitFailure) else Refused)(
                    str(error) + "; expired_worktrees_removed=" + repr(removed)) from error

    def finish(result):
        return result | {"removed_worktrees": removed, "candidate_refusals": refusals}

    try:
        if expiry_failures:
            raise GitFailure("expired_cleanup_failed:" + repr(expiry_failures))
        if options.path is not None:
            candidates = [row for row in candidates if _same(row[0], options.path)]
        # An unexpired attached task resumes regardless of allocation age.
        # Base/pin/source compatibility is still checked by native recovery.
        for path, branch, head, age, expired in candidates:
            if not expired and branch == "refs/heads/" + options.branch:
                result = reuse(SimpleNamespace(**(vars(options) | {"path": path})))
                clear_matching_stale(options.source, branch, head)
                return finish(result)
        for path, branch, head, age, expired in candidates:
            try:
                marked = not expired and branch != "HEAD" and stale_head(options.source, branch) == head
                if not expired:
                    if branch == "HEAD":
                        raise Refused("detached_head")
                    if not marked and age <= FOUR_HOURS:
                        raise Refused("head_recent")
                    _check_pins(path, expected)
            except (Refused, OSError, subprocess.SubprocessError) as error:
                refusals.append(dict(path=str(path), branch=branch, reason=str(error)))
                if options.path is not None:
                    raise
                continue
            return finish(_allocate(options.source, path, options, base, expected, removed=expired) | {
                "previous_branch": branch.removeprefix("refs/heads/"),
                "previous_head": head,
                "reuse_reason": "head_older_than_6h_removed" if expired else
                                "stale" if marked else "head_older_than_4h",
            })
        result = dict(event="worktree_init", status="no_reusable")
        if refusals:
            result["candidate_refusals"] = refusals
        return finish(result)
    except (Refused, OSError, subprocess.SubprocessError) as error:
        if removed:
            raise (GitFailure if isinstance(error, GitFailure) else Refused)(
                str(error) + "; expired_worktrees_removed=" + repr(removed)) from error
        raise


def return_tree(options):
    # Release is a single native marker write. It deliberately has no PR,
    # remote, merge, join, clean-tree, or branch-switch prerequisite.
    return mark_stale(options.source, options.path)


def sweep(source, dev, force=False, exclude_paths=()):
    del dev
    rows = inventory(source)
    main = _main_path(rows)
    source = main
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
