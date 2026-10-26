"""Ordinary checkpoints and non-force publication, using native Git objects."""

from contextlib import ExitStack
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import uuid

from worktree_protocol import (Refused, GitFailure, git, value, identity, tree_scope,
                               git_scope, acquire, remote_endpoint, read_input,
                               exclusive_tree, native_lock_candidates, clear_native_locks,
                               common, inventory, reuse, scope_fds, git_environment)


def creation_witness(source, reference):
    log = common(source) / "logs" / reference
    if log.is_symlink() or not log.is_file():
        raise Refused("initialization_creation_witness_missing")
    lines = log.read_bytes().splitlines()
    if not lines:
        raise Refused("initialization_creation_witness_missing")
    first = lines[0].split(b"\t", 1)
    fields = first[0].split()
    if (len(first) != 2 or len(fields) < 2 or set(fields[0]) != {ord("0")}
            or len(fields[0]) != len(fields[1])
            or not re.fullmatch(rb"[0-9a-f]{40}|[0-9a-f]{64}", fields[1])):
        raise Refused("initialization_creation_witness_invalid")
    token = first[1].decode("ascii")
    creation = fields[1].decode("ascii")
    if not re.fullmatch(r"worktree-init:[0-9a-f]{32}", token):
        raise Refused("branch already exists: initialization_creation_witness_invalid")
    if value(source, "rev-parse", "--verify", reference + "^{commit}") != creation:
        raise Refused("initialization_branch_identity_changed")
    if git(source, "symbolic-ref", "--quiet", reference, check=False).returncode == 0:
        raise Refused("initialization_branch_identity_changed")
    return token, creation


def recovery_root(stack, source, path, commit):
    reference = "refs/heads/lane/governance/recovery-" + uuid.uuid4().hex
    acquire(stack, source, "ref:" + reference, True)
    stack.recovery_roots = getattr(stack, "recovery_roots", []) + [reference]
    git(path, "update-ref", "--no-deref", "--create-reflog", reference, commit, "0" * len(commit))
    if value(path, "rev-parse", "--verify", reference + "^{commit}") != commit:
        raise Refused("recovery_root_changed:" + reference)
    return reference


def recover_initialization(options):
    """Resume an owned initializer, preserving extant ordinary bytes before checkout."""
    reference = "refs/heads/" + options.branch
    if options.path.is_symlink():
        raise Refused("linked_tree")
    rows = [row for row in inventory(options.source)
            if Path(row["worktree"]).resolve() == options.path.resolve()]
    if rows and "locked" not in rows[0]:
        return reuse(options, allow_recovered_base=True)
    with ExitStack() as stack:
        try:
            path = tree_scope(stack, options.source, options.path, True)
        except Refused as error:
            raise Refused("initialization_in_progress") from error
        acquire(stack, options.source, "ref:" + reference, True)
        rows = [row for row in inventory(options.source) if Path(row["worktree"]).resolve() == path]
        if not rows and path.exists():
            identity(options.source, path)
        if rows and not rows[0].get("locked", "").startswith("worktree-init:"):
            if "locked" in rows[0]:
                raise Refused("intentional_worktree_lock")
            # Ordinary reuse uses its own shared entry and index/ref scopes.
            stack.close()
            return reuse(options, allow_recovered_base=True)
        token, creation = creation_witness(options.source, reference)
        expected = getattr(options, "expected_token", None)
        if expected and expected != token:
            raise Refused("initialization_token_changed")
        if not rows:
            if path.exists() or path.is_symlink() or any(row.get("branch") == reference
                                                       for row in inventory(options.source)):
                raise Refused("initialization_path_identity_changed")
            for row in inventory(options.source):
                if row.get("locked", "").startswith("worktree-init:") and (
                        row["locked"] == token or not row.get("HEAD") or set(row["HEAD"]) == {"0"}):
                    raise Refused("initialization_registration_unverifiable")
            git(options.source, "worktree", "add", "--no-checkout", "--lock", "--reason", token,
                path, options.branch)
            rows = [row for row in inventory(options.source) if Path(row["worktree"]).resolve() == path]
        if len(rows) != 1 or rows[0].get("locked") != token or path.is_symlink():
            raise Refused("initialization_token_or_path_changed")
        pointer = path / ".git"
        if pointer.is_symlink() or not pointer.is_file():
            raise Refused("initialization_git_pointer")
        text = pointer.read_text().strip()
        if not text.startswith("gitdir: ") or "\n" in text:
            raise Refused("initialization_git_pointer")
        raw_metadata = path / text[8:]
        metadata = raw_metadata.resolve()
        if (metadata.parent != common(options.source) / "worktrees" or raw_metadata.is_symlink()
                or metadata.parent.is_symlink()
                or Path((metadata / "gitdir").read_text().strip()).resolve() != pointer.resolve()
                or (metadata / (metadata / "commondir").read_text().strip()).resolve() != common(options.source)):
            raise Refused("initialization_metadata_identity_changed")
        if not (metadata / "HEAD").exists():
            acquire(stack, options.source, "ref:" + str(metadata) + ":HEAD", True)
            git(options.source, "update-ref", "--no-deref", "worktrees/" + metadata.name + "/HEAD",
                creation, "0" * len(creation))
        else:
            if rows[0].get("branch") != reference and (
                    rows[0].get("branch") or rows[0].get("HEAD") != creation):
                raise Refused("initialization_branch_identity_changed")
            acquire(stack, options.source, "ref:" + str(metadata) + ":HEAD", True)
        if rows[0].get("branch") != reference:
            git(path, "symbolic-ref", "-m", token, "HEAD", reference)
        item, verified = identity(options.source, path)
        if verified != metadata or item.get("branch") != reference:
            raise Refused("initialization_registration_changed")
        acquire(stack, options.source, "index:" + str(metadata), True)
        # A temporary native index snapshots partial checkout bytes without moving
        # the creation branch, so the creation witness survives an interrupted retry.
        alternate = metadata / ("initialization-index-" + uuid.uuid4().hex)
        recovery = None
        try:
            env = {"GIT_INDEX_FILE": str(alternate)}
            git(path, "read-tree", creation, env=env)
            git(path, "add", "--ignore-removal", "--", ".", env=env, timeout=1200)
            tree = value_from(git(path, "write-tree", env=env))
            if tree != value(path, "rev-parse", creation + "^{tree}"):
                commit = value_from(git(path, "commit-tree", tree, "-p", creation,
                                       input=b"Preserve interrupted initialization snapshot\n"))
                recovery = recovery_root(stack, options.source, path, commit)
        finally:
            alternate.unlink(missing_ok=True)
        cleared = []
        try:
            git(path, "read-tree", creation)
        except GitFailure as error:
            locks = native_lock_candidates(path, metadata, reference, error)
            if not locks:
                raise
            cleared = clear_native_locks(options.source, path, locks)
            git(path, "read-tree", creation)
        missing = [name for name in git(path, "ls-files", "-z").stdout.split(b"\0")
                   if name and not os.path.lexists(path / os.fsdecode(name))]
        if missing:
            git(path, "checkout-index", "-z", "--stdin", input=b"\0".join(missing) + b"\0",
                timeout=1200)
        # read-tree leaves existing files without cached stat data. Refresh it
        # without staging preserved edits; exit 1 is normal for dirty files.
        refreshed = git(path, "update-index", "--refresh", check=False, timeout=1200)
        if refreshed.returncode not in (0, 1):
            raise GitFailure(refreshed.stderr.decode(errors="replace").strip()
                             or "initialization index refresh failed")
        git(path, "hook", "run", "--ignore-missing", "post-checkout", "--",
            "0" * len(creation), creation, "1")
        if not options.skip_restore:
            with subprocess.Popen(["dotnet", "restore", "tools/StrataLint.sln", "--locked-mode"],
                                  cwd=path, env=git_environment(), pass_fds=scope_fds()) as process:
                try:
                    code = process.wait(timeout=1800)
                except BaseException:
                    process.terminate()
                    try:
                        process.wait(timeout=30)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()
                    raise
                if code:
                    raise Refused("initialization_restore_failed:" + str(code))
        current, _ = identity(options.source, path)
        if current.get("locked") != token or current.get("branch") != reference:
            raise Refused("initialization_identity_changed")
        creation_witness(options.source, reference)
        git(path, "symbolic-ref", "-m", "worktree-recovered:" + token.removeprefix("worktree-init:"),
            "HEAD", reference)
        git(options.source, "worktree", "unlock", path)
        return dict(event="worktree_init", status="recovered", path=str(path), branch=options.branch,
                    recovery_branch=recovery, creation_commit=creation, native_locks=cleared)


def value_from(result):
    return os.fsdecode(result.stdout).strip()


def confirm(root, remote, branch, commit, endpoint=None):
    endpoint = endpoint or remote_endpoint(root, remote, push=True)
    reference = "refs/heads/" + branch
    git(root, "check-ref-format", reference)
    advertised = git(root, "ls-remote", "--exit-code", "--heads", "--", endpoint, reference).stdout.splitlines()
    if len(advertised) != 1:
        raise Refused("remote_tip_unknown")
    tip, actual = advertised[0].split(b"\t")
    if os.fsdecode(actual) != reference:
        raise Refused("remote_identity")
    tip = tip.decode("ascii")
    # Fetch the observed object, without updating tracking refs or FETCH_HEAD.
    git(root, "fetch", "--no-write-fetch-head", "--no-tags", "--", endpoint, tip)
    if git(root, "merge-base", "--is-ancestor", commit, tip, check=False).returncode:
        raise Refused("remote_does_not_retain_commit:" + commit)
    return dict(remote=remote, endpoint=endpoint, branch=branch, required_commit=commit, observed_tip=tip,
                relation="equal" if commit == tip else "ancestor")


def commit_snapshot(path, metadata, branch, message, stack, source):
    try:
        return ordinary_snapshot(path, metadata, branch, message)
    except GitFailure as error:
        locks = native_lock_candidates(path, metadata, branch, error)
        if not locks:
            raise
        with exclusive_tree(stack, source, path):
            cleared = clear_native_locks(source, path, locks)
            stack.native_locks = getattr(stack, "native_locks", []) + cleared
            try:
                return dict(ordinary_snapshot(path, metadata, branch, message), native_locks=cleared)
            except (Refused, OSError, subprocess.SubprocessError) as retry_error:
                retry_error.native_locks = cleared + getattr(retry_error, "native_locks", [])
                raise


def ordinary_snapshot(path, metadata, branch, message):
    """Consume the ordinary index under the caller's Git operation scope."""
    if git(path, "ls-files", "--unmerged").stdout:
        raise Refused("unmerged_index")
    for marker in ("MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD", "rebase-merge", "rebase-apply", "sequencer"):
        if (metadata / marker).exists():
            raise Refused("unfinished_operation:" + marker)
    parent = value(path, "rev-parse", "--verify", "HEAD^{commit}")
    git(path, "add", "-A", "--", ".")
    difference = git(path, "diff", "--cached", "--quiet", "--exit-code", check=False)
    if difference.returncode not in (0, 1):
        raise Refused(difference.stderr.decode(errors="replace").strip() or "index_comparison_failed")
    if difference.returncode:
        git(path, "commit", "-F", "-", input=message)
    commit = value(path, "rev-parse", "HEAD")
    return dict(event="worktree_checkpoint", status="committed" if difference.returncode else "unchanged",
                commit=commit, parent=parent, branch=branch)


def checkpoint(options):
    with ExitStack() as stack:
        path = tree_scope(stack, options.source, options.path)
        _, metadata = identity(options.source, path)
        branch = git_scope(stack, options.source, path)
        if not branch.startswith("refs/heads/"):
            raise Refused("checkpoint_current_branch_required")
        message = (read_input(options.source, options.message_file) if options.message_file
                   else b"Checkpoint working tree before publication\n")
        return commit_snapshot(path, metadata, branch, message, stack, options.source)


def publish(options):
    with ExitStack() as stack:
        path = tree_scope(stack, options.source, options.path)
        identity(options.source, path)
        branch = git_scope(stack, options.source, path)
        actual_branch = branch.removeprefix("refs/heads/")
        if options.branch != actual_branch:
            raise Refused("publication_branch_mismatch")
        commit = value(path, "rev-parse", "--verify", options.commit + "^{commit}")
        if git(path, "merge-base", "--is-ancestor", commit, "HEAD", check=False).returncode:
            raise Refused("publication_commit_outside_branch")
        endpoint = remote_endpoint(path, options.remote, push=True)
        # A newer remote tip already retaining this unit is sufficient; no rewind.
        try:
            evidence = confirm(path, options.remote, options.branch, commit, endpoint)
        except Refused:
            git(path, "push", "--", endpoint, commit + ":refs/heads/" + options.branch)
            evidence = confirm(path, options.remote, options.branch, commit, endpoint)
        return dict(event="worktree_publication", status="confirmed", **evidence)


def finalize(options):
    # Job creation, descendant ownership and joining belong to the host. This
    # synchronous command runs only after the owning host has joined its handles.
    # Other participants keep their shared entry and independent edit scopes.
    if not options.writers_joined:
        raise Refused("host_must_join_task_writers")
    result = checkpoint(options)
    options.commit = result["commit"]
    return publish(options)


def validate_mirror(root, head, integration_tip, landing, message):
    """Check the producer's identity, parent and net-patch contract for any head."""
    head = value(root, "rev-parse", "--verify", head + "^{commit}")
    landing = value(root, "rev-parse", "--verify", landing + "^{commit}")
    parents = value(root, "show", "-s", "--format=%P", head).split()
    if len(parents) != 1:
        raise Refused("mirror_requires_single_parent:" + head)
    original = value(root, "show", "-s", "--format=%(trailers:key=Original-Dev-Commit,valueonly)", head)
    if original != landing or value(root, "show", "-s", "--format=%s", head) != message:
        raise Refused("mirror_identity_changed:" + head)
    if git(root, "merge-base", "--is-ancestor", parents[0], integration_tip, check=False).returncode:
        raise Refused("mirror_base_outside_integration:" + head)

    def patch_id(parent, commit):
        patch = git(root, "diff", "--no-ext-diff", "--no-textconv", "--binary", parent, commit).stdout
        return git(root, "patch-id", "--stable", input=patch).stdout.split()[:1]

    if patch_id(parents[0], head) != patch_id(landing + "^1", landing):
        raise Refused("mirror_patch_mismatch:" + head)
    return dict(commit=head, base=parents[0], original_commit=landing)


def prepare_mirror(options):
    options.initialization_stage = "preflight"
    try:
        return initialize_mirror(options)
    except (Refused, OSError, subprocess.SubprocessError) as error:
        print("WORKTREE_FAILED " + json.dumps(dict(stage=options.initialization_stage,
            target=str(options.path), retained_material=dict(path=str(options.path), branch=options.branch),
            recovery_action="reclaim the registered mirror with make worktree-remove NAMES=" + options.path.name,
            reason=str(error))), file=sys.stderr, flush=True)
        raise


def initialize_mirror(options):
    """Producer-owned temporary checkout operation; failure leaves its source."""
    import uuid
    with ExitStack() as stack:
        endpoint = remote_endpoint(options.source, options.remote, push=True)
        if options.path.exists() or options.path.is_symlink():
            raise Refused("mirror_destination_occupied")
        path = tree_scope(stack, options.source, options.path, True)
        reference = "refs/heads/" + options.branch
        git(options.source, "check-ref-format", reference)
        acquire(stack, options.source, "ref:" + reference, True)
        existing = git(options.source, "rev-parse", "--verify", reference, check=False)
        args = [] if existing.returncode == 0 else ["-b", options.branch]
        token = "worktree-init:" + uuid.uuid4().hex
        options.initialization_stage = "registration"
        git(options.source, "worktree", "add", "--lock", "--reason", token,
            *args, path, options.branch if not args else options.base)
        _, metadata = identity(options.source, path)
        acquire(stack, options.source, "index:" + str(metadata), True)
        landing = value(path, "rev-parse", "--verify", options.merge + "^{commit}")
        if value(path, "rev-parse", "HEAD") == value(options.source, "rev-parse", options.base):
            parents = value(path, "show", "-s", "--format=%P", landing).split()
            mainline = ["--mainline", "1"] if len(parents) > 1 else []
            options.initialization_stage = "checkout"
            git(path, "cherry-pick", "--no-commit", *mainline, landing)
            options.initialization_stage = "commit"
            git(path, "commit", "--allow-empty", "-m", options.message +
                "\n\nOriginal-Dev-Commit: " + landing)
        head = value(path, "rev-parse", "HEAD")
        validate_mirror(path, head, options.base, landing, options.message)
        options.initialization_stage = "publication"
        git(path, "push", "--", endpoint, head + ":" + reference)
        options.initialization_stage = "confirmation"
        evidence = confirm(path, options.remote, options.branch, head, endpoint)
        if (metadata / "locked").read_text().strip() != token:
            raise Refused("mirror_initialization_identity_changed")
        options.initialization_stage = "unlock"
        git(options.source, "worktree", "unlock", path)
        return dict(event="worktree_mirror", status="confirmed", commit=head, **evidence)
