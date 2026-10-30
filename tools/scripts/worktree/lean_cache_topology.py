"""Git checkout classification and main-checkout cache warm-up guidance."""
from __future__ import annotations

import pathlib
import re
import shlex
import subprocess


def git_absolute_path(root, *arguments):
    result = subprocess.run(["git", "-C", str(root), "rev-parse", *arguments],
                            check=True, capture_output=True, text=True, timeout=10)
    value = result.stdout.rstrip("\n")
    if not value or "\n" in value or not pathlib.Path(value).is_absolute():
        raise ValueError("Git path is not an absolute path")
    return pathlib.Path(value).resolve()


def checkout_topology(root):
    """Return (linked, validated main path); refuse unknown classification."""
    try:
        git_directory = git_absolute_path(root, "--absolute-git-dir")
        common_directory = git_absolute_path(root, "--path-format=absolute", "--git-common-dir")
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        detail = getattr(error, "stderr", None) or str(error)
        raise ValueError(f"cannot determine checkout Git topology: {detail}") from error
    linked = git_directory != common_directory
    try:
        result = subprocess.run(["git", "-C", str(root), "worktree", "list", "--porcelain", "-z"],
                                check=True, capture_output=True, text=True, timeout=10)
        if not result.stdout.endswith("\0\0"):
            raise ValueError("missing or incomplete Git worktree records")
        checkouts = []
        for record in result.stdout[:-2].split("\0\0"):
            lines = record.split("\0")
            fields = dict((line.partition(" ")[0], line.partition(" ")[2]) for line in lines)
            if (not lines[0].startswith("worktree ") or len(fields) != len(lines)
                    or set(fields) - {"worktree", "HEAD", "branch", "detached", "bare", "locked", "prunable"}
                    or not fields.get("worktree") or not pathlib.Path(fields["worktree"]).is_absolute()):
                raise ValueError("unparsable Git worktree record")
            if "bare" in fields:
                raise ValueError("Git main checkout is bare")
            if (not re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", fields.get("HEAD", ""))
                    or ("branch" in fields) == ("detached" in fields)
                    or ("branch" in fields and not fields["branch"].startswith("refs/heads/"))
                    or fields.get("detached", "")):
                raise ValueError("unparsable Git worktree HEAD or branch")
            checkouts.append(pathlib.Path(fields["worktree"]).resolve())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        if linked:
            return True, None
        detail = getattr(error, "stderr", None) or str(error)
        raise ValueError(f"cannot determine checkout Git topology: {detail}") from error
    if not linked:
        return False, None
    candidate = checkouts[0]
    try:
        if (git_absolute_path(candidate, "--show-toplevel") != candidate
                or git_absolute_path(candidate, "--path-format=absolute", "--git-common-dir") != common_directory):
            return True, None
    except (OSError, ValueError, subprocess.SubprocessError):
        return True, None
    return True, candidate


def warm_dev_remediation(main_checkout):
    if main_checkout is None:
        return ("sync dev and warm the dev cache in this repository's dev main checkout: "
                "make warm-donor there (its location cannot be determined from this worktree)")
    return "sync dev and warm the dev cache: make -C " + shlex.quote(str(main_checkout)) + " warm-donor"
