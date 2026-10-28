
## Worktree is read-only for review seats
Do not merge, rebase, commit, reset, stash or switch branches in this worktree, and do not push. For fresh-dev checks, `git fetch origin dev` and use pinned object reads: `git show <commit>:<path>`, `git grep <pattern> <commit> -- <path>` and `git diff <base> <head> -- <path>`.

Do not create another worktree, including under `/tmp`, `/private/tmp` or `$TMPDIR`. If a check needs another worktree, report it to the caller, who follows CLAUDE.md §6.1.

Builds and tests may run in the assigned worktree; they must leave `git status --short` empty and `git rev-parse HEAD` equal to the assigned head.
