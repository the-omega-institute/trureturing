
## Worktree is read-only for review seats
Review seats only observe the assigned HEAD. Do not fetch, create worktrees, switch branches, merge, rebase, commit, reset, stash or push. Never create a worktree under `/tmp`, `/private/tmp` or `$TMPDIR`.

Use pinned reads: `git show <commit>:<path>`, `git grep <pattern> <commit> -- <path>` and `git diff <base> <head> -- <path>`. Keep `git rev-parse HEAD` equal to the assigned head.

Do not run builds or tests that write files, including ignored caches or reports. Report checks that need writes back to the caller; the caller runs them in a compatible linked worktree per CLAUDE.md §6.1, reusing one first and creating one only when isolation is needed. A clean `git status --short` alone does not prove read-only execution.
