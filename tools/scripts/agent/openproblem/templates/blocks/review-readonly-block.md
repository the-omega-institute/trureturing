
## Worktree is read-only for review seats
Do not merge, rebase, commit, reset, stash or switch branches in this worktree, and do not push. For fresh-dev checks, `git fetch origin dev` and query objects directly (`git grep <sha>`, `git show <sha>:<path>`, `git diff <sha> HEAD`), or create a temporary worktree under `/tmp` with `git worktree add --detach` and remove it before you return. Builds and tests you run must leave `git status --short` empty and `git rev-parse HEAD` equal to the assigned head.
