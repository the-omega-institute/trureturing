
## Sync with dev before the first emit (binding; precedes every door step)
A worktree's base can carry another lane's file that `make emit` or a door rejects, and that dev has since fixed (for example a Library note with a noncanonical `triage` value). Bring the branch to current dev before the first `make emit`:
- `git fetch origin dev`;
- then `git merge --ff-only origin/dev` when the branch has no commits of its own, otherwise `git merge --no-edit origin/dev`.

The uncommitted delivery stays in place. If the merge conflicts, `git merge --abort` and stop with `open`. A failure that names only another lane's file, and that persists after this sync, is a door blocker: report it.

**Recount capacity after the sync.** Other lanes keep adding files to the same directories. After merging `origin/dev`, run `git ls-tree --name-only origin/dev <dir>/ | wc -l` again for every directory that receives a new file: the `Library/<Domain>` note directory, the D5 bucket and the Blueprint bucket. If a count is 96 or more, move the new file before the doors to a registered directory with room, and update every reference to it (the Scribe `LibraryNoteRef`, the dossier and the module comment). SL-003 blocks a new file in a directory that already holds 96 or more entries.
