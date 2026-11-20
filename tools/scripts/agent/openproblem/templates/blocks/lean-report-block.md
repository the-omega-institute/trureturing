## One lean-report producer per machine
Serialize scoped Lean-report producers on a shared host. Immediately before each of them, run `pgrep -fl 'lean-inspector|report-supervisor' || true`; if another producer is running (another worktree), wait for it with a bounded loop (`for i in $(seq 1 720); do pgrep -f 'lean-inspector|report-supervisor' >/dev/null || break; sleep 30; done`) and then run yours. The door itself may still return exit 3 `REPORT_SLOT_BUSY` when another worktree takes the slot first; that changes nothing, so wait the same way and rerun the door. Keep waiting and retrying for up to six hours in total (`seq 1 720`); return with `open` only after six hours without obtaining the slot. A `make lean-report-scoped LEAN_TARGETS="<the same list>"` that fails with `Too many open files in system`, exit 124, or a lean-report-materials frame error from a killed inspector batch is host load, not a defect: wait two minutes and rerun within the same six hours.

## One row per reading in the PR body
Report each check once, as its final result at the delivered head: `make emit` is ONE row reading "exit 0; a rerun reports 0 changed blueprints" — never "make emit (first)" / "make emit (second)" rows, never a row for an intermediate run that was superseded. Review seats reject intermediate-run rows as process chronology (CLAUDE.md §2.10). The direct `lake env lean` row carries `/usr/bin/time -l` wall seconds AND maximum resident set size.

## Only this lane's files
If `make emit` rewrites a Blueprint projection that belongs to another delivery (any file other than this lane's module mirror), restore it to `origin/dev`'s bytes before committing (`git checkout origin/dev -- <path>`) and do not mention it in the PR body; the PR touches only this lane's module, mirror, emitted Markdown, Golden door output, Library note, dossier and (if any) Reg file.

## Full report seed recovery

Scoped report production uses `make lean-report-scoped LEAN_TARGETS="<the same list>"` and reads the local Lake cache. If an explicitly requested full report fails with `LEAN_REPORT_CACHE_INCOMPATIBLE … reason=linked-worktree`, follow the reported recovery command. It rebuilds the report seed on the clean main dev checkout and runs `make lean-cache-ensure FULL_BUILD=1` in the worktree. Rerun the full report after successful recovery.
