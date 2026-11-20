
## Full report seed recovery

Scoped report production uses `make lean-report-scoped LEAN_TARGETS="<the same list>"` and reads the local Lake cache. If an explicitly requested full report fails with `LEAN_REPORT_CACHE_INCOMPATIBLE … reason=linked-worktree`, follow the reported recovery command. It rebuilds the report seed on the clean main dev checkout and runs `make lean-cache-ensure FULL_BUILD=1` in the worktree. Rerun the full report after successful recovery.
