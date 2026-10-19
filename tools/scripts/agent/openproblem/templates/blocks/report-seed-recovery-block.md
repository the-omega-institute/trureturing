
## Report seed recovery (binding; extends the infrastructure retry rule)
If `make lean-report-scoped LEAN_TARGETS="<the same list>"`, or a door that runs it, fails with `LEAN_REPORT_CACHE_INCOMPATIBLE … reason=linked-worktree`, the report seed in this worktree predates the current reuse receipt. This is not a defect of the lane. Recover once with the canonical reseed from the warm main checkout (the remediation the tool prints):
1. `rm -rf -- .lake && make lean-cache-ensure && make lean LEAN_TARGETS="<the delivered modules and every frozen module you re-pin, dotted>"` in this worktree;
2. rerun the failed door, still waiting for the report slot as above.

Return `open` only if the same diagnostic recurs after the reseed, and cite both logs. The reseed deletes only this worktree's `.lake`; it does not touch tracked files, commits or other worktrees.
