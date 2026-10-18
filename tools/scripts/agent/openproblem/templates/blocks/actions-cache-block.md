
## Actions cache before every push
Immediately before each push to the PR branch, delete this PR's merge-ref `lean-project-*` Actions caches so its CI restores dev's current project cache instead of its own older one:
`for id in $(gh cache list --limit 300 --json id,ref,key -q '.[]|select(.ref=="refs/pull/<PR>/merge" and (.key|startswith("lean-project")))|.id'); do gh cache delete $id; done` (replace `<PR>` with this PR's number). Caches are not truth sources; this changes only the incremental starting point. Do not mention the deletion in the PR body.

## Session recovery line
Keep session recovery ids in the provenance section for the orchestrator and implementation seats actually used. Give each carrier's resume command with its supplied session id; never include a local rollout path.
