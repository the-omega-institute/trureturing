Make engineering test selection fail closed at the execution boundary

AI disclosure: this fix was implemented by the codex-cli `fix_or_done` worker under `consensus-rnd:sshx` after three independent review seats rejected pass 0 (architecture, tests, and quality). The worker implemented the four blocking findings and ran the named production-boundary, workflow-consumer, fallback, mutation, and preflight checks. The prior seat findings are inputs; the fresh verification receipts in this PR are worker-observed.

This PR keeps the candidate-side incremental plan as an optimization while requiring TRX evidence that every planned test identity actually executed. Zero matches, launcher substitution, missing evidence, and selected execution failures fall back to the unfiltered suite. Invalid or unreadable plan artifacts take the same unfiltered fallback.

The base-owned `pull_request_target` workflow now derives an independent floor directly from `HEAD^1..HEAD`. Changes under `tools/`, to this workflow, or to repository-root inputs force a direct unfiltered test invocation even when the candidate planner reports `none`.

The workflow change and every script it calls are included in this same PR. 合入后立即观察首个真实触发的运行；若该运行红，则立即回滚。The observed run link will be added to the PR after that first post-merge trigger, as required for a `pull_request_target` workflow.
