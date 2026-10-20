
## Local gate result in the PR body (CLAUDE.md §2.1, §2.4, §2.9; mandatory)
Review seats reject a body that reports the required CI success but omits a local gate that did not pass. The Verification section states the final local gate as current result data:
- the exact command `make gate BASE=<40-hex>`;
- the head it ran at and the protected base;
- the exit code;
- every blocking diagnostic line verbatim. For a Scribe change this is normally SL-022 "protected-surface change detected" on each `.scribe.cs`.

Say plainly that SL-022 is the protected-surface observation for Scribe changes and that the required CI check `required` is the admission authority, and give the state of `required` at the delivered head. If the gate ran at an earlier head than the delivered one, give the `git diff --stat <gate head> HEAD -- D5 Golden Blueprint` reading too. Never omit a non-zero gate, and never present it as a failure of the mathematics.
