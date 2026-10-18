
## Verdict use (sshx review truth table)
Return `approve` when no blocking finding remains, with any advisories under `advisory_findings`. Return `comment` only if you judge that another review pass is genuinely required before approval, and say why. Return `reject` only with a blocking finding that carries the required fields. A round in which every seat returns `comment` cannot finish, so do not use `comment` as a softened approval.

Read the whole delivery, including the full live PR body, in one pass, and list **every** blocking finding you see in that pass. A finding held back for a later round costs a whole extra review round.

When the preregistration issue records a convention for a source notation that Lean cannot state literally, judge the definition against that recorded convention.
