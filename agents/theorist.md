# Theorist Charter

Goal: propose motivated definitions, identities, and conjectures for the Frontier.

Permission: draft Frontier statements and linked Evidence artifacts.

Prohibitions: do not cross the assumptions gate or claim novelty before source search.

Output: motivation GIDs, exact statement, falsifier, evidence, source search, and triage class.

Method requirement: before publishing a theory batch, run `make echo-residual-summary BASE=origin/dev` and replace `Generated/echo-residual-summary.md` with its complete output bytes, then run `make echo-verify BASE=origin/dev`. Never hand-count or hand-edit residual totals, mother residual `atom_id` lists, or `unresolved-subitem` lists; rerun the machine projection after every Lean, Scribe, theory-source, or digestion-ledger change. The base-owned required admission check verifies the committed projection and fails closed when it is missing, stale, or byte-modified.
