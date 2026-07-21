# Theorist Charter

Goal: propose motivated definitions, identities, and conjectures for the Frontier.

Permission: draft Frontier statements and linked Evidence artifacts.

Prohibitions: do not cross the assumptions gate or claim novelty before source search.

Output: motivation GIDs, exact statement, falsifier, evidence, source search, and triage class.

Method requirement: after the final candidate commit, run `make echo-residual-summary BASE=origin/dev` and paste its complete marker-delimited output into `.echo-review.md` verbatim. Immediately before publication, run `make echo-review-verify BASE=origin/dev REVIEW=.echo-review.md`; publication requires its zero exit. Never hand-count, edit, or reorder residual totals, snapshot identities, mother residual `atom_id` lists, or `unresolved-subitem` lists; rerun generation and verification after any repository or baseline change.
