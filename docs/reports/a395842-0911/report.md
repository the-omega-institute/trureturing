# A395842 implementation record

## Provenance and scope

One Codex implementation worker using the `lean4` skill, with no delegated workers
or independent review in this attempt. The numerical and literature readings in
the task brief are supplied by the orchestrator and triage worker; they are not
reported as this worker's own measurements.

Repository: https://github.com/the-omega-institute/trureturing
Branch: `lane/math/a395842`.
Initial base: `6af98a19b1fd4f76f1bc1bf92b61593a0c167a09` (`origin/dev`).
Tier: 第一档 (recent OEIS conjecture).

Target: for the uniquely specified integer power series with g₀ = 0,
g₁ = g₂ = 1 and coeff n (G iterated n) = coeff n (G iterated (n−1))
for n > 2, prove 2 divides the diagonal coefficient for every n ≥ 2.
Neither the series nor the diagonal sequence may encode the parity conclusion.
No extension to the parity conjecture for A177775 is in scope.

## Preregistration

Proposed bridge, still ASSUMED-UNVERIFIED: identify G modulo 2 with
H = Σᵣ x^(2^r), prove the iterate coefficient formula
[x^(2^r)] H iterated m = choose(m+r−1,r) modulo 2, and use binary
binomial arithmetic plus the additive support to discharge the diagonal rule
and the diagonal parity. The nontrivial candidate witness is the connection
between the implicit diagonal constraints and this characteristic-two series.
Before implementation, search D5, pinned Mathlib, and the external Lean/literature
ecosystem, including every public declaration of the two specified iterate modules.

No theory volume or atom will be created. Any justified freeze uses the existing
uncovered-deposit / ledger-align --add path. Stop on a published proof of the same
diagonal conjecture, on a route depending only on the unproved A177775 claim,
or on an already proved bridge leaving only binding and index rewriting.

## Initial instruction reading

Read the complete CLAUDE.md, agents/CONTEXT.md and lean4/SKILL.md.
User-required persistent commits and the repository make/cache/gate protocol
override the skill-only default of a single pass without commits.
The task's implementation completion condition is a proved target with a PR;
it does not authorize claiming that an unmerged PR has landed on dev.

## Current result

Implementation in progress. No theorem has yet been claimed or frozen.

## Unclaimed

No claim of an exhaustive literature search, a proof of G's parity, a proof of
A177775, an independent review, or a successful build has been made.
Unopened external pages are ASSUMED-UNVERIFIED.
