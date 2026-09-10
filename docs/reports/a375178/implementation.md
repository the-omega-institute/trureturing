# A375178 implementation record

Target: for every prime `p ≥ 7`, the sum
`a(p) = ∑ k ∈ range p, choose (p + k - 1) k ^ 3` is `1 mod p^5`.
Tier: first. The user's arXiv/OEIS search supports openness only in its stated
scope; this record does not assert worldwide novelty.

Provenance: Codex implementation worker, Lean 4 skill, one model and no independent
review yet. The proof route and earlier literature search were supplied by the user.
Base: `5a99ae1169edaf09a73a9685ec0dcb2ce3da2dad`.

## Initial checks

The complete `CLAUDE.md` and `agents/CONTEXT.md` were read. Working branch:
`lane/math/a375178`. No theory volume or atom will be created for this task.

Local search with `rg -n -i 'a375178|wolstenholme|harmonic.*(congru|mod)|调和.*同余'
D5 Problems` returned no matches (exit 1). The first mathlib search could not run:
this worktree has no `.lake` yet (exit 2); this is not negative search evidence.

Python arbitrary-precision integer probe, using `math.comb` and trial-division
primes in `[5,257]`: p³ has 0/53 failures; p⁵ for p≥7 has 0/52 failures;
p⁶ has 51/52 failures (only p=37 passes); `v₇(a(7)−1)=5`.
All these measurements agree with the brief. These are probes, not proofs or
positive finite certificates for freezing.

The first 19 computed values are:
`0, 1, 9, 244, 9065, 389376, 18188478, 897376152, 46011772521,
2427553965160, 130930630643384, 7186614533569296, 400132290102421214,
22543708920891189136, 1282873288801683197250, 73628947696550668509744,
4257138240245923453355625, 247733479854085081062353400,
14498252738780732999484606360`.
The subsequent OEIS b-file comparison matches all 19 terms. The initial JSON URL
`https://oeis.org/search?q=id:A375178&fmt=json` returned HTTP 403, an invalid query.

## Unclaimed

No universal congruence, counterexample, Lean build, freeze, or literature-search
completion is claimed at this checkpoint. The two higher conjectures are outside
scope. Pages not retrieved by this worker remain `ASSUMED-UNVERIFIED`.

## Kernel checkpoints

The one-step product expansion, inverse power sums (by the pinned finite-field
theorem), cast/range summation, reversal and shuffle for H(1,3), and
p³ H(3)=0 in ZMod(p⁵) compile without sorry or additional axioms.
The last result uses the identity
t³(x³+y³)=−3t⁴x⁴ when t⁵=0 and x+y=txy,
then the four-th power sum and cancellation of the unit 2.
The tested scratch file's axiom output contains only propext, Classical.choice,
and Quot.sound (the abstract paired-cube identity does not require choice).
The actual universal A375178 statement is not yet proved.
