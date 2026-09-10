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

The universal congruence is now proved in the incremental Lean check.
The full project gates, freeze, and PR remain pending at this checkpoint. The two higher conjectures are outside
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
The final binomial cube expansion and universal theorem now compile (scratch
check 12, exit 0). The final theorem has only propext, Classical.choice, and
Quot.sound in its transitive axiom closure.


## Proof and admission assessment

For the sole authored public theorem
D5/S3/ArithSums/A375178Supercongruence.supercongruence:

- proof_shape: content.
- direct frozen dependencies (GID + statement_id): none; no D5 imports.
  Pinned mathlib is reused, especially
  FiniteField.sum_pow_lt_card_sub_one.
- escape_witness: lifted_doubleH, supported by doubleH_zero, together with
  the first-order binomial_cube_expansion. This implements the brief's
  proposed missing first-order cancellation.
- admission_basis: escape-witness.
- utility: none. The sequence definition and symbolic theorem, as well as
  the private general algebraic and harmonic lemmas, do not produce bounded
  enumerations, checkers, numeric reductions, or certified finite instances.
  Small literal positivity proofs are internal side conditions only.

The four checks of CLAUDE.md 3.2 apply as follows:
(i) the final elaborated proof uses lifted_doubleH as h13, while its sum
identity uses binomial_cube_expansion; both are in the dependency closure;
(ii) proving doubleH_zero requires constructing reversal and shuffle
identities over varying finite fields, and the expansion requires induction
over arbitrary finite products, rather than instantiating a frozen
congruence; (iii) these statements concern weighted inverse sums and one
binomial summand, not the final sequence congruence; (iv) the expanded sum
is rewritten using h13 to kill its second term. Removing this rewrite
leaves that summand undischarged. The witnesses are used in the live proof,
not attached as unused conjunction components. The repository proof-edges.sh audit returns
EDGES_OK edges=25 kernel_nonauxiliary_constants=2. The two authored public
constants are the definition a and theorem supercongruence. Raw graph
projections stay in the runner attempt directory, not tracked reports.

The public definition a is the exact sequence, not a second theorem.
All supporting lemmas are private and analyzed inside the public theorem.

## Mathematical argument

Let H_r be the sum of 1/k^r over 1<=k<p, and H_(1,3) the sum of
1/(j*k^3) over 1<=j<k<p. Work with units in ZMod(p^5); the implementation
includes the zero index only when its inverse term vanishes.

First-order expansion gives
a(p)-1 = p^3 H_3 + 3 p^4 H_(1,3) in ZMod(p^5).
The product expansion has an explicit quadratic remainder, so cubing
discards only a multiple of p^5.

For the first term, put x=1/k and y=1/(p-k). Then x+y=p*x*y.
Modulo p^5, p^3(x^3+y^3)=-3p^4*x^4. Sum over k and reflect the
interval: 2p^3 H_3=-3p^4 H_4=0, using the fourth inverse-power sum in
ZMod(p). The unit 2 can be cancelled.

For the second term, reflection of the two indices yields
H_(1,3)=H_(3,1) modulo p. The shuffle identity is
H_1*H_3=H_(1,3)+H_(3,1)+H_4. Finite-field power sums give
H_1=H_4=0 for p>=7, hence H_(1,3)=0. Both terms vanish as required.

## Attempt history

The initial ring and finite-field lemmas compiled first. The next successful
unit was the paired cubic identity and its sum. The nested-sum conversion
then connected the double harmonic identity to natural range sums.
The binomial recurrence required explicitly casting its natural equality;
exact_mod_cast did not normalize that equation. The final congruence
translation required normalizing Nat.cast_one before change. These were
elaboration issues in the same proof route, not remaining mathematical gaps.
Every successful unit was committed and pushed. No finite probe is counted
as partial mathematical progress.

Capacity audit at the proof/document checkpoint: make -C tools capacity-audit
returned CAPACITY_AUDIT_RESULT exit=0 reason=clean.
