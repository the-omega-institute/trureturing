---
slug: oeis-a393867-all-terms-odd
bibkey: hanna2026a393867
doi: null
url: https://oeis.org/A393867
triage: open
motivation_gids:
  - D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative
---

# A393867: every logarithmic-derivative coefficient is odd

## Problem

The second OEIS A393867 comment is exactly: "Conjecture: all terms are odd."
The target is `Odd (a393867 n)` for every `n >= 1`, using the definition in
`PrimePowerShiftLogDerivative`. This is the first-tier 2026 conjecture; the
prime-divisibility comment and A393866's shifted printed formula are distinct.

## Implementation record

Skill context: `lean4`; Codex implementation worker, single source of reasoning,
zero independent review seats in this worker. User-supplied numerical claims
were independently rerun here. No multi-model consensus is claimed.
Base: `6af98a19b1fd4f76f1bc1bf92b61593a0c167a09`.
The existing frozen Lean module is read-only. The parity directory contains
26 files before this change (`find D5/S1/Recurrence/Parity -type f | wc -l`).

## Preregistered proof route

Proposed escape witness: the paired-coefficient theorem
`F_(2m) = F_(2m+1)` modulo two, derived from the integral source equations.
Implementation form: over `ZMod 2`, set `D = (1+X)*F' - F`. Its odd-degree
coefficients vanish identically. At even degree `k > 0`, take the defining
equation at `n=k+1`; the prime is odd, so the power rule turns this equation
into `coeff k (D * F^(prime n - 1)) = 0`. Strong induction and the constant
coefficient one force `coeff k D = 0`. The base uses the integral equation at
`n=1`, which gives `F_1=1` before reducing modulo two. Thus `D=0` proves the
paired-coefficient witness. Multiplying by the unit inverse of F then gives
`(1+X)*(F'/F)=1`, whose coefficients recursively all equal one.
This preserves the proposed paired-coefficient mathematics while eliminating
the need to introduce a separate series H and substitution by X squared.
The witness is a proof obligation, not a hypothesis.

## Search receipts

- Repository D5: `rg` for `A39386[678]`, `a393867`, and `convolution_pairing`.
  Read all 278 lines of `PrimePowerShiftLogDerivative`, including private
  helpers. `generating_equation`, `lt_prime`, and the inverse definition are
  reusable. `hanna_conjecture` proves prime divisibility only, which does not
  imply oddness. `printed_formula_false` concerns the shifted formula only.
  `prime_dvd_coeff_pow` controls divisibility by the indexing prime, not two.
  Its private `coeff_mul_vanish` shows the useful lowest-coefficient pattern.
- Read the general public `convolution_pairing` in
  `ConvolutionRecurrenceOddPowersOfTwo`; that module is `generality: I`, so
  this G module cannot import it (SL-010). The derivative route does not need it.
- Pinned mathlib: Lean v4.33.0, mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`. Exact OEIS identifiers absent;
  `Hanna` hits are unrelated names. Located `coeff_derivative`,
  `derivative_pow`, and `ZMod.intCast_eq_one_iff_odd` for direct reuse.
- OEIS JSON query `id:A393866|id:A393867`, fetched successfully (HTTP 200):
  both entries returned; A393867 still prints both conjecture comments.
- GitHub code API: exact queries `"A393867" language:Lean` and
  `"A393866" language:Lean` each returned total_count=0, incomplete_results=false.
- Loogle: `PowerSeries, "derivative"` returned 30 declarations, including the
  power rule. The logarithm results require rational-algebra hypotheses and
  do not prove the characteristic-two paired-coefficient statement.
- arXiv API: `all:A393866 OR all:A393867` returned totalResults=0;
  `(all:prime AND all:Hanna) AND (all:logarithmic OR all:"power series")`
  also returned totalResults=0. Both responses were valid Atom feeds with
  the exact query echoed. No failure is counted as a negative result.
  No proof found in this explicit search scope; no global absence claim.

## Numerical semantic echo

Independently ran the specified strict-prefix Miller recurrence at N=100,
asserting both exact Miller division and `prime n | c_n` at each step, then
used `g_n = n*F_n - sum_(k=1..n-1) g_k*F_(n-k)`.
All 100 prime-divisibility assertions passed. F's first 21 coefficients and
g's first 20 coefficients match the directly fetched OEIS DATA exactly.
No even g term among indices 1 through 100; no failure among the 50 pairs
`(F_(2m),F_(2m+1))`, m=0 through 49. F at indices 1 through 100 has 41 even
and 59 odd entries, agreeing with the brief. At indices 0 through 99 the
counts are 40 and 60; this is an indexing distinction, not a conflicting run.
F parity at indices 0 through 20:
`1,1,0,0,0,0,1,1,0,0,0,0,1,1,1,1,1,1,1,1,0`.
These checks are probes, not a finite positive formal instance or progress
toward the unbounded theorem.

## Build receipts

`make lean-cache-ensure`: EXIT=0; `LEAN_CACHE` status=seeded,
method=clonefile, donor=/Users/chronoai/trureturing, clonefile_attempts=1,
stamp_miss=null; project and mathlib olean states both warm.
The first genuine Lean attempt implemented the defect power rule and the
strong induction `defect_f_zero`. Initial errors were zero-coefficient
rewrites, the distinction between `constantCoeff` and `coeff 0`, and a
nonexistent `ZMod.eq_zero_or_eq_one` name. These were repaired using explicit
Mathlib coefficient rewrites and a private kernel `decide` on `ZMod 2`.
The file-level hot-cache compilation now exits 0 and proves `defect_f_zero`
without `sorry` or added axioms. This is an unbounded structural lemma, not
a finite-check progress claim; the target theorem is still pending.

Next checkpoint: both public theorems `generating_coeff_pair` and
`a393867_odd` compile (file-level EXIT=0), with `#print axioms` reporting only
`propext`, `Classical.choice`, and `Quot.sound` for each. The main theorem
uses `generating_coeff_pair` through `paired_derivative` and
`log_mod_two_identity`; the paired result is on the live derivation path.
Project build, report, emission, content checks, and freezing remain pending.

## Unclaimed and unverified

No proof, priority, exhaustive literature search, A393868 result, or completed
PR is claimed at this checkpoint. A393866 and A393868 b-files were not opened:
`ASSUMED-UNVERIFIED`. The user's arXiv search report is not represented as a
search performed by this worker. No theory volume or atom will be created.

## Theorem admission analysis

Both public declarations have `proof_shape: content` and
`admission_basis: escape-witness`. `utility: none`: these are unbounded
symbolic statements proved by induction and formal-series algebra, not
bounded enumeration, a checker, numerical reduction, or a certified finite
instance. The private initial coefficient and the two-element coefficient
field calculation only support the universal proof.

For `generating_coeff_pair`, the new construction is the strong induction in
`defect_f_zero`, which derives the paired-coefficient conclusion itself
(the second legitimate witness form in CLAUDE 3.2). It uses a newly established
coefficient at every even degree; its proof cannot be reduced to instantiation
or projection of the frozen source equations. The independent intermediate
power-defect equality `defect_pow` supports that induction, but its algebraic
normalization alone is not claimed as the novel content.

For `a393867_odd`, the named witness is `generating_coeff_pair`:

1. Dependency closure: the chain is `a393867_odd` -> `log_mod_two_identity`
   -> `paired_derivative` -> `generating_coeff_pair` -> `defect_f_zero`.
2. Not a frozen projection: the frozen source only defines the series and
   proves divisibility by the nth prime. The new strong induction is needed
   to prove the coefficient pairing modulo two.
3. Not definitionally equivalent: pairing concerns coefficients of F;
   the target concerns coefficients of its derivative times its unit inverse.
   Formal differentiation, inversion, and a second induction connect them.
4. Live path: `paired_derivative` uses the equality for each even degree;
   `log_mod_two_identity` multiplies that equality by the inverse, and the
   final coefficient induction uses this product identity. No discarded
   conjunction or unused witness is used to establish the dependency.

There are no unrelated public companions. The directed consumer edge is
`a393867_odd` -> `generating_coeff_pair` and answers exactly the preregistered
oddness conjecture. The only direct frozen module is
`D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative`, state pin
`sha256:ac377909f3efe06da244e7960fe628f1ea740f752641f94947b75c57a790b785`.
The source theorem dependencies are `generating_equation` and `lt_prime`;
the original definitions `generatingSeries`, `prime`, `logDerivative`, and
`a393867` retain their meanings. Declaration-level identities will be read
from the canonical report/export before delivery.
