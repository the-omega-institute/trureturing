# R2-MATCH: all-order matching SOS investigation

Verdict: **blocked**. Equation (5), the corrected equation (1), and the matching
type were checked in Lean. Equation (2) remains unproved. No theorem was frozen.

Provenance: this is the implementation worker of the user-supplied `consensus-rnd:sshx`
R2-MATCH brief for https://github.com/the-omega-institute/trureturing/issues/6377.
The worker did not invoke a local skill or delegate work. All results below are
single-worker measurements; no independent review or orchestrator verification
is claimed.

Base: `aee1eaff34f997e44f04147cee1010bb482c4c1b`.
Pinned Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`; Lean `v4.33.0`.

## Verified Partial Result: Equation (5)

The source below was compiled at
`D5/S3/Zeros/Convolution/AlternatingFactorialSum.lean` by `make lean`.
The complete project build exited `0` (12580 jobs). All three printed theorem
axiom closures were exactly `propext`, `Classical.choice`, `Quot.sound`.
The proof quantifies over every `d h : Nat`. Numerical calibration is not a proof
premise. The factorial equality is stated over the rationals, with exact casts
of natural factorials; no rounding or truncated division occurs.

`proof_shape: bind-only` for these three partial theorems: inverse-series
identities, coefficient projections, factorial/choose rewrites and ring
normalization supply all their facts. `admission_basis: none` for an independent
freeze of this partial module. `escape_witness: none` for the partial module.
The task's proposed escape witness remains the full equation (2).
This is a source archive, not a deposit, and is not a proof of equation (2).

`utility: none` applies declaration by declaration:

- `opposite_inv_series_mul`: an arbitrary-degree identity over every commutative ring.
- `alternating_choose_convolution`: an arbitrary-parameter symbolic coefficient identity.
- `alternating_factorial_sum`: an arbitrary-parameter symbolic finite-sum identity.

None enumerates a bounded set of parameter instances, implements a checker,
reduces a theorem to unmet numerical premises, or certifies a numerical instance.
All other computational utility fields are `not-applicable(kind=none)`.

No positivity of the full Hermite matrix `H_0(R)` is asserted.
No `FiniteSymbolCriterion` hypothesis, `FiniteAdditiveSymbol.additive_splits`,
or in-flight Hermite parity module is used.

```lean
/- GID: D5/S3/Zeros/Convolution/AlternatingFactorialSum
   generality: G
   mirror-B: D5/B/S3/Zeros/Convolution/AlternatingFactorialSum
   mirror-E: none(waiver:symbolic-generating-function)
   anchors: []
   utility: none
   digest: Alternating factorial convolution from negative binomial series. -/

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-!
All declarations quantify over arbitrary natural degrees and ring coefficients.
The series identity and the two finite-sum identities are symbolic identities,
not bounded enumerations, checkers, numerical reductions, or certified instances.
This is step (5) of the matching-SOS task; it does not prove the matching identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Convolution.AlternatingFactorialSum

open PowerSeries
open scoped BigOperators

/-- The two opposite negative binomial series combine by square substitution. -/
theorem opposite_inv_series_mul {R : Type*} [CommRing R] (d : ℕ) :
    rescale (-1 : R) (invOneSubPow R d).val * (invOneSubPow R d).val =
      expand 2 (by norm_num) (invOneSubPow R d).val := by
  let a : PowerSeries R := (invOneSubPow R d).val
  let b : PowerSeries R := rescale (-1 : R) a
  let c : PowerSeries R := expand 2 (by norm_num) a
  have ha : (1 - X : PowerSeries R)^d * a = 1 := by
    change (1 - X : PowerSeries R)^d * (invOneSubPow R d).val = 1
    rw [← invOneSubPow_inv_eq_one_sub_pow]
    exact (invOneSubPow R d).inv_val
  have hb : (1 + X : PowerSeries R)^d * b = 1 := by
    simpa [b, map_mul, map_pow, map_sub, rescale_neg_one_X] using
      congrArg (rescale (-1 : R)) ha
  have hc : (1 - X^2 : PowerSeries R)^d * c = 1 := by
    simpa [c, map_mul, map_pow, map_sub] using
      congrArg (expand 2 (by norm_num) : PowerSeries R →ₐ[R] PowerSeries R) ha
  have hab : (b * a) * (1 - X^2 : PowerSeries R)^d = 1 := by
    rw [show (1 - X^2 : PowerSeries R) = (1 + X) * (1 - X) by ring, mul_pow]
    calc
      _ = ((1 + X)^d * b) * ((1 - X)^d * a) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  change b * a = c
  calc
    b * a = (b * a) * ((1 - X^2)^d * c) := by rw [hc, mul_one]
    _ = c := by rw [← mul_assoc, hab, one_mul]

/-- Coefficient extraction keeps both parameters unbounded. -/
theorem alternating_choose_convolution (d h : ℕ) :
    (∑ ell ∈ Finset.range (2*h+1), (-1 : ℚ)^ell *
      ((d+ell).choose d : ℚ) * ((d+(2*h-ell)).choose d : ℚ)) =
        ((d+h).choose d : ℚ) := by
  have hc := congrArg (coeff (2*h)) (opposite_inv_series_mul (R := ℚ) (d+1))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simpa only [coeff_rescale, invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk,
    coeff_expand_mul, Nat.succ_eq_add_one] using hc

/-- The alternating factorial identity for every pair of natural parameters. -/
theorem alternating_factorial_sum (d h : ℕ) :
    (∑ ell ∈ Finset.range (2*h+1), (-1 : ℚ)^ell * ((2*h).choose ell : ℚ) *
      ((d+ell).factorial : ℚ) * ((d+2*h-ell).factorial : ℚ)) =
        ((2*h).factorial : ℚ) / (h.factorial : ℚ) *
          (d.factorial : ℚ) * ((d+h).factorial : ℚ) := by
  have hf (i : ℕ) :
      ((d+i).choose d : ℚ) * (d.factorial : ℚ) * (i.factorial : ℚ) =
        ((d+i).factorial : ℚ) := by
    exact_mod_cast (show (d+i).choose d * d.factorial * i.factorial = (d+i).factorial by
      simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right d i))
  calc
    _ = ((2*h).factorial : ℚ) * (d.factorial : ℚ)^2 *
        ∑ ell ∈ Finset.range (2*h+1), (-1 : ℚ)^ell *
          ((d+ell).choose d : ℚ) * ((d+(2*h-ell)).choose d : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      have he : ell ≤ 2*h := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hell
      have hn : ((2*h).choose ell : ℚ) * (ell.factorial : ℚ) *
          ((2*h-ell).factorial : ℚ) = ((2*h).factorial : ℚ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial he
      rw [show d+2*h-ell = d+(2*h-ell) by omega, ← hf ell, ← hf (2*h-ell)]
      calc
        _ = (-1 : ℚ)^ell *
            (((2*h).choose ell : ℚ) * (ell.factorial : ℚ) * ((2*h-ell).factorial : ℚ)) *
            (d.factorial : ℚ)^2 * ((d+ell).choose d : ℚ) *
            ((d+(2*h-ell)).choose d : ℚ) := by ring
        _ = _ := by rw [hn]; ring
    _ = ((2*h).factorial : ℚ) * (d.factorial : ℚ)^2 * ((d+h).choose d : ℚ) := by
      rw [alternating_choose_convolution]
    _ = _ := by
      rw [← hf h]
      have hh : (h.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero h
      field_simp

#print axioms opposite_inv_series_mul
#print axioms alternating_choose_convolution
#print axioms alternating_factorial_sum

end D5.S3.Zeros.Convolution.AlternatingFactorialSum
```

## Outcome And Scope

`verdict: blocked`. The full equation (2) was neither proved nor refuted.
Two attempts at the required combinatorial identification stopped at explicit
unproved goals. The worker stops mathematical implementation at the user-specified
two-attempt boundary. No all-degree nonnegativity consequence, removal of H_1,
equivalence (7), or positive semidefiniteness of H_0(R) is claimed.

`bind_only_attempt`: instantiated the frozen
`FiniteConvolutionCoefficients.coeff_additiveConvolution`, unfolded reflection,
and normalized coefficients using `Polynomial.comp_C_mul_X_coeff`.
The resulting all-degree equality with `matchingSum` remained unproved.
The initial type-class failure for the finite matching subtype was repaired
by unfolding the subtype before `Fintype.ofFinite`; the repeated probe retained
the full equality as its unsolved target.

`escape_witness`: proposed = equation (2); established = none.
`admission_basis: none` for a first freeze of these partial results.
`proof_shape: bind-only` for every proved theorem archived here; the full target
has no proof to classify. `utility: none`, with per-declaration reasons below.

`frozen_output: none`; this is an unfrozen source record.
No matching-SOS anchor was found by the recorded CAS search.
No `make deposit` was run: the requested escape witness was not established.
No state pin, Scribe mirror, or coverage edge was created.
Nothing was added to `Trureturing.lean`; no resource limit or constant was changed.

## Corrected Equation (1)

Reading the source definition gives the falling factorial outside the sum, and
the two input falling factorials in the denominator:

```text
I_k(p) = (-1)^k (n)_(2k)
         * sum_{i=0}^{2k} (-1)^i e_i e_(2k-i) / ((n)_i (n)_(2k-i)).
```

The transferred equation (1) had those positions reversed. The corrected form
agrees with equation (4) in the brief and with the independent calibration.
`symmetrize_coefficient` below proves the corrected form for arbitrary
`n k : Nat`, `2*k <= n`, and arbitrary real polynomial `p`.
Odd coefficient cancellation and the elementary-symmetric monomial identification
in step (4) were not formalized in this attempt.

The only directly applied frozen theorem is
`D5/S3/Zeros/Convolution/FiniteConvolutionCoefficients.coeff_additiveConvolution`,
whose declaration `statement_id` in the existing canonical report is
`sha256:22e74279dd95309d79b0e8a1737f0f3cc47b35cea04bebdf984da4f26e3926f7`.
Its module state pin is
`sha256:58abac734b6a8969c6215223633e21fea7d3901df1967f9531622190c058d12c`.
The reflection theorem uses the frozen `dilate` definition and Mathlib coefficient
rewrites; it applies no frozen theorem. The three factorial-series theorems
apply Mathlib facts only. The dependency direction is
`symmetrize_coefficient -> coeff_reflection, coeff_additiveConvolution` and
`alternating_factorial_sum -> alternating_choose_convolution -> opposite_inv_series_mul`.
These partial chains have no proved connection to equation (2).

## Full Repository Audit

All commands below ran on the specified base and the installed pinned Mathlib,
with complete output retained in the worker artifact `full-repo-audit.json`.
The base was fixed before candidate source was created.

```sh
git grep -n -P '\b(symmetrize_matching_sos|matching_sos|matchingSum)\b' aee1eaff34f997e44f04147cee1010bb482c4c1b
git grep -n -P '(?i)matching.{0,60}(sos|convolution|symmetri)|(?:convolution|symmetri).{0,60}matching|alternating.{0,30}factorial' aee1eaff34f997e44f04147cee1010bb482c4c1b
git grep -n -P '\b(IsMatching|Sym2\.lift|esymm|coeff_prod_X_sub_C|symmetrize|invOneSubPow)\b' aee1eaff34f997e44f04147cee1010bb482c4c1b -- '*.lean'
git -C .lake/packages/mathlib grep -n -P '(?i)matching.{0,60}(polynomial|sum.of.squares|convolution|symmetri)|(?:symmetri|convolution).{0,60}matching|alternating.{0,30}factorial' -- Mathlib
```

Readings: exact names 0; broad repository expression 9 unrelated lines;
related Lean API expression 32 lines; broad Mathlib expression 4 unrelated lines.
The nine repository lines concern unrelated convolution prose and alternating
factorial cumulants. The four Mathlib lines concern Tutte's symmetric difference,
alternating-group cardinality, and a comment about discrete convolution.
The related candidates include degree-4/5/6 symmetrizations, Newton/Vieta
reconstruction, and negative-binomial coefficient formulas; none supplies the
matching-SOS bridge.

Positive controls using the same PCRE word boundaries:

```sh
git grep -n -P '\b(coeff_additiveConvolution|splits_expand_two|nonnegative_roots_of_splits_expand_two)\b' aee1eaff34f997e44f04147cee1010bb482c4c1b -- '*.lean'
git -C .lake/packages/mathlib grep -n -P '\b(IsMatching|coeff_mul|choose_mul_factorial_mul_factorial)\b' -- Mathlib/Combinatorics/SimpleGraph/Matching.lean Mathlib/RingTheory/PowerSeries/Basic.lean Mathlib/Data/Nat/Choose/Basic.lean
```

Controls returned 12 and 63 lines respectively. The relevant root-geometry
APIs and frozen Hermite-Sylvester source were read; the in-flight L1 was not used.
The CAS expression
`(?i)symmetrize|matching.{0,60}(sos|convolution)|(?:匹配.{0,30}平方和|平方和.{0,30}匹配)`
returned 0 lines on the base's complete `Meta/Digestion/atoms` tree.
The all-repository controls above prove that the PCRE search is operational.

Additional pinned-Mathlib searches covered alternating choose/factorial formulas,
`Sym2`, matching cardinalities, `MvPolynomial.esymm`, Vieta, and power-series
coefficient/expansion APIs. `gh search code '"symmetrize_matching_sos" language:Lean'`
returned `[]`; the positive control `"invOneSubPow" language:Lean` returned
three requested results. A broader `"symmetrize" "matching" language:Lean`
query returned seven unrelated candidates. This is an indexed third-party search,
not an exhaustive audit of every external Lean repository.

`dominating_theorem_search: not-found-in-searched-scope`.
Absolute semantic nonexistence under arbitrary renaming or a different encoding
is `ASSUMED-UNVERIFIED`; textual search and an unsuccessful Lean probe do not
prove such a nonexistence theorem.

## Independent Exact Rechecks

`identity5_recheck`: all 63 pairs `h = 0..6, d = 0..8` agree, using integer
factorials and exact arithmetic. This finite experiment is separate from the
all-parameter Lean theorem above.

`calibration_recheck`: unordered matchings were recursively enumerated and the
polynomial coefficients were independently computed from the frozen additive
convolution and reflection definitions using exact rational arithmetic.

| k | Matching count | M_k | (8)_k | I_k |
|---|---:|---:|---:|---:|
| 0 | 1 | 1 | 1 | 1 |
| 1 | 28 | 336 | 8 | 42 |
| 2 | 210 | 27048 | 56 | 483 |
| 3 | 420 | 508704 | 336 | 1514 |
| 4 | 105 | 1018584 | 1680 | 6063/10 |

The coefficient input was
`X^8 - 28 X^7 + 322 X^6 - 1960 X^5 + 6769 X^4 - 13132 X^3 + 13068 X^2 - 5040 X`.
The recheck program and all 63 exact pairs are retained as `recheck.py` and
`recheck.json` in the worker artifact directory.

## Two Combinatorial Attempts

1. Direct step-(3) coefficient extraction:
   `coefficient-identification-1.lean` was run with `make lean`, exit `2`.
   After unfolding the matching polynomial and `MvPolynomial.coeff_sum`,
   one unsolved goal remained: the sum over matchings of the coefficient of
   their edge-square product equals the signed factorial expression in (3).
   No coefficient-to-count identity was established.

2. Marked-edge deletion:
   `coefficient-identification-2.lean` was run with `make lean`, exit `2`.
   The two cardinality reductions elaborate. The sole remaining goal is:

```lean
(Σ M : Matching n (k + 1), {e // e ∈ M.val}) ≃
  ({e : Sym2 (Fin n) // ¬ e.IsDiag} × Matching (n - 2) k)
```

The hypothesis is `2 * (k + 1) <= n`. The missing construction must delete the
selected edge, relabel the complementary root indices, and prove the inverse
operations. Even this unweighted equivalence would not finish the weighted
monomial-fiber identity or step (4). No third combinatorial route was attempted.
The first version of attempt 2 had an additional missing-parentheses error in
a sum; its original diagnostic is preserved as `coefficient-identification-2-initial.log`.
The final attempt-2 log has only the equivalence goal.

## Verified Matching Type And Coefficient Source

`quantification`: the recorded full target has `forall n k`, `2*k <= n`,
and every `r : Fin n -> Real`. It is a `Prop` definition, not a theorem.
The proved coefficient formula retains the same arbitrary `n,k`.
No degree-specific replacement is claimed.

`matching_type`: `Finset (Sym2 (Fin n))`, restricted to exactly `k` edges,
no diagonal edges, and pairwise disjoint endpoint finsets.
`Sym2` identifies the two orientations of an edge; the outer finset identifies
edge order. Vertices are indices, so equal root values remain separate vertices.
There is no centering, root-injectivity, or nonzero-root hypothesis.
`Sym2.lift` is well defined because swapping endpoints preserves the square.

`utility: none`, declaration by declaration:

- `Matching`: a symbolic family of index types, with unbounded `n,k`.
- its `Fintype` instance: standard finite-subtype infrastructure.
- `edgeSquare`: a symbolic polynomial over every commutative ring.
- `matchingSum`: a general finite sum, with no enumeration of parameter values.
- `rootPolynomial`: a symbolic product for an arbitrary root family.
- `MatchingIdentity`: the unbounded target proposition, without a proof assertion.
- `coeff_reflection`: arbitrary-degree coefficient normalization.
- `symmetrize_coefficient`: arbitrary-degree frozen-API normalization.

None is a bounded enumeration, checker, numerical reduction, or certified
numerical instance. The failed coefficient and marked-edge theorem candidates
also concern arbitrary parameters and are not certified results.

`finite_symbol_criterion_check`: the two verified source files have no occurrence
of `FiniteSymbolCriterion`, `FiniteAdditiveSymbol`, or `additive_splits`.
The positive-control search finds all five theorem declarations.
The displayed theorem types introduce no such premise.
No `sorry`, `admit`, custom axiom, `maxHeartbeats`, or `maxRecDepth` occurs
in either verified source file. Failed-probe diagnostic placeholders are not
proof evidence and are not included in the verified files.

`local_make_lean_EXIT: 0` for the final two verified sources, 12580 jobs.
Both coefficient theorem axiom closures are exactly the standard three axioms.
The final build log is `verified-partial-make-lean.log`.
No Lean report was newly generated for these unfrozen probes.

```lean
/- GID: D5/S3/Zeros/Convolution/MatchingSosProbe
   generality: G
   mirror-B: D5/B/S3/Zeros/Convolution/MatchingSosProbe
   mirror-E: none(waiver:symbolic-matching-identity)
   anchors: []
   utility: none
   digest: All-degree matching sum of squares probe for symmetrization. -/

import D5.S3.Zeros.Convolution.FiniteConvolutionCoefficients
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
`Matching` and its finite instance describe arbitrary finite index matchings.
`edgeSquare`, `matchingSum`, and `rootPolynomial` are symbolic algebraic definitions.
`MatchingIdentity` records the unproved all-degree target as a proposition.
`coeff_reflection` and `symmetrize_coefficient` normalize the existing definitions.
None is a bounded enumeration, checker, numerical reduction, or certified instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Convolution.MatchingSosProbe

open Polynomial
open scoped BigOperators
open D5.S3.Zeros.Convolution.FiniteFreeCommutatorDegreeFour
open D5.S3.Zeros.Convolution.FiniteConvolutionCoefficients

/-- Unordered, loop-free, vertex-disjoint edges on root indices. -/
def Matching (n k : ℕ) :=
  { M : Finset (Sym2 (Fin n)) // M.card = k ∧
    (∀ e ∈ M, ¬ e.IsDiag) ∧
    (M : Set (Sym2 (Fin n))).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) }

noncomputable instance (n k : ℕ) : Fintype (Matching n k) := by
  classical
  unfold Matching
  exact Fintype.ofFinite _

/-- Symmetry makes this a well-defined square on unordered pairs. -/
def edgeSquare {n : ℕ} {R : Type*} [CommRing R] (r : Fin n → R) : Sym2 (Fin n) → R :=
  Sym2.lift ⟨fun i j => (r i - r j) ^ 2, by intro i j; ring⟩

def matchingSum {n : ℕ} {R : Type*} [CommRing R] (r : Fin n → R) (k : ℕ) : R :=
  ∑ M : Matching n k, ∏ e ∈ M.val, edgeSquare r e

def rootPolynomial {n : ℕ} (r : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (X - C (r i))

/-- The full target, recorded as a proposition and not asserted as a theorem. -/
def MatchingIdentity : Prop := ∀ (n k : ℕ), 2 * k ≤ n → ∀ (r : Fin n → ℝ),
  (-1 : ℝ) ^ k * (symmetrize n (rootPolynomial r)).coeff (n - 2 * k) =
    matchingSum r k / (n.descFactorial k : ℝ)

/-- Reflection multiplies the descending coefficient by its alternating sign. -/
theorem coeff_reflection (n j : ℕ) (hj : j ≤ n) (p : ℝ[X]) :
    (dilate n (-1) p).coeff (n - j) = (-1 : ℝ) ^ j * p.coeff (n - j) := by
  simp only [dilate, coeff_C_mul, comp_C_mul_X_coeff, inv_neg, inv_one]
  have hn : (-1 : ℝ) ^ n = (-1) ^ j * (-1) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have hs : (-1 : ℝ) ^ (n - j) * (-1) ^ (n - j) = 1 := by rw [← mul_pow]; norm_num
  rw [hn]
  calc
    _ = (-1 : ℝ) ^ j * p.coeff (n - j) * ((-1) ^ (n - j) * (-1) ^ (n - j)) := by ring
    _ = _ := by rw [hs, mul_one]

/-- Corrected step (1), derived from the frozen definition at arbitrary degree. -/
theorem symmetrize_coefficient (n k : ℕ) (hk : 2 * k ≤ n) (p : ℝ[X]) :
    (-1 : ℝ) ^ k * (symmetrize n p).coeff (n - 2 * k) =
      (-1 : ℝ) ^ k * (n.descFactorial (2 * k) : ℝ) *
        ∑ i ∈ Finset.range (2 * k + 1),
          (-1 : ℝ) ^ i * elementaryCoeff n p i * elementaryCoeff n p (2 * k - i) /
            ((n.descFactorial i : ℝ) * (n.descFactorial (2 * k - i) : ℝ)) := by
  rw [symmetrize, coeff_additiveConvolution n p _ (2 * k) hk, mul_assoc]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_reflection n (2 * k - i) (by omega)]
  unfold elementaryCoeff
  have hs : (-1 : ℝ) ^ i * (-1) ^ i = 1 := by rw [← mul_pow]; norm_num
  congr 1
  calc
    _ = ((-1 : ℝ) ^ i * (-1) ^ i) *
        (p.coeff (n - i) * ((-1) ^ (2 * k - i) * p.coeff (n - (2 * k - i)))) := by
          rw [hs, one_mul]
    _ = _ := by ring

#print axioms coeff_reflection
#print axioms symmetrize_coefficient

end D5.S3.Zeros.Convolution.MatchingSosProbe
```

## Artifact Location And Remaining Unknowns

Worker-owned artifacts are in:
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/matching-sos-0908/attempt-1`.

`assumed_unverified`: absolute no-equivalent-theorem claim beyond the searched
syntax and candidates; the unproved equation (2); the monomial-fiber counting
bijection and step (4); all-degree H_1 removal and equivalence (7); independent
review and peak RSS. No positive-semidefiniteness claim for H_0(R) is made.
The machine-verifiable statements above are limited to the two archived sources.

## Report Admission Check

PR #6409's admission job in run `34212840963` rejected the initial report location:
`SL-003 docs/reports: directory contains 25 files (admission limit 24, repository tolerance 48)`.
The report was moved into `docs/reports/convolution/` to satisfy the directory
capacity rule. No threshold, constant, or mathematical source was changed.
