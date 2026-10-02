/- GID: D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.claim; result=D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.result; claim=D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.claim
   digest: A conjugate pair in the unit disk gives Schur ratio 73/60, refuting Conjecture 6.2. -/

/-
proof_shape: result: bind-only (finite tableau enumeration and rational normalization)
escape_witness: none
admission_basis: open-problem-resolution (#11514; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation

noncomputable section

open Classical in
/-- Definition 6.1: nonreal entries have a conjugate entry, and every real number occurs
an even number of times. The first condition is membership, without a multiplicity condition. -/
def selfConjugate {n : ℕ} (z : Fin n → ℂ) : Prop :=
  (∀ i, (z i).im ≠ 0 → ∃ j, z j = conj (z i)) ∧
    (∀ x : ℝ, Even ((Finset.univ.filter fun i => z i = (x : ℂ)).card))

/-- The elementary symmetric function: each strictly increasing index tuple is represented
once by its set of indices. -/
def e {n : ℕ} (d : ℕ) (z : Fin n → ℂ) : ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard d, ∏ i ∈ s, z i

/-- The complete homogeneous symmetric function. A multiset of cardinality `d` in the
ordered alphabet `Fin n` represents exactly one weakly increasing index tuple. -/
def h {n : ℕ} (d : ℕ) (z : Fin n → ℂ) : ℂ :=
  ∑ s : Sym (Fin n) d, (s.val.map z).prod

open Classical in
/-- The Schur function of the hook `(a + 1, 1^b)`, summed over semistandard tableaux.
The corner is `c`; the arm is the unique sorted tuple of the multiset `arm`, all at least
`c`; the leg is the unique strictly increasing tuple of the set `leg`, all greater than
`c`. Grouping the tableau monomials by weight gives the source's Kostka expansion. -/
def schurHook {n : ℕ} (a b : ℕ) (z : Fin n → ℂ) : ℂ :=
  ∑ c : Fin n, ∑ arm : Sym (Fin n) a,
    ∑ leg ∈ (Finset.univ : Finset (Fin n)).powersetCard b,
      if (∀ i ∈ arm.val, c ≤ i) ∧ (∀ j ∈ leg, c < j)
      then z c * (arm.val.map z).prod * (∏ j ∈ leg, z j) else 0

/-- The rational function displayed before Corollary 6.1, with complex division. -/
def Q (t n k : ℕ) (ζ : Fin n → ℂ) : ℂ :=
  ∑ d ∈ Finset.range (t - n + 1),
    (-1 : ℂ) ^ d * ((t.choose (n + d) : ℂ) * schurHook d (n - k - 1) ζ) /
      ((t.choose n : ℂ) * e (n - k) ζ)

/-- Both clauses of Conjecture 6.2 of Ostrovskii and Shcherbakov, arXiv:2508.13554v2,
page 15. The closed disk is expressed by the complex norm and the nonnegative orthant
by nonnegative real parts. -/
def claim : Prop :=
  ∀ k n t : ℕ, k < n → n ≤ t → ∀ z : Fin n → ℂ,
    selfConjugate z → (∀ i, ‖z i‖ ≤ 1) →
      ‖Q t n k (z + 1)‖ ≤ 1 ∧
        ((∀ i, 0 ≤ (z i).re) →
          ‖schurHook (t - n) (n - k - 1) z‖ ≤ (t.choose n : ℝ) * ‖e (n - k) z‖)

/-- The conjugate pair `-9/10 ± (2/5) i` is in the unit disk, but its shifted Schur
ratio at `(t,n,k) = (3,2,1)` is `73/60 > 1`. -/
theorem result : ¬ claim := by
  classical
  let z : Fin 2 → ℂ := ![-9 / 10 + (2 / 5) * Complex.I, -9 / 10 - (2 / 5) * Complex.I]
  have hsc : selfConjugate z := by
    constructor
    · intro i _
      fin_cases i
      · refine ⟨1, ?_⟩
        apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> norm_num [z]
      · refine ⟨0, ?_⟩
        apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> norm_num [z]
    · intro x
      have hempty : (Finset.univ.filter fun i => z i = (x : ℂ)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have him := congrArg Complex.im (Finset.mem_filter.mp hi).2
        fin_cases i <;> norm_num [z] at him
      rw [hempty]
      exact ⟨0, rfl⟩
  have hdisk : ∀ i, ‖z i‖ ≤ 1 := by
    intro i
    have hs : Complex.normSq (z i) = 97 / 100 := by
      fin_cases i <;> norm_num [z, Complex.normSq_apply]
    have hs' : ‖z i‖ ^ 2 = 97 / 100 := (Complex.sq_norm _).trans hs
    nlinarith [norm_nonneg (z i)]
  have he : e 1 (z + 1) = (1 / 5 : ℂ) := by
    simp [e, Finset.powersetCard_one, Fin.sum_univ_two, z]
    ring
  have hs0 : schurHook 0 0 (z + 1) = (1 / 5 : ℂ) := by
    simp [schurHook, Sym.eq_nil_of_card_zero, Sym.coe_nil, Fin.sum_univ_two, z]
    ring
  have hs1 : schurHook 1 0 (z + 1) = (-13 / 100 : ℂ) := by
    unfold schurHook
    simp only [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty, mul_one]
    simp_rw [← Equiv.sum_comp (Sym.oneEquiv : Fin 2 ≃ Sym (Fin 2) 1)]
    norm_num [Sym.oneEquiv_apply, Fin.sum_univ_two, z]
    ring_nf
    norm_num [Complex.I_sq]
  have hQ : Q 3 2 1 (z + 1) = (73 / 60 : ℂ) := by
    norm_num [Q, Finset.sum_range_succ, hs0, hs1, he]
  intro hc
  have hbound := (hc 1 2 3 (by decide) (by decide) z hsc hdisk).1
  rw [hQ] at hbound
  norm_num at hbound

end

end D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
