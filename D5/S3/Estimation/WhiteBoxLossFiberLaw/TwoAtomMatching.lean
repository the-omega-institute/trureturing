/- GID: D5/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching
   generality: G
   mirror-B: D5/B/S3/Estimation/WhiteBoxLossFiberLaw/TwoAtomMatching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square completion and radial lower bounds for nonnegative two-atom codes. -/

/-
Library-search audit trail:
* The pinned Mathlib inner-product search found `norm_sub_sq`,
  `real_inner_self_eq_norm_sq`, `real_inner_le_norm`, and finite-sum inner-product
  distribution, but no nonnegative two-atom coding or white-box loss declaration.
* A repository search over D5 found no declaration of the two-atom code energy,
  its radial lower bound, or its square-completion identity. The present identities
  therefore establish the reusable algebraic core needed by the quantitative matching
  theorem; the infimum-to-dictionary matching argument remains open.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching

open scoped BigOperators RealInnerProductSpace

abbrev AtomIndex := Fin 2

def UnitDictionary (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  {D : AtomIndex → E // ∀ i, ‖D i‖ = 1}

def FeasibleCode (c : AtomIndex → ℝ) : Prop := ∀ i, 0 ≤ c i

def atomCombination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : UnitDictionary E) (c : AtomIndex → ℝ) : E := ∑ i, c i • D.1 i

def codeEnergy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : ℝ) (x : E) (D : UnitDictionary E) (c : AtomIndex → ℝ) : ℝ :=
  ‖x - atomCombination D c‖ ^ 2 / 2 + lam * ∑ i, c i

def codeCost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : ℝ) (x : E) (D : UnitDictionary E) : ℝ :=
  sInf {z : ℝ | ∃ c, FeasibleCode c ∧ codeEnergy lam x D c = z}

/- The square-completion identity is the active algebraic relation used below. -/
theorem code_energy_excess_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam n : ℝ) (e : E) (D : UnitDictionary E) (c : AtomIndex → ℝ)
    (he : ‖e‖ = 1) :
    codeEnergy lam (n • e) D c - (lam * n - lam ^ 2 / 2) =
      ‖(n - lam) • e - atomCombination D c‖ ^ 2 / 2 +
        lam * ∑ i, c i * (1 - inner ℝ e (D.1 i)) := by
  unfold codeEnergy atomCombination
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp [norm_smul, he, real_inner_smul_left, inner_add_right, inner_smul_right,
    sum_inner, Fin.sum_univ_two]
  ring

/- Every feasible code pays at least the radial amount for a unit signal direction.
This is the pointwise inequality from which the value-function lower bound is
obtained by taking an infimum. -/
theorem feasible_code_energy_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam n : ℝ) (e : E) (D : UnitDictionary E) (c : AtomIndex → ℝ)
    (he : ‖e‖ = 1) (hlam : 0 ≤ lam) (hc : FeasibleCode c) :
    lam * n - lam ^ 2 / 2 ≤ codeEnergy lam (n • e) D c := by
  have hres : 0 ≤ ‖(n - lam) • e - atomCombination D c‖ ^ 2 / 2 := by positivity
  have hcorr : 0 ≤ lam * ∑ i, c i * (1 - inner ℝ e (D.1 i)) := by
    have hinner : ∀ i, inner ℝ e (D.1 i) ≤ 1 := by
      intro i
      simpa [he, D.2 i] using real_inner_le_norm e (D.1 i)
    have hterms : ∀ i, 0 ≤ c i * (1 - inner ℝ e (D.1 i)) := by
      intro i
      exact mul_nonneg (hc i) (sub_nonneg.mpr (hinner i))
    exact mul_nonneg hlam (Finset.sum_nonneg (fun i _ => hterms i))
  have hdiff : 0 ≤ codeEnergy lam (n • e) D c - (lam * n - lam ^ 2 / 2) := by
    rw [code_energy_excess_eq lam n e D c he]
    exact add_nonneg hres hcorr
  linarith

/- Taking the infimum preserves the pointwise radial floor. The zero code supplies
the nonempty side condition; no attainment or uniqueness is asserted here. -/
theorem code_cost_radial_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam n : ℝ) (e : E) (D : UnitDictionary E)
    (he : ‖e‖ = 1) (hlam : 0 ≤ lam) :
    lam * n - lam ^ 2 / 2 ≤ codeCost lam (n • e) D := by
  unfold codeCost
  apply le_csInf
    (show ({z : ℝ | ∃ c, FeasibleCode c ∧ codeEnergy lam (n • e) D c = z}).Nonempty from
      let z0 : AtomIndex → ℝ := fun _ => 0
      ⟨codeEnergy lam (n • e) D z0, ⟨z0, (fun _ => le_rfl), rfl⟩⟩)
  rintro z ⟨c, hc, rfl⟩
  exact feasible_code_energy_lower_bound lam n e D c he hlam hc

/- Once the two target directions are separated, witnesses for both directions
must occupy different slots. This is the finite matching step used after the
quantitative near-equality estimates. -/
theorem two_slot_matching_from_separate_witnesses
    {E : Type*} [PseudoMetricSpace E]
    (D : AtomIndex → E) (u w : E) (δ : ℝ)
    (hsep : 2 * δ ≤ dist u w)
    (hu : ∃ i, dist (D i) u < δ) (hw : ∃ i, dist (D i) w < δ) :
    (dist (D 0) u < δ ∧ dist (D 1) w < δ) ∨
      (dist (D 0) w < δ ∧ dist (D 1) u < δ) := by
  rcases hu with ⟨i, hi⟩
  rcases hw with ⟨j, hj⟩
  fin_cases i <;> fin_cases j
  · exfalso
    have htri := dist_triangle u (D 0) w
    rw [dist_comm u (D 0)] at htri
    have hi' : dist (D 0) u < δ := by simpa using hi
    have hj' : dist (D 0) w < δ := by simpa using hj
    linarith
  · exact Or.inl ⟨hi, hj⟩
  · exact Or.inr ⟨hj, hi⟩
  · exfalso
    have htri := dist_triangle u (D 1) w
    rw [dist_comm u (D 1)] at htri
    have hi' : dist (D 1) u < δ := by simpa using hi
    have hj' : dist (D 1) w < δ := by simpa using hj
    linarith

end D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
