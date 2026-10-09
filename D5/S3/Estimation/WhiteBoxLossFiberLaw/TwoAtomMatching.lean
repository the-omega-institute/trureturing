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

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

namespace D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching

open scoped BigOperators RealInnerProductSpace

local notation "AtomIndex" => Fin 2

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
    Fin.sum_univ_two]
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

/-- The explicit energy gap for detecting a nearby atom. -/
def alignmentGap (lam n δ : ℝ) : ℝ :=
  min ((n - lam) ^ 2 / 8) (lam * (n - lam) * δ ^ 2 / 4)

private theorem alignment_gap_pos (lam n δ : ℝ)
    (hlam : 0 < lam) (hn : lam < n) (hδ : 0 < δ) :
    0 < alignmentGap lam n δ := by
  unfold alignmentGap
  apply lt_min <;> positivity

/-- A code whose excess is below both explicit thresholds has a nearby atom. -/
private theorem energy_near_radial_has_atom
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam n δ : ℝ) (e : E) (D : UnitDictionary E) (c : AtomIndex → ℝ)
    (he : ‖e‖ = 1) (hlam : 0 < lam) (hn : lam < n) (hδ : 0 < δ)
    (hc : FeasibleCode c)
    (henergy : codeEnergy lam (n • e) D c <
      lam * n - lam ^ 2 / 2 + alignmentGap lam n δ) :
    ∃ i, dist (D.1 i) e < δ := by
  have hcomplete := code_energy_excess_eq lam n e D c he
  have hmass : ‖atomCombination D c‖ ≤ ∑ i, c i := by
    calc
      ‖atomCombination D c‖ ≤ ∑ i, ‖c i • D.1 i‖ := norm_sum_le _ _
      _ = ∑ i, c i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_smul, D.2 i, mul_one, Real.norm_eq_abs, abs_of_nonneg (hc i)]
  have hdef : 0 ≤ ∑ i, c i * (1 - inner ℝ e (D.1 i)) := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hc i)
    have h := real_inner_le_norm e (D.1 i)
    rw [he, D.2 i, mul_one] at h
    linarith
  have hpen := mul_nonneg hlam.le hdef
  have hs : (n - lam) / 2 < ∑ i, c i := by
    by_contra hs
    have hs' := le_of_not_gt hs
    have hrnorm : ‖(n - lam) • e‖ = n - lam := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hn)]
    have hrev := norm_sub_norm_le ((n - lam) • e) (atomCombination D c)
    rw [hrnorm] at hrev
    have hres : (n - lam) / 2 ≤ ‖(n - lam) • e - atomCombination D c‖ := by
      linarith
    have hgap := min_le_left ((n - lam) ^ 2 / 8) (lam * (n - lam) * δ ^ 2 / 4)
    change alignmentGap lam n δ ≤ (n - lam) ^ 2 / 8 at hgap
    have hnonneg := norm_nonneg ((n - lam) • e - atomCombination D c)
    nlinarith [sq_nonneg (‖(n - lam) • e - atomCombination D c‖ - (n - lam) / 2)]
  by_contra hnear
  push Not at hnear
  have hcorr : ∀ i, δ ^ 2 / 2 ≤ 1 - inner ℝ e (D.1 i) := by
    intro i
    have hd := hnear i
    rw [dist_eq_norm] at hd
    have hid := norm_sub_sq_real (D.1 i) e
    rw [D.2 i, he, real_inner_comm] at hid
    have hnn := norm_nonneg (D.1 i - e)
    nlinarith
  have hsum : (∑ i, c i) * (δ ^ 2 / 2) ≤
      ∑ i, c i * (1 - inner ℝ e (D.1 i)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcorr i) (hc i))
  have hsum' := mul_le_mul_of_nonneg_left hsum hlam.le
  have hstrict : lam * ((n - lam) / 2 * (δ ^ 2 / 2)) <
      lam * ((∑ i, c i) * (δ ^ 2 / 2)) := by
    apply mul_lt_mul_of_pos_left _ hlam
    exact mul_lt_mul_of_pos_right hs (by positivity)
  have hgap := min_le_right ((n - lam) ^ 2 / 8) (lam * (n - lam) * δ ^ 2 / 4)
  change alignmentGap lam n δ ≤ lam * (n - lam) * δ ^ 2 / 4 at hgap
  have hres := sq_nonneg ‖(n - lam) • e - atomCombination D c‖
  nlinarith

/-- A strict near-equality bound for the infimal cost forces one atom into the
specified direction ball, without any attainment hypothesis. -/
private theorem cost_near_radial_has_atom
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam n δ : ℝ) (e : E) (D : UnitDictionary E)
    (he : ‖e‖ = 1) (hlam : 0 < lam) (hn : lam < n) (hδ : 0 < δ)
    (hcost : codeCost lam (n • e) D <
      lam * n - lam ^ 2 / 2 + alignmentGap lam n δ) :
    ∃ i, dist (D.1 i) e < δ := by
  have hne : ({z : ℝ | ∃ c, FeasibleCode c ∧ codeEnergy lam (n • e) D c = z}).Nonempty :=
    ⟨codeEnergy lam (n • e) D (fun _ => 0), (fun _ => 0), (fun _ => le_rfl), rfl⟩
  obtain ⟨z, ⟨c, hc, rfl⟩, hz⟩ := exists_lt_of_csInf_lt hne hcost
  exact energy_near_radial_has_atom lam n δ e D c he hlam hn hδ hc hz

/-- Two near-radial samples force simultaneous matching by the two slots of one
actual dictionary. The gap is explicit and independent of the dictionary. -/
theorem quantitative_two_slot_matching
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam n m a b δ : ℝ) (u w : E) (D : UnitDictionary E)
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hlam : 0 < lam)
    (hn : lam < n) (hm : lam < m) (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 < δ) (hsep : 2 * δ ≤ dist u w)
    (hcost : a * codeCost lam (n • u) D + b * codeCost lam (m • w) D <
      a * (lam * n - lam ^ 2 / 2) + b * (lam * m - lam ^ 2 / 2) +
        min (a * alignmentGap lam n δ) (b * alignmentGap lam m δ)) :
    (dist (D.1 0) u < δ ∧ dist (D.1 1) w < δ) ∨
      (dist (D.1 0) w < δ ∧ dist (D.1 1) u < δ) := by
  have hlowu := code_cost_radial_lower_bound lam n u D hu hlam.le
  have hloww := code_cost_radial_lower_bound lam m w D hw hlam.le
  have hupperu : codeCost lam (n • u) D <
      lam * n - lam ^ 2 / 2 + alignmentGap lam n δ := by
    have hgap := min_le_left (a * alignmentGap lam n δ) (b * alignmentGap lam m δ)
    have hweight := mul_le_mul_of_nonneg_left hloww hb.le
    nlinarith
  have hupperw : codeCost lam (m • w) D <
      lam * m - lam ^ 2 / 2 + alignmentGap lam m δ := by
    have hgap := min_le_right (a * alignmentGap lam n δ) (b * alignmentGap lam m δ)
    have hweight := mul_le_mul_of_nonneg_left hlowu ha.le
    nlinarith
  exact two_slot_matching_from_separate_witnesses D.1 u w δ hsep
    (cost_near_radial_has_atom lam n δ u D hu hlam hn hδ hupperu)
    (cost_near_radial_has_atom lam m δ w D hw hlam hm hδ hupperw)

/-- Positive gap attached to the simultaneous matching bound. -/
private theorem matching_gap_pos (lam n m a b δ : ℝ)
    (hlam : 0 < lam) (hn : lam < n) (hm : lam < m)
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) :
    0 < min (a * alignmentGap lam n δ) (b * alignmentGap lam m δ) :=
  lt_min (mul_pos ha (alignment_gap_pos lam n δ hlam hn hδ))
    (mul_pos hb (alignment_gap_pos lam m δ hlam hm hδ))

/-- Equality in the actual infimal radial bound holds precisely when an atom
is aligned with the signal direction. -/
theorem code_cost_eq_radial_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam n : ℝ) (e : E) (D : UnitDictionary E)
    (he : ‖e‖ = 1) (hlam : 0 < lam) (hn : lam < n) :
    codeCost lam (n • e) D = lam * n - lam ^ 2 / 2 ↔ ∃ i, D.1 i = e := by
  constructor
  · intro heq
    by_contra hnone
    push Not at hnone
    have h0 : 0 < dist (D.1 0) e := dist_pos.mpr (hnone 0)
    have h1 : 0 < dist (D.1 1) e := dist_pos.mpr (hnone 1)
    let δ := min (dist (D.1 0) e) (dist (D.1 1) e)
    have hd : 0 < δ := lt_min h0 h1
    have hcost : codeCost lam (n • e) D <
        lam * n - lam ^ 2 / 2 + alignmentGap lam n δ := by
      rw [heq]
      linarith [alignment_gap_pos lam n δ hlam hn hd]
    obtain ⟨i, hi⟩ := cost_near_radial_has_atom lam n δ e D he hlam hn hd hcost
    fin_cases i
    · have hh : dist (D.1 0) e < δ := by simpa using hi
      exact (not_lt_of_ge (min_le_left (dist (D.1 0) e) (dist (D.1 1) e))) hh
    · have hh : dist (D.1 1) e < δ := by simpa using hi
      exact (not_lt_of_ge (min_le_right (dist (D.1 0) e) (dist (D.1 1) e))) hh
  · rintro ⟨i, hi⟩
    have lower := code_cost_radial_lower_bound lam n e D he hlam.le
    apply le_antisymm _ lower
    unfold codeCost
    have hbdd : BddBelow {z : ℝ | ∃ c, FeasibleCode c ∧ codeEnergy lam (n • e) D c = z} := by
      refine ⟨lam * n - lam ^ 2 / 2, ?_⟩
      rintro z ⟨c, hc, rfl⟩
      exact feasible_code_energy_lower_bound lam n e D c he hlam.le hc
    let c : AtomIndex → ℝ := fun j => if j = i then n - lam else 0
    have hc : FeasibleCode c := by
      intro j
      dsimp [c]
      split_ifs <;> linarith
    have hcomb : atomCombination D c = (n - lam) • e := by
      fin_cases i <;> simp [atomCombination, c, Fin.sum_univ_two]
      all_goals exact congrArg (fun z => (n - lam) • z) hi
    have hsum : (∑ j, c j) = n - lam := by
      fin_cases i <;> simp [c, Fin.sum_univ_two]
    have henergy : codeEnergy lam (n • e) D c = lam * n - lam ^ 2 / 2 := by
      unfold codeEnergy
      rw [hcomb, hsum]
      have hsub : n • e - (n - lam) • e = lam • e := by module
      rw [hsub, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hlam]
      ring
    exact csInf_le hbdd ⟨c, hc, henergy⟩

/-- The normalized sum of two orthogonal unit directions. -/
def bisector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : E := (Real.sqrt 2)⁻¹ • (u + v)

private theorem bisector_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : inner ℝ u v = 0) :
    ‖bisector u v‖ = 1 ∧ (Real.sqrt 2) • bisector u v = u + v := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : ‖u + v‖ = Real.sqrt 2 := by
    apply (sq_eq_sq₀ (norm_nonneg _) hsqrt.le).mp
    rw [norm_add_sq_real, hu, hv, horth, hsq]
    norm_num
  constructor
  · rw [bisector, norm_smul, hsum, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt)]
    exact inv_mul_cancel₀ hsqrt.ne'
  · rw [bisector, smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]

/-- The weighted objective at perturbation weight t. -/
def jointCost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam a b t : ℝ) (u v : E) (D : UnitDictionary E) : ℝ :=
  a * codeCost lam u D + b * codeCost lam (u + v) D + t * codeCost lam v D

/-- The radial baseline for the two positive-weight samples. -/
def baseline (lam a b : ℝ) : ℝ :=
  a * (lam - lam ^ 2 / 2) + b * (Real.sqrt 2 * lam - lam ^ 2 / 2)

/-- An explicit dictionary-independent near-equality threshold. -/
def matchingGap (lam a b δ : ℝ) : ℝ :=
  min (a * alignmentGap lam 1 δ) (b * alignmentGap lam (Real.sqrt 2) δ)

/-- Quantitative two-slot matching for orthogonal unit samples. This statement
includes all ordered unit dictionaries, including repeated and antipodal atoms. -/
theorem whitebox_quantitative_matching
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam a b δ : ℝ) (u v : E) (D : UnitDictionary E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hsep : δ < ‖u - bisector u v‖ / 2) :
    0 < matchingGap lam a b δ ∧
    (jointCost lam a b 0 u v D < baseline lam a b + matchingGap lam a b δ →
      (dist (D.1 0) u < δ ∧ dist (D.1 1) (bisector u v) < δ) ∨
        (dist (D.1 0) (bisector u v) < δ ∧ dist (D.1 1) u < δ)) := by
  have hsqrt : 1 < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg 2
    nlinarith
  have hinv : 1 / Real.sqrt 2 < 1 := (div_lt_one (by linarith)).mpr hsqrt
  have hn : lam < 1 := hsmall.trans hinv
  have hm : lam < Real.sqrt 2 := hn.trans hsqrt
  obtain ⟨hw, hsum⟩ := bisector_geometry u v hu hv horth
  refine ⟨matching_gap_pos lam 1 (Real.sqrt 2) a b δ hlam hn hm ha hb hδ, ?_⟩
  intro hcost
  apply quantitative_two_slot_matching lam 1 (Real.sqrt 2) a b δ u (bisector u v) D
    hu hw hlam hn hm ha hb hδ
  · rw [dist_eq_norm]
    linarith
  · simpa [jointCost, baseline, matchingGap, hsum, mul_comm] using hcost

private theorem code_cost_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam : ℝ) (x : E) (D : UnitDictionary E) (hlam : 0 ≤ lam) :
    0 ≤ codeCost lam x D ∧ codeCost lam x D ≤ ‖x‖ ^ 2 / 2 := by
  have hnonneg : ∀ c, FeasibleCode c → 0 ≤ codeEnergy lam x D c := by
    intro c hc
    unfold codeEnergy
    exact add_nonneg (by positivity)
      (mul_nonneg hlam (Finset.sum_nonneg (fun i _ => hc i)))
  have hne : ({z : ℝ | ∃ c, FeasibleCode c ∧ codeEnergy lam x D c = z}).Nonempty :=
    ⟨codeEnergy lam x D (fun _ => 0), (fun _ => 0), (fun _ => le_rfl), rfl⟩
  have hfloor : 0 ≤ codeCost lam x D := by
    apply le_csInf hne
    rintro z ⟨c, hc, rfl⟩
    exact hnonneg c hc
  refine ⟨hfloor, ?_⟩
  have hbdd : BddBelow {z : ℝ | ∃ c, FeasibleCode c ∧ codeEnergy lam x D c = z} := by
    refine ⟨0, ?_⟩
    rintro z ⟨c, hc, rfl⟩
    exact hnonneg c hc
  apply csInf_le hbdd
  refine ⟨(fun _ => 0), (fun _ => le_rfl), ?_⟩
  simp [codeEnergy, atomCombination]

/-- The objective changes by at most t/2 when a unit sample is assigned weight t. -/
theorem perturbation_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam a b t : ℝ) (u v : E) (D : UnitDictionary E)
    (hlam : 0 ≤ lam) (hv : ‖v‖ = 1) (ht : 0 ≤ t) :
    jointCost lam a b 0 u v D ≤ jointCost lam a b t u v D ∧
      jointCost lam a b t u v D ≤ jointCost lam a b 0 u v D + t / 2 := by
  obtain ⟨hlow, hhigh⟩ := code_cost_bounds lam v D hlam
  rw [hv] at hhigh
  have hlow' := mul_nonneg ht hlow
  have hhigh' := mul_le_mul_of_nonneg_left hhigh ht
  simp only [jointCost, zero_mul, add_zero]
  constructor <;> nlinarith

/-- The ordered baseline dictionary. -/
def canonicalDictionary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) : UnitDictionary E :=
  ⟨![u, w], by intro i; fin_cases i <;> assumption⟩

private theorem bisector_ne_left
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hv : ‖v‖ = 1) (horth : inner ℝ u v = 0) :
    bisector u v ≠ u := by
  intro heq
  have hinner := congrArg (fun x => inner ℝ v x) heq
  have hreverse : inner ℝ v u = 0 := by rw [real_inner_comm]; exact horth
  simp [bisector, inner_smul_right, inner_add_right, hreverse,
    real_inner_self_eq_norm_sq, hv] at hinner

private theorem whitebox_parameter_bounds (lam : ℝ)
    (hsmall : lam < 1 / Real.sqrt 2) : lam < 1 ∧ lam < Real.sqrt 2 := by
  have hsqrt : 1 < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg 2
    nlinarith
  have hinv : 1 / Real.sqrt 2 < 1 := (div_lt_one (by linarith)).mpr hsqrt
  exact ⟨hsmall.trans hinv, (hsmall.trans hinv).trans hsqrt⟩

/-- The unperturbed objective reaches its baseline precisely at the two ordered
canonical dictionaries. -/
theorem zero_global_minima
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam a b : ℝ) (u v : E) (D : UnitDictionary E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (ha : 0 < a) (hb : 0 < b) :
    baseline lam a b ≤ jointCost lam a b 0 u v D ∧
      (jointCost lam a b 0 u v D = baseline lam a b ↔
        (D.1 0 = u ∧ D.1 1 = bisector u v) ∨
          (D.1 0 = bisector u v ∧ D.1 1 = u)) := by
  obtain ⟨hw, hsum⟩ := bisector_geometry u v hu hv horth
  obtain ⟨hn, hm⟩ := whitebox_parameter_bounds lam hsmall
  have hlowu : lam - lam ^ 2 / 2 ≤ codeCost lam u D := by
    simpa using code_cost_radial_lower_bound lam 1 u D hu hlam.le
  have hloww : Real.sqrt 2 * lam - lam ^ 2 / 2 ≤ codeCost lam (u + v) D := by
    simpa [hsum, mul_comm] using
      code_cost_radial_lower_bound lam (Real.sqrt 2) (bisector u v) D hw hlam.le
  have hweightu := mul_le_mul_of_nonneg_left hlowu ha.le
  have hweightw := mul_le_mul_of_nonneg_left hloww hb.le
  refine ⟨by dsimp [jointCost, baseline]; nlinarith, ?_⟩
  constructor
  · intro heq
    have hequ : codeCost lam u D = lam - lam ^ 2 / 2 := by
      dsimp [jointCost, baseline] at heq
      nlinarith
    have heqw : codeCost lam (u + v) D = Real.sqrt 2 * lam - lam ^ 2 / 2 := by
      dsimp [jointCost, baseline] at heq
      nlinarith
    have huatom : ∃ i, D.1 i = u :=
      (code_cost_eq_radial_iff lam 1 u D hu hlam hn).mp (by simpa using hequ)
    have hwatom : ∃ i, D.1 i = bisector u v :=
      (code_cost_eq_radial_iff lam (Real.sqrt 2) (bisector u v) D hw hlam hm).mp
        (by simpa [hsum, mul_comm] using heqw)
    obtain ⟨i, hi⟩ := huatom
    obtain ⟨j, hj⟩ := hwatom
    have hne := bisector_ne_left u v hv horth
    fin_cases i <;> fin_cases j
    · exact (hne (hj.symm.trans hi)).elim
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr ⟨hj, hi⟩
    · exact (hne (hj.symm.trans hi)).elim
  · intro hmatch
    have huatom : ∃ i, D.1 i = u := by
      rcases hmatch with h | h
      · exact ⟨0, h.1⟩
      · exact ⟨1, h.2⟩
    have hwatom : ∃ i, D.1 i = bisector u v := by
      rcases hmatch with h | h
      · exact ⟨1, h.2⟩
      · exact ⟨0, h.1⟩
    have hequ := (code_cost_eq_radial_iff lam 1 u D hu hlam hn).mpr huatom
    have heqw :=
      (code_cost_eq_radial_iff lam (Real.sqrt 2) (bisector u v) D hw hlam hm).mpr hwatom
    simp only [one_smul, mul_one] at hequ
    rw [hsum] at heqw
    simp [jointCost, baseline, hequ, heqw, mul_comm]

/-- Every global minimizer of a sufficiently small positive perturbation lies
near one of the two canonical ordered dictionaries. No compactness assumption
or minimizer-existence hypothesis is used. -/
theorem small_positive_minimizers_localize
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (lam a b : ℝ) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (horth : inner ℝ u v = 0)
    (hlam : 0 < lam) (hsmall : lam < 1 / Real.sqrt 2)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1) :
    ∀ δ > 0, ∃ η > 0, ∀ t, 0 < t → t < η →
      ∀ D : UnitDictionary E,
      (∀ D' : UnitDictionary E,
        jointCost lam a b t u v D ≤ jointCost lam a b t u v D') →
      (dist (D.1 0) u < δ ∧ dist (D.1 1) (bisector u v) < δ) ∨
        (dist (D.1 0) (bisector u v) < δ ∧ dist (D.1 1) u < δ) := by
  intro δ hδ
  obtain ⟨hw, hsum⟩ := bisector_geometry u v hu hv horth
  let D0 := canonicalDictionary u (bisector u v) hu hw
  have hbase : jointCost lam a b 0 u v D0 = baseline lam a b :=
    (zero_global_minima lam a b u v D0 hu hv horth hlam hsmall ha hb).2.mpr
      (Or.inl ⟨rfl, rfl⟩)
  have hdist : 0 < ‖u - bisector u v‖ := by
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr (bisector_ne_left u v hv horth).symm
  let ε := min δ (‖u - bisector u v‖ / 4)
  have hε : 0 < ε := lt_min hδ (by positivity)
  have hεsep : ε < ‖u - bisector u v‖ / 2 := by
    have hh := min_le_right δ (‖u - bisector u v‖ / 4)
    dsimp [ε]
    linarith
  have hk : 0 < matchingGap lam a b ε :=
    (whitebox_quantitative_matching lam a b ε u v D0 hu hv horth
      hlam hsmall ha hb hε hεsep).1
  let η := min (matchingGap lam a b ε) (1 - a - b)
  have hη : 0 < η := lt_min hk (by linarith)
  refine ⟨η, hη, ?_⟩
  intro t ht htin D hmin
  have hpertD := (perturbation_bounds lam a b t u v D hlam.le hv ht.le).1
  have hpert0 := (perturbation_bounds lam a b t u v D0 hlam.le hv ht.le).2
  have hcomparison := hmin D0
  have htgap : t < matchingGap lam a b ε :=
    htin.trans_le (min_le_left _ _)
  have hclose : jointCost lam a b 0 u v D < baseline lam a b + matchingGap lam a b ε := by
    rw [hbase] at hpert0
    linarith
  have hmatch := (whitebox_quantitative_matching lam a b ε u v D hu hv horth
    hlam hsmall ha hb hε hεsep).2 hclose
  have heδ : ε ≤ δ := min_le_left _ _
  rcases hmatch with h | h
  · exact Or.inl ⟨h.1.trans_le heδ, h.2.trans_le heδ⟩
  · exact Or.inr ⟨h.1.trans_le heδ, h.2.trans_le heδ⟩

end D5.S3.Estimation.WhiteBoxLossFiberLaw.TwoAtomMatching
