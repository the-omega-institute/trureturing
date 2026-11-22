/- GID: D5/S3/Fourier/WeightedPhaseRelationLattice
   generality: G
   mirror-B: D5/B/S3/Fourier/WeightedPhaseRelationLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Fourier/TorusOrbitClosure]
   utility: none
   digest: The complete integer relation lattice controls weighted common-time phase deficit. -/

import D5.S3.Fourier.TorusOrbitClosure
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The all-real and nonnegative-time phase orbit closures are the annihilator of the
integer relations. -/

set_option autoImplicit false

open Set
open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Fourier.WeightedPhaseRelationLattice

private theorem exists_nonresonant_step {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ s ∈ Ioo (0 : ℝ) 1, ∀ (k : J → ℤ) (m : ℤ),
      (∑ j, (k j : ℝ) * γ j) * s = (m : ℝ) * (2 * Real.pi) →
        (∑ j, (k j : ℝ) * γ j) = 0 := by
  let dot (k : J → ℤ) : ℝ := ∑ j, (k j : ℝ) * γ j
  let bad : (J → ℤ) × ℤ → ℝ := fun p => (p.2 : ℝ) * (2 * Real.pi) / dot p.1
  have hcount : (range bad).Countable := countable_range bad
  have hnot : ¬ Ioo (0 : ℝ) 1 ⊆ range bad := by
    intro hsub
    exact (not_le_of_gt zero_lt_one) (Cardinal.Real.Ioo_countable_iff.mp (hcount.mono hsub))
  obtain ⟨s, hs, hgood⟩ := not_subset.mp hnot
  refine ⟨s, hs, fun k m h => ?_⟩
  by_contra hne
  apply hgood
  refine ⟨(k, m), ?_⟩
  change (m : ℝ) * (2 * Real.pi) / dot k = s
  exact (div_eq_iff hne).2 (by simpa [dot, mul_comm s] using h.symm)

private theorem circle_character_exp {J : Type*} [Fintype J] (k : J → ℤ) (θ : J → ℝ) :
    (∏ j, Circle.exp (θ j) ^ k j) = Circle.exp (∑ j, (k j : ℝ) * θ j) := by
  simp_rw [← Circle.exp_intCast_mul]
  exact (map_sum Circle.expHom _ _).symm

/-- The all-real orbit closure is the common kernel of the zero-dot-product integer
characters, and nonnegative times give the same closure. -/
theorem closure_real_phase_orbit {J : Type*} [Fintype J] (γ : J → ℝ) :
    let T := closure (range (fun (t : ℝ) (j : J) => Circle.exp (γ j * t)))
    T = {p | ∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 → (∏ j, p j ^ k j) = 1} ∧
      closure ((fun (t : ℝ) (j : J) => Circle.exp (γ j * t)) '' Ici 0) = T := by
  intro T
  let orbit (t : ℝ) (j : J) := Circle.exp (γ j * t)
  let kernel : Set (J → Circle) :=
    {p | ∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 → (∏ j, p j ^ k j) = 1}
  change T = kernel ∧ closure (orbit '' Ici 0) = T
  have hchar (k : J → ℤ) (t : ℝ) :
      (∏ j, orbit t j ^ k j) = Circle.exp ((∑ j, (k j : ℝ) * γ j) * t) := by
    simp only [orbit, circle_character_exp, ← mul_assoc, ← Finset.sum_mul]
  have hreal : T ⊆ kernel := by
    intro z hz k hk
    have hc : Continuous (fun w : J → Circle => ∏ j, w j ^ k j) := by
      exact continuous_finsetProd _ fun j _ => (continuous_apply j).zpow (k j)
    apply closure_minimal (t := {w | (∏ j, w j ^ k j) = 1}) ?_
      (isClosed_eq hc continuous_const) hz
    rintro _ ⟨t, rfl⟩
    change (∏ j, orbit t j ^ k j) = 1
    rw [hchar, hk, zero_mul, Circle.exp_zero]
  have hkernel : kernel ⊆ closure (orbit '' Ici 0) := by
    intro z hz
    obtain ⟨s, hs01, hs⟩ := exists_nonresonant_step γ
    have hd : z ∈ closure (range (fun n : ℕ => orbit s ^ n)) := by
      apply (D5.S3.Fourier.TorusOrbitClosure.result (orbit s) z).2
      intro k hk
      rw [hchar] at hk
      obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hk
      exact hz k (hs k m hm)
    refine closure_mono ?_ hd
    rintro _ ⟨n, rfl⟩
    refine ⟨(n : ℝ) * s, mul_nonneg (Nat.cast_nonneg n) hs01.1.le, ?_⟩
    funext j
    change Circle.exp (γ j * ((n : ℝ) * s)) = Circle.exp (γ j * s) ^ n
    rw [mul_left_comm, Circle.exp_natCast_mul]

  have hnonneg : closure (orbit '' Ici 0) ⊆ T := closure_mono (image_subset_range _ _)
  exact ⟨hreal.antisymm (hkernel.trans hnonneg), hnonneg.antisymm (hreal.trans hkernel)⟩

/-- For every real lift centered at the sine-maximizing phase, membership in the
continuous orbit closure is equivalent to the affine congruences for the complete
integer relation rows. -/
theorem centered_lift_iff {J A : Type*} [Fintype J]
    (γ : J → ℝ) (K : Matrix A J ℤ)
    (hK : ∀ k : J → ℤ, k ∈ Submodule.span ℤ (range K.row) ↔
      (∑ j, (k j : ℝ) * γ j) = 0) (x : J → ℝ) :
    (fun j => Circle.exp (x j + Real.pi / 2)) ∈
      closure (range (fun (t : ℝ) (j : J) => Circle.exp (γ j * t))) ↔
    ∃ z : A → ℤ, (K.map (Int.cast : ℤ → ℝ)) *ᵥ x =
      fun a => (z a : ℝ) * (2 * Real.pi) -
        (Real.pi / 2) * ((K.map (Int.cast : ℤ → ℝ)) *ᵥ (1 : J → ℝ)) a := by
  classical
  let R := K.map (Int.cast : ℤ → ℝ)
  let θ : J → ℝ := fun j => x j + Real.pi / 2
  have hshift (a : A) : (R *ᵥ θ) a = (R *ᵥ x) a + (Real.pi / 2) * (R *ᵥ 1) a := by
    simp only [Matrix.mulVec, dotProduct, θ, Pi.one_apply, mul_one, mul_add, Finset.sum_add_distrib,
      Finset.sum_mul, mul_comm (Real.pi / 2)]
  rw [(closure_real_phase_orbit γ).1]
  change (∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 →
      (∏ j, Circle.exp (θ j) ^ k j) = 1) ↔ _
  constructor
  · intro h
    have hr (a : A) : ∃ m : ℤ, (R *ᵥ θ) a = (m : ℝ) * (2 * Real.pi) := by
      apply Circle.exp_eq_one.mp
      change Circle.exp (∑ j, ((K.row a j : ℤ) : ℝ) * θ j) = 1
      rw [← circle_character_exp (K.row a) θ]
      exact h _ ((hK _).mp (Submodule.subset_span (mem_range_self a)))
    choose z hz using hr
    exact ⟨z, funext fun a => eq_sub_of_add_eq ((hshift a).symm.trans (hz a))⟩
  · rintro ⟨z, hz⟩ k hk
    have hr (a : A) : (R *ᵥ θ) a = (z a : ℝ) * (2 * Real.pi) := by
      rw [hshift, congrFun hz a, sub_add_cancel]
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp ((hK k).mpr hk)
    rw [circle_character_exp]
    apply Circle.exp_eq_one.mpr
    refine ⟨∑ a ∈ c.support, c a * z a, ?_⟩
    calc
      (∑ j, (k j : ℝ) * θ j) = ∑ a ∈ c.support, (c a : ℝ) * (R *ᵥ θ) a := by
        have hentry (j : J) : k j = ∑ a ∈ c.support, c a * K a j := by
          simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
            using (congrFun hc j).symm
        simp only [hentry, Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum,
          Matrix.mulVec, dotProduct, R, Matrix.map_apply, mul_assoc]
        exact Finset.sum_comm
      _ = ((∑ a ∈ c.support, c a * z a : ℤ) : ℝ) * (2 * Real.pi) := by
        simp only [hr, Int.cast_sum, Int.cast_mul, Finset.sum_mul, mul_assoc]

private theorem exists_weighted_fiber_minimum {J A : Type*} [Fintype J] [Fintype A]
    [DecidableEq J] [DecidableEq A] (R : Matrix A J ℝ) (w : J → ℝ)
    (hw : ∀ j, 0 < w j) (hR : LinearIndependent ℝ R.row) (b : A → ℝ) :
    let M := diagonal w
    let G := R * M⁻¹ * Rᵀ
    ∃ x : J → ℝ, R *ᵥ x = b ∧ x ⬝ᵥ (M *ᵥ x) = b ⬝ᵥ (G⁻¹ *ᵥ b) ∧
      ∀ y : J → ℝ, R *ᵥ y = b → x ⬝ᵥ (M *ᵥ x) ≤ y ⬝ᵥ (M *ᵥ y) := by
  intro M G
  have hM : M.PosDef := .diagonal hw
  have hG : G.PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hM.inv.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff.mpr hR)
  let u := G⁻¹ *ᵥ b
  let x := M⁻¹ *ᵥ (Rᵀ *ᵥ u)
  have hx : R *ᵥ x = b := by
    change R *ᵥ (M⁻¹ *ᵥ (Rᵀ *ᵥ u)) = b
    rw [mulVec_mulVec (Rᵀ *ᵥ u), mulVec_mulVec u]
    change G *ᵥ (G⁻¹ *ᵥ b) = b
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit),
      one_mulVec]
  have hMx : M *ᵥ x = Rᵀ *ᵥ u := by
    change M *ᵥ (M⁻¹ *ᵥ (Rᵀ *ᵥ u)) = Rᵀ *ᵥ u
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit),
      one_mulVec]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hMx, dotProduct_transpose_mulVec, hx, dotProduct_comm]
  · intro y hy
    let v := y - x
    have hv : R *ᵥ v = 0 := by simp [v, mulVec_sub, hy, hx]
    have hvx : v ⬝ᵥ (M *ᵥ x) = 0 := by
      rw [hMx, dotProduct_transpose_mulVec, hv, dotProduct_zero]
    have hxv : x ⬝ᵥ (M *ᵥ v) = 0 := by
      have hMtranspose : Mᵀ = M := diagonal_transpose w
      rwa [← hMtranspose, dotProduct_transpose_mulVec]
    have hvv : 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
      simpa only [star_trivial] using hM.posSemidef.dotProduct_mulVec_nonneg v
    have hyx : y = x + v := by simp [v]
    conv_rhs => rw [hyx]
    simp only [mulVec_add, add_dotProduct, dotProduct_add, hvx, hxv, add_zero, zero_add]
    exact le_add_of_nonneg_right hvv

/-- The inverse Gram energy of the complete relation lattice bounds the normalized
sine deficit at a common time. The deficit vanishes exactly when a winding makes the
affine offset zero. -/
theorem weighted_phase_deficit_bounds {J A : Type*} [Fintype J] [Fintype A]
    [DecidableEq J] [DecidableEq A] (γ w : J → ℝ) (K : Matrix A J ℤ)
    (hw : ∀ j, 0 < w j) (hW : 0 < ∑ j, w j)
    (hK : ∀ k : J → ℤ, k ∈ Submodule.span ℤ (range K.row) ↔
      (∑ j, (k j : ℝ) * γ j) = 0)
    (hind : LinearIndependent ℝ (K.map (Int.cast : ℤ → ℝ)).row) :
    let W := ∑ j, w j
    let R := K.map (Int.cast : ℤ → ℝ)
    let M := diagonal w
    let G := R * M⁻¹ * Rᵀ
    let b (z : A → ℤ) (a : A) :=
      (z a : ℝ) * (2 * Real.pi) - (Real.pi / 2) * (R *ᵥ (1 : J → ℝ)) a
    let E := ⨅ z : A → ℤ, b z ⬝ᵥ (G⁻¹ *ᵥ b z)
    let D := 1 - (⨆ t : ℝ, (∑ j, w j * Real.sin (γ j * t)) / W)
    2 * E / (Real.pi ^ 2 * W) ≤ D ∧ D ≤ E / (2 * W) ∧ (IsEmpty A → E = 0) ∧
      (D = 0 ↔ ∃ z : A → ℤ, b z = 0) := by
  intro W R M G b E D
  change 0 < W at hW
  let orbit (t : ℝ) (j : J) := Circle.exp (γ j * t)
  let T := closure (range orbit)
  let lift (x : J → ℝ) (j : J) := Circle.exp (x j + Real.pi / 2)
  let score (p : J → Circle) := (∑ j, w j * (p j : ℂ).im) / W
  let loss (p : J → Circle) := 1 - score p
  let Q (x : J → ℝ) := x ⬝ᵥ (M *ᵥ x)
  let energy (z : A → ℤ) := b z ⬝ᵥ (G⁻¹ *ᵥ b z)
  have hQ (x : J → ℝ) : Q x = ∑ j, w j * x j ^ 2 := by
    simp only [Q, M, mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmin (z : A → ℤ) :
      ∃ x : J → ℝ, R *ᵥ x = b z ∧ Q x = energy z ∧
        ∀ y : J → ℝ, R *ᵥ y = b z → Q x ≤ Q y :=
    exists_weighted_fiber_minimum R w hw hind (b z)
  have hQnonneg (x : J → ℝ) : 0 ≤ Q x := by
    rw [hQ]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j).le (sq_nonneg _)
  have henergy_nonneg (z : A → ℤ) : 0 ≤ energy z := by
    obtain ⟨x, _, hx, _⟩ := hmin z
    rw [← hx]
    exact hQnonneg x
  have hE : BddBelow (range energy) := ⟨0, by rintro _ ⟨z, rfl⟩; exact henergy_nonneg z⟩
  have him (a : ℝ) : (Circle.exp a : ℂ).im = Real.sin a := by
    exact Complex.exp_ofReal_mul_I_im a
  have hscore : Continuous score := by
    exact (continuous_finsetSum _ fun j _ => continuous_const.mul
      (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply j)))).div_const W
  have hloss : Continuous loss := continuous_const.sub hscore
  have hT : IsCompact T := isClosed_closure.isCompact
  have hnonempty : (loss '' T).Nonempty :=
    ⟨loss (orbit 0), orbit 0, subset_closure (mem_range_self 0), rfl⟩
  have hbounded : BddBelow (loss '' T) := (hT.image hloss).bddBelow
  have hSup : BddAbove (range (fun t => score (orbit t))) :=
    ((hT.image hscore).bddAbove).mono (by
      rintro _ ⟨t, rfl⟩
      exact ⟨orbit t, subset_closure (mem_range_self t), rfl⟩)
  have hD : D = sInf (loss '' T) := by
    change 1 - (⨆ t : ℝ, (∑ j, w j * Real.sin (γ j * t)) / W) = _
    have htime (t : ℝ) : score (orbit t) = (∑ j, w j * Real.sin (γ j * t)) / W := by
      simp only [score, orbit, him]
    simp_rw [← htime]
    apply le_antisymm
    · refine le_csInf hnonempty ?_
      rintro _ ⟨p, hp, rfl⟩
      apply sub_le_sub_left _ 1
      exact closure_minimal (t := {p | score p ≤ ⨆ t, score (orbit t)})
        (by rintro _ ⟨t, rfl⟩; exact le_ciSup hSup t)
        (isClosed_le hscore continuous_const) hp
    · have hs : (⨆ t, score (orbit t)) ≤ 1 - sInf (loss '' T) := by
        refine ciSup_le fun t => ?_
        have ht := csInf_le hbounded
          (show loss (orbit t) ∈ loss '' T from ⟨orbit t, subset_closure (mem_range_self t), rfl⟩)
        exact le_sub_comm.mp ht
      exact le_sub_comm.mp hs
  have hlift (x : J → ℝ) : lift x ∈ T ↔ ∃ z : A → ℤ, R *ᵥ x = b z :=
    centered_lift_iff γ K hK x
  have hloss_lift (x : J → ℝ) :
      loss (lift x) * W = ∑ j, w j * (1 - Real.cos (x j)) := by
    simp only [loss, score, lift, him, Real.sin_add_pi_div_two, sub_mul, one_mul,
      div_mul_cancel₀ _ hW.ne', mul_sub, mul_one, Finset.sum_sub_distrib, W]
  have hcos_lower (x : J → ℝ) (hx : ∀ j, |x j| ≤ Real.pi) :
      (2 / Real.pi ^ 2) * Q x ≤ loss (lift x) * W := by
    rw [hQ, hloss_lift, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc
      (2 / Real.pi ^ 2) * (w j * x j ^ 2) = w j * ((2 / Real.pi ^ 2) * x j ^ 2) := by ring
      _ ≤ w j * (1 - Real.cos (x j)) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.cos_le_one_sub_mul_cos_sq (hx j)]) (hw j).le
  have hcos_upper (x : J → ℝ) : loss (lift x) * W ≤ Q x / 2 := by
    rw [hQ, hloss_lift, Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    calc
      w j * (1 - Real.cos (x j)) ≤ w j * (x j ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.one_sub_sq_div_two_le_cos (x := x j)])
          (hw j).le
      _ = w j * x j ^ 2 / 2 := by ring
  have hprincipal (p : J → Circle) : ∃ x : J → ℝ, lift x = p ∧ ∀ j, |x j| ≤ Real.pi := by
    let rotated (j : J) := p j * Circle.exp (-(Real.pi / 2))
    let x (j : J) := Complex.arg (rotated j : ℂ)
    refine ⟨x, ?_, fun j => Complex.abs_arg_le_pi (rotated j : ℂ)⟩
    funext j
    change Circle.exp (Complex.arg (rotated j : ℂ) + Real.pi / 2) = p j
    rw [Circle.exp_add, Circle.exp_arg, show rotated j = _ from rfl, mul_assoc,
      ← Circle.exp_add, neg_add_cancel, Circle.exp_zero, mul_one]
  have hDle (p : J → Circle) (hp : p ∈ T) : D ≤ loss p := by
    rw [hD]
    exact csInf_le hbounded ⟨p, hp, rfl⟩
  have hLower : 2 * E / (Real.pi ^ 2 * W) ≤ D := by
    rw [hD]
    refine le_csInf hnonempty ?_
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨x, hx, hxπ⟩ := hprincipal p
    obtain ⟨z, hz⟩ := (hlift x).mp (hx.symm ▸ hp)
    obtain ⟨y, _, hy, hymin⟩ := hmin z
    have hEx : E ≤ Q x :=
      (ciInf_le hE z).trans (hy ▸ hymin x hz)
    have hcos := hcos_lower x hxπ
    rw [hx] at hcos
    calc
      2 * E / (Real.pi ^ 2 * W) = ((2 / Real.pi ^ 2) * E) / W := by ring
      _ ≤ loss p := (div_le_iff₀ hW).mpr
        ((mul_le_mul_of_nonneg_left hEx (by positivity)).trans hcos)
  have hUpper : D ≤ E / (2 * W) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hW)).mpr
    change D * (2 * W) ≤ ⨅ z, energy z
    refine le_ciInf fun z => ?_
    obtain ⟨x, hx, hxE, _⟩ := hmin z
    have hp := (hlift x).mpr ⟨z, hx⟩
    calc
      D * (2 * W) = 2 * (D * W) := by ring
      _ ≤ 2 * (loss (lift x) * W) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hDle _ hp) hW.le) (by norm_num)
      _ ≤ 2 * (Q x / 2) := mul_le_mul_of_nonneg_left (hcos_upper x) (by norm_num)
      _ = energy z := by rw [hxE]; ring
  refine ⟨hLower, hUpper, ?_, ?_⟩
  · intro hempty
    change (⨅ z, energy z) = 0
    simp [energy, dotProduct]
  · constructor
    · intro hzero
      have hmem := (hT.image hloss).sInf_mem hnonempty
      rw [← hD, hzero] at hmem
      obtain ⟨p, hp, hlp⟩ := hmem
      obtain ⟨x, rfl, hxπ⟩ := hprincipal p
      have hcos := hcos_lower x hxπ
      rw [hlp, zero_mul] at hcos
      have hQzero : Q x = 0 := le_antisymm
        (nonpos_of_mul_nonpos_right hcos (by positivity)) (hQnonneg x)
      rw [hQ] at hQzero
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hw j).le (sq_nonneg (x j)))).mp hQzero
      have hxzero : x = 0 := by
        funext j
        exact sq_eq_zero_iff.mp
          ((mul_eq_zero.mp (hterms j (Finset.mem_univ j))).resolve_left (hw j).ne')
      obtain ⟨z, hz⟩ := (hlift x).mp hp
      exact ⟨z, by simpa [hxzero] using hz.symm⟩
    · rintro ⟨z, hz⟩
      have hp : lift 0 ∈ T := (hlift 0).mpr ⟨z, by simp [hz]⟩
      have hl : loss (lift 0) = 0 := by simpa [hW.ne'] using hloss_lift 0
      have hEnonneg : 0 ≤ E := le_ciInf henergy_nonneg
      have hDnonneg : 0 ≤ D :=
        (show 0 ≤ 2 * E / (Real.pi ^ 2 * W) by positivity).trans hLower
      exact le_antisymm (hl ▸ hDle _ hp) hDnonneg

#print axioms closure_real_phase_orbit
#print axioms centered_lift_iff
#print axioms weighted_phase_deficit_bounds

end D5.S3.Fourier.WeightedPhaseRelationLattice
