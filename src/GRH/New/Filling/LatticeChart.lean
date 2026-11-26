import GRH.New.Filling.CrudeBoundDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: dictionaries between two encodings of the same objects.

This file: Continuity and norm formulas for the product Bessel function, kernel and amplitudes. H∩K
read as congruence subgroup fixing the mark; class sums as finite sums. -/

namespace Filling

section

variable {E 𝔰} [Field E] [CMType E] {S : Filling E 𝔰} [σ : Side] {γ}

@[fun_prop] lemma continuous_besselFn i : Continuous (S.besselFn · i) := by fun_prop [besselFn]

@[fun_prop] lemma continuous_besselKernel :
  Continuous (S.besselKernel γ) := by fun_prop [besselKernel]

lemma enorm_besselKernel y : ‖S.besselKernel γ y‖ₑ =
  (∏ v, ‖(S.besselSys v).W σ (y v)‖ₑ) * ∏ v, ‖(S.besselSys v).W σ (((S.ratToInf γ)⁻¹ * y) v)‖ₑ := by
  simp [enorm]; norm_cast; simp [← sq_eq_sq₀, PiLp.nnnorm_eq_of_L2, besselKernel, besselFn,
    mul_pow, ← Finset.prod_pow, Fintype.sum_prod_type, Fintype.prod_sum, Fintype.sum_mul_sum]

lemma enorm_amplitude_le c c' : ‖S.amplitude c c' γ‖ₑ ≤ S.amplitudeAbs c c' γ := by grw [amplitude,
  MeasureTheory.enorm_integral_le_lintegral_enorm, enorm_toReal_smul_le, amplitudeAbs]

end

attribute [local simp] IsIntMatrix Matrix.diagonal Matrix.mul_apply middleBaseChange ite_mem

variable {E} [Field E] [CMType E] {𝔰} (S :
  Filling E 𝔰) {k}

lemma isIntMatrix_middleBaseChange_mul {m} {l : Matrix _ m _} : (IsIntMatrix (Ô E) (scaleAt
  S.piBar⁻¹.1 𝔰.k₀ * l) → IsIntMatrix (Ô E) (middleBaseChange 𝔰 S.piBar * l)) ∧ (IsIntMatrix (Ô E)
  (middleBaseChange 𝔰 S.piBar * l) ↔ IsIntMatrix (Ô E) l ∧ ∀ j, l 𝔰.k₀ j ∈ Ô E ∙ ↑S.piBar) := by
  simp [← mem_span_unit_iff, -mem_span_singleton_iff_exists_mul]
  grind [mul_mem, piBar_mem, star_mem_Ô, mem_span_singleton_iff_exists_mul (O := Ô E)]

lemma forall_inclHFin_sub_one_iff (P : _ → _) : P 0 → ((∀ a b, P (((S.inclHFin k).1.1 - 1) a b)) ↔
  ∀ a b, P ((middleBaseChange 𝔰 S.piBar * ((k.1.1 - 1) * scaleAt (star S.piBar⁻¹.1) 𝔰.k₀) :) a
  b)) := by simp_all [inclHFin, toLatBasis, besselLatticeBasis, toBesselH, mul_sub, sub_mul,
  ← star_mul]; congr! 3 <;> grind

attribute [-simp] Matrix.sub_apply in
/-- Let the finite idele p be a unit at w or w̄ for each w, and k integral unitary with row o
congruent to that of 1 modulo pÔ. Then k − 1, with row o divided by p and column o by p̄, is
integral. -/
lemma isIntMatrix_scaleAt_sub_one {κ} [Fintype κ] (p : (𝔸f E)ˣ) o (hp : ∀ w, Valued.v (p.1 w) = 1 ∨
  Valued.v (p.1 (star w)) = 1) {k : Gf E κ} (h : k.1 ∈ congruenceGL (Ô E ∙ ↑p) fun () ↦ o) :
  IsIntMatrix (Ô E) (scaleAt p⁻¹.1 o * ((k.1.1 - 1) * scaleAt (star p⁻¹.1) o)) := by
  rcases h.2, star_mem_Ô ∘' mem_span_unit_iff.1 ∘'
    (U.inv_val_eq_conjTranspose k ▸ (inv_mem h).2 ()), h.1.isIntMatrix.sub .one
  simp_all [star_mul, ← Matrix.conjTranspose_apply, mem_Ô, ↓mem_span_unit_iff]; intros
  cases hp ‹_› <;> simp_all [v_inv]

lemma inclHFin_mem_latStabilizer : S.inclHFin k ∈ S.latStabilizer ↔ ↑k ∈ congruenceGL
  (Ô E ∙ ↑S.piBar) fun () ↦ 𝔰.k₀ := .trans ⟨(·.isIntMatrix.sub .one), by simp_all [latStabilizer,
  ← unitaryLevel_one, S.isUnimodular_latMiddle.splitGram.mem_unitaryLevel, -IsIntMatrix]⟩
  ((S.forall_inclHFin_sub_one_iff _ (by simp)).trans ⟨fun h ↦
  (S.isIntMatrix_middleBaseChange_mul.2.1 (by
    simpa +contextual [Matrix.mul_assoc, ← star_mul, -Matrix.diagonal, -IsIntMatrix] using
      IsIntMatrix.mul h (N := scaleAt (star S.piBar.1) 𝔰.k₀) (by simp [piBar_mem, star_mem_Ô]))).imp
  (mem_Kf.2 <| by simpa using ·.add .one) (by simp),
  S.isIntMatrix_middleBaseChange_mul.1 ∘ isIntMatrix_scaleAt_sub_one _ _ (by grind [N_split])⟩)

lemma reduction_inclHFin_eq_one_iff h i w : S.reduction ⟨_, h⟩ i w = 1 ↔
  Kf.reduceAt w ⟨k, (S.inclHFin_mem_latStabilizer.1 h).1⟩ = 1 := by
  repeat erw [intGL.map_eq_one]
  simp_rw [reduceAt_eq_zero]
  erw [S.forall_inclHFin_sub_one_iff fun x ↦ Valued.v (x w) < 1] <;> simp [S.chosenPlaces_q i,
    (N_split ..).resolve_right, v_inv, apply_ite, ite_apply, -Matrix.one_apply]; tauto

lemma classSum_eq_sum f : classSum stdRatPoints S.columnLevel f = (∑ c : S.Classes,
  f c.out : ℝ) := by simp [classSum, aut_columnLevel, ← finsum_eq_sum_of_fintype]; rfl

lemma card_resField_eq_levelPrime i (w : S.chosenPlaces i) : .card (ResField w.1) =
  S.levelPrime i := by grind [card_ResField, chosenPlaces_q]
