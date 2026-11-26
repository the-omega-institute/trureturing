import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.ExpSurjective
import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Rigidity.CasimirGrowth
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Lowest K-type and Casimir value determine a discrete series coefficient; analytic
vectors (known result; see Lib.DiscreteSeries.Rigidity.CasimirGrowth). -/

open Matrix InnerProductSpace Fintype Norms.L2Operator Real Int


variable {n} [Fintype n] {M X H} [AddCommGroup M] [Module ℂ M] {ε} {l : @HCParam n ε} {ρ :
  GlModule n M} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup H] {ϖ :
  USign ε →* X →L[ℂ] X} {ι B A} (hp : IsUnitaryRep A ϖ B) (hd : IsDerivedAction ϖ ι ρ)

/-- Analytic vectors: let λ have some gap, ρ satisfy `IsUnitaryCasimirGe` (invariant inner product,
Ω ≥ |λ|²−|ρ|² throughout), x be K-highest, c a scalar coefficient map with |c_g(v)| ≤ D‖v‖. If c_1
kills every M_s of `GlModule.filtration` x, then c_g(x) = 0 for all g. -/
lemma HCParam.IsKHighest.coeffMap_eq_zero [InnerProductSpace ℂ H] {ρ ν} {x : H} {D h} [l.HasGap h]
    (hx : l.IsKHighest ρ ν x) (i : IsUnitaryCasimirGe l ρ) {c : USign ε → _ →ₗ[ℂ] ℂ} (hd :
  ρ.IsCoeffMap c) (hb : ∀ g v,
  ‖c g v‖ ≤ D * ‖v‖) (hy : ∀ s, ∀ v ∈ ρ.filtration ε x s, c 1 v = 0) g : c g x = 0 := by
  obtain ⟨⟨R, r⟩, X, Y, rfl⟩ := Finite.exists_le (|ν ·|.toNat), exists_eq_expU_mul_expU g
  have k (Y : unitaryLie _) g (hy : ∀ s, ∀ v ∈ ρ.filtration ε x s, c g v = 0) :=
    let rec f (m s : ℕ) v (hv : v ∈ ρ.filtration ε x s) : ∀ t ∈ unitInterval, ‖c (g * expU (t • Y))
      v‖ ≤ exp (m * -exp (-exp 1 * ((card n + 1) ^ 4 * ‖Y.1‖ + 1) * t)) * (exp (R + 1 + s) * (|D| *
      ‖v‖ + 1)) := have ⟨p, q⟩ := hx.norm_apply_le_of_mem_filtration i (toNat_le.1 <| r ·) hv Y
      image_norm_le_of_norm_deriv_right_lt_deriv_boundary (HasDerivAt.continuousOn (by tauto))
      (fun t _ ↦ (hd ..).hasDerivWithinAt) (by simp [hy s v hv]; bound)
      (fun _ ↦ hasDerivAt_deriv_iff.2 (by fun_prop)) fun t ⟨a, b⟩ ↦ (fun u ↦ by
      grw [hb, le_abs_self D, lt_add_one (_ * _)] at u; simp [← exp_add, field] at u
      have : s < m := by rify; grw [neg_nonpos.2, exp_zero] at u <;> bound
      grw [IsKHighest.coeffMap_eq_zero.f m _ _ p t ⟨a, b.le⟩, q]
      simp (disch := fun_prop) [exp_add, field]; grw [← u, ← sub_nonneg]; ring; bound) ∘ Eq.ge
    fun s v hv ↦ (summable_const_iff _).1 (.of_norm_bounded (.mul_right _
    (summable_exp_nat_mul_iff.2 (by simp; bound)))
      (IsKHighest.coeffMap_eq_zero.f · s v hv 1 (by simp)))
  simpa using k Y _ (k X 1 hy) 0 _ ρ.self_mem_filtration

include hd in lemma IsDerivedAction.isCoeffMap [NormedSpace ℂ H] (φ : X →L[ℂ] H) :
  ρ.IsCoeffMap fun g ↦ (φ ∘L ϖ g).1 ∘ₗ ι := by
  intro _ _ _ t; convert! ((sub_self t ▸ hd ..).comp_sub_const ..).map_clm (φ ∘L _)
  simp [rep_apply_apply, mul_assoc, -map_mul]; rcongr
  simp [← exp_add_of_commute, ← add_smul, commute_iff_eq, smul_comm t]

include hp

/-- For a representation π on X with invariant positive definite hermitian form B as in
`IsUnitaryRep`, there are a complex inner product space H and a linear isomorphism j : X → H
with ⟨jx, jy⟩ = B(x,y). -/
lemma IsUnitaryRep.exists_innerProductSpace : ∃ (H : type_of% X) (_ : NormedAddCommGroup H) (_ :
  InnerProductSpace ℂ H) (j : X ≃ₗ[ℂ] H), (∀ x y, ⟪j x, j y⟫_ℂ = B x y) ∧ ∀ g x, ‖j (ϖ g x)‖ = ‖j
  x‖ := by refine' ⟨X, (Core.mk (.mk ⟨(B ·)⟩ ..) _).toNormedAddCommGroup, .ofCore _, 1, _,
  (congr(√$(hp.2 · · _).re))⟩ <;> simp [inner] <;> grind [IsUnitaryRep, Complex.zero_re]

lemma IsUnitaryRep.form_apply_eq_form_inv_apply g x y : B x (ϖ g y) =
  B (ϖ g⁻¹ x) y := by simp [← hp.2 g⁻¹ x, rep_apply_apply]

include hd

lemma IsDerivedAction.form_E_eq_sign_mul a b v w : B (ι (ρ.E a b v)) (ι w) =
  (ε a * ε b).1 * B (ι v) (ι (ρ.E b a w)) := have k Y := ((hd Y v).map_clm (B _)).star.unique (by
    convert (hd (-Y) w).map_clm (B (ι v)); simp [hp.form_apply_eq_form_inv_apply,
      hp.3]; rcongr; simp [← Matrix.exp_neg])
  have m z := k ⟨(z * ε b : ℂ) • single a b 1 - (star z * ε a) • single b a 1,
    ext (by simp [signMatrix]; grind)⟩; by rcases m (ε b), m (.I * ε b); simp_all
    [hp.3, -smul_single, mul_assoc, ← cast_mul]; grind [Complex.I_sq]
