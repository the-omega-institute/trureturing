/- GID: D5/S3/Zeros/GRH/New/Exchange/StableSpaces
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/StableSpaces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.StableSpaces. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/StableSpaces.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.PartnersMatch
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

This file: A stable space containing a standard datum contains all partner data. -/


open Matrix MeasureTheory SemilocalField schwartzBruhat IsIntMatrix Finset Function MatMul Fint
variable {F a b m n} [V : SemilocalField F] [Fintype a] [Fintype b] [Fintype m] [Fintype n]
  {χ P Φ Ψ} [hχ : TameLocalChar χ] {e : b ⊕ a ≃ n} {U : Set (Matrix n b F)} (hP : ∀ g : GL n F,
  ∀ f ∈ P, (f <| g.1 * ·) ∈ P) (hS : P ≤ schwartzBruhat U) (hΨ : IsLocallyConstant Ψ) (Q :
  IsPartner V.O e χ Φ Ψ) (A : IntegralFrame F n m b)

lemma IntegralFrame.exists_stdRowDatum_eq_stdDatum σ : ∃ c, ‖c‖ = 1 ∧ stdRowDatum σ χ A.L' =
  A.stdDatum (c * invOnUnits χ ·.det) := by
  refine' A.blocks_spec |> fun _ ↦
    (⟨_, hχ.norm_eq_one ·, funext fun x ↦ if_congr _ (invOnUnits_eq_mul_of_unit ‹_› ▸ _) _⟩)
    (isPrimitiveMatrix_iff_isIntegralUnit_det (A := (A.L.fromCols (A.K.fromCols A.I)).submatrix id
    σ.symm).1 ⟨_, (A.L'.fromRows (A.K'.fromRows A.I')).submatrix σ.symm id, _⟩).2 <;>
    simp_all [IsIntMatrix, reindex_equiv σ, ↓fromRows_mul_fromCols, ← det_mul, ← submatrix_mul]

attribute [local simp] mul_add stdColDatum
include hS hP hΨ Q

/-- Let χ be tame and P a GL_n(F)-stable space of Schwartz–Bruhat functions containing rΨ_s, Ψ_s
the standard datum of an integral s, r ℕ-valued, r(x) ≠ 0 at an integral x with sx = 1. Then
P contains every locally constant function having a partner. -/
lemma partner_mem_of_stdColDatum {p x s} (hp : p ∈ P) (hx : IsIntMatrix O x) (hs : IsIntMatrix O s)
  (e₁ : s * x = 1) (r : _ → ℕ) (H : ∀ y, p y = r y • stdColDatum χ s y) (h₁ : r x ≠ 0) : Ψ ∈ P := by
  obtain ⟨⟨c, hc⟩, _⟩ := ((V.unif_nilpotent.smul_const (.id _)).eventually
    (ContinuousMap.eventually_mapsTo isCompact_O.matrix
    ((isLocallyConstant_curry (Q.mem_matchingPairs hχ hΨ).1.2 (· + ·) (-· + ·)).isOpen_fiber Ψ)
    (by simp_intro _))).exists, (isCompact_intGL (n := n) V.isCompact_O).compactSpace
  let d : GL n F := V.ϖ⁻¹ ^ c • .mk'' (1 - x * (s - V.ϖ ^ c • s))
    (by simp [↓det_one_sub_mul_comm x, *])
  have L := isLocallyConstant_curry (Γ := intGL n O) (hS hp) (d.1 * ·.1.1 * ·) (·.1.2 * d.2 * ·)
  rw [← P.smul_mem_iff ((L.comp (‖· x‖)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := .haar) (x := 1) (.of_compactSpace _) (by simp_intro _) (by simp [d, invOnUnits, *])).ne']
  convert ← integral_mem_of_isLocallyConstant .haar (L.comp (norm ∘ · • Ψ)) fun k ↦
    (funext fun y ↦ ?_).subst (P.smul_mem (Ψ (k.1.2 * x)) (hP (d * k) _ hp))
  obtain ⟨_ | ⟨l, c, ⟨⟩⟩, j, a, ⟨⟩⟩ := not_or_of_imp (Q.2 ‹_›),
    (valPair.exists_firstCols_iff e).2 ⟨hx, by tauto⟩
  simp_all; rw [← integral_mul_right_eq_self _ ⟨_, div_mem a c⟩]
  simp [mul_firstCols, ← integral_smul_const]
  simp [H, invOnUnits]; split_ifs with i v <;> simp [hχ.norm_eq_one, *]
  have ⟨g, m, _⟩ :=
    isPrimitiveMatrix_iff.1 (isPrimitiveMatrix_iff_isIntegralUnit_det.2 ⟨hs.mul i, v⟩)
  erw [← Q.right_mul _ m, ← congrFun (hc (k.2.isIntMatrix_inv.mul (i.sub (hx.mul m.isIntMatrix)))),
    (_ : V.ϖ ^ c • _ + _ = y)]; grind [hχ.norm_eq_one v, norm_zero]
  simp [d, *, smul_sub, ← Matrix.mul_assoc, sub_sub]

/-- Let P be GL_n(F)-stable and M contain all S_z(y) = S₀(y + LzK'y), S₀ the standard datum of
K', with L, K' blocks of an `IntegralFrame`.
If P contains each element of M killed by all Λ with Λ(S_z) = ψ(tr Tz)Λ(S₀), and Λ(S₀) =
0 if T is unimodular, then P contains every locally constant function having a partner. -/
lemma IntegralFrame.partner_mem_of_unimodular_vanishing {ψ} {M : Submodule ℂ _} (hψ :
  HasIntegralConductor ψ) :
  let S (z : Matrix b b F) y := stdColDatum χ A.K' (y + A.L * z * (A.K' * y))
  (∀ z, S z ∈ M) →
    (∀ Ψ ∈ M, (∀ T (Λ : _ →ₗ[ℂ] ℂ), (∀ z, Λ (S z) = ψ (T * z).trace • Λ (stdColDatum χ
  A.K')) → (IsPrimitiveMatrix O T → Λ (stdColDatum χ A.K') = 0) → Λ Ψ = 0) → Ψ ∈ P) → Ψ ∈ P := by
  obtain ⟨R, π, η, κ, u, d⟩ := id hχ
  let l r := ite (r = 1) 1 (@map b b _ _ r (surjInv κ.1))
  intro S hM h₂
  obtain ⟨⟨c, _, aK, aL, aK', _⟩, ⟨φ, hφ, e⟩, hl⟩ := A.blocks_spec,
    exists_primitive_residue_addChar κ hψ.2, fun r ↦ congrFun₂ (by aesop : (l r).map π = r)
  use partner_mem_of_stdColDatum hP hS hΨ Q (hP (-V.ϖ⁻¹ • 1) _ (h₂ (∑ r, η r.det • S (V.ϖ.2 •
    (l r).map (↑))) (sum_mem (by bound)) fun T Λ hZ _ ↦ by_contra ?_)) (aL.sub (aK.smul ϖ_mem)) c
    (by simp [*]) _ (fun y ↦ .trans (sum_apply ..) ((sum_filter_ne_zero _).symm.trans
    (sum_eq_card_nsmul ?_))) (card_ne_zero.2 ⟨1, by simp [l, ← Units.smul_def, S, invOnUnits, *]⟩)
  simp_intro q [hZ, ← mul_assoc, ← sum_mul]
  have i a b := (hψ.2 _).1 fun s _ ↦ by simpa [trace_mul_single] using ((right_eq_mul₀ q.2).1
    (.trans
    (congrArg _ (by grind [stdColDatum, IsIntMatrix.add, mul, IsIntMatrix.sub, =_ Matrix.mul_assoc,
    add_sub_cancel_right, Matrix.mul_add, IsIntMatrix, zero_mem])) (hZ (.single b a s))))
  obtain := (matrix_gauss_sum hφ u (η ·.det) (by simp)).1 (of (π ⟨_, i · ·⟩)), d (det (of (⟨_, i ·
    ·⟩))), isPrimitiveMatrix_of_stdColDatum_ne_zero (χ := χ) .one T, (e <| trace <|
    of (⟨_, i · ·⟩) * l ·)
  simp_all [matrixFourier, trace, mul_apply, det_apply', η.inv_apply_eq_inv, IsIntMatrix]
  simp_intro r hr
  obtain ⟨_, g, i, k, _⟩ := d (l r).det, show IsIntMatrix O ((l r).map (·.1)) by
    simp [IsIntMatrix], isIntMatrix_of_stdColDatum_ne_zero aK' hr.2
  obtain := d (det (of (⟨_, g.mul k · ·⟩) - of (⟨_, ϖ_mem⟩ * ⟨_, mul c i · ·⟩))), d (det (of (⟨_,
    g.mul k · ·⟩))), (aL.mul (g.mul k)).sub (i.smul ϖ_mem), invOnUnits_mul (χ :=
    χ) g.det_mem k.det_mem
  simp_all [↓S, ↓← det_mul, det_apply, (κ.2 _).2, ← Matrix.mul_assoc, Units.smul_def,
    smul_smul, ← mul_assoc, -MulMemClass.mk_mul_mk]
