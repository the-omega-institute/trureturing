/- GID: D5/S3/Zeros/GRH/New/TwistedHecke/InterlacingCone
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/TwistedHecke/InterlacingCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.TwistedHecke.InterlacingCone. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/TwistedHecke/InterlacingCone.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.HaarUnique
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Dimension bounds mod p from flags and a cone volume (see New.TwistedHecke.Counting).

This file: Cyclic interlacing cone volume as a signed sum over permutations, via determinant of
indicators. The cyclic interlacing cone fills the share of one flag in volume. -/

open Fin Finset Set ENNReal Equiv Fintype LinearMap Matrix MeasureTheory Tuple

variable {k m : ℕ} {T : Type} [Add T] [One T] (v : T → Bool) (P : ℝ) (k' : ℕ)

/-- For permutations σ_j, the linear map ν ↦ β with β(b,j) = ±(P·ν(b,j+1) − ν(σ_j b, j)), the
sign being + if v j is true and − otherwise. -/
@[simps!] def permStep (σ : T → Perm (Fin k)) : Module.End ℝ (Fin k × T → ℝ) := .pi fun x ↦
  ite (v x.2) (1 : ℝ) (-1) • (P • .proj (x.1, x.2 + 1) - .proj (σ x.2 x.1, x.2))

/-- The set Σ of real vectors β ≥ 0 with ∑_b β(b,j) in [D_j − 1, D_j] for every j. -/
def slab (D : T → ℝ) := {β : Fin k' × T → ℝ | 0 ≤ β ∧ ∀ j, ∑ b, β (b, j) ∈ Icc (D j - 1) (D j)}

/-- The cone of ν such that, for all j and b: P·ν(b+1,j+1) ≤ ν(b,j) if v j is true, and ν(b+1,j)
≤ P·ν(b,j+1) otherwise. -/
def pieriCone := {ν | ∀ j (b b' : Fin k), b.1 + 1 = b' → permStep v P 1 ν (ite (v j) b' b, j) ≤
  ν (b, j) - ν (b', j)}

/-- For weakly decreasing x, y in ℝ^k, the matrix with (b,c) entry 1 if y_c < x_b and 0
otherwise has determinant 1 if x₁ > y₁ ≥ x₂ > y₂ ≥ ⋯ ≥ x_k > y_k, and 0 otherwise. -/
lemma det_interlacing_indicator {x y : Fin k → ℝ} (hx : Antitone x) (hy : Antitone y) :
  det (of fun b c ↦ ite
  (y c < x b) (1 : ℝ) 0) = ite ((∀ b, y b < x b) ∧ ∀ b c, b.1 + 1 = c.1 → x c ≤ y b) 1 0 := by
  induction' k with k ih
  · simp
  obtain ⟨b, h⟩ | h := exists_or_forall_not fun b ↦ y 0 < x (succ b)
  · rw [det_zero_of_row_eq b.succ_ne_zero] <;> [grind [hy b.castSucc.zero_le]; ext c]
    grind [of_apply, hy c.zero_le, hx b.succ.zero_le]
  simp [det_succ_column_zero', sum_univ_succ, forall_fin_succ, h]
  erw [ih] <;> grind [Antitone]

omit [Add T] [One T] in
/-- For a finite set of letters, `slab` k D is bounded. -/
lemma isBounded_inter_slab [Fintype T] (D : T → ℝ) Y :
    Bornology.IsBounded (Y ∩ slab k D) := (Metric.isBounded_Icc ..).subset fun _ ⟨_, h, g⟩ ↦
    ⟨h, fun x ↦ (single_le_sum (fun b _ ↦ h (b, _)) (by simp)).trans (g _).2⟩

/-- Let P > 1, q = P^{m+1}, and `permStep` v P 1 ν ∈ Ω exactly when ν ∈ `pieriCone` v P. Then
vol(Ω ∩ Σ) = (q − 1)^k/k! · ∑_{τ∈S_k} sgn(τ)/|det(q − A_τ)| · vol(Σ), with Σ = `slab` k
D and A_τ the permutation matrix. -/
lemma volume_inter_slab_eq_signed_sum {v : Fin (m + 1) → _} (hP : 1 < P) D {Ω : Set _} (hΩ : ∀ ν,
  permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) : let Δ τ := |(1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ τ).det|
  volume.real (Ω ∩ slab k D) =
          Δ id / k.factorial * (∑ τ : Perm (Fin k), τ.sign / Δ τ) * volume.real (slab k D) := by
  let S σ (τ : _ → Perm (Fin k)) (Y : Set _) := {ν | let β := permStep v P σ (ν ∘ prodCongrLeft τ)
    (∀ j, ∑ b, permStep v P 1 ν (b, j) ∈ Icc (D j - 1) (D j)) ∧ (∀ j b, 0 < β (b, j)) ∧ β ∈ Y}
  -- the map of `σ` is injective, as `P > 1`
  have z σ : (@permStep k _ _ _ v P σ).det ≠ 0 := (bot_lt_ker_of_det_eq_zero · |>.not_ge fun ν h ↦
    norm_le_zero_iff.1 (by nlinarith [(funext fun x ↦ by simpa [ite_eq_iff'] using (mul_eq_zero.1
    congr($h (_, _ - 1))) : P • ν = ν ∘ _) ▸ pi_norm_comp_le .., norm_smul P ν, P.le_norm_self]))
  -- change of variables; the walls `β x = 0` are null sets
  have V σ τ Y : volume (S σ τ Y) = .ofReal |(permStep v P σ * (Perm.permMatrix ℝ
    (prodCongrLeft τ)).toLin').det⁻¹| * volume (Y ∩ slab k D) := by
    erw [← measure_inter_conull (ae_all_iff.2 (Measure.ae_eval_ne _ · 0)) (s := Y ∩ _), ←
      Measure.addHaar_preimage_linearMap _ (by simp [z])]
    congr with ν
    simp [S, slab, -Perm.coe_one, ← mul_sum, ← Perm.mul_apply, Pi.le_def, -Perm.coe_mul,
      fun e j ↦ Equiv.sum_comp e (ν ⟨·, j⟩), permMatrix_mulVec, ↓permStep_apply]
    grind
  let B : (_ → ℝ) →ₗ[ℝ] Fin k × Fin m.succ → ℝ := LinearMap.pi fun x ↦ P⁻¹ ^ x.2.1.succ • proj x.1
  have ⟨c, hc⟩ : ∃ c, ∀ σ, (@permStep k _ _ _ v P σ).det = c * (1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ
      (List.ofFn σ).prod).det := ⟨_, fun σ ↦ by
    let G := (Perm.permMatrix ℝ (prodCongrLeft (partialProd σ ∘ castSucc))).toLin'
    let A := funLeft ℝ ℝ ((last _).partialProd σ ·, last m)
    rw [show _ • _ = A ∘ₗ B by ext; simp +zetaDelta [partialProd, List.take_of_length_le]]
    simpa [← det_toMatrix' (_ - _), toMatrix'_comp, det_one_sub_mul_comm B.toMatrix', field, G]
      using congr(($(show permStep v P σ * G = (permStep v 1 1 - permStep v 0 1) * G * (P • 1 -
      .pi fun x ↦ x.2.cases 0 (proj ⟨x.1, ·.castSucc⟩)) * (1 - B ∘ₗ A) by
      ext x ⟨b, j⟩
      cases j using lastCases <;>
      simp +zetaDelta [← succ_last, partialProd_succ, permMatrix_mulVec] <;> grind)).det)⟩
  have e ν : ∑ τ, (S 1 τ Ω).indicator (fun _ ↦ 1) ν =
      ∑ σ, (S σ 1 univ).indicator (fun _ ↦ ((List.ofFn σ).prod.sign : ℝ)) ν := ?_
  · simpa [↓integral_finsetSum, integrable_indicator_iff, fun σ ↦
      (by simp [S, hΩ, pieriCone, -permStep_apply]; use ?_ <;> fun_prop :
      MeasurableSet (S σ 1 univ) ∧ MeasurableSet (S 1 σ Ω)), ↓(V ..).trans_lt (mul_lt_top coe_lt_top
      (isBounded_inter_slab ..).measure_lt_top), -enorm_mul, Measure.real, hc, field, card_perm,
      ↓← ((prodCongrLeft fun g : Fin m → _ ↦ .mulRight (List.ofFn g).prod⁻¹).trans
        (consEquiv fun _ ↦ Perm
      (Fin k))).sum_comp, sum_prod_type_right, ← sum_mul, div_eq_inv_mul, abs_unit_intCast, V, by
      simpa [hc] using z 1, mul_right_comm _ _ (Int.cast _), Nat.cast_comm] using congr(∫ ν, $(e ν))
  -- the product of the determinants, expanded, and read after sorting
  let τ j := sort (-ν ⟨·, j⟩)
  have anti j := (monotone_sort (-ν ⟨·, j⟩)).neg
  simp_rw [indicator, S, hΩ, pieriCone, mem_ofPred, ite_and (∀ j, _ ∈ _), sum_ite_irrel,
    ← forall_and]
  rw [sum_eq_single τ fun σ ne ↦ ite_eq_right fun h ↦ ne (funext fun j ↦ eq_sort_iff'.2
    ((strictMono_iff_forall_covBy _).2 fun _ _ e ↦ .left _ _ (by
    simpa using (h ..).1.trans_le ((h ..).2 _ e.coe_fin.succ_eq)))), eq_comm]
  congr
  trans ∏ j, ((of fun b' b : Fin k ↦ ite (0 < permStep v P (fun _ ↦ .swap b b') ν (b, j)) 1
    0).reindex (τ j).symm (τ (j + 1)).symm).det
  · simp [↓det_reindex, ← Int.cast_prod, ← Units.coe_prod, det_apply', map_list_prod,
      prod_ofFn, -List.ofFn_succ, (AddGroup.addRight_bijective 1).prod_comp (Perm.sign <| τ ·),
      prod_univ_sum, Fintype.prod_ite_zero, -Units.val_mul]
  convert Fintype.prod_boole with j
  have a := (anti (j + 1)).const_mul (by bound : 0 ≤ P)
  by_cases v j <;> [convert (det_transpose _).trans (det_interlacing_indicator a (anti j)); convert
    det_interlacing_indicator (anti j) a using 2] <;> simp [← ext_iff, τ, *, forall_and, sub_add]
  infer_instance

/-- Let P > 1, q = P^N, and let Ω be a set such that `permStep` v P 1 ν lies in Ω exactly when ν
lies in `pieriCone` v P. Then ∏_{l=1}^{k} (q^l − 1)/(q − 1) · vol(Ω ∩ Σ) = vol(Σ), for Σ =
`slab` k D. -/
lemma prod_mul_volume_inter_slab {N} [NeZero N] {v P} (hP : 1 < P) (D : ZMod N → ℝ) {Ω} (hΩ : ∀ ν,
  permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) : (∏ l : Fin k, ((P ^ N) ^ (l.1 + 1) - 1) /
  (P ^ N - 1)) * volume.real (Ω ∩ slab k D) = volume.real (slab k D) := by
  have q := one_lt_pow₀ hP (NeZero.ne N)
  cases N; bound
  erw [volume_inter_slab_eq_signed_sum P hP D hΩ]
  set P := P ^ _
  -- the case of a single index (m = 0) with v = ⊤ and q = P^N (renamed P by the `set`): the cone is
  -- an orthant in the coordinates `β_l - q β_(l+1)`, and rescaling them maps its part of `Σ` onto
  -- `Σ`
  let d i := (P ^ (i + 1) - 1) / (P - 1)
  let p c : (Fin k × Fin 1 → ℝ) →ₗ[ℝ] ℝ := if h : c < k then .proj (⟨c, h⟩, 0) else 0
  let F : Module.End ℝ _ := LinearMap.pi fun x ↦ d x.1 • (p x.1 - P • p (x.1 + 1))
  have det : F.det = ∏ b : Fin k, d b := by
    rw [← det_toMatrix', ← det_reindex_self (prodUnique ..), det_of_isUpperTriangular]
      <;> simp [Fin.ext_iff, F, p, DFunLike.dite_apply, BlockTriangular]; lia
  have deg β : ∑ b, F β (b, 0) = ∑ b, β (b, 0) := sub_eq_zero.1 (by convert (sum_range_sub' (fun c ↦
    (d c - 1) * p c β) k) <;> simp [sum_range, F, p, ↓← sum_sub_distrib, -smul_dite] <;> grind)
  have D0 : 0 < F.det := by simp [prod_pos, d, one_lt_pow₀, *]
  have := @volume_inter_slab_eq_signed_sum k 0 P ⊤ q 1 (pieriCone ⊤ P) (by simp [pieriCone, field])
  erw [@Set.ext _ (_ ∩ _) (F ⁻¹' slab k 1), Measure.real, volume.addHaar_preimage_linearMap D0.ne',
    toReal_mul, mul_left_inj' (toReal_pos (mt (measure_mono_null (s := .Icc 0 (↑k)⁻¹) fun β ⟨h, g⟩ ↦
    ⟨h, by simp; grw [← h _, g _]; simp [mul_inv_le_one]⟩) (by simp [Real.volume_Icc_pi]))
    (Set.univ_inter _ ▸ isBounded_inter_slab ..).measure_lt_top.ne).ne', pow_one] at this
  simp [↓← this, ← det, abs_of_nonneg, D0.le, field, d]; rfl
  simp [slab, deg, ← and_assoc, pieriCone, Pi.le_def]
  simpa [F, p, DFunLike.dite_apply, d, one_lt_pow₀, *] using fun β _ _ ↦ ⟨by bound, fun h ↦
    ⟨by grind, WellFoundedGT.fix fun b I ↦ (h b).trans' (by grind [mul_nonneg])⟩⟩
