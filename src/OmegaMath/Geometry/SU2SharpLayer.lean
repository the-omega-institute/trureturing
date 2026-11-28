import OmegaMath.Geometry.SU2HolonomySupport
import OmegaMath.Geometry.SU2RankOneOverlap

/-!
Omega original.

The asymmetric overlap inequality excludes a same-layer edge at the sharp
reconstruction angle on the second defect interval.
-/

open scoped Quaternion InnerProductSpace BigOperators

noncomputable section

namespace Omega.Geometry.HolonomySpectrum

open Real Finset Omega.Geometry.UnitQuaternion Omega.Geometry.SU2ChordalIntervals

local notation "U" => unitary ℍ[ℝ]

private theorem re_le_norm (x : ℍ[ℝ]) : x.re ≤ ‖x‖ := by
  have h := real_inner_le_norm x (1 : ℍ[ℝ])
  rw [Quaternion.inner_def, star_one, mul_one, norm_one, mul_one] at h
  exact h

private theorem cos_round (x y : U) : cos (roundDist x y) = ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ := by
  have h := real_inner_mem_Icc_of_norm_eq_one (norm_coe x) (norm_coe y)
  exact cos_arccos h.1 h.2

private theorem re_pairing_weighted {w : Fin 4 → ℝ} (hw : ∀ i, 0 ≤ w i) (q r : Fin 4 → U) :
    (pairing (weightedColumn w q) (weightedColumn w r)).re =
      ∑ i, w i * ⟪(q i : ℍ[ℝ]), (r i : ℍ[ℝ])⟫_ℝ := by
  rw [← real_inner_eq_re_pairing, PiLp.inner_apply]
  simp only [weightedColumn_apply, real_inner_smul_left, real_inner_smul_right]
  exact sum_congr rfl (fun i _ => by rw [← mul_assoc, mul_self_sqrt (hw i)])

/-- The two translated cap centers are within the sharp comparison angle
throughout the second interval. -/
theorem same_layer_second_range {ι κ : Type*} [Fintype ι] {δ t s k G : ℝ}
    (P : SU2Patch ι δ) (Q : SU2Patch κ δ) (e : ι → κ) (u : U)
    (C : SU2Cap P.point (arccos s)) (D : SU2Cap Q.point (arccos s))
    (hp : ∀ i, roundDist (P.point i * u) (Q.point (e i)) ≤ δ)
    (hhol : ∀ i j, P.holonomy.gain i j = Q.holonomy.gain (e i) (e j))
    (hδ : 0 ≤ δ) (hδπ : δ ≤ π) (hπ : (434 / 125) * δ ≤ π)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hθ : 0 ≤ 4 * t ^ 2 + 4 * t - 1)
    (hc : 1 - 6 * t ^ 2 - 4 * t ^ 3 ≤ cos δ)
    (hs : 0 < s) (hs' : s < 1) (hspec : s ≤ holonomyCosine t)
    (hangle : 0 ≤ (434 / 125) * δ - arccos s)
    (hk : cos ((434 / 125) * δ - arccos s) ≤ k) (hk₀ : k < 0)
    (hgap : 1 / 2 < cos δ - k) (hG : G ≤ (cos δ - (7 / 8) * k) ^ 2)
    (hcert : QuarticCertificate s G) :
    roundDist (C.center * u) D.center ≤ (434 / 125) * δ := by
  by_contra! hbad
  let R := arccos s
  let K : ℝ := 434 / 125
  let α := ‖C.nearest‖
  let v := (C.center * u)⁻¹
  let c := 1 - 6 * t ^ 2 - 4 * t ^ 3
  have hc₁ : c ≤ 1 := hc.trans (cos_le_one _)
  obtain ⟨f, w, hw, hw₁, hwz⟩ := exists_contact_fin_four C.mem_hull C.pos C.support
  let P₁ := (P.rightTranslate (u * v)).pullback f
  let Q₁ := (Q.rightTranslate v).pullback (e ∘ f)
  let M := P₁.holonomy
  have hM (i j : Fin 4) : M.gain i j = Q₁.holonomy.gain i j := hhol (f i) (f j)
  let a := weightedColumn w (fun _ => (1 : U))
  let b := weightedColumn w P₁.point
  let d := weightedColumn w Q₁.point
  have ha : ‖a‖ = 1 := norm_weightedColumn _ hw hw₁
  have hb : ‖b‖ = 1 := norm_weightedColumn _ hw hw₁
  have hd : ‖d‖ = 1 := norm_weightedColumn _ hw hw₁
  obtain ⟨z, hz, hzProj⟩ := four_point_spectral_support M hw hw₁ ht ht' hθ
    (fun i j l hij hjl hil => hc.trans (P₁.triangle i j l hij hjl hil))
  have hr₁ := weightedColumn_lower_at M (fun _ => (1 : U)) hw hw₁ hc₁
    (fun i j hij => by simpa only [inv_one, one_mul, mul_one] using hc.trans (P₁.edge i j hij))
  have hr₂ := weightedColumn_lower_at M P₁.point hw hw₁ hc₁
    (fun i j hij => hc.trans (P₁.aligned i j hij))
  have hr₃ := weightedColumn_lower_at M Q₁.point hw hw₁ hc₁
    (fun i j hij => by rw [hM]; exact hc.trans (Q₁.aligned i j hij))
  have hz₁ := hzProj a ha hr₁
  have hz₂ := hzProj b hb hr₂
  have hz₃ := hzProj d hd hr₃
  have hα : s ≤ α := by
    have h := C.cos_radius_le_nearest_norm (arccos_nonneg _) (arccos_le_pi _)
    rwa [cos_arccos (by linarith) hs'.le] at h
  have hab : pairing a b = (α : ℍ[ℝ]) := by
    dsimp only [a, b]
    rw [pairing_weightedColumn _ _ hw]
    simp only [inv_one, one_mul]
    change (∑ i, w i • ((P.point (f i) : ℍ[ℝ]) * (↑(u * v) : ℍ[ℝ]))) = _
    simp only [← smul_mul_assoc, ← sum_mul, hwz]
    have hsC : α • (C.center : ℍ[ℝ]) = C.nearest := by
      rw [C.normalized]
      change ‖C.nearest‖ • (‖C.nearest‖⁻¹ • C.nearest) = C.nearest
      rw [smul_smul, mul_inv_cancel₀ C.pos.ne', one_smul]
    rw [← hsC, smul_mul_assoc]
    have h : (C.center : ℍ[ℝ]) * (↑(u * v) : ℍ[ℝ]) = 1 := by
      change (↑(C.center * (u * v)) : ℍ[ℝ]) = 1
      rw [← mul_assoc, show (C.center * u) * v = 1 from mul_inv_cancel _]
      rfl
    rw [h, Algebra.smul_def, mul_one]
    rfl
  have hX (i : Fin 4) : (Q₁.point i : ℍ[ℝ]).re ≤ k := by
    have hdist : K * δ - R ≤ roundDist (1 : U) (Q₁.point i) := by
      have htri := round_triangle (C.center * u) (Q.point (e (f i))) D.center
      have hh := D.radius (e (f i))
      have he : roundDist (1 : U) (Q₁.point i) =
          roundDist (C.center * u) (Q.point (e (f i))) := by
        change roundDist (1 : U) (Q.point (e (f i)) * v) = _
        rw [← round_mul_right v (C.center * u) (Q.point (e (f i)))]
        rw [show (C.center * u) * v = 1 from mul_inv_cancel _]
      rw [he]
      dsimp only [K, R]
      linarith only [htri, hh, hbad]
    have hc' := cos_le_cos_of_nonneg_of_le_pi hangle (round_le_pi _ _) hdist
    rw [cos_round, Quaternion.inner_def] at hc'
    change ((1 : ℍ[ℝ]) * star (Q₁.point i : ℍ[ℝ])).re ≤ _ at hc'
    rw [one_mul, Quaternion.re_star] at hc'
    exact hc'.trans hk
  have hY (i : Fin 4) : cos δ ≤ ⟪(P₁.point i : ℍ[ℝ]), (Q₁.point i : ℍ[ℝ])⟫_ℝ := by
    apply (round_le_iff _ _ hδ hδπ).mp
    change roundDist (P.point (f i) * (u * v)) (Q.point (e (f i)) * v) ≤ δ
    rw [← mul_assoc, round_mul_right]
    exact hp (f i)
  let X := pairing a d
  let Y := pairing b d
  have hX' : X.re ≤ k := by
    dsimp only [X,a,d]
    rw [re_pairing_weighted hw]
    have h := sum_le_sum (s := univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hX i) (hw i))
    change (∑ i, w i * ((1 : ℍ[ℝ]) * star (Q₁.point i : ℍ[ℝ])).re) ≤ k
    rw [← sum_mul, hw₁, one_mul] at h
    simpa only [one_mul, Quaternion.re_star] using h
  have hY' : cos δ ≤ Y.re := by
    dsimp only [Y,b,d]
    rw [re_pairing_weighted hw]
    have h := sum_le_sum (s := univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hY i) (hw i))
    simpa only [← sum_mul, hw₁, one_mul] using h
  have hα' : α < 7 / 8 := by
    have h₁ := re_le_norm (pairing (b - a) d)
    rw [pairing_sub_left] at h₁
    change (Y-X).re ≤ _ at h₁
    have h₂ := quaternion_cauchy (x := b - a) (y := d)
    rw [pairing_sub_left, hd, mul_one] at h₂
    change ‖Y-X‖ ≤ ‖b-a‖ at h₂
    have hdist : 1 / 2 < ‖b-a‖ := by
      change Y.re - X.re ≤ _ at h₁
      linarith only [h₁, h₂, hX', hY', hgap]
    have hh := pow_lt_pow_left₀ hdist (by norm_num : (0 : ℝ) ≤ 1 / 2) two_ne_zero
    have hr : ⟪b, a⟫_ℝ = α := by
      rw [real_inner_comm, real_inner_eq_re_pairing, hab]
      rfl
    rw [norm_sub_sq_real, ha, hb, hr, one_pow] at hh
    linarith only [hh]
  have hpG : G ≤ ‖Y - (7 / 8 : ℝ) • X‖ ^ 2 := by
    apply hG.trans
    have hh := re_le_norm (Y - (7 / 8 : ℝ) • X)
    change Y.re - (7 / 8) * X.re ≤ _ at hh
    have hc' : 0 ≤ cos δ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith only [hπ, hδ]⟩
    have hnon : 0 ≤ cos δ - (7 / 8) * k := by
      linarith only [hc', hk₀]
    exact pow_le_pow_left₀ hnon (by linarith only [hh, hX', hY']) 2
  have hs₁ : (1 + s) / 2 ≤ ‖pairing a z‖ ^ 2 := by
    rw [norm_pairing_comm]
    linarith only [hspec, hz₁]
  have hs₂ : (1 + s) / 2 ≤ ‖pairing b z‖ ^ 2 := by
    rw [norm_pairing_comm]
    linarith only [hspec, hz₂]
  have hs₃ : (1 + s) / 2 ≤ ‖pairing d z‖ ^ 2 := by
    rw [norm_pairing_comm]
    linarith only [hspec, hz₃]
  exact asymmetric_overlap_excluded ha hb hd hz hs hs' hα hα' hab hs₁ hs₂ hs₃ hpG hcert

end Omega.Geometry.HolonomySpectrum
