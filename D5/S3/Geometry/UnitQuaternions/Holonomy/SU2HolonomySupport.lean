/- GID: D5/S3/Geometry/UnitQuaternions/Holonomy/SU2HolonomySupport
   generality: G
   mirror-B: none(waiver:covered-by-chordal-su2-sharp-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four-point holonomy moments bound both the nearest-point norm and the overlap with a largest-eigenvalue quaternionic line. -/

import D5.S3.Geometry.UnitQuaternions.Holonomy.SU2HolonomyHemisphere

/-!
Omega original.

Four-point holonomy moments bound both the nearest-point norm and the
overlap with a largest-eigenvalue quaternionic line.
-/

open scoped Quaternion BigOperators InnerProductSpace

noncomputable section

namespace Omega.Geometry.HolonomySpectrum

open Real Finset Omega.Geometry.UnitQuaternion

local notation "U" => unitary ℍ[ℝ]

/-- The lower cosine supplied by the four-point holonomy moment bound. -/
def holonomyCosine (t : ℝ) : ℝ :=
  (1 + 2 * t) * (1 - 3 * t - 3 * t ^ 2) / √(1 - 2 * t - 2 * t ^ 2)

private theorem holonomyCosine_pos {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < holonomyCosine t := by
  have hsq := pow_le_pow_left₀ ht ht' 2
  unfold holonomyCosine
  apply div_pos
  · exact mul_pos (by positivity) (by linarith)
  · exact sqrt_pos.mpr (by linarith)

private theorem holonomyCosine_le_one {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 4)
    (hθ : 0 ≤ 4 * t ^ 2 + 4 * t - 1) : holonomyCosine t ≤ 1 := by
  let N := (1 + 2 * t) * (1 - 3 * t - 3 * t ^ 2)
  let X := 1 - 2 * t - 2 * t ^ 2
  have hs := pow_le_pow_left₀ ht ht' 2
  have hX : 0 < X := by dsimp [X]; linarith
  have hN : 0 < N := mul_pos (by positivity) (by linarith)
  have hp : N * (1 + 2 * t) ≤ X := by
    dsimp [N, X]
    nlinarith only [mul_nonneg (mul_nonneg ht (by positivity : 0 ≤ t + 1)) hθ]
  have hN₁ : N ≤ 1 + 2 * t := by
    dsimp [N]
    exact mul_le_of_le_one_right (by positivity) (by nlinarith [sq_nonneg t])
  have hN₂ : N ^ 2 ≤ X := by
    have h := mul_le_mul_of_nonneg_left hN₁ hN.le
    nlinarith only [h, hp]
  change N / √X ≤ 1
  rw [div_le_iff₀ (sqrt_pos.mpr hX), one_mul]
  exact le_sqrt_of_sq_le hN₂

private theorem four_rayleigh_data (g : HolonomyGains (Fin 4)) {w : Fin 4 → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {c : ℝ} (hc : c ≤ 1)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      c ≤ (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re) :
    ∃ μ : Fin 4 → ℝ, Antitone μ ∧
      ∃ b : OrthonormalBasis (Fin 4 × Fin 4) ℝ (Columns (Fin 4)),
        (∀ i k, realAction (holonomyMatrix g w) (b (i,k)) = μ i • b (i,k)) ∧
        μ 0 + μ 1 + μ 2 + μ 3 = 1 ∧ μ 0 ^ 2 + μ 1 ^ 2 + μ 2 ^ 2 + μ 3 ^ 2 = 1 ∧
        (5 + 3 * c) / 8 ≤ μ 0 ^ 3 + μ 1 ^ 3 + μ 2 ^ 3 + μ 3 ^ 3 := by
  obtain ⟨ν, hν, b, hb⟩ := exists_ordered_spectrum (isHermitian_holonomyMatrix g w)
  let μ : Fin 4 → ℝ := fun i => ν i
  have hM₁ := spectrum_moments (holonomyMatrix g w) b hb 1
  have hM₂ := spectrum_moments (holonomyMatrix g w) b hb 2
  have hM₃ := spectrum_moments (holonomyMatrix g w) b hb 3
  simp only [pow_one, holonomy_trace g hw, hs] at hM₁
  simp only [holonomy_trace_sq g hw, hs, one_pow] at hM₂
  have h₁ : ∑ i, μ i = 1 := hM₁
  have h₂ : ∑ i, μ i ^ 2 = 1 := hM₂
  have h₃ : (5 + 3 * c) / 8 ≤ ∑ i, μ i ^ 3 := by
    have htrace := holonomy_trace_cube_lower g hw hs htri
    have hw' := (simplex_moments w hw hs (by simp)).2
    have hw₂ : (5 / 8 : ℝ) ≤ ∑ i, (3 * w i ^ 2 - 2 * w i ^ 3) := by
      change (3 * (4 : ℝ) - 2) / 4 ^ 2 ≤ _ at hw'
      norm_num at hw'
      simpa only [sum_sub_distrib] using hw'
    have hmul := mul_le_mul_of_nonneg_left hw₂ (sub_nonneg.mpr hc)
    change _ ≤ ∑ i, ν i ^ 3
    rw [hM₃]
    linarith only [htrace, hmul]
  rw [Fin.sum_univ_four] at h₁ h₂ h₃
  exact ⟨μ, hν, b, hb, by linarith only [h₁], by linarith only [h₂], by linarith only [h₃]⟩

/-- The same largest-eigenvalue quaternionic line has large overlap with
every column that meets the Rayleigh lower bound. -/
theorem four_point_spectral_support (g : HolonomyGains (Fin 4)) {w : Fin 4 → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hθ : 0 ≤ 4 * t ^ 2 + 4 * t - 1)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → 1 - 6 * t ^ 2 - 4 * t ^ 3 ≤
      (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re) :
    ∃ v : Columns (Fin 4), ‖v‖ = 1 ∧ ∀ x : Columns (Fin 4), ‖x‖ = 1 →
      (1 + 3 * (1 - 6 * t ^ 2 - 4 * t ^ 3)) / 4 ≤
        ⟪x, realAction (holonomyMatrix g w) x⟫_ℝ →
      (1 + holonomyCosine t) / 2 ≤ ‖pairing v x‖ ^ 2 := by
  have hc : 1 - 6 * t ^ 2 - 4 * t ^ 3 ≤ 1 := by
    nlinarith only [sq_nonneg t, pow_nonneg ht 3]
  obtain ⟨μ, hμ, b, hb, hm₁, hm₂, hm₃⟩ := four_rayleigh_data g hw hs hc htri
  obtain ⟨v, hv, htop⟩ :=
    top_eigenline_bound (by decide) _ (isHermitian_holonomyMatrix g w) μ hμ b hb
  refine ⟨v, hv, fun x hx hr => ?_⟩
  have h := htop x hx
  let ω := 2 * ‖pairing v x‖ ^ 2 - 1
  have hR : (1 + 3 * (1 - 6 * t ^ 2 - 4 * t ^ 3)) / 2 ≤ μ 0 + μ 1 + ω * (μ 0 - μ 1) := by
    change _ ≤ μ 1 + (μ 0 - μ 1) * ‖pairing v x‖ ^ 2 at h
    dsimp [ω]
    linarith only [hr, h]
  have hp := four_point_support ht ht' hθ (hμ (by decide : (0 : Fin 4) ≤ 1))
    (hμ (by decide : (1 : Fin 4) ≤ 2)) (hμ (by decide : (1 : Fin 4) ≤ 3))
    hm₁ hm₂ hm₃ hR
  change holonomyCosine t ≤ ω at hp
  dsimp [ω] at hp
  linarith only [hp]

/-- Two uniformly aligned weighted columns have quaternionic overlap
at least the holonomy cosine. -/
theorem four_point_overlap_lower (g : HolonomyGains (Fin 4)) {w : Fin 4 → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hθ : 0 ≤ 4 * t ^ 2 + 4 * t - 1)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → 1 - 6 * t ^ 2 - 4 * t ^ 3 ≤
      (↑(g.gain i j * g.gain j k * g.gain k i) : ℍ[ℝ]).re)
    (x y : Columns (Fin 4)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hR : (1 + 3 * (1 - 6 * t ^ 2 - 4 * t ^ 3)) / 2 ≤
      ⟪x, realAction (holonomyMatrix g w) x⟫_ℝ +
      ⟪y, realAction (holonomyMatrix g w) y⟫_ℝ) :
    holonomyCosine t ≤ ‖pairing x y‖ := by
  have hc : 1 - 6 * t ^ 2 - 4 * t ^ 3 ≤ 1 := by
    nlinarith only [sq_nonneg t, pow_nonneg ht 3]
  by_cases ha : ‖pairing x y‖ < 1
  · obtain ⟨μ, hμ, b, hb, hm₁, hm₂, hm₃⟩ := four_rayleigh_data g hw hs hc htri
    have hu := rayleigh_two_unit_le_norm (by decide) _ μ hμ b hb x y hx hy ha
    change _ ≤ (1 + ‖pairing x y‖) * μ 0 + (1 - ‖pairing x y‖) * μ 1 at hu
    apply four_point_support ht ht' hθ (hμ (by decide : (0 : Fin 4) ≤ 1))
      (hμ (by decide : (1 : Fin 4) ≤ 2)) (hμ (by decide : (1 : Fin 4) ≤ 3)) hm₁ hm₂ hm₃
    linarith only [hR, hu]
  · exact (holonomyCosine_le_one ht ht' hθ).trans (le_of_not_gt ha)


theorem weightedColumn_lower_at {w : Fin 4 → ℝ} (g : HolonomyGains (Fin 4)) (q : Fin 4 → U)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {c : ℝ} (hc : c ≤ 1)
    (h : ∀ i j, i ≠ j → c ≤ (↑((q i)⁻¹ * g.gain i j * q j) : ℍ[ℝ]).re) :
    (1 + 3 * c) / 4 ≤ ⟪weightedColumn w q, realAction (holonomyMatrix g w) (weightedColumn w q)⟫_ℝ := by
  have hW := (simplex_moments w hw hs (by simp)).1
  have hW' : (1 / 4 : ℝ) ≤ ∑ i, w i ^ 2 := hW
  have h' := rayleigh_weightedColumn_lower g q hw hs h
  have hmul := mul_le_mul_of_nonneg_left hW' (sub_nonneg.mpr hc)
  linarith only [h', hmul]

/-- The nonzero nearest point of a holonomy patch has norm at least the
four-point holonomy cosine. -/
theorem SU2Patch.nearest_norm_lower {ι : Type*} [Fintype ι] {δ t : ℝ}
    (P : SU2Patch ι δ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hθ : 0 ≤ 4 * t ^ 2 + 4 * t - 1)
    (hc : 1 - 6 * t ^ 2 - 4 * t ^ 3 ≤ cos δ) {v : ℍ[ℝ]}
    (hv : v ∈ convexHull ℝ (Set.range fun i => (P.point i : ℍ[ℝ]))) (hv₀ : 0 < ‖v‖)
    (hV : ∀ i, ‖v‖ ^ 2 ≤ ⟪v, (P.point i : ℍ[ℝ])⟫_ℝ) :
    holonomyCosine t ≤ ‖v‖ := by
  let c := 1 - 6 * t ^ 2 - 4 * t ^ 3
  have hc₁ : c ≤ 1 := hc.trans (cos_le_one _)
  obtain ⟨f, w, hw, hs, hwv⟩ := exists_contact_fin_four hv hv₀ hV
  let Q := P.pullback f
  let M := Q.holonomy
  let a := weightedColumn w (fun _ => (1 : U))
  let b := weightedColumn w Q.point
  have ha : ‖a‖ = 1 := norm_weightedColumn _ hw hs
  have hb : ‖b‖ = 1 := norm_weightedColumn _ hw hs
  have hab : pairing a b = v := by
    dsimp only [a,b]
    rw [pairing_weightedColumn _ _ hw]
    simpa only [inv_one, one_mul, Q, SU2Patch.pullback] using hwv
  have h1 := weightedColumn_lower_at M (fun _ => (1 : U)) hw hs hc₁
    (fun i j hij => by simpa only [inv_one, one_mul, mul_one] using hc.trans (Q.edge i j hij))
  have h2 := weightedColumn_lower_at M Q.point hw hs hc₁
    (fun i j hij => hc.trans (Q.aligned i j hij))
  have hsum : (1 + 3 * c) / 2 ≤
      ⟪a, realAction (holonomyMatrix M w) a⟫_ℝ + ⟪b, realAction (holonomyMatrix M w) b⟫_ℝ := by
    exact (show (1 + 3 * c) / 2 = (1 + 3 * c) / 4 + (1 + 3 * c) / 4 by ring) ▸ (add_le_add h1 h2)
  have h := four_point_overlap_lower M hw hs ht ht' hθ
    (fun i j k hij hjk hik => hc.trans (Q.triangle i j k hij hjk hik))
    a b ha hb hsum
  rwa [hab] at h

/-- The holonomy cosine supplies a cap whenever the five-point spectral
obstruction excludes the origin. -/
theorem SU2Patch.exists_holonomy_cap {ι : Type*} [Fintype ι] [Nonempty ι] {δ t s : ℝ}
    (P : SU2Patch ι δ) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) (hθ : 0 ≤ 4 * t ^ 2 + 4 * t - 1)
    (hc : 1 - 6 * t ^ 2 - 4 * t ^ 3 ≤ cos δ) (hc₀ : 9 / 16 < cos δ)
    (hs₀ : 0 < s) (hs₁ : s ≤ 1) (hs : s ≤ holonomyCosine t) :
    Nonempty (SU2Cap P.point (arccos s)) := by
  obtain ⟨v, hv, hsupport⟩ := SphericalJung.exists_min_norm_support (fun i => (P.point i : ℍ[ℝ]))
  have hv₀ : 0 < ‖v‖ := norm_pos_iff.mpr (fun he => P.zero_not_mem hc₀ (he ▸ hv))
  have hnorm := hs.trans (P.nearest_norm_lower ht ht' hθ hc hv hv₀ hsupport)
  exact SU2Cap.of_nearest (arccos_nonneg _) (arccos_le_pi _) v hv hv₀
    ((cos_arccos (by linarith) hs₁).le.trans hnorm) hsupport


/-- The closed-form holonomy cosine governs caps throughout the interval
from a quarter of pi to the five-point hemisphere threshold. -/
theorem SU2Patch.exists_cap_of_holonomy_defect {ι : Type*} [Fintype ι] [Nonempty ι]
    {δ : ℝ} (P : SU2Patch ι δ) (hlo : π / 4 ≤ δ) (hhi : δ < arccos (9 / 16)) :
    let t := cos ((π - δ) / 3) - 1 / 2
    6 * t ^ 2 + 4 * t ^ 3 = 1 - cos δ ∧
      Nonempty (SU2Cap P.point (arccos (holonomyCosine t))) := by
  let a := (π - δ) / 3
  let t := cos a - 1 / 2
  have hδ : 0 ≤ δ := by linarith [pi_pos]
  have hδπ : δ ≤ π := hhi.le.trans (arccos_le_pi _)
  have hc : 9 / 16 < cos δ := by
    have hs := strictAntiOn_cos ⟨hδ, hδπ⟩ ⟨arccos_nonneg _, arccos_le_pi _⟩ hhi
    rwa [cos_arccos (by norm_num) (by norm_num)] at hs
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha' : a ≤ π / 4 := by dsimp [a]; linarith
  have hcos := cos_le_cos_of_nonneg_of_le_pi ha (by linarith [pi_pos] : π / 4 ≤ π) ha'
  rw [cos_pi_div_four] at hcos
  have ht₀ : (√(2 : ℝ) - 1) / 2 ≤ t := by dsimp [t]; linarith
  have ht : 0 ≤ t := by
    have h : (1 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
    linarith only [ht₀, h]
  have htrig := cos_three_mul a
  have hcosneg : cos (π - δ) = -cos δ := cos_pi_sub δ
  rw [show 3 * a = π - δ by dsimp [a]; ring, hcosneg] at htrig
  have he : 6 * t ^ 2 + 4 * t ^ 3 = 1 - cos δ := by
    dsimp [t]
    linarith only [htrig]
  have hθ : 0 ≤ 4 * t ^ 2 + 4 * t - 1 := by
    have h : (1 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
    have hn : 0 ≤ (√(2 : ℝ) - 1) / 2 := by linarith
    nlinarith only [pow_le_pow_left₀ hn ht₀ 2, ht₀, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hquarter : t ≤ 1 / 4 := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h (by norm_num : (0 : ℝ) ≤ 1 / 4) two_ne_zero
    have hhh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) h.le 3
    linarith only [hh, hhh, he, hc]
  refine ⟨he, P.exists_holonomy_cap ht hquarter hθ ?_ hc
    (holonomyCosine_pos ht hquarter) (holonomyCosine_le_one ht hquarter hθ) le_rfl⟩
  linarith only [he]

end Omega.Geometry.HolonomySpectrum
