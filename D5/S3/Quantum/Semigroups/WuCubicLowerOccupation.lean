/- GID: D5/S3/Quantum/Semigroups/WuCubicLowerOccupation
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicLowerOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational entropy sharpening and Schur matrix for the lower near-Gibbs Wu cubic tests. -/

import D5.S3.Quantum.Semigroups.WuCubicLowerCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicLowerOccupation

open WuRepeatedMiddleCubic (alpha)
open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate
open WuCubicHellingerMatrix
  (Vec3 Mat3 basis coordinates displacement levels quadratic occupationMatrix lowerTilt upperTilt
    occupationTaylorCoefficient_eq_quadratic)
open WuCubicOccupationTaylor
open WuCubicSignedTransfer (sourceDeficitAt)
open WuCubicEntropyRemainders (mass_normalized_cubic_entropy_le)
open WuCubicRefinedHellinger (signedTiltRow refined_hellinger_deficit_bound)
open WuCubicLowerCoefficients
open private gamma from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private log_lower from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private occupationGibbsProb_fun_eq cubicMass_pos gibbsLevels_pos
  from D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
open private occupation_entropy_nonneg from D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
open private edgeWeights edgeRows entropyWeights massChange gibbsMass massRow edge_energy_eq
  from D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix
open private matchedLower matchedUpper from D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix
open private schur_loss_le from D5.S3.Quantum.Semigroups.WuCubicRefinedHellinger

/-- Twice the upper bound for the physical coefficient of the entropy. -/
def entropyScale (r : ℝ) : ℝ := 1 - (r - 1) ^ 2 / (4 * (r ^ 2 + r + 1))

theorem two_alpha_le_entropyScale {r : ℝ} (hr : 1 < r) :
    2 * alpha r ≤ entropyScale r := by
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hD : 0 < 4 * (r ^ 2 + r + 1) := by positivity
  have hsum : 0 < r + 1 := by positivity
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hscale : entropyScale r = 3 * (r + 1) ^ 2 / (4 * (r ^ 2 + r + 1)) := by
    unfold entropyScale
    apply (eq_div_iff hD.ne').mpr
    have h := div_mul_cancel₀ ((r - 1) ^ 2) hD.ne'
    rw [sub_mul, one_mul, h]
    ring
  have hlog' := mul_le_mul_of_nonneg_left (log_lower hr.le)
    (show 0 ≤ 3 * (r + 1) ^ 2 by positivity)
  have hleft : 3 * (r + 1) ^ 2 * (2 * (r - 1) / (r + 1)) =
      2 * (3 * (r ^ 2 - 1)) := by
    field_simp [hsum.ne'] <;> ring
  rw [hleft] at hlog'
  rw [hscale, alpha, if_neg hr.ne', ← mul_div_assoc]
  apply (div_le_iff₀ (show 0 < 4 * (r ^ 2 + r + 1) * Real.log r from mul_pos hD hlog)).mpr
  have hright : 3 * (r + 1) ^ 2 / (4 * (r ^ 2 + r + 1)) *
      (4 * (r ^ 2 + r + 1) * Real.log r) = 3 * (r + 1) ^ 2 * Real.log r := by
    calc
      _ = (3 * (r + 1) ^ 2 / (4 * (r ^ 2 + r + 1)) *
            (4 * (r ^ 2 + r + 1))) * Real.log r := (mul_assoc _ _ _).symm
      _ = _ := by rw [div_mul_cancel₀ _ hD.ne']
  exact hlog'.trans_eq hright.symm

def scaledOccupation (r : ℝ) (y : Vec3) : Mat3 :=
  fun i j =>
    gamma r * (∑ k, edgeWeights r y k * edgeRows r k i * edgeRows r k j) +
      entropyScale r *
        (-(9 / 4) * (∑ k, entropyWeights r y k * basis k i * basis k j) +
          ((1 - massChange r y / (3 * gibbsMass r)) / (4 * gibbsMass r)) *
            massRow r y i * massRow r y j)

theorem scaledOccupation_isSymm (r : ℝ) (y : Vec3) : (scaledOccupation r y).IsSymm := by
  change (scaledOccupation r y)ᵀ = scaledOccupation r y
  apply Matrix.ext
  intro i j
  simp only [Matrix.transpose_apply, scaledOccupation]
  have hedge : (∑ k, edgeWeights r y k * edgeRows r k j * edgeRows r k i) =
      ∑ k, edgeWeights r y k * edgeRows r k i * edgeRows r k j := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hentropy : (∑ k, entropyWeights r y k * basis k j * basis k i) =
      ∑ k, entropyWeights r y k * basis k i * basis k j := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hedge, hentropy]
  ring

/-- The matrix checked by the lower verifier before restoring the physical units. -/
def lowerMatrix (r : ℝ) (y : Vec3) :
    Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ :=
  let w := signedTiltRow r y (asymmetry r y) (residual r y) (linearPivot r y)
  fromBlocks (fun i j => scaledOccupation r y i j - (∑ l, basis l i * basis l j) / 1024)
    (fun i _ => w i / 2) (fun _ j => w j / 2) (fun _ _ => weight r y)

theorem lowerMatrix_isSymm (r : ℝ) (y : Vec3) : (lowerMatrix r y).IsSymm := by
  change (lowerMatrix r y)ᵀ = lowerMatrix r y
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.transpose_apply, lowerMatrix, fromBlocks, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr]
  rw [(scaledOccupation_isSymm r y).apply i j]
  congr 1
  apply congrArg (fun v : ℝ => v / 1024)
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem occupation_sharp {r : ℝ} (hr : 1 < r) (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + h i) (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let y := displacement 1 h
    quadratic (scaledOccupation r y) (coordinates h) ≤
      occupationDeficit r (levels r y 0) (levels r y 1) (levels r y 2) := by
  intro y
  let g := gibbsLevels r
  let x := fun i => g i + 1 * h i
  let Tg := cubicMass g
  let μ := massDisplacement g h 1
  let E := occupationEnergyFactor r 1 h
  have hx' : ∀ i, 1 / 2 ≤ x i := by simpa only [x, g, one_mul] using hx
  have hxpos (i : Fin 4) : 0 < x i := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hx' i)
  have hT : 0 < Tg := cubicMass_pos (gibbsLevels_pos hr.le)
  have hmass : cubicMass x - Tg = μ := by
    simpa only [one_mul, x, Tg, μ] using cubic_mass_sub_eq g h 1
  have hent :
      occupationEntropy r x ≤
        (∑ i, ((9 / 2) * g i * (x i - g i) ^ 2 + (9 / 2) * (x i - g i) ^ 3 +
          (3 / 2) * (x i - g i) ^ 4)) - (cubicMass x - Tg) ^ 2 / (2 * Tg) +
            (cubicMass x - Tg) ^ 3 / (6 * Tg ^ 2) := by
    rw [occupationEntropy, occupationGibbsProb_fun_eq hr.le]
    exact mass_normalized_cubic_entropy_le x g hx' hg
  have hhalf : occupationEntropy r x / 2 ≤ E - occupationTaylorCoefficient r 1 h := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply hent.trans_eq
    rw [hmass]
    simp only [x, one_mul, add_sub_cancel_left, occupationTaylorCoefficient, E, μ, Tg, g,
      Fin.sum_univ_four]
    ring
  have hscale : 0 ≤ entropyScale r :=
    (mul_nonneg (by norm_num) (alpha_bounds_of_one_le hr.le).1).trans (two_alpha_le_entropyScale hr)
  have hweighted : alpha r * occupationEntropy r x ≤
      entropyScale r * (E - occupationTaylorCoefficient r 1 h) := calc
    _ ≤ (entropyScale r / 2) * occupationEntropy r x :=
      mul_le_mul_of_nonneg_right (by linarith only [two_alpha_le_entropyScale hr])
        (occupation_entropy_nonneg hr.le x hxpos)
    _ = entropyScale r * (occupationEntropy r x / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hhalf hscale
  have henergy : quadratic
      (fun i j => gamma r * (∑ k, edgeWeights r y k * edgeRows r k i * edgeRows r k j))
      (coordinates h) = E := by
    change _ = occupationEnergyFactor r 1 h
    rw [← edge_energy_eq (zero_lt_one.trans hr) 1 h hh]
    simp only [quadratic, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_four, y]
    ring
  have hmatrix : quadratic (scaledOccupation r y) (coordinates h) =
      E - entropyScale r * (E - occupationTaylorCoefficient r 1 h) := by
    rw [occupationTaylorCoefficient_eq_quadratic (zero_lt_one.trans hr) 1 h hh, ← henergy]
    simp only [scaledOccupation, occupationMatrix, quadratic, dotProduct, Matrix.mulVec,
      Fin.sum_univ_three, y]
    ring
  have hsource := occupation_source_deficit_eq hr.le h hh (d := 1) hxpos
  change sourceDeficitAt r occupationFrame (levels r y 0) (levels r y 1) (levels r y 2) =
    (1 : ℝ) ^ 2 * E - alpha r * occupationEntropy r x at hsource
  have hm : 0 ≤ levels r y 0 := (hxpos 0).le
  have hn : 0 ≤ levels r y 1 := (hxpos 1).le
  have hq : 0 ≤ levels r y 2 := (hxpos 2).le
  have hid : normalizedDeficit r 1 (levels r y 0) (levels r y 1) (levels r y 2) =
    sourceDeficitAt r occupationFrame (levels r y 0) (levels r y 1) (levels r y 2) := rfl
  rw [← occupation_deficit_eq hr.le hm hn hq, hid, hmatrix, hsource, one_pow, one_mul]
  exact sub_le_sub_left hweighted _

/-- The tested lower block is the physical Schur matrix with the sharper
entropy contribution in its occupation block. -/
theorem lowerMatrix_eq_schur {r : ℝ} (hr : 1 < r) (y : Vec3) :
    lowerMatrix r y =
      WuCubicRefinedHellinger.schurMatrix r y (physicalWeight r y) (physicalAsymmetry r y)
        (physicalResidual r y) (physicalPivot r y) +
      fromBlocks (fun i j => scaledOccupation r y i j - occupationMatrix r y i j)
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
  have hp : physicalWeight r y / (r - 1) ^ 2 = weight r y := by
    rw [(physical_factors hr y).1, mul_comm ((r - 1) ^ 2) (weight r y),
      mul_div_cancel_right₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hr.ne'))]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [lowerMatrix, WuCubicRefinedHellinger.schurMatrix, Matrix.add_apply,
      fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, hp, signed_row_eq hr y, add_zero]
  ring

private theorem lower_quadratic (r : ℝ) (h : Fin 4 → ℝ) (hh : h 3 = 0) (s : ℝ)
    (hPSD : (lowerMatrix r (displacement 1 h)).PosSemidef) :
    let y := displacement 1 h
    let w := signedTiltRow r y (asymmetry r y) (residual r y) (linearPivot r y)
    0 ≤ quadratic (scaledOccupation r y) (coordinates h) - (∑ i, h i ^ 2) / 1024 +
      dotProduct w (coordinates h) * s + weight r y * s ^ 2 := by
  intro y w
  let ξ := coordinates h
  have hquad := hPSD.dotProduct_mulVec_nonneg (Sum.elim ξ (fun _ => s))
  have hgram : quadratic (fun i j => ∑ l, basis l i * basis l j) ξ = ∑ i, h i ^ 2 := by
    norm_num [quadratic, ξ, basis, coordinates, dotProduct, Matrix.mulVec,
      Fin.sum_univ_three, Fin.sum_univ_four, hh, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  change 0 ≤ quadratic (scaledOccupation r y) ξ - (∑ i, h i ^ 2) / 1024 +
    dotProduct w ξ * s + weight r y * s ^ 2
  rw [← hgram]
  change 0 ≤ star (Sum.elim ξ (fun _ : Fin 1 => s)) ⬝ᵥ
    (lowerMatrix r y *ᵥ Sum.elim ξ (fun _ : Fin 1 => s)) at hquad
  simp only [star_trivial, lowerMatrix, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, Fin.sum_univ_three] at hquad
  simp only [fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr] at hquad
  simp only [quadratic, dotProduct, Matrix.mulVec, Fin.sum_univ_three, w]
  linarith only [hquad]

open WuCubicGibbsScaledCoefficients (g0scaled g2scaled gibbs_endpoint_linear_costs_eq)
open private tilt_scaling from D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix
open private spectral_coefficients_nonneg from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

set_option maxHeartbeats 1000000 in
theorem normalized_deficit_ge_of_lower_matrix {r : ℝ} (U : unitary Mat) (hr : 1 < r)
    (h : Fin 4 → ℝ) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + h i) (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i) :
    let y := displacement 1 h
    let m := levels r y 0
    let n := levels r y 1
    let q := levels r y 2
    m ≤ n → n ≤ q → q ≤ 1 →
    (∀ i, 0 < tests r y i) → (lowerMatrix r y).PosSemidef →
    (∑ i, h i ^ 2) / 1024 ≤ normalizedDeficit r U m n q := by
  intro y m n q hmn hnq hq1 htests hPSD
  let t := r - 1
  let p := physicalWeight r y
  let k := physicalAsymmetry r y
  let R := physicalResidual r y
  let β := physicalPivot r y
  let η := R ^ 2 / (4 * β)
  let G₀ := cutBias r m n q 0 / 2 - 2 * matchedLower r m n q
  let G₂ := cutBias r m n q 2 / 2 - 2 * matchedUpper r m n q
  let Gs := G₀ + G₂
  let ξ := coordinates h
  let w := signedTiltRow r y k R β
  have ht : 0 < t := sub_pos.mpr hr
  have hm : 0 ≤ m := by
    change 0 ≤ gibbsLevels r 0 + 1 * h 0
    rw [one_mul]
    exact (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hx 0)
  obtain ⟨hL₀, hleft, hright, hend₀, hend₂, hP₀, hP₂, hlong, hstrong, hβ, hdisc⟩ :=
    physical_tests hr y hnq htests
  obtain ⟨_, hB, _⟩ := spectral_coefficients_nonneg hr.le hm hmn hnq hq1
  have hp : 0 < p :=
    add_pos_of_pos_of_nonneg (add_pos hP₀ hP₂) (div_nonneg (hB 1) (by norm_num))
  have hphysical := refined_hellinger_deficit_bound U hr.le hm hmn hnq hq1
    hL₀ hleft hright hend₀ hend₂ hP₀ hP₂ hlong hstrong hβ hdisc
  change occupationDeficit r m n q - (max 0 (2 * η - Gs)) ^ 2 / (4 * p) ≤ _ at hphysical
  have hocc := occupation_sharp hr h hh hx hg
  change quadratic (scaledOccupation r y) ξ ≤ occupationDeficit r m n q at hocc
  obtain ⟨hscale₀, hscale₂⟩ := tilt_scaling hr (d := 1) (by norm_num) h hh
  obtain ⟨htilt₀, htilt₂⟩ := gibbs_endpoint_linear_costs_eq (zero_lt_one.trans hr) 1 h hh
  change G₀ = 1 * g0scaled r 1 h at htilt₀
  change G₂ = 1 * g2scaled r 1 h at htilt₂
  have hw₀ : G₀ = t * dotProduct (lowerTilt r y) ξ := by rw [htilt₀, one_mul, hscale₀]
  have hw₂ : G₂ = t * dotProduct (upperTilt r y) ξ := by rw [htilt₂, one_mul, hscale₂]
  have hrow : dotProduct w ξ = dotProduct (lowerTilt r y) ξ + dotProduct (upperTilt r y) ξ -
      R / (2 * β) * ((1 - k) * dotProduct (lowerTilt r y) ξ -
        (1 + k) * dotProduct (upperTilt r y) ξ) := by
    simp only [w, signedTiltRow, dotProduct, Fin.sum_univ_three]
    ring
  have hres : (1 - k) * G₀ - (1 + k) * G₂ = R := by
    change (1 - k) * G₀ - (1 + k) * G₂ = G₀ - G₂ - k * (G₀ + G₂)
    ring
  have hw : t * dotProduct w ξ = Gs - 2 * η := calc
    _ = (t * dotProduct (lowerTilt r y) ξ + t * dotProduct (upperTilt r y) ξ) -
        R / (2 * β) * ((1 - k) * (t * dotProduct (lowerTilt r y) ξ) -
          (1 + k) * (t * dotProduct (upperTilt r y) ξ)) := by rw [hrow]; ring
    _ = _ := by
      rw [← hw₀, ← hw₂, hres]
      change Gs - R / (2 * β) * R = Gs - 2 * η
      dsimp only [η]
      field_simp [(show 0 < β from hβ).ne']
      ring
  let v := Gs - 2 * η
  have hschur : v ^ 2 / (4 * p) ≤
      quadratic (scaledOccupation r y) ξ - (∑ i, h i ^ 2) / 1024 := by
    apply schur_loss_le ht hp hw
    intro s
    have hq := lower_quadratic r h hh s hPSD
    change 0 ≤ quadratic (scaledOccupation r y) ξ - (∑ i, h i ^ 2) / 1024 +
      dotProduct (signedTiltRow r y (asymmetry r y) (residual r y) (linearPivot r y)) ξ * s +
      weight r y * s ^ 2 at hq
    have he : p / t ^ 2 = weight r y := by
      change physicalWeight r y / (r - 1) ^ 2 = _
      rw [(physical_factors hr y).1, mul_comm ((r - 1) ^ 2) (weight r y),
        mul_div_cancel_right₀ _ (pow_ne_zero _ ht.ne')]
    rw [he]
    simpa only [w, k, R, β, signed_row_eq hr y] using hq
  have hv : 2 * η - Gs = -v := by dsimp only [v]; ring
  have hmax : max 0 (2 * η - Gs) ≤ |v| :=
    max_le (abs_nonneg _) (hv.le.trans (neg_le_abs v))
  have hsq := (sq_le_sq₀ (le_max_left 0 (2 * η - Gs)) (abs_nonneg v)).mpr hmax
  rw [sq_abs] at hsq
  have hloss := div_le_div_of_nonneg_right hsq (show 0 ≤ 4 * p by positivity)
  calc
    _ ≤ quadratic (scaledOccupation r y) ξ - v ^ 2 / (4 * p) := le_sub_comm.mp hschur
    _ ≤ occupationDeficit r m n q - (max 0 (2 * η - Gs)) ^ 2 / (4 * p) :=
      sub_le_sub hocc hloss
    _ ≤ _ := hphysical

end D5.S3.Quantum.Semigroups.WuCubicLowerOccupation
