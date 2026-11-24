/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Computational and Fourier scores in dimension five sum to less than 377/100. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveBasis
import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFiveCrossBound

/-! The five-dimensional computational/Fourier harmonic-overlap threshold. -/

open scoped BigOperators ComplexConjugate InnerProductSpace
open InnerProductSpace QuantumPhaseEstimationGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

def fiveA : ℝ := 1 - Real.sqrt ((5 + Real.sqrt 5) / 10)
def fiveE : ℝ := 1 - Real.sqrt ((7 + Real.sqrt 5) / 10)

private theorem five_gap_constants :
    (1493 / 10000 : ℝ) < fiveA ∧ (389 / 10000 : ℝ) < fiveE ∧ fiveE < 1 / 20 := by
  have hs : Real.sqrt (5 : ℝ) < 22361 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hs' : (21 / 10 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  unfold fiveA fiveE
  have ha : Real.sqrt ((5 + Real.sqrt 5) / 10) < 8507 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith only [hs]
  have he : Real.sqrt ((7 + Real.sqrt 5) / 10) < 9611 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith only [hs]
  have he' : (19 / 20 : ℝ) < Real.sqrt ((7 + Real.sqrt 5) / 10) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith only [hs']
  exact ⟨by linarith only [ha], by linarith only [he], by linarith only [he']⟩

theorem five_gap_order : 0 < fiveA ∧ 0 < fiveE ∧ 2 * fiveE < fiveA := by
  obtain ⟨hA, hE, hE'⟩ := five_gap_constants
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The radical estimate lies below the prescribed entropy threshold. -/
theorem five_radical_lt_377_div_100 :
    4 - 8 * fiveE + 8 * fiveE ^ 2 / fiveA < 377 / 100 := by
  obtain ⟨hA, hE, hEmax⟩ := five_gap_constants
  let a : ℝ := 1493 / 10000
  let e : ℝ := 389 / 10000
  have ha : 0 < a := by norm_num [a]
  have hE0 : e ≤ fiveE := hE.le
  have hA0 : a ≤ fiveA := hA.le
  have hdiv : fiveE ^ 2 / fiveA ≤ fiveE ^ 2 / a :=
    div_le_div_of_nonneg_left (sq_nonneg _) ha hA0
  have hs : 0 ≤ (fiveE - e) * (a - (fiveE + e)) :=
    mul_nonneg (sub_nonneg.mpr hE0) (by dsimp [a, e]; linarith only [hEmax])
  have hmono : (fiveE ^ 2 - e ^ 2) / a ≤ fiveE - e := by
    apply (div_le_iff₀ ha).2
    nlinarith only [hs]
  rw [sub_div] at hmono
  have hcert : (53682 / 933125 : ℝ) = 2 * e - 2 * (e ^ 2 / a) := by
    norm_num [a, e]
  rw [mul_div_assoc]
  linarith only [hcert, hdiv, hmono]

private theorem norm_sq_basis_sum (b : OrthonormalBasis Idx ℂ CoordinateFive)
    (I : Finset Idx) (a : Idx → ℂ) :
    ‖∑ i ∈ I, a i • b i‖ ^ 2 = coeffEnergy I a := by
  let v : EuclideanSpace ℂ Idx := WithLp.toLp 2 fun i => if i ∈ I then a i else 0
  have hrepr : b.repr.symm v = ∑ i ∈ I, a i • b i := by
    rw [← b.sum_repr_symm v]
    change (∑ i, (if i ∈ I then a i else 0) • b i) = _
    calc
      _ = ∑ i ∈ I, (if i ∈ I then a i else 0) • b i := by
        symm
        exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hi])
      _ = _ := Finset.sum_congr rfl (fun i hi => by simp [hi])
  rw [← hrepr, b.repr.symm.norm_map, EuclideanSpace.norm_sq_eq]
  unfold coeffEnergy
  change (∑ i, ‖(if i ∈ I then a i else 0)‖ ^ 2) = _
  calc
    _ = ∑ i ∈ I, ‖(if i ∈ I then a i else 0)‖ ^ 2 := by
      symm
      exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hi])
    _ = _ := Finset.sum_congr rfl (fun i hi => by simp [hi])

private theorem inner_basis_sums (I J : Finset Idx) (a b : Idx → ℂ) :
    ⟪(∑ i ∈ I, a i • coordinateBasisFive i), ∑ j ∈ J, b j • fourierBasisFive j⟫_ℂ =
      crossForm I J (fun i => conj (a i)) b := by
  unfold crossForm
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, five_cross_entry,
    Finset.sum_mul, fiveEntry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem synthesis_sq_bounds (s : Finset (Idx ⊕ Idx)) (w : EuclideanSpace ℂ s)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hs : s.card ≤ n) :
    (1 - Real.sqrt (crossCap n)) * ‖w‖ ^ 2 ≤
        ‖maskSynthesis coordinateBasisFive fourierBasisFive s w‖ ^ 2 ∧
    ‖maskSynthesis coordinateBasisFive fourierBasisFive s w‖ ^ 2 ≤
        (1 + Real.sqrt (crossCap n)) * ‖w‖ ^ 2 := by
  let e (i : Idx ⊕ Idx) : ℂ := if h : i ∈ s then w ⟨i, h⟩ else 0
  let a (i : Idx) : ℂ := e (Sum.inl i)
  let b (j : Idx) : ℂ := e (Sum.inr j)
  let U := ∑ i ∈ s.toLeft, a i • coordinateBasisFive i
  let V := ∑ j ∈ s.toRight, b j • fourierBasisFive j
  have hvec : maskSynthesis coordinateBasisFive fourierBasisFive s w = U + V := by
    let v : Idx ⊕ Idx → CoordinateFive := Sum.elim coordinateBasisFive fourierBasisFive
    calc
      _ = ∑ i : s, e i.val • v i.val := by
        change (∑ i : s, w i • v i.val) = _
        apply Finset.sum_congr rfl
        intro i _
        simp [e, i.property]
      _ = ∑ i ∈ s, e i • v i := Finset.sum_coe_sort s (fun i => e i • v i)
      _ = U + V := Finset.sum_sum_eq_sum_toLeft_add_sum_toRight s _
  have hcoeff : ‖w‖ ^ 2 = coeffEnergy s.toLeft a + coeffEnergy s.toRight b := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ i : s, ‖e i.val‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [e, i.property]
      _ = ∑ i ∈ s, ‖e i‖ ^ 2 := Finset.sum_coe_sort s (fun i => ‖e i‖ ^ 2)
      _ = _ := Finset.sum_sum_eq_sum_toLeft_add_sum_toRight s _
  have hcard := s.card_toLeft_add_card_toRight
  have hcross := crossForm_sq_le s.toLeft s.toRight (fun i => conj (a i)) b hn
    (hcard.trans_le hs)
  rw [← inner_basis_sums] at hcross
  have hconj : coeffEnergy s.toLeft (fun i => conj (a i)) = coeffEnergy s.toLeft a := by
    simp [coeffEnergy]
  rw [hconj] at hcross
  have hU : ‖U‖ ^ 2 = coeffEnergy s.toLeft a := norm_sq_basis_sum _ _ _
  have hV : ‖V‖ ^ 2 = coeffEnergy s.toRight b := norm_sq_basis_sum _ _ _
  have hcap : 0 ≤ crossCap n := by
    rcases hn with rfl | rfl <;> unfold crossCap <;>
      linarith only [Real.goldenRatio_pos]
  have hnorm : 2 * ‖⟪U, V⟫_ℂ‖ ≤ Real.sqrt (crossCap n) * ‖w‖ ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    simp only [mul_pow, Real.sq_sqrt hcap, hcoeff]
    have h := mul_nonneg hcap
      (sq_nonneg (coeffEnergy s.toLeft a - coeffEnergy s.toRight b))
    change ‖⟪U, V⟫_ℂ‖ ^ 2 ≤ _ at hcross
    nlinarith only [h, hcross]
  have hreal := abs_le.mp (Complex.abs_re_le_norm ⟪U, V⟫_ℂ)
  rw [hvec, norm_add_sq (𝕜 := ℂ), hU, hV]
  change (1 - _) * ‖w‖ ^ 2 ≤ _ + 2 * (⟪U, V⟫_ℂ).re + _ ∧
    _ + 2 * (⟪U, V⟫_ℂ).re + _ ≤ (1 + _) * ‖w‖ ^ 2
  constructor <;> linarith only [hcoeff, hnorm, hreal.1, hreal.2]

private theorem crossCap_four : crossCap 4 = (5 + Real.sqrt 5) / 10 := by
  unfold crossCap Real.goldenRatio
  push_cast
  ring

private theorem crossCap_five : crossCap 5 = (7 + Real.sqrt 5) / 10 := by
  unfold crossCap Real.goldenRatio
  push_cast
  ring

/-- Every coordinate/Fourier Born law in dimension five supplies the same two mask gaps. -/
theorem five_spectralMaskGaps (z : CoordinateFive) (hz : ‖z‖ = 1) :
    SpectralMaskGaps (basisLaw coordinateBasisFive fourierBasisFive z) 5 fiveA fiveE := by
  have hpos := five_gap_order.2.1
  change SpectralMaskGaps (basisLaw coordinateBasisFive fourierBasisFive z)
    (Fintype.card Idx) fiveA fiveE
  apply spectralMaskGaps_of_synthesis _ _ _ hpos _ _ z hz
  · unfold fiveA
    have h := Real.sqrt_nonneg ((5 + Real.sqrt 5) / 10)
    linarith only [h]
  · intro s hs w
    have h := (synthesis_sq_bounds s w (n := 4) (Or.inl rfl)
      (by simp only [Fintype.card_fin] at hs; omega)).2
    rw [crossCap_four] at h
    have ha : 2 - fiveA = 1 + Real.sqrt ((5 + Real.sqrt 5) / 10) := by unfold fiveA; ring
    rwa [ha]
  · intro s hs w
    have h := (synthesis_sq_bounds s w (n := 5) (Or.inr rfl)
      (by simpa using le_of_eq hs)).1
    rwa [crossCap_five] at h

/-- The exact radical bound for the two basis scores in dimension five. -/
private theorem fiveScore_le_radical (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    fiveScore x y ≤ 4 - 8 * fiveE + 8 * fiveE ^ 2 / fiveA := by
  obtain ⟨hA, hE, hAE⟩ := five_gap_order
  unfold fiveScore
  apply score_upper_bound_of_mask_gaps (n := 5) _ _ (by decide)
  · intro i
    cases i <;> exact sq_nonneg _
  · intro i
    cases i <;> exact sq_nonneg _
  · rw [basisLaw_sum, hx]; norm_num
  · rw [basisLaw_sum, hy]; norm_num
  · exact hA
  · exact hE.le
  · exact hAE.le
  · exact five_spectralMaskGaps x hx
  · exact five_spectralMaskGaps y hy

/-- The score with the positive Fourier matrix acting on the input vectors. -/
def positiveFourierScore (x y : CoordinateFive) : ℝ :=
  score (fun i => ‖x i‖ ^ 2) (fun i => ‖y i‖ ^ 2) +
    score (fun i => ‖QFT 5 (WithLp.ofLp x) i‖ ^ 2)
      (fun i => ‖QFT 5 (WithLp.ofLp y) i‖ ^ 2)

private def conjugateVector (x : CoordinateFive) : CoordinateFive :=
  WithLp.toLp 2 (fun i => conj (x i))

private theorem norm_conjugateVector (x : CoordinateFive) : ‖conjugateVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector, Complex.norm_conj]

private theorem inverseQFT_conjugateVector (x : CoordinateFive) (i : Idx) :
    inverseQFT 5 (WithLp.ofLp (conjugateVector x)) i = conj (QFT 5 (WithLp.ofLp x) i) := by
  simp [conjugateVector, inverseQFT, QFT, scale]

private theorem positiveFourierScore_eq (x y : CoordinateFive) :
    positiveFourierScore x y = fiveScore (conjugateVector x) (conjugateVector y) := by
  rw [fiveScore_eq_sum]
  simp only [positiveFourierScore, inverseQFT_conjugateVector, Complex.norm_conj]
  simp only [conjugateVector, PiLp.toLp_apply, Complex.norm_conj]

/-- The exact radical upper bound in the positive-QFT convention of the analytic proof. -/
theorem positiveFourierScore_le_radical (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    positiveFourierScore x y ≤ 4 - 8 * fiveE + 8 * fiveE ^ 2 / fiveA := by
  rw [positiveFourierScore_eq]
  exact fiveScore_le_radical _ _ (by simpa only [norm_conjugateVector] using hx)
    (by simpa only [norm_conjugateVector] using hy)

/-- Qian §11(3)'s threshold for arbitrary unit vectors and the positive Fourier matrix. -/
theorem positiveFourierScore_lt_377_div_100 (x y : CoordinateFive)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : positiveFourierScore x y < 377 / 100 :=
  (positiveFourierScore_le_radical x y hx hy).trans_lt five_radical_lt_377_div_100

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
