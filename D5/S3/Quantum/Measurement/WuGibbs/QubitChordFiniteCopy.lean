/- GID: D5/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/WuGibbs/QubitChordFiniteCopy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Projective readout and pure-endpoint preparation give Bernoulli product bounds on finite-copy qubit trace distance along a closed Bloch chord. -/

import D5.S3.Quantum.Information.ActualQubitChordObstruction
import D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Measurement.Auric.DiamondBounds
import D5.S3.TotalVariation.Pinsker

/-!
# Finite-copy trace distance on a physical Bloch chord

The projective readout along the chord direction and the preparation from its
two pure endpoints give Bernoulli product laws on opposite sides of the same
quantum trace distance.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace CStarAlgebra

namespace Wu.QubitChordFiniteCopy

set_option autoImplicit false

open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix blochMatrix_trace)
open D5.S3.Quantum.Information.ActualQubitChordObstruction (det_bloch)
open D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability (copyState)
open D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation (IsPOVM)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceDistance traceNorm)
open D5.S3.Quantum.Measurement.Auric.DiamondBounds
  (twice_effect_trace_le_traceNorm traceNorm_le_twice_trace_of_majorant)
open D5.S3.TotalVariation.Pinsker (totalVariation total_variation_eq_sum_positive)

abbrev BlochVector := EuclideanSpace ℝ (Fin 3)
abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The two weights are ordered by the sign, positive first. -/
def bernoulliMass (a : ℝ) : Fin 2 → ℝ :=
  ![(1 + a) / 2, (1 - a) / 2]

def bernoulliCopies (n : ℕ) (a : ℝ) (x : Fin n → Fin 2) : ℝ :=
  ∏ k, bernoulliMass a (x k)

private theorem bernoulliMass_nonneg {a : ℝ} (ha : |a| ≤ 1) (i : Fin 2) :
    0 ≤ bernoulliMass a i := by
  rcases abs_le.mp ha with ⟨hl, hu⟩
  fin_cases i <;> simp [bernoulliMass] <;> linarith

private theorem bernoulliMass_sum (a : ℝ) : ∑ i, bernoulliMass a i = 1 := by
  simp [Fin.sum_univ_two, bernoulliMass]
  ring

private theorem bernoulliCopies_sum (n : ℕ) (a : ℝ) :
    ∑ x, bernoulliCopies n a x = 1 := by
  rw [show (∑ x, bernoulliCopies n a x) = (∑ i, bernoulliMass a i) ^ n from
    (Fintype.sum_pow (bernoulliMass a) n).symm, bernoulliMass_sum, one_pow]

private theorem bloch_psd (r : BlochVector) (hr : ‖r‖ ≤ 1) :
    (blochMatrix 1 r).PosSemidef := by
  have hH : (blochMatrix 1 r).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blochMatrix, Matrix.conjTranspose_apply, sub_eq_add_neg]
  have hsum := congrArg Complex.re hH.trace_eq_sum_eigenvalues
  rw [blochMatrix_trace] at hsum
  simp only [Fin.sum_univ_two, Complex.add_re, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re] at hsum
  have hprod := congrArg Complex.re hH.det_eq_prod_eigenvalues
  rw [det_bloch] at hprod
  simp only [Fin.prod_univ_two, Complex.mul_re, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hprod
  have hnonneg : 0 ≤ hH.eigenvalues 0 * hH.eigenvalues 1 := by
    have hs := (sq_le_sq₀ (norm_nonneg r) zero_le_one).mpr hr
    nlinarith only [hprod, hs]
  apply hH.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  fin_cases i
  · change 0 ≤ hH.eigenvalues 0
    by_contra! hneg
    have hpos : 0 < hH.eigenvalues 1 := by linarith only [hsum, hneg]
    exact (not_lt_of_ge hnonneg) (mul_neg_of_neg_of_pos hneg hpos)
  · change 0 ≤ hH.eigenvalues 1
    by_contra! hneg
    have hpos : 0 < hH.eigenvalues 0 := by linarith only [hsum, hneg]
    exact (not_lt_of_ge hnonneg) (mul_neg_of_pos_of_neg hpos hneg)

private theorem bloch_pairing (r s : BlochVector) :
    (Matrix.trace (blochMatrix 1 r * blochMatrix 1 s)).re = (1 + ⟪r, s⟫_ℝ) / 2 := by
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, blochMatrix, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_three]
  ring

def chordState (m e : BlochVector) (a : ℝ) : QubitMatrix :=
  blochMatrix 1 (m + a • e)

def chordRadius (m : BlochVector) : ℝ :=
  Real.sqrt (1 - ‖m‖ ^ 2)

private theorem chord_norm_sq (m e : BlochVector) (he : ‖e‖ = 1)
    (hme : ⟪m, e⟫_ℝ = 0) (a : ℝ) :
    ‖m + a • e‖ ^ 2 = ‖m‖ ^ 2 + a ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, hme, norm_smul, Real.norm_eq_abs,
    he, mul_one, sq_abs]
  ring

/-- These are the positive and negative spectral projections of the Pauli
observable along a unit Bloch direction. -/
def chordProjector (e : BlochVector) : Fin 2 → QubitMatrix :=
  ![blochMatrix 1 e, blochMatrix 1 (-e)]

theorem chordProjector_isProjective (e : BlochVector) (he : ‖e‖ = 1) :
    IsPOVM (chordProjector e) ∧
    ∀ i, chordProjector e i * chordProjector e i = chordProjector e i := by
  have hneg : ‖-e‖ = 1 := by simpa using he
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · exact bloch_psd e he.le
    · exact bloch_psd (-e) hneg.le
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chordProjector, Fin.sum_univ_two, Matrix.add_apply, blochMatrix] <;> ring
  · intro i
    fin_cases i
    · exact D5.S3.Quantum.Information.ActualQubitChordObstruction.pure e he
    · exact D5.S3.Quantum.Information.ActualQubitChordObstruction.pure (-e) hneg

private theorem chord_readout (m e : BlochVector) (he : ‖e‖ = 1)
    (hme : ⟪m, e⟫_ℝ = 0) (a : ℝ) (ha : ‖m + a • e‖ ≤ 1) (i : Fin 2) :
    Matrix.trace (chordProjector e i * chordState m e a) = (bernoulliMass a i : ℂ) := by
  have hinner : ⟪e, m + a • e⟫_ℝ = a := by
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm m e, hme, he]
    ring
  have hP := ((chordProjector_isProjective e he).1.1 i).isHermitian
  have hR : (chordState m e a).IsHermitian := (bloch_psd (m + a • e) ha).isHermitian
  apply Complex.ext
  · rw [Complex.ofReal_re]
    fin_cases i
    · change (Matrix.trace (blochMatrix 1 e * blochMatrix 1 (m + a • e))).re = (1 + a) / 2
      rw [bloch_pairing, hinner]
    · change (Matrix.trace (blochMatrix 1 (-e) * blochMatrix 1 (m + a • e))).re = (1 - a) / 2
      rw [bloch_pairing, inner_neg_left, hinner, sub_eq_add_neg]
  · rw [Complex.ofReal_im]
    apply Complex.conj_eq_iff_im.mp
    change star (Matrix.trace (chordProjector e i * chordState m e a)) = _
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hP.eq, hR.eq,
      Matrix.trace_mul_comm]

/-- The two pure Bloch endpoints used for preparation. -/
def chordEndpoint (m e : BlochVector) : Fin 2 → QubitMatrix :=
  ![chordState m e (chordRadius m), chordState m e (-chordRadius m)]

theorem chordEndpoint_isPure (m e : BlochVector) (he : ‖e‖ = 1)
    (hme : ⟪m, e⟫_ℝ = 0) (hm : ‖m‖ ^ 2 ≤ 1) (i : Fin 2) :
    (chordEndpoint m e i).PosSemidef ∧ (chordEndpoint m e i).trace = 1 ∧
    chordEndpoint m e i * chordEndpoint m e i = chordEndpoint m e i := by
  have h_radius_sq : chordRadius m ^ 2 = 1 - ‖m‖ ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hm)
  have hpure (a : ℝ) (ha : a ^ 2 = chordRadius m ^ 2) : ‖m + a • e‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [chord_norm_sq m e he hme, ha, h_radius_sq]
    ring
  have hp (a : ℝ) (ha : a ^ 2 = chordRadius m ^ 2) :
      (chordState m e a).PosSemidef ∧ (chordState m e a).trace = 1 ∧
      chordState m e a * chordState m e a = chordState m e a :=
    ⟨bloch_psd _ (hpure a ha).le, blochMatrix_trace 1 _,
      D5.S3.Quantum.Information.ActualQubitChordObstruction.pure _ (hpure a ha)⟩
  fin_cases i
  · exact hp _ rfl
  · exact hp _ (by ring)

private theorem chord_affine (m e : BlochVector) (t : ℝ) :
    (∑ i, (bernoulliMass t i : ℂ) • chordEndpoint m e i) =
      chordState m e (t * chordRadius m) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Matrix.add_apply, bernoulliMass,
      chordEndpoint, chordState, blochMatrix,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul] <;> ring

private theorem chord_preparation (m e : BlochVector) (he : ‖e‖ = 1)
    (hme : ⟪m, e⟫_ℝ = 0) (a : ℝ) (ha : ‖m + a • e‖ ≤ 1) :
    (∀ i, 0 ≤ bernoulliMass (a / chordRadius m) i) ∧
    (∑ i, (bernoulliMass (a / chordRadius m) i : ℂ) • chordEndpoint m e i) =
      chordState m e a := by
  have ha_sq := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr ha
  rw [chord_norm_sq m e he hme] at ha_sq
  have ha_abs : |a| ≤ chordRadius m := by
    unfold chordRadius
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    linarith only [ha_sq]
  rw [chord_affine]
  by_cases hzero : chordRadius m = 0
  · have hle : |a| ≤ 0 := by simpa only [hzero] using ha_abs
    have ha_zero : a = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg a))
    refine ⟨bernoulliMass_nonneg (by simp [ha_zero]), ?_⟩
    simp [ha_zero]
  · have hnonneg : 0 ≤ chordRadius m := Real.sqrt_nonneg _
    have hpos : 0 < chordRadius m := lt_of_le_of_ne hnonneg (fun heq => hzero heq.symm)
    have hmean : |a / chordRadius m| ≤ 1 := by
      rw [abs_div, abs_of_pos hpos]
      exact (div_le_iff₀ hpos).mpr (by simpa only [one_mul] using ha_abs)
    exact ⟨bernoulliMass_nonneg hmean, congrArg (chordState m e) (div_mul_cancel₀ a hzero)⟩

/-- Tensor product with a possibly different one-copy matrix at each site. -/
private def tensorFactors {n : ℕ} (A : Fin n → QubitMatrix) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => ∏ k, A k (x k) (y k)

private theorem tensorFactors_mul {n : ℕ} (A B : Fin n → QubitMatrix) :
    tensorFactors A * tensorFactors B = tensorFactors (fun k => A k * B k) := by
  ext x y
  simp only [Matrix.mul_apply, tensorFactors, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (k : Fin n) (j : Fin 2) =>
    A k (x k) j * B k j (y k))).symm

private theorem tensorFactors_adjoint {n : ℕ} (A : Fin n → QubitMatrix) :
    (tensorFactors A)ᴴ = tensorFactors (fun k => (A k)ᴴ) := by
  ext x y
  simp only [Matrix.conjTranspose_apply, tensorFactors, star_prod]

private theorem tensorFactors_psd {n : ℕ} (A : Fin n → QubitMatrix)
    (hA : ∀ k, (A k).PosSemidef) : (tensorFactors A).PosSemidef := by
  classical
  have hfactor (k : Fin n) : ∃ B : QubitMatrix, A k = Bᴴ * B := by
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hA k).nonneg
    exact ⟨B, hB⟩
  choose B hB using hfactor
  have h : A = fun k => (B k)ᴴ * B k := funext hB
  rw [h, ← tensorFactors_mul, ← tensorFactors_adjoint]
  exact Matrix.posSemidef_conjTranspose_mul_self _

private theorem trace_tensorFactors {n : ℕ} (A : Fin n → QubitMatrix) :
    (tensorFactors A).trace = ∏ k, (A k).trace := by
  exact (Fintype.prod_sum (fun (k : Fin n) (i : Fin 2) => A k i i)).symm

private theorem tensorFactors_one (n : ℕ) :
    tensorFactors (fun _ : Fin n => (1 : QubitMatrix)) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensorFactors]
  · have hk : ∃ k, x k ≠ y k := by
      by_contra! h
      exact hxy (funext h)
    obtain ⟨k, hk⟩ := hk
    have hzero : ∏ l : Fin n, (1 : QubitMatrix) (x l) (y l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
    simpa only [tensorFactors, Matrix.one_apply, ite_eq_right hxy] using hzero

private theorem tensor_preparation {A : Fin 2 → QubitMatrix} {a : ℝ} {ρ : QubitMatrix}
    (h : (∑ i, (bernoulliMass a i : ℂ) • A i) = ρ) (n : ℕ) :
    copyState n ρ = ∑ x : Fin n → Fin 2,
      (bernoulliCopies n a x : ℂ) • tensorFactors (fun k => A (x k)) := by
  ext x y
  simp only [copyState, bernoulliCopies, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    tensorFactors, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k (i : Fin 2) => (bernoulliMass a i : ℂ) * A i (x k) (y k))]
  apply Finset.prod_congr rfl
  intro k _
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    (congrArg (fun M : QubitMatrix => M (x k) (y k)) h).symm

private def productProjector (n : ℕ) (e : BlochVector) (x : Fin n → Fin 2) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  tensorFactors (fun k => chordProjector e (x k))

private theorem productProjector_isPOVM (n : ℕ) (e : BlochVector) (he : ‖e‖ = 1) :
    IsPOVM (productProjector n e) := by
  have hPOVM := (chordProjector_isProjective e he).1
  refine ⟨fun x => tensorFactors_psd _ (fun k => hPOVM.1 (x k)), ?_⟩
  rw [← tensorFactors_one n]
  ext x y
  simp only [Matrix.sum_apply, productProjector, tensorFactors]
  rw [← Fintype.prod_sum (fun k (i : Fin 2) => chordProjector e i (x k) (y k))]
  apply Finset.prod_congr rfl
  intro k _
  simpa only [Matrix.sum_apply] using
    congrArg (fun M : QubitMatrix => M (x k) (y k)) hPOVM.2

private theorem product_readout (n : ℕ) (m e : BlochVector) (he : ‖e‖ = 1)
    (hme : ⟪m, e⟫_ℝ = 0) (a : ℝ) (ha : ‖m + a • e‖ ≤ 1) (x : Fin n → Fin 2) :
    Matrix.trace (productProjector n e x * copyState n (chordState m e a)) =
      (bernoulliCopies n a x : ℂ) := by
  change Matrix.trace (tensorFactors (fun k => chordProjector e (x k)) *
    tensorFactors (fun _ => chordState m e a)) = _
  rw [tensorFactors_mul, trace_tensorFactors]
  simp only [chord_readout m e he hme a ha, bernoulliCopies, Complex.ofReal_prod]

private theorem measured_tv_le {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X]
    (ρ σ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hρtr : ρ.trace = 1) (hσtr : σ.trace = 1)
    (M : X → Matrix ι ι ℂ) (hM : IsPOVM M) (p q : X → ℝ)
    (hp : ∀ x, (M x * ρ).trace = (p x : ℂ)) (hq : ∀ x, (M x * σ).trace = (q x : ℂ))
    (hmass : (∑ x, p x) = ∑ x, q x) :
    totalVariation p q ≤ traceNorm (ρ - σ) / 2 := by
  classical
  let accepted : Finset X := Finset.univ.filter (fun x => q x ≤ p x)
  let E := ∑ x ∈ accepted, M x
  have hE : E.PosSemidef := Matrix.posSemidef_sum accepted (fun x _ => hM.1 x)
  have hsum : E + (∑ x ∈ acceptedᶜ, M x) = 1 := by
    rw [show E = ∑ x ∈ accepted, M x from rfl, Finset.sum_add_sum_compl, hM.2]
  have hEc : (1 - E).PosSemidef := by
    rw [← hsum, add_sub_cancel_left]
    exact Matrix.posSemidef_sum _ (fun x _ => hM.1 x)
  have htrace : (ρ - σ).trace = 0 := by rw [Matrix.trace_sub, hρtr, hσtr, sub_self]
  have hbound :=
    twice_effect_trace_le_traceNorm (ρ - σ) E (hρ.isHermitian.sub hσ.isHermitian) htrace hE hEc
  have hread : (E * (ρ - σ)).trace.re = totalVariation p q := by
    rw [total_variation_eq_sum_positive p q hmass]
    change ((∑ x ∈ accepted, M x) * (ρ - σ)).trace.re = ∑ x ∈ accepted, (p x - q x)
    simp only [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum, Matrix.mul_sub,
      Matrix.trace_sub, hp, hq, Complex.sub_re, Complex.ofReal_re]
  rw [hread] at hbound
  linarith only [hbound]

private theorem prepared_traceNorm_le {ι X : Type*} [Fintype ι] [Fintype X]
    (ρ σ : Matrix ι ι ℂ) (hρtr : ρ.trace = 1) (hσtr : σ.trace = 1)
    (A : X → Matrix ι ι ℂ) (hA : ∀ x, (A x).PosSemidef) (hAtr : ∀ x, (A x).trace = 1)
    (p q : X → ℝ) (hp : ρ = ∑ x, (p x : ℂ) • A x) (hq : σ = ∑ x, (q x : ℂ) • A x)
    (hmass : (∑ x, p x) = ∑ x, q x) :
    traceNorm (ρ - σ) / 2 ≤ totalVariation p q := by
  classical
  let H := ∑ x, ((max (p x - q x) 0 : ℝ) : ℂ) • A x
  have hD : ρ - σ = ∑ x, ((p x - q x : ℝ) : ℂ) • A x := by
    rw [hp, hq, ← Finset.sum_sub_distrib]
    simp only [Complex.ofReal_sub, sub_smul]
  have hH : H.PosSemidef :=
    Matrix.posSemidef_sum _ (fun x _ => (hA x).smul
      (Complex.zero_le_real.mpr (le_max_right (p x - q x) 0)))
  have hmajor : (H - (ρ - σ)).PosSemidef := by
    change ((∑ x, ((max (p x - q x) 0 : ℝ) : ℂ) • A x) - (ρ - σ)).PosSemidef
    rw [hD, ← Finset.sum_sub_distrib]
    apply Matrix.posSemidef_sum
    intro x _
    rw [← sub_smul, ← Complex.ofReal_sub]
    exact (hA x).smul
      (Complex.zero_le_real.mpr (sub_nonneg.mpr (le_max_left (p x - q x) 0)))
  have htrace : (ρ - σ).trace = 0 := by rw [Matrix.trace_sub, hρtr, hσtr, sub_self]
  have hbound := traceNorm_le_twice_trace_of_majorant (ρ - σ) H htrace hH hmajor
  have hmassH : H.trace.re = totalVariation p q := by
    rw [total_variation_eq_sum_positive p q hmass, Finset.sum_filter]
    simp only [H, Matrix.trace_sum, Matrix.trace_smul, hAtr, smul_eq_mul, mul_one,
      Complex.re_sum, Complex.ofReal_re]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : q x ≤ p x
    · rw [ite_eq_left hx, max_eq_left (sub_nonneg.mpr hx)]
    · rw [ite_eq_right hx, max_eq_right (sub_nonpos.mpr (le_of_not_ge hx))]
  rw [hmassH] at hbound
  linarith only [hbound]

private theorem copy_chord_psd (n : ℕ) (m e : BlochVector) (a : ℝ)
    (ha : ‖m + a • e‖ ≤ 1) : (copyState n (chordState m e a)).PosSemidef :=
  tensorFactors_psd (fun _ => chordState m e a) (fun _ => bloch_psd _ ha)

private theorem trace_copy_chord (n : ℕ) (m e : BlochVector) (a : ℝ) :
    (copyState n (chordState m e a)).trace = 1 := by
  change (tensorFactors (fun _ : Fin n => chordState m e a)).trace = 1
  rw [trace_tensorFactors]
  simp [chordState, blochMatrix_trace]

/-- The actual tensor power packaged as a trace-one PSD matrix. -/
def chordCopies (n : ℕ) (m e : BlochVector) (a : ℝ) (ha : ‖m + a • e‖ ≤ 1) :
    DensityState (Fin n → Fin 2) :=
  ⟨CStarMatrix.ofMatrix (copyState n (chordState m e a)),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (copy_chord_psd n m e a ha).nonneg,
    trace_copy_chord n m e a⟩

/-- Projective measurement along the chord attains the lower classical
comparison. Preparation from the pure chord endpoints gives the upper one.
The tangential case has zero radius and forces both longitudinal means to
zero. The empty tensor product is allowed. -/
theorem finite_copy_chord_comparison (n : ℕ) (m e : BlochVector) (he : ‖e‖ = 1)
    (hme : ⟪m, e⟫_ℝ = 0) (a b : ℝ)
    (ha : ‖m + a • e‖ ≤ 1) (hb : ‖m + b • e‖ ≤ 1) :
    totalVariation (bernoulliCopies n a) (bernoulliCopies n b) ≤
        traceDistance (chordCopies n m e a ha) (chordCopies n m e b hb) ∧
      traceDistance (chordCopies n m e a ha) (chordCopies n m e b hb) ≤
        totalVariation (bernoulliCopies n (a / chordRadius m))
          (bernoulliCopies n (b / chordRadius m)) := by
  let ρ := copyState n (chordState m e a)
  let σ := copyState n (chordState m e b)
  have htr (t : ℝ) : (copyState n (chordState m e t)).trace = 1 :=
    trace_copy_chord n m e t
  have hm : ‖m‖ ^ 2 ≤ 1 := by
    have hs := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr ha
    rw [chord_norm_sq m e he hme] at hs
    linarith only [hs, sq_nonneg a]
  change _ ≤ traceNorm (ρ - σ) / 2 ∧ traceNorm (ρ - σ) / 2 ≤ _
  constructor
  · exact measured_tv_le ρ σ (copy_chord_psd n m e a ha) (copy_chord_psd n m e b hb)
      (htr a) (htr b)
      (productProjector n e) (productProjector_isPOVM n e he)
      (bernoulliCopies n a) (bernoulliCopies n b)
      (product_readout n m e he hme a ha) (product_readout n m e he hme b hb)
      (by simp only [bernoulliCopies_sum])
  · let A : (Fin n → Fin 2) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
      fun x => tensorFactors (fun k => chordEndpoint m e (x k))
    have hA (x : Fin n → Fin 2) : (A x).PosSemidef :=
      tensorFactors_psd _ (fun k => (chordEndpoint_isPure m e he hme hm (x k)).1)
    have hAtr (x : Fin n → Fin 2) : (A x).trace = 1 := by
      change (tensorFactors (fun k => chordEndpoint m e (x k))).trace = 1
      rw [trace_tensorFactors]
      have htrace (i : Fin 2) : (chordEndpoint m e i).trace = 1 :=
        (chordEndpoint_isPure m e he hme hm i).2.1
      simp only [htrace, Finset.prod_const_one]
    exact prepared_traceNorm_le ρ σ (htr a) (htr b) A hA hAtr
      (bernoulliCopies n (a / chordRadius m)) (bernoulliCopies n (b / chordRadius m))
      (tensor_preparation (chord_preparation m e he hme a ha).2 n)
      (tensor_preparation (chord_preparation m e he hme b hb).2 n)
      (by simp only [bernoulliCopies_sum])

end Wu.QubitChordFiniteCopy
