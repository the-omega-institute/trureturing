/- GID: D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The F₃ steering inequality has the sharp ellipsoid-centre threshold two thirds. -/

import D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
import D5.S3.Arith.Lattices.Klartag.Walk.ChainEllipsoid

/-! The three-setting steering bound and its exact centre-length threshold. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli blochA blochB corr vlen centre vlen_eq_norm vlen_nonneg)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH
  (vlen_sq normalized_unit delta flipped
    flip_purity_identity bob_radius_le delta_le_centre tightState tight_psd tight_readouts
    tight_centre bell bell_trace_real_expansion unit_dot_le)
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
  (trace_flip)
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.GurvitsBarnumBall
  renaming flip → partySwap
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin)
open D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit

namespace D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold

/-- Bob's ellipsoid centre, including the pure-Alice marginal convention. -/
def centreB (ρ : TwoQubit) : Fin 3 → ℝ :=
  if vlen (blochA ρ) = 1 then blochB ρ
  else fun j => (blochB ρ j - ∑ i, corr ρ i j * blochA ρ i) / (1 - vlen (blochA ρ) ^ 2)

/-- Three unit Alice settings and an orthonormal Bob frame. -/
def fThreeValues (ρ : TwoQubit) : Set ℝ :=
  {r | ∃ α β : Fin 3 → Fin 3 → ℝ,
    (∀ i, vlen (α i) = 1) ∧
    (∀ i j, β i ⬝ᵥ β j = if i = j then 1 else 0) ∧
    r = ‖∑ i, trace (ρ * (spin (α i) ⊗ₖ spin (β i)))‖ / Real.sqrt 3}

/-- Maximal F₃ steering value. -/
def fThree (ρ : TwoQubit) : ℝ := sSup (fThreeValues ρ)

def claim : Prop :=
  (∀ ρ : TwoQubit, ρ.PosSemidef → trace ρ = 1 →
    fThree ρ ≤ max (Real.sqrt (3 * (1 - vlen (centreB ρ)))) 1) ∧
  (∀ t : ℝ, 0 ≤ t → t < 2 / 3 → ∃ ρ : TwoQubit,
    ρ.PosSemidef ∧ trace ρ = 1 ∧ vlen (centreB ρ) = t ∧ 1 < fThree ρ)

private lemma swap_trace_product (ρ : TwoQubit) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (partySwap ρ * (A ⊗ₖ B)) = trace (ρ * (B ⊗ₖ A)) := by
  have hk : (B ⊗ₖ A).submatrix Prod.swap Prod.swap = A ⊗ₖ B := by
    simpa only [conjTranspose_kronecker, conjTranspose_conjTranspose] using
      (conjTranspose_kronecker' Aᴴ Bᴴ).symm
  change trace (ρ.submatrix Prod.swap Prod.swap * (A ⊗ₖ B)) = _
  rw [← hk]
  exact (congrArg trace (submatrix_mul ρ (B ⊗ₖ A) Prod.swap Prod.swap Prod.swap
    (Equiv.prodComm (Fin 2) (Fin 2)).bijective).symm).trans
      (trace_flip (ρ * (B ⊗ₖ A)))

private lemma swap_readouts (ρ : TwoQubit) :
    blochA (partySwap ρ) = blochB ρ ∧
    blochB (partySwap ρ) = blochA ρ ∧ corr (partySwap ρ) = (corr ρ)ᵀ ∧
    centre (partySwap ρ) = centreB ρ ∧ centreB (partySwap ρ) = centre ρ := by
  have ha : blochA (partySwap ρ) = blochB ρ := by
    funext i
    exact congrArg Complex.re (swap_trace_product ρ (pauli i) 1)
  have hb : blochB (partySwap ρ) = blochA ρ := by
    funext i
    exact congrArg Complex.re (swap_trace_product ρ 1 (pauli i))
  have hT : corr (partySwap ρ) = (corr ρ)ᵀ := by
    funext i j
    exact congrArg Complex.re (swap_trace_product ρ (pauli i) (pauli j))
  refine ⟨ha, hb, hT, ?_, ?_⟩
  · rw [centre, centreB, ha, hb, hT]
    rfl
  · rw [centre, centreB, ha, hb, hT]
    rfl

private lemma frame_energy (T : Matrix (Fin 3) (Fin 3) ℝ)
    (β : Fin 3 → Fin 3 → ℝ)
    (hβ : ∀ i j, β i ⬝ᵥ β j = if i = j then 1 else 0) :
    ∑ i, vlen (T *ᵥ β i) ^ 2 = ∑ i, ∑ j, T i j ^ 2 := by
  let O : Matrix (Fin 3) (Fin 3) ℝ := β
  have hOO : O * Oᵀ = 1 := Matrix.ext hβ
  have hrev : Oᵀ * O = 1 := mul_eq_one_comm.mp hOO
  have hr (r : Fin 3 → ℝ) : ∑ i, (r ⬝ᵥ β i) ^ 2 = ∑ j, r j ^ 2 := by
    have hh : (O *ᵥ r) ⬝ᵥ (O *ᵥ r) = r ⬝ᵥ r := by
      simpa only [one_mulVec] using
        D5.S3.Arith.Lattices.Klartag.Walk.ChainEllipsoid.quad_congr_one
          (A := (1 : Matrix (Fin 3) (Fin 3) ℝ)) (S := O)
          (by simpa only [mul_one] using hrev) r
    simpa only [O, Matrix.mulVec, dotProduct, mul_comm, pow_two] using hh
  simp only [vlen_sq, dotProduct, Matrix.mulVec, ← pow_two]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => hr (T i))

private lemma setting_trace (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (a b : Fin 3 → ℝ) :
    trace (ρ * (spin a ⊗ₖ spin b)) = ((a ⬝ᵥ (corr ρ *ᵥ b) : ℝ) : ℂ) := by
  simpa only [bell.eq_def, add_zero, sub_zero, spin, Pi.zero_apply, Complex.ofReal_zero,
    zero_smul, Finset.sum_const_zero, zero_kronecker, add_zero, zero_dotProduct] using
    bell_trace_real_expansion ρ hρ a 0 b 0

private lemma setting_bound (ρ : TwoQubit) (hρ : ρ.IsHermitian)
    (α β : Fin 3 → Fin 3 → ℝ) (hα : ∀ i, vlen (α i) = 1)
    (hβ : ∀ i j, β i ⬝ᵥ β j = if i = j then 1 else 0) :
    ‖∑ i, trace (ρ * (spin (α i) ⊗ₖ spin (β i)))‖ / Real.sqrt 3 ≤
      Real.sqrt (∑ i, ∑ j, corr ρ i j ^ 2) := by
  have ht : (∑ i, trace (ρ * (spin (α i) ⊗ₖ spin (β i)))) =
      ((∑ i, α i ⬝ᵥ (corr ρ *ᵥ β i) : ℝ) : ℂ) := by
    simp only [setting_trace ρ hρ, Complex.ofReal_sum]
  rw [ht, Complex.norm_real, Real.norm_eq_abs]
  have hs : |∑ i, α i ⬝ᵥ (corr ρ *ᵥ β i)| ≤ ∑ i, vlen (corr ρ *ᵥ β i) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => unit_dot_le _ _ (hα i))
  have hz3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  apply (div_le_iff₀ hz3).2
  have hroot : ∑ i, vlen (corr ρ *ᵥ β i) ≤
      Real.sqrt (∑ i, ∑ j, corr ρ i j ^ 2) * Real.sqrt 3 := by
    simpa [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, frame_energy (corr ρ) β hβ] using
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun i => vlen (corr ρ *ᵥ β i)) (fun _ : Fin 3 => (1 : ℝ))
  exact hs.trans hroot

private lemma values_nonempty (ρ : TwoQubit) : (fThreeValues ρ).Nonempty := by
  rw [fThreeValues]
  refine ⟨_, (fun _ => ![0, 0, 1]), (fun i => Pi.single i 1), ?_, ?_, rfl⟩
  · intro i
    simpa only [abs_one] using
      D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.vlen_e3 (1 : ℝ)
  · intro i j
    simp only [dotProduct_single, Pi.single_apply, mul_one, eq_comm]

private lemma values_bddAbove (ρ : TwoQubit) (hρ : ρ.IsHermitian) :
    BddAbove (fThreeValues ρ) := by
  refine ⟨Real.sqrt (∑ i, ∑ j, corr ρ i j ^ 2), ?_⟩
  rintro r ⟨α, β, hα, hβ, rfl⟩
  exact setting_bound ρ hρ α β hα hβ

private lemma fThree_le_frobenius (ρ : TwoQubit) (hρ : ρ.IsHermitian) :
    fThree ρ ≤ Real.sqrt (∑ i, ∑ j, corr ρ i j ^ 2) := by
  rw [fThree]
  apply csSup_le (values_nonempty ρ)
  rintro r ⟨α, β, hα, hβ, rfl⟩
  exact setting_bound ρ hρ α β hα hβ

private lemma summed_flip (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    2 * (∑ i, ∑ j, corr ρ i j ^ 2) + vlen (blochB ρ) ^ 2 ≤ 3 + 6 * delta ρ := by
  have h (k : Fin 3) : (∑ i, ∑ j, corr ρ i j ^ 2) -
      vlen (corr ρ *ᵥ Pi.single k 1) ^ 2 +
      (blochB ρ ⬝ᵥ Pi.single k 1) ^ 2 ≤ 1 + 2 * delta ρ := by
    have hn : vlen (Pi.single k (1 : ℝ)) = 1 := by
      rw [vlen_eq_norm, PiLp.toLp_single]
      simpa only [norm_one] using
        (PiLp.norm_single (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ) k (1 : ℝ))
    have hf : (flipped ρ (Pi.single k 1)).PosSemidef :=
      hρ.transpose.mul_mul_conjTranspose_same _
    have hp : 0 ≤ (trace (ρ * flipped ρ (Pi.single k 1))).re :=
      RHLinalg.trace_mul_nonneg_of_posSemidef hρ hf
    have hi := flip_purity_identity ρ hρ.isHermitian htr (Pi.single k 1) hn
    linarith
  let T : Matrix (Fin 3) (Fin 3) ℝ := corr ρ
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => h k)
  change (∑ k, ((∑ i, ∑ j, T i j ^ 2) - vlen (T *ᵥ Pi.single k 1) ^ 2 +
    (blochB ρ ⬝ᵥ Pi.single k 1) ^ 2)) ≤ ∑ k : Fin 3, (1 + 2 * delta ρ) at hs
  simp only [mulVec_single_one, dotProduct_single_one] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, vlen_sq,
    dotProduct, ← pow_two, Matrix.col_apply] at hs
  rw [Finset.sum_comm (f := fun x i => T i x ^ 2)] at hs
  norm_num at hs
  change 2 * (∑ i, ∑ j, T i j ^ 2) + vlen (blochB ρ) ^ 2 ≤ 3 + 6 * delta ρ
  rw [vlen_sq]
  simp only [dotProduct, ← pow_two]
  linarith

private lemma affine_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    (∑ i, ∑ j, corr ρ i j ^ 2) ≤ 3 - 3 * vlen (centre ρ) +
      (3 * vlen (centre ρ) - 2) * vlen (blochB ρ) ^ 2 := by
  have hs := summed_flip ρ hρ htr
  have hd := delta_le_centre ρ hρ htr
  nlinarith

private lemma envelope (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    (∑ i, ∑ j, corr ρ i j ^ 2) ≤ max (3 * (1 - vlen (centre ρ))) 1 := by
  have ha := affine_bound ρ hρ htr
  have hb := bob_radius_le ρ hρ htr
  have hz := vlen_nonneg (blochB ρ)
  have hr : vlen (blochB ρ) ^ 2 ≤ 1 := pow_le_one₀ hz hb
  by_cases hc : 0 ≤ 3 * vlen (centre ρ) - 2
  · apply le_trans (b := 1) _ (le_max_right _ _)
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hr)]
  · apply le_trans (b := 3 * (1 - vlen (centre ρ))) _ (le_max_left _ _)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc)
      (sq_nonneg (vlen (blochB ρ)))]

private lemma universal_bound (ρ : TwoQubit) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    fThree ρ ≤ max (Real.sqrt (3 * (1 - vlen (centreB ρ)))) 1 := by
  have hp : (partySwap ρ).PosSemidef := hρ.submatrix Prod.swap
  have he := envelope (partySwap ρ) hp ((trace_flip ρ).trans htr)
  obtain ⟨_, _, hT, hc, _⟩ := swap_readouts ρ
  rw [hc, hT] at he
  have hsum : (∑ i, ∑ j, (corr ρ)ᵀ i j ^ 2) = ∑ i, ∑ j, corr ρ i j ^ 2 :=
    Finset.sum_comm
  rw [hsum] at he
  apply (fThree_le_frobenius ρ hρ.isHermitian).trans
  by_cases h : 3 * (1 - vlen (centreB ρ)) ≤ 1
  · rw [max_eq_right h] at he
    exact (Real.sqrt_le_one.mpr he).trans (le_max_right _ _)
  · rw [max_eq_left (le_of_not_ge h)] at he
    exact (Real.sqrt_le_sqrt he).trans (le_max_left _ _)

private lemma balanced_setting (ρ : TwoQubit) (hρ : ρ.IsHermitian) (p q : ℝ)
    (hT : corr ρ = diagonal ![p, -p, q]) (hE : 1 < 2 * p ^ 2 + q ^ 2) :
    1 < fThree ρ := by
  let c : ℝ := Real.sqrt 3 / 3
  have hc : c ^ 2 = 1 / 3 := by
    dsimp [c]
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  let β : Fin 3 → Fin 3 → ℝ :=
    ![![(1 + c) / 2, (c - 1) / 2, c], ![(c - 1) / 2, (1 + c) / 2, c], ![-c, -c, c]]
  have hβ : ∀ i j, β i ⬝ᵥ β j = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [β, dotProduct, Fin.sum_univ_three] <;> nlinarith [hc]
  let L := Real.sqrt ((2 * p ^ 2 + q ^ 2) / 3)
  have hL : 0 < L := Real.sqrt_pos.2 (by linarith)
  have hLs : L ^ 2 = (2 * p ^ 2 + q ^ 2) / 3 :=
    Real.sq_sqrt (by positivity)
  have hx (i : Fin 3) : vlen (corr ρ *ᵥ β i) = L := by
    have heq : vlen (corr ρ *ᵥ β i) ^ 2 = L ^ 2 := by
      rw [vlen_sq, hT]
      simp only [dotProduct, mulVec_diagonal]
      fin_cases i <;>
        norm_num [β, Fin.sum_univ_three] <;>
        nlinarith [congrArg (fun x : ℝ => p ^ 2 * x) hc,
          congrArg (fun x : ℝ => q ^ 2 * x) hc]
    exact (sq_eq_sq₀ (vlen_nonneg _) hL.le).mp heq
  have hne (i : Fin 3) : corr ρ *ᵥ β i ≠ 0 := by
    intro h
    have hz : vlen (corr ρ *ᵥ β i) = 0 := by rw [h, vlen_eq_norm]; simp
    linarith [hx i]
  let α : Fin 3 → Fin 3 → ℝ := fun i =>
    (vlen (corr ρ *ᵥ β i))⁻¹ • (corr ρ *ᵥ β i)
  have hα (i : Fin 3) : vlen (α i) = 1 := (normalized_unit _ (hne i)).1
  have hv (i : Fin 3) : α i ⬝ᵥ (corr ρ *ᵥ β i) = L := by
    change ((vlen (corr ρ *ᵥ β i))⁻¹ • (corr ρ *ᵥ β i)) ⬝ᵥ (corr ρ *ᵥ β i) = L
    rw [smul_dotProduct, smul_eq_mul, ← vlen_sq, hx i]
    simpa only [pow_two] using inv_mul_cancel_left₀ (ne_of_gt hL) L
  have hvsum : (∑ i, trace (ρ * (spin (α i) ⊗ₖ spin (β i)))) = ((3 * L : ℝ) : ℂ) := by
    simp only [setting_trace ρ hρ, hv, Fin.sum_univ_three]
    push_cast
    ring
  have hm : ‖∑ i, trace (ρ * (spin (α i) ⊗ₖ spin (β i)))‖ / Real.sqrt 3 ≤ fThree ρ :=
    le_csSup (values_bddAbove ρ hρ) ⟨α, β, hα, hβ, rfl⟩
  apply lt_of_lt_of_le _ hm
  rw [hvsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (lt_div_iff₀ (Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num))).2
  rw [one_mul]
  apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by norm_num), mul_pow, hLs]
  linarith

private lemma threshold_parameters (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 2 / 3) :
    0 < 2 - 2 * t - t ^ 2 ∧
    0 ≤ t * (1 - t) / (2 - 2 * t - t ^ 2) ∧
    t * (1 - t) / (2 - 2 * t - t ^ 2) < 1 := by
  have ht : t < 1 := by linarith
  have hd : 0 < 2 - 2 * t - t ^ 2 := by
    nlinarith [mul_nonneg ht₀ (show 0 ≤ 2 / 3 - t by linarith)]
  refine ⟨hd, div_nonneg (mul_nonneg ht₀ (by linarith)) hd.le, ?_⟩
  apply (div_lt_one hd).2
  nlinarith

private lemma threshold_energy (t s : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 2 / 3)
    (hs : s = t * (1 - t) / (2 - 2 * t - t ^ 2)) :
    1 < 2 * (Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s))) ^ 2 +
      (1 - t + t * s) ^ 2 := by
  obtain ⟨hd, hs₀, hs₁⟩ := threshold_parameters t ht₀ ht₁
  rw [← hs] at hs₀ hs₁
  have hx := Real.sq_sqrt (show 0 ≤ 1 + s by linarith)
  have ht : 0 ≤ 1 - t := by linarith
  have hy := Real.sq_sqrt (show 0 ≤ (1 - t) * (1 - s) by positivity)
  rw [mul_pow, hx, hy]
  let E := 2 * ((1 + s) * ((1 - t) * (1 - s))) + (1 - t + t * s) ^ 2
  have hsD : s * (2 - 2 * t - t ^ 2) = t * (1 - t) :=
    (eq_div_iff (ne_of_gt hd)).mp hs
  have heq : (E - 1) * (2 - 2 * t - t ^ 2) = (2 - 3 * t) ^ 2 := by
    calc
      (E - 1) * (2 - 2 * t - t ^ 2) =
          (2 - 4 * t + t ^ 2) * (2 - 2 * t - t ^ 2) +
          2 * (t * (1 - t)) * (s * (2 - 2 * t - t ^ 2)) -
          (s * (2 - 2 * t - t ^ 2)) ^ 2 := by dsimp [E]; ring
      _ = (2 - 3 * t) ^ 2 := by rw [hsD]; ring
  have hn : 0 < (2 - 3 * t) ^ 2 := sq_pos_of_pos (by linarith)
  change 1 < E
  have hp : 0 < (E - 1) * (2 - 2 * t - t ^ 2) := heq.symm ▸ hn
  exact lt_of_sub_pos ((mul_pos_iff_of_pos_right hd).mp hp)

private lemma threshold_family (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 2 / 3) :
    ∃ ρ : TwoQubit, ρ.PosSemidef ∧ trace ρ = 1 ∧
      vlen (centreB ρ) = t ∧ 1 < fThree ρ := by
  let s := t * (1 - t) / (2 - 2 * t - t ^ 2)
  obtain ⟨_, hs₀, hs₁⟩ := threshold_parameters t ht₀ ht₁
  have ht : t ≤ 1 := by linarith
  obtain ⟨htr, _, _, hT⟩ := tight_readouts t s ht hs₀ hs₁.le
  have hp := tight_psd t s ht₀ hs₁.le
  obtain ⟨_, _, hflip, _, hc⟩ := swap_readouts (tightState t s)
  refine ⟨partySwap (tightState t s), hp.submatrix Prod.swap,
    (trace_flip _).trans htr, ?_, ?_⟩
  · rw [hc]
    exact tight_centre t s ht₀ ht hs₀ hs₁
  · apply balanced_setting (partySwap (tightState t s))
      (hp.submatrix Prod.swap).isHermitian
      (Real.sqrt (1 + s) * Real.sqrt ((1 - t) * (1 - s))) (1 - t + t * s)
    · exact (hflip.trans (congrArg Matrix.transpose hT)).trans (diagonal_transpose _)
    · exact threshold_energy t s ht₀ ht₁ rfl

theorem result : claim := ⟨universal_bound, threshold_family⟩

end D5.S3.Quantum.Contextuality.SteeringEllipsoidFThreeThreshold
