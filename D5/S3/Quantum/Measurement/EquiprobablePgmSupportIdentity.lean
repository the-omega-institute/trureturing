/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Original-prior PGM advantage is a centered dispersion on singular support. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation

/-!
The centered-dispersion argument is from the anonymous manuscript
“Why the Active-Set PGM Comparison Can Fail” (3 November 2026), section 2.
The manuscript has no supplied license grant. Its attribution is anonymous;
the CC BY 4.0 license of the separate Ma–Zhang note does not apply to it.
The actual score and squared Hilbert-Schmidt norm are reused, respectively,
from EquiprobablePgmActiveSetRefutation and RHLinalg.frobSq (whose original
Anthropic/Zeta attribution and Apache-2.0 license remain at their owner).

Admission commitment before compilation: the new content is the singular
spectral quarter-power normalization and its use in the centered PGM identity.
No invertibility assumption is made. Real negative powers vanish at zero.
The I header records the inherited I-classified score owner, not a restriction
of the universally quantified density-matrix statements below.
The full-versus-active comparison is not a consequence of this identity.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity

open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma finite_spectrum_continuous (Q : Matrix n n ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ Q) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

/-- The support inverse quarter-power squares to the support inverse square-root;
its sandwich of the average is the ordinary positive square-root, including zero eigenvalues. -/
theorem support_quarter_normalization (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) :
    Q ^ (-(1 / 4) : ℝ) * Q ^ (-(1 / 4) : ℝ) = Q ^ (-(1 / 2) : ℝ) ∧
      Q ^ (-(1 / 4) : ℝ) * Q * Q ^ (-(1 / 4) : ℝ) = CFC.sqrt Q := by
  have hm (f g : ℝ → ℝ) : cfc f Q * cfc g Q = cfc (fun x => f x * g x) Q :=
    (cfc_mul f g Q (finite_spectrum_continuous Q f)
      (finite_spectrum_continuous Q g)).symm
  have hr (x y : ℝ) (hx : 0 < x) : x ^ y * x ^ y = x ^ (y + y) :=
    (Real.rpow_add hx y y).symm
  constructor
  · simp only [CFC.rpow_eq_cfc_real hQ.nonneg]
    rw [hm]
    apply cfc_congr
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hQ.nonneg hx
    rcases eq_or_lt_of_le hx0 with h | h
    · subst x
      norm_num
    · change x ^ (-(1 / 4) : ℝ) * x ^ (-(1 / 4) : ℝ) = x ^ (-(1 / 2) : ℝ)
      rw [hr x _ h]
      norm_num
  · simp only [CFC.rpow_eq_cfc_real hQ.nonneg]
    calc
      cfc (fun x : ℝ => x ^ (-(1 / 4) : ℝ)) Q * Q *
          cfc (fun x : ℝ => x ^ (-(1 / 4) : ℝ)) Q =
          cfc (fun x : ℝ => x ^ (-(1 / 4) : ℝ)) Q * cfc (fun x : ℝ => x) Q *
          cfc (fun x : ℝ => x ^ (-(1 / 4) : ℝ)) Q := by
            rw [cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint]
      _ = cfc (fun x : ℝ => (x ^ (-(1 / 4) : ℝ) * x) *
          x ^ (-(1 / 4) : ℝ)) Q := by rw [hm, hm]
      _ = CFC.sqrt Q := by
        rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hQ.nonneg]
        apply cfc_congr
        intro x hx
        have hx0 := spectrum_nonneg_of_nonneg hQ.nonneg hx
        rcases eq_or_lt_of_le hx0 with h | h
        · subst x
          norm_num
        · change (x ^ (-(1 / 4) : ℝ) * x) * x ^ (-(1 / 4) : ℝ) = x ^ (1 / 2 : ℝ)
          calc
            _ = (x ^ (-(1 / 4) : ℝ) * x ^ (1 : ℝ)) * x ^ (-(1 / 4) : ℝ) := by
              rw [Real.rpow_one]
            _ = x ^ ((-(1 / 4) : ℝ) + 1 + (-(1 / 4) : ℝ)) := by
              rw [← Real.rpow_add h, ← Real.rpow_add h]
            _ = _ := by norm_num

omit [DecidableEq n] in
private lemma quarter_frob (R W T : Matrix n n ℂ)
    (hR : Rᴴ = R) (hT : Tᴴ = T) (hRR : R * R = W) :
    RHLinalg.frobSq (R * T * R) = (trace (T * (W * T) * W)).re := by
  unfold RHLinalg.frobSq
  simp only [Matrix.conjTranspose_mul, hR, hT]
  change (trace (R * (T * R) * (R * T * R))).re = _
  apply congrArg Complex.re
  calc
    trace (R * (T * R) * (R * T * R)) =
        trace ((T * R) * (R * T * R) * R) := by
          simpa only [mul_assoc] using Matrix.trace_mul_comm R ((T * R) * (R * T * R))
    _ = trace (T * (R * R * T) * (R * R)) := by
      simp only [mul_assoc]
    _ = trace (T * (W * T) * W) := by rw [hRR]

omit [DecidableEq n] in
private lemma frob_smul (r : ℝ) (T : Matrix n n ℂ) :
    RHLinalg.frobSq (r • T) = r ^ 2 * RHLinalg.frobSq T := by
  simp [RHLinalg.frobSq, Matrix.conjTranspose_smul,
    Matrix.trace_smul, smul_smul, pow_two, mul_assoc]

omit [DecidableEq n] in
private lemma centered_frob_sum {ι : Type*}
    (B : Finset ι) (hB : B.Nonempty) (X : ι → Matrix n n ℂ)
    (hX : ∀ i ∈ B, (X i).IsHermitian) :
    (∑ i ∈ B, RHLinalg.frobSq (X i - (1 / (B.card : ℝ)) • ∑ j ∈ B, X j)) =
      (∑ i ∈ B, RHLinalg.frobSq (X i)) -
        (1 / (B.card : ℝ)) * RHLinalg.frobSq (∑ j ∈ B, X j) := by
  let T := ∑ j ∈ B, X j
  let r : ℝ := 1 / (B.card : ℝ)
  have hT : T.IsHermitian := by
    exact isSelfAdjoint_sum B hX
  have hrT : (r • T).IsHermitian := hT.smul (isSelfAdjoint_iff.mpr rfl)
  have hex (i : ι) (hi : i ∈ B) :
      RHLinalg.frobSq (X i - r • T) = RHLinalg.frobSq (X i) -
        2 * r * (trace (X i * T)).re + r ^ 2 * RHLinalg.frobSq T := by
    rw [sub_eq_add_neg, RHLinalg.frobSq_add_hermitian (hX i hi) hrT.neg]
    have hn : RHLinalg.frobSq (-(r • T)) = RHLinalg.frobSq (r • T) := by
      simp [RHLinalg.frobSq]
    rw [hn, frob_smul]
    simp [Matrix.trace_neg, Matrix.trace_smul]
    ring
  have hcross : (∑ i ∈ B, (trace (X i * T)).re) = RHLinalg.frobSq T := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul]
    change (trace (T * T)).re = RHLinalg.frobSq T
    rw [RHLinalg.frobSq, hT.eq]
    rfl
  have hc : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast hB.card_pos.ne'
  change (∑ i ∈ B, RHLinalg.frobSq (X i - r • T)) = _
  rw [Finset.sum_congr rfl hex]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hcross]
  dsimp [r, T]
  field_simp
  ring

set_option maxHeartbeats 800000 in
/-- The original-prior PGM advantage is exactly the centered squared Hilbert-Schmidt
norm of the Moore-Penrose quarter-power sandwiches. No rank assumption is needed. -/
theorem centered_identity {d N : ℕ}
    (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ) (hN : 0 < N)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (B : Finset (Fin N)) (hB : B.Nonempty) :
    let S := ∑ j ∈ B, (1 / (N : ℂ)) • ρ j
    let R := S ^ (-(1 / 4) : ℝ)
    pgmScore ρ B - 1 / N =
      ∑ i ∈ B, RHLinalg.frobSq
        (R * ((1 / (N : ℂ)) • ρ i) * R - (1 / (B.card : ℝ)) • CFC.sqrt S) := by
  let σ := fun i => (1 / (N : ℂ)) • ρ i
  let S := ∑ j ∈ B, σ j
  let R := S ^ (-(1 / 4) : ℝ)
  have hσ (i : Fin N) : (σ i).PosSemidef := by
    apply (hρ i).smul
    apply Complex.nonneg_iff.mpr
    constructor
    · simp only [one_div, Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast]
      positivity
    · simp
  have hS : S.PosSemidef := Matrix.posSemidef_sum B (fun i _ => hσ i)
  have hR : R.IsHermitian := (CFC.rpow_nonneg (a := S) (y := -(1 / 4))).posSemidef.1
  have hnorm := support_quarter_normalization S hS
  have hsum : (∑ i ∈ B, R * σ i * R) = CFC.sqrt S := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    exact hnorm.2
  have hX (i : Fin N) (_ : i ∈ B) : (R * σ i * R).IsHermitian := by
    simpa only [hR.eq] using Matrix.isHermitian_conjTranspose_mul_mul R (hσ i).1
  have hvar := centered_frob_sum B hB (fun i => R * σ i * R) hX
  rw [hsum] at hvar
  have hscore : (∑ i ∈ B, RHLinalg.frobSq (R * σ i * R)) = pgmScore ρ B := by
    unfold pgmScore
    apply Finset.sum_congr rfl
    intro i _
    change RHLinalg.frobSq (R * σ i * R) =
      (trace (σ i * (S ^ (-(1 / 2) : ℝ) * σ i * S ^ (-(1 / 2) : ℝ)))).re
    simpa only [mul_assoc] using
      quarter_frob R _ (σ i) hR.eq (hσ i).1.eq hnorm.1
  have hfrob : RHLinalg.frobSq (CFC.sqrt S) = (B.card : ℝ) / N := by
    have hsqrt : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).posSemidef.1
    rw [RHLinalg.frobSq, hsqrt.eq, CFC.sqrt_mul_sqrt_self S hS.nonneg]
    change (trace S).re = _
    have hinv : (1 / (N : ℂ)) = ((1 / (N : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    simp only [S, σ, Matrix.trace_sum, Matrix.trace_smul, htr, smul_eq_mul,
      mul_one, hinv, Complex.re_sum, Complex.ofReal_re, Finset.sum_const, nsmul_eq_mul,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  rw [hscore, hfrob] at hvar
  change pgmScore ρ B - 1 / N = _
  rw [hvar]
  congr 1
  field_simp

/-- In particular the original-prior score is at least random guessing, on every
nonempty label set, including singular averages and singleton label sets. -/
theorem random_guessing_le {d N : ℕ}
    (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ) (hN : 0 < N)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (B : Finset (Fin N)) (hB : B.Nonempty) : 1 / (N : ℝ) ≤ pgmScore ρ B := by
  have hid := centered_identity ρ hN hρ htr B hB
  dsimp only at hid
  have hn : 0 ≤ pgmScore ρ B - 1 / N := by
    rw [hid]
    apply Finset.sum_nonneg
    intro i _
    exact (Complex.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg).1
  linarith

end D5.S3.Quantum.Measurement.EquiprobablePgmSupportIdentity
