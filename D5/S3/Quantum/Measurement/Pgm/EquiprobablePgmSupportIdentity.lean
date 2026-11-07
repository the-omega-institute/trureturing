/- GID: D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmSupportIdentity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Pgm/EquiprobablePgmSupportIdentity
   mirror-E: none(waiver:universal-actual-object-proof)
   anchors: []
   utility: none
   digest: Singular-support PGM mechanism, actual bounds, completion and minimality. -/

import D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation
import D5.S3.Quantum.Lieb.SupportPerspectiveTransport
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import D5.S3.Quantum.FiniteDimensional

/-!
Anonymous mechanism attribution is retained. The old literal byline is Wenlin
Zhang and Haobo / trureturing. The new note is by Haobo Ma then Wenlin Zhang;
its CC BY 4.0 grant applies to that note only. Hyunho Cha is credited for the
symmetric scores and the qubit and commuting constructions. No priority claim
is made. Normalization and algebra helpers are retained on actual consumer
paths; their presence is not an independent admission witness.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity

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
/-- Finite Hermitian variance used by the PGM identity and its discrimination bound. -/
lemma centered_frob_sum {ι : Type*}
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

open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)

theorem diagonal_inverse_sqrt {n : Type*} [Fintype n] [DecidableEq n]
    (s : n → ℝ) (hs : ∀ x, 0 ≤ s x) :
    (diagonal (fun x => (s x : ℂ))) ^ (-(1 / 2) : ℝ) =
      diagonal (fun x => ((Real.sqrt (s x))⁻¹ : ℂ)) := by
  have hS : (diagonal (fun x => (s x : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun x => by
      change (0 : ℂ) ≤ (s x : ℂ)
      exact_mod_cast hs x)
  rw [CFC.rpow_eq_cfc_real hS.nonneg, cfc_diagonal]
  congr 1
  funext x
  congr 1
  rw [Real.rpow_neg (hs x), ← Real.sqrt_eq_rpow]
  push_cast
  rfl

/-- Every diagonal ensemble has this actual Moore–Penrose PGM score, including
singular joint support. Division by a zero spectral mass has the support value zero. -/
theorem diagonal_score {d N : ℕ} (hN : 0 < N) (p : Fin N → Fin d → ℝ)
    (hp : ∀ i x, 0 ≤ p i x) (B : Finset (Fin N)) :
    pgmScore (fun i => diagonal (fun x => (p i x : ℂ))) B =
      (1 / (N : ℝ)) * ∑ i ∈ B, ∑ x, (p i x) ^ 2 / (∑ j ∈ B, p j x) := by
  let s : Fin d → ℝ := fun x => (1 / (N : ℝ)) * ∑ j ∈ B, p j x
  have hs (x) : 0 ≤ s x := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => hp i x)
  have hsum : (∑ j ∈ B, (1 / (N : ℂ)) • diagonal (fun x => (p j x : ℂ))) =
      diagonal (fun x => (s x : ℂ)) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [s, Matrix.sum_apply, Finset.mul_sum]
    · simp [Matrix.sum_apply, Matrix.smul_apply, hxy]
  unfold pgmScore
  rw [hsum, diagonal_inverse_sqrt s hs]
  have hsingle (i : Fin N) :
      (trace ((1 / (N : ℂ)) • diagonal (fun x => (p i x : ℂ)) *
        (diagonal (fun x => ((Real.sqrt (s x))⁻¹ : ℂ)) *
          (1 / (N : ℂ)) • diagonal (fun x => (p i x : ℂ)) *
            diagonal (fun x => ((Real.sqrt (s x))⁻¹ : ℂ))))).re =
        (1 / (N : ℝ)) * ∑ x, (p i x) ^ 2 / (∑ j ∈ B, p j x) := by
    simp only [← Matrix.diagonal_smul, Pi.smul_apply, smul_eq_mul, Matrix.diagonal_mul_diagonal,
      trace_diagonal, Complex.re_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hsqrt := Real.sq_sqrt (hs x)
    have hpow : ((Real.sqrt (s x))⁻¹) ^ 2 = (s x)⁻¹ := by
      rw [inv_pow, hsqrt]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div,
      ← Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.ofReal_re]
    calc
      _ = (1 / (N : ℝ)) ^ 2 * (p i x) ^ 2 * ((Real.sqrt (s x))⁻¹) ^ 2 := by ring
      _ = _ := by
        rw [hpow]
        dsimp [s]
        simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv, one_mul]
        have hcancel : (N : ℝ) * (N : ℝ)⁻¹ ^ 2 = (N : ℝ)⁻¹ := by
          field_simp
        linear_combination (p i x) ^ 2 * (∑ j ∈ B, p j x)⁻¹ * hcancel
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hsingle i)

open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore success)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open D5.S3.Quantum.Matrix.CartesianVariance

/-- Actual support inverse-square-root effects, with the original priors. -/
def pgmEffects {d N : ℕ} (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (B : Finset (Fin N)) (i : Fin N) : Matrix (Fin d) (Fin d) ℂ :=
  if i ∈ B then
    let W := (∑ j ∈ B, (1 / (N : ℂ)) • ρ j) ^ (-(1 / 2) : ℝ)
    W * ((1 / (N : ℂ)) • ρ i) * W
  else 0

private theorem weighted_nonneg {d N : ℕ}
    (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ) (hρ : ∀ i, (ρ i).PosSemidef)
    (i : Fin N) : ((1 / (N : ℂ)) • ρ i).PosSemidef := by
  apply (hρ i).smul
  exact Complex.nonneg_iff.mpr ⟨by simp, by simp⟩

private theorem inverse_sqrt_eq {d : ℕ} (S : Matrix (Fin d) (Fin d) ℂ)
    (hS : S.PosSemidef) : S ^ (-(1 / 2) : ℝ) = spectralInverseSqrt S := by
  rw [CFC.rpow_eq_cfc_real hS.nonneg]
  unfold spectralInverseSqrt
  apply cfc_congr
  intro x hx
  dsimp only
  rw [Real.rpow_neg (spectrum_nonneg_of_nonneg hS.nonneg hx), Real.sqrt_eq_rpow]

/-- Each input is supported on the joint spectral support, and the actual PGM
sums to that projection, without a positive-definite assumption. -/
theorem pgm_support {d N : ℕ} (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (B : Finset (Fin N)) :
    let S := ∑ j ∈ B, (1 / (N : ℂ)) • ρ j
    let P := spectralSupport S
    IsStarProjection P ∧
      (∀ i ∈ B, P * ((1 / (N : ℂ)) • ρ i) = (1 / (N : ℂ)) • ρ i ∧
        ((1 / (N : ℂ)) • ρ i) * P = (1 / (N : ℂ)) • ρ i) ∧
      (∀ i, (pgmEffects ρ B i).PosSemidef) ∧ ∑ i, pgmEffects ρ B i = P := by
  let σ := fun i => (1 / (N : ℂ)) • ρ i
  let S := ∑ j ∈ B, σ j
  let P := spectralSupport S
  let W := S ^ (-(1 / 2) : ℝ)
  have hσ := weighted_nonneg ρ hρ
  have hS : S.PosSemidef := Matrix.posSemidef_sum B (fun i _ => hσ i)
  have hn := spectral_sqrt_normalization S hS
  dsimp only at hn
  have hW : Wᴴ = W := (CFC.rpow_nonneg (a := S) (y := -(1 / 2))).posSemidef.1.eq
  refine ⟨⟨hn.2.2.2.1, hn.2.2.1⟩, ?_, ?_, ?_⟩
  · intro i hi
    apply support_of_nonneg_le_smul S (σ i) P hn.2.2.1 hn.2.2.2.2.2.2.1 (hσ i) 1
    simpa only [one_smul] using
      Finset.single_le_sum (fun j _ => (hσ j).nonneg) hi
  · intro i
    unfold pgmEffects
    split_ifs
    · simpa only [hW] using (hσ i).conjTranspose_mul_mul_same W
    · exact Matrix.PosSemidef.zero
  · change (∑ i, if i ∈ B then W * σ i * W else 0) = P
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    change W * S * W = P
    rw [show W = spectralInverseSqrt S from inverse_sqrt_eq S hS]
    exact hn.2.2.2.2.2.2.2

/-- Completion on any selected label gives an actual POVM with exactly the
support PGM score. Its complement has zero overlap with every selected state. -/
theorem pgm_completion {k N : ℕ}
    (ρ : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (B : Finset (Fin N)) (b : Fin N) (hb : b ∈ B) :
    let P := spectralSupport (∑ j ∈ B, (1 / (N : ℂ)) • ρ j)
    let E := fun i => pgmEffects ρ B i + if i = b then 1 - P else 0
    finitePOVM E ∧ (∀ i, i ∉ B → E i = 0) ∧ success ρ E = pgmScore ρ B := by
  have hs := pgm_support ρ hρ B
  dsimp only at hs ⊢
  let P := spectralSupport (∑ j ∈ B, (1 / (N : ℂ)) • ρ j)
  have hcomp : (1 - P).PosSemidef := hs.1.one_sub_nonneg.posSemidef
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    apply (hs.2.2.1 i).add
    split_ifs
    · exact hcomp
    · exact Matrix.PosSemidef.zero
  · rw [Finset.sum_add_distrib, hs.2.2.2]
    simp
  · intro i hi
    have hib : i ≠ b := by intro h; subst i; exact hi hb
    simp [pgmEffects, hi, hib]
  · unfold success pgmScore
    simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re, Finset.sum_add_distrib]
    have hfirst :
        (∑ i, (trace ((1 / (N : ℂ)) • ρ i * pgmEffects ρ B i)).re) =
          ∑ i ∈ B, (trace ((1 / (N : ℂ)) • ρ i *
            ((∑ j ∈ B, (1 / (N : ℂ)) • ρ j) ^ (-(1 / 2) : ℝ) *
              ((1 / (N : ℂ)) • ρ i) *
              (∑ j ∈ B, (1 / (N : ℂ)) • ρ j) ^ (-(1 / 2) : ℝ)))).re := by
      calc
        _ = ∑ i ∈ B, (trace ((1 / (N : ℂ)) • ρ i * pgmEffects ρ B i)).re := by
          symm
          apply Finset.sum_subset (Finset.subset_univ B)
          intro i _ hi
          simp [pgmEffects, hi]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [pgmEffects, if_pos hi]
    rw [hfirst]
    have hzero : (∑ i, (trace ((1 / (N : ℂ)) • ρ i *
        (if i = b then 1 - P else 0))).re) = 0 := by
      rw [Finset.sum_eq_single b]
      · simp only [ite_true, P, Matrix.mul_sub, Matrix.mul_one,
          (hs.2.1 b hb).2, sub_self, Matrix.trace_zero, Complex.zero_re]
      · intro i _ hi
        simp [hi]
      · simp
    change _ + (∑ i, (trace ((1 / (N : ℂ)) • ρ i *
      (if i = b then 1 - P else 0))).re) = _
    rw [hzero, add_zero]

private theorem quarter_support {d : ℕ} (S : Matrix (Fin d) (Fin d) ℂ)
    (hS : S.PosSemidef) :
    let T := S ^ (1 / 4 : ℝ)
    let R := S ^ (-(1 / 4) : ℝ)
    T * R = spectralSupport S ∧ R * T = spectralSupport S ∧ T * T = CFC.sqrt S := by
  have hm (f g : ℝ → ℝ) : cfc f S * cfc g S = cfc (fun x => f x * g x) S := by
    apply (cfc_mul f g S ?_ ?_).symm <;>
      rw [continuousOn_iff_continuous_domRestrict] <;> fun_prop
  dsimp only
  have hprod : S ^ (1 / 4 : ℝ) * S ^ (-(1 / 4) : ℝ) = spectralSupport S := by
    simp only [CFC.rpow_eq_cfc_real hS.nonneg, spectralSupport]
    rw [hm]
    apply cfc_congr
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hS.nonneg hx
    dsimp only
    rcases eq_or_lt_of_le hx0 with h | h
    · subst x; norm_num
    · rw [← Real.rpow_add h]
      norm_num [h.ne']
  refine ⟨hprod, ?_, ?_⟩
  · rw [← hprod]
    simp only [CFC.rpow_eq_cfc_real hS.nonneg, hm]
    congr 1
    funext x
    exact mul_comm _ _
  · simp only [CFC.rpow_eq_cfc_real hS.nonneg]
    rw [hm, CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hS.nonneg]
    apply cfc_congr
    intro x hx
    have hx0 := spectrum_nonneg_of_nonneg hS.nonneg hx
    dsimp only
    rcases eq_or_lt_of_le hx0 with h | h
    · subst x; norm_num
    · rw [← Real.rpow_add h]
      norm_num

private theorem centered_pair_sum {d N : ℕ} (B : Finset (Fin N)) (hB : B.Nonempty)
    (X Y : Fin N → Matrix (Fin d) (Fin d) ℂ) (L : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∑ i ∈ B, X i = L) (hY : ∑ i ∈ B, Y i = L) :
    (∑ i ∈ B, (trace ((X i - (1 / (B.card : ℝ)) • L) *
      (Y i - (1 / (B.card : ℝ)) • L))).re) =
      (∑ i ∈ B, (trace (X i * Y i)).re) -
        (1 / (B.card : ℝ)) * (trace (L * L)).re := by
  let r : ℝ := 1 / (B.card : ℝ)
  have hXL : (∑ i ∈ B, (trace (X i * L)).re) = (trace (L * L)).re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hX]
  have hLY : (∑ i ∈ B, (trace (L * Y i)).re) = (trace (L * L)).re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hY]
  have hex (i : Fin N) : (trace ((X i - r • L) * (Y i - r • L))).re =
      (trace (X i * Y i)).re - r * (trace (X i * L)).re -
        r * (trace (L * Y i)).re + r ^ 2 * (trace (L * L)).re := by
    simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul]
    ring
  change (∑ i ∈ B, (trace ((X i - r • L) * (Y i - r • L))).re) = _
  simp_rw [hex]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hXL, hLY]
  dsimp [r]
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  field_simp
  ring

set_option maxHeartbeats 800000 in
private theorem supported_upper_bound {k N : ℕ}
    (ρ : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hN : 0 < N)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (B : Finset (Fin N)) (hB : B.Nonempty)
    (E : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : finitePOVM E)
    (hout : ∀ i, i ∉ B → E i = 0) :
    success ρ E ≤ 1 / N +
      Real.sqrt (((B.card : ℝ) - 1) * (pgmScore ρ B - 1 / N) / N) := by
  let σ := fun i => (1 / (N : ℂ)) • ρ i
  let S := ∑ j ∈ B, σ j
  let R := S ^ (-(1 / 4) : ℝ)
  let T := S ^ (1 / 4 : ℝ)
  let L := CFC.sqrt S
  let P := spectralSupport S
  let X := fun i => R * σ i * R
  let Y := fun i => T * E i * T
  let r : ℝ := 1 / (B.card : ℝ)
  have hσ := weighted_nonneg ρ hρ
  have hS : S.PosSemidef := Matrix.posSemidef_sum B (fun i _ => hσ i)
  have hR : Rᴴ = R := (CFC.rpow_nonneg (a := S) (y := -(1 / 4))).posSemidef.1.eq
  have hT : Tᴴ = T := (CFC.rpow_nonneg (a := S) (y := 1 / 4)).posSemidef.1.eq
  have hL : Lᴴ = L := (CFC.sqrt_nonneg S).posSemidef.1.eq
  have hn := quarter_support S hS
  dsimp only at hn
  have hsupport := (pgm_support ρ hρ B).2.1
  have hX : ∀ i, (X i).PosSemidef := fun i => by
    simpa only [hR] using (hσ i).conjTranspose_mul_mul_same R
  have hY : ∀ i, (Y i).PosSemidef := fun i => by
    simpa only [hT] using (hE.1 i).conjTranspose_mul_mul_same T
  have hsumX : ∑ i ∈ B, X i = L := by
    change (∑ i ∈ B, R * σ i * R) = L
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    exact (D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity.support_quarter_normalization S hS).2
  have hsumE : ∑ i ∈ B, E i = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ B) (fun i _ hi => hout i hi)]
    exact hE.2
  have hsumY : ∑ i ∈ B, Y i = L := by
    change (∑ i ∈ B, T * E i * T) = L
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsumE, Matrix.mul_one]
    exact hn.2.2
  have hfrobL : RHLinalg.frobSq L = (B.card : ℝ) / N := by
    rw [RHLinalg.frobSq, hL, CFC.sqrt_mul_sqrt_self S hS.nonneg]
    change (trace S).re = _
    simp [S, σ, Matrix.trace_sum, Matrix.trace_smul, htr]
    ring
  have hLL : (trace (L * L)).re = (B.card : ℝ) / N := by
    simpa only [RHLinalg.frobSq, hL, RCLike.re_eq_complex_re] using hfrobL
  have hpair (i : Fin N) (hi : i ∈ B) :
      trace (X i * Y i) = trace (σ i * E i) := by
    calc
      _ = trace (σ i * (R * T) * E i * (T * R)) := by
        dsimp [X, Y]
        simpa only [mul_assoc] using
          (Matrix.trace_mul_comm R (σ i * R * (T * E i * T)))
      _ = trace (σ i * P * E i * P) := by rw [hn.1, hn.2.1]
      _ = trace (P * σ i * P * E i) := by
        simpa only [mul_assoc] using Matrix.trace_mul_comm (σ i * P * E i) P
      _ = trace (σ i * E i) := by rw [(hsupport i hi).1, (hsupport i hi).2]
  have hscore : (∑ i ∈ B, (trace (X i * Y i)).re) = success ρ E := by
    rw [Finset.sum_congr rfl (fun i hi => congrArg Complex.re (hpair i hi))]
    unfold success
    apply Finset.sum_subset (Finset.subset_univ B)
    intro i _ hi
    simp [hout i hi]
  have hcenter := centered_pair_sum B hB X Y L hsumX hsumY
  rw [hscore, hLL] at hcenter
  have hc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hcancel : (1 / (B.card : ℝ)) * ((B.card : ℝ) / N) = 1 / N := by field_simp
  rw [hcancel] at hcenter
  have hvarX := D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity.centered_identity
    ρ hN hρ htr B hB
  dsimp only at hvarX
  change pgmScore ρ B - 1 / N =
    ∑ i ∈ B, RHLinalg.frobSq (X i - r • L) at hvarX
  have hsumYsq : (∑ i ∈ B, RHLinalg.frobSq (Y i)) ≤ RHLinalg.frobSq L := by
    calc
      _ ≤ ∑ i ∈ B, (trace (Y i * L)).re := by
        apply Finset.sum_le_sum
        intro i hi
        have hle : Y i ≤ L := by
          rw [← hsumY]
          exact Finset.single_le_sum (fun j _ => (hY j).nonneg) hi
        have hp := RHLinalg.trace_mul_nonneg_of_posSemidef (hY i)
          (sub_nonneg.mpr hle).posSemidef
        rw [Matrix.mul_sub, Matrix.trace_sub, RCLike.re_eq_complex_re, Complex.sub_re] at hp
        simpa only [RHLinalg.frobSq, (hY i).isHermitian.eq, RCLike.re_eq_complex_re] using sub_nonneg.mp hp
      _ = RHLinalg.frobSq L := by
        rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hsumY,
          RHLinalg.frobSq, hL, RCLike.re_eq_complex_re]
  have hvarY : (∑ i ∈ B, RHLinalg.frobSq (Y i - r • L)) ≤ ((B.card : ℝ) - 1) / N := by
    have hv := D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity.centered_frob_sum
      B hB Y (fun i _ => (hY i).isHermitian)
    rw [hsumY, hfrobL, hcancel] at hv
    change (∑ i ∈ B, RHLinalg.frobSq (Y i - r • L)) = _ at hv
    rw [hv]
    rw [hfrobL] at hsumYsq
    rw [sub_div]
    linarith
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul B
    (fun i _ => frobSq_nonneg (X i - r • L))
    (fun i _ => frobSq_nonneg (Y i - r • L)) (fun i _ => show
      (trace ((X i - r • L) * (Y i - r • L))).re ^ 2 ≤
        RHLinalg.frobSq (X i - r • L) * RHLinalg.frobSq (Y i - r • L) from by
      have hm := trace_product_cauchy (X i - r • L) (Y i - r • L)
      have hreal : (trace ((X i - r • L) * (Y i - r • L))).re ^ 2 ≤
          Complex.normSq (trace ((X i - r • L) * (Y i - r • L))) := by
        simp only [Complex.normSq_apply]
        nlinarith [sq_nonneg ((trace ((X i - r • L) * (Y i - r • L))).im)]
      exact hreal.trans hm)
  change (∑ i ∈ B, (trace ((X i - r • L) * (Y i - r • L))).re) ^ 2 ≤ _ at hCS
  rw [hcenter, ← hvarX] at hCS
  have hnonneg := sub_nonneg.mpr
    (D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity.random_guessing_le ρ hN hρ htr B hB)
  have hmul := mul_le_mul_of_nonneg_left hvarY hnonneg
  have hbound : (success ρ E - 1 / N) ^ 2 ≤
      ((B.card : ℝ) - 1) * (pgmScore ρ B - 1 / N) / N := by
    convert hCS.trans hmul using 1 <;> ring
  have hrad : 0 ≤ ((B.card : ℝ) - 1) * (pgmScore ρ B - 1 / N) / N :=
    le_trans (sq_nonneg _) hbound
  nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg
    (((B.card : ℝ) - 1) * (pgmScore ρ B - 1 / N) / N)]

/-- The two separately valid upper bounds hold simultaneously for every actual
POVM, with its actual nonzero-effect active set. No ordering of the two PGM
advantages is asserted. Both one-label endpoints are included. -/
theorem actual_bounds {k N : ℕ}
    (ρ : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hN : 0 < N)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (E : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : finitePOVM E) :
    let A := Finset.univ.filter (fun i => E i ≠ 0)
    A.Nonempty ∧ success ρ E ≤ min
      (1 / N + Real.sqrt (((A.card : ℝ) - 1) * (pgmScore ρ A - 1 / N) / N))
      (1 / N + Real.sqrt (((N : ℝ) - 1) * (pgmScore ρ Finset.univ - 1 / N) / N)) := by
  let A := Finset.univ.filter (fun i => E i ≠ 0)
  have hout : ∀ i, i ∉ A → E i = 0 := by simpa [A]
  have hA : A.Nonempty := by
    by_contra h
    have hz : ∀ i, E i = 0 := fun i => hout i (by simpa [Finset.not_nonempty_iff_eq_empty.mp h])
    have hc := hE.2
    simp only [hz, Finset.sum_const_zero] at hc
    have he := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ => M 0 0) hc
    simpa using he
  refine ⟨hA, le_min (supported_upper_bound ρ hN hρ htr A hA E hE hout) ?_⟩
  have hU : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  simpa only [Finset.card_univ, Fintype.card_fin] using
    supported_upper_bound ρ hN hρ htr Finset.univ hU E hE (by simp)

open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore)

/-- Every singleton has exactly the original random-guessing score, even when its
state is singular. This includes the one-label endpoint of the valid bounds. -/
theorem singleton_score {d N : ℕ} (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hN : 0 < N) (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (i : Fin N) : pgmScore ρ {i} = 1 / (N : ℝ) := by
  have h := centered_identity ρ hN hρ htr {i} (Finset.singleton_nonempty i)
  dsimp only at h
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one,
    div_one, one_smul] at h
  have hσ : ((1 / (N : ℂ)) • ρ i).PosSemidef := by
    apply (hρ i).smul
    apply Complex.nonneg_iff.mpr
    constructor
    · simp only [one_div, Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast]
      positivity
    · simp
  rw [(support_quarter_normalization _ hσ).2, sub_self] at h
  have hz : RHLinalg.frobSq (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
    simp [RHLinalg.frobSq]
  rw [hz] at h
  exact sub_eq_zero.mp h

/-- In one dimension every nonempty restricted PGM score is exactly 1/N. -/
theorem dimension_one_score {N : ℕ}
    (ρ : Fin N → Matrix (Fin 1) (Fin 1) ℂ) (hN : 0 < N)
    (htr : ∀ i, trace (ρ i) = 1) (B : Finset (Fin N)) (hB : B.Nonempty) :
    pgmScore ρ B = 1 / (N : ℝ) := by
  have hrho : ρ = fun _ => diagonal (fun _ : Fin 1 => (1 : ℂ)) := by
    funext i
    ext x y
    fin_cases x
    fin_cases y
    simpa [trace, Fin.sum_univ_one] using htr i
  rw [hrho]
  have hdiag := diagonal_score hN (fun (_ : Fin N) (_ : Fin 1) => 1)
    (by intro i x; norm_num) B
  norm_num only [Complex.ofReal_one] at hdiag
  rw [hdiag]
  have hcard : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  simp [Fin.sum_univ_one, hcard]

/-- For at most two labels the original comparison holds for every nonempty
label set, hence for every actual optimum's active set. -/
theorem at_most_two_labels {d N : ℕ}
    (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ) (hN : 0 < N) (hN2 : N ≤ 2)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (B : Finset (Fin N)) (hB : B.Nonempty) :
    ((B.card : ℝ) - 1) * (pgmScore ρ B - 1 / (N : ℝ)) ≤
      ((N : ℝ) - 1) * (pgmScore ρ Finset.univ - 1 / (N : ℝ)) := by
  by_cases hc : B.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    rw [singleton_score ρ hN hρ htr i, sub_self, mul_zero]
    exact mul_nonneg (by
      have hx : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      linarith)
      (sub_nonneg.mpr (random_guessing_le ρ hN hρ htr Finset.univ
        ⟨⟨0, hN⟩, Finset.mem_univ _⟩))
  · have hcard := Finset.card_le_univ B
    have hpos := hB.card_pos
    simp only [Fintype.card_fin] at hcard
    have heq : B.card = N := by omega
    have hfull : B = Finset.univ := Finset.eq_univ_of_card B (by simpa only [Fintype.card_fin] using heq)
    subst B
    simp

/-- A pure omitted Bloch vector inside the pure symmetric pair's dual ball has
no larger weak population. This is a limited geometric control only. -/
theorem pure_pair_population (z x y w : ℝ) (hz : 0 < z) (hz1 : z < 1)
    (hpure : x ^ 2 + y ^ 2 + w ^ 2 = 1)
    (hball : x ^ 2 + y ^ 2 + (w - z) ^ 2 ≤ 1 - z ^ 2) :
    z ≤ w ∧ (1 - w) / 2 ≤ (1 - z) / 2 ∧ 0 < (1 - z) / 2 := by
  have hw : z ≤ w := by nlinarith
  exact ⟨hw, by linarith, by linarith⟩

private theorem active_reindex_sum {N m : ℕ} {M : Type*} [AddCommMonoid M]
    (p : Fin N → Prop) [DecidablePred p] (e : Fin m ≃ {i // p i}) (f : Fin N → M) :
    (∑ j, f (e j).val) = ∑ i ∈ Finset.univ.filter p, f i := by
  apply Finset.sum_bij (fun j _ => (e j).val)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e j).property⟩
  · intro j hj k hk h
    apply e.injective
    exact Subtype.ext h
  · intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    refine ⟨e.symm ⟨i, hp⟩, Finset.mem_univ _, ?_⟩
    simp
  · intro j hj
    rfl

private theorem success_factor {d N : ℕ}
    (ρ E : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    success ρ E = (1 / (N : ℝ)) * ∑ i, (trace (ρ i * E i)).re := by
  simp [success, Matrix.smul_mul, trace_smul, Complex.mul_re, Finset.mul_sum]

/-- Restricting an actual optimum to its actual active effects yields an optimum
of the normalized active ensemble. The same actual matrices are retained;
only the uniform prior changes from 1/N to 1/m. -/
theorem active_reduction {k N m : ℕ}
    (ρ E : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hN : 0 < N) (hm : 0 < m)
    (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, trace (ρ i) = 1)
    (hE : finitePOVM E)
    (hopt : ∀ F, finitePOVM F → success ρ F ≤ success ρ E)
    (e : Fin m ≃ {i // E i ≠ 0}) :
    let μ := fun j => ρ (e j).val
    let F := fun j => E (e j).val
    (∀ j, (μ j).PosSemidef ∧ trace (μ j) = 1) ∧
    finitePOVM F ∧ (∀ j, F j ≠ 0) ∧
    success ρ E = (m : ℝ) / N * success μ F ∧
    (∀ G, finitePOVM G → success μ G ≤ success μ F) := by
  let A := Finset.univ.filter (fun i => E i ≠ 0)
  let μ := fun j : Fin m => ρ (e j).val
  let F := fun j : Fin m => E (e j).val
  have hz (i : Fin N) (hi : i ∉ A) : E i = 0 := by simpa [A] using hi
  have sum_active {M : Type} [AddCommMonoid M] (f : Fin N → M)
      (hf : ∀ i, i ∉ A → f i = 0) : (∑ i ∈ A, f i) = ∑ i, f i := by
    exact Finset.sum_subset (Finset.subset_univ A) (fun i _ hi => hf i hi)
  have hF : finitePOVM F := by
    refine ⟨fun j => hE.1 _, ?_⟩
    change (∑ j, E (e j).val) = 1
    rw [active_reindex_sum (fun i => E i ≠ 0) e E]
    exact (sum_active E hz).trans hE.2
  have hscale (G : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
      (hG : ∀ i, i ∉ A → G i = 0) :
      success ρ G = (m : ℝ) / N * success μ (fun j => G (e j).val) := by
    rw [success_factor, success_factor]
    change (1 / (N : ℝ)) * ∑ i, (trace (ρ i * G i)).re =
      (m : ℝ) / N * ((1 / (m : ℝ)) * ∑ j, (trace (ρ (e j).val * G (e j).val)).re)
    rw [active_reindex_sum (fun i => E i ≠ 0) e (fun i => (trace (ρ i * G i)).re)]
    rw [sum_active _ (by intro i hi; simp [hG i hi])]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  refine ⟨fun j => ⟨hρ _, htr _⟩, hF, fun j => (e j).property, hscale E hz, ?_⟩
  intro G hG
  let H : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
    fun i => if hi : E i ≠ 0 then G (e.symm ⟨i, hi⟩) else 0
  have hHF (j : Fin m) : H (e j).val = G j := by simp [H, (e j).property]
  have hHz (i : Fin N) (hi : i ∉ A) : H i = 0 := by simp [H, hz i hi]
  have hH : finitePOVM H := by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : E i ≠ 0
      · simpa only [H, dif_pos hi] using hG.1 (e.symm ⟨i, hi⟩)
      · simpa only [H, dif_neg hi] using (Matrix.PosSemidef.zero :
          (0 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).PosSemidef)
    · calc
        (∑ i, H i) = ∑ i ∈ A, H i := (sum_active H hHz).symm
        _ = ∑ j, H (e j).val := (active_reindex_sum (fun i => E i ≠ 0) e H).symm
        _ = ∑ j, G j := by simp only [hHF]
        _ = 1 := hG.2
  have hle := hopt H hH
  rw [hscale H hHz, hscale E hz] at hle
  have he : (fun j => H (e j).val) = G := funext hHF
  rw [he] at hle
  exact (mul_le_mul_iff_right₀ (div_pos (by exact_mod_cast hm) (by exact_mod_cast hN))).mp hle


/-- The limited pure-pair control stated for an actual pure density matrix and
an actual positive semidefinite discrimination slack. This does not prove the
all-pure PGM comparison. -/
theorem pure_density_control (z : ℝ) (hz : 0 < z) (hz1 : z < 1)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (hpure : ρ * ρ = ρ)
    (hslack : (((1 / 6 : ℂ) •
      (((1 + Real.sqrt (1 - z ^ 2) : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (z : ℂ) • D5.S3.Quantum.FiniteDimensional.qubitZ)) - (1 / 3 : ℂ) • ρ).PosSemidef) :
    (ρ 1 1).re ≤ (1 - z) / 2 := by
  let r := D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch ρ
  let g : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![0, 0, z]
  let R := Real.sqrt (1 - z ^ 2)
  have hgeom := D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_geometry_of_isHermitian
    ρ hρ.isHermitian
  have hr : ‖r‖ = 1 := hgeom.2 htr hpure
  have hform : ρ = D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix 1 r := by
    simpa [htr, r] using hgeom.1
  have hs : (D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix R (g - r)).PosSemidef := by
    have h := hslack.smul (show (0 : ℂ) ≤ 3 by norm_num)
    convert h using 1
    rw [hform]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
        D5.S3.Quantum.FiniteDimensional.qubitZ, g, R, Matrix.one_apply] <;> ring
  have hn := D5.S3.Quantum.Information.ActualPureQubitCostInfimum.norm_bloch_le_trace_of_posSemidef _ hs
  rw [D5.S3.Quantum.Information.ActualPureQubitCostInfimum.bloch_blochMatrix,
    D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix_trace,
    Complex.ofReal_re] at hn
  have hsq : ‖g - r‖ ^ 2 ≤ R ^ 2 := by
    nlinarith [norm_nonneg (g - r), Real.sqrt_nonneg (1 - z ^ 2)]
  have hp : 0 < 1 - z ^ 2 := by nlinarith
  have hR : R ^ 2 = 1 - z ^ 2 := Real.sq_sqrt hp.le
  have hpure' : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 := by
    have he := EuclideanSpace.real_norm_sq_eq r
    rw [hr] at he
    simpa [Fin.sum_univ_three] using he.symm
  have hball : r 0 ^ 2 + r 1 ^ 2 + (r 2 - z) ^ 2 ≤ 1 - z ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hsq
    simp [g] at hsq
    nlinarith
  have hw := (pure_pair_population z (r 0) (r 1) (r 2) hz hz1 hpure' hball).2.1
  have ht := congrArg Complex.re htr
  have hr2 : r 2 = (ρ 0 0).re - (ρ 1 1).re := rfl
  simp only [trace, Fin.sum_univ_two, Complex.add_re, Matrix.diag, Complex.one_re] at ht
  linarith

end D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSupportIdentity

/- Escape-audit delivery: four registrations for centered_identity, random_guessing_le,
states_posDef and pair_classification have validated evidence. Remaining
theorem-specific bindings are unfinished; the concrete gaps are disclosed at
https://github.com/the-omega-institute/trureturing/issues/27499.
The issue is not proof, validation or independent approval. -/
