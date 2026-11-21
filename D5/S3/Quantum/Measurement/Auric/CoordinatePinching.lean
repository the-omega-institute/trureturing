/- GID: D5/S3/Quantum/Measurement/Auric/CoordinatePinching
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/CoordinatePinching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact flat-phase decoding after a first coordinate PVM with arbitrary flagged projective continuation. -/

import D5.S3.Observer.Conditioning
import D5.S3.Quantum.PureState.JointRecordDecoding
import D5.S3.Quantum.Measurement.Auric.ProjectiveTree

/-! Exact phase-record discrimination after the first projective observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.Auric.CoordinatePinching

noncomputable section

open Matrix
open D5.S3.Observer.Conditioning (unreadState unreadState_idempotent)
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Subentropy.GuessingProbability
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open JointRecordDecoding

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem pvm_kraus_normalized {k : ℕ} (p : CompletePVM ι k) :
    (∑ b, (p.proj b)ᴴ * p.proj b) = 1 := by
  simp_rw [(p.hermitian _).eq, p.idempotent]
  exact p.complete

/-- The nonselective action is a finite CPTP channel. -/
def pinchingChannel {k : ℕ} (p : CompletePVM ι k) : QuantumChannel ι ι :=
  (finite_kraus_quantum_channel p.proj (pvm_kraus_normalized p)).choose

theorem pinchingChannel_apply {k : ℕ} (p : CompletePVM ι k) (X : Matrix ι ι ℂ) :
    CStarMatrix.ofMatrix.symm ((pinchingChannel p).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) = unreadState p.proj X := by
  unfold pinchingChannel unreadState
  rw [(finite_kraus_quantum_channel p.proj (pvm_kraus_normalized p)).choose_spec X]
  simp_rw [(p.hermitian _).eq]

/-- The diagonal projectors onto the fibers of a finite coordinate partition. -/
def coordinatePVM {k : ℕ} (c : ι → Fin k) : CompletePVM ι k where
  proj b := diagonal fun i => if c i = b then 1 else 0
  hermitian b := by
    change (diagonal _)ᴴ = diagonal _
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : c i = b <;> simp [h]
  idempotent b := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : c i = b <;> simp [h]
  orthogonal b d hbd := by
    rw [diagonal_mul_diagonal, ← diagonal_zero]
    congr 1
    funext i
    by_cases h : c i = b
    · simp [h, hbd]
    · simp [h]
  complete := by
    classical
    ext i l
    by_cases h : i = l
    · subst l
      simp [Matrix.sum_apply]
    · simp [Matrix.sum_apply, diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- The coordinate profile restricted to one fiber, with zeros elsewhere. -/
def maskedProfile {k : ℕ} (c : ι → Fin k) (t : ι → ℝ) (b : Fin k) (i : ι) : ℝ :=
  if c i = b then t i else 0

def blockAmplitude {k : ℕ} (c : ι → Fin k) (t : ι → ℝ) (b : Fin k) : ℝ :=
  ∑ i, maskedProfile c t b i

def pinchedOptimum {k : ℕ} (c : ι → Fin k) (t : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ b, (blockAmplitude c t b) ^ 2

omit [Fintype ι] [DecidableEq ι] in
private theorem maskedProfile_nonneg {k : ℕ} (c : ι → Fin k) (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (b : Fin k) (i : ι) :
    0 ≤ maskedProfile c t b i := by
  by_cases h : c i = b <;> simp [maskedProfile, h, ht]

omit [DecidableEq ι] in
private theorem sum_blockAmplitude {k : ℕ} (c : ι → Fin k) (t : ι → ℝ) :
    (∑ b, blockAmplitude c t b) = ∑ i, t i := by
  unfold blockAmplitude maskedProfile
  rw [Finset.sum_comm]
  simp

private theorem compress_phaseDensity {k : ℕ} (c : ι → Fin k) (b : Fin k)
    (u : ι → ι → ℂ) (t : ι → ℝ) (j : ι) :
    (coordinatePVM c).proj b * rankOneDensity (phaseVector u t j) *
      (coordinatePVM c).proj b = rankOneDensity (phaseVector u (maskedProfile c t b) j) := by
  ext i l
  by_cases hi : c i = b <;> by_cases hl : c l = b <;>
    simp [coordinatePVM, mul_diagonal, diagonal_mul, rankOneDensity, vecMulVec_apply, Pi.star_apply, phaseVector,
      maskedProfile, hi, hl]

omit [DecidableEq ι] in
/-- Trace against a phase effect for an unnormalized phase vector.
This calculation also applies to a zero vector. -/
private theorem trace_phaseEffect_rankOne (u : ι → ι → ℂ) (s : ι → ℝ)
    (j : ι) (hu : ∀ i, ‖u j i‖ = 1) :
    (trace (phaseEffect u j * rankOneDensity (phaseVector u s j))).re =
      (Fintype.card ι : ℝ)⁻¹ * (∑ i, s i) ^ 2 := by
  have hunit (i : ι) : star (u j i) * u j i = 1 := by
    have h : star (u j i) * u j i = (Complex.normSq (u j i) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    rw [h, Complex.normSq_eq_norm_sq, hu]
    norm_num
  let a : ℝ := (Real.sqrt (Fintype.card ι))⁻¹
  have hdot : star (phaseBasis u j) ⬝ᵥ phaseVector u s j = (↑(a * ∑ i, s i) : ℂ) := by
    simp only [phaseBasis, phaseVector, dotProduct, Pi.star_apply, star_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_sum,
      Finset.mul_sum, a]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (star (u j i) * _) * (_ * u j i) = _
    linear_combination ((a : ℂ) * (s i : ℂ)) * hunit i
  have hconj : star (star (phaseBasis u j) ⬝ᵥ phaseVector u s j) =
      star (phaseVector u s j) ⬝ᵥ phaseBasis u j := by
    simp [dotProduct, Pi.star_apply, mul_comm]
  have ha : a ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    dsimp [a]
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [phaseEffect, rankOneDensity, rankOneDensity, vecMulVec_mul_vecMulVec,
    trace_vecMulVec, dotProduct_smul, dotProduct_comm (phaseBasis u j),
    ← hconj, hdot, Complex.star_def, Complex.conj_ofReal]
  rw [smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re, ← pow_two, mul_pow, ha]

/-- The actual density ensemble after the nonselective first observation. -/
def pinchedPhaseStates {k : ℕ} (c : ι → Fin k) (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (hnorm : ∑ i, t i ^ 2 = 1) (j : ι) : DensityState ι :=
  (pinchingChannel (coordinatePVM c)).mapState
    (pureState (phaseVector u t j) (phaseVector_norm u t hu hnorm j))

theorem pinchedPhaseStates_matrix {k : ℕ}
    (c : ι → Fin k) (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (hnorm : ∑ i, t i ^ 2 = 1) (j : ι) :
    CStarMatrix.ofMatrix.symm (pinchedPhaseStates c u t hu hnorm j).1 =
      ∑ b, rankOneDensity (phaseVector u (maskedProfile c t b) j) := by
  change CStarMatrix.ofMatrix.symm ((pinchingChannel (coordinatePVM c)).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (rankOneDensity (phaseVector u t j)))) = _
  rw [pinchingChannel_apply]
  exact Finset.sum_congr rfl fun b _ => compress_phaseDensity c b u t j

omit [DecidableEq ι] in
private theorem uniformPrior_sum [Nonempty ι] :
    (∑ j : ι, uniformPrior ι j) = 1 := by
  simp [uniformPrior]

variable {k : ℕ} (c : ι → Fin k) (u : ι → ι → ℂ) (t : ι → ℝ)
  (hu : ∀ j i, ‖u j i‖ = 1) (hnorm : ∑ i, t i ^ 2 = 1)

/-- The full phase POVM attains the pinched score. -/
theorem success_phaseEffect_pinched [Nonempty ι] :
    successProbability (uniformPrior ι) (pinchedPhaseStates c u t hu hnorm) (phaseEffect u) =
      pinchedOptimum c t := by
  unfold successProbability
  simp only [pinchedPhaseStates_matrix, Matrix.mul_sum, trace_sum, Complex.re_sum]
  simp_rw [fun j b => trace_phaseEffect_rankOne u (maskedProfile c t b) j (hu j)]
  have h :
      (∑ b, (Fintype.card ι : ℝ)⁻¹ * (blockAmplitude c t b) ^ 2) = pinchedOptimum c t := by
    rw [← Finset.mul_sum]
    rfl
  change (∑ j, uniformPrior ι j * ∑ b, (Fintype.card ι : ℝ)⁻¹ *
    (blockAmplitude c t b) ^ 2) = _
  rw [h, ← Finset.sum_mul, uniformPrior_sum, one_mul]

/-- The sum of the block diagonal dual certificates gives the exact maximum over all POVMs. -/
theorem isGreatest_pinchedPhase [Nonempty ι] (ht : ∀ i, 0 ≤ t i)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) :
    IsGreatest (successProbabilitySet (uniformPrior ι) (pinchedPhaseStates c u t hu hnorm))
      (pinchedOptimum c t) := by
  let D (b : Fin k) : Matrix ι ι ℂ :=
    diagonal fun i => ((blockAmplitude c t b * maskedProfile c t b i : ℝ) : ℂ)
  refine ⟨⟨phaseEffect u, phaseEffect_posSemidef u, sum_phaseEffect u horth,
    (success_phaseEffect_pinched c u t hu hnorm).symm⟩, ?_⟩
  rintro _ ⟨M, hM, hs, rfl⟩
  have upper (j : ι) (b : Fin k) :
      (trace (M j * rankOneDensity (phaseVector u (maskedProfile c t b) j))).re ≤
        (trace (M j * D b)).re := by
    have h := RHLinalg.trace_mul_nonneg_of_posSemidef (hM j)
      (diagonal_sub_rankOne_posSemidef (maskedProfile c t b)
        (maskedProfile_nonneg c t ht b) (u j) (hu j))
    change 0 ≤ (trace (M j * (D b - rankOneDensity
      (phaseVector u (maskedProfile c t b) j)))).re at h
    rwa [Matrix.mul_sub, trace_sub, Complex.sub_re, sub_nonneg] at h
  have trace_dual (b : Fin k) : (trace (D b)).re = (blockAmplitude c t b) ^ 2 := by
    simp [D, trace_diagonal, Complex.re_sum, ← Finset.mul_sum, blockAmplitude, pow_two]
  unfold successProbability
  simp only [pinchedPhaseStates_matrix, Matrix.mul_sum, trace_sum, Complex.re_sum]
  calc
    _ ≤ ∑ j, uniformPrior ι j * ∑ b, (trace (M j * D b)).re := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => upper j b) (by
          unfold uniformPrior
          positivity)
    _ = pinchedOptimum c t := by
      simp only [uniformPrior, ← Finset.mul_sum]
      rw [Finset.sum_comm (f := fun j b => (trace (M j * D b)).re)]
      simp_rw [← Complex.re_sum, ← trace_sum, ← Matrix.sum_mul, hs, one_mul]
      simp [pinchedOptimum, trace_dual]

theorem pGuess_pinchedPhase [Nonempty ι] (ht : ∀ i, 0 ≤ t i)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) :
    pGuess (uniformPrior ι) (pinchedPhaseStates c u t hu hnorm) = pinchedOptimum c t :=
  (isGreatest_pinchedPhase c u t hu hnorm ht horth).csSup_eq

/-- The trace adjoint of pinching is pinching itself. -/
private theorem trace_pinching {k : ℕ} (p : CompletePVM ι k) (M X : Matrix ι ι ℂ) :
    trace (unreadState p.proj M * X) = trace (M * unreadState p.proj X) := by
  simp only [unreadState, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm (p.proj b) (M * (p.proj b * X))]
  simp only [Matrix.mul_assoc]

private theorem pinching_povm {X : Type*} [Fintype X] {k : ℕ} (p : CompletePVM ι k)
    (M : X → Matrix ι ι ℂ) (hM : ∀ j, (M j).PosSemidef) (hs : ∑ j, M j = 1) :
    (∀ j, (unreadState p.proj (M j)).PosSemidef) ∧ ∑ j, unreadState p.proj (M j) = 1 := by
  constructor
  · intro j
    apply Matrix.posSemidef_sum
    intro b _
    simpa only [(p.hermitian b).eq] using (hM j).mul_mul_conjTranspose_same (p.proj b)
  · unfold unreadState
    rw [Finset.sum_comm]
    simp_rw [← Matrix.sum_mul, ← Matrix.mul_sum, hs, Matrix.mul_one, p.idempotent]
    exact p.complete

private theorem pinching_mul_proj {k : ℕ} (p : CompletePVM ι k) (X : Matrix ι ι ℂ)
    (b : Fin k) : unreadState p.proj X * p.proj b = p.proj b * X * p.proj b := by
  unfold unreadState
  simp only [Matrix.sum_mul, Matrix.mul_assoc]
  rw [Finset.sum_eq_single b]
  · rw [p.idempotent]
  · intro d _ hdb
    rw [p.orthogonal d b hdb, Matrix.mul_zero, Matrix.mul_zero]
  · simp

/-- The full phase measurement and its block-compressed POVM have the same score on the
pinched ensemble. Compression preserves both positivity and completeness. -/
theorem compressed_phaseEffect_attains [Nonempty ι]
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) :
    (∀ j, (unreadState (coordinatePVM c).proj (phaseEffect u j)).PosSemidef) ∧
    (∑ j, unreadState (coordinatePVM c).proj (phaseEffect u j)) = 1 ∧
    successProbability (uniformPrior ι) (pinchedPhaseStates c u t hu hnorm)
      (fun j => unreadState (coordinatePVM c).proj (phaseEffect u j)) = pinchedOptimum c t := by
  obtain ⟨hpos, hsum⟩ := pinching_povm (coordinatePVM c) (phaseEffect u)
    (phaseEffect_posSemidef u) (sum_phaseEffect u horth)
  refine ⟨hpos, hsum, ?_⟩
  rw [← success_phaseEffect_pinched c u t hu hnorm]
  unfold successProbability
  refine Finset.sum_congr rfl fun j _ => ?_
  let X := rankOneDensity (phaseVector u t j)
  let Y := CStarMatrix.ofMatrix.symm
    ((pinchingChannel (coordinatePVM c)).toCompletelyPositiveMap (CStarMatrix.ofMatrix X))
  change _ * (trace (unreadState (coordinatePVM c).proj (phaseEffect u j) * Y)).re =
    _ * (trace (phaseEffect u j * Y)).re
  dsimp only [Y]
  rw [pinchingChannel_apply, trace_pinching]
  rw [unreadState_idempotent
    ⟨fun b => ((coordinatePVM c).hermitian b).eq, (coordinatePVM c).idempotent,
      (coordinatePVM c).orthogonal, (coordinatePVM c).complete⟩]

/-- Exactly the cross-block terms of the coherent squared amplitude are lost.
The sum on the right runs over each unordered pair once. -/
theorem phase_decoding_loss [Nonempty ι] (ht : ∀ i, 0 ≤ t i)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) :
    pGuess (uniformPrior ι) (fun j => pureState (phaseVector u t j)
      (phaseVector_norm u t hu hnorm j)) -
      pGuess (uniformPrior ι) (pinchedPhaseStates c u t hu hnorm) =
    2 * (Fintype.card ι : ℝ)⁻¹ *
      ∑ b, ∑ d, if b < d then blockAmplitude c t b * blockAmplitude c t d else 0 := by
  rw [pGuess_phase u t hu horth ht hnorm, pGuess_pinchedPhase c u t hu hnorm ht horth,
    ← sum_blockAmplitude c t]
  let a := blockAmplitude c t
  have split (b d : Fin k) : a b * a d =
      (if b = d then a b ^ 2 else 0) +
      (if b < d then a b * a d else 0) +
      (if d < b then a d * a b else 0) := by
    rcases lt_trichotomy b d with h | h | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · subst d
      simp [pow_two]
    · simp [h, h.ne.symm, not_lt_of_ge h.le, mul_comm]
  have expand : (∑ b, a b) ^ 2 = (∑ b, a b ^ 2) +
      2 * ∑ b, ∑ d, if b < d then a b * a d else 0 := by
    rw [pow_two, Fintype.sum_mul_sum]
    calc
      _ = ∑ b, ∑ d, ((if b = d then a b ^ 2 else 0) +
          (if b < d then a b * a d else 0) +
          (if d < b then a d * a b else 0)) := by
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => split b d
      _ = _ := by
        simp only [Finset.sum_add_distrib, Fintype.sum_ite_eq]
        rw [Finset.sum_comm (f := fun b d => if d < b then a d * a b else 0)]
        ring
  change (Fintype.card ι : ℝ)⁻¹ * (∑ b, a b) ^ 2 -
    (Fintype.card ι : ℝ)⁻¹ * (∑ b, a b ^ 2) = _
  rw [expand]
  ring

/-- Coherent decoding and decoding after the first coordinate PVM have equal optima
exactly when the entire nonzero profile lies in one block. -/
theorem phase_decoding_no_loss_iff [Nonempty ι] (ht : ∀ i, 0 ≤ t i)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) :
    pGuess (uniformPrior ι) (fun j => pureState (phaseVector u t j)
      (phaseVector_norm u t hu hnorm j)) =
      pGuess (uniformPrior ι) (pinchedPhaseStates c u t hu hnorm) ↔
      ∃ b, ∀ i, c i ≠ b → t i = 0 := by
  let a := blockAmplitude c t
  have ha (b : Fin k) : 0 ≤ a b :=
    Finset.sum_nonneg fun i _ => maskedProfile_nonneg c t ht b i
  have hterm (b d : Fin k) : 0 ≤ if b < d then a b * a d else 0 := by
    split
    · exact mul_nonneg (ha b) (ha d)
    · exact le_rfl
  have hcard : 0 < 2 * (Fintype.card ι : ℝ)⁻¹ := by positivity
  rw [← sub_eq_zero, phase_decoding_loss c u t hu hnorm ht horth, mul_eq_zero,
    or_iff_right hcard.ne']
  change (∑ b, ∑ d, if b < d then a b * a d else 0) = 0 ↔ _
  simp only [Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
    Finset.sum_nonneg (fun d _ => hterm b d)), Finset.sum_eq_zero_iff_of_nonneg
    (fun d _ => hterm _ d), Finset.mem_univ, true_implies]
  constructor
  · intro h
    have hex : ∃ i, t i ≠ 0 := by
      by_contra! hz
      simp [hz] at hnorm
    obtain ⟨i, hi⟩ := hex
    have hle (l : ι) : t l ≤ a (c l) := by
      have hs := Finset.single_le_sum
        (f := maskedProfile c t (c l))
        (fun j _ => maskedProfile_nonneg c t ht (c l) j) (Finset.mem_univ l)
      simpa [a, blockAmplitude, maskedProfile] using hs
    have hi' : 0 < a (c i) := (lt_of_le_of_ne (ht i) hi.symm).trans_le (hle i)
    refine ⟨c i, fun l hl => le_antisymm ((hle l).trans_eq ?_) (ht l)⟩
    rcases lt_or_gt_of_ne hl with hlt | hgt
    · exact (mul_eq_zero.mp (by simpa only [ite_eq_left hlt] using h (c l) (c i))).resolve_right hi'.ne'
    · exact (mul_eq_zero.mp (by simpa only [ite_eq_left hgt] using h (c i) (c l))).resolve_left hi'.ne'
  · rintro ⟨b, hb⟩ d e
    have hz (f : Fin k) (hf : f ≠ b) : a f = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : c i = f
      · simp [maskedProfile, h, hb i (h.trans_ne hf)]
      · simp [maskedProfile, h]
    by_cases hlt : d < e
    · rw [ite_eq_left hlt]
      by_cases hd : d = b
      · exact mul_eq_zero.mpr (Or.inr (hz e (hd ▸ hlt.ne.symm)))
      · exact mul_eq_zero.mpr (Or.inl (hz d hd))
    · exact ite_eq_right hlt

section Terminal

variable {κ : Type*} [Fintype κ]

omit [DecidableEq ι] in
private theorem flagKraus_mul (f : Fin 2) (K Q : Matrix ι ι ℂ) :
    flagKraus f K * Q = flagKraus f (K * Q) := by
  ext ⟨g, i⟩ j
  by_cases h : g = f <;> simp [Matrix.mul_apply, flagKraus, h]

/-- Every actual terminal Kraus has only its own first-projector right support.
The terminal channel therefore factors through the root pinching on all matrices. -/
theorem flaggedChannel_pinching {k : ℕ} (p : CompletePVM ι k)
    (descend : Fin k → Protocol ι) (X : Matrix ι ι ℂ) :
    let q : Protocol ι := .branch 1 k p descend
    (flaggedChannel q).toCompletelyPositiveMap (CStarMatrix.ofMatrix (unreadState p.proj X)) =
      (flaggedChannel q).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) := by
  let q : Protocol ι := .branch 1 k p descend
  change (flaggedChannel q).toCompletelyPositiveMap _ = (flaggedChannel q).toCompletelyPositiveMap _
  apply CStarMatrix.ofMatrix.symm.injective
  rw [flaggedChannel_apply, flaggedChannel_apply]
  refine Finset.sum_congr rfl ?_
  rintro ⟨b, h⟩ _
  let K := flagKraus (flag q ⟨b, h⟩) (kraus q ⟨b, h⟩)
  have hK : K * p.proj b = K := by
    have support := terminal_has_group_right_support 1 p descend {b} b
      (Finset.mem_singleton_self b) h
    simp [firstGroupEffect] at support
    dsimp [K]
    rw [flagKraus_mul]
    exact congrArg (flagKraus (flag q ⟨b, h⟩)) support
  have hKt : p.proj b * Kᴴ = Kᴴ := by
    simpa only [conjTranspose_mul, (p.hermitian b).eq] using congrArg conjTranspose hK
  change K * unreadState p.proj X * Kᴴ = K * X * Kᴴ
  calc
    _ = K * (unreadState p.proj X * p.proj b) * Kᴴ := by
      simp only [Matrix.mul_assoc, hKt]
    _ = K * (p.proj b * X * p.proj b) * Kᴴ := by rw [pinching_mul_proj]
    _ = (K * p.proj b) * X * (p.proj b * Kᴴ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hK, hKt]

/-- The ordinary trace-adjoint pullback for the actual flagged terminal channel. -/
private def pullFlaggedEffect (q : Protocol ι) (M : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) :
    Matrix ι ι ℂ :=
  ∑ h : Terminal q, (flagKraus (flag q h) (kraus q h))ᴴ * M * flagKraus (flag q h) (kraus q h)

private theorem pullFlaggedEffect_povm (q : Protocol ι)
    (M : κ → Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hM : ∀ j, (M j).PosSemidef)
    (hs : ∑ j, M j = 1) :
    (∀ j, (pullFlaggedEffect q (M j)).PosSemidef) ∧ ∑ j, pullFlaggedEffect q (M j) = 1 := by
  constructor
  · intro j
    exact Matrix.posSemidef_sum _ fun h _ => (hM j).conjTranspose_mul_mul_same _
  · unfold pullFlaggedEffect
    rw [Finset.sum_comm]
    simp_rw [← Matrix.sum_mul, ← Matrix.mul_sum, hs, Matrix.mul_one]
    exact flagged_normalized q

private theorem trace_pullFlaggedEffect (q : Protocol ι) (X : Matrix ι ι ℂ)
    (M : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) :
    trace (pullFlaggedEffect q M * X) = trace (M *
      CStarMatrix.ofMatrix.symm ((flaggedChannel q).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix X))) := by
  rw [flaggedChannel_apply]
  simp only [pullFlaggedEffect, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  let K := flagKraus (flag q h) (kraus q h)
  change trace ((Kᴴ * M * K) * X) = trace (M * (K * X * Kᴴ))
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm Kᴴ (M * (K * X))]
  simp only [Matrix.mul_assoc]

private theorem success_pullFlaggedEffect (q : Protocol ι) (p : κ → ℝ)
    (ρ : κ → DensityState ι) (M : κ → Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) :
    successProbability p (fun j => (flaggedChannel q).mapState (ρ j)) M =
      successProbability p ρ (fun j => pullFlaggedEffect q (M j)) := by
  unfold successProbability
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [trace_pullFlaggedEffect, Equiv.apply_symm_apply]
  rfl

private theorem flagged_mapState_pinching {k : ℕ} (p : CompletePVM ι k)
    (descend : Fin k → Protocol ι) (ρ : DensityState ι) :
    let q : Protocol ι := .branch 1 k p descend
    (flaggedChannel q).mapState ((pinchingChannel p).mapState ρ) = (flaggedChannel q).mapState ρ := by
  let q : Protocol ι := .branch 1 k p descend
  apply Subtype.ext
  simp only [QuantumChannel.mapState_value]
  let X := CStarMatrix.ofMatrix.symm ρ.1
  have h := pinchingChannel_apply p X
  apply_fun CStarMatrix.ofMatrix at h
  simp only [Equiv.apply_symm_apply] at h
  change (flaggedChannel q).toCompletelyPositiveMap
    ((pinchingChannel p).toCompletelyPositiveMap ρ.1) = (flaggedChannel q).toCompletelyPositiveMap ρ.1
  calc
    _ = (flaggedChannel q).toCompletelyPositiveMap (CStarMatrix.ofMatrix (unreadState p.proj X)) := by
      rw [← h]
      simp [X]
    _ = _ := by
      rw [flaggedChannel_pinching p descend X]
      simp [X, q]

end Terminal

/-- AURIC output states with the specified first coordinate PVM and arbitrary continuation. -/
def flaggedPhaseStates (descend : Fin k → Protocol ι) (j : ι) : DensityState (Fin 2 × ι) :=
  (flaggedChannel (.branch 1 k (coordinatePVM c) descend)).mapState
    (pureState (phaseVector u t j) (phaseVector_norm u t hu hnorm j))

/-- Any joint flag/residual POVM after any actual continuation has score at most
the exact root-pinched optimum. -/
theorem flagged_phase_success_le [Nonempty ι] (ht : ∀ i, 0 ≤ t i)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0)
    (descend : Fin k → Protocol ι)
    (M : ι → Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hM : ∀ j, (M j).PosSemidef)
    (hs : ∑ j, M j = 1) :
    successProbability (uniformPrior ι) (flaggedPhaseStates c u t hu hnorm descend) M ≤
      pinchedOptimum c t := by
  let q : Protocol ι := .branch 1 k (coordinatePVM c) descend
  obtain ⟨hpos, hsum⟩ := pullFlaggedEffect_povm q M hM hs
  have hstates : flaggedPhaseStates c u t hu hnorm descend =
      fun j => (flaggedChannel q).mapState (pinchedPhaseStates c u t hu hnorm j) := by
    funext j
    exact (flagged_mapState_pinching (coordinatePVM c) descend _).symm
  rw [hstates, success_pullFlaggedEffect]
  exact (isGreatest_pinchedPhase c u t hu hnorm ht horth).2 ⟨_, hpos, hsum, rfl⟩

/-- Apply the same residual effect at each flag. -/
def ignoreFlag (A : Matrix ι ι ℂ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  fun x y => if x.1 = y.1 then A x.2 y.2 else 0

private theorem flagKraus_one_mul_adjoint_apply (f : Fin 2) (A : Matrix ι ι ℂ)
    (x y : Fin 2 × ι) :
    (flagKraus f A * (flagKraus f (1 : Matrix ι ι ℂ))ᴴ) x y =
      if x.1 = f ∧ y.1 = f then A x.2 y.2 else 0 := by
  by_cases hx : x.1 = f <;> by_cases hy : y.1 = f <;>
    simp [Matrix.mul_apply, flagKraus, Matrix.conjTranspose_apply, hx, hy, Matrix.one_apply,
      eq_comm]

private theorem ignoreFlag_posSemidef (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (ignoreFlag A).PosSemidef := by
  have h : ignoreFlag A =
      ∑ f, flagKraus f A * (flagKraus f (1 : Matrix ι ι ℂ))ᴴ := by
    ext x y
    simp only [Matrix.sum_apply, flagKraus_one_mul_adjoint_apply, ignoreFlag]
    by_cases hxy : x.1 = y.1
    · simp [hxy]
    · have hf (f : Fin 2) : ¬ (x.1 = f ∧ y.1 = f) :=
        fun ⟨hx, hy⟩ => hxy (hx.trans hy.symm)
      simp [hxy, hf]
  rw [h]
  apply Matrix.posSemidef_sum
  intro f _
  simpa only [flagKraus_mul, Matrix.one_mul] using
    hA.mul_mul_conjTranspose_same (flagKraus f (1 : Matrix ι ι ℂ))

omit [Fintype ι] in
private theorem sum_ignoreFlag {X : Type*} [Fintype X]
    (M : X → Matrix ι ι ℂ) (h : ∑ j, M j = 1) :
    ∑ j, ignoreFlag (M j) = 1 := by
  ext x y
  by_cases hxy : x.1 = y.1
  · simpa [Matrix.sum_apply, ignoreFlag, hxy, Matrix.one_apply, Prod.ext_iff] using
      congrArg (fun A : Matrix ι ι ℂ => A x.2 y.2) h
  · simp [Matrix.sum_apply, ignoreFlag, hxy, Prod.ext_iff]

omit [DecidableEq ι] in
private theorem ignoreFlag_mul_flagKraus (A K : Matrix ι ι ℂ) (f : Fin 2) :
    ignoreFlag A * flagKraus f K = flagKraus f (A * K) := by
  ext x j
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, ignoreFlag, flagKraus]
  rw [Finset.sum_eq_single x.1]
  · by_cases h : x.1 = f <;> simp [h]
  · intro g _ hg
    simp [Ne.symm hg]
  · simp

omit [DecidableEq ι] in
private theorem pull_ignoreFlag (f : Fin 2) (K A : Matrix ι ι ℂ) :
    (flagKraus f K)ᴴ * ignoreFlag A * flagKraus f K = Kᴴ * A * K := by
  rw [Matrix.mul_assoc, ignoreFlag_mul_flagKraus, Matrix.mul_assoc Kᴴ A K]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, flagKraus,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single f]
  · simp
  · intro g _ hg
    simp [hg]
  · simp

private theorem pull_identityLeaves (p : CompletePVM ι k) (f : Fin k → Fin 2)
    (A : Matrix ι ι ℂ) :
    pullFlaggedEffect (.branch 1 k p (fun b => .leaf (f b) 1)) (ignoreFlag A) =
      unreadState p.proj A := by
  unfold pullFlaggedEffect
  change ∑ h : Sigma (fun _ : Fin k => Unit),
    (flagKraus (f h.1) ((1 : Matrix ι ι ℂ) * (p.proj h.1 * 1)))ᴴ *
      ignoreFlag A * flagKraus (f h.1) (1 * (p.proj h.1 * 1)) = _
  rw [Fintype.sum_sigma]
  simp [pull_ignoreFlag, fun b => (p.hermitian b).eq, unreadState]

/-- Identity continuations and the full phase measurement on the residual
register attain the bound for any deterministic terminal flag assignment. -/
theorem flagged_identity_attains [Nonempty ι]
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) (f : Fin k → Fin 2) :
    (∀ j, (ignoreFlag (phaseEffect u j)).PosSemidef) ∧
    (∑ j, ignoreFlag (phaseEffect u j)) = 1 ∧
    successProbability (uniformPrior ι)
      (flaggedPhaseStates c u t hu hnorm (fun b => .leaf (f b) 1))
      (fun j => ignoreFlag (phaseEffect u j)) = pinchedOptimum c t := by
  refine ⟨fun j => ignoreFlag_posSemidef _ (phaseEffect_posSemidef u j),
    sum_ignoreFlag (phaseEffect u) (sum_phaseEffect u horth), ?_⟩
  unfold flaggedPhaseStates
  rw [success_pullFlaggedEffect]
  simp_rw [pull_identityLeaves]
  rw [← success_phaseEffect_pinched c u t hu hnorm]
  unfold successProbability
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pureState_matrix, trace_pinching]
  change _ = _ * (trace (phaseEffect u j * _)).re
  rw [← pinchingChannel_apply]
  rfl

/-- The exact maximum over the actual AURIC continuations and all joint
flag/residual POVMs, allowing a single common terminal flag for attainment. -/
theorem isGreatest_flaggedPhase [Nonempty ι] (ht : ∀ i, 0 ≤ t i)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0) :
    IsGreatest {s | ∃ descend : Fin k → Protocol ι,
      s ∈ successProbabilitySet (uniformPrior ι) (flaggedPhaseStates c u t hu hnorm descend)}
      (pinchedOptimum c t) := by
  obtain ⟨hM, hs, hscore⟩ := flagged_identity_attains c u t hu hnorm horth (fun _ => 0)
  refine ⟨⟨fun _ => .leaf 0 1, _, hM, hs, hscore.symm⟩, ?_⟩
  rintro _ ⟨descend, M, hM, hs, rfl⟩
  exact flagged_phase_success_le c u t hu hnorm ht horth descend M hM hs

end

end D5.S3.Quantum.Measurement.Auric.CoordinatePinching
