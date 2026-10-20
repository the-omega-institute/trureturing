/- GID: D5/S3/Quantum/Information/HedgingMajorityThreshold
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/HedgingMajorityThreshold
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Certain majority success in qubit hedging requires certain single-game success. -/

import D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence
import D5.S3.QuantumStates.ZeroWeightSupportFace
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.QuantumBounds.NonlocalityDepthQuantumBound

/-! Strict-majority certainty for the parallel Arunachalam–Molina–Russo qubit game. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.HedgingMajorityThreshold

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence (partialTraceFirst)

/-- The amplitude of the initial shared pair. -/
def sharedAmp (α : ℝ) (x z : Fin 2) : ℂ :=
  if x = z then (if x = 0 then (α : ℂ) else (Real.sqrt (1 - α ^ 2) : ℂ)) else 0

/-- The initial vector, indexed by Bob's word and Alice's retained word. -/
def sharedVec (n : ℕ) (α : ℝ) : (Fin n → Fin 2) × (Fin n → Fin 2) → ℂ :=
  fun p => ∏ i, sharedAmp α (p.1 i) (p.2 i)

/-- The successful one-game vector. -/
def winVec (θ : ℝ) (y z : Fin 2) : ℂ :=
  if y = z then (if y = 0 then (Real.cos θ : ℂ) else (Real.sin θ : ℂ)) else 0

/-- The successful rank-one projection and its full orthogonal complement. -/
def outcomeProj (θ : ℝ) (b : Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let P := vecMulVec (fun p => winVec θ p.1 p.2) (star (fun p => winVec θ p.1 p.2))
  if b = 1 then P else 1 - P

/-- The game-by-game tensor, regrouped into Bob's and Alice's words. -/
def gameTensor (n : ℕ) (M : Fin n → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix ((Fin n → Fin 2) × (Fin n → Fin 2)) ((Fin n → Fin 2) × (Fin n → Fin 2)) ℂ :=
  fun p q => ∏ i, M i (p.1 i, p.2 i) (q.1 i, q.2 i)

/-- The projection onto outcomes with at least k successes. -/
def winAtLeast (n k : ℕ) (θ : ℝ) :=
  ∑ a : Fin n → Fin 2 with k ≤ #{i | a i = 1},
    gameTensor n (fun i => outcomeProj θ (a i))

/-- The output of Bob's joint channel, acting on the first word. -/
def output {m n : ℕ} (K : Fin m → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (α : ℝ) :=
  ∑ l, (K l ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) *
    vecMulVec (sharedVec n α) (star (sharedVec n α)) *
    (K l ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))ᴴ

/-- Certain majority success is equivalent to certain single-game success. -/
def claim : Prop :=
  ∀ (n k : ℕ), n < 2 * k → k ≤ n → ∀ (α θ : ℝ), 0 < α → α ≤ 1 →
    ((∃ (m : ℕ) (K : Fin m → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
        ∑ l, (K l)ᴴ * K l = 1 ∧ trace (winAtLeast n k θ * output K α) = 1) ↔
      α ^ 2 = Real.cos θ ^ 2)

private theorem tensor_mul {n : ℕ}
    (M N : Fin n → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    gameTensor n M * gameTensor n N = gameTensor n (fun i => M i * N i) := by
  ext p q
  change (∑ r : (Fin n → Fin 2) × (Fin n → Fin 2),
    (∏ i, M i (p.1 i, p.2 i) (r.1 i, r.2 i)) *
    ∏ i, N i (r.1 i, r.2 i) (q.1 i, q.2 i)) =
    ∏ i, ∑ r : Fin 2 × Fin 2,
      M i (p.1 i, p.2 i) r * N i r (q.1 i, q.2 i)
  rw [Fintype.prod_sum]
  have h := (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 2)
    (fun _ => Fin 2)).sum_comp
    (fun r => (∏ i, M i (p.1 i, p.2 i) (r.1 i, r.2 i)) *
      ∏ i, N i (r.1 i, r.2 i) (q.1 i, q.2 i))
  rw [← h]
  apply Finset.sum_congr rfl
  intro r _
  exact Finset.prod_mul_distrib.symm

private theorem win_norm (θ : ℝ) : star (fun p : Fin 2 × Fin 2 => winVec θ p.1 p.2) ⬝ᵥ
    (fun p => winVec θ p.1 p.2) = 1 := by
  norm_num only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, winVec,
    Pi.star_apply, ite_true, ite_false, Fin.isValue, zero_ne_one, one_ne_zero,
    star_zero, zero_mul, mul_zero, zero_add, add_zero,
    Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  exact_mod_cast (by nlinarith [Real.cos_sq_add_sin_sq θ] :
    Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1)

private theorem outcome_laws (θ : ℝ) :
    (∀ b, (outcomeProj θ b)ᴴ = outcomeProj θ b) ∧
    (∀ a b, outcomeProj θ a * outcomeProj θ b = if a = b then outcomeProj θ a else 0) := by
  have hp : outcomeProj θ 1 * outcomeProj θ 1 = outcomeProj θ 1 := by
    unfold outcomeProj
    rw [ite_eq_left rfl, vecMulVec_mul_vecMulVec, win_norm θ, one_smul]
  have hh : (outcomeProj θ 1)ᴴ = outcomeProj θ 1 := by
    unfold outcomeProj
    rw [ite_eq_left rfl, conjTranspose_vecMulVec, star_star]
  have hzero : outcomeProj θ 0 = 1 - outcomeProj θ 1 := by
    unfold outcomeProj
    rw [ite_eq_right (by decide), ite_eq_left rfl]
  constructor
  · intro b
    fin_cases b
    · change (outcomeProj θ 0)ᴴ = outcomeProj θ 0
      rw [hzero, conjTranspose_sub, conjTranspose_one, hh]
    · exact hh
  · intro a b
    fin_cases a <;> fin_cases b
    · change outcomeProj θ 0 * outcomeProj θ 0 = outcomeProj θ 0
      rw [hzero]
      noncomm_ring [hp]
    · change outcomeProj θ 0 * outcomeProj θ 1 = 0
      rw [hzero, sub_mul, one_mul, hp, sub_self]
    · change outcomeProj θ 1 * outcomeProj θ 0 = 0
      rw [hzero, mul_sub, mul_one, hp, sub_self]
    · exact hp

private theorem outcome_tensor_product {n : ℕ} (θ : ℝ) (a b : Fin n → Fin 2) :
    gameTensor n (fun i => outcomeProj θ (a i)) *
      gameTensor n (fun i => outcomeProj θ (b i)) =
    if a = b then gameTensor n (fun i => outcomeProj θ (a i)) else 0 := by
  rw [tensor_mul]
  by_cases hab : a = b
  · subst b
    rw [ite_eq_left rfl]
    congr 1
    funext i
    exact ((outcome_laws θ).2 (a i) (a i)).trans (ite_eq_left rfl)
  · rw [ite_eq_right hab]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra h
      exact hab (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    ext p q
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change (outcomeProj θ (a i) * outcomeProj θ (b i))
      (p.1 i, p.2 i) (q.1 i, q.2 i) = 0
    rw [(outcome_laws θ).2, ite_eq_right hi]
    rfl

private theorem winning_projector (n k : ℕ) (θ : ℝ) :
    (winAtLeast n k θ)ᴴ = winAtLeast n k θ ∧
      winAtLeast n k θ * winAtLeast n k θ = winAtLeast n k θ := by
  have hadj (a : Fin n → Fin 2) :
      (gameTensor n (fun i => outcomeProj θ (a i)))ᴴ =
        gameTensor n (fun i => outcomeProj θ (a i)) := by
    let e := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 2) (fun _ => Fin 2)
    have h := D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Tensor.tensor_star
      (fun i => outcomeProj θ (a i))
    have he := congrArg (fun A => A.submatrix e.symm e.symm) h
    change gameTensor n (fun i => (outcomeProj θ (a i))ᴴ) =
      (gameTensor n (fun i => outcomeProj θ (a i)))ᴴ at he
    rw [show (fun i => (outcomeProj θ (a i))ᴴ) =
      (fun i => outcomeProj θ (a i)) from funext fun i => (outcome_laws θ).1 (a i)] at he
    exact he.symm
  constructor
  · unfold winAtLeast
    rw [conjTranspose_sum]
    exact Finset.sum_congr rfl fun a _ => hadj a
  · unfold winAtLeast
    rw [Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Matrix.mul_sum]
    simp only [outcome_tensor_product θ]
    rw [Finset.sum_ite_eq, ite_eq_left ha]

private theorem tensor_trace {n : ℕ}
    (M : Fin n → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    trace (gameTensor n M) = ∏ i, trace (M i) := by
  let tensor (r : ℕ) (N : Fin r → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      Matrix (Fin r → Fin 2 × Fin 2) (Fin r → Fin 2 × Fin 2) ℂ :=
    fun p q => ∏ i, N i (p i) (q i)
  have ht : ∀ (r : ℕ) (N : Fin r → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      trace (tensor r N) = ∏ i, trace (N i) := by
    intro r
    induction r with
    | zero =>
      intro N
      norm_num [tensor, trace, Matrix.diag, Fintype.card_fun]
    | succ r ih =>
      intro N
      have he : trace (tensor (r + 1) N) =
          trace (N 0 ⊗ₖ tensor r (fun i => N i.succ)) := by
        change (∑ p : Fin (r + 1) → Fin 2 × Fin 2, ∏ i, N i (p i) (p i)) =
          ∑ p : (Fin 2 × Fin 2) × (Fin r → Fin 2 × Fin 2),
            N 0 p.1 p.1 * ∏ i, N i.succ (p.2 i) (p.2 i)
        rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => Fin 2 × Fin 2)).sum_comp]
        apply Finset.sum_congr rfl
        intro p _
        change (∏ i, N i ((Fin.cons p.1 p.2 : Fin (r + 1) → Fin 2 × Fin 2) i)
          ((Fin.cons p.1 p.2 : Fin (r + 1) → Fin 2 × Fin 2) i)) =
          N 0 p.1 p.1 * ∏ i, N i.succ (p.2 i) (p.2 i)
        rw [Fin.prod_univ_succ]
        rfl
      rw [he, trace_kronecker, ih, Fin.prod_univ_succ]
  rw [← ht n M]
  change (∑ p : (Fin n → Fin 2) × (Fin n → Fin 2),
    ∏ i, M i (p.1 i, p.2 i) (p.1 i, p.2 i)) =
    ∑ p : Fin n → Fin 2 × Fin 2, ∏ i, M i (p i) (p i)
  exact ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin 2)
    (fun _ => Fin 2)).sum_comp _).symm

private def pairState (α : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  vecMulVec (fun p => sharedAmp α p.1 p.2) (star (fun p => sharedAmp α p.1 p.2))

private theorem shared_density (n : ℕ) (α : ℝ) :
    vecMulVec (sharedVec n α) (star (sharedVec n α)) =
      gameTensor n (fun _ => pairState α) := by
  ext p q
  simp only [vecMulVec_apply, sharedVec, Pi.star_apply, star_prod,
    pairState, gameTensor, Finset.prod_mul_distrib]

private theorem pair_trace (α : ℝ) (ha : 0 < α) (ha' : α ≤ 1) :
    trace (pairState α) = 1 := by
  have hs : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  norm_num only [pairState, trace, Matrix.diag, vecMulVec_apply, sharedAmp,
    Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply, Fin.isValue,
    ite_true, ite_false, zero_ne_one, one_ne_zero, star_zero, mul_zero,
    zero_mul, add_zero, zero_add, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  exact_mod_cast (by nlinarith : α * α + Real.sqrt (1 - α ^ 2) *
    Real.sqrt (1 - α ^ 2) = 1)

private def testLocal (θ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
    diagonal (fun z => if z = 0 then (Real.sin θ : ℂ) ^ 2 else -(Real.cos θ : ℂ) ^ 2)

private theorem local_zero_compression (θ : ℝ) :
    outcomeProj θ 1 * testLocal θ * outcomeProj θ 1 = 0 := by
  ext p q
  rcases p with ⟨y,z⟩
  rcases q with ⟨y',z'⟩
  fin_cases y <;> fin_cases z <;> fin_cases y' <;> fin_cases z' <;>
    norm_num [outcomeProj, vecMulVec_apply, winVec, testLocal, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, kroneckerMap_apply, diagonal,
      Pi.star_apply, Fin.isValue, ite_true, ite_false, zero_ne_one, one_ne_zero,
      Matrix.one_apply, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin] <;> ring

private theorem majority_intersection {n k : ℕ} (hn : n < 2 * k)
    (a b : Fin n → Fin 2) (ha : k ≤ #{i | a i = 1})
    (hb : k ≤ #{i | b i = 1}) : ∃ i, a i = 1 ∧ b i = 1 := by
  by_contra h
  have hd : Disjoint (Finset.univ.filter fun i => a i = 1)
      (Finset.univ.filter fun i => b i = 1) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact h ⟨i, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
  have hc := Finset.card_le_card (Finset.subset_univ
    ((Finset.univ.filter fun i => a i = 1) ∪ (Finset.univ.filter fun i => b i = 1)))
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ, Fintype.card_fin] at hc
  omega

private theorem majority_zero_compression {n k : ℕ} (hn : n < 2 * k) (θ : ℝ) :
    winAtLeast n k θ * gameTensor n (fun _ => testLocal θ) * winAtLeast n k θ = 0 := by
  unfold winAtLeast
  rw [Matrix.sum_mul, Matrix.sum_mul]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro b hb
  rw [tensor_mul, tensor_mul]
  obtain ⟨i, hai, hbi⟩ := majority_intersection hn a b
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  ext p q
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  change (outcomeProj θ (a i) * testLocal θ * outcomeProj θ (b i))
    (p.1 i, p.2 i) (q.1 i, q.2 i) = 0
  rw [hai, hbi, local_zero_compression]
  rfl

private theorem output_psd {m n : ℕ}
    (K : Fin m → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (α : ℝ) :
    (output K α).PosSemidef := by
  unfold output
  exact Matrix.posSemidef_sum _ fun l _ =>
    (posSemidef_vecMulVec_self_star (sharedVec n α)).mul_mul_conjTranspose_same _

private theorem output_trace {m n : ℕ}
    (K : Fin m → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hK : ∑ l, (K l)ᴴ * K l = 1) (α : ℝ) (ha : 0 < α) (ha' : α ≤ 1) :
    trace (output K α) = 1 := by
  have hLift : ∑ l, (K l ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))ᴴ *
      (K l ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) = 1 := by
    simp only [conjTranspose_kronecker, conjTranspose_one,
      ← mul_kronecker_mul, one_mul]
    have hs : (∑ l, ((K l)ᴴ * K l) ⊗ₖ
        (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) =
        (∑ l, (K l)ᴴ * K l) ⊗ₖ
          (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
      ext p q
      simp only [Matrix.sum_apply, kroneckerMap_apply]
      change (∑ l, ((K l)ᴴ * K l) p.1 q.1 * (1 : Matrix _ _ ℂ) p.2 q.2) =
        (∑ l, ((K l)ᴴ * K l) p.1 q.1) * (1 : Matrix _ _ ℂ) p.2 q.2
      exact (Finset.sum_mul _ _ _).symm
    rw [hs, hK, one_kronecker_one]
  obtain ⟨channel, action⟩ :=
    D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
      (fun l => K l ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) hLift
  have ht := channel.trace_preserving
    (CStarMatrix.ofMatrix (vecMulVec (sharedVec n α) (star (sharedVec n α))))
  change trace (CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (vecMulVec (sharedVec n α) (star (sharedVec n α)))))) =
      trace (vecMulVec (sharedVec n α) (star (sharedVec n α))) at ht
  rw [action] at ht
  change trace (output K α) = _ at ht
  rw [ht, shared_density, tensor_trace]
  simp only [pair_trace α ha ha', Finset.prod_const_one]

private theorem trace_retained {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] (X : Matrix (A × B) (A × B) ℂ) (D : Matrix B B ℂ) :
    trace (((1 : Matrix A A ℂ) ⊗ₖ D) * X) = trace (D * partialTraceFirst X) := by
  simp only [trace, Matrix.diag, mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, Finset.sum_const_zero,
    ite_true, partialTraceFirst, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

private theorem pair_marginal (α : ℝ) (ha : 0 < α) (ha' : α ≤ 1) :
    partialTraceFirst (pairState α) =
      diagonal (fun z : Fin 2 => if z = 0 then (α : ℂ) ^ 2 else 1 - (α : ℂ) ^ 2) := by
  have hs : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  ext z w
  fin_cases z <;> fin_cases w <;>
    norm_num [partialTraceFirst, pairState, vecMulVec_apply, sharedAmp,
      Fin.sum_univ_two, Pi.star_apply, diagonal, Fin.isValue, ite_true, ite_false,
      zero_ne_one, one_ne_zero, star_zero, zero_mul, mul_zero, add_zero, zero_add,
      Complex.star_def, Complex.conj_ofReal]
  · ring
  · rw [← Complex.ofReal_mul]
    exact_mod_cast (by nlinarith : Real.sqrt (1 - α ^ 2) * Real.sqrt (1 - α ^ 2) =
      1 - α ^ 2)

private theorem local_channel_readout {m n : ℕ}
    (K : Fin m → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hK : ∑ l, (K l)ᴴ * K l = 1) (α : ℝ)
    (D : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    trace (((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⊗ₖ D) * output K α) =
      trace (((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⊗ₖ D) *
        vecMulVec (sharedVec n α) (star (sharedVec n α))) := by
  have hs : (∑ l, ((K l)ᴴ * K l) ⊗ₖ D) =
      (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⊗ₖ D := by
    calc
      _ = (∑ l, (K l)ᴴ * K l) ⊗ₖ D := by
        ext p q
        simp only [Matrix.sum_apply, kroneckerMap_apply]
        change (∑ l, ((K l)ᴴ * K l) p.1 q.1 * D p.2 q.2) =
          (∑ l, ((K l)ᴴ * K l) p.1 q.1) * D p.2 q.2
        exact (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [hK]
  unfold output
  rw [Matrix.mul_sum, trace_sum]
  calc
    _ = ∑ l, trace ((((K l)ᴴ * K l) ⊗ₖ D) *
        vecMulVec (sharedVec n α) (star (sharedVec n α))) := by
      apply Finset.sum_congr rfl
      intro l _
      have hf : (K l ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ))ᴴ *
          ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⊗ₖ D) *
          (K l ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) =
          ((K l)ᴴ * K l) ⊗ₖ D := by
        rw [conjTranspose_kronecker, conjTranspose_one,
          ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, one_mul, mul_one]
      rw [← hf]
      rw [← mul_assoc, ← mul_assoc, trace_mul_cycle]
      simp only [mul_assoc]
    _ = _ := by rw [← trace_sum, ← Matrix.sum_mul, hs]

private theorem output_marginal {m n : ℕ}
    (K : Fin m → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hK : ∑ l, (K l)ᴴ * K l = 1) (α θ : ℝ) (ha : 0 < α) (ha' : α ≤ 1) :
    trace (gameTensor n (fun _ => testLocal θ) * output K α) =
      ((α ^ 2 - Real.cos θ ^ 2 : ℝ) : ℂ) ^ n := by
  let d : Fin 2 → ℂ := fun z =>
    if z = 0 then (Real.sin θ : ℂ) ^ 2 else -(Real.cos θ : ℂ) ^ 2
  let D : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
    fun z w => ∏ i, diagonal d (z i) (w i)
  have he : gameTensor n (fun _ => testLocal θ) =
      (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⊗ₖ D := by
    ext p q
    change (∏ i, (if p.1 i = q.1 i then (1 : ℂ) else 0) *
      diagonal d (p.2 i) (q.2 i)) =
      (if p.1 = q.1 then (1 : ℂ) else 0) * ∏ i, diagonal d (p.2 i) (q.2 i)
    rw [Finset.prod_mul_distrib, Fintype.prod_boole]
    congr 2
    exact propext funext_iff.symm
  rw [he, local_channel_readout K hK, ← he, shared_density, tensor_mul, tensor_trace]
  have ht : trace (testLocal θ * pairState α) =
      ((α ^ 2 - Real.cos θ ^ 2 : ℝ) : ℂ) := by
    unfold testLocal
    rw [trace_retained, pair_marginal α ha ha', diagonal_mul_diagonal, trace_diagonal]
    simp only [Fin.sum_univ_two, Fin.isValue, ite_true, ite_false, one_ne_zero]
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq θ] :
      Real.sin θ ^ 2 * α ^ 2 + -Real.cos θ ^ 2 * (1 - α ^ 2) =
        α ^ 2 - Real.cos θ ^ 2)
  simp only [ht, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem projection_support {ι : Type*} [Fintype ι]
    (P ρ : Matrix ι ι ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hρ : ρ.PosSemidef) (ht : trace (P * ρ) = trace ρ) : ρ = P * ρ * P := by
  classical
  have hQ : (1 - P)ᴴ = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hP]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hPP]
  have htQ : trace (ρ * (1 - P)) = 0 := by
    rw [mul_sub, mul_one, trace_sub, trace_mul_comm ρ P, ht, sub_self]
  have hs := D5.S3.QuantumStates.ZeroWeightSupportFace.zero_weight_support_face
    ρ (1 - P) hρ hQ hQQ htQ
  have he : 1 - (1 - P) = P := by abel
  rw [he] at hs
  exact hs.2

private def signedUnit (r : ℝ) : ℂ := if 0 ≤ r then 1 else -1

private theorem signedUnit_norm (r : ℝ) : star (signedUnit r) * signedUnit r = 1 := by
  unfold signedUnit
  split_ifs <;> norm_num

private theorem signedUnit_action (r : ℝ) :
    signedUnit r * ((|r| : ℝ) : ℂ) = (r : ℂ) := by
  unfold signedUnit
  split_ifs with h
  · rw [abs_of_nonneg h, one_mul]
  · rw [abs_of_neg (lt_of_not_ge h), Complex.ofReal_neg]
    ring

private theorem certain_strategy {n k : ℕ} (hk : k ≤ n) (α θ : ℝ)
    (ha : 0 < α) (he : α ^ 2 = Real.cos θ ^ 2) :
    ∃ (m : ℕ) (K : Fin m → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
      ∑ l, (K l)ᴴ * K l = 1 ∧ trace (winAtLeast n k θ * output K α) = 1 := by
  have hα : α = |Real.cos θ| := by
    nlinarith [sq_abs (Real.cos θ), abs_nonneg (Real.cos θ)]
  have hβ : Real.sqrt (1 - α ^ 2) = |Real.sin θ| := by
    have heq : 1 - α ^ 2 = Real.sin θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [heq, Real.sqrt_sq_eq_abs]
  let phase : Fin 2 → ℂ := fun z =>
    signedUnit (if z = 0 then Real.cos θ else Real.sin θ)
  let phases : (Fin n → Fin 2) → ℂ := fun x => ∏ i, phase (x i)
  let U : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := diagonal phases
  have hU : Uᴴ * U = 1 := by
    rw [show U = diagonal phases from rfl, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    apply congrArg diagonal
    funext x
    change star (∏ i, phase (x i)) * (∏ i, phase (x i)) = 1
    rw [star_prod, ← Finset.prod_mul_distrib]
    simp only [phase, signedUnit_norm, Finset.prod_const_one]
  have hamp (y z : Fin 2) : phase y * sharedAmp α y z = winVec θ y z := by
    by_cases hyz : y = z
    · subst z
      fin_cases y
      · change signedUnit (Real.cos θ) * (α : ℂ) = (Real.cos θ : ℂ)
        rw [hα, signedUnit_action]
      · change signedUnit (Real.sin θ) * (Real.sqrt (1 - α ^ 2) : ℂ) =
          (Real.sin θ : ℂ)
        rw [hβ, signedUnit_action]
    · unfold sharedAmp winVec
      rw [ite_eq_right hyz, ite_eq_right hyz, mul_zero]
  let v : (Fin n → Fin 2) × (Fin n → Fin 2) → ℂ :=
    fun p => ∏ i, winVec θ (p.1 i) (p.2 i)
  have hUv : (U ⊗ₖ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)) *ᵥ
      sharedVec n α = v := by
    funext p
    rw [show U = diagonal phases from rfl,
      show (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) =
        diagonal (fun _ => 1) from diagonal_one.symm,
      diagonal_kronecker_diagonal, mulVec_diagonal]
    change ((∏ i, phase (p.1 i)) * 1) * (∏ i, sharedAmp α (p.1 i) (p.2 i)) =
      ∏ i, winVec θ (p.1 i) (p.2 i)
    rw [mul_one, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hamp _ _
  have hout : output (fun _ : Fin 1 => U) α = gameTensor n (fun _ => outcomeProj θ 1) := by
    unfold output
    rw [Fin.sum_univ_one, mul_vecMulVec, vecMulVec_mul, vecMul_conjTranspose,
      star_star, hUv]
    ext p q
    simp only [v, vecMulVec_apply, Pi.star_apply, star_prod, outcomeProj, ite_true,
      gameTensor, Finset.prod_mul_distrib]
  refine ⟨1, (fun _ => U), ?_, ?_⟩
  · rw [Fin.sum_univ_one]
    exact hU
  · rw [hout]
    have hm : (fun _ : Fin n => (1 : Fin 2)) ∈
        (Finset.univ.filter fun a : Fin n → Fin 2 => k ≤ #{i | a i = 1}) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.filter_true,
        Finset.card_univ, Fintype.card_fin]
      exact hk
    have hfix : winAtLeast n k θ * gameTensor n (fun _ => outcomeProj θ 1) =
        gameTensor n (fun _ => outcomeProj θ 1) := by
      unfold winAtLeast
      rw [Matrix.sum_mul]
      simp only [outcome_tensor_product θ]
      rw [Finset.sum_ite_eq', ite_eq_left hm]
    rw [hfix, tensor_trace]
    have ht : trace (outcomeProj θ 1) = 1 := by
      unfold outcomeProj
      rw [ite_eq_left rfl, trace_vecMulVec, dotProduct_comm, win_norm]
    simp only [ht, Finset.prod_const_one]

/-- Bob can guarantee a strict majority exactly in the certain single-game case. -/
theorem result : claim := by
  intro n k hn hk α θ ha ha'
  constructor
  · rintro ⟨m, K, hK, hwin⟩
    obtain ⟨hP, hPP⟩ := winning_projector n k θ
    have hs := projection_support (winAtLeast n k θ) (output K α) hP hPP
      (output_psd K α) (hwin.trans (output_trace K hK α ha ha').symm)
    have hz : trace (gameTensor n (fun _ => testLocal θ) * output K α) = 0 := by
      conv_lhs => rw [hs]
      rw [← mul_assoc, trace_mul_cycle, ← mul_assoc, majority_zero_compression hn θ,
        zero_mul, trace_zero]
    rw [output_marginal K hK α θ ha ha'] at hz
    have he := eq_zero_of_pow_eq_zero hz
    exact sub_eq_zero.mp (Complex.ofReal_injective he)
  · exact certain_strategy hk α θ ha

end D5.S3.Quantum.Information.HedgingMajorityThreshold
