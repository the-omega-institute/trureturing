/- GID: D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/QramCountStatisticInsufficiency
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.claim; result=D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.result; claim=D5/S3/Quantum/Tomography/QramCountStatisticInsufficiency.claim
   digest: The plus-count statistic loses exact-weight discrimination information. -/

import D5.S3.Observer.BornReduction
import D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation

/-! The equal-prior exact-weight model of L. Bohac, arXiv:2512.17503v1,
Remark 5.3. The function is sampled once and shared by all copies. The witness measures
both registers in the Walsh basis and rejects equal nonzero outcomes. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency

open D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation (u4 u4_unitary)

/-- The number of true addresses of a Boolean memory. -/
def weight {n : ℕ} (f : Fin (2 ^ n) → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x = true).card

/-- The uniform prior is supported on all memories of exactly this weight. -/
def weightClass (n m : ℕ) : Finset (Fin (2 ^ n) → Bool) :=
  Finset.univ.filter fun f => weight f = m

/-- The normalized phase address state produced by one query. -/
def addressState (n : ℕ) (f : Fin (2 ^ n) → Bool) : Fin (2 ^ n) → ℂ :=
  fun x => (-1 : ℂ) ^ (f x).toNat / (Real.sqrt (2 ^ n) : ℂ)

/-- The all-plus address state. -/
def plusState (n : ℕ) : Fin (2 ^ n) → ℂ := addressState n (fun _ => false)

/-- The induced state of copies of the same uniformly sampled exact-weight memory. -/
def copyState (n t m : ℕ) :
    Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ :=
  (1 / (weightClass n m).card : ℂ) •
    ∑ f ∈ weightClass n m, Matrix.of fun x y =>
      ∏ i, addressState n f (x i) * star (addressState n f (y i))

/-- The single-register plus projector. -/
def plusProj (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.vecMulVec (plusState n) (star (plusState n))

/-- The projector for exactly `k` plus outcomes in `t` registers. -/
def countProj (n t k : ℕ) :
    Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ :=
  ∑ s ∈ (Finset.univ : Finset (Fin t)).powersetCard k, Matrix.of fun x y =>
    ∏ i, (if i ∈ s then plusProj n else 1 - plusProj n) (x i) (y i)

/-- Equal-prior success, accepting the first weight with effect `e`. -/
def successProb (n t m₀ m₁ : ℕ)
    (e : Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ) : ℝ :=
  (1 / 2 : ℝ) * (Matrix.trace (copyState n t m₀ * e)).re +
    (1 / 2 : ℝ) * (Matrix.trace (copyState n t m₁ * (1 - e))).re

/-- A deterministic decision rule using only the number of plus outcomes. -/
def countTest (n t : ℕ) (g : Fin (t + 1) → Bool) :
    Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ :=
  ∑ k : Fin (t + 1), if g k then countProj n t k else 0

/-- Sufficiency of the plus count for every equal-prior exact-weight test. -/
def claim : Prop :=
  ∀ n ≥ 1, ∀ t ≥ 1, ∀ m₀ m₁, m₀ ≤ 2 ^ n → m₁ ≤ 2 ^ n →
    ∀ e : Matrix (Fin t → Fin (2 ^ n)) (Fin t → Fin (2 ^ n)) ℂ,
      e.PosSemidef → (1 - e).PosSemidef →
        ∃ g : Fin (t + 1) → Bool,
          successProb n t m₀ m₁ e ≤ successProb n t m₀ m₁ (countTest n t g)

private def walsh (y x : Fin 4) : ℂ :=
  u4 y x

private def walshPair (y z : Fin 4) (x : Fin 2 → Fin 4) : ℂ :=
  walsh y (x 0) * walsh z (x 1)

private def reject : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ :=
  ∑ y : Fin 3, Matrix.vecMulVec (walshPair y.succ y.succ)
    (star (walshPair y.succ y.succ))

private def witness : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ := 1 - reject

private lemma walsh_orthogonal (y z : Fin 4) :
    (star (walsh y)) ⬝ᵥ walsh z = if y = z then 1 else 0 := by
  change (star (u4 y)) ⬝ᵥ u4 z = if y = z then 1 else 0
  simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct,
    Pi.star_apply, mul_comm, eq_comm] using
    congrArg (fun a : Matrix (Fin 4) (Fin 4) ℂ => a z y)
      (Matrix.mem_unitaryGroup_iff.mp u4_unitary)

private lemma plus_walsh : plusState 2 = walsh 0 := by
  have hs : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  funext x
  delta plusState addressState walsh u4
  fin_cases x <;> norm_num [hs, Matrix.smul_apply, smul_eq_mul]

private lemma class_one : weightClass 2 1 =
    {![true, false, false, false], ![false, true, false, false],
      ![false, false, true, false], ![false, false, false, true]} := by
  decide

private lemma class_two : weightClass 2 2 =
    {![true, true, false, false], ![true, false, true, false],
      ![true, false, false, true], ![false, true, true, false],
      ![false, true, false, true], ![false, false, true, true]} := by
  decide

private lemma tensor_inner {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (u v : ι → α → ℂ) :
    (star (fun x : ι → α => ∏ i, u i (x i))) ⬝ᵥ (fun x => ∏ i, v i (x i)) =
      ∏ i, (star (u i)) ⬝ᵥ v i := by
  simp only [dotProduct, Pi.star_apply, star_prod]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : ι) (x : α) => star (u i x) * v i x)).symm

private lemma pair_inner (u v a b : Fin 4 → ℂ) :
    (star (fun x : Fin 2 → Fin 4 => u (x 0) * v (x 1))) ⬝ᵥ
      (fun x => a (x 0) * b (x 1)) = (star u ⬝ᵥ a) * (star v ⬝ᵥ b) := by
  simpa [Fin.prod_univ_two] using tensor_inner (![u, v]) (![a, b])

private lemma trace_rank {α : Type*} [Fintype α] (u v : α → ℂ) :
    Matrix.trace (Matrix.vecMulVec u (star u) * Matrix.vecMulVec v (star v)) =
      (star u ⬝ᵥ v) * (star v ⬝ᵥ u) := by
  have h := D5.S3.Observer.BornReduction.rank_one_pure_state_modulus_square_reduction
    (fun _ : Unit => Matrix.vecMulVec v (star v)) (Matrix.vecMulVec u (star u)) () v u rfl rfl
  change Matrix.trace (Matrix.vecMulVec u (star u) * Matrix.vecMulVec v (star v)) = _ at h
  rw [h, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  exact congrArg (fun z : ℂ => z * (star v ⬝ᵥ u)) (Matrix.star_dotProduct u v).symm

private lemma copyState_rank (n t m : ℕ) : copyState n t m =
    (1 / (weightClass n m).card : ℂ) • ∑ f ∈ weightClass n m,
      Matrix.vecMulVec (fun x : Fin t → Fin (2 ^ n) => ∏ i, addressState n f (x i))
        (star (fun x => ∏ i, addressState n f (x i))) := by
  unfold copyState
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  ext x y
  simp [Matrix.vecMulVec_apply, Finset.prod_mul_distrib, star_prod]

private lemma one_overlap (f : Fin 4 → Bool) (hf : f ∈ weightClass 2 1) (y : Fin 4) :
    (star (addressState 2 f) ⬝ᵥ walsh y) *
      (star (walsh y) ⬝ᵥ addressState 2 f) = (1 / 4 : ℂ) := by
  have hs : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  change (∑ x : Fin 4, star (addressState 2 f x) * walsh y x) *
    (∑ x : Fin 4, star (walsh y x) * addressState 2 f x) = _
  rw [class_one] at hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> fin_cases y <;>
    delta addressState walsh u4 <;>
    norm_num [Fin.sum_univ_succ, hs, Matrix.smul_apply, smul_eq_mul]

private lemma weight_one_law (y z : Fin 4) :
    Matrix.trace (copyState 2 2 1 *
      Matrix.vecMulVec (walshPair y z) (star (walshPair y z))) = (1 / 16 : ℂ) := by
  rw [copyState_rank, Matrix.smul_mul, Matrix.trace_smul, Finset.sum_mul, Matrix.trace_sum]
  have h (f : Fin 4 → Bool) (hf : f ∈ weightClass 2 1) :
      Matrix.trace (Matrix.vecMulVec
        (fun x : Fin 2 → Fin 4 => ∏ i, addressState 2 f (x i))
        (star (fun x => ∏ i, addressState 2 f (x i))) *
        Matrix.vecMulVec (walshPair y z) (star (walshPair y z))) = (1 / 16 : ℂ) := by
    rw [trace_rank]
    simp only [Fin.prod_univ_two]
    change (star (fun x : Fin 2 → Fin 4 => addressState 2 f (x 0) *
      addressState 2 f (x 1)) ⬝ᵥ (fun x => walsh y (x 0) * walsh z (x 1))) *
      (star (fun x : Fin 2 → Fin 4 => walsh y (x 0) * walsh z (x 1)) ⬝ᵥ
        (fun x => addressState 2 f (x 0) * addressState 2 f (x 1))) = _
    rw [pair_inner, pair_inner]
    calc
      _ = ((star (addressState 2 f) ⬝ᵥ walsh y) *
          (star (walsh y) ⬝ᵥ addressState 2 f)) *
        ((star (addressState 2 f) ⬝ᵥ walsh z) *
          (star (walsh z) ⬝ᵥ addressState 2 f)) := by ring
      _ = 1 / 16 := by rw [one_overlap f hf y, one_overlap f hf z]; norm_num
  calc
    _ = (1 / (weightClass 2 1).card : ℂ) •
        ∑ _f ∈ weightClass 2 1, (1 / 16 : ℂ) := by
      congr 1
      exact Finset.sum_congr rfl fun f hf => h f hf
    _ = 1 / 16 := by norm_num [class_one]

private lemma class_two_states :
    addressState 2 ![true, true, false, false] = -walsh 2 ∧
    addressState 2 ![true, false, true, false] = -walsh 1 ∧
    addressState 2 ![true, false, false, true] = -walsh 3 ∧
    addressState 2 ![false, true, true, false] = walsh 3 ∧
    addressState 2 ![false, true, false, true] = walsh 1 ∧
    addressState 2 ![false, false, true, true] = walsh 2 := by
  have hs : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext x <;> fin_cases x <;>
    delta addressState walsh u4 <;> norm_num [hs, Matrix.smul_apply, smul_eq_mul]

private lemma weight_two_state : copyState 2 2 2 = (1 / 3 : ℂ) • reject := by
  rw [copyState_rank, class_two]
  norm_num [Finset.sum_insert, Finset.sum_singleton, Fin.prod_univ_two]
  rw [class_two_states.1, class_two_states.2.1, class_two_states.2.2.1,
    class_two_states.2.2.2.1, class_two_states.2.2.2.2.1, class_two_states.2.2.2.2.2]
  delta reject
  norm_num [Fin.sum_univ_succ, Finset.sum_insert,
    Finset.sum_singleton, Finset.card_insert_of_notMem]
  ext x y
  delta walshPair
  simp [Matrix.vecMulVec_apply]
  ring

private lemma pair_orthogonal (y z u v : Fin 4) :
    star (walshPair y z) ⬝ᵥ walshPair u v = if y = u ∧ z = v then 1 else 0 := by
  change (star (fun x : Fin 2 → Fin 4 => walsh y (x 0) * walsh z (x 1))) ⬝ᵥ
    (fun x => walsh u (x 0) * walsh v (x 1)) = _
  rw [pair_inner, walsh_orthogonal, walsh_orthogonal]
  split_ifs <;> simp_all

private lemma reject_projector : IsStarProjection reject where
  isIdempotentElem := by
    change reject * reject = reject
    unfold reject
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.vecMulVec_mul_vecMulVec,
      pair_orthogonal, Fin.succ_inj, and_self]
    simp [apply_ite]
  isSelfAdjoint := by
    change rejectᴴ = reject
    delta reject
    simp [Matrix.conjTranspose_sum]

open scoped MatrixOrder in
private lemma witness_valid : witness.PosSemidef ∧ (1 - witness).PosSemidef :=
  ⟨reject_projector.one_sub.nonneg.posSemidef,
    reject_projector.one_sub.one_sub.nonneg.posSemidef⟩

private lemma address_norm (f : Fin 4 → Bool) :
    star (addressState 2 f) ⬝ᵥ addressState 2 f = 1 := by
  have hs : Real.sqrt 4 = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  change (∑ x : Fin 4, star (addressState 2 f x) * addressState 2 f x) = 1
  have h (x : Fin 4) : star (addressState 2 f x) * addressState 2 f x = (1 / 4 : ℂ) := by
    cases hb : f x <;> delta addressState <;> norm_num [hb, hs]
  simp_rw [h]
  norm_num

private lemma weight_one_trace : Matrix.trace (copyState 2 2 1) = 1 := by
  rw [copyState_rank, Matrix.trace_smul, Matrix.trace_sum]
  have h (f : Fin 4 → Bool) :
      Matrix.trace (Matrix.vecMulVec
        (fun x : Fin 2 → Fin 4 => ∏ i, addressState 2 f (x i))
        (star (fun x => ∏ i, addressState 2 f (x i)))) = 1 := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm, tensor_inner]
    change (∏ _i : Fin 2, star (addressState 2 f) ⬝ᵥ addressState 2 f) = 1
    simp only [address_norm, Finset.prod_const_one]
  calc
    _ = (1 / (weightClass 2 1).card : ℂ) • ∑ _f ∈ weightClass 2 1, (1 : ℂ) := by
      congr 1
      exact Finset.sum_congr rfl fun f _ => h f
    _ = 1 := by norm_num [class_one]

private lemma reject_trace : Matrix.trace reject = 3 := by
  unfold reject
  rw [Matrix.trace_sum]
  have h (y : Fin 3) : Matrix.trace (Matrix.vecMulVec (walshPair y.succ y.succ)
      (star (walshPair y.succ y.succ))) = 1 := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm, pair_orthogonal]
    simp
  simp_rw [h]
  norm_num

private lemma weight_two_trace : Matrix.trace (copyState 2 2 2) = 1 := by
  rw [weight_two_state, Matrix.trace_smul, reject_trace]
  norm_num

private lemma witness_success : successProb 2 2 1 2 witness = 29 / 32 := by
  have h₁ : Matrix.trace (copyState 2 2 1 * reject) = (3 / 16 : ℂ) := by
    unfold reject
    rw [Finset.mul_sum, Matrix.trace_sum]
    simp_rw [weight_one_law]
    norm_num
  have h₂ : Matrix.trace (copyState 2 2 2 * reject) = 1 := by
    rw [weight_two_state, Matrix.smul_mul, reject_projector.isIdempotentElem.eq,
      Matrix.trace_smul, reject_trace]
    norm_num
  delta successProb witness
  simp only [sub_sub_cancel]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, weight_one_trace, h₁, h₂]
  norm_num

private lemma weight_two_law (y z : Fin 4) :
    Matrix.trace (copyState 2 2 2 *
      Matrix.vecMulVec (walshPair y z) (star (walshPair y z))) =
        if y = z ∧ y ≠ 0 then (1 / 3 : ℂ) else 0 := by
  rw [weight_two_state, Matrix.smul_mul, Matrix.trace_smul]
  unfold reject
  rw [Finset.sum_mul, Matrix.trace_sum]
  simp_rw [trace_rank, pair_orthogonal]
  fin_cases y <;> fin_cases z <;> norm_num [Fin.sum_univ_succ]

private lemma complement_walsh : 1 - plusProj 2 =
    ∑ y : Fin 3, Matrix.vecMulVec (walsh y.succ) (star (walsh y.succ)) := by
  have h := D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation.sum_projectors
    (Matrix.UnitaryGroup.transpose ⟨u4, u4_unitary⟩)
  change (∑ y : Fin 4, Matrix.vecMulVec (walsh y) (star (walsh y))) = 1 at h
  rw [Fin.sum_univ_succ] at h
  rw [plusProj, plus_walsh]
  rw [← h, add_sub_cancel_left]

private lemma count_walsh (k : Fin 3) : countProj 2 2 k =
    ∑ y : Fin 4, ∑ z : Fin 4,
      if (if y = 0 then 1 else 0) + (if z = 0 then 1 else 0) = (k : ℕ) then
        Matrix.vecMulVec (walshPair y z) (star (walshPair y z)) else 0 := by
  have h₀ : (Finset.univ : Finset (Fin 2)).powersetCard 0 = {∅} :=
    Finset.powersetCard_zero _
  have h₁ : (Finset.univ : Finset (Fin 2)).powersetCard 1 = {{0}, {1}} := by
    simpa [Fin.univ_succ] using Finset.powersetCard_one (Finset.univ : Finset (Fin 2))
  have h₂ : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {{0, 1}} := by
    simpa [Fin.univ_succ] using Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
  have hp : plusProj 2 = Matrix.vecMulVec (walsh 0) (star (walsh 0)) := by
    rw [plusProj, plus_walsh]
  unfold countProj
  simp_rw [complement_walsh]
  delta walshPair
  fin_cases k <;> ext x y <;>
    simp [h₀, h₁, h₂, hp, Fin.prod_univ_two,
      Fin.sum_univ_succ, Matrix.vecMulVec_apply] <;>
    ring

private lemma count_laws (k : Fin 3) :
    Matrix.trace (copyState 2 2 1 * countProj 2 2 k) =
      (![9 / 16, 3 / 8, 1 / 16] : Fin 3 → ℂ) k ∧
    Matrix.trace (copyState 2 2 2 * countProj 2 2 k) =
      (![1, 0, 0] : Fin 3 → ℂ) k := by
  rw [count_walsh]
  constructor
  · simp_rw [Finset.mul_sum, Matrix.trace_sum, mul_ite, Matrix.mul_zero,
      apply_ite, Matrix.trace_zero, weight_one_law]
    fin_cases k <;> norm_num [Fin.sum_univ_succ]
  · simp_rw [Finset.mul_sum, Matrix.trace_sum, mul_ite, Matrix.mul_zero,
      apply_ite, Matrix.trace_zero, weight_two_law]
    fin_cases k <;> norm_num [Fin.sum_univ_succ]

private lemma count_bound (g : Fin 3 → Bool) :
    successProb 2 2 1 2 (countTest 2 2 g) ≤ 23 / 32 := by
  have h₁₀ : Matrix.trace (copyState 2 2 1 * countProj 2 2 0) = (9 / 16 : ℂ) :=
    (count_laws 0).1
  have h₁₁ : Matrix.trace (copyState 2 2 1 * countProj 2 2 1) = (3 / 8 : ℂ) :=
    (count_laws 1).1
  have h₁₂ : Matrix.trace (copyState 2 2 1 * countProj 2 2 2) = (1 / 16 : ℂ) :=
    (count_laws 2).1
  have h₂₀ : Matrix.trace (copyState 2 2 2 * countProj 2 2 0) = 1 := (count_laws 0).2
  have h₂₁ : Matrix.trace (copyState 2 2 2 * countProj 2 2 1) = 0 := (count_laws 1).2
  have h₂₂ : Matrix.trace (copyState 2 2 2 * countProj 2 2 2) = 0 := (count_laws 2).2
  delta successProb countTest
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, weight_two_trace]
  cases h₀ : g 0 <;> cases h₁ : g 1 <;> cases h₂ : g 2 <;>
    norm_num [Fin.sum_univ_succ, h₀, h₁, h₂, Matrix.mul_add,
      Matrix.trace_add, h₁₀, h₁₁, h₁₂, h₂₀, h₂₁, h₂₂]

/-- The count statistic is insufficient, already for two copies and four addresses. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨g, hg⟩ := h 2 (by norm_num) 2 (by norm_num) 1 2 (by norm_num)
    (by norm_num) witness witness_valid.1 witness_valid.2
  have hb := count_bound g
  rw [witness_success] at hg
  linarith

end D5.S3.Quantum.Tomography.QramCountStatisticInsufficiency
