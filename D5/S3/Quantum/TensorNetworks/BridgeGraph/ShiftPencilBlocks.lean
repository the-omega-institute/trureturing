/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/ShiftPencilBlocks
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: ShiftPencilBlocks for width-three bridge flow. -/

/-
proof_shape: base_of_parameterized: bind-only; consumer: LongReservoir.base_witness
escape_witness: base_of_parameterized: none
proof_shape: pencil_rank_of_le: content
escape_witness: pencil_rank_of_le: ShiftPencilBlocks.rectangular_chain_zero
proof_shape: block_mulVec: bind-only; consumer: ReservoirSchur.widthTwo_kernelEmbedding
escape_witness: block_mulVec: none
proof_shape: pencil_mulVec: bind-only; consumer: ShiftPencilBlocks.antiDiagonal_kernel
escape_witness: pencil_mulVec: none
proof_shape: antiDiagonal_kernel: bind-only; consumer: ReservoirSchur.widthTwo_kernelEmbedding
escape_witness: antiDiagonal_kernel: none
proof_shape: rows_card: bind-only; consumer: ShiftPencilBlocks.witness_of_widthTwo_rank
escape_witness: rows_card: none
proof_shape: cols_card: bind-only; consumer: ShiftPencilBlocks.witness_of_widthTwo_rank
escape_witness: cols_card: none
proof_shape: widthTwo_block_decomposition: bind-only; consumer: ShiftPencilBlocks.widthTwo_rank_sum
escape_witness: widthTwo_block_decomposition: none
proof_shape: witness_of_typed_slices: bind-only; consumer: ShiftPencilBlocks.witness_of_widthTwo_rank
escape_witness: witness_of_typed_slices: none
proof_shape: different_depth_witness: content
escape_witness: different_depth_witness: ShiftPencilBlocks.rectangular_chain_zero
proof_shape: same_depth_kernel_dimension: content
escape_witness: same_depth_kernel_dimension: ShiftPencilBlocks.rectangular_chain_zero
proof_shape: zero_defect_witness: content
escape_witness: zero_defect_witness: ShiftPencilBlocks.rectangular_chain_zero
proof_shape: double_fin_pick: bind-only; consumer: LongReservoir.longCross_SL_short_row
escape_witness: double_fin_pick: none
proof_shape: neg_one_pow_square: bind-only; consumer: LongReservoir.cokernel_long_kernel
escape_witness: neg_one_pow_square: none
proof_shape: short_short_cyclic_schur_rank: content
escape_witness: short_short_cyclic_schur_rank: FloorSelectorCycles.balanced_cycle_zero
proof_shape: long_long_cyclic_schur_rank: content
escape_witness: long_long_cyclic_schur_rank: FloorSelectorCycles.balanced_cycle_zero
proof_shape: matrix_injective_of_rank: bind-only; consumer: LongReservoir.long_long_injective_witness
escape_witness: matrix_injective_of_rank: none
proof_shape: schur_two_equations: bind-only; consumer: LongReservoir.long_reservoir_injective
escape_witness: schur_two_equations: none
admission_basis: escape-witness (pencil_rank_of_le)
Module content mechanism: rectangular_chain_zero: propagation to the pencil boundary.
Direct frozen dependencies: none on the implementation baseline.
Utility: none; symbolic constructions and proofs for arbitrary dimensions,
not bounded enumeration, a checker, numeric reduction, or a certified instance.
Information-escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14762
-/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
open Matrix Module

open D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open Matrix Module
section

private structure PencilData (a b : ℕ) where
  p : ℕ
  alpha : ℕ
  beta : ℕ
  p_pos : 0 < p
  beta_pos : 0 < beta
  left_dim : a = p * alpha + (p + 1) * beta
  right_dim : b = (p + 1) * alpha + (p + 2) * beta

private theorem parameterization (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hba : b < 2 * a) : Nonempty (PencilData a b) := by
  let m := b - a
  let p := (a - 1) / m
  let beta := (a - 1) % m + 1
  let alpha := m - beta
  have hm : 0 < m := by dsimp [m]; omega
  have hma : m < a := by dsimp [m]; omega
  have hrem : (a - 1) % m < m := Nat.mod_lt _ hm
  have hbpos : 0 < beta := by dsimp [beta]; omega
  have hbm : beta ≤ m := by dsimp [beta]; omega
  have ham : alpha + beta = m := Nat.sub_add_cancel hbm
  have hdiv : p * m + beta = a := by
    have h : p * m + (a - 1) % m = a - 1 := by
      dsimp [p]
      simpa only [mul_comm] using Nat.div_add_mod (a - 1) m
    dsimp [beta]
    omega
  have hp : 0 < p := by
    by_contra h
    have hz : p = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, zero_mul, zero_add] at hdiv
    omega
  have hleft : a = p * alpha + (p + 1) * beta := by
    nlinarith [congrArg (fun t => p * t) ham]
  have hright : b = (p + 1) * alpha + (p + 2) * beta := by
    have hmab : m + a = b := by dsimp [m]; omega
    nlinarith [congrArg (fun t => p * t) ham]
  exact ⟨⟨p, alpha, beta, hp, hbpos, hleft, hright⟩⟩

def ParameterizedBaseWitness : Prop :=
  ∀ p q alpha beta gamma delta : ℕ, 0 < p → 0 < q → 0 < beta → 0 < delta →
    RationalWitness
      (p * alpha + (p + 1) * beta) ((p + 1) * alpha + (p + 2) * beta)
      (q * gamma + (q + 1) * delta) ((q + 1) * gamma + (q + 2) * delta)

theorem base_of_parameterized (h : ParameterizedBaseWitness) : BaseWitness := by
  intro a b c d ha hab hba hc hcd hdc
  obtain ⟨⟨p, alpha, beta, hp, hb, he, hf⟩⟩ := parameterization a b ha hab hba
  obtain ⟨⟨q, gamma, delta, hq, hd, hg, hh⟩⟩ := parameterization c d hc hcd hdc
  rw [he, hf, hg, hh]
  exact h p q alpha beta gamma delta hp hq hb hd

end
section

open Matrix Module

def rectExtend {x y : ℕ} (z : Fin x × Fin y → ℚ) (i k : ℕ) : ℚ :=
  if hi : i < x then if hk : k < y then z (⟨i, hi⟩, ⟨k, hk⟩) else 0 else 0

def shift1 (x : ℕ) : Matrix (Fin x) (Fin (x + 1)) ℚ :=
  (1 : Matrix ℕ ℕ ℚ).submatrix (fun i : Fin x => i.val + 1) Fin.val

def pencil (x y : ℕ) : Matrix (Fin x × Fin (y + 1)) (Fin (x + 1) × Fin y) ℚ :=
  kronecker ((rectId x (x + 1))) ((rectId y (y + 1))).transpose +
    kronecker (shift1 x) (shift1 y).transpose

private lemma fin_sum_lookup (n k : ℕ) (z : Fin n → ℚ) :
    (∑ i : Fin n, if i.val = k then z i else 0) =
      if hk : k < n then z ⟨k, hk⟩ else 0 := by
  classical
  by_cases hk : k < n
  · rw [dif_pos hk]
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
    · simp
    · intro i _ hi
      have hn : i.val ≠ k := by intro h; exact hi (Fin.ext h)
      simp [hn]
    · simp
  · rw [dif_neg hk]
    apply Finset.sum_eq_zero
    intro i _
    have hn : i.val ≠ k := by have hi := i.isLt; omega
    simp [hn]

private lemma pencil_entry (x y : ℕ) (r : Fin x × Fin (y + 1))
    (s : Fin (x + 1) × Fin y) :
    pencil x y r s =
      (if r.1.val = s.1.val ∧ r.2.val = s.2.val then 1 else 0) +
      (if r.1.val + 1 = s.1.val ∧ s.2.val + 1 = r.2.val then 1 else 0) := by
  change (if r.1.val = s.1.val then (1 : ℚ) else 0) *
      (if s.2.val = r.2.val then 1 else 0) +
    (if r.1.val + 1 = s.1.val then 1 else 0) *
      (if s.2.val + 1 = r.2.val then 1 else 0) = _
  split_ifs <;> simp_all

private lemma pencil_transpose_mulVec (x y : ℕ) (z : Fin x × Fin (y + 1) → ℚ)
    (s : Fin (x + 1) × Fin y) :
    (pencil x y).transpose.mulVec z s =
      rectExtend z s.1.val s.2.val +
      if 0 < s.1.val then rectExtend z (s.1.val - 1) (s.2.val + 1) else 0 := by
  classical
  change (∑ r : Fin x × Fin (y + 1), pencil x y r s * z r) = _
  simp_rw [pencil_entry, add_mul, ite_mul, one_mul, zero_mul,
    Fintype.sum_prod_type, Finset.sum_add_distrib]
  have hfirst (i : Fin x) :
      (∑ k : Fin (y + 1), if i.val = s.1.val ∧ k.val = s.2.val then z (i, k) else 0) =
      if i.val = s.1.val then z (i, s.2.castSucc) else 0 := by
    by_cases hi : i.val = s.1.val
    · simp only [hi, true_and]
      rw [fin_sum_lookup, dif_pos (by omega)]
      rfl
    · simp [hi]
  have hsecond (i : Fin x) :
      (∑ k : Fin (y + 1), if i.val + 1 = s.1.val ∧ s.2.val + 1 = k.val then
        z (i, k) else 0) =
      if i.val + 1 = s.1.val then z (i, s.2.succ) else 0 := by
    by_cases hi : i.val + 1 = s.1.val
    · simp only [hi, true_and]
      have he (k : Fin (y + 1)) : s.2.val + 1 = k.val ↔ k.val = s.2.val + 1 := eq_comm
      simp_rw [he]
      rw [fin_sum_lookup, dif_pos (by omega)]
      rfl
    · simp [hi]
  simp_rw [hfirst, hsecond]
  rw [fin_sum_lookup]
  have hs : s.2.val < y + 1 := by omega
  congr 1
  · by_cases hi : s.1.val < x
    · simp only [rectExtend, dif_pos hi, dif_pos hs]
      rfl
    · simp [rectExtend, hi]
  · by_cases hpos : 0 < s.1.val
    · rw [if_pos hpos]
      have he (i : Fin x) : i.val + 1 = s.1.val ↔ i.val = s.1.val - 1 := by omega
      simp_rw [he]
      rw [fin_sum_lookup]
      have hj : s.2.val + 1 < y + 1 := by have h := s.2.isLt; omega
      by_cases hi : s.1.val - 1 < x
      · simp only [rectExtend, dif_pos hi, dif_pos hj]
        rfl
      · simp [rectExtend, hi]
    · rw [if_neg hpos]
      apply Finset.sum_eq_zero
      intro i _
      have he : ¬ i.val + 1 = s.1.val := by omega
      simp [he]

private theorem rectangular_chain_zero (x y : ℕ) (hxy : x ≤ y) (z : ℕ → ℕ → ℚ)
    (htop : ∀ k, k < y → z 0 k = 0)
    (hbottom : ∀ i k, i + 1 = x → k < y → z i (k + 1) = 0)
    (hstep : ∀ i k, i + 1 < x → k < y → z (i + 1) k + z i (k + 1) = 0) :
    ∀ i k, i < x → k ≤ y → z i k = 0 := by
  have hlow : ∀ i k, i < x → i + k < y → z i k = 0 := by
    intro i
    induction i with
    | zero => intro k _ hk; exact htop k (by omega)
    | succ i ih =>
      intro k hi hk
      have hv := ih (k + 1) (by omega) (by omega)
      have he := hstep i k hi (by omega)
      simpa [hv] using he
  have hhigh : ∀ dist i k, i + dist + 1 = x → dist < k → k ≤ y → z i k = 0 := by
    intro dist
    induction dist with
    | zero =>
      intro i k hi hk hky
      have he := hbottom i (k - 1) (by omega) (by omega)
      have hh : k - 1 + 1 = k := by omega
      simpa [hh] using he
    | succ dist ih =>
      intro i k hi hk hky
      have hv := ih (i + 1) (k - 1) (by omega) (by omega) (by omega)
      have he := hstep i (k - 1) (by omega) (by omega)
      have hh : k - 1 + 1 = k := by omega
      rw [hv, zero_add, hh] at he
      exact he
  intro i k hi hk
  by_cases hl : i + k < y
  · exact hlow i k hi hl
  · exact hhigh (x - (i + 1)) i k (by omega) (by omega) hk

private theorem pencil_transpose_injective (x y : ℕ) (hxy : x ≤ y) :
    Function.Injective (pencil x y).transpose.mulVecLin := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change (pencil x y).transpose.mulVec z = 0 at hz
  let f := rectExtend z
  have eqn (i j : ℕ) (hi : i ≤ x) (hj : j < y) :
      f i j + (if 0 < i then f (i - 1) (j + 1) else 0) = 0 := by
    have h := congrFun hz (⟨i, by omega⟩, ⟨j, hj⟩)
    simpa only [pencil_transpose_mulVec, Pi.zero_apply] using h
  have htop : ∀ k, k < y → f 0 k = 0 := by
    intro k hk
    simpa using eqn 0 k (by omega) hk
  have hbottom : ∀ i k, i + 1 = x → k < y → f i (k + 1) = 0 := by
    intro i k hi hk
    have h := eqn (i + 1) k (by omega) hk
    have ho : f (i + 1) k = 0 := by simp [f, rectExtend, hi]
    simpa [ho] using h
  have hstep : ∀ i k, i + 1 < x → k < y → f (i + 1) k + f i (k + 1) = 0 := by
    intro i k hi hk
    simpa using eqn (i + 1) k (by omega) hk
  funext r
  have h := rectangular_chain_zero x y hxy f htop hbottom hstep r.1.val r.2.val
    r.1.isLt (by have hh := r.2.isLt; omega)
  simpa [f, rectExtend, r.1.isLt, r.2.isLt] using h

theorem pencil_rank_of_le (x y : ℕ) (hxy : x ≤ y) :
    (pencil x y).rank = x * (y + 1) := by
  rw [← Matrix.rank_transpose, Matrix.rank,
    LinearMap.finrank_range_of_inj (pencil_transpose_injective x y hxy)]
  simp

private theorem pencil_transpose_swap (x y : ℕ) :
    (pencil x y).transpose =
      (pencil y x).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
  ext i j
  change (rectId x (x + 1)) j.1 i.1 * (rectId y (y + 1)) i.2 j.2 +
      shift1 x j.1 i.1 * shift1 y i.2 j.2 =
    (rectId y (y + 1)) i.2 j.2 * (rectId x (x + 1)) j.1 i.1 +
      shift1 y i.2 j.2 * shift1 x j.1 i.1
  simp only [mul_comm]

private theorem pencil_rank_of_ge (x y : ℕ) (hyx : y ≤ x) :
    (pencil x y).rank = (x + 1) * y := by
  rw [← Matrix.rank_transpose, pencil_transpose_swap, Matrix.rank_submatrix,
    pencil_rank_of_le y x hyx]
  exact mul_comm _ _

end
section

open Matrix Module

section
variable {m n r s : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s]

end

end
section

open Matrix Module

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m n : ι → Type*} [∀ i, Fintype (m i)] [∀ i, Fintype (n i)]

lemma block_mulVec (A : ∀ i, Matrix (m i) (n i) ℚ)
    (z : (Σ i, n i) → ℚ) (i : ι) (j : m i) :
    (blockDiagonal' A).mulVec z ⟨i, j⟩ = (A i).mulVec (fun k => z ⟨i, k⟩) j := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro k _ hki
    apply Finset.sum_eq_zero
    intro l _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hki), zero_mul]
  · simp

private noncomputable def blockKernelEquiv (A : ∀ i, Matrix (m i) (n i) ℚ) :
    LinearMap.ker (blockDiagonal' A).mulVecLin ≃ₗ[ℚ]
      ∀ i, LinearMap.ker (A i).mulVecLin where
  toFun z i := ⟨fun k => z.val ⟨i, k⟩, by
    have h := z.property
    change (blockDiagonal' A).mulVec z.val = 0 at h
    change (A i).mulVec (fun k => z.val ⟨i, k⟩) = 0
    funext j
    simpa only [block_mulVec, Pi.zero_apply] using congrFun h ⟨i, j⟩⟩
  invFun z := ⟨fun i => (z i.1).val i.2, by
    change (blockDiagonal' A).mulVec _ = 0
    funext ⟨i, j⟩
    have h := (z i).property
    change (A i).mulVec (z i).val = 0 at h
    simpa only [block_mulVec, Pi.zero_apply] using congrFun h j⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by funext i; apply Subtype.ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem block_rank (A : ∀ i, Matrix (m i) (n i) ℚ) :
    (blockDiagonal' A).rank = ∑ i, (A i).rank := by
  have ht := (blockDiagonal' A).mulVecLin.finrank_range_add_finrank_ker
  have hk : finrank ℚ (LinearMap.ker (blockDiagonal' A).mulVecLin) =
      ∑ i, finrank ℚ (LinearMap.ker (A i).mulVecLin) :=
    (blockKernelEquiv A).finrank_eq.trans (Module.finrank_pi_fintype ℚ)
  rw [hk, Module.finrank_pi, Fintype.card_sigma] at ht
  have hs : ∑ i, ((A i).rank + finrank ℚ (LinearMap.ker (A i).mulVecLin)) =
      ∑ i, Fintype.card (n i) := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Matrix.rank, Module.finrank_pi] using (A i).mulVecLin.finrank_range_add_finrank_ker
  rw [Finset.sum_add_distrib] at hs
  dsimp [Matrix.rank] at hs ⊢
  omega
end

def tensorBlockEquiv {ι κ : Type*} (m : ι → Type*) (n : κ → Type*) :
    ((Σ i, m i) × (Σ j, n j)) ≃ (Σ t : ι × κ, m t.1 × n t.2) :=
  (Equiv.sigmaProdDistrib m (Σ j, n j)).trans
    ((Equiv.sigmaCongrRight fun i =>
      (Equiv.prodComm (m i) (Σ j, n j)).trans
        ((Equiv.sigmaProdDistrib n (m i)).trans
          (Equiv.sigmaCongrRight fun j => Equiv.prodComm (n j) (m i)))).trans
      Equiv.sigmaAssocProd.symm)

private theorem tensor_block_diagonal {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {m n : ι → Type*} {r s : κ → Type*}
    (A : ∀ i, Matrix (m i) (n i) ℚ) (B : ∀ j, Matrix (r j) (s j) ℚ) :
    kronecker (blockDiagonal' A) (blockDiagonal' B) =
      (blockDiagonal' (fun t : ι × κ => kronecker (A t.1) (B t.2))).submatrix
        (tensorBlockEquiv m r) (tensorBlockEquiv n s) := by
  classical
  ext ⟨⟨i, a⟩, ⟨j, b⟩⟩ ⟨⟨k, c⟩, ⟨l, d⟩⟩
  change blockDiagonal' A ⟨i, a⟩ ⟨k, c⟩ * blockDiagonal' B ⟨j, b⟩ ⟨l, d⟩ =
    blockDiagonal' (fun t : ι × κ => kronecker (A t.1) (B t.2))
      ⟨(i, j), (a, b)⟩ ⟨(k, l), (c, d)⟩
  by_cases hi : i = k
  · subst k
    by_cases hj : j = l
    · subst l
      simp [tensorBlockEquiv, Matrix.kronecker, Matrix.kroneckerMap]
    · have hpair : (i, j) ≠ (i, l) := by intro h; exact hj (congrArg Prod.snd h)
      simp [tensorBlockEquiv, Matrix.kronecker, Matrix.kroneckerMap,
        blockDiagonal'_apply_ne _ _ _ hj, blockDiagonal'_apply_ne _ _ _ hpair]
  · have hpair : (i, j) ≠ (k, l) := by intro h; exact hi (congrArg Prod.fst h)
    simp [tensorBlockEquiv, Matrix.kronecker, Matrix.kroneckerMap,
      blockDiagonal'_apply_ne _ _ _ hi, blockDiagonal'_apply_ne _ _ _ hpair]

end
section

open Matrix Module

private lemma rectExtend_swap {x y : ℕ} (u : Fin x × Fin y → ℚ) (i j : ℕ) :
    rectExtend (fun k : Fin y × Fin x => u (k.2, k.1)) i j = rectExtend u j i := by
  by_cases hi : i < y <;> by_cases hj : j < x <;> simp [rectExtend, hi, hj]

lemma pencil_mulVec (x y : ℕ) (u : Fin (x + 1) × Fin y → ℚ)
    (r : Fin x × Fin (y + 1)) :
    (pencil x y).mulVec u r = rectExtend u r.1.val r.2.val +
      if 0 < r.2.val then rectExtend u (r.1.val + 1) (r.2.val - 1) else 0 := by
  have h := pencil_transpose_mulVec y x (fun k => u (k.2, k.1)) (r.2, r.1)
  rw [pencil_transpose_swap, Matrix.submatrix_mulVec_equiv] at h
  change (pencil x y).mulVec u r = _ at h
  simp only [rectExtend_swap] at h
  exact h

def antiDiagonal (p : ℕ) : Fin (p + 1) × Fin (p + 1) → ℚ :=
  fun k => if k.1.val + k.2.val = p then (-1) ^ k.1.val else 0

private lemma antiDiagonal_extend (p i j : ℕ) :
    rectExtend (antiDiagonal p) i j = if i + j = p then (-1 : ℚ) ^ i else 0 := by
  by_cases hi : i < p + 1 <;> by_cases hj : j < p + 1
  · simp [rectExtend, antiDiagonal, hi, hj]
  · have hn : ¬ i + j = p := by omega
    simp [rectExtend, hi, hj, hn]
  · have hn : ¬ i + j = p := by omega
    simp [rectExtend, hi, hj, hn]
  · have hn : ¬ i + j = p := by omega
    simp [rectExtend, hi, hj, hn]

theorem antiDiagonal_kernel (p : ℕ) : (pencil p (p + 1)).mulVec (antiDiagonal p) = 0 := by
  funext r
  rw [pencil_mulVec, antiDiagonal_extend]
  by_cases hk : 0 < r.2.val
  · rw [if_pos hk, antiDiagonal_extend]
    have hh : r.1.val + 1 + (r.2.val - 1) = p ↔ r.1.val + r.2.val = p := by omega
    simp only [hh]
    by_cases hd : r.1.val + r.2.val = p
    · simp [hd, pow_succ]
    · simp [hd]
  · have hi := r.1.isLt
    have hd : ¬ r.1.val + r.2.val = p := by omega
    simp [hk, hd]

end
section

open Matrix Module

def blockLength (p alpha beta : ℕ) : (Fin alpha ⊕ Fin beta) → ℕ := Sum.elim (fun _ => p) (fun _ => p + 1)

def leftDim (p alpha beta : ℕ) := p * alpha + (p + 1) * beta
def rightDim (p alpha beta : ℕ) := (p + 1) * alpha + (p + 2) * beta

lemma rows_card (p alpha beta : ℕ) : Fintype.card ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t))) = leftDim p alpha beta := by
  change Fintype.card (Sigma (fun t : Fin alpha ⊕ Fin beta => Fin (blockLength p alpha beta t))) = _
  rw [Fintype.card_sigma]
  simp [Fintype.sum_sum_type, blockLength, leftDim, mul_comm]

lemma cols_card (p alpha beta : ℕ) : Fintype.card ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1))) = rightDim p alpha beta := by
  change Fintype.card (Sigma (fun t : Fin alpha ⊕ Fin beta => Fin (blockLength p alpha beta t + 1))) = _
  rw [Fintype.card_sigma]
  simp [Fintype.sum_sum_type, blockLength, rightDim, mul_comm]

def arrow0 (p alpha beta : ℕ) : Matrix ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t))) ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1))) ℚ :=
  blockDiagonal' (fun t => (rectId (blockLength p alpha beta t) (blockLength p alpha beta t + 1)))

def arrow1 (p alpha beta : ℕ) : Matrix ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t))) ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1))) ℚ :=
  blockDiagonal' (fun t => shift1 (blockLength p alpha beta t))

def widthTwoMatrix (p q alpha beta gamma delta : ℕ) :
    Matrix ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength q gamma delta t + 1)))
      ((Σ t : Fin alpha ⊕ Fin beta, Fin (blockLength p alpha beta t + 1)) × (Σ t : Fin gamma ⊕ Fin delta, Fin (blockLength q gamma delta t))) ℚ :=
  kronecker (arrow0 p alpha beta) (arrow0 q gamma delta).transpose +
    kronecker (arrow1 p alpha beta) (arrow1 q gamma delta).transpose

lemma widthTwo_block_decomposition (p q alpha beta gamma delta : ℕ) :
    widthTwoMatrix p q alpha beta gamma delta =
      (blockDiagonal' (fun t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta) =>
        pencil (blockLength p alpha beta t.1) (blockLength q gamma delta t.2))).submatrix
      (tensorBlockEquiv (fun t => Fin (blockLength p alpha beta t))
        (fun t => Fin (blockLength q gamma delta t + 1)))
      (tensorBlockEquiv (fun t => Fin (blockLength p alpha beta t + 1))
        (fun t => Fin (blockLength q gamma delta t))) := by
  rw [widthTwoMatrix, arrow0, arrow0, arrow1, arrow1,
    blockDiagonal'_transpose, blockDiagonal'_transpose,
    tensor_block_diagonal, tensor_block_diagonal]
  have hb : blockDiagonal' (fun t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta) =>
      pencil (blockLength p alpha beta t.1) (blockLength q gamma delta t.2)) =
    blockDiagonal' (fun t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta) =>
      kronecker ((rectId (blockLength p alpha beta t.1) (blockLength p alpha beta t.1 + 1)))
        ((rectId (blockLength q gamma delta t.2) (blockLength q gamma delta t.2 + 1))).transpose) +
    blockDiagonal' (fun t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta) =>
      kronecker (shift1 (blockLength p alpha beta t.1))
        (shift1 (blockLength q gamma delta t.2)).transpose) :=
      blockDiagonal'_add _ _
  rw [hb]
  rfl

private theorem widthTwo_rank_sum (p q alpha beta gamma delta : ℕ) :
    (widthTwoMatrix p q alpha beta gamma delta).rank =
      ∑ t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta),
        (pencil (blockLength p alpha beta t.1) (blockLength q gamma delta t.2)).rank := by
  rw [widthTwo_block_decomposition, Matrix.rank_submatrix, block_rank]

theorem witness_of_typed_slices {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    {a b c d : ℕ} (hi : Fintype.card I = a) (hj : Fintype.card J = b)
    (hk : Fintype.card K = c) (hl : Fintype.card L = d)
    (M : Fin 3 → Matrix I J ℚ) (N : Fin 3 → Matrix L K ℚ)
    (hr : (∑ r : Fin 3, kronecker (M r) (N r)).rank = min (a * d) (b * c)) :
    RationalWitness a b c d := by
  classical
  let ei := (Fintype.equivFinOfCardEq hi).symm
  let ej := (Fintype.equivFinOfCardEq hj).symm
  let ek := (Fintype.equivFinOfCardEq hk).symm
  let el := (Fintype.equivFinOfCardEq hl).symm
  let M' : Fin 3 → Matrix (Fin a) (Fin b) ℚ := fun r => (M r).submatrix ei ej
  let N' : Fin 3 → Matrix (Fin d) (Fin c) ℚ := fun r => (N r).submatrix el ek
  refine ⟨M', N', ?_⟩
  have heq : flow M' N' =
      (∑ r : Fin 3, kronecker (M r) (N r)).submatrix
        (Equiv.prodCongr ei el) (Equiv.prodCongr ej ek) := by
    ext i j
    rfl
  rw [heq, Matrix.rank_submatrix, hr]

private lemma typed_two_slice_flow {I J K L : Type*} (A B : Matrix I J ℚ) (C D : Matrix L K ℚ) :
    (∑ r : Fin 3, kronecker ((threeSlices A B 0) r) ((threeSlices C D 0) r)) =
      kronecker A C + kronecker B D := by
  rw [typed_three_slice_flow]
  ext i j
  simp [Matrix.kronecker_apply]

private theorem witness_of_widthTwo_rank (p q alpha beta gamma delta : ℕ)
    (hr : (widthTwoMatrix p q alpha beta gamma delta).rank =
      min (leftDim p alpha beta * rightDim q gamma delta)
        (rightDim p alpha beta * leftDim q gamma delta)) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim q gamma delta) (rightDim q gamma delta) := by
  apply witness_of_typed_slices (rows_card _ _ _) (cols_card _ _ _)
    (rows_card _ _ _) (cols_card _ _ _)
    ((threeSlices (arrow0 p alpha beta) (arrow1 p alpha beta) 0))
    ((threeSlices (arrow0 q gamma delta).transpose (arrow1 q gamma delta).transpose 0))
  rw [typed_two_slice_flow]
  exact hr

private theorem widthTwo_rank_of_lt (p q alpha beta gamma delta : ℕ) (hpq : p < q) :
    (widthTwoMatrix p q alpha beta gamma delta).rank =
      leftDim p alpha beta * rightDim q gamma delta := by
  rw [widthTwo_rank_sum]
  calc
    (∑ t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta),
      (pencil (blockLength p alpha beta t.1) (blockLength q gamma delta t.2)).rank) =
        ∑ t : (Fin alpha ⊕ Fin beta) × (Fin gamma ⊕ Fin delta),
          blockLength p alpha beta t.1 * (blockLength q gamma delta t.2 + 1) := by
      apply Finset.sum_congr rfl
      intro t _
      apply pencil_rank_of_le
      rcases t with ⟨i, j⟩
      cases i <;> cases j <;> dsimp [blockLength] <;> omega
    _ = leftDim p alpha beta * rightDim q gamma delta := by
      simp [Fintype.sum_prod_type, Fintype.sum_sum_type, blockLength, leftDim, rightDim]
      ring

theorem different_depth_witness (p q alpha beta gamma delta : ℕ) (hpq : p ≠ q) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim q gamma delta) (rightDim q gamma delta) := by
  rcases lt_or_gt_of_ne hpq with h | h
  · apply witness_of_widthTwo_rank
    have hr := widthTwo_rank_of_lt p q alpha beta gamma delta h
    have hu := (widthTwoMatrix p q alpha beta gamma delta).rank_le_card_width
    simp only [Fintype.card_prod, cols_card, rows_card] at hu
    rw [hr] at hu
    rw [hr, min_eq_left hu]
  · apply witness_swap
    apply witness_of_widthTwo_rank
    have hr := widthTwo_rank_of_lt q p gamma delta alpha beta h
    have hu := (widthTwoMatrix q p gamma delta alpha beta).rank_le_card_width
    simp only [Fintype.card_prod, cols_card, rows_card] at hu
    rw [hr] at hu
    rw [hr, min_eq_left hu]

private def baseRank (p alpha beta gamma delta : ℕ) :=
  alpha * gamma * (p * (p + 1)) + alpha * delta * (p * (p + 2)) +
    beta * gamma * (p * (p + 2)) + beta * delta * ((p + 1) * (p + 2))

private theorem same_depth_rank (p alpha beta gamma delta : ℕ) :
    (widthTwoMatrix p p alpha beta gamma delta).rank = baseRank p alpha beta gamma delta := by
  have hss := pencil_rank_of_le p p le_rfl
  have hsl := pencil_rank_of_le p (p + 1) (by omega)
  have hls := pencil_rank_of_ge (p + 1) p (by omega)
  have hll := pencil_rank_of_le (p + 1) (p + 1) le_rfl
  rw [widthTwo_rank_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, blockLength, Sum.elim_inl,
    Sum.elim_inr, hss, hsl, hls, hll, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, baseRank]
  simp only [Nat.cast_id]
  ring

private theorem same_depth_dimension_identities (p alpha beta gamma delta : ℕ) :
    baseRank p alpha beta gamma delta + beta * gamma =
      leftDim p alpha beta * rightDim p gamma delta ∧
    baseRank p alpha beta gamma delta + alpha * delta =
      rightDim p alpha beta * leftDim p gamma delta := by
  constructor <;> dsimp [baseRank, leftDim, rightDim] <;> ring

theorem same_depth_kernel_dimension (p alpha beta gamma delta : ℕ) :
    finrank ℚ (LinearMap.ker (widthTwoMatrix p p alpha beta gamma delta).mulVecLin) =
      alpha * delta := by
  have h := (widthTwoMatrix p p alpha beta gamma delta).mulVecLin.finrank_range_add_finrank_ker
  change (widthTwoMatrix p p alpha beta gamma delta).rank + _ = _ at h
  simp only [Module.finrank_pi, Fintype.card_prod, cols_card, rows_card,
    same_depth_rank] at h
  have hd := (same_depth_dimension_identities p alpha beta gamma delta).2
  omega

theorem zero_defect_witness (p alpha beta gamma delta : ℕ)
    (hzero : alpha * delta = 0 ∨ beta * gamma = 0) :
    RationalWitness (leftDim p alpha beta) (rightDim p alpha beta)
      (leftDim p gamma delta) (rightDim p gamma delta) := by
  apply witness_of_widthTwo_rank
  rw [same_depth_rank]
  obtain ⟨ht, hs⟩ := same_depth_dimension_identities p alpha beta gamma delta
  rcases hzero with hk | hc
  · rw [hk, add_zero] at hs
    rw [← hs, min_eq_right (by omega)]
  · rw [hc, add_zero] at ht
    rw [← ht, min_eq_left (by omega)]

end
section

lemma double_fin_pick (n m r s : ℕ) (a b : ℚ) (u : Fin n × Fin m → ℚ) :
    (∑ i : Fin n, ∑ j : Fin m,
      (if i.val = r then a else 0) * (if j.val = s then b else 0) * u (i, j)) =
      a * b * rectExtend u r s := by
  classical
  by_cases hr : r < n <;> by_cases hs : s < m
  · have hi (i : Fin n) : i.val = r ↔ i = ⟨r, hr⟩ := by simp only [Fin.ext_iff]
    have hj (j : Fin m) : j.val = s ↔ j = ⟨s, hs⟩ := by simp only [Fin.ext_iff]
    simp_rw [hi, hj]
    simp [ite_mul, mul_ite, rectExtend, hr, hs]
  · have hj (j : Fin m) : j.val ≠ s := by have h := j.isLt; omega
    simp [hj, rectExtend, hr, hs]
  · have hi (i : Fin n) : i.val ≠ r := by have h := i.isLt; omega
    simp [hi, rectExtend, hr, hs]
  · have hi (i : Fin n) : i.val ≠ r := by have h := i.isLt; omega
    simp [hi, rectExtend, hr, hs]

lemma neg_one_pow_square (n : ℕ) : ((-1 : ℚ) ^ n) * ((-1 : ℚ) ^ n) = 1 := by
  rw [← pow_two, ← pow_mul, mul_comm n 2, pow_mul]
  norm_num

end
section

open Matrix Module

private theorem short_short_schur_identity (A B G D : ℕ)
    (X : Matrix (Fin A) (Fin A) ℚ) (Y : Matrix (Fin G) (Fin G) ℚ)
    (BM : Matrix (Fin B) (Fin A) ℚ) (DM : Matrix (Fin G) (Fin D) ℚ)
    (κ : ℚ) (hR : IsUnit (1 + kronecker X Y)) :
    (κ + 1) • kronecker BM DM -
      kronecker BM Y * (1 + kronecker X Y)⁻¹ * kronecker X DM =
    κ • kronecker BM DM +
      kronecker BM (1 : Matrix (Fin G) (Fin G) ℚ) *
        (1 + kronecker X Y)⁻¹ * kronecker (1 : Matrix (Fin A) (Fin A) ℚ) DM := by
  let R : Matrix (Fin A × Fin G) (Fin A × Fin G) ℚ := 1 + kronecker X Y
  let H := kronecker (1 : Matrix (Fin A) (Fin A) ℚ) Y
  let J := kronecker X (1 : Matrix (Fin G) (Fin G) ℚ)
  let L := kronecker BM (1 : Matrix (Fin G) (Fin G) ℚ)
  let T := kronecker (1 : Matrix (Fin A) (Fin A) ℚ) DM
  have hR' : IsUnit R := hR
  letI := hR'.invertible
  have hcomm : Commute H R := by
    change H * R = R * H
    dsimp [H, R]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hi : H * R⁻¹ = R⁻¹ * H := by
    have h := hcomm.invOf_right
    rw [invOf_eq_nonsing_inv] at h
    exact h
  have hHJ : H * J = kronecker X Y := by
    dsimp [H, J]
    rw [← Matrix.mul_kronecker_mul]
    simp
  have hLH : L * H = kronecker BM Y := by
    dsimp [L, H]
    rw [← Matrix.mul_kronecker_mul]
    simp
  have hJT : J * T = kronecker X DM := by
    dsimp [J, T]
    rw [← Matrix.mul_kronecker_mul]
    simp
  have hLT : L * T = kronecker BM DM := by
    dsimp [L, T]
    rw [← Matrix.mul_kronecker_mul]
    simp
  have hI : R⁻¹ * kronecker X Y = 1 - R⁻¹ := by
    have hh : kronecker X Y = R - 1 := by dsimp [R]; abel
    rw [hh, Matrix.mul_sub, Matrix.nonsing_inv_mul R ((isUnit_iff_isUnit_det _).mp hR'),
      Matrix.mul_one]
  have hcorr : kronecker BM Y * R⁻¹ * kronecker X DM = L * (1 - R⁻¹) * T := by
    rw [← hLH, ← hJT]
    calc
      L * H * R⁻¹ * (J * T) = L * (H * R⁻¹) * J * T := by simp only [Matrix.mul_assoc]
      _ = L * (R⁻¹ * H) * J * T := by rw [hi]
      _ = L * (R⁻¹ * (H * J)) * T := by simp only [Matrix.mul_assoc]
      _ = L * (1 - R⁻¹) * T := by rw [hHJ, hI]
  change (κ + 1) • kronecker BM DM - kronecker BM Y * R⁻¹ * kronecker X DM =
    κ • kronecker BM DM + L * R⁻¹ * T
  rw [hcorr, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLT,
    add_smul, one_smul]
  abel

theorem short_short_cyclic_schur_rank (A B G D p : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (hp : 0 < p) :
    (((p : ℚ) + 1) • kronecker (rowSelector A B) ((rowSelector G D).transpose) -
      kronecker (rowSelector A B) (forwardHalf G) * (reservoir A G)⁻¹ *
        kronecker (-backward A) ((rowSelector G D).transpose)).rank = min (A * D) (B * G) := by
  have hR := (cyclic_resolvent_lemma A B G D hB hBA hD hDG (p : ℚ) (by exact_mod_cast hp)).1
  have h := short_short_schur_identity A B G D (-backward A) (forwardHalf G)
    (rowSelector A B) ((rowSelector G D).transpose) (p : ℚ) hR
  dsimp only [reservoir]
  rw [h]
  exact schur_rank A B G D hB hBA hD hDG (p : ℚ) (by exact_mod_cast hp)

theorem long_long_cyclic_schur_rank (A B G D p : ℕ) (hA : 0 < A) (hAB : A ≤ B)
    (hG : 0 < G) (hGD : G ≤ D) (hp : 0 < p) :
    (((p : ℚ) + 1) • kronecker (rowSelector B A).transpose (rowSelector D G) -
      kronecker (-backward B).transpose (rowSelector D G) *
        (1 + kronecker (-backward B).transpose (forwardHalf D).transpose)⁻¹ *
          kronecker (rowSelector B A).transpose (forwardHalf D).transpose).rank =
        min (A * D) (B * G) := by
  have h := short_short_cyclic_schur_rank B A D G p hA hAB hG hGD hp
  rw [← Matrix.rank_transpose]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_add, Matrix.transpose_nonsing_inv,
    Matrix.transpose_transpose, Matrix.transpose_one, reservoir, Matrix.mul_assoc]
  simp only [reservoir, Matrix.mul_assoc] at h
  convert h using 1
  · congr 1
  · exact min_comm _ _

end
section

open Matrix Module

lemma matrix_injective_of_rank {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℚ) (hA : A.rank = Fintype.card n) : Function.Injective A.mulVecLin := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + _ = _ at h
  rw [hA, Module.finrank_pi] at h
  omega

lemma schur_two_equations {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (R : Matrix m m ℚ) (T : Matrix m n ℚ) (L : Matrix k m ℚ) (H : Matrix k n ℚ)
    (hR : IsUnit R) (hS : Function.Injective (H-L*R⁻¹*T).mulVec)
    (v : m → ℚ) (w : n → ℚ)
    (hr : R.mulVec v + T.mulVec w = 0) (he : L.mulVec v + H.mulVec w = 0) :
    v = 0 ∧ w = 0 := by
  have hr' : R.mulVec v = -(T.mulVec w) := eq_neg_of_add_eq_zero_left hr
  have hv : v = -((R⁻¹*T).mulVec w) := by
    have h := congrArg R⁻¹.mulVec hr'
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR), Matrix.one_mulVec] at h
    exact h
  have hw : (H-L*R⁻¹*T).mulVec w = 0 := by
    rw [hv, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at he
    rw [Matrix.sub_mulVec]
    exact sub_eq_zero.mpr (eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using he))
  have hw0 : w = 0 := hS (by simpa using hw)
  rw [hw0] at hr
  simp only [Matrix.mulVec_zero, add_zero] at hr
  exact ⟨Matrix.mulVec_injective_of_isUnit hR (by simpa using hr),hw0⟩

end


end D5.S3.Quantum.TensorNetworks.BridgeGraph.ShiftPencilBlocks
