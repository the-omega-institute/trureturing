/- GID: D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.claim; result=D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.result; claim=D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.claim
   digest: Weighted multicopy designs and qubit discrimination beyond the design construction. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Tactic.FinCases

set_option linter.style.longLine false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (IsPure)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (success)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

namespace D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation

def tensorPow {d : ℕ} (k : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ :=
  fun i j => ∏ t : Fin k, A (finFunctionFinEquiv.symm i t) (finFunctionFinEquiv.symm j t)

def permOp (d k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ := by
  classical
  exact fun i j => if finFunctionFinEquiv.symm i = finFunctionFinEquiv.symm j ∘ σ then 1 else 0

def PiSym (d k : ℕ) : Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ :=
  (k.factorial : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), permOp d k σ

def IsWeightedDesign {d N : ℕ} (k : ℕ) (ρ : Fin N → DensityState (Fin d))
    (p : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ i, 0 < p i → IsPure (ρ i)) ∧
    ∑ i, (p i : ℂ) • tensorPow k (ρ i).1 = (trace (PiSym d k))⁻¹ • PiSym d k

def DesignExists (d k N : ℕ) : Prop :=
  ∃ ρ : Fin N → DensityState (Fin d), ∃ p : Fin N → ℝ, IsWeightedDesign k ρ p

def Nprime (d k : ℕ) : ℕ := sInf {N : ℕ | DesignExists d k N}

def maxMixed (d : ℕ) (hd : 0 < d) : DensityState (Fin d) := by
  refine ⟨CStarMatrix.ofMatrix ((d : ℝ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg d))).nonneg)
  · change trace ((d : ℝ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) = 1
    simp [trace_smul, hd.ne', Complex.real_smul]

def adjoin {d N : ℕ} (ρ : Fin N → DensityState (Fin d)) (hd : 0 < d) :
    Fin (N + 1) → DensityState (Fin d) :=
  Fin.lastCases (maxMixed d hd) ρ

def Discr {d N : ℕ} (k : ℕ) (ρ : Fin N → DensityState (Fin d)) : ℝ :=
  sSup {r : ℝ | ∃ E : Fin N → Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ,
    IsPOVM E ∧ r = success (fun i => tensorPow k (ρ i).1) E}

def claim : Prop :=
  ∀ d k : ℕ, ∀ hd : 0 < d, 0 < k →
    ∀ (ρ : Fin (Nprime d k) → DensityState (Fin d)) (p : Fin (Nprime d k) → ℝ),
      IsWeightedDesign k ρ p → ∀ E : Fin (Nprime d k + 1) → DensityState (Fin d),
        Discr k E ≤ Discr k (adjoin ρ hd)

-- In the ordered three-qubit basis, the rightmost tensor factor is the low bit.
private def bit (i : Fin 8) (t : Fin 3) : Fin 2 := finFunctionFinEquiv.symm i t

private theorem tensor23 (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 8) :
    tensorPow 3 A i j = A (bit i 2) (bit j 2) * A (bit i 1) (bit j 1) *
      A (bit i 0) (bit j 0) := by
  simp only [tensorPow, bit, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.succ_zero_eq_one, Fin.reduceSucc]
  ring

private def weight : Fin 8 → ℕ := ![0,1,1,2,1,2,2,3]

private def P8 : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if weight i = weight j then
    if weight i = 0 ∨ weight i = 3 then 1 else 1 / 3 else 0

set_option maxHeartbeats 4000000 in
-- Kernel reduction enumerates all permutations of the three-element type.
private theorem perms3 : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
    {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
      Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by
  decide

private theorem bit_table (i : Fin 8) (t : Fin 3) : bit i t =
    (![![0,0,0],![1,0,0],![0,1,0],![1,1,0],![0,0,1],![1,0,1],![0,1,1],![1,1,1]] :
      Fin 8 → Fin 3 → Fin 2) i t := by
  fin_cases i <;> fin_cases t <;> rfl

private theorem permOp23 (σ : Equiv.Perm (Fin 3)) (i j : Fin 8) :
    permOp 2 3 σ i j = if (fun t => bit i t) = (fun t => bit j (σ t)) then 1 else 0 := rfl

private theorem sum_perms3 (f : Equiv.Perm (Fin 3) → ℂ) :
    ∑ σ, f σ = f 1 + f (Equiv.swap 0 1) + f (Equiv.swap 0 2) +
      f (Equiv.swap 1 2) + f (Equiv.swap 0 1 * Equiv.swap 1 2) +
      f (Equiv.swap 1 2 * Equiv.swap 0 1) := by
  rw [perms3]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  ring

set_option maxHeartbeats 2000000 in
-- The symmetriser certificate checks all 64 entries.
private theorem piSym23 : PiSym 2 3 = P8 := by
  classical
  unfold PiSym
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  rw [sum_perms3]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hb : (0 : Fin 2) ≠ 1 := by decide
  fin_cases i <;> fin_cases j <;>
    norm_num [permOp23, bit_table, P8, weight, Matrix.smul_apply, Matrix.sum_apply,
      Function.comp_def, Matrix.cons_val_two,
      funext_iff, Fin.forall_fin_succ, Equiv.swap_apply_def, Equiv.Perm.mul_apply, Fin.reduceSucc,
      h01, h02, h12, hb, Ne.symm h01, Ne.symm h02, Ne.symm h12, Ne.symm hb]

private theorem trace_P8 : trace P8 = 4 := by
  change ∑ i, P8 i i = 4
  norm_num [P8, weight, Fin.sum_univ_succ]

private def octVec : Fin 6 → Fin 2 → ℂ :=
  ![![1,0],![0,1],![1,1],![1,-1],![1,Complex.I],![1,-Complex.I]]

private def octScale : Fin 6 → ℝ := ![1,1,1/2,1/2,1/2,1/2]

private def octMat (i : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  octScale i • vecMulVec (octVec i) (star (octVec i))

private theorem octScale_nonneg (i : Fin 6) : 0 ≤ octScale i := by
  fin_cases i <;> norm_num [octScale]

private theorem octMat_psd (i : Fin 6) : (octMat i).PosSemidef :=
  (posSemidef_vecMulVec_self_star (octVec i)).smul (octScale_nonneg i)

private theorem octMat_trace (i : Fin 6) : trace (octMat i) = 1 := by
  dsimp only [octMat]
  rw [trace_smul, trace_vecMulVec]
  change octScale i • (∑ j, octVec i j * star (octVec i j)) = 1
  fin_cases i <;> norm_num [octVec, octScale, Fin.sum_univ_succ,
    Pi.star_apply, Complex.real_smul]

private def octStates (i : Fin 6) : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix (octMat i),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (octMat_psd i).nonneg, octMat_trace i⟩

private theorem octStates_pure (i : Fin 6) : IsPure (octStates i) := by
  refine ⟨Real.sqrt (octScale i) • octVec i, ?_⟩
  change octMat i = vecMulVec (Real.sqrt (octScale i) • octVec i)
    (star (Real.sqrt (octScale i) • octVec i))
  rw [star_smul, star_trivial, smul_vecMulVec, vecMulVec_smul, smul_smul,
    ← pow_two, Real.sq_sqrt (octScale_nonneg i)]
  rfl

set_option maxHeartbeats 2000000 in
-- The octahedron moment certificate checks all 64 tensor entries.
private theorem octMoment :
    ∑ i : Fin 6, (1/6 : ℂ) • tensorPow 3 (octMat i) = (1/4 : ℂ) • P8 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_succ, tensor23,
      bit_table, octMat, octVec, octScale, vecMulVec_apply, P8, weight, Matrix.cons_val_two]
  all_goals apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

private theorem octDesign : IsWeightedDesign 3 octStates (fun _ => 1/6) := by
  refine ⟨fun _ => by norm_num, by norm_num [Fin.sum_univ_succ],
    fun i _ => octStates_pure i, ?_⟩
  dsimp only [octStates]
  push_cast
  change ∑ i : Fin 6, (1/6 : ℂ) • tensorPow 3 (octMat i) =
    (trace (PiSym 2 3))⁻¹ • PiSym 2 3
  rw [piSym23, trace_P8]
  convert octMoment using 1; norm_num

private theorem nprime_le_six : Nprime 2 3 ≤ 6 :=
  Nat.sInf_le (show DesignExists 2 3 6 from ⟨octStates, fun _ => 1/6, octDesign⟩)

private def pt (A : Matrix (Fin 8) (Fin 8) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  let e : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv
  (partialTranspose (A.submatrix e e)).submatrix e.symm e.symm

private def Q : Matrix (Fin 8) (Fin 8) ℂ := pt ((1/4 : ℂ) • P8)

private def minorIndices : Fin 6 → Fin 8 := ![0,1,2,3,6,7]

private theorem minor_table : Q.submatrix minorIndices minorIndices =
    (!![1/4,0,0,1/12,0,0; 0,1/12,0,0,0,0; 0,0,1/12,0,0,1/12;
        1/12,0,0,1/12,0,0; 0,0,0,0,1/12,0; 0,0,1/12,0,0,1/4] :
      Matrix (Fin 6) (Fin 6) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q, pt, partialTranspose, finProdFinEquiv, minorIndices, P8, weight]

private theorem minor_det : (Q.submatrix minorIndices minorIndices).det = 1/746496 := by
  let π : Fin 6 ≃ Fin 6 := Equiv.ofBijective ![0,2,1,3,5,4] (by decide)
  let e : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv.trans π
  let blocks : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![!![1/4,1/12;1/12,1/12], !![1/12,1/12;1/12,1/4], !![1/12,0;0,1/12]]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hb : (Q.submatrix minorIndices minorIndices).submatrix e e = blockDiagonal blocks := by
    rw [minor_table]
    ext x y
    rcases x with ⟨a,b⟩
    rcases y with ⟨c,d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [e, π, blocks, blockDiagonal_apply, finProdFinEquiv,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12]
    all_goals rfl
  rw [← det_submatrix_equiv_self e, hb, det_blockDiagonal]
  norm_num [blocks, Fin.prod_univ_succ, det_fin_two, Matrix.cons_val_two]

private theorem rank_Q : Q.rank = 6 := by
  have hl := rank_submatrix_le Q minorIndices minorIndices
  have hm : (Q.submatrix minorIndices minorIndices).rank = 6 :=
    rank_of_det_ne_zero (by rw [minor_det]; norm_num)
  let collapse : Fin 8 → Fin 6 := ![0,1,2,3,2,3,4,5]
  let B : Matrix (Fin 8) (Fin 6) ℂ := fun i j => if (collapse i : ℕ) = (j : ℕ) then 1 else 0
  have hf : Q = B * Q.submatrix minorIndices id := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [B, collapse, Matrix.mul_apply, Fin.sum_univ_succ, Q, pt,
        partialTranspose, finProdFinEquiv, minorIndices, P8, weight]
  have hu := (rank_mul_le_left B (Q.submatrix minorIndices id)).trans (rank_le_card_width B)
  rw [← hf] at hu
  rw [hm] at hl
  simpa only [Fintype.card_fin] using le_antisymm hu hl

private theorem rank_sum {N : ℕ} (s : Finset (Fin N))
    (A : Fin N → Matrix (Fin 8) (Fin 8) ℂ) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  have h := LinearMap.rank_finsetSum_le s (fun i => Matrix.toLin' (A i))
  rw [← map_sum] at h
  have hc : ((∑ i ∈ s, A i).rank : Cardinal) ≤ ∑ i ∈ s, ((A i).rank : Cardinal) := by
    dsimp only [Matrix.rank]
    simpa only [Matrix.toLin'_apply', ← Module.finrank_eq_rank] using h
  exact_mod_cast hc

private def ptVector (v : Fin 2 → ℂ) (i : Fin 8) : ℂ :=
  v (bit i 2) * v (bit i 1) * star (v (bit i 0))

set_option maxHeartbeats 2000000 in
-- Entrywise reindexing identifies the transposed tensor as an outer product.
private theorem pure_pt (v : Fin 2 → ℂ) :
    pt (tensorPow 3 (vecMulVec v (star v))) = vecMulVec (ptVector v) (star (ptVector v)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pt, partialTranspose, Matrix.submatrix_apply, tensor23, ptVector,
      vecMulVec_apply, Pi.star_apply, star_mul, star_star]
    <;> norm_num [finProdFinEquiv, bit_table, Matrix.cons_val_two] <;> ring

private theorem pure_pt_rank (ρ : DensityState (Fin 2)) (hρ : IsPure ρ) (c : ℂ) :
    (c • pt (tensorPow 3 ρ.1)).rank ≤ 1 := by
  obtain ⟨v, hv⟩ := hρ
  change ρ.1 = vecMulVec v (star v) at hv
  rw [hv, pure_pt, ← smul_vecMulVec]
  exact rank_vecMulVec_le _ _

private theorem design_rank {N : ℕ} (ρ : Fin N → DensityState (Fin 2)) (p : Fin N → ℝ)
    (h : IsWeightedDesign 3 ρ p) :
    6 ≤ (Finset.univ.filter (fun i => 0 < p i)).card := by
  classical
  let S := Finset.univ.filter (fun i => 0 < p i)
  have hm : Q = ∑ i ∈ S, (p i : ℂ) • pt (tensorPow 3 (ρ i).1) := by
    have hh := congrArg pt h.2.2.2
    rw [piSym23, trace_P8] at hh
    have hc : (4 : ℂ)⁻¹ = 1/4 := by norm_num
    rw [hc] at hh
    change pt (∑ i, (p i : ℂ) • tensorPow 3 (ρ i).1) = Q at hh
    rw [← hh]
    ext a b
    simp only [pt, partialTranspose, Matrix.submatrix_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : p i = 0 := le_antisymm (le_of_not_gt (by simpa [S] using hi)) (h.1 i)
    simp [hz]
  have hb : ∀ i ∈ S, ((p i : ℂ) • pt (tensorPow 3 (ρ i).1)).rank ≤ 1 :=
    fun i hi => pure_pt_rank (ρ i) (h.2.2.1 i (Finset.mem_filter.mp hi).2) _
  calc
    6 = Q.rank := rank_Q.symm
    _ = (∑ i ∈ S, (p i : ℂ) • pt (tensorPow 3 (ρ i).1)).rank := congrArg Matrix.rank hm
    _ ≤ ∑ i ∈ S, ((p i : ℂ) • pt (tensorPow 3 (ρ i).1)).rank := rank_sum S _
    _ ≤ ∑ _i ∈ S, 1 := Finset.sum_le_sum hb
    _ = S.card := by simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nprime23 : Nprime 2 3 = 6 := by
  have he : ∃ N, DesignExists 2 3 N := ⟨6, octStates, fun _ => 1/6, octDesign⟩
  obtain ⟨ρ, p, hp⟩ := Nat.sInf_mem he
  have hle := (design_rank ρ p hp).trans (Finset.card_filter_le _ _)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  change Nat.le 6 (Nprime 2 3) at hle
  exact Nat.le_antisymm nprime_le_six hle

private theorem six_design_pure (ρ : Fin 6 → DensityState (Fin 2)) (p : Fin 6 → ℝ)
    (h : IsWeightedDesign 3 ρ p) : (∀ i, 0 < p i) ∧ (∀ i, IsPure (ρ i)) := by
  classical
  have hc := design_rank ρ p h
  have he : Finset.univ.filter (fun i => 0 < p i) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa using hc)
  have hp : ∀ i, 0 < p i := by
    intro i
    have hi : i ∈ Finset.univ.filter (fun j : Fin 6 => 0 < p j) := by
      rw [he]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  exact ⟨hp, fun i => h.2.2.1 i (hp i)⟩

private def tensorVec (v : Fin 2 → ℂ) (i : Fin 8) : ℂ :=
  v (bit i 2) * v (bit i 1) * v (bit i 0)

private theorem pure_tensor (v : Fin 2 → ℂ) :
    tensorPow 3 (vecMulVec v (star v)) = vecMulVec (tensorVec v) (star (tensorVec v)) := by
  ext i j
  simp only [tensor23, tensorVec, vecMulVec_apply, Pi.star_apply, star_mul]
  ring

private theorem tensor_trace (A : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (tensorPow 3 A) = (trace A) ^ 3 := by
  change (∑ i : Fin 8, tensorPow 3 A i i) = (trace A) ^ 3
  simp only [trace, Fin.sum_univ_succ, tensor23, bit_table]
  norm_num [Matrix.cons_val_two]
  ring

private theorem P8_hermitian : P8.IsHermitian := by
  change P8ᴴ = P8
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P8, weight, conjTranspose_apply]

private theorem P8_idem : P8 * P8 = P8 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mul_apply, Fin.sum_univ_succ, P8, weight]

private theorem P8_psd : P8.PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self P8
  rwa [P8_hermitian.eq, P8_idem] at h

private theorem P8_complement : (1 - P8).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (1 - P8)
  rw [(isHermitian_one.sub P8_hermitian).eq] at h
  have hi : (1 - P8) * (1 - P8) = 1 - P8 :=
    (show IsIdempotentElem P8 from P8_idem).one_sub
  rwa [hi] at h

private theorem tensorVec_fixed (v : Fin 2 → ℂ) : P8 *ᵥ tensorVec v = tensorVec v := by
  ext i
  fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_succ, tensorVec,
    bit_table, P8, weight, Matrix.cons_val_two] <;> ring

private theorem pure_tensor_le_sym (ρ : DensityState (Fin 2)) (hρ : IsPure ρ) :
    (P8 - tensorPow 3 ρ.1).PosSemidef := by
  obtain ⟨v, hv⟩ := hρ
  change ρ.1 = vecMulVec v (star v) at hv
  rw [hv, pure_tensor]
  let T := vecMulVec (tensorVec v) (star (tensorVec v))
  have ht0 : trace (tensorPow 3 (CStarMatrix.ofMatrix.symm ρ.1)) = 1 := by
    rw [tensor_trace]
    have htr := ρ.trace_eq_one
    change trace (CStarMatrix.ofMatrix.symm ρ.1) = 1 at htr
    rw [htr]
    norm_num
  have ht : trace T = 1 := by
    change trace (vecMulVec (tensorVec v) (star (tensorVec v))) = 1
    rw [← pure_tensor]
    rw [hv] at ht0
    exact ht0
  have hn : star (tensorVec v) ⬝ᵥ tensorVec v = 1 := by
    rw [dotProduct_comm]
    exact ht
  have hT : T.IsHermitian := (posSemidef_vecMulVec_self_star (tensorVec v)).isHermitian
  have hi : T * T = T := by
    dsimp only [T]
    rw [vecMulVec_mul_vecMulVec, hn]
    simp
  have hl : P8 * T = T := by rw [mul_vecMulVec, tensorVec_fixed]
  have hr : T * P8 = T := by
    have h := congrArg conjTranspose hl
    simpa only [conjTranspose_mul, P8_hermitian.eq, hT.eq] using h
  have hs : (P8 - T) * (P8 - T) = P8 - T := by
    rw [sub_mul, mul_sub, mul_sub, P8_idem, hl, hr, hi, sub_self, sub_zero]
  have h := posSemidef_conjTranspose_mul_self (P8 - T)
  rwa [(P8_hermitian.sub hT).eq, hs] at h

private def Y : Matrix (Fin 8) (Fin 8) ℂ := P8 + (1/8 : ℝ) • (1 - P8)

private theorem dual_pure (ρ : DensityState (Fin 2)) (hρ : IsPure ρ) :
    (Y - tensorPow 3 ρ.1).PosSemidef := by
  have h := (pure_tensor_le_sym ρ hρ).add (P8_complement.smul (by norm_num : (0:ℝ) ≤ 1/8))
  convert h using 1
  dsimp only [Y]
  abel

private theorem mixed_tensor : tensorPow 3 (maxMixed 2 (by norm_num)).1 =
    (1/8 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  change tensorPow 3 ((2 : ℝ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tensor23, bit_table, Matrix.smul_apply, Complex.real_smul,
      Matrix.one_apply, Matrix.cons_val_two]

private theorem dual_mixed : (Y - tensorPow 3 (maxMixed 2 (by norm_num)).1).PosSemidef := by
  rw [mixed_tensor]
  have he : Y - (1/8 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) = (7/8 : ℝ) • P8 := by
    dsimp only [Y]
    module
  rw [he]
  exact P8_psd.smul (by norm_num : (0:ℝ) ≤ 7/8)

private theorem trace_Y : (trace Y).re = 9/2 := by
  simp only [Y, trace_add, trace_smul, trace_sub, trace_P8, trace_one,
    Fintype.card_fin, Complex.real_smul, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

private theorem weak_dual (R E : Fin 7 → Matrix (Fin 8) (Fin 8) ℂ)
    (Z : Matrix (Fin 8) (Fin 8) ℂ) (hE : IsPOVM E)
    (hZ : ∀ i, (Z - R i).PosSemidef) : success R E ≤ (trace Z).re / 7 := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    RHLinalg.trace_mul_nonneg_of_posSemidef (hZ i) (hE.1 i))
  have hz : ∑ i, (trace (Z * E i)).re = (trace Z).re := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.mul_sum, hE.2, mul_one]
  change 0 ≤ ∑ i, (trace ((Z - R i) * E i)).re at h
  simp only [sub_mul, trace_sub, Complex.sub_re, Finset.sum_sub_distrib, hz] at h
  have he : success R E = (∑ i, (trace (R i * E i)).re) / 7 := by
    simp only [success, smul_mul_assoc, trace_smul, smul_eq_mul, Complex.mul_re]
    norm_num
    rw [← Finset.mul_sum]
    ring
  rw [he]
  linarith

private theorem discr_pure_le (ρ : Fin 6 → DensityState (Fin 2))
    (hρ : ∀ i, IsPure (ρ i)) : Discr 3 (adjoin ρ (by norm_num)) ≤ 9/14 := by
  apply csSup_le
  · let E : Fin 7 → Matrix (Fin 8) (Fin 8) ℂ := ![1,0,0,0,0,0,0]
    refine ⟨success (fun i => tensorPow 3 (adjoin ρ (by norm_num) i).1) E, E, ?_, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> first | exact PosSemidef.one | exact PosSemidef.zero
    · norm_num [E, Fin.sum_univ_succ]
  · rintro r ⟨E, hE, rfl⟩
    have hz : ∀ i : Fin 7, (Y - tensorPow 3 (adjoin ρ (by norm_num) i).1).PosSemidef := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · dsimp only [adjoin]
        rw [Fin.lastCases_last]
        exact dual_mixed
      · dsimp only [adjoin]
        rw [Fin.lastCases_castSucc]
        exact dual_pure (ρ j) (hρ j)
    have hh := weak_dual _ E Y hE hz
    rw [trace_Y] at hh
    norm_num at hh ⊢
    exact hh

end D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation
