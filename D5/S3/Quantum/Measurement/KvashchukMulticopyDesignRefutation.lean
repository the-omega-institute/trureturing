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
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Divergence.GibbsVariationalIdentity

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
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact D5.S3.Quantum.Divergence.GibbsVariationalIdentity.gibbsState
    (0 : CStarMatrix (Fin d) (Fin d) ℂ) (IsSelfAdjoint.zero _)

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
  rw [tensorPow.eq_1]
  simp only [bit, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.succ_zero_eq_one, Fin.reduceSucc]
  ring

private def weight : Fin 8 → ℕ := ![0,1,1,2,1,2,2,3]

private def P8 : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if weight i = weight j then
    if weight i = 0 ∨ weight i = 3 then 1 else 1 / 3 else 0

private theorem bit_table (i : Fin 8) (t : Fin 3) : bit i t =
    (![![0,0,0],![1,0,0],![0,1,0],![1,1,0],![0,0,1],![1,0,1],![0,1,1],![1,1,1]] :
      Fin 8 → Fin 3 → Fin 2) i t := by
  rw [bit.eq_1]
  fin_cases i <;> fin_cases t <;> rfl

private theorem permOp23 (σ : Equiv.Perm (Fin 3)) (i j : Fin 8) :
    permOp 2 3 σ i j = if (fun t => bit i t) = (fun t => bit j (σ t)) then 1 else 0 := rfl

private theorem sum_perms_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n + 1), ∑ σ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (p, σ)) := by
  rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  rfl

set_option maxHeartbeats 2000000 in
-- The symmetriser certificate checks all 64 entries.
private theorem piSym23 : PiSym 2 3 = P8 := by
  classical
  unfold PiSym
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  have hp : (∑ σ, permOp 2 3 σ i j) =
      ∑ σ : Equiv.Perm (Fin 3),
        (if (fun t => bit i t) = (fun t => bit j (σ t)) then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro σ _
    exact permOp23 σ i j
  rw [hp, sum_perms_succ]
  simp_rw [sum_perms_succ (n := 1), Fintype.sum_unique]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hb : (0 : Fin 2) ≠ 1 := by decide
  fin_cases i <;> fin_cases j <;>
    norm_num [bit_table, P8, weight, Matrix.smul_apply, Matrix.sum_apply,
      Function.comp_def, Matrix.cons_val_two,
      funext_iff, Fin.forall_fin_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Fin.reduceSucc,
      h01, h02, h12, hb, Ne.symm h01, Ne.symm h02, Ne.symm h12, Ne.symm hb]

private theorem trace_P8 : trace P8 = 4 := by
  change ∑ i, P8 i i = 4
  norm_num [P8, weight, Fin.sum_univ_succ]

def octVec : Fin 6 → Fin 2 → ℂ :=
  ![![1,0],![0,1],![1,1],![1,-1],![1,Complex.I],![1,-Complex.I]]

private def octScale : Fin 6 → ℝ := ![1,1,1/2,1/2,1/2,1/2]

private def octMat (i : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  octScale i • vecMulVec (octVec i) (star (octVec i))

private theorem octScale_nonneg (i : Fin 6) : 0 ≤ octScale i := by
  rw [octScale.eq_1]
  fin_cases i <;> norm_num

private theorem octMat_psd (i : Fin 6) : (octMat i).PosSemidef := by
  rw [octMat.eq_1]
  exact (posSemidef_vecMulVec_self_star (octVec i)).smul (octScale_nonneg i)

private theorem octMat_trace (i : Fin 6) : trace (octMat i) = 1 := by
  dsimp only [octMat]
  rw [trace_smul, trace_vecMulVec]
  change octScale i • (∑ j, octVec i j * star (octVec i j)) = 1
  rw [octVec.eq_1]
  fin_cases i <;> norm_num [octScale, Fin.sum_univ_succ,
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
  rw [Q.eq_1, pt.eq_1, minorIndices.eq_1]
  ext i j
  simp only [Matrix.submatrix_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTranspose, finProdFinEquiv, P8, weight]

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
  rw [vecMulVec_apply, Pi.star_apply, ptVector.eq_1 v i, ptVector.eq_1 v j]
  fin_cases i <;> fin_cases j <;>
    simp only [pt, partialTranspose, Matrix.submatrix_apply, tensor23,
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
    simp only [pt, Matrix.submatrix_apply]
    rw [D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.partialTranspose.eq_1]
    simp only [partialTranspose, Matrix.submatrix_apply, Matrix.sum_apply,
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
  classical
  have h := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.tensor_trace
    (fun _ : Fin 3 => A)
  have hreindex : trace (tensorPow 3 A) =
      trace (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp
        (fun _ : Fin 3 => A)) := by
    unfold trace diag tensorPow
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp
    exact (Equiv.sum_comp (finFunctionFinEquiv : (Fin 3 → Fin 2) ≃ Fin 8)
      (fun i : Fin 8 => ∏ t : Fin 3,
        A (finFunctionFinEquiv.symm i t) (finFunctionFinEquiv.symm i t))).symm
  rw [hreindex, h]
  simp

private theorem P8_hermitian : P8.IsHermitian := by
  change P8ᴴ = P8
  ext i j
  rw [conjTranspose_apply, P8.eq_1 j i, P8.eq_1 i j, weight.eq_1]
  fin_cases i <;> fin_cases j <;> norm_num

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
  rw [tensorVec.eq_1 v i]
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
  have hTP : IsStarProjection T := ⟨hi, hT⟩
  have hP : IsStarProjection P8 := ⟨P8_idem, P8_hermitian⟩
  exact Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr (hTP.le_of_mul_eq_right hP hl))

private def Y : Matrix (Fin 8) (Fin 8) ℂ := P8 + (1/8 : ℝ) • (1 - P8)

private theorem dual_pure (ρ : DensityState (Fin 2)) (hρ : IsPure ρ) :
    (Y - tensorPow 3 ρ.1).PosSemidef := by
  have h := (pure_tensor_le_sym ρ hρ).add (P8_complement.smul (by norm_num : (0:ℝ) ≤ 1/8))
  convert h using 1
  dsimp only [Y]
  abel

private theorem mixed_tensor : tensorPow 3 (maxMixed 2 (by norm_num)).1 =
    (1/8 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  change tensorPow 3 (CStarMatrix.ofMatrix.symm
    (@D5.S3.Quantum.Divergence.GibbsVariationalIdentity.gibbsState (Fin 2)
      inferInstance inferInstance ⟨0⟩ (0 : CStarMatrix (Fin 2) (Fin 2) ℂ) (IsSelfAdjoint.zero _)).1) = _
  rw [@D5.S3.Quantum.Divergence.GibbsVariationalIdentity.gibbs_state_zero
    (Fin 2) inferInstance inferInstance ⟨0⟩]
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
  rw [Y.eq_1]
  simp only [trace_add, trace_smul, trace_sub, trace_P8, trace_one,
    Fintype.card_fin, Complex.real_smul, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

private theorem success7 (R E : Fin 7 → Matrix (Fin 8) (Fin 8) ℂ) :
    success R E = (∑ i, (trace (R i * E i)).re) / 7 := by
  simp only [success, smul_mul_assoc, trace_smul, smul_eq_mul, Complex.mul_re]
  norm_num
  rw [← Finset.mul_sum]
  ring

private theorem weak_dual (R E : Fin 7 → Matrix (Fin 8) (Fin 8) ℂ)
    (Z : Matrix (Fin 8) (Fin 8) ℂ) (hE : IsPOVM E)
    (hZ : ∀ i, (Z - R i).PosSemidef) : success R E ≤ (trace Z).re / 7 := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    RHLinalg.trace_mul_nonneg_of_posSemidef (hZ i) (hE.1 i))
  have hz : ∑ i, (trace (Z * E i)).re = (trace Z).re := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.mul_sum, hE.2, mul_one]
  change 0 ≤ ∑ i, (trace ((Z - R i) * E i)).re at h
  simp only [sub_mul, trace_sub, Complex.sub_re, Finset.sum_sub_distrib, hz] at h
  rw [success7]
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
    have hn : (9/2 : ℝ) / 7 = 9/14 := by norm_num
    rw [hn] at hh
    exact hh

private theorem tensor_psd (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) :
    (tensorPow 3 A).PosSemidef := by
  let f : Fin 8 → (Fin 2 × Fin 2) × Fin 2 := fun i => ((bit i 2, bit i 1), bit i 0)
  have he : tensorPow 3 A = (kronecker (kronecker A A) A).submatrix f f := by
    ext i j
    simp only [tensor23, submatrix_apply, f]
    rfl
  rw [he]
  exact ((hA.kronecker hA).kronecker hA).submatrix f

private theorem discr_bdd (ρ : Fin 7 → DensityState (Fin 2)) :
    BddAbove {r : ℝ | ∃ E : Fin 7 → Matrix (Fin 8) (Fin 8) ℂ,
      IsPOVM E ∧ r = success (fun i => tensorPow 3 (ρ i).1) E} := by
  classical
  let R : Fin 7 → Matrix (Fin 8) (Fin 8) ℂ := fun i => tensorPow 3 (ρ i).1
  let Z := ∑ i, R i
  refine ⟨(trace Z).re / 7, ?_⟩
  rintro r ⟨E, hE, rfl⟩
  apply weak_dual R E Z hE
  intro i
  have he : Z - R i = ∑ j ∈ Finset.univ.erase i, R j := by
    dsimp only [Z]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    abel
  rw [he]
  apply posSemidef_sum
  intro j _
  apply tensor_psd
  exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (ρ j).2.1).posSemidef

private def omega3 : ℂ := (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

private theorem omega_unit : star omega3 * omega3 = 1 := by
  rw [omega3.eq_1]
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> nlinarith

private theorem omega_sq : omega3 ^ 2 = star omega3 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> norm_num [omega3, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith

private theorem omega_sum : 1 + omega3 + star omega3 = 0 := by
  apply Complex.ext <;> norm_num [omega3]
  ring

private def phase : Fin 3 → ℂ := ![1, omega3, star omega3]

private theorem phase_unit (j : Fin 3) : star (phase j) * phase j = 1 := by
  fin_cases j
  · norm_num [phase]
  · exact omega_unit
  · change star (star omega3) * star omega3 = 1
    rw [star_star, mul_comm]
    exact omega_unit

private def trineMat (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℝ) • vecMulVec ![1, phase j] (star ![1, phase j])

private theorem trine_psd (j : Fin 3) : (trineMat j).PosSemidef :=
  (posSemidef_vecMulVec_self_star ![1, phase j]).smul (by norm_num : (0:ℝ) ≤ 1/2)

private theorem trine_trace (j : Fin 3) : trace (trineMat j) = 1 := by
  rw [trineMat.eq_1]
  rw [trace_smul, trace_vecMulVec]
  norm_num [dotProduct, Fin.sum_univ_succ, Pi.star_apply, Complex.real_smul]
  simp only [starRingEnd_apply]
  linear_combination (1/2 : ℂ) * phase_unit j

private def witnessMat : Fin 7 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![octMat 0, octMat 1, trineMat 0, trineMat 1, trineMat 2,
    diagonal ![2/3,1/3], diagonal ![1/3,2/3]]

private theorem witness_psd (i : Fin 7) : (witnessMat i).PosSemidef := by
  rw [witnessMat.eq_1]
  fin_cases i
  · exact octMat_psd 0
  · exact octMat_psd 1
  · exact trine_psd 0
  · exact trine_psd 1
  · exact trine_psd 2
  · apply posSemidef_diagonal_iff.mpr
    intro j
    fin_cases j <;> norm_num [Complex.nonneg_iff]
  · apply posSemidef_diagonal_iff.mpr
    intro j
    fin_cases j <;> norm_num [Complex.nonneg_iff]

private theorem witness_trace (i : Fin 7) : trace (witnessMat i) = 1 := by
  fin_cases i
  · exact octMat_trace 0
  · exact octMat_trace 1
  · exact trine_trace 0
  · exact trine_trace 1
  · exact trine_trace 2
  · norm_num [witnessMat, trace_diagonal, Fin.sum_univ_succ]
  · norm_num [witnessMat, trace_diagonal, Fin.sum_univ_succ]

private def witness (i : Fin 7) : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix (witnessMat i),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (witness_psd i).nonneg, witness_trace i⟩

private def trineEffectVec (j : Fin 3) : Fin 8 → ℂ :=
  ![1/4,phase j/3,phase j/3,star (phase j)/3,phase j/3,
    star (phase j)/3,star (phase j)/3,1/4]

private def witnessPOVM : Fin 7 → Matrix (Fin 8) (Fin 8) ℂ :=
  ![(1/64 : ℝ) • (vecMulVec ![-6,0,0,0,0,0,0,1] (star ![-6,0,0,0,0,0,0,1]) +
       (15 : ℝ) • vecMulVec ![1,0,0,0,0,0,0,0] (star ![1,0,0,0,0,0,0,0])),
    (1/64 : ℝ) • (vecMulVec ![1,0,0,0,0,0,0,-6] (star ![1,0,0,0,0,0,0,-6]) +
       (15 : ℝ) • vecMulVec ![0,0,0,0,0,0,0,1] (star ![0,0,0,0,0,0,0,1])),
    vecMulVec (trineEffectVec 0) (star (trineEffectVec 0)),
    vecMulVec (trineEffectVec 1) (star (trineEffectVec 1)),
    vecMulVec (trineEffectVec 2) (star (trineEffectVec 2)),
    (1/2 : ℝ) • vecMulVec ![0,1,-1,0,0,0,0,0] (star ![0,1,-1,0,0,0,0,0]) +
      (1/6 : ℝ) • vecMulVec ![0,1,1,0,-2,0,0,0] (star ![0,1,1,0,-2,0,0,0]),
    (1/2 : ℝ) • vecMulVec ![0,0,0,1,0,-1,0,0] (star ![0,0,0,1,0,-1,0,0]) +
      (1/6 : ℝ) • vecMulVec ![0,0,0,1,0,1,-2,0] (star ![0,0,0,1,0,1,-2,0])]

private theorem witnessPOVM_psd (i : Fin 7) : (witnessPOVM i).PosSemidef := by
  rw [witnessPOVM.eq_1]
  fin_cases i
  · exact ((posSemidef_vecMulVec_self_star _).add
      ((posSemidef_vecMulVec_self_star _).smul (by norm_num : (0:ℝ) ≤ 15))).smul
      (by norm_num : (0:ℝ) ≤ 1/64)
  · exact ((posSemidef_vecMulVec_self_star _).add
      ((posSemidef_vecMulVec_self_star _).smul (by norm_num : (0:ℝ) ≤ 15))).smul
      (by norm_num : (0:ℝ) ≤ 1/64)
  · exact posSemidef_vecMulVec_self_star _
  · exact posSemidef_vecMulVec_self_star _
  · exact posSemidef_vecMulVec_self_star _
  · exact ((posSemidef_vecMulVec_self_star _).smul (by norm_num : (0:ℝ) ≤ 1/2)).add
      ((posSemidef_vecMulVec_self_star _).smul (by norm_num : (0:ℝ) ≤ 1/6))
  · exact ((posSemidef_vecMulVec_self_star _).smul (by norm_num : (0:ℝ) ≤ 1/2)).add
      ((posSemidef_vecMulVec_self_star _).smul (by norm_num : (0:ℝ) ≤ 1/6))

private theorem omega_conj : star omega3 = -1 - omega3 := by
  linear_combination omega_sum

set_option maxHeartbeats 2000000 in
-- All entries of the seven-effect sum reduce to the cubic-root identities.
private theorem witnessPOVM_sum : ∑ i, witnessPOVM i = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.sum_apply, Fin.sum_univ_succ, witnessPOVM, trineEffectVec,
      phase, vecMulVec_apply, Matrix.smul_apply, Pi.star_apply, map_ofNat, Matrix.cons_val_two,
      Complex.real_smul, Matrix.one_apply, -cons_vecMulVec, -vecMulVec_cons]
  all_goals simp only [starRingEnd_apply, omega_conj]
  all_goals ring_nf
  all_goals simp only [omega_sq, omega_conj]
  all_goals ring

private theorem witnessPOVM_valid : IsPOVM witnessPOVM :=
  ⟨witnessPOVM_psd, witnessPOVM_sum⟩

private theorem phase_cube (j : Fin 3) : phase j ^ 3 = 1 := by
  have h : omega3 ^ 3 = 1 := by rw [pow_succ, omega_sq, omega_unit]
  rw [phase.eq_1]
  fin_cases j
  · norm_num
  · exact h
  · change (star omega3) ^ 3 = 1
    rw [← star_pow, h, star_one]

private theorem trine_tensor (j : Fin 3) : tensorPow 3 (trineMat j) =
    (1/8 : ℝ) • vecMulVec (tensorVec ![1,phase j]) (star (tensorVec ![1,phase j])) := by
  rw [← pure_tensor]
  ext a b
  simp only [tensor23, trineMat, Matrix.smul_apply]
  norm_num [Complex.real_smul]
  ring

private theorem trine_overlap (j : Fin 3) :
    star (trineEffectVec j) ⬝ᵥ tensorVec ![1,phase j] = 5/2 := by
  rw [trineEffectVec.eq_1]
  norm_num [dotProduct, Fin.sum_univ_succ, tensorVec,
    bit_table, Pi.star_apply, Matrix.cons_val_two, map_ofNat]
  simp only [starRingEnd_apply]
  ring_nf
  rw [phase_cube]
  linear_combination phase_unit j

private theorem trine_score (j : Fin 3) :
    (trace (tensorPow 3 (trineMat j) *
      vecMulVec (trineEffectVec j) (star (trineEffectVec j)))).re = 25/32 := by
  rw [trine_tensor, smul_mul_assoc, trace_smul, vecMulVec_mul_vecMulVec, trace_vecMulVec]
  have ho : tensorVec ![1,phase j] ⬝ᵥ star (trineEffectVec j) = 5/2 := by
    rw [dotProduct_comm, trine_overlap]
  have hr : star (tensorVec ![1,phase j]) ⬝ᵥ trineEffectVec j = 5/2 := by
    rw [star_dotProduct, trine_overlap]
    norm_num
  simp only [dotProduct_smul, smul_eq_mul, hr, ho]
  norm_num [Complex.real_smul]

private theorem witness_scores (i : Fin 7) :
    (trace (tensorPow 3 (witnessMat i) * witnessPOVM i)).re =
      (![51/64,51/64,25/32,25/32,25/32,8/27,8/27] : Fin 7 → ℝ) i := by
  change (∑ a : Fin 8, ∑ b : Fin 8, tensorPow 3 (witnessMat i) a b *
    witnessPOVM i b a).re = _
  fin_cases i
  · norm_num [witnessMat, witnessPOVM, octMat, octScale, octVec, trace, mul_apply,
      Fin.sum_univ_succ, tensor23, bit_table, vecMulVec_apply, Matrix.smul_apply,
      Complex.real_smul, Matrix.cons_val_two, Pi.star_apply,
      -cons_vecMulVec, -vecMulVec_cons]
  · norm_num [witnessMat, witnessPOVM, octMat, octScale, octVec, trace, mul_apply,
      Fin.sum_univ_succ, tensor23, bit_table, vecMulVec_apply, Matrix.smul_apply,
      Complex.real_smul, Matrix.cons_val_two, Pi.star_apply,
      -cons_vecMulVec, -vecMulVec_cons]
  · exact trine_score 0
  · exact trine_score 1
  · exact trine_score 2
  · norm_num [witnessMat, witnessPOVM, trace, mul_apply, Fin.sum_univ_succ,
      tensor23, bit_table, vecMulVec_apply, Matrix.smul_apply, Complex.real_smul,
      Matrix.cons_val_two, diagonal_apply, Pi.star_apply,
      -cons_vecMulVec, -vecMulVec_cons]
  · norm_num [witnessMat, witnessPOVM, trace, mul_apply, Fin.sum_univ_succ,
      tensor23, bit_table, vecMulVec_apply, Matrix.smul_apply, Complex.real_smul,
      Matrix.cons_val_two, diagonal_apply, Pi.star_apply,
      -cons_vecMulVec, -vecMulVec_cons]

private theorem witness_success :
    success (fun i => tensorPow 3 (witness i).1) witnessPOVM = 1957/3024 := by
  rw [success7]
  change (∑ i : Fin 7, (trace (tensorPow 3 (witnessMat i) * witnessPOVM i)).re) / 7 = _
  simp only [witness_scores]
  norm_num [Fin.sum_univ_succ]

private theorem discr_witness_ge : 1957/3024 ≤ Discr 3 witness := by
  rw [← witness_success]
  exact le_csSup (discr_bdd witness) ⟨witnessPOVM, witnessPOVM_valid, rfl⟩

private theorem discr_design_le (ρ : Fin 6 → DensityState (Fin 2)) (p : Fin 6 → ℝ)
    (h : IsWeightedDesign 3 ρ p) : Discr 3 (adjoin ρ (by norm_num)) ≤ 9/14 :=
  discr_pure_le ρ (six_design_pure ρ p h).2

theorem result : ¬ claim := by
  intro h
  have hs := h 2 3 (by norm_num) (by norm_num)
  rw [nprime23] at hs
  have hu := discr_design_le octStates (fun _ => 1/6) octDesign
  have hl := discr_witness_ge
  have hc := hs octStates (fun _ => 1/6) octDesign witness
  have hb : (1957/3024 : ℝ) ≤ 9/14 := hl.trans (hc.trans hu)
  norm_num at hb

end D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation
