/- GID: D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Coordinate kernels of the embedded Bell-state permutation witnesses. -/

import D5.S3.Quantum.Entanglement.PermutationCriteria.Witnesses
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks

noncomputable section

namespace D5.S3.Quantum.Entanglement.PermutationCriteria

open _root_.Matrix Finset

/-- Select the row or column position of a party. -/
def sidePos {r : ℕ} (side : Bool) (k : Fin r) : Fin (2 * r) :=
  if side then ketPos k else braPos k

/-- Whether a flat position is on the selected matrix side. -/
def sideSelected {r : ℕ} (side : Bool) (p : Fin (2 * r)) : Prop :=
  if side then p.val % 2 = 0 else p.val % 2 ≠ 0

private theorem sidePos_party {r : ℕ} (side : Bool) (p : Fin (2 * r))
    (hp : sideSelected side p) : sidePos side (party p) = p := by
  cases side
  · exact braPos_party p hp
  · exact ketPos_party p hp

private theorem sideSelected_sidePos {r : ℕ} (side : Bool) (k : Fin r) :
    sideSelected side (sidePos side k) := by
  cases side
  · dsimp [sideSelected, sidePos, braPos]
    omega
  · simp [sideSelected, sidePos, ketPos]

/-- The selected row or column string of a reshaped correlated matrix unit. -/
def sideImage {r d : ℕ} (side : Bool) (σ : Equiv.Perm (Fin (2 * r)))
    (hd : 2 ≤ d) (S : Finset (Fin r)) (t : Fin 2 × Fin 2) : Index r d :=
  fun k => merge (bitPattern hd S t.1) (bitPattern hd S t.2)
    (σ.symm (sidePos side k))

/-- Two reshaped basis strings agree exactly when every bit appearing on that side agrees. -/
theorem sideImage_kernel {r d : ℕ} (side : Bool) (σ : Equiv.Perm (Fin (2 * r)))
    (hd : 2 ≤ d) (S : Finset (Fin r)) (t u : Fin 2 × Fin 2) :
    sideImage side σ hd S t = sideImage side σ hd S u ↔
      ((∃ i ∈ S, sideSelected side (σ (ketPos i))) → t.1 = u.1) ∧
      ((∃ i ∈ S, sideSelected side (σ (braPos i))) → t.2 = u.2) := by
  constructor
  · intro h
    constructor
    · rintro ⟨i, hi, hp⟩
      have he := congrFun h (party (σ (ketPos i)))
      change merge (bitPattern hd S t.1) (bitPattern hd S t.2)
          (σ.symm (sidePos side (party (σ (ketPos i))))) =
        merge (bitPattern hd S u.1) (bitPattern hd S u.2)
          (σ.symm (sidePos side (party (σ (ketPos i))))) at he
      rw [sidePos_party side _ hp, Equiv.symm_apply_apply, merge_ketPos,
        merge_ketPos] at he
      apply Fin.ext
      have hv := congrArg Fin.val he
      simpa [bitPattern, hi] using hv
    · rintro ⟨i, hi, hp⟩
      have he := congrFun h (party (σ (braPos i)))
      change merge (bitPattern hd S t.1) (bitPattern hd S t.2)
          (σ.symm (sidePos side (party (σ (braPos i))))) =
        merge (bitPattern hd S u.1) (bitPattern hd S u.2)
          (σ.symm (sidePos side (party (σ (braPos i))))) at he
      rw [sidePos_party side _ hp, Equiv.symm_apply_apply, merge_braPos,
        merge_braPos] at he
      apply Fin.ext
      have hv := congrArg Fin.val he
      simpa [bitPattern, hi] using hv
  · rintro ⟨ht, hu⟩
    funext k
    change merge (bitPattern hd S t.1) (bitPattern hd S t.2) (σ.symm (sidePos side k)) =
      merge (bitPattern hd S u.1) (bitPattern hd S u.2) (σ.symm (sidePos side k))
    by_cases hp : (σ.symm (sidePos side k)).val % 2 = 0
    · simp only [merge, hp, if_pos]
      by_cases hi : party (σ.symm (sidePos side k)) ∈ S
      · have hs : sideSelected side (σ (ketPos (party (σ.symm (sidePos side k))))) := by
          rw [ketPos_party _ hp, Equiv.apply_symm_apply]
          exact sideSelected_sidePos side k
        rw [ht ⟨_, hi, hs⟩]
      · simp [bitPattern, hi]
    · simp only [merge, hp, if_neg]
      by_cases hi : party (σ.symm (sidePos side k)) ∈ S
      · have hs : sideSelected side (σ (braPos (party (σ.symm (sidePos side k))))) := by
          rw [braPos_party _ hp, Equiv.apply_symm_apply]
          exact sideSelected_sidePos side k
        rw [hu ⟨_, hi, hs⟩]
        simp only [if_false]
      · simp [bitPattern, hi]

/-- A permuted Bell witness consists of the four correlated half entries. -/
theorem permute_bellWitness {r d : ℕ} (hd : 2 ≤ d)
    (σ : Equiv.Perm (Fin (2 * r))) (i j : Fin r) :
    permute σ (bellWitness hd i j) =
      BellBlocks.fourEntries (sideImage true σ hd {i, j})
        (sideImage false σ hd {i, j}) := by
  rw [bellWitness_eq]
  change permute σ (Matrix.single _ _ (1 / 2 : ℂ)) +
      permute σ (Matrix.single _ _ (1 / 2 : ℂ)) +
      permute σ (Matrix.single _ _ (1 / 2 : ℂ)) +
      permute σ (Matrix.single _ _ (1 / 2 : ℂ)) = _
  rw [permute_single, permute_single, permute_single, permute_single]
  simp only [BellBlocks.fourEntries, Fintype.sum_prod_type, Fin.sum_univ_two]
  change Matrix.single (sideImage true σ hd {i, j} (0, 0))
        (sideImage false σ hd {i, j} (0, 0)) (1 / 2 : ℂ) +
      Matrix.single (sideImage true σ hd {i, j} (0, 1))
        (sideImage false σ hd {i, j} (0, 1)) (1 / 2 : ℂ) +
      Matrix.single (sideImage true σ hd {i, j} (1, 0))
        (sideImage false σ hd {i, j} (1, 0)) (1 / 2 : ℂ) +
      Matrix.single (sideImage true σ hd {i, j} (1, 1))
        (sideImage false σ hd {i, j} (1, 1)) (1 / 2 : ℂ) = _
  simp only [add_assoc]

/-- The Bell witness norm is determined by the number of ket and bra disagreements
between the two parties' output-side labels. -/
theorem bellWitness_traceNorm {r d : ℕ} (hd : 2 ≤ d)
    (σ : Equiv.Perm (Fin (2 * r))) (i j : Fin r) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (permute σ (bellWitness hd i j)) =
      BellBlocks.bellValue
        (LabelRecovery.pairDistance (RowSetRecovery.rowLabels (rowSet σ) i)
          (RowSetRecovery.rowLabels (rowSet σ) j)) := by
  classical
  let rk := decide ((σ (ketPos i)).val % 2 = 0 ∨ (σ (ketPos j)).val % 2 = 0)
  let rb := decide ((σ (braPos i)).val % 2 = 0 ∨ (σ (braPos j)).val % 2 = 0)
  let ck := decide ((σ (ketPos i)).val % 2 ≠ 0 ∨ (σ (ketPos j)).val % 2 ≠ 0)
  let cb := decide ((σ (braPos i)).val % 2 ≠ 0 ∨ (σ (braPos j)).val % 2 ≠ 0)
  have hK : rk = true ∨ ck = true := by
    by_cases hk : (σ (ketPos i)).val % 2 = 0
    · left; simp [rk, hk]
    · right; simp [ck, hk]
  have hB : rb = true ∨ cb = true := by
    by_cases hb : (σ (braPos i)).val % 2 = 0
    · left; simp [rb, hb]
    · right; simp [cb, hb]
  have hR : ∀ t u, sideImage true σ hd {i, j} t = sideImage true σ hd {i, j} u ↔
      (rk = true → t.1 = u.1) ∧ (rb = true → t.2 = u.2) := by
    intro t u
    simpa [rk, rb, sideSelected] using sideImage_kernel true σ hd {i, j} t u
  have hC : ∀ t u, sideImage false σ hd {i, j} t = sideImage false σ hd {i, j} u ↔
      (ck = true → t.1 = u.1) ∧ (cb = true → t.2 = u.2) := by
    intro t u
    simpa [ck, cb, sideSelected] using sideImage_kernel false σ hd {i, j} t u
  have hcount : ((if rk && ck then 1 else 0) + (if rb && cb then 1 else 0)) =
      LabelRecovery.pairDistance (RowSetRecovery.rowLabels (rowSet σ) i)
        (RowSetRecovery.rowLabels (rowSet σ) j) := by
    by_cases hki : (σ (ketPos i)).val % 2 = 0 <;>
      by_cases hkj : (σ (ketPos j)).val % 2 = 0 <;>
      by_cases hbi : (σ (braPos i)).val % 2 = 0 <;>
      by_cases hbj : (σ (braPos j)).val % 2 = 0 <;>
      simp [rk, rb, ck, cb, LabelRecovery.pairDistance, RowSetRecovery.rowLabels,
        rowSet, hki, hkj, hbi, hbj]
  rw [permute_bellWitness]
  have hnorm := BellBlocks.traceNorm_fourEntries
    (sideImage true σ hd {i, j}) (sideImage false σ hd {i, j}) rk rb ck cb hK hB hR hC
  rw [hcount] at hnorm
  exact hnorm

/-- Equality of all density-state permutation norms preserves every paired-label distance. -/
theorem dependent_pairDistance {r d : ℕ} (hd : 2 ≤ d)
    {σ μ : Equiv.Perm (Fin (2 * r))} (h : Dependent r d σ μ) (i j : Fin r) :
    LabelRecovery.pairDistance (RowSetRecovery.rowLabels (rowSet σ) i)
        (RowSetRecovery.rowLabels (rowSet σ) j) =
      LabelRecovery.pairDistance (RowSetRecovery.rowLabels (rowSet μ) i)
        (RowSetRecovery.rowLabels (rowSet μ) j) := by
  have he := h (bellWitness hd i j) (bellWitness_isDensity hd i j)
  rw [bellWitness_traceNorm hd σ i j, bellWitness_traceNorm hd μ i j] at he
  apply BellBlocks.bellValue_injective (by
    unfold LabelRecovery.pairDistance
    split_ifs <;> omega) (by
    unfold LabelRecovery.pairDistance
    split_ifs <;> omega) he

end D5.S3.Quantum.Entanglement.PermutationCriteria
