/- GID: D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Complete classification of permutation trace-norm dependence on density matrices. -/

import D5.S3.Quantum.Entanglement.PermutationCriteria.BellWitnesses

noncomputable section

namespace D5.S3.Quantum.Entanglement.PermutationCriteria

open _root_.Matrix Finset
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open NormInvariance

private def rowPerm {r : ℕ} (ν : Equiv.Perm (Fin (2 * r)))
    (hp : ∀ p, (ν p).val % 2 = 0 ↔ p.val % 2 = 0) : Equiv.Perm (Fin r) :=
  Equiv.ofBijective (fun k => party (ν (ketPos k))) (Finite.injective_iff_bijective.mp (by
    intro i j hij
    have hi : (ν (ketPos i)).val % 2 = 0 := (hp _).2 (by simp [ketPos])
    have hj : (ν (ketPos j)).val % 2 = 0 := (hp _).2 (by simp [ketPos])
    have he := congrArg ketPos hij
    rw [ketPos_party _ hi, ketPos_party _ hj] at he
    simpa using congrArg party (ν.injective he)))

private def colPerm {r : ℕ} (ν : Equiv.Perm (Fin (2 * r)))
    (hp : ∀ p, (ν p).val % 2 = 0 ↔ p.val % 2 = 0) : Equiv.Perm (Fin r) :=
  Equiv.ofBijective (fun k => party (ν (braPos k))) (Finite.injective_iff_bijective.mp (by
    intro i j hij
    have hi : (ν (braPos i)).val % 2 ≠ 0 := by
      simpa [braPos] using (hp (braPos i)).not.mpr (by simp [braPos])
    have hj : (ν (braPos j)).val % 2 ≠ 0 := by
      simpa [braPos] using (hp (braPos j)).not.mpr (by simp [braPos])
    have he := congrArg braPos hij
    rw [braPos_party _ hi, braPos_party _ hj] at he
    simpa using congrArg party (ν.injective he)))

private theorem merge_reindex {r d : ℕ} (ν : Equiv.Perm (Fin (2 * r)))
    (hp : ∀ p, (ν p).val % 2 = 0 ↔ p.val % 2 = 0)
    (a b : Index r d) (p : Fin (2 * r)) :
    merge a b (ν p) = merge (fun k => a (rowPerm ν hp k))
      (fun k => b (colPerm ν hp k)) p := by
  by_cases h : p.val % 2 = 0
  · have hν : (ν p).val % 2 = 0 := (hp p).2 h
    simp [merge, h, hν, rowPerm, ketPos_party p h]
  · have hν : (ν p).val % 2 ≠ 0 := (hp p).not.mpr h
    simp [merge, h, hν, colPerm, braPos_party p h]

/-- Permutations with the same row set differ only by independent row and column reindexing. -/
theorem traceNorm_eq_of_rowSet {r d : ℕ} (σ μ : Equiv.Perm (Fin (2 * r)))
    (hrow : rowSet μ = rowSet σ) (ρ : Matrix (Index r d) (Index r d) ℂ) :
    traceNorm (permute μ ρ) = traceNorm (permute σ ρ) := by
  let ν := σ.symm.trans μ
  have hp : ∀ p, (ν p).val % 2 = 0 ↔ p.val % 2 = 0 := by
    intro p
    have h := Finset.ext_iff.mp hrow (σ.symm p)
    simpa [rowSet, ν, Equiv.trans_apply] using h
  let er : Equiv.Perm (Index r d) :=
    Equiv.arrowCongr (rowPerm ν hp).symm (Equiv.refl (Fin d))
  let ec : Equiv.Perm (Index r d) :=
    Equiv.arrowCongr (colPerm ν hp).symm (Equiv.refl (Fin d))
  have he : permute μ ρ = (permute σ ρ).submatrix er ec := by
    ext a b
    change entry ρ (fun p => merge a b (μ p)) =
      entry ρ (fun p => merge (er a) (ec b) (σ p))
    apply congrArg (entry ρ)
    funext p
    have h := merge_reindex ν hp a b (σ p)
    simpa [ν, er, ec, Equiv.arrowCongr, Equiv.trans_apply, Function.comp_def] using h
  rw [he]
  exact traceNorm_submatrix_equiv _ er ec

private theorem J_even_iff {r : ℕ} (p : Fin (2 * r)) :
    (J r p).val % 2 = 0 ↔ p.val % 2 ≠ 0 := by
  by_cases h : p.val % 2 = 0 <;> simp [J, h, ketPos, braPos]

private theorem rowSet_output_exchange {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) :
    rowSet (σ.trans (J r)) = (rowSet σ)ᶜ := by
  ext p
  simp [rowSet, Equiv.trans_apply, J_even_iff]

private theorem rowSet_input_exchange {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) :
    rowSet ((J r).trans σ) = (rowSet σ).map (J r).toEmbedding := by
  ext p
  rw [Finset.mem_map_equiv]
  simp only [rowSet, mem_filter, mem_univ, true_and]
  rfl

private theorem permute_input_exchange {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r)))
    (ρ : Matrix (Index r d) (Index r d) ℂ) (hρ : ρ.IsHermitian) :
    permute ((J r).trans σ) ρ = (permute σ ρ).map star := by
  ext a b
  simp only [permute, entry, Equiv.trans_apply, J_ketPos, J_braPos, Matrix.map_apply]
  exact (hρ.apply _ _).symm

private theorem traceNorm_map_star {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : traceNorm (A.map star) = traceNorm A := by
  rw [← Matrix.transpose_conjTranspose, traceNorm_conjTranspose, traceNorm_transpose]

/-- The four universal row-set symmetries give equal norms on every density matrix. -/
theorem dependent_of_rowSet_orbit {r d : ℕ} (σ μ : Equiv.Perm (Fin (2 * r)))
    (hrow : rowSet μ = rowSet σ ∨ rowSet μ = (rowSet σ)ᶜ ∨
      rowSet μ = (rowSet σ).map (J r).toEmbedding ∨
      rowSet μ = ((rowSet σ).map (J r).toEmbedding)ᶜ) :
    Dependent r d σ μ := by
  intro ρ hρ
  symm
  rcases hrow with h | h | h | h
  · exact traceNorm_eq_of_rowSet σ μ h ρ
  · calc
      traceNorm (permute μ ρ) = traceNorm (permute (σ.trans (J r)) ρ) :=
        traceNorm_eq_of_rowSet _ _ (h.trans (rowSet_output_exchange σ).symm) ρ
      _ = traceNorm (permute σ ρ) := by
        rw [permute_output_exchange, traceNorm_transpose]
  · calc
      traceNorm (permute μ ρ) = traceNorm (permute ((J r).trans σ) ρ) :=
        traceNorm_eq_of_rowSet _ _ (h.trans (rowSet_input_exchange σ).symm) ρ
      _ = traceNorm (permute σ ρ) := by
        rw [permute_input_exchange σ ρ hρ.1.isHermitian, traceNorm_map_star]
  · have hs : rowSet (((J r).trans σ).trans (J r)) =
        ((rowSet σ).map (J r).toEmbedding)ᶜ := by
      rw [rowSet_output_exchange, rowSet_input_exchange]
    calc
      traceNorm (permute μ ρ) = traceNorm (permute (((J r).trans σ).trans (J r)) ρ) :=
        traceNorm_eq_of_rowSet _ _ (h.trans hs.symm) ρ
      _ = traceNorm (permute σ ρ) := by
        rw [permute_output_exchange, traceNorm_transpose,
          permute_input_exchange σ ρ hρ.1.isHermitian, traceNorm_map_star]

end D5.S3.Quantum.Entanglement.PermutationCriteria

/-!
The dependence relation is Definition 1 of Clarisse and Wocjan,
"On independent permutation separability criteria", quant-ph/0504160v2.
Positions are numbered from zero and the permutation convention is the
one in Section II. The conclusion concerns equality of norm functions,
not incomparability of the sets detected by entanglement criteria.

admission_basis: open-problem-resolution (issue #30402).
result: proof_shape: content; escape_witness: density-state separation by
one-party mixed states and two-party Bell states; consumers: none.
-/

namespace D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification

open LabelRecovery RowSetRecovery

/-- For every positive number of parties and local dimension at least two,
two permutation criteria have identical trace norms on all states exactly
when their row sets belong to the same four-symmetry orbit. -/
theorem result (r d : ℕ) (hr : 1 ≤ r) (hd : 2 ≤ d)
    (σ μ : Equiv.Perm (Fin (2 * r))) :
    Dependent r d σ μ ↔
      rowSet μ = rowSet σ ∨ rowSet μ = (rowSet σ)ᶜ ∨
      rowSet μ = (rowSet σ).map (J r).toEmbedding ∨
      rowSet μ = ((rowSet σ).map (J r).toEmbedding)ᶜ := by
  constructor
  · intro h
    exact recover_rowSets (rowSet σ) (rowSet μ)
      (dependent_sameSide hd h) (dependent_pairDistance hd h)
  · exact dependent_of_rowSet_orbit σ μ

#print axioms result

end D5.S3.Quantum.Entanglement.PermutationCriteria.ClarisseWocjanClassification
