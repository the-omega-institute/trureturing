/- GID: D5/S3/Quantum/Schatten/DiagonalSingularValues
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/DiagonalSingularValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sorted singular values of nonnegative diagonal matrices. -/

import D5.S3.Quantum.Schatten.SingularValueOrder

/-! Any permutation sorting the diagonal entries determines the sorted singular values. -/
noncomputable section
open Matrix
namespace D5.S3.Quantum.Schatten

/-- A nonnegative diagonal matrix has its diagonal entries as its sorted singular values. -/
theorem singularValuesSorted_diagonal_of_antitone_perm {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (σ : Equiv.Perm (Fin n)) (hσ : Antitone (a ∘ σ))
    (i : Fin (Fintype.card (Fin n))) :
    singularValuesSorted (diagonal (fun j => (a j : ℂ))) i =
      a (σ ⟨i.val, by simpa using i.isLt⟩) := by
  classical
  let A := diagonal (fun j => (a j : ℂ))
  let hH := isHermitian_mul_conjTranspose_self Aᴴ
  have hg : Aᴴ * Aᴴᴴ = diagonal (fun j => ((a j ^ 2 : ℝ) : ℂ)) := by
    simp [A, diagonal_mul_diagonal, pow_two]
  obtain ⟨τ, hτ⟩ := hH.eigenvalues_eq_of_unitary_similarity_diagonal
    (U := (1 : Matrix (Fin n) (Fin n) ℂ)) (by simp) (f := fun j => a j ^ 2)
    (by simpa using hg)
  have hs (j : Fin n) : singularValues A (τ j) = a j := by
    change Real.sqrt (hH.eigenvalues (τ j)) = a j
    rw [show hH.eigenvalues (τ j) = a j ^ 2 from congrFun hτ j, Real.sqrt_sq (ha j)]
  have hm : Multiset.map (singularValues A) Finset.univ.val =
      Multiset.map (fun j => a (σ j)) Finset.univ.val := by
    calc Multiset.map (singularValues A) Finset.univ.val =
        Multiset.map (singularValues A) (Multiset.map τ Finset.univ.val) := by
          rw [Multiset.map_univ_val_equiv]
      _ = Multiset.map a Finset.univ.val := by
        rw [Multiset.map_map]
        congr 1
        funext j
        exact hs j
      _ = Multiset.map a (Multiset.map σ Finset.univ.val) := by
        rw [Multiset.map_univ_val_equiv]
      _ = _ := by rw [Multiset.map_map]; rfl
  have hsorted : (Multiset.map (singularValues A) Finset.univ.val).sort (· ≥ ·) =
      List.ofFn (a ∘ σ) := by
    rw [hm]
    simp only [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hσ.sortedGE_ofFn
  change ((Multiset.map (singularValues A) Finset.univ.val).sort (· ≥ ·)).get _ = _
  simp only [hsorted, List.get_eq_getElem, List.getElem_ofFn, Function.comp_apply]

end D5.S3.Quantum.Schatten
