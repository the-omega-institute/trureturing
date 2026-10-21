/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual relabel row matrices equal the reduced forward gyration. -/

/- Construct both factors from the actual vertex bijection and derive target adjacency from the edge bijection. Standard coordinates use the row convention. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualRankedPermutationRelabel
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualWordMatrixPath

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.ActualRelabelResidue
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding
open CountedMatrixOverlap (CountMat)
open CountedOrderTypeGyration
open CountedRelativeGyrationTransport
open ZeroWindowRelabeling (Relabel)
open SourceOnly.KernelRSSquareGyration (rows)
open SourceOnly.ActualWordMatrixPath (D counts reindex timeMap relabelEdge)

/-- This coefficient equality uses the ACTUAL edge bijection, so arbitrary
parallel-edge permutations have not been discarded from the input. -/
theorem actual_Q_mul_P {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    (r : Relabel (countedGraph A) (countedGraph B)) :
    Q r.vertex A * P r.vertex = B := by
  rw [Q_mul_P]
  ext j k
  have h := SourceOnly.ActualWordMatrixPath.relabel_adjacency r (r.vertex.symm j) k
  change StandardBeamEndpointRows.adjacency
    (CountedMatrixBeamDiagram.countedGraph A) (r.vertex.symm j) (r.vertex.symm k) =
    StandardBeamEndpointRows.adjacency (CountedMatrixBeamDiagram.countedGraph B)
      (r.vertex (r.vertex.symm j)) k at h
  have hz : (A (r.vertex.symm j) (r.vertex.symm k) : ℤ) = (B j k : ℤ) := by
    simpa only [CountedMatrixBeamDiagram.adjacency_counted,
      CountedMatrixBeamDiagram.integerCounts, Equiv.apply_symm_apply] using h
  exact_mod_cast hz

/-- Literal standard-basis entries, with the ROW index first. -/
theorem rows_standard {n m : ℕ} (f : (Fin n → D) →ₗ[D] (Fin m → D))
    (i : Fin n) (j : Fin m) :
    rows (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin m)) f i j =
      f (Pi.single i 1) j := by
  simp only [rows, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    Pi.basisFun_repr, Pi.basisFun_apply]

theorem rows_right_standard {n m : ℕ} (M : Matrix (Fin n) (Fin m) D) :
    rows (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin m)) M.toLinearMapRight' = M := by
  exact SourceOnly.ActualWordMatrixPath.rows_right M

theorem reindex_rows {n m : ℕ} (e : Fin n ≃ Fin m) :
    rows (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin m))
      (reindex e).toLinearMap = counts (P e) := by
  classical
  ext i j
  rw [rows_standard]
  by_cases hij : e i = j
  · subst j
    simp [reindex, counts, P]
  · have he : e.symm j ≠ i := by
      intro h
      apply hij
      exact (congrArg e h).symm.trans (e.apply_symm_apply j)
    simp [reindex, counts, P, hij, he, Ne.symm he]

theorem backward_map {n m : ℕ} (e : Fin n ≃ Fin m) (A : CountMat n n) :
    (timeMap (countedGraph A)).comp (reindex e).symm.toLinearMap =
      (counts (Q e A)).toLinearMapRight' := by
  classical
  apply LinearMap.ext
  intro z
  funext i
  rw [SourceOnly.ActualWordMatrixPath.time_counted]
  change (∑ k : Fin n, z (e k) * counts A k i) =
    ∑ j : Fin m, z j * counts (Q e A) j i
  apply Fintype.sum_equiv e
  intro k
  simp only [counts, Q, Matrix.map_apply, Equiv.symm_apply_apply]

theorem backward_rows {n m : ℕ} (e : Fin n ≃ Fin m) (A : CountMat n n) :
    rows (Pi.basisFun D (Fin m)) (Pi.basisFun D (Fin n))
      ((timeMap (countedGraph A)).comp (reindex e).symm.toLinearMap) =
        counts (Q e A) := by
  rw [backward_map, rows_right_standard]

/-- The exact requested comparison, for every finite n,m, including zero,
and every nonzero d with 3 dividing d. There is no added equality premise. -/
theorem relabel_residue {n m d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (A : CountMat n n) (B : CountMat m m)
    (r : Relabel (countedGraph A) (countedGraph B)) :
    (relabelEdge r (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin m))).weight d =
      ZMod.castHom hd (ZMod 3) ((timed r).gyration d) := by
  change dyadicGyration d
    (rows (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin m)) (reindex r.vertex).toLinearMap)
    (rows (Pi.basisFun D (Fin m)) (Pi.basisFun D (Fin n))
      ((timeMap (countedGraph A)).comp (reindex r.vertex).symm.toLinearMap)) = _
  rw [reindex_rows, backward_rows]
  calc
    _ = ZMod.castHom hd (ZMod 3)
        (relativeForwardGyration (d := d) (P r.vertex) (Q r.vertex A)) :=
      dyadicGyration_nonnegative hd (P r.vertex) (Q r.vertex A)
    _ = _ := (ranked_residue hd r.vertex (Q r.vertex A)
      (P_mul_Q r.vertex A) (actual_Q_mul_P r) r rfl).symm

end SourceOnly.ActualRelabelResidue
