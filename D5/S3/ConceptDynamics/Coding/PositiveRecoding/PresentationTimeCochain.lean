/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/PresentationTimeCochain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/PresentationTimeCochain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same time/id edge in every finite presentation basis measures actual primitive-orbit count. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.RankedTimeRecoding
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualWordEnumeratedLoop

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.PresentationTimeCochain
open D5.S3.ConceptDynamics.Coding
open TwoSidedFiniteInduction
open CountedOrderTypeGyration
open ActualPositiveWordPeriodicCochain (Orbit orbitChart)
open SourceOnly.ActualWordMatrixPath (D counts vertex vertex_matrix presentationBasis)
open SourceOnly.KernelRSSquareGyration (rows value)
open SourceOnly.FiniteKernelLadder (rows_id)
open SourceOnly.BasedLoopCoordinateTransport (closed_square)

/-- The SAME actual time/id edge in the P1 chart and a finite coefficient
basis. Time need not be invertible, the graph may have zero vertices, and
neither endpoint term is assumed zero. -/
theorem time_calibration (F : Presentation) {m : ℕ}
    (c : Module.Basis (Fin m) D (F.V → D)) (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    let b := presentationBasis F
    let K := value (d := d) b c LinearMap.id (vertex F).time
    (value (d := d) b b (vertex F).time LinearMap.id + K =
      K + value (d := d) c c (vertex F).time LinearMap.id) ∧
    dyadicGyration d (rows c c (vertex F).time) 1 =
      (Fintype.card (Orbit F d) : ZMod 3) := by
  let b := presentationBasis F
  let A := ActualPositiveWordPeriodicCochain.matrix F
  have h₀ : value (d := d) b b (vertex F).time LinearMap.id =
      (Fintype.card (Orbit F d) : ZMod 3) := by
    change dyadicGyration d (vertex F).matrix (rows b b LinearMap.id) = _
    rw [vertex_matrix]
    change dyadicGyration d (counts A) (rows b b LinearMap.id) = _
    rw [rows_id]
    have h := dyadicGyration_nonnegative (d := d) hd A (1 : CountedMatrixOverlap.CountMat _ _)
    have hi : counts (1 : CountedMatrixOverlap.CountMat (Fintype.card F.V) (Fintype.card F.V)) = 1 := by
      simp only [counts, Matrix.map_one, map_zero, map_one]
    change dyadicGyration d (counts A) 1 = _
    change dyadicGyration d (counts A) (counts 1) = _ at h
    rw [hi, SourceOnly.RankedTimeRecoding.relative_time, map_natCast] at h
    rw [Fintype.card_congr (orbitChart F d)] at h
    exact h
  have hsq := closed_square (d := d) hd b c (vertex F).time LinearMap.id
    (vertex F).time (LinearMap.id_comp _) (LinearMap.comp_id _)
  refine ⟨hsq,?_⟩
  have he : value (d := d) b b (vertex F).time LinearMap.id =
      value (d := d) c c (vertex F).time LinearMap.id :=
    add_left_cancel ((add_comm _ _).trans hsq)
  have hc := he.symm.trans h₀
  simpa only [value, rows_id] using hc

end SourceOnly.PresentationTimeCochain
