/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelCharts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transport both relabel factors through the actual charts. -/

/- Compose the actual vertex and edge charts and transport both RS factors. An individual open edge value is not assumed invariant under basis change. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualRelabelResidue
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualWordLocalizedComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.ActualRelabelResidue
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding
open EssentialWordRealization TwoSidedFiniteInduction TypedPositiveSplitWord
open CountedMatrixOverlap (CountMat)
open CountedOrderTypeGyration
open CountedRelativeGyrationTransport
open ActualPositiveWordPeriodicCochain (chart matrix chartComparison relabelMap)
open ZeroWindowRelabeling (Relabel)
open SourceOnly.ActualWordMatrixPath (D reindex timeMap relabelEdge presentationBasis)
open SourceOnly.KernelRSSquareGyration (rows)

def compose {V E W J X K : Type}
    {G : DirectedMultigraph V E} {H : DirectedMultigraph W J} {I : DirectedMultigraph X K}
    (r : Relabel G H) (s : Relabel H I) : Relabel G I where
  vertex := r.vertex.trans s.vertex
  edge := r.edge.trans s.edge
  source a := (s.source (r.edge a)).trans (congrArg s.vertex (r.source a))
  target a := (s.target (r.edge a)).trans (congrArg s.vertex (r.target a))

def identityRelabel {n : ℕ} (A : CountMat n n) : Relabel (countedGraph A) (countedGraph A) :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ => rfl, fun _ => rfl⟩

section Charts
variable {V E W J : Type} [Fintype V] [Fintype E] [DecidableEq V]
  [Fintype W] [Fintype J] [DecidableEq W]
  {G : DirectedMultigraph V E} {H : DirectedMultigraph W J}
  {n m : ℕ} {A : CountMat n n} {B : CountMat m m}

/-- Literally cH^{-1} after r after cG, on vertices AND numbered edges. -/
def countedInCharts (cG : Relabel (countedGraph A) G)
    (cH : Relabel (countedGraph B) H) (r : Relabel G H) :
    Relabel (countedGraph A) (countedGraph B) := compose (compose cG r) cH.symm

theorem charted_weight (cG : Relabel (countedGraph A) G)
    (cH : Relabel (countedGraph B) H) (r : Relabel G H)
    (d : ℕ) [NeZero d] :
    (relabelEdge r
      ((Pi.basisFun D (Fin n)).map (reindex cG.vertex))
      ((Pi.basisFun D (Fin m)).map (reindex cH.vertex))).weight d =
    (relabelEdge (countedInCharts cG cH r)
      (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin m))).weight d := by
  let cr := countedInCharts cG cH r
  have hf : (reindex r.vertex).toLinearMap.comp (reindex cG.vertex).toLinearMap =
      (reindex cH.vertex).toLinearMap.comp (reindex cr.vertex).toLinearMap := by
    apply LinearMap.ext
    intro z
    funext w
    change z (cG.vertex.symm (r.vertex.symm w)) =
      z (cG.vertex.symm (r.vertex.symm (cH.vertex (cH.vertex.symm w))))
    rw [cH.vertex.apply_symm_apply]
  have hb (z : Fin m → D) :
      (reindex r.vertex).symm (reindex cH.vertex z) =
        reindex cG.vertex ((reindex cr.vertex).symm z) := by
    ext v
    change z (cH.vertex.symm (r.vertex v)) =
      z (cH.vertex.symm (r.vertex (cG.vertex (cG.vertex.symm v))))
    rw [cG.vertex.apply_symm_apply]
  have hs : ((timeMap G).comp (reindex r.vertex).symm.toLinearMap).comp
      (reindex cH.vertex).toLinearMap =
    (reindex cG.vertex).toLinearMap.comp
      ((timeMap (countedGraph A)).comp (reindex cr.vertex).symm.toLinearMap) := by
    apply LinearMap.ext
    intro z
    funext v
    change timeMap G ((reindex r.vertex).symm (reindex cH.vertex z)) v =
      reindex cG.vertex (timeMap (countedGraph A) ((reindex cr.vertex).symm z)) v
    rw [hb]
    exact (congrFun (LinearMap.congr_fun
      (SourceOnly.ActualWordMatrixPath.relabel_time cG) ((reindex cr.vertex).symm z)) v).symm
  have hr := SourceOnly.FiniteKernelLadder.rows_transport
    (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin m))
    (reindex cG.vertex) (reindex cH.vertex)
    (reindex cr.vertex).toLinearMap (reindex r.vertex).toLinearMap hf
  have ht := SourceOnly.FiniteKernelLadder.rows_transport
    (Pi.basisFun D (Fin m)) (Pi.basisFun D (Fin n))
    (reindex cH.vertex) (reindex cG.vertex)
    ((timeMap (countedGraph A)).comp (reindex cr.vertex).symm.toLinearMap)
    ((timeMap G).comp (reindex r.vertex).symm.toLinearMap) hs
  exact congrArg₂ (dyadicGyration d) hr ht

theorem charted_residue (cG : Relabel (countedGraph A) G)
    (cH : Relabel (countedGraph B) H) (r : Relabel G H)
    (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    (relabelEdge r
      ((Pi.basisFun D (Fin n)).map (reindex cG.vertex))
      ((Pi.basisFun D (Fin m)).map (reindex cH.vertex))).weight d =
      ZMod.castHom hd (ZMod 3) ((timed (countedInCharts cG cH r)).gyration d) :=
  (charted_weight cG cH r d).trans
    (relabel_residue hd A B (countedInCharts cG cH r))
end Charts

theorem identity_basis {n : ℕ} (A : CountMat n n) :
    (Pi.basisFun D (Fin n)).map (reindex (identityRelabel A).vertex) =
      Pi.basisFun D (Fin n) := by
  apply DFunLike.ext
  intro i
  rfl

/-- Actual arbitrary-presentation relabel leaf, in P1's chosen two charts. -/
theorem presentation_relabel_residue {F H : Presentation}
    (r : Relabel F.graph H.graph) (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    (relabelEdge r (presentationBasis F) (presentationBasis H)).weight d =
      ZMod.castHom hd (ZMod 3) ((relabelMap r).gyration d) := by
  have hphase : timed (countedInCharts (chart F) (chart H) r) = relabelMap r := by
    apply TimedEquiv.ext
    intro x
    rfl
  exact (charted_residue (chart F) (chart H) r d hd).trans
    (congrArg (fun u => ZMod.castHom hd (ZMod 3) (u.gyration d)) hphase)

/-- The next correction uses the real counted composite chart(F)^{-1} r. -/
theorem chart_forward_residue {F : Presentation} {n : ℕ} {A : CountMat n n}
    (r : Relabel (countedGraph A) F.graph) (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    (relabelEdge r (Pi.basisFun D (Fin n)) (presentationBasis F)).weight d =
      ZMod.castHom hd (ZMod 3) ((chartComparison r).gyration d) := by
  have h := charted_residue (identityRelabel A) (chart F) r d hd
  rw [identity_basis] at h
  have hphase : timed (countedInCharts (identityRelabel A) (chart F) r) =
      chartComparison r := by
    apply TimedEquiv.ext
    intro x
    rfl
  rw [hphase] at h
  exact h

/-- The old^{-1} correction has the literal opposite phase. Neither chart
term is erased, even when the chart preserves beam action. -/
theorem chart_backward_residue {F : Presentation} {n : ℕ} {A : CountMat n n}
    (r : Relabel (countedGraph A) F.graph) (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    (relabelEdge r.symm (presentationBasis F) (Pi.basisFun D (Fin n))).weight d =
      -ZMod.castHom hd (ZMod 3) ((chartComparison r).gyration d) := by
  have h := charted_residue (chart F) (identityRelabel A) r.symm d hd
  rw [identity_basis] at h
  have hphase : timed (countedInCharts (chart F) (identityRelabel A) r.symm) =
      (chartComparison r).symm := by
    apply TimedEquiv.ext
    intro x
    rfl
  rw [hphase, TimedEquiv.gyration_symm, map_neg] at h
  exact h

/-- Immediate actual positive-leaf specialization with BOTH chart terms.
The nonnegative middle factors are the original R,S. -/
theorem positive_leaf_residue {F H : Presentation} {n m : ℕ}
    (R : CountMat n m) (S : CountMat m n)
    (old : Relabel (SplitTowerTranslation.counted (R*S)) F.graph)
    (next : Relabel (SplitTowerTranslation.counted (S*R)) H.graph)
    (d : ℕ) [NeZero d] (hd : 3 ∣ d) :
    (SourceOnly.ActualWordMatrixPath.dictionary (.positive R S old next)).weight d =
      ActualWordLocalizedComparison.localizedCochain d hd (.positive R S old next) := by
  have hp : (SourceOnly.ActualWordMatrixPath.positiveEdge R S).weight d =
      dyadicGyration d (SourceOnly.ActualWordMatrixPath.counts R)
        (SourceOnly.ActualWordMatrixPath.counts S) := by
    exact congrArg₂ (dyadicGyration d)
      (rows_right_standard (SourceOnly.ActualWordMatrixPath.counts R))
      (rows_right_standard (SourceOnly.ActualWordMatrixPath.counts S))
  simp only [SourceOnly.ActualWordMatrixPath.dictionary,
    SourceOnly.FiniteKernelLadder.Path.weight, hp,
    chart_backward_residue old d hd, chart_forward_residue next d hd,
    ActualWordLocalizedComparison.localizedCochain, add_zero, add_assoc]
  rfl

end SourceOnly.ActualRelabelResidue
