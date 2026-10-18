/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parallel-edge discrepancy on the original primitive path basis. -/

/- Compare the actual discrepancy on the original primitive paths and canonical PathBasis. Reuse the existing parallel-edge vanishing theorem. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.CountedRelativeGyrationTransport
import D5.S3.ConceptDynamics.Coding.CountedPositiveTriangleModThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.ActualRelabelResidue
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding
open CountedMatrixOverlap (CountMat Edge Path)
open CountedOrderTypeGyration
open CountedRelativeGyrationTransport
open ZeroWindowRelabeling (Relabel)

def timed {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    (r : Relabel (countedGraph A) (countedGraph B)) : TimedEquiv A B :=
  ⟨r.homeomorph.toEquiv, SplitTowerTranslation.relabel_homeomorph_time r⟩

/-- Reuse the owning vanishing proof on the same coordinatewise action and
canonical primitive basis, without exporting its private implementation types. -/
theorem timed_three_zero {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} (r : Relabel (countedGraph A) (countedGraph A))
    (hv : r.vertex = Equiv.refl _) :
    ZMod.castHom hd (ZMod 3) ((timed r).gyration d) = 0 := by
  exact parallel_edge_offset_sum_three_zero hd r.edge
    (fun a => by
      have hs := r.source a
      change (r.edge a).source = r.vertex a.source at hs
      simpa only [hv, Equiv.refl_apply] using hs)
    (fun a => by
      have ht := r.target a
      change (r.edge a).target = r.vertex a.target at ht
      simpa only [hv, Equiv.refl_apply] using ht)
    ((timed r).primitiveEquiv d) (fun _ _ => rfl)

/-- The genuine discrepancy is on B, with edge permutation r after s^{-1}.
Its two endpoint identities follow from the SAME actual vertex bijection. -/
def discrepancy {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    (r s : Relabel (countedGraph A) (countedGraph B))
    (hv : r.vertex = s.vertex) : Relabel (countedGraph B) (countedGraph B) where
  vertex := Equiv.refl _
  edge := s.edge.symm.trans r.edge
  source a := by
    change (countedGraph B).source (r.edge (s.edge.symm a)) = (countedGraph B).source a
    rw [r.source, hv]
    exact (s.source (s.edge.symm a)).symm.trans
      (congrArg Edge.source (s.edge.apply_symm_apply a))
  target a := by
    change (countedGraph B).target (r.edge (s.edge.symm a)) = (countedGraph B).target a
    rw [r.target, hv]
    exact (s.target (s.edge.symm a)).symm.trans
      (congrArg Edge.target (s.edge.apply_symm_apply a))

theorem discrepancy_factor {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    (r s : Relabel (countedGraph A) (countedGraph B))
    (hv : r.vertex = s.vertex) :
    (timed s).comp (timed (discrepancy r s hv)) = timed r := by
  apply TimedEquiv.ext
  intro x
  apply Subtype.ext
  funext t
  change r.edge (s.edge.symm (s.edge (x.val t))) = r.edge (x.val t)
  exact congrArg r.edge (s.edge.symm_apply_apply (x.val t))

/-- Arbitrary parallel edges may change phase; their TOTAL reduced phase
vanishes by the original T proof. No zero phase rule for r is asserted. -/
theorem same_vertex_residue {n m d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} {B : CountMat m m}
    (r s : Relabel (countedGraph A) (countedGraph B))
    (hv : r.vertex = s.vertex) :
    ZMod.castHom hd (ZMod 3) ((timed r).gyration d) =
      ZMod.castHom hd (ZMod 3) ((timed s).gyration d) := by
  rw [← discrepancy_factor r s hv, TimedEquiv.gyration_comp, map_add,
    timed_three_zero hd _ rfl, add_zero]

end SourceOnly.ActualRelabelResidue
