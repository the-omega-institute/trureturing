/- SOURCE ONLY, UNCOMPILED. Original T visibility delta is required.
The actual phase is compared on the original primitive paths and PathBasis.
The vanishing proof is reused at its ORIGINAL declaration, never duplicated.
-/
import D5.S3.ConceptDynamics.Coding.CountedRelativeGyrationTransport
import D5.S3.ConceptDynamics.Coding.CountedPositiveTriangleModThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
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

/-- T's weaker carrier, applied to P1's literal map; no phase is chosen. -/
def coding {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    (u : TimedEquiv A B) : PathCoding A B := ⟨u.equiv, u.semiconj⟩

/-- Both sides use the same actual PrimitivePath, canonicalPath and FORWARD
offset. Only the sum index changes via the saved orbitBasisEquiv. -/
theorem coding_gyration {n m d : ℕ} [NeZero d]
    {A : CountMat n n} {B : CountMat m m} (u : TimedEquiv A B) :
    pathGyration (d := d) (coding u) = u.gyration d := by
  rw [pathGyration_basis]
  rfl

/-- An endpoint-preserving edge map commutes with every integer translation
coordinate by coordinate, not merely with the induced beam action. -/
def edgeTimed {n : ℕ} {A B : CountMat n n} (e : EdgeCoding A B) :
    TimedEquiv A B where
  equiv := e.path.equiv
  time _ _ := rfl

theorem edgeTimed_three_zero {n d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {A : CountMat n n} (e : EdgeCoding A A) :
    ZMod.castHom hd (ZMod 3) ((edgeTimed e).gyration d) = 0 := by
  have hz := edgeCoding_three_zero (d := d) hd e
  change ZMod.castHom hd (ZMod 3) (pathGyration (d := d) e.path) = 0 at hz
  have hc : coding (edgeTimed e) = e.path := rfl
  rw [← hc, coding_gyration] at hz
  exact hz

/-- The genuine discrepancy is on B, with edge permutation r after s^{-1}.
Its two endpoint identities follow from the SAME actual vertex bijection. -/
def discrepancy {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    (r s : Relabel (countedGraph A) (countedGraph B))
    (hv : r.vertex = s.vertex) : EdgeCoding B B where
  equiv := s.edge.symm.trans r.edge
  source a := by
    change (r.edge (s.edge.symm a)).source = a.source
    rw [r.source, hv]
    exact (s.source (s.edge.symm a)).symm.trans
      (congrArg Edge.source (s.edge.apply_symm_apply a))
  target a := by
    change (r.edge (s.edge.symm a)).target = a.target
    rw [r.target, hv]
    exact (s.target (s.edge.symm a)).symm.trans
      (congrArg Edge.target (s.edge.apply_symm_apply a))

theorem discrepancy_factor {n m : ℕ} {A : CountMat n n} {B : CountMat m m}
    (r s : Relabel (countedGraph A) (countedGraph B))
    (hv : r.vertex = s.vertex) :
    (timed s).comp (edgeTimed (discrepancy r s hv)) = timed r := by
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
    edgeTimed_three_zero hd, add_zero]

end SourceOnly.ActualRelabelResidue
