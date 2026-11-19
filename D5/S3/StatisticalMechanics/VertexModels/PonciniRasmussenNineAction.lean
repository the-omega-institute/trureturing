/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Module]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result; premises=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition_check,D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.unit_check
   digest: The checked table gives exact generator multiplication in the literal diagram algebra. -/

/-
admission_basis: open-problem-resolution (#27843; Refuted)
escape_witness: none (the settlement of the external open problem is the new content)
Qualified-name abbreviations:
PonciniRasmussenMinpolyRefutation = D5.S3.StatisticalMechanics.PonciniRasmussenMinpolyRefutation

Direct frozen dependencies (declaration statement_ids):
D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.NCMatching
  sha256:e57e27461371a52ec60ddecf793e8636b33575dfd226354a0a39adeb4fc8c180
D5/S3/Topology/FiniteMatchingClosure.Boundary
  sha256:2d22740b62cc9ff6a486d404f032436c21abd62130e080eb9e91719ecefa9bc6
D5/S3/Topology/FiniteMatchingClosure.Matching
  sha256:fd9df4ba1fc572f200a8c9ff58f36e53a205ade28d7c790a87120a8723a6cdb9
D5/S3/Topology/FiniteMatchingClosure.cupcapMatching
  sha256:c244a1d0c295526be0811c97ed793929c5a156f92b1269a8c33c7bfda9bf3109
D5/S3/Topology/FiniteMatchingClosure.mate
  sha256:28b6db6a4ff9477dd543699cd3439ba967d854c089c412870c9eb135520ccf46
D5/S3/Topology/FiniteMatchingComposition.composite
  sha256:916faedcd34e169a2fbdf6728df71f94600d26fc1f3c6b285d74c8f06225beff
D5/S3/Topology/FiniteMatchingComposition.internalLoopCount
  sha256:93bdce1ab5e61437907986b6f2bdde47b0b5f569fbacb1d341051b76d3d98b2c
D5/S3/Topology/FiniteMatchingSewing.matching_ext
  sha256:c122a00bd61ef1c7696ea12717caa82fe0b7d18ae95f1c43e0f1984a19ffa070
unit_basis: proof_shape=bind-only; consumers=PonciniRasmussenMinpolyRefutation.annihilator_aeval
generator_basis: proof_shape=bind-only; consumers=PonciniRasmussenMinpolyRefutation.sparse_lift
-/
import D5.S3.StatisticalMechanics.VertexModels.PonciniRasmussenNineDiagrams
import D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
import D5.S3.Topology.FiniteMatchingClosure
import D5.S3.Topology.FiniteMatchingComposition
import D5.S3.Topology.FiniteMatchingSewing
import D5.S3.Topology.CupCapComposition

set_option autoImplicit false
noncomputable section
namespace D5.S3.StatisticalMechanics.PonciniRasmussenNineAction
open D5.S3.StatisticalMechanics.PonciniRasmussenNineDiagrams
open D5.S3.Combinatorics.PerfectMatchings.PlanarDiagramAlgebra
open D5.S3.Topology.FiniteMatchingClosure
open D5.S3.Topology.FiniteMatchingComposition
open D5.S3.Topology.FiniteMatchingSewing
open D5.S3.Topology.CupCapComposition
/-- The last coordinate is the literal through-strand identity. -/
theorem unit_basis {R : Type*} [CommRing R] :
    (MonoidAlgebra.single (diagram ⟨4861,by omega⟩) 1 : TL R 9) = 1 := by
  change MonoidAlgebra.single _ 1 = MonoidAlgebra.single _ 1
  congr 1
  apply Subtype.ext
  exact matching_ext (unit_check)

/-- Every tabulated transition is left multiplication by the literal cup-cap diagram. -/
theorem generator_basis {R : Type*} [CommRing R] (g : Fin 8) (i : Fin 4862) :
    (generator g : TL R 9) * MonoidAlgebra.single (diagram i) 1 =
      if ht : (transition g i).val < 4862 then
        MonoidAlgebra.single (diagram ⟨(transition g i).val,ht⟩) 1 else 0 := by
  rw [generator, single_mul_single]
  by_cases ht : (transition g i).val < 4862
  · rw [dite_eq_left ht]
    have hn : (diagram i).val.mate (false,⟨g.val,by omega⟩) ≠
        (false,⟨g.val+1,by omega⟩) := by
      intro h
      have := (transition_check i g).1.mp h
      omega
    rw [ite_eq_left ((internalLoopCount_cupcap_eq_zero_iff g.val (by omega) (diagram i).val).mpr hn)]
    simp only [mul_one]
    congr 1
    apply Subtype.ext
    apply matching_ext
    intro x
    exact (composite_cupcap_mate g.val (by omega) (diagram i).val x).trans
      ((transition_check i g).2 ht x).symm
  · rw [dite_eq_right ht]
    have hp : (diagram i).val.mate (false,⟨g.val,by omega⟩) =
        (false,⟨g.val+1,by omega⟩) := (transition_check i g).1.mpr (by omega)
    have hn := internalLoopCount_cupcap_pos g.val (by omega) (diagram i).val hp
    rw [ite_eq_right (Nat.ne_of_gt hn)]

end D5.S3.StatisticalMechanics.PonciniRasmussenNineAction
