/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Module]
   utility: none
   digest: The checked table gives exact generator multiplication in the literal diagram algebra. -/
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
