import D5.S3.Quantum.Foundation.SectionROGFrame
import Reg.D5.S3.Quantum.Foundation.SectionPositiveLift

/-! Original whole-carrier and ROG-frame source reconstruction. The selected
relation readouts retain every original hypothesis and conclusion. Complete
variation, sensitivity, dependence and source-selection evidence is unsupplied. -/

noncomputable section
universe u v
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace
open _root_.D5.S3.Quantum.Foundation.SectionPositiveLift
open _root_.D5.S3.Quantum.Foundation.SectionROGFrame
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.SectionPositiveLift

namespace Reg.D5.S3.Quantum.Foundation.SectionROGFrame

namespace whole_pure_carrier

abbrev sourceScope : Prop := type_of% (@whole_pure_carrier.{u,v})

def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (L : Submodule ℝ (HermitianMat ι 𝕜)) (hrog : ROG L) ,
    O.readout () ⟨Set (HermitianMat ι 𝕜), Eq⟩ ((base L).extremePoints ℝ) (pureRanks L)

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@whole_pure_carrier.{u,v})

end whole_pure_carrier

namespace rog_frame

abbrev sourceScope : Prop := type_of% (@rog_frame.{u,v})

def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (L : Submodule ℝ (HermitianMat ι 𝕜)) (hI : (1 : HermitianMat ι 𝕜) ∈ L)
    (hrog : ROG L) (v : EuclideanSpace 𝕜 ι) (hv : ‖v‖ = 1) (hvL : rankOne v ∈ L)
    (i₀ : ι) ,
    ∃ b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι), O.readout () ⟨EuclideanSpace 𝕜 ι, Eq⟩ (b i₀) v ∧
      (∀ j, rankOne (b j) ∈ L) ∧
      (∀ j, rankOne (b j) ∈ (base L).extremePoints ℝ) ∧
      (∑ j, rankOne (b j)) = 1

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@rog_frame.{u,v})

end rog_frame

end Reg.D5.S3.Quantum.Foundation.SectionROGFrame
