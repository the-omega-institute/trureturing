import D5.S3.Quantum.Foundation.SectionROGFrame
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Original whole-carrier and ROG-frame source reconstruction. The selected
relation readouts retain every original hypothesis and conclusion. Complete
variation, sensitivity, dependence and source-selection evidence is unsupplied. -/

noncomputable section
universe u v
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace
open _root_.D5.S3.Quantum.Foundation.SectionROGFrame
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Foundation.SectionROGFrame

/-- The observed relation acts on actual mathematical operands. -/
abbrev relationSignature.{w} : Signature where
  Params := Σ A : Type w, A → A → Prop
  State P := P.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def relationActual.{w} : Realization relationSignature.{w} :=
  realize relationSignature (fun _ P x y => P.2 x y) (fun e => nomatch e)

namespace rankOne_nonneg

abbrev sourceScope : Prop := type_of% (@rankOne_nonneg.{u,v})

def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (v : ι → 𝕜), O.readout () ⟨HermitianMat ι 𝕜, (· ≤ ·)⟩ 0 (rankOne v)

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@rankOne_nonneg.{u,v})

end rankOne_nonneg

namespace pair_rankOne

abbrev sourceScope : Prop := type_of% (@pair_rankOne.{u,v})

def arena : Arena where
  signature := relationSignature.{u}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (A : HermitianMat ι 𝕜) (v : ι → 𝕜),
    O.readout () ⟨𝕜, Eq⟩ (⟪A, rankOne v⟫_ℝ : 𝕜) (star v ⬝ᵥ (A.mat *ᵥ v))

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@pair_rankOne.{u,v})

end pair_rankOne


namespace whole_pure_carrier

abbrev sourceScope : Prop := type_of% (@whole_pure_carrier.{u,v})

def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (L : Submodule ℝ (HermitianMat ι 𝕜)) (hrog : ROG L),
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
    (i₀ : ι),
    ∃ b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι), O.readout () ⟨EuclideanSpace 𝕜 ι, Eq⟩ (b i₀) v ∧
      (∀ j, rankOne (b j) ∈ L) ∧
      (∀ j, rankOne (b j) ∈ (base L).extremePoints ℝ) ∧
      (∑ j, rankOne (b j)) = 1

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@rog_frame.{u,v})

end rog_frame

end Reg.D5.S3.Quantum.Foundation.SectionROGFrame
