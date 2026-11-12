import D5.S3.Quantum.Foundation.SectionPositiveLift
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Exact original source telescopes with a selected mathematical relation readout.
The enrolled dependent-family realization supplies source bridges. Whole-family
variation, sensitivity, observational dependence and source selection are not
supplied, so these are not complete four-slot registrations. -/

noncomputable section
universe u v
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace
open _root_.D5.S3.Quantum.Foundation.SectionPositiveLift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Foundation.SectionPositiveLift

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

namespace positive_functional_psd_lift

abbrev sourceScope : Prop := type_of% (@positive_functional_psd_lift.{u,v})

def arena : Arena where
  signature := relationSignature.{0}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (L : Submodule ℝ (HermitianMat ι 𝕜)) (hI : (1 : HermitianMat ι 𝕜) ∈ L)
    (f : L →ₗ[ℝ] ℝ) (hf : ∀ X : L, 0 ≤ (X : HermitianMat ι 𝕜) → 0 ≤ f X),
    ∃ E : HermitianMat ι 𝕜, 0 ≤ E ∧ ∀ X : L, O.readout () ⟨ℝ, Eq⟩ (f X) ⟪E, (X : HermitianMat ι 𝕜)⟫_ℝ

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@positive_functional_psd_lift.{u,v})

end positive_functional_psd_lift

namespace rank_one_deflation

abbrev sourceScope : Prop := type_of% (@rank_one_deflation.{u,v})

def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (M : HermitianMat ι 𝕜) (hM : 0 ≤ M)
    (v : ι → 𝕜) (hv : star v ⬝ᵥ (M.mat *ᵥ v) = 1),
    O.readout () ⟨HermitianMat ι 𝕜, (· ≤ ·)⟩ 0 ((rankOne v).conj M.mat) ∧ 0 ≤ M - (rankOne v).conj M.mat

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@rank_one_deflation.{u,v})

end rank_one_deflation

namespace common_original_effect_lift

abbrev sourceScope : Prop := type_of% (@common_original_effect_lift.{u,v})

def arena : Arena where
  signature := relationSignature.{u}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (L : Submodule ℝ (HermitianMat ι 𝕜)) (hI : (1 : HermitianMat ι 𝕜) ∈ L)
    (v : ι → 𝕜) (hv : star v ⬝ᵥ v = 1) (hp : rankOne v ∈ L)
    (m : ℕ) (w : Fin m → (ι → 𝕜))
    (hq : ∀ j, rankOne (w j) ∈ L),
    (∃ f : L →ₗ[ℝ] ℝ, Proper f ∧ f ⟨rankOne v, hp⟩ = 1 ∧
      ∀ j, f ⟨rankOne (w j), hq j⟩ = 0) ↔
    ∃ M ∈ lifts L, ∀ j, O.readout () ⟨𝕜, Eq⟩ (star v ⬝ᵥ (M.mat *ᵥ w j)) 0

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@common_original_effect_lift.{u,v})

end common_original_effect_lift

namespace lift_geometry

abbrev sourceScope : Prop := type_of% (@lift_geometry.{u,v})

def arena : Arena where
  signature := relationSignature.{0}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (L : Submodule ℝ (HermitianMat ι 𝕜)) (hI : (1 : HermitianMat ι 𝕜) ∈ L),
    (lifts L).Nonempty ∧ IsCompact (lifts L) ∧ Convex ℝ (lifts L) ∧
    (∀ M ∈ lifts L, O.readout () ⟨ℝ, Eq⟩ M.trace (Fintype.card ι)) ∧
    (affineSpan ℝ (lifts L)).direction = Lᗮ ∧
    Module.finrank ℝ (affineSpan ℝ (lifts L)).direction = Module.finrank ℝ Lᗮ

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@lift_geometry.{u,v})

end lift_geometry

end Reg.D5.S3.Quantum.Foundation.SectionPositiveLift
