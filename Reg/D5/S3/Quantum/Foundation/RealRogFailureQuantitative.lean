import D5.S3.Quantum.Foundation.RealRogFailureQuantitative
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact reconstruction and positivity for both new public source families.
Whole-family intervention, sensitivity, observational dependence and a lawful
four-slot source selection remain unsupplied. There is no declared_validated
registration in this mirror. -/

noncomputable section
universe u
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise

namespace Reg.D5.S3.Quantum.Foundation.RealRogFailureQuantitative

open _root_.D5.S3.Quantum.Foundation.RealRogFailureQuantitative
open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Coordinates where
  Index : Type u
  [finite : Fintype Index]
  [decidable : DecidableEq Index]

attribute [instance] Coordinates.finite Coordinates.decidable

abbrev matrixSignature : Signature where
  Params := Coordinates.{u}
  State P := (P.Index → ℝ) × (P.Index → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Matrix P.Index P.Index ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def matrixActual : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ P vw =>
    (1 / 2 : ℝ) • (vecMulVec vw.2 vw.2 +
      ((Fintype.card P.Index : ℝ) - 1)⁻¹ • (1 - vecMulVec vw.1 vw.1)) -
      ((vw.1 ⬝ᵥ vw.2) ^ 2 / (2 * (Fintype.card P.Index : ℝ))) • vecMulVec vw.1 vw.1)
    (fun e => nomatch e)

abbrev matrixArena : Arena where
  signature := matrixSignature.{u}
  Law O := ∀ (P : Coordinates.{u}) (v w : P.Index → ℝ),
    v ⬝ᵥ v = 1 → w ⬝ᵥ w = 1 → 2 ≤ Fintype.card P.Index →
    (O.readout () P (v, w)).PosSemidef

abbrev matrixSourceScope : Prop := type_of% (@midpoint_psd_gap.{u})

theorem matrix_source_bridge : matrixSourceScope.{u} ↔ matrixArena.{u}.Law matrixActual.{u} := by
  constructor
  · intro h P v w hv hw hd
    exact @h P.Index P.finite P.decidable v w hv hw hd
  · intro h Index finite decidable v w hv hw hd
    exact h (@Coordinates.mk Index finite decidable) v w hv hw hd

theorem matrix_actual_positive : matrixArena.{u}.Law matrixActual.{u} :=
  matrix_source_bridge.mp (@midpoint_psd_gap.{u})

structure SectionInputs extends Coordinates.{u} where
  space : Submodule ℝ (Matrix Index Index ℝ)
  cone : PointedCone ℝ space
  unit : space →ₗ[ℝ] ℝ

abbrev comparisonSignature : Signature where
  Params := SectionInputs.{u}
  State P := P.space × P.space
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def comparisonActual : Realization comparisonSignature.{u} :=
  realize comparisonSignature (fun _ P sz => comparison P.cone P.unit sz.1 sz.2)
    (fun e => nomatch e)

abbrev comparisonArena : Arena where
  signature := comparisonSignature.{u}
  Law O := ∀ P : SectionInputs.{u},
    let L := P.space
    let C := P.cone
    let u := P.unit
    let T := fun s z => O.readout () P (s, z)
    (∀ A : L, A ∈ C ↔ (A : Matrix P.Index P.Index ℝ).PosSemidef) →
    (∀ A : L, u A = (A : Matrix P.Index P.Index ℝ).trace) →
    ∀ (j s x : L), (j : Matrix P.Index P.Index ℝ) = 1 →
    ∀ (v w : P.Index → ℝ),
    (s : Matrix P.Index P.Index ℝ) = vecMulVec v v →
    (x : Matrix P.Index P.Index ℝ) = vecMulVec w w →
    v ⬝ᵥ v = 1 → w ⬝ᵥ w = 1 → 2 ≤ Fintype.card P.Index →
    0 < (v ⬝ᵥ w) ^ 2 →
    ∀ f : L →ₗ[ℝ] ℝ, confirms C u s f → f x = 0 →
    let c := (v ⬝ᵥ w) ^ 2
    let y := ((Fintype.card P.Index : ℝ) - 1)⁻¹ • (j - s)
    let m := (1 / 2 : ℝ) • (x + y)
    let δ := c / (2 * (Fintype.card P.Index : ℝ))
    c < 1 ∧ s ∈ base C u ∧ x ∈ base C u ∧ y ∈ base C u ∧ m ∈ base C u ∧
      T s x = 0 ∧ T s y = 0 ∧ (m : Matrix P.Index P.Index ℝ).PosDef ∧ m - δ • s ∈ C ∧
      (∀ g : L →ₗ[ℝ] ℝ, confirms C u s g → δ ≤ g m) ∧ δ ≤ T s m ∧ 0 < δ

abbrev comparisonSourceScope : Prop := type_of% (@normalized_cross_pair_gap.{u})

theorem comparison_source_bridge :
    comparisonSourceScope.{u} ↔ comparisonArena.{u}.Law comparisonActual.{u} := by
  constructor
  · intro h P
    exact @h P.Index P.finite P.decidable P.space P.cone P.unit
  · intro h Index finite decidable L C unit
    exact h (@SectionInputs.mk (@Coordinates.mk Index finite decidable) L C unit)

theorem comparison_actual_positive : comparisonArena.{u}.Law comparisonActual.{u} :=
  comparison_source_bridge.mp (@normalized_cross_pair_gap.{u})

end Reg.D5.S3.Quantum.Foundation.RealRogFailureQuantitative
