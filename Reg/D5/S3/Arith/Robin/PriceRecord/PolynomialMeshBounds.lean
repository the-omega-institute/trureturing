import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds
import Reg.Support.SingleDependentReadout

/-! Full-family audit operands for polynomial mesh geometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ r k => (((k + 1) ^ r : ℕ) : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ r k => (2 : ℝ) ^ r * (((k ^ r : ℕ) : ℝ)) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ r : ℕ, 2 ≤ r → ∀ k : ℕ, 4 ≤ k →
    let N : ℝ := ((k ^ r : ℕ) : ℝ)
    let H : ℝ := (2 : ℝ) ^ r
    let G : ℝ := (r : ℝ) * (2 : ℝ) ^ (r - 1)
    V.readout () r k ≤ H * N ∧
      V.readout () r k - N ≤ G * (N / (k : ℝ)) ∧
      V.readout () r k ≤ N ^ 2

private theorem source_reconstruction :
    (type_of% (@mesh_geometry)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 2 le_rfl 4 le_rfl).1
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 4, 5, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@mesh_geometry)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@mesh_geometry, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mesh_geometry) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds.mesh_geometry.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ r k => (((k + 1) ^ r : ℕ) : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

/- Source occurrence selection remains absent. The typed family obligations
   alone do not establish a declared_validated source binding. Other public
   helpers retain their separate source reconstruction and audit obligations. -/

end Reg.D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds

namespace Reg.D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds.Interpolation

open Filter
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect (clock pressure price)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ X =>
    Real.eulerMascheroniConstant + Real.log (Real.log X) - 1 / Real.log X -
      pressure (price X)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ r : ℕ, 2 ≤ r → ∀ beta sigma C A : ℝ, 0 ≤ C → 0 ≤ A →
    1 / 2 < sigma → sigma < 1 → 0 ≤ beta → beta - 1 / (r : ℝ) < sigma →
    (∀ X : ℝ, 2 ≤ X → |X - clock X| ≤ C * Real.rpow X beta) →
    (∀ᶠ k : ℕ in atTop,
      -A ≤ (Real.rpow ((k ^ r : ℕ) : ℝ) (1 - sigma) *
        Real.log ((k ^ r : ℕ) : ℝ)) * V.readout () () ((k ^ r : ℕ) : ℝ)) →
    ∃ B : ℝ, 0 ≤ B ∧ ∃ T : ℝ, ∀ X : ℝ, T ≤ X →
      -B ≤ (Real.rpow X (1 - sigma) * Real.log X) * V.readout () () X

private theorem actual_law : arena.Law actual := @pressure_samples_to_all

private theorem source_reconstruction :
    (type_of% (@pressure_samples_to_all)) ↔ arena.Law actual := Iff.rfl

/- This full-source reconstruction retains the entire real tail, all natural
   mesh exponents and the original full-clock hypothesis. Whole-family
   variation, sensitivity, actual observational dependence and compiler source
   binding remain unsupplied; no complete Contract.Registration is asserted. -/

end Reg.D5.S3.Arith.Robin.PriceRecord.PolynomialMeshBounds.Interpolation
