import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Audits of the integer embedding and projected charge readouts in the two P48q dual laws. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual

open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix

open private normMatrix normEntry normEntry_eq from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNormImageCertificate

noncomputable section

local notation "ZRow" => (Fin 48 → ℤ)
local notation "CRow" => (Fin 48 → ℂ)
local notation "c" => Int.castRingHom ℂ
local notation "embed" => (fun a : ZRow => c ∘ a)
local notation "B" => Matrix.toBilin' (nebeGram.map c)
local notation "A" => nebeOrderThree
local notation "T" => rowAction ℂ A
local notation "N" => (1 + A + A ^ 2 : Matrix (Fin 48) (Fin 48) ℤ)

abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ZRow) (fun _ => CRow)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)

private theorem rejected_at_zero : ¬ ∃ a : ZRow, (0 : CRow) = rejected.readout () () a := by
  rintro ⟨a, ha⟩
  exact zero_ne_one (congrFun ha 0)

namespace Ambient

def actual : Realization signature :=
  realize signature (fun _ _ a => c ∘ a) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ μ : CRow,
    (∀ x : ZRow, ∃ m : ℤ, B (embed x) μ = (m : ℂ)) ↔
      ∃ a : ZRow, μ = R.readout () () a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact rejected_at_zero ((h 0).mp (fun x => ⟨0, by simp⟩))

def family : Registration arena (type_of% gram_dual_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gram_dual_iff, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, Pi.single 0 1, ?_⟩
    intro h
    have hcoord := congrFun h (0 : Fin 48)
    change c (0 : ℤ) = c ((Pi.single 0 1 : ZRow) 0) at hcoord
    have hint : (0 : ℤ) = (Pi.single 0 1 : ZRow) 0 := Int.cast_injective (α := ℂ) hcoord
    exact zero_ne_one (hint.trans (by simp))

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    gram_dual_iff (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual.gram_dual_iff.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual.Ambient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => c ∘ a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Ambient

namespace Fixed

def actual : Realization signature :=
  realize signature (fun _ _ a => (3 : ℂ)⁻¹ • embed (a ᵥ* N)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ μ : CRow,
    (T μ = μ ∧ ∀ x : ZRow, x ᵥ* A = x → ∃ m : ℤ, B (embed x) μ = (m : ℂ)) ↔
      ∃ a : ZRow, μ = R.readout () () a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact rejected_at_zero ((h 0).mp ⟨(rowAction ℂ A).map_zero, fun x _ => ⟨0, by simp⟩⟩)

set_option maxRecDepth 4096 in
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, Pi.single 0 1, ?_⟩
  intro h
  have hzero := congrFun h (0 : Fin 48)
  change (3 : ℂ)⁻¹ * c (((0 : ZRow) ᵥ* N) 0) =
    (3 : ℂ)⁻¹ * c (((Pi.single 0 1 : ZRow) ᵥ* N) 0) at hzero
  rw [Matrix.zero_vecMul, Matrix.single_one_vecMul] at hzero
  have hcast : c (N 0 0) = 0 := by
    simpa [mul_eq_zero] using hzero.symm
  have hdiag : normMatrix 0 0 = 0 := by
    apply Int.cast_injective (α := ℂ)
    change c (N 0 0) = c 0
    rw [map_zero]
    exact hcast
  have hne : normEntry 0 0 ≠ 0 := by decide +kernel
  exact hne ((normEntry_eq 0 0).symm.trans hdiag)

def family : Registration arena (type_of% fixed_dual_iff_projected_charge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_dual_iff_projected_charge, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    fixed_dual_iff_projected_charge (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual.fixed_dual_iff_projected_charge.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual.Fixed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => (3 : ℂ)⁻¹ • embed (a ᵥ* N)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Fixed

end

end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual
