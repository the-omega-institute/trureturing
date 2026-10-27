import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (Edge H P)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (J indicator)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass (a)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ENNReal

abbrev signature : Signature where
  Params := Address
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p z => S p z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (p : Address) (z : H) (u : Edge), R.readout () p z u = z (descendant p u)) ∧
    (∀ (p : Address) (u : Edge), p.length < (descendant p u).val.length) ∧
    (∀ z : H, R.readout () [] z = z) ∧
    (∀ (A : Finset Address), PrefixFree A → ∀ z : H,
      ∑ p ∈ A, ‖R.readout () p z‖^2 ≤ ‖z‖^2) ∧
    (∀ (p : Address) (z : H),
      HasSum (fun u : Edge => z (descendant p u) • indicator u) (J (R.readout () p z))) ∧
    (∀ (A : Finset Address), PrefixFree A → ∀ (h : ℕ) (z : H),
      ∑ p ∈ A, ‖J (R.readout () p z - P h (R.readout () p z))‖^2 ≤
        (a^(h+1)/(1-a))*‖z‖^2)

private def e : Edge := ⟨[false], by simp⟩

def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.1 [] (lp.single 2 e (1 : ℝ)) e
  change (0 : ℝ) = 1 at he
  exact zero_ne_one he

def familyRegistration : Registration arena (type_of% strict_suffix_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strict_suffix_energy, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨[], (0 : H), lp.single 2 e (1 : ℝ), ?_⟩
    change S [] 0 ≠ S [] (lp.single 2 e (1 : ℝ))
    rw [strict_suffix_energy.2.2.1, strict_suffix_energy.2.2.1]
    intro he
    have hv := congrArg (fun z : H => z e) he
    change (0 : ℝ) = 1 at hv
    exact zero_ne_one hv

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_suffix_energy)
    (type_of% (realize signature (fun _ p z => S p z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix.suffixUnit,
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p z => S p z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix
