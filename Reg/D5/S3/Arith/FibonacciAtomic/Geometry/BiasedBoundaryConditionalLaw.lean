import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The actual prepend map as the readout of the complete conditional law family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (Omega M cylinder G J)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (H)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory hiding cylinder

abbrev signature : Signature where
  Params := Address
  State _ := Omega
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Omega
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p ω => prepend p ω) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ p : Address, M (cylinder p) ≠ 0) ∧
    (∀ p : Address, (M.restrict (cylinder p)).map (tail p.length) = M (cylinder p) • M) ∧
    (∀ p : Address, MeasurePreserving (R.readout () p) M (conditional p)) ∧
    conditional [] = M ∧
    (∀ (p : Address) (F : G), pullback p F =ᵐ[M] F ∘ prepend p) ∧
    (∀ (p : Address) (F : G), ‖pullback p F‖ ≤ pullbackBound p * ‖F‖) ∧
    (∀ (p : Address) (z : H), conditionalTrace p z =ᵐ[M] (J z) ∘ prepend p) ∧
    (∀ (p : Address) (ω : Omega), tail p.length (prepend p ω) = ω)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℕ => true) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm := (h.2.2.1 []).map_eq
  change M.map (fun _ : Omega => fun _ : ℕ => true) = conditional [] at hm
  rw [h.2.2.2.1] at hm
  have hs : MeasurableSet (cylinder [false]) := by
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)
  have he := congrArg (fun μ : Measure Omega => μ (cylinder [false])) hm
  rw [Measure.map_apply measurable_const hs] at he
  have hempty : (fun _ : Omega => fun _ : ℕ => true) ⁻¹' cylinder [false] = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hp
    have hh := hp 0 (by simp)
    simp at hh
  rw [hempty, measure_empty] at he
  exact h.1 [false] he.symm

def familyRegistration : Registration arena (type_of% conditional_pullback_law) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conditional_pullback_law, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨[], (fun _ : ℕ => false), (fun _ : ℕ => true), ?_⟩
    intro he
    have hh := congrArg (fun ω : Omega => ω 0) he
    change false = true at hh
    exact Bool.noConfusion hh

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@conditional_pullback_law)
    (type_of% (realize signature (fun _ p ω => prepend p ω) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw.conditionalUnit,
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p ω => prepend p ω) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "fn", "fn", "arg"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw
