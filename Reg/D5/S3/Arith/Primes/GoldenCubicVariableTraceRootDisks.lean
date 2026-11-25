import D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

open D5.S1.Scale
open D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks

namespace Reg.D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => Polynomial ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ => variableBlock) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let observed := R.readout () ()
    VariableTraceLaw observed

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change VariableTraceLaw (fun _ => 0) at h
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hd := h.2.2.2.1 5 2 (by decide) (by decide) (by decide) 0 0 0
  dsimp only at hd
  let ρ : ZMod 25 →+* ZMod 5 := ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)
  have hroot : read (fun _ => (0 : Polynomial ℤ)) 0 (0 : ZMod 5)=0 := by
    simp [D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks.read]
  obtain ⟨x,_,hu⟩ := hd hroot (by rw [map_zero])
  have hz : (0:ZMod 25)=x := hu 0 ⟨by rw [map_zero], by
    simp [D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks.read]⟩
  have h5 : (5:ZMod 25)=x := hu 5 ⟨by decide, by
    simp [D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks.read]⟩
  exact (by decide : (0:ZMod 25)≠5) (hz.trans h5.symm)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hi : i = () := Subsingleton.elim _ _
  subst i
  refine ⟨(), 0, 1, ?_⟩
  change variableBlock 0 ≠ variableBlock 1
  intro h
  have he := congrArg (fun p : Polynomial ℤ => p.eval₂ (Int.castRingHom ℤ) (1:ℤ)) h
  change read variableBlock 0 (1:ℤ) = read variableBlock 1 (1:ℤ) at he
  have ha := actual_variable_trace_root_disks
  change VariableTraceLaw variableBlock at ha
  rw [ha.1 0, ha.1 1] at he
  norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ] at he

def family : Registration arena (type_of% @actual_variable_trace_root_disks) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_variable_trace_root_disks, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@actual_variable_trace_root_disks) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks.actual_variable_trace_root_disks.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => variableBlock) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Primes.GoldenCubicVariableTraceRootDisks
