import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

def sevenOnes : Nat.Partition 7 :=
  ⟨Multiset.replicate 7 1, by simp, by norm_num⟩

def sevenSingle : Nat.Partition 7 :=
  ⟨{7}, by simp, by norm_num⟩

namespace WeightBound

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ Nat.Partition (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (_ : ℕ) p => weight p.parts) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (n : ℕ) _ => n.factorial + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 7 ≤ n → ∀ p : Nat.Partition n, R.readout () n p ≤ n.factorial

def registration : Registration arena (type_of% (@weight_le_factorial)) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hh := h (by decide : 7 ≤ 7) sevenOnes
    change Nat.factorial 7 + 1 ≤ Nat.factorial 7 at hh
    omega
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@weight_le_factorial, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := ?_ }
  intro i
  refine ⟨7, sevenOnes, sevenSingle, ?_⟩
  change weight sevenOnes.parts ≠ weight sevenSingle.parts
  norm_num [sevenOnes, sevenSingle, weight]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_le_factorial)
    (type_of% (realize signature
      (fun (_ : Unit) (_ : ℕ) p => weight p.parts) (fun e => nomatch e)))
    (ℕ → Type) Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight.weight_le_factorial.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight.WeightBound.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (_ : ℕ) p => weight p.parts) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Nat.Partition
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end WeightBound

namespace Maximum

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (_ : Unit) n => maximumWeight n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ : Unit) (_ : ℕ) => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 7 ≤ n → R.readout () () n = n.factorial

def registration : Registration arena (type_of% (@maximum_weight_eq_factorial)) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hh := h (by decide : 7 ≤ 7)
    change 0 = Nat.factorial 7 at hh
    norm_num at hh
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@maximum_weight_eq_factorial, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := ?_ }
  intro i
  refine ⟨(), 7, 8, ?_⟩
  dsimp only [actual, realize]
  rw [maximum_weight_eq_factorial (n := 7) (by decide),
    maximum_weight_eq_factorial (n := 8) (by decide)]
  decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@maximum_weight_eq_factorial)
    (type_of% (realize signature
      (fun (_ : Unit) (_ : Unit) n => maximumWeight n) (fun e => nomatch e)))
    Type Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight.maximum_weight_eq_factorial.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight.Maximum.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (_ : Unit) n => maximumWeight n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Maximum

namespace Small

abbrev signature := Maximum.signature
abbrev actual := Maximum.actual
abbrev rejected := Maximum.rejected

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 1 = 1 ∧ R.readout () () 2 = 6 ∧ R.readout () () 3 = 21 ∧
    R.readout () () 4 = 72 ∧ R.readout () () 5 = 155 ∧ R.readout () () 6 = 1296

def registration : Registration arena (type_of% maximum_weight_small) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hh := h.1
    change (0 : ℕ) = 1 at hh
    norm_num at hh
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨maximum_weight_small, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := Maximum.registration.dependence }

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    maximum_weight_small
    (type_of% (realize signature
      (fun (_ : Unit) (_ : Unit) n => maximumWeight n) (fun e => nomatch e)))
    Type Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight.maximum_weight_small.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight.Small.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (_ : Unit) n => maximumWeight n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Small


namespace Absorption

abbrev signature := Maximum.signature
abbrev actual := Maximum.actual

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ : Unit) n => if n = 1 then 2 else 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s n : ℕ}, 1 ≤ s → s ≤ n →
    R.readout () () s * (n - s + 1).factorial ≤ R.readout () () n

def registration : Registration arena (type_of% (@maximum_weight_mul_factorial_le)) := by
  have hbad : ¬ arena.Law rejected := by
    intro h
    have hh := h (s := 1) (n := 2) (by decide) (by decide)
    change 2 * Nat.factorial 2 ≤ 1 at hh
    norm_num at hh
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@maximum_weight_mul_factorial_le, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := Maximum.registration.dependence }

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@maximum_weight_mul_factorial_le)
    (type_of% (realize signature
      (fun (_ : Unit) (_ : Unit) n => maximumWeight n) (fun e => nomatch e)))
    Type Unit := {
  unitName := `D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight.maximum_weight_mul_factorial_le.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight.Absorption.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (_ : Unit) n => maximumWeight n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Absorption

end
end Reg.D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight

