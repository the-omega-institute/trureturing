import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight
import Reg.Support.SingleDependentReadout

/-! Dependent-family audits for adjacency and weight observations on cube words. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight

open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight
open _root_.D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCoordinateMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Word (n : ℕ) := Finset (Fin n) → ZMod 2

abbrev adjacencySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ Word Word

def actualAdjacency : Realization adjacencySignature :=
  realize adjacencySignature (fun _ _ f => adjacency f) (fun e => nomatch e)

def rejectedAdjacency : Realization adjacencySignature :=
  realize adjacencySignature (fun _ _ _ x => if x = ∅ then 1 else 0) (fun e => nomatch e)

private theorem adjacency_dependence : ObservationalDependence adjacencySignature actualAdjacency := by
  intro role
  refine ⟨1, 0, (fun _ => 1), ?_⟩
  intro h
  have hne : adjacency (0 : Word 1) ∅ ≠ adjacency (n := 1) (fun _ => 1) ∅ := by decide
  exact hne (congrFun h ∅)

abbrev congruenceArena : Arena where
  signature := adjacencySignature
  Law R := ∀ {n : ℕ} (f : Word n), Nat.ModEq 4 (weight (R.readout () n f)) (n * weight f)

private theorem rejected_congruence : ¬ congruenceArena.Law rejectedAdjacency := by
  intro h
  have hne : ¬ Nat.ModEq 4 1 0 := by decide
  exact hne (@h 0 0)

def congruenceFamily : Registration congruenceArena (type_of% (@weight_adjacency_mod_four)) where
  actual := actualAdjacency
  bridge := Iff.rfl
  variation := ⟨@weight_adjacency_mod_four, rejectedAdjacency, rejected_congruence⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    congruenceArena.Law actualAdjacency rejectedAdjacency rejected_congruence
  dependence := adjacency_dependence

abbrev momentArena : Arena where
  signature := adjacencySignature
  Law R := ∀ {n : ℕ} (_ : Even n) (i : Fin n) (f : Word n),
    weight (R.readout () n f) % 4 =
      (n % 4) * (∑ x, coordinateBit i x * adjacency f x).val

private theorem rejected_moment : ¬ momentArena.Law rejectedAdjacency := by
  intro h
  have hne : (1 : ℕ) ≠ 0 := by decide
  exact hne (@h 2 (by decide) 0 0)

def momentFamily :
    Registration momentArena (type_of% (@weight_adjacency_mod_four_eq_coordinate_moment)) where
  actual := actualAdjacency
  bridge := Iff.rfl
  variation := ⟨@weight_adjacency_mod_four_eq_coordinate_moment, rejectedAdjacency, rejected_moment⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    momentArena.Law actualAdjacency rejectedAdjacency rejected_moment
  dependence := adjacency_dependence

abbrev weightSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ Word (fun _ => ℕ)

def actualWeight : Realization weightSignature :=
  realize weightSignature (fun _ _ f => weight f) (fun e => nomatch e)

def rejectedWeight : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev kernelArena : Arena where
  signature := weightSignature
  Law R := ∀ {n : ℕ} (_ : 4 ∣ n) (_ : Fin n) (f : Word n) (_ : adjacency f = 0),
    4 ∣ R.readout () n f

private theorem rejected_kernel : ¬ kernelArena.Law rejectedWeight := by
  intro h
  have hzero : adjacency (0 : Word 4) = 0 := by
    funext x
    simp [adjacency]
  have hne : ¬ (4 : ℕ) ∣ 1 := by decide
  exact hne (@h 4 (by decide) 0 0 hzero)

private theorem weight_dependence : ObservationalDependence weightSignature actualWeight := by
  intro role
  refine ⟨0, 0, (fun _ => 1), ?_⟩
  change weight (0 : Word 0) ≠ weight (n := 0) (fun _ => 1)
  decide

def kernelFamily :
    Registration kernelArena (type_of% (@four_dvd_weight_of_adjacency_eq_zero)) where
  actual := actualWeight
  bridge := Iff.rfl
  variation := ⟨@four_dvd_weight_of_adjacency_eq_zero, rejectedWeight, rejected_kernel⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    kernelArena.Law actualWeight rejectedWeight rejected_kernel
  dependence := weight_dependence

def congruenceAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@weight_adjacency_mod_four) (Realization adjacencySignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight.weight_adjacency_mod_four.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight.congruenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨congruenceArena⟩
  objectArena := .source ⟨congruenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source congruenceArena ⟨congruenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjacencySignature (fun _ _ f => adjacency f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def momentAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@weight_adjacency_mod_four_eq_coordinate_moment) (Realization adjacencySignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight.weight_adjacency_mod_four_eq_coordinate_moment.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight.momentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨momentArena⟩
  objectArena := .source ⟨momentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source momentArena ⟨momentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjacencySignature (fun _ _ f => adjacency f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def kernelAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@four_dvd_weight_of_adjacency_eq_zero) (Realization weightSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight.four_dvd_weight_of_adjacency_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight.kernelFamily
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨kernelFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ f => weight f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms congruenceAudit
#print axioms momentAudit
#print axioms kernelAudit

end Reg.D5.S3.Combinatorics.Graph.Hypercube.BinaryAdjacencyWeight
