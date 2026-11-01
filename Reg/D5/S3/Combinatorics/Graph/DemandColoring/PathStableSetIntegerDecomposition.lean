import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition
open _root_.D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S1.Words.AdmissibleWords.PathStableSetPolytope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Pointwise
noncomputable section

namespace NaturalLayers
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ n : ℕ, ℕ × (Fin n → ℕ)) (fun p => Fin p.1) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ p i => p.2.2 i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (z : Fin n → ℕ),
    (∀ i, z i ≤ k) → (∀ i j, i.val + 1 = j.val → z i + z j ≤ k) →
    ∃ W : Fin k → Fin n → Bool, (∀ c, Adm n (W c)) ∧
      ∀ i, (Finset.univ.filter (fun c => W c i = true)).card = R.readout () ⟨n,k,z⟩ i

def registration : Registration arena (type_of% (@exists_admissible_layers)) := by
  classical
  have hbad : ¬ arena.Law rejected := by
    intro h
    obtain ⟨W, _, count⟩ := h 1 0 (fun _ => 0) (by simp) (by simp)
    have impossible := count 0
    simpa [rejected, realize, signature] using impossible
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨exists_admissible_layers, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := ?_ }
  intro i
  refine ⟨⟨2, 1, fun v => v.val⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
  change (0 : ℕ) ≠ 1
  decide

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration
      (@exists_admissible_layers)
      (type_of% (realize signature (fun (_ : Unit) (p : signature.Params) (i : Fin p.1) => p.2.2 i)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition.exists_admissible_layers.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition.NaturalLayers.registration
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
    (fun (_ : Unit) (p : signature.Params) (i : Fin p.1) => p.2.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","arg","body","arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }
end NaturalLayers

namespace LatticeDecomposition
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ n : ℕ, ℕ × (Fin n → ℤ)) (fun p => Fin p.1) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p i => (p.2.2 i : ℝ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (q : Fin n → ℤ),
    (fun i => (q i : ℝ)) ∈ (k : ℝ) • polytope n ↔
      ∃ W : Fin k → Fin n → Bool, (∀ c, Adm n (W c)) ∧
        (fun i => R.readout () ⟨n,k,q⟩ i) = ∑ c, occupancy (W c)

def registration : Registration arena (type_of% (@lattice_mem_nat_smul_polytope_iff)) := by
  classical
  have hbad : ¬ arena.Law rejected := by
    intro h
    have member : (fun _ : Fin 1 => ((0 : ℤ) : ℝ)) ∈ ((0 : ℕ) : ℝ) • polytope 1 := by
      refine ⟨0, ⟨by simp, by simp⟩, ?_⟩
      funext i
      simp
    obtain ⟨W, _, equal⟩ := (h 1 0 (fun _ => 0)).mp member
    have impossible := congrFun equal 0
    simpa [rejected, realize, signature] using impossible
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨lattice_mem_nat_smul_polytope_iff, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := ?_ }
  intro i
  refine ⟨⟨2, 1, fun v => (v.val : ℤ)⟩, (0 : Fin 2), (1 : Fin 2), ?_⟩
  change ((0 : ℤ) : ℝ) ≠ ((1 : ℤ) : ℝ)
  norm_num

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration
      (@lattice_mem_nat_smul_polytope_iff)
      (type_of% (realize signature
        (fun (_ : Unit) (p : signature.Params) (i : Fin p.1) => (p.2.2 i : ℝ))
        (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition.lattice_mem_nat_smul_polytope_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition.LatticeDecomposition.registration
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
    (fun (_ : Unit) (p : signature.Params) (i : Fin p.1) => (p.2.2 i : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","arg","arg","body","arg","fn","arg","body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }
end LatticeDecomposition

end
end Reg.D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition
