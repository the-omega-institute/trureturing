import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostRelativePBW

/-! Source readouts of the actual relative ghost words and their original mode actions. -/

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostRelativePBW

open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostRelativePBW
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ v => v) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (∀ (B C : Finset ℕ), positiveSet B → positiveSet C → R.readout () () (W B C) = Wcoord B C) ∧
    (∀ p : pairCarrier, (basisEquiv (Finsupp.single p 1) : Fock) = R.readout () () (W p.1.1 p.1.2)) ∧
    Function.Bijective basisEquiv ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      R.readout () () (bneg r (W B C)) =
      if r ∈ B then 0 else (-1 : ℂ) ^ bPrefix r B • W (insert r B) C) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      R.readout () () (c (r : ℤ) (W B C)) =
      if r ∈ B then (-1 : ℂ) ^ bPrefix r B • W (B.erase r) C else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      R.readout () () (cneg r (W B C)) =
      if r ∈ C then 0 else (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (insert r C)) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      R.readout () () (b (r : ℤ) (W B C)) =
      if r ∈ C then (-1 : ℂ) ^ (B.card + cPrefix r C) • W B (C.erase r) else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      R.readout () () (bneg r (c (r : ℤ) (W B C))) =
      if r ∈ B then W B C else 0) ∧
    (∀ (r : ℕ) (B C : Finset ℕ), 1 ≤ r → positiveSet B → positiveSet C →
      R.readout () () (cneg r (b (r : ℤ) (W B C))) =
      if r ∈ C then W B C else 0) ∧
    (∀ (B C : Finset ℕ), positiveSet B → positiveSet C →
      invB (occ B C) = B ∧ invC (occ B C) = C) ∧
    (∀ S : Finset ℕ, 3 ∉ S → occ (invB S) (invC S) = S) ∧
    (∀ r : ℕ, 1 ≤ r → c (r : ℤ) down = 0 ∧ b (r : ℤ) down = 0)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

private theorem source_bridge : (type_of% @relative_pbw_complete) ↔ arena.Law actual := by
  constructor
  · rintro ⟨hw, hu, hbij, hbn, hcp, hcn, hbp, hpb, hpc, hib, hio, hv⟩
    exact ⟨hw, fun p => congrArg Subtype.val (hu p), hbij, hbn, hcp, hcn, hbp,
      hpb, hpc, hib, hio, hv⟩
  · rintro ⟨hw, hu, hbij, hbn, hcp, hcn, hbp, hpb, hpc, hib, hio, hv⟩
    exact ⟨hw, fun p => Subtype.ext (hu p), hbij, hbn, hcp, hcn, hbp,
      hpb, hpc, hib, hio, hv⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.1 ∅ ∅ (by intro t ht; simp at ht) (by intro t ht; simp at ht)
  change (0 : Fock) = Wcoord ∅ ∅ at he
  have hn : Wcoord ∅ ∅ ≠ 0 := by
    simp [Wcoord, sign, signExponent, occ, ket]
  exact hn he.symm

def family : Registration arena (type_of% @relative_pbw_complete) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp relative_pbw_complete, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), vacuum, 0, ?_⟩
    simp [actual, realize, vacuum, ket]

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@relative_pbw_complete) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostRelativePBW.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostRelativePBW.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Unit
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostRelativePBW
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Fermionic.BcGhostRelativePBW
