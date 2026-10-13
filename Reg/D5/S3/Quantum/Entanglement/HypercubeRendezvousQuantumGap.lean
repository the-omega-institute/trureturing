import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap

open _root_.D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap
open _root_.D5.S3.Quantum.Entanglement.RendezvousVectorSystemGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t d => decide (2 * t < d)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

/-- The full claim with its dimension guard observed, keeping both game values fixed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ t d : ℕ, 2 ≤ t → R.readout () t d = true → omegaQ d t < omegaNS d t

private theorem zero_dimension_value (P : Correlation 0 2) : value P = 0 := by
  classical
  haveI : IsEmpty (Output 0 2) := ⟨fun A => by
    have empty : A.val = ∅ := Finset.eq_empty_of_isEmpty A.val
    have card := A.property
    rw [empty, Finset.card_empty] at card
    exact (by decide : (0 : ℕ) ≠ 2) card⟩
  simp [value]

private theorem zero_supremum (s : Set ℝ) (zero : ∀ r ∈ s, r = 0) : sSup s = 0 := by
  have subset : s ⊆ {0} := Set.subset_singleton_iff.mpr zero
  rcases Set.subset_singleton_iff_eq.mp subset with empty | singleton
  · rw [empty, Real.sSup_empty]
  · rw [singleton, csSup_singleton]

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have qzero : omegaQ 0 2 = 0 := by
    apply zero_supremum
    rintro r ⟨P, _, rfl⟩
    exact zero_dimension_value P
  have nszero : omegaNS 0 2 = 0 := by
    apply zero_supremum
    rintro r ⟨P, _, rfl⟩
    exact zero_dimension_value P
  have bad := law 2 0 (by decide) rfl
  rw [qzero, nszero] at bad
  exact (lt_irrefl (0 : ℝ)) bad

def evidence : Registration arena claim where
  actual := actual
  bridge := by
    constructor
    · intro source t d ht hd
      exact source t d ht (of_decide_eq_true hd)
    · intro law t d ht hd
      exact law t d ht (decide_eq_true hd)
  variation := ⟨by
    intro t d ht hd
    exact result t d ht (of_decide_eq_true hd), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨2, 0, 5, by change false ≠ true; decide⟩

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap.result)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str
    `D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap.result
    "Reg.D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap/\
    Reg.D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap.arena/[anonymous]")
    "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap,
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap,
      name := `D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap.claim,
      path := #[] },
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "domain"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap
