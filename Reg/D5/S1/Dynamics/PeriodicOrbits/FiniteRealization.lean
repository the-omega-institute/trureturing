import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.PeriodicOrbits.FiniteRealization

namespace Reg.D5.S1.Dynamics.PeriodicOrbits.FiniteRealization

open LeanInformationAudit Function
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
open _root_.D5.S1.Dynamics.PeriodicOrbits.FiniteRealization

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ → ℕ) {M : ℕ}, 0 < M →
    ((∃ σ : Equiv.Perm (Fin (a M)), σ ^ M = 1 ∧
      ∀ d ∈ M.divisors, fixedCount σ d = (R.readout () () a) d) ↔
    ∀ d ∈ M.divisors, 0 ≤ delta a d ∧ (d : ℤ) ∣ delta a d)

abbrev sourceScope := type_of% (@finite_realization_iff)

private theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h a M hM
    exact @h a M hM
  · intro h a M hM
    exact @h a M hM

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hz : ∀ d ∈ Nat.divisors 1,
      0 ≤ delta (fun _ => 0) d ∧ (d : ℤ) ∣ delta (fun _ => 0) d := by
    intro d hd
    simp [delta]
  obtain ⟨σ, _, hσ⟩ := (@h (fun _ => 0) 1 (by decide)).mpr hz
  have hc := hσ 1 (by simp)
  simp [fixedCount, rejected, realize] at hc

def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@finite_realization_iff), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have hzero := congrFun h 0
    change 0 = 1 at hzero
    omega

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@finite_realization_iff) (Realization signature) Unit Unit where
  unitName := `D5.S1.Dynamics.PeriodicOrbits.FiniteRealization.finite_realization_iff.__information_unit
  realizationName := `Reg.D5.S1.Dynamics.PeriodicOrbits.FiniteRealization.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ _ a => a) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.PeriodicOrbits.FiniteRealization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Dynamics.PeriodicOrbits.FiniteRealization
