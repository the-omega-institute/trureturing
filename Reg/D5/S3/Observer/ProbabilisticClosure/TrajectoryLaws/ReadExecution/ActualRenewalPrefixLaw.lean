import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution
open ActualRenewalStopping ActualRenewalPrefixLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory
universe u v w

structure WordParams where
  S : Type u
  R : Type v
  labels : Set S
  update : S → Bool → R → S
  k : ℕ

abbrev wordSignature : Signature where
  Params := WordParams.{u,v}
  State p := p.S × (Fin (p.k + 1) → p.R)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.S
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ p x => word p.labels p.update p.k x.1 x.2) (fun e => nomatch e)
def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ _ x => x.1) (fun e => nomatch e)
def wordArena : Arena where
  signature := wordSignature.{u,v}
  Law F := ∀ {S : Type u} {R : Type v} (L : Set S) (U : S → Bool → R → S)
    (s : S) (r : ℕ → R) (a : ℕ) (K : ℕ → ℕ),
    epoch L U s r a K 0 = F.readout () ⟨S,R,L,U,a⟩ (s, fun j => r j.val) ∧
    ∀ n, epoch L U s r a K (n + 1) = F.readout () ⟨S,R,L,U,K n⟩
      (epoch L U s r a K n, fun j => r (clock a K n + j.val))

private theorem word_rejected : ¬ wordArena.{u,v}.Law wordRejected := by
  intro h
  let U : ULift.{u} Bool → Bool → ULift.{v} Unit → ULift.{u} Bool := fun _ _ _ => ⟨true⟩
  have hh := (h (∅ : Set (ULift.{u} Bool)) U ⟨false⟩ (fun _ => ⟨()⟩) 0 (fun _ => 0)).1
  have he := (actual_words (∅ : Set (ULift.{u} Bool)) U ⟨false⟩ (fun _ => ⟨()⟩) 0 (fun _ => 0)).1
  rw [he] at hh
  change (⟨true⟩ : ULift.{u} Bool) = ⟨false⟩ at hh
  cases hh

def wordRecord : Registration wordArena.{u,v} (type_of% (@actual_words.{u,v})) where
  actual := wordActual
  bridge := Iff.rfl
  variation := ⟨actual_words, wordRejected, word_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordRejected, ?_, rfl, word_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    let U : ULift.{u} Bool → Bool → ULift.{v} Bool → ULift.{u} Bool := fun _ _ r => ⟨r.down⟩
    refine ⟨⟨ULift.{u} Bool,ULift.{v} Bool,∅,U,0⟩,
      (⟨false⟩,fun _ => ⟨false⟩), (⟨false⟩,fun _ => ⟨true⟩), ?_⟩
    change (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩
    decide

def wordRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_words.{u,v}) (type_of% (realize wordSignature.{u,v}
      (fun _ p x => word p.labels p.update p.k x.1 x.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `ActualRenewalPrefixLaw.actual_words.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw.wordRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨wordArena⟩, objectArena := .source ⟨wordArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source wordArena ⟨wordRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent,
  readout := some (realize wordSignature.{u,v}
    (fun _ p x => word p.labels p.update p.k x.1 x.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw,
    definition := none, coordinates := #[0,1,2,3,4,5,6,7],
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

structure MeasureParams where
  Ω : Type u
  m : MeasurableSpace Ω
  P : @Measure Ω m
abbrev massSignature : Signature where
  Params := MeasureParams.{u}
  State p := Set p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def massActual : Realization massSignature :=
  realize massSignature (fun _ p E => p.P E) (fun e => nomatch e)
def massRejected : Realization massSignature :=
  realize massSignature (fun _ _ _ => 1) (fun e => nomatch e)
def massArena : Arena where
  signature := massSignature.{u}
  Law F := ∀ {Ω : Type u} [m : MeasurableSpace Ω] {S : Type v} {R : Type w}
    [MeasurableSpace S] [MeasurableSpace R]
    (P : Measure Ω) (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    (η : Measure S) (a f : PMF ℕ) (ρ : Measure R) [IsProbabilityMeasure ρ]
    (_ : Measurable I) (_ : Measurable τ) (_ : ∀ j, Measurable (fun ω => K ω j))
    (_ : ∀ j, Measurable (fun ω => ξ ω j)) (_ : Primitive P I τ K ξ η a f ρ)
    (n : ℕ) (D : (q : ℕ × (Fin n → ℕ)) → Set (S × (Fin (cut q.1 q.2) → R)))
    (_ : ∀ q, MeasurableSet (D q)) (k : ℕ) (B : Set (Fin (k + 1) → R)) (_ : MeasurableSet B),
    F.readout () ⟨Ω,m,P⟩ (pastEvent I τ K ξ n D ∩ {ω | K ω n = k} ∩
      (fun ω j => ξ ω (clock (τ ω) (K ω) n + j.val)) ⁻¹' B) =
    F.readout () ⟨Ω,m,P⟩ (pastEvent I τ K ξ n D) * f k *
      (Measure.pi fun _ : Fin (k + 1) => ρ) B

private theorem mass_rejected : ¬ massArena.{u,v,w}.Law massRejected := by
  intro h
  let E := ULift.{u} Empty
  let A := ULift.{v} Unit
  let R := ULift.{w} Unit
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace R := ⊤
  let I : E → A := fun e => nomatch e.down
  let τ : E → ℕ := fun e => nomatch e.down
  let K : E → ℕ → ℕ := fun e => nomatch e.down
  let ξ : E → ℕ → R := fun e => nomatch e.down
  let ρ : Measure R := Measure.dirac ⟨()⟩
  have hp : Primitive (0 : Measure E) I τ K ξ (0 : Measure A)
      (PMF.pure 0) (PMF.pure 0) ρ := by
    intro n a l r D B hD hB
    simp
  have hh := h (0 : Measure E) I τ K ξ (0 : Measure A) (PMF.pure 0) (PMF.pure 0) ρ
    (by fun_prop) (by fun_prop) (fun _ => by fun_prop) (fun _ => by fun_prop) hp
    0 (fun _ => Set.univ) (fun _ => MeasurableSet.univ) 0 ∅ MeasurableSet.empty
  simpa [massRejected, realize] using hh

def massRecord : Registration massArena.{u,v,w} (type_of% (@random_cut_freshness.{v,w,u})) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨random_cut_freshness, massRejected, mass_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨massRejected, ?_, rfl, mass_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    let A := ULift.{u} Bool
    letI : MeasurableSpace A := ⊤
    refine ⟨⟨A,inferInstance,Measure.dirac ⟨false⟩⟩, ∅, Set.univ, ?_⟩
    simp [massActual, realize]

def massRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@random_cut_freshness.{v,w,u}) (type_of% (realize massSignature.{u}
      (fun _ p E => p.P E) (fun e => nomatch e))) Unit Unit := {
  unitName := `ActualRenewalPrefixLaw.random_cut_freshness.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw.massRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨massArena⟩, objectArena := .source ⟨massArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source massArena ⟨massRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent,
  readout := some (realize massSignature.{u} (fun _ p E => p.P E) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw
