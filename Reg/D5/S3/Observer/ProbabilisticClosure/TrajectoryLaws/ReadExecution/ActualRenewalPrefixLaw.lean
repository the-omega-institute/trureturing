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

def initialArena : Arena where
  signature := massSignature.{u}
  Law F := ∀ {Ω : Type u} [m : MeasurableSpace Ω] {S : Type v} {R : Type w}
    [MeasurableSpace S] [MeasurableSpace R]
    (P : Measure Ω) (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    [Countable S] [MeasurableSingletonClass S]
    (L : Set S) (U : S → Bool → R → S)
    (η : PMF S) (a f : PMF ℕ) (ρ : Measure R) [IsProbabilityMeasure ρ]
    (A C : S → PMF S)
    (_ : ∀ b, Measurable (fun p : S × R => effective L U p.1 b p.2))
    (_ : ∀ s b, ρ.map (effective L U s b) = (if b then C s else A s).toMeasure)
    (_ : Measurable I) (_ : Measurable τ) (_ : ∀ j, Measurable (fun ω => ξ ω j))
    (_ : Primitive P I τ K ξ η.toMeasure a f ρ) (B : Set S) (_ : MeasurableSet B),
    F.readout () ⟨Ω,m,P⟩ {ω | epoch L U (I ω) (ξ ω) (τ ω) (K ω) 0 ∈ B} =
      (a.bind fun k => η.bind fun s => (zeroRow A k s).bind C).toMeasure B

private theorem initial_rejected : ¬ initialArena.{u,v,w}.Law massRejected := by
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
  let η : PMF A := PMF.pure ⟨()⟩
  let ρ : Measure R := Measure.dirac ⟨()⟩
  let U : A → Bool → R → A := fun s _ _ => s
  have hr : ∀ s b, ρ.map (effective Set.univ U s b) = (PMF.pure s).toMeasure := by
    intro s b
    simp [effective, PMF.toMeasure_pure]
  -- A nonzero initialization measure prevents an empty realization; the
  -- countermodel instead varies the observed mass of the empty output event.
  have hh := h (Measure.dirac (⟨()⟩ : ULift.{u} Unit))
    (fun _ => (⟨()⟩ : A)) (fun _ => 0) (fun _ _ => 0) (fun _ _ => (⟨()⟩ : R))
    Set.univ U η (PMF.pure 0) (PMF.pure 0) ρ PMF.pure PMF.pure
    (fun _ => by simpa [effective] using measurable_fst) hr
    (by fun_prop) (by fun_prop) (fun _ => by fun_prop)
    (by
      intro n a l r D B hD hB
      simp [sourceSlice, rawPrefix, rawBlock, η, PMF.toMeasure_pure,
        PMF.pure_apply, Fintype.prod_boole])
    ∅ MeasurableSet.empty
  simpa [massRejected, realize] using hh

def initialRecord : Registration initialArena.{u,v,w} (type_of% (@actual_initial_law.{v,w,u})) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨actual_initial_law, massRejected, initial_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨massRejected, ?_, rfl, initial_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := massRecord.dependence

def initialRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_initial_law.{v,w,u}) (type_of% (realize massSignature.{u}
      (fun _ p E => p.P E) (fun e => nomatch e))) Unit Unit := {
  unitName := `ActualRenewalPrefixLaw.actual_initial_law.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw.initialRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨initialArena⟩, objectArena := .source ⟨initialArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source initialArena ⟨initialRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent,
  readout := some (realize massSignature.{u} (fun _ p E => p.P E) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

def stepArena : Arena where
  signature := massSignature.{u}
  Law F := ∀ {Ω : Type u} [m : MeasurableSpace Ω] {S : Type v} {R : Type w}
    [MeasurableSpace S] [MeasurableSpace R]
    (P : Measure Ω) (I : Ω → S) (τ : Ω → ℕ) (K : Ω → ℕ → ℕ) (ξ : Ω → ℕ → R)
    [Countable S] [MeasurableSingletonClass S]
    (L : Set S) (U : S → Bool → R → S)
    (η : Measure S) (a f : PMF ℕ) (ρ : Measure R) [IsProbabilityMeasure ρ]
    (A C : S → PMF S)
    (_ : ∀ b, Measurable (fun p : S × R => effective L U p.1 b p.2))
    (_ : ∀ s b, ρ.map (effective L U s b) = (if b then C s else A s).toMeasure)
    (_ : Measurable I) (_ : Measurable τ) (_ : ∀ j, Measurable (fun ω => K ω j))
    (_ : ∀ j, Measurable (fun ω => ξ ω j)) (_ : Primitive P I τ K ξ η a f ρ)
    (n : ℕ) (D : (q : ℕ × (Fin n → ℕ)) → Set (S × (Fin (cut q.1 q.2) → R)))
    (_ : ∀ q, MeasurableSet (D q)) (s : S)
    (_ : ∀ ω ∈ pastEvent I τ K ξ n D, epoch L U (I ω) (ξ ω) (τ ω) (K ω) n = s)
    (k : ℕ) (B : Set S) (_ : MeasurableSet B),
    F.readout () ⟨Ω,m,P⟩ (pastEvent I τ K ξ n D ∩ {ω | K ω n = k} ∩
      {ω | epoch L U (I ω) (ξ ω) (τ ω) (K ω) (n + 1) ∈ B}) =
    F.readout () ⟨Ω,m,P⟩ (pastEvent I τ K ξ n D) * f k *
      ((zeroRow A k s).bind C).toMeasure B

private theorem step_rejected : ¬ stepArena.{u,v,w}.Law massRejected := by
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
  let U : A → Bool → R → A := fun s _ _ => s
  have hp : Primitive (0 : Measure E) I τ K ξ (0 : Measure A)
      (PMF.pure 0) (PMF.pure 0) ρ := by
    intro n a l r D B hD hB
    simp
  have hr : ∀ s b, ρ.map (effective Set.univ U s b) = (PMF.pure s).toMeasure := by
    intro s b
    simp [effective, PMF.toMeasure_pure]
  have hh := h (0 : Measure E) I τ K ξ Set.univ U (0 : Measure A)
    (PMF.pure 0) (PMF.pure 0) ρ PMF.pure PMF.pure
    (fun _ => by simpa [effective] using measurable_fst) hr
    (by fun_prop) (by fun_prop) (fun _ => by fun_prop) (fun _ => by fun_prop) hp
    0 (fun _ => Set.univ) (fun _ => MeasurableSet.univ) (⟨()⟩ : A)
    (fun ω => nomatch ω.down) 0 ∅ MeasurableSet.empty
  simpa [massRejected, realize] using hh

def stepRecord : Registration stepArena.{u,v,w} (type_of% (@actual_past_step.{v,w,u})) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨actual_past_step, massRejected, step_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨massRejected, ?_, rfl, step_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := massRecord.dependence

def stepRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_past_step.{v,w,u}) (type_of% (realize massSignature.{u}
      (fun _ p E => p.P E) (fun e => nomatch e))) Unit Unit := {
  unitName := `ActualRenewalPrefixLaw.actual_past_step.__information_unit,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw.stepRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨stepArena⟩, objectArena := .source ⟨stepArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source stepArena ⟨stepRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent,
  readout := some (realize massSignature.{u} (fun _ p E => p.P E) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.ActualRenewalPrefixLaw
