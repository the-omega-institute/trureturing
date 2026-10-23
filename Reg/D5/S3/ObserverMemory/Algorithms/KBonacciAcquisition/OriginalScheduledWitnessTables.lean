import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open MeasureTheory
open D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
noncomputable section
universe s t u

abbrev Parameters := Σ Seed : Type s, Σ Tape : Type t, Σ L : ℕ,
  Σ schedule : Seed → List ℕ,
  Σ phi : ℕ → (Fin L → Bool) → Seed → Tape,
  Σ rho : Tape → Fin (L+1), Σ T : ℕ → (Fin L → Bool) → Set Seed, ℕ

@[reducible] def signature : Signature where
  Params := Parameters.{s,t}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p.2.2.1 → Bool) → Fin (p.2.2.1+1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{s,t} :=
  realize signature (fun _ p seed =>
    let L := p.2.2.1
    let schedule := p.2.2.2.1
    let phi := p.2.2.2.2.1
    let rho := p.2.2.2.2.2.1
    let T := p.2.2.2.2.2.2.1
    let index := p.2.2.2.2.2.2.2
    witnessTable (scheduleGate schedule (L+1+index) ∩ {s | ∀ b, s ∈ T index b})
      rho (phi index) seed) (fun e => nomatch e)

def rejected : Realization signature.{s,t} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena.{config,seed,tape} : Arena where
  signature := signature.{seed,tape}
  Law R := ∀ {S : Type seed} {Θ : Type tape}
    [MeasurableSpace S] [MeasurableSpace Θ] {C : Type config}
    (mu : Measure S) [IsProbabilityMeasure mu] (L : ℕ) (stop : Bool)
    (schedule : S → List ℕ)
    (hschedule : ∀ m, MeasurableSet (scheduleGate schedule m))
    (prog : S → C → Instruction C ℕ Bool) (initial : S → C)
    (q : ℕ → (Fin L → Bool) → ℕ → Bool)
    (phi : ℕ → (Fin L → Bool) → S → Θ)
    (rho : Θ → Fin (L + 1)) (T : ℕ → (Fin L → Bool) → Set S)
    (readout : C → Θ) (target : ℕ → (Fin L → Bool) → Measure Θ) (eps : ENNReal)
    (hT : ∀ m b, MeasurableSet (T m b))
    (conull : ∀ m b, ∀ᵐ seed ∂mu, seed ∈ T m b)
    (hphi : ∀ m b, Measurable (phi m b)) (hrho : Measurable rho)
    (cap : ∀ m b, measurableTotalVariation (mu.map (phi m b)) (target m b) ≤ eps)
    (low : ∀ m b (i : Fin L), q m b i = b i)
    (high : ∀ m b i, L ≤ i → i < L + 1 + m → q m b i = false)
    (bounded : ∀ seed, (schedule seed).length ≤ 2 ∧
      (stop = true → (schedule seed).Pairwise (· < ·)))
    (discipline : ∀ m b seed,
      Disciplined stop (schedule seed) (prog seed) (initial seed) (q m b))
    (terminal : ∀ m b seed, seed ∈ T m b → ∃ last : C × List (ℕ × Bool),
      last ∈ StateTransition.eval (step (prog seed) (q m b)) (initial seed, []))
    (output : ∀ m b seed last, seed ∈ T m b →
      last ∈ StateTransition.eval (step (prog seed) (q m b)) (initial seed, []) →
      readout last.1 = phi m b seed) ,
    let H := fun m => scheduleGate schedule (L + 1 + m)
    Filter.Tendsto (fun m => mu ((H m)ᶜ)) Filter.atTop (nhds 0) ∧
    ∀ m, let D := H m ∩ {seed | ∀ b, seed ∈ T m b}
      ∃ (F : S → Catalog stop L) (w : PMF (Catalog stop L)),
        Measurable F ∧ w.toMeasure = mu.map F ∧
        (∀ seed, (F seed).val = R.readout ()
          ⟨S, Θ, L, schedule, phi, rho, T, m⟩ seed) ∧
        mu (Dᶜ) = mu ((H m)ᶜ) ∧
        ∀ b, measurableTotalVariation
          (w.toMeasure.map (fun f => f.val b)) ((target m b).map rho) ≤ eps + mu ((H m)ᶜ)

private theorem positive : arena.{u,s,t}.Law actual := by
  exact @scheduled_witness_approximation.{u,s,t}

private theorem faithful_bridge :
    (type_of% (@scheduled_witness_approximation.{u,s,t})) ↔
      arena.{u,s,t}.Law actual := by
  rfl

private theorem negative : ¬arena.{u,s,t}.Law rejected := by
  classical
  intro law
  let S := ULift.{s} Unit
  let Tape := ULift.{t} (Fin 2)
  let C := ULift.{u} Unit
  let mu : Measure S := Measure.dirac (ULift.up ())
  let phi : ℕ → (Fin 1 → Bool) → S → Tape := fun _ _ _ => ULift.up 1
  let rho : Tape → Fin 2 := ULift.down
  have hphi : ∀ m b, Measurable (phi m b) := fun _ _ => measurable_const
  have hrho : Measurable rho := measurable_of_countable _
  have bad := law mu 1 false (fun _ => [])
    (by intro m; simp [scheduleGate])
    (fun _ _ => .halt) (fun _ => ULift.up ())
    (fun _ b => lowReply b) phi rho (fun _ _ => Set.univ)
    (fun _ => ULift.up 1) (fun m b => mu.map (phi m b)) 0
    (by intros; exact MeasurableSet.univ) (by intros; simp)
    hphi hrho (by intros; simp [measurableTotalVariation])
    (by intro m b i; simp only [lowReply, dif_pos i.isLt, Fin.eta])
    (by intro m b i hi him; simp [lowReply, show ¬i<1 by omega])
    (by intros; simp) (by intros m b seed z reached i k h; cases h)
    (by
      intro m b seed hs
      exact ⟨(ULift.up (), []), StateTransition.mem_eval.mpr
        ⟨Relation.ReflTransGen.refl, rfl⟩⟩)
    (by intros; rfl)
  obtain ⟨F, w, hF, hw, hf, _, hrow⟩ := bad.2 0
  let b : Fin 1 → Bool := fun _ => false
  have zeroRow : w.toMeasure.map (fun f => f.val b) = Measure.dirac (0 : Fin 2) := by
    rw [hw, Measure.map_map
      (show Measurable (fun f : Catalog false 1 => f.val b) from measurable_of_countable _) hF]
    have const : (fun seed => (F seed).val b) = fun _ => (0 : Fin 2) := by
      funext seed
      exact congrFun (hf seed) b
    rw [show (fun f : Catalog false 1 => f.val b) ∘ F = fun _ => (0 : Fin 2) from const]
    simp [mu]
  have hbound := hrow b
  rw [zeroRow] at hbound
  have event := (le_iSup (fun E : {E : Set (Fin 2) // MeasurableSet E} =>
    max ((Measure.dirac (0 : Fin 2)) E.1 - ((mu.map (phi 0 b)).map rho) E.1)
      (((mu.map (phi 0 b)).map rho) E.1 - (Measure.dirac (0 : Fin 2)) E.1))
      ⟨{1}, MeasurableSet.singleton 1⟩).trans hbound
  norm_num [mu, phi, rho, scheduleGate, Measure.map_map hrho (hphi 0 b)] at event

private theorem dependent : ObservationalDependence signature.{s,t} actual := by
  classical
  intro role
  let p : Parameters.{s,t} :=
    ⟨ULift.{s} Bool, ULift.{t} (Fin 2), 1, (fun _ => []),
      (fun _ _ seed => ULift.up (if seed.down then 1 else 0)),
      ULift.down, (fun _ _ => Set.univ), 0⟩
  refine ⟨p, ULift.up false, ULift.up true, ?_⟩
  intro h
  have bad := congrFun h (fun _ => false)
  norm_num [actual, realize, witnessTable, scheduleGate, p] at bad

def evidence.{config,seed,tape} : Registration arena.{config,seed,tape}
    (type_of% (@scheduled_witness_approximation.{config,seed,tape})) where
  actual := actual
  bridge := faithful_bridge
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, (by intro j hj; exact (hj (Subsingleton.elim _ _)).elim),
        (by funext e; exact nomatch e), negative⟩
    · intro e; exact nomatch e
  dependence := dependent

noncomputable def registration.{config,seed,tape} : LeanInformationAudit.Contract.Registration.{_,0,1,0,0,0,_,_,0,0,0,0}
    (@scheduled_witness_approximation.{config,seed,tape})
    (type_of% (realize signature.{seed,tape} actual.{seed,tape}.readout actual.{seed,tape}.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables.scheduled_witness_approximation,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{config,seed,tape}⟩, objectArena := .source ⟨arena.{config,seed,tape}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{config,seed,tape} ⟨evidence.{config,seed,tape}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature.{seed,tape} (fun _ p seed =>
    let L := p.2.2.1
    let schedule := p.2.2.2.1
    let phi := p.2.2.2.2.1
    let rho := p.2.2.2.2.2.1
    let T := p.2.2.2.2.2.2.1
    let index := p.2.2.2.2.2.2.2
    witnessTable (scheduleGate schedule (L+1+index) ∩ {s | ∀ b, s ∈ T index b})
      rho (phi index) seed) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables,
    definition := none, coordinates := #[0, 1, 7, 9, 14, 15, 16, 32],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "body", "arg"],
      stateBinder := 36, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms positive
#print axioms faithful_bridge
#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ScheduledViewCongruence
noncomputable section
universe u

abbrev Parameters := Σ A : Type u, Σ _ : Bool, List A
@[reducible] def signature : Signature.{u+1,u,0,0,0} where
  Params := Parameters.{u}
  State p := p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p q => view p.2.1 p.2.2 q) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => []) (fun e => nomatch e)

@[reducible] def arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law R := ∀ {A : Type u} (stop : Bool) (xs : List A) (q r : A → Bool)
    (_same : ∀ i ∈ xs, q i = r i),
    R.readout () ⟨A,stop,xs⟩ q = view stop xs r

private theorem positive : arena.{u}.Law actual.{u} := view_congr
private theorem faithful_bridge : (type_of% (@view_congr.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl
private theorem negative : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have bad := h false [ULift.up ()] (fun _ : ULift.{u} Unit => true)
    (fun _ => true) (by simp)
  simp [rejected,realize,view] at bad
private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  refine ⟨⟨ULift.{u} Unit,false,[ULift.up ()]⟩,fun _ => true,fun _ => false,?_⟩
  simp [actual,realize,view]

def evidence : Registration arena.{u} (type_of% (@view_congr.{u})) where
  actual := actual.{u}
  bridge := faithful_bridge
  variation := ⟨positive,rejected.{u},negative⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected.{u},(by intro j hj; exact (hj (Subsingleton.elim _ _)).elim),
        (by funext e; exact nomatch e),negative⟩
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{u+1,0,1,0,0,0,u+1,u,0,0,0,0}
    (@view_congr.{u}) (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ScheduledViewCongruence.view_congr,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ScheduledViewCongruence.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables,
    definition := none, coordinates := #[0,1,2],
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.ScheduledViewCongruence
