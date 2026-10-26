import D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-realized audits of strict startup recurrence and initialized counting. -/

open _root_.D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open _root_.D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open _root_.D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open _root_.D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open _root_.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup
open _root_.D5.S3.TotalVariation.Pinsker _root_.D5.S3.TotalVariation.Metric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup
universe u
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

abbrev Inputs := (Z : Type u) × (p : ℝ) × (q : ℝ) × (r : ℝ) × ℝ
@[reducible] def signature : Signature where
  Params := Inputs.{u}
  State x := GeneratedObserver x.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def accuracy : Realization signature.{u} := realize _
  (fun _ x O => decide (O.toObserver.Accurate x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 true))
  (fun e => nomatch e)

@[reducible] def guaranteeSignature : Signature := { signature.{u} with Output := fun _ _ => Prop }

def guarantee : Realization guaranteeSignature.{u} := realize _
  (fun _ x O => ∀ h : List Visible, 0 < historyMass x.2.1 x.2.2.1 x.2.2.2.1 h →
    ∀ H : Nat, 0 < H → totalVariation
      (actualFutureWordWeight x.2.1 x.2.2.1 x.2.2.2.1 h H)
      (generatedLaw O.update O.row (O.toObserver.run h) H) ≤ x.2.2.2.2)
  (fun e => nomatch e)

def rejected : Realization signature.{u} := realize _ (fun _ _ _ => true) (fun e => nomatch e)

def guaranteeRejected : Realization guaranteeSignature.{u} :=
  realize _ (fun _ _ _ => True) (fun e => nomatch e)

@[reducible] def collisionArena : Arena where
  signature := signature.{u}
  Law F := ∀ {Z : Type u} (O : GeneratedObserver Z) {p q r ε : ℝ}
    (_hp : admissible p q r) (_hne : a p q ≠ b r)
    (_hacc : F.readout () ⟨Z,p,q,r,ε⟩ O = true) (i j : Nat) (_hij : i < j)
    (_he : startupState O.toObserver i = startupState O.toObserver j),
    minority (theta p q r) i < 2*ε

@[reducible] def nonrecurrenceArena : Arena where
  signature := signature.{u}
  Law F := ∀ {Z : Type u} (O : GeneratedObserver Z) {p q r ε : ℝ}
    (_hp : admissible p q r) (_hne : a p q ≠ b r)
    (_hε : 0 < 2*ε) (_hεk : 2*ε < kappa p q r)
    (_hacc : F.readout () ⟨Z,p,q,r,ε⟩ O = true)
    (i : Nat) (_hi : i < J p q r ε) (j : Nat) (_hij : i < j),
    startupState O.toObserver i ≠ startupState O.toObserver j

@[reducible] def lowerArena : Arena where
  signature := guaranteeSignature.{u}
  Law F := ∀ {Z : Type u} [Fintype Z] (O : GeneratedObserver Z) {p q r ε : ℝ}
    (_hp : admissible p q r) (_hne : a p q ≠ b r)
    (_hε : 0 < 2*ε) (_hεk : 2*ε < kappa p q r)
    (_hacc : F.readout () ⟨Z,p,q,r,ε⟩ O),
    6+min (N1 p q r ε) (J p q r ε+1) ≤ Fintype.card Z

private def wrong {Z : Type*} (O : GeneratedObserver Z) : GeneratedObserver Z where
  initial := O.initial
  update := O.update
  row _ y := if y = 0 then 1 else 0
  row_nonneg _ _ := by split_ifs <;> norm_num
  row_sum _ := by simp

private def delta : GeneratedObserver (ULift.{u} Unit) where
  initial := ⟨()⟩
  update _ _ := ⟨()⟩
  row _ y := if y = 0 then 1 else 0
  row_nonneg _ _ := by split_ifs <;> norm_num
  row_sum _ := by simp

private theorem hp : admissible (1/8) (1/8) (1/8) := by norm_num [admissible]
private theorem hne : a (1/8) (1/8) ≠ b (1/8) := by norm_num [a,b]
private theorem he : 0 < 2*(1/100 : ℝ) := by norm_num
private theorem hek : 2*(1/100 : ℝ) < kappa (1/8) (1/8) (1/8) := by
  norm_num [kappa,a,b,c,s]

private theorem wrong_not_accurate {Z : Type*} (O : GeneratedObserver Z) :
    ¬ (wrong O).toObserver.Accurate (1/8) (1/8) (1/8) (1/100) true := by
  intro h
  have hh := h [] (by rw [empty_history_mass]; norm_num) (Or.inl rfl) 1
  have hw : actualFutureWordWeight (1/8) (1/8) (1/8) [] = emptyLaw (1/8) (1/8) (1/8) := rfl
  rw [hw, one_horizon_tv] at hh
  norm_num [GeneratedObserver.toObserver, generatedLaw, wrong, empty_one_step, totalVariation, Fin.sum_univ_succ, B] at hh

private theorem accuracy_dependence : ObservationalDependence signature.{u} accuracy := by
  intro i
  let O := cutoffGenerator hp hne (N1 (1/8) (1/8) (1/8) (1/100))
  let W := ULift.{u} (SharpState (N1 (1/8) (1/8) (1/8) (1/100)))
  let OW := transport (Equiv.ulift.symm) O
  have ha : OW.toObserver.Accurate (1/8) (1/8) (1/8) (1/100) true :=
    transport_accurate _ O (N1_generator_accuracy hp hne he hek)
  refine ⟨⟨W,1/8,1/8,1/8,1/100⟩,OW,wrong OW,?_⟩
  change decide (OW.toObserver.Accurate (1/8) (1/8) (1/8) (1/100) true) ≠
    decide ((wrong OW).toObserver.Accurate (1/8) (1/8) (1/8) (1/100) true)
  intro h
  exact wrong_not_accurate OW (of_decide_eq_true (h ▸ (decide_eq_true ha)))

private theorem guarantee_dependence : ObservationalDependence guaranteeSignature.{u} guarantee := by
  intro i
  let O := cutoffGenerator hp hne (N1 (1/8) (1/8) (1/8) (1/100))
  let W := ULift.{u} (SharpState (N1 (1/8) (1/8) (1/8) (1/100)))
  let OW := transport (Equiv.ulift.symm) O
  have ha := transport_accurate (Equiv.ulift.symm) O (N1_generator_accuracy hp hne he hek)
  refine ⟨⟨W,1/8,1/8,1/8,1/100⟩,OW,wrong OW,?_⟩
  intro h
  have hg : guarantee.readout () ⟨W,1/8,1/8,1/8,1/100⟩ OW :=
    fun h hh H _ => ha h hh (Or.inl rfl) H
  have hb : guarantee.readout () ⟨W,1/8,1/8,1/8,1/100⟩ (wrong OW) := by
    have heq : guarantee.readout () ⟨W,1/8,1/8,1/8,1/100⟩ OW =
        guarantee.readout () ⟨W,1/8,1/8,1/8,1/100⟩ (wrong OW) := h
    exact Eq.mp heq hg
  exact wrong_not_accurate OW
    (_root_.D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity.guarantee_accurate hp _ hb)

private theorem collision_negative : ¬ collisionArena.{u}.Law rejected := by
  intro h
  have hh := h delta (ε := 1/100) hp hne rfl 0 1 (by omega) rfl
  norm_num [minority] at hh

private theorem nonrecurrence_negative : ¬ nonrecurrenceArena.{u}.Law rejected := by
  intro h
  have ht := theta_bounds hp hne
  have hn := (cutoff_first_nonstrict ht.1 ht.2 he (by norm_num : 2*(1/100 : ℝ) < 1/2)).1
  change 0 < N2 (1/8) (1/8) (1/8) (1/100) at hn
  have hj : 0 < J (1/8) (1/8) (1/8) (1/100) := by unfold J; split_ifs <;> omega
  exact h delta hp hne he hek rfl 0 hj 1 (by omega) rfl

private theorem lower_negative : ¬ lowerArena.{u}.Law guaranteeRejected := by
  intro h
  have hh := h delta hp hne he hek True.intro
  simp only [Fintype.card_ulift, Fintype.card_unit] at hh
  omega

def collisionEvidence : Registration collisionArena.{u} (type_of% (@startup_collision_strict.{u})) where
  actual := accuracy
  bridge := by simp only [collisionArena,accuracy,realize,decide_eq_true_eq]
  variation := ⟨by simpa only [collisionArena,accuracy,realize,decide_eq_true_eq] using
    (@startup_collision_strict.{u}),rejected,collision_negative⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,collision_negative⟩,
    fun i => nomatch i⟩
  dependence := accuracy_dependence

def nonrecurrenceEvidence : Registration nonrecurrenceArena.{u} (type_of% (@startup_never_recurs_before_J.{u})) where
  actual := accuracy
  bridge := by simp only [nonrecurrenceArena,accuracy,realize,decide_eq_true_eq]
  variation := ⟨by simpa only [nonrecurrenceArena,accuracy,realize,decide_eq_true_eq] using
    (@startup_never_recurs_before_J.{u}),rejected,nonrecurrence_negative⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,nonrecurrence_negative⟩,
    fun i => nomatch i⟩
  dependence := accuracy_dependence

def lowerEvidence : Registration lowerArena.{u} (type_of% (@generated_initialized_lower.{u})) where
  actual := guarantee
  bridge := Iff.rfl
  variation := ⟨@generated_initialized_lower.{u},guaranteeRejected,lower_negative⟩
  sensitivity := ⟨fun i => ⟨guaranteeRejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,lower_negative⟩,
    fun i => nomatch i⟩
  dependence := guarantee_dependence


def collisionRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.startup_collision_strict.{u})
    (type_of% (realize signature.{u} (fun _ x O => decide (O.toObserver.Accurate x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 true)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.startup_collision_strict,
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.collisionEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨collisionArena.{u}⟩, objectArena := .source ⟨collisionArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source collisionArena.{u} ⟨collisionEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ x O => decide (O.toObserver.Accurate x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 true)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup,
    definition := none, coordinates := #[0,2,3,4,5],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","domain"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","fn","fn","fn","fn","arg","arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def nonrecurrenceRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.startup_never_recurs_before_J.{u})
    (type_of% (realize signature.{u} (fun _ x O => decide (O.toObserver.Accurate x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 true)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.startup_never_recurs_before_J,
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.nonrecurrenceEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨nonrecurrenceArena.{u}⟩, objectArena := .source ⟨nonrecurrenceArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source nonrecurrenceArena.{u} ⟨nonrecurrenceEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ x O => decide (O.toObserver.Accurate x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 true)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup,
    definition := none, coordinates := #[0,2,3,4,5],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","domain"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn","fn","fn","fn","fn","arg","arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def lowerRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.generated_initialized_lower.{u})
    (type_of% (realize guaranteeSignature.{u} (fun _ x O => ∀ h : List Visible, 0 < historyMass x.2.1 x.2.2.1 x.2.2.2.1 h → ∀ H : Nat, 0 < H → totalVariation (actualFutureWordWeight x.2.1 x.2.2.1 x.2.2.2.1 h H) (generatedLaw O.update O.row (O.toObserver.run h) H) ≤ x.2.2.2.2) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.generated_initialized_lower,
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.lowerEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨lowerArena.{u}⟩, objectArena := .source ⟨lowerArena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source lowerArena.{u} ⟨lowerEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize guaranteeSignature.{u} (fun _ x O => ∀ h : List Visible, 0 < historyMass x.2.1 x.2.2.1 x.2.2.2.1 h → ∀ H : Nat, 0 < H → totalVariation (actualFutureWordWeight x.2.1 x.2.2.1 x.2.2.2.1 h H) (generatedLaw O.update O.row (O.toObserver.run h) H) ≤ x.2.2.2.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","domain"],
      stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }


@[reducible] def minimumSignature : Signature where
  Params := (p : ℝ) × (q : ℝ) × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def minimumActual : Realization minimumSignature := realize _
  (fun _ x ε => N1 x.1 x.2.1 x.2.2 ε) (fun e => nomatch e)

def minimumRejected : Realization minimumSignature := realize _
  (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def minimumArena : Arena where
  signature := minimumSignature
  Law F := ∀ {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r),
    (∀ n, Attainable p q r ε n → 6+min (N1 p q r ε) (J p q r ε+1) ≤ n) ∧
    6+min (N1 p q r ε) (J p q r ε+1) ≤ minimum hp hne hε hεk ∧
    minimum hp hne hε hεk ≤ 6+F.readout () ⟨p,q,r⟩ ε ∧
    (N2 p q r ε < N1 p q r ε → 7+N2 p q r ε ≤ minimum hp hne hε hεk) ∧
    (minority (theta p q r) (N2 p q r ε) = 2*ε → N2 p q r ε+2 ≤ N1 p q r ε →
      8+N2 p q r ε ≤ minimum hp hne hε hεk)

private theorem minimum_negative : ¬ minimumArena.Law minimumRejected := by
  intro h
  have hl := (initialized_generated_strict_minimum hp hne he hek).2.1
  have hu := (h hp hne he hek).2.2.1
  change minimum hp hne he hek ≤ 6+0 at hu
  have hn := (N1_threshold hp hne he hek).1
  have hm : 1 ≤ min (N1 (1/8) (1/8) (1/8) (1/100))
      (J (1/8) (1/8) (1/8) (1/100)+1) := le_min hn (by omega)
  omega

private theorem minimum_dependence : ObservationalDependence minimumSignature minimumActual := by
  intro i
  refine ⟨⟨1/8,1/8,1/8⟩,(1/100:ℝ),1,?_⟩
  change N1 (1/8) (1/8) (1/8) (1/100) ≠ N1 (1/8) (1/8) (1/8) 1
  have hn := (N1_threshold hp hne he hek).1
  have hz : N1 (1/8) (1/8) (1/8) 1 = 0 := by simp [N1,cutoff]
  omega

def minimumEvidence : Registration minimumArena (type_of% (@initialized_generated_strict_minimum)) where
  actual := minimumActual
  bridge := Iff.rfl
  variation := ⟨@initialized_generated_strict_minimum,minimumRejected,minimum_negative⟩
  sensitivity := ⟨fun i => ⟨minimumRejected,fun j h => (h (Subsingleton.elim j i)).elim,
    rfl,minimum_negative⟩,fun i => nomatch i⟩
  dependence := minimum_dependence

def minimumRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.initialized_generated_strict_minimum)
    (type_of% (realize minimumSignature
      (fun _ x ε => N1 x.1 x.2.1 x.2.2 ε) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.initialized_generated_strict_minimum,
  realizationName := `Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup.minimumEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨minimumArena⟩, objectArena := .source ⟨minimumArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source minimumArena ⟨minimumEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize minimumSignature
    (fun _ x ε => N1 x.1 x.2.1 x.2.2 ε) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup,
    definition := none, coordinates := #[0,1,2],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "arg","arg","fn","arg","arg","arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms minimumEvidence

#print axioms collisionEvidence
#print axioms nonrecurrenceEvidence
#print axioms lowerEvidence
end
end Reg.D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup
