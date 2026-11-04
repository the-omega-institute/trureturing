import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Whole-domain support observations and source-bound variation. -/

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private constantTable score_le_support from
  D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
noncomputable section
open scoped BigOperators

abbrev Parameters := ℕ

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun L => FullScore L) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => support true y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {L : ℕ} (hL : 3 ≤ L) (y : FullScore L), EarlyPair y →
    highLower hL y ≤ R.readout () L y - inputAnchor hL y

private def terminalScore (L : ℕ) (t : ℝ) (ht : 0 ≤ t) : FullScore L where
  A := fun _ => 0
  C := fun _ => 0
  P := fun _ => 0
  T := t
  nonnegA := by simp
  nonnegC := by simp
  nonnegP := by simp
  nonnegT := ht
  terminalA := rfl
  terminalC := rfl
  terminalP := rfl

private theorem terminal_score (L : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Word L → Fin (L + 1)) :
    score (terminalScore L t ht) f = if f (fun _ => true) = 0 then t else 0 := by
  classical
  unfold score
  have hr (b : Word L) : reward (terminalScore L t ht) b (f b) =
      if b = (fun _ => true) then (if f b = 0 then t else 0) else 0 := by
    refine Fin.cases ?_ (fun i => ?_) (f b)
    · simp [reward,baseline,terminalScore]
    · simp [reward,numerical,terminalScore,Fin.succ_ne_zero]
  simp_rw [hr]
  simp

private theorem terminal_support (L : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    support true (terminalScore L t ht) = t := by
  classical
  apply le_antisymm
  · unfold support
    apply Finset.sup'_le
    intro f _
    rw [terminal_score]
    split <;> linarith
  · have h := score_le_support true (terminalScore L t ht) (constantTable true L 0)
    simpa [terminal_score,constantTable] using h

private theorem positive : arena.Law actual := @arbitrary_input_lower_bound
private theorem faithful_bridge :
    (type_of% (@arbitrary_input_lower_bound)) ↔ arena.Law actual := Iff.rfl

private theorem negative : ¬arena.Law rejected := by
  intro h
  have h := @h 3 (by omega) (terminalScore 3 0 le_rfl) (by intro b i hi hlate; rfl)
  have hn : 0 ≤ highLower (by omega) (terminalScore 3 0 le_rfl) :=
    (le_max_left 0 _).trans (le_max_left _ _)
  change highLower (by omega) (terminalScore 3 0 le_rfl) ≤
    -1 - inputAnchor (by omega) (terminalScore 3 0 le_rfl) at h
  have hz : inputAnchor (by omega) (terminalScore 3 0 le_rfl) = 0 := by
    simp [inputAnchor,early,gamma,pairTotal,terminalScore]
  rw [hz,sub_zero] at h
  linarith

def evidence : Registration arena (type_of% (@arbitrary_input_lower_bound)) where
  actual := actual
  bridge := faithful_bridge
  variation := ⟨positive,rejected,negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨3, terminalScore 3 0 le_rfl, terminalScore 3 1 (by norm_num), ?_⟩
    change support true (terminalScore 3 0 le_rfl) ≠
      support true (terminalScore 3 1 (by norm_num))
    rw [terminal_support,terminal_support]
    norm_num

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@arbitrary_input_lower_bound)
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain.arbitrary_input_lower_bound,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ y => support true y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","body","arg","fn","arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms faithful_bridge
#print axioms evidence
#print axioms registration

open private late_peak_nonneg from
  D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain

private theorem zero_peak {L : ℕ} (y : FullScore L) (hg : ∀ i, gamma y i = 0) :
    latePeak y = 0 := by
  apply le_antisymm
  · unfold latePeak
    apply Finset.sup'_le
    intro o _
    cases o <;> simp [hg]
  · exact late_peak_nonneg y

namespace Balanced

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun L => FullScore L) (fun _ => Bool → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y stop => support stop y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {L : ℕ} (hL : 3 ≤ L) (g : Fin L → ℝ) (S t : ℝ)
    (hg : ∀ i, 0 ≤ g i) (hS : 0 ≤ S) (ht : 0 ≤ t),
    latePeak (balancedChain hL g S t hg hS ht) ≤ t →
    let V := balancedChain hL g S t hg hS ht
    beta V = g ∧ coefficientMass V = (∑ i, g i) + S + t ∧
      pairTotal V = S ∧ inputAnchor hL V = g ⟨0,by omega⟩ + g ⟨1,by omega⟩ + S + t ∧
      EarlyPair V ∧ (∀ i, gamma V i = g i) ∧
      R.readout () L V false - inputAnchor hL V =
        max (highLower hL V) (latePeak V - early hL V) ∧
      R.readout () L V true - inputAnchor hL V =
        max (highLower hL V) (latePeak V - early hL V)

private theorem positive : arena.Law actual := @balanced_chain_exact
private theorem faithful_bridge :
    (type_of% (@balanced_chain_exact)) ↔ arena.Law actual := Iff.rfl

open private chain_gamma chain_pair_total from
  D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain

private theorem negative : ¬arena.Law rejected := by
  intro h
  let V := balancedChain (L:=3) (by omega) (fun _ => 0) 0 0 (by simp) le_rfl le_rfl
  have hp : latePeak V = 0 := zero_peak V (by intro i; simp [V,chain_gamma])
  have ha : inputAnchor (by omega) V = 0 := by
    simp [inputAnchor,early,V,chain_gamma,chain_pair_total]
    rfl
  have hx := @h 3 (by omega) (fun _ => 0) 0 0 (by simp) le_rfl le_rfl (by simpa [V] using hp.le)
  have hn : 0 ≤ max (highLower (by omega) V) (latePeak V - early (by omega) V) :=
    ((le_max_left 0 _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have he := hx.2.2.2.2.2.2.1
  change -1 - inputAnchor (by omega) V = _ at he
  rw [ha,sub_zero] at he
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, terminalScore 3 0 le_rfl, terminalScore 3 1 (by norm_num), ?_⟩
  intro h
  have ht := congrFun h true
  change support true (terminalScore 3 0 le_rfl) =
    support true (terminalScore 3 1 (by norm_num)) at ht
  rw [terminal_support,terminal_support] at ht
  norm_num at ht

def evidence : Registration arena (type_of% (@balanced_chain_exact)) where
  actual := actual
  bridge := faithful_bridge
  variation := ⟨positive,rejected,negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := dependence

end Balanced

namespace Comparison

@[reducible] def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun L => FullScore L) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => support false y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ L y => if hL : 3 ≤ L then inputAnchor hL y + 1 else 1)
    (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {L : ℕ} (hL : 3 ≤ L) (y : FullScore L),
    (∀ b, y.A b = 0) → EarlyPair y → latePeak y ≤ y.T →
    latePeak y ≤ early hL y + delta hL true y →
    ∃ V : FullScore L, (∀ b, V.A b = 0) ∧ EarlyPair V ∧ beta V = beta y ∧
      coefficientMass V = coefficientMass y ∧ inputAnchor hL V = inputAnchor hL y ∧
      R.readout () L V - inputAnchor hL V ≤ delta hL true y

private theorem positive : arena.Law actual := @balanced_chain_comparison
private theorem faithful_bridge :
    (type_of% (@balanced_chain_comparison)) ↔ arena.Law actual := Iff.rfl

private theorem negative : ¬arena.Law rejected := by
  intro h
  let y := terminalScore 3 0 le_rfl
  have hp : latePeak y = 0 := zero_peak y (by intro i; simp [gamma,y,terminalScore])
  have he : early (by omega) y = 0 := by simp [early,gamma,y,terminalScore]
  have ha : inputAnchor (by omega) y = 0 := by simp [inputAnchor,early,gamma,pairTotal,y,terminalScore]
  have hd : delta (by omega) true y = 0 := by rw [delta,terminal_support,ha]; simp
  obtain ⟨V,_,_,_,_,_,hv⟩ := @h 3 (by omega) y (by intro b; rfl)
    (by intro b i hi hlate; rfl) (by simpa [y,terminalScore] using hp.le)
    (by rw [hp,he,hd]; simp)
  change (if hL : 3 ≤ 3 then inputAnchor hL V + 1 else 1) - inputAnchor (by omega) V ≤ _ at hv
  simp only [show 3 ≤ 3 by omega, dite_true,add_sub_cancel_left,hd] at hv
  norm_num at hv

def evidence : Registration arena (type_of% (@balanced_chain_comparison)) where
  actual := actual
  bridge := faithful_bridge
  variation := ⟨positive,rejected,negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected negative
  dependence := by
    intro i
    refine ⟨3, terminalScore 3 0 le_rfl, terminalScore 3 1 (by norm_num), ?_⟩
    intro h
    have hmono (t : ℝ) (ht : 0 ≤ t) : support false (terminalScore 3 t ht) = t := by
      classical
      apply le_antisymm
      · unfold support
        apply Finset.sup'_le
        intro f _
        rw [terminal_score]
        split <;> linarith
      · have hh := score_le_support false (terminalScore 3 t ht) (constantTable false 3 0)
        simpa [terminal_score,constantTable] using hh
    change support false (terminalScore 3 0 le_rfl) =
      support false (terminalScore 3 1 (by norm_num)) at h
    rw [hmono,hmono] at h
    norm_num at h

end Comparison

noncomputable def balancedRegistration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@balanced_chain_exact)
    (type_of% (realize Balanced.signature Balanced.actual.readout Balanced.actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain.balanced_chain_exact,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain.Balanced.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨Balanced.arena⟩, objectArena := .source ⟨Balanced.arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Balanced.arena ⟨Balanced.evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Balanced.signature (fun _ _ y stop => support stop y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","arg","arg","arg","arg","arg","arg","fn","arg","fn","arg","fn","arg"],
      stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def comparisonRegistration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@balanced_chain_comparison)
    (type_of% (realize Comparison.signature Comparison.actual.readout Comparison.actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain.balanced_chain_comparison,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain.Comparison.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨Comparison.arena⟩, objectArena := .source ⟨Comparison.arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Comparison.arena ⟨Comparison.evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Comparison.signature (fun _ _ y => support false y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg","body","arg","arg","arg","arg","arg","fn","arg","fn","arg"],
      stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms Balanced.faithful_bridge
#print axioms Balanced.evidence
#print axioms balancedRegistration
#print axioms Comparison.faithful_bridge
#print axioms Comparison.evidence
#print axioms comparisonRegistration

end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.HighTerminalChain
