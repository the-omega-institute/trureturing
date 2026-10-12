import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelSuperharmonic NativeBorelEndpointIdentification
open NativeFullResidual FourthSegmentStoppedLaw NativeBorelTVTopology NativeConditionalControl.Tail
open NativeBorelEndpointIdentification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
attribute [local instance] Classical.propDecidable

abbrev coreSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor × PDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def coreActual : Realization coreSignature :=
  realize _ (fun i F z => if i = 0 then sixthFunctional F z.1 else sixthFunctional F z.2)
    (fun e => nomatch e)

def coreArena : Arena where
  signature := coreSignature
  Law R := ∀ F, ∃ G : Set PDescriptor, MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    ∀ Q ∈ G, CoreAt F Q ∧
      ∀ᵐ Q' ∂F.C Q, Q' ∈ G ∧ R.readout 1 F (Q, Q') = R.readout 0 F (Q, Q')

theorem core_bridge : (type_of% (@common_flow_absorbing_core)) ↔
    coreArena.Law coreActual := Iff.rfl

theorem core_actual_law : coreArena.Law coreActual := core_bridge.mp common_flow_absorbing_core

abbrev survivingSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def survivingActual : Realization survivingSignature :=
  realize _ (fun _ F Q => q F Q) (fun e => nomatch e)

def survivingArena : Arena where
  signature := survivingSignature
  Law R := ∀ F, ∃ G : Set PDescriptor, MeasurableSet G ∧ (∀ᵐ Q ∂F.nuP, Q ∈ G) ∧
    (∀ Q ∈ G, CoreAt F Q ∧
      ∀ᵐ Q' ∂F.C Q, Q' ∈ G ∧ sixthFunctional F Q' = sixthFunctional F Q) ∧
    ∀ Q ∈ G, R.readout 0 F Q ≠ 0 ↔ Q = nativeEndpoint .p true

theorem surviving_bridge : (type_of% (@common_flow_surviving_native)) ↔
    survivingArena.Law survivingActual := Iff.rfl

theorem surviving_actual_law : survivingArena.Law survivingActual :=
  surviving_bridge.mp common_flow_surviving_native

abbrev limitsSignature : Signature where
  Params := CommonFlow
  State _ := ℕ × PDescriptor
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def limitsActual : Realization limitsSignature :=
  realize _ (fun i F z => if i = 0 then q F z.2 else if i = 1 then
    q F z.2 / threeStepAverage F z.2 else coordinate z.1 1 z.2 / endpointRate ^ z.1)
    (fun e => nomatch e)

def limitsArena : Arena where
  signature := limitsSignature
  Law R := ∀ F,
    (∀ᵐ Q ∂F.nuP,
      R.readout 0 F (0, Q) = (if Q = nativeEndpoint .p true then endpointCompletion else 0) ∧
      R.readout 1 F (0, Q) = (if Q = nativeEndpoint .p true then 1 else 0)) ∧
    (∀ᵐ Q ∂F.nuP, Tendsto (fun n => R.readout 2 F (n, Q)) atTop
      (𝓝 (if Q = nativeEndpoint .p true then endpointCompletion else 0))) ∧
    Tendsto (fun n => (∫⁻ Q, coordinate n 1 Q ∂F.nuP) / endpointRate ^ n) atTop
      (𝓝 (endpointCompletion * F.nuP {nativeEndpoint .p true}))

theorem limits_bridge : (type_of% (@common_flow_upper_endpoint_limits)) ↔
    limitsArena.Law limitsActual := Iff.rfl

theorem limits_actual_law : limitsArena.Law limitsActual :=
  limits_bridge.mp common_flow_upper_endpoint_limits

abbrev transitionSignature : Signature where
  Params := CommonFlow
  State _ := PDescriptor × BDescriptor
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := BDescriptor
  Anchor := Empty
  finiteAnchor := inferInstance

def transitionActual : Realization transitionSignature :=
  realize _ (fun i _ z => if i = 0 then z.2 else nativeEndpoint .beta true)
    (fun e => nomatch e)

def transitionArena : Arena where
  signature := transitionSignature
  Law R := ∀ F, ∀ᵐ Q ∂F.nuP, q F Q ≠ 0 →
    u Q = upper ∧ F.L Q = endpointRate • F.C Q ∧
      ∀ᵐ W ∂F.B Q, R.readout 0 F (Q, W) = R.readout 1 F (Q, W) ∧
        ∀ᵐ Q' ∂F.A W, Q' = nativeEndpoint .p true

theorem transition_bridge : (type_of% (@common_flow_surviving_transitions)) ↔
    transitionArena.Law transitionActual := Iff.rfl

theorem transition_actual_law : transitionArena.Law transitionActual :=
  transition_bridge.mp common_flow_surviving_transitions


abbrev tailsSignature : Signature where
  Params := unitInterval
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def tailsArena : Arena where
  signature := tailsSignature
  Law R := ∀ (r : unitInterval) (j : ℕ),
    R.readout 0 r j = (alphaMass r * betaMass r) ^ j ∧
    R.readout 1 r j = alphaMass r * (alphaMass r * betaMass r) ^ j

def tailsActual : Realization tailsSignature :=
  realize tailsSignature (fun i r j =>
    if i = 0 then (native .p r : Measure _) (tailSet .p j)
    else (native .beta r : Measure _) (tailSet .beta j)) (fun e => nomatch e)

def tailsRejected : Realization tailsSignature :=
  realize tailsSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem tailsRejected_law : ¬ tailsArena.Law tailsRejected := by
  intro h
  have h0 := (h lowerRate 0).1
  simpa [tailsRejected, realize] using h0

def tailsRecord : Registration tailsArena (type_of% (@native_tails)) where
  actual := tailsActual
  bridge := Iff.rfl
  variation := ⟨native_tails, tailsRejected, tailsRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      change Fin 2 at i
      let bad : Realization tailsSignature := realize tailsSignature
        (fun k r j => if k = i then 0 else tailsActual.readout k r j) (fun e => nomatch e)
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro k hki
        funext r j
        simp [bad, realize, hki]
      · intro h
        fin_cases i
        · have ht := (h lowerRate 0).1
          simpa [bad, realize] using ht
        · have ht := (h lowerRate 0).2
          change (0 : ℝ≥0∞) = alphaMass lowerRate * _ at ht
          have hr := congrArg ENNReal.toReal ht
          norm_num [alphaMass, lowerRate] at hr
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨lowerRate, (0 : ℕ), (1 : ℕ), ?_⟩
    intro h
    fin_cases i
    · change (native .p lowerRate : Measure _) (tailSet .p 0) =
        (native .p lowerRate : Measure _) (tailSet .p 1) at h
      rw [(native_tails _ _).1, (native_tails _ _).1] at h
      have hr := congrArg ENNReal.toReal h
      norm_num [alphaMass, betaMass, lowerRate, unitInterval.coe_toNNReal,
        unitInterval.symm, ENNReal.toReal_mul] at hr
    · change (native .beta lowerRate : Measure _) (tailSet .beta 0) =
        (native .beta lowerRate : Measure _) (tailSet .beta 1) at h
      rw [(native_tails _ _).2, (native_tails _ _).2] at h
      have hr := congrArg ENNReal.toReal h
      norm_num [alphaMass, betaMass, lowerRate, unitInterval.coe_toNNReal,
        unitInterval.symm, ENNReal.toReal_mul] at hr

def tailsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_tails)
    (type_of% (realize tailsSignature (fun i r j =>
      if i = 0 then (native .p r : Measure _) (tailSet .p j)
      else (native .beta r : Measure _) (tailSet .beta j)) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification.tails,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification.tailsRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨tailsArena⟩, objectArena := .source ⟨tailsArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source tailsArena ⟨tailsRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize tailsSignature (fun i r j =>
    if i = 0 then (native .p r : Measure _) (tailSet .p j)
    else (native .beta r : Measure _) (tailSet .beta j)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification,
    definition := none, coordinates := #[0], readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }, {
      path := #["body", "body", "arg", "fn", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


abbrev coordinateSignature : Signature where
  Params := Σ _ : ActivePhase, unitInterval
  State p := ValidTail p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateArena : Arena where
  signature := coordinateSignature
  Law R := ∀ (s : ActivePhase) (r : unitInterval) (t : ValidTail s),
    R.readout () ⟨s, r⟩ t = explicitStoppedWordLaw s r {t.val}

def coordinateActual : Realization coordinateSignature :=
  realize coordinateSignature (fun _ p t => (native p.1 p.2 : Measure _) {t})
    (fun e => nomatch e)

def coordinateRejected : Realization coordinateSignature :=
  realize coordinateSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem coordinateRejected_law : ¬ coordinateArena.Law coordinateRejected := by
  intro h
  have ht := h .p lowerRate (pAtom 0 0)
  change (0 : ℝ≥0∞) = explicitStoppedWordLaw .p lowerRate {(pAtom 0 0).val} at ht
  rw [← native_coordinate, (native_atoms _).1] at ht
  have hr := congrArg ENNReal.toReal ht
  norm_num [alphaMass, lowerRate] at hr

def coordinateRecord : Registration coordinateArena (type_of% (@native_coordinate)) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨native_coordinate, coordinateRejected, coordinateRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coordinateRejected, ?_, rfl, coordinateRejected_law⟩
      intro j hj
      exact False.elim (hj (show j = i from by cases i; cases j; rfl))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨.p, lowerRate⟩, pAtom 0 0, infinity .p, ?_⟩
    intro h
    change (native .p lowerRate : Measure _) {pAtom 0 0} =
      (native .p lowerRate : Measure _) {infinity .p} at h
    rw [(native_atoms _).1, (native_atoms _).2.2.2] at h
    have hr := congrArg ENNReal.toReal h
    norm_num [alphaMass, lowerRate] at hr

def coordinateRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_coordinate)
    (type_of% (realize coordinateSignature
      (fun _ p t => (native p.1 p.2 : Measure _) {t}) (fun e => nomatch e)))
    (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification.coordinate,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification.coordinateRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨coordinateArena⟩, objectArena := .source ⟨coordinateArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source coordinateArena ⟨coordinateRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize coordinateSignature
    (fun _ p t => (native p.1 p.2 : Measure _) {t}) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification,
    definition := none, coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

abbrev emissionSignature : Signature where
  Params := ActivePhase × unitInterval
  State _ := Unit
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def emissionActual : Realization emissionSignature :=
  realize _ (fun i p _ => if i = 0 then emission p.1 (native p.1 p.2) else alphaMass p.2) (fun e => nomatch e)

def emissionArena : Arena where
  signature := emissionSignature
  Law R := ∀ s r, R.readout 0 (s, r) () = R.readout 1 (s, r) ()

theorem emission_bridge : (type_of% (@native_emission)) ↔
    emissionArena.Law emissionActual := Iff.rfl

theorem emission_actual_law : emissionArena.Law emissionActual :=
  emission_bridge.mp native_emission



abbrev inclusionSignature : Signature where
  Params := ActivePhase
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := ValidTail s → RawTail
  Anchor := Empty
  finiteAnchor := inferInstance

def inclusionActual : Realization inclusionSignature :=
  realize _ (fun _ _ _ => Subtype.val) (fun e => nomatch e)

def inclusionArena : Arena where
  signature := inclusionSignature
  Law R := ∀ s, MeasurableEmbedding (R.readout () s ())

theorem inclusion_bridge : (type_of% (@inclusion_embedding)) ↔
    inclusionArena.Law inclusionActual := Iff.rfl

theorem inclusion_actual_law : inclusionArena.Law inclusionActual :=
  inclusion_bridge.mp inclusion_embedding

abbrev legalSignature : Signature where
  Params := ActivePhase
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawTail
  Anchor := Empty
  finiteAnchor := inferInstance

def legalActual : Realization legalSignature :=
  realize _ (fun _ s ω => stoppedReadWord s ω) (fun e => nomatch e)

def legalArena : Arena where
  signature := legalSignature
  Law R := ∀ s ω, Valid s (R.readout () s ω)

theorem legal_bridge : (type_of% (@stopped_legal)) ↔ legalArena.Law legalActual := Iff.rfl

theorem legal_actual_law : legalArena.Law legalActual := legal_bridge.mp stopped_legal

abbrev geometricSignature : Signature where
  Params := ℝ≥0∞ × ℝ≥0∞
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def geometricActual : Realization geometricSignature := realize _
  (fun _ p j => ∑' n : ℕ, if j ≤ n then p.2 * p.1^n else 0) (fun e => nomatch e)

def geometricArena : Arena where
  signature := geometricSignature
  Law R := ∀ z d j, R.readout () (z,d) j = z^j * ∑' n : ℕ, d*z^n

theorem geometric_bridge : (type_of% (@geometric_tail)) ↔
    geometricArena.Law geometricActual := Iff.rfl

theorem geometric_actual_law : geometricArena.Law geometricActual :=
  geometric_bridge.mp geometric_tail

abbrev atomTailSignature : Signature where
  Params := ℕ × ℕ × Letter
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def pAtomTailActual : Realization atomTailSignature := realize _
  (fun _ p _ => pAtom p.2.1 p.2.2 ∈ tailSet .p p.1) (fun e => nomatch e)

def bAtomTailActual : Realization atomTailSignature := realize _
  (fun _ p _ => betaAtom p.2.1 p.2.2 ∈ tailSet .beta p.1) (fun e => nomatch e)

def atomTailArena : Arena where
  signature := atomTailSignature
  Law R := ∀ j n i, R.readout () (j,n,i) () ↔ j ≤ n

theorem p_atom_tail_bridge : (type_of% (@p_atom_tail)) ↔
    atomTailArena.Law pAtomTailActual := Iff.rfl

theorem p_atom_tail_actual_law : atomTailArena.Law pAtomTailActual :=
  p_atom_tail_bridge.mp p_atom_tail

theorem beta_atom_tail_bridge : (type_of% (@beta_atom_tail)) ↔
    atomTailArena.Law bAtomTailActual := Iff.rfl

theorem beta_atom_tail_actual_law : atomTailArena.Law bAtomTailActual :=
  beta_atom_tail_bridge.mp beta_atom_tail

abbrev stopTailSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def stopTailActual : Realization stopTailSignature := realize _
  (fun _ _ j => betaStop ∈ tailSet .beta j) (fun e => nomatch e)

def stopTailArena : Arena where
  signature := stopTailSignature
  Law R := ∀ j, ¬ R.readout () () j

theorem beta_stop_not_tail_bridge : (type_of% (@beta_stop_not_tail)) ↔
    stopTailArena.Law stopTailActual := Iff.rfl

theorem beta_stop_not_tail_actual_law : stopTailArena.Law stopTailActual :=
  beta_stop_not_tail_bridge.mp beta_stop_not_tail

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
