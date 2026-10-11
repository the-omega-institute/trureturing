import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
noncomputable section

abbrev wordSignature : Signature where
  Params := unitInterval
  State _ := List Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ r w => wordMass r w) (fun e => nomatch e)

def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ _ _ => 0) (fun e => nomatch e)

def wordArena : Arena where
  signature := wordSignature
  Law f := ∀ (r : unitInterval) (j : ℕ) (b : Letter),
    f.readout () r (pWord j b) =
      (if b = 0 then alphaMass r else betaMass r ^ 2) * (alphaMass r * betaMass r)^j

theorem word_source_bridge : (type_of% (@p_word_mass)) ↔ wordArena.Law wordActual := Iff.rfl

theorem word_rejected : ¬ wordArena.Law wordRejected := by
  intro h
  have hh := h 1 0 0
  norm_num [wordRejected, realize, alphaMass, betaMass] at hh

def wordRegistration : Registration wordArena (type_of% (@p_word_mass)) where
  actual := wordActual
  bridge := word_source_bridge
  variation := ⟨p_word_mass, wordRejected, word_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨wordRejected, ?_, rfl, word_rejected⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : unitInterval), [], [1], ?_⟩
    change wordMass (1 : unitInterval) [] ≠ wordMass 1 [1]
    simpa [wordMass, bernoulliMeasure] using (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)

abbrev finiteSignature : Signature where
  Params := (_ : ActivePhase) × unitInterval
  State _ := List Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def finiteActual : Realization finiteSignature :=
  realize finiteSignature (fun _ p w => explicitStoppedWordLaw p.1 p.2 {some w})
    (fun e => nomatch e)

def finiteRejected : Realization finiteSignature :=
  realize finiteSignature (fun _ _ _ => 0) (fun e => nomatch e)

def finiteArena : Arena where
  signature := finiteSignature
  Law f := ∀ (s : ActivePhase) (r : unitInterval) (w : List Letter),
    f.readout () ⟨s,r⟩ w = if ∃ b, WordFamily s b w then wordMass r w else 0

theorem finite_source_bridge :
    (type_of% (@explicit_finite_mass)) ↔ finiteArena.Law finiteActual := Iff.rfl

theorem finite_rejected : ¬ finiteArena.Law finiteRejected := by
  intro h
  have hh := h .p 1 (pWord 0 0)
  have hf : ∃ b, WordFamily .p b (pWord 0 0) := ⟨0,0,rfl⟩
  rw [if_pos hf, p_word_mass] at hh
  norm_num [finiteRejected, realize, alphaMass, betaMass] at hh

def finiteRegistration : Registration finiteArena (type_of% (@explicit_finite_mass)) where
  actual := finiteActual
  bridge := finite_source_bridge
  variation := ⟨explicit_finite_mass, finiteRejected, finite_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨finiteRejected, ?_, rfl, finite_rejected⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨.p,1⟩, pWord 0 0, pWord 0 1, ?_⟩
    change explicitStoppedWordLaw .p 1 {some (pWord 0 0)} ≠
      explicitStoppedWordLaw .p 1 {some (pWord 0 1)}
    have hf : ∃ b, WordFamily .p b (pWord 0 0) := ⟨0,0,rfl⟩
    have hg : ∃ b, WordFamily .p b (pWord 0 1) := ⟨1,0,rfl⟩
    rw [explicit_finite_mass, if_pos hf, p_word_mass,
      explicit_finite_mass, if_pos hg, p_word_mass]
    norm_num [alphaMass, betaMass]


noncomputable def word_registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@p_word_mass) (Realization wordSignature) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.word_registration_1.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.wordRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨wordArena⟩
  objectArena := .source ⟨wordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wordArena ⟨wordRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wordSignature (fun _ r w => wordMass r w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def finite_registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@explicit_finite_mass) (Realization finiteSignature) Unit Unit := {
  unitName := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.finite_registration_1.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.finiteRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteSignature (fun _ p w => explicitStoppedWordLaw p.1 p.2 {some w}) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms wordRegistration
#print axioms word_registration_1
#print axioms finite_registration_1
#print axioms finiteRegistration

end

namespace PeriodicReuse
open _root_.D5.S3.Arith.FibonacciAtomic.TriangularSharedImplementation (Nonstop)

abbrev prefixSignature : Signature where
  Params := ℕ
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Letter
  Anchor := Empty
  finiteAnchor := inferInstance

def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ n ω => readPrefix ω (n+1)) (fun e => nomatch e)
def prefixRejected : Realization prefixSignature :=
  realize prefixSignature (fun _ _ _ => []) (fun e => nomatch e)
def prefixArena : Arena where
  signature := prefixSignature
  Law R := ∀ (ω : Stream) (n : ℕ),
    R.readout () n ω = ω 0 :: readPrefix (fun i => ω (i+1)) n
private theorem rejected_prefix : ¬ prefixArena.Law prefixRejected := by
  intro law
  have he := law (fun _ => 0) 0
  change ([] : List Letter) = [0] at he
  cases he
private theorem prefix_dependence : ObservationalDependence prefixSignature prefixActual := by
  intro role
  refine ⟨0,(fun _ => 0),(fun _ => 1),?_⟩
  change ([0] : List Letter) ≠ [1]
  decide

abbrev loopSignature : Signature where
  Params := Unit
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Stream
  Anchor := Empty
  finiteAnchor := inferInstance

def loopActual : Realization loopSignature :=
  realize loopSignature (fun _ _ ω => ω) (fun e => nomatch e)
def loopRejected : Realization loopSignature :=
  realize loopSignature (fun _ _ _ _ => 1) (fun e => nomatch e)
def loopArena : Arena where
  signature := loopSignature
  Law R := ∀ (ω : Stream), Nonstop totalRead pendingColor (.active .p) ω →
    ∀ j : ℕ, Prefix (R.readout () () ω) (loopWord j)
private theorem rejected_loop : ¬ loopArena.Law loopRejected := by
  intro law
  have he := law (infiniteTail .p) (infinite_tail_nonstop .p) 1
  change ([1,1] : List Letter) = [1,0] at he
  exact (by decide : ([1,1] : List Letter) ≠ [1,0]) he
private theorem loop_dependence : ObservationalDependence loopSignature loopActual := by
  intro role
  refine ⟨(),(fun _ => 0),(fun _ => 1),?_⟩
  intro he
  have hh := congrFun he 0
  change (0 : Letter) = 1 at hh
  exact (by decide : (0 : Letter) ≠ 1) hh

abbrev headSignature : Signature where
  Params := Unit
  State _ := Stream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Letter
  Anchor := Empty
  finiteAnchor := inferInstance

def headActual : Realization headSignature :=
  realize headSignature (fun _ _ ω => ω 0) (fun e => nomatch e)
def headRejected : Realization headSignature :=
  realize headSignature (fun _ _ _ => 1) (fun e => nomatch e)
def headArena : Arena where
  signature := headSignature
  Law R := ∀ (ω : Stream), Nonstop totalRead pendingColor (.active .beta) ω →
    R.readout () () ω = 0 ∧ Nonstop totalRead pendingColor (.active .p) (fun i => ω (i+1))
private theorem rejected_head : ¬ headArena.Law headRejected := by
  intro law
  have he := (law (infiniteTail .beta) (infinite_tail_nonstop .beta)).1
  change (1 : Letter) = 0 at he
  exact (by decide : (1 : Letter) ≠ 0) he
private theorem head_dependence : ObservationalDependence headSignature headActual := by
  intro role
  refine ⟨(),(fun _ => 0),(fun _ => 1),?_⟩
  change (0 : Letter) ≠ 1
  decide

abbrev infiniteSignature : Signature where
  Params := Unit
  State _ := ActivePhase
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Stream
  Anchor := Empty
  finiteAnchor := inferInstance

def infiniteActual : Realization infiniteSignature :=
  realize infiniteSignature (fun _ _ s => infiniteTail s) (fun e => nomatch e)
def infiniteRejected : Realization infiniteSignature :=
  realize infiniteSignature (fun _ _ _ _ => 1) (fun e => nomatch e)
def infiniteArena : Arena where
  signature := infiniteSignature
  Law R := ∀ s : ActivePhase, Nonstop totalRead pendingColor (.active s) (R.readout () () s)
private theorem rejected_infinite : ¬ infiniteArena.Law infiniteRejected := by
  intro law
  have he := nonstop_p_prefix (fun _ => 1) (law .p) 1
  change ([1,1] : List Letter) = [1,0] at he
  exact (by decide : ([1,1] : List Letter) ≠ [1,0]) he
private theorem infinite_dependence : ObservationalDependence infiniteSignature infiniteActual := by
  intro role
  refine ⟨(),ActivePhase.p,ActivePhase.beta,?_⟩
  intro he
  have hh := congrFun he 0
  change (1 : Letter) = 0 at hh
  exact (by decide : (1 : Letter) ≠ 0) hh


def prefixRecord : Registration prefixArena (type_of% (@prefix_succ)) where
  actual := prefixActual
  bridge := Iff.rfl
  variation := ⟨prefix_succ,prefixRejected,rejected_prefix⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨prefixRejected,?_,rfl,rejected_prefix⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := prefix_dependence

def prefixRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prefix_succ) (type_of% (realize prefixSignature (fun _ n ω => readPrefix ω (n+1)) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.PeriodicReuse.prefix,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.PeriodicReuse.prefixRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨prefixArena⟩, objectArena := .source ⟨prefixArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source prefixArena ⟨prefixRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize prefixSignature (fun _ n ω => readPrefix ω (n+1)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw,
    definition := none, coordinates := #[1],
    readouts := #[{
        path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := some #["fn", "arg"], booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms prefixRecord


def loopRecord : Registration loopArena (type_of% (@nonstop_p_prefix)) where
  actual := loopActual
  bridge := Iff.rfl
  variation := ⟨nonstop_p_prefix,loopRejected,rejected_loop⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨loopRejected,?_,rfl,rejected_loop⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := loop_dependence

def loopRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nonstop_p_prefix) (type_of% (realize loopSignature (fun _ _ ω => ω) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.PeriodicReuse.loop,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.PeriodicReuse.loopRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨loopArena⟩, objectArena := .source ⟨loopArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source loopArena ⟨loopRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize loopSignature (fun _ _ ω => ω) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw,
    definition := none, coordinates := #[],
    readouts := #[{
        path := #["body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms loopRecord


def headRecord : Registration headArena (type_of% (@nonstop_beta_return)) where
  actual := headActual
  bridge := Iff.rfl
  variation := ⟨nonstop_beta_return,headRejected,rejected_head⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨headRejected,?_,rfl,rejected_head⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := head_dependence

def headRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nonstop_beta_return) (type_of% (realize headSignature (fun _ _ ω => ω 0) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.PeriodicReuse.head,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.PeriodicReuse.headRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨headArena⟩, objectArena := .source ⟨headArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source headArena ⟨headRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize headSignature (fun _ _ ω => ω 0) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw,
    definition := none, coordinates := #[],
    readouts := #[{
        path := #["body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms headRecord


def infiniteRecord : Registration infiniteArena (type_of% (@infinite_tail_nonstop)) where
  actual := infiniteActual
  bridge := Iff.rfl
  variation := ⟨infinite_tail_nonstop,infiniteRejected,rejected_infinite⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨infiniteRejected,?_,rfl,rejected_infinite⟩
      intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := infinite_dependence

def infiniteRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@infinite_tail_nonstop) (type_of% (realize infiniteSignature (fun _ _ s => infiniteTail s) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.PeriodicReuse.infinite,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw.PeriodicReuse.infiniteRecord,
  realizationSource := none, generated := false,
  arena := .source ⟨infiniteArena⟩, objectArena := .source ⟨infiniteArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source infiniteArena ⟨infiniteRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize infiniteSignature (fun _ _ s => infiniteTail s) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw,
    definition := none, coordinates := #[],
    readouts := #[{
        path := #["body", "arg"], stateBinder := 0, functionOperand := false,
        stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }
#print axioms infiniteRecord

end PeriodicReuse

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
