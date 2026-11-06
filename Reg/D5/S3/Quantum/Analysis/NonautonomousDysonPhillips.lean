import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
import Reg.Support.DependentFamily

/-! Full-telescope dependent-family audits of the causal estimate and evolution. -/

open scoped Nat Topology NNReal
open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def zeroSemigroup : Contraction PUnit.{u+1} where
  operator _ := 1
  zero := rfl
  add _ _ := by ext x
  norm_le _ := ContinuousLinearMap.norm_id_le
  continuous _ := continuous_const

namespace Iterate

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E),
    ∀ {r T M C : ℝ} (_hrT : r ≤ T)
    (_hB : ContinuousOn B (Set.Icc r T)) (_hM : 0 ≤ M)
    (_hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M)
    {v : ℝ → E} (_hv : ContinuousOn v (Set.Icc r T))
    (_hvC : ∀ s ∈ Set.Icc r T, ‖v s‖ ≤ C)
    (n : ℕ) {t : ℝ} (_ht : t ∈ Set.Icc r T),
    R.readout () () ‖causalIterate S B r v n t‖ (C * ((M * (t - r)) ^ n / n !))

private theorem actual_law : arena.{u}.Law actual := @causal_iterate_bound.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h zeroSemigroup (fun _ => 0) (r := 0) (T := 0) (M := 0) (C := 0)
    le_rfl continuous_const.continuousOn le_rfl (fun _ _ => by simp)
    (v := fun _ => 0) continuous_const.continuousOn (fun _ _ => by simp)
    0 ⟨le_rfl, le_rfl⟩

def family : Registration arena.{u} (type_of% (@causal_iterate_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@causal_iterate_bound.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.iterateUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.Iterate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Iterate

namespace Evolution

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) [CompleteSpace E],
    ∀ {T M : ℝ} (_hT : 0 ≤ T)
    (_hB : ContinuousOn B (Set.Icc 0 T)) (_hM : 0 ≤ M)
    (_hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M),
    (∀ n t r, (t, r) ∈ triangle T → ∀ x : E,
      R.readout () () ‖term S B n t r x‖ (M ^ n * (t - r) ^ n / n ! * ‖x‖)) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      HasSum (fun n => term S B n t r x) (evolution S B t r x)) ∧
    (∀ x : E, ContinuousOn (fun p : ℝ × ℝ => evolution S B p.1 p.2 x) (triangle T)) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      evolution S B t r x = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (evolution S B s r x))) ∧
    (∀ r ∈ Set.Icc 0 T, evolution S B r r = 1) ∧
    (∀ r ∈ Set.Icc 0 T, ∀ (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc r T) →
      (∀ t ∈ Set.Icc r T, X t = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (X s))) →
      ∀ t ∈ Set.Icc r T, X t = evolution S B t r x) ∧
    (∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T →
      (evolution S B t s).comp (evolution S B s r) = evolution S B t r) ∧
    (∀ t r, (t, r) ∈ triangle T → ‖evolution S B t r‖ ≤ Real.exp (M * (t - r))) ∧
    (∀ n r x, term S B (n + 1) r r x = 0) ∧
    (∀ (B' : ℝ → E →L[ℂ] E) t r, (t, r) ∈ triangle T →
      Set.EqOn B B' (Set.Icc r t) → evolution S B t r = evolution S B' t r) ∧
    (∀ (Bzero : E →L[ℂ] E), Set.EqOn B (fun _ => Bzero) (Set.Icc 0 T) →
      ∀ t r, (t, r) ∈ triangle T → ∀ x : E, evolution S B t r x =
        DysonPhillipsPerturbation.dysonSum S.action Bzero (t - r) x) ∧
    (Set.EqOn B (fun _ => 0) (Set.Icc 0 T) → ∀ t r, (t, r) ∈ triangle T →
      evolution S B t r = S.action (t - r))

private theorem actual_law : arena.{u}.Law actual := @nonautonomous_bounded_perturbation.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp := h zeroSemigroup (fun _ => 0) (T := 0) (M := 0)
    le_rfl continuous_const.continuousOn le_rfl (fun _ _ => by simp)
  exact hp.1 0 0 0 ⟨le_rfl, le_rfl, le_rfl⟩ 0

def family : Registration arena.{u} (type_of% (@nonautonomous_bounded_perturbation.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonautonomous_bounded_perturbation.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.evolutionUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.Evolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Evolution

abbrev equalitySignature : Signature where
  Params := Type u
  State F := F
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ F := F → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def equalityActual : Realization equalitySignature.{u} :=
  realize equalitySignature (fun _ F x y => x = y) (fun e => nomatch e)
def equalityRejected : Realization equalitySignature.{u} :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem equality_dependence : ObservationalDependence equalitySignature.{u} equalityActual := by
  intro i
  refine ⟨ULift.{u} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
  intro h
  have hb := congrFun h (ULift.up false)
  simp [equalityActual, realize] at hb
namespace ExtendEq
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {F : Type u} (f : ℝ → F) {r T : ℝ} (h : r ≤ T)
      {s : ℝ} (_hs : s ∈ Set.Icc r T),
    R.readout () F (extend f h s) (f s)
private theorem actual_law : arena.{u}.Law equalityActual := @_root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.extend_eq.{u}
private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  exact fun h => h (fun _ : ℝ => PUnit.unit) (r := 0) (T := 0) le_rfl ⟨le_rfl,le_rfl⟩
def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.extend_eq.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.extend_eq.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ExtendEqUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ExtendEq.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some equalityActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ExtendEq
namespace TermZero
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E], ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) (t r : ℝ) (x : E),
    R.readout () E (term S B 0 t r x) (S.action (t-r) x)
private theorem actual_law : arena.{u}.Law equalityActual := @term_zero.{u}
private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  exact fun h => h zeroSemigroup (fun _ => 0) 0 0 0
def family : Registration arena.{u} (type_of% (@term_zero.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@term_zero.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermZeroUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermZero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some equalityActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TermZero
namespace TermSucc
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E], ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) (n : ℕ) (t r : ℝ) (x : E),
    R.readout () E (term S B (n+1) t r x)
      (∫ s in r..t, S.action (t-s) (B s (term S B n s r x)))
private theorem actual_law : arena.{u}.Law equalityActual := @term_succ.{u}
private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  exact fun h => h zeroSemigroup (fun _ => 0) 0 0 0 0
def family : Registration arena.{u} (type_of% (@term_succ.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@term_succ.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermSuccUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermSucc.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some equalityActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TermSucc
namespace TermSmul
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E], ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) (n : ℕ) (t r : ℝ) (c : ℂ) (x : E),
    R.readout () E (term S B n t r (c • x)) (c • term S B n t r x)
private theorem actual_law : arena.{u}.Law equalityActual := @term_smul.{u}
private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  exact fun h => h zeroSemigroup (fun _ => 0) 0 0 0 0 0
def family : Registration arena.{u} (type_of% (@term_smul.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@term_smul.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermSmulUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermSmul.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some equalityActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TermSmul
namespace TermLocality
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E], ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) {B' : ℝ → E →L[ℂ] E} {r T : ℝ}
      (_hBB : Set.EqOn B B' (Set.Icc r T)) (n : ℕ) {t : ℝ} (_ht : t ∈ Set.Icc r T) (x : E),
    R.readout () E (term S B n t r x) (term S B' n t r x)
private theorem actual_law : arena.{u}.Law equalityActual := @term_locality.{u}
private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  exact fun h => h zeroSemigroup (fun _ => 0) (B' := fun _ => 0) (r := 0) (T := 0)
    (fun _ _ => rfl) 0 ⟨le_rfl,le_rfl⟩ 0
def family : Registration arena.{u} (type_of% (@term_locality.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@term_locality.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermLocalityUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermLocality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some equalityActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TermLocality
namespace SumDiagonal
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E], ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) (r : ℝ) (x : E),
    R.readout () E (sum S B r r x) x
private theorem actual_law : arena.{u}.Law equalityActual := @sum_diagonal.{u}
private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  exact fun h => h zeroSemigroup (fun _ => 0) 0 0
def family : Registration arena.{u} (type_of% (@sum_diagonal.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_diagonal.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.SumDiagonalUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.SumDiagonal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some equalityActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SumDiagonal
namespace TermConstant
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E], ∀ (S : Contraction E) (Bzero : E →L[ℂ] E) (n : ℕ) (t r : ℝ) (x : E),
    R.readout () E (term S (fun _ => Bzero) n t r x)
      (DysonPhillipsPerturbation.dysonTerm S.action Bzero n (t-r) x)
private theorem actual_law : arena.{u}.Law equalityActual := @term_constant.{u}
private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  exact fun h => h zeroSemigroup 0 0 0 0 0
def family : Registration arena.{u} (type_of% (@term_constant.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@term_constant.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermConstantUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.TermConstant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some equalityActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TermConstant
namespace SumZeroCoefficient
def arena : Arena where
  signature := equalitySignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E], ∀ (S : Contraction E) (t r : ℝ) (x : E),
    R.readout () E (sum S (fun _ => 0) t r x) (S.action (t-r) x)
private theorem actual_law : arena.{u}.Law equalityActual := @sum_zero_coefficient.{u}
private theorem rejected_law : ¬ arena.{u}.Law equalityRejected := by
  exact fun h => h zeroSemigroup 0 0 0
def family : Registration arena.{u} (type_of% (@sum_zero_coefficient.{u})) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨actual_law, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_zero_coefficient.{u}) (Realization equalitySignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.SumZeroCoefficientUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.SumZeroCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some equalityActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SumZeroCoefficient
namespace ActionBound
def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ (S : Contraction E) (t : ℝ) (x : E),
    R.readout () () ‖S.action t x‖ ‖x‖
private theorem actual_law : arena.{u}.Law actual := @Contraction.action_bound.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  exact fun h => h zeroSemigroup 0 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro h
  have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at hb
def family : Registration arena.{u} (type_of% (@Contraction.action_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Contraction.action_bound.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ActionBoundUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ActionBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ActionBound
structure TopologicalInput where
  F : Type u
  topology : TopologicalSpace F
attribute [instance] TopologicalInput.topology
abbrev curveSignature : Signature where
  Params := TopologicalInput.{u}
  State p := ℝ → p.F
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev jointSignature : Signature where
  Params := TopologicalInput.{u}
  State p := (ℝ × p.F) → p.F
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance
def curveActual : Realization curveSignature.{u} := by
  classical
  exact realize curveSignature (fun _ _ f => decide (Continuous f)) (fun e => nomatch e)
def curveRejected : Realization curveSignature.{u} :=
  realize curveSignature (fun _ _ _ => false) (fun e => nomatch e)
def jointActual : Realization jointSignature.{u} := by
  classical
  exact realize jointSignature (fun _ _ f => decide (Continuous f)) (fun e => nomatch e)
def jointRejected : Realization jointSignature.{u} :=
  realize jointSignature (fun _ _ _ => false) (fun e => nomatch e)
private def jump (t : ℝ) : ULift.{u} Bool := if t = 0 then ⟨true⟩ else ⟨false⟩
private theorem jump_not_continuous : ¬ Continuous jump.{u} := by
  intro h
  have ho := h.isOpen_preimage {ULift.up true} (isOpen_discrete _)
  have hs : jump.{u} ⁻¹' {ULift.up true} = {0} := by
    ext t
    by_cases ht : t = 0 <;> simp [jump, ht]
  rw [hs] at ho
  exact not_isOpen_singleton 0 ho
private theorem curve_dependence : ObservationalDependence curveSignature.{u} curveActual := by
  classical
  intro i
  refine ⟨⟨ULift.{u} Bool, inferInstance⟩, (fun _ => ⟨false⟩), jump, ?_⟩
  simp [curveActual, realize, jump_not_continuous, continuous_const]
private theorem joint_dependence : ObservationalDependence jointSignature.{u} jointActual := by
  classical
  intro i
  refine ⟨⟨ULift.{u} Bool, inferInstance⟩, (fun _ => ⟨false⟩), (fun p => jump p.1), ?_⟩
  have hn : ¬ Continuous (fun p : ℝ × ULift.{u} Bool => jump.{u} p.1) := by
    intro h
    exact jump_not_continuous (h.comp (continuous_id.prodMk
      (continuous_const (y := (ULift.up false : ULift.{u} Bool)))))
  simp [jointActual, realize, hn, continuous_const]
namespace ActionContinuous
def arena : Arena where
  signature := jointSignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] (S : Contraction E),
    R.readout () ⟨E, inferInstance⟩ (fun p : ℝ × E => S.action p.1 p.2) = true
private theorem actual_law : arena.{u}.Law jointActual := by
  simpa only [arena, jointActual, realize, decide_eq_true_eq] using @Contraction.action_continuous.{u}
private theorem rejected_law : ¬ arena.{u}.Law jointRejected := by
  exact fun h => Bool.noConfusion (h zeroSemigroup)
def family : Registration arena.{u} (type_of% (@Contraction.action_continuous.{u})) where
  actual := jointActual
  bridge := by simp only [arena, jointActual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, jointRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨jointRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := joint_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Contraction.action_continuous.{u}) (Realization jointSignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ActionContinuousUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ActionContinuous.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some jointActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ActionContinuous
namespace ContinuousExtend
def arena : Arena where
  signature := curveSignature.{u}
  Law R := ∀ {F : Type u} [TopologicalSpace F] {f : ℝ → F} {r T : ℝ}
      (h : r ≤ T) (_hf : ContinuousOn f (Set.Icc r T)),
    R.readout () ⟨F, inferInstance⟩ (extend f h) = true
private theorem actual_law : arena.{u}.Law curveActual := by
  simpa only [arena, curveActual, realize, decide_eq_true_eq] using @continuous_extend.{u}
private theorem rejected_law : ¬ arena.{u}.Law curveRejected := by
  exact fun h => Bool.noConfusion (h (F := PUnit.{u+1}) (f := fun _ => PUnit.unit)
    (r := 0) (T := 0) le_rfl continuous_const.continuousOn)
def family : Registration arena.{u} (type_of% (@continuous_extend.{u})) where
  actual := curveActual
  bridge := by simp only [arena, curveActual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, curveRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨curveRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := curve_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_extend.{u}) (Realization curveSignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ContinuousExtendUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ContinuousExtend.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some curveActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ContinuousExtend
namespace OrbitContinuous
def arena : Arena where
  signature := curveSignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
      (S : Contraction E) (r : ℝ) (x : E),
    R.readout () ⟨E, inferInstance⟩ (fun s => S.action (s-r) x) = true
private theorem actual_law : arena.{u}.Law curveActual := by
  simpa only [arena, curveActual, realize, decide_eq_true_eq] using @orbit_continuous.{u}
private theorem rejected_law : ¬ arena.{u}.Law curveRejected := by
  exact fun h => Bool.noConfusion (h zeroSemigroup 0 0)
def family : Registration arena.{u} (type_of% (@orbit_continuous.{u})) where
  actual := curveActual
  bridge := by simp only [arena, curveActual, realize, decide_eq_true_eq]
  variation := ⟨actual_law, curveRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨curveRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := curve_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@orbit_continuous.{u}) (Realization curveSignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.OrbitContinuousUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.OrbitContinuous.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some curveActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end OrbitContinuous
structure NormedInput where
  E : Type u
  [normed : NormedAddCommGroup E]
  [complexSpace : NormedSpace ℂ E]
attribute [instance] NormedInput.normed NormedInput.complexSpace
abbrev operatorSignature : Signature where
  Params := NormedInput.{u}
  State p := p.E →L[ℂ] p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (p.E →L[ℂ] p.E) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def operatorActual : Realization operatorSignature.{u} :=
  realize operatorSignature (fun _ _ A B => A = B) (fun e => nomatch e)
def operatorRejected : Realization operatorSignature.{u} :=
  realize operatorSignature (fun _ _ _ _ => False) (fun e => nomatch e)
namespace ActionAdd
def arena : Arena where
  signature := operatorSignature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
      (S : Contraction E) {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b),
    R.readout () ⟨E⟩ (S.action (a+b)) ((S.action a).comp (S.action b))
private theorem actual_law : arena.{u}.Law operatorActual := @action_add.{u}
private theorem rejected_law : ¬ arena.{u}.Law operatorRejected := by
  exact fun h => h zeroSemigroup (a := 0) (b := 0) le_rfl le_rfl
private theorem dependence : ObservationalDependence operatorSignature.{u} operatorActual := by
  intro i; let K := ULift.{u} Unit → ℂ
  refine ⟨⟨K⟩, 0, 1, ?_⟩
  intro h
  have he : (1 : K →L[ℂ] K) = 0 := Eq.mp (congrFun h 0) rfl
  have hv := congrArg (fun A : K →L[ℂ] K => A (fun _ => 1) (ULift.up ())) he
  change (1 : ℂ) = 0 at hv
  exact one_ne_zero hv
def family : Registration arena.{u} (type_of% (@action_add.{u})) where
  actual := operatorActual
  bridge := Iff.rfl
  variation := ⟨actual_law, operatorRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨operatorRejected, ?_, rfl, rejected_law⟩
      exact fun j hji => (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@action_add.{u}) (Realization operatorSignature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ActionAddUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.ActionAdd.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some operatorActual.{u}
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ActionAdd
end Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
