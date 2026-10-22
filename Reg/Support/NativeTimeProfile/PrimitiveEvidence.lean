import D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
import D5.S3.ConceptDynamics.Spacetime.ComplementFibers
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.Support.NativeTimeProfile.PrimitiveEvidence
open _root_.D5.S0.History.Spacetime.ArchiveCarrier
open _root_.D5.S3.ConceptDynamics.Spacetime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ComplementCharge TotalCopyNormalization NativeTimeProfile
noncomputable section
open Classical

@[reducible] def signature : Signature where
  Params := Unit
  State _ := Rich 3
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ X => match i.val with | 0 => readout (gamma X) | _ => q X)
  (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ X : Rich 3, F.readout 0 () X = F.readout 1 () X

private theorem positive : arena.Law actual := readout_gamma

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p X => if j = i then actual.readout j p X + 1 else actual.readout j p X)
  (fun e => nomatch e)

private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  let X := (ComplementFibers.balancedSection 3 0).val
  have h := law X
  have hp : readout (gamma X) = q X := readout_gamma X
  change (if (0 : Fin 2) = i then readout (gamma X) + 1 else readout (gamma X)) =
    (if (1 : Fin 2) = i then q X + 1 else q X) at h
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> norm_num at h <;> omega

def evidence : Registration arena (type_of% (@readout_gamma)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p X
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨(), (ComplementFibers.balancedSection 3 0).val,
      (ComplementFibers.balancedSection 3 1).val, ?_⟩
    have h0 : q (ComplementFibers.balancedSection 3 0).val = 0 :=
      ComplementFibers.balancedSection_readout 3 0
    have h1 : q (ComplementFibers.balancedSection 3 1).val = 1 :=
      ComplementFibers.balancedSection_readout 3 1
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · change readout (gamma _) ≠ readout (gamma _)
      rw [readout_gamma, readout_gamma, h0, h1]
      decide
    · simpa only [actual, realize, show (1 : Fin 2) ≠ 0 by decide, ite_false] using
        (show q (ComplementFibers.balancedSection 3 0).val ≠
          q (ComplementFibers.balancedSection 3 1).val from by rw [h0,h1]; decide)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.readout_gamma)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.readout_gamma
  realizationName := `Reg.Support.NativeTimeProfile.PrimitiveEvidence.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
private def profileDelta : Profile := gamma (ComplementFibers.balancedSection 3 1).val
private theorem profileDelta_readout : NativeTimeProfile.readout profileDelta = 1 := by
  rw [profileDelta, readout_gamma]
  exact ComplementFibers.balancedSection_readout 3 1

namespace UnaryPush
@[reducible] def signature : Signature where
  Params := Unary
  State _ := B
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Profile
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i p X => match i.val with | 0 => gamma (unary p X).val | _ => push (unaryCell p) (gamma X.val)) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (p : Unary) (X : B), F.readout 0 p X = F.readout 1 p X
private theorem positive : arena.Law actual := gamma_unary

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p X => if j = i then actual.readout j p X + profileDelta
    else actual.readout j p X) (fun e => nomatch e)
private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  let p : Unary := Unary.shift 0
  let X := ComplementFibers.balancedSection 3 0
  have h := congrArg NativeTimeProfile.readout (law p X)
  have hp := congrArg NativeTimeProfile.readout (positive p X)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    simp only [changed, realize, ite_true, show (0 : Fin 2) ≠ 1 by decide,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, map_add, profileDelta_readout] at h <;> omega

private theorem lhs_readout (X : B) :
    NativeTimeProfile.readout (actual.readout 0 (Unary.shift 0) X) = q X.val := by
  change NativeTimeProfile.readout (gamma (unary (Unary.shift 0) X).val) = _
  rw [readout_gamma]
  rfl

def evidence : Registration arena (type_of% (@gamma_unary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p X
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    let p : Unary := Unary.shift 0
    let X := ComplementFibers.balancedSection 3 0
    let Y := ComplementFibers.balancedSection 3 1
    refine ⟨p, X, Y, ?_⟩
    intro h
    have hx := positive p X
    have hy := positive p Y
    have hi : i = 0 ∨ i = 1 := by omega
    have hh : actual.readout 0 p X = actual.readout 0 p Y := by
      rcases hi with rfl | rfl
      · exact h
      · exact hx.trans (h.trans hy.symm)
    have hh' := congrArg NativeTimeProfile.readout hh
    change NativeTimeProfile.readout (actual.readout 0 (Unary.shift 0) X) =
      NativeTimeProfile.readout (actual.readout 0 (Unary.shift 0) Y) at hh'
    rw [lhs_readout, lhs_readout] at hh'
    have h0 : q X.val = 0 := ComplementFibers.balancedSection_readout 3 0
    have h1 : q Y.val = 1 := ComplementFibers.balancedSection_readout 3 1
    rw [h0,h1] at hh'
    contradiction

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.gamma_unary)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.gamma_unary
  realizationName := `Reg.Support.NativeTimeProfile.PrimitiveEvidence.UnaryPush.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end UnaryPush

namespace ParallelPush
@[reducible] def signature : Signature where
  Params := B
  State _ := B
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Profile
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i p X => match i.val with | 0 => gamma (ParallelComposition.parallelBalanced p X).val | _ => gamma p.val + gamma X.val) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (p : B) (X : B), F.readout 0 p X = F.readout 1 p X
private theorem positive : arena.Law actual := gamma_parallel

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p X => if j = i then actual.readout j p X + profileDelta
    else actual.readout j p X) (fun e => nomatch e)
private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  let p : B := zero
  let X := ComplementFibers.balancedSection 3 0
  have h := congrArg NativeTimeProfile.readout (law p X)
  have hp := congrArg NativeTimeProfile.readout (positive p X)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    simp only [changed, realize, ite_true, show (0 : Fin 2) ≠ 1 by decide,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, map_add, profileDelta_readout] at h <;> omega

private theorem lhs_readout (X : B) :
    NativeTimeProfile.readout (actual.readout 0 (zero) X) = q X.val := by
  change NativeTimeProfile.readout (gamma (ParallelComposition.parallelBalanced (zero) X).val) = _
  rw [readout_gamma]
  change q (ParallelComposition.parallel zero.val X.val) = q X.val
  rw [ParallelComposition.q_parallel]
  have hz : q zero.val = 0 := ComplementFibers.balancedSection_readout 3 0
  rw [hz, zero_add]

def evidence : Registration arena (type_of% (@gamma_parallel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p X
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    let p : B := zero
    let X := ComplementFibers.balancedSection 3 0
    let Y := ComplementFibers.balancedSection 3 1
    refine ⟨p, X, Y, ?_⟩
    intro h
    have hx := positive p X
    have hy := positive p Y
    have hi : i = 0 ∨ i = 1 := by omega
    have hh : actual.readout 0 p X = actual.readout 0 p Y := by
      rcases hi with rfl | rfl
      · exact h
      · exact hx.trans (h.trans hy.symm)
    have hh' := congrArg NativeTimeProfile.readout hh
    change NativeTimeProfile.readout (actual.readout 0 (zero) X) =
      NativeTimeProfile.readout (actual.readout 0 (zero) Y) at hh'
    rw [lhs_readout, lhs_readout] at hh'
    have h0 : q X.val = 0 := ComplementFibers.balancedSection_readout 3 0
    have h1 : q Y.val = 1 := ComplementFibers.balancedSection_readout 3 1
    rw [h0,h1] at hh'
    contradiction

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.gamma_parallel)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.gamma_parallel
  realizationName := `Reg.Support.NativeTimeProfile.PrimitiveEvidence.ParallelPush.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end ParallelPush

namespace ProductPush
@[reducible] def signature : Signature where
  Params := B
  State _ := B
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Profile
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i p X => match i.val with | 0 => gamma (GeneratedProduct.productBalanced p X).val | _ => productPush (gamma p.val) (gamma X.val)) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (p : B) (X : B), F.readout 0 p X = F.readout 1 p X
private theorem positive : arena.Law actual := gamma_product

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p X => if j = i then actual.readout j p X + profileDelta
    else actual.readout j p X) (fun e => nomatch e)
private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  let p : B := ComplementFibers.balancedSection 3 1
  let X := ComplementFibers.balancedSection 3 0
  have h := congrArg NativeTimeProfile.readout (law p X)
  have hp := congrArg NativeTimeProfile.readout (positive p X)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    simp only [changed, realize, ite_true, show (0 : Fin 2) ≠ 1 by decide,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, map_add, profileDelta_readout] at h <;> omega

private theorem lhs_readout (X : B) :
    NativeTimeProfile.readout (actual.readout 0 (ComplementFibers.balancedSection 3 1) X) = q X.val := by
  change NativeTimeProfile.readout (gamma (GeneratedProduct.productBalanced (ComplementFibers.balancedSection 3 1) X).val) = _
  rw [readout_gamma]
  change q (GeneratedProduct.product (ComplementFibers.balancedSection 3 1).val X.val) = q X.val
  rw [GeneratedProduct.q_product]
  have hq : q (ComplementFibers.balancedSection 3 1).val = 1 :=
    ComplementFibers.balancedSection_readout 3 1
  rw [hq, one_mul]

def evidence : Registration arena (type_of% (@gamma_product)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p X
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    let p : B := ComplementFibers.balancedSection 3 1
    let X := ComplementFibers.balancedSection 3 0
    let Y := ComplementFibers.balancedSection 3 1
    refine ⟨p, X, Y, ?_⟩
    intro h
    have hx := positive p X
    have hy := positive p Y
    have hi : i = 0 ∨ i = 1 := by omega
    have hh : actual.readout 0 p X = actual.readout 0 p Y := by
      rcases hi with rfl | rfl
      · exact h
      · exact hx.trans (h.trans hy.symm)
    have hh' := congrArg NativeTimeProfile.readout hh
    change NativeTimeProfile.readout (actual.readout 0 (ComplementFibers.balancedSection 3 1) X) =
      NativeTimeProfile.readout (actual.readout 0 (ComplementFibers.balancedSection 3 1) Y) at hh'
    rw [lhs_readout, lhs_readout] at hh'
    have h0 : q X.val = 0 := ComplementFibers.balancedSection_readout 3 0
    have h1 : q Y.val = 1 := ComplementFibers.balancedSection_readout 3 1
    rw [h0,h1] at hh'
    contradiction

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.gamma_product)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.gamma_product
  realizationName := `Reg.Support.NativeTimeProfile.PrimitiveEvidence.ProductPush.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end ProductPush

namespace NativeEvaluation
@[reducible] def signature : Signature where
  Params := Σ n : Nat, CopyTerm n × (Fin n → B)
  State _ := Augmented
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p z => decide (model p.2.1 (fun i => pack (p.2.2 i)) = z))
  (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {n : Nat} (N : CopyTerm n) (h : TemporalFree N)
    (v : Fin n → B) (Y : B) (he : eval N v = some Y),
    F.readout 0 ⟨n,N,v⟩ (pack Y) = true
private theorem positive : arena.Law actual := by
  intro n N h v Y he
  simpa only [actual, realize, decide_eq_true_eq] using model_eval N h v Y he
def changed : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
private theorem changed_negative : ¬ arena.Law changed := by
  intro law
  have h := law CopyTerm.input trivial (fun _ => zero) zero rfl
  change false = true at h
  cases h

def evidence : Registration arena (type_of% (@model_eval)) where
  actual := actual
  bridge := by
    simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨positive, changed, changed_negative⟩
  sensitivity := ⟨fun i => ⟨changed,
    (by intro j h; exact (h (Subsingleton.elim j i)).elim), rfl, changed_negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨1, CopyTerm.input, fun _ => zero⟩, pack zero, (0,0), ?_⟩
    have hn : pack zero ≠ (0,0) := by
      intro h
      have := congrArg Prod.fst h
      norm_num [pack] at this
    change decide (pack zero = pack zero) ≠ decide (pack zero = (0,0))
    simp [hn]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.model_eval) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.model_eval
  realizationName := `Reg.Support.NativeTimeProfile.PrimitiveEvidence.NativeEvaluation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end NativeEvaluation

end
end Reg.Support.NativeTimeProfile.PrimitiveEvidence
