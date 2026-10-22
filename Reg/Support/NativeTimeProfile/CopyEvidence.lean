import D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Reg.Support.NativeTimeProfile.CopyEvidence
open _root_.D5.S0.History.Spacetime.ArchiveCarrier
open _root_.D5.S3.ConceptDynamics.Spacetime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ComplementCharge TotalCopyNormalization NativeTimeProfile
open scoped BigOperators
noncomputable section
open Classical

@[reducible] def signature : Signature where
  Params := Σ r : Nat, CopyTerm r × B
  State p := Fin p.1 → Nat
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Profile
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i p v =>
    match i.val with
    | 0 => gamma (value p.2.1 (fun j => copies (v j) p.2.2)).val
    | _ => ∑ J : Finset (Fin p.1),
      (∏ j ∈ J, (v j : Int)) • profileCoefficients p.2.1 p.2.2 J)
  (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ {r : Nat} (N : CopyTerm r), TemporalFree N → ∀ (X : B) (v : Fin r → Nat),
    F.readout 0 ⟨r,N,X⟩ v = F.readout 1 ⟨r,N,X⟩ v
private theorem positive : arena.Law actual :=
  @profile_multiaffine

private def delta : Profile := gamma (ComplementFibers.balancedSection 3 1).val
private theorem readout_delta : NativeTimeProfile.readout delta = 1 := by
  rw [delta, readout_gamma]
  exact ComplementFibers.balancedSection_readout 3 1

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p v => if j = i then actual.readout j p v + delta else actual.readout j p v)
  (fun e => nomatch e)

private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  let X := ComplementFibers.balancedSection 3 1
  have h := congrArg NativeTimeProfile.readout (law (r := 1) .input trivial X (fun _ => 0))
  have hp := congrArg NativeTimeProfile.readout (positive (r := 1) .input trivial X (fun _ => 0))
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;>
    simp only [changed, realize, ite_true, show (0 : Fin 2) ≠ 1 by decide,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, map_add, readout_delta] at h <;> omega

private theorem input_readout (X : B) (n : Nat) :
    NativeTimeProfile.readout (actual.readout 0 ⟨1,.input,X⟩ (fun _ => n)) =
      (n : Int) * q X.val := by
  change NativeTimeProfile.readout (gamma (copies n X).val) = _
  induction n with
  | zero =>
    rw [copies, readout_gamma]
    simpa [zero] using (show q (ComplementFibers.balancedSection 3 0).val = 0 from
      ComplementFibers.balancedSection_readout 3 0)
  | succ n ih =>
    rw [copies, gamma_parallel, map_add, ih, readout_gamma]
    push_cast
    ring

def evidence : Registration arena (type_of% (@profile_multiaffine)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p v
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    let X := ComplementFibers.balancedSection 3 1
    refine ⟨⟨1,.input,X⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have h0 := positive (r := 1) .input trivial X (fun _ => 0)
    have h1 := positive (r := 1) .input trivial X (fun _ => 1)
    have hi : i = 0 ∨ i = 1 := by omega
    have hh : actual.readout 0 ⟨1,.input,X⟩ (fun _ => 0) =
        actual.readout 0 ⟨1,.input,X⟩ (fun _ => 1) := by
      rcases hi with rfl | rfl
      · exact h
      · exact h0.trans (h.trans h1.symm)
    have hh' := congrArg NativeTimeProfile.readout hh
    rw [input_readout, input_readout] at hh'
    have hX : q X.val = 1 := ComplementFibers.balancedSection_readout 3 1
    rw [hX] at hh'
    norm_num at hh'

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.profile_multiaffine)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.profile_multiaffine
  realizationName := `Reg.Support.NativeTimeProfile.CopyEvidence.evidence
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
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
namespace Necessity
open RegionFilterQExpressibility
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Region
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ R => match i.val with | 0 => decide (CopyQExpressible R) | _ => decide (Tail R)) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ R : Region, F.readout 0 () R = true → F.readout 1 () R = true
private theorem positive : arena.Law actual := by
  intro R
  change decide (CopyQExpressible R) = true → decide (Tail R) = true
  simpa only [decide_eq_true_eq] using copy_q_expressible_implies_tail R
private theorem empty_tail : Tail (∅ : Region) := ⟨0, by
  intro p t t' ht ht'
  simp⟩
private def alternating : Region := {z | z.1 % 2 = 0}
private theorem alternating_not_tail : ¬ Tail alternating := by
  rintro ⟨c,hc⟩
  have h := hc (fun _ => 0) (2 * (min c 0 - 1)) (2 * (min c 0 - 1) - 1)
    (by omega) (by omega)
  change (2 * (min c 0 - 1)) % 2 = 0 ↔ (2 * (min c 0 - 1) - 1) % 2 = 0 at h
  omega

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p R => if j = i then !(actual.readout j p R) else actual.readout j p R)
  (fun e => nomatch e)
private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  have he := tail_implies_copy_q_expressible ∅ empty_tail
  have hn : ¬ CopyQExpressible alternating := fun h =>
    alternating_not_tail (copy_q_expressible_implies_tail alternating h)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · have h := law alternating
    simp [changed, actual, realize, hn, alternating_not_tail] at h
  · have h := law ∅
    simp [changed, actual, realize, he, empty_tail] at h

def evidence : Registration arena (type_of% (@copy_q_expressible_implies_tail)) where
  actual := actual
  bridge := by
    change (∀ R : Region, CopyQExpressible R → Tail R) ↔ _
    simp only [actual, realize, Fin.val_zero, Fin.val_one, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      ite_false, decide_eq_true_eq]
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p R
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨(), ∅, alternating, ?_⟩
    have he := tail_implies_copy_q_expressible ∅ empty_tail
    have hn : ¬ CopyQExpressible alternating := fun h =>
      alternating_not_tail (copy_q_expressible_implies_tail alternating h)
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp [actual, realize, he, hn, empty_tail, alternating_not_tail]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copy_q_expressible_implies_tail)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copy_q_expressible_implies_tail
  realizationName := `Reg.Support.NativeTimeProfile.CopyEvidence.Necessity.evidence
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
      path := #["body","domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true },
      {
      path := #["body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end Necessity

namespace Sufficiency
open RegionFilterQExpressibility
@[reducible] def signature : Signature where
  Params := Unit
  State _ := Region
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ R => match i.val with | 0 => decide (Tail R) | _ => decide (CopyQExpressible R)) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ R : Region, F.readout 0 () R = true → F.readout 1 () R = true
private theorem positive : arena.Law actual := by
  intro R
  change decide (Tail R) = true → decide (CopyQExpressible R) = true
  simpa only [decide_eq_true_eq] using tail_implies_copy_q_expressible R
private theorem empty_tail : Tail (∅ : Region) := ⟨0, by
  intro p t t' ht ht'
  simp⟩
private def alternating : Region := {z | z.1 % 2 = 0}
private theorem alternating_not_tail : ¬ Tail alternating := by
  rintro ⟨c,hc⟩
  have h := hc (fun _ => 0) (2 * (min c 0 - 1)) (2 * (min c 0 - 1) - 1)
    (by omega) (by omega)
  change (2 * (min c 0 - 1)) % 2 = 0 ↔ (2 * (min c 0 - 1) - 1) % 2 = 0 at h
  omega

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p R => if j = i then !(actual.readout j p R) else actual.readout j p R)
  (fun e => nomatch e)
private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  have he := tail_implies_copy_q_expressible ∅ empty_tail
  have hn : ¬ CopyQExpressible alternating := fun h =>
    alternating_not_tail (copy_q_expressible_implies_tail alternating h)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · have h := law alternating
    simp [changed, actual, realize, hn, alternating_not_tail] at h
  · have h := law ∅
    simp [changed, actual, realize, he, empty_tail] at h

def evidence : Registration arena (type_of% (@tail_implies_copy_q_expressible)) where
  actual := actual
  bridge := by
    change (∀ R : Region, Tail R → CopyQExpressible R) ↔ _
    simp only [actual, realize, Fin.val_zero, Fin.val_one, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      ite_false, decide_eq_true_eq]
  variation := ⟨positive, changed 0, changed_negative 0⟩
  sensitivity := ⟨fun i => ⟨changed i,
    fun j h => by
      funext p R
      simp only [changed, realize, if_neg h], rfl, changed_negative i⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    change Fin 2 at i
    refine ⟨(), ∅, alternating, ?_⟩
    have he := tail_implies_copy_q_expressible ∅ empty_tail
    have hn : ¬ CopyQExpressible alternating := fun h =>
      alternating_not_tail (copy_q_expressible_implies_tail alternating h)
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp [actual, realize, he, hn, empty_tail, alternating_not_tail]

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.tail_implies_copy_q_expressible)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.tail_implies_copy_q_expressible
  realizationName := `Reg.Support.NativeTimeProfile.CopyEvidence.Sufficiency.evidence
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
      path := #["body","domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true },
      {
      path := #["body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end Sufficiency
namespace RegionalLinearity
open RegionFilterQExpressibility
@[reducible] def signature : Signature where
  Params := Region × Nat
  State _ := B
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i p X =>
    match i.val with
    | 0 => regionReadout p.1 (copies p.2 X)
    | _ => (p.2 : Int) * regionReadout p.1 X) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (R : Region) (n : Nat) (X : B), F.readout 0 (R,n) X = F.readout 1 (R,n) X
private theorem positive : arena.Law actual := copies_region_linear

def changed (i : Fin 2) : Realization signature := realize signature
  (fun j p X => if j = i then actual.readout j p X + 1 else actual.readout j p X)
  (fun e => nomatch e)
private theorem changed_negative (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro law
  let X := ComplementFibers.balancedSection 3 0
  have h := law Set.univ 1 X
  have hp := positive Set.univ 1 X
  change (if (0 : Fin 2) = i then actual.readout 0 (Set.univ,1) X + 1
    else actual.readout 0 (Set.univ,1) X) =
    (if (1 : Fin 2) = i then actual.readout 1 (Set.univ,1) X + 1
    else actual.readout 1 (Set.univ,1) X) at h
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at h
    rw [hp] at h
    omega
  · simp only [ite_true, show (0 : Fin 2) ≠ 1 by decide, ite_false] at h
    rw [hp] at h
    omega

private theorem univ_readout (X : B) : regionReadout Set.univ X = q X.val := by
  simp [regionReadout, q, ComplementCharge.readout, charge]
private theorem lhs_readout (X : B) : actual.readout 0 (Set.univ,1) X = q X.val := by
  change regionReadout Set.univ (copies 1 X) = _
  rw [copies_region_linear]
  simp [univ_readout]

def evidence : Registration arena (type_of% (@copies_region_linear)) where
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
    let X := ComplementFibers.balancedSection 3 0
    let Y := ComplementFibers.balancedSection 3 1
    refine ⟨(Set.univ,1), X, Y, ?_⟩
    intro h
    have hx := positive Set.univ 1 X
    have hy := positive Set.univ 1 Y
    have hi : i = 0 ∨ i = 1 := by omega
    have hh : actual.readout 0 (Set.univ,1) X = actual.readout 0 (Set.univ,1) Y := by
      rcases hi with rfl | rfl
      · exact h
      · exact hx.trans (h.trans hy.symm)
    rw [lhs_readout, lhs_readout] at hh
    have h0 : q X.val = 0 := ComplementFibers.balancedSection_readout 3 0
    have h1 : q Y.val = 1 := ComplementFibers.balancedSection_readout 3 1
    rw [h0,h1] at hh
    contradiction

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copies_region_linear)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.copies_region_linear
  realizationName := `Reg.Support.NativeTimeProfile.CopyEvidence.RegionalLinearity.evidence
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
    definition := some {
      owner := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
      name := `D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.CopiesRegionLinear
      path := #[] }
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },
      {
      path := #["body","body","body","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end RegionalLinearity

namespace PolynomialIdentification
@[reducible] def signature : Signature where
  Params := Int
  State _ := Polynomial Int
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a P => decide (P = Polynomial.X * Polynomial.C a)) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law F := ∀ (P : Polynomial Int) (a : Int)
    (h : ∀ n : Nat, P.eval (n : Int) = (n : Int) * a), F.readout 0 a P = true
private theorem positive : arena.Law actual := by
  intro P a h
  simpa only [actual, realize, decide_eq_true_eq] using polynomial_identification P a h
def changed : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
private theorem changed_negative : ¬ arena.Law changed := by
  intro law
  have h := law 0 0 (by intro n; simp)
  change false = true at h
  cases h

def evidence : Registration arena (type_of% (@polynomial_identification)) where
  actual := actual
  bridge := by
    simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨positive, changed, changed_negative⟩
  sensitivity := ⟨fun i => ⟨changed,
    (by intro j h; exact (h (Subsingleton.elim j i)).elim), rfl, changed_negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨0, 0, Polynomial.X, ?_⟩
    change decide ((0 : Polynomial Int) = Polynomial.X * Polynomial.C 0) ≠
      decide ((Polynomial.X : Polynomial Int) = Polynomial.X * Polynomial.C 0)
    simp

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.polynomial_identification) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile.polynomial_identification
  realizationName := `Reg.Support.NativeTimeProfile.CopyEvidence.PolynomialIdentification.evidence
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
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evidence
#print axioms registration
end PolynomialIdentification

end
end Reg.Support.NativeTimeProfile.CopyEvidence
