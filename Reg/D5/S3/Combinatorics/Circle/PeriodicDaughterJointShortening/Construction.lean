import D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening.Construction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact dependent-family audit of the full MINUS-one common-cut theorem. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening

/- Exact dependent-family pattern from settled PhysicalJointRepetition Reg,
51518b6ee6ccebd7ee3cb0e03e5c13589a570a9c, adapted to K=(d+1)*r-1 and
its explicit global cut. -/
abbrev Input := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

abbrev signature : Signature where
  Params := Input
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output side p := match side with
    | false => List (Fin (length p.1 p.2.2.1)) → Prop
    | true => List (Fin (length p.1 p.2.2.1 + 1)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun side p t => match side with
      | false => OriginalOrder (length p.1 p.2.2.1) t
      | true => OriginalOrder (length p.1 p.2.2.1 + 1) t)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun side _ _ => match side with
    | false => fun _ => False
    | true => fun _ => False) (fun e => nomatch e)

def deleted (side : Bool) : Realization signature :=
  realize signature
    (fun j p t => if h : j = side then h ▸ rejected.readout side p t
      else actual.readout j p t)
    (fun e => nomatch e)

/-- All twelve original binders, including the dependent physical word and
both full actual base witnesses, remain under this universal law. -/
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (d w r cut : ℕ) (hd : 2 ≤ d) (hw0 : 1 ≤ w)
      (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (hcut : cut ≤ d)
      (tau : List (Fin d)),
    OriginalOrder d w tau →
    OriginalOrder (d + 1) (2 * w) (earWord d tau cut) →
    commonCut d r cut ≤ length d r ∧
    A.readout false ⟨d, w, r, cut⟩ (seed d w r) (shortenedWord d r hr tau cut) ∧
    A.readout true ⟨d, w, r, cut⟩ (2 * seed d w r)
      (earWord (length d r) (shortenedWord d r hr tau cut) (commonCut d r cut))

private theorem actual_law : arena.Law actual := by
  intro d w r cut hd hw0 hw hr hcut tau hold hnew
  simpa [actual, realize] using
    periodic_daughter_joint_shortening d w r cut hd hw0 hw hr hcut tau hold hnew

/- One inhabited base witness is reused for variation and both deletions.
It is not the registered family or a replacement for its twelve binders. -/
private theorem base_old : OriginalOrder 2 1 [0, 1] := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  cases h with
  | zero => norm_num [OriginalOrder, actualSource, centered, modulus]
  | succ h => cases h <;> norm_num [OriginalOrder, actualSource, centered, modulus]

private theorem base_new : OriginalOrder 3 2 (earWord 2 [0, 1] 0) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  cases h with
  | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
  | succ h =>
      cases h with
      | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
      | succ h =>
          cases h with
          | zero => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]
          | succ h => norm_num [OriginalOrder, earWord, actualSource, centered, modulus]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 1 2 0 (by omega) (by omega) (by omega) (by omega) (by omega)
    [0, 1] base_old base_new).2.1
  exact hh

private theorem deleted_law (side : Bool) : ¬ arena.Law (deleted side) := by
  intro h
  have hh := h 2 1 2 0 (by omega) (by omega) (by omega) (by omega) (by omega)
    [0, 1] base_old base_new
  cases side with
  | false =>
      have hf := hh.2.1
      dsimp [deleted, rejected, actual, realize] at hf
  | true =>
      have hf := hh.2.2
      dsimp [deleted, rejected, actual, realize] at hf

private theorem source_bridge :
    (type_of% (@periodic_daughter_joint_shortening)) ↔ arena.Law actual := by
  constructor
  · intro h d w r cut hd hw0 hw hr hcut tau hold hnew
    simpa [actual, realize] using h d w r cut hd hw0 hw hr hcut tau hold hnew
  · intro h d w r cut hd hw0 hw hr hcut tau hold hnew
    simpa [actual, realize] using h d w r cut hd hw0 hw hr hcut tau hold hnew

private def word5 : List (Fin 5) := [0, 1, 2, 3, 4]
private def word6 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

private theorem zero_order (k : ℕ) (hk : 0 < k) (xs : List (Fin k))
    (hp : xs.Perm (List.finRange k)) : OriginalOrder k 0 xs := by
  obtain ⟨hN, ho⟩ := _root_.D5.S3.Combinatorics.Circle.TwoRunSource.modulus_positive_odd k hk
  have hhalf : 0 ≤ modulus k / 2 := by omega
  have hf : actualSource k 0 = fun _ => (0 : ℤ) := by
    funext i
    apply centered_unique hN ho (centered_bounds hN ho _) ⟨by omega, hhalf⟩
    simp [centered_mod]
  refine ⟨hp, ?_, ?_⟩
  · simp [hf]
  · intro h
    simp only [hf, List.map_const', List.sum_replicate, nsmul_zero, Set.mem_Icc]
    exact ⟨by omega, hhalf⟩

private theorem bad5 : ¬ OriginalOrder 5 2 word5 := by
  intro h
  have hh := (h.2.2 4).1
  norm_num [word5, actualSource, centered, modulus] at hh

private theorem bad6 : ¬ OriginalOrder 6 2 word6 := by
  intro h
  have hh := (h.2.2 5).1
  norm_num [word6, actualSource, centered, modulus] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro side
  let p : Input := ⟨2, 1, 2, 0⟩
  refine ⟨p, 0, 2, ?_⟩
  cases side with
  | false =>
      intro he
      have hp := congrFun he word5
      apply bad5
      have hz := zero_order 5 (by omega) word5 (by decide)
      simpa [actual, realize, p, length] using hp.mp hz
  | true =>
      intro he
      have hp := congrFun he word6
      apply bad6
      have hz := zero_order 6 (by omega) word6 (by decide)
      simpa [actual, realize, p, length] using hp.mp hz

def source_registration : Registration arena (type_of% (@periodic_daughter_joint_shortening)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro side
      cases side with
      | false =>
          refine ⟨deleted false, ?_, rfl, deleted_law false⟩
          intro j hji
          cases j with
          | false => exact False.elim (hji rfl)
          | true => simp [deleted, realize]
      | true =>
          refine ⟨deleted true, ?_, rfl, deleted_law true⟩
          intro j hji
          cases j with
          | false => simp [deleted, realize]
          | true => exact False.elim (hji rfl)
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening.periodic_daughter_joint_shortening)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening.periodic_daughter_joint_shortening.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening.Construction
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end Reg.D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening
