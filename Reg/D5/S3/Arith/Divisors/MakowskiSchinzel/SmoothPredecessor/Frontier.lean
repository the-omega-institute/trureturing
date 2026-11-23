import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Frontier
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of frontier refinement of the weighted smooth fold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Frontier

open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev refineSignature : Signature where
  Params := (ℕ → ℕ) × ℕ × (List ℕ × ℕ → Bool) × ℕ
  State _ := List ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def refineActual : Realization refineSignature :=
  realize refineSignature (fun _ a n => ((refine a.2.1 a.2.2.1 a.2.2.2 n).map
      fun x => smoothSum a.1 x.1 a.2.1 x.2).sum)
    (fun e => nomatch e)

def refineRejected : Realization refineSignature :=
  realize refineSignature
    (fun _ a n => ((refine a.2.1 a.2.2.1 a.2.2.2 n).map
      fun x => smoothSum a.1 x.1 a.2.1 x.2).sum + 1) (fun e => nomatch e)

abbrev refineArena : Arena where
  signature := refineSignature
  Law R := ∀ (w : ℕ → ℕ) (X : ℕ) (leaf : List ℕ × ℕ → Bool) (k : ℕ) (n : List ℕ × ℕ),
    R.readout () (w, X, leaf, k) n = smoothSum w n.1 X n.2

private theorem refineRejected_law : ¬refineArena.Law refineRejected := by
  intro h
  have hh := h (fun _ => 0) 0 (fun _ => true) 0 ([], 0)
  have hs := sum_refine (fun _ => 0) 0 (fun _ => true) 0 ([], 0)
  change ((refine 0 (fun _ => true) 0 ([], 0)).map
    fun x => smoothSum (fun _ => 0) x.1 0 x.2).sum + 1 = _ at hh
  omega

def refineFamily : Registration refineArena (type_of% (@sum_refine)) where
  actual := refineActual
  bridge := Iff.rfl
  variation := ⟨sum_refine, refineRejected, refineRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨refineRejected, ?_, rfl, refineRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(id, 1, fun _ => true, 0), ([], 0), ([], 1), ?_⟩
    norm_num [refineActual, realize, refine, smoothSum]

def refineAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_refine) (Realization refineSignature)
    ((ℕ → ℕ) → ℕ → List (List ℕ × ℕ) → ℕ) Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.sum_refine.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Frontier.refineFamily
  realizationSource := none
  generated := false
  arena := .source ⟨refineArena⟩
  objectArena := .source ⟨refineArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source refineArena ⟨refineFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize refineSignature
    (fun _ a n => ((refine a.2.1 a.2.2.1 a.2.2.2 n).map
      fun x => smoothSum a.1 x.1 a.2.1 x.2).sum) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Frontier
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev frontierSignature : Signature where
  Params := (ℕ → ℕ) × ℕ
  State _ := List ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def frontierActual : Realization frontierSignature :=
  realize frontierSignature (fun _ a n => smoothSum a.1 n.1 a.2 n.2) (fun e => nomatch e)

def frontierRejected : Realization frontierSignature :=
  realize frontierSignature (fun _ a n => smoothSum a.1 n.1 a.2 n.2 + 1)
    (fun e => nomatch e)

abbrev frontierArena : Arena where
  signature := frontierSignature
  Law R := ∀ (w : ℕ → ℕ) {X k : ℕ} {n : List ℕ × ℕ} {F : List (List ℕ × ℕ)},
    frontierOk X k n F = true → R.readout () (w, X) n = (F.map fun x => smoothSum w x.1 X x.2).sum

private theorem frontierRejected_law : ¬frontierArena.Law frontierRejected := by
  intro h
  have hok : frontierOk 0 0 ([], 0) [([], 0)] = true := by decide
  have hh := h (fun _ => 0) hok
  have hs := smoothSum_eq_of_frontierOk (fun _ => 0) hok
  change smoothSum (fun _ => 0) ([] : List ℕ) 0 0 + 1 = _ at hh
  change smoothSum (fun _ => 0) ([] : List ℕ) 0 0 = _ at hs
  omega

def frontierFamily :
    Registration frontierArena (type_of% (@smoothSum_eq_of_frontierOk)) where
  actual := frontierActual
  bridge := Iff.rfl
  variation := ⟨smoothSum_eq_of_frontierOk, frontierRejected, frontierRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨frontierRejected, ?_, rfl, frontierRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(id, 1), ([], 0), ([], 1), ?_⟩
    norm_num [frontierActual, realize, smoothSum]

def frontierAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smoothSum_eq_of_frontierOk) (Realization frontierSignature)
    ((ℕ → ℕ) → List ℕ → ℕ → ℕ → ℕ) Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.smoothSum_eq_of_frontierOk.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Frontier.frontierFamily
  realizationSource := none
  generated := false
  arena := .source ⟨frontierArena⟩
  objectArena := .source ⟨frontierArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frontierArena ⟨frontierFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frontierSignature
    (fun _ a n => smoothSum a.1 n.1 a.2 n.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Frontier
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Frontier
