import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence

open scoped BigOperators
open _root_.D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion
open _root_.D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private theorem quarter_interior : Interior (fun _ => (1 / 4 : ℝ)) 2 := by
  constructor <;> intros <;> norm_num

namespace Reconstruction

abbrev signature : Signature where
  Params := (ℕ → ℝ) × ℕ
  State p := Fin (p.2 + 2) → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p b => law (activity p.1 p.2) b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u : ℕ → ℝ) (n : ℕ) (_hu : Interior u (n + 2)),
    (∀ i, 0 < activity u n i) ∧
    R.readout () (u, n) = completion u n ∧
    partition (activity u n) =
      (∏ i : Fin n, (1 - u (i.val + 1))) / ∏ i : Fin (n + 1), seam u i.val ∧
    Means u (n + 1) (R.readout () (u, n)) ∧
    ∀ (w : Fin (n + 2) → ℝ), (∀ i, 0 < w i) →
      (Means u (n + 1) (law w) ↔ w = activity u n)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := congrFun (h (fun _ => 1 / 4) 0 quarter_interior).2.1 (fun _ => false)
  norm_num [rejected, realize, completion, Fin.prod_univ_succ, pair] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨((fun _ => (1 / 4 : ℝ)), 0), (fun _ => false), (fun i => decide (i = 0)), ?_⟩
  change law (activity (fun _ => (1 / 4 : ℝ)) 0) (fun _ => false) ≠
    law (activity (fun _ => (1 / 4 : ℝ)) 0) (fun i => decide (i = 0))
  rw [(activity_mean_correspondence _ 0 quarter_interior).2.1]
  norm_num [completion, Fin.prod_univ_succ, pair]

def family : Registration arena (type_of% (@activity_mean_correspondence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨activity_mean_correspondence, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@activity_mean_correspondence) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence.Reconstruction.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence.Reconstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reconstruction


namespace InteriorMeans

abbrev signature : Signature where
  Params := Σ n : ℕ, Fin (n + 2) → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => meansOf p.2 i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (w : Fin (n + 2) → ℝ) (_hw : ∀ i, 0 < w i),
    Interior (R.readout () ⟨n, w⟩) (n + 2) ∧
      Means (R.readout () ⟨n, w⟩) (n + 1) (law w)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := (h 0 (fun _ => 1) (fun _ => zero_lt_one)).1.1 0 (by omega)
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  let u : ℕ → ℝ := fun i => if i = 0 then 1 / 4 else 1 / 3
  have hu : Interior u 2 := by
    constructor
    · intro i _
      by_cases hi : i = 0 <;> norm_num [u, hi]
    · intro i hi
      have : i = 0 := by omega
      subst i
      norm_num [u]
  have h := activity_mean_correspondence u 0 hu
  have hm := (positive_activity_means 0 (activity u 0) h.1).2
  have he (i : Fin 2) : meansOf (activity u 0) i.val = u i.val :=
    (hm i).symm.trans (h.2.2.2.1 i)
  refine ⟨⟨0, activity u 0⟩, 0, 1, ?_⟩
  change meansOf (activity u 0) 0 ≠ meansOf (activity u 0) 1
  have hzero := he (0 : Fin 2)
  have hone := he (1 : Fin 2)
  norm_num [u] at hzero hone
  intro hz
  linarith

def family : Registration arena (type_of% (@positive_activity_means)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive_activity_means, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@positive_activity_means) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence.InteriorMeans.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence.InteriorMeans.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end InteriorMeans

#print axioms Reconstruction.audit
#print axioms InteriorMeans.audit

end
end Reg.D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence
