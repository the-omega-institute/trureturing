import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight

open scoped BigOperators Matrix
open _root_.D5.S3.Quantum.Entanglement.PhaseHistoryBound (transition)
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℝ × ℕ × Bool × Bool
  State p := Fin p.2.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => pathMass p.1 p.2.1 p.2.2.1 w p.2.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℝ) (_hp : 0 < p) (_hp1 : p < 1)
    (n : ℕ) (_hn : 1 ≤ n) (l r : Bool) (w : Fin n → Bool)
    (_hw : Adm (n + 2) (Fin.cons l (Fin.snoc w r))),
    R.readout () (p, n, l, r) w =
      p ^ r.toNat * (1 - p) ^ (n + 1 - l.toNat - r.toNat) *
        (p / (1 - p) ^ 2) ^ (∑ i, (w i).toNat) ∧
      0 < R.readout () (p, n, l, r) w

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := (h (1 / 2) (by norm_num) (by norm_num) 1 (by omega)
    false false (fun _ => false) (by decide)).2
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(1 / 2, 1, false, false), (fun _ => false), (fun _ => true), ?_⟩
  norm_num [actual, realize, pathMass, transition]

def family : Registration arena (type_of% (@path_weight_formula)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨path_weight_formula, rejected, rejected_law⟩
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
    (@path_weight_formula) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight.family
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
    owner := `D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight
    definition := none
    coordinates := #[0, 3, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

abbrev minorSignature : Signature where
  Params := Σ N : ℕ, (Fin (N + 1) → ℝ) × Bool × Bool
  State q := Fin (q.1 + 1) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def minorActual : Realization minorSignature :=
  realize minorSignature (fun _ q θ => (cutMinor q.1 q.2.1 θ q.2.2.1 q.2.2.2).det)
    (fun e => nomatch e)

def minorRejected : Realization minorSignature :=
  realize minorSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev minorArena : Arena where
  signature := minorSignature
  Law R := ∀ (N : ℕ) (p θ : Fin (N + 1) → ℝ)
    (_hp : ∀ k, 0 < p k ∧ p k < 1) (_hmono : StrictMono p)
    (_hθ : ∀ k, 0 < θ k) (l r : Bool),
    Function.Injective (halfWord N) ∧
    R.readout () ⟨N, p, l, r⟩ θ =
      (∏ k, θ k / activityPartition (p k) ((2 * N + 1) + (2 * N + 1)) l r) *
        (∏ i : Fin (N + 1), ∏ j ∈ Finset.Ioi i,
          (p j / (1 - p j) ^ 2 - p i / (1 - p i) ^ 2)) ^ 2 ∧
      0 < R.readout () ⟨N, p, l, r⟩ θ

private theorem minorRejected_law : ¬minorArena.Law minorRejected := by
  intro h
  have hh := (h 0 (fun _ => 1 / 2) (fun _ => 1) (by intro k; norm_num)
    (by intro i j hij; have := i.isLt; have := j.isLt; have : i.val < j.val := hij; omega)
    (by intro k; norm_num) false false).2.2
  norm_num [minorRejected, realize] at hh

private theorem minorActual_dependence : ObservationalDependence minorSignature minorActual := by
  intro _
  refine ⟨⟨0, (fun _ => 1 / 2), false, false⟩, (fun _ => 1), (fun _ => 2), ?_⟩
  change (cutMinor 0 (fun _ => 1 / 2) (fun _ => 1) false false).det ≠
    (cutMinor 0 (fun _ => 1 / 2) (fun _ => 2) false false).det
  have hp : ∀ k : Fin 1, 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := by
    intro k; norm_num
  have hm : StrictMono (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
    intro i j hij
    have := i.isLt
    have := j.isLt
    have : i.val < j.val := hij
    omega
  have h1 := (persistent_mixture_minor 0 (fun _ => 1 / 2) (fun _ => 1)
    hp hm (by intro k; norm_num) false false).2
  have h2 := (persistent_mixture_minor 0 (fun _ => 1 / 2) (fun _ => 2)
    hp hm (by intro k; norm_num) false false).2
  have he : (cutMinor 0 (fun _ => 1 / 2) (fun _ => 2) false false).det =
      2 * (cutMinor 0 (fun _ => 1 / 2) (fun _ => 1) false false).det := by
    rw [h2.1, h1.1]
    simp
    <;> ring
  intro h
  linarith [h1.2]

def minorFamily : Registration minorArena (type_of% (@persistent_mixture_minor)) where
  actual := minorActual
  bridge := Iff.rfl
  variation := ⟨persistent_mixture_minor, minorRejected, minorRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨minorRejected, ?_, rfl, minorRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := minorActual_dependence

def minorAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@persistent_mixture_minor) (Realization minorSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight.minorUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight.minorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨minorArena⟩
  objectArena := .source ⟨minorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source minorArena ⟨minorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize minorSignature minorActual.readout minorActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight
    definition := none
    coordinates := #[0, 1, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms minorFamily
#print axioms minorAudit

end
end Reg.D5.S3.Combinatorics.Graph.LegalWords.MarkovBlockWeight
