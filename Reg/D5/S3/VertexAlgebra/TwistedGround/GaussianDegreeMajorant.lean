import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant
import Reg.Support.DependentFamily
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
open Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant

private def vacuum (n : ℕ) : ℝ := if n = 0 then 1 else 0
private theorem vacuum_nonneg (n : ℕ) : 0 ≤ vacuum n := by unfold vacuum; split <;> norm_num
private theorem vacuum_zero : vacuum 0 = 1 := by simp [vacuum]
private theorem vacuum_rec (n : ℕ) :
    (n + 1 : ℝ) * vacuum (n + 1) ≤ (0 + 0 * n) * vacuum n := by
  simp [vacuum]

abbrev boundSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualBound : Realization boundSignature :=
  realize _ (fun _ c r => Real.exp (c / (1 - r))) (fun e => nomatch e)
def rejectedBound : Realization boundSignature :=
  realize _ (fun _ _ _ => -1) (fun e => nomatch e)
private theorem bound_dependence : ObservationalDependence boundSignature actualBound := by
  intro i
  refine ⟨1, 0, 1 / 2, ?_⟩
  change Real.exp (1 / (1 - 0)) ≠ Real.exp (1 / (1 - 1 / 2))
  intro h
  have := Real.exp_injective h
  norm_num at this

namespace Partial
def arena : Arena where
  signature := boundSignature
  Law R := ∀ (a : ℕ → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hr1 : r < 1) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤ (c + r * n) * a n) (N : ℕ),
    (∑ n ∈ Finset.range (N + 1), a n) ≤ R.readout () c r
private theorem rejected_fails : ¬ arena.Law rejectedBound := by
  intro h
  have hh := h vacuum (c := 0) (r := 0) (by norm_num) (by norm_num)
    (by norm_num) vacuum_nonneg vacuum_zero vacuum_rec 0
  norm_num [vacuum, rejectedBound, realize] at hh
def evidence : Registration arena (type_of% @partial_sum_bound) where
  actual := actualBound
  bridge := Iff.rfl
  variation := ⟨@partial_sum_bound, rejectedBound, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedBound, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := bound_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@partial_sum_bound) (Realization boundSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant.Partial.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant.Partial.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature actualBound.readout actualBound.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Partial

namespace Tsum
def arena : Arena where
  signature := boundSignature
  Law R := ∀ (a : ℕ → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hr1 : r < 1) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤ (c + r * n) * a n),
    (∑' n, a n) ≤ R.readout () c r
private theorem rejected_fails : ¬ arena.Law rejectedBound := by
  intro h
  have hh := h vacuum (c := 0) (r := 0) (by norm_num) (by norm_num)
    (by norm_num) vacuum_nonneg vacuum_zero vacuum_rec
  norm_num [vacuum, rejectedBound, realize] at hh
def evidence : Registration arena (type_of% @tsum_bound) where
  actual := actualBound
  bridge := Iff.rfl
  variation := ⟨@tsum_bound, rejectedBound, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedBound, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := bound_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tsum_bound) (Realization boundSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant.Tsum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant.Tsum.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature actualBound.readout actualBound.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Tsum

namespace Summability
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize _ (fun _ _ a => a) (fun e => nomatch e)
def rejected : Realization signature :=
  realize _ (fun _ _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hr1 : r < 1) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 = 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * a (n + 1) ≤ (c + r * n) * a n),
    Summable (R.readout () () a)
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh : Summable (fun _ : ℕ => (1 : ℝ)) :=
    h vacuum (c := 0) (r := 0) (by norm_num) (by norm_num)
      (by norm_num) vacuum_nonneg vacuum_zero vacuum_rec
  letI := Finite.of_summable_const (by norm_num : (0 : ℝ) < 1) hh
  exact not_finite ℕ
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have := congrFun h 0
  norm_num [actual, realize] at this

def evidence : Registration arena (type_of% @summable_of_creation_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@summable_of_creation_recurrence, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summable_of_creation_recurrence) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant.Summability.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant.Summability.evidence
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
  escapeFrom := some (ℕ → ℝ)
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Summability

end Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianDegreeMajorant
