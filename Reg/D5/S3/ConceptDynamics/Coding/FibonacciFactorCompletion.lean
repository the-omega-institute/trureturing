import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal23
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ → Guard
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Guard
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ path n => path n) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => .G1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s e : Guard) (w : List Label) (hw : LegalWord s e w)
    (a : ℕ → Label) (path : ℕ → Guard) (h0 : path 0 = s)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p+1)))
    (hprefix : ∀ p (hp : p < w.length), a p = w[p]), r.readout () path w.length = e

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h .G0 .G0 [] (by rfl) (fun _ => .L0) (fun _ => .G0)
    rfl (fun _ => rfl) (by intro p hp; simp at hp)
  cases impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.prefix_path_endpoint) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.prefix_path_endpoint, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(fun n => if n = 0 then .G0 else .G1), 0, 1, ?_⟩
    simp [actual, realize]

def prefix_path_endpoint_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.prefix_path_endpoint)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ path n => path n) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal23.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal23.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ path n => path n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms prefix_path_endpoint_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal23

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal27
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ state => state) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀
    (model : Model) (o : Ownership) (K : ℕ) (hK : 2 ≤ K)
    (budget : ℝ) (hbudget : actualAutomaticCost K < budget)
    (execution : List Return)
    (hcap : ∀ a ∈ execution, a.r ≤ K)
    (hhigh : ∀ (before : List Return) (a : Return) (after : List Return),
      execution = before ++ a :: after → a.r = K →
        lam - g ^ 2 * chi ^ K *
          execute .high before (initial .high model) < budget),
    ActualPairSupply model o (r.readout () () budget) .strict execution

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := h .original (fun _ => false) 2 (by decide) (actualAutomaticCost 2 + 1)
    (lt_add_one _) [] (by simp) (by
      intro before a after hsplit
      have hlen := congrArg List.length hsplit
      simp at hlen)
  obtain ⟨err, herr, _⟩ := bad .high
  have hb := herr 0
  change |err 0| < (-1 : ℝ) at hb
  linarith [abs_nonneg (err 0)]

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_capped_strict_supply_of_high_costs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_capped_strict_supply_of_high_costs, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def actual_capped_strict_supply_of_high_costs_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_capped_strict_supply_of_high_costs)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ state => state) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal27.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal27.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ state => state) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_capped_strict_supply_of_high_costs_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal27

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal26
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ K x => x - g ^ 2 * chi ^ K * hSide .high) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => actualAutomaticCost 2) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (hK : 2 ≤ K),
    actualAutomaticCost K < r.readout () K lam ∧
    lam - rho ≤ actualAutomaticCost K ∧
    lam - g ^ 2 * chi * xSide .high ≤ actualAutomaticCost K ∧
    (∀ D : ℝ, aSide .high < D →
      lam - g ^ 2 * chi * D < actualAutomaticCost K) ∧
    (∀ (n : ℕ) (D : ℝ), n < K → aSide .high < D →
      lam - g ^ 2 * chi ^ n * D < actualAutomaticCost K)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  exact (lt_irrefl (actualAutomaticCost 2)) (h 2 (by decide)).1

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_automatic_cost_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_automatic_cost_envelope, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    change (0 : ℝ) - _ ≠ 1 - _
    intro h
    linarith

def actual_automatic_cost_envelope_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_automatic_cost_envelope)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ K x => x - g ^ 2 * chi ^ K * hSide .high) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal26.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal26.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ K x => x - g ^ 2 * chi ^ K * hSide .high) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_automatic_cost_envelope_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal26

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal25
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Model, Σ _ : ℝ, ℕ
  State := fun _ => Set (List Return)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Set ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ p family => actualFamilyHighGaps p.1 p.2.1 p.2.2 family) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => Set.univ) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K)))
    (family : Set (List Return)) (eps : ℝ) (heps : 0 < eps)
    (hsupply : ∀ execution ∈ family,
      ActualPairSupply model o (b - eps) .closed execution) ,
    ∀ gap ∈ r.readout () ⟨model, b, K⟩ family,
      eps / (g ^ 2 * chi ^ K) ≤ gap


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hlo, hhi⟩ := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.record_interval_nonempty
  have impossible := h .original (fun _ => false) b 2 (by decide) hlo hhi ∅ 1
    (by norm_num) (by simp) (1 / (g ^ 2 * chi ^ 2) - 1) (by trivial)
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_uniform_margin_gap_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_uniform_margin_gap_lower_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨.original, 0, 2⟩, ∅, {([⟨1, 2, by decide, by decide⟩] : List Return)}, ?_⟩
    intro same
    have member : initial .high .original - (lam - 0) / g ^ 2 / chi ^ 2 ∈
        actualFamilyHighGaps .original 0 2 {([⟨1, 2, by decide, by decide⟩] : List Return)} := by
      exact ⟨[], ⟨1, 2, by decide, by decide⟩, [], by simp, rfl, rfl⟩
    change actualFamilyHighGaps .original 0 2 ∅ =
      actualFamilyHighGaps .original 0 2 {([⟨1, 2, by decide, by decide⟩] : List Return)} at same
    rw [← same] at member
    simpa [actualFamilyHighGaps] using member

def actual_uniform_margin_gap_lower_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_uniform_margin_gap_lower_bound)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p family => actualFamilyHighGaps p.1 p.2.1 p.2.2 family) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal25.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal25.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ p family => actualFamilyHighGaps p.1 p.2.1 p.2.2 family) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_uniform_margin_gap_lower_bound_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal25

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal29
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : Model, Σ _ : ℝ, ℕ
  State := fun _ => Set (List Return)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => EReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ p family => actualFamilyDelta p.1 p.2.1 p.2.2 family) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (model : Model) (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K)))
    (family : Set (List Return))
    (hcap : ∀ execution ∈ family, ∀ a ∈ execution, a.r ≤ K) ,
    ActualUniformFamilyMargin model o b family ↔
      0 < r.readout () ⟨model, b, K⟩ family


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨b, hlo, hhi⟩ := Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply.SupplyWitnesses.record_interval_nonempty
  have margin : ActualUniformFamilyMargin .original (fun _ => false) b ∅ :=
    ⟨1, by norm_num, by simp⟩
  have impossible := (h .original (fun _ => false) b 2 (by decide) hlo hhi ∅ (by simp)).mp margin
  exact (lt_irrefl (0 : EReal)) impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_uniform_family_margin_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_uniform_family_margin_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨.original, 0, 2⟩, ∅, {([⟨1, 2, by decide, by decide⟩] : List Return)}, ?_⟩
    change actualFamilyDelta .original 0 2 ∅ ≠
      actualFamilyDelta .original 0 2 {([⟨1, 2, by decide, by decide⟩] : List Return)}
    have empty : actualFamilyDelta .original 0 2 ∅ = ⊤ := by
      simp [actualFamilyDelta, actualFamilyHighGaps]
    have upper : actualFamilyDelta .original 0 2 {([⟨1, 2, by decide, by decide⟩] : List Return)} ≤
        ((initial .high .original - (lam - 0) / g ^ 2 / chi ^ 2 : ℝ) : EReal) := by
      exact sInf_le ⟨_, ⟨[], ⟨1, 2, by decide, by decide⟩, [], by simp, rfl, rfl⟩, rfl⟩
    intro same
    rw [← same, empty] at upper
    exact (not_le_of_gt (EReal.coe_lt_top _)) upper

def actual_uniform_family_margin_iff_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.actual_uniform_family_margin_iff)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p family => actualFamilyDelta p.1 p.2.1 p.2.2 family) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal29.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal29.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ p family => actualFamilyDelta p.1 p.2.1 p.2.2 family) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_uniform_family_margin_iff_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal29


namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal21
noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Bool → List Label)
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize observationSignature (fun _ U L => canonicalReturnLo U L) (fun e => nomatch e)

def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => phi + 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀
    (o : Ownership) (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L)
    (hlegal : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (hdifferent : U false ≠ U true) (hcolors : ∀ i, (U i).length = (W i).length),
    let θ := familyEndpointBudget P Q h U V W L
    0 ≤ θ ∧ (familyEndpointCosts P Q h U V W L).length = 2*h.length+4*L ∧
    EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) Q h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) (V i) (W i)) ∧
    ∃ (e : Guard) (w : List Label), LegalWord s1 e w ∧
      r.readout () U L < coordinate w 0 ∧ coordinate w 0 < canonicalReturnHi U L ∧
      ∀ zs : List Bool,
        OperationRecord o θ .closed (address ((P ++ choiceBlocks U zs) ++ w))
          (recordWithTail o (h ++ choiceBlocks W zs) w) ∧
        OperationFiniteSource (address ((P ++ choiceBlocks U zs) ++ w)) ∧
        ∀ p, recordWithTail o (h ++ choiceBlocks W zs) w
          ((h ++ choiceBlocks W zs).length+p) = observe o (coordinate w p) 0

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let U : Bool → List Label := fun i => if i then [.L2] else [.L0]
  have result := h (fun _ => false) .G0 .G0 [] [] [] rfl rfl rfl
    U (fun _ => [.L0]) (fun _ => [(0 : Color)]) 1 (by decide)
    (by intro i; cases i <;> rfl) (by intro i; rfl)
    (by intro i; cases i <;> rfl) (by intro i; rfl)
    (by decide) (by intro i; cases i <;> rfl)
  obtain ⟨e, w, hw, lower, _⟩ := result.2.2.2.2
  obtain ⟨path, h0, _, support, _⟩ := literal_address_path .G0 e w hw
  have upper := (support 0).2
  rw [h0] at upper
  change coordinate w 0 ≤ phi at upper
  change phi + 1 < coordinate w 0 at lower
  linarith

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.canonical_high_fixed_finite_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.canonical_high_fixed_finite_tail,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence :=
    Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry.ExactOriginal46.evidence.dependence

def canonical_high_fixed_finite_tail_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.canonical_high_fixed_finite_tail)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ U L => canonicalReturnLo U L) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal21.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal21.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ U L => canonicalReturnLo U L) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
    definition := none
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms canonical_high_fixed_finite_tail_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ExactOriginal21
