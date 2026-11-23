import D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open scoped BigOperators

/-! Source-bound cardinality observations for recursive two-trees. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation

open SimpleGraph

local instance : DecidableRel (twoTree 0).Adj := Top.adjDecidable (Fin 3)
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

abbrev countSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def vertexCount : Realization countSignature :=
  realize countSignature (fun _ _ d => Fintype.card (TwoTreeV d)) (fun e => nomatch e)

def edgeCount : Realization countSignature :=
  realize countSignature (fun _ _ d => Nat.card (twoTree d).edgeSet) (fun e => nomatch e)

def zeroCount : Realization countSignature :=
  realize countSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev vertexArena : Arena where
  signature := countSignature
  Law R := ∀ d : ℕ, (twoTree d).IsChordal ∧ (twoTree d).Connected ∧
    R.readout () () d = 3 * 2 ^ d

abbrev edgeArena : Arena where
  signature := countSignature
  Law R := ∀ d : ℕ, R.readout () () d = 3 * (2 ^ (d + 1) - 1)

private theorem no_vertex_zero : ¬ vertexArena.Law zeroCount := by
  intro h
  have h0 := (h 0).2.2
  change (0 : ℕ) = 3 at h0
  omega

private theorem no_edge_zero : ¬ edgeArena.Law zeroCount := by
  intro h
  have h0 := h 0
  change (0 : ℕ) = 3 at h0
  omega

def vertexEvidence : Registration vertexArena (type_of% twoTree_isChordal) where
  actual := vertexCount
  bridge := Iff.rfl
  variation := ⟨twoTree_isChordal, zeroCount, no_vertex_zero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroCount, ?_, rfl, no_vertex_zero⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun e => nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Fintype.card (TwoTreeV 0) ≠ Fintype.card (TwoTreeV 1)
    rw [(twoTree_isChordal 0).2.2, (twoTree_isChordal 1).2.2]
    decide

def edgeEvidence : Registration edgeArena (type_of% twoTree_edge_count) where
  actual := edgeCount
  bridge := Iff.rfl
  variation := ⟨twoTree_edge_count, zeroCount, no_edge_zero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroCount, ?_, rfl, no_edge_zero⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun e => nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Nat.card (twoTree 0).edgeSet ≠ Nat.card (twoTree 1).edgeSet
    rw [twoTree_edge_count, twoTree_edge_count]
    decide


def vertexRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@SimpleGraph.twoTree_isChordal) (Realization countSignature) Unit Unit where
  unitName := `SimpleGraph.twoTree_isChordal.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation.vertexEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨vertexArena⟩
  objectArena := .source ⟨vertexArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source vertexArena ⟨vertexEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ d => Fintype.card (TwoTreeV d)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def edgeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@SimpleGraph.twoTree_edge_count) (Realization countSignature) Unit Unit where
  unitName := `SimpleGraph.twoTree_edge_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation.edgeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨edgeArena⟩
  objectArena := .source ⟨edgeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source edgeArena ⟨edgeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ d => Nat.card (twoTree d).edgeSet) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


open scoped ENNReal

abbrev stretchParams := Σ d : ℕ, SimpleGraph (TwoTreeV d) × TwoTreeV d

abbrev stretchSignature : Signature where
  Params := stretchParams
  State p := TwoTreeV p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ∞
  Anchor := Empty
  finiteAnchor := inferInstance

def stretchActual : Realization stretchSignature :=
  realize stretchSignature (fun _ p v => p.2.1.edist p.2.2 v) (fun e => nomatch e)

def stretchZero : Realization stretchSignature :=
  realize stretchSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev stretchArena : Arena where
  signature := stretchSignature
  Law R := ∀ d : ℕ,
    (∀ T ≤ twoTree d, T.IsTree → ∃ u v, (twoTree d).Adj u v ∧
      (d + 2 : ℕ) ≤ R.readout () ⟨d, T, u⟩ v) ∧
    (∃ T ≤ twoTree d, T.IsTree ∧
      ∀ u v, (twoTree d).Adj u v → T.edist u v ≤ (d + 2 : ℕ))

private theorem no_stretch_zero : ¬ stretchArena.Law stretchZero := by
  intro h
  obtain ⟨T, hTG, hT, _⟩ := (twoTree_min_spanning_tree_stretch_eq 0).2
  obtain ⟨u, v, _, hm⟩ := (h 0).1 T hTG hT
  change (2 : ℕ∞) ≤ 0 at hm
  exact (by decide : ¬ (2 : ℕ∞) ≤ 0) hm

def stretchEvidence : Registration stretchArena (type_of% twoTree_min_spanning_tree_stretch_eq) where
  actual := stretchActual
  bridge := Iff.rfl
  variation := ⟨twoTree_min_spanning_tree_stretch_eq, stretchZero, no_stretch_zero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨stretchZero, ?_, rfl, no_stretch_zero⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun e => nomatch e
  dependence := by
    intro i
    refine ⟨⟨0, ⊤, 0⟩, 0, 1, ?_⟩
    change (⊤ : SimpleGraph (Fin 3)).edist 0 0 ≠ (⊤ : SimpleGraph (Fin 3)).edist 0 1
    rw [edist_self, edist_top_of_ne (by decide : (0 : Fin 3) ≠ 1)]
    decide

abbrev integralParams := Σ d : ℕ, (TwoTreeV d → TwoTreeV d → ℤ) × (TwoTreeV d → ℤ) × TwoTreeV d

abbrev integralSignature : Signature where
  Params := integralParams
  State p := TwoTreeV p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def integralActual : Realization integralSignature :=
  realize integralSignature
    (fun _ p v => p.2.1 p.2.2.2 v - (p.2.2.1 v - p.2.2.1 p.2.2.2)) (fun e => nomatch e)

def integralZero : Realization integralSignature :=
  realize integralSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev integralArena : Arena where
  signature := integralSignature
  Law R := ∀ d : ℕ, ∃ g : TwoTreeV d → TwoTreeV d → ℤ,
    (∀ u v, (twoTree d).Adj u v → g v u = -g u v) ∧
    (∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
      ‖g u v + g v w - g u w‖ ≤ 1) ∧
    (∀ φ : TwoTreeV d → ℤ, ∃ u v, (twoTree d).Adj u v ∧
      1 ≤ ‖R.readout () ⟨d, g, φ, u⟩ v‖)

private theorem no_integral_zero : ¬ integralArena.Law integralZero := by
  intro h
  obtain ⟨g, _, _, hg⟩ := h 0
  obtain ⟨u, v, _, hu⟩ := hg (fun _ => 0)
  change (1 : ℝ) ≤ ‖(0 : ℤ)‖ at hu
  norm_num at hu

def integralEvidence : Registration integralArena (type_of% twoTree_integer_lower_bound_one) where
  actual := integralActual
  bridge := Iff.rfl
  variation := ⟨twoTree_integer_lower_bound_one, integralZero, no_integral_zero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨integralZero, ?_, rfl, no_integral_zero⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun e => nomatch e
  dependence := by
    intro i
    let g (_ : TwoTreeV 0) (v : TwoTreeV 0) : ℤ := if (v : Fin 3) = 0 then 0 else 1
    refine ⟨⟨0, g, fun _ => 0, 0⟩, 0, 1, ?_⟩
    change (0 : ℤ) ≠ 1
    decide


def stretchRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@SimpleGraph.twoTree_min_spanning_tree_stretch_eq) (Realization stretchSignature) Unit Unit where
  unitName := `SimpleGraph.twoTree_min_spanning_tree_stretch_eq.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation.stretchEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨stretchArena⟩
  objectArena := .source ⟨stretchArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stretchArena ⟨stretchEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stretchSignature (fun _ p v => p.2.1.edist p.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def integralRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@SimpleGraph.twoTree_integer_lower_bound_one) (Realization integralSignature) Unit Unit where
  unitName := `SimpleGraph.twoTree_integer_lower_bound_one.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation.integralEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨integralArena⟩
  objectArena := .source ⟨integralArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source integralArena ⟨integralEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize integralSignature (fun _ p v => p.2.1 p.2.2.2 v - (p.2.2.1 v - p.2.2.1 p.2.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

universe u

abbrev banachSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def banachActual : Realization banachSignature :=
  realize banachSignature (fun _ _ d => twoTreeBanachConstant d) (fun e => nomatch e)

def banachTwo : Realization banachSignature :=
  realize banachSignature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev banachArena : Arena where
  signature := banachSignature
  Law R := ∀ d : ℕ,
    (∀ u v, (twoTree d).Adj u v → twoTreeCanonicalGain d v u = -twoTreeCanonicalGain d u v) ∧
    (∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
      ‖twoTreeCanonicalGain d u v + twoTreeCanonicalGain d v w - twoTreeCanonicalGain d u w‖ ≤ 1) ∧
    (∀ φ : TwoTreeV d → TwoTreeCycles d, ∃ u v, (twoTree d).Adj u v ∧
      R.readout () () d ≤ ‖twoTreeCanonicalGain d u v - (φ v - φ u)‖) ∧
    (∀ {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
      (g : TwoTreeV d → TwoTreeV d → E) (ε : ℝ), 0 ≤ ε →
      (∀ u v, (twoTree d).Adj u v → g v u = -g u v) →
      (∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
        ‖g u v + g v w - g u w‖ ≤ ε) →
      ∃ φ : TwoTreeV d → E, ∀ u v, (twoTree d).Adj u v →
        ‖g u v - (φ v - φ u)‖ ≤ twoTreeBanachConstant d * ε) ∧
    (∀ z : TwoTreeCirculation ℝ d,
      (∑ e, z.val e • twoTreeCanonicalCirculationGain d (twoTreeEdgeSource d e)
        (twoTreeEdgeTarget d e)) = z) ∧
    (∀ φ : TwoTreeV d → TwoTreeCirculation ℝ d, ∃ u v, (twoTree d).Adj u v ∧
      twoTreeBanachConstant d ≤
        twoTreeFillingNorm d (twoTreeCanonicalCirculationGain d u v - (φ v - φ u))) ∧
    (∃ φ : TwoTreeV d → TwoTreeCirculation ℝ d, ∀ u v, (twoTree d).Adj u v →
      twoTreeFillingNorm d (twoTreeCanonicalCirculationGain d u v - (φ v - φ u)) ≤
        twoTreeBanachConstant d) ∧
    (∀ i : TwoTreeTriangles d, twoTreeTriangleSum d (twoTreeCanonicalGain d) i = PiLp.single 1 i 1)

private theorem no_banach_two : ¬ banachArena.{u}.Law banachTwo := by
  intro h
  have h0 := twoTree_banach_exact_constant.{0} 0
  obtain ⟨φ, hφ⟩ := h0.2.2.2.1 (twoTreeCanonicalGain 0) 1 (by norm_num) h0.1 h0.2.1
  obtain ⟨a, b, hab, hr⟩ := (h 0).2.2.1 φ
  have hu := hφ a b hab
  change (2 : ℝ) ≤ _ at hr
  norm_num [twoTreeBanachConstant] at hu
  linarith

def banachEvidence : Registration banachArena.{u} (type_of% twoTree_banach_exact_constant.{u}) where
  actual := banachActual
  bridge := Iff.rfl
  variation := ⟨twoTree_banach_exact_constant.{u}, banachTwo, no_banach_two⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨banachTwo, ?_, rfl, no_banach_two⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun e => nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change twoTreeBanachConstant 0 ≠ twoTreeBanachConstant 1
    norm_num [twoTreeBanachConstant]

def banachRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@SimpleGraph.twoTree_banach_exact_constant.{u}) (Realization banachSignature) Unit Unit where
  unitName := `SimpleGraph.twoTree_banach_exact_constant.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation.banachEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨banachArena.{u}⟩
  objectArena := .source ⟨banachArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source banachArena.{u} ⟨banachEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize banachSignature (fun _ _ d => twoTreeBanachConstant d)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "fn", "arg", "body", "arg", "body", "arg", "body",
        "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev gainParams := Σ d : ℕ, Σ H : Type u, Σ _ : Group H, (TwoTreeV d → H) × TwoTreeV d

abbrev gainSignature : Signature where
  Params := gainParams.{u}
  State p := TwoTreeV p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def gainReader (p : gainParams.{u}) (v : TwoTreeV p.1) : p.2.1 := by
  rcases p with ⟨d, H, inst, φ, a⟩
  letI : Group H := inst
  exact (φ a)⁻¹ * φ v

def gainActual : Realization gainSignature.{u} :=
  realize gainSignature (fun _ p v => gainReader p v) (fun e => nomatch e)

def gainOne : Realization gainSignature.{u} :=
  realize gainSignature (fun _ p _ => by letI := p.2.2.1; exact 1) (fun e => nomatch e)

abbrev gainArena : Arena where
  signature := gainSignature.{u}
  Law R := ∀ (d : ℕ) {H : Type u} [h : Group H] [PseudoMetricSpace H]
    [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] (g : TwoTreeV d → TwoTreeV d → H) (ε : ℝ),
    0 ≤ ε →
    (∀ u v, (twoTree d).Adj u v → g v u = (g u v)⁻¹) →
    (∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
      dist (g u v * g v w) (g u w) ≤ ε) →
    ∃ φ : TwoTreeV d → H, ∀ a b, (twoTree d).Adj a b →
      dist (g a b) (R.readout () ⟨d, H, h, φ, a⟩ b) ≤ ε

@[instance_reducible] private def discreteMetric (X : Type*) [DecidableEq X] : MetricSpace X where
  dist a b := if a = b then 0 else 1
  dist_self a := ite_eq_left rfl
  dist_comm a b := by split_ifs <;> simp_all
  dist_triangle a b c := by split_ifs <;> simp_all
  eq_of_dist_eq_zero := by intro a b h; split_ifs at h <;> simp_all

private def swap : Equiv.Perm (ULift.{u} (Fin 2)) :=
  Equiv.swap ⟨0⟩ ⟨1⟩

private theorem swap_ne_one : swap.{u} ≠ 1 := by
  intro h
  have h' := congrArg (fun s : Equiv.Perm (ULift.{u} (Fin 2)) => (s ⟨0⟩).down) h
  simpa [swap] using h'

private theorem gauge_reverse {K : Type*} [Group K] (a b : K) :
    b⁻¹ * a = (a⁻¹ * b)⁻¹ := by
  rw [mul_inv_rev, inv_inv]

private theorem gauge_triangle {K : Type*} [Group K] (a b c : K) :
    (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c := by
  rw [mul_assoc, mul_inv_cancel_left]

private theorem no_gain_one : ¬ gainArena.{u}.Law gainOne.{u} := by
  classical
  intro h
  let H := Equiv.Perm (ULift.{u} (Fin 2))
  let : MetricSpace H := discreteMetric H
  let : IsIsometricSMul H H := ⟨fun c => Isometry.of_dist_eq (fun a b => by
    change (if c * a = c * b then (0 : ℝ) else 1) = (if a = b then 0 else 1)
    simp only [mul_left_cancel_iff])⟩
  let : IsIsometricSMul Hᵐᵒᵖ H := ⟨fun c => Isometry.of_dist_eq (fun a b => by
    change (if a * c.unop = b * c.unop then (0 : ℝ) else 1) = (if a = b then 0 else 1)
    simp only [mul_right_cancel_iff])⟩
  let θ (a : TwoTreeV 0) : H := if (a : Fin 3) = 0 then 1 else swap
  let g : TwoTreeV 0 → TwoTreeV 0 → H := fun a b => (θ a)⁻¹ * θ b
  obtain ⟨φ, hφ⟩ := h 0 g 0 le_rfl
    (fun a b _ => gauge_reverse (θ a) (θ b))
    (by
      intro a b c _ _ _
      change Dist.dist (((θ a)⁻¹ * θ b) * ((θ b)⁻¹ * θ c)) ((θ a)⁻¹ * θ c) ≤ 0
      rw [gauge_triangle, _root_.dist_self])
  have hv := hφ 0 1 (by decide)
  change dist (g 0 1) (1 : H) ≤ 0 at hv
  have he := dist_le_zero.mp hv
  exact swap_ne_one (by simpa [g, θ] using he)

def gainEvidence : Registration gainArena.{u}
    (type_of% twoTree_exists_one_approximate_gain_potential.{u}) where
  actual := gainActual
  bridge := Iff.rfl
  variation := ⟨twoTree_exists_one_approximate_gain_potential.{u}, gainOne, no_gain_one⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨gainOne, ?_, rfl, no_gain_one⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun e => nomatch e
  dependence := by
    intro i
    let H := Equiv.Perm (ULift.{u} (Fin 2))
    let θ (a : TwoTreeV 0) : H := if (a : Fin 3) = 0 then 1 else swap
    refine ⟨⟨0, H, inferInstance, θ, 0⟩, 1, 0, ?_⟩
    change (θ 0)⁻¹ * θ 1 ≠ (θ 0)⁻¹ * θ 0
    simpa [θ] using swap_ne_one.{u}

def gainRegistration : Contract.Registration.{_, _, _, 0, 0, 0, u+1, 0, 0, u, 0, 0}
    (@SimpleGraph.twoTree_exists_one_approximate_gain_potential.{u})
    (Realization gainSignature.{u}) Unit Unit where
  unitName := `SimpleGraph.twoTree_exists_one_approximate_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation.gainEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gainArena.{u}⟩
  objectArena := .source ⟨gainArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gainArena.{u} ⟨gainEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gainSignature.{u} (fun _ p v => gainReader p v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation
    definition := none
    coordinates := #[0, 1, 2, 11, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeStretchSeparation
