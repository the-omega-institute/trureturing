import D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound attempts retain the complete original telescopes and infinite
coefficient families. Source-selection serialization and current binding
certificates remain unresolved under https://github.com/the-omega-institute/trureturing/issues/23169;
no validated audit status is asserted. -/

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open CollisionAbsoluteEvaluation.Labelled CollisionNormalConvergence
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.FiniteConvolution UniformGradedLocalCorrelator
open LeanInformationAudit
open scoped Topology BigOperators

abbrev majorantSource := type_of% (@chamber_compact_summable_majorant)
abbrev normalSource := type_of% (@collision_normal_evaluation)

structure Parameters where
  n : ℕ
  sigma : Equiv.Perm (Fin n)

def majorantSignature : Signature where
  Params := Parameters
  State p := (Fin p.n → ℤ) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p.n → ℤ) → (Fin p.n → ℂ) → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def majorantActual : Realization majorantSignature :=
  realize _ (fun _ _ c e z => c e * monomial z e) (fun e => nomatch e)

def majorantArena : Arena where
  signature := majorantSignature
  Law R := ∀ (n : ℕ) (sigma : Equiv.Perm (Fin n)) (c : (Fin n → ℤ) → ℂ),
    (∀ z, RadialChamber sigma z → Summable (fun e => ‖c e * monomial z e‖)) →
    ∀ (K : Set (Fin n → ℂ)), IsCompact K →
      K ⊆ {z | RadialChamber sigma z} →
      ∃ u : (Fin n → ℤ) → ℝ, (∀ e, 0 ≤ u e) ∧ Summable u ∧
        ∀ e z, z ∈ K → ‖R.readout () ⟨n, sigma⟩ c e z‖ ≤ u e

private theorem majorant_positive : majorantArena.Law majorantActual :=
  @chamber_compact_summable_majorant

private def majorantBad : Realization majorantSignature :=
  realize _ (fun _ _ _ _ _ => 1) (fun e => nomatch e)

private theorem majorant_bad : ¬ majorantArena.Law majorantBad := by
  intro h
  have hz : RadialChamber (Equiv.refl (Fin 1)) (fun _ => (1 : ℂ)) := by
    refine ⟨fun _ => one_ne_zero, ?_⟩
    intro i j hij
    have : i = j := Subsingleton.elim _ _
    exact (hij.ne this).elim
  obtain ⟨u, _, hu, hb⟩ := h 1 (Equiv.refl _) (fun _ => 0)
    (by intro z _; simp) {fun _ => (1 : ℂ)} (isCompact_singleton)
    (by intro z hz'; rcases Set.mem_singleton_iff.mp hz' with rfl; exact hz)
  have hc : Summable (fun _ : Fin 1 → ℤ => (1 : ℝ)) :=
    hu.of_nonneg_of_le (fun _ => by norm_num) (fun e => by
      simpa [majorantBad, realize] using hb e (fun _ => 1) (Set.mem_singleton _))
  exact Set.infinite_univ (Set.Finite.of_summable_const (by norm_num : (0 : ℝ) < 1) hc)

private theorem majorant_dependence : ObservationalDependence majorantSignature majorantActual := by
  intro i
  refine ⟨⟨0, Equiv.refl _⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have h0 := congrFun (congrFun h 0) (fun i => Fin.elim0 i)
  simp [majorantActual, realize, monomial] at h0

def majorantFamily : Registration majorantArena majorantSource where
  actual := majorantActual
  bridge := Iff.rfl
  variation := ⟨majorant_positive, majorantBad, majorant_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨majorantBad, ?_, rfl, majorant_bad⟩
      intro j hj
      exact (hj (by cases i; cases j; rfl)).elim
    · intro i; exact nomatch i
  dependence := majorant_dependence

def majorantAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chamber_compact_summable_majorant) (Realization majorantSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence.majorantUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence.majorantFamily
  realizationSource := none
  generated := false
  arena := .source ⟨majorantArena⟩
  objectArena := .source ⟨majorantArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source majorantArena ⟨majorantFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize majorantSignature majorantActual.readout majorantActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

structure CollisionParameters extends Parameters where
  orders : (Fin n × Fin n) → ℕ

def normalSignature : Signature where
  Params := CollisionParameters
  State p := LabelledPolynomial ℂ p.n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p.n → ℤ) → (Fin p.n → ℂ) → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def normalActual : Realization normalSignature :=
  realize _ (fun _ p L e z => (orderedRationalFor ℂ p.n p.sigma
    (algebraMap (LabelledPolynomial ℂ p.n) (CommonRational ℂ p.n) L /
      algebraMap (LabelledPolynomial ℂ p.n) (CommonRational ℂ p.n)
        (∏ q ∈ labelledPairs p.n, pairPolynomial q.1 q.2 ^ p.orders q))).coeff
          (orderExponents p.n p.sigma e) * monomial z e) (fun e => nomatch e)

-- Full source telescope, without replacing the genuine coefficients or numerator.
example : normalSource := @collision_normal_evaluation

def normalArena : Arena where
  signature := normalSignature
  Law R := ∀ (n : ℕ) (sigma : Equiv.Perm (Fin n)) (L : LabelledPolynomial ℂ n)
    (m : (Fin n × Fin n) → ℕ) (K : TopologicalSpace.Compacts (Fin n → ℂ)),
    (K : Set (Fin n → ℂ)) ⊆ {z | RadialChamber sigma z} →
    let value := fun z : Fin n → ℂ =>
      laurentValue L z / ∏ p ∈ labelledPairs n, (z p.1 - z p.2) ^ m p
    ∃ (T : (Fin n → ℤ) → C(K, ℂ)) (F : C(K, ℂ)),
      (∀ e (z : K), T e z = R.readout () ⟨⟨n, sigma⟩, m⟩ L e z) ∧
      (∀ z : K, F z = value z) ∧ Summable (fun e : Fin n → ℤ => ‖T e‖) ∧
      HasSum T F ∧ HasSumUniformlyOn (R.readout () ⟨⟨n, sigma⟩, m⟩ L) value K

private theorem normal_positive : normalArena.Law normalActual := @collision_normal_evaluation

private def normalBad : Realization normalSignature :=
  realize _ (fun _ _ _ _ _ => 1) (fun e => nomatch e)

private theorem normal_bad : ¬ normalArena.Law normalBad := by
  intro h
  let z : Fin 1 → ℂ := fun _ => 1
  have hz : RadialChamber (Equiv.refl (Fin 1)) z := by
    refine ⟨fun _ => one_ne_zero, ?_⟩
    intro i j hij
    exact (hij.ne (Subsingleton.elim _ _)).elim
  let K : TopologicalSpace.Compacts (Fin 1 → ℂ) := ⟨{z}, isCompact_singleton⟩
  obtain ⟨T, F, hT, _, hnorm, _⟩ := h 1 (Equiv.refl _) 0 (fun _ => 0) K
    (by intro w hw; rcases Set.mem_singleton_iff.mp hw with rfl; exact hz)
  have hc : Summable (fun _ : Fin 1 → ℤ => (1 : ℝ)) :=
    hnorm.of_nonneg_of_le (fun _ => by norm_num) (fun e => by
      have hb := (T e).norm_coe_le_norm (⟨z, Set.mem_singleton _⟩ : K)
      simpa only [hT, normalBad, realize, Realization.readout, norm_one] using hb)
  exact Set.infinite_univ (Set.Finite.of_summable_const (by norm_num : (0 : ℝ) < 1) hc)

private theorem normal_dependence : ObservationalDependence normalSignature normalActual := by
  intro i
  refine ⟨⟨⟨0, Equiv.refl _⟩, fun _ => 0⟩, (0 : LabelledPolynomial ℂ 0),
    (1 : LabelledPolynomial ℂ 0), ?_⟩
  intro h
  have h0 := congrFun (congrFun h 0) (fun i => Fin.elim0 i)
  simp [normalActual, realize, monomial, labelledPairs] at h0

def normalFamily : Registration normalArena normalSource where
  actual := normalActual
  bridge := Iff.rfl
  variation := ⟨normal_positive, normalBad, normal_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨normalBad, ?_, rfl, normal_bad⟩
      intro j hj
      exact (hj (by cases i; cases j; rfl)).elim
    · intro i; exact nomatch i
  dependence := normal_dependence

def normalAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@collision_normal_evaluation) (Realization normalSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence.normalUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence.normalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨normalArena⟩
  objectArena := .source ⟨normalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normalArena ⟨normalFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normalSignature normalActual.readout normalActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms majorantFamily
#print axioms normalFamily
end Reg.D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence
