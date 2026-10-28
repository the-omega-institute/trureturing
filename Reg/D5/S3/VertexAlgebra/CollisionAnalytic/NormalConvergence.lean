import D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound attempts retain the complete original telescopes and infinite
coefficient families. Source-selection serialization and current binding
certificates are separate obligations; no validated audit status is asserted. -/

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
    (by intro z hz'; simpa only [Set.mem_singleton_iff.mp hz'] using hz)
  have hc : Summable (fun _ : Fin 1 → ℤ => (1 : ℝ)) :=
    hu.of_nonneg_of_le (fun _ => by norm_num) (fun e => by
      simpa [majorantBad, realize] using hb e (fun _ => 1) (Set.mem_singleton _))
  exact Set.infinite_univ (Set.Finite.of_summable_const (by norm_num : (0 : ℝ) < 1) hc)

private theorem majorant_dependence : ObservationalDependence majorantSignature majorantActual := by
  intro i
  refine ⟨⟨0, Equiv.refl _⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have h0 := congrFun (congrFun h 0) (fun i => Fin.elim0 i)
  simpa [majorantActual, realize, monomial] using h0

def majorantFamily : Registration majorantArena majorantSource where
  actual := majorantActual
  bridge := Iff.rfl
  variation := ⟨majorant_positive, majorantBad, majorant_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨majorantBad, ?_, rfl, majorant_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := majorant_dependence

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
    (algebraMap _ (CommonRational ℂ p.n) L /
      algebraMap _ (CommonRational ℂ p.n)
        (∏ q ∈ labelledPairs p.n, pairPolynomial q.1 q.2 ^ p.orders q))).coeff
          (orderExponents p.n p.sigma e) * monomial z e) (fun e => nomatch e)

-- Full source telescope, without replacing the genuine coefficients or numerator.
example : normalSource := @collision_normal_evaluation

/-- The enrolled readout used by the source-bound attempt. The source-selection
certificate is deliberately not supplied by this definition. -/
def normalReadout := realize normalSignature normalActual.readout normalActual.anchor

#print axioms majorantFamily
#print axioms normalActual
end Reg.D5.S3.VertexAlgebra.CollisionAnalytic.NormalConvergence
