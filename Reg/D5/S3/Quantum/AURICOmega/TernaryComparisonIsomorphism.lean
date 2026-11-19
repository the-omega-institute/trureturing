import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.DependentFamily
import Mathlib.Topology.Algebra.Star.Unitary

/-! Source-bound audit of the isomorphism between complete rank-five ternary comparison
structures and the unit quaternions.

The rejected law and the observational dependence use the unit quaternion comparison model
lifted to an arbitrary universe. It is noncommutative, chain connected, touches zero and has
feature rank five; its reading is `1 - ‖x - y‖ ^ 2 / 4`, and the unit quaternions are closed in
the complete space of quaternions, so its reading is complete. It therefore satisfies every
hypothesis of the theorem. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
  (liftedModel liftedModel_noncommutative liftedModel_chainConnected liftedModel_touchesZero
    liftedModel_hasFeatureRank_five one_ne_neg_one)

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- The quaternion reading is one minus a quarter of the squared distance in the quaternions. -/
theorem kappa_eq_one_sub_dist_sq (a b : unitary ℍ[ℝ]) :
    quaternionModel.kappa a b = 1 - dist (a : ℍ[ℝ]) (b : ℍ[ℝ]) ^ 2 / 4 := by
  change (1 + ⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ) / 2 = _
  rw [dist_eq_norm, norm_sub_sq_real, CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]
  ring

/-- The reading of the lifted quaternion model is complete. -/
theorem liftedModel_readingComplete : ReadingComplete liftedModel.{u} := by
  intro x hx
  have hcauchy : CauchySeq fun n => ((x n).down : ℍ[ℝ]) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hx (ε ^ 2 / 4) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h : 1 - ε ^ 2 / 4 < quaternionModel.kappa (x m).down (x n).down := hN m n hm hn
    rw [kappa_eq_one_sub_dist_sq] at h
    have h' : dist ((x m).down : ℍ[ℝ]) ((x n).down : ℍ[ℝ]) ^ 2 < ε ^ 2 := by linarith
    exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).mp h'
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hLmem : L ∈ unitary ℍ[ℝ] :=
    isClosed_unitary.mem_of_tendsto hL (Filter.Eventually.of_forall fun n => (x n).down.2)
  refine ⟨⟨⟨L, hLmem⟩⟩, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL (min 1 ε) (lt_min one_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hd := hN n hn
  change 1 - ε < quaternionModel.kappa (x n).down ⟨L, hLmem⟩
  rw [kappa_eq_one_sub_dist_sq]
  change 1 - ε < 1 - dist ((x n).down : ℍ[ℝ]) L ^ 2 / 4
  have h0 := dist_nonneg (x := ((x n).down : ℍ[ℝ])) (y := L)
  have h1 := hd.trans_le (min_le_left 1 ε)
  have h2 := hd.trans_le (min_le_right 1 ε)
  nlinarith

/-! The transfer inside `u (C.tri x y z)` of `exists_unitQuaternion_equiv`, against its first two
arguments. -/
namespace Transfer

abbrev signature : Signature where
  Params := Σ M : Type u, Σ _ : TernaryComparison M, Σ _ : M, M
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.2.1.tri p.2.2.1 p.2.2.2 s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- Retain the complete carrier, structure, hypothesis and base-point telescope and all three
conjuncts of `exists_unitQuaternion_equiv`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law rd := ∀ {M : Type u} (C : TernaryComparison M), C.Noncommutative → C.ChainConnected →
    C.TouchesZero → C.HasFeatureRank 5 → ReadingComplete C → ∀ o : M,
    ∃ u : M ≃ unitary ℍ[ℝ], u o = 1 ∧
      (∀ x y z : M, u (rd.readout () ⟨M, C, x, y⟩ z) = quaternionModel.tri (u x) (u y) (u z)) ∧
      (∀ x y : M, C.kappa x y = quaternionModel.kappa (u x) (u y))

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨w, -, htri, -⟩ := h liftedModel.{u} liftedModel_noncommutative
    liftedModel_chainConnected liftedModel_touchesZero liftedModel_hasFeatureRank_five
    liftedModel_readingComplete ⟨1⟩
  have hh : w ⟨1⟩ = w ⟨1⟩ * (w ⟨-1⟩)⁻¹ * w ⟨1⟩ := htri ⟨1⟩ ⟨-1⟩ ⟨1⟩
  rw [mul_assoc] at hh
  have h1 : (w ⟨-1⟩)⁻¹ * w ⟨1⟩ = 1 := by
    have h2 := congrArg (fun a => (w ⟨1⟩)⁻¹ * a) hh
    simpa only [inv_mul_cancel_left, inv_mul_cancel] using h2.symm
  have h3 : w ⟨-1⟩ = w ⟨1⟩ := inv_mul_eq_one.mp h1
  exact one_ne_neg_one (congrArg ULift.down (w.injective h3)).symm

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} (unitary ℍ[ℝ]), liftedModel, ⟨1⟩, ⟨1⟩⟩, ⟨1⟩, ⟨-1⟩, ?_⟩
  change liftedModel.tri ⟨1⟩ ⟨1⟩ ⟨1⟩ ≠ liftedModel.tri ⟨1⟩ ⟨1⟩ ⟨-1⟩
  rw [liftedModel.tri_self_left, liftedModel.tri_self_left]
  exact fun e => one_ne_neg_one (congrArg ULift.down e)

def source_registration :
    Registration arena.{u} (type_of% @exists_unitQuaternion_equiv.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_unitQuaternion_equiv.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Transfer

def exists_unitQuaternion_equiv_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_unitQuaternion_equiv.{u}) (Realization Transfer.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism.exists_unitQuaternion_equiv_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism.Transfer.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Transfer.arena.{u}⟩
  objectArena := .source ⟨Transfer.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Transfer.arena.{u} ⟨Transfer.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Transfer.signature.{u} (fun _ p s => p.2.1.tri p.2.2.1 p.2.2.2 s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
    definition := none
    coordinates := #[0, 1, 9, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "fn", "arg", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
