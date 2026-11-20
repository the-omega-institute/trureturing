import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.DependentFamily
import Mathlib.Topology.Algebra.Star.Unitary

/-! Source-bound audits of the isomorphism between complete rank-five ternary comparison
structures and the unit quaternions, of the normalized embedding, of the closedness of the image
of a reading-preserving map and of the distance form of the quaternion reading.

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

/-- The reading of the lifted quaternion model is complete. -/
theorem liftedModel_readingComplete : ReadingComplete liftedModel.{u} := by
  intro x hx
  have hcauchy : CauchySeq fun n => ((x n).down : ℍ[ℝ]) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hx (ε ^ 2 / 4) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h : 1 - ε ^ 2 / 4 < quaternionModel.kappa (x m).down (x n).down := hN m n hm hn
    rw [kappa_eq_one_sub_dist_sq, Subtype.dist_eq] at h
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

/-! The transfer inside `v (C.tri x y z)` of `exists_normalized_embedding`, against its first two
arguments. The signature, readouts and dependence are those of `Transfer`. -/
namespace NormalizedTransfer

/-- Retain the complete carrier, structure, hypothesis and base-point telescope and all four
conjuncts of `exists_normalized_embedding`. -/
abbrev arena : Arena where
  signature := Transfer.signature.{u}
  Law rd := ∀ {M : Type u} (C : TernaryComparison M), C.Noncommutative → C.ChainConnected →
    C.TouchesZero → C.HasFeatureRank 5 → ∀ o : M,
    ∃ v : M → unitary ℍ[ℝ], Function.Injective v ∧ v o = 1 ∧
      (∀ x y z : M, v (rd.readout () ⟨M, C, x, y⟩ z) = v x * (v y)⁻¹ * v z) ∧
      (∀ x y : M, C.kappa x y = quaternionModel.kappa (v x) (v y))

theorem rejected_law : ¬ arena.{u}.Law Transfer.rejected := by
  intro h
  obtain ⟨w, hinj, -, htri, -⟩ := h liftedModel.{u} liftedModel_noncommutative
    liftedModel_chainConnected liftedModel_touchesZero liftedModel_hasFeatureRank_five ⟨1⟩
  have hh : w ⟨1⟩ = w ⟨1⟩ * (w ⟨-1⟩)⁻¹ * w ⟨1⟩ := htri ⟨1⟩ ⟨-1⟩ ⟨1⟩
  rw [mul_assoc] at hh
  have h1 : (w ⟨-1⟩)⁻¹ * w ⟨1⟩ = 1 := by
    have h2 := congrArg (fun a => (w ⟨1⟩)⁻¹ * a) hh
    simpa only [inv_mul_cancel_left, inv_mul_cancel] using h2.symm
  have h3 : w ⟨-1⟩ = w ⟨1⟩ := inv_mul_eq_one.mp h1
  exact one_ne_neg_one (congrArg ULift.down (hinj h3)).symm

def source_registration :
    Registration arena.{u} (type_of% @exists_normalized_embedding.{u}) where
  actual := Transfer.actual
  bridge := Iff.rfl
  variation := ⟨@exists_normalized_embedding.{u}, Transfer.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨Transfer.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := Transfer.dependence

end NormalizedTransfer

/-! The image `Set.range v` in `isClosed_range`, as a function of the map `v`. -/
namespace Image

abbrev signature : Signature where
  Params := Type u
  State M := M → unitary ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set (unitary ℍ[ℝ])
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => Set.range s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ({1}ᶜ : Set (unitary ℍ[ℝ]))) (fun e => nomatch e)

/-- Retain the complete carrier, structure, map and hypothesis telescope of `isClosed_range`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law rd := ∀ {M : Type u} (C : TernaryComparison M) (v : M → unitary ℍ[ℝ]),
    (∀ x y : M, C.kappa x y = quaternionModel.kappa (v x) (v y)) → ReadingComplete C →
      IsClosed (rd.readout () M v)

/-- The unit quaternions other than one do not form a closed set: the complement of a point is
open, and the unit three-sphere is connected. -/
theorem not_isClosed_compl_one : ¬ IsClosed ({1}ᶜ : Set (unitary ℍ[ℝ])) := by
  intro hc
  have : PreconnectedSpace (unitary ℍ[ℝ]) := Subtype.preconnectedSpace (by
    rw [coe_unitary_eq_sphere]
    exact isPreconnected_sphere (by rw [Quaternion.rank_eq_four]; norm_num) 0 1)
  rcases isClopen_iff.mp ⟨hc, isOpen_compl_singleton⟩ with h | h
  · have hm : (-1 : unitary ℍ[ℝ]) ∈ ({1}ᶜ : Set (unitary ℍ[ℝ])) :=
      fun e => one_ne_neg_one (Set.mem_singleton_iff.mp e).symm
    rw [h] at hm
    exact hm
  · have hm : (1 : unitary ℍ[ℝ]) ∈ ({1}ᶜ : Set (unitary ℍ[ℝ])) := by
      rw [h]
      trivial
    exact hm rfl

theorem rejected_law : ¬ arena.{u}.Law rejected :=
  fun h => not_isClosed_compl_one
    (h liftedModel.{u} ULift.down (fun _ _ => rfl) liftedModel_readingComplete)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨PUnit.{u + 1}, fun _ => 1, fun _ => -1, fun h => ?_⟩
  have hm : (1 : unitary ℍ[ℝ]) ∈ Set.range fun _ : PUnit.{u + 1} => (1 : unitary ℍ[ℝ]) :=
    ⟨PUnit.unit, rfl⟩
  rw [show (Set.range fun _ : PUnit.{u + 1} => (1 : unitary ℍ[ℝ])) =
    Set.range fun _ : PUnit.{u + 1} => (-1 : unitary ℍ[ℝ]) from h] at hm
  obtain ⟨_, hx⟩ := hm
  exact one_ne_neg_one hx.symm

def source_registration :
    Registration arena.{u} (type_of% @isClosed_range.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isClosed_range.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Image

/-! The reading against a fixed first argument, for `kappa_eq_one_sub_dist_sq`. -/
namespace Reading

abbrev signature : Signature where
  Params := unitary ℍ[ℝ]
  State _ := unitary ℍ[ℝ]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a s => quaternionModel.kappa a s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain the complete argument telescope of `kappa_eq_one_sub_dist_sq`. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ a b : unitary ℍ[ℝ], r.readout () a b = 1 - dist a b ^ 2 / 4

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1
  rw [dist_self] at hh
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, -1, fun h => ?_⟩
  change quaternionModel.kappa 1 1 = quaternionModel.kappa 1 (-1) at h
  rw [quaternionModel.kappa_self] at h
  exact one_ne_neg_one ((quaternionModel.kappa_eq_one_iff 1 (-1)).1 h.symm)

def source_registration : Registration arena (type_of% kappa_eq_one_sub_dist_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kappa_eq_one_sub_dist_sq, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Reading

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

def exists_normalized_embedding_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_normalized_embedding.{u}) (Realization Transfer.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism.exists_normalized_embedding_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism.NormalizedTransfer.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨NormalizedTransfer.arena.{u}⟩
  objectArena := .source ⟨NormalizedTransfer.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source NormalizedTransfer.arena.{u} ⟨NormalizedTransfer.source_registration.{u}⟩
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
    coordinates := #[0, 1, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def isClosed_range_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@isClosed_range.{u}) (Realization Image.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism.isClosed_range_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism.Image.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Image.arena.{u}⟩
  objectArena := .source ⟨Image.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Image.arena.{u} ⟨Image.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Image.signature.{u} (fun _ _ s => Set.range s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def kappa_eq_one_sub_dist_sq_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      kappa_eq_one_sub_dist_sq (Realization Reading.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism.kappa_eq_one_sub_dist_sq_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism.Reading.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Reading.arena⟩
  objectArena := .source ⟨Reading.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Reading.arena ⟨Reading.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reading.signature
    (fun _ a s => quaternionModel.kappa a s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
