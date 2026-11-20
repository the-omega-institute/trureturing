import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.DependentFamily

/-! Source-bound audits of the dimension bound for finite-rank ternary comparison structures.

The two dimension bounds are audited through the dimension `d` of the target `ℝ^d`; the rejected
reading `0` fails on the unit quaternions, carried to an arbitrary universe: a preconnected,
compact, noncommutative group, injected continuously into `ℝ⁴` by its coordinates, with the
orthogonal representation of its inner product kernel and with the quaternion comparison
structure of feature rank five. Chain connectivity is audited through the structure `C`; the
rejected reading keeps the transfer of `C` and replaces its reading by the indicator of
equality, which is not chain connected on the unit quaternions. -/

namespace Reg.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive (liftedModel
  liftedModel_noncommutative liftedModel_hasFeatureRank_five)

open scoped InnerProductSpace Quaternion Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-- The unit quaternions in universe `u`. -/
abbrev Quat : Type u := ULift.{u} (unitary ℍ[ℝ])

theorem preconnectedSpace_unitary : PreconnectedSpace (unitary ℍ[ℝ]) :=
  Subtype.preconnectedSpace (by
    rw [coe_unitary_eq_sphere]
    exact isPreconnected_sphere (by rw [Quaternion.rank_eq_four]; norm_num) 0 1)

local instance : PreconnectedSpace Quat.{u} := by
  have := preconnectedSpace_unitary
  refine ⟨?_⟩
  have h := isPreconnected_range
    (continuous_uliftUp : Continuous (ULift.up.{u} : unitary ℍ[ℝ] → Quat.{u}))
  rwa [Function.Surjective.range_eq (fun q => ⟨q.down, rfl⟩)] at h

local instance : CompactSpace (unitary ℍ[ℝ]) :=
  isCompact_iff_compactSpace.mp (by
    rw [coe_unitary_eq_sphere]
    exact isCompact_sphere 0 1)

local instance : LocallyCompactSpace Quat.{u} :=
  Homeomorph.ulift.isOpenEmbedding.locallyCompactSpace

/-- The unit quaternion as a quaternion. -/
def val (q : Quat.{u}) : ℍ[ℝ] := (q.down : ℍ[ℝ])

/-- The coordinates of a unit quaternion in `ℝ⁴`. -/
def coords (q : Quat.{u}) : EuclideanSpace ℝ (Fin 4) :=
  Quaternion.linearIsometryEquivTuple (val q)

theorem coords_continuous : Continuous coords.{u} :=
  Quaternion.linearIsometryEquivTuple.continuous.comp
    (continuous_subtype_val.comp continuous_uliftDown)

theorem coords_injective : Function.Injective coords.{u} := by
  intro p q h
  exact ULift.ext (Subtype.ext (Quaternion.linearIsometryEquivTuple.injective h))

theorem val_mul (g x : Quat.{u}) : val (g * x) = val g * val x := rfl

theorem val_continuous_mul (x : Quat.{u}) : Continuous fun g : Quat.{u} => val (g * x) := by
  simp only [val_mul]
  exact (continuous_subtype_val.comp continuous_uliftDown).mul continuous_const

theorem val_gram (g x y : Quat.{u}) : ⟪val (g * x), val (g * y)⟫_ℝ = ⟪val x, val y⟫_ℝ := by
  rw [val_mul, val_mul]
  exact LinearIsometry.inner_map_map
    { toLinearMap := LinearMap.mulLeft ℝ (val g)
      norm_map' := fun r => by
        rw [LinearMap.mulLeft_apply, norm_mul, val, CStarRing.norm_coe_unitary, one_mul] } _ _

/-- A continuous injective orthogonal representation of the unit quaternions. -/
theorem exists_orthogonalRep : ∃ ρ : Quat.{u} →* Matrix.orthogonalGroup
    (Fin (Module.finrank ℝ (Submodule.span ℝ (Set.range val.{u})))) ℝ,
    Continuous ρ ∧ Function.Injective ρ := by
  obtain ⟨ρ, hρc, hρ⟩ := _root_.D5.S3.Quantum.AURICOmega.InvariantGramRepresentation.exists_orthogonal_rep_ker_eq
    val.{u} val_continuous_mul val_gram
  refine ⟨ρ, hρc, (injective_iff_map_eq_one ρ).2 fun g hg => ?_⟩
  have h := (hρ g).1 hg 1
  rw [mul_one] at h
  exact ULift.ext (Subtype.ext (by simpa [val] using h))

theorem quat_noncommutative : ∃ a b : Quat.{u}, a * b ≠ b * a := by
  refine ⟨⟨unitI⟩, ⟨unitJ⟩, fun h => ?_⟩
  have h' := congrArg (fun q : Quat.{u} => (val q).imK) h
  change ((unitI : ℍ[ℝ]) * unitJ).imK = ((unitJ : ℍ[ℝ]) * unitI).imK at h'
  simp [unitI, unitJ] at h'
  norm_num at h'

theorem liftedModel_tri_continuous :
    Continuous fun p : Quat.{u} × Quat.{u} × Quat.{u} => liftedModel.tri p.1 p.2.1 p.2.2 := by
  change Continuous fun p : Quat.{u} × Quat.{u} × Quat.{u} =>
    (ULift.up (p.1.down * p.2.1.down⁻¹ * p.2.2.down) : Quat.{u})
  fun_prop

theorem liftedModel_kappa_continuousAt (x : Quat.{u}) : ContinuousAt (liftedModel.kappa x) x := by
  have h : Continuous fun y : Quat.{u} => (1 + ⟪(x.down : ℍ[ℝ]), (y.down : ℍ[ℝ])⟫_ℝ) / 2 := by
    fun_prop
  exact h.continuousAt

/-! The dimension `d` in the conclusion `3 ≤ d` of `three_le_of_orthogonal`. -/
namespace GroupBound

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete dimension, group, neighbourhood, map and representation telescope of
`three_le_of_orthogonal`. -/
abbrev arena : Arena where
  signature := signature
  Law rd := ∀ {d n : ℕ} {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [PreconnectedSpace G] {V : Set G}, V ∈ 𝓝 (1 : G) →
    ∀ (f : G → EuclideanSpace ℝ (Fin d)), ContinuousOn f V → Set.InjOn f V →
    ∀ (ρ : G →* Matrix.orthogonalGroup (Fin n) ℝ), Continuous ρ → Function.Injective ρ →
    (∃ a b : G, a * b ≠ b * a) → 3 ≤ rd.readout () () d

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨ρ, hρc, hρi⟩ := exists_orthogonalRep.{u}
  have hh := h (V := Set.univ) Filter.univ_mem coords.{u} coords_continuous.continuousOn
    coords_injective.injOn ρ hρc hρi quat_noncommutative
  exact absurd hh (by decide)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 3, 0, ?_⟩
  decide

abbrev sourceStatement : Prop := type_of% @three_le_of_orthogonal.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@three_le_of_orthogonal.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end GroupBound

/-! The dimension `d` in the first conjunct `3 ≤ d` of `three_le_dim_of_hasFeatureRank`. -/
namespace StructureBound

def actual : Realization GroupBound.signature :=
  realize GroupBound.signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization GroupBound.signature :=
  realize GroupBound.signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the complete dimension, carrier, structure, continuity, rank and neighbourhood
telescope and both conjuncts of `three_le_dim_of_hasFeatureRank`. -/
abbrev arena : Arena where
  signature := GroupBound.signature
  Law rd := ∀ {d : ℕ} {M : Type u} [TopologicalSpace M] [LocallyCompactSpace M]
    [PreconnectedSpace M] (C : TernaryComparison M),
    Continuous (fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) → (∀ x, ContinuousAt (C.kappa x) x) →
    C.Noncommutative → ∀ {r : ℕ}, C.HasFeatureRank r → ∀ {o : M} {V : Set M}, V ∈ 𝓝 o →
    ∀ (f : M → EuclideanSpace ℝ (Fin d)), ContinuousOn f V → Set.InjOn f V →
    3 ≤ rd.readout () () d ∧ 5 ≤ r

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h liftedModel.{u} liftedModel_tri_continuous liftedModel_kappa_continuousAt
    liftedModel_noncommutative liftedModel_hasFeatureRank_five (o := ⟨1⟩) (V := Set.univ)
    Filter.univ_mem coords.{u} coords_continuous.continuousOn coords_injective.injOn
  exact absurd hh.1 (by decide)

theorem dependence : ObservationalDependence GroupBound.signature actual := by
  intro i
  cases i
  refine ⟨(), 3, 0, ?_⟩
  decide

abbrev sourceStatement : Prop := type_of% @three_le_dim_of_hasFeatureRank.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@three_le_dim_of_hasFeatureRank.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end StructureBound

/-! The structure `C` in the conclusion `C.ChainConnected` of `chainConnected_of_connected`. -/
namespace Chain

/-- The structure with the same transfer and the indicator of equality as reading. -/
def discrete {M : Type u} (C : TernaryComparison M) : TernaryComparison M := by
  classical
  exact
  { tri := C.tri
    kappa := fun x y => if x = y then 1 else 0
    tri_self_left := C.tri_self_left
    tri_self_right := C.tri_self_right
    tri_assoc := C.tri_assoc
    kappa_symm := fun x y => by
      by_cases h : x = y
      · simp [h]
      · simp [h, Ne.symm h]
    kappa_eq_one_iff := fun x y => by
      by_cases h : x = y <;> simp [h]
    kappa_nonneg := fun x y => by
      by_cases h : x = y <;> simp [h]
    kappa_tri_right := fun x y u v => by
      have hinj : C.tri x u v = C.tri y u v ↔ x = y := by
        constructor
        · intro e
          have e' := congrArg (fun z => C.tri z v u) e
          simp only [C.tri_assoc, C.tri_self_left, C.tri_self_right] at e'
          exact e'
        · rintro rfl
          rfl
      simp only [hinj]
    kappa_tri_left := fun u v x y => by
      have hinj : C.tri u v x = C.tri u v y ↔ x = y := by
        constructor
        · intro e
          have e' := congrArg (fun z => C.tri v u z) e
          simp only [← C.tri_assoc, C.tri_self_left, C.tri_self_right] at e'
          exact e'
        · rintro rfl
          rfl
      simp only [hinj]
    kappa_gram_nonneg := fun n x c => by
      have key : ∑ i, ∑ j, c i * c j * (if x i = x j then (1 : ℝ) else 0) =
          ∑ z ∈ Finset.univ.image x, (∑ j ∈ Finset.univ.filter (fun j => x j = z), c j) ^ 2 := by
        have h1 : ∀ i, ∑ j, c i * c j * (if x i = x j then (1 : ℝ) else 0) =
            c i * ∑ j ∈ Finset.univ.filter (fun j => x j = x i), c j := by
          intro i
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases h : x i = x j
          · simp [h]
          · simp [h, Ne.symm h]
        simp only [h1]
        rw [← Finset.sum_fiberwise_of_maps_to (g := x) (t := Finset.univ.image x)
          (fun i _ => Finset.mem_image_of_mem x (Finset.mem_univ i))]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
      rw [key]
      exact Finset.sum_nonneg fun z _ => sq_nonneg _ }

theorem discrete_not_chainConnected {M : Type u} (C : TernaryComparison M) {x y : M}
    (hxy : x ≠ y) : ¬ (discrete C).ChainConnected := by
  intro h
  have hr := h (1 / 2) (by norm_num) x y
  have key : ∀ z, Relation.ReflTransGen (fun a b : M => 1 - 1 / 2 < (discrete C).kappa a b) x z →
      z = x := by
    intro z hz
    induction hz with
    | refl => rfl
    | @tail b c _ hbc ih =>
      classical
      have hbc' : 1 - 1 / 2 < (if b = c then (1 : ℝ) else 0) := by
        simpa [discrete] using hbc
      by_cases hb : b = c
      · rw [← hb]
        exact ih
      · simp [hb] at hbc'
        norm_num at hbc'
  exact hxy (key y hr).symm

abbrev signature : Signature where
  Params := Type u
  State M := TernaryComparison M
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ M := TernaryComparison M
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ s => discrete s) (fun e => nomatch e)

/-- Retain the complete carrier, topology, structure and continuity telescope of
`chainConnected_of_connected`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law rd := ∀ {M : Type u} [TopologicalSpace M] [PreconnectedSpace M] (C : TernaryComparison M),
    (∀ x, ContinuousAt (C.kappa x) x) → (rd.readout () M C).ChainConnected

theorem one_ne_negOne : (⟨1⟩ : Quat.{u}) ≠ ⟨-1⟩ := fun h =>
  Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive.one_ne_neg_one (congrArg ULift.down h)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact discrete_not_chainConnected liftedModel.{u} one_ne_negOne
    (h liftedModel.{u} liftedModel_kappa_continuousAt)

theorem unitary_one_ne_unitI : (1 : unitary ℍ[ℝ]) ≠ unitI := by
  intro h
  have h' := congrArg (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).re) h
  change ((1 : unitary ℍ[ℝ]) : ℍ[ℝ]).re = (unitI : ℍ[ℝ]).re at h'
  simp [unitI] at h'

theorem one_ne_unitI : (⟨1⟩ : Quat.{u}) ≠ ⟨unitI⟩ := fun h =>
  unitary_one_ne_unitI (congrArg ULift.down h)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨Quat.{u}, liftedModel.{u}, discrete liftedModel.{u}, ?_⟩
  change liftedModel.{u} ≠ discrete liftedModel.{u}
  intro e
  have h1 := congrArg (fun C : TernaryComparison Quat.{u} => C.kappa ⟨1⟩ ⟨unitI⟩) e
  have h0 : liftedModel.{u}.kappa ⟨1⟩ ⟨unitI⟩ = 1 / 2 := by
    change (1 + ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), (unitI : ℍ[ℝ])⟫_ℝ) / 2 = 1 / 2
    rw [inner_eq_components]
    simp [unitI]
  classical
  have h2 : (discrete liftedModel.{u}).kappa ⟨1⟩ ⟨unitI⟩ = 0 := by
    simp [discrete, unitary_one_ne_unitI]
  rw [h0, h2] at h1
  norm_num at h1

abbrev sourceStatement : Prop := type_of% @chainConnected_of_connected.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chainConnected_of_connected.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Chain

def three_le_of_orthogonal_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@three_le_of_orthogonal.{u}) (Realization GroupBound.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.three_le_of_orthogonal_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.GroupBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨GroupBound.arena.{u}⟩
  objectArena := .source ⟨GroupBound.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source GroupBound.arena.{u} ⟨GroupBound.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize GroupBound.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def three_le_dim_of_hasFeatureRank_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@three_le_dim_of_hasFeatureRank.{u}) (Realization GroupBound.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.three_le_dim_of_hasFeatureRank_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.StructureBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨StructureBound.arena.{u}⟩
  objectArena := .source ⟨StructureBound.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source StructureBound.arena.{u} ⟨StructureBound.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize GroupBound.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def chainConnected_of_connected_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@chainConnected_of_connected.{u}) (Realization Chain.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.chainConnected_of_connected_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.Chain.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Chain.arena.{u}⟩
  objectArena := .source ⟨Chain.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Chain.arena.{u} ⟨Chain.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Chain.signature.{u} (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound
