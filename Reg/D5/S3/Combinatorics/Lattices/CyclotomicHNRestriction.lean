import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction
import D5.S3.Combinatorics.Lattices.EuclideanCommonLattice
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Module.ULift

/-! Order-submodule equality and actual HN endpoint observations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Combinatorics.Lattices
open EuclideanSublattices EuclideanHarderNarasimhan EuclideanHNEquivariance
open CyclotomicHNRestriction HarderNarasimhan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

namespace Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction

abbrev Params := Σ E : Type v, NormedAddCommGroup E

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Params.{v}
    (fun p => letI := p.2; Submodule ℤ p.1)
    (fun p => letI := p.2; Submodule ℤ p.1 → Prop)

def actual : Realization signature.{v} :=
  realize signature (fun _ p M N => letI := p.2; M = N) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def law (V : Realization signature.{v}) : Prop :=
  ∀ {A : Type u} {E : Type v} [ring : CommRing A] [NoZeroDivisors A]
    [normed : NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mod : Module A E]
    (z : A) (hz : Algebra.adjoin ℤ ({z} : Set A) = ⊤)
    (L : Submodule ℤ E) (T : E ≃ₗᵢ[ℝ] E)
    (hT : L.map (T.toLinearMap.restrictScalars ℤ) = L)
    (hact : ∀ x : E, T x = z • x)
    [Algebra.IsAlgebraic ℤ A] [FiniteDimensional ℝ E] [DiscreteTopology L]
    (l : List (Sublattice L)) (hl : (slopeData L).Filtration ⊥ ⊤ l),
    let saturated := fun F : Sublattice L =>
      ∃ P : Submodule A E,
        V.readout () ⟨E, normed⟩ (P.restrictScalars ℤ) (integral L F) ∧
        ∀ (a : A), a ≠ 0 → ∀ x ∈ L, a • x ∈ P → x ∈ P
    (∀ F ∈ l, saturated F) ∧
      ∀ t : ℝ, saturated (above L (slopeData L) t ⊥ l)

abbrev arena : Arena where
  signature := signature.{v}
  Law := law.{u,v}

private theorem rejected_fails : ¬ arena.{u,v}.Law rejected := by
  classical
  intro law
  let A := ULift.{u} ℤ
  letI : IsDomain A := MulEquiv.isDomain ℤ ULift.ringEquiv.toMulEquiv
  let E := EuclideanSpace ℝ (ULift.{v} Empty)
  letI : Algebra.IsAlgebraic ℤ A := ⟨fun x => by
    have h := isAlgebraic_intCast (R := ℤ) (A := A) x.down
    have he : (x.down : A) = x := by
      apply ULift.ext
      exact Int.cast_id
    exact he ▸ h⟩
  let L : Submodule ℤ E := ⊥
  let T := LinearIsometryEquiv.refl ℝ E
  have hz : Algebra.adjoin ℤ ({(1 : A)} : Set A) = ⊤ := by
    apply top_unique
    intro a _
    have h := (Algebra.adjoin ℤ ({(1 : A)} : Set A)).algebraMap_mem a.down
    simpa [A] using h
  have hT : L.map (T.toLinearMap.restrictScalars ℤ) = L := by simp [L, T]
  have hact : ∀ x : E, T x = (1 : A) • x := by simp [T]
  have hf : (slopeData L).Filtration ⊥ ⊤ [] := by
    have hbot : (⊥ : Sublattice L) = ⊤ := Subsingleton.elim _ _
    rw [← hbot]
    exact .nil _
  obtain ⟨P, hP, _⟩ := (law 1 hz L T hT hact [] hf).2 0
  exact hP

private theorem dependence : ObservationalDependence signature.{v} actual := by
  classical
  intro _
  let E := EuclideanSpace ℝ (ULift.{v} Unit)
  let x := EuclideanSpace.basisFun (ULift.{v} Unit) ℝ (ULift.up ())
  refine ⟨⟨E, inferInstance⟩, ⊥, ⊤, ?_⟩
  intro h
  have he : (⊤ : Submodule ℤ E) = ⊥ := Eq.mp (congrFun h ⊥) rfl
  have hm : x ∈ (⊥ : Submodule ℤ E) := he ▸ (show x ∈ (⊤ : Submodule ℤ E) by trivial)
  have hz : x = 0 := hm
  have hn := (EuclideanSpace.basisFun (ULift.{v} Unit) ℝ).norm_eq_one (ULift.up ())
  change ‖x‖ = 1 at hn
  rw [hz, norm_zero] at hn
  norm_num at hn

def family : Registration arena.{u,v} (type_of% @hn_saturated.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hn_saturated.{u,v}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u,v}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hn_saturated.{u,v}) (Realization signature.{v}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.hn_saturated
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value", "body", "arg",
        "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction

namespace Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.Stage

abbrev Space := EuclideanSpace ℝ (ULift.{v} Unit)

def basis : Module.Basis (ULift.{v} Unit) ℝ Space :=
  (EuclideanSpace.basisFun (ULift.{v} Unit) ℝ).toBasis

def lattice : Submodule ℤ Space := Submodule.span ℤ (Set.range basis.{v})

instance : DiscreteTopology lattice.{v} := by
  unfold lattice
  infer_instance

private theorem bot_lt_top : (⊥ : Sublattice lattice.{v}) < ⊤ := by
  apply lt_of_le_of_ne bot_le
  intro he
  have h := congrArg (integral lattice.{v}) he
  rw [EuclideanCommonLattice.bot_carrier, EuclideanSlopeMorphism.integral_top] at h
  have hx : basis.{v} (ULift.up ()) ∈ lattice.{v} :=
    Submodule.subset_span (Set.mem_range_self _)
  rw [← h] at hx
  have hz : basis.{v} (ULift.up ()) = 0 := hx
  have hn := (EuclideanSpace.basisFun (ULift.{v} Unit) ℝ).norm_eq_one (ULift.up ())
  change ‖basis.{v} (ULift.up ())‖ = 1 at hn
  rw [hz, norm_zero] at hn
  norm_num at hn

private theorem first_factor : ∃ F : Sublattice lattice.{v},
    (slopeData lattice).Semistable ⊥ F := by
  obtain ⟨l, hl, _⟩ := ((euclidean_hn lattice.{v} ⊥ ⊤).2.1).mpr bot_le
  have ht := bot_lt_top.{v}
  cases l with
  | nil =>
    generalize ha : (⊥ : Sublattice lattice.{v}) = a at hl ht
    generalize hb : (⊤ : Sublattice lattice.{v}) = b at hl ht
    cases hl
    exact (lt_irrefl _ ht).elim
  | cons F l =>
    generalize ha : (⊥ : Sublattice lattice.{v}) = a at hl ⊢
    generalize hb : (⊤ : Sublattice lattice.{v}) = b at hl
    cases hl with | cons hs _ _ _ => exact ⟨F, hs⟩

abbrev Params := Σ E : Type v, Σ normed : NormedAddCommGroup E,
  letI := normed
  Σ inner : InnerProductSpace ℝ E,
    letI := inner
    Submodule ℤ E

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Params.{v}
    (fun p => letI := p.2.1; letI := p.2.2.1; Sublattice p.2.2.2)
    (fun p => letI := p.2.1; letI := p.2.2.1; Sublattice p.2.2.2)

def actual : Realization signature.{v} :=
  realize signature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro _
  refine ⟨⟨Space.{v}, inferInstance, inferInstance, lattice.{v}⟩, ⊥, ⊤, ?_⟩
  change (⊥ : Sublattice lattice.{v}) ≠ ⊤
  exact ne_of_lt bot_lt_top

private theorem integer_stable {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (L : Submodule ℤ E) (F : Sublattice L) :
    OrderStable (A := ULift.{u} ℤ) L F := by
  intro a x hx
  exact (integral L F).smul_mem a.down hx

end Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.Stage

namespace Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.Semistability

open Stage

abbrev signature : Signature := Stage.signature.{v}

def actual : Realization signature.{v} := Stage.actual

def rejected : Realization signature.{v} := Stage.rejected

def law (V : Realization signature.{v}) : Prop :=
  ∀ {A : Type u} {E : Type v} [CommRing A]
    [normed : NormedAddCommGroup E] [inner : InnerProductSpace ℝ E]
    [Module A E]
    (z : A) (hz : Algebra.adjoin ℤ ({z} : Set A) = ⊤)
    (L : Submodule ℤ E) (T : E ≃ₗᵢ[ℝ] E)
    (hT : L.map (T.toLinearMap.restrictScalars ℤ) = L)
    (hact : ∀ x : E, T x = z • x)
    [FiniteDimensional ℝ E] [DiscreteTopology L]
    (c : ℝ) (F G : Sublattice L)
    (hF : OrderStable (A := A) L F) (hG : OrderStable (A := A) L G),
    (slopeData L).Semistable (V.readout () ⟨E, normed, inner, L⟩ F) G ↔
      OrderSemistable (A := A) L c F G

abbrev arena : Arena where
  signature := signature.{v}
  Law := law.{u,v}

private theorem rejected_fails : ¬ arena.{u,v}.Law rejected := by
  classical
  intro law
  let A := ULift.{u} ℤ
  let E := Space.{v}
  let L := lattice.{v}
  let T := LinearIsometryEquiv.refl ℝ E
  have hz : Algebra.adjoin ℤ ({(1 : A)} : Set A) = ⊤ := by
    apply top_unique
    intro a _
    have h := (Algebra.adjoin ℤ ({(1 : A)} : Set A)).algebraMap_mem a.down
    simpa [A] using h
  have hT : L.map (T.toLinearMap.restrictScalars ℤ) = L := by simp [L, T]
  have hact : ∀ x : E, T x = (1 : A) • x := by simp [T]
  obtain ⟨F, hF⟩ := first_factor.{v}
  have h := (law 1 hz L T hT hact 0 F F
    (integer_stable L F) (integer_stable L F)).mp hF
  exact lt_irrefl F h.1

def family : Registration arena.{u,v} (type_of% @semistable_restriction.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@semistable_restriction.{u,v}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u,v}.Law actual rejected rejected_fails
  dependence := Stage.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@semistable_restriction.{u,v}) (Realization signature.{v}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.semistable_restriction
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.Semistability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ F => F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction
    definition := none
    coordinates := #[1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.Semistability

namespace Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.Filtration

open Stage

abbrev signature : Signature := Stage.signature.{v}

def actual : Realization signature.{v} := Stage.actual

def rejected : Realization signature.{v} := Stage.rejected

def law (V : Realization signature.{v}) : Prop :=
  ∀ {A : Type u} {E : Type v} [CommRing A]
    [normed : NormedAddCommGroup E] [inner : InnerProductSpace ℝ E]
    [Module A E]
    (z : A) (hz : Algebra.adjoin ℤ ({z} : Set A) = ⊤)
    (L : Submodule ℤ E) (T : E ≃ₗᵢ[ℝ] E)
    (hT : L.map (T.toLinearMap.restrictScalars ℤ) = L)
    (hact : ∀ x : E, T x = z • x)
    [FiniteDimensional ℝ E] [DiscreteTopology L]
    (c : ℝ) (F G : Sublattice L)
    (hF : OrderStable (A := A) L F) (hG : OrderStable (A := A) L G) (l : List (Sublattice L)),
    (slopeData L).Filtration (V.readout () ⟨E, normed, inner, L⟩ F) G l ↔
      OrderFiltration (A := A) L c F G l

abbrev arena : Arena where
  signature := signature.{v}
  Law := law.{u,v}

private theorem rejected_fails : ¬ arena.{u,v}.Law rejected := by
  classical
  intro law
  let A := ULift.{u} ℤ
  let E := Space.{v}
  let L := lattice.{v}
  let T := LinearIsometryEquiv.refl ℝ E
  have hz : Algebra.adjoin ℤ ({(1 : A)} : Set A) = ⊤ := by
    apply top_unique
    intro a _
    have h := (Algebra.adjoin ℤ ({(1 : A)} : Set A)).algebraMap_mem a.down
    simpa [A] using h
  have hT : L.map (T.toLinearMap.restrictScalars ℤ) = L := by simp [L, T]
  have hact : ∀ x : E, T x = (1 : A) • x := by simp [T]
  have hr : OrderFiltration (A := A) L 0 ⊤ ⊤ [] :=
    .nil _ (integer_stable L ⊤)
  have h := (law 1 hz L T hT hact 0 ⊤ ⊤
    (integer_stable L ⊤) (integer_stable L ⊤) []).mpr hr
  change (slopeData L).Filtration ⊥ ⊤ [] at h
  have he : (⊥ : Sublattice L) = ⊤ := by
    generalize ha : (⊥ : Sublattice L) = a at h ⊢
    generalize hb : (⊤ : Sublattice L) = b at h ⊢
    cases h
    rfl
  exact (ne_of_lt bot_lt_top.{v}) he

def family : Registration arena.{u,v} (type_of% @filtration_restriction.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@filtration_restriction.{u,v}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u,v}.Law actual rejected rejected_fails
  dependence := Stage.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@filtration_restriction.{u,v}) (Realization signature.{v}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.filtration_restriction
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.Filtration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ F => F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction
    definition := none
    coordinates := #[1, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn",
        "arg", "fn", "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.CyclotomicHNRestriction.Filtration
