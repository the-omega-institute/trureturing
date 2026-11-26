import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism
import Reg.Support.UniverseSingleReadout

/-! The order comparison of source and target HN slopes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open _root_.D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism
open _root_.D5.S3.Combinatorics.Lattices.EuclideanSublattices
open _root_.D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (N : Submodule ℤ E) (C : Submodule ℤ F)
    [DiscreteTopology N] [DiscreteTopology C] (a : Sublattice N) (b : Sublattice C)
    (f : E →L[ℝ] F) (h : ℝ),
    (∀ x ∈ integral N a, f x ∈ C) →
    (∃ x ∈ integral N a, f x ∉ Submodule.span ℝ (integral C b : Set F)) →
    (∀ x ∈ Submodule.span ℝ (integral N a : Set E),
      ‖(Submodule.span ℝ (integral C b : Set F))ᗮ.starProjection (f x)‖ ≤
      Real.exp h * ‖x‖) →
    V.readout () () ((slopeData N).muMin ⊥ a) ((slopeData C).muMax b ⊤ + h)

private theorem rejected_fails : ¬ arena.{u,v}.Law rejected := by
  classical
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Unit)
  let F := EuclideanSpace ℝ (ULift.{v} Unit)
  let b := EuclideanSpace.basisFun (ULift.{u} Unit) ℝ
  let c := EuclideanSpace.basisFun (ULift.{v} Unit) ℝ
  let e : ULift.{u} Unit ≃ ULift.{v} Unit := Equiv.ulift.trans Equiv.ulift.symm
  let f := b.equiv c e
  let N := Submodule.span ℤ (Set.range b.toBasis)
  let C := Submodule.span ℤ (Set.range c.toBasis)
  have hfC : ∀ x ∈ N, f x ∈ C := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨e i, (b.equiv_apply_basis c e i).symm⟩
    | zero => simpa using C.zero_mem
    | add x y _ _ ihx ihy => simpa using C.add_mem ihx ihy
    | smul n x _ ih => simpa using C.smul_mem n ih
  have hf0 : ∃ x ∈ N, f x ≠ 0 := by
    refine ⟨b ⟨()⟩, Submodule.subset_span ⟨⟨()⟩, rfl⟩, ?_⟩
    intro hz
    have hn := f.norm_map (b ⟨()⟩)
    rw [hz, norm_zero, b.orthonormal.norm_eq_one] at hn
    norm_num at hn
  have hn : ‖f.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ Real.exp 0 := by
    rw [Real.exp_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have htop : integral N ⊤ = N := integral_top N
  have hbot : integral C ⊥ = ⊥ := by
    change
      (((Submodule.span ℝ (((⊥ : Submodule ℤ C).map C.subtype) : Set F)).restrictScalars
        ℤ).comap C.subtype).map C.subtype = ⊥
    simp
  have hfmod : ∃ x ∈ integral N ⊤,
      f x ∉ Submodule.span ℝ (integral C ⊥ : Set F) := by
    obtain ⟨x, hx, hfx⟩ := hf0
    refine ⟨x, htop.symm ▸ hx, ?_⟩
    rw [hbot]
    simpa using hfx
  exact law N C ⊤ ⊥ f.toContinuousLinearEquiv.toContinuousLinearMap 0
    (by intro x hx; change f x ∈ C; exact hfC x (htop ▸ hx)) hfmod (fun x _ =>
      ((Submodule.span ℝ (integral C ⊥ : Set F))ᗮ.norm_starProjection_apply_le (f x)).trans
        ((f.toContinuousLinearEquiv.toContinuousLinearMap.le_opNorm x).trans
          (mul_le_mul_of_nonneg_right hn (norm_nonneg x))))

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
  norm_num at h

def family : Registration arena.{u,v} (type_of% @slope_morphism.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@slope_morphism.{u,v}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u,v}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@slope_morphism.{u,v}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism.slope_morphism
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism

namespace Reg.D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism.IntegralTop

abbrev Params := Σ E : Type u, NormedAddCommGroup E
abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Params.{u}
    (fun p => letI := p.2; Submodule ℤ p.1)
    (fun p => letI := p.2; Submodule ℤ p.1 → Prop)
def actual : Realization signature.{u} :=
  realize signature (fun _ p M N => letI := p.2; M = N) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law T := ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E),
    T.readout () ⟨E, inferInstance⟩ (integral L ⊤) L
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let E := EuclideanSpace ℝ (ULift.{u} Empty)
  let L : Submodule ℤ E := ⊥
  exact law L
private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro _
  let E := EuclideanSpace ℝ (ULift.{u} Unit)
  let x := EuclideanSpace.basisFun (ULift.{u} Unit) ℝ (ULift.up ())
  refine ⟨⟨E, inferInstance⟩, ⊥, ⊤, ?_⟩
  intro h
  have heq : (⊤ : Submodule ℤ E) = ⊥ := Eq.mp (congrFun h ⊥) rfl
  have hm : x ∈ (⊥ : Submodule ℤ E) := heq ▸ (show x ∈ ⊤ from trivial)
  have hz : x = 0 := hm
  have hn := (EuclideanSpace.basisFun (ULift.{u} Unit) ℝ).norm_eq_one (ULift.up ())
  change ‖x‖ = 1 at hn
  rw [hz, norm_zero] at hn
  norm_num at hn

def family : Registration arena.{u}
    (type_of% @integral_top.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_top.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_top.{u}) (Realization signature.{u}) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism.integral_top
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism.IntegralTop.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p M N => letI := p.2; M = N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism.IntegralTop
