/- GID: D5/S3/VertexAlgebra/Analysis/OriginalSmoothDomain
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalSmoothDomain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The dense invariant original smooth domain and its actual smeared operators. -/

import D5.S3.VertexAlgebra.Analysis.OriginalInfiniteSmearing
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The projective intersection is embedded injectively in the original Hilbert
completion. It is not a negative-order extrapolation or an algebraic output
restriction. The opposite-charge domain below is the same explicit intersection. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace Topology ComplexConjugate
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open SourceBPZ.OriginalMatterHermitian SmoothCircleFourier
open private inclusion_injective inclusion_self inclusion_comp from
  D5.S3.VertexAlgebra.Analysis.OriginalSobolev
open private Hm_charged_circle actual_phase from
  D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
open private modeExtension_embed from
  D5.S3.VertexAlgebra.Analysis.OriginalModeExtension
open private smear_compatible smear_apply vector_summable smear_vector_bound from
  D5.S3.VertexAlgebra.Analysis.OriginalInfiniteSmearing
open private coefficient_conjugate from
  D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier

open Model

variable (M : Model)

/-- Compatible representatives in every nonnegative Sobolev completion. -/
def Model.smoothFamilies : Submodule ℂ (∀ k : ℕ, M.Sobolev k) where
  carrier x := ∀ (j k : ℕ) (hjk : j ≤ k), M.inclusion j k hjk (x k) = x j
  zero_mem' := by intro j k h; exact map_zero _
  add_mem' := by
    intro x y hx hy j k h
    simp only [Pi.add_apply, map_add, hx j k h, hy j k h]
  smul_mem' := by
    intro c x hx j k h
    simp only [Pi.smul_apply, map_smul, hx j k h]

abbrev Model.Smooth := M.smoothFamilies

def Model.evaluation : M.Smooth →ₗ[ℂ] M.Hilbert where
  toFun x := x.1 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evaluation_injective : Function.Injective M.evaluation := by
  intro x y hxy
  apply Subtype.ext
  funext k
  apply inclusion_injective M 0 k (Nat.zero_le k)
  rw [x.2 0 k (Nat.zero_le k), y.2 0 k (Nat.zero_le k)]
  exact hxy

/-- H_infinity as an actual dense submodule of the original Hilbert completion. -/
def Model.smoothDomain : Submodule ℂ M.Hilbert := M.evaluation.range

def Model.domainEquiv : M.Smooth ≃ₗ[ℂ] M.smoothDomain :=
  LinearEquiv.ofInjective M.evaluation (evaluation_injective M)

def Model.finiteFamily : Carrier M.D →ₗ[ℂ] M.Smooth where
  toFun v := ⟨fun k => M.embed k v, fun j k h => inclusion_embed M j k h v⟩
  map_add' v w := Subtype.ext (funext fun k => (M.embed k).map_add v w)
  map_smul' c v := Subtype.ext (funext fun k => (M.embed k).map_smul c v)

private theorem finite_in_domain (v : Carrier M.D) : M.embed 0 v ∈ M.smoothDomain :=
  ⟨M.finiteFamily v, rfl⟩

private theorem smoothDomain_dense : Dense (M.smoothDomain : Set M.Hilbert) :=
  (embed_dense M 0).mono (by rintro _ ⟨v,rfl⟩; exact finite_in_domain M v)

/-- All Sobolev representatives of the smeared image; infinite support is permitted. -/
def Model.smearFamily (a : Charge M.D) (f : Test) : M.Smooth →ₗ[ℂ] M.Smooth where
  toFun x := ⟨fun k => M.smear a f k (x.1 (M.order a+k)), by
    intro j k hjk
    rw [smear_compatible]
    exact congrArg (M.smear a f j) (x.2 _ _ (Nat.add_le_add_left hjk _))⟩
  map_add' x y := Subtype.ext (funext fun k => (M.smear a f k).map_add _ _)
  map_smul' c x := Subtype.ext (funext fun k => (M.smear a f k).map_smul c _)

/-- The actual charged field smeared on the common dense invariant domain. -/
def Model.field (a : Charge M.D) (f : Test) : M.Hilbert →ₗ.[ℂ] M.Hilbert where
  domain := M.smoothDomain
  toFun := M.evaluation.comp ((M.smearFamily a f).comp M.domainEquiv.symm.toLinearMap)

/-- The cocycle sign is retained in the SECOND slot of the pairing identity. -/
def Model.eta (a : Charge M.D) : ℂ := paritySign (chargeEnergy M.D a)

def Model.opposite (a : Charge M.D) (f : Test) : M.Hilbert →ₗ.[ℂ] M.Hilbert :=
  M.eta a • M.field (-a) f.conjugate

private theorem eta_cocycle (a : Charge M.D) : M.eta a = epsilon M.D a (-a) :=
  (actual_phase a).symm

private theorem field_eval (a : Charge M.D) (f : Test) (x : M.Smooth) :
    M.field a f (M.domainEquiv x) =
      M.smear a f 0 (x.1 (M.order a)) := by
  change M.evaluation (M.smearFamily a f (M.domainEquiv.symm (M.domainEquiv x))) = _
  rw [M.domainEquiv.symm_apply_apply]
  rfl

private theorem extended_mode_pairing (a : Charge M.D) (m : ℤ)
    (x : M.Sobolev (M.order a)) (y : M.Sobolev (M.order (-a))) :
    ⟪M.modeExtension a 0 m x, M.inclusion 0 (M.order (-a)) (Nat.zero_le _) y⟫_ℂ =
      ⟪M.inclusion 0 (M.order a) (Nat.zero_le _) x,
        M.eta a • M.modeExtension (-a) 0 (-m) y⟫_ℂ := by
  refine (embed_dense M _).induction_on x ?_ ?_
  · exact isClosed_eq
      ((M.modeExtension a 0 m).continuous.inner continuous_const)
      ((M.inclusion 0 (M.order a) (Nat.zero_le _)).continuous.inner continuous_const)
  · intro u
    refine (embed_dense M _).induction_on y ?_ ?_
    · exact isClosed_eq
        (continuous_const.inner
          (M.inclusion 0 (M.order (-a)) (Nat.zero_le _)).continuous)
        (continuous_const.inner
          ((M.modeExtension (-a) 0 (-m)).continuous.const_smul (M.eta a)))
    · intro v
      have hmode := modeExtension_embed M a 0 m u
      have hopp := modeExtension_embed M (-a) 0 (-m) v
      simp only [Nat.add_zero] at hmode hopp
      rw [hmode, hopp, inclusion_embed, inclusion_embed,
        ← (M.embed 0).map_smul, embed_inner, embed_inner]
      have hn : chargeEnergy M.D (-a) = chargeEnergy M.D a := by
        simp only [chargeEnergy, bilinear_neg_neg]
      simpa only [mode, eta, hn] using Hm_charged_circle a m u v

private theorem family_mode_pairing (a : Charge M.D) (m : ℤ) (x y : M.Smooth) :
    ⟪M.modeExtension a 0 m (x.1 (M.order a)), M.evaluation y⟫_ℂ =
      ⟪M.evaluation x, M.eta a •
        M.modeExtension (-a) 0 (-m) (y.1 (M.order (-a)))⟫_ℂ := by
  have hh := extended_mode_pairing M a m (x.1 _) (y.1 _)
  rw [x.2 0 _ (Nat.zero_le _), y.2 0 _ (Nat.zero_le _)] at hh
  exact hh

private theorem family_smear_pairing (a : Charge M.D) (f : Test) (x y : M.Smooth) :
    ⟪M.evaluation (M.smearFamily a f x), M.evaluation y⟫_ℂ =
      ⟪M.evaluation x, M.eta a • M.evaluation (M.smearFamily (-a) f.conjugate y)⟫_ℂ := by
  change ⟪M.smear a f 0 (x.1 _), M.evaluation y⟫_ℂ =
    ⟪M.evaluation x, M.eta a • M.smear (-a) f.conjugate 0 (y.1 _)⟫_ℂ
  have hleft := (innerSLFlip ℂ (M.evaluation y)).map_tsum
    (vector_summable M a f 0 (x.1 (M.order a+0)))
  have hright := (innerSL ℂ (M.evaluation x)).map_tsum
    (vector_summable M (-a) f.conjugate 0 (y.1 (M.order (-a)+0)))
  simp only [innerSLFlip_apply_apply] at hleft
  simp only [innerSL_apply_apply] at hright
  rw [smear_apply, inner_smul_right, smear_apply, hleft, hright]
  change (∑' m : ℤ, ⟪f.coefficient m • M.modeExtension a 0 m (x.1 _), M.evaluation y⟫_ℂ) = _
  rw [← tsum_mul_left]
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun n => M.eta a * ⟪M.evaluation x,
      f.conjugate.coefficient n • M.modeExtension (-a) 0 n (y.1 _)⟫_ℂ)]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply, inner_smul_left, inner_smul_right,
    coefficient_conjugate, neg_neg]
  simp only [Nat.add_zero]
  rw [family_mode_pairing, inner_smul_right]
  ring

private theorem field_formal (a : Charge M.D) (f : Test) :
    (M.field a f).IsFormalAdjoint (M.opposite a f) := by
  intro u v
  let x := M.domainEquiv.symm u
  let y := M.domainEquiv.symm v
  have hu : M.domainEquiv x = u := M.domainEquiv.apply_symm_apply u
  have hv : M.domainEquiv y = v := M.domainEquiv.apply_symm_apply v
  have hu0 : (u : M.Hilbert) = M.evaluation x := (congrArg Subtype.val hu).symm
  have hv0 : (v : M.Hilbert) = M.evaluation y := (congrArg Subtype.val hv).symm
  change ⟪M.field a f u, (v : M.Hilbert)⟫_ℂ =
    ⟪(u : M.Hilbert), M.eta a • M.field (-a) f.conjugate v⟫_ℂ
  rw [← hu, ← hv, field_eval, field_eval]
  exact family_smear_pairing M a f x y

private theorem field_le_opposite_adjoint (a : Charge M.D) (f : Test) :
    M.field a f ≤ (M.opposite a f).adjoint :=
  (field_formal M a f).symm.le_adjoint (smoothDomain_dense M)

private theorem field_closable (a : Charge M.D) (f : Test) :
    (M.field a f).IsClosable :=
  (LinearPMap.adjoint_isClosed (T := M.opposite a f) (smoothDomain_dense M)).isClosable.leIsClosable
    (field_le_opposite_adjoint M a f)

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
