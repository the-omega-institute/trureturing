/- GID: D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/OrthogonalPointwiseStabilizers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Radical-free pointwise stabilizers are orthogonal quotient algebras. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19944
utility none: structural existence and Lie equivalences; no finite certificate or algorithm.
escape_witness: Stabilizer.quotientLieHom_surjective, Stabilizer.quotientKernel_nilpotent
  Stabilizer.nilpotent_of_triple_bracket_zero: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientKernel_nilpotent
  Stabilizer.stabilizer: proof_shape: bind-only; escape_witness: none;
    consumers: D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Blocks.nonzero_square_block_decomposition, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.assemble_mem_derivations, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.normalized_block_decomposition, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.productToDerivations, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.productToDerivations_injective, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.productToDerivations_surjective, D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.restrictBlock_mem_stabilizer, D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result, Stabilizer.orthAction, Stabilizer.orthAction_preserves_radical, Stabilizer.quotientAction, Stabilizer.quotientAction_injective, Stabilizer.quotientAction_skew, Stabilizer.quotientKernel_maps_into_W, Stabilizer.quotientKernel_nilpotent, Stabilizer.quotientLieHom, Stabilizer.quotientLieHom_surjective, Stabilizer.stabilizer_equiv_of_trivialRadical, Stabilizer.stabilizer_kernel_triple_zero, Stabilizer.stabilizer_maps_into_orthogonal
  Stabilizer.stabilizer_maps_into_orthogonal: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.orthAction, Stabilizer.stabilizer_kernel_triple_zero
  Stabilizer.stabilizer_kernel_triple_zero: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientKernel_nilpotent
  Stabilizer.quotientForm_symm: proof_shape: bind-only; escape_witness: none;
    consumers: D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result, Stabilizer.quotientForm_nondegenerate
  Stabilizer.quotientForm_nondegenerate: proof_shape: bind-only; escape_witness: none;
    consumers: D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result
  Stabilizer.orthRadical_eq_intersection: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientKernel_maps_into_W
  Stabilizer.orthAction: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.orthAction_preserves_radical, Stabilizer.quotientAction, Stabilizer.quotientKernel_maps_into_W, Stabilizer.quotientLieHom_surjective
  Stabilizer.orthAction_preserves_radical: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientAction
  Stabilizer.quotientAction: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientAction_injective, Stabilizer.quotientAction_skew, Stabilizer.quotientKernel_maps_into_W, Stabilizer.quotientKernel_nilpotent, Stabilizer.quotientLieHom, Stabilizer.quotientLieHom_surjective
  Stabilizer.quotientAction_skew: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientLieHom
  Stabilizer.quotientLieHom: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientLieHom_surjective, Stabilizer.stabilizer_equiv_of_trivialRadical
  Stabilizer.quotientKernel_maps_into_W: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientKernel_nilpotent
  Stabilizer.quotientKernel_nilpotent: proof_shape: content; escape_witness: Stabilizer.quotientKernel_nilpotent;
    consumers: Stabilizer.quotientAction_injective
  Stabilizer.quotientAction_injective: proof_shape: content; escape_witness: Stabilizer.quotientKernel_nilpotent;
    consumers: Stabilizer.stabilizer_equiv_of_trivialRadical
  Stabilizer.orthProjection: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.extendOrthogonal, Stabilizer.extendOrthogonal_on_image, Stabilizer.extendOrthogonal_skew, Stabilizer.orthProjection_leftInverse, Stabilizer.orthProjection_pairing, Stabilizer.orthProjection_zero, Stabilizer.quotientLieHom_surjective
  Stabilizer.orthProjection_pairing: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.extendOrthogonal_skew, Stabilizer.orthProjection_leftInverse, Stabilizer.orthProjection_zero
  Stabilizer.orthProjection_leftInverse: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.extendOrthogonal_on_image
  Stabilizer.orthProjection_zero: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientLieHom_surjective
  Stabilizer.extendOrthogonal: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.extendOrthogonal_on_image, Stabilizer.extendOrthogonal_skew, Stabilizer.quotientLieHom_surjective
  Stabilizer.extendOrthogonal_on_image: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientLieHom_surjective
  Stabilizer.extendOrthogonal_skew: proof_shape: bind-only; escape_witness: none;
    consumers: Stabilizer.quotientLieHom_surjective
  Stabilizer.quotientLieHom_surjective: proof_shape: content; escape_witness: Stabilizer.quotientLieHom_surjective;
    consumers: Stabilizer.stabilizer_equiv_of_trivialRadical
  Stabilizer.stabilizer_equiv_of_trivialRadical: proof_shape: content; escape_witness: Stabilizer.quotientKernel_nilpotent, Stabilizer.quotientLieHom_surjective;
    consumers: D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result
  NormalForm.standardForm_symm: proof_shape: bind-only; escape_witness: none;
    consumers: D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result, NormalForm.skewAdjoint_equiv_so
  NormalForm.standardForm_quadratic: proof_shape: bind-only; escape_witness: none;
    consumers: NormalForm.skewAdjoint_equiv_so
  NormalForm.standardSkewMatrixEquiv: proof_shape: bind-only; escape_witness: none;
    consumers: NormalForm.skewAdjoint_equiv_so
  NormalForm.skewAdjoint_equiv_so: proof_shape: bind-only; escape_witness: none;
    consumers: D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.result
-/

import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.Algebra.Lie.Classical


attribute [local instance] Classical.propDecidable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
private theorem nilpotent_of_triple_bracket_zero {L : Type*} [LieRing L] [LieAlgebra k L]
    (h : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = 0) : LieRing.IsNilpotent L := by
  apply LieModule.IsNilpotent.mk (R := k) (L := L) (M := L) (k := 2)
  simp only [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
  apply (LieSubmodule.lie_eq_bot_iff _ _).mpr
  intro x hx y hy
  have hy' : y ∈ (⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆ : LieIdeal k L).toSubmodule := hy
  clear hy
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at hy'
  induction hy' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, b, rfl⟩ := hz
      exact h x a.val b.val
  | zero => simp
  | add a b ha hb ia ib => simp [ia, ib]
  | smul c a ha ia => simp [ia]

variable (B : LinearMap.BilinForm k V) (W : Submodule k V)
def stabilizer : LieSubalgebra k (Module.End k V) where
  carrier := {f | f ∈ skewAdjointLieSubalgebra B ∧ ∀ w ∈ W, f w = 0}
  zero_mem' := ⟨(skewAdjointLieSubalgebra B).zero_mem, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfW⟩ ⟨hg, hgW⟩
    exact ⟨(skewAdjointLieSubalgebra B).add_mem hf hg, by intro w hw; simp only [LinearMap.add_apply, hfW w hw, hgW w hw, add_zero]⟩
  smul_mem' := by
    rintro c f ⟨hf, hfW⟩
    exact ⟨(skewAdjointLieSubalgebra B).smul_mem c hf, by intro w hw; simp only [LinearMap.smul_apply, hfW w hw, smul_zero]⟩
  lie_mem' := by
    rintro f g ⟨hf, hfW⟩ ⟨hg, hgW⟩
    refine ⟨(skewAdjointLieSubalgebra B).lie_mem hf hg, ?_⟩
    intro w hw
    simp [Ring.lie_def, Module.End.mul_apply, hfW w hw, hgW w hw]
private theorem stabilizer_maps_into_orthogonal (f : stabilizer B W) (v : V) :
    f.val v ∈ B.orthogonal W := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  have hf : B.IsSkewAdjoint f.val :=
    (LinearMap.mem_skewAdjointSubmodule (B := B) f.val).mp f.property.1
  simpa [f.property.2 w hw] using (hf w v).symm
private theorem stabilizer_kernel_triple_zero
    (f g h : stabilizer B W)
    (hg : ∀ v ∈ B.orthogonal W, g.val v ∈ W)
    :
    f.val * g.val * h.val = 0 := by
  ext v
  exact f.property.2 (g.val (h.val v))
    (hg (h.val v) (stabilizer_maps_into_orthogonal B W h v))

variable (hB : B.IsSymm)
theorem quotientForm_symm : LinearMap.BilinForm.IsSymm ((LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl)) := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y => exact hB.eq x.val y.val
theorem quotientForm_nondegenerate : LinearMap.BilinForm.Nondegenerate ((LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl)) := by
  change LinearMap.Nondegenerate ((LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl))
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (quotientForm_symm B W hB).isRefl]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (B.restrict (B.orthogonal W)) x = 0
    ext y
    exact hx (Submodule.Quotient.mk y)

include hB in
private theorem orthRadical_eq_intersection [FiniteDimensional k V] (hND : B.Nondegenerate) :
    (LinearMap.ker (B.restrict (B.orthogonal W))) = (W ⊓ B.orthogonal W).comap (B.orthogonal W).subtype := by
  ext u
  constructor
  · intro hu
    have hz : ∀ v : B.orthogonal W, B u.val v.val = 0 := by
      intro v
      exact LinearMap.congr_fun hu v
    have ho : u.val ∈ B.orthogonal (B.orthogonal W) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      rw [hB.eq]
      exact hz ⟨v, hv⟩
    rw [B.orthogonal_orthogonal hND hB.isRefl W] at ho
    exact ⟨ho, u.property⟩
  · rintro ⟨huW, huU⟩
    change (B.restrict (B.orthogonal W)) u = 0
    ext v
    change B u.val v.val = 0
    exact v.property u.val huW
private def orthAction : stabilizer B W →ₗ⁅k⁆ Module.End k (B.orthogonal W) where
  toFun f := f.val.restrict (fun v _ => stabilizer_maps_into_orthogonal B W f v)
  map_add' := by intro f g; ext v; rfl
  map_smul' := by intro c f; ext v; rfl
  map_lie' := by intro f g; ext v; rfl
private theorem orthAction_preserves_radical (f : stabilizer B W)
    (u : B.orthogonal W) (hu : u ∈ (LinearMap.ker (B.restrict (B.orthogonal W)))) :
    orthAction B W f u ∈ (LinearMap.ker (B.restrict (B.orthogonal W))) := by
  change (B.restrict (B.orthogonal W)) (orthAction B W f u) = 0
  ext v
  have hf : B.IsSkewAdjoint f.val :=
    (LinearMap.mem_skewAdjointSubmodule (B := B) f.val).mp f.property.1
  have hz : B u.val ((orthAction B W f v).val) = 0 :=
    LinearMap.congr_fun hu (orthAction B W f v)
  change B (f.val u.val) v.val = 0
  change B u.val (f.val v.val) = 0 at hz
  rw [hf u.val v.val]
  change B u.val (-(f.val v.val)) = 0
  rw [map_neg, hz, neg_zero]
private def quotientAction : stabilizer B W →ₗ⁅k⁆
    Module.End k ((B.orthogonal W) ⧸ (LinearMap.ker (B.restrict (B.orthogonal W)))) where
  toFun f := ((LinearMap.ker (B.restrict (B.orthogonal W)))).mapQ ((LinearMap.ker (B.restrict (B.orthogonal W)))) (orthAction B W f)
    (fun u hu => orthAction_preserves_radical B W f u hu)
  map_add' := by
    intro f g
    ext u
    rfl
  map_smul' := by
    intro c f
    ext u
    rfl
  map_lie' := by
    intro f g
    ext u
    rfl
private theorem quotientAction_skew (f : stabilizer B W) :
    ((LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl)).IsSkewAdjoint (quotientAction B W f) := by
  intro u v
  induction u using Submodule.Quotient.induction_on with
  | _ u =>
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      have hf : B.IsSkewAdjoint f.val :=
        (LinearMap.mem_skewAdjointSubmodule (B := B) f.val).mp f.property.1
      exact hf u.val v.val
private def quotientLieHom : stabilizer B W →ₗ⁅k⁆
    skewAdjointLieSubalgebra ((LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl)) :=
  { (quotientAction B W).toLinearMap.codRestrict
      (skewAdjointLieSubalgebra ((LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl))).toSubmodule
      (fun f => (LinearMap.mem_skewAdjointSubmodule _).mpr
        (quotientAction_skew B W hB f)) with
    map_lie' := fun {f g} => Subtype.ext ((quotientAction B W).map_lie f g) }

include hB in
private theorem quotientKernel_maps_into_W [FiniteDimensional k V] (hND : B.Nondegenerate)
    (f : (quotientAction B W).ker) (u : B.orthogonal W) : f.val.val u.val ∈ W := by
  have hf := LieHom.mem_ker.mp f.property
  have hz : quotientAction B W f.val (Submodule.Quotient.mk u) = 0 := by rw [hf]; rfl
  have hu : orthAction B W f.val u ∈ (LinearMap.ker (B.restrict (B.orthogonal W))) :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  have hu' := (orthRadical_eq_intersection B W hB hND).le hu
  exact hu'.1

include hB in
private theorem quotientKernel_nilpotent [FiniteDimensional k V] (hND : B.Nondegenerate) :
    LieRing.IsNilpotent (quotientAction B W).ker := by
  apply nilpotent_of_triple_bracket_zero (k := k)
  have hc (f g h : (quotientAction B W).ker) : f.val.val * g.val.val * h.val.val = 0 :=
    stabilizer_kernel_triple_zero B W f.val g.val h.val
      (fun u hu => quotientKernel_maps_into_W B W hB hND g ⟨u, hu⟩)
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  change ⁅f.val.val, ⁅g.val.val, h.val.val⁆⁆ = 0
  simp only [Ring.lie_def, mul_sub, sub_mul, ← mul_assoc, hc, sub_self]

include hB in
private theorem quotientAction_injective [FiniteDimensional k V] (hND : B.Nondegenerate)
    [LieAlgebra.HasTrivialRadical k (stabilizer B W)] :
    Function.Injective (quotientAction B W) := by
  haveI : LieRing.IsNilpotent (quotientAction B W).ker := quotientKernel_nilpotent B W hB hND
  apply (quotientAction B W).ker_eq_bot.mp
  exact LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable _

section OrthogonalProjection
variable {E : Type*} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable (i : E →ₗ[k] V) (hC : (B.compl₁₂ i i).Nondegenerate)

private noncomputable def orthProjection : V →ₗ[k] E :=
  (LinearMap.BilinForm.toDual (B.compl₁₂ i i) hC).symm.toLinearMap.comp (B.compl₂ i)
private theorem orthProjection_pairing (v : V) (e : E) :
    B (i (orthProjection B i hC v)) (i e) = B v (i e) := by
  exact LinearMap.BilinForm.apply_toDual_symm_apply (B := B.compl₁₂ i i) (hB := hC) ((B.compl₂ i) v) e
private theorem orthProjection_leftInverse : Function.LeftInverse (orthProjection B i hC) i := by
  intro e
  apply (LinearMap.BilinForm.toDual (B.compl₁₂ i i) hC).injective
  ext z
  exact orthProjection_pairing B i hC (i e) z
private theorem orthProjection_zero (v : V) (hv : ∀ e, B v (i e) = 0) :
    orthProjection B i hC v = 0 := by
  apply (LinearMap.BilinForm.toDual (B.compl₁₂ i i) hC).injective
  ext z
  change B (i (orthProjection B i hC v)) (i z) = B (i 0) (i z)
  simpa only [map_zero, LinearMap.zero_apply] using (orthProjection_pairing B i hC v z).trans (hv z)

private noncomputable def extendOrthogonal (f : Module.End k E) : Module.End k V :=
  i.comp (f.comp (orthProjection B i hC))
private theorem extendOrthogonal_on_image (f : Module.End k E) (e : E) :
    extendOrthogonal B i hC f (i e) = i (f e) := by
  simp only [extendOrthogonal, LinearMap.comp_apply, orthProjection_leftInverse B i hC e]

include hB in
private theorem extendOrthogonal_skew (f : Module.End k E)
    (hf : (B.compl₁₂ i i).IsSkewAdjoint f) :
    B.IsSkewAdjoint (extendOrthogonal B i hC f) := by
  have hi (a : E) (v : V) :
      B (i a) v = B (i a) (i (orthProjection B i hC v)) := by
    calc
      B (i a) v = B v (i a) := hB.eq _ _
      _ = B (i (orthProjection B i hC v)) (i a) :=
        (orthProjection_pairing B i hC v a).symm
      _ = B (i a) (i (orthProjection B i hC v)) := hB.eq _ _
  intro v w
  change B (i (f (orthProjection B i hC v))) w = B v (-(i (f (orthProjection B i hC w))))
  calc
    B (i (f (orthProjection B i hC v))) w =
        (B.compl₁₂ i i) (f (orthProjection B i hC v)) (orthProjection B i hC w) := hi _ _
    _ = (B.compl₁₂ i i) (orthProjection B i hC v) ((-f) (orthProjection B i hC w)) := hf _ _
    _ = B v (-(i (f (orthProjection B i hC w)))) := by
      simpa only [LinearMap.neg_apply, LinearMap.compl₁₂_apply, map_neg] using
        congrArg Neg.neg (orthProjection_pairing B i hC v (f (orthProjection B i hC w)))
end OrthogonalProjection
private theorem quotientLieHom_surjective [FiniteDimensional k V] :
    Function.Surjective (quotientLieHom B W hB) := by
  classical
  intro F
  obtain ⟨E, hE⟩ := Submodule.exists_isCompl ((LinearMap.ker (B.restrict (B.orthogonal W))))
  let eQ : E ≃ₗ[k] ((B.orthogonal W) ⧸ (LinearMap.ker (B.restrict (B.orthogonal W)))) :=
    (((LinearMap.ker (B.restrict (B.orthogonal W)))).quotientEquivOfIsCompl E hE).symm
  let i : E →ₗ[k] V := (B.orthogonal W).subtype.comp E.subtype
  have hC : (B.compl₁₂ i i).Nondegenerate :=
    LinearMap.IsSymm.nondegenerate_restrict_of_isCompl_ker
      (⟨fun x y => hB.eq x.val y.val⟩ : LinearMap.IsSymm (B.restrict (B.orthogonal W))) hE.symm
  have he (a b : E) : (LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl) (eQ a) (eQ b) = (B.compl₁₂ i i) a b := by rfl
  let fE : Module.End k E := eQ.symm.conj F.val
  have hfE : (B.compl₁₂ i i).IsSkewAdjoint fE := by
    intro a b
    rw [← he, ← he]
    have hF : ((LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl)).IsSkewAdjoint F.val :=
      (LinearMap.mem_skewAdjointSubmodule _).mp F.property
    change (LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl) (eQ (eQ.symm (F.val (eQ a)))) (eQ b) =
      (LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl) (eQ a) (-eQ (eQ.symm (F.val (eQ b))))
    simpa only [eQ.apply_symm_apply, Pi.neg_apply, map_neg] using hF (eQ a) (eQ b)
  let g : Module.End k V := extendOrthogonal B i hC fE
  have hg : g ∈ stabilizer B W := by
    refine ⟨(LinearMap.mem_skewAdjointSubmodule (B := B) g).mpr
      (extendOrthogonal_skew B hB i hC fE hfE), ?_⟩
    intro w hw
    have hp : orthProjection B i hC w = 0 :=
      orthProjection_zero B i hC w (fun a => a.val.property w hw)
    change i (fE (orthProjection B i hC w)) = 0
    simp only [hp, map_zero]
  let fg : stabilizer B W := ⟨g, hg⟩
  refine ⟨fg, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro q
  obtain ⟨e, rfl⟩ := eQ.surjective q
  change quotientAction B W fg (eQ e) = F.val (eQ e)
  calc
    quotientAction B W fg (eQ e) = eQ (fE e) := by
      change (Submodule.Quotient.mk (orthAction B W fg e.val) :
        (B.orthogonal W) ⧸ (LinearMap.ker (B.restrict (B.orthogonal W)))) = Submodule.Quotient.mk (fE e).val
      apply congrArg (fun u : B.orthogonal W =>
        (Submodule.Quotient.mk u : (B.orthogonal W) ⧸ (LinearMap.ker (B.restrict (B.orthogonal W)))))
      apply Subtype.ext
      exact extendOrthogonal_on_image B i hC fE e
    _ = F.val (eQ e) := by
      change eQ (eQ.symm (F.val (eQ e))) = F.val (eQ e)
      exact eQ.apply_symm_apply _
theorem stabilizer_equiv_of_trivialRadical [FiniteDimensional k V] (hND : B.Nondegenerate)
    [LieAlgebra.HasTrivialRadical k (stabilizer B W)] :
    Nonempty (stabilizer B W ≃ₗ⁅k⁆ skewAdjointLieSubalgebra ((LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W)) (LinearMap.ker (B.restrict (B.orthogonal W))) (fun x y => hB.isRefl x.val y.val) le_rfl))) := by
  refine ⟨LieEquiv.ofBijective (quotientLieHom B W hB) ⟨?_, quotientLieHom_surjective B W hB⟩⟩
  intro f g hfg
  apply quotientAction_injective B W hB hND
  exact congrArg Subtype.val hfg

end D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer

namespace D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm
attribute [local instance 100] LieRing.ofAssociativeRing
open QuadraticMap
variable {k : Type*} [Field k]
theorem standardForm_symm (n : Type*) [Fintype n] [DecidableEq n] :
    LinearMap.BilinForm.IsSymm (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix n n k)) := by
  constructor
  intro x y
  simp only [Matrix.toLinearMap₂'_apply', Matrix.one_mulVec, RingHom.id_apply]
  exact dotProduct_comm x y
private theorem standardForm_quadratic (n : Type*) [Fintype n] [DecidableEq n] :
    LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix n n k)) = QuadraticMap.weightedSumSquares k (1 : n → k) := by
  ext x
  simp [LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct]

private noncomputable def standardSkewMatrixEquiv (n : Type*) [Fintype n] [DecidableEq n] :
    skewAdjointLieSubalgebra (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix n n k) : LinearMap.BilinForm k (n → k)) ≃ₗ⁅k⁆ LieAlgebra.Orthogonal.so n k := by
  apply LieEquiv.ofSubalgebras _ _ lieEquivMatrix'
  ext A
  rw [LieSubalgebra.mem_map_submodule, Submodule.mem_map_equiv]
  change Matrix.toLin' A ∈ (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix n n k) : LinearMap.BilinForm k (n → k)).skewAdjointSubmodule ↔
    A ∈ skewAdjointMatricesSubmodule (1 : Matrix n n k)
  rw [LinearMap.mem_skewAdjointSubmodule, mem_skewAdjointMatricesSubmodule]
  change LinearMap.IsAdjointPair (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix n n k) : LinearMap.BilinForm k (n → k)) (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix n n k) : LinearMap.BilinForm k (n → k))
    (Matrix.toLin' A) (-(Matrix.toLin' A)) ↔ Matrix.IsAdjointPair 1 1 A (-A)
  have hneg : -(Matrix.toLin' A) = Matrix.toLin' (-A) := (map_neg Matrix.toLin' A).symm
  have hnegf : (-⇑(Matrix.toLin' A) : (n → k) → (n → k)) = ⇑(Matrix.toLin' (-A)) := by
    funext x
    exact congrArg (fun f : Module.End k (n → k) => f x) hneg
  rw [hnegf]
  exact isAdjointPair_toLinearMap₂' 1 1 A (-A)

variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
theorem skewAdjoint_equiv_so [IsAlgClosed k] [CharZero k]
    (B : LinearMap.BilinForm k V) (hB : B.IsSymm) (hND : B.Nondegenerate) :
    Nonempty (skewAdjointLieSubalgebra B ≃ₗ⁅k⁆
      LieAlgebra.Orthogonal.so (Fin (Module.finrank k V)) k) := by
  letI : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  have hassoc : QuadraticMap.associated B.toQuadraticMap = B :=
    QuadraticMap.associated_left_inverse k hB.eq
  obtain ⟨e⟩ := QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed B.toQuadraticMap
    (by simpa only [hassoc] using hND.1)
  have hstdassoc : QuadraticMap.associated
      (QuadraticMap.weightedSumSquares k (1 : Fin (Module.finrank k V) → k)) =
      (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k)) := by
    rw [← standardForm_quadratic]
    exact QuadraticMap.associated_left_inverse k (standardForm_symm _).eq
  have hcomp : (QuadraticMap.weightedSumSquares k (1 : Fin (Module.finrank k V) → k)).comp
      e.toLinearEquiv.toLinearMap = B.toQuadraticMap := by
    ext x
    exact e.map_app x
  have hbilin : ((Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k))).compl₁₂
      e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap = B := by
    have hh := congrArg (QuadraticMap.associatedHom k) hcomp
    rw [QuadraticMap.associated_comp, hstdassoc, hassoc] at hh
    exact hh
  have eLie := skewAdjointLieSubalgebraEquiv
    ((Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k))) e.toLinearEquiv
  rw [hbilin] at eLie
  exact ⟨eLie.trans (standardSkewMatrixEquiv _)⟩

end D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm
