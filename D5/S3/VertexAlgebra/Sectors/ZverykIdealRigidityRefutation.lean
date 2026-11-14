/- GID: D5/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Virasoro and Borcherds presentation, action, and ideal structure. -/

/-
admission_basis: open-problem-resolution (#27461; Refuted)
escape_witness: none (settling result)
Direct frozen dependencies: D5/S1/Words/WeakShuffleNormalization.diagonal,
through VBKMRecursiveAction.cartan; the public owner awaits canonical re-pinning.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30339
Definitions are labelled bind-only as encodings, not as proofs of new propositions.
Declarations (consumer names are qualified by their owning module):
D: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.D_single, ZverykIdealRigidityRefutation.D_bracket, ZverykIdealRigidityRefutation.op, ZverykIdealRigidityRefutation.op_bracket, ZverykIdealRigidityRefutation.evaluation_ad_vacuum, ZverykIdealRigidityRefutation.singular_detected.
D_single: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.D_bracket, ZverykIdealRigidityRefutation.singular_detected.
D_bracket: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.op_bracket.
op: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.op_bracket, ZverykIdealRigidityRefutation.evaluation, ZverykIdealRigidityRefutation.evaluation_basis, ZverykIdealRigidityRefutation.evaluation_prepend, ZverykIdealRigidityRefutation.evaluation_relation, ZverykIdealRigidityRefutation.N_le_kernel, ZverykIdealRigidityRefutation.evaluation_adMode, ZverykIdealRigidityRefutation.evaluation_ad_vacuum, ZverykIdealRigidityRefutation.singular_detected.
op_bracket: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.evaluation_relation.
evaluation: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.evaluation_basis, ZverykIdealRigidityRefutation.evaluation_prepend, ZverykIdealRigidityRefutation.evaluation_relation, ZverykIdealRigidityRefutation.N_le_kernel, ZverykIdealRigidityRefutation.evaluation_adMode, ZverykIdealRigidityRefutation.evaluation_ad_vacuum, ZverykIdealRigidityRefutation.singular_detected, ZverykIdealRigidityRefutation.singular_not_mem.
evaluation_basis: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.evaluation_relation, ZverykIdealRigidityRefutation.singular_detected.
evaluation_prepend: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.N_le_kernel.
evaluation_relation: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.N_le_kernel.
N_le_kernel: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.singular_not_mem.
adMode: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.evaluation_adMode, ZverykIdealRigidityRefutation.evaluation_ad_vacuum, ZverykIdealRigidityRefutation.singular, ZverykIdealRigidityRefutation.singular_detected, ZverykIdealRigidityRefutation.representation_singular_vacuum.
evaluation_adMode: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.evaluation_ad_vacuum.
vacuum: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.evaluation_ad_vacuum, ZverykIdealRigidityRefutation.singular_detected, ZverykIdealRigidityRefutation.singular_not_mem.
evaluation_ad_vacuum: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.singular_detected.
singular: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.singular_detected, ZverykIdealRigidityRefutation.singular_not_mem, ZverykIdealRigidityRefutation.representation_singular_vacuum, ZverykIdealRigidityRefutation.presentedSingular_ne_zero.
singular_detected: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.singular_not_mem.
singular_not_mem: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presentedSingular_ne_zero.
localH: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest.
localE: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest, ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest.
localF: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.local_sl2_relations, ZverykIdealRigidityRefutation.rankOne_in_span, ZverykIdealRigidityRefutation.datum_no_rank_highest.
local_sl2_relations: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.datum_no_rank_highest.
rankOne_in_span: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.datum_no_rank_highest.
datum_no_rank_highest: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: ZverykIdealRigidityRefutation.datum_cross_no_highest, ZverykIdealRigidityRefutation.datum_mode_no_highest.
datum_cross_no_highest: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: ZverykIdealRigidityRefutation.datum_localRelations_empty.
datum_mode_no_highest: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: ZverykIdealRigidityRefutation.datum_localRelations_empty.
datum_localRelations_empty: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: ZverykIdealRigidityRefutation.datum_localIdeal_zero.
datum_localIdeal_zero: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: ZverykIdealRigidityRefutation.localQuotientMap_injective.
presentedSingular: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_positive_singular, ZverykIdealRigidityRefutation.presented_e_singular, ZverykIdealRigidityRefutation.presented_singular_eigen, ZverykIdealRigidityRefutation.presented_separating_weight, ZverykIdealRigidityRefutation.cartan_singular, ZverykIdealRigidityRefutation.positive_singular, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives, ZverykIdealRigidityRefutation.not_rigid_of_survival, ZverykIdealRigidityRefutation.result_of_survival, ZverykIdealRigidityRefutation.representation_singular_vacuum, ZverykIdealRigidityRefutation.presentedSingular_ne_zero.
presented_seed_zero_weight: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_positive_singular.
presented_positive_seed: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_positive_singular.
presented_central_seed: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_positive_singular.
presented_central_modes: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_positive_singular.
presented_positive_singular: proof_shape: content; frozen: none; escape_witness: VBKMSingularVector.positive_modes_kill; consumers: ZverykIdealRigidityRefutation.positive_singular.
presented_e_singular: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.positive_singular.
presented_singular_eigen: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presented_separating_weight, ZverykIdealRigidityRefutation.cartan_singular.
presented_separating_weight: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
negativeGenerator: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.allGenerators, ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.mixedSpan, ZverykIdealRigidityRefutation.generators_in_mixedSpan, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
positiveGenerator: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.allGenerators, ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.mixedSpan, ZverykIdealRigidityRefutation.generators_in_mixedSpan, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.positive_singular, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
cartanGenerators: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.allGenerators, ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.cartan_negative, ZverykIdealRigidityRefutation.cartan_singular, ZverykIdealRigidityRefutation.mixedSpan, ZverykIdealRigidityRefutation.generators_in_mixedSpan, ZverykIdealRigidityRefutation.mixed_positive_negative, ZverykIdealRigidityRefutation.separating_cartan, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives, ZverykIdealRigidityRefutation.cartan_map, ZverykIdealRigidityRefutation.not_rigid_of_survival.
allGenerators: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.mode_mem_generators, ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.generators_in_mixedSpan.
mode_mem_generators: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.allGenerators_generate, ZverykIdealRigidityRefutation.mixed_positive_negative.
allGenerators_generate: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
cartan_negative: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
cartan_singular: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
mixedSpan: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.generators_in_mixedSpan, ZverykIdealRigidityRefutation.mixed_positive_negative.
generators_in_mixedSpan: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.mixed_positive_negative.
mixed_positive_negative: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
positive_singular: proof_shape: content; frozen: none; escape_witness: VBKMSingularVector.positive_modes_kill; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
negativeWeight: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.negative_weights_positive, ZverykIdealRigidityRefutation.separating_negative, ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
negative_weights_positive: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
separating_negative: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
separating_cartan: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.ideal_exists_of_singular_survives.
ideal_exists_of_singular_survives: proof_shape: content; frozen: none; escape_witness: VBKMWeightIdeal.positive_stable; consumers: ZverykIdealRigidityRefutation.not_rigid_of_survival.
localQuotientMap: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.localQuotientMap_surjective, ZverykIdealRigidityRefutation.localQuotientMap_injective, ZverykIdealRigidityRefutation.cartan_map, ZverykIdealRigidityRefutation.not_rigid_of_survival.
localQuotientMap_surjective: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.not_rigid_of_survival.
localQuotientMap_injective: proof_shape: content; frozen: none; escape_witness: VBKMPrimitiveKernel.raising_kernel_on_span; consumers: ZverykIdealRigidityRefutation.not_rigid_of_survival.
cartan_map: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.not_rigid_of_survival.
not_rigid_of_survival: proof_shape: content; frozen: none; escape_witness: VBKMWeightIdeal.positive_stable; consumers: ZverykIdealRigidityRefutation.result_of_survival.
result_of_survival: proof_shape: content; frozen: none; escape_witness: VBKMWeightIdeal.positive_stable; consumers: ZverykIdealRigidityRefutation.result.
representationGenerator: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.freeRepresentation, ZverykIdealRigidityRefutation.freeRepresentation_h, ZverykIdealRigidityRefutation.freeRepresentation_e, ZverykIdealRigidityRefutation.freeRepresentation_f, ZverykIdealRigidityRefutation.freeRepresentation_L.
freeRepresentation: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.freeRepresentation_h, ZverykIdealRigidityRefutation.freeRepresentation_e, ZverykIdealRigidityRefutation.freeRepresentation_f, ZverykIdealRigidityRefutation.freeRepresentation_L, ZverykIdealRigidityRefutation.freeRepresentation_relations, ZverykIdealRigidityRefutation.presentationIdeal_le_representation_kernel, ZverykIdealRigidityRefutation.representation.
freeRepresentation_h: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.freeRepresentation_relations.
freeRepresentation_e: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.freeRepresentation_relations.
freeRepresentation_f: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.freeRepresentation_relations, ZverykIdealRigidityRefutation.representation_pf.
freeRepresentation_L: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.freeRepresentation_relations, ZverykIdealRigidityRefutation.representation_pL.
freeRepresentation_relations: proof_shape: content; frozen: none; escape_witness: VBKMVirasoroBootstrap.positive_brackets_from_mixed; consumers: ZverykIdealRigidityRefutation.presentationIdeal_le_representation_kernel.
presentationIdeal_le_representation_kernel: proof_shape: content; frozen: none; escape_witness: VBKMVirasoroBootstrap.positive_brackets_from_mixed; consumers: ZverykIdealRigidityRefutation.representation.
representation: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.representation_pf, ZverykIdealRigidityRefutation.representation_pL, ZverykIdealRigidityRefutation.representation_singular_vacuum, ZverykIdealRigidityRefutation.presentedSingular_ne_zero.
representation_pf: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.representation_singular_vacuum.
representation_pL: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.representation_singular_vacuum.
representation_singular_vacuum: proof_shape: bind-only; frozen: none; escape_witness: none; consumers: ZverykIdealRigidityRefutation.presentedSingular_ne_zero.
presentedSingular_ne_zero: proof_shape: content; frozen: none; escape_witness: ZverykIdealRigidityRefutation.presentedSingular_ne_zero; consumers: ZverykIdealRigidityRefutation.result.
result: proof_shape: content; frozen: none; escape_witness: ZverykIdealRigidityRefutation.presentedSingular_ne_zero; consumers: terminal result.
-/

import D5.S3.VertexAlgebra.Sectors.VBKMPresentation
import D5.S3.VertexAlgebra.Sectors.VBKMPrimitiveKernel
import D5.S3.VertexAlgebra.Sectors.VBKMSingularVector
import D5.S3.VertexAlgebra.Sectors.VBKMWeightIdeal
import D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] LieRing.ofAssociativeRing
universe u v
open D5.S3.VertexAlgebra.Sectors.VBKMPresentation
open D5.S3.VertexAlgebra.Sectors.VBKMPresentation.EnhancedCartanData
open D5.S3.VertexAlgebra.Sectors.VBKMSingularVector
open D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction
namespace D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation

private noncomputable def D (r : ℕ+) : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun n => -(n : ℂ) • Finsupp.single (n-r.val) 1)

private theorem D_single (r : ℕ+) (n : ℤ) (c : ℂ) :
    D r (Finsupp.single n c) = (-(n : ℂ)*c) • Finsupp.single (n-r.val) 1 := by
  simp [D,smul_smul,mul_comm]

private theorem D_bracket (r s : ℕ+) (x : (ℤ →₀ ℂ)) :
    D r (D s x) - D s (D r x) = ((s.val : ℂ)-(r.val : ℂ)) • D (r+s) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | single n c =>
    simp only [D_single,map_smul,smul_smul]
    have h1 : n-(s.val : ℤ)-(r.val : ℤ) = n-((r+s).val : ℤ) := by simp; omega
    have h2 : n-(r.val : ℤ)-(s.val : ℤ) = n-((r+s).val : ℤ) := by simp; omega
    rw [h1,h2]
    push_cast
    module
  | add x y hx hy =>
    convert congrArg₂ (fun a b : (ℤ →₀ ℂ) => a+b) hx hy using 1 <;>
      simp only [map_add,smul_add] <;> module

private noncomputable def op : (Bool ⊕ ℕ+) → Module.End ℂ (ℂ × (ℤ →₀ ℂ))
  | .inl true => (LinearMap.inr ℂ ℂ (ℤ →₀ ℂ)).comp
      ((LinearMap.fst ℂ ℂ (ℤ →₀ ℂ)).smulRight (Finsupp.single 1 1))
  | .inl false => 0
  | .inr r => (0 : ℂ →ₗ[ℂ] ℂ).prodMap (D r)

private theorem op_bracket (r s : ℕ+) (x : (ℂ × (ℤ →₀ ℂ))) :
    op (.inr r) (op (.inr s) x) - op (.inr s) (op (.inr r) x) =
      ((s.val : ℂ)-(r.val : ℂ)) • op (.inr (r+s)) x := by
  apply Prod.ext
  · simp [op]
  · change D r (D s x.2) - D s (D r x.2) = _
    exact D_bracket r s x.2

private noncomputable def evaluation : ((List (Bool ⊕ ℕ+)) →₀ ℂ) →ₗ[ℂ] Module.End ℂ (ℂ × (ℤ →₀ ℂ)) :=
  Finsupp.linearCombination ℂ (fun (w : List (Bool ⊕ ℕ+)) => (w.map op).prod)

private theorem evaluation_basis (w : (List (Bool ⊕ ℕ+))) : evaluation ((fun (w : List (Bool ⊕ ℕ+)) => Finsupp.single w (1 : ℂ)) w) = (fun (w : List (Bool ⊕ ℕ+)) => (w.map op).prod) w := by
  simp [evaluation]

private theorem evaluation_prepend (u : (List (Bool ⊕ ℕ+))) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    evaluation ((fun (u : List (Bool ⊕ ℕ+)) => Finsupp.lmapDomain ℂ ℂ (List.append u)) u x) = (fun (w : List (Bool ⊕ ℕ+)) => (w.map op).prod) u * evaluation x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | single w c => simp [evaluation,Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
  | add x y hx hy => simp only [map_add,hx,hy,mul_add]

private theorem evaluation_relation (r s : ℕ+) (v : (List (Bool ⊕ ℕ+))) :
    evaluation (relation r s v) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [relation,map_sub,map_smul,evaluation_basis,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,
    LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,LinearMap.zero_apply]
  exact sub_eq_zero.mpr (op_bracket r s ((fun (w : List (Bool ⊕ ℕ+)) => (w.map op).prod) v x))

private theorem N_le_kernel : N ≤ LinearMap.ker evaluation := by
  apply Submodule.span_le.mpr
  rintro x ⟨u,v,r,s,rfl⟩
  change evaluation ((fun (u : List (Bool ⊕ ℕ+)) => Finsupp.lmapDomain ℂ ℂ (List.append u)) u (relation r s v)) = 0
  rw [evaluation_prepend,evaluation_relation,mul_zero]

private noncomputable def adMode (r : ℕ+) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) : ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  (fun (g : Bool ⊕ ℕ+) => Finsupp.lmapDomain ℂ ℂ (List.cons g)) (.inr r) x - (fun (g : Bool ⊕ ℕ+) => Finsupp.lmapDomain ℂ ℂ (fun u => u ++ [g])) (.inr r) x

private theorem evaluation_adMode (r : ℕ+) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    evaluation (adMode r x) = op (.inr r) * evaluation x - evaluation x * op (.inr r) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [adMode] <;> module
  | single w c =>
    simp [adMode,evaluation,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,
      Algebra.smul_mul_assoc,Algebra.mul_smul_comm]
  | add x y hx hy =>
    convert congrArg₂ (fun a b : Module.End ℂ (ℂ × (ℤ →₀ ℂ)) => a+b) hx hy using 1 <;>
      simp only [adMode,map_add,map_sub,mul_add,add_mul] <;> module

private noncomputable def vacuum : (ℂ × (ℤ →₀ ℂ)) := (1,0)

private theorem evaluation_ad_vacuum (r : ℕ+) (x : ((List (Bool ⊕ ℕ+)) →₀ ℂ)) :
    evaluation (adMode r x) vacuum = op (.inr r) (evaluation x vacuum) := by
  rw [evaluation_adMode]
  simp [vacuum,op]
  change evaluation x (0 : (ℂ × (ℤ →₀ ℂ))) = 0
  exact map_zero _

private noncomputable def singular : ((List (Bool ⊕ ℕ+)) →₀ ℂ) :=
  adMode 1 (adMode 1 (adMode 1 (adMode 1 ((fun (w : List (Bool ⊕ ℕ+)) => Finsupp.single w (1 : ℂ)) [.inl true])))) -
  (3 : ℂ) • adMode 2 (adMode 1 (adMode 1 ((fun (w : List (Bool ⊕ ℕ+)) => Finsupp.single w (1 : ℂ)) [.inl true]))) -
  (7/4 : ℂ) • adMode 2 (adMode 2 ((fun (w : List (Bool ⊕ ℕ+)) => Finsupp.single w (1 : ℂ)) [.inl true])) +
  (3 : ℂ) • adMode 3 (adMode 1 ((fun (w : List (Bool ⊕ ℕ+)) => Finsupp.single w (1 : ℂ)) [.inl true])) +
  (3/2 : ℂ) • adMode 4 ((fun (w : List (Bool ⊕ ℕ+)) => Finsupp.single w (1 : ℂ)) [.inl true])

private theorem singular_detected : evaluation singular vacuum =
    (0,(1/4 : ℂ) • Finsupp.single (-3) 1) := by
  simp only [singular,map_add,map_sub,map_smul,LinearMap.add_apply,
    LinearMap.sub_apply,LinearMap.smul_apply,evaluation_ad_vacuum,
    evaluation_basis,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil]
  norm_num [op,vacuum,D_single,LinearMap.prodMap_apply,Prod.smul_mk,
    Prod.add_def,Prod.sub_def]
  ext n
  simp only [Finsupp.add_apply,Finsupp.neg_apply]
  by_cases hn : n = -3 <;> simp [Finsupp.single_apply,hn] <;> norm_num

private theorem singular_not_mem : singular ∉ N := by
  intro h
  have hz : evaluation singular = 0 := N_le_kernel h
  have hdet := singular_detected
  rw [hz,LinearMap.zero_apply] at hdet
  have hh := congrArg (fun x : (ℂ × (ℤ →₀ ℂ)) => x.2 (-3)) hdet
  norm_num at hh

end D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
namespace D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
open EnhancedCartanData
open D5.S3.VertexAlgebra.Sectors.VBKMPrimitiveKernel

private noncomputable def localH (side : Bool) (i : Bool) : Presented datum :=
  if side then -ph datum (datum.coroot i) else ph datum (datum.coroot i)
private noncomputable def localE (side : Bool) (i : Bool) : Presented datum :=
  sideSeed datum (!side) i
private noncomputable def localF (side : Bool) (i : Bool) : Presented datum :=
  sideSeed datum side i

private theorem local_sl2_relations (side i : Bool) :
    ⁅localE side i,localF side i⁆ = localH side i ∧
    ⁅localH side i,localE side i⁆ = datum.matrix i i • localE side i ∧
    ⁅localH side i,localF side i⁆ = -datum.matrix i i • localF side i := by
  cases side <;> simp only [localH,localE,localF,sideSeed,Bool.not_false,Bool.not_true,
    Bool.false_eq_true,ite_false,ite_true]
  · simp [pe_pf,ph_pe,ph_pf,matrix,neg_smul]
  · have hef : ⁅pf datum i,pe datum i⁆ = -ph datum (datum.coroot i) := by
      rw [← lie_skew,pe_pf,if_pos rfl]
    simp [hef,neg_lie,ph_pf,ph_pe,neg_neg,matrix,neg_smul]

private theorem rankOne_in_span (side i : Bool) :
    rankOne datum i ⊆ Submodule.span ℂ ({localE side i,localF side i,localH side i} : Set (Presented datum)) := by
  intro y hy
  cases side <;>
    simp only [rankOne,localE,localF,localH,sideSeed,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,ite_false,ite_true] at hy ⊢
  · exact Submodule.subset_span hy
  · rcases hy with rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · have hh0 : -ph datum (datum.coroot i) ∈ Submodule.span ℂ
          ({pf datum i,pe datum i,-ph datum (datum.coroot i)} : Set (Presented datum)) :=
        Submodule.subset_span (by simp)
      have hh := (Submodule.span ℂ ({pf datum i,pe datum i,-ph datum (datum.coroot i)} :
          Set (Presented datum))).neg_mem hh0
      simpa using hh

private theorem datum_no_rank_highest (side i : Bool) (w x : Presented datum) (b : ℂ)
    (hHw : ⁅localH side i,w⁆ = b • w) (hEw : ⁅localE side i,w⁆ = 0)
    (hμ : ∀ n : ℕ, (2/datum.matrix i i)*b ≠ (n : ℂ)) :
    ¬ HighestProper (rankOne datum i) {sideSeed datum (!side) i}
      {ph datum (datum.coroot i)} w x := by
  rintro ⟨hxne,hx,hEx,hDx,hlt⟩
  have ha : datum.matrix i i ≠ 0 := by cases i <;> norm_num [datum,matrix]
  obtain ⟨hef,hhe,hhf⟩ := local_sl2_relations side i
  have hEx' : ⁅localE side i,x⁆ = 0 := hEx _ (Set.mem_singleton _)
  have hh := normalized_not_proper (localH side i) (localE side i) (localF side i)
    (datum.matrix i i) b ha hef hhe hhf w x hHw hEw hμ (rankOne datum i)
    (rankOne_in_span side i) hx hEx' hxne
  exact hh hlt

private theorem datum_cross_no_highest (side i k : Bool) (hik : i ≠ k) (x : Presented datum) :
    ¬ HighestProper (rankOne datum i) {sideSeed datum (!side) i}
      {ph datum (datum.coroot i)} (sideSeed datum side k) x := by
  apply datum_no_rank_highest side i _ x (-datum.matrix i k)
  · cases side <;> simp [localH,sideSeed,ph_pf,ph_pe,neg_lie,neg_smul,matrix]
  · cases side
    · simp [localE,sideSeed,pe_pf,hik]
    · have hh : ⁅pe datum k,pf datum i⁆ = 0 := by simp [pe_pf,Ne.symm hik]
      have hh' : ⁅pf datum i,pe datum k⁆ = 0 := by rw [← lie_skew,hh,neg_zero]
      simpa [localE,sideSeed] using hh'
  · intro n hn
    have hh := congrArg Complex.re hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    cases i <;> cases k <;> norm_num [datum,matrix] at hh hik <;> linarith

private theorem datum_mode_no_highest (side i : Bool) (j : Unit) (n : ℤ) (hn : 0 < n)
    (x : Presented datum) :
    ¬ HighestProper (rankOne datum i) {sideSeed datum (!side) i}
      {ph datum (datum.coroot i)} (pL datum j (modeSign side*n)) x := by
  apply datum_no_rank_highest side i _ x ((n : ℂ)/3)
  · cases side <;> cases i <;> simp [localH,modeSign,ph_pL,neg_lie,datum]
    <;> push_cast <;> module
  · cases side
    · simpa [localE,sideSeed,modeSign] using pe_negative datum i j (-n) (by omega)
    · simpa [localE,sideSeed,modeSign] using pf_positive datum i j n hn
  · intro m hm
    have hh := congrArg Complex.re hm
    have hn' : (0 : ℝ) < n := by exact Int.cast_pos.mpr hn
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    cases i <;> norm_num [datum,matrix] at hh <;> nlinarith

private theorem datum_localRelations_empty : localRelations datum = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨side,h⟩
  rcases h with h | h | h | h
  · obtain ⟨i,k,hik,h⟩ := h
    exact datum_cross_no_highest side i k hik x h
  · obtain ⟨i,j,n,hn,h⟩ := h
    exact datum_mode_no_highest side i j n hn x h
  · obtain ⟨i,j,hc,hb,h⟩ := h
    cases i <;> norm_num [datum] at hc
  · obtain ⟨j,k,n,hjk,h⟩ := h
    exact hjk (Subsingleton.elim _ _)

private theorem datum_localIdeal_zero : localIdeal datum = ⊥ := by
  simp [localIdeal,datum_localRelations_empty]

end D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation


namespace D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
open EnhancedCartanData

private noncomputable def presentedSingular : Presented datum :=
  singularWord (pL datum ()) (pf datum true)

private theorem presented_seed_zero_weight :
    ⁅pL datum () 0,pf datum true⁆ = (-3/8 : ℂ) • pf datum true := by
  rw [pL_zero,ph_pf]
  norm_num [datum]

private theorem presented_positive_seed (n : ℤ) (hn : 0 < n) :
    ⁅pL datum () n,pf datum true⁆ = 0 := by
  rw [← lie_skew,pf_positive datum true () n hn,neg_zero]

private theorem presented_central_seed :
    ⁅ph datum (datum.central ()),pf datum true⁆ = (1/3 : ℂ) • pf datum true := by
  rw [ph_pf]
  norm_num [datum]

private theorem presented_central_modes (n : ℤ) :
    ⁅ph datum (datum.central ()),pL datum () n⁆ = 0 := by
  rw [ph_pL]
  norm_num [datum]

private theorem presented_positive_singular (n : ℤ) (hn : 0 < n) :
    ⁅pL datum () n,presentedSingular⁆ = 0 := by
  apply positive_modes_kill (pL datum ()) (ph datum (datum.central ())) presentedSingular
    (pL_commute datum ())
  · exact singularWord_mode_one (pL datum ()) (ph datum (datum.central ())) (pf datum true)
      (pL_commute datum ()) presented_seed_zero_weight (presented_positive_seed 1 (by norm_num))
  · exact singularWord_mode_two (pL datum ()) (ph datum (datum.central ())) (pf datum true)
      (pL_commute datum ()) presented_seed_zero_weight (presented_positive_seed 1 (by norm_num))
      (presented_positive_seed 2 (by norm_num)) presented_central_seed presented_central_modes
  · exact hn

set_option maxHeartbeats 2000000 in
private theorem presented_e_singular (i : Bool) : ⁅pe datum i,presentedSingular⁆ = 0 := by
  rw [presentedSingular,singularWord_commute (pL datum ()) (pe datum i) (pf datum true)
    (fun n hn => pe_negative datum i () n hn),pe_pf]
  cases i
  · simp [singularWord]
  · simp only [ite_true]
    apply singularWord_cartan (pL datum ()) (ph datum (datum.central ()))
      (ph datum (datum.coroot true)) (datum.pairing (datum.coroot true) (datum.virRoot ()))
    · intro r
      rw [← lie_skew,ph_pL]
      push_cast
      module
    · exact pL_commute datum ()

private theorem presented_singular_eigen (a : ℂ × ℂ) :
    ⁅ph datum a,presentedSingular⁆ =
      (-datum.pairing a (datum.root true)-4*datum.pairing a (datum.virRoot ())) • presentedSingular := by
  apply singularWord_eigen
  · exact fun n => ph_pL datum a () n
  · simpa [neg_smul] using ph_pf datum a true

private theorem presented_separating_weight :
    ⁅-ph datum (1,0),presentedSingular⁆ = (-8/3 : ℂ) • presentedSingular := by
  rw [neg_lie,presented_singular_eigen]
  norm_num [datum]

end D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation


namespace D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
open EnhancedCartanData D5.S3.VertexAlgebra.Sectors.VBKMWeightIdeal

private noncomputable def negativeGenerator : (Bool ⊕ ℕ+) → Presented datum
  | .inl i => pf datum i
  | .inr r => pL datum () (-(r.val : ℤ))
private noncomputable def positiveGenerator : (Bool ⊕ ℕ+) → Presented datum
  | .inl i => pe datum i
  | .inr r => pL datum () r.val
private noncomputable def cartanGenerators : Set (Presented datum) := Set.range (ph datum)
private noncomputable def allGenerators : Set (Presented datum) :=
  cartanGenerators ∪ Set.range negativeGenerator ∪ Set.range positiveGenerator

private theorem mode_mem_generators (n : ℤ) : pL datum () n ∈ allGenerators := by
  by_cases hn : n < 0
  · let r : ℕ+ := ⟨(-n).toNat,by omega⟩
    have hr : -(r.val : ℤ) = n := by
      dsimp [r]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    exact Or.inl (Or.inr ⟨Sum.inr r,by simp [negativeGenerator,hr]⟩)
  · by_cases hn0 : n = 0
    · subst n
      rw [pL_zero]
      exact Or.inl (Or.inl ⟨datum.degree (),rfl⟩)
    · let r : ℕ+ := ⟨n.toNat,by omega⟩
      have hr : (r.val : ℤ) = n := by dsimp [r];rw [Int.toNat_of_nonneg (by omega)]
      exact Or.inr ⟨Sum.inr r,by simp [positiveGenerator,hr]⟩

private theorem allGenerators_generate :
    LieSubalgebra.lieSpan ℂ (Presented datum) allGenerators = ⊤ := by
  apply presentation_generates
  intro g
  apply LieSubalgebra.subset_lieSpan
  rcases g with a | (i | (i | ⟨j,n⟩))
  · exact Or.inl (Or.inl ⟨a,rfl⟩)
  · exact Or.inr ⟨Sum.inl i,rfl⟩
  · exact Or.inl (Or.inr ⟨Sum.inl i,rfl⟩)
  · cases j
    exact mode_mem_generators n

private theorem cartan_negative (a : Presented datum) (ha : a ∈ cartanGenerators)
    (n : (Bool ⊕ ℕ+)) : ⁅a,negativeGenerator n⁆ ∈
      Submodule.span ℂ (Set.range negativeGenerator) := by
  obtain ⟨b,rfl⟩ := ha
  have hn : negativeGenerator n ∈ Submodule.span ℂ (Set.range negativeGenerator) :=
    Submodule.subset_span ⟨n,rfl⟩
  cases n with
  | inl i =>
    rw [negativeGenerator,ph_pf]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hn)
  | inr r =>
    rw [negativeGenerator,ph_pL]
    exact Submodule.smul_mem _ _ hn

private theorem cartan_singular (a : Presented datum) (ha : a ∈ cartanGenerators) :
    ⁅a,presentedSingular⁆ ∈ Submodule.span ℂ ({presentedSingular} : Set (Presented datum)) := by
  obtain ⟨b,rfl⟩ := ha
  rw [presented_singular_eigen]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

private noncomputable def mixedSpan : Submodule ℂ (Presented datum) :=
  Submodule.span ℂ (Set.range negativeGenerator) ⊔ Submodule.span ℂ cartanGenerators ⊔
    Submodule.span ℂ (Set.range positiveGenerator)

private theorem generators_in_mixedSpan : allGenerators ⊆ mixedSpan := by
  rintro x ((hc | hn) | hp)
  · have hle : Submodule.span ℂ cartanGenerators ≤ mixedSpan := le_sup_of_le_left le_sup_right
    exact hle (Submodule.subset_span hc)
  · have hle : Submodule.span ℂ (Set.range negativeGenerator) ≤ mixedSpan := le_sup_of_le_left le_sup_left
    exact hle (Submodule.subset_span hn)
  · have hle : Submodule.span ℂ (Set.range positiveGenerator) ≤ mixedSpan := le_sup_right
    exact hle (Submodule.subset_span hp)

private theorem mixed_positive_negative (p n : (Bool ⊕ ℕ+)) :
    ⁅positiveGenerator p,negativeGenerator n⁆ ∈ mixedSpan := by
  have hmode (k : ℤ) : pL datum () k ∈ mixedSpan := generators_in_mixedSpan (mode_mem_generators k)
  have hcartan (a : ℂ × ℂ) : ph datum a ∈ mixedSpan :=
    generators_in_mixedSpan (Or.inl (Or.inl ⟨a,rfl⟩))
  cases p with
  | inl i =>
    cases n with
    | inl k =>
      simp only [positiveGenerator,negativeGenerator,pe_pf]
      split_ifs
      · exact hcartan _
      · exact mixedSpan.zero_mem
    | inr r =>
      rw [positiveGenerator,negativeGenerator,pe_negative datum i () _ (by
        have := r.pos; omega)]
      exact mixedSpan.zero_mem
  | inr r =>
    cases n with
    | inl i =>
      rw [positiveGenerator,negativeGenerator,← lie_skew,pf_positive datum i () _ (by
        exact_mod_cast r.pos),neg_zero]
      exact mixedSpan.zero_mem
    | inr s =>
      rw [positiveGenerator,negativeGenerator,pL_commute]
      apply mixedSpan.add_mem (mixedSpan.smul_mem _ (hmode _))
      split_ifs
      · exact mixedSpan.smul_mem _ (hcartan _)
      · exact mixedSpan.zero_mem

private theorem positive_singular (p : (Bool ⊕ ℕ+)) : ⁅positiveGenerator p,presentedSingular⁆ = 0 := by
  cases p with
  | inl i => exact presented_e_singular i
  | inr r => exact presented_positive_singular r.val (by exact_mod_cast r.pos)

private noncomputable def negativeWeight : (Bool ⊕ ℕ+) → ℂ
  | .inl i => if i then 4/3 else 1
  | .inr r => (r.val : ℂ)/3

private theorem negative_weights_positive (n : (Bool ⊕ ℕ+)) : 0 < (negativeWeight n).re := by
  cases n with
  | inl i => cases i <;> norm_num [negativeWeight]
  | inr r =>
    simp only [negativeWeight,Complex.div_ofNat_re,Complex.natCast_re]
    exact div_pos (by exact_mod_cast r.pos) (by norm_num)

private theorem separating_negative (n : (Bool ⊕ ℕ+)) :
    ⁅-ph datum (1,0),negativeGenerator n⁆ = (-negativeWeight n) • negativeGenerator n := by
  cases n with
  | inl i =>
    rw [negativeGenerator,neg_lie,ph_pf]
    cases i <;> norm_num [datum,negativeWeight]
  | inr r =>
    rw [negativeGenerator,neg_lie,ph_pL]
    norm_num [datum,negativeWeight]
    push_cast
    module

private theorem separating_cartan (a : Presented datum) (ha : a ∈ cartanGenerators) :
    ⁅-ph datum (1,0),a⁆ = 0 := by
  obtain ⟨b,rfl⟩ := ha
  rw [neg_lie,ph_commute,neg_zero]

private theorem ideal_exists_of_singular_survives (hv : presentedSingular ≠ 0) :
    ∃ K : LieIdeal ℂ (Presented datum), K ≠ ⊥ ∧
      K.toSubmodule ⊓ Submodule.span ℂ cartanGenerators = ⊥ := by
  exact nonzero_disjoint_ideal negativeGenerator positiveGenerator presentedSingular
    (-ph datum (1,0)) cartanGenerators cartan_negative cartan_singular
    mixed_positive_negative positive_singular allGenerators_generate negativeWeight (-8/3)
    separating_negative presented_separating_weight negative_weights_positive (by norm_num)
    separating_cartan hv

end D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation


namespace D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
open EnhancedCartanData

private noncomputable def localQuotientMap : Presented datum →ₗ⁅ℂ⁆ VBKM datum :=
  { (localIdeal datum).toSubmodule.mkQ with
    map_lie' := fun {a b} => LieSubmodule.Quotient.mk_bracket (localIdeal datum) a b }

private theorem localQuotientMap_surjective : Function.Surjective localQuotientMap := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ x => exact ⟨x,rfl⟩

private theorem localQuotientMap_injective : Function.Injective localQuotientMap := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker (localIdeal datum).toSubmodule.mkQ = ⊥
  rw [Submodule.ker_mkQ]
  rw [datum_localIdeal_zero]
  rfl

private theorem cartan_map :
    (Submodule.span ℂ cartanGenerators).map localQuotientMap.toLinearMap = cartanSubspace datum := by
  rw [Submodule.map_span]
  unfold cartanSubspace
  congr 1
  ext x
  constructor
  · rintro ⟨y,⟨a,rfl⟩,rfl⟩
    exact ⟨a,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨ph datum a,⟨a,rfl⟩,rfl⟩

private theorem not_rigid_of_survival (hv : presentedSingular ≠ 0) : ¬ datum.IdealRigidity := by
  obtain ⟨K,hne,hsep⟩ := ideal_exists_of_singular_survives hv
  have hmapsep : (K.map localQuotientMap).toSubmodule ⊓ cartanSubspace datum = ⊥ := by
    rw [LieIdeal.coe_map_of_surjective localQuotientMap_surjective,← cartan_map,
      ← Submodule.map_inf _ localQuotientMap_injective,hsep,Submodule.map_bot]
  intro hR
  have hk0 := hR (K.map localQuotientMap) hmapsep
  exact hne (LieIdeal.bot_of_map_eq_bot localQuotientMap_injective hk0)

private theorem result_of_survival (hv : presentedSingular ≠ 0) : ¬ claim := by
  intro hclaim
  have hh := hclaim Bool Unit (ℂ × ℂ) (ℂ × ℂ) datum datum_enhanced datum_symmetrizable
    1 0 (Or.inl one_ne_zero)
  have hdef : datum.deform 1 0 = datum := by simp [deform]
  rw [if_neg one_ne_zero,hdef] at hh
  exact not_rigid_of_survival hv (hh datum_condition43)

end D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
namespace D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
open EnhancedCartanData D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction

private noncomputable def representationGenerator : ((ℂ × ℂ) ⊕ (Bool ⊕ (Bool ⊕ (Unit × ℤ)))) → Module.End ℂ (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N)
  | .inl a => qcartan a
  | .inr (.inl i) => qraising i
  | .inr (.inr (.inl i)) => qleft (.inl i)
  | .inr (.inr (.inr (_,n))) => qmode n

private noncomputable def freeRepresentation : (FreeLieAlgebra ℂ ((ℂ × ℂ) ⊕ (Bool ⊕ (Bool ⊕ (Unit × ℤ))))) →ₗ⁅ℂ⁆ Module.End ℂ (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) :=
  FreeLieAlgebra.lift ℂ representationGenerator

private theorem freeRepresentation_h (a : ℂ × ℂ) :
    freeRepresentation (h a) = qcartan a := by
  exact FreeLieAlgebra.lift_of_apply representationGenerator (.inl a)
private theorem freeRepresentation_e (i : Bool) :
    freeRepresentation (e i) = qraising i := by
  exact FreeLieAlgebra.lift_of_apply representationGenerator (.inr (.inl i))
private theorem freeRepresentation_f (i : Bool) :
    freeRepresentation (f i) = qleft (.inl i) := by
  exact FreeLieAlgebra.lift_of_apply representationGenerator (.inr (.inr (.inl i)))
private theorem freeRepresentation_L (j : Unit) (n : ℤ) :
    freeRepresentation (L j n) = qmode n := by
  exact FreeLieAlgebra.lift_of_apply representationGenerator (.inr (.inr (.inr (j,n))))

private theorem freeRepresentation_relations (x : (FreeLieAlgebra ℂ ((ℂ × ℂ) ⊕ (Bool ⊕ (Bool ⊕ (Unit × ℤ))))))
    (hx : x ∈ presentationRelations datum) : freeRepresentation x = 0 := by
  rcases hx with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
  · obtain ⟨a,b,rfl⟩ := h1
    simp only [map_sub,freeRepresentation_h,qcartan_add]
    module
  · obtain ⟨a,c,rfl⟩ := h2
    simp only [map_sub,map_smul,freeRepresentation_h,qcartan_smul,sub_self]
  · obtain ⟨a,b,rfl⟩ := h3
    rw [LieHom.map_lie,freeRepresentation_h,freeRepresentation_h,qcartan_commute]
  · obtain ⟨a,i,rfl⟩ := h4
    simp only [map_sub,LieHom.map_lie,map_smul,freeRepresentation_h,freeRepresentation_e,qcartan_qraising]
    cases i <;> simp [datum,tokenWeight] <;> module
  · obtain ⟨a,i,rfl⟩ := h5
    simp only [map_add,LieHom.map_lie,map_smul,freeRepresentation_h,freeRepresentation_f,qcartan_qleft]
    cases i <;> simp [datum,tokenWeight] <;> module
  · obtain ⟨i,k,rfl⟩ := h6
    simp only [map_sub,LieHom.map_lie,freeRepresentation_e,freeRepresentation_f,qraising_qleft]
    by_cases hik : i=k
    · subst k
      simp only [ite_true,freeRepresentation_h]
      simp [datum]
    · simp [hik]
  · obtain ⟨a,j,n,rfl⟩ := h7
    simp only [map_sub,LieHom.map_lie,map_smul,freeRepresentation_h,freeRepresentation_L,qcartan_mode]
    simp [datum]
    module
  · obtain ⟨j,n,m,rfl⟩ := h8
    simp only [map_sub,LieHom.map_lie,map_smul,freeRepresentation_h,freeRepresentation_L,qmode_virasoro]
    by_cases heq : n = -m <;> simp [heq,datum,D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction.central,freeRepresentation_h] <;> module
  · obtain ⟨j,rfl⟩ := h9
    simp only [map_sub,freeRepresentation_L,freeRepresentation_h,qmode_zero]
    simp [datum,D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction.degree]
  · obtain ⟨j,k,n,m,hjk,hnm,rfl⟩ := h10
    exact False.elim (hjk (Subsingleton.elim _ _))
  · obtain ⟨i,j,n,hn,rfl⟩ := h11
    rw [LieHom.map_lie,freeRepresentation_e,freeRepresentation_L,qraising_negative i n hn]
  · obtain ⟨i,j,n,hn,rfl⟩ := h12
    rw [LieHom.map_lie,freeRepresentation_f,freeRepresentation_L,← lie_skew,qmode_positive_root n hn i,neg_zero]

private theorem presentationIdeal_le_representation_kernel :
    presentationIdeal datum ≤ freeRepresentation.ker := by
  apply LieSubmodule.lieSpan_le.mpr
  intro x hx
  exact freeRepresentation_relations x hx

private noncomputable def representation : Presented datum →ₗ⁅ℂ⁆ Module.End ℂ (((List (Bool ⊕ ℕ+)) →₀ ℂ) ⧸ N) :=
  { (presentationIdeal datum).toSubmodule.liftQ freeRepresentation.toLinearMap
      presentationIdeal_le_representation_kernel with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with
      | _ x =>
        induction b using Submodule.Quotient.induction_on with
        | _ y => exact freeRepresentation.map_lie x y }

private theorem representation_pf (i : Bool) : representation (pf datum i) = qleft (.inl i) :=
  freeRepresentation_f i
private theorem representation_pL (j : Unit) (n : ℤ) : representation (pL datum j n) = qmode n :=
  freeRepresentation_L j n

end D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation

namespace D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
open EnhancedCartanData D5.S3.VertexAlgebra.Sectors.VBKMRecursiveAction

private theorem representation_singular_vacuum :
    representation presentedSingular qvacuum = N.mkQ singular := by
  have h1 : qmode (-1) = qleft (.inr 1) := qmode_negative 1
  have h2 : qmode (-2) = qleft (.inr 2) := qmode_negative 2
  have h3 : qmode (-3) = qleft (.inr 3) := qmode_negative 3
  have h4 : qmode (-4) = qleft (.inr 4) := qmode_negative 4
  simp only [presentedSingular,singularWord,map_add,map_sub,map_smul,LieHom.map_lie,
    representation_pL,representation_pf,h1,h2,h3,h4]
  simp only [LieRing.of_associative_ring_bracket,Module.End.mul_apply,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,map_add,map_sub,map_smul]
  simp only [qvacuum,qleft_project,left_basis]
  simp only [singular,adMode,map_add,map_sub,map_smul]
  simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
    map_add,map_sub,map_smul,List.append_assoc,List.cons_append,List.nil_append,
    List.singleton_append]

private theorem presentedSingular_ne_zero : presentedSingular ≠ 0 := by
  intro hv
  have hh := representation_singular_vacuum
  rw [hv,map_zero,LinearMap.zero_apply] at hh
  exact singular_not_mem ((Submodule.Quotient.mk_eq_zero _).mp hh.symm)

theorem result : ¬ claim := result_of_survival presentedSingular_ne_zero

end D5.S3.VertexAlgebra.Sectors.ZverykIdealRigidityRefutation
