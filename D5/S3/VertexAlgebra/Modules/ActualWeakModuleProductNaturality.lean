/- SOURCE CANDIDATE: UNCOMPILED / UNACCEPTED.
   Only the sealed suppliers listed in source-inputs.json were inspected.
   P, targetModule, U, inputMap, j, mu, and alpha below are the original APIs.
   No category, representing equivalence, or replacement bifunctor is defined. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleIntertwinerRepresentability
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleAssociator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductNaturality

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleHom (homSpace recordEquiv restrict)
open ActualWeakModuleUniversalField (P PairSector targetModule)
open ActualWeakModuleIntertwinerRepresentability
open ActualWeakModuleIntertwinerExtraction (extractionLinear extraction_natural)
open ActualWeakModuleProductMultiplicity
open ActualWeakModuleAssociator

universe u v w u' v' w' t
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Inputs
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'}
variable (hD : (gramReal D).PosDef)

/-- Record conversion of the literal corrected representability inputMap.
    This helper is consumed by j, finite reconstruction, alpha, and the pentagon. -/
def productHom (f : ModuleHom A' A) (g : ModuleHom B' B) :
    ModuleHom (targetModule A' B') (targetModule A B) :=
  (recordEquiv (targetModule A' B') (targetModule A B)).symm
    (inputMap hD A B A' B' f g)

/-- Preservation at EVERY rational Hahn exponent of the literal full U on
    arbitrary original input vectors. No truncation or new field is used. -/
theorem productHom_U_coeff (f : ModuleHom A' A) (g : ModuleHom B' B)
    (x : X') (y : Y') (q : ℚ) :
    (productHom hD f g).linearMap ((ActualWeakModuleUniversalField.U A' B' hD x).coeff q y) =
      (ActualWeakModuleUniversalField.U A B hD (f.linearMap x)).coeff q (g.linearMap y) := by
  have hf := congrArg (fun I : FullFields hD A' B' (targetModule A B) => (I.val x).coeff q y)
    (inputMap_field_preserving hD A B A' B' f g)
  simpa only [forward_coeff, ActualWeakModuleFullIntertwiner.map_coeff,
    ModuleHom.id, LinearMap.id_apply, universalElement_coeff,
    productHom, recordEquiv, Equiv.symm, Equiv.coe_fn_mk] using hf

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
private theorem extraction_universal (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) :
    extractionLinear hD A B (targetModule A B) (universalElement hD A B) c d x y =
      recordEquiv _ _ (ActualWeakModuleUniversalField.tagHom A B c d x y) := by
  apply Sectors.ActualWeakTargetFullFusion.forward_injective hD
    (representative D c) (representative D d) (targetModule A B)
  rw [ActualWeakModuleIntertwinerExtraction.sector_forward_extraction]
  apply Subtype.ext
  apply Sectors.ActualWeakTargetFullIntertwiner.fields_ext
  intro s t q
  rw [ActualWeakModuleIntertwinerExtraction.restriction_coeff,
    Sectors.ActualWeakTargetFullFusion.forward_coefficient,
    Sectors.ActualWeakTargetFullFusion.canonical_val,
    ActualWeakModuleIntertwinerExtraction.inclusion_apply,
    ActualWeakModuleIntertwinerExtraction.inclusion_apply,
    universalElement_coeff]
  have hu := ActualWeakModuleUniversalField.U_elementary_coeff A B hD c d s t x y q
  simp only [ActualWeakModuleUniversalField.elementary, ActualWeakModuleUniversalField.C] at hu
  rw [hu]
  simp only [recordEquiv, Equiv.coe_fn_mk, ActualWeakModuleUniversalField.tagHom,
    ModuleHom.comp, FullJacobiDirectSum.inclusionHom, LinearMap.comp_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply]
  apply DFinsupp.ext
  intro cd
  by_cases hc : (c,d) = cd
  · subst cd
    dsimp only [DirectSum.lof, DFinsupp.lsingle, DFinsupp.singleAddHom,
      DFunLike.coe, LinearMap.instFunLike]
    simp only [DFinsupp.single, Pi.single, Function.update, dite_true]
  · dsimp only [DirectSum.lof, DFinsupp.lsingle, DFinsupp.singleAddHom,
      DFunLike.coe, LinearMap.instFunLike]
    simp only [DFinsupp.single, Pi.single, Function.update,
      dif_neg (Ne.symm hc), dif_neg hc]


set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
/-- Elementary action of the EXISTING inputMap, derived by backward/extraction
    naturality and the original universal Hahn coefficient equation. -/
theorem inputMap_elementary (f : ModuleHom A' A) (g : ModuleHom B' B)
    (c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A' c) (y : Multiplicity B' d) :
    (inputMap hD A B A' B' f g).val
      (DirectSum.lof ℂ _ (PairSector A' B') (c,d) (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] y))) =
      DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (v ⊗ₜ[ℂ] (restrict f c x ⊗ₜ[ℂ] restrict g d y)) := by
  change (backwardHom hD A' B' (targetModule A B)
      (ActualWeakModuleFullIntertwiner.map (H hD) f g
        (ModuleHom.id (targetModule A B)) (universalElement hD A B))).linearMap _ = _
  rw [backwardHom_elementary]
  have hn := extraction_natural hD f g (ModuleHom.id (targetModule A B))
    (universalElement hD A B) c d x y
  rw [extraction_universal hD] at hn
  have hv := congrArg (fun k : Sectors.ActualWeakTargetFullFusion.Hom
    (representative D c + representative D d) (targetModule A B) => k.val v) hn
  simp only [H, Sectors.ActualWeakTargetFullFusion.targetHomMap,
    LinearMap.coe_mk, AddHom.coe_mk, ModuleHom.id, LinearMap.comp_apply,
    LinearMap.id_apply, recordEquiv, Equiv.coe_fn_mk,
    ActualWeakModuleUniversalField.tagHom, ModuleHom.comp,
    FullJacobiDirectSum.inclusionHom, LinearMap.flip_apply, TensorProduct.mk_apply] at hv ⊢
  rw [hv]
  apply DFinsupp.ext
  intro cd
  by_cases hc : (c,d) = cd
  · subst cd
    dsimp only [DirectSum.lof, DFinsupp.lsingle, DFinsupp.singleAddHom,
      DFunLike.coe, LinearMap.instFunLike]
    simp only [DFinsupp.single, Pi.single, Function.update, dite_true]
  · dsimp only [DirectSum.lof, DFinsupp.lsingle, DFinsupp.singleAddHom,
      DFunLike.coe, LinearMap.instFunLike]
    simp only [DFinsupp.single, Pi.single, Function.update,
      dif_neg (Ne.symm hc), dif_neg hc]


/-- Both tensor layers are algebraic: w is an arbitrary original pair
    multiplicity, not just a pure tensor or a member of a chosen basis. -/
theorem productHom_pair (f : ModuleHom A' A) (g : ModuleHom B' B)
    (c d : Discriminant D) (v : Carrier D) (w : PairMultiplicity A' B' (c,d)) :
    (productHom hD f g).linearMap
      (DirectSum.lof ℂ _ (PairSector A' B') (c,d) (v ⊗ₜ[ℂ] w)) =
      DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (v ⊗ₜ[ℂ] TensorProduct.map (restrict f c) (restrict g d) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      change (inputMap hD A B A' B' f g).val _ = _
      simpa only [TensorProduct.map_tmul] using inputMap_elementary hD f g c d v x y
  | add w z hw hz =>
      simpa only [map_add, TensorProduct.tmul_add, hw, hz]

/-- Equality is in the original Omega/jointWeight nested subtype. The carrier
    state is ground = T_carry^-1([0]1), including epsilon(-n,n)^-1. -/
theorem j_natural (f : ModuleHom A' A) (g : ModuleHom B' B)
    (c d : Discriminant D) (w : PairMultiplicity A' B' (c,d)) :
    restrict (productHom hD f g) (c+d) (j A' B' hD c d w) =
      j A B hD c d (TensorProduct.map (restrict f c) (restrict g d) w) := by
  apply Subtype.ext
  apply Subtype.ext
  change (productHom hD f g).linearMap (j A' B' hD c d w).val.val = _
  rw [j_val, j_val, productHom_pair]

/-- The dependent equality remains inside Fiber; no charge section is changed. -/
theorem jAt_natural (f : ModuleHom A' A) (g : ModuleHom B' B)
    (e : Discriminant D) (i : Fiber (D := D) e) (w : PairMultiplicity A' B' i.val) :
    restrict (productHom hD f g) e (jAt A' B' hD e i w) =
      jAt A B hD e i (TensorProduct.map (restrict f i.val.1) (restrict g i.val.2) w) := by
  rcases i with ⟨⟨c,d⟩,hi⟩
  subst e
  exact j_natural hD f g c d w

/-- Literal finite dependent direct-sum map on the supplied fibers of mu. -/
def fiberInput (f : ModuleHom A' A) (g : ModuleHom B' B) (e : Discriminant D) :
    FiberSum A' B' e →ₗ[ℂ] FiberSum A B e :=
  DirectSum.lmap (fun i : Fiber (D := D) e =>
    TensorProduct.map (restrict f i.val.1) (restrict g i.val.2))

theorem nu_natural (f : ModuleHom A' A) (g : ModuleHom B' B)
    (e : Discriminant D) (z : FiberSum A' B' e) :
    restrict (productHom hD f g) e (nu A' B' hD e z) =
      nu A B hD e (fiberInput f g e z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | of i w =>
      simpa only [← DirectSum.lof_eq_of ℂ, nu_lof, fiberInput, DirectSum.lmap_lof] using
        jAt_natural hD f g e i w

/-- Naturality of the ACTUAL normalized finite reconstruction, on every vector. -/
theorem mu_natural (f : ModuleHom A' A) (g : ModuleHom B' B)
    (e : Discriminant D) (x : Multiplicity (targetModule A' B') e) :
    mu A B hD e (restrict (productHom hD f g) e x) =
      fiberInput f g e (mu A' B' hD e x) := by
  calc
    _ = mu A B hD e (restrict (productHom hD f g) e
        (nu A' B' hD e (mu A' B' hD e x))) := by rw [nu_mu]
    _ = mu A B hD e (nu A B hD e (fiberInput f g e (mu A' B' hD e x))) := by
      rw [nu_natural]
    _ = _ := mu_nu A B hD e _

/-- A finite formula over the SOURCE vector's own support, valid when a map
    kills summands. There is no equality-of-supports or injectivity assumption. -/
theorem multiplicity_input_expansion (f : ModuleHom A' A) (g : ModuleHom B' B)
    (e : Discriminant D) (x : Multiplicity (targetModule A' B') e) :
    restrict (productHom hD f g) e x =
      ∑ i ∈ (mu A' B' hD e x).support,
        jAt A B hD e i (TensorProduct.map (restrict f i.val.1) (restrict g i.val.2)
          (mu A' B' hD e x i)) := by
  conv_lhs => rw [← nu_mu A' B' hD e x, nu_expansion]
  simp only [map_sum, jAt_natural]

end Inputs

section ThreeInputs
variable {X : Type u} {Y : Type v} {Z : Type w}
variable {X' : Type u'} {Y' : Type v'} {Z' : Type w'}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
variable [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
variable [AddCommGroup Z'] [Module ℂ Z']
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable {C : FullJacobiLatticeModule D Z}
variable {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'}
variable {C' : FullJacobiLatticeModule D Z'}
variable (hD : (gramReal D).PosDef)

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
/-- Literal action on actual E_L, before applying any flattening. -/
theorem input_E_L (f : ModuleHom A' A) (g : ModuleHom B' B) (h : ModuleHom C' C)
    (c d e : Discriminant D) (v : Carrier D)
    (x : Multiplicity A' c) (y : Multiplicity B' d) (z : Multiplicity C' e) :
    (productHom hD (productHom hD f g) h).linearMap (E_L A' B' C' hD c d e v x y z) =
      E_L A B C hD c d e v (restrict f c x) (restrict g d y) (restrict h e z) := by
  change (productHom hD (productHom hD f g) h).linearMap
    (DirectSum.lof ℂ _ (PairSector (targetModule A' B') C') (c+d,e)
      (v ⊗ₜ[ℂ] (j A' B' hD c d (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z))) = _
  rw [productHom_pair, TensorProduct.map_tmul, j_natural, TensorProduct.map_tmul]
  rfl

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
theorem input_E_R (f : ModuleHom A' A) (g : ModuleHom B' B) (h : ModuleHom C' C)
    (c d e : Discriminant D) (v : Carrier D)
    (x : Multiplicity A' c) (y : Multiplicity B' d) (z : Multiplicity C' e) :
    (productHom hD f (productHom hD g h)).linearMap (E_R A' B' C' hD c d e v x y z) =
      E_R A B C hD c d e v (restrict f c x) (restrict g d y) (restrict h e z) := by
  change (productHom hD f (productHom hD g h)).linearMap
    (DirectSum.lof ℂ _ (PairSector A' (targetModule B' C')) (c,d+e)
      (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] j B' C' hD d e (y ⊗ₜ[ℂ] z)))) = _
  rw [productHom_pair, TensorProduct.map_tmul, j_natural, TensorProduct.map_tmul]
  rfl

def leftTripleInput (f : ModuleHom A' A) (g : ModuleHom B' B) (h : ModuleHom C' C) :
    LeftTriple A' B' C' →ₗ[ℂ] LeftTriple A B C :=
  DirectSum.lmap (fun i : Triple D => TensorProduct.map LinearMap.id
    (TensorProduct.map (TensorProduct.map (restrict f i.1) (restrict g i.2.1))
      (restrict h i.2.2)))

def rightTripleInput (f : ModuleHom A' A) (g : ModuleHom B' B) (h : ModuleHom C' C) :
    RightTriple A' B' C' →ₗ[ℂ] RightTriple A B C :=
  DirectSum.lmap (fun i : Triple D => TensorProduct.map LinearMap.id
    (TensorProduct.map (restrict f i.1)
      (TensorProduct.map (restrict g i.2.1) (restrict h i.2.2))))

/-- All original vectors, using the actual finite E_L generation theorem. -/
theorem flattenLeft_natural (f : ModuleHom A' A) (g : ModuleHom B' B) (h : ModuleHom C' C)
    (s : LeftP A' B' C') :
    flattenLeft A B C hD ((productHom hD (productHom hD f g) h).linearMap s) =
      leftTripleInput f g h (flattenLeft A' B' C' hD s) := by
  apply E_L_induction A' B' C' hD
    (fun s => flattenLeft A B C hD ((productHom hD (productHom hD f g) h).linearMap s) =
      leftTripleInput f g h (flattenLeft A' B' C' hD s))
    (by simp) (fun a b ha hb => by simp only [map_add, ha, hb]) ?_ s
  intro c d e v x y z
  rw [input_E_L]
  simp only [E_L, flattenLeft_elementary, leftTripleInput, DirectSum.lmap_lof,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- The corresponding naturality for the original right flattening. -/
theorem flattenRight_natural (f : ModuleHom A' A) (g : ModuleHom B' B) (h : ModuleHom C' C)
    (s : RightP A' B' C') :
    flattenRight A B C hD ((productHom hD f (productHom hD g h)).linearMap s) =
      rightTripleInput f g h (flattenRight A' B' C' hD s) := by
  apply E_R_induction A' B' C' hD
    (fun s => flattenRight A B C hD ((productHom hD f (productHom hD g h)).linearMap s) =
      rightTripleInput f g h (flattenRight A' B' C' hD s))
    (by simp) (fun a b ha hb => by simp only [map_add, ha, hb]) ?_ s
  intro c d e v x y z
  rw [input_E_R]
  simp only [E_R, flattenRight_elementary, rightTripleInput, DirectSum.lmap_lof,
    TensorProduct.map_tmul, LinearMap.id_apply]

set_option maxHeartbeats 2000000 in
-- Elaborating the original nested module types needs a larger local heartbeat allowance.
/-- Naturality of ACTUAL alpha as equality of original full ModuleHom records.
    The source all-mode laws are carried by associatorIso.hom and productHom.
    No restriction on f,g,h, on their kernels, or on the six carrier universes. -/
theorem alpha_natural (f : ModuleHom A' A) (g : ModuleHom B' B) (h : ModuleHom C' C) :
    (productHom hD f (productHom hD g h)).comp (associatorIso A' B' C' hD).hom =
      (associatorIso A B C hD).hom.comp (productHom hD (productHom hD f g) h) := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro s
  change (productHom hD f (productHom hD g h)).linearMap (alpha A' B' C' hD s) =
    alpha A B C hD ((productHom hD (productHom hD f g) h).linearMap s)
  apply E_L_induction A' B' C' hD
    (fun s => (productHom hD f (productHom hD g h)).linearMap (alpha A' B' C' hD s) =
      alpha A B C hD ((productHom hD (productHom hD f g) h).linearMap s))
    (by simp) (fun a b ha hb => by simp only [map_add, ha, hb]) ?_ s
  intro c d e v x y z
  rw [alpha_E_L, map_smul, input_E_R, input_E_L, alpha_E_L]

end ThreeInputs
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductNaturality
