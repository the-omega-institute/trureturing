/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularProper
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularProper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIProperTorusArithmetic
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularActions
import D5.S3.FiniteGroups.NikolovSegal.PartIITransvectionSupply
import Mathlib.Algebra.Group.Conj
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "unitAction%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularActions"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularActions"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual unitriangular action kernel {id} not found"
open Lean Elab Term in
elab "unitRec%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularReconstruction"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularReconstruction"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual filtration reconstruction kernel {id} not found"
namespace NikolovSegal.PartIIUnitriangularProper
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIFieldMaps
universe u
variable {F : Type u} [Field F] {n : ℕ}

private theorem actual_cocycle_power {G : Type*} [Group G]
    (beta : MulAut G) (v : G) (d : ℕ) :
    (MulAut.conj (v*(beta v)⁻¹)*beta)^d=
      MulAut.conj (v*((beta^d) v)⁻¹)*beta^d := by
  have hc : ∀ B : MulAut G,
      MulAut.conj (v*(B v)⁻¹)*B=MulAut.conj v*B*(MulAut.conj v)⁻¹ := by
    intro B
    apply MulEquiv.ext; intro z
    simp only [MulAut.mul_apply,MulAut.conj_apply,MulAut.conj_inv_apply,
      map_mul,map_inv,mul_inv_rev,inv_inv]

  rw [hc,conj_pow,← hc]

private theorem actual_constant_power (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (v : Matrix.SpecialLinearGroup (Fin n) F) (hv : LayerDepth 1 (v.val-1))
    (hvc : FirstLayerConstant v 1) (d : ℕ) :
    LayerDepth 1 ((((heightTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) v).val-1) ∧
      FirstLayerConstant (((heightTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) v)
        (orbitProduct phi d (lambda:F)) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply,orbitProduct,Finset.prod_range_zero] using ⟨hv,hvc⟩
  | succ d ih =>
    have h := actual_field_graph_first_layer phi eps _ ih.1 _ ih.2
    have hd := (unitAction% torus_depth) lambda 1 _ h.1
    have ht := (unitAction% torus_first) lambda _ _ h.2
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    exact ⟨hd,by simpa only [(rootFieldKernel% orbitProduct_succ)] using ht⟩

/-- Printed PartII Lemma9.1's actual powered proper-matrix construction,
for every finite field and every matrix rank, with the genuine field/positive
 graph automorphism. A diagonal correction and u are chosen before ALL
 targets. The entire powered automorphism identity is proved, not just a
 first-layer formula or a component-law assumption. -/
theorem lemma9_1_actual_powered_proper_matrix [Fintype F] [DecidableEq F]
    (phi : RingAut F) (eps : Bool) (d : ℕ) (hd : 0<d)
    (hF : (d+1)^d < Fintype.card F) :
    ∃ lambda : Fˣ, ∃ u g : Matrix.SpecialLinearGroup (Fin n) F,
      LayerDepth 1 (u.val-1) ∧ LayerDepth 1 (g.val-1) ∧
      FirstLayerConstant g (1-orbitProduct phi d (lambda:F)) ∧
      (∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0) ∧
      (MulAut.conj u*(heightTorus lambda*fieldGraphAut phi eps))^d=
        MulAut.conj g*(heightTorus lambda*fieldGraphAut phi eps)^d := by
  classical
  obtain ⟨a,ha,hN⟩ := PartIIProperTorusArithmetic.lemma9_1_torus_scalar phi d hd hF
  let lambda : Fˣ := Units.mk0 a ha
  let v : Matrix.SpecialLinearGroup (Fin n) F := stripUnit 1 (by decide) (fun _ => 1)
  have hv : LayerDepth 1 (v.val-1) := by
    change LayerDepth 1 ((1+layerStrip 1 (fun _ => (1:F)))-1)
    rw [add_sub_cancel_left]
    exact (unitLayer% strip_depth) 1 _
  have hc : FirstLayerConstant v 1 := by
    intro i hi
    have hij : (⟨i,by omega⟩ : Fin n) ≠ ⟨i+1,hi⟩ := by
      intro h; have hh := congrArg Fin.val h; change i=i+1 at hh; omega
    simp [v,stripUnit,Matrix.add_apply,Matrix.one_apply,layerStrip,hij]
  let beta : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := heightTorus lambda*fieldGraphAut phi eps
  let u := v*(beta v)⁻¹
  let g := v*((beta^d) v)⁻¹
  have hb := actual_constant_power lambda phi eps v hv hc 1
  have hbd := actual_constant_power lambda phi eps v hv hc d
  have hbu : LayerDepth 1 ((beta v).val-1) := by simpa only [pow_one] using hb.1
  have hu := (unitRec% product_depth) 1 (by decide) v (beta v)⁻¹ hv
    ((unitLayer% inverse_unit_depth) _ hbu)
  have hg := (unitRec% product_depth) 1 (by decide) v ((beta^d) v)⁻¹ hv
    ((unitLayer% inverse_unit_depth) _ hbd.1)
  have hgc : FirstLayerConstant g (1-orbitProduct phi d (lambda:F)) := by
    simpa only [sub_eq_add_neg] using (unitAction% first_mul) v ((beta^d) v)⁻¹ hv
      ((unitLayer% inverse_unit_depth) _ hbd.1) 1 _ hc
      ((unitAction% first_inv) _ hbd.1 _ hbd.2)
  refine ⟨lambda,u,g,hu,hg,hgc,?_,actual_cocycle_power beta v d⟩
  intro i hi
  rw [hgc i hi]
  exact sub_ne_zero.mpr (Ne.symm hN)

/-- Actual Lemma9.1 construction consumed by the complete equation(13)
filtration reconstruction. The same pre-target u/diagonal/powered proper
matrix realizes every admissible target in every higher layer, arbitrary
rank and finite field satisfying the printed bound. This is the proper
matrix component of Proposition6.5; it is not that proposition's full
semilinear commutator PRODUCT. -/
theorem actual_powered_proper_layer_coverage [Fintype F] [DecidableEq F]
    (phi : RingAut F) (eps : Bool) (d : ℕ) (hd : 0<d)
    (hF : (d+1)^d < Fintype.card F) :
    ∃ lambda : Fˣ, ∃ u g : Matrix.SpecialLinearGroup (Fin n) F,
      LayerDepth 1 (u.val-1) ∧ LayerDepth 1 (g.val-1) ∧
      (MulAut.conj u*(heightTorus lambda*fieldGraphAut phi eps))^d=
        MulAut.conj g*(heightTorus lambda*fieldGraphAut phi eps)^d ∧
      ∀ k : ℕ, 0<k → ∀ b : Matrix.SpecialLinearGroup (Fin n) F,
        LayerDepth (k+1) (b.val-1) →
        ∃ x : Matrix.SpecialLinearGroup (Fin n) F,
          LayerDepth k (x.val-1) ∧ x⁻¹*g⁻¹*x*g=b := by
  obtain ⟨lambda,u,g,hu,hg,_,hp,he⟩ := lemma9_1_actual_powered_proper_matrix phi eps d hd hF
  refine ⟨lambda,u,g,hu,hg,he,?_⟩
  intro k hk b hb
  exact PartIIUnitriangularReconstruction.actual_proper_commutator_layer_reconstruction k hk g hg hp b hb
end NikolovSegal.PartIIUnitriangularProper
