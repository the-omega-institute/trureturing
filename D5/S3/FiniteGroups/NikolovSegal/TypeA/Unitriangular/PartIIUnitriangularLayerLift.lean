/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayerLift
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayerLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLayers
import Lean.Elab.Term
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Lean Elab Term in
elab "unitLayer%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularLayers"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLayers"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual unitriangular layer kernel {id} not found"
namespace NikolovSegal.PartIIUnitriangularLift
open PartIIUnitriangularLayers
universe u
variable {F : Type u} [Field F] {n : ℕ}
private theorem depth_one : LayerDepth 0 (1 : Matrix (Fin n) (Fin n) F) := by
  intro i j hij
  have hne : i ≠ j := by intro h; subst j; omega
  simp [Matrix.one_apply,hne]
private theorem inverse_upper (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) : LayerDepth 0 (a⁻¹).val := by
  have hd := (unitLayer% inverse_unit_depth) a ha
  have hh := (unitLayer% depth_add) ((unitLayer% depth_mono) hd (by omega)) depth_one
  simpa only [sub_add_cancel] using hh

/-- Actual equation(13) lifted to the full matrix height congruence: one
true kth-layer commutator realizes an arbitrary (k+1)st-layer group element
modulo the genuine (k+2)nd layer. The proper g is fixed before every b. -/
theorem actual_proper_next_layer_lift (k : ℕ) (hk : 0 < k)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (hg : LayerDepth 1 (g.val-1))
    (hproper : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0)
    (b : Matrix.SpecialLinearGroup (Fin n) F) (hb : LayerDepth (k+1) (b.val-1)) :
    ∃ u : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (u.val-1) ∧
      LayerDepth (k+2) (((u⁻¹*g⁻¹*u*g)⁻¹*b).val-1) := by
  let t : Fin (n-(k+1)) → F := fun i => (b.val-1) ⟨i.val,by omega⟩ ⟨i.val+k+1,by omega⟩
  obtain ⟨u,hu,hc,hv⟩ := actual_proper_group_layer_surjective k hk g hg hproper t
  let c := u⁻¹*g⁻¹*u*g
  have hd : LayerDepth (k+2) (b.val-c.val) := by
    intro i j hij
    have he : b.val-c.val=(b.val-1)-(c.val-1) := by abel
    rw [he,Matrix.sub_apply]
    by_cases h : j.val < i.val+k+1
    · rw [hb i j h,hc i j h,sub_self]
    · have he : j.val=i.val+k+1 := by omega
      have hi : i.val<n-(k+1) := by omega
      have hv' := hv ⟨i.val,hi⟩
      have hj : j=(⟨i.val+k+1,by omega⟩ : Fin n) := Fin.ext he
      rw [hj]
      change (c.val-1) i ⟨i.val+k+1,by omega⟩=(b.val-1) i ⟨i.val+k+1,by omega⟩ at hv'
      rw [hv',sub_self]
  have hc1 : LayerDepth 1 (c.val-1) := (unitLayer% depth_mono) hc (by omega)
  have hm := (unitLayer% depth_mul) (inverse_upper c hc1) hd
  refine ⟨u,hu,?_⟩
  have he : (c⁻¹*b).val-1=(c⁻¹).val*(b.val-c.val) := by
    have h0 : (c⁻¹).val*c.val=1 := congrArg Subtype.val (inv_mul_cancel c)
    rw [Matrix.SpecialLinearGroup.coe_mul,mul_sub,h0]
  rw [he]
  simpa only [Nat.zero_add] using hm
end NikolovSegal.PartIIUnitriangularLift
