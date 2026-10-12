/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularReconstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLayerLift
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Lean Elab Term in
elab "unitLift%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularLayerLift"
  let suffix := ".NikolovSegal.PartIIUnitriangularLift." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLayerLift"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual next-layer kernel {id} not found"
namespace NikolovSegal.PartIIUnitriangularReconstruction
open PartIIUnitriangularLayers PartIIUnitriangularLift
universe u
variable {F : Type u} [Field F] {n : ℕ}
private theorem upper (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth 1 (a.val-1)) : LayerDepth 0 a.val := by
  have hh := (unitLayer% depth_add) ((unitLayer% depth_mono) ha (by omega)) (unitLift% depth_one)
  simpa only [sub_add_cancel] using hh
private theorem product_depth (k : ℕ) (hk : 0 < k)
    (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hb : LayerDepth k (b.val-1)) : LayerDepth k ((a*b).val-1) := by
  have he : (a*b).val-1=(a.val-1)*(b.val-1)+(a.val-1)+(b.val-1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    noncomm_ring
  rw [he]
  exact (unitLayer% depth_add) ((unitLayer% depth_add)
    ((unitLayer% depth_mono) ((unitLayer% depth_mul) ha hb) (by omega)) ha) hb
private theorem commutator_depth (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hb : LayerDepth l (b.val-1)) :
    LayerDepth (k+l) ((a⁻¹*b⁻¹*a*b).val-1) := by
  have ha1 : LayerDepth 1 (a.val-1) := (unitLayer% depth_mono) ha hk
  have hb1 : LayerDepth 1 (b.val-1) := (unitLayer% depth_mono) hb hl
  have hh := (unitLayer% depth_mul) ((unitLift% inverse_upper) a ha1) ((unitLift% inverse_upper) b hb1)
  have hW : LayerDepth (k+l) ((a.val-1)*(b.val-1)-(b.val-1)*(a.val-1)) := by
    have h2 : LayerDepth (k+l) ((b.val-1)*(a.val-1)) := by
      simpa only [Nat.add_comm] using (unitLayer% depth_mul) hb ha
    simpa only [sub_eq_add_neg] using (unitLayer% depth_add) ((unitLayer% depth_mul) ha hb)
      ((unitLayer% depth_neg) h2)
  have he : (a⁻¹*b⁻¹*a*b).val-1=
      (a⁻¹).val*(b⁻¹).val*((a.val-1)*(b.val-1)-(b.val-1)*(a.val-1)) := by
    have h0 : (a⁻¹).val*(b⁻¹).val*(b.val*a.val)=1 :=
      congrArg Subtype.val (show a⁻¹*b⁻¹*(b*a)=1 by group)
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    noncomm_ring [h0]
  rw [he]
  simpa only [Nat.zero_add] using (unitLayer% depth_mul) hh hW

private theorem improve (k l : ℕ) (hk : 0 < k) (hkl : k+1 ≤ l)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (hg : LayerDepth 1 (g.val-1))
    (hproper : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0)
    (x b : Matrix.SpecialLinearGroup (Fin n) F) (hx : LayerDepth k (x.val-1))
    (hres : LayerDepth l (((x⁻¹*g⁻¹*x*g)⁻¹*b).val-1)) :
    ∃ X : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (X.val-1) ∧
      LayerDepth (l+1) (((X⁻¹*g⁻¹*X*g)⁻¹*b).val-1) := by
  let c := x⁻¹*g⁻¹*x*g
  let r := c⁻¹*b
  have hr : LayerDepth ((l-1)+1) (r.val-1) := by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ l)] using hres
  obtain ⟨z,hz,hd⟩ := actual_proper_next_layer_lift (l-1) (by omega) g hg hproper r hr
  let d := z⁻¹*g⁻¹*z*g
  have hd' : LayerDepth (l+1) ((d⁻¹*r).val-1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ l),show l-1+2=l+1 by omega] using hd
  have hx1 : LayerDepth 1 (x.val-1) := (unitLayer% depth_mono) hx hk
  have hz1 : LayerDepth 1 (z.val-1) := (unitLayer% depth_mono) hz (by omega)
  have hc : LayerDepth (k+1) (c.val-1) := commutator_depth k 1 hk (by decide) x g hx hg
  have hc1 : LayerDepth 1 (c.val-1) := (unitLayer% depth_mono) hc (by omega)
  have hd1 : LayerDepth 1 (d.val-1) := (unitLayer% depth_mono)
    (commutator_depth (l-1) 1 (by omega) (by decide) z g hz hg) (by omega)
  have he : LayerDepth (l+1) ((c⁻¹*z⁻¹*c*z).val-1) := (unitLayer% depth_mono)
    (commutator_depth (k+1) (l-1) (by omega) (by omega) c z hc hz) (by omega)
  have hconj : LayerDepth (l+1) ((z⁻¹*c*z).val-c.val) := by
    have hh := (unitLayer% depth_mul) (upper c hc1) he
    have heq : (z⁻¹*c*z).val-c.val=c.val*((c⁻¹*z⁻¹*c*z).val-1) := by
      have heq0 : c*(c⁻¹*z⁻¹*c*z)=z⁻¹*c*z := by group
      rw [mul_sub,mul_one,← Matrix.SpecialLinearGroup.coe_mul,heq0]
    rw [heq]
    simpa only [Nat.zero_add] using hh
  have hrd : LayerDepth (l+1) (r.val-d.val) := by
    have hh := (unitLayer% depth_mul) (upper d hd1) hd'
    have heq : r.val-d.val=d.val*((d⁻¹*r).val-1) := by
      rw [mul_sub,mul_one,← Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel_left]
    rw [heq]
    simpa only [Nat.zero_add] using hh
  have hbr : LayerDepth (l+1) (b.val-(c*d).val) := by
    have hh := (unitLayer% depth_mul) (upper c hc1) hrd
    have heq : b.val-(c*d).val=c.val*(r.val-d.val) := by
      rw [mul_sub,← Matrix.SpecialLinearGroup.coe_mul,← Matrix.SpecialLinearGroup.coe_mul]
      have h0 : c*r=b := by dsimp only [r]; group
      rw [h0]
    rw [heq]
    simpa only [Nat.zero_add] using hh
  let X := x*z
  let C := X⁻¹*g⁻¹*X*g
  have hCc : LayerDepth (l+1) (C.val-(c*d).val) := by
    have hh := (unitLayer% depth_mul) hconj (upper d hd1)
    have h0 : C=(z⁻¹*c*z)*d := by dsimp only [C,X,c,d]; group
    have heq : C.val-(c*d).val=((z⁻¹*c*z).val-c.val)*d.val := by
      rw [sub_mul,← Matrix.SpecialLinearGroup.coe_mul,← Matrix.SpecialLinearGroup.coe_mul,h0]
    rw [heq]
    simpa only [Nat.add_zero] using hh
  have hbC : LayerDepth (l+1) (b.val-C.val) := by
    have hh := (unitLayer% depth_add) hbr ((unitLayer% depth_neg) hCc)
    have heq : b.val-C.val=(b.val-(c*d).val)+(-(C.val-(c*d).val)) := by abel
    rw [heq]
    exact hh
  have hX : LayerDepth k (X.val-1) := product_depth k hk x z hx ((unitLayer% depth_mono) hz (by omega))
  have hC1 : LayerDepth 1 (C.val-1) := (unitLayer% depth_mono)
    (commutator_depth k 1 hk (by decide) X g hX hg) (by omega)
  refine ⟨X,hX,?_⟩
  have hh := (unitLayer% depth_mul) ((unitLift% inverse_upper) C hC1) hbC
  have heq : (C⁻¹*b).val-1=(C⁻¹).val*(b.val-C.val) := by
    rw [mul_sub,← Matrix.SpecialLinearGroup.coe_mul,← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  rw [heq]
  simpa only [Nat.zero_add] using hh

/-- Full actual unitriangular reconstruction from printed PartII equation(13).
For every fixed proper g, its single commutator-value map from the kth layer
covers the ENTIRE (k+1)st layer, for arbitrary rank and every field. The
finite induction solves all remaining higher coordinates, retaining the
noncommutative conjugation terms rather than commuting them away.
This is the proper-matrix kernel; Lemma9.1 and semilinear powered assembly
remain required for the uniform Proposition6.5 supplier. -/
theorem actual_proper_commutator_layer_reconstruction (k : ℕ) (hk : 0 < k)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (hg : LayerDepth 1 (g.val-1))
    (hproper : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0)
    (b : Matrix.SpecialLinearGroup (Fin n) F) (hb : LayerDepth (k+1) (b.val-1)) :
    ∃ x : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (x.val-1) ∧ x⁻¹*g⁻¹*x*g=b := by
  have h : ∀ d : ℕ, ∃ x : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (x.val-1) ∧
      LayerDepth (k+1+d) (((x⁻¹*g⁻¹*x*g)⁻¹*b).val-1) := by
    intro d
    induction d with
    | zero =>
      refine ⟨1,?_,?_⟩
      · intro i j hij; simp
      · simpa using hb
    | succ d ih =>
      obtain ⟨x,hx,hr⟩ := ih
      obtain ⟨X,hX,hR⟩ := improve k (k+1+d) hk (by omega) g hg hproper x b hx hr
      exact ⟨X,hX,by simpa only [Nat.add_assoc] using hR⟩
  obtain ⟨x,hx,hr⟩ := h n
  have hz : (((x⁻¹*g⁻¹*x*g)⁻¹*b).val-1)=0 :=
    (unitLayer% depth_n_zero) ((unitLayer% depth_mono) hr (by omega))
  have he : (x⁻¹*g⁻¹*x*g)⁻¹*b=1 := by
    apply Subtype.ext
    exact sub_eq_zero.mp hz
  exact ⟨x,hx,by simpa only [inv_mul_eq_one] using he⟩
end NikolovSegal.PartIIUnitriangularReconstruction
