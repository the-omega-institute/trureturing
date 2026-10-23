/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphOddSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphOddSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularGraphLayers
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Lean Elab Term in
elab "unitGraph%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularGraphLayers"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularGraphLayers"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual graph-layer kernel {id} not found"
namespace NikolovSegal.PartIIUnitriangularGraphOddSupply
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularGraphLayers PartIIFieldMaps
universe u
variable {F : Type u} [Field F] {n : ℕ}
private def positiveRoot (k : ℕ) (i : Fin (n-k)) : Prop :=
  mirrorWeight n i.val-mirrorWeight n (i.val+k)=1
private instance positiveRootDecidable (k : ℕ) (i : Fin (n-k)) : Decidable (positiveRoot k i) :=
  inferInstanceAs (Decidable (mirrorWeight n i.val-mirrorWeight n (i.val+k)=1))
private theorem root_sign (lambda : Fˣ) (k : ℕ) (hk : 0<k) (hodd : k%2=1)
    (i : Fin (n-k)) :
    (unitGraph% rootWeight) lambda k i=if positiveRoot k i then lambda else lambda⁻¹ := by
  classical
  have h := (actual_mirror_odd_root_weights (⟨i.val,by omega⟩ : Fin n)
    ⟨i.val+k,by omega⟩ (by change i.val < i.val+k; omega) (by simpa using hodd)).1
  change lambda ^ (mirrorWeight n i.val-mirrorWeight n (i.val+k))=_
  by_cases hp : positiveRoot k i
  · rw [if_pos hp,show mirrorWeight n i.val-mirrorWeight n (i.val+k)=1 from hp,zpow_one]
  · have hn : mirrorWeight n i.val-mirrorWeight n (i.val+k)= -1 := h.resolve_left hp
    rw [if_neg hp,hn,zpow_neg_one]

/-- Actual norm witness for prescribed q-divisor powers. Its leading
commutator is the doubled-power value. This is an equality in the genuine
layer, never an asserted nonabelian inclusion of single commutator sets. -/
private theorem norm_value (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (d k : ℕ) (hk : 0<k) (hodd : k%2=1)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    let beta : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := (mirrorTorus lambda*fieldGraphAut phi eps)^d
    let x := a*beta a
    LayerDepth k (x.val-1) ∧ LayerDepth k ((x⁻¹*beta x).val-1) ∧
    ∀ i : Fin (n-k), (unitOdd% coordinate) k (x⁻¹*beta x) i=
      fieldValue phi 1 (2*d) 1
        (if positiveRoot k i then (lambda:F) else ((lambda⁻¹:Fˣ):F))
        ((unitOdd% coordinate) k a i) := by
  classical
  dsimp only
  let beta : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := (mirrorTorus lambda*fieldGraphAut phi eps)^d
  let x := a*beta a
  have hb : LayerDepth k ((beta a).val-1) := (unitGraph% mirror_graph_depth) lambda phi eps k hk a ha d
  have hx : LayerDepth k (x.val-1) := (unitRec% product_depth) k hk a (beta a) ha hb
  have hbx : LayerDepth k ((beta x).val-1) := (unitGraph% mirror_graph_depth) lambda phi eps k hk x hx d
  refine ⟨hx,(unitRec% product_depth) k hk _ _ ((unitOdd% inverse_depth) k hk x hx) hbx,?_⟩
  intro i
  have hbb := actual_mirror_field_graph_doubled_power lambda phi eps k hk hodd a ha d
  have he : beta (beta a)=((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(2*d)) a := by
    simp only [beta,← MulAut.mul_apply,← pow_add,show d+d=2*d by omega]
  rw [(unitOdd% product_coordinate) k hk x⁻¹ (beta x) ((unitOdd% inverse_depth) k hk x hx) hbx,
    (unitOdd% inverse_coordinate) k hk x hx]
  change -(unitOdd% coordinate) k (a*beta a) i+(unitOdd% coordinate) k (beta (a*beta a)) i=_
  rw [map_mul,(unitOdd% product_coordinate) k hk a (beta a) ha hb,
    (unitOdd% product_coordinate) k hk (beta a) (beta (beta a)) hb
      ((unitGraph% mirror_graph_depth) lambda phi eps k hk (beta a) hb d),he,hbb.2 i,
    root_sign lambda k hk hodd i]
  simp only [fieldValue,one_mul,pow_one]
  by_cases hp : positiveRoot k i
  · simp only [if_pos hp]; ring
  · simp only [if_neg hp,Units.val_inv_eq_inv_val]; ring

/-- Printed PartII Lemma9.2 odd-layer PRODUCT for arbitrary prescribed
field/positive-graph tuples. The proved scalar theorem is consumed at
exponents 2*d dividing 2*q. One torus tuple is fixed before ALL odd heights
and targets. Witnesses retain their actual norm-of-strip shape, including
unused root coordinates. The endpoint uses the prescribed dth-power
commutator VALUES, not substituted doubled-power values. -/
theorem actual_uniform_field_graph_odd_layer_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M)
    (hF : (2*q+1)^(2*q) < Fintype.card F)
    (phiP phiN : Fin M → RingAut F) (epsP epsN : Fin M → Bool)
    (dP dN : Fin M → ℕ)
    (hdP : ∀ j, 0<dP j ∧ dP j ∣ q) (hdN : ∀ j, 0<dN j ∧ dN j ∣ q) :
    ∃ lambdaP lambdaN : Fin M → Fˣ, ∀ k : ℕ, ∀ hk : 0<k, k%2=1 →
      ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (b.val-1) →
      ∃ x z : Fin M → Matrix.SpecialLinearGroup (Fin n) F,
        (∀ j, LayerDepth k ((x j).val-1) ∧ LayerDepth k ((z j).val-1)) ∧
        (∀ j, ∃ X Z : Fin n → F,
          x j=stripUnit k hk X*((mirrorTorus (lambdaP j)*fieldGraphAut (phiP j) (epsP j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP j)) (stripUnit k hk X) ∧
          z j=stripUnit k hk Z*((mirrorTorus ((lambdaN j)⁻¹)*fieldGraphAut (phiN j) (epsN j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN j)) (stripUnit k hk Z)) ∧
        LayerDepth (k+1) (((NikolovSegal.orderedProduct (fun j =>
          (x j)⁻¹*((mirrorTorus (lambdaP j)*fieldGraphAut (phiP j) (epsP j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP j)) (x j))*
          NikolovSegal.orderedProduct (fun j =>
          (z j)⁻¹*((mirrorTorus ((lambdaN j)⁻¹)*fieldGraphAut (phiN j) (epsN j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN j)) (z j)))⁻¹*b).val-1) := by
  classical
  have hq2 : 0<2*q := by omega
  have hdP2 : ∀ j, 0<2*dP j ∧ 2*dP j ∣ 2*q := fun j => ⟨by have h := (hdP j).1; omega,Nat.mul_dvd_mul_left 2 (hdP j).2⟩
  have hdN2 : ∀ j, 0<2*dN j ∧ 2*dN j ∣ 2*q := fun j => ⟨by have h := (hdN j).1; omega,Nat.mul_dvd_mul_left 2 (hdN j).2⟩
  obtain ⟨lp,hlp,hsp⟩ := lemma7_1 (c:=1) hq2 (by simpa using hM) (by simpa using hF)
    phiP (fun _ => 1) (fun j => 2*dP j) (fun _ => 1) (fun _ => one_ne_zero) hdP2 (fun _ => by simp)
  obtain ⟨lm,hlm,hsm⟩ := lemma7_1 (c:=1) hq2 (by simpa using hM) (by simpa using hF)
    phiN (fun _ => 1) (fun j => 2*dN j) (fun _ => 1) (fun _ => one_ne_zero) hdN2 (fun _ => by simp)
  let lambdaP : Fin M → Fˣ := fun j => Units.mk0 (lp j) (hlp j)
  let lambdaN : Fin M → Fˣ := fun j => Units.mk0 (lm j) (hlm j)
  refine ⟨lambdaP,lambdaN,?_⟩
  intro k hk hodd b hb
  have ht : ∀ i : Fin (n-k), ∃ t s : Fin M → F,
      (∑ j, fieldValue (phiP j) 1 (2*dP j) 1
        (if positiveRoot k i then lp j else (lp j)⁻¹) (t j))+
      (∑ j, fieldValue (phiN j) 1 (2*dN j) 1
        (if positiveRoot k i then (lm j)⁻¹ else lm j) (s j))=(unitOdd% coordinate) k b i := by
    intro i
    by_cases hi : positiveRoot k i
    · obtain ⟨t,ht⟩ := hsp ((unitOdd% coordinate) k b i)
      refine ⟨t,fun _ => 0,?_⟩
      simpa only [if_pos hi,fieldValue,map_zero,mul_zero,sub_self,Finset.sum_const_zero,add_zero] using ht
    · obtain ⟨s,hs⟩ := hsm ((unitOdd% coordinate) k b i)
      refine ⟨fun _ => 0,s,?_⟩
      simpa only [if_neg hi,fieldValue,map_zero,mul_zero,sub_self,Finset.sum_const_zero,zero_add] using hs
  choose t s ht using ht
  let X : Fin M → Fin n → F := fun j row => if h : row.val<n-k then t ⟨row.val,h⟩ j else 0
  let Z : Fin M → Fin n → F := fun j row => if h : row.val<n-k then s ⟨row.val,h⟩ j else 0
  let xp := fun j => stripUnit k hk (X j)
  let zn := fun j => stripUnit k hk (Z j)
  let bp : Fin M → MulAut (Matrix.SpecialLinearGroup (Fin n) F) := fun j => (mirrorTorus (lambdaP j)*fieldGraphAut (phiP j) (epsP j))^(dP j)
  let bn : Fin M → MulAut (Matrix.SpecialLinearGroup (Fin n) F) := fun j => (mirrorTorus ((lambdaN j)⁻¹)*fieldGraphAut (phiN j) (epsN j))^(dN j)
  let x := fun j => xp j*bp j (xp j)
  let z := fun j => zn j*bn j (zn j)
  have hcx : ∀ j i, (unitOdd% coordinate) k (xp j) i=t i j := by
    intro j i; rw [(unitOdd% strip_coordinate)]; simp only [X,dif_pos i.isLt]
  have hcz : ∀ j i, (unitOdd% coordinate) k (zn j) i=s i j := by
    intro j i; rw [(unitOdd% strip_coordinate)]; simp only [Z,dif_pos i.isLt]
  have hA := fun j => norm_value (lambdaP j) (phiP j) (epsP j) (dP j) k hk hodd (xp j) ((unitOdd% strip_depth) k hk _)
  have hB := fun j => norm_value ((lambdaN j)⁻¹) (phiN j) (epsN j) (dN j) k hk hodd (zn j) ((unitOdd% strip_depth) k hk _)
  let A := fun j => (x j)⁻¹*bp j (x j)
  let B := fun j => (z j)⁻¹*bn j (z j)
  have hPA := (unitOdd% ordered_layer) k hk A (fun j => (hA j).2.1)
  have hPB := (unitOdd% ordered_layer) k hk B (fun j => (hB j).2.1)
  refine ⟨x,z,fun j => ⟨(hA j).1,(hB j).1⟩,fun j => ⟨X j,Z j,rfl,rfl⟩,?_⟩
  apply (unitOdd% agree_next) k hk _ b ((unitRec% product_depth) k hk _ _ hPA.1 hPB.1) hb
  intro i
  rw [(unitOdd% product_coordinate) k hk _ _ hPA.1 hPB.1,hPA.2 i,hPB.2 i]
  have heA : ∀ j, (unitOdd% coordinate) k (A j) i=fieldValue (phiP j) 1 (2*dP j) 1
      (if positiveRoot k i then lp j else (lp j)⁻¹) (t i j) := by
    intro j; rw [(hA j).2.2 i,hcx j i]
    simp only [lambdaP,Units.val_mk0,Units.val_inv_eq_inv_val]
  have heB : ∀ j, (unitOdd% coordinate) k (B j) i=fieldValue (phiN j) 1 (2*dN j) 1
      (if positiveRoot k i then (lm j)⁻¹ else lm j) (s i j) := by
    intro j; rw [(hB j).2.2 i,hcz j i]
    simp only [lambdaN,Units.val_mk0,Units.val_inv_eq_inv_val,inv_inv]
  simp only [heA,heB]
  exact ht i
end NikolovSegal.PartIIUnitriangularGraphOddSupply
