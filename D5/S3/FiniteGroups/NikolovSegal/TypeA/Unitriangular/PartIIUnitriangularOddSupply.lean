/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularOddSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularOddSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularProper
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIIUnitriangularOddSupply
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIFieldMaps
universe u
variable {F : Type u} [Field F] {n : ℕ}

private theorem inverse_depth (k : ℕ) (hk : 0<k)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (hg : LayerDepth k (g.val-1)) :
    LayerDepth k ((g⁻¹).val-1) := by
  have hi := (unitLift% inverse_upper) g ((unitLayer% depth_mono) hg hk)
  have hh := (unitLayer% depth_mul) hi hg
  have he : (g⁻¹).val-1= -((g⁻¹).val*(g.val-1)) := by
    rw [mul_sub,← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one,mul_one]
    abel
  rw [he]
  exact (unitLayer% depth_neg) (by simpa only [Nat.zero_add] using hh)

private def coordinate (k : ℕ) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (i : Fin (n-k)) : F := a ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩
private theorem coordinate_one (k : ℕ) (hk : 0<k) (i : Fin (n-k)) :
    coordinate k (1:Matrix.SpecialLinearGroup (Fin n) F) i=0 := by
  have hne : (⟨i.val,by omega⟩ : Fin n) ≠ ⟨i.val+k,by omega⟩ := by
    intro h; have hh := congrArg Fin.val h; change i.val=i.val+k at hh; omega
  simp [coordinate,Matrix.one_apply,hne]
private theorem product_coordinate (k : ℕ) (hk : 0<k)
    (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hb : LayerDepth k (b.val-1)) (i : Fin (n-k)) :
    coordinate k (a*b) i=coordinate k a i+coordinate k b i := by
  have he : (a*b).val-1=(a.val-1)*(b.val-1)+(a.val-1)+(b.val-1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
  have h0 := (unitLayer% depth_mul) ha hb ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩
    (by change i.val+k < i.val+(k+k); omega)
  have hij : (⟨i.val,by omega⟩ : Fin n) ≠ ⟨i.val+k,by omega⟩ := by
    intro h; have hh := congrArg Fin.val h; change i.val=i.val+k at hh; omega
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) F => A ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩) he
  simpa only [coordinate,Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply,if_neg hij,sub_zero,h0,zero_add] using h
private theorem inverse_coordinate (k : ℕ) (hk : 0<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) (i : Fin (n-k)) :
    coordinate k a⁻¹ i = -coordinate k a i := by
  have h := product_coordinate k hk a a⁻¹ ha (inverse_depth k hk a ha) i
  rw [mul_inv_cancel,coordinate_one k hk] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h.symm)

private def diagonalAction (a : Fin n → Fˣ) (g : Matrix.SpecialLinearGroup (Fin n) F) :
    Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal (fun i => (a i:F))*g.val*Matrix.diagonal (fun i => (((a i)⁻¹:Fˣ):F)),by
    rw [Matrix.det_mul,Matrix.det_mul,g.prop,mul_one,← Matrix.det_mul,Matrix.diagonal_mul_diagonal]
    have he : (fun i : Fin n => (a i:F)*(((a i)⁻¹:Fˣ):F))=fun _ => (1:F) := by funext i; simp
    rw [he,Matrix.diagonal_one,Matrix.det_one]⟩
private def diagonalAut (a : Fin n → Fˣ) : MulAut (Matrix.SpecialLinearGroup (Fin n) F) where
  toFun := diagonalAction a
  invFun := diagonalAction (fun i => (a i)⁻¹)
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp only [diagonalAction,Matrix.diagonal_mul,Matrix.mul_diagonal,inv_inv]
    calc
      _ = ((((a i)⁻¹:Fˣ):F):F)*(a i:F)*g i j*(((a j)⁻¹:Fˣ):F)*(a j:F) := by ring
      _ = _ := by simp [mul_assoc]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp only [diagonalAction,Matrix.diagonal_mul,Matrix.mul_diagonal,inv_inv]
    calc
      _ = (a i:F)*(((a i)⁻¹:Fˣ):F)*g i j*(a j:F)*(((a j)⁻¹:Fˣ):F) := by ring
      _ = _ := by simp [mul_assoc]
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.diagonal _*(g.val*h.val)*Matrix.diagonal _=
      (Matrix.diagonal _*g.val*Matrix.diagonal _)*(Matrix.diagonal _*h.val*Matrix.diagonal _)
    have hi : Matrix.diagonal (fun i : Fin n => (((a i)⁻¹:Fˣ):F))*Matrix.diagonal (fun i => (a i:F))=1 := by
      rw [Matrix.diagonal_mul_diagonal]; apply Matrix.diagonal_eq_one.mpr; funext i; simp
    simp only [mul_assoc]
    rw [← mul_assoc (Matrix.diagonal (fun i : Fin n => (((a i)⁻¹:Fˣ):F))) (Matrix.diagonal (fun i => (a i:F))),hi,one_mul]
private theorem diagonal_entry (a : Fin n → Fˣ) (g : Matrix.SpecialLinearGroup (Fin n) F)
    (i j : Fin n) : diagonalAut a g i j=(a i:F)*g i j*(((a j)⁻¹:Fˣ):F) := by
  change (Matrix.diagonal (fun i => (a i:F))*g.val*Matrix.diagonal (fun i => (((a i)⁻¹:Fˣ):F))) i j=_
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal]
private theorem diagonal_depth (a : Fin n → Fˣ) (k : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (hg : LayerDepth k (g.val-1)) :
    LayerDepth k ((diagonalAut a g).val-1) := by
  intro i j hij
  have h := hg i j hij
  simp only [Matrix.sub_apply] at h ⊢
  rw [diagonal_entry,sub_eq_zero.mp h]
  by_cases he : i=j
  · subst j; simp [Matrix.one_apply]
  · simp [Matrix.one_apply,he]

/-- Alternating actual diagonal torus; every odd-height root has weight
lambda or lambda^-1, independently of rank and height. -/
def parityTorus (lambda : Fˣ) : MulAut (Matrix.SpecialLinearGroup (Fin n) F) :=
  diagonalAut (fun i => lambda⁻¹^(i.val%2))

private theorem parity_coordinate (lambda : Fˣ) (k : ℕ) (hodd : k%2=1)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (i : Fin (n-k)) :
    coordinate k (parityTorus lambda g) i=
      (if i.val%2=0 then (lambda:F) else ((lambda⁻¹:Fˣ):F))*coordinate k g i := by
  unfold coordinate
  rw [show parityTorus lambda=diagonalAut (fun i : Fin n => lambda⁻¹^(i.val%2)) from rfl,diagonal_entry]
  by_cases hi : i.val%2=0
  · have hj : (i.val+k)%2=1 := by omega
    simp only [hi,hj,pow_zero,pow_one,Units.val_one,inv_inv,one_mul,ite_true]
    ring
  · have hi' : i.val%2=1 := by omega
    have hj : (i.val+k)%2=0 := by omega
    simp only [hi',hj,pow_zero,pow_one,Units.val_one,inv_one,mul_one,ite_false,Nat.one_ne_zero]

private theorem field_depth (phi : RingAut F) (k : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (hg : LayerDepth k (g.val-1)) :
    LayerDepth k ((fieldAut phi g).val-1) := by
  intro i j hij
  have h := hg i j hij
  simp only [Matrix.sub_apply] at h ⊢
  change phi (g i j)-(1:Matrix (Fin n) (Fin n) F) i j=0
  rw [sub_eq_zero.mp h]
  simp [Matrix.one_apply]
private theorem field_coordinate (phi : RingAut F) (k : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (i : Fin (n-k)) :
    coordinate k (fieldAut phi g) i=phi (coordinate k g i) := rfl

private theorem parity_field_power (lambda : Fˣ) (phi : RingAut F)
    (k : ℕ) (hodd : k%2=1) (g : Matrix.SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth k (g.val-1)) (d : ℕ) :
    LayerDepth k ((((parityTorus lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) g).val-1) ∧
      ∀ i : Fin (n-k), coordinate k (((parityTorus lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) g) i=
        orbitProduct phi d (if i.val%2=0 then (lambda:F) else ((lambda⁻¹:Fˣ):F))*(phi^d) (coordinate k g i) := by
  induction d with
  | zero =>
    refine ⟨hg,?_⟩; intro i
    simp [orbitProduct]
  | succ d ih =>
    have hd := diagonal_depth (fun i : Fin n => lambda⁻¹^(i.val%2)) k _ (field_depth phi k _ ih.1)
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    refine ⟨hd,?_⟩; intro i
    rw [parity_coordinate lambda k hodd,field_coordinate,ih.2 i,map_mul,
      (rootFieldKernel% orbitProduct_succ),pow_succ',RingAut.mul_apply]
    ring

private theorem ordered_layer {M : ℕ} (k : ℕ) (hk : 0<k)
    (a : Fin M → Matrix.SpecialLinearGroup (Fin n) F) (ha : ∀ j, LayerDepth k ((a j).val-1)) :
    LayerDepth k ((NikolovSegal.orderedProduct a).val-1) ∧
      ∀ i : Fin (n-k), coordinate k (NikolovSegal.orderedProduct a) i=∑ j, coordinate k (a j) i := by
  induction M with
  | zero =>
    constructor
    · intro i j hij; simp [NikolovSegal.orderedProduct]
    · intro i; simp [NikolovSegal.orderedProduct,coordinate_one k hk]
  | succ M ih =>
    have htail := ih (fun j => a j.succ) (fun j => ha j.succ)
    have he : NikolovSegal.orderedProduct a=a 0*NikolovSegal.orderedProduct (fun j => a j.succ) := by
      simp only [NikolovSegal.orderedProduct,List.ofFn_succ,List.prod_cons]
    rw [he]
    refine ⟨(unitRec% product_depth) k hk _ _ (ha 0) htail.1,?_⟩
    intro i
    rw [product_coordinate k hk _ _ (ha 0) htail.1,htail.2 i,Fin.sum_univ_succ]

private theorem agree_next (k : ℕ) (hk : 0<k)
    (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hb : LayerDepth k (b.val-1))
    (hc : ∀ i : Fin (n-k), coordinate k a i=coordinate k b i) :
    LayerDepth (k+1) ((a⁻¹*b).val-1) := by
  have hd : LayerDepth (k+1) (b.val-a.val) := by
    intro i j hij
    by_cases hlt : j.val < i.val+k
    · have h1 := ha i j hlt
      have h2 := hb i j hlt
      simp only [Matrix.sub_apply] at h1 h2 ⊢
      rw [sub_eq_zero.mp h1,sub_eq_zero.mp h2,sub_self]
    · have hj : j.val=i.val+k := by omega
      have hi : i.val<n-k := by omega
      have h1 : (⟨i.val,by omega⟩ : Fin n)=i := Fin.ext rfl
      have h2 : (⟨i.val+k,by omega⟩ : Fin n)=j := Fin.ext hj.symm
      have h := hc ⟨i.val,hi⟩
      simp only [coordinate,h1,h2] at h
      exact sub_eq_zero.mpr h.symm
  have hh := (unitLayer% depth_mul) ((unitLift% inverse_upper) a ((unitLayer% depth_mono) ha hk)) hd
  have he : (a⁻¹*b).val-1=(a⁻¹).val*(b.val-a.val) := by
    rw [mul_sub,← Matrix.SpecialLinearGroup.coe_mul,← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
  rw [he]
  simpa only [Nat.zero_add] using hh

private theorem strip_coordinate (k : ℕ) (hk : 0<k) (t : Fin n → F) (i : Fin (n-k)) :
    coordinate k (stripUnit k hk t) i=t ⟨i.val,by omega⟩ := by
  have hne : (⟨i.val,by omega⟩ : Fin n) ≠ ⟨i.val+k,by omega⟩ := by
    intro h; have hh := congrArg Fin.val h; change i.val=i.val+k at hh; omega
  simp [coordinate,stripUnit,Matrix.add_apply,Matrix.one_apply,layerStrip,hne]
private theorem strip_depth (k : ℕ) (hk : 0<k) (t : Fin n → F) :
    LayerDepth k ((stripUnit k hk t).val-1) := by
  change LayerDepth k ((1+layerStrip k t)-1)
  rw [add_sub_cancel_left]
  exact (unitLayer% strip_depth) k t

private theorem actual_odd_value (lambda : Fˣ) (phi : RingAut F) (d k : ℕ)
    (hk : 0<k) (hodd : k%2=1)
    (x : Matrix.SpecialLinearGroup (Fin n) F) (hx : LayerDepth k (x.val-1)) :
    LayerDepth k ((x⁻¹*((parityTorus lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) x).val-1) ∧
      ∀ i : Fin (n-k), coordinate k (x⁻¹*((parityTorus lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) x) i=
        fieldValue phi 1 d 1 (if i.val%2=0 then (lambda:F) else ((lambda⁻¹:Fˣ):F)) (coordinate k x i) := by
  have h := parity_field_power lambda phi k hodd x hx d
  refine ⟨(unitRec% product_depth) k hk _ _ (inverse_depth k hk x hx) h.1,?_⟩
  intro i
  rw [product_coordinate k hk _ _ (inverse_depth k hk x hx) h.1,inverse_coordinate k hk x hx,h.2 i]
  simp only [fieldValue,one_mul,pow_one,sub_eq_add_neg,add_comm]

/-- Rank-independent odd-layer VALUE coverage, the field-action branch of
printed PartII Lemma9.2. Two genuine alternating diagonal tuples are fixed
before every odd height and every actual matrix target. The published field
lemma is PROVED and consumed; there is no layer-coverage premise. Both scalar
signs, all unused coordinates and the noncommutative product are retained.
Graph-action layers and full even-layer induction remain separate obligations. -/
theorem actual_uniform_field_odd_layer_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : q*(q+1)<M) (hF : (q+1)^q < Fintype.card F)
    (phiP phiN : Fin M → RingAut F) (dP dN : Fin M → ℕ)
    (hdP : ∀ j, 0<dP j ∧ dP j ∣ q) (hdN : ∀ j, 0<dN j ∧ dN j ∣ q) :
    ∃ lambdaP lambdaN : Fin M → Fˣ, ∀ k : ℕ, ∀ hk : 0<k, k%2=1 →
      ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (b.val-1) →
      ∃ x z : Fin M → Matrix.SpecialLinearGroup (Fin n) F,
        (∀ j, LayerDepth k ((x j).val-1) ∧ LayerDepth k ((z j).val-1)) ∧
        (∀ j, ∃ X Z : Fin n → F, x j=stripUnit k hk X ∧ z j=stripUnit k hk Z) ∧
        LayerDepth (k+1) (((NikolovSegal.orderedProduct (fun j =>
          (x j)⁻¹*((parityTorus (lambdaP j)*fieldAut (phiP j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP j)) (x j))*
          NikolovSegal.orderedProduct (fun j =>
          (z j)⁻¹*((parityTorus ((lambdaN j)⁻¹)*fieldAut (phiN j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN j)) (z j)))⁻¹*b).val-1) := by
  classical
  obtain ⟨lp,hlp,hsp⟩ := lemma7_1 (c:=1) hq (by simpa using hM) (by simpa using hF)
    phiP (fun _ => 1) dP (fun _ => 1) (fun _ => one_ne_zero) hdP (fun _ => by simp)
  obtain ⟨lm,hlm,hsm⟩ := lemma7_1 (c:=1) hq (by simpa using hM) (by simpa using hF)
    phiN (fun _ => 1) dN (fun _ => 1) (fun _ => one_ne_zero) hdN (fun _ => by simp)
  let lambdaP : Fin M → Fˣ := fun j => Units.mk0 (lp j) (hlp j)
  let lambdaN : Fin M → Fˣ := fun j => Units.mk0 (lm j) (hlm j)
  refine ⟨lambdaP,lambdaN,?_⟩
  intro k hk hodd b hb
  have ht : ∀ i : Fin (n-k), ∃ t s : Fin M → F,
      (∀ j, if i.val%2=0 then s j=0 else t j=0) ∧
      (∑ j, fieldValue (phiP j) 1 (dP j) 1
        (if i.val%2=0 then lp j else (lp j)⁻¹) (t j))+
      (∑ j, fieldValue (phiN j) 1 (dN j) 1
        (if i.val%2=0 then (lm j)⁻¹ else lm j) (s j))=coordinate k b i := by
    intro i
    by_cases hi : i.val%2=0
    · obtain ⟨t,ht⟩ := hsp (coordinate k b i)
      refine ⟨t,fun _ => 0,?_,?_⟩
      · intro j; simp [hi]
      · simpa only [if_pos hi,fieldValue,map_zero,mul_zero,sub_self,Finset.sum_const_zero,add_zero] using ht
    · obtain ⟨s,hs⟩ := hsm (coordinate k b i)
      refine ⟨fun _ => 0,s,?_,?_⟩
      · intro j; simp [hi]
      · simpa only [if_neg hi,fieldValue,map_zero,mul_zero,sub_self,Finset.sum_const_zero,zero_add] using hs
  choose t s hzero ht using ht
  let X : Fin M → Fin n → F := fun j row => if h : row.val<n-k then t ⟨row.val,h⟩ j else 0
  let Z : Fin M → Fin n → F := fun j row => if h : row.val<n-k then s ⟨row.val,h⟩ j else 0
  let x : Fin M → Matrix.SpecialLinearGroup (Fin n) F := fun j => stripUnit k hk (X j)
  let z : Fin M → Matrix.SpecialLinearGroup (Fin n) F := fun j => stripUnit k hk (Z j)
  have hx : ∀ j, LayerDepth k ((x j).val-1) := fun j => strip_depth k hk _
  have hz : ∀ j, LayerDepth k ((z j).val-1) := fun j => strip_depth k hk _
  have hcx : ∀ j i, coordinate k (x j) i=t i j := by
    intro j i
    rw [strip_coordinate]
    simp only [X,dif_pos i.isLt]
  have hcz : ∀ j i, coordinate k (z j) i=s i j := by
    intro j i
    rw [strip_coordinate]
    simp only [Z,dif_pos i.isLt]
  let A := fun j => (x j)⁻¹*((parityTorus (lambdaP j)*fieldAut (phiP j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP j)) (x j)
  let B := fun j => (z j)⁻¹*((parityTorus ((lambdaN j)⁻¹)*fieldAut (phiN j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN j)) (z j)
  have hA := fun j => actual_odd_value (lambdaP j) (phiP j) (dP j) k hk hodd (x j) (hx j)
  have hB := fun j => actual_odd_value ((lambdaN j)⁻¹) (phiN j) (dN j) k hk hodd (z j) (hz j)
  have hPA := ordered_layer k hk A (fun j => (hA j).1)
  have hPB := ordered_layer k hk B (fun j => (hB j).1)
  refine ⟨x,z,fun j => ⟨hx j,hz j⟩,fun j => ⟨X j,Z j,rfl,rfl⟩,?_⟩
  apply agree_next k hk _ b ((unitRec% product_depth) k hk _ _ hPA.1 hPB.1) hb
  intro i
  rw [product_coordinate k hk _ _ hPA.1 hPB.1,hPA.2 i,hPB.2 i]
  have heA : ∀ j, coordinate k (A j) i=fieldValue (phiP j) 1 (dP j) 1
      (if i.val%2=0 then lp j else (lp j)⁻¹) (t i j) := by
    intro j
    rw [(hA j).2 i,hcx j i]
    simp only [lambdaP,Units.val_mk0,Units.val_inv_eq_inv_val]
  have heB : ∀ j, coordinate k (B j) i=fieldValue (phiN j) 1 (dN j) 1
      (if i.val%2=0 then (lm j)⁻¹ else lm j) (s i j) := by
    intro j
    rw [(hB j).2 i,hcz j i]
    simp only [lambdaN,Units.val_mk0,Units.val_inv_eq_inv_val,inv_inv]
  simp only [heA,heB]
  exact ht i
end NikolovSegal.PartIIUnitriangularOddSupply
