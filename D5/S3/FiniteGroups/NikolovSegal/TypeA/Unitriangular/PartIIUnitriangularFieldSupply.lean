/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularFieldSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularLayersGlobal
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace NikolovSegal.PartIIUnitriangularFieldSupply
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularOddSupply PartIIFieldMaps
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- Actual diagonal torus for the fixed kth layer: every kth-height root
has weight lambda. Its first/second-layer instances are the two printed
last batches of Proposition6.5, with no rank-dependent field exponent. -/
def layerTorus (k : ℕ) (lambda : Fˣ) : MulAut (Matrix.SpecialLinearGroup (Fin n) F) :=
  (unitOdd% diagonalAut) (fun i => lambda⁻¹^(i.val/k))
private theorem layer_torus_coordinate (k : ℕ) (hk : 0<k) (lambda : Fˣ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (i : Fin (n-k)) :
    (unitOdd% coordinate) k (layerTorus k lambda a) i=(lambda:F)*(unitOdd% coordinate) k a i := by
  change ((unitOdd% diagonalAut) (fun j : Fin n => lambda⁻¹^(j.val/k)) a) ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩=_
  rw [(unitOdd% diagonal_entry)]
  let A : Fˣ := lambda⁻¹^(i.val/k)
  let B : Fˣ := (lambda⁻¹^((i.val+k)/k))⁻¹
  have hu : A*B=lambda := by
    dsimp only [A,B]
    rw [Nat.add_div_right i.val hk,pow_succ]
    simp [mul_comm,mul_left_comm,mul_assoc]
  change (A:F)*a ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩*(B:F)=(lambda:F)*a ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩
  calc
    _ = ((A*B:Fˣ):F)*a ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩ := by simp only [Units.val_mul]; ring
    _ = _ := by rw [hu]
private theorem layer_field_power (k : ℕ) (hk : 0<k) (lambda : Fˣ) (phi : RingAut F)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) (d : ℕ) :
    LayerDepth k ((((layerTorus k lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a).val-1) ∧
      ∀ i : Fin (n-k), (unitOdd% coordinate) k (((layerTorus k lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a) i=
        orbitProduct phi d (lambda:F)*(phi^d) ((unitOdd% coordinate) k a i) := by
  induction d with
  | zero => refine ⟨ha,?_⟩; intro i; simp [orbitProduct]
  | succ d ih =>
    have hd := (unitOdd% diagonal_depth) (fun i : Fin n => lambda⁻¹^(i.val/k)) k _ ((unitOdd% field_depth) phi k _ ih.1)
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    refine ⟨hd,?_⟩; intro i
    rw [layer_torus_coordinate k hk lambda,(unitOdd% field_coordinate),ih.2 i,map_mul,
      (rootFieldKernel% orbitProduct_succ),pow_succ',RingAut.mul_apply]
    ring
private theorem layer_field_value (k : ℕ) (hk : 0<k) (lambda : Fˣ) (phi : RingAut F)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) (d : ℕ) :
    LayerDepth k ((a⁻¹*((layerTorus k lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a).val-1) ∧
      ∀ i : Fin (n-k), (unitOdd% coordinate) k (a⁻¹*((layerTorus k lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a) i=
        fieldValue phi 1 d 1 (lambda:F) ((unitOdd% coordinate) k a i) := by
  have h := layer_field_power k hk lambda phi a ha d
  refine ⟨(unitRec% product_depth) k hk _ _ ((unitOdd% inverse_depth) k hk a ha) h.1,?_⟩
  intro i
  rw [(unitOdd% product_coordinate) k hk _ _ ((unitOdd% inverse_depth) k hk a ha) h.1,
    (unitOdd% inverse_coordinate) k hk a ha,h.2 i]
  simp only [fieldValue,one_mul,pow_one,sub_eq_add_neg,add_comm]

/-- Actual fixed-layer scalar PRODUCT, consumed for the two leading layers
of Proposition6.5. Exact diagonal/field powers, genuine strip witnesses and
all matrix target coordinates are reconstructed from proved Lemma7.1.
Corrections precede every target and M/cutoff are independent of rank. -/
theorem actual_uniform_field_fixed_layer_product [Fintype F] [DecidableEq F]
    (k : ℕ) (hk : 0<k) {q M : ℕ} (hq : 0<q) (hM : q*(q+1)<M)
    (hF : (q+1)^q < Fintype.card F) (phi : Fin M → RingAut F) (d : Fin M → ℕ)
    (hd : ∀ i, 0<d i ∧ d i ∣ q) :
    ∃ lambda : Fin M → Fˣ, ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (b.val-1) →
      ∃ x : Fin M → Matrix.SpecialLinearGroup (Fin n) F,
        (∀ i, LayerDepth k ((x i).val-1)) ∧
        LayerDepth (k+1) (((NikolovSegal.orderedProduct (fun i =>
          (x i)⁻¹*((layerTorus k (lambda i)*fieldAut (phi i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d i)) (x i)))⁻¹*b).val-1) := by
  classical
  obtain ⟨l,hl,hs⟩ := lemma7_1 (c:=1) hq (by simpa using hM) (by simpa using hF)
    phi (fun _ => 1) d (fun _ => 1) (fun _ => one_ne_zero) hd (fun _ => by simp)
  let lambda : Fin M → Fˣ := fun i => Units.mk0 (l i) (hl i)
  refine ⟨lambda,?_⟩
  intro b hb
  have ht : ∀ j : Fin (n-k), ∃ t : Fin M → F,
      (∑ i, fieldValue (phi i) 1 (d i) 1 (l i) (t i))=(unitOdd% coordinate) k b j := by
    intro j; exact hs _
  choose t ht using ht
  let X : Fin M → Fin n → F := fun i row => if h : row.val<n-k then t ⟨row.val,h⟩ i else 0
  let x : Fin M → Matrix.SpecialLinearGroup (Fin n) F := fun i => stripUnit k hk (X i)
  have hx : ∀ i, LayerDepth k ((x i).val-1) := fun i => (unitOdd% strip_depth) k hk (X i)
  have hxc : ∀ i j, (unitOdd% coordinate) k (x i) j=t j i := by
    intro i j
    rw [(unitOdd% strip_coordinate)]
    simp only [X,dif_pos j.isLt]
  let A := fun i => (x i)⁻¹*((layerTorus k (lambda i)*fieldAut (phi i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d i)) (x i)
  have hA := fun i => layer_field_value k hk (lambda i) (phi i) (x i) (hx i) (d i)
  have hP := (unitOdd% ordered_layer) k hk A (fun i => (hA i).1)
  refine ⟨x,hx,?_⟩
  apply (unitOdd% agree_next) k hk _ b hP.1 hb
  intro j
  rw [hP.2 j]
  have he : ∀ i, (unitOdd% coordinate) k (A i) j=fieldValue (phi i) 1 (d i) 1 (l i) (t j i) := by
    intro i
    rw [(hA i).2 j,hxc i j]
    rfl
  simp only [he]
  exact ht j

/-- The complete FIELD-action branch of printed PartII Proposition6.5,
all finite matrix ranks. Four ordered batches and the one actual powered
proper correction cover the ENTIRE upper unitriangular group. Scalar
choices, diagonal corrections and u0 precede ALL targets; M and field
cutoff are independent of rank. The first/second layers are genuinely
solved and the residual is consumed by the full U3 reconstruction.
This is not graph-tuple/bare-auto/all-simple scalar supply. -/
theorem actual_uniform_field_U_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : q*(q+1)<M) (hF : (q+1)^q < Fintype.card F)
    (phi1 phi2 phiP phiN : Fin M → RingAut F) (d1 d2 dP dN : Fin M → ℕ)
    (hd1 : ∀ i, 0<d1 i ∧ d1 i ∣ q) (hd2 : ∀ i, 0<d2 i ∧ d2 i ∣ q)
    (hdP : ∀ i, 0<dP i ∧ dP i ∣ q) (hdN : ∀ i, 0<dN i ∧ dN i ∣ q)
    (phi0 : RingAut F) (d0 : ℕ) (hd0 : 0<d0 ∧ d0 ∣ q) :
    ∃ lambda1 lambda2 lambdaP lambdaN : Fin M → Fˣ, ∃ lambda0 : Fˣ,
      ∃ u0 : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth 1 (u0.val-1) ∧
      ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth 1 (b.val-1) →
        ∃ x1 x2 x z : Fin M → Matrix.SpecialLinearGroup (Fin n) F,
          ∃ y : Matrix.SpecialLinearGroup (Fin n) F,
          (∀ i, LayerDepth 1 ((x1 i).val-1) ∧ LayerDepth 1 ((x2 i).val-1) ∧
            LayerDepth 1 ((x i).val-1) ∧ LayerDepth 1 ((z i).val-1)) ∧ LayerDepth 1 (y.val-1) ∧
          NikolovSegal.orderedProduct (fun i => (x1 i)⁻¹*
            ((layerTorus 1 (lambda1 i)*fieldAut (phi1 i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d1 i)) (x1 i))*
          NikolovSegal.orderedProduct (fun i => (x2 i)⁻¹*
            ((layerTorus 2 (lambda2 i)*fieldAut (phi2 i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d2 i)) (x2 i))*
          NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
            ((parityTorus (lambdaP i)*fieldAut (phiP i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP i)) (x i))*
          NikolovSegal.orderedProduct (fun i => (z i)⁻¹*
            ((parityTorus ((lambdaN i)⁻¹)*fieldAut (phiN i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN i)) (z i))*
          (y⁻¹*((MulAut.conj u0*(heightTorus lambda0*fieldAut phi0) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d0) y)=b := by
  classical
  obtain ⟨lambda1,h1⟩ := actual_uniform_field_fixed_layer_product (n:=n) 1 (by decide) hq hM hF phi1 d1 hd1
  obtain ⟨lambda2,h2⟩ := actual_uniform_field_fixed_layer_product (n:=n) 2 (by decide) hq hM hF phi2 d2 hd2
  obtain ⟨lambdaP,lambdaN,lambda0,u0,hu0,h3⟩ :=
    PartIIUnitriangularLayersGlobal.actual_uniform_field_U3_product (n:=n) hq hM hF phiP phiN dP dN hdP hdN phi0 d0 hd0
  refine ⟨lambda1,lambda2,lambdaP,lambdaN,lambda0,u0,hu0,?_⟩
  intro b hb
  obtain ⟨x1,hx1,hr1⟩ := h1 b hb
  let P1 := NikolovSegal.orderedProduct (fun i => (x1 i)⁻¹*
    ((layerTorus 1 (lambda1 i)*fieldAut (phi1 i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d1 i)) (x1 i))
  let b2 := P1⁻¹*b
  obtain ⟨x2,hx2,hr2⟩ := h2 b2 hr1
  let P2 := NikolovSegal.orderedProduct (fun i => (x2 i)⁻¹*
    ((layerTorus 2 (lambda2 i)*fieldAut (phi2 i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d2 i)) (x2 i))
  let b3 := P2⁻¹*b2
  obtain ⟨x,z,y,hxz,hy,he⟩ := h3 b3 hr2
  refine ⟨x1,x2,x,z,y,?_,(unitLayer% depth_mono) hy (by decide),?_⟩
  · intro i
    exact ⟨hx1 i,(unitLayer% depth_mono) (hx2 i) (by decide),
      (unitLayer% depth_mono) (hxz i).1 (by decide),(unitLayer% depth_mono) (hxz i).2 (by decide)⟩
  · calc
      _ = P1*P2*(NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
          ((parityTorus (lambdaP i)*fieldAut (phiP i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP i)) (x i))*
          NikolovSegal.orderedProduct (fun i => (z i)⁻¹*
          ((parityTorus ((lambdaN i)⁻¹)*fieldAut (phiN i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN i)) (z i))*
          (y⁻¹*((MulAut.conj u0*(heightTorus lambda0*fieldAut phi0) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d0) y)) := by
        dsimp only [P1,P2]; group
      _ = P1*P2*b3 := by rw [he]
      _ = b := by dsimp only [b3,b2]; group
end NikolovSegal.PartIIUnitriangularFieldSupply
