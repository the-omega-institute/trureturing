/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphFixedLayers
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphFixedLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularGraphGlobal
import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularFieldSupply
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Lean Elab Term in
elab "unitFixed%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularFieldSupply"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularFieldSupply"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual fixed-layer kernel {id} not found"
namespace NikolovSegal.PartIIUnitriangularGraphFixedLayers
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularFieldSupply PartIIFieldMaps
universe u
variable {F : Type u} [Field F] {n : ℕ}
private def graphSign (k : ℕ) (eps : Bool) : F := if eps then (-1:F)^(k+1) else 1
private theorem graph_sign_square (k : ℕ) (eps : Bool) :
    (graphSign k eps:F)*(graphSign k eps:F)=1 := by
  cases eps
  · simp [graphSign]
  · change (-1:F)^(k+1)*(-1:F)^(k+1)=1
    rw [← pow_two,← pow_mul,mul_comm (k+1) 2,pow_mul]
    simp
private theorem graph_coordinate (k : ℕ) (hk : 0<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1))
    (i : Fin (n-k)) :
    (unitOdd% coordinate) k (positiveGraph a) i=(-1:F)^(k+1)*(unitOdd% coordinate) k a i.rev := by
  change (unitOdd% coordinate) k (heightTorus (-1:Fˣ) ((unitAction% rawGraph) a)) i=_
  rw [(unitGraph% height_coordinate),(unitGraph% raw_graph_coordinate) k hk a ha,pow_succ]
  simp only [Units.val_neg,Units.val_one]
  ring
private theorem field_graph_coordinate (phi : RingAut F) (eps : Bool)
    (k : ℕ) (hk : 0<k) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (i : Fin (n-k)) :
    (unitOdd% coordinate) k (fieldGraphAut phi eps a) i=
      (graphSign k eps:F)*phi ((unitOdd% coordinate) k a (if eps then i.rev else i)) := by
  cases eps
  · simpa only [fieldGraphAut,graphSign,Bool.false_eq_true,ite_false,mul_one,one_mul] using (unitOdd% field_coordinate) phi k a i
  · change (unitOdd% coordinate) k (fieldAut phi (positiveGraph a)) i=_
    rw [(unitOdd% field_coordinate),graph_coordinate k hk a ha]
    simp only [graphSign,ite_true,map_mul,map_pow,map_neg,map_one]
private theorem fixed_graph_depth (k : ℕ) (hk : 0<k) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (d : ℕ) :
    LayerDepth k ((((layerTorus k lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a).val-1) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using ha
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    exact (unitOdd% diagonal_depth) _ k _ ((unitGraph% field_graph_depth) phi eps k hk _ ih)
private theorem fixed_graph_step (k : ℕ) (hk : 0<k) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (i : Fin (n-k)) :
    (unitOdd% coordinate) k ((layerTorus k lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) a) i=
      (lambda:F)*(graphSign k eps:F)*phi ((unitOdd% coordinate) k a (if eps then i.rev else i)) := by
  rw [MulAut.mul_apply,(unitFixed% layer_torus_coordinate) k hk lambda,field_graph_coordinate phi eps k hk a ha]
  ring
private theorem fixed_graph_double (k : ℕ) (hk : 0<k) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (i : Fin (n-k)) :
    (unitOdd% coordinate) k (((layerTorus k lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^2) a) i=
      (lambda:F)*phi (lambda:F)*(phi^2) ((unitOdd% coordinate) k a i) := by
  have hb : LayerDepth k ((((layerTorus k lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) a).val-1)) := by
    simpa only [pow_one] using fixed_graph_depth k hk lambda phi eps a ha 1
  rw [pow_two,MulAut.mul_apply,fixed_graph_step k hk lambda phi eps _ hb,fixed_graph_step k hk lambda phi eps a ha,map_mul,map_mul]
  have hs : phi (graphSign k eps:F)=(graphSign k eps:F) := by cases eps <;> simp [graphSign,map_pow,map_neg,map_one]
  have hi : (if eps then (if eps then i.rev else i).rev else (if eps then i.rev else i))=i := by cases eps <;> simp
  rw [hs,hi]
  calc
    _ = (lambda:F)*phi (lambda:F)*((graphSign k eps:F)*(graphSign k eps:F))*(phi^2) ((unitOdd% coordinate) k a i) := by simp only [pow_two,RingAut.mul_apply]; ring
    _ = _ := by rw [graph_sign_square]; ring
private theorem fixed_graph_doubled_power (k : ℕ) (hk : 0<k) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (d : ℕ) :
    ∀ i : Fin (n-k), (unitOdd% coordinate) k
      (((layerTorus k lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(2*d)) a) i=
      orbitProduct phi (2*d) (lambda:F)*(phi^(2*d)) ((unitOdd% coordinate) k a i) := by
  induction d with
  | zero => intro i; simp [orbitProduct]
  | succ d ih =>
    intro i
    rw [show 2*(d+1)=2+2*d by omega,pow_add,MulAut.mul_apply,
      fixed_graph_double k hk lambda phi eps _ (fixed_graph_depth k hk lambda phi eps a ha _) i,ih i,map_mul]
    have hN : orbitProduct phi (2+2*d) (lambda:F)=
        (lambda:F)*phi (lambda:F)*phi (phi (orbitProduct phi (2*d) (lambda:F))) := by
      rw [show 2+2*d=(2*d+1)+1 by omega,(rootFieldKernel% orbitProduct_succ),
        (rootFieldKernel% orbitProduct_succ),map_mul]
      ring
    rw [hN]
    simp only [pow_two,pow_add,RingAut.mul_apply]
    ring
private theorem fixed_norm_value (k : ℕ) (hk : 0<k) (lambda : Fˣ)
    (phi : RingAut F) (eps : Bool) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (d : ℕ) :
    let beta : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := (layerTorus k lambda*fieldGraphAut phi eps)^d
    let x := a*beta a
    LayerDepth k (x.val-1) ∧ LayerDepth k ((x⁻¹*beta x).val-1) ∧
    ∀ i : Fin (n-k), (unitOdd% coordinate) k (x⁻¹*beta x) i=
      fieldValue phi 1 (2*d) 1 (lambda:F) ((unitOdd% coordinate) k a i) := by
  dsimp only
  let beta : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := (layerTorus k lambda*fieldGraphAut phi eps)^d
  let x := a*beta a
  have hb : LayerDepth k ((beta a).val-1) := fixed_graph_depth k hk lambda phi eps a ha d
  have hx : LayerDepth k (x.val-1) := (unitRec% product_depth) k hk a (beta a) ha hb
  have hbx : LayerDepth k ((beta x).val-1) := fixed_graph_depth k hk lambda phi eps x hx d
  refine ⟨hx,(unitRec% product_depth) k hk _ _ ((unitOdd% inverse_depth) k hk x hx) hbx,?_⟩
  intro i
  have he : beta (beta a)=((layerTorus k lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(2*d)) a := by
    simp only [beta,← MulAut.mul_apply,← pow_add,show d+d=2*d by omega]
  rw [(unitOdd% product_coordinate) k hk x⁻¹ (beta x) ((unitOdd% inverse_depth) k hk x hx) hbx,
    (unitOdd% inverse_coordinate) k hk x hx]
  change -(unitOdd% coordinate) k (a*beta a) i+(unitOdd% coordinate) k (beta (a*beta a)) i=_
  rw [map_mul,(unitOdd% product_coordinate) k hk a (beta a) ha hb,
    (unitOdd% product_coordinate) k hk (beta a) (beta (beta a)) hb
      (fixed_graph_depth k hk lambda phi eps (beta a) hb d),he,fixed_graph_doubled_power k hk lambda phi eps a ha d i]
  simp only [fieldValue,one_mul,pow_one]
  ring

/-- Actual fixed-layer PRODUCT for arbitrary field/positive-graph tuples.
It consumes doubled-exponent Lemma7.1 and actual norm witnesses to supply
the PRESCRIBED divisor powers. Both printed leading-layer batches follow,
including graph reversal signs in characteristic two. Corrections precede
every target and the quantitative constants are independent of rank. -/
theorem actual_uniform_field_graph_fixed_layer_product [Fintype F] [DecidableEq F]
    (k : ℕ) (hk : 0<k) {q M : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M)
    (hF : (2*q+1)^(2*q) < Fintype.card F)
    (phi : Fin M → RingAut F) (eps : Fin M → Bool) (d : Fin M → ℕ)
    (hd : ∀ i, 0<d i ∧ d i ∣ q) :
    ∃ lambda : Fin M → Fˣ, ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (b.val-1) →
      ∃ x : Fin M → Matrix.SpecialLinearGroup (Fin n) F,
        (∀ i, LayerDepth k ((x i).val-1)) ∧
        LayerDepth (k+1) (((NikolovSegal.orderedProduct (fun i =>
          (x i)⁻¹*((layerTorus k (lambda i)*fieldGraphAut (phi i) (eps i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d i)) (x i)))⁻¹*b).val-1) := by
  classical
  have hq2 : 0<2*q := by omega
  have hd2 : ∀ i, 0<2*d i ∧ 2*d i ∣ 2*q := fun i => ⟨by have h := (hd i).1; omega,Nat.mul_dvd_mul_left 2 (hd i).2⟩
  obtain ⟨l,hl,hs⟩ := lemma7_1 (c:=1) hq2 (by simpa using hM) (by simpa using hF)
    phi (fun _ => 1) (fun i => 2*d i) (fun _ => 1) (fun _ => one_ne_zero) hd2 (fun _ => by simp)
  let lambda : Fin M → Fˣ := fun i => Units.mk0 (l i) (hl i)
  refine ⟨lambda,?_⟩
  intro b hb
  have ht : ∀ j : Fin (n-k), ∃ t : Fin M → F,
      (∑ i, fieldValue (phi i) 1 (2*d i) 1 (l i) (t i))=(unitOdd% coordinate) k b j := by
    intro j; exact hs _
  choose t ht using ht
  let X : Fin M → Fin n → F := fun i row => if h : row.val<n-k then t ⟨row.val,h⟩ i else 0
  let a : Fin M → Matrix.SpecialLinearGroup (Fin n) F := fun i => stripUnit k hk (X i)
  let beta : Fin M → MulAut (Matrix.SpecialLinearGroup (Fin n) F) := fun i => (layerTorus k (lambda i)*fieldGraphAut (phi i) (eps i))^(d i)
  let x := fun i => a i*beta i (a i)
  have ha : ∀ i, LayerDepth k ((a i).val-1) := fun i => (unitOdd% strip_depth) k hk (X i)
  have hac : ∀ i j, (unitOdd% coordinate) k (a i) j=t j i := by
    intro i j; rw [(unitOdd% strip_coordinate)]; simp only [X,dif_pos j.isLt]
  let A := fun i => (x i)⁻¹*beta i (x i)
  have hA := fun i => fixed_norm_value k hk (lambda i) (phi i) (eps i) (a i) (ha i) (d i)
  have hP := (unitOdd% ordered_layer) k hk A (fun i => (hA i).2.1)
  refine ⟨x,fun i => (hA i).1,?_⟩
  apply (unitOdd% agree_next) k hk _ b hP.1 hb
  intro j
  rw [hP.2 j]
  have he : ∀ i, (unitOdd% coordinate) k (A i) j=fieldValue (phi i) 1 (2*d i) 1 (l i) (t j i) := by
    intro i; rw [(hA i).2.2 j,hac i j]; rfl
  simp only [he]
  exact ht j

/-- Full printed Proposition6.5 for actual prescribed field/positive-graph
tuples on arbitrary-rank SL. Four ordered batches and one proper final
correction cover the ENTIRE U. All divisor powers, reflection signs and
noncommutative accumulation are genuine. The single correction tuple
precedes every target; length 4M+1 and the cutoff are uniform in rank.
Bare automorphism normalization and full group assembly remain separate. -/
theorem actual_uniform_field_graph_U_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M) (hF : (2*q+1)^(2*q) < Fintype.card F)
    (phi1 phi2 phiP phiN : Fin M → RingAut F) (eps1 eps2 epsP epsN : Fin M → Bool) (d1 d2 dP dN : Fin M → ℕ)
    (hd1 : ∀ i, 0<d1 i ∧ d1 i ∣ q) (hd2 : ∀ i, 0<d2 i ∧ d2 i ∣ q)
    (hdP : ∀ i, 0<dP i ∧ dP i ∣ q) (hdN : ∀ i, 0<dN i ∧ dN i ∣ q)
    (phi0 : RingAut F) (eps0 : Bool) (d0 : ℕ) (hd0 : 0<d0 ∧ d0 ∣ q) :
    ∃ lambda1 lambda2 lambdaP lambdaN : Fin M → Fˣ, ∃ lambda0 : Fˣ,
      ∃ u0 : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth 1 (u0.val-1) ∧
      ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth 1 (b.val-1) →
        ∃ x1 x2 x z : Fin M → Matrix.SpecialLinearGroup (Fin n) F,
          ∃ y : Matrix.SpecialLinearGroup (Fin n) F,
          (∀ i, LayerDepth 1 ((x1 i).val-1) ∧ LayerDepth 1 ((x2 i).val-1) ∧
            LayerDepth 1 ((x i).val-1) ∧ LayerDepth 1 ((z i).val-1)) ∧ LayerDepth 1 (y.val-1) ∧
          NikolovSegal.orderedProduct (fun i => (x1 i)⁻¹*
            ((layerTorus 1 (lambda1 i)*fieldGraphAut (phi1 i) (eps1 i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d1 i)) (x1 i))*
          NikolovSegal.orderedProduct (fun i => (x2 i)⁻¹*
            ((layerTorus 2 (lambda2 i)*fieldGraphAut (phi2 i) (eps2 i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d2 i)) (x2 i))*
          NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
            ((PartIIUnitriangularGraphLayers.mirrorTorus (lambdaP i)*fieldGraphAut (phiP i) (epsP i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP i)) (x i))*
          NikolovSegal.orderedProduct (fun i => (z i)⁻¹*
            ((PartIIUnitriangularGraphLayers.mirrorTorus ((lambdaN i)⁻¹)*fieldGraphAut (phiN i) (epsN i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN i)) (z i))*
          (y⁻¹*((MulAut.conj u0*(heightTorus lambda0*fieldGraphAut phi0 eps0) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d0) y)=b := by
  classical
  obtain ⟨lambda1,h1⟩ := actual_uniform_field_graph_fixed_layer_product (n:=n) 1 (by decide) hq hM hF phi1 eps1 d1 hd1
  obtain ⟨lambda2,h2⟩ := actual_uniform_field_graph_fixed_layer_product (n:=n) 2 (by decide) hq hM hF phi2 eps2 d2 hd2
  obtain ⟨lambdaP,lambdaN,lambda0,u0,hu0,h3⟩ :=
    PartIIUnitriangularGraphGlobal.actual_uniform_field_graph_U3_product (n:=n) hq hM hF phiP phiN epsP epsN dP dN hdP hdN phi0 eps0 d0 hd0
  refine ⟨lambda1,lambda2,lambdaP,lambdaN,lambda0,u0,hu0,?_⟩
  intro b hb
  obtain ⟨x1,hx1,hr1⟩ := h1 b hb
  let P1 := NikolovSegal.orderedProduct (fun i => (x1 i)⁻¹*
    ((layerTorus 1 (lambda1 i)*fieldGraphAut (phi1 i) (eps1 i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d1 i)) (x1 i))
  let b2 := P1⁻¹*b
  obtain ⟨x2,hx2,hr2⟩ := h2 b2 hr1
  let P2 := NikolovSegal.orderedProduct (fun i => (x2 i)⁻¹*
    ((layerTorus 2 (lambda2 i)*fieldGraphAut (phi2 i) (eps2 i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(d2 i)) (x2 i))
  let b3 := P2⁻¹*b2
  obtain ⟨x,z,y,hxz,hy,he⟩ := h3 b3 hr2
  refine ⟨x1,x2,x,z,y,?_,(unitLayer% depth_mono) hy (by decide),?_⟩
  · intro i
    exact ⟨hx1 i,(unitLayer% depth_mono) (hx2 i) (by decide),
      (unitLayer% depth_mono) (hxz i).1 (by decide),(unitLayer% depth_mono) (hxz i).2 (by decide)⟩
  · calc
      _ = P1*P2*(NikolovSegal.orderedProduct (fun i => (x i)⁻¹*
          ((PartIIUnitriangularGraphLayers.mirrorTorus (lambdaP i)*fieldGraphAut (phiP i) (epsP i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP i)) (x i))*
          NikolovSegal.orderedProduct (fun i => (z i)⁻¹*
          ((PartIIUnitriangularGraphLayers.mirrorTorus ((lambdaN i)⁻¹)*fieldGraphAut (phiN i) (epsN i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN i)) (z i))*
          (y⁻¹*((MulAut.conj u0*(heightTorus lambda0*fieldGraphAut phi0 eps0) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d0) y)) := by
        dsimp only [P1,P2]; group
      _ = P1*P2*b3 := by rw [he]
      _ = b := by dsimp only [b3,b2]; group
end NikolovSegal.PartIIUnitriangularGraphFixedLayers
