/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphTwoLayer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphTwoLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularGraphOddSupply
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Lean Elab Term in
elab "unitTwo%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularTwoLayer"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularTwoLayer"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual two-layer kernel {id} not found"
namespace NikolovSegal.PartIIUnitriangularGraphTwoLayer
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularGraphLayers
universe u
variable {F : Type u} [Field F] {n : ℕ}
private theorem raw_graph_next_zero (k : ℕ) (hk : 1<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hz : (unitTwo% NextZero) k a) :
    (unitTwo% NextZero) k ((unitAction% rawGraph) a) := by
  have hi := (unitTwo% next_inverse) k hk a ha hz
  intro i
  change ((unitAction% rawGraph) a) ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=0
  rw [(unitAction% rawGraph_entry)]
  have h1 : (⟨i.val+(k+1),by omega⟩ : Fin n).rev=⟨i.rev.val,by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_rev]; omega
  have h2 : (⟨i.val,by omega⟩ : Fin n).rev=⟨i.rev.val+(k+1),by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_rev]; omega
  rw [h1,h2]
  exact hi i.rev
private theorem field_graph_next_zero (phi : RingAut F) (eps : Bool) (k : ℕ) (hk : 1<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hz : (unitTwo% NextZero) k a) :
    (unitTwo% NextZero) k (fieldGraphAut phi eps a) := by
  cases eps
  · exact (unitTwo% field_next_zero) phi k a hz
  · exact (unitTwo% field_next_zero) phi k _ ((unitTwo% torus_next_zero) (-1:Fˣ) k _ (raw_graph_next_zero k hk a ha hz))
private theorem mirror_next_zero (lambda : Fˣ) (k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (hz : (unitTwo% NextZero) k a) :
    (unitTwo% NextZero) k (mirrorTorus lambda a) := by
  intro i
  change ((unitOdd% diagonalAut) (fun j : Fin n => lambda ^ mirrorWeight n j.val) a)
    ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=0
  rw [(unitOdd% diagonal_entry)]
  have h : a ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=0 := hz i
  rw [h,mul_zero,zero_mul]
private theorem mirror_power_next_zero (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (k d : ℕ) (hk : 1<k) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hz : (unitTwo% NextZero) k a) :
    (unitTwo% NextZero) k (((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using hz
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    exact mirror_next_zero lambda k _ (field_graph_next_zero phi eps k hk _
      ((unitGraph% mirror_graph_depth) lambda phi eps k (by omega) a ha d) ih)
private theorem inverse_preserves_finite {G : Type*} [Group G] [Finite G]
    (alpha : MulAut G) (P : G → Prop) (h : ∀ a, P a → P (alpha a))
    (a : G) (ha : P a) : P (alpha⁻¹ a) := by
  let f : {a : G // P a} → {a : G // P a} := fun b => ⟨alpha b.val,h b.val b.prop⟩
  have hi : Function.Injective f := by
    intro b c he
    apply Subtype.ext
    exact alpha.injective (congrArg Subtype.val he)
  obtain ⟨b,hb⟩ := Finite.surjective_of_injective hi ⟨a,ha⟩
  have he : alpha b.val=a := congrArg Subtype.val hb
  have he' : b.val=alpha⁻¹ a := by rw [← he]; exact (MulAut.inv_apply_self G alpha b.val).symm
  rw [← he']; exact b.prop
private theorem torus_graph_inverse_preserves [Fintype F] (lambda : Fˣ) (phi : RingAut F)
    (eps : Bool) (d k : ℕ) (hk : 1<k) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hz : (unitTwo% NextZero) k a) :
    LayerDepth k (((((heightTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d)⁻¹) a).val-1) ∧
      (unitTwo% NextZero) k ((((heightTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d)⁻¹) a) := by
  apply inverse_preserves_finite _ (fun b => LayerDepth k (b.val-1) ∧ (unitTwo% NextZero) k b) _ a ⟨ha,hz⟩
  intro b hb
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using hb
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    exact ⟨(unitAction% torus_depth) lambda k _ ((unitGraph% field_graph_depth) phi eps k (by omega) _ ih.1),
      (unitTwo% torus_next_zero) lambda k _ (field_graph_next_zero phi eps k hk _ ih.1 ih.2)⟩
private theorem graph_value_depth (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (d k : ℕ) (hk : 0<k) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((a⁻¹*((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a).val-1) :=
  (unitRec% product_depth) k hk _ _ ((unitOdd% inverse_depth) k hk a ha)
    ((unitGraph% mirror_graph_depth) lambda phi eps k hk a ha d)
private theorem norm_next_zero (lambda : Fˣ) (phi : RingAut F) (eps : Bool)
    (d k : ℕ) (hk : 1<k) (t : Fin n → F) :
    (unitTwo% NextZero) k (stripUnit k (by omega) t*
      ((mirrorTorus lambda*fieldGraphAut phi eps : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) (stripUnit k (by omega) t)) :=
  (unitTwo% next_zero_product) k hk _ _ ((unitOdd% strip_depth) k (by omega) t)
    ((unitGraph% mirror_graph_depth) lambda phi eps k (by omega) _ ((unitOdd% strip_depth) k (by omega) t) d)
    ((unitTwo% strip_next_zero) k (by omega) t)
    (mirror_power_next_zero lambda phi eps k d hk _ ((unitOdd% strip_depth) k (by omega) t) ((unitTwo% strip_next_zero) k (by omega) t))
private theorem even_branch [Fintype F] (lambda0 : Fˣ) (phi0 : RingAut F) (eps0 : Bool) (d0 k : ℕ)
    (hk : 1<k) (g b : Matrix.SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val-1))
    (hp : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0) :
    ∃ y : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (y.val-1) ∧
      LayerDepth k ((y⁻¹*(MulAut.conj g*
        (heightTorus lambda0*fieldGraphAut phi0 eps0)^d0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) y).val-1) ∧
      ∀ i : Fin (n-(k+1)),
        (unitOdd% coordinate) (k+1) (y⁻¹*(MulAut.conj g*
          (heightTorus lambda0*fieldGraphAut phi0 eps0)^d0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) y) i=(unitOdd% coordinate) (k+1) b i := by
  let beta0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := (heightTorus lambda0*fieldGraphAut phi0 eps0)^d0
  have hgi := (unitLayer% inverse_unit_depth) g hg
  obtain ⟨s,hs⟩ := actual_proper_layer_bracket_surjective k g⁻¹.val ((unitTwo% proper_inverse) g hg hp)
    (fun i => (unitOdd% coordinate) (k+1) b i)
  let z := stripUnit k (by omega : 0<k) s
  have hz : LayerDepth k (z.val-1) := (unitOdd% strip_depth) k (by omega) s
  let y := beta0⁻¹ z
  have hy := torus_graph_inverse_preserves lambda0 phi0 eps0 d0 k hk z hz ((unitTwo% strip_next_zero) k (by omega) s)
  let L := y⁻¹*z
  let R := z⁻¹*g*z*g⁻¹
  have hL : LayerDepth k (L.val-1) := (unitRec% product_depth) k (by omega) y⁻¹ z
    ((unitOdd% inverse_depth) k (by omega) y hy.1) hz
  have hLz : (unitTwo% NextZero) k L := (unitTwo% next_zero_product) k hk y⁻¹ z
    ((unitOdd% inverse_depth) k (by omega) y hy.1) hz ((unitTwo% next_inverse) k hk y hy.1 hy.2)
    ((unitTwo% strip_next_zero) k (by omega) s)
  have hR := (unitLayer% actual_group_layer_identity) k (by omega) s g⁻¹ hgi
  have hRd : LayerDepth (k+1) (R.val-1) := by simpa only [inv_inv] using hR.1
  have hRv : ∀ i : Fin (n-(k+1)), (unitOdd% coordinate) (k+1) R i=(unitOdd% coordinate) (k+1) b i := by
    intro i
    have hv := hR.2 i.val (by omega)
    have hsi := hs i
    have hij : (⟨i.val,by omega⟩ : Fin n) ≠ ⟨i.val+(k+1),by omega⟩ := by
      intro h; have hh := congrArg Fin.val h; change i.val=i.val+(k+1) at hh; omega
    have hij' : (⟨i.val,by omega⟩ : Fin n) ≠ ⟨i.val+k+1,by omega⟩ := by
      intro h; have hh := congrArg Fin.val h; change i.val=i.val+k+1 at hh; omega
    simp only [inv_inv,Matrix.sub_apply,Matrix.one_apply,if_neg hij',sub_zero] at hv
    change R ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=_
    convert hv.trans hsi using 1 <;> congr 1 <;> omega
  have hb0 : beta0 y=z := MulAut.apply_inv_self _ beta0 z
  have he : y⁻¹*(MulAut.conj g*beta0) y=L*R := by
    rw [MulAut.mul_apply,MulAut.conj_apply,hb0]
    dsimp only [L,R]
    group
  refine ⟨y,hy.1,?_,?_⟩
  · rw [he]
    exact (unitRec% product_depth) k (by omega) L R hL ((unitLayer% depth_mono) hRd (by omega))
  · intro i
    rw [he,(unitTwo% next_product) k hk L R hL ((unitLayer% depth_mono) hRd (by omega)),hLz i,hRv i,zero_add]


/-- Genuine coupled odd/even equation(16) for arbitrary field/positive-graph
and prescribed positive divisor tuples. The actual norm strip witnesses
supply zero next-layer coordinates. One actual proper final correction,
chosen before every target, supplies the even coordinate. No whole-block
or local-coverage premise occurs. -/
theorem actual_uniform_field_graph_two_layer_lift [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : (2*q)*(2*q+1)<M) (hF : (2*q+1)^(2*q) < Fintype.card F)
    (phiP phiN : Fin M → RingAut F) (epsP epsN : Fin M → Bool) (dP dN : Fin M → ℕ)
    (hdP : ∀ j, 0<dP j ∧ dP j ∣ q) (hdN : ∀ j, 0<dN j ∧ dN j ∣ q)
    (phi0 : RingAut F) (eps0 : Bool) (d0 : ℕ) (hd0 : 0<d0 ∧ d0 ∣ q) :
    ∃ lambdaP lambdaN : Fin M → Fˣ, ∃ lambda0 : Fˣ, ∃ u0 : Matrix.SpecialLinearGroup (Fin n) F,
      LayerDepth 1 (u0.val-1) ∧ ∀ k : ℕ, 1<k → k%2=1 →
        ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (b.val-1) →
        ∃ x z : Fin M → Matrix.SpecialLinearGroup (Fin n) F, ∃ y : Matrix.SpecialLinearGroup (Fin n) F,
          (∀ j, LayerDepth k ((x j).val-1) ∧ LayerDepth k ((z j).val-1)) ∧ LayerDepth k (y.val-1) ∧
          LayerDepth (k+2) (((NikolovSegal.orderedProduct (fun j =>
            (x j)⁻¹*((mirrorTorus (lambdaP j)*fieldGraphAut (phiP j) (epsP j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP j)) (x j))*
            NikolovSegal.orderedProduct (fun j =>
            (z j)⁻¹*((mirrorTorus ((lambdaN j)⁻¹)*fieldGraphAut (phiN j) (epsN j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN j)) (z j))*
            (y⁻¹*((MulAut.conj u0*(heightTorus lambda0*fieldGraphAut phi0 eps0) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d0) y))⁻¹*b).val-1) := by
  classical
  obtain ⟨lambdaP,lambdaN,hodd⟩ := PartIIUnitriangularGraphOddSupply.actual_uniform_field_graph_odd_layer_product (n:=n) hq hM hF phiP phiN epsP epsN dP dN hdP hdN
  have hdle : d0≤2*q := (Nat.le_of_dvd hq hd0.2).trans (by omega)
  have hF0 : (d0+1)^d0 < Fintype.card F := lt_of_le_of_lt
    ((Nat.pow_le_pow_left (by omega : d0+1≤2*q+1) d0).trans (Nat.pow_le_pow_right (by omega : 0<2*q+1) hdle)) hF
  obtain ⟨lambda0,u0,g,hu,hg,_,hp,he⟩ := PartIIUnitriangularProper.lemma9_1_actual_powered_proper_matrix phi0 eps0 d0 hd0.1 hF0
  have he' : (MulAut.conj u0*(heightTorus lambda0*fieldGraphAut phi0 eps0))^d0=
      MulAut.conj g*(heightTorus lambda0*fieldGraphAut phi0 eps0)^d0 := by
    exact he
  refine ⟨lambdaP,lambdaN,lambda0,u0,hu,?_⟩
  intro k hk hko b hb
  obtain ⟨y,hy,hB,hBv⟩ := even_branch lambda0 phi0 eps0 d0 k hk g b hg hp
  let B := y⁻¹*(MulAut.conj g*(heightTorus lambda0*fieldGraphAut phi0 eps0)^d0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) y
  let target := b*B⁻¹
  have hd : LayerDepth k (target.val-1) := (unitRec% product_depth) k (by omega) b B⁻¹ hb
    ((unitOdd% inverse_depth) k (by omega) B hB)
  obtain ⟨x,z,hxz,hstrip,hres⟩ := hodd k (by omega) hko target hd
  let AP := fun j => (x j)⁻¹*((mirrorTorus (lambdaP j)*fieldGraphAut (phiP j) (epsP j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP j)) (x j)
  let AN := fun j => (z j)⁻¹*((mirrorTorus ((lambdaN j)⁻¹)*fieldGraphAut (phiN j) (epsN j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN j)) (z j)
  have hAP := fun j => graph_value_depth (lambdaP j) (phiP j) (epsP j) (dP j) k (by omega) (x j) (hxz j).1
  have hAN := fun j => graph_value_depth ((lambdaN j)⁻¹) (phiN j) (epsN j) (dN j) k (by omega) (z j) (hxz j).2
  have hPP := (unitOdd% ordered_layer) k (by omega) AP (fun j => hAP j)
  have hPN := (unitOdd% ordered_layer) k (by omega) AN (fun j => hAN j)
  let A := NikolovSegal.orderedProduct AP*NikolovSegal.orderedProduct AN
  have hA : LayerDepth k (A.val-1) := (unitRec% product_depth) k (by omega) _ _ hPP.1 hPN.1
  have hAz : (unitTwo% NextZero) k A := by
    have hAPz : ∀ j, (unitTwo% NextZero) k (AP j) := by
      intro j
      obtain ⟨s,t,hs,ht⟩ := hstrip j
      have hz : (unitTwo% NextZero) k (x j) := by rw [hs]; exact norm_next_zero (lambdaP j) (phiP j) (epsP j) (dP j) k hk s
      exact (unitTwo% next_zero_product) k hk _ _ ((unitOdd% inverse_depth) k (by omega) _ (hxz j).1)
        ((unitGraph% mirror_graph_depth) (lambdaP j) (phiP j) (epsP j) k (by omega) _ (hxz j).1 (dP j))
        ((unitTwo% next_inverse) k hk _ (hxz j).1 hz) (mirror_power_next_zero (lambdaP j) (phiP j) (epsP j) k (dP j) hk _ (hxz j).1 hz)
    have hANz : ∀ j, (unitTwo% NextZero) k (AN j) := by
      intro j
      obtain ⟨s,t,hs,ht⟩ := hstrip j
      have hz : (unitTwo% NextZero) k (z j) := by rw [ht]; exact norm_next_zero ((lambdaN j)⁻¹) (phiN j) (epsN j) (dN j) k hk t
      exact (unitTwo% next_zero_product) k hk _ _ ((unitOdd% inverse_depth) k (by omega) _ (hxz j).2)
        ((unitGraph% mirror_graph_depth) ((lambdaN j)⁻¹) (phiN j) (epsN j) k (by omega) _ (hxz j).2 (dN j))
        ((unitTwo% next_inverse) k hk _ (hxz j).2 hz) (mirror_power_next_zero ((lambdaN j)⁻¹) (phiN j) (epsN j) k (dN j) hk _ (hxz j).2 hz)
    exact (unitTwo% next_zero_product) k hk _ _ hPP.1 hPN.1
      ((unitTwo% ordered_next_zero) k hk AP (fun j => hAP j) hAPz)
      ((unitTwo% ordered_next_zero) k hk AN (fun j => hAN j) hANz)
  have hAv := (unitTwo% coordinate_eq_of_residual) k (by omega) A target hA hd hres
  refine ⟨x,z,y,hxz,hy,?_⟩
  rw [he']
  apply (unitTwo% agree_two) k (by omega) (A*B) b ((unitRec% product_depth) k (by omega) A B hA hB) hb
  · intro i
    rw [(unitOdd% product_coordinate) k (by omega) A B hA hB,hAv i,
      (unitOdd% product_coordinate) k (by omega) b B⁻¹ hb ((unitOdd% inverse_depth) k (by omega) B hB),
      (unitOdd% inverse_coordinate) k (by omega) B hB]
    ring
  · intro i
    rw [(unitTwo% next_product) k hk A B hA hB,hAz i,hBv i,zero_add]
end NikolovSegal.PartIIUnitriangularGraphTwoLayer
