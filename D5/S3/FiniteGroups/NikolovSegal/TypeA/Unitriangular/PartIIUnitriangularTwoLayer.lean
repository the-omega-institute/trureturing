/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularTwoLayer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularTwoLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularOddSupply
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Lean Elab Term in
elab "unitOdd%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIUnitriangularOddSupply"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularOddSupply"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual odd-layer kernel {id} not found"
namespace NikolovSegal.PartIIUnitriangularTwoLayer
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularOddSupply
universe u
variable {F : Type u} [Field F] {n : ℕ}
private def NextZero (k : ℕ) (a : Matrix.SpecialLinearGroup (Fin n) F) : Prop :=
  ∀ i : Fin (n-(k+1)), (unitOdd% coordinate) (k+1) a i=0
private theorem next_product (k : ℕ) (hk : 1<k)
    (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hb : LayerDepth k (b.val-1))
    (i : Fin (n-(k+1))) :
    (unitOdd% coordinate) (k+1) (a*b) i=
      (unitOdd% coordinate) (k+1) a i+(unitOdd% coordinate) (k+1) b i := by
  have he : (a*b).val-1=(a.val-1)*(b.val-1)+(a.val-1)+(b.val-1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
  have h0 := (unitLayer% depth_mul) ha hb ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩
    (by change i.val+(k+1) < i.val+(k+k); omega)
  have hij : (⟨i.val,by omega⟩ : Fin n) ≠ ⟨i.val+(k+1),by omega⟩ := by
    intro h; have hh := congrArg Fin.val h; change i.val=i.val+(k+1) at hh; omega
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) F => A ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩) he
  change (a*b) ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=a ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩+b ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩
  simpa only [Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply,if_neg hij,sub_zero,h0,zero_add] using h
private theorem next_inverse (k : ℕ) (hk : 1<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1))
    (hz : NextZero k a) : NextZero k a⁻¹ := by
  intro i
  have h := next_product k hk a a⁻¹ ha ((unitOdd% inverse_depth) k (by omega) a ha) i
  rw [mul_inv_cancel,(unitOdd% coordinate_one) (k+1) (by omega),hz i,zero_add] at h
  exact h.symm
private theorem next_zero_product (k : ℕ) (hk : 1<k)
    (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hb : LayerDepth k (b.val-1))
    (haz : NextZero k a) (hbz : NextZero k b) : NextZero k (a*b) := by
  intro i; rw [next_product k hk a b ha hb,haz i,hbz i,zero_add]
private theorem strip_next_zero (k : ℕ) (hk : 0<k) (t : Fin n → F) :
    NextZero k (stripUnit k hk t) := by
  intro i
  have hij : (⟨i.val,by omega⟩ : Fin n) ≠ ⟨i.val+(k+1),by omega⟩ := by
    intro h; have hh := congrArg Fin.val h; change i.val=i.val+(k+1) at hh; omega
  change (1+layerStrip k t) ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=0
  simp [Matrix.add_apply,Matrix.one_apply,hij,layerStrip]
private theorem field_next_zero (phi : RingAut F) (k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (hz : NextZero k a) :
    NextZero k (fieldAut phi a) := by
  intro i; rw [(unitOdd% field_coordinate),hz i,map_zero]
private theorem torus_next_zero (lambda : Fˣ) (k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (hz : NextZero k a) :
    NextZero k (heightTorus lambda a) := by
  intro i
  change (heightTorus lambda a) ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=0
  rw [(unitAction% torus_entry)]
  have h : a ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=0 := hz i
  rw [h,mul_zero,zero_mul]
private theorem parity_next_zero (lambda : Fˣ) (k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (hz : NextZero k a) :
    NextZero k (parityTorus lambda a) := by
  intro i
  change ((unitOdd% diagonalAut) (fun j : Fin n => lambda⁻¹^(j.val%2)) a) ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=0
  rw [(unitOdd% diagonal_entry)]
  have h : a ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=0 := hz i
  rw [h,mul_zero,zero_mul]
private theorem parity_power_next_zero (lambda : Fˣ) (phi : RingAut F)
    (k d : ℕ) (a : Matrix.SpecialLinearGroup (Fin n) F) (hz : NextZero k a) :
    NextZero k (((parityTorus lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using hz
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    exact parity_next_zero lambda k _ (field_next_zero phi k _ ih)
private theorem ordered_next_zero {M : ℕ} (k : ℕ) (hk : 1<k)
    (a : Fin M → Matrix.SpecialLinearGroup (Fin n) F)
    (ha : ∀ j, LayerDepth k ((a j).val-1)) (hz : ∀ j, NextZero k (a j)) :
    NextZero k (NikolovSegal.orderedProduct a) := by
  induction M with
  | zero => intro i; simpa only [NikolovSegal.orderedProduct,List.ofFn_zero,List.prod_nil] using (unitOdd% coordinate_one) (k+1) (by omega) i
  | succ M ih =>
    have ht := (unitOdd% ordered_layer) k (by omega) (fun j => a j.succ) (fun j => ha j.succ)
    have he : NikolovSegal.orderedProduct a=a 0*NikolovSegal.orderedProduct (fun j => a j.succ) := by
      simp only [NikolovSegal.orderedProduct,List.ofFn_succ,List.prod_cons]
    rw [he]
    exact next_zero_product k hk _ _ (ha 0) ht.1 (hz 0) (ih _ (fun j => ha j.succ) (fun j => hz j.succ))

private theorem torus_field_inverse_preserves (lambda : Fˣ) (phi : RingAut F)
    (d k : ℕ) (a : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hz : NextZero k a) :
    LayerDepth k (((((heightTorus lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d)⁻¹) a).val-1) ∧
      NextZero k ((((heightTorus lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d)⁻¹) a) := by
  have he : (heightTorus lambda : MulAut (Matrix.SpecialLinearGroup (Fin n) F))⁻¹=heightTorus lambda⁻¹ := by
    apply MulEquiv.ext; intro g; rfl
  have hf : (fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))⁻¹=fieldAut phi.symm := by
    apply MulEquiv.ext; intro g; rfl
  rw [← inv_pow,mul_inv_rev,he,hf]
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using ⟨ha,hz⟩
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    exact ⟨(unitOdd% field_depth) phi.symm k _ ((unitAction% torus_depth) lambda⁻¹ k _ ih.1),
      field_next_zero phi.symm k _ (torus_next_zero lambda⁻¹ k _ ih.2)⟩

private theorem agree_two (k : ℕ) (hk : 0<k)
    (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hb : LayerDepth k (b.val-1))
    (h1 : ∀ i : Fin (n-k), (unitOdd% coordinate) k a i=(unitOdd% coordinate) k b i)
    (h2 : ∀ i : Fin (n-(k+1)), (unitOdd% coordinate) (k+1) a i=(unitOdd% coordinate) (k+1) b i) :
    LayerDepth (k+2) ((a⁻¹*b).val-1) := by
  have hd : LayerDepth (k+2) (b.val-a.val) := by
    intro i j hij
    by_cases hlt : j.val < i.val+k
    · have h1 := ha i j hlt
      have h2 := hb i j hlt
      simp only [Matrix.sub_apply] at h1 h2 ⊢
      rw [sub_eq_zero.mp h1,sub_eq_zero.mp h2,sub_self]
    · by_cases he : j.val=i.val+k
      · have hi : i.val<n-k := by omega
        have hi' : (⟨i.val,by omega⟩ : Fin n)=i := Fin.ext rfl
        have hj' : (⟨i.val+k,by omega⟩ : Fin n)=j := Fin.ext he.symm
        have h := h1 ⟨i.val,hi⟩
        change a ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩=b ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩ at h
        rw [hi',hj'] at h
        exact sub_eq_zero.mpr h.symm
      · have he : j.val=i.val+(k+1) := by omega
        have hi : i.val<n-(k+1) := by omega
        have hi' : (⟨i.val,by omega⟩ : Fin n)=i := Fin.ext rfl
        have hj' : (⟨i.val+(k+1),by omega⟩ : Fin n)=j := Fin.ext he.symm
        have h := h2 ⟨i.val,hi⟩
        change a ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩=b ⟨i.val,by omega⟩ ⟨i.val+(k+1),by omega⟩ at h
        rw [hi',hj'] at h
        exact sub_eq_zero.mpr h.symm
  have hh := (unitLayer% depth_mul) ((unitLift% inverse_upper) a ((unitLayer% depth_mono) ha hk)) hd
  have he : (a⁻¹*b).val-1=(a⁻¹).val*(b.val-a.val) := by
    rw [mul_sub,← Matrix.SpecialLinearGroup.coe_mul,← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
  rw [he]
  simpa only [Nat.zero_add] using hh
private theorem coordinate_eq_of_residual (k : ℕ) (hk : 0<k)
    (a b : Matrix.SpecialLinearGroup (Fin n) F)
    (ha : LayerDepth k (a.val-1)) (hb : LayerDepth k (b.val-1))
    (hr : LayerDepth (k+1) ((a⁻¹*b).val-1)) :
    ∀ i : Fin (n-k), (unitOdd% coordinate) k a i=(unitOdd% coordinate) k b i := by
  intro i
  have h := (unitOdd% product_coordinate) k hk a⁻¹ b ((unitOdd% inverse_depth) k hk a ha) hb i
  rw [(unitOdd% inverse_coordinate) k hk a ha] at h
  have h0 : (unitOdd% coordinate) k (a⁻¹*b) i=0 := by
    have h := hr ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩ (by change i.val+k < i.val+(k+1); omega)
    have hij : (⟨i.val,by omega⟩ : Fin n) ≠ ⟨i.val+k,by omega⟩ := by
      intro h; have hh := congrArg Fin.val h; change i.val=i.val+k at hh; omega
    change (a⁻¹*b) ⟨i.val,by omega⟩ ⟨i.val+k,by omega⟩=0
    simpa only [Matrix.sub_apply,Matrix.one_apply,if_neg hij,sub_zero] using h
  rw [h0] at h
  exact neg_add_eq_zero.mp h.symm

private theorem proper_inverse (g : Matrix.SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val-1))
    (hp : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0) :
    ∀ i : ℕ, ∀ hi : i+1<n, g⁻¹ ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0 := by
  intro i hi
  rw [(unitAction% adjacent_inverse) g hg i hi]
  exact neg_ne_zero.mpr (hp i hi)

private theorem even_branch (lambda0 : Fˣ) (phi0 : RingAut F) (d0 k : ℕ)
    (hk : 1<k) (g b : Matrix.SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val-1))
    (hp : ∀ i : ℕ, ∀ hi : i+1<n, g ⟨i,by omega⟩ ⟨i+1,hi⟩ ≠ 0) :
    ∃ y : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (y.val-1) ∧
      LayerDepth k ((y⁻¹*(MulAut.conj g*
        (heightTorus lambda0*fieldAut phi0)^d0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) y).val-1) ∧
      ∀ i : Fin (n-(k+1)),
        (unitOdd% coordinate) (k+1) (y⁻¹*(MulAut.conj g*
          (heightTorus lambda0*fieldAut phi0)^d0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) y) i=(unitOdd% coordinate) (k+1) b i := by
  let beta0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := (heightTorus lambda0*fieldAut phi0)^d0
  have hgi := (unitLayer% inverse_unit_depth) g hg
  obtain ⟨s,hs⟩ := actual_proper_layer_bracket_surjective k g⁻¹.val (proper_inverse g hg hp)
    (fun i => (unitOdd% coordinate) (k+1) b i)
  let z := stripUnit k (by omega : 0<k) s
  have hz : LayerDepth k (z.val-1) := (unitOdd% strip_depth) k (by omega) s
  let y := beta0⁻¹ z
  have hy := torus_field_inverse_preserves lambda0 phi0 d0 k z hz (strip_next_zero k (by omega) s)
  let L := y⁻¹*z
  let R := z⁻¹*g*z*g⁻¹
  have hL : LayerDepth k (L.val-1) := (unitRec% product_depth) k (by omega) y⁻¹ z
    ((unitOdd% inverse_depth) k (by omega) y hy.1) hz
  have hLz : NextZero k L := next_zero_product k hk y⁻¹ z
    ((unitOdd% inverse_depth) k (by omega) y hy.1) hz (next_inverse k hk y hy.1 hy.2)
    (strip_next_zero k (by omega) s)
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
    rw [he,next_product k hk L R hL ((unitLayer% depth_mono) hRd (by omega)),hLz i,hRv i,zero_add]

/-- Genuine two-layer equation(16) lift, PartII pp266--267, for arbitrary
prescribed FIELD tuples. Actual scalar PRODUCT arithmetic fixes alternating
corrections before all heights/targets. The real Lemma9.1 correction supplies
 the adjacent even coordinate; its noncommutative final factor is retained.
This proves simultaneous kth/(k+1)st equations modulo U(k+2), not full U3
coverage, graph-tuple coverage or the all-simple uniform supplier. -/
theorem actual_uniform_field_two_layer_lift [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : q*(q+1)<M) (hF : (q+1)^q < Fintype.card F)
    (phiP phiN : Fin M → RingAut F) (dP dN : Fin M → ℕ)
    (hdP : ∀ j, 0<dP j ∧ dP j ∣ q) (hdN : ∀ j, 0<dN j ∧ dN j ∣ q)
    (phi0 : RingAut F) (d0 : ℕ) (hd0 : 0<d0 ∧ d0 ∣ q) :
    ∃ lambdaP lambdaN : Fin M → Fˣ, ∃ lambda0 : Fˣ, ∃ u0 : Matrix.SpecialLinearGroup (Fin n) F,
      LayerDepth 1 (u0.val-1) ∧ ∀ k : ℕ, 1<k → k%2=1 →
        ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth k (b.val-1) →
        ∃ x z : Fin M → Matrix.SpecialLinearGroup (Fin n) F, ∃ y : Matrix.SpecialLinearGroup (Fin n) F,
          (∀ j, LayerDepth k ((x j).val-1) ∧ LayerDepth k ((z j).val-1)) ∧ LayerDepth k (y.val-1) ∧
          LayerDepth (k+2) (((NikolovSegal.orderedProduct (fun j =>
            (x j)⁻¹*((parityTorus (lambdaP j)*fieldAut (phiP j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP j)) (x j))*
            NikolovSegal.orderedProduct (fun j =>
            (z j)⁻¹*((parityTorus ((lambdaN j)⁻¹)*fieldAut (phiN j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN j)) (z j))*
            (y⁻¹*((MulAut.conj u0*(heightTorus lambda0*fieldAut phi0) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d0) y))⁻¹*b).val-1) := by
  classical
  obtain ⟨lambdaP,lambdaN,hodd⟩ := actual_uniform_field_odd_layer_product (n:=n) hq hM hF phiP phiN dP dN hdP hdN
  have hdle : d0≤q := Nat.le_of_dvd hq hd0.2
  have hF0 : (d0+1)^d0 < Fintype.card F := lt_of_le_of_lt
    ((Nat.pow_le_pow_left (by omega : d0+1≤q+1) d0).trans (Nat.pow_le_pow_right (by omega : 0<q+1) hdle)) hF
  obtain ⟨lambda0,u0,g,hu,hg,_,hp,he⟩ := PartIIUnitriangularProper.lemma9_1_actual_powered_proper_matrix phi0 false d0 hd0.1 hF0
  have he' : (MulAut.conj u0*(heightTorus lambda0*fieldAut phi0))^d0=
      MulAut.conj g*(heightTorus lambda0*fieldAut phi0)^d0 := by
    simpa only [fieldGraphAut,Bool.false_eq_true,ite_false,mul_one] using he
  refine ⟨lambdaP,lambdaN,lambda0,u0,hu,?_⟩
  intro k hk hko b hb
  obtain ⟨y,hy,hB,hBv⟩ := even_branch lambda0 phi0 d0 k hk g b hg hp
  let B := y⁻¹*(MulAut.conj g*(heightTorus lambda0*fieldAut phi0)^d0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) y
  let target := b*B⁻¹
  have hd : LayerDepth k (target.val-1) := (unitRec% product_depth) k (by omega) b B⁻¹ hb
    ((unitOdd% inverse_depth) k (by omega) B hB)
  obtain ⟨x,z,hxz,hstrip,hres⟩ := hodd k (by omega) hko target hd
  let AP := fun j => (x j)⁻¹*((parityTorus (lambdaP j)*fieldAut (phiP j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP j)) (x j)
  let AN := fun j => (z j)⁻¹*((parityTorus ((lambdaN j)⁻¹)*fieldAut (phiN j) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN j)) (z j)
  have hAP := fun j => (unitOdd% actual_odd_value) (lambdaP j) (phiP j) (dP j) k (by omega) hko (x j) (hxz j).1
  have hAN := fun j => (unitOdd% actual_odd_value) ((lambdaN j)⁻¹) (phiN j) (dN j) k (by omega) hko (z j) (hxz j).2
  have hPP := (unitOdd% ordered_layer) k (by omega) AP (fun j => (hAP j).1)
  have hPN := (unitOdd% ordered_layer) k (by omega) AN (fun j => (hAN j).1)
  let A := NikolovSegal.orderedProduct AP*NikolovSegal.orderedProduct AN
  have hA : LayerDepth k (A.val-1) := (unitRec% product_depth) k (by omega) _ _ hPP.1 hPN.1
  have hAz : NextZero k A := by
    have hAPz : ∀ j, NextZero k (AP j) := by
      intro j
      obtain ⟨s,t,hs,ht⟩ := hstrip j
      have hz : NextZero k (x j) := by rw [hs]; exact strip_next_zero k (by omega) s
      exact next_zero_product k hk _ _ ((unitOdd% inverse_depth) k (by omega) _ (hxz j).1)
        ((unitOdd% parity_field_power) (lambdaP j) (phiP j) k hko _ (hxz j).1 (dP j)).1
        (next_inverse k hk _ (hxz j).1 hz) (parity_power_next_zero (lambdaP j) (phiP j) k (dP j) _ hz)
    have hANz : ∀ j, NextZero k (AN j) := by
      intro j
      obtain ⟨s,t,hs,ht⟩ := hstrip j
      have hz : NextZero k (z j) := by rw [ht]; exact strip_next_zero k (by omega) t
      exact next_zero_product k hk _ _ ((unitOdd% inverse_depth) k (by omega) _ (hxz j).2)
        ((unitOdd% parity_field_power) ((lambdaN j)⁻¹) (phiN j) k hko _ (hxz j).2 (dN j)).1
        (next_inverse k hk _ (hxz j).2 hz) (parity_power_next_zero ((lambdaN j)⁻¹) (phiN j) k (dN j) _ hz)
    exact next_zero_product k hk _ _ hPP.1 hPN.1
      (ordered_next_zero k hk AP (fun j => (hAP j).1) hAPz)
      (ordered_next_zero k hk AN (fun j => (hAN j).1) hANz)
  have hAv := coordinate_eq_of_residual k (by omega) A target hA hd hres
  refine ⟨x,z,y,hxz,hy,?_⟩
  rw [he']
  apply agree_two k (by omega) (A*B) b ((unitRec% product_depth) k (by omega) A B hA hB) hb
  · intro i
    rw [(unitOdd% product_coordinate) k (by omega) A B hA hB,hAv i,
      (unitOdd% product_coordinate) k (by omega) b B⁻¹ hb ((unitOdd% inverse_depth) k (by omega) B hB),
      (unitOdd% inverse_coordinate) k (by omega) B hB]
    ring
  · intro i
    rw [next_product k hk A B hA hB,hAz i,hBv i,zero_add]
end NikolovSegal.PartIIUnitriangularTwoLayer
