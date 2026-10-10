/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayersGlobal
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLayersGlobal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIUnitriangularTwoLayer
import Mathlib.GroupTheory.QuotientGroup.Basic
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace NikolovSegal.PartIIUnitriangularLayersGlobal
open PartIIUnitriangularLayers PartIIUnitriangularActions PartIIUnitriangularOddSupply
universe u
variable {F : Type u} [Field F] {n : ℕ}

private def U : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) where
  carrier := {g | LayerDepth 1 (g.val-1)}
  one_mem' := by intro i j hij; simp
  mul_mem' := by intro a b ha hb; exact (unitRec% product_depth) 1 (by decide) a b ha hb
  inv_mem' := by intro a ha; exact (unitOdd% inverse_depth) 1 (by decide) a ha
private def layer (k : ℕ) : Subgroup (U (F:=F) (n:=n)) where
  carrier := {g | LayerDepth (k+1) ((g.val).val-1)}
  one_mem' := by intro i j hij; simp
  mul_mem' := by intro a b ha hb; exact (unitRec% product_depth) (k+1) (by omega) a.val b.val ha hb
  inv_mem' := by intro a ha; exact (unitOdd% inverse_depth) (k+1) (by omega) a.val ha
private instance layer_normal (k : ℕ) : (layer (F:=F) (n:=n) k).Normal where
  conj_mem a ha b := by
    have hbi : LayerDepth 1 ((b.val⁻¹).val-1) := (unitOdd% inverse_depth) 1 (by decide) b.val b.prop
    have hc := (unitRec% commutator_depth) (k+1) 1 (by omega) (by decide) a.val b.val⁻¹ ha hbi
    have hprod := (unitRec% product_depth) (k+1) (by omega) a.val
      (a.val⁻¹*(b.val⁻¹)⁻¹*a.val*b.val⁻¹) ha ((unitLayer% depth_mono) hc (by omega))
    have he : a.val*(a.val⁻¹*(b.val⁻¹)⁻¹*a.val*b.val⁻¹)=b.val*a.val*b.val⁻¹ := by group
    rw [he] at hprod
    exact hprod

private theorem quotient_commute (k : ℕ)
    (a b : U (F:=F) (n:=n))
    (ha : LayerDepth 3 (a.val.val-1)) (hb : LayerDepth (k+3) (b.val.val-1)) :
    Commute (QuotientGroup.mk' (layer (k+4)) a) (QuotientGroup.mk' (layer (k+4)) b) := by
  let π := QuotientGroup.mk' (layer (F:=F) (n:=n) (k+4))
  have hc := (unitRec% commutator_depth) 3 (k+3) (by decide) (by omega) a.val b.val ha hb
  have he : π (a⁻¹*b⁻¹*a*b)=1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (unitLayer% depth_mono) hc (by omega)
  change π a*π b=π b*π a
  have h := he
  simp only [map_mul,map_inv] at h
  calc
    π a*π b = (π b*π a)*(π a⁻¹*π b⁻¹*π a*π b) := by simp only [map_inv]; group
    _ = π b*π a := by simp only [map_inv]; rw [h,mul_one]

private def value (alpha : MulAut (U (F:=F) (n:=n))) (x : U (F:=F) (n:=n)) := x⁻¹*alpha x
private theorem value_depth (k : ℕ) (hk : 0<k)
    (alpha : MulAut (U (F:=F) (n:=n)))
    (halpha : ∀ a, LayerDepth k (a.val.val-1) → LayerDepth k ((alpha a).val.val-1))
    (x : U (F:=F) (n:=n)) (hx : LayerDepth k (x.val.val-1)) :
    LayerDepth k ((value alpha x).val.val-1) :=
  (unitRec% product_depth) k hk _ _ ((unitOdd% inverse_depth) k hk x.val hx) (halpha x hx)
private theorem q_value_update (k : ℕ) (alpha : MulAut (U (F:=F) (n:=n)))
    (x t : U (F:=F) (n:=n))
    (hv : LayerDepth 3 ((value alpha x).val.val-1))
    (ht : LayerDepth (k+3) (t.val.val-1)) :
    QuotientGroup.mk' (layer (k+4)) (value alpha (x*t))=
      QuotientGroup.mk' (layer (k+4)) (value alpha x)*
        QuotientGroup.mk' (layer (k+4)) (value alpha t) := by
  let π := QuotientGroup.mk' (layer (F:=F) (n:=n) (k+4))
  have hc := quotient_commute k (value alpha x) t hv ht
  have he : value alpha (x*t)=t⁻¹*value alpha x*alpha t := by
    dsimp only [value]
    rw [map_mul]
    group
  change π (value alpha (x*t))=π (value alpha x)*π (value alpha t)
  rw [he,map_mul,map_mul,map_inv]
  have hcomm : π t⁻¹*π (value alpha x)=π (value alpha x)*π t⁻¹ := by
    simpa only [map_inv] using hc.inv_right.eq.symm
  calc
    _ = (π t⁻¹*π (value alpha x))*π (alpha t) := by rw [map_inv]
    _ = π (value alpha x)*(π t⁻¹*π (alpha t)) := by rw [hcomm,mul_assoc]
    _ = _ := by rw [← map_mul]; rfl

private theorem ordered_pair {G : Type*} [Group G] {R : ℕ}
    (a b : Fin R → G) (hcomm : ∀ i j, Commute (a i) (b j)) :
    NikolovSegal.orderedProduct (fun i => a i*b i)=
      NikolovSegal.orderedProduct a*NikolovSegal.orderedProduct b := by
  induction R with
  | zero => simp [NikolovSegal.orderedProduct]
  | succ R ih =>
    have ht := ih (fun i => a i.succ) (fun i => b i.succ) (fun i j => hcomm i.succ j.succ)
    have hc : Commute (NikolovSegal.orderedProduct (fun i : Fin R => a i.succ)) (b 0) := by
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact hcomm i.succ 0
    simp only [NikolovSegal.orderedProduct,List.ofFn_succ,List.prod_cons] at ht ⊢
    rw [ht]
    change a 0*b 0*(NikolovSegal.orderedProduct (fun i : Fin R => a i.succ)*NikolovSegal.orderedProduct (fun i : Fin R => b i.succ))=_
    calc
      _ = a 0*(b 0*NikolovSegal.orderedProduct (fun i : Fin R => a i.succ))*NikolovSegal.orderedProduct (fun i : Fin R => b i.succ) := by group
      _ = _ := by rw [hc.eq.symm]; simp only [NikolovSegal.orderedProduct]; group
private theorem map_ordered {G H : Type*} [Group G] [Group H] (f : G →* H) {R : ℕ} (a : Fin R → G) :
    f (NikolovSegal.orderedProduct a)=NikolovSegal.orderedProduct (fun i => f (a i)) := by
  simp only [NikolovSegal.orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def]

private theorem q_ordered_update {R : ℕ} (k : ℕ)
    (alpha : Fin R → MulAut (U (F:=F) (n:=n))) (x t : Fin R → U (F:=F) (n:=n))
    (hv : ∀ i, LayerDepth 3 ((value (alpha i) (x i)).val.val-1))
    (ht : ∀ i, LayerDepth (k+3) ((t i).val.val-1))
    (hvt : ∀ i, LayerDepth (k+3) ((value (alpha i) (t i)).val.val-1)) :
    QuotientGroup.mk' (layer (k+4)) (NikolovSegal.orderedProduct (fun i => value (alpha i) (x i*t i)))=
      QuotientGroup.mk' (layer (k+4)) (NikolovSegal.orderedProduct (fun i => value (alpha i) (x i)))*
        QuotientGroup.mk' (layer (k+4)) (NikolovSegal.orderedProduct (fun i => value (alpha i) (t i))) := by
  rw [map_ordered,map_ordered,map_ordered]
  simp only [q_value_update k _ _ _ (hv _) (ht _)]
  apply ordered_pair
  intro i j
  exact quotient_commute k _ _ (hv i) (hvt j)

private noncomputable def restriction [Fintype F] (alpha : MulAut (Matrix.SpecialLinearGroup (Fin n) F))
    (h : ∀ a, LayerDepth 1 (a.val-1) → LayerDepth 1 ((alpha a).val-1)) : MulAut (U (F:=F) (n:=n)) := by
  classical
  let f : U (F:=F) (n:=n) →* U (F:=F) (n:=n) :=
    { toFun := fun a => ⟨alpha a.val,h a.val a.prop⟩
      map_one' := by apply Subtype.ext; exact map_one alpha
      map_mul' := by intro a b; apply Subtype.ext; exact map_mul alpha a.val b.val }
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact alpha.injective (congrArg Subtype.val he)
  exact MulEquiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
private theorem restriction_apply [Fintype F]
    (alpha : MulAut (Matrix.SpecialLinearGroup (Fin n) F))
    (h : ∀ a, LayerDepth 1 (a.val-1) → LayerDepth 1 ((alpha a).val-1)) (a : U (F:=F) (n:=n)) :
    (restriction alpha h a).val=alpha a.val := rfl

private theorem ordered_depth {R : ℕ} (k : ℕ) (hk : 0<k)
    (a : Fin R → U (F:=F) (n:=n)) (ha : ∀ i, LayerDepth k ((a i).val.val-1)) :
    LayerDepth k ((NikolovSegal.orderedProduct a).val.val-1) := by
  have he : (NikolovSegal.orderedProduct a).val=NikolovSegal.orderedProduct (fun i => (a i).val) :=
    map_ordered (U (F:=F) (n:=n)).subtype a
  rw [he]
  exact ((unitOdd% ordered_layer) k hk (fun i => (a i).val) ha).1
private def systemValue {R : ℕ}
    (alphaP alphaN : Fin R → MulAut (U (F:=F) (n:=n))) (alpha0 : MulAut (U (F:=F) (n:=n)))
    (x z : Fin R → U (F:=F) (n:=n)) (y : U (F:=F) (n:=n)) : U (F:=F) (n:=n) :=
  NikolovSegal.orderedProduct (fun i => value (alphaP i) (x i))*
    NikolovSegal.orderedProduct (fun i => value (alphaN i) (z i))*value alpha0 y
private theorem q_system_update {R : ℕ} (k : ℕ)
    (alphaP alphaN : Fin R → MulAut (U (F:=F) (n:=n))) (alpha0 : MulAut (U (F:=F) (n:=n)))
    (hp : ∀ l, 0<l → ∀ i a, LayerDepth l (a.val.val-1) → LayerDepth l (((alphaP i) a).val.val-1))
    (hn : ∀ l, 0<l → ∀ i a, LayerDepth l (a.val.val-1) → LayerDepth l (((alphaN i) a).val.val-1))
    (h0 : ∀ l, 0<l → ∀ a, LayerDepth l (a.val.val-1) → LayerDepth l ((alpha0 a).val.val-1))
    (x z t s : Fin R → U (F:=F) (n:=n)) (y v : U (F:=F) (n:=n))
    (hx : ∀ i, LayerDepth 3 ((x i).val.val-1)) (hz : ∀ i, LayerDepth 3 ((z i).val.val-1))
    (hy : LayerDepth 3 (y.val.val-1))
    (ht : ∀ i, LayerDepth (k+3) ((t i).val.val-1)) (hs : ∀ i, LayerDepth (k+3) ((s i).val.val-1))
    (hv : LayerDepth (k+3) (v.val.val-1)) :
    QuotientGroup.mk' (layer (k+4)) (systemValue alphaP alphaN alpha0 (fun i => x i*t i) (fun i => z i*s i) (y*v))=
      QuotientGroup.mk' (layer (k+4)) (systemValue alphaP alphaN alpha0 x z y)*
        QuotientGroup.mk' (layer (k+4)) (systemValue alphaP alphaN alpha0 t s v) := by
  let π := QuotientGroup.mk' (layer (F:=F) (n:=n) (k+4))
  let P := NikolovSegal.orderedProduct (fun i => value (alphaP i) (x i))
  let N := NikolovSegal.orderedProduct (fun i => value (alphaN i) (z i))
  let T := NikolovSegal.orderedProduct (fun i => value (alphaP i) (t i))
  let S := NikolovSegal.orderedProduct (fun i => value (alphaN i) (s i))
  let Y := value alpha0 y
  let V := value alpha0 v
  have hpx := fun i => value_depth 3 (by decide) (alphaP i) (hp 3 (by decide) i) _ (hx i)
  have hnz := fun i => value_depth 3 (by decide) (alphaN i) (hn 3 (by decide) i) _ (hz i)
  have hpt := fun i => value_depth (k+3) (by omega) (alphaP i) (hp (k+3) (by omega) i) _ (ht i)
  have hns := fun i => value_depth (k+3) (by omega) (alphaN i) (hn (k+3) (by omega) i) _ (hs i)
  have hY := value_depth 3 (by decide) alpha0 (h0 3 (by decide)) y hy
  have hN := ordered_depth 3 (by decide) _ hnz
  have hT := ordered_depth (k+3) (by omega) _ hpt
  have hS := ordered_depth (k+3) (by omega) _ hns
  have hNT : Commute (π N) (π T) := quotient_commute k N T hN hT
  have hYT : Commute (π Y) (π T) := quotient_commute k Y T hY hT
  have hYS : Commute (π Y) (π S) := quotient_commute k Y S hY hS
  unfold systemValue
  simp only [map_mul]
  rw [q_ordered_update k alphaP x t hpx ht hpt,q_ordered_update k alphaN z s hnz hs hns,
    q_value_update k alpha0 y v hY hv]
  change (π P*π T)*(π N*π S)*(π Y*π V)=(π P*π N*π Y)*(π T*π S*π V)
  calc
    _ = (π P*π N)*(π T*π S)*(π Y*π V) := by
      calc
        _ = π P*(π T*π N)*π S*(π Y*π V) := by group
        _ = _ := by rw [hNT.eq.symm]; group
    _ = _ := by
      have hc := hYT.mul_right hYS
      calc
        _ = (π P*π N)*((π T*π S)*π Y)*π V := by group
        _ = _ := by rw [hc.eq.symm]; group

private theorem finite_layer_reconstruction {R : ℕ}
    (alphaP alphaN : Fin R → MulAut (U (F:=F) (n:=n))) (alpha0 : MulAut (U (F:=F) (n:=n)))
    (hp : ∀ l, 0<l → ∀ i a, LayerDepth l (a.val.val-1) → LayerDepth l (((alphaP i) a).val.val-1))
    (hn : ∀ l, 0<l → ∀ i a, LayerDepth l (a.val.val-1) → LayerDepth l (((alphaN i) a).val.val-1))
    (h0 : ∀ l, 0<l → ∀ a, LayerDepth l (a.val.val-1) → LayerDepth l ((alpha0 a).val.val-1))
    (hlocal : ∀ d : ℕ, ∀ b : U (F:=F) (n:=n), LayerDepth (2*d+3) (b.val.val-1) →
      ∃ t s : Fin R → U (F:=F) (n:=n), ∃ v : U (F:=F) (n:=n),
        (∀ i, LayerDepth (2*d+3) ((t i).val.val-1) ∧ LayerDepth (2*d+3) ((s i).val.val-1)) ∧
        LayerDepth (2*d+3) (v.val.val-1) ∧
        LayerDepth (2*d+5) (((systemValue alphaP alphaN alpha0 t s v)⁻¹*b).val.val-1))
    (b : U (F:=F) (n:=n)) (hb : LayerDepth 3 (b.val.val-1)) :
    ∃ x z : Fin R → U (F:=F) (n:=n), ∃ y : U (F:=F) (n:=n),
      (∀ i, LayerDepth 3 ((x i).val.val-1) ∧ LayerDepth 3 ((z i).val.val-1)) ∧
      LayerDepth 3 (y.val.val-1) ∧ systemValue alphaP alphaN alpha0 x z y=b := by
  have h : ∀ d : ℕ, ∃ x z : Fin R → U (F:=F) (n:=n), ∃ y : U (F:=F) (n:=n),
      (∀ i, LayerDepth 3 ((x i).val.val-1) ∧ LayerDepth 3 ((z i).val.val-1)) ∧
      LayerDepth 3 (y.val.val-1) ∧
      LayerDepth (2*d+3) (((systemValue alphaP alphaN alpha0 x z y)⁻¹*b).val.val-1) := by
    intro d
    induction d with
    | zero =>
      refine ⟨fun _ => 1,fun _ => 1,1,?_,?_,?_⟩
      · intro i; constructor <;> intro r c hrc <;> simp
      · intro r c hrc; simp
      · simpa [systemValue,value,NikolovSegal.orderedProduct] using hb
    | succ d ih =>
      obtain ⟨x,z,y,hxz,hy,hr⟩ := ih
      let P := systemValue alphaP alphaN alpha0 x z y
      let residual := P⁻¹*b
      obtain ⟨t,s,v,hts,hv,hinc⟩ := hlocal d residual hr
      let X := fun i => x i*t i
      let Z := fun i => z i*s i
      let Y := y*v
      have hX : ∀ i, LayerDepth 3 ((X i).val.val-1) := fun i =>
        (unitRec% product_depth) 3 (by decide) _ _ (hxz i).1 ((unitLayer% depth_mono) (hts i).1 (by omega))
      have hZ : ∀ i, LayerDepth 3 ((Z i).val.val-1) := fun i =>
        (unitRec% product_depth) 3 (by decide) _ _ (hxz i).2 ((unitLayer% depth_mono) (hts i).2 (by omega))
      have hY : LayerDepth 3 (Y.val.val-1) :=
        (unitRec% product_depth) 3 (by decide) _ _ hy ((unitLayer% depth_mono) hv (by omega))
      refine ⟨X,Z,Y,fun i => ⟨hX i,hZ i⟩,hY,?_⟩
      let π := QuotientGroup.mk' (layer (F:=F) (n:=n) (2*d+4))
      have hi : π ((systemValue alphaP alphaN alpha0 t s v)⁻¹*residual)=1 :=
        (QuotientGroup.eq_one_iff _).mpr hinc
      have he : π (systemValue alphaP alphaN alpha0 t s v)=π residual := by
        simpa only [map_mul,map_inv,inv_mul_eq_one] using hi
      have hu := q_system_update (2*d) alphaP alphaN alpha0 hp hn h0 x z t s y v
        (fun i => (hxz i).1) (fun i => (hxz i).2) hy (fun i => (hts i).1) (fun i => (hts i).2) hv
      have hnew : π (systemValue alphaP alphaN alpha0 X Z Y)=π b := by
        rw [hu,he]
        dsimp only [residual]
        change π P*(π P⁻¹*π b)=π b
        simp only [map_inv,mul_inv_cancel_left]
      have hzero : π ((systemValue alphaP alphaN alpha0 X Z Y)⁻¹*b)=1 := by
        rw [map_mul,map_inv,hnew,inv_mul_cancel]
      have hz : LayerDepth (2*d+5) (((systemValue alphaP alphaN alpha0 X Z Y)⁻¹*b).val.val-1) :=
        (QuotientGroup.eq_one_iff (N:=layer (F:=F) (n:=n) (2*d+4)) _).mp hzero
      simpa only [show 2*(d+1)+3=2*d+5 by omega] using hz
  obtain ⟨x,z,y,hxz,hy,hr⟩ := h n
  have hz : (((systemValue alphaP alphaN alpha0 x z y)⁻¹*b).val.val-1)=0 :=
    (unitLayer% depth_n_zero) ((unitLayer% depth_mono) hr (by omega))
  have he : (systemValue alphaP alphaN alpha0 x z y)⁻¹*b=1 := by
    apply Subtype.ext; apply Subtype.ext
    exact sub_eq_zero.mp hz
  exact ⟨x,z,y,hxz,hy,by simpa only [inv_mul_eq_one] using he⟩

private theorem parity_power_depth (lambda : Fˣ) (phi : RingAut F) (d k : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((((parityTorus lambda*fieldAut phi : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a).val-1) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using ha
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply]
    exact (unitOdd% diagonal_depth) (fun i : Fin n => lambda⁻¹^(i.val%2)) k _ ((unitOdd% field_depth) phi k _ ih)
private theorem inner_depth (g : Matrix.SpecialLinearGroup (Fin n) F)
    (hg : LayerDepth 1 (g.val-1)) (k : ℕ) (hk : 0<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((MulAut.conj g a).val-1) := by
  have hgi := (unitOdd% inverse_depth) 1 (by decide) g hg
  have hc := (unitRec% commutator_depth) k 1 hk (by decide) a g⁻¹ ha hgi
  have hprod := (unitRec% product_depth) k hk a (a⁻¹*(g⁻¹)⁻¹*a*g⁻¹) ha
    ((unitLayer% depth_mono) hc (by omega))
  have he : a*(a⁻¹*(g⁻¹)⁻¹*a*g⁻¹)=MulAut.conj g a := by rw [MulAut.conj_apply]; group
  rw [he] at hprod
  exact hprod
private theorem corrected_field_power_depth (u0 : Matrix.SpecialLinearGroup (Fin n) F)
    (hu0 : LayerDepth 1 (u0.val-1)) (lambda : Fˣ) (phi : RingAut F) (d k : ℕ) (hk : 0<k)
    (a : Matrix.SpecialLinearGroup (Fin n) F) (ha : LayerDepth k (a.val-1)) :
    LayerDepth k ((((MulAut.conj u0*(heightTorus lambda*fieldAut phi) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d) a).val-1) := by
  induction d with
  | zero => simpa only [pow_zero,MulAut.one_apply] using ha
  | succ d ih =>
    rw [pow_succ',MulAut.mul_apply,MulAut.mul_apply,MulAut.mul_apply]
    exact inner_depth u0 hu0 k hk _ ((unitAction% torus_depth) lambda k _ ((unitOdd% field_depth) phi k _ ih))

private theorem real_system [Fintype F] {R : ℕ}
    (deltaP deltaN : Fin R → MulAut (Matrix.SpecialLinearGroup (Fin n) F))
    (delta0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F))
    (hp : ∀ i a, LayerDepth 1 (a.val-1) → LayerDepth 1 (((deltaP i) a).val-1))
    (hn : ∀ i a, LayerDepth 1 (a.val-1) → LayerDepth 1 (((deltaN i) a).val-1))
    (h0 : ∀ a, LayerDepth 1 (a.val-1) → LayerDepth 1 ((delta0 a).val-1))
    (x z : Fin R → U (F:=F) (n:=n)) (y : U (F:=F) (n:=n)) :
    (systemValue (fun i => restriction (deltaP i) (hp i))
      (fun i => restriction (deltaN i) (hn i)) (restriction delta0 h0) x z y).val=
      NikolovSegal.orderedProduct (fun i => (x i).val⁻¹*(deltaP i) (x i).val)*
      NikolovSegal.orderedProduct (fun i => (z i).val⁻¹*(deltaN i) (z i).val)*
      (y.val⁻¹*delta0 y.val) := by
  change (U (F:=F) (n:=n)).subtype (systemValue _ _ _ x z y)=_
  unfold systemValue
  rw [map_mul,map_mul,map_ordered,map_ordered]
  simp only [value,map_mul,map_inv,restriction_apply,Subgroup.subtype_apply]

/-- Complete U3 reconstruction for arbitrary prescribed FIELD tuples,
PartII Lemma9.2's field-action branch. The genuine two-layer solver is
consumed at every odd height, with exact quotient accumulation: old values
lie in U3 and increments in Uk, so their commutators vanish modulo U(k+2).
No factors commute in the original group. One correction tuple precedes
ALL group targets; length 2*M+1 and cutoff are independent of rank.
Graph tuples and the first two layers remain required for full Prop6.5. -/
theorem actual_uniform_field_U3_product [Fintype F] [DecidableEq F]
    {q M : ℕ} (hq : 0<q) (hM : q*(q+1)<M) (hF : (q+1)^q < Fintype.card F)
    (phiP phiN : Fin M → RingAut F) (dP dN : Fin M → ℕ)
    (hdP : ∀ i, 0<dP i ∧ dP i ∣ q) (hdN : ∀ i, 0<dN i ∧ dN i ∣ q)
    (phi0 : RingAut F) (d0 : ℕ) (hd0 : 0<d0 ∧ d0 ∣ q) :
    ∃ lambdaP lambdaN : Fin M → Fˣ, ∃ lambda0 : Fˣ, ∃ u0 : Matrix.SpecialLinearGroup (Fin n) F,
      LayerDepth 1 (u0.val-1) ∧ ∀ b : Matrix.SpecialLinearGroup (Fin n) F, LayerDepth 3 (b.val-1) →
        ∃ x z : Fin M → Matrix.SpecialLinearGroup (Fin n) F, ∃ y : Matrix.SpecialLinearGroup (Fin n) F,
          (∀ i, LayerDepth 3 ((x i).val-1) ∧ LayerDepth 3 ((z i).val-1)) ∧ LayerDepth 3 (y.val-1) ∧
          NikolovSegal.orderedProduct (fun i =>
            (x i)⁻¹*((parityTorus (lambdaP i)*fieldAut (phiP i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dP i)) (x i))*
          NikolovSegal.orderedProduct (fun i =>
            (z i)⁻¹*((parityTorus ((lambdaN i)⁻¹)*fieldAut (phiN i) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^(dN i)) (z i))*
          (y⁻¹*((MulAut.conj u0*(heightTorus lambda0*fieldAut phi0) : MulAut (Matrix.SpecialLinearGroup (Fin n) F))^d0) y)=b := by
  classical
  obtain ⟨lambdaP,lambdaN,lambda0,u0,hu0,hlocal⟩ :=
    PartIIUnitriangularTwoLayer.actual_uniform_field_two_layer_lift (n:=n) hq hM hF phiP phiN dP dN hdP hdN phi0 d0 hd0
  let deltaP : Fin M → MulAut (Matrix.SpecialLinearGroup (Fin n) F) := fun i => (parityTorus (lambdaP i)*fieldAut (phiP i))^(dP i)
  let deltaN : Fin M → MulAut (Matrix.SpecialLinearGroup (Fin n) F) := fun i => (parityTorus ((lambdaN i)⁻¹)*fieldAut (phiN i))^(dN i)
  let delta0 : MulAut (Matrix.SpecialLinearGroup (Fin n) F) := (MulAut.conj u0*(heightTorus lambda0*fieldAut phi0))^d0
  have hp : ∀ k, 0<k → ∀ i a, LayerDepth k (a.val-1) → LayerDepth k (((deltaP i) a).val-1) := by
    intro k hk i a ha; exact parity_power_depth (lambdaP i) (phiP i) (dP i) k a ha
  have hn : ∀ k, 0<k → ∀ i a, LayerDepth k (a.val-1) → LayerDepth k (((deltaN i) a).val-1) := by
    intro k hk i a ha; exact parity_power_depth ((lambdaN i)⁻¹) (phiN i) (dN i) k a ha
  have h0 : ∀ k, 0<k → ∀ a, LayerDepth k (a.val-1) → LayerDepth k ((delta0 a).val-1) := by
    intro k hk a ha; exact corrected_field_power_depth u0 hu0 lambda0 phi0 d0 k hk a ha
  let alphaP := fun i => restriction (deltaP i) (hp 1 (by decide) i)
  let alphaN := fun i => restriction (deltaN i) (hn 1 (by decide) i)
  let alpha0 := restriction delta0 (h0 1 (by decide))
  have hpU : ∀ k, 0<k → ∀ i a, LayerDepth k (a.val.val-1) → LayerDepth k (((alphaP i) a).val.val-1) := by
    intro k hk i a ha
    rw [restriction_apply]
    exact hp k hk i a.val ha
  have hnU : ∀ k, 0<k → ∀ i a, LayerDepth k (a.val.val-1) → LayerDepth k (((alphaN i) a).val.val-1) := by
    intro k hk i a ha
    rw [restriction_apply]
    exact hn k hk i a.val ha
  have h0U : ∀ k, 0<k → ∀ a, LayerDepth k (a.val.val-1) → LayerDepth k ((alpha0 a).val.val-1) := by
    intro k hk a ha
    rw [restriction_apply]
    exact h0 k hk a.val ha
  have hlocalU : ∀ d : ℕ, ∀ b : U (F:=F) (n:=n), LayerDepth (2*d+3) (b.val.val-1) →
      ∃ t s : Fin M → U (F:=F) (n:=n), ∃ v : U (F:=F) (n:=n),
        (∀ i, LayerDepth (2*d+3) ((t i).val.val-1) ∧ LayerDepth (2*d+3) ((s i).val.val-1)) ∧
        LayerDepth (2*d+3) (v.val.val-1) ∧
        LayerDepth (2*d+5) (((systemValue alphaP alphaN alpha0 t s v)⁻¹*b).val.val-1) := by
    intro d b hb
    obtain ⟨t,s,v,hts,hv,hres⟩ := hlocal (2*d+3) (by omega) (by omega) b.val hb
    let T : Fin M → U (F:=F) (n:=n) := fun i => ⟨t i,(unitLayer% depth_mono) (hts i).1 (by omega)⟩
    let S : Fin M → U (F:=F) (n:=n) := fun i => ⟨s i,(unitLayer% depth_mono) (hts i).2 (by omega)⟩
    let V : U (F:=F) (n:=n) := ⟨v,(unitLayer% depth_mono) hv (by omega)⟩
    refine ⟨T,S,V,hts,hv,?_⟩
    change LayerDepth (2*d+5) (((systemValue alphaP alphaN alpha0 T S V).val⁻¹*b.val).val-1)
    rw [real_system deltaP deltaN delta0 (hp 1 (by decide)) (hn 1 (by decide)) (h0 1 (by decide)) T S V]
    simpa only [show 2*d+3+2=2*d+5 by omega] using hres
  refine ⟨lambdaP,lambdaN,lambda0,u0,hu0,?_⟩
  intro b hb
  let B : U (F:=F) (n:=n) := ⟨b,(unitLayer% depth_mono) hb (by omega)⟩
  obtain ⟨x,z,y,hxz,hy,he⟩ := finite_layer_reconstruction alphaP alphaN alpha0 hpU hnU h0U hlocalU B hb
  refine ⟨fun i => (x i).val,fun i => (z i).val,y.val,hxz,hy,?_⟩
  have h := congrArg Subtype.val he
  rw [real_system deltaP deltaN delta0 (hp 1 (by decide)) (hn 1 (by decide)) (h0 1 (by decide)) x z y] at h
  exact h
end NikolovSegal.PartIIUnitriangularLayersGlobal
