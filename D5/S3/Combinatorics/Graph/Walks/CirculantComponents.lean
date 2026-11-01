/- GID: D5/S3/Combinatorics/Graph/Walks/CirculantComponents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CirculantComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Circulant, mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic]
   utility: none
   digest: Finite walks identify native circulant components with generated additive cosets. -/
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace CubicCirculant
open SimpleGraph
noncomputable section
variable {A : Type} [AddCommGroup A]

def translateIso (S : Set A) (a : A) :
    circulantGraph S ≃g circulantGraph S where
  toEquiv := Equiv.addRight a
  map_rel_iff' := by
    intro u v
    exact circulantGraph_adj_translate

private theorem translate_reachable (S : Set A) (a : A) {u v : A}
    (h : (circulantGraph S).Reachable u v) :
    (circulantGraph S).Reachable (u+a) (v+a) := by
  obtain ⟨p⟩ := h
  exact ⟨p.map (translateIso S a).toHom⟩

/-- Finite walks in a native circulant join precisely the cosets of its generated subgroup. -/
theorem circulant_reachable_iff (S : Set A) (u v : A) :
    (circulantGraph S).Reachable u v ↔ v-u ∈ AddSubgroup.closure S := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => simpa using (AddSubgroup.closure S).zero_mem
    | @cons x y z hxy p ih =>
      have hs : y-x ∈ AddSubgroup.closure S := by
        rcases hxy.2 with h | h
        · have hh := (AddSubgroup.closure S).neg_mem (AddSubgroup.subset_closure h)
          simpa using hh
        · exact AddSubgroup.subset_closure h
      have hh := (AddSubgroup.closure S).add_mem ih hs
      simpa only [sub_add_sub_cancel] using hh
  · intro hv
    let R : AddSubgroup A := {
      carrier := {x | (circulantGraph S).Reachable 0 x}
      zero_mem' := .refl _
      add_mem' := by
        intro x y hx hy
        have hh : (circulantGraph S).Reachable x (x+y) := by
          have hh := translate_reachable S x hy
          rw [zero_add,add_comm y x] at hh
          exact hh
        exact hx.trans hh
      neg_mem' := by
        intro x hx
        have hh := translate_reachable S (-x) hx.symm
        simpa using hh }
    have hSR : S ⊆ R := by
      intro x hx
      by_cases hz : x = 0
      · simpa [hz] using (show (0 : A) ∈ R from R.zero_mem)
      · show (circulantGraph S).Reachable 0 x
        apply Adj.reachable
        exact ⟨Ne.symm hz,Or.inr (by simpa using hx)⟩
    have hR : v-u ∈ R := ((AddSubgroup.closure_le R).mpr hSR) hv
    have hh := translate_reachable S u hR
    simpa using hh

/-- Native connected components, rather than an assumed decomposition, are generated cosets. -/
def componentQuotientEquiv (S : Set A) :
    (circulantGraph S).ConnectedComponent ≃ A ⧸ AddSubgroup.closure S := by
  let f : (circulantGraph S).ConnectedComponent → A ⧸ AddSubgroup.closure S :=
    Quot.lift (fun x => (x : A ⧸ AddSubgroup.closure S)) (by
      intro x y h
      apply QuotientAddGroup.eq.mpr
      simpa [sub_eq_add_neg,add_comm] using (circulant_reachable_iff S x y).mp h)
  apply Equiv.ofBijective f
  constructor
  · intro c d
    refine Quot.inductionOn c ?_
    intro x
    refine Quot.inductionOn d ?_
    intro y h
    apply ConnectedComponent.sound
    apply (circulant_reachable_iff S x y).mpr
    have hh := QuotientAddGroup.eq.mp h
    simpa [sub_eq_add_neg,add_comm] using hh
  · intro q
    refine Quotient.inductionOn' q ?_
    intro x
    exact ⟨(circulantGraph S).connectedComponentMk x,rfl⟩

/-- Translation gives an explicit native graph isomorphism from the generated subgroup
to each actual component support. -/
def componentOriginIso (S : Set A) (C : (circulantGraph S).ConnectedComponent) :
    (circulantGraph S).induce (AddSubgroup.closure S : Set A) ≃g C.toSimpleGraph := by
  let r : A := C.nonempty_supp.choose
  have hr : r ∈ C.supp := C.nonempty_supp.choose_spec
  have hto (x : AddSubgroup.closure S) : x.val+r ∈ C.supp := by
    have hx : (circulantGraph S).Reachable 0 x.val :=
      (circulant_reachable_iff S 0 x.val).mpr (by simpa using x.property)
    have hh := translate_reachable S r hx
    have hh' : (circulantGraph S).Reachable r (x.val+r) := by simpa using hh
    exact (ConnectedComponent.sound hh').symm.trans hr
  have hfrom (y : C) : y.val-r ∈ AddSubgroup.closure S :=
    (circulant_reachable_iff S r y.val).mp (C.reachable_of_mem_supp hr y.property)
  exact {
    toEquiv := {
      toFun := fun x => ⟨x.val+r,hto x⟩
      invFun := fun y => ⟨y.val-r,hfrom y⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
    map_rel_iff' := by
      intro x y
      exact circulantGraph_adj_translate }

private theorem closure_pair_eq_zmultiples (n a b : ℕ) :
    AddSubgroup.closure ({(a : ZMod n),(b : ZMod n)} : Set (ZMod n)) =
      AddSubgroup.zmultiples (Nat.gcd a b : ZMod n) := by
  have hp : ({(a : ZMod n),(b : ZMod n)} : Set (ZMod n)) =
      {(a : ZMod n)} ∪ {(b : ZMod n)} := by ext x; simp [or_comm]
  rw [hp,AddSubgroup.closure_union,← AddSubgroup.zmultiples_eq_closure,
    ← AddSubgroup.zmultiples_eq_closure]
  simpa using AddSubgroup.zmultiples_zsmul_sup (1 : ZMod n) (a : ℤ) (b : ℤ)

/-- The exact number of components is the step gcd whenever the second step divides the order. -/
theorem component_count {n : ℕ} [NeZero n] (a b : ℕ) (hb : b ∣ n) :
    Nat.card (circulantGraph ({(a : ZMod n),(b : ZMod n)} : Set (ZMod n))).ConnectedComponent =
      Nat.gcd a b := by
  rw [Nat.card_congr (componentQuotientEquiv _),closure_pair_eq_zmultiples]
  change (AddSubgroup.zmultiples (Nat.gcd a b : ZMod n)).index = Nat.gcd a b
  have hgen : AddSubgroup.zmultiples (1 : ZMod n) = ⊤ := by
    apply top_unique
    intro x _
    have hx := AddSubgroup.nsmul_mem_zmultiples (1 : ZMod n) x.val
    simpa using hx
  have hi := AddSubgroup.index_zmultiples_zsmul hgen (Nat.gcd a b : ℤ)
  have hd : Nat.gcd a b ∣ n := (Nat.gcd_dvd_right a b).trans hb
  simpa [ZMod.addOrderOf_one,Nat.gcd_eq_left hd] using hi

/-- Existing cyclic-group coordinates send the unit step to the actual graph generator. -/
def stepEquiv [Finite A] (a : A) :
    ZMod (addOrderOf a) ≃+ AddSubgroup.zmultiples a :=
  zmodAddEquivOfGenerator (g := ⟨a,AddSubgroup.mem_zmultiples a⟩)
    (by
      rintro ⟨x,hx⟩
      obtain ⟨j,hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨j,Subtype.ext hj⟩)
    (Nat.card_zmultiples a)

theorem antipode_add (p : ℕ) :
    ((p+2 : ℕ) : ZMod (2*(p+2))) + ((p+2 : ℕ) : ZMod (2*(p+2))) = 0 := by
  rw [← Nat.cast_add]
  convert ZMod.natCast_self (2*(p+2)) using 1 <;> congr 1 <;> omega

private theorem antipode_ne_zero (p : ℕ) :
    ((p+2 : ℕ) : ZMod (2*(p+2))) ≠ 0 := by
  intro h
  have hh := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega)] at hh
  norm_num at hh

theorem antipode_order (p : ℕ) :
    addOrderOf ((p+2 : ℕ) : ZMod (2*(p+2))) = 2 := by
  apply addOrderOf_eq_prime
  · simpa only [two_nsmul] using antipode_add p
  · exact antipode_ne_zero p

/-- In the native even cyclic group the only nonzero involution is the antipodal vertex. -/
private theorem unique_antipode (p : ℕ) (x : ZMod (2*(p+2)))
    (hx : x ≠ 0) (hxx : x+x=0) : x = ((p+2 : ℕ) : ZMod (2*(p+2))) := by
  have hc : ((x.val+x.val : ℕ) : ZMod (2*(p+2))) = 0 := by
    simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using hxx
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hc
  have hpos : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx ((ZMod.val_eq_zero x).mp h))
  have hlt := ZMod.val_lt x
  have hlo : 2*(p+2) ≤ x.val+x.val := Nat.le_of_dvd (by omega) hd
  have hz : x.val+x.val - 2*(p+2) = 0 :=
    Nat.eq_zero_of_dvd_of_lt (Nat.dvd_sub hd (dvd_refl _)) (by omega)
  apply ZMod.val_injective
  rw [ZMod.val_natCast_of_lt (by omega)]
  omega

private theorem half_step (p : ℕ) (a : ZMod (2*(p+2)))
    (heven : Even (addOrderOf a)) :
    (addOrderOf a / 2) • a = ((p+2 : ℕ) : ZMod (2*(p+2))) := by
  have hpos := (isOfFinAddOrder_of_finite a).addOrderOf_pos
  have he : addOrderOf a / 2 + addOrderOf a / 2 = addOrderOf a := by
    rcases heven with ⟨j,hj⟩
    omega
  apply unique_antipode p
  · intro hz
    have hd := addOrderOf_dvd_of_nsmul_eq_zero hz
    have hh : 0 < addOrderOf a / 2 := by omega
    have hh' := Nat.le_of_dvd hh hd
    omega
  · rw [← add_nsmul,he,addOrderOf_nsmul_eq_zero]

theorem antipode_not_mem_odd_step (p : ℕ) (a : ZMod (2*(p+2)))
    (hodd : Odd (addOrderOf a)) :
    ((p+2 : ℕ) : ZMod (2*(p+2))) ∉ AddSubgroup.zmultiples a := by
  intro hm
  have hd := addOrderOf_dvd_of_mem_zmultiples hm
  rw [antipode_order] at hd
  rcases hodd with ⟨j,hj⟩
  obtain ⟨k,hk⟩ := hd
  omega

def generatedGraphIso {B : Type} [AddCommGroup B]
    (K : AddSubgroup A) (e : B ≃+ K) (u v : B) :
    circulantGraph ({u,v} : Set B) ≃g
      (circulantGraph ({(e u : A),(e v : A)} : Set A)).induce (K : Set A) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    have hi : Function.Injective (fun z : B => (e z : A)) :=
      Subtype.val_injective.comp e.injective
    have hd (x y z : B) :
        (e x : A)-(e y : A)=(e z : A) ↔ x-y=z := by
      constructor
      · intro h
        apply e.injective
        apply Subtype.ext
        simpa using h
      · intro h
        rw [← h,map_sub]
        rfl
    change (circulantGraph ({(e u : A),(e v : A)} : Set A)).Adj (e x) (e y) ↔
      (circulantGraph ({u,v} : Set B)).Adj x y
    simp only [circulantGraph_adj,Set.mem_insert_iff,Set.mem_singleton_iff]
    rw [hi.eq_iff,hd,hd,hd,hd]

private theorem closure_even_step (p : ℕ) (a : ZMod (2*(p+2)))
    (heven : Even (addOrderOf a)) :
    AddSubgroup.closure ({a,((p+2 : ℕ) : ZMod (2*(p+2)))} : Set (ZMod (2*(p+2)))) =
      AddSubgroup.zmultiples a := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact AddSubgroup.mem_zmultiples _
    · have hx' : x=((p+2 : ℕ) : ZMod (2*(p+2))) := Set.mem_singleton_iff.mp hx
      rw [hx',← half_step p a heven]
      exact AddSubgroup.nsmul_mem_zmultiples a _
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.subset_closure (by simp)

/-- Even generator order gives an antipodal cycle on each actual component. -/
def evenComponentIso (p : ℕ) (a : ZMod (2*(p+2)))
    (heven : Even (addOrderOf a))
    (C : (circulantGraph ({a,((p+2 : ℕ) : ZMod (2*(p+2)))} : Set (ZMod (2*(p+2))))).ConnectedComponent) :
    circulantGraph ({(1 : ZMod (addOrderOf a)),((addOrderOf a / 2 : ℕ) : ZMod (addOrderOf a))} :
      Set (ZMod (addOrderOf a))) ≃g C.toSimpleGraph := by
  let e := stepEquiv a
  have h1 : (e 1 : ZMod (2*(p+2))) = a := by simp [e,stepEquiv]
  have hh : (e ((addOrderOf a / 2 : ℕ) : ZMod (addOrderOf a)) : ZMod (2*(p+2))) = ((p+2 : ℕ) : ZMod (2*(p+2))) := by
    rw [← Nat.smul_one_eq_cast,map_nsmul]
    change (addOrderOf a / 2) • (e 1 : ZMod (2*(p+2))) = ((p+2 : ℕ) : ZMod (2*(p+2)))
    rw [h1,half_step p a heven]
  have ei : circulantGraph ({(1 : ZMod (addOrderOf a)),((addOrderOf a / 2 : ℕ) : ZMod (addOrderOf a))} :
      Set (ZMod (addOrderOf a))) ≃g
      (circulantGraph ({a,((p+2 : ℕ) : ZMod (2*(p+2)))} : Set (ZMod (2*(p+2))))).induce
        (AddSubgroup.zmultiples a : Set (ZMod (2*(p+2)))) := by
    simpa only [h1,hh] using generatedGraphIso (AddSubgroup.zmultiples a) e
      (1 : ZMod (addOrderOf a)) ((addOrderOf a / 2 : ℕ) : ZMod (addOrderOf a))
  have ec := componentOriginIso ({a,((p+2 : ℕ) : ZMod (2*(p+2)))} : Set (ZMod (2*(p+2)))) C
  rw [closure_even_step p a heven] at ec
  exact ei.trans ec


/-- Specifying the order only transports the existing cyclic-group supplier. -/
def stepEquivOfOrder [Finite A] (a : A) (k : ℕ) (hk : addOrderOf a = k) :
    ZMod k ≃+ AddSubgroup.zmultiples a := hk ▸ stepEquiv a

@[simp] theorem stepEquivOfOrder_one [Finite A] (a : A) (k : ℕ)
    (hk : addOrderOf a = k) : (stepEquivOfOrder a k hk 1 : A) = a := by
  subst k
  simp [stepEquivOfOrder,stepEquiv]

private theorem closure_pair_sup (a b : A) :
    AddSubgroup.closure ({a,b} : Set A) =
      AddSubgroup.zmultiples a ⊔ AddSubgroup.zmultiples b := by
  have hp : ({a,b} : Set A) = {a} ∪ {b} := by ext x; simp [or_comm]
  rw [hp,AddSubgroup.closure_union,← AddSubgroup.zmultiples_eq_closure,
    ← AddSubgroup.zmultiples_eq_closure]

/-- An odd-order cyclic subgroup and the antipodal involution supply independent coordinates. -/
def oddCoordinates (p : ℕ) (a : ZMod (2*(p+2))) (ell : ℕ)
    (hell : addOrderOf a = ell) (hodd : Odd ell) :
    (ZMod ell × ZMod 2) ≃+
      AddSubgroup.closure ({a,((p+2 : ℕ) : ZMod (2*(p+2)))} : Set (ZMod (2*(p+2)))) := by
  let H := AddSubgroup.zmultiples a
  let T := AddSubgroup.zmultiples ((p+2 : ℕ) : ZMod (2*(p+2)))
  let K := AddSubgroup.closure ({a,((p+2 : ℕ) : ZMod (2*(p+2)))} : Set (ZMod (2*(p+2))))
  let e := stepEquivOfOrder a ell hell
  let f := stepEquivOfOrder ((p+2 : ℕ) : ZMod (2*(p+2))) 2 (antipode_order p)
  have hHK : H ≤ K := by
    rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.subset_closure (by simp)
  have hTK : T ≤ K := by
    rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.subset_closure (by simp)
  let F : (ZMod ell × ZMod 2) →+ K := {
    toFun := fun x => ⟨(e x.1 : ZMod (2*(p+2))) + (f x.2 : ZMod (2*(p+2))),
      K.add_mem (hHK (e x.1).property) (hTK (f x.2).property)⟩
    map_zero' := by apply Subtype.ext; simp
    map_add' := by intro x y; apply Subtype.ext; simp; abel }
  refine AddEquiv.ofBijective F ⟨?_,?_⟩
  · intro x y hxy
    have hsum : (e x.1 : ZMod (2*(p+2))) + (f x.2 : ZMod (2*(p+2))) =
        (e y.1 : ZMod (2*(p+2))) + (f y.2 : ZMod (2*(p+2))) := congrArg Subtype.val hxy
    have hd : (f (x.2-y.2) : ZMod (2*(p+2))) ∈ H := by
      have hh := H.sub_mem (e y.1).property (e x.1).property
      have he : (f (x.2-y.2) : ZMod (2*(p+2))) = (e y.1 : ZMod (2*(p+2)))-(e x.1 : ZMod (2*(p+2))) := by
        rw [map_sub]
        change (f x.2 : ZMod (2*(p+2)))-(f y.2 : ZMod (2*(p+2))) = _
        linear_combination hsum
      rwa [he]
    have hbin : x.2-y.2 = 0 ∨ x.2-y.2 = 1 := by
      have hb := ZMod.val_lt (x.2-y.2)
      have hv : (x.2-y.2).val = 0 ∨ (x.2-y.2).val = 1 := by omega
      rcases hv with h | h
      · left; apply ZMod.val_injective; simpa using h
      · right; apply ZMod.val_injective; simpa only [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < 2)] using h
    have hsecond : x.2=y.2 := by
      rcases hbin with h | h
      · exact sub_eq_zero.mp h
      · rw [h] at hd
        have hf : (f 1 : ZMod (2*(p+2))) = ((p+2 : ℕ) : ZMod (2*(p+2))) := by
          exact stepEquivOfOrder_one _ _ _
        rw [hf] at hd
        exact (antipode_not_mem_odd_step p a (hell.symm ▸ hodd) hd).elim
    apply Prod.ext
    · apply e.injective
      apply Subtype.ext
      rw [hsecond] at hsum
      exact add_right_cancel hsum
    · exact hsecond
  · rintro ⟨z,hz⟩
    rw [closure_pair_sup] at hz
    obtain ⟨u,hu,v,hv,huv⟩ := AddSubgroup.mem_sup.mp hz
    obtain ⟨x,hx⟩ := e.surjective ⟨u,hu⟩
    obtain ⟨y,hy⟩ := f.surjective ⟨v,hv⟩
    refine ⟨(x,y),Subtype.ext ?_⟩
    change (e x : ZMod (2*(p+2))) + (f y : ZMod (2*(p+2))) = z
    rw [hx,hy]
    exact huv

/-- The product's unit jumps are exactly the native Cartesian cycle and two-clique edges. -/
def productPrismIso (r : ℕ) :
    ((cycleGraph (r+3)) □ (⊤ : SimpleGraph (ZMod 2))) ≃g
      circulantGraph ({((1,0) : ZMod (r+3) × ZMod 2),(0,1)} :
        Set (ZMod (r+3) × ZMod 2)) where
  toEquiv := (ZMod.finEquiv (r+3)).toEquiv.prodCongr (Equiv.refl _)
  map_rel_iff' := by
    intro x y
    rcases x with ⟨i,a⟩
    rcases y with ⟨j,b⟩
    let f := ZMod.finEquiv (r+3)
    have hc (i j : Fin (r+3)) : (cycleGraph (r+3)).Adj i j ↔
        f i - f j = 1 ∨ f j - f i = 1 := by
      rw [cycleGraph_adj]
      have hd (i j : Fin (r+3)) : f i - f j = 1 ↔ i-j=1 := by
        rw [← map_sub,← map_one f]
        exact f.injective.eq_iff
      rw [hd,hd]
    have hb : ∀ a b : ZMod 2, a-b=1 ↔ a ≠ b := by decide +kernel
    have hs : f i-f j=1 → i ≠ j := fun h => ((hc i j).mpr (Or.inl h)).ne
    have ht : f j-f i=1 → i ≠ j := fun h => ((hc i j).mpr (Or.inr h)).ne
    change ((f i,a) ≠ (f j,b) ∧
      (((f i-f j,a-b) ∈ ({((1,0) : ZMod (r+3) × ZMod 2),(0,1)} : Set _)) ∨
       ((f j-f i,b-a) ∈ ({((1,0) : ZMod (r+3) × ZMod 2),(0,1)} : Set _)))) ↔
      ((cycleGraph (r+3)).Adj i j ∧ a=b) ∨ (a ≠ b ∧ i=j)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Prod.mk.injEq,
      sub_eq_zero,hb,f.injective.eq_iff,hc]
    aesop

/-- Odd generator order gives a Cartesian prism on each actual component support. -/
def oddComponentIso (p r : ℕ) (a : ZMod (2*(p+2)))
    (hell : addOrderOf a = r+3) (hodd : Odd (r+3))
    (C : (circulantGraph ({a,((p+2 : ℕ) : ZMod (2*(p+2)))} :
      Set (ZMod (2*(p+2))))).ConnectedComponent) :
    ((cycleGraph (r+3)) □ (⊤ : SimpleGraph (ZMod 2))) ≃g C.toSimpleGraph := by
  let e := oddCoordinates p a (r+3) hell hodd
  have h1 : (e (1,0) : ZMod (2*(p+2))) = a := by
    change (stepEquivOfOrder a (r+3) hell 1 : ZMod (2*(p+2))) +
      (stepEquivOfOrder ((p+2 : ℕ) : ZMod (2*(p+2))) 2 (antipode_order p) 0 : ZMod (2*(p+2))) = a
    simp
  have ht : (e (0,1) : ZMod (2*(p+2))) = ((p+2 : ℕ) : ZMod (2*(p+2))) := by
    change (stepEquivOfOrder a (r+3) hell 0 : ZMod (2*(p+2))) +
      (stepEquivOfOrder ((p+2 : ℕ) : ZMod (2*(p+2))) 2 (antipode_order p) 1 : ZMod (2*(p+2))) = _
    simp
  have ei := generatedGraphIso
    (AddSubgroup.closure ({a,((p+2 : ℕ) : ZMod (2*(p+2)))} : Set (ZMod (2*(p+2)))))
    e (1,0) (0,1)
  rw [h1,ht] at ei
  exact (productPrismIso r).trans (ei.trans (componentOriginIso _ C))

/-- The exact number of odd-order components is half the cycle-step gcd. -/
theorem odd_component_number (p : ℕ) (a : ℕ)
    (hodd : Odd (addOrderOf (a : ZMod (2*(p+2))))) :
    Nat.gcd (2*(p+2)) a = 2 * Nat.gcd a (p+2) := by
  let K := AddSubgroup.closure ({(a : ZMod (2*(p+2))),((p+2 : ℕ) : ZMod (2*(p+2)))} :
    Set (ZMod (2*(p+2))))
  have hcard : Nat.card K = 2 * addOrderOf (a : ZMod (2*(p+2))) := by
    rw [← Nat.card_congr (oddCoordinates p (a : ZMod (2*(p+2))) _ rfl hodd).toEquiv]
    simp [Nat.card_prod,Nat.mul_comm]
  have hindex : K.index = Nat.gcd a (p+2) := by
    change Nat.card (ZMod (2*(p+2)) ⧸ K) = _
    rw [← Nat.card_congr (componentQuotientEquiv _)]
    exact component_count a (p+2) (by exact ⟨2, by omega⟩)
  have hmul := K.index_mul_card
  rw [hcard,hindex,Nat.card_eq_fintype_card,ZMod.card] at hmul
  have hord : addOrderOf (a : ZMod (2*(p+2))) = (2*(p+2))/Nat.gcd (2*(p+2)) a :=
    ZMod.addOrderOf_coe a (by omega)
  have hdiv : Nat.gcd (2*(p+2)) a * addOrderOf (a : ZMod (2*(p+2))) = 2*(p+2) := by
    rw [hord,Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  have hpos := (isOfFinAddOrder_of_finite (a : ZMod (2*(p+2)))).addOrderOf_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hdiv]
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hmul.symm

/-- The exact number of even-order components is the cycle-step gcd. -/
theorem even_component_number (p : ℕ) (a : ℕ)
    (heven : Even (addOrderOf (a : ZMod (2*(p+2))))) :
    Nat.gcd a (p+2) = Nat.gcd (2*(p+2)) a := by
  have ec := component_count (n := 2*(p+2)) a (p+2) (by exact ⟨2, by omega⟩)
  rw [Nat.card_congr (componentQuotientEquiv _),closure_even_step p _ heven] at ec
  have hgen : AddSubgroup.zmultiples (1 : ZMod (2*(p+2))) = ⊤ := by
    apply top_unique
    intro x _
    have hx := AddSubgroup.nsmul_mem_zmultiples (1 : ZMod (2*(p+2))) x.val
    simpa using hx
  have hi := AddSubgroup.index_zmultiples_zsmul hgen (a : ℤ)
  change (AddSubgroup.zmultiples (a : ZMod (2*(p+2)))).index = _ at ec
  rw [ZMod.addOrderOf_one,Int.gcd_natCast_natCast] at hi
  have hi' : (AddSubgroup.zmultiples (a : ZMod (2*(p+2)))).index = Nat.gcd (2*(p+2)) a := by
    simpa only [natCast_zsmul,Nat.smul_one_eq_cast,Nat.gcd_comm] using hi
  exact ec.symm.trans hi' 


/-- The cubic range excludes generator orders one and two on the actual cyclic vertices. -/
theorem step_order_lower_bound (p a : ℕ) (ha : 1 ≤ a) (halt : a < p+2) :
    3 ≤ addOrderOf (a : ZMod (2*(p+2))) := by
  have hpos := (isOfFinAddOrder_of_finite (a : ZMod (2*(p+2)))).addOrderOf_pos
  have hnonzero : (a : ZMod (2*(p+2))) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at hh
    omega
  have htwo : (2 : ℕ) • (a : ZMod (2*(p+2))) ≠ 0 := by
    intro h
    have hc : ((2*a : ℕ) : ZMod (2*(p+2))) = 0 := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul] using h
    have hh := congrArg ZMod.val hc
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at hh
    omega
  by_contra hn
  have hh : addOrderOf (a : ZMod (2*(p+2))) = 1 ∨
      addOrderOf (a : ZMod (2*(p+2))) = 2 := by omega
  rcases hh with h | h
  · exact hnonzero (AddMonoid.addOrderOf_eq_one_iff.mp h)
  · have hz := addOrderOf_nsmul_eq_zero (a : ZMod (2*(p+2)))
    rw [h] at hz
    exact htwo hz


end
end CubicCirculant
