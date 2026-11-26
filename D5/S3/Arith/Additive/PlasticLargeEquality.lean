/- GID: D5/S3/Arith/Additive/PlasticLargeEquality
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticLargeEquality
   mirror-E: none(waiver:integer-template-equality-rigidity)
   anchors: []
   utility: none
   digest: All plastic extremizers of at least eleven points have one of two translated shapes. -/

import D5.S3.Arith.Additive.PlasticTenPointEquality

/-! Equality rigidity for arbitrary signed integer sets, using actual maximum
insertion and the previously proved ten-point classification. -/
set_option autoImplicit false

namespace D5.S3.Arith.Additive.PlasticLargeEquality
open PlasticExtremal
open scoped Pointwise

private def simple (a : ℤ) (n : ℕ) (b : Bool) : Finset ℤ :=
  if b then insert a (Finset.Icc (a+2) (a+(n:ℤ)))
  else Finset.Icc a (a+(n:ℤ)-1)

private def top (a : ℤ) (n : ℕ) (b : Bool) : ℤ :=
  if b then a+(n:ℤ) else a+(n:ℤ)-1

private def good (E : Finset ℤ) (n : ℕ) : Prop :=
  (∃ a b, E = simple a n b) ∨
  (n=10 ∧ ∃ a : ℤ,
    E=({a,a+1} ∪ Finset.Icc (a+3) (a+10)) ∨
    E=({a,a+3} ∪ Finset.Icc (a+5) (a+12)))

private theorem simple_mem (a z : ℤ) (n : ℕ) (b : Bool) :
    z ∈ simple a n b ↔
      if b then z=a ∨ (a+2≤z ∧ z≤a+(n:ℤ))
      else a≤z ∧ z≤a+(n:ℤ)-1 := by
  cases b <;> simp [simple, Finset.mem_Icc, eq_comm]

private theorem simple_top (a : ℤ) (n : ℕ) (b : Bool) (hn : 10 ≤ n) :
    top a n b ∈ simple a n b ∧ ∀ z ∈ simple a n b, z≤top a n b := by
  cases b <;> simp only [top, Bool.false_eq_true, ↓reduceIte, simple_mem]
  all_goals constructor
  all_goals try omega

private theorem simple_extend (a : ℤ) (n : ℕ) (b : Bool) (hn : 10 ≤ n) :
    insert (top a n b+1) (simple a n b) = simple a (n+1) b := by
  ext z
  cases b <;> simp only [Finset.mem_insert, simple_mem, top, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_one] <;> omega

private theorem simple_erase (a : ℤ) (n : ℕ) (b : Bool) (hn : 10 ≤ n) :
    (simple a (n+1) b).erase (top a (n+1) b) = simple a n b := by
  ext z
  cases b <;> simp only [Finset.mem_erase, simple_mem, top, Bool.false_eq_true,
    ↓reduceIte, Nat.cast_add, Nat.cast_one] <;> omega

private theorem four_iff (E : Finset ℤ) (x y : ℤ)
    (hmax : ∀ z ∈ E, z ≤ x) (hxy : x < y) :
    weight (shifted (memory E x) (y - x)) = 4 ↔
      y-1∈E ∧ y-2∈E ∧ y-3∈E ∧ y-4∈E ∧ y-6∈E ∧ y-7∈E ∧ y-9∈E := by
  have h1 := shifted_memory_iff E x y 1 hmax hxy (by omega) (by omega)
  have h2 := shifted_memory_iff E x y 2 hmax hxy (by omega) (by omega)
  have h3 := shifted_memory_iff E x y 3 hmax hxy (by omega) (by omega)
  have h4 := shifted_memory_iff E x y 4 hmax hxy (by omega) (by omega)
  have h6 := shifted_memory_iff E x y 6 hmax hxy (by omega) (by omega)
  have h7 := shifted_memory_iff E x y 7 hmax hxy (by omega) (by omega)
  have h9 := shifted_memory_iff E x y 9 hmax hxy (by omega) (by omega)
  simp only [weight,h1,h2,h3,h4,h6,h7,h9]
  split_ifs <;> simp_all

private theorem four_gap (E : Finset ℤ) (x y : ℤ)
    (hmax : ∀ z ∈ E, z ≤ x) (hxy : x < y)
    (hw : weight (shifted (memory E x) (y - x)) = 4) : y=x+1 := by
  have h := (four_iff E x y hmax hxy).1 hw
  have := hmax (y-1) h.1
  omega

private theorem simple_four (a : ℤ) (n : ℕ) (b : Bool) (hn : 10 ≤ n) :
    weight (shifted (memory (simple a n b) (top a n b)) 1)=4 := by
  have hm := (simple_top a n b hn).2
  have hh := four_iff (simple a n b) (top a n b) (top a n b+1) hm (by omega)
  rw [show top a n b+1-top a n b=1 by omega] at hh
  apply hh.2
  cases b <;> simp only [simple_mem, top, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem image_interval (a l u : ℤ) :
    (Finset.Icc l u).image (fun z => a+z) = Finset.Icc (a+l) (a+u) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨w, hw, rfl⟩; omega
  · intro hz; exact ⟨z-a, by omega, by omega⟩

private theorem ten_good (E : Finset ℤ) (hcard : E.card=10) :
    count E+26=4*E.card ↔ good E E.card := by
  have hh := (PlasticTenPointEquality.whole_ten_point_equality E hcard).1
  simp only [Finset.image_insert, Finset.image_union, Finset.image_singleton,
    image_interval, add_zero] at hh
  rw [hcard]
  have heq : count E+26=4*10 ↔ count E=14 := by omega
  rw [heq, hh]
  simp only [good, simple, Nat.cast_ofNat]
  constructor
  · rintro ⟨a,h|h|h|h⟩
    · exact Or.inl ⟨a,false,by simpa [add_sub_assoc] using h⟩
    · exact Or.inl ⟨a,true,by simpa [add_sub_assoc] using h⟩
    · exact Or.inr ⟨True.intro,a,Or.inl h⟩
    · exact Or.inr ⟨True.intro,a,Or.inr h⟩
  · rintro (⟨a,b,h⟩|⟨_,a,h|h⟩)
    · cases b
      · exact ⟨a,Or.inl (by simpa [add_sub_assoc] using h)⟩
      · exact ⟨a,Or.inr (Or.inl (by simpa [add_sub_assoc] using h))⟩
    · exact ⟨a,Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨a,Or.inr (Or.inr (Or.inr h))⟩

private theorem good_step (E : Finset ℤ) (x y : ℤ) (n : ℕ) (hn : 10 ≤ n)
    (hx : x ∈ E) (hmax : ∀ z ∈ E, z ≤ x) (hxy : x < y) :
    good (insert y E) (n+1) ↔
      good E n ∧ weight (shifted (memory E x) (y - x)) = 4 := by
  classical
  have hynot : y∉E := by intro h; have := hmax y h; omega
  constructor
  · intro hg
    obtain ⟨a,b,hs⟩ := hg.resolve_right (by rintro ⟨h,_⟩; omega)
    obtain ⟨ht,hm⟩ := simple_top a (n+1) b (by omega)
    have hy_mem : y∈simple a (n+1) b := by rw [← hs]; simp
    have htop_mem : top a (n+1) b∈insert y E := by rw [hs]; exact ht
    have hy_top : y=top a (n+1) b := by
      have hyt := hm y hy_mem
      rcases Finset.mem_insert.1 htop_mem with h|h
      · exact h.symm
      · have := hmax _ h; omega
    have hE : E=simple a n b := by
      have he := congrArg (fun F : Finset ℤ => F.erase y) hs
      rw [Finset.erase_insert hynot, hy_top, simple_erase a n b hn] at he
      exact he
    have hx_top : x=top a n b := by
      have hxt : x∈simple a n b := by rw [← hE]; exact hx
      have htE : top a n b∈E := by rw [hE]; exact (simple_top a n b hn).1
      have := (simple_top a n b hn).2 x hxt
      have := hmax _ htE
      omega
    have hy_next : y=x+1 := by
      rw [hx_top,hy_top]
      cases b <;> simp [top] <;> omega
    refine ⟨Or.inl ⟨a,b,hE⟩,?_⟩
    rw [show y-x=1 by omega, hE, hx_top]
    exact simple_four a n b hn
  · rintro ⟨hg,hw⟩
    have hy_next := four_gap E x y hmax hxy hw
    rcases hg with ⟨a,b,hE⟩|⟨hn10,a,hE|hE⟩
    · have hx_top : x=top a n b := by
        have hxt : x∈simple a n b := by rw [← hE]; exact hx
        have htE : top a n b∈E := by rw [hE]; exact (simple_top a n b hn).1
        have := (simple_top a n b hn).2 x hxt
        have := hmax _ htE
        omega
      refine Or.inl ⟨a,b,?_⟩
      rw [hy_next,hx_top,hE]
      exact simple_extend a n b hn
    · have hx_eq : x=a+10 := by
        have hxm := hx
        rw [hE] at hxm
        have htop : a+10∈E := by rw [hE]; simp
        have := hmax _ htop
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_Icc] at hxm
        omega
      have h9 := ((four_iff E x y hmax hxy).1 hw).2.2.2.2.2.2
      rw [hE] at h9
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_Icc] at h9
      omega
    · have hx_eq : x=a+12 := by
        have hxm := hx
        rw [hE] at hxm
        have htop : a+12∈E := by rw [hE]; simp
        have := hmax _ htop
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_Icc] at hxm
        omega
      have h9 := ((four_iff E x y hmax hxy).1 hw).2.2.2.2.2.2
      rw [hE] at h9
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_Icc] at h9
      omega

/-- Actual maximum insertion carries both numerical and structural tightness. -/
private theorem classify (E : Finset ℤ) : 10≤E.card →
    (count E+26=4*E.card ↔ good E E.card) := by
  classical
  induction E using Finset.induction_on_max with
  | empty => simp
  | @insert y E hy ih =>
    intro hn
    by_cases hten : (insert y E).card=10
    · exact ten_good _ hten
    have hynot : y∉E := fun h => lt_irrefl y (hy y h)
    have hcard := Finset.card_insert_of_notMem hynot
    have hprev : 10≤E.card := by omega
    have hne : E.Nonempty := Finset.card_pos.1 (by omega)
    let x := E.max' hne
    have hx : x ∈ E := Finset.max'_mem E hne
    have hm : ∀ z ∈ E, z ≤ x := fun z hz => Finset.le_max' E z hz
    have hxy : x < y := hy x hx
    have hc := count_insert E x y hm hxy
    have hb := count_bound E hprev
    have hw := weight_le_four (shifted (memory E x) (y-x))
    have he : count (insert y E)+26=4*(E.card+1) ↔
        count E+26=4*E.card ∧ weight (shifted (memory E x) (y - x)) = 4 := by omega
    rw [hcard,he,ih hprev]
    exact (good_step E x y E.card hprev hx hm hxy).symm

/-- Full classification for arbitrary integer exponent sets of size at least eleven,
including equality for their actual real-power sumsets. -/
theorem whole_large_equality (E : Finset ℤ) (hn : 11 ≤ E.card) :
    let n := E.card
    let classified := ∃ a : ℤ,
      E=(Finset.Icc (0:ℤ) ((n:ℤ)-1)).image (fun z => a+z) ∨
      E=(insert (0:ℤ) (Finset.Icc 2 (n:ℤ))).image (fun z => a+z)
    (count E=4*n-26 ↔ classified) ∧
    ∀ r : ℝ, 1<r → r^3=r+1 →
      (((E.image (fun z => r^z))+(E.image (fun z => r^z))).card=
        n*(n+1)/2-4*n+26 ↔ classified) := by
  classical
  dsimp only
  have hc := classify E (by omega)
  have hg : good E E.card ↔ ∃ a : ℤ,
      E=(Finset.Icc (0:ℤ) ((E.card:ℤ)-1)).image (fun z => a+z) ∨
      E=(insert (0:ℤ) (Finset.Icc 2 (E.card:ℤ))).image (fun z => a+z) := by
    simp only [good, Finset.image_insert, image_interval, add_zero]
    constructor
    · rintro (⟨a,b,h⟩|⟨h,_⟩)
      · cases b
        · exact ⟨a,Or.inl (by simpa [simple, add_sub_assoc] using h)⟩
        · exact ⟨a,Or.inr (by simpa [simple, add_sub_assoc] using h)⟩
      · omega
    · rintro ⟨a,h|h⟩
      · exact Or.inl ⟨a,false,by simpa [simple, add_sub_assoc] using h⟩
      · exact Or.inl ⟨a,true,by simpa [simple, add_sub_assoc] using h⟩
  have hcount : count E=4*E.card-26 ↔ count E+26=4*E.card := by omega
  have hclass := hcount.trans (hc.trans hg)
  refine ⟨hclass,?_⟩
  intro r hr hroot
  have hs := sum_card_identity r hr hroot E
  have hprod : 8*E.card≤E.card*(E.card+1) := by nlinarith
  have hM : 4*E.card≤E.card*(E.card+1)/2 := by omega
  constructor
  · intro hsum; apply hclass.1; omega
  · intro hshape; have := hclass.2 hshape; omega

end D5.S3.Arith.Additive.PlasticLargeEquality
