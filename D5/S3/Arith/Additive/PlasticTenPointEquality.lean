/- GID: D5/S3/Arith/Additive/PlasticTenPointEquality
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticTenPointEquality
   mirror-E: none(waiver:integer-template-equality-classification)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Additive/PlasticTenPointEquality.whole_ten_point_equality; premises=D5/S3/Arith/Additive/PlasticTenPointEquality.backward_certificate
   digest: Every ten-point plastic extremizer is one of four translated integer patterns. -/

import D5.S3.Arith.Additive.PlasticExtremal

/-! Tight finite-state transitions classify arbitrary signed ten-point exponent sets. -/
set_option autoImplicit false

namespace D5.S3.Arith.Additive.PlasticTenPointEquality
open PlasticExtremal
open scoped Pointwise

private def modelPoint (j i : ℕ) : ℤ :=
  if j = 0 then i else if j = 1 then (if i = 0 then 0 else (i:ℤ)+1)
  else if j = 2 then (if i < 2 then i else (i:ℤ)+1)
  else (if i = 0 then 0 else if i = 1 then 3 else (i:ℤ)+3)

private def model (j k : ℕ) : Finset ℤ := (Finset.range k).image (modelPoint j)
private def last (j k : ℕ) : ℤ := modelPoint j (k-1)
private def targets (k : ℕ) : Finset (Finset ℤ) :=
  (Finset.range 4).image (fun j => memory (model j k) (last j k))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem model_data : ∀ j ∈ Finset.range 4, ∀ k ∈ Finset.Icc 1 10,
    (model j k).card = k ∧ last j k ∈ model j k ∧
      (∀ z ∈ model j k, z ≤ last j k) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem terminal_certificate : ∀ S ∈ states,
    potential 9 S = 14 → S ∈ targets 10 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_1 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 0 S < 15 → advance S g ∈ targets 2 →
      potential 0 S + weight (shifted S g) = potential 1 (advance S g) →
      S ∈ targets 1 ∧ g ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_2 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 1 S < 15 → advance S g ∈ targets 3 →
      potential 1 S + weight (shifted S g) = potential 2 (advance S g) →
      S ∈ targets 2 ∧ g ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_3 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 2 S < 15 → advance S g ∈ targets 4 →
      potential 2 S + weight (shifted S g) = potential 3 (advance S g) →
      S ∈ targets 3 ∧ g ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_4 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 3 S < 15 → advance S g ∈ targets 5 →
      potential 3 S + weight (shifted S g) = potential 4 (advance S g) →
      S ∈ targets 4 ∧ g ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_5 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 4 S < 15 → advance S g ∈ targets 6 →
      potential 4 S + weight (shifted S g) = potential 5 (advance S g) →
      S ∈ targets 5 ∧ g ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_6 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 5 S < 15 → advance S g ∈ targets 7 →
      potential 5 S + weight (shifted S g) = potential 6 (advance S g) →
      S ∈ targets 6 ∧ g ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_7 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 6 S < 15 → advance S g ∈ targets 8 →
      potential 6 S + weight (shifted S g) = potential 7 (advance S g) →
      S ∈ targets 7 ∧ g ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_8 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 7 S < 15 → advance S g ∈ targets 9 →
      potential 7 S + weight (shifted S g) = potential 8 (advance S g) →
      S ∈ targets 8 ∧ g ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem backward_9 : ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential 8 S < 15 → advance S g ∈ targets 10 →
      potential 8 S + weight (shifted S g) = potential 9 (advance S g) →
      S ∈ targets 9 ∧ g ≤ 3 := by decide +kernel

private theorem backward_certificate (k : ℕ) (hk : k ∈ Finset.Icc 1 9) :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1:ℤ) 9,
    potential (k-1) S < 15 → advance S g ∈ targets (k+1) →
      potential (k-1) S + weight (shifted S g) = potential k (advance S g) →
      S ∈ targets k ∧ g ≤ 3 := by
  obtain ⟨hk1,hk9⟩ := Finset.mem_Icc.1 hk
  interval_cases k
  · exact backward_1
  · exact backward_2
  · exact backward_3
  · exact backward_4
  · exact backward_5
  · exact backward_6
  · exact backward_7
  · exact backward_8
  · exact backward_9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Exhaustively kernel-check the finite state and gap carrier.
private theorem model_extension : ∀ j ∈ Finset.range 4, ∀ k ∈ Finset.Icc 1 9,
    ∀ g ∈ Finset.Icc (1:ℤ) 9,
    advance (memory (model j k) (last j k)) g ∈ targets (k+1) →
    potential (k-1) (memory (model j k) (last j k)) +
      weight (shifted (memory (model j k) (last j k)) g) =
        potential k (advance (memory (model j k) (last j k)) g) →
    ∃ q ∈ Finset.range 4,
      insert (last j k+g) (model j k) = model q (k+1) := by decide +kernel

private theorem memory_translate (E : Finset ℤ) (a x : ℤ) :
    memory (E.image (fun z => a+z)) (a+x) = memory E x := by
  classical
  have hmem (z : ℤ) : a+z ∈ E.image (fun w => a+w) ↔ z ∈ E := by
    constructor
    · intro hz
      obtain ⟨w, hw, he⟩ := Finset.mem_image.1 hz
      have hwz : w=z := by omega
      simpa only [hwz] using hw
    · intro hz
      exact Finset.mem_image.2 ⟨z, hz, rfl⟩
  ext d
  simp only [memory, Finset.mem_filter]
  rw [show a+x-d=a+(x-d) by omega, hmem]

private theorem count_translate (E : Finset ℤ) (a : ℤ) :
    count (E.image (fun z => a+z)) = count E := by
  classical
  have hmem (z : ℤ) : a+z ∈ E.image (fun w => a+w) ↔ z ∈ E := by
    constructor
    · intro hz
      obtain ⟨w, hw, he⟩ := Finset.mem_image.1 hz
      have hwz : w=z := by omega
      simpa only [hwz] using hw
    · intro hz
      exact Finset.mem_image.2 ⟨z, hz, rfl⟩
  have hfilters (L : Finset ℤ) :
      ((E.image (fun z => a+z)).filter
        (fun t => ∀ d ∈ L, t-d ∈ E.image (fun z => a+z))).card =
      (E.filter (fun t => ∀ d ∈ L, t-d ∈ E)).card := by
    have hs : (E.image (fun z => a+z)).filter
          (fun t => ∀ d ∈ L, t-d ∈ E.image (fun z => a+z)) =
        (E.filter (fun t => ∀ d ∈ L, t-d ∈ E)).image (fun z => a+z) := by
      ext t
      constructor
      · intro ht
        obtain ⟨ht, hp⟩ := Finset.mem_filter.1 ht
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ht
        refine Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_⟩, rfl⟩
        intro d hd
        have hh := hp d hd
        rw [show a+z-d=a+(z-d) by omega] at hh
        exact (hmem (z-d)).1 hh
      · intro ht
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ht
        obtain ⟨hz, hp⟩ := Finset.mem_filter.1 hz
        refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨z, hz, rfl⟩, ?_⟩
        intro d hd
        rw [show a+z-d=a+(z-d) by omega]
        exact (hmem (z-d)).2 (hp d hd)
    rw [hs, Finset.card_image_of_injective]
    intro u v huv
    change a+u=a+v at huv
    omega
  change
    ((E.image (fun z => a+z)).filter
      (fun t => ∀ d ∈ ({1,2,4} : Finset ℤ), t-d ∈ E.image (fun z => a+z))).card +
    ((E.image (fun z => a+z)).filter
      (fun t => ∀ d ∈ ({1,3,6} : Finset ℤ), t-d ∈ E.image (fun z => a+z))).card +
    ((E.image (fun z => a+z)).filter
      (fun t => ∀ d ∈ ({2,7} : Finset ℤ), t-d ∈ E.image (fun z => a+z))).card +
    ((E.image (fun z => a+z)).filter
      (fun t => ∀ d ∈ ({1,4,9} : Finset ℤ), t-d ∈ E.image (fun z => a+z))).card =
    (E.filter (fun t => ∀ d ∈ ({1,2,4} : Finset ℤ), t-d ∈ E)).card +
    (E.filter (fun t => ∀ d ∈ ({1,3,6} : Finset ℤ), t-d ∈ E)).card +
    (E.filter (fun t => ∀ d ∈ ({2,7} : Finset ℤ), t-d ∈ E)).card +
    (E.filter (fun t => ∀ d ∈ ({1,4,9} : Finset ℤ), t-d ∈ E)).card
  rw [hfilters, hfilters, hfilters, hfilters]

/-- Tightness in a relevant layer determines the entire prefix, not merely its state. -/
private theorem classify_tight (E : Finset ℤ) :
    1 ≤ E.card → E.card ≤ 10 →
    ∀ y ∈ E, (∀ z ∈ E, z ≤ y) → memory E y ∈ targets E.card →
    count E = potential (E.card-1) (memory E y) →
    ∃ a : ℤ, ∃ j ∈ Finset.range 4,
      E = (model j E.card).image (fun z => a+z) := by
  classical
  induction E using Finset.induction_on_max with
  | empty => simp
  | @insert y E hy ih =>
    intro hn hle z hz hmax ht hc
    have hz_eq : z=y := by
      have hyz := hmax y (by simp)
      rcases Finset.mem_insert.1 hz with rfl|hz
      · rfl
      · have := hy z hz; omega
    subst z
    have hynot : y ∉ E := fun h => lt_irrefl y (hy y h)
    rw [Finset.card_insert_of_notMem hynot] at hle ht hc ⊢
    simp only [Nat.add_sub_cancel] at hc
    rcases E.eq_empty_or_nonempty with rfl|hE
    · refine ⟨y,0,by decide,?_⟩
      simp [model,modelPoint]
    · let x := E.max' hE
      have hx : x ∈ E := Finset.max'_mem E hE
      have hmx : ∀ z ∈ E, z ≤ x := fun z hz => Finset.le_max' E z hz
      have hxy : x < y := hy x hx
      have hpos : 0 < E.card := Finset.card_pos.2 hE
      have hcert := prefix_certificate E x hx hmx (by omega)
      have hs := memory_mem_states E x hx
      have hnonneg : ∀ b ∈ memory E x, 0 ≤ b := by
        intro b hb
        exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hb).1).1
      let g : ℤ := min (y-x) 9
      obtain ⟨hcap,hweight⟩ := cap_gap (memory E x) hnonneg (y-x)
      have hg : g ∈ Finset.Icc (1:ℤ) 9 := by
        dsimp [g]; exact Finset.mem_Icc.2 ⟨by omega,by omega⟩
      have htrans : memory (insert y E) y = advance (memory E x) g := by
        rw [memory_insert E x y hmx hxy]
        exact hcap.symm
      rw [htrans] at ht hc
      have hstep := table_step (E.card-1) (by simp only [Finset.mem_range]; omega)
        (memory E x) hs g hg hcert.2
      have he : E.card-1+1=E.card := by omega
      rw [he] at hstep
      have hcount := count_insert E x y hmx hxy
      rw [← hweight] at hcount
      change count (insert y E) = count E + weight (shifted (memory E x) g) at hcount
      have hprev : count E = potential (E.card-1) (memory E x) := by omega
      have htight : potential (E.card-1) (memory E x) + weight (shifted (memory E x) g) =
          potential E.card (advance (memory E x) g) := by omega
      obtain ⟨hprevtarget,hg3⟩ := backward_certificate E.card
        (Finset.mem_Icc.2 ⟨by omega,by omega⟩) (memory E x) hs g hg hcert.2 ht htight
      have hgap : y-x=g := by dsimp [g] at hg3 ⊢; omega
      obtain ⟨a,j,hj,hmodel⟩ := ih (by omega) (by omega) x hx hmx hprevtarget hprev
      obtain ⟨hcard,hmlast,hmodelmax⟩ := model_data j hj E.card
        (Finset.mem_Icc.2 ⟨by omega,by omega⟩)
      have hxmem : x ∈ (model j E.card).image (fun z => a+z) := by rw [← hmodel]; exact hx
      obtain ⟨u,hu,hu_eq⟩ := Finset.mem_image.1 hxmem
      have hlastmem : a+last j E.card ∈ E := by
        exact (Finset.subset_of_eq hmodel.symm)
          (Finset.mem_image.2 ⟨last j E.card,hmlast,rfl⟩)
      have hx_eq : x=a+last j E.card := by
        have := hmodelmax u hu
        have := hmx (a+last j E.card) hlastmem
        omega
      have hmemeq : memory E x = memory (model j E.card) (last j E.card) := by
        calc
          memory E x = memory ((model j E.card).image (fun z => a+z)) x :=
            congrArg (fun F => memory F x) hmodel
          _ = memory (model j E.card) (last j E.card) := by
            rw [hx_eq,memory_translate]
      rw [hmemeq] at ht htight
      obtain ⟨q,hq,hqmodel⟩ := model_extension j hj E.card
        (Finset.mem_Icc.2 ⟨by omega,by omega⟩) g hg ht htight
      refine ⟨a,q,hq,?_⟩
      have hy_eq : y=a+(last j E.card+g) := by omega
      calc
        insert y E = insert (a+(last j E.card+g)) ((model j E.card).image (fun z => a+z)) :=
          congrArg₂ insert hy_eq hmodel
        _ = (insert (last j E.card+g) (model j E.card)).image (fun z => a+z) := by
          rw [Finset.image_insert]
        _ = (model q (E.card+1)).image (fun z => a+z) := congrArg _ hqmodel


set_option maxRecDepth 100000 in
private theorem model_counts : ∀ j ∈ Finset.range 4, count (model j 10) = 14 := by
  decide +kernel

private theorem model_forms :
    model 0 10 = Finset.Icc (0:ℤ) 9 ∧
    model 1 10 = insert (0:ℤ) (Finset.Icc 2 10) ∧
    model 2 10 = ({0,1}:Finset ℤ) ∪ Finset.Icc 3 10 ∧
    model 3 10 = ({0,3}:Finset ℤ) ∪ Finset.Icc 5 12 := by decide +kernel

private theorem count_eq_iff_models (E : Finset ℤ) (hcard : E.card = 10) :
    count E=14 ↔ ∃ a : ℤ, ∃ j ∈ Finset.range 4,
      E=(model j 10).image (fun z => a+z) := by
  constructor
  · intro hc
    have hE : E.Nonempty := Finset.card_pos.1 (by omega)
    let y := E.max' hE
    have hy : y ∈ E := Finset.max'_mem E hE
    have hm : ∀ z ∈ E, z ≤ y := fun z hz => Finset.le_max' E z hz
    have hcert := prefix_certificate E y hy hm (by omega)
    rw [hcard] at hcert
    change count E ≤ potential 9 (memory E y) ∧ potential 9 (memory E y) < 15 at hcert
    have ht : potential 9 (memory E y)=14 := by omega
    have hs := terminal_certificate (memory E y) (memory_mem_states E y hy) ht
    have hc' : count E=potential (E.card-1) (memory E y) := by simpa [hcard, hc] using ht.symm
    obtain ⟨a,j,hj,he⟩ := classify_tight E (by omega) (by omega) y hy hm (by simpa [hcard] using hs) hc'
    exact ⟨a,j,hj,by simpa only [hcard] using he⟩
  · rintro ⟨a,j,hj,rfl⟩
    rw [count_translate]
    exact model_counts j hj

/-- Complete equality classification among arbitrary ten-point integer sets,
including the corresponding actual real-power sumsets. -/
theorem whole_ten_point_equality (E : Finset ℤ) (hcard : E.card = 10) :
    let classified := ∃ a : ℤ,
      E=(Finset.Icc (0:ℤ) 9).image (fun z => a+z) ∨
      E=(insert (0:ℤ) (Finset.Icc 2 10)).image (fun z => a+z) ∨
      E=(({0,1}:Finset ℤ) ∪ Finset.Icc 3 10).image (fun z => a+z) ∨
      E=(({0,3}:Finset ℤ) ∪ Finset.Icc 5 12).image (fun z => a+z)
    (count E=14 ↔ classified) ∧
    ∀ r : ℝ, 1<r → r^3=r+1 →
      (((E.image (fun z => r^z))+(E.image (fun z => r^z))).card=41 ↔ classified) := by
  classical
  dsimp only
  have hclass := count_eq_iff_models E hcard
  have hforms : (∃ a : ℤ, ∃ j ∈ Finset.range 4,
      E=(model j 10).image (fun z => a+z)) ↔
      ∃ a : ℤ,
      E=(Finset.Icc (0:ℤ) 9).image (fun z => a+z) ∨
      E=(insert (0:ℤ) (Finset.Icc 2 10)).image (fun z => a+z) ∨
      E=(({0,1}:Finset ℤ) ∪ Finset.Icc 3 10).image (fun z => a+z) ∨
      E=(({0,3}:Finset ℤ) ∪ Finset.Icc 5 12).image (fun z => a+z) := by
    obtain ⟨h0,h1,h2,h3⟩ := model_forms
    constructor
    · rintro ⟨a,j,hj,he⟩
      have hj' : j<4 := Finset.mem_range.1 hj
      refine ⟨a,?_⟩
      interval_cases j
      · exact Or.inl (by simpa only [h0] using he)
      · exact Or.inr (Or.inl (by simpa only [h1] using he))
      · exact Or.inr (Or.inr (Or.inl (by simpa only [h2] using he)))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [h3] using he)))
    · rintro ⟨a,h|h|h|h⟩
      · exact ⟨a,0,by decide,by simpa only [h0] using h⟩
      · exact ⟨a,1,by decide,by simpa only [h1] using h⟩
      · exact ⟨a,2,by decide,by simpa only [h2] using h⟩
      · exact ⟨a,3,by decide,by simpa only [h3] using h⟩
  have hciff := hclass.trans hforms
  refine ⟨hciff,?_⟩
  intro r hr hroot
  have hs := sum_card_identity r hr hroot E
  rw [hcard] at hs
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.reduceDiv] at hs
  constructor
  · intro hsum
    apply hciff.1
    omega
  · intro hshape
    have hc := hciff.2 hshape
    omega

end D5.S3.Arith.Additive.PlasticTenPointEquality
