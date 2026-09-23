/- GID: D5/S3/Combinatorics/Graph/ThreeColorOuterCases
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ThreeColorOuterCases
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Outer mixed counts force the unique mixed singleton-color leaf obstruction. -/

import D5.S3.Combinatorics.Graph.ThreeColorOuterBounds
import D5.S3.Combinatorics.Graph.ThreeColorReciprocal

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ThreeColorOuterCases

open Finset
open D5.S3.Combinatorics.Graph.ThreeColorReciprocal

variable {W : Type*} [DecidableEq W]

open Classical in
/-- For a nonisolated graph the outer mixed counts leave precisely the
singleton-color leaf exception below potential two. -/
theorem nonisolated_obstruction (s : Finset W) (adj : W → W → Prop)
    (color : W → Fin 3)
    (hsym : ∀ u ∈ s, ∀ v ∈ s, adj u v → adj v u)
    (hproper : ∀ u ∈ s, ∀ v ∈ s, adj u v → color u ≠ color v)
    (hm : ∀ v ∈ s, Mixed s adj color v → (neighborhood s adj v).card = 2)
    (hne : ∀ v ∈ s, (neighborhood s adj v).Nonempty)
    (houter : (s.filter (Mixed s adj color)).card = 0 ∨
      (s.filter (Mixed s adj color)).card = 1 ∨
      6 ≤ (s.filter (Mixed s adj color)).card)
    (hB : potential s adj color < 2) :
    ∃ w ∈ s, ∃ l ∈ s,
      (∀ v ∈ s, Mixed s adj color v ↔ v = w) ∧
      neighborhood s adj l = {w} ∧ (s.filter fun v => color v = color l) = {l} := by
  classical
  let m := fun i => (mixedColor s adj color i).card
  let x := fun i j => (ordinary s adj color i j).card
  have red := population_reduction s adj color hsym hproper hm hne
  have diag : ∀ i, x i i = 0 := red.1
  have valid : ∀ i j, i ≠ j → x i j = 0 → m j + x j i ≤ m i := red.2.1
  have sum_m : (∑ i, m i) = (s.filter (Mixed s adj color)).card := by
    have h := card_eq_sum_card_fiberwise (s := s.filter (Mixed s adj color))
      (t := univ) (f := color) (fun v hv => mem_univ _)
    simpa [m, mixedColor, filter_filter, and_comm, and_left_comm] using h.symm
  have bound : max (chargedLower m x) (quadraticLower m x) < 2 := lt_of_le_of_lt red.2.2 hB
  by_cases hl : 6 ≤ ∑ i, m i
  · exact False.elim ((not_lt_of_ge (ThreeColorOuterBounds.large_population m x diag hl))
      ((le_max_right _ _).trans_lt bound))
  have small : (∑ i, m i) ≤ 1 := by rw [sum_m] at hl ⊢; omega
  let e := Tuple.sort m
  have ordered := Tuple.monotone_sort m
  have e01 : m (e 0) ≤ m (e 1) := ordered (by decide)
  have e12 : m (e 1) ≤ m (e 2) := ordered (by decide)
  have esum : m (e 0) + m (e 1) + m (e 2) = ∑ i, m i := by
    have h := Equiv.sum_comp e m
    simpa [Fin.sum_univ_succ, add_assoc] using h
  have ez0 : m (e 0)=0 := by omega
  have ez1 : m (e 1)=0 := by omega
  let p : Equiv.Perm (Fin 3) := (Equiv.swap 0 2).trans e
  have p0 : p 0 = e 2 := by simp [p]
  have p1 : p 1 = e 1 := by
    change e (Equiv.swap (0 : Fin 3) 2 1) = e 1
    congr 1
  have p2 : p 2 = e 0 := by simp [p]
  have mz1 : m (p 1)=0 := by rw [p1]; exact ez1
  have mz2 : m (p 2)=0 := by rw [p2]; exact ez0
  have pk : m (p 0)= ∑ i, m i := by rw [p0]; omega
  have pd (i j : Fin 3) (h : i ≠ j) : p i ≠ p j := fun hh => h (p.injective hh)
  have perm : chargedLower (fun i => m (p i)) (fun i j => x (p i) (p j)) =
      chargedLower m x := by
    have inner (i : Fin 3) : (∑ j, x (p i) (p j)) = ∑ j, x (p i) j := Equiv.sum_comp p _
    have dbl (f : Fin 3 → Fin 3 → ℚ) : (∑ i, ∑ j, f (p i) (p j)) = ∑ i, ∑ j, f i j := by
      have row (i : Fin 3) : (∑ j, f (p i) (p j)) = ∑ j, f (p i) j := Equiv.sum_comp p _
      simp_rw [row]
      exact Equiv.sum_comp p (fun i => ∑ j, f i j)
    unfold chargedLower
    simp_rw [inner]
    rw [Equiv.sum_comp p (fun i => 1 / ((m i + ∑ j, x i j : ℕ) + 1 : ℚ)),
      Equiv.sum_comp p (fun i => (m i : ℚ))]
    congr 2
    convert dbl (fun i j => if i=j then 0 else
      (x i j : ℚ)/((x j i : ℚ)+1)-(m j : ℚ)/(((x j i : ℚ)+1)*((x j i : ℚ)+2))) using 1
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    by_cases heq : i=j
    · simp [heq]
    · simp [heq, show p i ≠ p j from fun h => heq (p.injective h)]
  have low := ThreeColorOuterBounds.low_population (m (p 0))
    (x (p 0) (p 1)) (x (p 1) (p 0)) (x (p 0) (p 2)) (x (p 2) (p 0))
    (x (p 1) (p 2)) (x (p 2) (p 1)) (by omega)
    (fun h => by have := valid (p 0) (p 1) (pd 0 1 (by decide)) h; omega)
    (fun h => by have := valid (p 1) (p 0) (pd 1 0 (by decide)) h; omega)
    (fun h => by have := valid (p 0) (p 2) (pd 0 2 (by decide)) h; omega)
    (fun h => by have := valid (p 2) (p 0) (pd 2 0 (by decide)) h; omega)
    (by constructor
        · intro h; have := valid (p 1) (p 2) (pd 1 2 (by decide)) h; omega
        · intro h; have := valid (p 2) (p 1) (pd 2 1 (by decide)) h; omega)
  have ident : chargedLower (fun i => m (p i)) (fun i j => x (p i) (p j)) =
      1 / ((m (p 0) + x (p 0) (p 1) + x (p 0) (p 2) : ℕ) + 1 : ℚ) +
      1 / ((x (p 1) (p 0) + x (p 1) (p 2) : ℕ) + 1 : ℚ) +
      1 / ((x (p 2) (p 0) + x (p 2) (p 1) : ℕ) + 1 : ℚ) + (m (p 0) : ℚ) / 6 +
      ((x (p 0) (p 1) : ℚ) / (x (p 1) (p 0) + 1) +
       (x (p 1) (p 0) : ℚ) / (x (p 0) (p 1) + 1) +
       (x (p 0) (p 2) : ℚ) / (x (p 2) (p 0) + 1) +
       (x (p 2) (p 0) : ℚ) / (x (p 0) (p 2) + 1) +
       (x (p 1) (p 2) : ℚ) / (x (p 2) (p 1) + 1) +
       (x (p 2) (p 1) : ℚ) / (x (p 1) (p 2) + 1)) / 2 -
      (m (p 0) : ℚ) / 2 *
        (1 / (((x (p 0) (p 1) : ℚ) + 1) * (x (p 0) (p 1) + 2)) +
         1 / (((x (p 0) (p 2) : ℚ) + 1) * (x (p 0) (p 2) + 2))) := by
    norm_num [chargedLower, Fin.sum_univ_succ, diag, mz1, mz2]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rcases low with h | ⟨hk1, hz, he, hf⟩
  · rw [← ident, perm] at h
    exact False.elim (not_lt_of_ge h ((le_max_left _ _).trans_lt bound))
  have count : (s.filter (Mixed s adj color)).card=1 := by omega
  obtain ⟨w, hw⟩ := card_eq_one.mp count
  have hws : w ∈ s := (mem_filter.mp (hw.symm ▸ mem_singleton_self w)).1
  have unique (v : W) (hv : v ∈ s) : Mixed s adj color v ↔ v=w := by
    have h : v ∈ s.filter (Mixed s adj color) ↔ v=w := by rw [hw]; simp
    simpa [hv] using h
  have cover (v : W) (hv : v ∈ s) (hn : ¬Mixed s adj color v) :
      ∃ j, v ∈ ordinary s adj color (color v) j := by
    obtain ⟨u, hu⟩ := hne v hv
    refine ⟨color u, mem_filter.mpr ⟨hv, rfl, ⟨u, hu⟩, ?_⟩⟩
    intro z hz
    by_contra hh
    exact hn ⟨z, hz, u, hu, hh⟩
  have exceptional (i j k : Fin 3) (hji : j ≠ i) (hjk : j ≠ k)
      (hall : ∀ q : Fin 3, q=i ∨ q=j ∨ q=k)
      (hmi : m i=1) (hmj : m j=0) (hij : x i j=0) (hjk0 : x j k=0) :
      ∃ l ∈ s, neighborhood s adj l={w} ∧ (s.filter fun v => color v=color l)={l} := by
    have hbj : x j i=1 := by
      have ub := valid i j hji.symm hij
      have pos : x j i ≠ 0 := by
        intro hz
        have hb := valid j i hji hz
        omega
      omega
    obtain ⟨l, hl⟩ := card_eq_one.mp hbj
    have hlm : l ∈ ordinary s adj color j i := hl.symm ▸ mem_singleton_self l
    have hls := (mem_filter.mp hlm).1
    have hlc := (mem_filter.mp hlm).2.1
    have cls : (s.filter fun v => color v=j) = {l} := by
      apply Subset.antisymm
      · intro v hv
        obtain ⟨hvs,hvc⟩ := mem_filter.mp hv
        have hn : ¬Mixed s adj color v := by
          intro hh
          have hmemb : v ∈ mixedColor s adj color j := mem_filter.mpr ⟨hvs,hvc,hh⟩
          have hem : mixedColor s adj color j=∅ := card_eq_zero.mp hmj
          simpa [hem] using hmemb
        obtain ⟨q,hq⟩ := cover v hvs hn
        rw [hvc] at hq
        rcases hall q with heq | heq | heq
        · rw [heq] at hq
          simpa [hl] using hq
        · rw [heq] at hq
          have hem : ordinary s adj color j j=∅ := card_eq_zero.mp (diag j)
          simpa [hem] using hq
        · rw [heq] at hq
          have hem : ordinary s adj color j k=∅ := card_eq_zero.mp hjk0
          simpa [hem] using hq
      · intro v hv
        rw [mem_singleton] at hv
        subst v
        exact mem_filter.mpr ⟨hls,hlc⟩
    have only (z : W) (hz : z ∈ neighborhood s adj l) : z=w := by
      obtain ⟨hzs,hlz⟩ := mem_filter.mp hz
      have hzc := (mem_filter.mp hlm).2.2.2 z hz
      apply (unique z hzs).mp
      by_contra hn
      have hzmem : z ∈ ordinary s adj color i j := by
        refine mem_filter.mpr ⟨hzs,hzc,?_,?_⟩
        · exact ⟨l,mem_filter.mpr ⟨hls,hsym l hls z hzs hlz⟩⟩
        · intro y hy
          by_contra hh
          exact hn ⟨y,hy,l,mem_filter.mpr ⟨hls,hsym l hls z hzs hlz⟩,
            by simpa [hlc] using hh⟩
      have hem : ordinary s adj color i j=∅ := card_eq_zero.mp hij
      simpa [hem] using hzmem
    have nw : neighborhood s adj l = {w} := by
      obtain ⟨z,hz⟩ := hne l hls
      have heq := only z hz
      apply Subset.antisymm
      · intro v hv; simpa only [mem_singleton] using only v hv
      · intro v hv; rw [mem_singleton] at hv; simpa [hv,heq] using hz
    exact ⟨l,hls,nw,by simpa [hlc] using cls⟩
  have allcolors (q : Fin 3) : q=p 0 ∨ q=p 1 ∨ q=p 2 := by
    obtain ⟨i,rfl⟩ := p.surjective q
    fin_cases i <;> simp
  rcases hz with ha | hc
  · obtain ⟨l,hls,hn,hc⟩ := exceptional (p 0) (p 1) (p 2)
      (pd 1 0 (by decide)) (pd 1 2 (by decide)) allcolors hk1 mz1 ha he
    exact ⟨w,hws,l,hls,unique,hn,hc⟩
  · obtain ⟨l,hls,hn,hc⟩ := exceptional (p 0) (p 2) (p 1)
      (pd 2 0 (by decide)) (pd 2 1 (by decide))
      (fun q => by have := allcolors q; tauto) hk1 mz2 hc hf
    exact ⟨w,hws,l,hls,unique,hn,hc⟩

open Classical in
/-- Without restrictions on isolates or color-class sizes, potential below two
at mixed count zero, one, or at least six forces a unique mixed vertex adjacent
to a leaf whose entire color class is a singleton. -/
theorem result (s : Finset W) (adj : W → W → Prop) (color : W → Fin 3)
    (hsym : ∀ u ∈ s, ∀ v ∈ s, adj u v → adj v u)
    (hproper : ∀ u ∈ s, ∀ v ∈ s, adj u v → color u ≠ color v)
    (hm : ∀ v ∈ s, Mixed s adj color v → (neighborhood s adj v).card = 2)
    (houter : (s.filter (Mixed s adj color)).card = 0 ∨
      (s.filter (Mixed s adj color)).card = 1 ∨
      6 ≤ (s.filter (Mixed s adj color)).card)
    (hB : potential s adj color < 2) :
    ∃ w ∈ s, ∃ l ∈ s,
      (∀ v ∈ s, Mixed s adj color v ↔ v = w) ∧
      neighborhood s adj l = {w} ∧ (s.filter fun v => color v = color l) = {l} := by
  classical
  let t := s.filter fun v => (neighborhood s adj v).Nonempty
  have ts : t ⊆ s := filter_subset _ _
  have neighbors (v : W) (hv : v ∈ s) : neighborhood t adj v = neighborhood s adj v := by
    ext u
    change (u ∈ t.filter (adj v)) ↔ (u ∈ s.filter (adj v))
    simp only [mem_filter]
    constructor
    · rintro ⟨hu,hva⟩; exact ⟨ts hu,hva⟩
    · rintro ⟨hu,hva⟩
      exact ⟨mem_filter.mpr ⟨hu, ⟨v, mem_filter.mpr ⟨hv, hsym v hv u hu hva⟩⟩⟩, hva⟩
  have nt (v : W) (hv : v ∈ t) : (neighborhood t adj v).Nonempty := by
    rw [neighbors v (ts hv)]
    exact (mem_filter.mp hv).2
  have mt (v : W) (hv : v ∈ t) (h : Mixed t adj color v) : (neighborhood t adj v).card = 2 := by
    unfold Mixed at h
    rw [neighbors v (ts hv)] at h ⊢
    exact hm v (ts hv) h
  have isolated (v : W) (hv : v ∈ s \ t) : neighborhood s adj v = ∅ := by
    have hn : ¬(neighborhood s adj v).Nonempty := by
      intro hn
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, hn⟩)
    exact not_nonempty_iff_eq_empty.mp hn
  have scalar (a r : Nat) :
      1 / ((a : ℚ)+1) ≤ 1 / ((a+r : Nat)+1 : ℚ) + (r : ℚ)/2 := by
    cases r with
    | zero => simp
    | succ r =>
      push_cast
      apply le_of_sub_nonneg
      field_simp
      ring_nf
      positivity
  have disj : Disjoint t (s \ t) := disjoint_left.mpr (fun v hv hz => (mem_sdiff.mp hz).2 hv)
  have count (i : Fin 3) : (s.filter fun v => color v=i).card =
      (t.filter fun v => color v=i).card + ((s \ t).filter fun v => color v=i).card := by
    have hs : s = t ∪ (s \ t) := (union_sdiff_of_subset ts).symm
    conv_lhs => rw [hs, filter_union]
    exact card_union_of_disjoint (disj.mono (filter_subset _ _) (filter_subset _ _))
  have cardz : ((s \ t).card : ℚ) = ∑ i : Fin 3, (((s \ t).filter fun v => color v=i).card : ℚ) := by
    exact_mod_cast (card_eq_sum_card_fiberwise (s := s \ t) (t := univ)
      (f := color) (fun v hv => mem_univ _))
  have classes :
      (∑ i : Fin 3, 1/(((t.filter fun v => color v=i).card : ℚ)+1)) ≤
      (∑ i : Fin 3, 1/(((s.filter fun v => color v=i).card : ℚ)+1)) + ((s \ t).card : ℚ)/2 := by
    rw [cardz, sum_div, ← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    rw [count]
    exact scalar _ _
  have weights : (∑ v ∈ s, 1/((neighborhood s adj v).card+1 : ℚ)) =
      (∑ v ∈ t, 1/((neighborhood t adj v).card+1 : ℚ)) + ((s \ t).card : ℚ) := by
    have live : (∑ v ∈ t, 1/((neighborhood s adj v).card+1 : ℚ)) =
        ∑ v ∈ t, 1/((neighborhood t adj v).card+1 : ℚ) := by
      apply sum_congr rfl
      intro v hv
      rw [neighbors v (ts hv)]
    have dead : (∑ v ∈ s \ t, 1/((neighborhood s adj v).card+1 : ℚ)) = ((s \ t).card : ℚ) := by
      simp only [sum_congr rfl (fun v hv => congrArg (fun a : Nat => 1/(a+1 : ℚ))
        (congrArg Finset.card (isolated v hv))), card_empty]
      simp
    calc
      _ = (∑ v ∈ t, 1/((neighborhood s adj v).card+1 : ℚ)) +
          ∑ v ∈ s \ t, 1/((neighborhood s adj v).card+1 : ℚ) := by
        rw [← sum_union disj, union_sdiff_of_subset ts]
      _ = _ := by rw [live, dead]
  have monotone : potential t adj color ≤ potential s adj color := by
    unfold potential
    rw [weights]
    linarith only [classes]
  have mix_eq : t.filter (Mixed t adj color) = s.filter (Mixed s adj color) := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvt,hvm⟩ := mem_filter.mp hv
      apply mem_filter.mpr ⟨ts hvt,?_⟩
      unfold Mixed at hvm ⊢
      rwa [neighbors v (ts hvt)] at hvm
    · intro hv
      obtain ⟨hvs,hvm⟩ := mem_filter.mp hv
      have hvn : (neighborhood s adj v).Nonempty := by
        obtain ⟨u,hu,_,_,_⟩ := hvm
        exact ⟨u,hu⟩
      apply mem_filter.mpr ⟨mem_filter.mpr ⟨hvs,hvn⟩,?_⟩
      unfold Mixed
      rwa [neighbors v hvs]
  have htouter : (t.filter (Mixed t adj color)).card = 0 ∨
      (t.filter (Mixed t adj color)).card = 1 ∨
      6 ≤ (t.filter (Mixed t adj color)).card := by rwa [mix_eq]
  obtain ⟨w,hw,l,hl,unique,nl,cl⟩ := nonisolated_obstruction t adj color
    (fun u hu v hv => hsym u (ts hu) v (ts hv))
    (fun u hu v hv => hproper u (ts hu) v (ts hv)) mt nt htouter (monotone.trans_lt hB)
  have wm : Mixed t adj color w := (unique w hw).mpr rfl
  have occupied (i : Fin 3) : 1 ≤ (t.filter fun v => color v=i).card := by
    obtain ⟨u,hu,v,hv,huv⟩ := wm
    have hus := (mem_filter.mp hu).1
    have hvs := (mem_filter.mp hv).1
    have hwu := hproper w (ts hw) u (ts hus) (mem_filter.mp hu).2
    have hwv := hproper w (ts hw) v (ts hvs) (mem_filter.mp hv).2
    have some : color w=i ∨ color u=i ∨ color v=i := by
      have hwc := (color w).isLt
      have huc := (color u).isLt
      have hvc := (color v).isLt
      have hic := i.isLt
      simp only [ne_eq, Fin.ext_iff] at hwu hwv huv ⊢
      omega
    apply card_pos.mpr
    rcases some with hc | hc | hc
    · exact ⟨w,mem_filter.mpr ⟨hw,hc⟩⟩
    · exact ⟨u,mem_filter.mpr ⟨hus,hc⟩⟩
    · exact ⟨v,mem_filter.mpr ⟨hvs,hc⟩⟩
  have strict_scalar (a r : ℕ) (ha : 1 ≤ a) :
      1/((a : ℚ)+1) + (r : ℚ)/3 ≤ 1/((a+r : ℕ)+1 : ℚ) + (r : ℚ)/2 := by
    obtain ⟨b,rfl⟩ : ∃ b, a=b+1 := ⟨a-1,by omega⟩
    cases r with
    | zero => simp
    | succ r =>
      push_cast
      apply le_of_sub_nonneg
      field_simp
      ring_nf
      positivity
  have strongclasses :
      (∑ i : Fin 3, 1/(((t.filter fun v => color v=i).card : ℚ)+1)) +
        ((s \ t).card : ℚ)/3 ≤
      (∑ i : Fin 3, 1/(((s.filter fun v => color v=i).card : ℚ)+1)) +
        ((s \ t).card : ℚ)/2 := by
    rw [cardz, sum_div, sum_div, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    rw [count]
    exact strict_scalar _ _ (occupied i)
  have strong : potential t adj color + ((s \ t).card : ℚ)/3 ≤ potential s adj color := by
    unfold potential
    rw [weights]
    linarith only [strongclasses]
  have base := reciprocal_bound t adj color
    (fun u hu v hv => hsym u (ts hu) v (ts hv))
    (fun u hu v hv => hproper u (ts hu) v (ts hv)) mt
  have empty : s \ t=∅ := by
    apply card_eq_zero.mp
    by_contra hn
    have hnq : (1 : ℚ) ≤ (s \ t).card := by exact_mod_cast (show 1 ≤ (s \ t).card by omega)
    linarith only [strong,base,hnq,hB]
  have eq : t=s := by
    exact Subset.antisymm ts (sdiff_eq_empty_iff_subset.mp empty)
  rw [eq] at hw hl unique nl cl
  exact ⟨w,hw,l,hl,unique,nl,cl⟩

end D5.S3.Combinatorics.Graph.ThreeColorOuterCases
