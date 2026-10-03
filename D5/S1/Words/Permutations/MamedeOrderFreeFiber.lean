/- GID: D5/S1/Words/Permutations/MamedeOrderFreeFiber
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeOrderFreeFiber
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Order-free endpoint extraction gives singleton-fiber uniqueness when j<i. -/

import D5.S1.Words.Permutations.MamedeShapeExtraction
import D5.S1.Words.Permutations.MamedeFactorSeparation

namespace D5.S1.Words.Permutations.MamedeOrderFreeFiber

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeGuardedWalk
open D5.S1.Words.Permutations.MamedeCrossing
open D5.S1.Words.Permutations.MamedeFactorSeparation


/-- The three endpoint strands determine oriented runs in every source word.
    The ascent is read by following the extreme strand through the reversed word. -/
private theorem source_forced_runs_order_free (n m M i j : Nat)
    (σ : Equiv.Perm (Fin (n + 1))) (a : List Nat)
    (hm : 1 ≤ m) (hmj : m < j) (hji : j < i) (hiM : i < M) (hMn : M ≤ n)
    (hmax : σ (position n (M + 1)) = position n m)
    (hj : σ (position n m) = position n (j + 1))
    (hi : σ (position n i) = position n (M + 1))
    (hfixed : ∀ k : Fin (n + 1),
      k.val + 1 < m ∨ M + 1 < k.val + 1 → σ k = k)
    (ha : singletonWord n σ a) :
    (∃ p q, a = p ++ descending j m ++ q ∧
      (∀ k ∈ p, k < j) ∧ (∀ k ∈ q, m < k)) ∧
    (∃ p q, a = p ++ ascending m M ++ q ∧
      (∀ k ∈ p, m < k) ∧ (∀ k ∈ q, k < M)) ∧
    (∃ p q, a = p ++ descending M i ++ q ∧
      (∀ k ∈ p, k < M) ∧ (∀ k ∈ q, i < k)) := by
  have position_val (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
      (position n t).val = t - 1 := by
    simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
  have high_guard (π : Equiv.Perm (Fin (n + 1))) (t : Nat)
      (ht : 1 ≤ t ∧ t ≤ M + 1)
      (hend : π (position n t) = position n (M + 1))
      (houter : ∀ s, M + 1 < s → s ≤ n + 1 → π (position n s) = position n s) :
      ∀ r : Fin (n + 1), r.val + 1 < t →
        (π r).val < (position n (M + 1)).val := by
    intro r hr
    rw [position_val (M + 1) ⟨by omega, by omega⟩]
    by_contra hnot
    let s := (π r).val + 1
    have hs : 1 ≤ s ∧ s ≤ n + 1 := ⟨by omega, (π r).isLt⟩
    have hspos : position n s = π r := by
      apply Fin.ext
      rw [position_val s hs]
      dsimp [s]
    by_cases hst : s = M + 1
    · have heq : position n t = r := π.injective (hend.trans (hst ▸ hspos))
      have hv := congrArg Fin.val heq
      rw [position_val t ⟨ht.1, by omega⟩] at hv
      omega
    · have hsM : M + 1 < s := by dsimp [s] at *; omega
      have heq : position n s = r := π.injective ((houter s hsM hs.2).trans hspos)
      have hv := congrArg Fin.val heq
      rw [position_val s hs] at hv
      dsimp [s] at hv
      omega
  have houter (s : Nat) (hsM : M + 1 < s) (hsn : s ≤ n + 1) :
      σ (position n s) = position n s := by
    apply hfixed
    right
    rw [position_val s ⟨by omega, hsn⟩]
    omega
  have hguard_m : ∀ r : Fin (n + 1), r.val + 1 < m →
      (σ r).val < (position n (j + 1)).val := by
    intro r hr
    have hfix : σ r = r := hfixed r (Or.inl hr)
    rw [hfix, position_val (j + 1) ⟨by omega, by omega⟩]
    omega
  have hwalk_m := guarded_walk_endpoint n m (j + 1) (position n (j + 1)) a
    ⟨hm, by omega⟩ ⟨by omega, by omega⟩
    (by rw [position_val (j + 1) ⟨by omega, by omega⟩]; omega)
    rfl ha.1 (by simpa [ha.2.2] using hj) (by simpa [ha.2.2] using hguard_m)
  have hfirst := forced_descent a m j (by omega) ha.2.1 hwalk_m.1 hwalk_m.2
  have hguard_i := high_guard σ i ⟨by omega, by omega⟩ hi houter
  have hwalk_i := guarded_walk_endpoint n i (M + 1) (position n (M + 1)) a
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by rw [position_val (M + 1) ⟨by omega, by omega⟩]; omega)
    rfl ha.1 (by simpa [ha.2.2] using hi) (by simpa [ha.2.2] using hguard_i)
  have hlast := forced_descent a i M (by omega) ha.2.1 hwalk_i.1 hwalk_i.2
  have hreverse_product : wordProduct n a.reverse = σ⁻¹ := by
    rw [← ha.2.2]
    simp only [wordProduct, List.map_reverse, List.prod_reverse_noncomm, List.map_map]
    congr 1
  have hreverse_valid : validWord n a.reverse := by
    intro k hk
    exact ha.1.1 k (List.mem_reverse.mp hk)
  have hreverse_reduced : reducedWord n a.reverse := by
    refine ⟨hreverse_valid, ?_⟩
    intro v hv hprod
    have hvalid : validWord n v.reverse := by
      intro k hk
      exact hv k (List.mem_reverse.mp hk)
    have hprod_reverse : wordProduct n v.reverse = wordProduct n a := by
      have h : wordProduct n v.reverse = (wordProduct n v)⁻¹ := by
        simp only [wordProduct, List.map_reverse, List.prod_reverse_noncomm, List.map_map]
        congr 1
      rw [h, hprod, hreverse_product, inv_inv, ha.2.2]
    have hle := ha.1.2 v.reverse hvalid hprod_reverse
    simpa using hle
  have consecutive_chain (w : List Nat) :
      consecutive w ↔ w.IsChain (fun x y => x + 1 = y ∨ y + 1 = x) := by
    induction w using List.twoStepInduction with
    | nil => simp [consecutive]
    | singleton a => simp [consecutive]
    | cons_cons a b rest _ ih =>
      simpa [consecutive, List.isChain_cons_cons] using
        and_congr Iff.rfl (ih b)
  have hreverse_consecutive : consecutive a.reverse := by
    rw [consecutive_chain]
    apply List.isChain_reverse.mpr
    apply (consecutive_chain a).mp ha.2.1 |>.imp
    intro x y h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hreverse_endpoint : σ⁻¹ (position n m) = position n (M + 1) := by
    rw [← hmax]
    simp
  have hreverse_outer (s : Nat) (hsM : M + 1 < s) (hsn : s ≤ n + 1) :
      σ⁻¹ (position n s) = position n s := by
    apply σ.injective
    simpa using (houter s hsM hsn).symm
  have hreverse_guard := high_guard σ⁻¹ m ⟨hm, by omega⟩
    hreverse_endpoint hreverse_outer
  have hwalk_rev := guarded_walk_endpoint n m (M + 1) (position n (M + 1))
    a.reverse ⟨hm, by omega⟩ ⟨by omega, by omega⟩
    (by rw [position_val (M + 1) ⟨by omega, by omega⟩]; omega)
    rfl hreverse_reduced (by simpa [hreverse_product] using hreverse_endpoint)
    (by simpa [hreverse_product] using hreverse_guard)
  obtain ⟨q, p, hrev, hq, hp⟩ := forced_descent a.reverse m M (by omega)
    hreverse_consecutive hwalk_rev.1 hwalk_rev.2
  have hasc : (descending M m).reverse = ascending m M := by
    unfold descending ascending
    apply List.ext_getElem
    · simp
    · intro r hr hr'
      have hmr : m ≤ M := by omega
      have hrange : r < M - m + 1 := by simpa using hr'
      simp only [List.getElem_reverse, List.getElem_map, List.getElem_range,
        List.length_map, List.length_range]
      omega
  have hmiddle : a = p.reverse ++ ascending m M ++ q.reverse := by
    have h := congrArg List.reverse hrev
    simpa [List.reverse_append, hasc, List.append_assoc] using h
  refine ⟨hfirst, ⟨p.reverse, q.reverse, hmiddle, ?_, ?_⟩, hlast⟩
  · intro k hk
    exact hp k (List.mem_reverse.mp hk)
  · intro k hk
    exact hq k (List.mem_reverse.mp hk)

/-- The forced endpoint runs share their extreme letters and form one excursion. -/
private theorem source_shape_order_free (n m M i j : Nat)
    (σ : Equiv.Perm (Fin (n + 1))) (a : List Nat)
    (hm : 1 ≤ m) (hmj : m < j) (hji : j < i) (hiM : i < M) (hMn : M ≤ n)
    (hmax : σ (position n (M + 1)) = position n m)
    (hj : σ (position n m) = position n (j + 1))
    (hi : σ (position n i) = position n (M + 1))
    (hfixed : ∀ k : Fin (n + 1),
      k.val + 1 < m ∨ M + 1 < k.val + 1 → σ k = k)
    (ha : singletonWord n σ a) :
    ∃ p q, sourceShape m M i j a p q := by
  obtain ⟨⟨p₁, q₁, hfirst, hp₁, hq₁⟩,
    ⟨p₂, q₂, hmiddle, hp₂, hq₂⟩,
    ⟨p₃, q₃, hlast, hp₃, hq₃⟩⟩ :=
    source_forced_runs_order_free n m M i j σ a
      hm hmj hji hiM hMn hmax hj hi hfixed ha
  have desc_bounds (hi lo k : Nat) (hlo : lo ≤ hi)
      (hk : k ∈ descending hi lo) : lo ≤ k ∧ k ≤ hi := by
    unfold descending at hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
    have hr' := List.mem_range.mp hr
    omega
  have asc_bounds (lo hi k : Nat) (hlo : lo ≤ hi)
      (hk : k ∈ ascending lo hi) : lo ≤ k ∧ k ≤ hi := by
    unfold ascending at hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
    have hr' := List.mem_range.mp hr
    omega
  have descending_split_last (lo hi : Nat) (h : lo < hi) :
      descending hi lo = descending hi (lo + 1) ++ [lo] := by
    unfold descending
    rw [show hi - lo + 1 = (hi - (lo + 1) + 1) + 1 by omega,
      List.range_succ, List.map_append]
    simp only [List.map_singleton]
    congr 1
    simp only [List.cons.injEq, and_true]
    omega
  have ascending_split_first (lo hi : Nat) (h : lo < hi) :
      ascending lo hi = lo :: ascending (lo + 1) hi := by
    unfold ascending
    rw [show hi - lo + 1 = (hi - (lo + 1) + 1) + 1 by omega,
      List.range_succ_eq_map]
    simp only [List.map_cons, Nat.add_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega
  have ascending_split_last (lo hi : Nat) (h : lo < hi) :
      ascending lo hi = ascending lo (hi - 1) ++ [hi] := by
    unfold ascending
    rw [show hi - lo + 1 = (hi - 1 - lo + 1) + 1 by omega,
      List.range_succ, List.map_append]
    simp only [List.map_singleton]
    congr 1
    simp only [List.cons.injEq, and_true]
    omega
  have descending_split_first (lo hi : Nat) (h : lo < hi) :
      descending hi lo = hi :: descending (hi - 1) lo := by
    unfold descending
    rw [show hi - lo + 1 = (hi - 1 - lo + 1) + 1 by omega,
      List.range_succ_eq_map]
    simp only [List.map_cons, Nat.sub_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega
  have hfirst_m : a =
      (p₁ ++ descending j (m + 1)) ++ m :: q₁ := by
    rw [hfirst, descending_split_last m j (by omega)]
    simp [List.append_assoc]
  have hmiddle_m : a = p₂ ++ m ::
      (ascending (m + 1) (M - 1) ++ M :: q₂) := by
    rw [hmiddle, ascending_split_first m M (by omega),
      ascending_split_last (m + 1) M (by omega)]
    simp [List.append_assoc]
  have hq₁m : m ∉ q₁ := by
    intro h
    have := hq₁ m h
    omega
  have hu_m : m ∉ ascending (m + 1) (M - 1) := by
    intro h
    have := asc_bounds (m + 1) (M - 1) m (by omega) h
    omega
  have hp₁M : M ∉ p₁ ++ descending j (m + 1) := by
    intro h
    rcases List.mem_append.mp h with h | h
    · have := hp₁ M h
      omega
    · have := desc_bounds j (m + 1) M (by omega) h
      omega
  have align_first_marker_order_free (p q r u v : List Nat) (x y : Nat)
      (h : p ++ x :: q = r ++ x :: (u ++ y :: v))
      (hqr : x ∉ q) (hu : x ∉ u)
      (hpy : y ∉ p) (hxy : x ≠ y) :
      p = r ∧ q = u ++ y :: v := by
    rcases List.append_eq_append_iff.mp h with
      ⟨t, hr, ht⟩ | ⟨t, hp, ht⟩
    · cases t with
      | nil =>
        simp only [List.append_nil] at hr ht
        exact ⟨hr.symm, List.cons.inj ht |>.2⟩
      | cons z t =>
        have hz : z = x := by
          have := congrArg List.head? ht
          simpa using this.symm
        subst z
        have hxq : x ∈ q := by
          have htail := List.cons.inj ht |>.2
          rw [htail]
          simp
        exact (hqr hxq).elim
    · cases t with
      | nil =>
        simp only [List.append_nil] at hp ht
        exact ⟨hp, (List.cons.inj ht).2.symm⟩
      | cons z t =>
        have hz : z = x := by
          have := congrArg List.head? ht
          simpa using this.symm
        subst z
        have hs : u ++ y :: v = t ++ x :: q := (List.cons.inj ht).2
        rcases List.append_eq_append_iff.mp hs with
          ⟨w, ht', hw⟩ | ⟨w, hu', hw⟩
        · have hyw : y ∈ w := by
            cases w with
            | nil =>
              have hyx : y = x := by
                have := congrArg List.head? hw
                simpa using this
              exact (hxy hyx.symm).elim
            | cons z w =>
              have hz : z = y := by
                have := congrArg List.head? hw
                simpa using this.symm
              simp [hz]
          have hy : y ∈ p := by
            rw [hp, ht']
            simp [hyw]
          exact (hpy hy).elim
        · have hxw : x ∈ w := by
            cases w with
            | nil =>
              have hxy' : x = y := by
                have := congrArg List.head? hw
                simpa using this
              exact (hxy hxy').elim
            | cons z w =>
              have hz : z = x := by
                have := congrArg List.head? hw
                simpa using this.symm
              simp [hz]
          have hx : x ∈ u := by
            rw [hu']
            simp [hxw]
          exact (hu hx).elim
  have hsplit_m := align_first_marker_order_free
    (p₁ ++ descending j (m + 1)) q₁ p₂
    (ascending (m + 1) (M - 1)) q₂ m M
    (hfirst_m.symm.trans hmiddle_m) hq₁m hu_m hp₁M (by omega)
  have hmiddle_M : a = (p₂ ++ ascending m (M - 1)) ++ M :: q₂ := by
    rw [hmiddle, ascending_split_last m M (by omega)]
    simp [List.append_assoc]
  have hlast_M : a = p₃ ++ M :: (descending (M - 1) i ++ q₃) := by
    rw [hlast, descending_split_first i M (by omega)]
    simp [List.append_assoc]
  have hp₂M : M ∉ p₂ := by
    rw [← hsplit_m.1]
    exact hp₁M
  have hp_ascM : M ∉ p₂ ++ ascending m (M - 1) := by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact hp₂M h
    · have := asc_bounds m (M - 1) M (by omega) h
      omega
  have hq₂M : M ∉ q₂ := by
    intro h
    have := hq₂ M h
    omega
  have hsplit_M := (List.append_cons_inj_of_notMem hp_ascM hq₂M).mp
    (hmiddle_M.symm.trans hlast_M)
  refine ⟨p₁, q₃, ?_, ?_, ?_⟩
  · dsimp [sourceShape, fullExcursion]
    rw [hfirst, hsplit_m.2, hsplit_M.2.2]
    rw [ascending_split_last (m + 1) M (by omega)]
    simp [List.append_assoc]
  · intro k hk
    constructor
    · have hk₂ : k ∈ p₂ := by
        rw [← hsplit_m.1]
        simp [hk]
      exact hp₂ k hk₂
    · exact hp₁ k hk
  · intro k hk
    constructor
    · exact hq₃ k hk
    · have hk₂ : k ∈ q₂ := by
        rw [hsplit_M.2.2]
        simp [hk]
      exact hq₂ k hk₂

/-- Under the first-orientation endpoint data with j<i, every pair of
    singleton reduced consecutive source words is equal. -/
theorem singleton_fiber_unique_of_j_lt_i (n m M i j : Nat)
    (σ : Equiv.Perm (Fin (n + 1)))
    (hm : 1 ≤ m) (hmj : m < j) (hji : j < i) (hiM : i < M) (hMn : M ≤ n)
    (hmax : σ (position n (M + 1)) = position n m)
    (hj : σ (position n m) = position n (j + 1))
    (hi : σ (position n i) = position n (M + 1))
    (hfixed : ∀ k : Fin (n + 1),
      k.val + 1 < m ∨ M + 1 < k.val + 1 → σ k = k)
    (a b : List Nat) (ha : singletonWord n σ a) (hb : singletonWord n σ b) :
    a = b := by
  obtain ⟨p, q, hshape⟩ := source_shape_order_free n m M i j σ a
    hm hmj hji hiM hMn hmax hj hi hfixed ha
  obtain ⟨r, s, hshape'⟩ := source_shape_order_free n m M i j σ b
    hm hmj hji hiM hMn hmax hj hi hfixed hb
  exact source_shape_unique_of_j_lt_i n m M i j a b p q r s
    hm hmj hji hiM hMn ha.1 hb.1 ha.2.1 hb.2.1 (ha.2.2.trans hb.2.2.symm)
    hshape hshape'

#print axioms singleton_fiber_unique_of_j_lt_i

end D5.S1.Words.Permutations.MamedeOrderFreeFiber
