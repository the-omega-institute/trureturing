/- GID: D5/S1/Words/Permutations/MamedeOppositeExtremalMaps
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeOppositeExtremalMaps
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Symmetric excursions and opposite extremal maps force oscillation. -/

import D5.S1.Words.Permutations.MamedeEndpointUniqueness

namespace D5.S1.Words.Permutations.MamedeEndpointUniqueness

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeCrossing
open D5.S1.Words.Permutations.MamedeGuardedWalk

/-- The full excursion down to the smallest generator and back swaps just its
    two exterior positions. -/
private theorem symmetric_excursion_product (n m M : Nat)
    (hm : 1 ≤ m) (hmM : m ≤ M) (hMn : M ≤ n) :
    wordProduct n (descending M m ++
      (List.range (M - m)).map (m + 1 + ·)) =
      Equiv.swap (position n m) (position n (M + 1)) := by
  have pos_val (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
      (position n t).val = t - 1 := by
    simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
  have desc_step (lo hi : Nat) (h : lo < hi) :
      descending hi lo = hi :: descending (hi - 1) lo := by
    have hn : hi - lo + 1 = ((hi - 1) - lo + 1) + 1 := by omega
    unfold descending
    rw [hn, List.range_succ_eq_map]
    simp only [List.map_cons, Nat.sub_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega
  have tail_last (lo hi : Nat) (h : lo < hi) :
      (List.range (hi - lo)).map (lo + 1 + ·) =
        (List.range (hi - 1 - lo)).map (lo + 1 + ·) ++ [hi] := by
    rw [show hi - lo = (hi - 1 - lo) + 1 by omega,
      List.range_succ, List.map_append]
    simp only [List.map_singleton]
    congr 1
    simp only [List.cons.injEq, and_true]
    omega
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases heq : M = m
    · subst M
      have hdesc : descending m m = [m] := by simp [descending]
      rw [hdesc, Nat.sub_self]
      simp only [List.range_zero, List.map_nil, List.append_nil]
      simp [wordProduct, adjacent, position]
    · have hlt : m < M := by omega
      have hprev' : m ≤ M - 1 := by omega
      have hprev := ih (M - 1) (by omega) hprev' (by omega)
      have hadj : adjacent n M =
          Equiv.swap (position n M) (position n (M + 1)) := by
        simp [adjacent, position]
      have hfix : (Equiv.swap (position n M) (position n (M + 1)))
          (position n m) = position n m := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; have := congrArg Fin.val h
          rw [pos_val m ⟨hm, by omega⟩,
            pos_val M ⟨by omega, by omega⟩] at this
          omega
        · intro h; have := congrArg Fin.val h
          rw [pos_val m ⟨hm, by omega⟩,
            pos_val (M + 1) ⟨by omega, by omega⟩] at this
          omega
      calc
        wordProduct n (descending M m ++
            (List.range (M - m)).map (m + 1 + ·)) =
            adjacent n M *
              wordProduct n (descending (M - 1) m ++
                (List.range (M - 1 - m)).map (m + 1 + ·)) * adjacent n M := by
                  rw [desc_step m M hlt, tail_last m M hlt]
                  simp [wordProduct, List.map_append, List.prod_append, mul_assoc]
        _ = Equiv.swap (position n m) (position n (M + 1)) := by
          rw [hprev, show M - 1 + 1 = M by omega, hadj]
          conv_lhs => arg 1; rw [Equiv.mul_swap_eq_swap_mul]
          rw [hfix, Equiv.swap_apply_left]
          simp

/-- A symmetric excursion cannot be bracketed by the same interior generator
    in a reduced word: the two boundary swaps cancel through its product. -/
private theorem symmetric_excursion_not_reduced (n m M : Nat) (p q : List Nat)
    (hm : 1 ≤ m) (hgap : m + 1 < M) (hMn : M ≤ n)
    (hp : p.getLast? = some (M - 1))
    (hq : q.head? = some (M - 1)) :
    ¬ reducedWord n
      (p ++ (descending M m ++ (List.range (M - m)).map (m + 1 + ·)) ++ q) := by
  let E := descending M m ++ (List.range (M - m)).map (m + 1 + ·)
  let k := M - 1
  have hpEq : p.dropLast ++ [k] = p :=
    List.dropLast_append_getLast? k (by simp [k, hp])
  obtain ⟨s, hqEq⟩ : ∃ s, q = k :: s := by
    cases q with
    | nil => simp at hq
    | cons t s =>
      have ht : t = k := by simpa [k] using hq
      exact ⟨s, by simp [ht]⟩
  have pos_val (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
      (position n t).val = t - 1 := by
    simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
  have fix_inner (t : Nat) (ht : m < t ∧ t < M + 1) :
      (Equiv.swap (position n m) (position n (M + 1))) (position n t) =
        position n t := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; have := congrArg Fin.val h
      rw [pos_val t ⟨by omega, by omega⟩,
        pos_val m ⟨hm, by omega⟩] at this
      omega
    · intro h; have := congrArg Fin.val h
      rw [pos_val t ⟨by omega, by omega⟩,
        pos_val (M + 1) ⟨by omega, by omega⟩] at this
      omega
  have hcomm : wordProduct n E * adjacent n k =
      adjacent n k * wordProduct n E := by
    have hadj : adjacent n k = Equiv.swap (position n k) (position n (k + 1)) := by
      simp [adjacent, position]
    rw [symmetric_excursion_product n m M hm (by omega) hMn, hadj,
      Equiv.mul_swap_eq_swap_mul]
    rw [fix_inner k (by dsimp [k]; omega),
      fix_inner (k + 1) (by dsimp [k]; omega)]
  intro hr
  let r := p.dropLast
  have hv : validWord n (r ++ E ++ s) := by
    intro t ht
    have hmem : t ∈ p ++ E ++ q := by
      rw [← hpEq, hqEq]
      simp only [List.mem_append, List.mem_cons] at ht ⊢
      tauto
    exact hr.1 t (by simpa [E] using hmem)
  have heq : wordProduct n (r ++ E ++ s) = wordProduct n (p ++ E ++ q) := by
    rw [← hpEq, hqEq]
    simp only [wordProduct, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons]
    change wordProduct n r * wordProduct n E * wordProduct n s =
      wordProduct n r * adjacent n k * wordProduct n E *
        adjacent n k * wordProduct n s
    symm
    calc
      wordProduct n r * adjacent n k * wordProduct n E *
          adjacent n k * wordProduct n s =
          wordProduct n r * (adjacent n k * wordProduct n E) *
            adjacent n k * wordProduct n s := by group
      _ = wordProduct n r * (wordProduct n E * adjacent n k) *
            adjacent n k * wordProduct n s := by rw [← hcomm]
      _ = wordProduct n r * wordProduct n E * wordProduct n s := by
            simp [adjacent, mul_assoc]
  have hmin : (p ++ E ++ q).length ≤ (r ++ E ++ s).length :=
    hr.2 (r ++ E ++ s) hv (by simpa [E] using heq)
  rw [← hpEq, hqEq] at hmin
  simp only [List.length_append, List.length_cons] at hmin
  dsimp [r] at hmin
  omega

/-- A reduced consecutive word containing the full symmetric excursion cannot
    have interior letters on both sides of that excursion. -/
theorem symmetric_excursion_outer_empty (n m M : Nat) (p q : List Nat)
    (hm : 1 ≤ m) (hmM : m < M) (hMn : M ≤ n)
    (hp : ∀ k ∈ p, m < k ∧ k < M)
    (hq : ∀ k ∈ q, m < k ∧ k < M)
    (hr : reducedWord n
      (p ++ (descending M m ++ (List.range (M - m)).map (m + 1 + ·)) ++ q))
    (hc : consecutive
      (p ++ (descending M m ++ (List.range (M - m)).map (m + 1 + ·)) ++ q)) :
    p = [] ∨ q = [] := by
  by_cases hpn : p = []
  · exact Or.inl hpn
  by_cases hqn : q = []
  · exact Or.inr hqn
  let E := descending M m ++ (List.range (M - m)).map (m + 1 + ·)
  have hgap : m + 1 < M := by
    have hx := hp (p.getLast hpn) (List.getLast_mem hpn)
    omega
  have desc_step : descending M m = M :: descending (M - 1) m := by
    have hn : M - m + 1 = ((M - 1) - m + 1) + 1 := by omega
    unfold descending
    rw [hn, List.range_succ_eq_map]
    simp only [List.map_cons, Nat.sub_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega
  have hEhead : ∃ u, E = M :: u := by
    refine ⟨descending (M - 1) m ++ (List.range (M - m)).map (m + 1 + ·), ?_⟩
    simp [E, desc_step]
  have hEend : ∃ u, E = u ++ [M] := by
    let tail := (List.range ((M - 1) - m)).map (m + 1 + ·)
    have ht : (List.range (M - m)).map (m + 1 + ·) = tail ++ [M] := by
      dsimp [tail]
      rw [show M - m = (M - 1 - m) + 1 by omega,
        List.range_succ, List.map_append]
      simp only [List.map_singleton]
      congr 1
      simp only [List.cons.injEq, and_true]
      omega
    refine ⟨descending M m ++ tail, ?_⟩
    simp [E, ht, List.append_assoc]
  have hc' : (p ++ E ++ q).IsChain (fun x y => x + 1 = y ∨ y + 1 = x) :=
    (chain _).mp hc
  obtain ⟨u, hu⟩ := hEhead
  have hrelp : (p.getLast hpn) + 1 = M ∨ M + 1 = p.getLast hpn := by
    have h : (p ++ (E ++ q)).IsChain (fun x y => x + 1 = y ∨ y + 1 = x) := by
      simpa only [List.append_assoc] using hc'
    have hboundary := h.rel_getLast_head_of_append hpn (by rw [hu]; simp)
    simpa [hu] using hboundary
  have hlast : p.getLast hpn = M - 1 := by
    have hb := hp (p.getLast hpn) (List.getLast_mem hpn)
    omega
  have hpOpt : p.getLast? = some (M - 1) := by
    conv_lhs => rw [← List.dropLast_append_getLast hpn]
    simp [hlast]
  cases q with
  | nil => contradiction
  | cons t s =>
    obtain ⟨v, hv⟩ := hEend
    have hrelq : M + 1 = t ∨ t + 1 = M := by
      have h : ((p ++ E) ++ (t :: s)).IsChain
          (fun x y => x + 1 = y ∨ y + 1 = x) := by
        simpa only [List.append_assoc] using hc'
      have hboundary := h.rel_getLast_head_of_append (by rw [hv]; simp) (by simp)
      simpa [hv, List.append_assoc] using hboundary
    have ht : t = M - 1 := by
      have hb := hq t (by simp)
      omega
    exact ((symmetric_excursion_not_reduced n m M p (t :: s) hm hgap hMn
      hpOpt (by simp [ht])) hr).elim

#print axioms maximum_peel
/-- Swapping both exterior positions of the attained generator interval forces
    oscillation, without an assumed word endpoint or source factorization. -/
theorem opposite_extremal_maps_oscillation (n m M : Nat)
    (sigma : Equiv.Perm (Fin (n + 1))) (a : List Nat)
    (ha : singletonWord n sigma a) (hmem : m ∈ a) (hMem : M ∈ a)
    (hm : 1 ≤ m) (hmM : m ≤ M) (hMn : M ≤ n)
    (hb : ∀ k ∈ a, m ≤ k ∧ k ≤ M)
    (hmax : sigma (position n (M + 1)) = position n m)
    (hmin : sigma (position n m) = position n (M + 1)) :
    oscillation a := by
  by_cases heq : m = M
  · subst M
    cases a with
    | nil => simp at hmem
    | cons k a =>
      have hk : k = m := by have := hb k (by simp); omega
      apply extremal_endpoint_oscillation n m (k :: a) ha.1 ha.2.1
      · exact Or.inl (by simp [hk])
      · exact Or.inr (fun t ht => (hb t ht).1)
  have hlt : m < M := by omega
  obtain ⟨lo, hi, _, _, _, hlo, hhi, hbounds, hfixed, _⟩ :=
    D5.S1.Words.Permutations.MamedeExtremalOrientation.extremal_orientation
      n a ha.1 ha.2.1 (by intro he; simp [he] at hmem)
  have hlo_eq : lo = m := by
    have := hb lo hlo
    have := hbounds m hmem
    omega
  have hhi_eq : hi = M := by
    have := hb hi hhi
    have := hbounds M hMem
    omega
  subst lo
  subst hi
  have pos_val (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
      (position n t).val = t - 1 := by
    simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
  have hreverse_product : wordProduct n a.reverse = sigma⁻¹ := by
    rw [rev_product, ha.2.2]
  have hreverse_map : sigma⁻¹ (position n m) = position n (M + 1) := by
    rw [← hmax]
    simp
  have force (w : List Nat) (pi : Equiv.Perm (Fin (n + 1)))
      (hr : reducedWord n w) (hc : consecutive w)
      (hp : wordProduct n w = pi)
      (he : pi (position n m) = position n (M + 1))
      (hf : ∀ x : Fin (n + 1), x.val + 1 < m → pi x = x) :
      ∃ p q, w = p ++ descending M m ++ q ∧
        (∀ k ∈ p, k < M) ∧ (∀ k ∈ q, m < k) := by
    have guard : ∀ r : Fin (n + 1), r.val + 1 < m →
        (pi r).val < (position n (M + 1)).val := by
      intro r hrm
      rw [hf r hrm, pos_val (M + 1) ⟨by omega, by omega⟩]
      omega
    have walk := guarded_walk_endpoint n m (M + 1) (position n (M + 1)) w
      ⟨hm, by omega⟩ ⟨by omega, by omega⟩
      (by rw [pos_val (M + 1) ⟨by omega, by omega⟩]; omega)
      rfl hr (by simpa [hp] using he) (by simpa [hp] using guard)
    exact forced_descent w m M hmM hc walk.1 walk.2
  obtain ⟨pd, qd, hd, hpd, hqd⟩ := force a sigma ha.1 ha.2.1 ha.2.2 hmin
    (fun x hx => by simpa [ha.2.2] using hfixed x (Or.inl hx))
  obtain ⟨qr, pr, hr, hqr, hpr⟩ := force a.reverse sigma⁻¹
    (rev_reduced n a ha.1) (rev_chain a ha.2.1) hreverse_product hreverse_map
    (by
      intro x hx
      apply sigma.injective
      simpa [ha.2.2] using (hfixed x (Or.inl hx)).symm)
  have hasc : (descending M m).reverse = ascending m M := by
    unfold descending ascending
    apply List.ext_getElem
    · simp
    · intro r hr hr'
      have hrange : r < M - m + 1 := by simpa using hr'
      simp only [List.getElem_reverse, List.getElem_map, List.getElem_range,
        List.length_map, List.length_range]
      omega
  let pa := pr.reverse
  let qa := qr.reverse
  have ha_run : a = pa ++ ascending m M ++ qa := by
    simpa [pa, qa, List.reverse_append, hasc, List.append_assoc] using
      congrArg List.reverse hr
  have hpa : ∀ k ∈ pa, m < k := fun k hk => hpr k (List.mem_reverse.mp hk)
  have hqa : ∀ k ∈ qa, k < M := fun k hk => hqr k (List.mem_reverse.mp hk)
  have desc_first : descending M m = M :: descending (M - 1) m := by
    unfold descending
    rw [show M - m + 1 = (M - 1 - m + 1) + 1 by omega,
      List.range_succ_eq_map]
    simp only [List.map_cons, Nat.sub_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    have := List.mem_range.mp hk
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega
  have desc_last : descending M m = descending M (m + 1) ++ [m] := by
    unfold descending
    rw [show M - m + 1 = (M - (m + 1) + 1) + 1 by omega,
      List.range_succ, List.map_append]
    simp only [List.map_singleton]
    congr 1
    simp only [List.cons.injEq, and_true]
    omega
  have asc_first : ascending m M =
      m :: (List.range (M - m)).map (m + 1 + ·) := by
    unfold ascending
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, Nat.add_zero, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega
  have asc_last : ascending m M = ascending m (M - 1) ++ [M] := by
    unfold ascending
    rw [show M - m + 1 = (M - 1 - m + 1) + 1 by omega,
      List.range_succ, List.map_append]
    simp only [List.map_singleton]
    congr 1
    simp only [List.cons.injEq, and_true]
    omega
  -- Prefix order determines which extreme is shared by the two forced runs.
  have he : pd ++ (descending M m ++ qd) = pa ++ (ascending m M ++ qa) := by
    simpa only [List.append_assoc] using hd.symm.trans ha_run
  rcases List.append_eq_append_iff.mp he with
    ⟨t, hprefix, _⟩ | ⟨t, hprefix, _⟩
  · have hpdl : ∀ k ∈ pd, m < k := by
      intro k hk
      apply hpa k
      rw [hprefix]
      simp [hk]
    have hnotm : m ∉ pd ++ descending M (m + 1) := by
      intro hk
      rcases List.mem_append.mp hk with hk | hk
      · have := hpdl m hk; omega
      · obtain ⟨r, hr, he⟩ := List.mem_map.mp hk
        have := List.mem_range.mp hr
        omega
    have he_m : (pd ++ descending M (m + 1)) ++ m :: qd =
        pa ++ m :: ((List.range (M - m)).map (m + 1 + ·) ++ qa) := by
      simpa [desc_last, asc_first, List.append_assoc] using hd.symm.trans ha_run
    have hsplit := (List.append_cons_inj_of_notMem hnotm
      (by intro hk; have := hqd m hk; omega)).mp he_m
    have hqal : ∀ k ∈ qa, m < k := by
      intro k hk
      apply hqd k
      rw [hsplit.2.2]
      simp [hk]
    have hform : a = pd ++
        (descending M m ++ (List.range (M - m)).map (m + 1 + ·)) ++ qa := by
      rw [hd, hsplit.2.2]
      simp only [List.append_assoc]
    have hout := symmetric_excursion_outer_empty n m M pd qa hm hlt hMn
      (fun k hk => ⟨hpdl k hk, hpd k hk⟩)
      (fun k hk => ⟨hqal k hk, hqa k hk⟩)
      (hform ▸ ha.1) (hform ▸ ha.2.1)
    apply extremal_endpoint_oscillation n M a ha.1 ha.2.1
    · rcases hout with hp | hq
      · left
        rw [hd, hp, desc_first]
        simp
      · right
        rw [ha_run, hq, asc_last]
        simp
    · exact Or.inl (fun k hk => (hb k hk).2)
  · have hpau : ∀ k ∈ pa, k < M := by
      intro k hk
      apply hpd k
      rw [hprefix]
      simp [hk]
    have hnotM : M ∉ pa ++ ascending m (M - 1) := by
      intro hk
      rcases List.mem_append.mp hk with hk | hk
      · have := hpau M hk; omega
      · obtain ⟨r, hr, he⟩ := List.mem_map.mp hk
        have := List.mem_range.mp hr
        omega
    have he_M : (pa ++ ascending m (M - 1)) ++ M :: qa =
        pd ++ M :: (descending (M - 1) m ++ qd) := by
      simpa [asc_last, desc_first, List.append_assoc] using ha_run.symm.trans hd
    have hsplit := (List.append_cons_inj_of_notMem hnotM
      (by intro hk; have := hqa M hk; omega)).mp he_M
    have hqdu : ∀ k ∈ qd, k < M := by
      intro k hk
      apply hqa k
      rw [hsplit.2.2]
      simp [hk]
    have hform : a = pa ++ (ascending m M ++ descending (M - 1) m) ++ qd := by
      rw [ha_run, hsplit.2.2]
      simp only [List.append_assoc]
    have hreflect : (ascending m M ++ descending (M - 1) m).map (n + 1 - ·) =
        descending (n + 1 - m) (n + 1 - M) ++
          (List.range ((n + 1 - m) - (n + 1 - M))).map (n + 1 - M + 1 + ·) := by
      rw [List.map_append]
      congr 1
      · unfold ascending descending
        simp only [List.map_map]
        apply List.ext_getElem
        · simp; omega
        · intro r hr hr'
          have hrange : r < M - m + 1 := by simpa using hr
          simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
          omega
      · unfold descending
        simp only [List.map_map]
        apply List.ext_getElem
        · simp; omega
        · intro r hr hr'
          have hrange : r < M - 1 - m + 1 := by simpa using hr
          simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
          omega
    have hword : a.map (n + 1 - ·) = pa.map (n + 1 - ·) ++
        (descending (n + 1 - m) (n + 1 - M) ++
          (List.range ((n + 1 - m) - (n + 1 - M))).map (n + 1 - M + 1 + ·)) ++
        qd.map (n + 1 - ·) := by
      rw [hform, List.map_append, List.map_append, hreflect]
    have reflected_bounds (p : List Nat) (hp : ∀ k ∈ p, m < k ∧ k < M) :
        ∀ k ∈ p.map (n + 1 - ·), n + 1 - M < k ∧ k < n + 1 - m := by
      intro k hk
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hk
      have := hp l hl
      omega
    have hout := symmetric_excursion_outer_empty n (n + 1 - M) (n + 1 - m)
      (pa.map (n + 1 - ·)) (qd.map (n + 1 - ·)) (by omega) (by omega) (by omega)
      (reflected_bounds pa (fun k hk => ⟨hpa k hk, hpau k hk⟩))
      (reflected_bounds qd (fun k hk => ⟨hqd k hk, hqdu k hk⟩))
      (hword ▸ reflect_reduced n a ha.1)
      (hword ▸ reflect_consecutive n a ha.1.1 ha.2.1)
    have hout' : pa = [] ∨ qd = [] := by simpa only [List.map_eq_nil_iff] using hout
    apply extremal_endpoint_oscillation n m a ha.1 ha.2.1
    · rcases hout' with hp | hq
      · left
        rw [ha_run, hp, asc_first]
        simp
      · right
        rw [hd, hq, desc_last]
        simp
    · exact Or.inr (fun k hk => (hb k hk).1)

#print axioms opposite_extremal_maps_oscillation
#print axioms word_reversal_invariants
#print axioms extremal_endpoint_oscillation
#print axioms oscillation_extremal_endpoint
#print axioms extremal_endpoint_unique
#print axioms symmetric_excursion_outer_empty

end D5.S1.Words.Permutations.MamedeEndpointUniqueness
