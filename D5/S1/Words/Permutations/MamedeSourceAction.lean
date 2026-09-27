/- GID: D5/S1/Words/Permutations/MamedeSourceAction
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeSourceAction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The deleted excursion and source shape constrain target crossings and support. -/

import D5.S1.Words.Permutations.MamedeCrossing

namespace D5.S1.Words.Permutations.MamedeSourceAction

open D5.S1.Words.Permutations.MamedeAdjacentWords

private theorem ascending_action (n lo hi t : Nat) (hlo : 1 ≤ lo) (hhi : lo ≤ hi ∧ hi ≤ n)
      (ht : 1 ≤ t ∧ t ≤ n + 1) :
      wordProduct n (ascending lo hi) (position n t) =
        position n (if t = hi + 1 then lo else if lo ≤ t ∧ t ≤ hi then t + 1 else t) := by
  let l := (List.range (hi - lo + 2)).map (fun r => position n (lo + r))
  have hlprod : wordProduct n (ascending lo hi) = l.formPerm := by
    unfold wordProduct ascending List.formPerm l
    congr 1
    apply List.ext_getElem
    · simp
    · intro r hr hr'
      simp [adjacent, position]
  have hv (s : Nat) (hs : 1 ≤ s ∧ s ≤ n + 1) : (position n s).val = s - 1 := by
    simp [position, Nat.mod_eq_of_lt (show s - 1 < n + 1 by omega)]
  have hnodup : l.Nodup := by
    apply List.nodup_range.map_on
    intro a ha b hb he
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    have he' := congrArg Fin.val he
    rw [hv (lo+a) ⟨by omega, by omega⟩, hv (lo+b) ⟨by omega, by omega⟩] at he'
    omega
  have hlen : l.length = hi - lo + 2 := by simp [l]
  have hget (r : Nat) (hr : r < l.length) : l[r] = position n (lo+r) := by simp [l]
  rw [hlprod]
  by_cases hmid : lo ≤ t ∧ t ≤ hi + 1
  · have hr : t-lo < l.length := by rw [hlen]; omega
    have hin : l[t-lo] = position n t := by rw [hget]; congr 1; omega
    rw [← hin, List.formPerm_apply_getElem l hnodup (t-lo) hr, hget]
    by_cases htop : t = hi+1
    · have heq : t-lo+1 = l.length := by rw [hlen]; omega
      rw [heq, Nat.mod_self]
      simp [htop]
    · have hmod : (t-lo+1) % l.length = t-lo+1 := Nat.mod_eq_of_lt (by rw [hlen]; omega)
      rw [hmod]
      have hbounds : lo ≤ t ∧ t ≤ hi := by omega
      simp [htop, hbounds, show lo+(t-lo+1)=t+1 by omega]
  · have hn : position n t ∉ l := by
      intro he
      obtain ⟨r, hr, heq⟩ := List.mem_map.mp he
      have hr' := List.mem_range.mp hr
      have he' := congrArg Fin.val heq
      rw [hv (lo+r) ⟨by omega, by omega⟩, hv t ht] at he'
      omega
    rw [List.formPerm_apply_of_notMem hn]
    have htop : t ≠ hi+1 := by omega
    have hbounds : ¬(lo ≤ t ∧ t ≤ hi) := by omega
    simp [htop, hbounds]

private theorem descending_action (n lo hi t : Nat)
      (hlo : 1 ≤ lo) (hhi : lo ≤ hi ∧ hi ≤ n)
      (ht : 1 ≤ t ∧ t ≤ n + 1) :
      wordProduct n (descending hi lo) (position n t) =
        position n (if t = lo then hi + 1 else if lo < t ∧ t ≤ hi + 1 then t - 1 else t) := by
  have hrev : descending hi lo = (ascending lo hi).reverse := by
    unfold descending ascending
    apply List.ext_getElem
    · simp
    · intro r hr hr'
      simp only [List.getElem_map, List.getElem_range, List.getElem_reverse,
        List.length_map, List.length_range]
      have : r < hi - lo + 1 := by simpa using hr
      omega
  have hprod : wordProduct n (descending hi lo) =
      (wordProduct n (ascending lo hi))⁻¹ := by
    rw [hrev]
    simp only [wordProduct, List.map_reverse, List.prod_reverse_noncomm, List.map_map]
    congr 1
  let u := if t = lo then hi + 1 else if lo < t ∧ t ≤ hi + 1 then t - 1 else t
  have hu : 1 ≤ u ∧ u ≤ n + 1 := by
    dsimp [u]
    split_ifs <;> omega
  have hF : (if u = hi + 1 then lo else if lo ≤ u ∧ u ≤ hi then u + 1 else u) = t := by
    dsimp [u]
    split_ifs <;> omega
  have hforward : wordProduct n (ascending lo hi) (position n u) = position n t := by
    rw [ascending_action n lo hi u hlo hhi hu, hF]
  rw [hprod]
  apply (wordProduct n (ascending lo hi)).injective
  simpa [u] using hforward.symm

theorem deletedExcursion_action (n m M i t : Nat)
      (hm : 1 ≤ m) (hmi : m < i) (hiM : i < M) (hMn : M ≤ n)
      (ht : 1 ≤ t ∧ t ≤ n + 1) :
      wordProduct n (deletedExcursion m M i) (position n t) =
        position n (if t = m then i else if t = i then M + 1 else
          if t = M + 1 then m else t) := by

  have append_prod (u v : List Nat) :
      wordProduct n (u ++ v) = wordProduct n u * wordProduct n v := by
    simp [wordProduct]
  have hm1 : 1 ≤ m ∧ m ≤ i - 1 := by omega
  have hi1 : 1 ≤ i ∧ i ≤ M - 1 := by omega
  have hM1 : 1 ≤ m + 1 ∧ m + 1 ≤ M := by omega
  have hR (s : Nat) (hs : 1 ≤ s ∧ s ≤ n + 1) :
      wordProduct n (descending (M - 1) i) (position n s) =
        position n (if s = i then M else if i < s ∧ s ≤ M then s - 1 else s) := by
    simpa [show M - 1 + 1 = M by omega] using
      descending_action n i (M - 1) s hi1.1 ⟨hi1.2, by omega⟩ hs
  have hA (s : Nat) (hs : 1 ≤ s ∧ s ≤ n + 1) :
      wordProduct n (ascending (m + 1) M) (position n s) =
        position n (if s = M + 1 then m + 1 else
          if m + 1 ≤ s ∧ s ≤ M then s + 1 else s) :=
    ascending_action n (m + 1) M s hM1.1 ⟨hM1.2, hMn⟩ hs
  have hL (s : Nat) (hs : 1 ≤ s ∧ s ≤ n + 1) :
      wordProduct n (descending (i - 1) m) (position n s) =
        position n (if s = m then i else if m < s ∧ s ≤ i then s - 1 else s) := by
    simpa [show i - 1 + 1 = i by omega] using
      descending_action n m (i - 1) s hm ⟨hm1.2, by omega⟩ hs
  have hprod : wordProduct n (deletedExcursion m M i) =
      wordProduct n (descending (i - 1) m) *
        wordProduct n (ascending (m + 1) M) *
          wordProduct n (descending (M - 1) i) := by
    simp [deletedExcursion, append_prod, mul_assoc]
  rw [hprod]
  change wordProduct n (descending (i - 1) m)
    (wordProduct n (ascending (m + 1) M)
      (wordProduct n (descending (M - 1) i) (position n t))) = _
  rw [hR t ht]
  by_cases htm : t = m
  · subst t
    have hR0 : (if m = i then M else if i < m ∧ m ≤ M then m - 1 else m) = m := by
      simp [show m ≠ i by omega, show ¬(i < m ∧ m ≤ M) by omega]
    rw [hR0, hA m ⟨hm, by omega⟩]
    have hA0 : (if m = M + 1 then m + 1 else
        if m + 1 ≤ m ∧ m ≤ M then m + 1 else m) = m := by
      split_ifs <;> omega
    rw [hA0, hL m ⟨hm, by omega⟩]
    simp
  · by_cases hti : t = i
    · subst t
      have hR0 : (if i = i then M else if i < i ∧ i ≤ M then i - 1 else i) = M := by simp
      rw [hR0, hA M ⟨by omega, by omega⟩]
      have hA0 : (if M = M + 1 then m + 1 else
          if m + 1 ≤ M ∧ M ≤ M then M + 1 else M) = M + 1 := by
        simp [hM1.2]
      rw [hA0, hL (M + 1) ⟨by omega, by omega⟩]
      have hnot : ¬(m < M + 1 ∧ M + 1 ≤ i) := by omega
      simp [show M + 1 ≠ m by omega,
        show ¬(m ≤ M ∧ M < i) by omega, hnot, htm]
    · by_cases htM : t = M + 1
      · subst t
        have hR0 : (if M + 1 = i then M else
            if i < M + 1 ∧ M + 1 ≤ M then M + 1 - 1 else M + 1) = M + 1 := by
          simp [show M + 1 ≠ i by omega]
        rw [hR0, hA (M + 1) ⟨by omega, by omega⟩]
        have hA0 : (if M + 1 = M + 1 then m + 1 else
            if m + 1 ≤ M + 1 ∧ M + 1 ≤ M then M + 2 else M + 1) = m + 1 := by simp
        rw [hA0, hL (m + 1) ⟨by omega, by omega⟩]
        simp [show m + 1 ≠ m by omega, show m + 1 - 1 = m by omega,
          show m < m + 1 ∧ m + 1 ≤ i by omega, htm, hti]
      · by_cases hsmall : t < m
        · have hR0 : (if t = i then M else if i < t ∧ t ≤ M then t - 1 else t) = t := by
            simp [hti, show ¬(i < t ∧ t ≤ M) by omega]
          rw [hR0, hA t ht]
          have hA0 : (if t = M + 1 then m + 1 else
              if m + 1 ≤ t ∧ t ≤ M then t + 1 else t) = t := by
            split_ifs <;> omega
          rw [hA0, hL t ht]
          simp [htm, hti, htM, show ¬(m < t ∧ t ≤ i) by omega]
        · by_cases hhigh : M + 1 < t
          · have hR0 : (if t = i then M else if i < t ∧ t ≤ M then t - 1 else t) = t := by
              simp [hti, show ¬(i < t ∧ t ≤ M) by omega]
            rw [hR0, hA t ht]
            have hA0 : (if t = M + 1 then m + 1 else
                if m + 1 ≤ t ∧ t ≤ M then t + 1 else t) = t := by
              split_ifs <;> omega
            rw [hA0, hL t ht]
            simp [htm, hti, htM, show ¬(m < t ∧ t ≤ i) by omega]
          · by_cases hbelow : t < i
            · have hR0 : (if t = i then M else if i < t ∧ t ≤ M then t - 1 else t) = t := by
                simp [hti, show ¬(i < t ∧ t ≤ M) by omega]
              rw [hR0, hA t ht]
              have hA0 : (if t = M + 1 then m + 1 else
                  if m + 1 ≤ t ∧ t ≤ M then t + 1 else t) = t + 1 := by
                simp [htM, show m + 1 ≤ t ∧ t ≤ M by omega]
              rw [hA0, hL (t + 1) ⟨by omega, by omega⟩]
              simp [htm, hti, htM, show t + 1 ≠ m by omega,
                show m < t + 1 ∧ t + 1 ≤ i by omega,
                show t + 1 - 1 = t by omega]
            · have hR0 : (if t = i then M else if i < t ∧ t ≤ M then t - 1 else t) =
                  t - 1 := by simp [hti, show i < t ∧ t ≤ M by omega]
              rw [hR0, hA (t - 1) ⟨by omega, by omega⟩]
              have hA0 : (if t - 1 = M + 1 then m + 1 else
                  if m + 1 ≤ t - 1 ∧ t - 1 ≤ M then t - 1 + 1 else t - 1) = t := by
                simp [show t - 1 ≠ M + 1 by omega,
                  show m + 1 ≤ t - 1 ∧ t - 1 ≤ M by omega,
                  show t - 1 + 1 = t by omega]
              rw [hA0, hL t ht]
              simp [htm, hti, htM, show ¬(m < t ∧ t ≤ i) by omega]

theorem source_full_product (n m M i j : Nat) (p q : List Nat)
    (hm : 1 ≤ m) (hmi : m < i) (hij : i ≤ j) (hjM : j < M) (hMn : M ≤ n)
    (hq : ∀ k ∈ q, i < k ∧ k < M) :
    wordProduct n (p ++ fullExcursion m M i j ++ q) =
      wordProduct n (imageWord i j p q) *
        wordProduct n (deletedExcursion m M i) := by
  have append_prod (u v : List Nat) :
      wordProduct n (u ++ v) = wordProduct n u * wordProduct n v := by
    simp [wordProduct]
  have hc : wordProduct n (deletedExcursion m M i) * wordProduct n q =
      wordProduct n q * wordProduct n (deletedExcursion m M i) := by
    change Commute (wordProduct n (deletedExcursion m M i)) (q.map (adjacent n)).prod
    apply Commute.list_prod_right
    intro s hs
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
    have h := hq k hk
    have hf :
        wordProduct n (deletedExcursion m M i) (position n k) = position n k ∧
          wordProduct n (deletedExcursion m M i) (position n (k + 1)) =
            position n (k + 1) := by
      constructor
      · have hact := deletedExcursion_action n m M i k hm hmi (by omega) hMn
          (show 1 ≤ k ∧ k ≤ n + 1 by omega)
        simpa [show k ≠ m by omega, show k ≠ i by omega,
          show k ≠ M + 1 by omega] using hact
      · have hact := deletedExcursion_action n m M i (k + 1) hm hmi (by omega) hMn
          (show 1 ≤ k + 1 ∧ k + 1 ≤ n + 1 by omega)
        simpa [show k + 1 ≠ m by omega, show k + 1 ≠ i by omega,
          show k ≠ M by omega, show k + 1 ≠ M + 1 by omega] using hact
    have hswap := Equiv.mul_swap_eq_swap_mul (wordProduct n (deletedExcursion m M i))
      (position n k) (position n (k + 1))
    rw [hf.1, hf.2] at hswap
    simpa [Commute, SemiconjBy, adjacent, position] using hswap
  have hsplit : descending j m = descending j i ++ descending (i - 1) m := by
    unfold descending
    rw [show j - m + 1 = (j - i + 1) + (i - 1 - m + 1) by omega,
      List.range_add, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    have := List.mem_range.mp hk
    simp only [Function.comp_apply]
    omega
  have hfull : fullExcursion m M i j = descending j i ++ deletedExcursion m M i := by
    simp [fullExcursion, deletedExcursion, hsplit, List.append_assoc]
  rw [hfull]
  simp only [imageWord, append_prod]
  calc
    wordProduct n p * wordProduct n (descending j i) *
        wordProduct n (deletedExcursion m M i) * wordProduct n q =
      (wordProduct n p * wordProduct n (descending j i)) *
        (wordProduct n (deletedExcursion m M i) * wordProduct n q) := by group
    _ = (wordProduct n p * wordProduct n (descending j i) * wordProduct n q) *
        wordProduct n (deletedExcursion m M i) := by rw [hc]; group

theorem source_target_factorization (n m M i j : Nat)
    (σ : Equiv.Perm (Fin (n + 1))) (a p₀ q₀ : List Nat)
    (hs : exactSourceHypotheses n m M i j σ)
    (hshape : sourceShape m M i j a p₀ q₀)
    (ha : singletonWord n σ a) :
    ∀ b, singletonWord n (σ * (wordProduct n (deletedExcursion m M i))⁻¹) b →
      ∃ p q, b = imageWord i j p q ∧
        (∀ k ∈ p, m < k ∧ k < j) ∧
        (∀ k ∈ q, i < k ∧ k < M) := by
  have target_endpoint (n m M i j : Nat)
      (σ : Equiv.Perm (Fin (n + 1)))
      (hs : exactSourceHypotheses n m M i j σ) :
      (σ * (wordProduct n (deletedExcursion m M i))⁻¹) (position n i) =
        position n (j + 1) := by
    rcases hs with ⟨hm, hmi, hij, hjM, hMn, _, hj, _, _, _, _, _⟩
    let γ := wordProduct n (deletedExcursion m M i)
    have hg : γ (position n m) = position n i := by
      have h := deletedExcursion_action n m M i m hm hmi (by omega) hMn
        (show 1 ≤ m ∧ m ≤ n + 1 by omega)
      simpa [γ, show m ≠ i by omega] using h
    have hinv : γ⁻¹ (position n i) = position n m := by
      rw [← hg]
      simp
    change (σ * γ⁻¹) (position n i) = position n (j + 1)
    rw [Equiv.Perm.mul_apply, hinv]
    exact hj

  have wordProduct_fixed_below (n r : Nat) (w : List Nat)
      (hr : 1 ≤ r ∧ r ≤ n + 1)
      (hw : ∀ k ∈ w, r < k ∧ k ≤ n) :
      wordProduct n w (position n r) = position n r := by
    have position_val (n t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        (position n t).val = t - 1 := by
      simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]

    have position_ne (n a b : Nat)
        (ha : 1 ≤ a ∧ a ≤ n + 1) (hb : 1 ≤ b ∧ b ≤ n + 1)
        (hab : a ≠ b) : position n a ≠ position n b := by
      intro h
      have hv := congrArg Fin.val h
      rw [position_val n a ha, position_val n b hb] at hv
      omega

    have adjacent_apply_position (n k t : Nat)
        (hk : 1 ≤ k ∧ k ≤ n) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        adjacent n k (position n t) =
          position n (if t = k then k + 1 else if t = k + 1 then k else t) := by
      have adjacent_position (r s : Nat) :
          adjacent r s = Equiv.swap (position r s) (position r (s + 1)) := by
        simp [adjacent, position]
      rw [adjacent_position]
      by_cases htk : t = k
      · subst t
        simp [Equiv.swap_apply_left]
      · by_cases htks : t = k + 1
        · subst t
          simp [Equiv.swap_apply_right]
        · simp only [htk, htks, ↓reduceIte]
          exact Equiv.swap_apply_of_ne_of_ne
            (position_ne n t k ht ⟨hk.1, by omega⟩ htk)
            (position_ne n t (k + 1) ht ⟨by omega, by omega⟩ htks)
    induction w with
    | nil => simp [wordProduct]
    | cons k w ih =>
      have hk := hw k (by simp)
      have hw' : ∀ l ∈ w, r < l ∧ l ≤ n := by
        intro l hl
        exact hw l (by simp [hl])
      change adjacent n k (wordProduct n w (position n r)) = position n r
      rw [ih hw', adjacent_apply_position n k r ⟨by omega, hk.2⟩ hr]
      simp [show r ≠ k by omega, show r ≠ k + 1 by omega]

  have adjacent_preserves_prefix (n k j : Nat) (x : Fin (n + 1))
      (hk : 1 ≤ k ∧ k < j ∧ k ≤ n) (hx : x.val < j) :
      (adjacent n k x).val < j := by
    have position_val (n t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        (position n t).val = t - 1 := by
      simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
    have adjacent_position (r s : Nat) :
        adjacent r s = Equiv.swap (position r s) (position r (s + 1)) := by
      simp [adjacent, position]
    rw [adjacent_position]
    by_cases hleft : x = position n k
    · rw [hleft, Equiv.swap_apply_left, position_val n (k + 1) ⟨by omega, by omega⟩]
      omega
    · by_cases hright : x = position n (k + 1)
      · rw [hright, Equiv.swap_apply_right, position_val n k ⟨hk.1, by omega⟩]
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
        exact hx

  have wordProduct_preserves_prefix (n j : Nat) (w : List Nat)
      (hw : ∀ k ∈ w, 1 ≤ k ∧ k < j ∧ k ≤ n)
      (x : Fin (n + 1)) (hx : x.val < j) :
      (wordProduct n w x).val < j := by
    induction w with
    | nil => simpa [wordProduct] using hx
    | cons k w ih =>
      have hk := hw k (by simp)
      have hw' : ∀ l ∈ w, 1 ≤ l ∧ l < j ∧ l ≤ n := by
        intro l hl
        exact hw l (by simp [hl])
      change (adjacent n k (wordProduct n w x)).val < j
      exact adjacent_preserves_prefix n k j (wordProduct n w x) hk (ih hw')

  have target_final_prefix_guard (n m M i j : Nat)
      (σ : Equiv.Perm (Fin (n + 1))) (a p q : List Nat)
      (hs : exactSourceHypotheses n m M i j σ)
      (hshape : sourceShape m M i j a p q)
      (hprod : wordProduct n a = σ) :
      ∀ r : Fin (n + 1), r.val + 1 < i →
        ((σ * (wordProduct n (deletedExcursion m M i))⁻¹) r).val <
          (position n (j + 1)).val := by
    have position_val (n t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        (position n t).val = t - 1 := by
      simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
    have append_prod (u v : List Nat) :
        wordProduct n (u ++ v) = wordProduct n u * wordProduct n v := by
      simp [wordProduct]
    rcases hs with ⟨hm, hmi, hij, hjM, hMn, _, _, _, _, _, _, _⟩
    have hfull := source_full_product n m M i j p q
      hm hmi hij hjM hMn hshape.2.2
    rw [← hshape.1, hprod] at hfull
    have hπ : wordProduct n (imageWord i j p q) =
        σ * (wordProduct n (deletedExcursion m M i))⁻¹ := by
      calc
        wordProduct n (imageWord i j p q) =
            (wordProduct n (imageWord i j p q) *
              wordProduct n (deletedExcursion m M i)) *
              (wordProduct n (deletedExcursion m M i))⁻¹ := by group
        _ = σ * (wordProduct n (deletedExcursion m M i))⁻¹ := by rw [← hfull]
    intro r hr
    let t := r.val + 1
    have ht : 1 ≤ t ∧ t ≤ n + 1 := by
      constructor
      · omega
      · exact r.isLt
    have hrt : position n t = r := by
      apply Fin.ext
      rw [position_val n t ht]
      dsimp [t]
    have hqfix : wordProduct n q (position n t) = position n t := by
      apply wordProduct_fixed_below n t q ht
      intro k hk
      have hq := hshape.2.2 k hk
      omega
    have hdfix : wordProduct n (descending j i) (position n t) = position n t := by
      have h := descending_action n i j t (by omega) ⟨hij, by omega⟩ ht
      simpa [show t ≠ i by omega,
        show ¬(i < t ∧ t ≤ j + 1) by omega] using h
    have hp : ∀ k ∈ p, 1 ≤ k ∧ k < j ∧ k ≤ n := by
      intro k hk
      have hpk := hshape.2.1 k hk
      omega
    have hx : (position n t).val < j := by
      rw [position_val n t ht]
      omega
    have hb : (wordProduct n (imageWord i j p q) (position n t)).val < j := by
      simp only [imageWord, append_prod, Equiv.Perm.mul_apply]
      rw [hqfix, hdfix]
      exact wordProduct_preserves_prefix n j p hp (position n t) hx
    rw [← hrt, ← hπ]
    rw [position_val n (j + 1) (show 1 ≤ j + 1 ∧ j + 1 ≤ n + 1 by omega)]
    simpa [show j + 1 - 1 = j by omega] using hb

  have target_forced_descent_weak (n m M i j : Nat)
      (σ : Equiv.Perm (Fin (n + 1))) (a p₀ q₀ : List Nat)
      (hs : exactSourceHypotheses n m M i j σ)
      (hshape : sourceShape m M i j a p₀ q₀)
      (ha : singletonWord n σ a) :
      ∀ b, singletonWord n
          (σ * (wordProduct n (deletedExcursion m M i))⁻¹) b →
        ∃ p q, b = imageWord i j p q ∧
          (∀ k ∈ p, k < j) ∧ (∀ k ∈ q, i < k) := by
    have position_val (n t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        (position n t).val = t - 1 := by
      simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
    rcases hs with ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    have hs : exactSourceHypotheses n m M i j σ :=
      ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    have hend := target_endpoint n m M i j σ hs
    have hguard := target_final_prefix_guard n m M i j σ a p₀ q₀ hs hshape ha.2.2
    intro b hb
    have hwalk : D5.S1.Words.Permutations.MamedeGuardedWalk.leftOnly (j + 1) b ∧
        D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd (j + 1) b = i := by
      apply D5.S1.Words.Permutations.MamedeCrossing.guarded_walk_endpoint n i (j + 1)
        (position n (j + 1)) b
      · constructor <;> omega
      · constructor <;> omega
      · have hxval := position_val n (j + 1)
          (show 1 ≤ j + 1 ∧ j + 1 ≤ n + 1 by omega)
        omega
      · rfl
      · exact hb.1
      · simpa [hb.2.2] using hend
      · simpa [hb.2.2] using hguard
    obtain ⟨p, q, hword, hp, hq⟩ :=
      D5.S1.Words.Permutations.MamedeGuardedWalk.forced_descent b i j hij
        hb.2.1 hwalk.1 hwalk.2
    exact ⟨p, q, hword, hp, hq⟩

  have target_fixed_exterior (n m M i j : Nat)
      (σ : Equiv.Perm (Fin (n + 1)))
      (hs : exactSourceHypotheses n m M i j σ)
      (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1)
      (hext : t ≤ m ∨ M + 1 ≤ t) :
      (σ * (wordProduct n (deletedExcursion m M i))⁻¹) (position n t) =
        position n t := by
    have position_val (n t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        (position n t).val = t - 1 := by
      simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
    rcases hs with ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    let γ := wordProduct n (deletedExcursion m M i)
    have hact (s : Nat) (hs : 1 ≤ s ∧ s ≤ n + 1) :=
      deletedExcursion_action n m M i s hm hmi (by omega) hMn hs
    have hpoint (s u : Nat) (hγ : γ (position n s) = position n u) :
        γ⁻¹ (position n u) = position n s := by
      rw [← hγ]
      simp
    change σ (γ⁻¹ (position n t)) = position n t
    rcases hext with hlow | hhigh
    · by_cases htm : t = m
      · subst t
        have hg : γ (position n (M + 1)) = position n m := by
          simpa [γ, show M + 1 ≠ m by omega,
            show M + 1 ≠ i by omega] using
            hact (M + 1) ⟨by omega, by omega⟩
        rw [hpoint (M + 1) m hg]
        exact hmax
      · have hg : γ (position n t) = position n t := by
          simpa [γ, htm, show t ≠ i by omega,
            show t ≠ M + 1 by omega] using hact t ht
        rw [hpoint t t hg]
        apply hfixed (position n t)
        left
        rw [position_val n t ht]
        omega
    · by_cases htM : t = M + 1
      · subst t
        have hg : γ (position n i) = position n (M + 1) := by
          simpa [γ, show i ≠ m by omega] using
            hact i ⟨by omega, by omega⟩
        rw [hpoint i (M + 1) hg]
        exact hi
      · have hg : γ (position n t) = position n t := by
          simpa [γ, show t ≠ m by omega,
            show t ≠ i by omega, htM] using hact t ht
        rw [hpoint t t hg]
        apply hfixed (position n t)
        right
        rw [position_val n t ht]
        omega

  have fixed_trace_avoids (t : Nat) (w : List Nat)
      (hl : D5.S1.Words.Permutations.MamedeGuardedWalk.leftOnly t w)
      (he : D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t w = t) :
      ∀ k ∈ w, k ≠ t ∧ k + 1 ≠ t := by
    induction w with
    | nil => simp
    | cons a w ih =>
      have hright : a ≠ t := hl.1
      have hleft : a + 1 ≠ t := by
        intro h
        have hs : D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t a = a := by simp [D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep, h]
        have hle := D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd_le a w
        have hend : D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd a w = t := by
          simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd, hs] using he
        omega
      have hs : D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t a = t := by
        simp [D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep, hleft]
      have htail : D5.S1.Words.Permutations.MamedeGuardedWalk.leftOnly t w := by
        simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.leftOnly, hs] using hl.2
      have hetail : D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t w = t := by
        simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd, hs] using he
      intro k hk
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact ⟨hright, hleft⟩
      · exact ih htail hetail k hk

  have fixed_suffix_guard (n t : Nat)
      (π : Equiv.Perm (Fin (n + 1)))
      (ht : 1 ≤ t ∧ t ≤ n + 1)
      (hfix : ∀ s, 1 ≤ s → t ≤ s → s ≤ n + 1 → π (position n s) = position n s) :
      ∀ r : Fin (n + 1), r.val + 1 < t →
        (π r).val < (position n t).val := by
    have position_val (n t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        (position n t).val = t - 1 := by
      simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
    intro r hr
    by_contra hnot
    let s := (π r).val + 1
    have hs : 1 ≤ s ∧ s ≤ n + 1 := by
      constructor
      · omega
      · exact (π r).isLt
    have hst : t ≤ s := by
      rw [position_val n t ht] at hnot
      dsimp [s]
      omega
    have hpos : position n s = π r := by
      apply Fin.ext
      rw [position_val n s hs]
      dsimp [s]
    have hsame : r = position n s := by
      apply π.injective
      rw [hfix s hs.1 hst hs.2]
      exact hpos.symm
    have hv := congrArg Fin.val hsame
    rw [position_val n s hs] at hv
    dsimp [s] at hv
    omega

  have target_generator_support (n m M i j : Nat)
      (σ : Equiv.Perm (Fin (n + 1)))
      (hs : exactSourceHypotheses n m M i j σ)
      (b : List Nat)
      (hb : singletonWord n
        (σ * (wordProduct n (deletedExcursion m M i))⁻¹) b) :
      ∀ k ∈ b, m < k ∧ k < M := by
    have position_val (n t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        (position n t).val = t - 1 := by
      simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
    rcases hs with ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    have hs : exactSourceHypotheses n m M i j σ :=
      ⟨hm, hmi, hij, hjM, hMn, hmax, hj, hi, hnm, hnM, hfixed, hex⟩
    let π := σ * (wordProduct n (deletedExcursion m M i))⁻¹
    have hfix := target_fixed_exterior n m M i j σ hs
    intro k hk
    have hkvalid := hb.1.1 k hk
    have havoid (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1)
        (hpt : π (position n t) = position n t)
        (hguard : ∀ r : Fin (n + 1), r.val + 1 < t →
          (π r).val < (position n t).val) :
        k ≠ t ∧ k + 1 ≠ t := by
      have hwalk := D5.S1.Words.Permutations.MamedeCrossing.guarded_walk_endpoint n t t
        (position n t) b ht ht (by rw [position_val n t ht]; omega)
        rfl hb.1 (by simpa [π, hb.2.2] using hpt)
        (by simpa [π, hb.2.2] using hguard)
      have htr : D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t b = t := hwalk.2
      exact fixed_trace_avoids t b hwalk.1 htr k hk
    constructor
    · by_contra hnot
      have hkm : k ≤ m := by omega
      have ht : 1 ≤ k ∧ k ≤ n + 1 := by omega
      have hpt : π (position n k) = position n k := hfix k ht (Or.inl hkm)
      have hguard : ∀ r : Fin (n + 1), r.val + 1 < k →
          (π r).val < (position n k).val := by
        intro r hr
        have hs' : 1 ≤ r.val + 1 ∧ r.val + 1 ≤ n + 1 := by
          constructor
          · omega
          · exact r.isLt
        have hrpos : position n (r.val + 1) = r := by
          apply Fin.ext
          rw [position_val n (r.val + 1) hs']
          simp
        have hrfix : π r = r := by
          rw [← hrpos]
          exact hfix (r.val + 1) hs' (Or.inl (by omega))
        rw [hrfix, position_val n k ht]
        omega
      exact (havoid k ht hpt hguard).1 rfl
    · by_contra hnot
      have hkM : M ≤ k := by omega
      have ht : 1 ≤ k + 1 ∧ k + 1 ≤ n + 1 := by omega
      have hpt : π (position n (k + 1)) = position n (k + 1) :=
        hfix (k + 1) ht (Or.inr (by omega))
      have hguard : ∀ r : Fin (n + 1), r.val + 1 < k + 1 →
          (π r).val < (position n (k + 1)).val := by
        apply fixed_suffix_guard n (k + 1) π ht
        intro s hs1 hks hsn
        exact hfix s ⟨hs1, hsn⟩ (Or.inr (by omega))
      exact (havoid (k + 1) ht hpt hguard).2 rfl

  intro b hb
  obtain ⟨p, q, hword, hp, hq⟩ :=
    target_forced_descent_weak n m M i j σ a p₀ q₀ hs hshape ha b hb
  have hsupport := target_generator_support n m M i j σ hs b hb
  refine ⟨p, q, hword, ?_, ?_⟩
  · intro k hk
    have hmem : k ∈ b := by rw [hword]; simp [imageWord, hk]
    exact ⟨(hsupport k hmem).1, hp k hk⟩
  · intro k hk
    have hmem : k ∈ b := by rw [hword]; simp [imageWord, hk]
    exact ⟨hq k hk, (hsupport k hmem).2⟩

end D5.S1.Words.Permutations.MamedeSourceAction
