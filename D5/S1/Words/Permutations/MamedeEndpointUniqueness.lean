/- GID: D5/S1/Words/Permutations/MamedeEndpointUniqueness
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeEndpointUniqueness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Extremal endpoints and opposite extremal maps force oscillation. -/

import D5.S1.Words.Permutations.MamedeCrossing
import D5.S1.Words.Permutations.MamedeExtremalOrientation
import Mathlib.Data.Fin.Rev

namespace D5.S1.Words.Permutations.MamedeEndpointUniqueness

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeCrossing
open D5.S1.Words.Permutations.MamedeGuardedWalk

/-- A reduced consecutive word starting at its greatest generator begins with
    a full descent. Every remaining generator lies above its final letter. -/
theorem maximum_peel (n M : Nat) (a : List Nat)
      (hr : reducedWord n (M :: a)) (hc : consecutive (M :: a))
      (hb : ∀ k ∈ M :: a, k ≤ M) :
      ∃ i q, 1 ≤ i ∧ i ≤ M ∧ M :: a = descending M i ++ q ∧
        (∀ k ∈ q, i < k) ∧
        wordProduct n (M :: a) (position n i) = position n (M + 1) := by
    have hM := hr.1 M (by simp)
    have pos_val (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
        (position n t).val = t - 1 := by
      simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
    have outer (v : List Nat) (hv : validWord n v) (hbv : ∀ k ∈ v, k ≤ M)
        (x : Fin (n + 1)) (hx : M < x.val) : wordProduct n v x = x := by
      induction v with
      | nil => simp [wordProduct]
      | cons k v ih =>
        have hk := hv k (by simp)
        have hkM := hbv k (by simp)
        have ht := ih (fun l hl => hv l (by simp [hl]))
          (fun l hl => hbv l (by simp [hl]))
        have ha : x ≠ position n k := by
          intro he; have := congrArg Fin.val he
          rw [pos_val k ⟨hk.1, by omega⟩] at this; omega
        have hb' : x ≠ position n (k + 1) := by
          intro he; have := congrArg Fin.val he
          rw [pos_val (k + 1) ⟨by omega, by omega⟩] at this; omega
        change (adjacent n k * wordProduct n v) x = x
        rw [Equiv.Perm.mul_apply, ht]
        simpa [adjacent, position] using Equiv.swap_apply_of_ne_of_ne ha hb'
    let σ := wordProduct n (M :: a)
    let x := σ⁻¹ (position n (M + 1))
    let i := x.val + 1
    have hi : 1 ≤ i ∧ i ≤ n + 1 := ⟨by dsimp [i]; omega, x.isLt⟩
    have hix : position n i = x := by
      apply Fin.ext
      rw [pos_val i hi]
      simp [i]
    have he : σ (position n i) = position n (M + 1) := by rw [hix]; simp [x]
    have hin : i ≤ M + 1 := by
      by_contra! hout
      have hfix := outer (M :: a) hr.1 hb (position n i) (by rw [pos_val i hi]; omega)
      have := congrArg Fin.val (hfix.symm.trans he)
      rw [pos_val i hi, pos_val (M + 1) ⟨by omega, by omega⟩] at this
      omega
    have guard : ∀ r : Fin (n + 1), r.val + 1 < i →
        (σ r).val < (position n (M + 1)).val := by
      intro r hri
      rw [pos_val (M + 1) ⟨by omega, by omega⟩]
      by_contra! hnot
      by_cases heq : (σ r).val = M
      · have heq' : σ r = position n (M + 1) := by
          apply Fin.ext
          simpa [pos_val (M + 1) ⟨by omega, by omega⟩] using heq
        have hrv := congrArg Fin.val (σ.injective (heq'.trans he.symm))
        rw [pos_val i hi] at hrv
        omega
      · have hfix := outer (M :: a) hr.1 hb (σ r) (by omega)
        have hrr : σ r = r := σ.injective hfix
        have := congrArg Fin.val hrr
        omega
    have walk := guarded_walk_endpoint n i (M + 1) (position n (M + 1)) (M :: a)
      hi ⟨by omega, by omega⟩
      (by rw [pos_val (M + 1) ⟨by omega, by omega⟩]; omega)
      rfl hr he guard
    have hiM : i ≤ M := by
      have ht := traceEnd_le M a
      have hs : leftStep (M + 1) M = M := by simp [leftStep]
      rw [← walk.2]
      simpa [traceEnd, hs] using ht
    obtain ⟨p, q, hpq, hp, hq⟩ := forced_descent (M :: a) i M hiM hc walk.1 walk.2
    have hpnil : p = [] := by
      cases p with
      | nil => rfl
      | cons k p =>
        have hk : k = M := by simpa using congrArg List.head? hpq.symm
        have := hp k (by simp)
        omega
    exact ⟨i, q, hi.1, hiM, by simpa [hpnil] using hpq, hq, he⟩

-- Reflect both positions and generator indices.
private theorem reflect_product (n : Nat) (w : List Nat) (hv : validWord n w) :
      wordProduct n (w.map (n + 1 - ·)) =
        Fin.revPerm * wordProduct n w * Fin.revPerm := by
    have gen (k : Nat) (hk : 1 ≤ k ∧ k ≤ n) :
        adjacent n (n + 1 - k) = Fin.revPerm * adjacent n k * Fin.revPerm := by
      have hpos (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
          Fin.revPerm (position n t) = position n (n + 2 - t) := by
        apply Fin.ext
        simp only [Fin.revPerm_apply, Fin.val_rev, position, Fin.val_ofNat]
        rw [Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega),
          Nat.mod_eq_of_lt (show n + 2 - t - 1 < n + 1 by omega)]
        omega
      have hadj (k : Nat) : adjacent n k = Equiv.swap (position n k) (position n (k + 1)) := by
        simp [adjacent, position]
      rw [hadj, hadj, Equiv.mul_swap_eq_swap_mul,
        hpos k ⟨hk.1, by omega⟩, hpos (k + 1) ⟨by omega, by omega⟩]
      have hrev : (Fin.revPerm : Equiv.Perm (Fin (n + 1))) * Fin.revPerm = 1 := by
        ext x; simp [Equiv.Perm.mul_apply]
      rw [mul_assoc, hrev, mul_one]
      rw [show n + 2 - (k + 1) = n + 1 - k by omega,
        show n + 2 - k = n + 1 - k + 1 by omega, Equiv.swap_comm]
    induction w with
    | nil => ext x; simp [wordProduct, Equiv.Perm.mul_apply]
    | cons k w ih =>
      have hk := hv k (by simp)
      have ht := ih (fun l hl => hv l (by simp [hl]))
      simp only [List.map_cons, wordProduct, List.map_cons, List.prod_cons] at ht ⊢
      rw [gen k hk, ht]
      have hrev : (Fin.revPerm : Equiv.Perm (Fin (n + 1))) * Fin.revPerm = 1 := by
        ext x; simp [Equiv.Perm.mul_apply]
      simp only [mul_assoc, ← mul_assoc Fin.revPerm Fin.revPerm, hrev, one_mul]
-- Apply the inverse reflection to any proposed shorter representing word.
private theorem reflect_reduced (n : Nat) (w : List Nat) (hr : reducedWord n w) :
      reducedWord n (w.map (n + 1 - ·)) := by
    have valid (v : List Nat) (hv : validWord n v) : validWord n (v.map (n + 1 - ·)) := by
      intro k hk
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hk
      have := hv l hl
      omega
    have twice (v : List Nat) (hv : validWord n v) :
        (v.map (n + 1 - ·)).map (n + 1 - ·) = v := by
      rw [List.map_map]
      calc
        _ = v.map id := by
          apply List.map_congr_left
          intro k hk
          have := hv k hk
          dsimp
          omega
        _ = v := List.map_id v
    refine ⟨valid w hr.1, ?_⟩
    intro v hv he
    have hp : wordProduct n (v.map (n + 1 - ·)) = wordProduct n w := by
      rw [reflect_product n v hv, he, ← reflect_product n (w.map (n + 1 - ·)) (valid w hr.1),
        twice w hr.1]
    have := hr.2 (v.map (n + 1 - ·)) (valid v hv) hp
    simpa using this
-- Reflection preserves the adjacent-index condition.
private theorem reflect_consecutive (n : Nat) (w : List Nat)
      (hv : validWord n w) (hc : consecutive w) :
      consecutive (w.map (n + 1 - ·)) := by
    induction w using List.twoStepInduction with
    | nil => simp [consecutive]
    | singleton k => simp [consecutive]
    | cons_cons k l w _ ih =>
      have hk := hv k (by simp)
      have hl := hv l (by simp)
      have ht := ih l (fun t ht => hv t (by simp [ht])) hc.2
      simp only [List.map_cons, consecutive]
      refine ⟨?_, ht⟩
      rcases hc.1 with h | h <;> omega
-- The chain API supplies the consecutive condition on each remaining tail.
private theorem chain (w : List Nat) :
      consecutive w ↔ w.IsChain (fun x y => x + 1 = y ∨ y + 1 = x) := by
    induction w with
    | nil => simp [consecutive]
    | cons x w ih => cases w <;> simp [consecutive, List.isChain_cons_cons, ih]
private theorem suffix_reduced (n : Nat) (p q : List Nat)
      (hr : reducedWord n (p ++ q)) : reducedWord n q := by
    refine ⟨fun k hk => hr.1 k (by simp [hk]), ?_⟩
    intro v hv he
    have hvp : validWord n (p ++ v) := by
      intro k hk
      rcases List.mem_append.mp hk with hk | hk
      · exact hr.1 k (by simp [hk])
      · exact hv k hk
    have hprod : wordProduct n (p ++ v) = wordProduct n (p ++ q) := by
      simpa only [wordProduct, List.map_append, List.prod_append] using
        congrArg (wordProduct n p * ·) he
    have := hr.2 (p ++ v) hvp hprod
    simp only [List.length_append] at this
    omega

private theorem rev_product (n : Nat) (v : List Nat) :
    wordProduct n v.reverse = (wordProduct n v)⁻¹ := by
  simp only [wordProduct, List.map_reverse, List.prod_reverse_noncomm, List.map_map]
  congr 1

private theorem rev_reduced (n : Nat) (v : List Nat) (hr : reducedWord n v) :
    reducedWord n v.reverse := by
  refine ⟨fun t ht => hr.1 t (List.mem_reverse.mp ht), ?_⟩
  intro w hw hew
  have hp : wordProduct n w.reverse = wordProduct n v := by
    rw [rev_product, hew, rev_product, inv_inv]
  simpa using hr.2 w.reverse (fun t ht => hw t (List.mem_reverse.mp ht)) hp

private theorem rev_chain (v : List Nat) (hc : consecutive v) : consecutive v.reverse := by
  rw [chain, List.isChain_reverse]
  exact (chain v).mp hc |>.imp (fun _ _ h => h.symm)

/-- An attained generator extremum at either end forces the exact broad-monotone
    spike-length predicate, using reducedness in the adjacent-swap model. -/
theorem extremal_endpoint_oscillation (n k : Nat) (w : List Nat)
    (hr : reducedWord n w) (hc : consecutive w)
    (hend : w.head? = some k ∨ w.getLast? = some k)
    (hext : (∀ t ∈ w, t ≤ k) ∨ (∀ t ∈ w, k ≤ t)) :
    let lengths := segmentLengths (spikes w)
    weakIncreasing lengths ∨ weakIncreasing lengths.reverse := by
  change oscillation w
  have internalSpikes_skip_descent (x y z : Nat) (r : List Nat)
      (hxy : y < x) (hyz : z < y) :
      internalSpikes (x :: y :: z :: r) = internalSpikes (y :: z :: r) := by
    simp [internalSpikes, show ¬ ((x < y ∧ z < y) ∨ (y < x ∧ y < z)) by omega]
  have internalSpikes_turn_valley (x y z : Nat) (r : List Nat)
      (hxy : y < x) (hyz : y < z) :
      internalSpikes (x :: y :: z :: r) = y :: internalSpikes (y :: z :: r) := by
    simp [internalSpikes, hxy, hyz]
  have internalSpikes_erase_descent (x y z : Nat) (r : List Nat)
      (hxy : y < x) (hyz : z < y) :
      internalSpikes (x :: y :: z :: r) = internalSpikes (x :: z :: r) := by
    cases r with
    | nil => simp [internalSpikes, hxy, hyz]; omega
    | cons t r =>
      rw [internalSpikes_skip_descent x y z (t :: r) hxy hyz]
      have hxz : z < x := lt_trans hyz hxy
      have hnoty : ¬ y < z := Nat.not_lt.mpr (Nat.le_of_lt hyz)
      have hnotx : ¬ x < z := Nat.not_lt.mpr (Nat.le_of_lt hxz)
      simp [internalSpikes, hyz, hxz, hnoty, hnotx]
  have spikes_erase_descent (x y z : Nat) (r : List Nat)
      (hxy : y < x) (hyz : z < y) :
      spikes (x :: y :: z :: r) = spikes (x :: z :: r) := by
    simp [spikes, internalSpikes_erase_descent x y z r hxy hyz]
  have descending_step (lo hi : Nat) (h : lo < hi) :
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
  have spikes_turn_valley (x i : Nat) (q : List Nat)
      (hxi : i < x) (hq : ∀ k ∈ q, i < k) :
      spikes (x :: i :: q) = x :: spikes (i :: q) := by
    cases q with
    | nil => simp [spikes, internalSpikes]
    | cons k q =>
      have hik := hq k (by simp)
      simp [spikes, internalSpikes_turn_valley x i k q hxi hik]
  have spikes_desc_prefix (x i y : Nat) (q : List Nat)
      (hiy : i ≤ y) (hyx : y < x) :
      spikes (x :: descending y i ++ q) = spikes (x :: i :: q) := by
    induction y using Nat.strong_induction_on generalizing x i q with
    | h y ih =>
      by_cases hiy' : i = y
      · subst y
        simp [descending]
      · have hiylt : i < y := by omega
        have hstep := descending_step i y hiylt
        have hhead : (y - 1) ∈ (descending (y - 1) i).head? := by
          simp [descending, List.head?_range]
        have htail := List.cons_head?_tail hhead
        calc
          spikes (x :: descending y i ++ q) =
              spikes (x :: y :: (y - 1) :: (descending (y - 1) i).tail ++ q) := by
                rw [hstep]
                exact congrArg (fun d => spikes (x :: y :: d ++ q)) htail.symm
          _ = spikes (x :: (y - 1) :: (descending (y - 1) i).tail ++ q) := by
                exact spikes_erase_descent x y (y - 1)
                  ((descending (y - 1) i).tail ++ q) (by omega) (by omega)
          _ = spikes (x :: descending (y - 1) i ++ q) := by
                exact congrArg (fun d => spikes (x :: d ++ q)) htail
          _ = spikes (x :: i :: q) := ih (y - 1) (by omega) x i q (by omega) (by omega)
  have spikes_descent (M i : Nat) (q : List Nat)
      (hiM : i < M) (hq : ∀ k ∈ q, i < k) :
      spikes (descending M i ++ q) = M :: spikes (i :: q) := by
    rw [descending_step i M hiM]
    rw [spikes_desc_prefix M i (M - 1) q (by omega) (by omega)]
    exact spikes_turn_valley M i q hiM hq
  have internalSpikes_mem (w : List Nat) (k : Nat)
      (hk : k ∈ internalSpikes w) : k ∈ w := by
    induction w with
    | nil => simp [internalSpikes] at hk
    | cons a w ih =>
      cases w with
      | nil => simp [internalSpikes] at hk
      | cons b w =>
        cases w with
        | nil => simp [internalSpikes] at hk
        | cons c r =>
          simp only [internalSpikes] at hk
          split_ifs at hk
          · rcases List.mem_cons.mp hk with rfl | hk
            · simp
            · exact List.mem_cons_of_mem _ (ih hk)
          · exact List.mem_cons_of_mem _ (ih hk)
  have spikes_mem (w : List Nat) (k : Nat)
      (hk : k ∈ spikes w) : k ∈ w := by
    cases w with
    | nil => simp [spikes] at hk
    | cons a w =>
      cases w with
      | nil => simpa [spikes] using hk
      | cons b r =>
        simp only [spikes, List.mem_cons, List.mem_append] at hk
        rcases hk with (rfl | hk) | hk
        · simp
        · exact internalSpikes_mem (a :: b :: r) k hk
        · rcases hk with hk | hk
          · subst k
            exact List.mem_cons_of_mem a (by simp [List.getLast!])
          · simp at hk
  have map_getLast_cons (f : Nat → Nat) (b : Nat) (r : List Nat) :
      ((b :: r).map f).getLast! = f ((b :: r).getLast!) := by
    induction r generalizing b with
    | nil => rfl
    | cons c r ih =>
      simpa [List.getLast!, List.getLast?] using ih c
  have reflect_internalSpikes (n : Nat) (w : List Nat)
      (hv : validWord n w) :
      internalSpikes (w.map (n + 1 - ·)) = (internalSpikes w).map (n + 1 - ·) := by
    induction w with
    | nil => simp [internalSpikes]
    | cons a w ih =>
      cases w with
      | nil => simp [internalSpikes]
      | cons b w =>
        cases w with
        | nil => simp [internalSpikes]
        | cons c r =>
          have ha := hv a (by simp)
          have hb := hv b (by simp)
          have hc := hv c (by simp)
          have ht := ih (fun k hk => hv k (by simp [hk]))
          have hturn :
              ((n + 1 - a < n + 1 - b ∧ n + 1 - c < n + 1 - b) ∨
                (n + 1 - b < n + 1 - a ∧ n + 1 - b < n + 1 - c)) ↔
              ((a < b ∧ c < b) ∨ (b < a ∧ b < c)) := by omega
          simp only [List.map_cons, internalSpikes]
          split_ifs <;> simp_all
  have reflect_spikes (n : Nat) (w : List Nat)
      (hv : validWord n w) :
      spikes (w.map (n + 1 - ·)) = (spikes w).map (n + 1 - ·) := by
    cases w with
    | nil => simp [spikes]
    | cons a w =>
      cases w with
      | nil => simp [spikes]
      | cons b r =>
        change (n + 1 - a) ::
            internalSpikes ((a :: b :: r).map (n + 1 - ·)) ++
              [((b :: r).map (n + 1 - ·)).getLast!] =
          ((a :: internalSpikes (a :: b :: r)) ++ [(b :: r).getLast!]).map (n + 1 - ·)
        rw [reflect_internalSpikes n (a :: b :: r) hv]
        simp only [List.map_append, List.map_cons]
        congr 1
        exact congrArg (fun z : Nat => [z]) (map_getLast_cons (n + 1 - ·) b r)
  have reflect_segmentLengths (n : Nat) (w : List Nat)
      (hv : validWord n w) :
      segmentLengths ((spikes w).map (n + 1 - ·)) = segmentLengths (spikes w) := by
    have bounds : ∀ k ∈ spikes w, 1 ≤ k ∧ k ≤ n := by
      intro k hk
      exact hv k (spikes_mem w k hk)
    have core : ∀ s : List Nat, (∀ k ∈ s, 1 ≤ k ∧ k ≤ n) →
        segmentLengths (s.map (n + 1 - ·)) = segmentLengths s := by
      intro s
      induction s with
      | nil => intros; rfl
      | cons a s ih =>
        intro hs
        cases s with
        | nil => rfl
        | cons b r =>
          have ha := hs a (by simp)
          have hb := hs b (by simp)
          have ht : ∀ k ∈ b :: r, 1 ≤ k ∧ k ≤ n := by
            intro k hk
            exact hs k (by simp [hk])
          have hd : (n + 1 - a - (n + 1 - b)) + (n + 1 - b - (n + 1 - a)) =
              (a - b) + (b - a) := by omega
          simp only [List.map_cons, segmentLengths, hd]
          exact congrArg (List.cons ((a - b) + (b - a))) (ih ht)
    exact core (spikes w) bounds
  have internalSpikes_snoc (p : List Nat) (x y z : Nat) :
      internalSpikes (p ++ [x, y, z]) = internalSpikes (p ++ [x, y]) ++
        (if (x < y ∧ z < y) ∨ (y < x ∧ y < z) then [y] else []) := by
    induction p using List.twoStepInduction with
    | nil => simp [internalSpikes]
    | singleton a =>
      simp only [List.cons_append, List.nil_append, internalSpikes]
      split_ifs <;> simp
    | cons_cons a b p _ ih =>
      cases p with
      | nil =>
        simp only [List.cons_append, List.nil_append, internalSpikes]
        split_ifs <;> simp
      | cons c r =>
        simp only [List.cons_append] at ih ⊢
        conv_lhs => rw [internalSpikes]
        conv_rhs => arg 1; rw [internalSpikes]
        split_ifs <;> simp_all [List.cons_append]
  have reverse_internalSpikes (w : List Nat) :
      internalSpikes w.reverse = (internalSpikes w).reverse := by
    induction w with
    | nil => simp [internalSpikes]
    | cons a w ih =>
      cases w with
      | nil => simp [internalSpikes]
      | cons b w =>
        cases w with
        | nil => simp [internalSpikes]
        | cons c r =>
          have hturn : ((c < b ∧ a < b) ∨ (b < c ∧ b < a)) ↔
              ((a < b ∧ c < b) ∨ (b < a ∧ b < c)) := by tauto
          simp only [List.reverse_cons, List.append_assoc] at ih ⊢
          simp only [List.singleton_append] at ih ⊢
          rw [internalSpikes_snoc r.reverse c b a]
          rw [internalSpikes]
          split_ifs <;> simp_all [List.reverse_cons]
  have reverse_spikes (w : List Nat) : spikes w.reverse = (spikes w).reverse := by
    have cons_formula (z : Nat) (t : List Nat) (hne : t ≠ []) :
        spikes (z :: t) = z :: internalSpikes (z :: t) ++ [(z :: t).getLast!] := by
      cases t with
      | nil => contradiction
      | cons k t => rfl
    cases w with
    | nil => simp [spikes]
    | cons a w =>
      cases w with
      | nil => simp [spikes]
      | cons b r =>
        cases r using List.reverseRecOn with
        | nil => simp [spikes, internalSpikes]
        | append_singleton r z =>
          have hwr : (a :: b :: (r ++ [z])).reverse =
              z :: ((b :: r).reverse ++ [a]) := by simp
          have hlast : (a :: b :: (r ++ [z])).getLast! = z := by
            change ((a :: b :: r) ++ [z]).getLast! = z
            simp [List.getLast!]
          have hfirst : (z :: ((b :: r).reverse ++ [a])).getLast! = a := by
            rw [← List.cons_append]
            simp [List.getLast!]
          have hi := reverse_internalSpikes (a :: b :: (r ++ [z]))
          rw [hwr] at hi ⊢
          rw [cons_formula z ((b :: r).reverse ++ [a]) (by simp), hfirst]
          rw [cons_formula a (b :: (r ++ [z])) (by simp), hlast]
          rw [hi]
          simp
  have segmentLengths_snoc (p : List Nat) (x y : Nat) :
      segmentLengths (p ++ [x, y]) =
        segmentLengths (p ++ [x]) ++ [(x - y) + (y - x)] := by
    induction p with
    | nil => simp [segmentLengths]
    | cons a p ih =>
      cases p with
      | nil => simp [segmentLengths]
      | cons b p =>
        simp only [List.cons_append] at ih ⊢
        conv_lhs => rw [segmentLengths]
        conv_rhs => arg 1; rw [segmentLengths]
        rw [ih]
        rfl
  have reverse_segmentLengths (s : List Nat) :
      segmentLengths s.reverse = (segmentLengths s).reverse := by
    induction s with
    | nil => simp [segmentLengths]
    | cons a s ih =>
      cases s with
      | nil => simp [segmentLengths]
      | cons b r =>
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at ih ⊢
        rw [segmentLengths_snoc r.reverse b a, ih]
        simp [segmentLengths, add_comm]
  have weakIncreasing_chain (l : List Nat) :
      weakIncreasing l ↔ l.IsChain (· ≤ ·) := by
    induction l with
    | nil => simp [weakIncreasing]
    | cons a l ih =>
      cases l with
      | nil => simp [weakIncreasing]
      | cons b r =>
        rw [weakIncreasing, List.isChain_cons_cons]
        exact and_congr Iff.rfl ih
  have weakIncreasing_rev_cons (d : Nat) (l : List Nat)
      (hl : weakIncreasing l.reverse)
      (hb : ∀ x ∈ l.head?, x ≤ d) :
      weakIncreasing (d :: l).reverse := by
    rw [weakIncreasing_chain] at hl ⊢
    rw [List.reverse_cons, List.isChain_append]
    refine ⟨hl, by simp, ?_⟩
    intro x hx y hy
    have hdy : d = y := by simpa using hy
    have hyd := hdy.symm
    subst y
    have hx' : x ∈ l.head? := by simpa only [List.getLast?_reverse] using hx
    exact hb x hx'
  have spikes_head (x : Nat) (q : List Nat) :
      x ∈ (spikes (x :: q)).head? := by
    cases q with
    | nil => simp [spikes]
    | cons k q => simp [spikes]
  have first_segment_bounded (i M : Nat) (s : List Nat)
      (hh : i ∈ s.head?)
      (hb : ∀ k ∈ s, i ≤ k ∧ k ≤ M) :
      ∀ d ∈ (segmentLengths s).head?, d ≤ M - i := by
    cases s with
    | nil => simp at hh
    | cons a s =>
      have hai : a = i := by simpa using hh
      subst a
      cases s with
      | nil => simp [segmentLengths]
      | cons b r =>
        have hbb := hb b (by simp)
        simp only [segmentLengths, List.head?_cons, Option.mem_some_iff]
        intro d hd
        subst d
        omega
  have segmentLengths_cons_spikes (M i : Nat) (q : List Nat)
      (hiM : i ≤ M) :
      segmentLengths (M :: spikes (i :: q)) =
        (M - i) :: segmentLengths (spikes (i :: q)) := by
    have hhead := List.cons_head?_tail (spikes_head i q)
    conv_lhs => arg 1; rw [← hhead]
    simp only [segmentLengths, Nat.sub_eq_zero_of_le hiM, add_zero]
    rw [hhead]
  have maximum_first_decreasing (n M : Nat) (a : List Nat)
      (hr : reducedWord n (M :: a)) (hc : consecutive (M :: a))
      (hb : ∀ k ∈ M :: a, k ≤ M) :
      weakIncreasing (segmentLengths (spikes (M :: a))).reverse := by
    have main : ∀ l, ∀ (n M : Nat) (a : List Nat), (M :: a).length = l →
        reducedWord n (M :: a) → consecutive (M :: a) →
        (∀ k ∈ M :: a, k ≤ M) →
        weakIncreasing (segmentLengths (spikes (M :: a))).reverse := by
      intro l
      induction l using Nat.strong_induction_on with
      | h l ih =>
        intro n M a hlen hr hc hb
        obtain ⟨i, q, hi, hiM, hw, hq, _⟩ := maximum_peel n M a hr hc hb
        by_cases hiM' : i = M
        · have hqn : q = [] := by
            cases q with
            | nil => rfl
            | cons k q =>
              have hk := hq k (by simp)
              have hkM := hb k (by rw [hw]; simp)
              omega
          have hw' : M :: a = [M] := by simpa [hiM', hqn, descending] using hw
          simp [hw', spikes, segmentLengths, weakIncreasing]
        · have hiMlt : i < M := by omega
          have hsplit : descending M i = descending M (i + 1) ++ [i] := by
            unfold descending
            have hlen : M - i + 1 = (M - (i + 1) + 1) + 1 := by omega
            rw [hlen, List.range_succ, List.map_append]
            simp only [List.map_singleton]
            congr 1
            simp only [List.cons.injEq, and_true]
            omega
          have hws : M :: a = descending M (i + 1) ++ (i :: q) := by
            rw [hw, hsplit, List.append_assoc]
            rfl
          have hrs := suffix_reduced n (descending M (i + 1)) (i :: q) (hws ▸ hr)
          have hcs : consecutive (i :: q) := (chain _).mpr
            (((chain _).mp (hws ▸ hc)).right_of_append)
          have hsM : ∀ k ∈ i :: q, k ≤ M := by
            intro k hk
            exact hb k (by rw [hws]; simp [hk])
          have hsi : ∀ k ∈ i :: q, i ≤ k := by
            intro k hk
            rcases List.mem_cons.mp hk with rfl | hk
            · omega
            · have := hq k hk; omega
          have hshort : (i :: q).length < l := by
            rw [← hlen, hws, List.length_append]
            have hpositive : 0 < (descending M (i + 1)).length := by
              simp [descending]
            omega
          have hb' : ∀ k ∈ (i :: q).map (n + 1 - ·), k ≤ n + 1 - i := by
            intro k hk
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk
            exact Nat.sub_le_sub_left (hsi t ht) (n + 1)
          have hdec := ih ((i :: q).map (n + 1 - ·)).length (by simpa using hshort)
            n (n + 1 - i) (q.map (n + 1 - ·)) (by simp)
            (reflect_reduced n (i :: q) hrs)
            (reflect_consecutive n (i :: q) hrs.1 hcs) hb'
          have hreflect : segmentLengths (spikes ((i :: q).map (n + 1 - ·))) =
              segmentLengths (spikes (i :: q)) := by
            rw [reflect_spikes n (i :: q) hrs.1, reflect_segmentLengths n (i :: q) hrs.1]
          simp only [List.map_cons] at hreflect
          rw [hreflect] at hdec
          rw [hw, spikes_descent M i q hiMlt hq,
            segmentLengths_cons_spikes M i q hiM]
          apply weakIncreasing_rev_cons (M - i) _ hdec
          apply first_segment_bounded i M _ (spikes_head i q)
          intro k hk
          have hks := spikes_mem (i :: q) k hk
          exact ⟨hsi k hks, hsM k hks⟩
    exact main (M :: a).length n M a rfl hr hc hb
  have first (v : List Nat) (hv : reducedWord n v) (hcv : consecutive v)
      (hh : v.head? = some k)
      (hb : (∀ t ∈ v, t ≤ k) ∨ (∀ t ∈ v, k ≤ t)) : oscillation v := by
    cases v with
    | nil => simp at hh
    | cons x v =>
      have hx : x = k := by simpa using hh
      subst x
      rcases hb with hb | hb
      · exact Or.inr (maximum_first_decreasing n k v hv hcv hb)
      · have hbr : ∀ t ∈ (k :: v).map (n + 1 - ·), t ≤ n + 1 - k := by
          intro t ht
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
          exact Nat.sub_le_sub_left (hb s hs) (n + 1)
        have hdec := maximum_first_decreasing n (n + 1 - k) (v.map (n + 1 - ·))
          (reflect_reduced n (k :: v) hv)
          (reflect_consecutive n (k :: v) hv.1 hcv) hbr
        have he : segmentLengths (spikes ((k :: v).map (n + 1 - ·))) =
            segmentLengths (spikes (k :: v)) := by
          rw [reflect_spikes n (k :: v) hv.1, reflect_segmentLengths n (k :: v) hv.1]
        simp only [List.map_cons] at he
        rw [he] at hdec
        exact Or.inr hdec
  rcases hend with hh | hl
  · exact first w hr hc hh hext
  · have hrev := first w.reverse (rev_reduced n w hr) (rev_chain w hc)
      (by simpa only [List.head?_reverse] using hl) (by simpa using hext)
    unfold oscillation at hrev ⊢
    rw [reverse_spikes, reverse_segmentLengths] at hrev
    simpa only [List.reverse_reverse, or_comm] using hrev

theorem extremal_endpoint_unique (n k : Nat) (a b : List Nat)
    (ha : reducedWord n a) (hb : reducedWord n b)
    (hca : consecutive a) (hcb : consecutive b)
    (he : wordProduct n a = wordProduct n b)
    (hend : (a.head? = some k ∧ b.head? = some k) ∨
      (a.getLast? = some k ∧ b.getLast? = some k))
    (hext : (∀ t ∈ a, t ≤ k) ∧ (∀ t ∈ b, t ≤ k) ∨
      (∀ t ∈ a, k ≤ t) ∧ (∀ t ∈ b, k ≤ t)) : a = b := by
  have main : ∀ l, ∀ (n k : Nat) (a b : List Nat), a.length = l →
      reducedWord n a → reducedWord n b → consecutive a → consecutive b →
      wordProduct n a = wordProduct n b → a.head? = some k → b.head? = some k →
      ((∀ t ∈ a, t ≤ k) ∧ (∀ t ∈ b, t ≤ k) ∨
        (∀ t ∈ a, k ≤ t) ∧ (∀ t ∈ b, k ≤ t)) → a = b := by
    intro l
    induction l using Nat.strong_induction_on with
    | h l ih =>
      have max_case (n k : Nat) (a b : List Nat) (hlen : a.length = l)
          (ha : reducedWord n a) (hb : reducedWord n b)
          (hca : consecutive a) (hcb : consecutive b)
          (he : wordProduct n a = wordProduct n b)
          (hhead_a : a.head? = some k) (hhead_b : b.head? = some k)
          (hea : ∀ t ∈ a, t ≤ k) (heb : ∀ t ∈ b, t ≤ k) : a = b := by
        cases a with
        | nil => simp at hhead_a
        | cons x a =>
          have hx : x = k := by simpa using hhead_a
          subst x
          cases b with
          | nil => simp at hhead_b
          | cons x b =>
            have hx : x = k := by simpa using hhead_b
            subst x
            obtain ⟨i, q, hi, hik, haq, hq, hei⟩ := maximum_peel n k a ha hca hea
            obtain ⟨j, r, hj, hjk, hbr, hr, hej⟩ := maximum_peel n k b hb hcb heb
            have hn := (ha.1 k (by simp)).2
            have hpv (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
                (position n t).val = t - 1 := by
              simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
            have hij : i = j := by
              rw [he] at hei
              have := congrArg Fin.val ((wordProduct n (k :: b)).injective (hei.trans hej.symm))
              rw [hpv i ⟨hi, by omega⟩, hpv j ⟨hj, by omega⟩] at this
              omega
            subst j
            -- Cancel the common initial descent and compare the smaller tails.
            have heqr : wordProduct n q = wordProduct n r := by
              rw [haq, hbr] at he
              simpa only [wordProduct, List.map_append, List.prod_append,
                mul_left_cancel_iff] using he
            have haq_r := suffix_reduced n (descending k i) q (haq ▸ ha)
            have hbr_r := suffix_reduced n (descending k i) r (hbr ▸ hb)
            have hq_len : q.length < l := by
              have := congrArg List.length haq
              simp [descending] at this
              rw [← hlen]
              simp
              omega
            have hlenqr : q.length = r.length := by
              have h1 := haq_r.2 r hbr_r.1 heqr.symm
              have h2 := hbr_r.2 q haq_r.1 heqr
              omega
            have ends (v : List Nat) (hv : consecutive (descending k i ++ v))
                (hbv : ∀ t ∈ v, i < t) (hne : v ≠ []) : v.head? = some (i + 1) := by
              have split : descending k i =
                  (List.range (k - i)).map (k - ·) ++ [i] := by
                unfold descending
                rw [List.range_succ, List.map_append]
                simp only [List.map_singleton]
                congr 1
                simp only [List.cons.injEq, and_true]
                omega
              cases v with
              | nil => simp at hne
              | cons t v =>
                have hc' := (chain _).mp hv
                rw [split, List.append_assoc] at hc'
                have ht := hc'.right_of_append.rel
                have ht' := hbv t (by simp)
                have : t = i + 1 := by rcases ht with ht | ht <;> omega
                simp [this]
            have hqc : consecutive q := (chain q).mpr
              (((chain _).mp (haq ▸ hca)).right_of_append)
            have hrc : consecutive r := (chain r).mpr
              (((chain _).mp (hbr ▸ hcb)).right_of_append)
            have hqr : q = r := by
              by_cases hqn : q = []
              · have : r = [] := List.length_eq_zero_iff.mp (by rw [← hlenqr, hqn]; rfl)
                rw [hqn, this]
              · have hrn : r ≠ [] := by intro h; apply hqn
                                        exact List.length_eq_zero_iff.mp (by rw [hlenqr, h]; rfl)
                exact ih q.length hq_len n (i + 1) q r rfl haq_r hbr_r hqc hrc heqr
                  (ends q (haq ▸ hca) hq hqn) (ends r (hbr ▸ hcb) hr hrn)
                  (Or.inr ⟨fun t ht => by have := hq t ht; omega,
                    fun t ht => by have := hr t ht; omega⟩)
            rw [haq, hbr, hqr]
      intro n k a b hlen ha hb hca hcb he hhead_a hhead_b hext
      rcases hext with ⟨hea, heb⟩ | ⟨hea, heb⟩
      · exact max_case n k a b hlen ha hb hca hcb he hhead_a hhead_b hea heb
      · -- Reflection changes a minimal first letter into a maximal first letter.
        let f := fun t => n + 1 - t
        have hhead (w : List Nat) (hw : w.head? = some k) : (w.map f).head? = some (f k) := by
          cases w with
          | nil => simp at hw
          | cons t w =>
            have ht : t = k := by simpa using hw
            simp only [List.map_cons, List.head?_cons, ht]
        have bound (w : List Nat) (hw : ∀ t ∈ w, k ≤ t) : ∀ t ∈ w.map f, t ≤ f k := by
          intro t ht
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
          exact Nat.sub_le_sub_left (hw s hs) (n + 1)
        have he' : wordProduct n (a.map f) = wordProduct n (b.map f) := by
          rw [reflect_product n a ha.1, reflect_product n b hb.1, he]
        have heq := max_case n (f k) (a.map f) (b.map f) (by simpa using hlen)
          (reflect_reduced n a ha) (reflect_reduced n b hb)
          (reflect_consecutive n a ha.1 hca) (reflect_consecutive n b hb.1 hcb)
          he' (hhead a hhead_a) (hhead b hhead_b) (bound a hea) (bound b heb)
        have inv (w : List Nat) (hw : validWord n w) : (w.map f).map f = w := by
          rw [List.map_map]
          calc
            _ = w.map id := by
              apply List.map_congr_left
              intro t ht
              have := hw t ht
              dsimp [f]
              omega
            _ = w := List.map_id w
        simpa only [inv a ha.1, inv b hb.1] using congrArg (List.map f) heq
  rcases hend with ⟨hhead_a, hhead_b⟩ | ⟨hlast_a, hlast_b⟩
  · exact main a.length n k a b rfl ha hb hca hcb he hhead_a hhead_b hext
  · have hrevext : (∀ t ∈ a.reverse, t ≤ k) ∧ (∀ t ∈ b.reverse, t ≤ k) ∨
        (∀ t ∈ a.reverse, k ≤ t) ∧ (∀ t ∈ b.reverse, k ≤ t) := by
      simpa only [List.mem_reverse] using hext
    have hrev := main a.reverse.length n k a.reverse b.reverse rfl
      (rev_reduced n a ha) (rev_reduced n b hb) (rev_chain a hca) (rev_chain b hcb)
      (by rw [rev_product, rev_product, he])
      (by simpa only [List.head?_reverse] using hlast_a)
      (by simpa only [List.head?_reverse] using hlast_b) hrevext
    exact List.reverse_injective hrev

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
#print axioms extremal_endpoint_oscillation
#print axioms extremal_endpoint_unique
#print axioms symmetric_excursion_outer_empty

end D5.S1.Words.Permutations.MamedeEndpointUniqueness
