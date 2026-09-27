/- GID: D5/S1/Words/Permutations/MamedeEndpointUniqueness
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeEndpointUniqueness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A common extremal endpoint determines a reduced consecutive word. -/

import D5.S1.Words.Permutations.MamedeCrossing
import Mathlib.Data.Fin.Rev

namespace D5.S1.Words.Permutations.MamedeEndpointUniqueness

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeCrossing
open D5.S1.Words.Permutations.MamedeGuardedWalk

theorem extremal_endpoint_unique (n k : Nat) (a b : List Nat)
    (ha : reducedWord n a) (hb : reducedWord n b)
    (hca : consecutive a) (hcb : consecutive b)
    (he : wordProduct n a = wordProduct n b)
    (hend : (a.head? = some k ∧ b.head? = some k) ∨
      (a.getLast? = some k ∧ b.getLast? = some k))
    (hext : (∀ t ∈ a, t ≤ k) ∧ (∀ t ∈ b, t ≤ k) ∨
      (∀ t ∈ a, k ≤ t) ∧ (∀ t ∈ b, k ≤ t)) : a = b := by
  have maximum_peel (n M : Nat) (a : List Nat)
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
  have reflect_product (n : Nat) (w : List Nat) (hv : validWord n w) :
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
  have reflect_reduced (n : Nat) (w : List Nat) (hr : reducedWord n w) :
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
  have reflect_consecutive (n : Nat) (w : List Nat)
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
  have chain (w : List Nat) :
      consecutive w ↔ w.IsChain (fun x y => x + 1 = y ∨ y + 1 = x) := by
    induction w with
    | nil => simp [consecutive]
    | cons x w ih => cases w <;> simp [consecutive, List.isChain_cons_cons, ih]
  have suffix_reduced (n : Nat) (p q : List Nat)
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
  · have rev_product (v : List Nat) :
        wordProduct n v.reverse = (wordProduct n v)⁻¹ := by
      simp only [wordProduct, List.map_reverse, List.prod_reverse_noncomm, List.map_map]
      congr 1
    have rev_reduced (v : List Nat) (hr : reducedWord n v) : reducedWord n v.reverse := by
      refine ⟨fun t ht => hr.1 t (List.mem_reverse.mp ht), ?_⟩
      intro w hw hew
      have hp : wordProduct n w.reverse = wordProduct n v := by
        rw [rev_product, hew, rev_product, inv_inv]
      simpa using hr.2 w.reverse (fun t ht => hw t (List.mem_reverse.mp ht)) hp
    have rev_chain (v : List Nat) (hc : consecutive v) : consecutive v.reverse := by
      rw [chain, List.isChain_reverse]
      exact (chain v).mp hc |>.imp (fun _ _ h => h.symm)
    have hrevext : (∀ t ∈ a.reverse, t ≤ k) ∧ (∀ t ∈ b.reverse, t ≤ k) ∨
        (∀ t ∈ a.reverse, k ≤ t) ∧ (∀ t ∈ b.reverse, k ≤ t) := by
      simpa only [List.mem_reverse] using hext
    have hrev := main a.reverse.length n k a.reverse b.reverse rfl
      (rev_reduced a ha) (rev_reduced b hb) (rev_chain a hca) (rev_chain b hcb)
      (by rw [rev_product, rev_product, he])
      (by simpa only [List.head?_reverse] using hlast_a)
      (by simpa only [List.head?_reverse] using hlast_b) hrevext
    exact List.reverse_injective hrev

#print axioms extremal_endpoint_unique

end D5.S1.Words.Permutations.MamedeEndpointUniqueness
