/- GID: D5/S1/Words/Permutations/MamedeCrossing
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeCrossing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Reduced adjacent-swap words exclude repeated pair crossings and guarded right steps. -/

import D5.S1.Words.Permutations.MamedeOrderChange
import D5.S1.Words.Permutations.MamedeGuardedWalk

namespace D5.S1.Words.Permutations.MamedeCrossing

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeOrderChange

theorem guarded_walk_endpoint (n i t : Nat) (x : Fin (n + 1)) (b : List Nat)
    (hi : 1 ≤ i ∧ i ≤ n + 1) (ht : 1 ≤ t ∧ t ≤ n + 1)
    (hix : i ≤ x.val + 1) (hx : position n t = x)
    (hb : reducedWord n b)
    (he : wordProduct n b (position n i) = x)
    (hguard : ∀ r : Fin (n + 1), r.val + 1 < i → (wordProduct n b r).val < x.val) :
    D5.S1.Words.Permutations.MamedeGuardedWalk.leftOnly t b ∧ D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t b = i := by
  have repeated_pair_conjugacy (n : Nat) (p u : List Nat) (k l : Nat)
      (ha : (wordProduct n (p ++ k :: u)) (position n l) =
        (wordProduct n p) (position n k))
      (hb : (wordProduct n (p ++ k :: u)) (position n (l + 1)) =
        (wordProduct n p) (position n (k + 1))) :
      adjacent n k * wordProduct n u = wordProduct n u * adjacent n l := by
    have adjacent_position (r s : Nat) :
        adjacent r s = Equiv.swap (position r s) (position r (s + 1)) := by
      simp [adjacent, position]
    let P := wordProduct n p
    let U := wordProduct n u
    have hA : (adjacent n k * U) (position n l) = position n k := by
      apply P.injective
      simpa [P, U, wordProduct, List.map_append, List.prod_append, wordProduct, Equiv.Perm.mul_apply, mul_assoc]
        using ha
    have hB : (adjacent n k * U) (position n (l + 1)) = position n (k + 1) := by
      apply P.injective
      simpa [P, U, wordProduct, List.map_append, List.prod_append, wordProduct, Equiv.Perm.mul_apply, mul_assoc]
        using hb
    have huA : U (position n l) = position n (k + 1) := by
      apply (adjacent n k).injective
      simpa [Equiv.Perm.mul_apply, adjacent_position] using hA
    have huB : U (position n (l + 1)) = position n k := by
      apply (adjacent n k).injective
      simpa [Equiv.Perm.mul_apply, adjacent_position] using hB
    rw [adjacent_position n k, adjacent_position n l]
    rw [Equiv.mul_swap_eq_swap_mul U]
    rw [huA, huB, Equiv.swap_comm]

  have repeated_pair_conjugacy_reverse (n : Nat) (p u : List Nat) (k l : Nat)
      (ha : (wordProduct n (p ++ k :: u)) (position n l) =
        (wordProduct n p) (position n (k + 1)))
      (hb : (wordProduct n (p ++ k :: u)) (position n (l + 1)) =
        (wordProduct n p) (position n k)) :
      adjacent n k * wordProduct n u = wordProduct n u * adjacent n l := by
    have adjacent_position (r s : Nat) :
        adjacent r s = Equiv.swap (position r s) (position r (s + 1)) := by
      simp [adjacent, position]
    let P := wordProduct n p
    let U := wordProduct n u
    have hA : (adjacent n k * U) (position n l) = position n (k + 1) := by
      apply P.injective
      simpa [P, U, wordProduct, List.map_append, List.prod_append, wordProduct, Equiv.Perm.mul_apply, mul_assoc]
        using ha
    have hB : (adjacent n k * U) (position n (l + 1)) = position n k := by
      apply P.injective
      simpa [P, U, wordProduct, List.map_append, List.prod_append, wordProduct, Equiv.Perm.mul_apply, mul_assoc]
        using hb
    have huA : U (position n l) = position n k := by
      apply (adjacent n k).injective
      simpa [Equiv.Perm.mul_apply, adjacent_position] using hA
    have huB : U (position n (l + 1)) = position n (k + 1) := by
      apply (adjacent n k).injective
      simpa [Equiv.Perm.mul_apply, adjacent_position] using hB
    rw [adjacent_position n k, adjacent_position n l]
    rw [Equiv.mul_swap_eq_swap_mul U]
    rw [huA, huB]

  have no_two_crossings (n : Nat) (p u q : List Nat) (k l : Nat)
      (x y : Fin (n + 1))
      (hr : reducedWord n (p ++ k :: (u ++ l :: q)))
      (hfirst : crossing (wordProduct n p) k x y)
      (hsecond : crossing (wordProduct n (p ++ k :: u)) l x y) : False := by
    have hp : adjacent n k * wordProduct n u = wordProduct n u * adjacent n l := by
      rcases hfirst with ⟨hAx, hBy⟩ | ⟨hAy, hBx⟩
      · rcases hsecond with ⟨hCx, hDy⟩ | ⟨hCy, hDx⟩
        · exact repeated_pair_conjugacy n p u k l
            (hCx.trans hAx.symm) (hDy.trans hBy.symm)
        · exact repeated_pair_conjugacy_reverse n p u k l
            (hCy.trans hBy.symm) (hDx.trans hAx.symm)
      · rcases hsecond with ⟨hCx, hDy⟩ | ⟨hCy, hDx⟩
        · exact repeated_pair_conjugacy_reverse n p u k l
            (hCx.trans hBx.symm) (hDy.trans hAy.symm)
        · exact repeated_pair_conjugacy n p u k l
            (hCy.trans hAy.symm) (hDx.trans hBx.symm)
    have hcancel : adjacent n k * wordProduct n u * adjacent n l = wordProduct n u := by
      rw [hp, mul_assoc]
      simp [adjacent]
    have heq : wordProduct n (p ++ k :: (u ++ l :: q)) = wordProduct n (p ++ u ++ q) := by
      simp only [wordProduct, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
      change wordProduct n p * (adjacent n k * (wordProduct n u *
        (adjacent n l * wordProduct n q))) =
          (wordProduct n p * wordProduct n u) * wordProduct n q
      calc
        _ = wordProduct n p * ((adjacent n k * wordProduct n u * adjacent n l) * wordProduct n q) := by group
        _ = _ := by rw [hcancel]; group
    have hv : validWord n (p ++ u ++ q) := by
      intro z hz
      apply hr.1 z
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      tauto
    have hmin := hr.2 (p ++ u ++ q) hv heq.symm
    simp only [List.length_append, List.length_cons] at hmin
    omega

  have initial_order_at_crossing (n : Nat) (p q : List Nat) (k : Nat)
      (x y : Fin (n + 1)) (hxy : x ≠ y)
      (hr : reducedWord n (p ++ k :: q))
      (hc : crossing (wordProduct n p) k x y) :
      before 1 x y = before (wordProduct n p) x y := by
    by_contra hne
    have hv : validWord n p := by
      intro l hl
      exact hr.1 l (by simp [hl])
    obtain ⟨r, l, u, hp, hcross⟩ :=
      order_change_has_crossing n 1 p hv x y hxy (by simpa using hne)
    have hw : p ++ k :: q = r ++ l :: (u ++ k :: q) := by
      rw [hp]
      simp [List.append_assoc]
    rw [hw] at hr
    have hsecond : crossing (wordProduct n (r ++ l :: u)) k x y := by
      simpa [hp] using hc
    exact no_two_crossings n r u q l k x y hr (by simpa using hcross) hsecond

  have final_order_at_crossing (n : Nat) (p q : List Nat) (k : Nat)
      (x y : Fin (n + 1)) (hxy : x ≠ y)
      (hr : reducedWord n (p ++ k :: q))
      (hc : crossing (wordProduct n p) k x y) :
      before (wordProduct n (p ++ [k])) x y =
        before (wordProduct n (p ++ k :: q)) x y := by
    by_contra hne
    have hv : validWord n q := by
      intro l hl
      exact hr.1 l (by simp [hl])
    let S := wordProduct n (p ++ [k])
    have hprod : wordProduct n (p ++ k :: q) = S * wordProduct n q := by
      simp [S, wordProduct, List.map_append, List.prod_append, wordProduct, mul_assoc]
    obtain ⟨u, l, t, hq, hcross⟩ :=
      order_change_has_crossing n S q hv x y hxy (by simpa [S, hprod] using hne)
    have hw : p ++ k :: q = p ++ k :: (u ++ l :: t) := by rw [hq]
    rw [hw] at hr
    have hsecond : crossing (wordProduct n (p ++ k :: u)) l x y := by
      simpa [S, wordProduct, List.map_append, List.prod_append, wordProduct, mul_assoc] using hcross
    exact no_two_crossings n p u t k l x y hr hc hsecond

  have guarded_no_right_step (n i : Nat) (x : Fin (n + 1)) (b : List Nat)
      (hi : 1 ≤ i) (hix : i ≤ x.val + 1)
      (hb : reducedWord n b)
      (he : wordProduct n b (position n i) = x)
      (hguard : ∀ r : Fin (n + 1), r.val + 1 < i → (wordProduct n b r).val < x.val)
      (p q : List Nat) (k : Nat) (hw : b = p ++ k :: q) :
      wordProduct n p (position n k) ≠ x := by
    have crossing_before_after (n k : Nat) (hk : 1 ≤ k ∧ k ≤ n)
        (σ : Equiv.Perm (Fin (n + 1))) (x y : Fin (n + 1))
        (hx : σ (position n k) = x) (hy : σ (position n (k + 1)) = y) :
        before σ x y ∧ ¬ before (σ * adjacent n k) x y := by
      have adjacent_position (r s : Nat) :
          adjacent r s = Equiv.swap (position r s) (position r (s + 1)) := by
        simp [adjacent, position]
      have hAv : (position n k).val = k - 1 := by
        simp [position, Nat.mod_eq_of_lt (show k - 1 < n + 1 by omega)]
      have hBv : (position n (k + 1)).val = k := by
        simp [position, Nat.mod_eq_of_lt (show k < n + 1 by omega)]
      have hpreX : σ⁻¹ x = position n k := by
        apply σ.injective
        simpa using hx.symm
      have hpreY : σ⁻¹ y = position n (k + 1) := by
        apply σ.injective
        simpa using hy.symm
      have hpostX : (σ * adjacent n k)⁻¹ x = position n (k + 1) := by
        simp [mul_inv_rev, Equiv.Perm.mul_apply, adjacent_position, hpreX]
      have hpostY : (σ * adjacent n k)⁻¹ y = position n k := by
        simp [mul_inv_rev, Equiv.Perm.mul_apply, adjacent_position, hpreY]
      constructor
      · change (σ⁻¹ x).val < (σ⁻¹ y).val
        rw [hpreX, hpreY, hAv, hBv]
        omega
      · change ¬ ((σ * adjacent n k)⁻¹ x).val < ((σ * adjacent n k)⁻¹ y).val
        rw [hpostX, hpostY, hAv, hBv]
        omega
    intro hright
    subst b
    let S := wordProduct n p
    let y := S (position n (k + 1))
    have hk : 1 ≤ k ∧ k ≤ n := hb.1 k (by simp)
    have hAv : (position n k).val = k - 1 := by
      simp [position, Nat.mod_eq_of_lt (show k - 1 < n + 1 by omega)]
    have hBv : (position n (k + 1)).val = k := by
      simp [position, Nat.mod_eq_of_lt (show k < n + 1 by omega)]
    have hxy : x ≠ y := by
      intro h
      have hab : position n k = position n (k + 1) :=
        S.injective (hright.trans h)
      have hv := congrArg Fin.val hab
      omega
    have hc : crossing S k x y := Or.inl ⟨hright, rfl⟩
    have hcross := crossing_before_after n k hk S x y hright rfl
    have hbeforeInitial : before 1 x y = before S x y :=
      initial_order_at_crossing n p q k x y hxy hb hc
    have hafterFinal : before (wordProduct n (p ++ [k])) x y =
        before (wordProduct n (p ++ k :: q)) x y :=
      final_order_at_crossing n p q k x y hxy hb hc
    by_cases hyx : y.val < x.val
    · have hnotInit : ¬ before 1 x y := by simp [before]; omega
      rw [hbeforeInitial] at hnotInit
      exact hnotInit hcross.1
    · have hxyval : x.val < y.val := by
        have hne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
        omega
      have hpost : ¬ before (wordProduct n (p ++ [k])) x y := by
        simpa [S, wordProduct, List.map_append, List.prod_append, wordProduct, mul_assoc] using hcross.2
      have hfinal : ¬ before (wordProduct n (p ++ k :: q)) x y := by
        rw [← hafterFinal]
        exact hpost
      have hpos : (wordProduct n (p ++ k :: q))⁻¹ x = position n i := by
        apply (wordProduct n (p ++ k :: q)).injective
        simpa using he.symm
      have hival : (position n i).val = i - 1 := by
        have hin : i ≤ n + 1 := by have := x.isLt; omega
        simp [position, Nat.mod_eq_of_lt (show i - 1 < n + 1 by omega)]
      let r : Fin (n + 1) := (wordProduct n (p ++ k :: q))⁻¹ y
      have hrne : r ≠ position n i := by
        intro h
        apply hxy
        have := congrArg (wordProduct n (p ++ k :: q)) h
        simpa [r, he] using this.symm
      have hrlt : r.val + 1 < i := by
        have hv : r.val ≠ (position n i).val := fun h => hrne (Fin.ext h)
        have hno : ¬ (position n i).val < r.val := by
          simpa [before, r, hpos] using hfinal
        omega
      have hgy : y.val < x.val := by
        simpa [r] using hguard r hrlt
      omega

  have guarded_trace (n i : Nat) (x : Fin (n + 1)) (b : List Nat)
      (hi : 1 ≤ i) (hix : i ≤ x.val + 1)
      (hb : reducedWord n b)
      (he : wordProduct n b (position n i) = x)
      (hguard : ∀ r : Fin (n + 1), r.val + 1 < i → (wordProduct n b r).val < x.val)
      (p w : List Nat) (hpw : b = p ++ w) (t : Nat)
      (ht : 1 ≤ t ∧ t ≤ n + 1)
      (hcurrent : wordProduct n p (position n t) = x) :
      D5.S1.Words.Permutations.MamedeGuardedWalk.leftOnly t w ∧
        1 ≤ D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t w ∧
        D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t w ≤ n + 1 ∧
        wordProduct n b (position n (D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t w)) = x := by
    have left_trace_step (n t k : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1)
        (hk : 1 ≤ k ∧ k ≤ n) (hne : k ≠ t)
        (S : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1))
        (hx : S (position n t) = x) :
        1 ≤ D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t k ∧ D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t k ≤ n + 1 ∧
          (S * adjacent n k) (position n (D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t k)) = x := by
      have adjacent_position (r s : Nat) :
          adjacent r s = Equiv.swap (position r s) (position r (s + 1)) := by
        simp [adjacent, position]
      have htv : (position n t).val = t - 1 := by
        simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
      have hAv : (position n k).val = k - 1 := by
        simp [position, Nat.mod_eq_of_lt (show k - 1 < n + 1 by omega)]
      have hBv : (position n (k + 1)).val = k := by
        simp [position, Nat.mod_eq_of_lt (show k < n + 1 by omega)]
      by_cases hleft : k + 1 = t
      · have hs : D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t k = k := by simp [D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep, hleft]
        refine ⟨by rw [hs]; omega, by rw [hs]; omega, ?_⟩
        rw [hs, Equiv.Perm.mul_apply, adjacent_position, Equiv.swap_apply_left]
        simpa [hleft] using hx
      · have hs : D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t k = t := by simp [D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep, hleft]
        have hneA : position n t ≠ position n k := by
          intro heq
          have hv := congrArg Fin.val heq
          omega
        have hneB : position n t ≠ position n (k + 1) := by
          intro heq
          have hv := congrArg Fin.val heq
          omega
        refine ⟨by rw [hs]; exact ht.1, by rw [hs]; exact ht.2, ?_⟩
        rw [hs, Equiv.Perm.mul_apply, adjacent_position,
          Equiv.swap_apply_of_ne_of_ne hneA hneB]
        exact hx
    induction w generalizing p t with
    | nil =>
      have hbp : b = p := by simpa using hpw
      refine ⟨trivial, ?_, ?_, ?_⟩
      · simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd] using ht.1
      · simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd] using ht.2
      · simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd, hbp] using hcurrent
    | cons k w ih =>
      have hne : k ≠ t := by
        intro hkt
        have hn := guarded_no_right_step n i x b hi hix hb he hguard p w k hpw
        exact hn (hkt ▸ hcurrent)
      have hk : 1 ≤ k ∧ k ≤ n := by
        apply hb.1 k
        rw [hpw]
        simp
      obtain ⟨ht'1, ht'2, hstate⟩ :=
        left_trace_step n t k ht hk hne (wordProduct n p) x hcurrent
      have hcurrent' : wordProduct n (p ++ [k])
          (position n (D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t k)) = x := by
        simpa [wordProduct, List.map_append, List.prod_append, wordProduct] using hstate
      have hpw' : b = (p ++ [k]) ++ w := by
        rw [hpw]
        simp [List.append_assoc]
      obtain ⟨hleft, hlo, hhi, hend⟩ :=
        ih (p ++ [k]) hpw' (D5.S1.Words.Permutations.MamedeGuardedWalk.leftStep t k) ⟨ht'1, ht'2⟩ hcurrent'
      exact ⟨by simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.leftOnly] using And.intro hne hleft,
        by simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd] using hlo,
        by simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd] using hhi,
        by simpa [D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd] using hend⟩

  have hcurrent : wordProduct n [] (position n t) = x := by simpa [wordProduct] using hx
  obtain ⟨hleft, hlo, hhi, hend⟩ :=
    guarded_trace n i x b hi.1 hix hb he hguard [] b (by simp) t ht hcurrent
  have hpos : position n (D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t b) = position n i := by
    apply (wordProduct n b).injective
    exact hend.trans he.symm
  have hval := congrArg Fin.val hpos
  have htrace : (position n (D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t b)).val =
      D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t b - 1 := by
    simp [position, Nat.mod_eq_of_lt
      (show D5.S1.Words.Permutations.MamedeGuardedWalk.traceEnd t b - 1 < n + 1 by omega)]
  have hival : (position n i).val = i - 1 := by
    simp [position, Nat.mod_eq_of_lt (show i - 1 < n + 1 by omega)]
  exact ⟨hleft, by omega⟩

end D5.S1.Words.Permutations.MamedeCrossing
