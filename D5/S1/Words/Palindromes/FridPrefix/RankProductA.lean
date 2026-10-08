/- GID: D5/S1/Words/Palindromes/FridPrefix/RankProductA
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/RankProductA
   mirror-E: none(waiver:exact-finite-product-invariant)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result; instance=D5/S1/Words/Palindromes/FridPrefix/ProductPotentialsA.potentialDigitsA
   digest: A checked product potential bounds rank gain on every accepted endpoint path. -/

/-
proof_shape: content (a_endpoint_score_bound).
escape_witness: backward path induction through the pruned finite product potential.
admission_basis: escape-witness.
Direct frozen dependencies: none; remaining dependencies are pinned Mathlib or this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.ProductChecker
import D5.S1.Words.Palindromes.FridPrefix.RankA
import D5.S1.Words.Palindromes.FridPrefix.ProductDataA
import D5.S1.Words.Palindromes.FridPrefix.ProductPotentialsA
import D5.S1.Words.Palindromes.FridPrefix.ProductMovesA
import Mathlib.Tactic.FinCases

namespace D5.S1.Words.FridPrefix
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
/-- Every accepted paired chunk word has rank gain at most one. -/
theorem a_endpoint_score_bound
    (xs : List (ℕ × ℕ)) (ha : xs ∈ (chunkEndpoint 6).accepts) :
    chunkScore rankA (xs.map Prod.snd) ≤ chunkScore rankA (xs.map Prod.fst)+1 := by
  have checked_groups : ∀ q : Fin 17,
      groupCheck rankA movesA rawGroupsA coreMasksA potentialDigitsA q.val = true := by
    intro q
    fin_cases q <;> decide +kernel
  let U (q p s : ℕ) := potential potentialDigitsA q p s
  let delta (q x : ℕ) := (rankA.transitions.getD q #[]).getD x 0
  let weight (q x : ℕ) := (rankA.weights.getD q #[]).getD x 0
  let advance (s : ℕ × ℤ) (x : ℕ) := (delta s.1 x,s.2+weight s.1 x)
  let score (ys : List ℕ) (q : ℕ) := (ys.foldl advance (q,(0:ℤ))).2
  have row (q : Fin 17) (p s : ℕ) (hp : p < 99)
      (hr : rawMember rawGroupsA q.val p s = true) :
      (if isAccept q.val then coreMember coreMasksA q.val p s && decide (U q.val p s ≤ 1)
        else true) = true ∧
      (movesA[q.val]!).all (fun (x,y,t) =>
        let p1 := delta p x
        let s1 := delta s y
        rawMember rawGroupsA t p1 s1 && (if coreMember coreMasksA t p1 s1 then
          coreMember coreMasksA q.val p s &&
            decide (U q.val p s+weight s y-weight p x ≤ U t p1 s1) else true)) = true := by
    have hc := checked_groups q
    simp only [groupCheck,List.all_eq_true] at hc
    have hp' : p ∈ List.range rankA.transitions.size := List.mem_range.mpr hp
    have hs' : s ∈ (rawGroupsA.getD q.val #[]).getD p [] :=
      List.contains_iff_mem.mp hr
    have hh := hc p hp' s hs'
    simpa only [rowCheck,U,delta,weight,sub_eq_add_neg,add_assoc,Bool.and_eq_true] using hh
  have move_check : movesCheck 6 movesA = true := by decide +kernel
  have move_mem (q : Fin 17) (x y : ℕ) (t : Fin 17)
      (h : t ∈ (chunkEndpoint 6).step q (x,y)) : (x,y,t.val) ∈ movesA[q.val]! := by
    have hc := move_check
    simp only [movesCheck, Bool.and_eq_true, List.all_eq_true] at hc
    have hg := (hc.2 q.val (List.mem_range.mpr q.isLt)).1
    have hm := hg (x,y,t.val) h
    simpa only [Array.contains_iff_mem] using hm
  have delta_small : ∀ q : Fin 99, ∀ x : Fin 64,
      delta q.val x.val < 99 := by decide +kernel
  have row_length : ∀ q : Fin 99, (rankA.transitions.getD q.val #[]).size = 64 := by
    decide +kernel
  have next_small (p x : ℕ) (hp : p < 99) : delta p x < 99 := by
    by_cases hx : x < 64
    · exact delta_small ⟨p,hp⟩ ⟨x,hx⟩
    · have hl := row_length ⟨p,hp⟩
      change (rankA.transitions.getD p #[]).size = 64 at hl
      have hn : (rankA.transitions.getD p #[])[x]? = none :=
        Array.getElem?_eq_none (by omega)
      change (rankA.transitions.getD p #[]).getD x 0 < 99
      rw [Array.getD_eq_getD_getElem?, hn]
      exact Nat.zero_lt_succ 98
  have score_acc (ys : List ℕ) (q : ℕ) (z : ℤ) :
      (ys.foldl advance (q,z)).2 = z+score ys q := by
    induction ys generalizing q z with
    | nil => simp [score]
    | cons x ys ih =>
      change (ys.foldl advance (delta q x,z+weight q x)).2 =
        z+(ys.foldl advance (delta q x,0+weight q x)).2
      rw [ih, ih]
      omega
  have score_cons (x : ℕ) (ys : List ℕ) (q : ℕ) :
      score (x::ys) q = weight q x+score ys (delta q x) := by
    change (ys.foldl advance (delta q x,0+weight q x)).2 = _
    rw [score_acc]
    simp
  have path_bound {q t : Fin 17} {ys : List (ℕ × ℕ)}
      (path : (chunkEndpoint 6).Path q t ys) (ht : t ∈ endpoint.accept)
      (p s : ℕ) (hp : p < 99) (hs : s < 99)
      (hr : rawMember rawGroupsA q.val p s = true) :
      coreMember coreMasksA q.val p s = true ∧
        U q.val p s+score (ys.map Prod.snd) s-score (ys.map Prod.fst) p ≤ 1 := by
    induction path generalizing p s with
    | nil t =>
      have haccept : isAccept t.val = true := by
        apply decide_eq_true
        exact ht
      have hrow := (row t p s hp hr).1
      simp only [haccept, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hrow
      simpa only [List.map_nil, score, List.foldl_nil, Prod.snd, add_zero, sub_zero]
        using hrow
    | cons t q u a ys hm path ih =>
      have htmove := move_mem q a.1 a.2 t hm
      have hrow := (row q p s hp hr).2
      have hstep := (Array.all_eq_true_iff_forall_mem.mp hrow) (a.1,a.2,t.val) htmove
      dsimp only at hstep
      rw [Bool.and_eq_true] at hstep
      have hb := ih ht (delta p a.1) (delta s a.2)
        (next_small p a.1 hp) (next_small s a.2 hs) hstep.1
      rw [hb.1] at hstep
      simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hstep
      refine ⟨hstep.2.1, ?_⟩
      simp only [List.map_cons, score_cons]
      have hb' := hb.2
      have hc' := hstep.2.2
      omega
  obtain ⟨q,hq,t,ht,⟨path⟩⟩ := NFA.accepts_iff_exists_path.mp ha
  have hq0 : q=0 := Fin.ext hq
  subst q
  have hr : rawMember rawGroupsA 0 0 0 = true := by decide +kernel
  have hU : U 0 0 0=0 := by decide +kernel
  have hb := (path_bound path ht 0 0 (by decide) (by decide) hr).2
  simp only [Fin.val_zero,hU,zero_add] at hb
  change chunkScore rankA (xs.map Prod.snd)-chunkScore rankA (xs.map Prod.fst) ≤ 1 at hb
  omega

end D5.S1.Words.FridPrefix
