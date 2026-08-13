/- GID: D5/S1/Words/Powers/GoldenDesubstitutionDepth
   generality: I
   mirror-B: D5/B/S1/Words/Powers/GoldenDesubstitutionDepth
   mirror-E: none(waiver:block-boundary-bookkeeping)
   anchors: []
   digest: Exact golden desubstitution depth is the uniform Zeckendorf shift, with a closed normal form. -/

import D5.S1.Words.Powers.GoldenDesubstitutionZeckendorf
import D5.S0.Rewriting.NormalFormFunction

namespace GoldenDesubstitutionDepth

open D5.S0.Conventions
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionNormalForm
open GoldenDesubstitutionZeckendorf

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem desubStep_wdigits' {x y : Nat} (h : desubStep x y) :
    wdigits x = (wdigits y).map (fun k => k + 1) := by
  rw [← h.2]
  exact golden_subst_start_wdigits y

private theorem chain_to_path {n m : Nat} {xs : List Nat}
    (hchain : List.IsChain desubStep (n :: xs))
    (hlast : (n :: xs).getLast? = some m) :
    Relation.ReflTransGen desubStep n m := by
  induction xs generalizing n m with
  | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst m
      exact .refl
  | cons y ys ih =>
      have hstep : desubStep n y := (List.isChain_cons_cons.mp hchain).1
      have htail : List.IsChain desubStep (y :: ys) :=
        (List.isChain_cons_cons.mp hchain).2
      have hlast' : (y :: ys).getLast? = some m := by
        simpa only [List.getLast?_cons_cons] using hlast
      exact .head hstep (ih htail hlast')

private theorem chain_digits {n m : Nat} {xs : List Nat}
    (hchain : List.IsChain desubStep (n :: xs))
    (hlast : (n :: xs).getLast? = some m) :
    wdigits n = (wdigits m).map (fun k => k + xs.length) := by
  induction xs generalizing n m with
  | nil =>
      simp only [List.length_nil, Nat.add_zero]
      have hnm : n = m := by
        simpa only [List.getLast?_singleton, Option.some.injEq] using hlast
      subst m
      simp
  | cons y ys ih =>
      have hstep : desubStep n y := (List.isChain_cons_cons.mp hchain).1
      have htail : List.IsChain desubStep (y :: ys) :=
        (List.isChain_cons_cons.mp hchain).2
      have hlast' : (y :: ys).getLast? = some m := by
        simpa only [List.getLast?_cons_cons] using hlast
      have hdigits := ih htail hlast'
      rw [desubStep_wdigits' hstep, hdigits, List.map_map]
      simp [Function.comp_def, Nat.add_assoc]

private theorem desubStep_target_ne_zero {x y : Nat} (h : desubStep x y) : y ≠ 0 := by
  intro hy
  subst y
  apply h.1
  simpa [goldenSubstStart_zero] using h.2.symm

private theorem chain_last_ne_zero {n m : Nat} {xs : List Nat}
    (hchain : List.IsChain desubStep (n :: xs))
    (hlast : (n :: xs).getLast? = some m) (hxs : xs ≠ []) : m ≠ 0 := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxs
  have hstep : desubStep n y := (List.isChain_cons_cons.mp hchain).1
  have htail : List.IsChain desubStep (y :: ys) :=
    (List.isChain_cons_cons.mp hchain).2
  have hlast' : (y :: ys).getLast? = some m := by
    simpa only [List.getLast?_cons_cons] using hlast
  by_cases hys : ys = []
  · subst ys
    have hym : y = m := by
      simpa only [List.getLast?_singleton, Option.some.injEq] using hlast'
    subst m
    exact desubStep_target_ne_zero hstep
  · exact chain_last_ne_zero htail hlast' hys

private def desubIter : Nat → Nat → Nat
  | 0, m => m
  | r + 1, m => goldenSubstStart (desubIter r m)

private def desubPathList (r m : Nat) : List Nat :=
  match r with
  | 0 => []
  | r + 1 => desubIter r m :: desubPathList r m

private theorem desubIter_ne_zero {m : Nat} (hm : m ≠ 0) :
    ∀ r, desubIter r m ≠ 0
  | 0 => hm
  | r + 1 => by
      have hprev := desubIter_ne_zero hm r
      rw [desubIter, goldenSubstStart]
      omega

private theorem desubPathList_length (r m : Nat) :
    (desubPathList r m).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [desubPathList, ih]

private theorem desubPathList_chain {m : Nat} (hm : m ≠ 0) : ∀ r,
    List.IsChain desubStep (desubIter r m :: desubPathList r m)
  | 0 => by simp [desubPathList, desubIter]
  | r + 1 => by
      change List.IsChain desubStep
        (desubIter (r + 1) m :: desubIter r m :: desubPathList r m)
      apply List.IsChain.cons_cons
      · constructor
        · exact desubIter_ne_zero hm (r + 1)
        · rfl
      · exact desubPathList_chain hm r

private theorem desubPathList_last {m : Nat} (hm : m ≠ 0) : ∀ r,
    (desubIter r m :: desubPathList r m).getLast? = some m
  | 0 => by
      rw [desubIter, desubPathList]
      simp
  | r + 1 => by
      rw [desubPathList, List.getLast?_cons_cons]
      exact desubPathList_last hm r

private theorem desubIter_wdigits (r m : Nat) :
    wdigits (desubIter r m) = (wdigits m).map (fun k => k + r) := by
  induction r with
  | zero => simp [desubIter]
  | succ r ih =>
      rw [desubIter, golden_subst_start_wdigits, ih, List.map_map]
      simp [Function.comp_def, Nat.add_assoc]

private theorem eq_of_wdigits_eq' {n m : Nat} (h : wdigits n = wdigits m) : n = m := by
  rw [← decode_wdigits n, ← decode_wdigits m, h]

private theorem map_shift_length_eq {m : Nat} (hm : m ≠ 0) {a b : Nat}
    (h : (wdigits m).map (fun k => k + a) =
      (wdigits m).map (fun k => k + b)) : a = b := by
  have hne : wdigits m ≠ [] := by
    intro hnil
    apply hm
    rw [← decode_wdigits m, hnil]
    simp
  cases hd : wdigits m with
  | nil => exact False.elim (hne hd)
  | cons k ks =>
      have hk : k + a = k + b := by
        simpa [hd] using congrArg List.head? h
      omega

/-- A desubstitution chain of `r` steps exists exactly for the indicated digit shift. -/
theorem golden_desubstitution_exact_length_iff (n m r : Nat) :
    (∃ xs : List Nat, xs.length = r ∧ List.IsChain desubStep (n :: xs) ∧
      (n :: xs).getLast? = some m) ↔
      (m ≠ 0 ∨ r = 0) ∧
        wdigits n = (wdigits m).map (fun k => k + r) := by
  constructor
  · rintro ⟨xs, hlen, hchain, hlast⟩
    refine ⟨?_, ?_⟩
    · by_cases hr : r = 0
      · exact Or.inr hr
      · left
        apply chain_last_ne_zero hchain hlast
        intro hxs
        apply hr
        simpa [hxs] using hlen.symm
    · simpa [hlen] using chain_digits hchain hlast
  · rintro ⟨hguard, hdigits⟩
    by_cases hr : r = 0
    · subst r
      have hnm : n = m := eq_of_wdigits_eq' (by simpa using hdigits)
      subst n
      exact ⟨[], rfl, List.IsChain.singleton _, by simp⟩
    · have hm : m ≠ 0 := hguard.resolve_right hr
      have hn : n = desubIter r m := by
        apply eq_of_wdigits_eq'
        exact hdigits.trans (desubIter_wdigits r m).symm
      subst n
      refine ⟨desubPathList r m, desubPathList_length r m,
        desubPathList_chain hm r, desubPathList_last hm r⟩

def desubstitutionShift (n : Nat) : Nat :=
  (wdigits n).getLastD 2 - 2

def desubstitutionClosed (n : Nat) : Nat :=
  ((wdigits n).map (fun k => k - desubstitutionShift n)).map Nat.fib |>.sum

private theorem closed_zero : desubstitutionClosed 0 = 0 := by
  simp [desubstitutionClosed, desubstitutionShift, wdigits]

private theorem getLastD_eq_of_ne_nil {α : Type*} {xs : List α}
    (hxs : xs ≠ []) (a b : α) : xs.getLastD a = xs.getLastD b := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
    List.getLast?_eq_getLast_of_ne_nil hxs]
  simp

private theorem map_getLastD {α β : Type*} (f : α → β) : ∀ (xs : List α) (a : α) (d : β),
    xs ≠ [] → (xs.map f).getLastD d = f (xs.getLastD a)
  | [], _, _, h => False.elim (h rfl)
  | x :: xs, a, d, _ => by
      cases xs with
      | nil => rfl
      | cons y ys =>
          cases ys with
          | nil => rfl
          | cons z zs =>
              simp only [List.map_cons]
              exact map_getLastD f (z :: zs) z (f a) (by simp)

private theorem terminal_last_digit (xs : List Nat)
    (hchain : List.IsChain (fun a b : Nat => b + 2 ≤ a) (xs ++ [0]))
    (hmem : 2 ∈ xs) : xs.getLastD 2 = 2 := by
  induction xs with
  | nil => simp at hmem
  | cons a xs ih =>
      change List.IsChain (fun x y : Nat => y + 2 ≤ x) (a :: xs ++ [0]) at hchain
      by_cases htail : 2 ∈ xs
      · calc
          (a :: xs).getLastD 2 = xs.getLastD a := List.getLastD_cons
          _ = xs.getLastD 2 := getLastD_eq_of_ne_nil (by
            intro h
            subst xs
            simp at htail) a 2
          _ = 2 := by
            cases xs with
            | nil => simp at htail
            | cons b bs =>
                exact ih (List.isChain_cons_cons.mp hchain).2 htail
      · have ha : a = 2 := by
          rcases (List.mem_cons.mp hmem) with h | h
          · exact h.symm
          · exact False.elim (htail h)
        subst a
        have hnil : xs = [] := by
          cases xs with
          | nil => rfl
          | cons b bs =>
              change List.IsChain (fun x y : Nat => y + 2 ≤ x) (2 :: b :: (bs ++ [0])) at hchain
              have hp := List.isChain_iff_pairwise.mp hchain
              have h2b := (List.pairwise_cons.mp hp).1 b (by simp)
              have htailPair := (List.pairwise_cons.mp hp).2
              have hb0 := (List.pairwise_cons.mp htailPair).1 0 (by simp)
              exfalso
              omega
        simp [hnil]

private theorem closed_of_terminal_digits {n m r : Nat}
    (hm : m ≠ 0) (htwo : 2 ∈ wdigits m)
    (hdigits : wdigits n = (wdigits m).map (fun k => k + r)) :
    desubstitutionClosed n = m := by
  have hdigits_m_ne_nil : wdigits m ≠ [] := by
    intro hnil
    apply hm
    rw [← decode_wdigits m, hnil]
    simp
  have hlast_m : (wdigits m).getLastD 2 = 2 := by
    exact terminal_last_digit (wdigits m) (wdigits_isCanonical m) htwo
  have hlast_n : (wdigits n).getLastD 2 = 2 + r := by
    rw [hdigits]
    rw [map_getLastD (fun k : Nat => k + r) (wdigits m) 2 2 hdigits_m_ne_nil]
    exact congrArg (fun z => z + r) hlast_m
  rw [desubstitutionClosed, desubstitutionShift, hlast_n, hdigits]
  simp only [List.map_map]
  change ((wdigits m).map (fun k => Nat.fib (k + r - (2 + r - 2)))).sum = m
  have hmap : (wdigits m).map
      (fun k => Nat.fib (k + r - (2 + r - 2))) = (wdigits m).map Nat.fib := by
    apply List.map_congr_left
    intro k hk
    congr 1
    omega
  rw [hmap]
  exact decode_wdigits m

/-- The normal-form function is the Fibonacci decoder of the uniformly downshifted digits. -/
theorem golden_desubstitution_nf_eq_wdigits_decode (n : Nat) :
    NormalFormFunction.nf desubStep desubStep_termination desubStep_localConfluence n =
      desubstitutionClosed n := by
  obtain ⟨m, hmprop, hmunique⟩ := golden_desubstitution_unique_terminal n
  have hspec := NormalFormFunction.nf_spec desubStep desubStep_termination
    desubStep_localConfluence n
  have hirr : ¬ ∃ x, desubStep
      (NormalFormFunction.nf desubStep desubStep_termination desubStep_localConfluence n) x := by
    intro h
    rcases h with ⟨x, hx⟩
    exact hspec.2 x hx
  have hnf_terminal :
      (NormalFormFunction.nf desubStep desubStep_termination desubStep_localConfluence n = 0) ∨
        goldenWord (NormalFormFunction.nf desubStep desubStep_termination
          desubStep_localConfluence n) = false :=
    (desubStep_irreducible_iff _).mp hirr
  have hnm : NormalFormFunction.nf desubStep desubStep_termination
      desubStep_localConfluence n = m :=
    hmunique _ ⟨hspec.1, hnf_terminal⟩
  rcases (golden_desubstitution_terminal_iff n m).mp hmprop with hzero | ⟨r, htwo, hdigits⟩
  · rcases hzero with ⟨rfl, rfl⟩
    simpa [hnm] using closed_zero.symm
  · have hclosed := closed_of_terminal_digits (by
      intro hm0
      rw [hm0, wdigits] at htwo
      simp at htwo)
      htwo hdigits
    exact hnm.trans hclosed.symm

example : ∃ xs : List Nat, xs.length = 1 ∧ List.IsChain desubStep (2 :: xs) ∧
    (2 :: xs).getLast? = some 1 := by
  refine ⟨[1], by simp, ?_, by simp⟩
  refine List.IsChain.cons_cons ⟨by decide, ?_⟩ (List.IsChain.singleton _)
  simpa [goldenSubstStart_zero] using
    (goldenSubstStart_step_true (i := 0) goldenWord_zero)

end GoldenDesubstitutionDepth
