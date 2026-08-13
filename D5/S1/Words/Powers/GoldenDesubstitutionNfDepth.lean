/- GID: D5/S1/Words/Powers/GoldenDesubstitutionNfDepth
   generality: I
   mirror-B: D5/B/S1/Words/Powers/GoldenDesubstitutionNfDepth
   mirror-E: none(waiver:block-boundary-bookkeeping)
   anchors: []
   digest: The golden normal form is reached at exactly the uniform Zeckendorf downshift depth. -/

import D5.S1.Words.Powers.GoldenDesubstitutionDepth

namespace GoldenDesubstitutionNfDepth

open D5.S0.Conventions
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionNormalForm
open GoldenDesubstitutionZeckendorf

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

/-- The uniform digit downshift from a number to its golden desubstitution normal form. -/
def desubstitutionShift (n : Nat) : Nat :=
  (wdigits n).getLastD 2 - 2

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
              change List.IsChain (fun x y : Nat => y + 2 ≤ x)
                (2 :: b :: (bs ++ [0])) at hchain
              have hp := List.isChain_iff_pairwise.mp hchain
              have h2b := (List.pairwise_cons.mp hp).1 b (by simp)
              have htailPair := (List.pairwise_cons.mp hp).2
              have hb0 := (List.pairwise_cons.mp htailPair).1 0 (by simp)
              exfalso
              omega
        simp [hnil]

private theorem map_shift_injective {m : Nat} (hm : m ≠ 0) {a b : Nat}
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

private theorem closed_shift_spec (n : Nat) :
    (GoldenDesubstitutionDepth.desubstitutionClosed n ≠ 0 ∨
      desubstitutionShift n = 0) ∧
      wdigits n =
        (wdigits (GoldenDesubstitutionDepth.desubstitutionClosed n)).map
          (fun k => k + desubstitutionShift n) := by
  have hspec := NormalFormFunction.nf_spec desubStep desubStep_termination
    desubStep_localConfluence n
  have hpath : Relation.ReflTransGen desubStep n
      (GoldenDesubstitutionDepth.desubstitutionClosed n) := by
    rw [← GoldenDesubstitutionDepth.golden_desubstitution_nf_eq_wdigits_decode n]
    exact hspec.1
  have hirr : ¬ ∃ x, desubStep
      (GoldenDesubstitutionDepth.desubstitutionClosed n) x := by
    rw [← GoldenDesubstitutionDepth.golden_desubstitution_nf_eq_wdigits_decode n]
    intro h
    rcases h with ⟨x, hx⟩
    exact hspec.2 x hx
  have hterminal : GoldenDesubstitutionDepth.desubstitutionClosed n = 0 ∨
      goldenWord (GoldenDesubstitutionDepth.desubstitutionClosed n) = false :=
    (desubStep_irreducible_iff _).mp hirr
  rcases (golden_desubstitution_terminal_iff n
      (GoldenDesubstitutionDepth.desubstitutionClosed n)).mp ⟨hpath, hterminal⟩ with
    hzero | ⟨r, htwo, hdigits⟩
  · rcases hzero with ⟨rfl, hclosed⟩
    refine ⟨Or.inr ?_, ?_⟩
    · simp [desubstitutionShift, wdigits]
    · simp [hclosed, wdigits]
  · have hm : GoldenDesubstitutionDepth.desubstitutionClosed n ≠ 0 := by
      intro hm0
      rw [hm0, wdigits] at htwo
      simp at htwo
    have hdigits_m_ne_nil :
        wdigits (GoldenDesubstitutionDepth.desubstitutionClosed n) ≠ [] := by
      intro hnil
      apply hm
      rw [← decode_wdigits (GoldenDesubstitutionDepth.desubstitutionClosed n), hnil]
      simp
    have hlast_m :
        (wdigits (GoldenDesubstitutionDepth.desubstitutionClosed n)).getLastD 2 = 2 :=
      terminal_last_digit _
        (wdigits_isCanonical (GoldenDesubstitutionDepth.desubstitutionClosed n)) htwo
    have hlast_n : (wdigits n).getLastD 2 = 2 + r := by
      rw [hdigits]
      rw [map_getLastD (fun k : Nat => k + r)
        (wdigits (GoldenDesubstitutionDepth.desubstitutionClosed n)) 2 2
        hdigits_m_ne_nil]
      exact congrArg (fun z => z + r) hlast_m
    have hshift : desubstitutionShift n = r := by
      rw [desubstitutionShift, hlast_n]
      omega
    refine ⟨Or.inl hm, ?_⟩
    simpa [hshift] using hdigits

/-- A chain from a number to its chosen normal form has exactly the uniform digit-shift depth. -/
theorem golden_desubstitution_nf_exact_depth_iff (n r : Nat) :
    (∃ xs : List Nat, xs.length = r ∧ List.IsChain desubStep (n :: xs) ∧
      (n :: xs).getLast? = some
        (NormalFormFunction.nf desubStep desubStep_termination
          desubStep_localConfluence n)) ↔
      r = desubstitutionShift n := by
  rw [GoldenDesubstitutionDepth.golden_desubstitution_nf_eq_wdigits_decode n]
  rw [GoldenDesubstitutionDepth.golden_desubstitution_exact_length_iff]
  have hcanonical := closed_shift_spec n
  constructor
  · intro h
    by_cases hm : GoldenDesubstitutionDepth.desubstitutionClosed n = 0
    · have hr : r = 0 := h.1.resolve_left (by simpa using hm)
      have hshift : desubstitutionShift n = 0 :=
        hcanonical.1.resolve_left (by simpa using hm)
      exact hr.trans hshift.symm
    · exact map_shift_injective hm (h.2.symm.trans hcanonical.2)
  · intro hr
    subst r
    exact hcanonical

example :
    ∃ xs : List Nat, xs.length = 0 ∧ List.IsChain desubStep (0 :: xs) ∧
      (0 :: xs).getLast? = some
        (NormalFormFunction.nf desubStep desubStep_termination
          desubStep_localConfluence 0) := by
  apply (golden_desubstitution_nf_exact_depth_iff 0 0).2
  simp [desubstitutionShift, wdigits]

end GoldenDesubstitutionNfDepth
