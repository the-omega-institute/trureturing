/- GID: D5/S1/Words/Permutations/MamedeFactorSeparation
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/MamedeFactorSeparation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Separated source factors determine a reduced consecutive word when j<i. -/

import D5.S1.Words.Permutations.MamedeEndpointUniqueness
import D5.S1.Words.Permutations.MamedeSourceAction

namespace D5.S1.Words.Permutations.MamedeFactorSeparation

open D5.S1.Words.Permutations.MamedeAdjacentWords
open D5.S1.Words.Permutations.MamedeEndpointUniqueness
open D5.S1.Words.Permutations.MamedeSourceAction

/-- The first-orientation shape is unique in an equal-product fiber when `j<i`.
    The shape of both words is a premise, independent of source extraction. -/
theorem source_shape_unique_of_j_lt_i (n m M i j : Nat) (a b p q r s : List Nat)
    (hm : 1 ≤ m) (hmj : m < j) (hji : j < i) (hiM : i < M) (hMn : M ≤ n)
    (ha : reducedWord n a) (hb : reducedWord n b)
    (hca : consecutive a) (hcb : consecutive b)
    (he : wordProduct n a = wordProduct n b)
    (hshape : sourceShape m M i j a p q)
    (hshape' : sourceShape m M i j b r s) : a = b := by
  have append_prod (u v : List Nat) :
      wordProduct n (u ++ v) = wordProduct n u * wordProduct n v := by
    simp [wordProduct]
  have pos_val (t : Nat) (ht : 1 ≤ t ∧ t ≤ n + 1) :
      (position n t).val = t - 1 := by
    simp [position, Nat.mod_eq_of_lt (show t - 1 < n + 1 by omega)]
  have fixed (w : List Nat) (hw : validWord n w) (x : Fin (n + 1))
      (hx : ∀ k ∈ w, x.val + 1 < k ∨ k + 1 < x.val + 1) :
      wordProduct n w x = x := by
    induction w with
    | nil => simp [wordProduct]
    | cons k w ih =>
      have hk := hw k (by simp)
      have hxx := hx k (by simp)
      have hn₁ : x ≠ position n k := by
        intro h; have := congrArg Fin.val h
        rw [pos_val k ⟨hk.1, by omega⟩] at this
        omega
      have hn₂ : x ≠ position n (k + 1) := by
        intro h; have := congrArg Fin.val h
        rw [pos_val (k + 1) ⟨by omega, by omega⟩] at this
        omega
      change (adjacent n k * wordProduct n w) x = x
      rw [Equiv.Perm.mul_apply, ih (fun l hl => hw l (by simp [hl]))
        (fun l hl => hx l (by simp [hl]))]
      simpa [adjacent, position] using Equiv.swap_apply_of_ne_of_ne hn₁ hn₂
  let C := wordProduct n (fullExcursion m M i j)
  -- The extra descent relates the full excursion to the existing three-cycle formula.
  let extra := (List.range (i - j - 1)).map (i - 1 - ·)
  have hsplit : descending (i - 1) m =
      extra ++ descending j m := by
    unfold descending
    dsimp [extra]
    rw [show i - 1 - m + 1 = (i - j - 1) + (j - m + 1) by omega,
      List.range_add, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    have := List.mem_range.mp hk
    simp only [Function.comp_apply]
    omega
  have hgamma : wordProduct n (deletedExcursion m M i) =
      wordProduct n extra * C := by
    simp [deletedExcursion, fullExcursion, hsplit, append_prod, C]
  have Cfix (x : Fin (n + 1))
      (hx : (m < x.val + 1 ∧ x.val + 1 ≤ j) ∨
        (i < x.val + 1 ∧ x.val + 1 ≤ M)) : C x = x := by
    have hpos : position n (x.val + 1) = x := by
      apply Fin.ext
      rw [pos_val (x.val + 1) ⟨by omega, x.isLt⟩]
      simp
    have hg : wordProduct n (deletedExcursion m M i) x = x := by
      have h := deletedExcursion_action n m M i (x.val + 1) hm (by omega) hiM hMn
        ⟨by omega, x.isLt⟩
      simpa only [if_neg (show x.val + 1 ≠ m by omega),
        if_neg (show x.val + 1 ≠ i by omega),
        if_neg (show x.val + 1 ≠ M + 1 by omega), hpos] using h
    have hextra : wordProduct n extra x = x := by
      apply fixed
      · intro k hk
        dsimp [extra] at hk
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk
        have := List.mem_range.mp ht
        omega
      · intro k hk
        dsimp [extra] at hk
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk
        have := List.mem_range.mp ht
        omega
    apply (wordProduct n extra).injective
    rw [← Equiv.Perm.mul_apply, ← hgamma, hg, hextra]
  have outside (lo hi : Nat) (hhi : hi ≤ n) (w : List Nat)
      (hw : ∀ k ∈ w, lo < k ∧ k < hi) (x : Fin (n + 1))
      (hx : ¬ (lo < x.val + 1 ∧ x.val + 1 ≤ hi)) : wordProduct n w x = x := by
    apply fixed
    · intro k hk; have := hw k hk; omega
    · intro k hk; have := hw k hk; omega
  have commute_C (lo hi : Nat) (hhi : hi ≤ n) (w : List Nat)
      (hw : ∀ k ∈ w, lo < k ∧ k < hi)
      (hregion : ∀ x : Fin (n + 1), lo < x.val + 1 ∧ x.val + 1 ≤ hi → C x = x) :
      C * wordProduct n w = wordProduct n w * C := by
    change Commute C (w.map (adjacent n)).prod
    apply Commute.list_prod_right
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    have h := hw k hk
    have h₁ := hregion (position n k) (by rw [pos_val k ⟨by omega, by omega⟩]; omega)
    have h₂ := hregion (position n (k + 1))
      (by rw [pos_val (k + 1) ⟨by omega, by omega⟩]; omega)
    have hs := Equiv.mul_swap_eq_swap_mul C (position n k) (position n (k + 1))
    rw [h₁, h₂] at hs
    simpa [Commute, SemiconjBy, adjacent, position] using hs
  have hqC := commute_C i M hMn q hshape.2.2 (fun x hx => Cfix x (Or.inr hx))
  have hsC := commute_C i M hMn s hshape'.2.2 (fun x hx => Cfix x (Or.inr hx))
  have htotal : wordProduct n p * wordProduct n q = wordProduct n r * wordProduct n s := by
    apply mul_right_cancel (b := C)
    have ht := he
    rw [hshape.1, hshape'.1] at ht
    simp only [append_prod] at ht
    change wordProduct n p * C * wordProduct n q =
      wordProduct n r * C * wordProduct n s at ht
    simpa only [mul_assoc, ← hqC, ← hsC] using ht
  have hp_r : wordProduct n p = wordProduct n r := by
    apply Equiv.ext
    intro x
    by_cases hx : m < x.val + 1 ∧ x.val + 1 ≤ j
    · have hqfix := outside i M hMn q hshape.2.2 x (by omega)
      have hsfix := outside i M hMn s hshape'.2.2 x (by omega)
      have ht := congrArg (fun z : Equiv.Perm (Fin (n + 1)) => z x) htotal
      simpa [Equiv.Perm.mul_apply, hqfix, hsfix] using ht
    · rw [outside m j (by omega) p hshape.2.1 x hx,
        outside m j (by omega) r hshape'.2.1 x hx]
  have hq_s : wordProduct n q = wordProduct n s := by
    rw [hp_r] at htotal
    exact mul_left_cancel htotal
  have chain (w : List Nat) :
      consecutive w ↔ w.IsChain (fun x y => x + 1 = y ∨ y + 1 = x) := by
    induction w with
    | nil => simp [consecutive]
    | cons x w ih => cases w <;> simp [consecutive, List.isChain_cons_cons, ih]
  have sub_reduced (u v w : List Nat) (hr : reducedWord n (u ++ v ++ w)) :
      reducedWord n v := by
    refine ⟨fun k hk => hr.1 k (by simp [hk]), ?_⟩
    intro z hz hez
    have hv : validWord n (u ++ z ++ w) := by
      intro k hk
      simp only [List.mem_append] at hk
      rcases hk with (hk | hk) | hk
      · exact hr.1 k (by simp [hk])
      · exact hz k hk
      · exact hr.1 k (by simp [hk])
    have hp : wordProduct n (u ++ z ++ w) = wordProduct n (u ++ v ++ w) := by
      simp only [append_prod, hez]
    have hmin := hr.2 (u ++ z ++ w) hv hp
    simp only [List.length_append] at hmin
    omega
  have hrp := sub_reduced [] p (fullExcursion m M i j ++ q)
    (by simpa only [List.nil_append, List.append_assoc] using
      (show reducedWord n (p ++ fullExcursion m M i j ++ q) from hshape.1 ▸ ha))
  have hrr := sub_reduced [] r (fullExcursion m M i j ++ s)
    (by simpa only [List.nil_append, List.append_assoc] using
      (show reducedWord n (r ++ fullExcursion m M i j ++ s) from hshape'.1 ▸ hb))
  have hrq := sub_reduced (p ++ fullExcursion m M i j) q []
    (by simpa [← hshape.1] using ha)
  have hrs := sub_reduced (r ++ fullExcursion m M i j) s []
    (by simpa [← hshape'.1] using hb)
  have ends : (fullExcursion m M i j).head? = some j ∧
      (fullExcursion m M i j).getLast? = some i := by
    have hd : descending j m ≠ [] := by simp [descending]
    have ht : descending (M - 1) i ≠ [] := by simp [descending]
    constructor
    · rw [fullExcursion, List.append_assoc, List.head?_append_of_ne_nil _ hd]
      simp [descending, List.head?_map, List.head?_range]
    · rw [fullExcursion, List.getLast?_append_of_ne_nil _ ht]
      simp [descending, List.getLast?_map, List.getLast?_range]
      omega
  have factors (v u z : List Nat) (hc : consecutive v)
      (hh : sourceShape m M i j v u z) :
      consecutive u ∧ consecutive z ∧
        (u ≠ [] → u.getLast? = some (j - 1)) ∧
        (z ≠ [] → z.head? = some (i + 1)) := by
    have hch := (chain v).mp hc
    rw [hh.1, List.append_assoc] at hch
    obtain ⟨hcu, hcrest, hboundu⟩ := List.isChain_append.mp hch
    obtain ⟨_, hcz, hboundz⟩ := List.isChain_append.mp hcrest
    refine ⟨(chain u).mpr hcu, (chain z).mpr hcz, ?_, ?_⟩
    · intro hne
      let k := u.getLast hne
      have hk : u.getLast? = some k := List.getLast?_eq_some_getLast hne
      have hmem := List.mem_of_getLast? hk
      have hlt := (hh.2.1 k hmem).2
      have hhead : (fullExcursion m M i j ++ z).head? = some j := by
        rw [List.head?_append_of_ne_nil _ (by intro h; have := ends.1; simp [h] at this)]
        exact ends.1
      have hrel := hboundu k (by simp [hk]) j (by simp [hhead])
      have hk' : k = j - 1 := by omega
      simpa [hk'] using hk
    · intro hne
      cases z with
      | nil => contradiction
      | cons k z =>
        have hgt := (hh.2.2 k (by simp)).1
        have hrel := hboundz i (by simp [ends.2]) k (by simp)
        have hk' : k = i + 1 := by omega
        simp [hk']
  obtain ⟨hcp, hcq, hp_end, hq_end⟩ := factors a p q hca hshape
  obtain ⟨hcr, hcs, hr_end, hs_end⟩ := factors b r s hcb hshape'
  have eq_words (u v : List Nat) (hu : reducedWord n u) (hv : reducedWord n v)
      (hcu : consecutive u) (hcv : consecutive v) (hprod : wordProduct n u = wordProduct n v)
      (k : Nat) (hend : u ≠ [] → v ≠ [] →
        (u.head? = some k ∧ v.head? = some k) ∨
        (u.getLast? = some k ∧ v.getLast? = some k))
      (hext : (∀ t ∈ u, t ≤ k) ∧ (∀ t ∈ v, t ≤ k) ∨
        (∀ t ∈ u, k ≤ t) ∧ (∀ t ∈ v, k ≤ t)) : u = v := by
    by_cases hune : u = []
    · subst u
      have hl := hv.2 [] (by simp [validWord]) hprod
      have hvnil : v = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      exact hvnil.symm
    by_cases hvne : v = []
    · subst v
      have hl := hu.2 [] (by simp [validWord]) hprod.symm
      exact List.length_eq_zero_iff.mp (by simpa using hl)
    exact extremal_endpoint_unique n k u v hu hv hcu hcv hprod (hend hune hvne) hext
  have hp : p = r := eq_words p r hrp hrr hcp hcr hp_r (j - 1)
    (fun hp hr => Or.inr ⟨hp_end hp, hr_end hr⟩)
    (Or.inl ⟨fun k hk => by have := hshape.2.1 k hk; omega,
      fun k hk => by have := hshape'.2.1 k hk; omega⟩)
  have hq : q = s := eq_words q s hrq hrs hcq hcs hq_s (i + 1)
    (fun hq hs => Or.inl ⟨hq_end hq, hs_end hs⟩)
    (Or.inr ⟨fun k hk => by have := hshape.2.2 k hk; omega,
      fun k hk => by have := hshape'.2.2 k hk; omega⟩)
  rw [hshape.1, hshape'.1, hp, hq]

#print axioms source_shape_unique_of_j_lt_i

end D5.S1.Words.Permutations.MamedeFactorSeparation
