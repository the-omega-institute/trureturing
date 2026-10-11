/- GID: D5/S3/Factorization/TwoDenseDivisorBlockMaximum
   generality: G
   mirror-B: D5/B/S3/Factorization/TwoDenseDivisorBlockMaximum
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The largest two-dense divisor block has ruler-scaled maximum odd count. -/

import D5.S3.Factorization.TwoDenseDivisorBlocksPalindrome
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Pairwise

namespace D5.S3.Factorization.TwoDenseDivisorBlockMaximum

/-- Odd counts in the same maximal blocks used by the existing divisor-length row. -/
def oddBlockCounts (n : ℕ) : List ℕ :=
  ((n.divisorsAntidiagonalList.map Prod.fst).splitBy
    (fun a b => decide (b ≤ 2 * a))).map
      (fun B => (B.filter (fun d => decide (Odd d))).length)

/-- OEIS A400194: the maximum block length is the ruler function times the
maximum odd count, with both maxima taken over the same actual blocks. -/
theorem result (n : ℕ) (hn : 0 < n) :
    (TwoDenseDivisorBlocksPalindrome.row n).toFinset.sup id =
      (n.factorization 2 + 1) * (oddBlockCounts n).toFinset.sup id := by
  classical
  let D := n.divisorsAntidiagonalList.map Prod.fst
  let P := D.splitBy (fun a b => decide (b ≤ 2 * a))
  let v := n.factorization 2
  have hmem (d : ℕ) : d ∈ D ↔ d ∣ n := by
    constructor
    · intro hd
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hd
      obtain ⟨hp, _⟩ := Nat.mem_divisorsAntidiagonalList.mp hp
      exact he ▸ ⟨p.2, hp.symm⟩
    · intro hd
      apply List.mem_map.mpr
      exact ⟨(d, n / d), Nat.mem_divisorsAntidiagonalList.mpr
        ⟨Nat.mul_div_cancel' hd, hn.ne'⟩, rfl⟩
  have hflat : P.flatten = D := List.flatten_splitBy _ _
  have hsort : P.flatten.Pairwise (· < ·) := by
    rw [hflat]
    exact Nat.sortedLT_map_fst_divisorsAntidiagonalList.pairwise
  have hne : [] ∉ P := List.nil_notMem_splitBy _ _
  have hboundary : P.IsChain (fun A C =>
      ∃ ha hc, 2 * A.getLast ha < C.head hc) := by
    apply (List.isChain_getLast_head_splitBy (fun a b => decide (b ≤ 2 * a)) D).imp
    intro A C h
    obtain ⟨ha, hc, h⟩ := h
    refine ⟨ha, hc, ?_⟩
    have hh : ¬ C.head hc ≤ 2 * A.getLast ha := of_decide_eq_false h
    omega
  -- A strict separating boundary prevents ratio-at-most-two endpoints from
  -- belonging to opposite sides, including all intervening entries.
  have connect : ∀ Q : List (List ℕ), Q.flatten.Pairwise (· < ·) → [] ∉ Q →
      Q.IsChain (fun A C => ∃ ha hc, 2 * A.getLast ha < C.head hc) →
      ∀ x ∈ Q.flatten, ∀ y ∈ Q.flatten, x ≤ 2 * y → y ≤ 2 * x →
      ∀ B ∈ Q, (x ∈ B ↔ y ∈ B) := by
    intro Q
    induction Q with
    | nil => simp
    | cons A T ih =>
      intro hs he hc x hx y hy hxy hyx B hB
      rw [List.flatten_cons] at hs
      obtain ⟨hsA, hsT, cross⟩ := List.pairwise_append.mp hs
      have gap : ∀ a ∈ A, ∀ c ∈ T.flatten, 2 * a < c := by
        intro a ha c hct
        cases T with
        | nil => simp at hct
        | cons C R =>
          obtain ⟨hneA, hneC, hcut⟩ := (List.isChain_cons_cons.mp hc).1
          have halast : a ≤ A.getLast hneA :=
            (hsA.imp (fun h => Nat.le_of_lt h)).rel_getLast ha
          have htc := List.pairwise_append.mp (show (C ++ R.flatten).Pairwise (· < ·) from hsT)
          have hhead : C.head hneC ≤ c := by
            rcases List.mem_append.mp hct with hct | hct
            · exact (htc.1.imp (fun h => Nat.le_of_lt h)).rel_head hct
            · exact Nat.le_of_lt (htc.2.2 _ (List.head_mem hneC) _ hct)
          omega
      have tailne : [] ∉ T := fun h => he (List.mem_cons_of_mem A h)
      have tailchain := hc.tail
      simp only [List.flatten_cons, List.mem_append] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rcases List.mem_cons.mp hB with hBA | hB
        · subst B
          exact iff_of_true hx hy
        · have notx : x ∉ B := by
            intro hb
            have := cross x hx x (List.mem_flatten.mpr ⟨B, hB, hb⟩)
            omega
          have noty : y ∉ B := by
            intro hb
            have := cross y hy y (List.mem_flatten.mpr ⟨B, hB, hb⟩)
            omega
          exact iff_of_false notx noty
      · have := gap x hx y hy
        omega
      · have := gap y hy x hx
        omega
      · rcases List.mem_cons.mp hB with hBA | hB
        · subst B
          have notx : x ∉ A := by
            intro ha
            have := cross x ha x hx
            omega
          have noty : y ∉ A := by
            intro ha
            have := cross y ha y hy
            omega
          exact iff_of_false notx noty
        · exact ih hsT tailne tailchain x hx y hy hxy hyx B hB
  have member_connect (x y : ℕ) (hx : x ∈ D) (hy : y ∈ D)
      (hxy : x ≤ 2 * y) (hyx : y ≤ 2 * x) (B : List ℕ) (hB : B ∈ P) :
      x ∈ B ↔ y ∈ B :=
    connect P hsort hne hboundary x (hflat.symm ▸ hx) y (hflat.symm ▸ hy) hxy hyx B hB
  have chain (u : ℕ) (hu : u ∣ n) (ho : ¬ 2 ∣ u) (B : List ℕ) (hB : B ∈ P) :
      ∀ j, j ≤ v → (2 ^ j * u ∈ B ↔ u ∈ B) := by
    have endpoint (j : ℕ) (hj : j ≤ v) : 2 ^ j * u ∈ D := by
      apply (hmem _).mpr
      have hu' := Nat.dvd_ordCompl_of_dvd_not_dvd hu ho
      have hpow : 2 ^ j ∣ 2 ^ v := pow_dvd_pow 2 hj
      have hprod := Nat.mul_dvd_mul hpow hu'
      rw [← Nat.ordProj_mul_ordCompl_eq_self n 2]
      exact hprod
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hj' : j ≤ v := by omega
      have heq : 2 ^ (j + 1) * u = 2 * (2 ^ j * u) := by
        rw [pow_succ]
        ac_rfl
      have hc := member_connect (2 ^ (j + 1) * u) (2 ^ j * u)
        (endpoint _ hj) (endpoint _ hj') (by omega) (by omega) B hB
      exact hc.trans (ih hj')
  have count (B : List ℕ) (hB : B ∈ P) :
      B.length = (v + 1) * (B.filter (fun d => decide (Odd d))).length := by
    have sub : List.Sublist B D := hflat ▸ List.sublist_flatten_of_mem hB
    have nodup : B.Nodup := sub.nodup Nat.sortedLT_map_fst_divisorsAntidiagonalList.nodup
    have divisor (d : ℕ) (hd : d ∈ B) : d ∣ n := (hmem _).mp (sub.subset hd)
    have nonzero (d : ℕ) (hd : d ∈ B) : d ≠ 0 := by
      intro hz
      have := divisor d hd
      rw [hz, zero_dvd_iff] at this
      omega
    have oddnot (u : ℕ) (ho : Odd u) : ¬ 2 ∣ u := by
      simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using ho
    let S := B.toFinset.filter (fun u => Odd u)
    let J := Finset.range (v + 1)
    have bij : (J ×ˢ S).card = B.toFinset.card := by
      apply Finset.card_bij (fun a _ => 2 ^ a.1 * a.2)
      · intro a ha
        obtain ⟨hj, hu⟩ := Finset.mem_product.mp ha
        obtain ⟨huB, ho⟩ := Finset.mem_filter.mp hu
        have huB' := List.mem_toFinset.mp huB
        exact List.mem_toFinset.mpr ((chain a.2 (divisor _ huB')
          (oddnot _ ho) B hB a.1 (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).mpr huB')
      · intro a ha b hb hab
        obtain ⟨_, hu⟩ := Finset.mem_product.mp ha
        obtain ⟨_, hw⟩ := Finset.mem_product.mp hb
        obtain ⟨huB, ho⟩ := Finset.mem_filter.mp hu
        obtain ⟨hwB, hwodd⟩ := Finset.mem_filter.mp hw
        have he : a.2 = b.2 := by
          have hh := congrArg (fun d => ordCompl[2] d) hab
          simpa only [Nat.ordCompl_pow_mul_of_not_dvd a.1 Nat.prime_two (oddnot _ ho),
            Nat.ordCompl_pow_mul_of_not_dvd b.1 Nat.prime_two (oddnot _ hwodd)] using hh
        have hp : 2 ^ a.1 = 2 ^ b.1 := by
          rw [← he] at hab
          exact mul_right_cancel₀ (nonzero _ (List.mem_toFinset.mp huB)) hab
        exact Prod.ext (Nat.pow_right_injective (by omega : 2 ≤ (2 : ℕ)) hp) he
      · intro d hd
        have hdB := List.mem_toFinset.mp hd
        have hd0 := nonzero d hdB
        let u := ordCompl[2] d
        have ho : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hd0
        have hudvd : u ∣ n := (Nat.ordCompl_dvd d 2).trans (divisor d hdB)
        have hj : d.factorization 2 ≤ v :=
          (Nat.factorization_le_iff_dvd hd0 hn.ne').mpr (divisor d hdB) 2
        have hdecomp : 2 ^ d.factorization 2 * u = d :=
          Nat.ordProj_mul_ordCompl_eq_self d 2
        have huB : u ∈ B :=
          (chain u hudvd ho B hB _ hj).mp (hdecomp.symm ▸ hdB)
        refine ⟨(d.factorization 2, u), Finset.mem_product.mpr ⟨?_, ?_⟩, hdecomp⟩
        · simpa [J] using (show d.factorization 2 < v + 1 by omega)
        · exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr huB,
            by simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using ho⟩
    change (Finset.range (v + 1) ×ˢ S).card = B.toFinset.card at bij
    rw [Finset.card_product, Finset.card_range] at bij
    have hS : S.card = (B.filter (fun d => decide (Odd d))).length := by
      rw [show S = (B.filter (fun d => decide (Odd d))).toFinset by
        simp [S, List.toFinset_filter]]
      exact List.toFinset_card_of_nodup (nodup.filter _)
    rw [hS, List.toFinset_card_of_nodup nodup] at bij
    exact bij.symm
  change (P.map List.length).toFinset.sup id =
    (v + 1) * (P.map (fun B => (B.filter (fun d => decide (Odd d))).length)).toFinset.sup id
  have mapset (f : List ℕ → ℕ) : (P.map f).toFinset = P.toFinset.image f := by
    ext d
    simp
  rw [mapset, mapset, Finset.sup_image, Finset.sup_image, Finset.mul_sup₀]
  apply Finset.sup_congr rfl
  intro B hB
  exact count B (List.mem_toFinset.mp hB)

#print axioms result

end D5.S3.Factorization.TwoDenseDivisorBlockMaximum
