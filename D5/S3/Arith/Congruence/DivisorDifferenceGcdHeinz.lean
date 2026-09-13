/- GID: D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/DivisorDifferenceGcdHeinz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.PrimeCounting]
   utility: none
   digest: Wiseman's A258409 gcd identity for divisors, consecutive gaps, and Heinz decoding. -/

import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz

private noncomputable def divisorList (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

noncomputable def consecutiveDivisorDifferences (n : ℕ) : List ℕ :=
  (divisorList n).zipWith (fun x y => y - x) (divisorList n).tail

def a (n : ℕ) : ℕ := n.divisors.gcd (fun d => d - 1)

noncomputable def consecutiveDifferenceGcd (n : ℕ) : ℕ :=
  (consecutiveDivisorDifferences n).toFinset.gcd id

noncomputable def heinzDifferences (n : ℕ) : ℕ :=
  ((consecutiveDivisorDifferences n).map (fun d => Nat.nth Nat.Prime (d - 1))).prod

noncomputable def primeIndexGcd (m : ℕ) : ℕ := m.primeFactors.gcd Nat.primeCounting

private theorem dvd_sub_base_of_dvd_gaps (a : ℕ) :
    ∀ (rest : List ℕ), (a :: rest).Pairwise (· ≤ ·) → ∀ k : ℕ,
      (∀ d ∈ (a :: rest).zipWith (fun x y => y - x) (a :: rest).tail, k ∣ d) →
        ∀ x ∈ a :: rest, k ∣ x - a := by
  intro rest
  revert a
  induction rest with
  | nil =>
      intro a _ k hg x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      simp
  | cons b bs ih =>
      intro a hs k hg x hx
      have hab : a ≤ b := (List.pairwise_cons.mp hs).1 b (by simp)
      have hgap : k ∣ b - a := by
        apply hg
        simp
      have htail : (b :: bs).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hs).2
      have hgap_tail : ∀ d ∈ (b :: bs).zipWith (fun x y => y - x) (b :: bs).tail, k ∣ d := by
        intro d hd
        apply hg
        simp only [List.zipWith, List.tail, List.mem_cons]
        exact Or.inr hd
      have ih' := ih b htail k hgap_tail
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · subst x
        simp
      · have hx' : x ∈ b :: bs := by simpa [hx]
        have hxb : k ∣ x - b := ih' x hx'
        have hbx : b ≤ x := by
          have hx'' : x = b ∨ x ∈ bs := by simpa only [List.mem_cons] using hx'
          rcases hx'' with rfl | hx''
          · exact le_rfl
          · exact (List.pairwise_cons.mp htail).1 x hx''
        rw [← Nat.sub_add_sub_cancel hbx hab]
        exact Nat.dvd_add hxb hgap

private theorem dvd_gaps_of_dvd_sub_base :
    ∀ (a : ℕ) (l : List ℕ) (k : ℕ),
      l.Pairwise (· ≤ ·) →
      (∀ x ∈ l, a ≤ x) →
      (∀ x ∈ l, k ∣ x - a) →
        ∀ d ∈ l.zipWith (fun x y => y - x) l.tail, k ∣ d := by
  intro a l
  induction l with
  | nil =>
      intro k _ _ _ d hd
      simp at hd
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro k _ _ _ d hd
          simp at hd
      | cons y ys =>
          intro k hs hbase hoff d hd
          have hax : a ≤ x := hbase x (by simp)
          have hxy : x ≤ y := (List.pairwise_cons.mp hs).1 y (by simp)
          have hfirst0 : k ∣ (y - a) - (x - a) :=
            Nat.dvd_sub (hoff y (by simp)) (hoff x (by simp))
          have hfirst : k ∣ y - x := by
            have heq : (y - a) - (x - a) = y - x := by omega
            exact heq ▸ hfirst0
          have htail_dvd : ∀ e ∈ (y :: ys).zipWith (fun u v => v - u) (y :: ys).tail, k ∣ e :=
            ih k (List.pairwise_cons.mp hs).2 (by
              intro z hz
              exact hbase z (by simp [hz])) (by
              intro z hz
              exact hoff z (by simp [hz]))
          simp only [List.zipWith, List.tail, List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact hfirst
          · exact htail_dvd d hd

private theorem sorted_list_gcd_sub_one_eq_gaps
    (rest : List ℕ) (hs : (1 :: rest).Pairwise (· ≤ ·)) :
    (1 :: rest).toFinset.gcd (fun d => d - 1) =
      ((1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail).toFinset.gcd id := by
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro d hd
    have hd' : d ∈ (1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail := by
      simpa using hd
    have hoff : ∀ x ∈ 1 :: rest, (1 :: rest).toFinset.gcd (fun d => d - 1) ∣ x - 1 := by
      intro x hx
      exact Finset.gcd_dvd (by simpa using hx)
    have hbase : ∀ x ∈ 1 :: rest, 1 ≤ x := by
      intro x hx
      have hx' : x = 1 ∨ x ∈ rest := by simpa only [List.mem_cons] using hx
      rcases hx' with hx' | hx'
      · simpa [hx']
      · exact (List.pairwise_cons.mp hs).1 x hx'
    exact dvd_gaps_of_dvd_sub_base 1 (1 :: rest) _ hs hbase hoff d hd'
  · apply Finset.dvd_gcd
    intro d hd
    have hgap : ∀ e ∈ (1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail,
        ((1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail).toFinset.gcd id ∣ e := by
      intro e he
      exact Finset.gcd_dvd (by simpa using he)
    have hoff := dvd_sub_base_of_dvd_gaps 1 rest hs _ hgap
    exact hoff d (by simpa using hd)

private theorem positive_gaps :
    ∀ (l : List ℕ), l.Pairwise (· < ·) →
      ∀ d ∈ l.zipWith (fun x y => y - x) l.tail, 0 < d := by
  intro l
  induction l with
  | nil =>
      intro _ d hd
      simp at hd
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro _ d hd
          simp at hd
      | cons y ys =>
          intro hs d hd
          have hxy : x < y := (List.pairwise_cons.mp hs).1 y (by simp)
          have htail := ih (List.pairwise_cons.mp hs).2
          simp only [List.zipWith, List.tail, List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact Nat.sub_pos_of_lt hxy
          · exact htail d hd

private theorem primeFactors_map_prod_eq_image
    (f : ℕ → ℕ) : ∀ (l : List ℕ),
      (∀ x ∈ l, Nat.Prime (f x)) →
        ((l.map f).prod).primeFactors = l.toFinset.image f := by
  intro l
  induction l with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro hf
      have hfx : Nat.Prime (f x) := hf x (by simp)
      have htail : ∀ y ∈ xs, Nat.Prime (f y) := by
        intro y hy
        exact hf y (by simp [hy])
      have hprod0 : (xs.map f).prod ≠ 0 := by
        apply List.prod_ne_zero
        intro hz
        rcases List.mem_map.mp hz with ⟨y, hy, hfy⟩
        exact (htail y hy).ne_zero hfy
      rw [List.map_cons, List.prod_cons, Nat.primeFactors_mul hfx.ne_zero hprod0,
        hfx.primeFactors, ih htail]
      simp [Finset.image_insert]

theorem wiseman_a258409 : ∀ n, 2 ≤ n →
    a n = primeIndexGcd (heinzDifferences n) ∧
      a n = consecutiveDifferenceGcd n := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hperm : (divisorList n).toFinset = n.divisors := by
    simp [divisorList]
  have hsorted : (divisorList n).Pairwise (· ≤ ·) := by
    simp [divisorList]
  have h1mem : 1 ∈ divisorList n := by
    have : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
    have hfin : 1 ∈ (divisorList n).toFinset := by simpa [hperm] using this
    exact List.mem_toFinset.mp hfin
  have hhead : ∃ rest, divisorList n = 1 :: rest := by
    cases h : divisorList n with
    | nil =>
        have : 1 ∈ ([] : List ℕ) := by simpa [h] using h1mem
        simp at this
    | cons x xs =>
        refine ⟨xs, ?_⟩
        have hxmem : x ∈ n.divisors := by
          rw [← hperm]
          simpa [h]
        have h1list : 1 ∈ x :: xs := by simpa [h] using h1mem
        have hx1 : x = 1 := by
          by_cases hxeq : x = 1
          · exact hxeq
          · have h1xs : 1 ∈ xs := by
              have hor : 1 = x ∨ 1 ∈ xs := by simpa only [List.mem_cons] using h1list
              exact hor.resolve_left (fun h => hxeq h.symm)
            have hxle : x ≤ 1 :=
              (List.pairwise_cons.mp (by simpa [h] using hsorted)).1 1 h1xs
            have hxge : 1 ≤ x :=
              Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors hxmem))
            omega
        simpa [h, hx1]
  rcases hhead with ⟨rest, hrest⟩
  have hsrest : (1 :: rest).Pairwise (· ≤ ·) := by simpa [hrest] using hsorted
  have haeq : a n = (divisorList n).toFinset.gcd (fun d => d - 1) := by
    simp only [a]
    rw [hperm]
  have hconsec : a n = consecutiveDifferenceGcd n := by
    calc
      a n = (divisorList n).toFinset.gcd (fun d => d - 1) := haeq
      _ = ((1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail).toFinset.gcd id := by
        rw [hrest]
        exact sorted_list_gcd_sub_one_eq_gaps rest hsrest
      _ = consecutiveDifferenceGcd n := by
        simp [consecutiveDifferenceGcd, consecutiveDivisorDifferences, hrest]
  let gaps := (1 :: rest).zipWith (fun x y => y - x) (1 :: rest).tail
  have hstrict : (1 :: rest).Pairwise (· < ·) := by
    rw [← hrest]
    simpa [divisorList] using (Finset.sortedLT_sort (n.divisors : Finset ℕ)).pairwise
  have hgap_pos : ∀ d ∈ gaps, 0 < d := by
    intro d hd
    exact positive_gaps (1 :: rest) hstrict d (by simpa [gaps] using hd)
  have hsupport : (heinzDifferences n).primeFactors =
      gaps.toFinset.image (fun d => Nat.nth Nat.Prime (d - 1)) := by
    rw [heinzDifferences, consecutiveDivisorDifferences, hrest]
    apply primeFactors_map_prod_eq_image
    intro d hd
    exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (d - 1)
  have hindex : ∀ d ∈ gaps,
      Nat.primeCounting (Nat.nth Nat.Prime (d - 1)) = d := by
    intro d hd
    have hdpos : 0 < d := hgap_pos d hd
    have hnth : Nat.primeCounting (Nat.nth Nat.Prime (d - 1)) = (d - 1) + 1 := by
      simpa [Nat.primeCounting, Nat.primeCounting'] using
        Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime (d - 1)
    calc
      Nat.primeCounting (Nat.nth Nat.Prime (d - 1)) = (d - 1) + 1 := hnth
      _ = d := Nat.sub_add_cancel (by omega)
  have hprimeeq : primeIndexGcd (heinzDifferences n) = gaps.toFinset.gcd id := by
    rw [primeIndexGcd, hsupport, Finset.gcd_image]
    apply Finset.gcd_congr rfl
    intro d hd
    exact hindex d (by simpa [gaps] using hd)
  have hprime : a n = primeIndexGcd (heinzDifferences n) := by
    calc
      a n = (divisorList n).toFinset.gcd (fun d => d - 1) := haeq
      _ = gaps.toFinset.gcd id := by
        rw [hrest]
        exact sorted_list_gcd_sub_one_eq_gaps rest hsrest
      _ = primeIndexGcd (heinzDifferences n) := hprimeeq.symm
  exact ⟨hprime, hconsec⟩

end D5.S3.Arith.Congruence.DivisorDifferenceGcdHeinz
