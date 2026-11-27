/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SupportModel
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/Data/Prefix00.prefix00_checked
   digest: Actual finite prime supports satisfy certified rank and budget interfaces. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.PrefixChecker
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Prime.Basic

/-! Prime support classes and complete certificate interfaces. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.Certificate

/-- Prime sources whose predecessors contain a given divisor. -/
def sources (Q : Finset ℕ) (r : ℕ) : Finset ℕ := Q.filter fun q => r ∣ q - 1

/-- Increasing enumeration of one finite prime source class. -/
def sourceList (Q : Finset ℕ) (r : ℕ) : List ℕ := (sources Q r).sort

/-- The actual finite budget counts non-Fermat primes only. -/
noncomputable def interesting (Q : Finset ℕ) : Finset ℕ := by
  classical
  exact Q.filter fun q => q ≠ 2 ∧ ¬∃ k : ℕ, q - 1 = 2 ^ k

/-- Sources for an odd modulus greater than one are non-Fermat. -/
theorem sources_subset_interesting {Q : Finset ℕ} {r : ℕ}
    (hr : 1 < r) (hro : Odd r) :
    sources Q r ⊆ interesting Q := by
  classical
  intro q hm
  obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hm
  apply Finset.mem_filter.mpr
  refine ⟨hm, ?_, ?_⟩
  · intro heq
    have hd1 : r ∣ 1 := by simpa [heq] using hd
    have := Nat.dvd_one.mp hd1
    omega
  · rintro ⟨k, hk⟩
    have heq : r = 1 := Nat.eq_one_of_dvd_coprimes
      (hro.coprime_two_right.pow_right k) dvd_rfl (hk ▸ hd)
    omega

/-- The non-Fermat budget bounds every source class for an odd modulus greater than one. -/
theorem sources_card_le {Q : Finset ℕ} {r T : ℕ}
    (hr : 1 < r) (hro : Odd r)
    (hbudget : (interesting Q).card ≤ T) : (sources Q r).card ≤ T :=
  (Finset.card_le_card (sources_subset_interesting hr hro)).trans hbudget

/-- Odd predecessors divisible by an odd number occur in its even progression. -/
theorem progression_of_dvd {q r : ℕ} (hq : Odd q) (hr : Odd r)
    (hd : r ∣ q - 1) : ∃ k, q = 2 * r * k + 1 := by
  obtain ⟨j, hj⟩ := hq
  have hqj : q = 2 * j + 1 := by omega
  have hrj : r ∣ 2 * j := by simpa [hqj] using hd
  obtain ⟨k, hk⟩ := hr.coprime_two_right.dvd_mul_left.mp hrj
  refine ⟨k, ?_⟩
  rw [hqj, hk]
  ring

/-- A checked table bounds ranks of any admissible finite class of primes. -/
theorem PrefixCertificate.ranks_on {S : Finset ℕ} {c : PrefixCertificate}
    (hc : c.check = true) (hro : Odd c.r)
    (hp : ∀ q ∈ S, q.Prime)
    (hlen : S.card ≤ c.table.length)
    (hd : ∀ q ∈ S, c.r ∣ q - 1)
    (hf : ∀ q ∈ S, ∀ s ∈ c.forbidden, ¬s ∣ q - 1) :
    List.Forall₂ (· ≤ ·) (c.table.take S.sort.length) S.sort := by
  have hc' := hc
  simp only [PrefixCertificate.check, Bool.and_eq_true, decide_eq_true_eq] at hc'
  apply ranks_of_cover hc'.1.1.2 hc'.1.2 hc'.2 S.sortedLT_sort.pairwise
  · simpa using hlen
  · simpa only [Finset.mem_sort] using hp
  · simpa only [Finset.mem_sort] using hf
  · intro q hq
    have hq' := (Finset.mem_sort (· ≤ ·)).mp hq
    have hr2 : 2 ≤ c.r := by
      have hh := hc'.1.1.1
      simp only [checkPrefixes, Bool.and_eq_true, decide_eq_true_eq] at hh
      exact hh.1.1
    have hqodd : Odd q := (hp q hq').odd_of_ne_two (by
      intro heq
      have hd1 : c.r ∣ 1 := by simpa [heq] using hd q hq'
      have := Nat.dvd_one.mp hd1
      omega)
    exact progression_of_dvd hqodd hro (hd q hq')

/-- Every checked certificate has a rank interpretation on actual finite source classes. -/
theorem PrefixCertificate.source_ranks {Q : Finset ℕ} {c : PrefixCertificate}
    (hc : c.check = true) (hro : Odd c.r)
    (hp : ∀ q ∈ Q, q.Prime)
    (hlen : (sources Q c.r).card ≤ c.table.length)
    (hf : ∀ s ∈ c.forbidden, sources Q s = ∅) :
    List.Forall₂ (· ≤ ·) (c.table.take (sourceList Q c.r).length)
      (sourceList Q c.r) := by
  apply c.ranks_on hc hro
  · intro q hq
    exact hp q (Finset.mem_filter.mp hq).1
  · exact hlen
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro q hq s hs hd
    have hh : q ∈ sources Q s := Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hq).1, hd⟩
    simpa [hf s hs] using hh

/-- Earlier support exclusions make the corresponding complete certificate applicable. -/
theorem PrefixCertificate.excludes_sources {Q : Finset ℕ} {c : PrefixCertificate}
    (hc : c.check = true) (hro : Odd c.r)
    (hp : ∀ q ∈ Q, q.Prime)
    (hlen : (sources Q c.r).card ≤ c.table.length)
    (hf : ∀ s ∈ c.forbidden, sources Q s = ∅) :
    ¬geom c.r (sourceList Q c.r).length * lowerProduct (sourceList Q c.r) < 1 := by
  have hh := hc
  simp only [PrefixCertificate.check, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact exclude_of_prefix hh.1.1.1
    (c.source_ranks hc hro hp hlen hf)

/-- Sorting changes neither the deletion product nor the underlying finite set. -/
theorem lowerProduct_sort (S : Finset ℕ) :
    lowerProduct S.sort = ∏ q ∈ S, ((q : ℚ) - 1) / q := by
  unfold lowerProduct
  calc
    _ = (S.toList.map (fun q : ℕ => ((q : ℚ) - 1) / q)).prod :=
      List.Perm.prod_eq ((Finset.sort_perm_toList S (· ≤ ·)).map _)
    _ = _ := Finset.prod_map_toList _ _

/-- Disjoint finite source classes split the deletion product exactly. -/
theorem lowerProduct_split (A B : Finset ℕ) :
    lowerProduct (A \ B).sort * lowerProduct (A ∩ B).sort = lowerProduct A.sort := by
  rw [lowerProduct_sort, lowerProduct_sort, lowerProduct_sort,
    ← Finset.prod_union (Finset.disjoint_sdiff_inter A B), Finset.sdiff_union_inter]

/-- Ranked actual classes inherit the joint threshold exclusion. -/
theorem checkJoint_excludes_ranked {T : ℕ} {only5 only11 both : List ℕ}
    {thresholds : List (ℕ × ℕ)} {a b c : List ℕ}
    (hc : checkJoint T only5 only11 both thresholds = true)
    (h5 : ∀ q ∈ only5, 1 ≤ q) (h11 : ∀ q ∈ only11, 1 ≤ q)
    (hb : ∀ q ∈ both, 1 ≤ q)
    (hbudget : a.length + b.length + c.length ≤ T)
    (ha : List.Forall₂ (· ≤ ·) (only5.take a.length) a)
    (hb' : List.Forall₂ (· ≤ ·) (only11.take b.length) b)
    (hc' : List.Forall₂ (· ≤ ·) (both.take c.length) c) :
    ¬(geom 5 (a.length + c.length) * lowerProduct (a ++ c) < 1 ∧
      geom 11 (b.length + c.length) * lowerProduct (b ++ c) < 1) := by
  intro hbad
  have hmono5 := lowerProduct_mono (List.rel_append ha hc')
  have hmono11 := lowerProduct_mono (List.rel_append hb' hc')
  have hg (r k : ℕ) : 0 ≤ geom r k := by
    apply Finset.sum_nonneg
    intro i hi
    exact pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg r)) _
  exact checkJoint_sound hc h5 h11 hb hbudget
    ⟨(mul_le_mul_of_nonneg_left hmono5 (hg _ _)).trans_lt hbad.1,
      (mul_le_mul_of_nonneg_left hmono11 (hg _ _)).trans_lt hbad.2⟩

#print axioms sources_subset_interesting
#print axioms progression_of_dvd
#print axioms PrefixCertificate.source_ranks
#print axioms PrefixCertificate.excludes_sources
#print axioms lowerProduct_split

end D5.S3.Arith.MakowskiSchinzel.Certificate
