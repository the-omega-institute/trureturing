/- GID: D5/S3/CharacterSums/SplitPrimeHostSeries
   generality: I
   mirror-B: D5/B/S3/CharacterSums/SplitPrimeHostSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both prime selections with simultaneous quadratic splitting have divergent logarithmic mass, past arbitrary independent cutoffs. -/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter ArithmeticFunction

namespace D5.S3.CharacterSums.SplitPrimeHostSeries

/-- Prime discriminant parameter subject to all the prescribed small splitting tests. -/
def splittingPrime (B d : ℕ) : Prop :=
  d.Prime ∧ d % 16 = 7 ∧ ∀ p ∈ Finset.range (B+1), p.Prime → p ≠ 2 → jacobiSym (-(d : ℤ)) p = 1

/-- The prime above a fixed discriminant parameter. -/
def companionPrime (d q : ℕ) : Prop := q.Prime ∧ q % 8 = 3 ∧ jacobiSym (-(d : ℤ)) q = 1

/-- The actual partial logarithmic prime mass in a support. -/
def mass (S : ℕ → Prop) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range X, Set.indicator (fun n => S n) (fun k : ℕ => Real.log k / k) n

private theorem weight_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) / n := by
  cases n with
  | zero => simp
  | succ k => exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_pos k)) (by positivity)

private theorem reduced_progression (m : ℕ) (hm : 0 < m) {S : ℕ → Prop}
    {a : ℕ} (ha : a.Coprime m) (hS : ∀ n, n.Prime → n ≡ a [MOD m] → S n) :
    Tendsto (mass S) atTop atTop ∧ ∀ N : ℕ, ∃ n > N, S n := by
  let inst : NeZero m := ⟨hm.ne'⟩
  have hu := (ZMod.isUnit_iff_coprime a m).2 ha
  have hnonneg (n : ℕ) : 0 ≤ Set.indicator (fun j => S j) (fun k : ℕ => Real.log k / k) n :=
    Set.indicator_apply_nonneg (fun _ => weight_nonneg n)
  refine ⟨(not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).1 ?_, fun N => ?_⟩
  · intro h
    apply vonMangoldt.not_summable_residueClass_prime_div hu
    apply Summable.of_nonneg_of_le (hf := h)
    · intro n
      split
      · exact div_nonneg (vonMangoldt.residueClass_nonneg (a : ZMod m) n) (Nat.cast_nonneg _)
      · simp
    · intro n
      classical
      by_cases hp : n.Prime
      · rw [ite_eq_left hp]
        by_cases hc : (n : ZMod m) = a
        · have hn := hS n hp ((ZMod.natCast_eq_natCast_iff ..).1 hc)
          rw [Set.indicator_of_mem (s := (fun j => S j)) hn]
          simp [vonMangoldt.residueClass, hc, vonMangoldt_apply_prime hp]
        · simpa [vonMangoldt.residueClass, hc] using hnonneg n
      · simpa [hp] using hnonneg n
  · obtain ⟨n, hn, hp, hc⟩ := Nat.forall_exists_prime_gt_and_modEq N hm.ne' ha
    exact ⟨n, hn, hS n hp hc⟩

private theorem select_crt {m k a b : ℕ} (h : m.Coprime k) (ha : a.Coprime m)
    (hb : b.Coprime k) :
    ∃ c : ℕ, c.Coprime (m*k) ∧ ∀ n, n ≡ c [MOD m*k] → n ≡ a [MOD m] ∧ n ≡ b [MOD k] := by
  let c := Nat.chineseRemainder h a b
  obtain ⟨hm, hk⟩ := c.property
  refine ⟨c, Nat.coprime_mul_iff_right.2 ⟨hm.gcd_eq.trans ha, hk.gcd_eq.trans hb⟩, fun n hn =>
    ⟨(hn.of_dvd (dvd_mul_right m k)).trans hm, (hn.of_dvd (dvd_mul_left k m)).trans hk⟩⟩

private theorem discriminants (B : ℕ) :
    Tendsto (mass (splittingPrime B)) atTop atTop ∧ ∀ N : ℕ, ∃ n > N, splittingPrime B n := by
  classical
  let F := (Finset.range (B+1)).filter (fun p => p.Prime ∧ p ≠ 2)
  let P := ∏ p ∈ F, p
  have hodd : Odd P := Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
    (fun p hp => ((Finset.mem_filter.mp hp).2.1).odd_of_ne_two (Finset.mem_filter.mp hp).2.2)
  have hpos : 0 < P := Nat.pos_of_ne_zero (fun h => by rw [h] at hodd; exact (by decide : ¬ Odd 0) hodd)
  obtain ⟨c,hc,hs⟩ := select_crt (m := 16) (k := P) (a := 7) (b := P-1)
    (by simpa using hodd.coprime_two_left.pow_left 4) (by decide)
    ((Nat.coprime_self_sub_left hpos).2 (Nat.coprime_one_left P))
  refine reduced_progression _ (by positivity) hc (fun n hn hnc => ?_)
  obtain ⟨h16,hP⟩ := hs n hnc
  refine ⟨hn, h16, fun p hp hpr ho => ?_⟩
  have hdiv : p ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hp,hpr,ho⟩)
  have he : (n : ℤ) ≡ (P : ℤ)-1 [ZMOD p] := by
    simpa [Nat.cast_sub (show 1 ≤ P from hpos)] using Int.natCast_modEq_iff.2 (hP.of_dvd hdiv)
  have hp0 : (P : ℤ) ≡ 0 [ZMOD p] := Int.modEq_zero_iff_dvd.2 (by exact_mod_cast hdiv)
  have hj : -(n : ℤ) ≡ 1 [ZMOD p] := by
    simpa using (he.trans (hp0.sub (Int.ModEq.refl 1))).neg
  rw [jacobiSym.mod_left' hj, jacobiSym.one_left]

private theorem companions {d : ℕ} (hd : d % 16 = 7) :
    Tendsto (mass (companionPrime d)) atTop atTop ∧ ∀ Q : ℕ, ∃ q > Q, companionPrime d q := by
  have hodd : Odd d := Nat.odd_iff.2 (by omega)
  obtain ⟨c,hc,hs⟩ := select_crt (m := 8) (k := d) (a := 3) (b := 1)
    (by simpa using hodd.coprime_two_left.pow_left 3) (by decide) (Nat.coprime_one_left d)
  have hdpos : 0 < d := by omega
  refine reduced_progression _ (Nat.mul_pos (by decide) hdpos) hc fun q hq hqc => ?_
  obtain ⟨h8,h1⟩ := hs q hqc
  have hq8 : q % 8 = 3 := h8
  have hd4 : d % 4 = 3 := by omega
  have hq4 : q % 4 = 3 := by omega
  have hsymbol : jacobiSym (q : ℤ) d = 1 := by
    have he : (q : ℤ) ≡ 1 [ZMOD d] := by simpa using Int.natCast_modEq_iff.2 h1
    rw [jacobiSym.mod_left' he, jacobiSym.one_left]
  refine ⟨hq,hq8,?_⟩
  rw [jacobiSym.neg _ (Nat.odd_iff.2 (by omega)), ZMod.χ₄_nat_three_mod_four hq4,
    jacobiSym.quadratic_reciprocity_three_mod_four hd4 hq4, hsymbol]
  norm_num

private theorem reverse_selection (B q : ℕ) (hp : q.Prime) (h8 : q % 8 = 3) :
    let S := fun d => splittingPrime B d ∧ companionPrime d q
    Tendsto (mass S) atTop atTop ∧ ∀ N : ℕ, ∃ d > N, S d := by
  dsimp only
  have incl (d : ℕ) (hd : splittingPrime (max B q) d) :
      splittingPrime B d ∧ companionPrime d q := by
    refine ⟨⟨hd.1, hd.2.1, fun p hm => hd.2.2 p (Finset.mem_range.mpr ?_)⟩,
      ⟨hp, h8, hd.2.2 q (Finset.mem_range.mpr (by omega)) hp (by omega)⟩⟩
    have := Finset.mem_range.mp hm
    omega
  obtain ⟨hlim, hlarge⟩ := discriminants (max B q)
  refine ⟨tendsto_atTop_mono (fun X => Finset.sum_le_sum (fun n _ => ?_)) hlim, fun N => ?_⟩
  · apply Set.indicator_le_indicator_of_subset (fun d => incl d) (f := fun k : ℕ => Real.log k / k)
    exact weight_nonneg
  · obtain ⟨d, hn, hd⟩ := hlarge N
    exact ⟨d, hn, incl d hd⟩

/-- The actual Jacobi-symbol supports have divergent logarithmic weight
in either order of prime selection, with independently prescribed lower bounds. -/
theorem split_prime_host_series (B : ℕ) :
    (Tendsto (mass (splittingPrime B)) atTop atTop ∧ ∀ N : ℕ, ∃ d > N, splittingPrime B d) ∧
    (∀ d : ℕ, splittingPrime B d → Tendsto (mass (companionPrime d)) atTop atTop ∧
      ∀ Q : ℕ, ∃ q > Q, companionPrime d q) ∧
    ∀ q : ℕ, q.Prime → q % 8 = 3 →
      let S := fun d => splittingPrime B d ∧ companionPrime d q
      Tendsto (mass S) atTop atTop ∧ ∀ N : ℕ, ∃ d > N, S d :=
  ⟨discriminants B, fun _ hd => companions hd.2.1, reverse_selection B⟩

end D5.S3.CharacterSums.SplitPrimeHostSeries
