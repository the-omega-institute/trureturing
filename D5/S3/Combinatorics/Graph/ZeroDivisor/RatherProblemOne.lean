/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne
   mirror-E: none(waiver:unbounded-native-prime-family)
   anchors: [mathlib/module/Mathlib.Data.ZMod.QuotientRing]
   utility: none
   digest: The actual three-prime zero-divisor independence polynomial is log concave and weakly unimodal. -/

import D5.S3.Combinatorics.Graph.ZeroDivisor.NativeCoefficients
import D5.S3.Combinatorics.RealRootedPermutations.LogConcave

/-! The native all-prime consumer of Rather's Problem 1, including the prime two. -/

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

namespace D5.S3.Combinatorics.Graph.ZeroDivisor.RatherProblemOne

set_option maxHeartbeats 1200000 in
/-- The original all-prime graph has attained support, log concavity and weak unimodality. -/
theorem rather_problem_one (p q r : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p < q) (hqr : q < r) :
    letI : NeZero (p*q*r) :=
      ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero⟩
    let a := p-1
    let b := q-1
    let c := r-1
    let N := max (a*b+a*c+b*c) (c+a*c+b*c)
    let G := Support.graph (ZMod (p*q*r))
    let s := fun k => (independencePolynomial G Finset.univ).coeff k
    14 ≤ N ∧ G.indepNum = N ∧
      (∃ S : Finset (Support.Vertex (ZMod (p*q*r))), G.IsIndepSet (S : Set _) ∧ S.card = N) ∧
      (∀ k, k ≤ N → 0 < s k) ∧ (∀ k, N < k → s k = 0) ∧
      (∀ k, 1 ≤ k → s (k-1)*s (k+1) ≤ s k^2) ∧
      (∃ m, m ≤ N ∧ MonotoneOn s (Set.Iic m) ∧ AntitoneOn s (Set.Ici m)) := by
  classical
  letI : NeZero (p*q*r) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero⟩
  let m : Fin 3 → ℕ := ![p,q,r]
  letI : ∀ i, Fact (m i).Prime := fun i => by
    fin_cases i
    · exact ⟨hp⟩
    · exact ⟨hq⟩
    · exact ⟨hr⟩
  letI : ∀ i, NeZero (m i) := fun i => ⟨(Fact.out : (m i).Prime).ne_zero⟩
  letI : ∀ i, Fintype (ZMod (m i)) := fun i => inferInstance
  letI : ∀ i, Nontrivial (ZMod (m i)) := fun i => inferInstance
  letI : ∀ i, NoZeroDivisors (ZMod (m i)) := fun i => inferInstance
  have hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [m] at hij ⊢
    · exact (Nat.coprime_primes hp hq).mpr (ne_of_lt hpq)
    · exact (Nat.coprime_primes hp hr).mpr (ne_of_lt (hpq.trans hqr))
    · exact (Nat.coprime_primes hq hp).mpr (ne_of_gt hpq)
    · exact (Nat.coprime_primes hq hr).mpr (ne_of_lt hqr)
    · exact (Nat.coprime_primes hr hp).mpr (ne_of_gt (hpq.trans hqr))
    · exact (Nat.coprime_primes hr hq).mpr (ne_of_gt hqr)
  have hmprod : (∏ i, m i) = p*q*r := by
    simp [m, Fin.prod_univ_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hq3 : 3 ≤ q := by have := hp.two_le; omega
  have hr5 : 5 ≤ r := by
    have hr4 : r ≠ 4 := by intro he; subst r; norm_num at hr
    omega
  let a := p-1
  let b := q-1
  let c := r-1
  let N := max (a*b+a*c+b*c) (c+a*c+b*c)
  let G := Support.graph (ZMod (p*q*r))
  let P := independencePolynomial G Finset.univ
  let s := fun k => P.coeff k
  let sQ := fun k => (s k : ℚ)
  have hco := NativeCoefficients.coefficients_three_domains
    ((ZMod.ringEquivCongr hmprod.symm).trans (Support.crt m hcop))
    (by simpa only [ZMod.card] using hpq.le)
    (by simpa only [ZMod.card] using hqr.le)
    (by simpa only [ZMod.card] using hq3)
    (by simpa only [ZMod.card] using hr5)
  change 14 ≤ N ∧ G.indepNum = N ∧ _
  have hco' : 14 ≤ N ∧ (∀ k, k ≤ N → 0 < sQ k) ∧
      (∀ k, N < k → sQ k = 0) ∧
      (∀ k, 1 ≤ k → k < N → sQ (k-1)*sQ (k+1) < sQ k^2) := by
    simpa only [ZMod.card] using hco
  obtain ⟨hN, hposQ, htailQ, hlcQ⟩ := hco'
  have hpos (k : ℕ) (hk : k ≤ N) : 0 < s k := by
    exact_mod_cast hposQ k hk
  have htail (k : ℕ) (hk : N < k) : s k = 0 := by
    exact_mod_cast htailQ k hk
  have hcount (k : ℕ) : s k =
      (((configurations G Finset.univ).filter fun S => S.card = k).card : ℤ) := by
    exact Support.coefficient_card Finset.univ k
  obtain ⟨S, hS⟩ := Finset.card_pos.mp (show 0 <
      ((configurations G Finset.univ).filter fun S => S.card = N).card by
    have h := hpos N le_rfl
    rw [hcount] at h
    exact_mod_cast h)
  have hSind : G.IsIndepSet (S : Set _) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hScard : S.card = N := (Finset.mem_filter.mp hS).2
  have hbound (T : Finset (Support.Vertex (ZMod (p*q*r))))
      (hT : G.IsIndepSet (T : Set _)) : T.card ≤ N := by
    have hmem : T ∈ (configurations G Finset.univ).filter fun U => U.card = T.card := by
      simp only [Finset.mem_filter, configurations, Finset.mem_powerset,
        Finset.subset_univ, true_and]
      exact ⟨hT, rfl⟩
    have hcpos : 0 < s T.card := by
      rw [hcount]
      exact_mod_cast Finset.card_pos.mpr ⟨T, hmem⟩
    by_contra hn
    rw [htail T.card (by omega)] at hcpos
    exact lt_irrefl 0 hcpos
  have halpha : G.indepNum = N := by
    apply le_antisymm
    · obtain ⟨T, hT⟩ := G.maximumIndepSet_exists
      rw [← G.maximumIndepSet_card_eq_indepNum T hT]
      exact hbound T hT.isIndepSet
    · rw [← hScard]
      exact hSind.card_le_indepNum
  have hlc (k : ℕ) (hk : 1 ≤ k) : s (k-1)*s (k+1) ≤ s k^2 := by
    by_cases hkN : k < N
    · have h : s (k-1)*s (k+1) < s k^2 := by
        exact_mod_cast hlcQ k hk hkN
      exact h.le
    · rw [htail (k+1) (by omega), mul_zero]
      exact sq_nonneg _
  let f := fun k => (s k : ℝ)
  have hposR (k : ℕ) (hk : k ≤ N) : 0 < f k := by
    exact_mod_cast hpos k hk
  have hlcR (k : ℕ) (hk : k+2 ≤ N) : f k*f (k+2) < f (k+1)^2 := by
    have h := hlcQ (k+1) (by omega) (by omega)
    norm_num only [Nat.add_sub_cancel] at h
    exact_mod_cast h
  obtain ⟨j, hj, hmax'⟩ := Finset.exists_max_image (Finset.range (N+1)) f
    (Finset.nonempty_range_iff.mpr (by omega))
  have hjN : j ≤ N := by simpa only [Finset.mem_range] using hj
  have hmax (i : ℕ) (hi : i ≤ N) : f i ≤ f j :=
    hmax' i (Finset.mem_range.mpr (by omega))
  have upstep (i : ℕ) (hi : i+1 ≤ j) : s i ≤ s (i+1) := by
    by_cases he : i+1 = j
    · have h := hmax i (by omega)
      rw [← he] at h
      exact_mod_cast h
    · have h := D5.S3.Combinatorics.RealRootedPermutations.LogConcave.increasing_before_max
        hposR hlcR hjN hmax i (by omega)
      exact_mod_cast h.le
  have downstep (i : ℕ) (hi : j ≤ i) : s (i+1) ≤ s i := by
    by_cases hiN : i < N
    · by_cases he : i = j
      · subst i
        have h := hmax (j+1) (by omega)
        exact_mod_cast h
      · have h := D5.S3.Combinatorics.RealRootedPermutations.LogConcave.decreasing_after_max
          hposR hlcR hjN hmax i (by omega) (by omega)
        exact_mod_cast h.le
    · rw [htail (i+1) (by omega)]
      by_cases he : i = N
      · subst i
        exact (hpos N le_rfl).le
      · rw [htail i (by omega)]
  have hup : MonotoneOn s (Set.Iic j) := by
    apply monotoneOn_of_le_succ Set.ordConnected_Iic
    intro i _ _ hnext
    exact upstep i hnext
  have hdown : AntitoneOn s (Set.Ici j) := by
    apply antitoneOn_of_succ_le Set.ordConnected_Ici
    intro i _ hi _
    exact downstep i hi
  exact ⟨hN, halpha, ⟨S, hSind, hScard⟩, hpos, htail, hlc, j, hjN, hup, hdown⟩

end D5.S3.Combinatorics.Graph.ZeroDivisor.RatherProblemOne
