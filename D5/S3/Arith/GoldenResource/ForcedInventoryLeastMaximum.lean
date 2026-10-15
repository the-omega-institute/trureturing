/- GID: D5/S3/Arith/GoldenResource/ForcedInventoryLeastMaximum
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/ForcedInventoryLeastMaximum
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Forced inventories give least fixed-price optimizers on positive base multiples. -/

import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison

noncomputable section
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenFutureExtensionMaximum

namespace D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum

/-- The LCM with the strict layer inventory maximizes the fixed-price objective
among positive base multiples and divides every such maximizer. Forced inactive
layers are retained, while removable equality-price layers are excluded by leastness. -/
theorem forced_inventory_least_maximum
    {lambda : ℝ} (hlambda : 0 < lambda)
    {m C : ℕ} (hm : 1 ≤ m) (hC : 1 ≤ C)
    (hcounts : ∀ q : ℕ, C.factorization q = optimalLayerCount lambda q) :
    (∀ n : ℕ, m ∣ n → 1 ≤ n →
      goldenResourceObjective lambda n ≤
        goldenResourceObjective lambda (Nat.lcm m C)) ∧
    (∀ n : ℕ, m ∣ n → 1 ≤ n →
      (∀ k : ℕ, m ∣ k → 1 ≤ k →
        goldenResourceObjective lambda k ≤ goldenResourceObjective lambda n) →
      Nat.lcm m C ∣ n) := by
  classical
  let J : ℕ → ℝ := goldenResourceObjective lambda
  let RelMax : ℕ → Prop := fun n =>
    m ∣ n ∧ 1 ≤ n ∧ ∀ k : ℕ, m ∣ k → 1 ≤ k → J k ≤ J n
  have hex : ∃ n : ℕ, RelMax n := by
    obtain ⟨n, hmn, hn, hmax⟩ := golden_future_extension_maximum_attained hlambda hm
    refine ⟨n, hmn, hn, ?_⟩
    intro k hmk hk
    exact (sub_le_sub_iff_right _).mp (hmax k hmk hk)
  let T := Nat.find hex
  have ht : RelMax T := Nat.find_spec hex
  have hleast : ∀ n : ℕ, RelMax n → T ≤ n := fun n hn => Nat.find_min' hex hn
  have hm0 : m ≠ 0 := by omega
  have hC0 : C ≠ 0 := by omega

  -- The strict inventory divides every relative maximum without using leastness.
  have count_dvd : ∀ n : ℕ, RelMax n → C ∣ n := by
    intro n hn
    have hn0 : n ≠ 0 := by have := hn.2.1; omega
    apply (Nat.factorization_le_iff_dvd hC0 hn0).mp
    intro q
    rw [hcounts]
    by_cases hq : q.Prime
    · have hnext : goldenLayerMarginal q (n.factorization q + 1) ≤ lambda := by
        have hnq : 1 ≤ n * q := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hn0 hq.ne_zero)
        have hc := hn.2.2 (n * q) (hn.1.trans (dvd_mul_right n q)) hnq
        have hd := golden_resource_objective_single_layer_delta lambda hn.2.1 hq
        have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
        change goldenResourceObjective lambda (n * q) ≤ goldenResourceObjective lambda n at hc
        nlinarith
      by_contra h
      have hk : n.factorization q + 1 ∈
          {k : ℕ | 1 ≤ k ∧ q.Prime ∧ lambda < goldenLayerMarginal q k} := by
        rw [positive_layers_eq_count_interval hlambda hq]
        exact ⟨by omega, by omega⟩
      exact (not_lt_of_ge hnext) hk.2.2
    · simp [optimalLayerCount, hq]

  have hT0 : T ≠ 0 := by have := ht.2.1; omega
  have hforced := (Nat.factorization_le_iff_dvd hm0 hT0).mpr ht.1
  have hactive := (Nat.factorization_le_iff_dvd hC0 hT0).mpr (count_dvd T ht)
  have hcoordinates : ∀ q : ℕ,
      T.factorization q = max (m.factorization q) (C.factorization q) := by
    intro q
    by_cases hq : q.Prime
    · rcases eq_or_lt_of_le (hforced q) with he | he
      · rw [← he]
        exact (Nat.max_eq_left (by simpa [he] using hactive q)).symm
      · have hqT : q ∣ T := Nat.dvd_of_factorization_pos (by omega)
        let R := T / q
        have hR : 1 ≤ R := Nat.div_pos (Nat.le_of_dvd (by omega : 0 < T) hqT) hq.pos
        have hR0 : R ≠ 0 := by omega
        have hRq : R * q = T := Nat.div_mul_cancel hqT
        have hmR : m ∣ R := by
          apply (Nat.factorization_le_iff_dvd hm0 hR0).mp
          rw [show R = T / q from rfl, Nat.factorization_div hqT]
          intro r
          by_cases hrq : r = q
          · subst r
            simpa [hq.factorization] using
              (show m.factorization q ≤ T.factorization q - 1 by omega)
          · simpa [hq.factorization, hrq] using hforced r
        have hRT : R < T := Nat.div_lt_self (by omega : 0 < T) hq.one_lt
        have hstrict : J R < J T := by
          have hle := ht.2.2 R hmR hR
          by_contra h
          have heq : J R = J T := le_antisymm hle (le_of_not_gt h)
          have hrmax : RelMax R := by
            refine ⟨hmR, hR, ?_⟩
            intro k hmk hk
            exact (ht.2.2 k hmk hk).trans_eq heq.symm
          exact (not_lt_of_ge (hleast R hrmax)) hRT
        have hRfactor : R.factorization q + 1 = T.factorization q := by
          have hf := congrArg (fun f : ℕ →₀ ℕ => f q)
            (Nat.factorization_mul hR0 hq.ne_zero)
          rw [hRq] at hf
          simpa [hq.factorization] using hf.symm
        have hd := golden_resource_objective_single_layer_delta lambda hR hq
        rw [hRq, hRfactor] at hd
        have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
        have hgain : lambda < goldenLayerMarginal q (T.factorization q) := by
          change goldenResourceObjective lambda R < goldenResourceObjective lambda T at hstrict
          nlinarith
        have hk : T.factorization q ∈
            {k : ℕ | 1 ≤ k ∧ q.Prime ∧ lambda < goldenLayerMarginal q k} :=
          ⟨by omega, hq, hgain⟩
        rw [positive_layers_eq_count_interval hlambda hq] at hk
        have heq : T.factorization q = C.factorization q := by
          apply Nat.le_antisymm
          · rw [hcounts]
            exact hk.2
          · exact hactive q
        rw [heq]
        exact (Nat.max_eq_right ((hforced q).trans_eq heq)).symm
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

  have hLCM0 : Nat.lcm m C ≠ 0 := Nat.lcm_ne_zero hm0 hC0
  have hTLCM : T = Nat.lcm m C := by
    apply Nat.eq_of_factorization_eq hT0 hLCM0
    intro q
    rw [Nat.factorization_lcm hm0 hC0]
    simpa only [Finsupp.sup_apply] using hcoordinates q
  constructor
  · intro n hmn hn
    have hnT := ht.2.2 n hmn hn
    simpa only [J, hTLCM] using hnT
  · intro n hmn hn hmax
    exact Nat.lcm_dvd hmn (count_dvd n ⟨hmn, hn, hmax⟩)

#print axioms forced_inventory_least_maximum

end D5.S3.Arith.GoldenResource.ForcedInventoryLeastMaximum
