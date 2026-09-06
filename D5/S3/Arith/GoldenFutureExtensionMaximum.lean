/- GID: D5/S3/Arith/GoldenFutureExtensionMaximum
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenFutureExtensionMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finitely many positive future prime layers produce a maximizing integer extension. -/

import D5.S3.Arith.GoldenPrimeLayerCofinite
import D5.S3.Arith.GoldenResourceObjectiveFactorization

/- Library-search audit trail (2026-09-06):
   * Repository searches for `future_positive_layers`, `positive_layers_form`,
     `goldenResourceObjective` together with divisibility or maximum patterns, and positive
     finite-prefix marginal variants found the frozen cutoff, decay, strict-decrease, local,
     and factorization results imported above, but no theorem asserting this attained future
     maximum.
   * Pinned Mathlib searches for the project-specific names found no hits. Searches around
     finite profitable prime layers and maximizing multiples found no packaged domain theorem;
     Mathlib does provide `Nat.prod_pow_factorization_eq_self`,
     `Nat.dvd_prod_pow_of_factorization_le`, `Nat.factorization_le_iff_dvd`,
     `Finset.exists_mem_eq_sup`, `Finset.le_sup`, `monotoneOn_of_le_add_one`, and
     `antitoneOn_of_add_one_le`, which are used below.
   * Third-party Lean ecosystem searches through NyxID/Firecrawl for the exact proposed witness
     name, the golden objective name, and semantic finite prime-layer variants returned no
     matching Lean declaration; the results were generic tutorials and elementary number theory.
     Three earlier Firecrawl requests without a content-type header failed with HTTP 400 and are
     not counted as completed searches. -/

namespace D5.S3.Arith.GoldenFutureExtensionMaximum

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenPrimeLayerCofinite
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization

noncomputable section

private theorem future_positive_layers_form_finite_prefix
    {lambda : ℝ} (hlambda : 0 < lambda) (n : ℕ) :
    ∃ layers : Finset (ℕ × ℕ),
      (∀ p a, (p, a) ∈ layers ↔
        p.Prime ∧ n.factorization p < a ∧ lambda < goldenLayerMarginal p a) ∧
      ∀ p a, (p, a) ∈ layers →
        ∀ b, n.factorization p < b → b ≤ a → (p, b) ∈ layers := by
  classical
  obtain ⟨P, hP⟩ := golden_layer_marginal_lt_of_prime_le hlambda
  let cutoff : ℕ → ℕ := fun p =>
    if hp : p.Prime then Nat.find (golden_layer_marginal_lt_of_le hp hlambda) else 0
  let depth := (Finset.range P).sup cutoff
  let layers := (Finset.range P ×ˢ Finset.range depth).filter fun layer =>
    layer.1.Prime ∧ n.factorization layer.1 < layer.2 ∧
      lambda < goldenLayerMarginal layer.1 layer.2
  have mem_layers (p a : ℕ) :
      (p, a) ∈ layers ↔
        p.Prime ∧ n.factorization p < a ∧ lambda < goldenLayerMarginal p a := by
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      have hpP : p < P := by
        by_contra hpP
        have hbelow := hP p h.1 (Nat.le_of_not_gt hpP) a (by omega)
        exact (not_lt_of_ge hbelow.le) h.2.2
      have haCutoff : a < cutoff p := by
        by_contra haCutoff
        have hdecay := Nat.find_spec (golden_layer_marginal_lt_of_le h.1 hlambda)
        have hfindLe : Nat.find (golden_layer_marginal_lt_of_le h.1 hlambda) ≤ a := by
          rw [← show cutoff p = Nat.find (golden_layer_marginal_lt_of_le h.1 hlambda) by
            simp only [cutoff, dif_pos h.1]]
          exact Nat.le_of_not_gt haCutoff
        have hbelow := hdecay a hfindLe
        exact (not_lt_of_ge hbelow.le) h.2.2
      have hcutoffDepth : cutoff p ≤ depth := by
        exact Finset.le_sup (Finset.mem_range.mpr hpP)
      have haDepth : a < depth := haCutoff.trans_le hcutoffDepth
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hpP,
        Finset.mem_range.mpr haDepth⟩, h⟩
  refine ⟨layers, mem_layers, ?_⟩
  intro p a ha b hnb hba
  rw [mem_layers] at ha ⊢
  refine ⟨ha.1, hnb, ?_⟩
  rcases eq_or_lt_of_le hba with rfl | hba
  · exact ha.2.2
  · exact ha.2.2.trans (golden_layer_strict_decrease ha.1 (by omega) hba)

private theorem golden_prime_local_objective_diff {p : ℕ} (hp : p.Prime)
    (lambda : ℝ) (a : ℕ) :
    goldenPrimeLocalObjective lambda p (a + 1) - goldenPrimeLocalObjective lambda p a =
      (goldenLayerMarginal p (a + 1) - lambda) * Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have ha : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  have hb : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1 + 1) :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  unfold goldenPrimeLocalObjective goldenLayerMarginal
  rw [Real.log_div hb.ne' (sub_pos.mpr hpInvLt).ne',
    Real.log_div ha.ne' (sub_pos.mpr hpInvLt).ne', Real.log_div hb.ne' ha.ne']
  push_cast
  field_simp [hpLog.ne']
  ring

/-- At every positive price, finitely many positive future layers determine a positive multiple
whose objective gain is maximal among all positive multiples of the starting integer. -/
theorem golden_future_extension_maximum_attained
    {lambda : ℝ} (hlambda : 0 < lambda) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m : ℕ, n ∣ m ∧ 1 ≤ m ∧
      ∀ k : ℕ, n ∣ k → 1 ≤ k →
        goldenResourceObjective lambda k - goldenResourceObjective lambda n ≤
          goldenResourceObjective lambda m - goldenResourceObjective lambda n := by
  classical
  obtain ⟨layers, mem_layers, layers_prefix⟩ :=
    future_positive_layers_form_finite_prefix hlambda n
  let top : ℕ → ℕ := fun p =>
    (layers.filter fun layer => layer.1 = p).sup Prod.snd
  let exponent : ℕ → ℕ := fun p => max (n.factorization p) (top p)
  let support := n.primeFactors ∪ layers.image Prod.fst
  have exponent_support : ∀ p, exponent p ≠ 0 → p ∈ support := by
    intro p hp
    by_contra hpSupport
    have hparts : p ∉ n.primeFactors ∧ p ∉ layers.image Prod.fst := by
      simpa only [support, Finset.mem_union, not_or] using hpSupport
    have hnFactorization : n.factorization p = 0 := by
      simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hparts.1
    have hfilter : layers.filter (fun layer => layer.1 = p) = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨layer, hlayer⟩
      have hmem := Finset.mem_filter.mp hlayer
      exact hparts.2 (Finset.mem_image.mpr ⟨layer, hmem.1, hmem.2⟩)
    have htop : top p = 0 := by simp [top, hfilter]
    exact hp (by simp [exponent, hnFactorization, htop])
  let target : ℕ →₀ ℕ := Finsupp.onFinset support exponent exponent_support
  let m := target.prod (· ^ ·)
  have target_prime : ∀ p ∈ target.support, p.Prime := by
    intro p hp
    have hpSupport : p ∈ support := Finsupp.support_onFinset_subset hp
    rcases Finset.mem_union.mp hpSupport with hp | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · obtain ⟨layer, hlayer, rfl⟩ := Finset.mem_image.mp hp
      exact (mem_layers layer.1 layer.2).mp hlayer |>.1
  have hmFactorization : m.factorization = target := by
    exact Nat.prod_pow_factorization_eq_self target_prime
  have hm0 : m ≠ 0 := by
    apply Finsupp.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (target_prime p hp).ne_zero
  have hm : 1 ≤ m := by omega
  have hn0 : n ≠ 0 := by omega
  have hfactorizationLe : n.factorization ≤ target := by
    intro p
    change n.factorization p ≤ exponent p
    exact Nat.le_max_left _ _
  have hnm : n ∣ m := Nat.dvd_prod_pow_of_factorization_le hn0 hfactorizationLe
  refine ⟨m, hnm, hm, ?_⟩
  intro k hnk hk
  have hk0 : k ≠ 0 := by omega
  have hnkFactorization : n.factorization ≤ k.factorization :=
    (Nat.factorization_le_iff_dvd hn0 hk0).mpr hnk
  have local_maximal (p : ℕ) (hp : p.Prime) (b : ℕ)
      (hb : n.factorization p ≤ b) :
      goldenPrimeLocalObjective lambda p b ≤
        goldenPrimeLocalObjective lambda p (exponent p) := by
    let baseline := n.factorization p
    let chosen := exponent p
    change baseline ≤ b at hb
    change goldenPrimeLocalObjective lambda p b ≤
      goldenPrimeLocalObjective lambda p chosen
    have hbaselineChosen : baseline ≤ chosen := by
      exact Nat.le_max_left _ _
    have hchosenTop : top p ≤ chosen := by
      exact Nat.le_max_right _ _
    have hnext : goldenLayerMarginal p (chosen + 1) ≤ lambda := by
      by_contra hgain
      have hpositive : lambda < goldenLayerMarginal p (chosen + 1) := lt_of_not_ge hgain
      have hfuture : (p, chosen + 1) ∈ layers :=
        (mem_layers p (chosen + 1)).mpr ⟨hp, by omega, hpositive⟩
      have htopBound : chosen + 1 ≤ top p := by
        have hfiltered : (p, chosen + 1) ∈
            layers.filter (fun layer => layer.1 = p) :=
          Finset.mem_filter.mpr ⟨hfuture, rfl⟩
        change chosen + 1 ≤ (layers.filter fun layer => layer.1 = p).sup Prod.snd
        simpa only [Prod.snd] using
          (Finset.le_sup (f := Prod.snd) hfiltered)
      omega
    have chosen_layer (hstrict : baseline < chosen) : (p, chosen) ∈ layers := by
      have hbaselineTop : baseline ≤ top p := by
        by_contra hnot
        have htopBaseline : top p ≤ baseline := Nat.le_of_not_ge hnot
        have hchosenBaseline : chosen = baseline := by
          dsimp only [chosen, exponent, baseline]
          exact Nat.max_eq_left htopBaseline
        omega
      have htopChosen : top p = chosen := by
        dsimp only [chosen, exponent]
        rw [Nat.max_eq_right hbaselineTop]
      have hnonempty : (layers.filter fun layer => layer.1 = p).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have htopZero : top p = 0 := by simp [top, hempty]
        rw [htopZero] at htopChosen
        omega
      obtain ⟨layer, hlayer, hlayerTop⟩ :=
        Finset.exists_mem_eq_sup _ hnonempty Prod.snd
      have hparts := Finset.mem_filter.mp hlayer
      have hfirst : layer.1 = p := hparts.2
      have hsecond : layer.2 = chosen := by
        calc
          layer.2 = top p := by simpa only [top] using hlayerTop.symm
          _ = chosen := htopChosen
      have hlayerEq : layer = (p, chosen) := Prod.ext hfirst hsecond
      rw [hlayerEq] at hparts
      exact hparts.1
    have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have up : MonotoneOn (goldenPrimeLocalObjective lambda p)
        (Set.Icc baseline chosen) := by
      apply monotoneOn_of_le_add_one Set.ordConnected_Icc
      intro a _ ha haNext
      rcases ha with ⟨hbaselineA, _⟩
      rcases haNext with ⟨_, hnextChosen⟩
      have hbaselineNext : baseline < a + 1 := hbaselineA.trans_lt (Nat.lt_succ_self a)
      have hstrict : baseline < chosen := hbaselineNext.trans_le hnextChosen
      have hfuture :=
        layers_prefix p chosen (chosen_layer hstrict) (a + 1) hbaselineNext hnextChosen
      have hgain := (mem_layers p (a + 1)).mp hfuture |>.2.2
      have hstep := mul_nonneg (sub_nonneg.mpr hgain.le) hpLog.le
      rw [← golden_prime_local_objective_diff hp lambda a] at hstep
      exact sub_nonneg.mp hstep
    have down : AntitoneOn (goldenPrimeLocalObjective lambda p) (Set.Ici chosen) := by
      apply antitoneOn_of_add_one_le Set.ordConnected_Ici
      intro a _ ha _
      have hgain : goldenLayerMarginal p (a + 1) ≤ lambda := by
        have hchosenA : chosen ≤ a := ha
        rcases eq_or_lt_of_le hchosenA with rfl | hlt
        · exact hnext
        · exact (golden_layer_strict_decrease hp (by omega)
            (Nat.add_lt_add_right hlt 1)).le.trans hnext
      have hstep := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hgain) hpLog.le
      rw [← golden_prime_local_objective_diff hp lambda a] at hstep
      exact sub_nonpos.mp hstep
    rcases le_total b chosen with hbc | hcb
    · exact up ⟨hb, hbc⟩ ⟨hbaselineChosen, le_rfl⟩ hbc
    · exact down (by simp) hcb hcb
  let primes := m.primeFactors ∪ k.primeFactors
  have hsumM := golden_resource_objective_sum_on lambda hm primes Finset.subset_union_left
  have hsumK := golden_resource_objective_sum_on lambda hk primes Finset.subset_union_right
  have hobjective : goldenResourceObjective lambda k ≤ goldenResourceObjective lambda m := by
    rw [hsumK, hsumM]
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime : p.Prime := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    have hmExponent : m.factorization p = exponent p := by
      rw [hmFactorization]
      rfl
    rw [hmExponent]
    exact local_maximal p hpPrime (k.factorization p) (hnkFactorization p)
  exact sub_le_sub_right hobjective _

#print axioms golden_future_extension_maximum_attained

end

end D5.S3.Arith.GoldenFutureExtensionMaximum
