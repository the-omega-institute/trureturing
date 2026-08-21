/- GID: D5/S3/Analytic/Zeta/ZetaPrimeIndependence
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime exponent coordinates are independent under the zeta distribution. -/

import Mathlib
import D5.S3.Analytic.Zeta.PrimeExponentLaw

/- Provenance: Native proof over pinned mathlib. -/

/- Search and proof receipt (2026-08-21).

   Generality.
   * Tag: `I`. H10 says `通用性头必填;标 G 者禁 import 实例事实`, and SL-010 forbids a
     `G` file from importing an `I` fact. This file directly imports
     `PrimeExponentLaw.lean` (`I`), which transitively imports and uses the
     particular `zetaDist` from `ZetaGibbs.lean` (`I`); therefore `I` is forced.
   * Repository imports, one by one: `D5/S3/Analytic/Zeta/PrimeExponentLaw.lean`
     is tagged `I`. Its repository dependency `D5/S3/Analytic/ZetaGibbs.lean`
     is also tagged `I`. `Mathlib` is external and has no repository tag.

   Thinness, per theorem.
   * `measure_iInter_factorization_ge` is SUBSTANTIVE: it proves pairwise
     coprimality of distinct prime powers, turns their conjunction into one
     lcm/product divisibility event off the null zero slot, invokes the public
     `measure_dvd`, and performs the finite real-rpow product calculation.
   * `iIndepFun_factorization` is SUBSTANTIVE: it proves independence first on
     the upper-tail pi-systems and proves that those systems generate the
     discrete measurable structure on `Nat`; this is the full infinite-family
     `iIndepFun` packaging, not merely pairwise independence.
   * `measure_iInter_factorization_eq` is THIN: after the packaging theorem, it
     applies the finite-intersection characterization to singleton coordinate
     sets and rewrites each factor with the existing single-prime mass law.

   Attribute audit. Each claim below was checked against the line immediately
   above the declaration in the pinned source. The Mathlib search also checked
   whether a declaration was generated through `to_additive`; none of the
   load-bearing declarations below is generated that way, so there are no
   inherited `to_additive` attributes to add.
   * Repository declarations `measure_dvd`, `measure_factorization_ge`, and
     `measure_factorization_eq` (`PrimeExponentLaw.lean:228,252,271`) carry no
     attributes. `weight`, `zetaDist`, and `zeta_dist_apply`
     (`ZetaGibbs.lean:19,55,59`) carry none; `weight_zero` (line 23) CARRIES
     `@[simp]`.
   * `Finset.prod_ne_zero_iff`
     (`Algebra/BigOperators/GroupWithZero/Finset.lean:60`),
     `Finset.dvd_prod_of_mem`
     (`Algebra/BigOperators/Group/Finset/Piecewise.lean:230`),
     `Finset.lcm_dvd` (`Algebra/GCDMonoid/Finset.lean:66`),
     `Finset.lcm_eq_prod` (`Algebra/GCDMonoid/FinsetLemmas.lean:35`), and
     `Nat.coprime_pow_primes` (`Data/Nat/Prime/Basic.lean:201`) carry no
     attributes. The inspected but unused generic
     `Finset.prod_dvd_of_coprime` (`RingTheory/Coprime/Lemmas.lean:102`) also
     carries none.
   * `Real.finsetProd_rpow` (`Analysis/SpecialFunctions/Pow/NNReal.lean:256`),
     `ENNReal.ofReal_prod_of_nonneg` (`Data/ENNReal/BigOperators.lean:64`),
     `Real.rpow_mul` (`Analysis/SpecialFunctions/Pow/Real.lean:412`), `ae_iff`
     and `measure_congr` (`MeasureTheory/OuterMeasure/AE.lean:78,270`) carry no
     attributes. `Real.rpow_natCast` (Real.lean:62) CARRIES
     `@[simp, norm_cast]`; `Real.rpow_nonneg` (Real.lean:163) CARRIES `@[bound]`.
     `Nat.Prime.pow_dvd_iff_le_factorization`
     (`Data/Nat/Factorization/Basic.lean:164`) and
     `PMF.toMeasure_apply_singleton`
     (`Probability/ProbabilityMassFunction/Basic.lean:228`) carry none.
   * `iIndepFun`, `iIndepFun_iff_iIndep`, `iIndepSets_iff`,
     `iIndepSets.iIndep`, `iIndepFun_iff_measure_inter_preimage_eq_mul`, and
     its alias `iIndepFun.measure_inter_preimage_eq_mul`
     (`Probability/Independence/Basic.lean:136,232,160,554,654,662`) carry no
     attributes. `IsPiSystem.comap` and `isPiSystem_Ici`
     (`MeasureTheory/PiSystem.lean:105,183`), `comap_generateFrom`
     (`MeasurableSpace/Basic.lean:161`), `borel_eq_top_of_discrete`
     (`BorelSpace/Basic.lean:59`), and `borel_eq_generateFrom_Ici`
     (`BorelSpace/Order.lean:94`) carry none. `MeasurableSet.singleton`
     (`MeasurableSpace/Defs.lean:248`) CARRIES `@[simp]`.
   * Lean core was audited separately. `propext` (`Init/Core.lean:1593`),
     `Quot.sound` (the `Quot` namespace's `sound`, Core.lean:1789), and the
     primitive `Classical.choice` (`Init/Prelude.lean:816`) are axioms with no
     attribute line. `Classical.choose`
     (`Init/Classical.lean:29`, a `noncomputable def`) and
     `Classical.choose_spec` (`Init/Classical.lean:32`) likewise have no
     attributes. An adversarial review caught this pair cited two lines too
     low, at 31 and 34, which are blank lines; the coordinates above were then
     read line by line against the pinned core source by the coordinator.

   Automation probe. After all three statements elaborated, a run-local file
   used `fail_if_success (solve | ...)` to test actual closure (not merely
   tactic progress), then closed each example with the theorem under test.
   For EACH statement, `decide`, plain `simp`, `omega`, and `norm_num` failed
   to close. Single-lemma `simp` probes also failed to close:
   * joint tail: `measure_dvd`, `Finset.lcm_eq_prod`, `Finset.lcm_dvd`,
     `Nat.coprime_pow_primes`, `measure_factorization_ge`,
     `Real.finsetProd_rpow`, and `ENNReal.ofReal_prod_of_nonneg`;
   * independence: `iIndepFun_iff_iIndep`, `iIndepSets.iIndep`,
     `iIndepSets_iff`, `IsPiSystem.comap`, `isPiSystem_Ici`,
     `borel_eq_generateFrom_Ici`, `borel_eq_top_of_discrete`,
     `MeasurableSpace.comap_generateFrom`, and
     `measure_iInter_factorization_ge`;
   * joint mass: `iIndepFun.measure_inter_preimage_eq_mul` and
     `measure_factorization_eq`.
     Every name resolved; there were no name-resolution errors. The two joint
     mass lemma arguments were reported as unused by the simp linter, which is
     still a measured failure to close, not a missing name. Scratch files were
     deleted after the probe.

   Candidates inspected (not declarations claimed to do real work).
   * `Finset.prod_dvd_of_coprime` was found at
     `RingTheory/Coprime/Lemmas.lean:102`, but it is stated with generic
     `IsCoprime` and does not directly give natural-number divisibility. The
     usable native route is `Finset.lcm_eq_prod` plus `Finset.lcm_dvd`.
   * `iIndepFun_iff_measure_inter_preimage_eq_mul` and
     `iIndepFun_iff_map_fun_eq_pi_map` were inspected. The first is used only
     after packaging for joint masses; the second is unused because proving a
     full product-measure identity would duplicate the pi-system argument.
   * `Probability/Distributions/Geometric.lean` supplies a generic geometric
     distribution, not the zeta-coordinate identification, and is unused.

   Declarations doing real work.
   * Joint tail: `Finset.prod_ne_zero_iff`, `Nat.coprime_pow_primes`,
     `Finset.lcm_eq_prod`, `Finset.lcm_dvd`, `Finset.dvd_prod_of_mem`,
     `Nat.Prime.pow_dvd_iff_le_factorization`, `measure_dvd`,
     `measure_factorization_ge`, `Real.finsetProd_rpow`,
     `ENNReal.ofReal_prod_of_nonneg`, `Real.rpow_natCast`, and `Real.rpow_mul`.
   * Packaging: `iIndepFun_iff_iIndep`, `iIndepSets.iIndep`,
     `iIndepSets_iff`, `IsPiSystem.comap`, `isPiSystem_Ici`,
     `borel_eq_generateFrom_Ici`, `borel_eq_top_of_discrete`,
     `MeasurableSpace.comap_generateFrom`, and the joint-tail theorem.
   * Joint mass: `iIndepFun.measure_inter_preimage_eq_mul` and
     `measure_factorization_eq`.

   Search provenance and the two pinned trees.
   * SUPPLIED BY THE DISPATCHER: Mathlib has no `zetaDist`, `zeta_dist`, or
     `ZetaDistribution`; `Mathlib/Probability/` has no `Nat.factorization`;
     the geometric file exists; and the three independence coordinates are
     `iIndepFun` (136), the finite-intersection iff (654), and the pi-map iff
     (861). These are recorded as supplied, not self-originated findings.
   * Independently verified in the pinned Mathlib tree by recursive exact-name
     searches: the four absence searches returned zero hits, the geometric
     file exists, and the three declarations occur at exactly 136, 654, 861.
   * Independently searched the pinned Lean core tree for the same zeta and
     factorization names and for coprime-product/divisibility declarations;
     it contains no result for this problem. It does contain the foundational
     `propext`, `Classical.choice`, `Classical.choose`, and `Quot.sound`
     declarations audited above. Thus both pinned trees were searched
     separately before the proof route was fixed.

   Residual, address, scope, and closure.
   * The residual is still open: the files with `ast_path: row/F2` and
     `ast_path: row/Euler-积-独立性` remain under `residual-open/`, each with
     empty `coverage_gids` and coverage receipts. This independently verifies
     the dispatcher-supplied open status without editing the ledger.
   * Remeasurement found one direct Lean file in `Zeta/` before this unit and
     two including it, below the strictly-more-than-twelve split threshold.
   * Ranked scope reached (1), (2), and (3). Joint mass is obtained from the
     full independence packaging rather than inclusion-exclusion; there is no
     remaining obstruction.
   * STRENGTHENING BEYOND THE DISPATCHED SCOPE, recorded explicitly. The
     dispatch asked for independence over a FINITE SET of primes.
     `iIndepFun_factorization` instead states `iIndepFun` for the coordinate
     family indexed by the ENTIRE type `Nat.Primes`. That is strictly stronger
     than what was requested: mathlib's predicate ranges over every finite
     subfamily, so the finite-set statement is one of its consequences rather
     than an equal formulation. The stronger form was reached by the worker and
     is not a restatement of the dispatch.
   * `#print axioms` reports exactly
     `{propext, Classical.choice, Quot.sound}` for each theorem. -/

namespace D5.S3.Analytic.Zeta.ZetaPrimeIndependence

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.PrimeExponentLaw

noncomputable section

/-- Joint upper tails of finitely many distinct prime-exponent coordinates factorize. -/
theorem measure_iInter_factorization_ge (s : ℝ) (hs : 1 < s)
    (P : Finset Nat.Primes) (k : Nat.Primes → ℕ) :
    (zetaDist s hs).toMeasure (⋂ p ∈ P, {n : ℕ | k p ≤ n.factorization p.1}) =
      ∏ p ∈ P, (zetaDist s hs).toMeasure {n : ℕ | k p ≤ n.factorization p.1} := by
  let μ := (zetaDist s hs).toMeasure
  let a := ∏ p ∈ P, p.1 ^ k p
  have ha : a ≠ 0 := by
    dsimp [a]
    exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ pow_ne_zero _ p.2.ne_zero
  have hcop : (P : Set Nat.Primes).Pairwise (Nat.Coprime.onFun fun p ↦ p.1 ^ k p) := by
    intro p hp q hq hpq
    exact Nat.coprime_pow_primes _ _ p.2 q.2 (fun h ↦ hpq (Subtype.ext h))
  have hz : μ ({0} : Set ℕ) = 0 := by
    rw [(zetaDist s hs).toMeasure_apply_singleton 0 MeasurableSet.of_discrete]
    simp [zeta_dist_apply, weight_zero s (by linarith)]
  have hne : ∀ᵐ n ∂μ, n ≠ 0 := by
    rw [ae_iff]
    simpa using hz
  calc
    μ (⋂ p ∈ P, {n : ℕ | k p ≤ n.factorization p}) = μ {n : ℕ | a ∣ n} := by
      apply measure_congr
      filter_upwards [hne] with n hn
      apply propext
      change n ∈ (⋂ p ∈ P, {n : ℕ | k p ≤ n.factorization p.1}) ↔ n ∈ {n : ℕ | a ∣ n}
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h
        rw [show a = ∏ p ∈ P, p.1 ^ k p by rfl, ← Finset.lcm_eq_prod hcop]
        exact Finset.lcm_dvd fun p hp ↦
          p.2.pow_dvd_iff_le_factorization hn |>.2 (h p hp)
      · intro h p hp
        apply p.2.pow_dvd_iff_le_factorization hn |>.1
        exact (Finset.dvd_prod_of_mem (fun q ↦ q.1 ^ k q) hp).trans h
    _ = weight s a := measure_dvd s hs a ha
    _ = ∏ p ∈ P, ENNReal.ofReal ((p.1 : ℝ) ^ (-(k p : ℝ) * s)) := by
      rw [weight]
      rw [show (a : ℝ) = ∏ p ∈ P, (p.1 : ℝ) ^ k p by simp [a]]
      rw [← Real.finsetProd_rpow P (fun p ↦ (p.1 : ℝ) ^ k p)
        (fun p hp ↦ by positivity) (-s)]
      rw [ENNReal.ofReal_prod_of_nonneg (fun p hp ↦ Real.rpow_nonneg (by positivity) _)]
      apply Finset.prod_congr rfl
      intro p hp
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    _ = ∏ p ∈ P, μ {n : ℕ | k p ≤ n.factorization p} := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (measure_factorization_ge s hs p.1 (k p) p.2).symm

/-- The prime-exponent coordinate functions are mutually independent. -/
theorem iIndepFun_factorization (s : ℝ) (hs : 1 < s) :
    iIndepFun (fun p : Nat.Primes ↦ fun n : ℕ ↦ n.factorization p.1)
      (zetaDist s hs).toMeasure := by
  let f : Nat.Primes → ℕ → ℕ := fun p n ↦ n.factorization p.1
  let π : Nat.Primes → Set (Set ℕ) :=
    fun p ↦ {u | ∃ t ∈ Set.range Set.Ici, Set.preimage (f p) t = u}
  rw [iIndepFun_iff_iIndep]
  refine iIndepSets.iIndep (m := fun p ↦ MeasurableSpace.comap (f p) inferInstance)
    (fun p ↦ le_top) π ?_ ?_ ?_
  · intro p
    exact isPiSystem_Ici.comap (f p)
  · intro p
    have hnat : (inferInstance : MeasurableSpace ℕ) =
        MeasurableSpace.generateFrom (Set.range Set.Ici) := by
      rw [← borel_eq_generateFrom_Ici ℕ, borel_eq_top_of_discrete]
      rfl
    rw [hnat, MeasurableSpace.comap_generateFrom]
    congr 1
  · rw [iIndepSets_iff]
    intro P sets hsets
    have hex : ∀ p : Nat.Primes, ∃ k : ℕ,
        p ∈ P → sets p = {n : ℕ | k ≤ n.factorization p.1} := by
      intro p
      by_cases hp : p ∈ P
      · rcases hsets p hp with ⟨t, ⟨k, rfl⟩, ht⟩
        exact ⟨k, fun _ ↦ ht.symm⟩
      · exact ⟨0, fun h ↦ (hp h).elim⟩
    choose k hk using hex
    rw [show (⋂ p ∈ P, sets p) =
        ⋂ p ∈ P, {n : ℕ | k p ≤ n.factorization p.1} by
      apply Set.iInter_congr
      intro p
      apply Set.iInter_congr
      intro hp
      exact hk p hp]
    rw [measure_iInter_factorization_ge s hs P k]
    apply Finset.prod_congr rfl
    intro p hp
    rw [hk p hp]

/-- Joint masses are products of the single-prime geometric masses. -/
theorem measure_iInter_factorization_eq (s : ℝ) (hs : 1 < s)
    (P : Finset Nat.Primes) (k : Nat.Primes → ℕ) :
    (zetaDist s hs).toMeasure (⋂ p ∈ P, {n : ℕ | n.factorization p.1 = k p}) =
      ∏ p ∈ P, ENNReal.ofReal
        ((1 - (p.1 : ℝ) ^ (-s)) * (p.1 : ℝ) ^ (-(k p : ℝ) * s)) := by
  let μ := (zetaDist s hs).toMeasure
  have h := (iIndepFun_factorization s hs).measure_inter_preimage_eq_mul
    P (sets := fun p : Nat.Primes ↦ ({k p} : Set ℕ))
    (fun p hp ↦ MeasurableSet.singleton (k p))
  calc
    μ (⋂ p ∈ P, {n : ℕ | n.factorization p.1 = k p}) =
        ∏ p ∈ P, μ {n : ℕ | n.factorization p.1 = k p} := by
      have heq (p : Nat.Primes) :
          (fun n : ℕ ↦ n.factorization p.1) ⁻¹' ({k p} : Set ℕ) =
            {n : ℕ | n.factorization p.1 = k p} := by
        ext n
        simp
      simpa only [heq] using h
    _ = ∏ p ∈ P, ENNReal.ofReal
        ((1 - (p.1 : ℝ) ^ (-s)) * (p.1 : ℝ) ^ (-(k p : ℝ) * s)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact measure_factorization_eq s hs p.1 (k p) p.2

end

end D5.S3.Analytic.Zeta.ZetaPrimeIndependence
