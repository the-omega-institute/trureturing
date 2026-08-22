/- GID: D5/S3/Analytic/Zeta/EulerLogBridge
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Real Euler-log and prime-energy bridges for the zeta distribution. -/

import Mathlib
/- Provenance: Native proof over pinned mathlib. -/
import D5.S3.Analytic.Zeta.PrimeMarginalEntropy
/- Search and proof receipt (2026-08-22).
   Generality and imports. Tag `I`; applied rule H10 is `通用性头必填;标 G 者禁 import
   实例事实`, enforced by SL-010. The direct repository import
   `D5/S3/Analytic/Zeta/PrimeMarginalEntropy.lean` is `I`, hence `I` is forced.
   Its repository import closure, listed one by one, is `PrimeExponentLaw.lean` (`I`),
   `ZetaEntropy.lean` (`I`), and `ZetaGibbs.lean` (`I`). `Mathlib` is external.
   Thinness, per exported theorem. Inherited Bridge A, `log_partitionFunction_eq_tsum_prime`,
   is SUBSTANTIVE: it proves real summability and transports the complex Euler product through
   real logarithms. New Bridge B, `expectedLog_eq_tsum_prime`, is SUBSTANTIVE: finite-support
   rows plus zeta log-moment summability establish a nonnegative product series before the
   Tonelli exchange. `countableEntropy_zeta_eq_tsum_prime` is THIN: it combines both bridges,
   `zeta_entropy_eq`, and `primeExponent_entropy_eq`; its summability step only licenses
   `tsum_add`. Private map, expectation, and factorization helpers make no public strengthening.
   Attribute audit. The declaration line was aligned with its immediately preceding attribute
   line in both pinned trees; generated additive declarations were traced through `to_additive`.
   Declarations in this file carry no attributes. Repository declarations `summable_real_weight`
   (`ZetaGibbs.lean:35`), `partition_function_toReal_eq_riemannZeta` (64), `pmfReal`
   (`ZetaEntropy.lean:153`), `pmfReal_summable` (159), `summable_log_weight` (170),
   `zeta_real_apply` (192), `expectedLog` (224), `zeta_entropy_eq` (260),
   `primeExponentPMF_apply` (`PrimeMarginalEntropy.lean:174`), `primeExponentPMF_eq_map` (183),
   `primeExponent_entropy_eq` (263), and `summable_primeExponent_entropy` (274) carry none.
   * `riemannZeta_eulerProduct_exp_log` (`DirichletLSeries.lean:160`),
     `Real.log_nat_eq_sum_factorization` (`Log/Basic.lean:430`), `Real.log_natCast_nonneg` (224),
     `Real.log_le_sub_one_of_pos` (306), `Complex.ofReal_log` (`Complex/Log.lean:71`),
     `Complex.ofReal_cpow` (`Pow/Real.lean:282`), and both differentiated-geometric results
     (`SpecificLimits/Normed.lean:541,547`) carry none. `Real.log_inv` (142) and `Real.log_exp`
     (74) CARRY `@[simp, push]`; `Real.log_nonpos` (221) CARRIES `@[bound]`.
   * `Real.rpow_pos_of_pos` (`Pow/Real.lean:116`) and `Real.rpow_nonneg` (163) CARRY
     `@[bound]`; `Real.rpow_le_rpow_of_exponent_le` (613) CARRIES `@[gcongr]`;
     `Real.rpow_neg_one` (471) and `Real.rpow_lt_one_of_one_lt_of_neg` (662) carry none.
     `inv_anti₀` (`GroupWithZero/Basic.lean:1226`) CARRIES `@[gcongr, bound]`.
     `Real.rpow_natCast` (`Pow/Real.lean:62`) CARRIES `@[simp, norm_cast]`; `Real.rpow_mul`
     (412) carries none; `Real.norm_eq_abs` (`Normed/Group/Real.lean:56`) CARRIES `@[simp]`.
     Exact-name searches in both trees left root `abs_of_pos` UNRESOLVED; same-named
     `HasFDerivAt.abs_of_pos` declarations were REJECTED as different declarations.
   * `Complex.ofReal_exp` (`Complex/Exponential.lean:189`) CARRIES `@[simp, norm_cast]`;
     `Complex.ofReal_tsum` (`Complex/Basic.lean:604`) CARRIES `@[norm_cast]`;
     `Complex.ofReal_injective` (`Data/Complex/Basic.lean:102`) carries none, while
     `ofReal_one` (155), `ofReal_neg` (192), and `ofReal_sub` (648) CARRY `@[simp, norm_cast]`.
   * `PMF.map_apply` (`ProbabilityMassFunction/Constructions.lean:54`) CARRIES `@[simp]`;
     `PMF.apply_ne_top` (`Basic.lean:125`) and `ENNReal.tsum_toReal_eq`
     (`InfiniteSum/ENNReal.lean:489`) carry none; `ENNReal.toReal_nonneg`
     (`Data/ENNReal/Basic.lean:268`) CARRIES `@[simp]`. `Finsupp.mem_support_iff`
     (`Data/Finsupp/Defs.lean:156`) CARRIES `@[simp, grind =]`; `Nat.support_factorization`
     (`Factorization/Defs.lean:56`) CARRIES `@[simp]`; `Nat.prime_of_mem_primeFactors`
     (`Nat/PrimeFin.lean:62`) carries none.
   * `Summable.of_nonneg_of_le` (`InfiniteSum/ENNReal.lean:530`),
     `summable_prod_of_nonneg` (`InfiniteSum/Real.lean:80`), `Summable.mul_left`,
     `Summable.tsum_mul_left` (`InfiniteSum/Ring.lean:45,55`), `summable_mul_left_iff` (106),
     and `tsum_mul_left` (115) carry none. `Summable.congr`, `Summable.add`, `Summable.sub`,
     `Summable.tsum_add`, `Summable.comp_injective`, `summable_of_ne_finset_zero`,
     `Summable.tsum_comm`, `tsum_eq_single`, `tsum_eq_sum`, and `tsum_subtype` are generated
     from bare `@[to_additive]` sources at `Basic.lean:74-76,328-329,715-716,494-495,456-457,
     588-589`, `Group.lean:58-59,292-293`, `Defs.lean:300-301`, and
     `Constructions.lean:260-263`; none inherits an attribute.
   * ADDED AFTER REVIEW, measured by the coordinator rather than by the worker. An adversarial
     receipt seat found four load-bearing declarations absent from the audit above; each was
     re-measured line by line against the pinned tree before being recorded here. `tsum_congr`
     does repeated work at seven sites in this file and is generated from `tprod_congr`
     (`Topology/Algebra/InfiniteSum/Basic.lean:471`, attribute line 470 a bare
     `@[to_additive]`); it inherits no attribute. `Finsupp.sum` is generated from `Finsupp.prod`
     (`Algebra/BigOperators/Finsupp/Basic.lean:48`, attribute line 47 a `@[to_additive]`
     carrying only a docstring); it inherits no attribute. `Subtype.coe_injective`
     (`Data/Subtype.lean:80`, line 79 blank) carries none. `Finset.sum_congr` is the one
     correction of substance: it is generated from `Finset.prod_congr`
     (`Algebra/BigOperators/Group/Finset/Basic.lean:104`) whose attribute line 103 reads
     `@[to_additive (attr := congr)]`, NOT a bare `@[to_additive]`, so the additive form
     CARRIES `@[congr]`. That is precisely the indirectly inherited attribute this audit is
     required to surface, and the original audit missed it.
   * Pinned Lean core was separately audited: no load-bearing series, zeta, factorization, or
     entropy declaration was found. `propext` (`Init/Core.lean:1593`), `Quot.sound` (1789),
     and `Classical.choice` (`Init/Prelude.lean:816`) are axioms with no attribute line.
   Automation probe. A fresh run-local file tested all three exported statements with closure
   probes for `decide`, plain `simp`, `omega`, and `norm_num`; all failed to close. Single-lemma
   `simp` also failed for Bridge A with `riemannZeta_eulerProduct_exp_log`,
   `partition_function_toReal_eq_riemannZeta`, and `Real.log_exp`; for Bridge B with reverse
   `Real.log_nat_eq_sum_factorization` (forward simp recurses), `summable_prod_of_nonneg`,
   `Summable.tsum_comm`, and `summable_log_weight`; and for the payoff with `zeta_entropy_eq`,
   `primeExponent_entropy_eq`, and `summable_primeExponent_entropy`. Every name resolved.
   The probe compiled with exit zero and was deleted.
   Candidates inspected (not claimed to do real work): all four zeta Euler-product declarations,
   `EulerProduct/Basic.lean`, ENNReal Tonelli, measure-theoretic Tonelli, `tsum_subtype`, and the
   repository independence/cylinder laws. Declarations doing real work: the complex exp-log
   Euler product and real/complex log conversions for A; finite factorization support,
   `summable_log_weight`, `summable_prod_of_nonneg`, and `Summable.tsum_comm` for B; the two
   imported entropy formulas and justified summable `tsum` rewrites for the payoff.
   Search provenance and stopping point. SUPPLIED BY THE DISPATCHER: the four pinned zeta Euler
   theorems are complex-valued at lines 89,96,102,160; `EulerProduct/Basic.lean` has no real-log
   form; Mathlib has no Shannon entropy and `InformationTheory/` has only Hamming, Coding, and
   KullbackLeibler; and `Real.log_nat_eq_sum_factorization` is pointwise, not the exchange.
   Independently verified in pinned Mathlib: those four signatures use `ℂ`; the Basic search
   returned no real-log hit; the six InformationTheory files are exactly those supplied, with
   only descriptive Shannon hits elsewhere. Independently searched pinned Lean core for the
   same zeta/Euler, entropy/PMF, factorization, Tonelli, and `tsum_comm` names: zero hits.
   Ranked scope reached Bridge B and then the payoff, both COMPLETE. No extra hypothesis, finite
   surrogate, hidden convergence premise, or stronger-than-requested public result was added.
   `#print axioms` gives exactly `{propext, Classical.choice, Quot.sound}` for each theorem. -/
namespace D5.S3.Analytic.Zeta.EulerLogBridge
open scoped ENNReal BigOperators
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy
noncomputable section
private lemma summable_prime_eulerLog (s : ℝ) (hs : 1 < s) :
    Summable (fun p : Nat.Primes ↦ -Real.log (1 - (p.1 : ℝ) ^ (-s))) := by
  have hq : Summable (fun p : Nat.Primes ↦ (p.1 : ℝ) ^ (-s)) :=
    (summable_real_weight s hs).comp_injective Subtype.coe_injective
  apply Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_) (hq.mul_left 2)
  · have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
    have hq0 : 0 ≤ (p.1 : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
    have hq1 : (p.1 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
    exact neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr hq1).le (by linarith))
  · let q : ℝ := (p.1 : ℝ) ^ (-s)
    have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
    have hq0 : 0 < q := Real.rpow_pos_of_pos (by positivity) _
    have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
    have hqhalf : q ≤ (2 : ℝ)⁻¹ := by
      calc
        q ≤ (p.1 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hpR.le (by linarith)
        _ = (p.1 : ℝ)⁻¹ := Real.rpow_neg_one _
        _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by exact_mod_cast p.2.two_le)
    have ha : 0 < 1 - q := sub_pos.mpr hq1
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
    rw [Real.log_inv] at h
    dsimp [q] at hqhalf ha h ⊢
    calc
      -Real.log (1 - (p.1 : ℝ) ^ (-s)) ≤
          (1 - (p.1 : ℝ) ^ (-s))⁻¹ - 1 := h
      _ = (p.1 : ℝ) ^ (-s) / (1 - (p.1 : ℝ) ^ (-s)) := by
        field_simp [ha.ne']
        ring
      _ ≤ 2 * (p.1 : ℝ) ^ (-s) := by
        rw [div_le_iff₀ ha]
        nlinarith

/-- The real logarithm of the zeta partition function is the sum of its prime Euler logs. -/
theorem log_partitionFunction_eq_tsum_prime (s : ℝ) (hs : 1 < s) :
    Real.log (partitionFunction s).toReal =
      ∑' p : Nat.Primes, -Real.log (1 - (p.1 : ℝ) ^ (-s)) := by
  let a : Nat.Primes → ℝ := fun p ↦ -Real.log (1 - (p.1 : ℝ) ^ (-s))
  have ha : Summable a := summable_prime_eulerLog s hs
  have hterm (p : Nat.Primes) :
      -Complex.log (1 - (p.1 : ℂ) ^ (-(s : ℂ))) = (a p : ℂ) := by
    have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
    have hq1 : (p.1 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
    have hbase : 0 ≤ 1 - (p.1 : ℝ) ^ (-s) := (sub_pos.mpr hq1).le
    have hpow : (p.1 : ℂ) ^ (-(s : ℂ)) =
        ((↑((p.1 : ℝ) ^ (-s)) : ℂ)) := by
      calc
        (p.1 : ℂ) ^ (-(s : ℂ)) = (p.1 : ℂ) ^ ((-s : ℝ) : ℂ) := by
          rw [Complex.ofReal_neg]
        _ = ((↑((p.1 : ℝ) ^ (-s)) : ℂ)) :=
          (Complex.ofReal_cpow (by positivity) (-s)).symm
    dsimp [a]
    rw [hpow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_log hbase, ← Complex.ofReal_neg]
  have hEuler := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) (by simpa using hs)
  have hexp : Real.exp (∑' p, a p) = (partitionFunction s).toReal := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_exp, Complex.ofReal_tsum]
    simpa only [hterm] using hEuler.trans
      (partition_function_toReal_eq_riemannZeta s hs).symm
  rw [← hexp, Real.log_exp]

private lemma pmfReal_map_apply (P : PMF ℕ) (f : ℕ → ℕ) (k : ℕ) :
    pmfReal (P.map f) k = ∑' n, if k = f n then pmfReal P n else 0 := by
  rw [pmfReal, PMF.map_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro n
    split_ifs <;> simp [pmfReal]
  · intro n
    split_ifs
    · exact P.apply_ne_top n
    · exact ENNReal.zero_ne_top

private lemma expected_factorization_eq (s : ℝ) (hs : 1 < s) (p : Nat.Primes) :
    ∑' n : ℕ, pmfReal (zetaDist s hs) n * (n.factorization p.1 : ℝ) =
      (p.1 : ℝ) ^ (-s) / (1 - (p.1 : ℝ) ^ (-s)) := by
  let q : ℝ := (p.1 : ℝ) ^ (-s)
  let P := primeExponentPMF s hs p
  let f : ℕ → ℕ := fun n ↦ n.factorization p.1
  have hq0 : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have habs : |q| < 1 := by simpa [abs_of_pos hq0] using hq1
  have hP (k : ℕ) : pmfReal P k = (1 - q) * q ^ k := by
    dsimp [P, q]
    rw [primeExponentPMF_apply]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul
      (by positivity : 0 ≤ (p.1 : ℝ))]
    congr 1
    ring
  have hweighted : Summable (fun k : ℕ ↦ (k : ℝ) * pmfReal P k) := by
    apply ((hasSum_coe_mul_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs] using habs)).summable.mul_left (1 - q)).congr
    intro k
    rw [hP]
    ring
  have hmap (k : ℕ) : pmfReal P k =
      ∑' n, if k = f n then pmfReal (zetaDist s hs) n else 0 := by
    rw [show P = (zetaDist s hs).map f by
      exact primeExponentPMF_eq_map s hs p]
    exact pmfReal_map_apply _ _ _
  let g : ℕ × ℕ → ℝ := fun kn ↦
    (kn.1 : ℝ) * if kn.1 = f kn.2 then pmfReal (zetaDist s hs) kn.2 else 0
  have hg0 : ∀ kn, 0 ≤ g kn := by
    intro kn
    dsimp [g]
    exact mul_nonneg (Nat.cast_nonneg _) (by
      split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl)
  have hmassfiber (k : ℕ) : Summable
      (fun n ↦ if k = f n then pmfReal (zetaDist s hs) n else 0) := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ by
        split_ifs
        · exact ENNReal.toReal_nonneg
        · exact le_rfl)
      (fun n ↦ ?_) (pmfReal_summable (zetaDist s hs))
    split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  have hfiber (k : ℕ) : Summable (fun n ↦ g (k, n)) := by
    change Summable (fun n ↦ (k : ℝ) *
      if k = f n then pmfReal (zetaDist s hs) n else 0)
    exact (hmassfiber k).mul_left (k : ℝ)
  have hg : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨hfiber, ?_⟩
    apply hweighted.congr
    intro k
    rw [hmap]
    change (k : ℝ) * (∑' n, if k = f n then pmfReal (zetaDist s hs) n else 0) =
      ∑' n, g (k, n)
    exact (hmassfiber k).tsum_mul_left (k : ℝ) |>.symm
  have hg' : Summable (Function.uncurry (fun k n : ℕ ↦
      (k : ℝ) * if k = f n then pmfReal (zetaDist s hs) n else 0)) := by
    change Summable g
    exact hg
  have hswap := hg'.tsum_comm
  have hmean : (∑' k : ℕ, (k : ℝ) * pmfReal P k) =
      q / (1 - q) := by
    simp_rw [hP]
    rw [show (fun k : ℕ ↦ (k : ℝ) * ((1 - q) * q ^ k)) =
        fun k : ℕ ↦ (1 - q) * ((k : ℝ) * q ^ k) by funext k; ring]
    rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one
      (by simpa [Real.norm_eq_abs] using habs)]
    field_simp [(sub_pos.mpr hq1).ne']
  calc
    ∑' n : ℕ, pmfReal (zetaDist s hs) n * (f n : ℝ) =
        ∑' n : ℕ, ∑' k : ℕ,
          (k : ℝ) * if k = f n then pmfReal (zetaDist s hs) n else 0 := by
            apply tsum_congr
            intro n
            rw [tsum_eq_single (f n)]
            · simp [mul_comm]
            · intro k hk
              simp [hk]
    _ = ∑' k : ℕ, ∑' n : ℕ,
          (k : ℝ) * if k = f n then pmfReal (zetaDist s hs) n else 0 := hswap
    _ = ∑' k : ℕ, (k : ℝ) *
          (∑' n, if k = f n then pmfReal (zetaDist s hs) n else 0) := by
            apply tsum_congr
            intro k
            exact (hmassfiber k).tsum_mul_left (k : ℝ)
    _ = ∑' k : ℕ, (k : ℝ) * pmfReal P k := by
          apply tsum_congr
          intro k
          rw [hmap]
    _ = q / (1 - q) := hmean
    _ = (p.1 : ℝ) ^ (-s) / (1 - (p.1 : ℝ) ^ (-s)) := by rfl

private lemma tsum_prime_factorization_log (n : ℕ) :
    ∑' p : Nat.Primes, (n.factorization p.1 : ℝ) * Real.log p.1 = Real.log n := by
  rw [Real.log_nat_eq_sum_factorization]
  change (∑' p : ↑({p : ℕ | p.Prime} : Set ℕ),
    (n.factorization p.1 : ℝ) * Real.log p.1) = _
  have hsub := tsum_subtype ({p : ℕ | p.Prime} : Set ℕ)
    (fun p ↦ (n.factorization p : ℝ) * Real.log p)
  rw [hsub]
  rw [tsum_eq_sum (s := n.factorization.support)]
  · rw [Finsupp.sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by
      simpa [Nat.support_factorization] using hp)
    simp [Set.indicator, hprime]
  · intro p hp
    have hz : n.factorization p = 0 := by
      by_contra hne
      exact hp (Finsupp.mem_support_iff.mpr hne)
    by_cases hprime : p.Prime
    · simp [Set.indicator, hprime, hz]
    · simp [Set.indicator, hprime]

/-- Expected logarithmic energy is the sum of the expected prime-coordinate energies. -/
theorem expectedLog_eq_tsum_prime (s : ℝ) (hs : 1 < s) :
    expectedLog (zetaDist s hs) =
      ∑' p : Nat.Primes, Real.log p.1 *
        ((p.1 : ℝ) ^ (-s) / (1 - (p.1 : ℝ) ^ (-s))) := by
  let P := zetaDist s hs
  let g : ℕ × Nat.Primes → ℝ := fun np ↦
    pmfReal P np.1 * ((np.1.factorization np.2.1 : ℝ) * Real.log np.2.1)
  have hg0 : ∀ np, 0 ≤ g np := by
    intro np
    exact mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  have hfactor (n : ℕ) : Summable (fun p : Nat.Primes ↦
      (n.factorization p.1 : ℝ) * Real.log p.1) := by
    have hnat : Summable (fun p : ℕ ↦
        (n.factorization p : ℝ) * Real.log p) := by
      apply summable_of_ne_finset_zero (s := n.factorization.support)
      intro p hp
      have hz : n.factorization p = 0 := by
        by_contra hne
        exact hp (Finsupp.mem_support_iff.mpr hne)
      simp [hz]
    exact hnat.comp_injective Subtype.coe_injective
  have henergy : Summable (fun n : ℕ ↦ pmfReal P n * Real.log n) := by
    apply ((summable_log_weight s hs).mul_left
      (partitionFunction s).toReal⁻¹).congr
    intro n
    dsimp [P]
    rw [zeta_real_apply]
    ring
  have hg : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨fun n ↦ ?_, ?_⟩
    · exact (hfactor n).mul_left (pmfReal P n)
    · apply henergy.congr
      intro n
      dsimp [g]
      rw [(hfactor n).tsum_mul_left, tsum_prime_factorization_log]
  have hg' : Summable (Function.uncurry (fun n : ℕ ↦ fun p : Nat.Primes ↦
      pmfReal P n * ((n.factorization p.1 : ℝ) * Real.log p.1))) := by
    change Summable g
    exact hg
  have hswap := hg'.tsum_comm
  rw [expectedLog]
  change (∑' n : ℕ, pmfReal P n * Real.log n) = _
  calc
    ∑' n : ℕ, pmfReal P n * Real.log n = ∑' n : ℕ, ∑' p : Nat.Primes, g (n, p) := by
      apply tsum_congr
      intro n
      dsimp [g]
      rw [(hfactor n).tsum_mul_left, tsum_prime_factorization_log]
    _ = ∑' p : Nat.Primes, ∑' n : ℕ, g (n, p) := hswap.symm
    _ = ∑' p : Nat.Primes, Real.log p.1 *
        ((p.1 : ℝ) ^ (-s) / (1 - (p.1 : ℝ) ^ (-s))) := by
      apply tsum_congr
      intro p
      dsimp [g]
      rw [show (fun n : ℕ ↦ pmfReal P n *
          ((n.factorization p.1 : ℝ) * Real.log p.1)) =
          fun n : ℕ ↦ Real.log p.1 *
            (pmfReal P n * (n.factorization p.1 : ℝ)) by
        funext n
        ring]
      rw [tsum_mul_left]
      dsimp [P]
      rw [expected_factorization_eq]

/-- The entropy of the zeta distribution is the sum of its prime-coordinate entropies. -/
theorem countableEntropy_zeta_eq_tsum_prime (s : ℝ) (hs : 1 < s) :
    countableEntropy (zetaDist s hs) =
      ∑' p : Nat.Primes, countableEntropy (primeExponentPMF s hs p) := by
  let e : Nat.Primes → ℝ := fun p ↦
    Real.log p.1 * ((p.1 : ℝ) ^ (-s) / (1 - (p.1 : ℝ) ^ (-s)))
  let a : Nat.Primes → ℝ := fun p ↦
    -Real.log (1 - (p.1 : ℝ) ^ (-s))
  have ha : Summable a := summable_prime_eulerLog s hs
  have hse : Summable (fun p ↦ s * e p) := by
    apply (summable_primeExponent_entropy s hs).sub ha |>.congr
    intro p
    rw [primeExponent_entropy_eq s hs p]
    dsimp [a, e]
    ring
  have hs0 : s ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have he : Summable e := (summable_mul_left_iff hs0).mp hse
  rw [zeta_entropy_eq s hs, expectedLog_eq_tsum_prime s hs,
    log_partitionFunction_eq_tsum_prime s hs]
  change s * (∑' p, e p) + ∑' p, a p = _
  rw [← he.tsum_mul_left s]
  calc
    (∑' p, s * e p) + ∑' p, a p =
        ∑' p, (a p + s * e p) := by
          rw [add_comm, (ha.tsum_add hse).symm]
    _ = ∑' p : Nat.Primes, countableEntropy (primeExponentPMF s hs p) := by
      apply tsum_congr
      intro p
      rw [primeExponent_entropy_eq s hs p]
      dsimp [a, e]
      ring

end

end D5.S3.Analytic.Zeta.EulerLogBridge
