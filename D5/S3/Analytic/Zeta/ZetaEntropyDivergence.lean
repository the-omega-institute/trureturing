/- GID: D5/S3/Analytic/Zeta/ZetaEntropyDivergence
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeta entropy diverges at criticality; fixed-prime marginal entropies converge. -/

import Mathlib
/- Provenance: Native proof over pinned mathlib. -/
import D5.S3.Analytic.Zeta.EulerLogBridge

/- Search and proof receipt (2026-08-22).

   Generality.
   * Tag `I`. The applied H10 rule is `通用性头必填;标 G 者禁 import 实例事实`,
     enforced by SL-010. This file uses the particular repository `zetaDist`; its direct import
     is `I`, so a `G` restatement is forbidden and `I` is forced.

   Imports.
   * Repository imports, one by one through the closure: `EulerLogBridge.lean` (`I`, direct),
     `PrimeMarginalEntropy.lean` (`I`), `PrimeExponentLaw.lean` (`I`), `ZetaEntropy.lean` (`I`),
     and `ZetaGibbs.lean` (`I`). `Mathlib` is external and has no repository generality tag.

   Thinness, per theorem.
   * `expectedLog_zeta_nonneg` is THIN: it unfolds the expectation and applies termwise
     nonnegativity of PMF mass and `log n`.
   * The private partition/real-tsum conversion is THIN: it only commutes `toReal` with the
     ENNReal sum and rewrites negative real powers as reciprocals.
   * `log_tendsto_atTop_of_pos_simple_pole` is SUBSTANTIVE and naturally general: for arbitrary
     `f : ℝ → ℝ` and arbitrary positive residue `c`, a right-hand simple-pole limit forces
     `log ∘ f` to tend to `atTop`. No separate eventual-positivity hypothesis is needed: the
     positive residue limit supplies the positive factor used by `Tendsto.pos_mul_atTop`.
   * `partition_log_tendsto_atTop` is THIN: it specializes that generic theorem using the real
     right-filter zeta residue corollary and rewrites through `partition_toReal_eq_tsum_rpow`.
   * `zeta_entropy_tendsto_atTop` is THIN but load-bearing: `zeta_entropy_eq` plus the proved
     nonnegative energy term gives the comparison with the divergent log-partition function.
   * `primeExponent_entropy_tendsto_critical` is THIN: the imported closed marginal formula and
     continuity give a finite real limit for each fixed prime.
   * Finding 2 remains OVERTURNED: `partition_toReal_eq_tsum_rpow` is deliberately unchanged.
     The proposed general identity is only the two-line composition of `ENNReal.tsum_toReal_eq`
     and `ENNReal.toReal_ofReal`; extracting it would be a thin wrapper around upstream, and the
     obligation not to restate upstream outranks natural generality here.

   Attribute audit. Each declaration line was aligned with its source attribute line in the
   pinned repository, Mathlib, or Lean core. Generated additive declarations were traced to the
   source `to_additive` line rather than guessed.
   * Repository declarations `weight` (`ZetaGibbs.lean:19`), `partitionFunction` (31), `zetaDist`
     (55), `pmfReal` (`ZetaEntropy.lean:153`), `countableEntropy` (156), `expectedLog` (224),
     `zeta_entropy_eq` (260), `primeExponentPMF` (`PrimeMarginalEntropy.lean:168`), and
     `primeExponent_entropy_eq` (263) have no attribute line.
   * `tsum_nonneg` is generated from `one_le_tprod` (`InfiniteSum/Order.lean:169`) by the bare
     `@[to_additive tsum_nonneg]` on line 168, so it inherits no attribute. `tsum_congr` is
     generated from `tprod_congr` (`InfiniteSum/Basic.lean:471`) by bare `@[to_additive]` on 470
     and likewise inherits none.
   * `ENNReal.toReal_ofReal` (`Data/ENNReal/Basic.lean:244`) CARRIES `@[simp]` from line 243;
     `ENNReal.toReal_nonneg` (268) CARRIES inline `@[simp]`; `ENNReal.tsum_toReal_eq`
     (`InfiniteSum/ENNReal.lean:489`) carries none.
   * `Real.rpow_nonneg` (`Pow/Real.lean:163`) CARRIES `@[bound]` from 162. `Real.rpow_neg` (259),
     `Real.rpow_lt_one_of_one_lt_of_neg` (662), `Real.log_natCast_nonneg`
     (`Log/Basic.lean:224`), `Real.tendsto_log_atTop` (350), and
     `tendsto_sub_mul_tsum_nat_rpow` (`LSeries/RiemannZeta.lean:252`) carry none.
     `Real.continuous_const_rpow` (`Pow/Continuity.lean:228`) CARRIES `@[fun_prop]` from 227;
     `ContinuousAt.log` (`Log/Basic.lean:501`) CARRIES `@[fun_prop]` from 500.
   * `tendsto_nhdsWithin_iff` (`Topology/NhdsWithin.lean:462`), `self_mem_nhdsWithin` (144),
     `nhdsWithin_le_nhds` (182), `tendsto_const_nhds` (`Topology/Neighborhoods.lean:190`),
     `tendsto_id`, `Tendsto.congr'`, `Tendsto.comp`, and `Tendsto.mono_left`
     (`Order/Filter/Tendsto.lean:120,105,123,131`) carry none. `Eventually.of_forall`
     (`Order/Filter/Basic.lean:651`) also carries none. `tendsto_atTop_mono'`
     (`AtTopBot/Tendsto.lean:67`) CARRIES `@[to_dual]` from 66.
   * `sub_pos` is generated from `one_lt_div'` (`Order/Group/Unbundled/Basic.lean:604`) by
     `@[to_additive (attr := simp) sub_pos]` on 603 and CARRIES `@[simp]`. `sub_ne_zero` is
     generated from `div_ne_one` (`Algebra/Group/Basic.lean:753`) by bare `@[to_additive]` on 752
     and inherits none. `one_div` (`Algebra/Group/Defs.lean:1095`) CARRIES `@[simp]` from the
     `@[to_additive (attr := simp)]` line 1094.
   * `ne_of_gt` is generated from `ne_of_lt` (`Order/Defs/PartialOrder.lean:103`) by the named
     `@[to_dual ne_of_gt]` on 102 and inherits no additional attribute. `le_trans` (70) and
     `Nat.Prime.one_lt` (`Data/Nat/Prime/Defs.lean:77`) carry none. `zero_le_one`
     (`Algebra/Order/ZeroLEOne.lean:28`), `zero_lt_one` (51), and `Nat.cast_nonneg`
     (`Data/Nat/Cast/Order/Ring.lean:34`) each CARRY `@[simp]` from their declaration lines.
   * `Tendsto.sub` is generated from `Tendsto.div'` (`Topology/Algebra/Group/Defs.lean:141`)
     by bare `@[to_additive sub]` on 140 and inherits no attribute. `ContinuousAt.sub` is
     generated from `ContinuousAt.div'` (148) by `@[to_additive (attr := fun_prop) sub]` on 147,
     so it CARRIES `@[fun_prop]`. `ContinuousAt.neg` is generated from `ContinuousAt.inv` (85)
     by `@[to_additive (attr := fun_prop)]` on 84 and CARRIES `@[fun_prop]`.
   * `ContinuousAt.add` is generated from `ContinuousAt.mul` (`Monoid/Defs.lean:101`) through the
     line-100 nested `to_additive (attr := fun_prop)`, so the additive form CARRIES `@[fun_prop]`;
     the multiplicative declaration's source attribute is `@[to_fun ...]`. `ContinuousAt.div`
     (`GroupWithZero.lean:213`) carries none. `continuous_neg` is generated from the
     `ContinuousInv` class field (`Group/Defs.lean:50`) by
     `@[to_additive (attr := continuity)]` on 49 and CARRIES `@[continuity]`;
     `Continuous.comp`, `Continuous.continuousAt`, and `ContinuousAt.tendsto`
     (`Topology/Continuous.lean:113,149,57`) carry none.
     `continuousAt_const` and `continuousAt_id` (`Topology/Continuous.lean:157,172`) likewise
     carry none.
   * `Tendsto.pos_mul_atTop` (`Topology/Algebra/Order/Field.lean:48`) and
     `tendsto_inv_nhdsGT_zero` (61) carry none. Pinned core `mul_nonneg`
     (`Init/Grind/Ordered/Ring.lean:301`) carries none. Root `le_add_of_nonneg_left` is generated
     from `le_mul_of_one_le_left'` (`Algebra/Order/Monoid/Unbundled/Basic.lean:433`) by the exact
     source line `@[to_additive le_add_of_nonneg_left]` on 432. The explicit generated name is why
     no declaration line is grep-visible; with no `attr :=` clause, it inherits no attribute.
     This correction came from an `import Mathlib` probe, `#check @le_add_of_nonneg_left`, rather
     than from search; the probe resolved the root declaration with `AddZeroClass`, `LE`, and
     `AddRightMono`, distinct from the rejected Int-specific and tactic-ring declarations.
   * The pre-remediation exact-token audit recorded nonzero target-file hits for every declaration
     added above as previously missing: `countableEntropy` 8, `sub_pos` 2, `sub_ne_zero` 1,
     `ne_of_gt` 2, `zero_lt_one` 2, `zero_le_one` 1, `le_trans` 1, `cast_nonneg` 2, `one_div` 1,
     and the method occurrence `.one_lt` 1. No zero-hit candidate was reported or added.
   * UNRESOLVED policy used here: failed grep is never evidence of absence. The three relevant
     `@[to_additive]` forms were checked at their source attribute lines: bare propagation carries
     no attributes, `(attr := ...)` propagates exactly those attributes, and an explicit generated
     name can be structurally invisible to declaration-line grep. A name may be recorded
     UNRESOLVED only after `import Mathlib` plus `#check @<name>` actually fails. Applying that
     probe-first rule to every former UNRESOLVED entry leaves no UNRESOLVED entry in this receipt.
   * Pinned core supplies the closure axioms `propext` (`Init/Core.lean:1593`), `Quot.sound`
     (1789), and `Classical.choice` (`Init/Prelude.lean:816`); each is an axiom with no attribute
     line. No load-bearing theorem here is generated from a core `to_additive` declaration.

   * ADDED AFTER RE-REVIEW, measured by the coordinator rather than by the worker. A receipt seat
     found dot-notation aliases missing from the audit. Two of the three held and are recorded
     here; the third did not and is recorded as rejected. `LT.lt.le` does real work once, at
     `hs'.le`, and `LT.lt.trans` does real work once, at `zero_lt_one.trans`. NEITHER NAME OCCURS
     LITERALLY IN THIS FILE — dot notation resolves to them — so a spelling-based audit cannot
     reach them and they must be audited by resolved identity instead.
     `LT.lt.le` is declared by `@[to_dual self] alias LT.lt.le := le_of_lt`
     (`Mathlib/Order/Basic.lean:143`); the aliased body is `@[to_dual self] lemma le_of_lt`
     (`Mathlib/Order/Defs/PartialOrder.lean:82`). `LT.lt.trans` is declared by
     `@[to_dual trans'] alias LT.lt.trans := lt_trans` (`Mathlib/Order/Basic.lean:138`); the
     aliased body is the bare `lemma lt_trans` (`Mathlib/Order/Defs/PartialOrder.lean:100`).
     Neither carries `simp`. Note that all three attribute occurrences above sit ON THE SAME LINE
     as their declaration keyword, and that `alias` with a same-line attribute is a further form
     an audit must handle alongside the three `@[to_additive]` forms already on record.
     REJECTED, with the measurement that refutes it: the same seat reported `LT.lt.ne'` as a
     missing load-bearing declaration. Dot-notation `.ne'` occurs ZERO times in this file; what
     the proof uses is the literal `ne_of_gt`, five times, and the audit already covers it. A
     probe settles that these are different declarations rather than aliases of one another —
     `#print ne_of_gt` yields an independent theorem, `∀ {α} [Preorder α] {a b : α}, b < a →
     a ≠ b`, with its own proof term `fun h he => absurd h (he ▸ lt_irrefl a)`. `LT.lt.ne'` is
     therefore a distinct declaration that this file never invokes.
   Automation probe.
   * A fresh run-local scratch file tested each of the four original exported statements with
     `decide`, plain `simp`, `omega`, and `norm_num`; none closed.
   * Single-lemma `simp` also failed to close expected-log nonnegativity with each of
     `Real.log_natCast_nonneg`, `ENNReal.toReal_nonneg`, and `tsum_nonneg`; partition-log
     divergence with each of `tendsto_sub_mul_tsum_nat_rpow`, `ENNReal.tsum_toReal_eq`,
     `Real.rpow_neg`, `tendsto_inv_nhdsGT_zero`, and `Real.tendsto_log_atTop`; entropy divergence
     with each of `zeta_entropy_eq`, `expectedLog_zeta_nonneg`,
     `partition_log_tendsto_atTop`, and `tendsto_atTop_mono'`; and fixed-prime convergence with
     each of `primeExponent_entropy_eq`, `Real.continuous_const_rpow`, `ContinuousAt.log`, and
     `ContinuousAt.div`. Every cited name resolved. The probe compiled with exit zero and was
     deleted.

   Candidates inspected versus declarations doing real work.
   * Inspected only: `riemannZeta_residue_one`,
     `ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right`,
     `partition_function_toReal_eq_riemannZeta`, `log_partitionFunction_eq_tsum_prime`, the
     repository zeta/zero residue wrappers, and generic at-top comparison lemmas. The first four
     are viable routes, but the already-real residue corollary is shorter.
   * Real work: `tendsto_sub_mul_tsum_nat_rpow`, the ENNReal/real sum conversions,
     `tendsto_inv_nhdsGT_zero`, `Tendsto.pos_mul_atTop`, `Real.tendsto_log_atTop`,
     `zeta_entropy_eq`, the PMF/log positivity lemmas, `primeExponent_entropy_eq`, and real-rpow,
     log, and division continuity.

   Search provenance.
   * SUPPLIED BY THE DISPATCHER: case-sensitive patterns `tendsto.*zetaDist`,
     `riemannZeta_residue`, `zeta_entropy_tendsto`, and `primeCounting` returned zero files under
     `D5/S3/Analytic/`, while `vonMangoldt` returned two; Mathlib has no Shannon-entropy API and
     `InformationTheory/` contains only Hamming, Coding, and Kullback-Leibler modules; the real
     residue theorem and the partition/zeta bridge were suggested; the directory had five direct
     Lean files and room below the split threshold.
   * Independently verified in the repository: the four zero counts and exactly the two
     `vonMangoldt` files (`ZetaEntropy.lean`, `PrimeMarginalEntropy.lean`); five direct pre-existing
     `Zeta/` files; and a mathematical-content search over all `D5/` found no zeta entropy limit.
     Case-insensitive residue search also found `completedRiemannZeta_residue_one` in
     `CompletedZetaMellinReconstruction.lean`; it was rejected as a different declaration and is
     why the supplied case-sensitive conclusion is not reported as a broader absence.
   * Independently verified in pinned Mathlib: `riemannZeta_residue_one` is exactly the punctured
     complex limit at `RiemannZeta.lean:239`; its real right-filter corollary is exactly
     `tendsto_sub_mul_tsum_nat_rpow` at 252; the six `InformationTheory/` files are precisely the
     supplied layout, with only descriptive Shannon mentions elsewhere. Independently searched
     pinned Lean core for zeta, Shannon/countable entropy, prime-counting, and von Mangoldt subject
     names: zero hits.

   Ranked stopping point.
   * Ranked scopes 1, 2, 3, and 4 are COMPLETE. Scope 4 is delivered as convergence to an explicit
     finite real value, which is stronger than the requested boundedness companion. Nothing in
     scopes 1-3 is stronger than requested except the harmless explicit right-filter restriction
     used to manage the dependent proof argument. `#print axioms` reports exactly
     `{propext, Classical.choice, Quot.sound}` for the four original public theorems and the new
     generic pole theorem. -/

namespace D5.S3.Analytic.Zeta.ZetaEntropyDivergence

open scoped ENNReal BigOperators Topology
open Filter Set
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy
open D5.S3.Analytic.Zeta.PrimeMarginalEntropy

noncomputable section

/-- Logarithmic energy is nonnegative under the zeta law. -/
theorem expectedLog_zeta_nonneg (s : ℝ) (hs : 1 < s) :
    0 ≤ expectedLog (zetaDist s hs) := by
  rw [expectedLog]
  exact tsum_nonneg fun n =>
    mul_nonneg ENNReal.toReal_nonneg (Real.log_natCast_nonneg n)

private lemma partition_toReal_eq_tsum_rpow (s : ℝ) :
    (partitionFunction s).toReal = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  rw [partitionFunction, ENNReal.tsum_toReal_eq (fun n => by simp [weight])]
  apply tsum_congr
  intro n
  rw [weight, ENNReal.toReal_ofReal (Real.rpow_nonneg n.cast_nonneg _),
    Real.rpow_neg n.cast_nonneg]
  simp only [one_div]

/-- A positive simple pole at `1` forces logarithmic divergence from the right. -/
theorem log_tendsto_atTop_of_pos_simple_pole (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hprod : Tendsto (fun s : ℝ => (s - 1) * f s) (nhdsWithin 1 (Ioi 1)) (𝓝 c)) :
    Tendsto (fun s : ℝ => Real.log (f s)) (nhdsWithin 1 (Ioi 1)) atTop := by
  have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    have hcont : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
      tendsto_id.sub (tendsto_const_nhds (x := (1 : ℝ)))
    have hcont' : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 0) := by
      simpa using hcont.mono_left
        (nhdsWithin_le_nhds : (𝓝[>] (1 : ℝ)) ≤ 𝓝 1)
    refine tendsto_nhdsWithin_iff.mpr ⟨hcont', ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_pos.mpr (show (1 : ℝ) < s from hs)
  have hinv : Tendsto (fun s : ℝ => (s - 1)⁻¹) (𝓝[>] 1) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  have hf : Tendsto f (𝓝[>] 1) atTop := by
    apply (hprod.pos_mul_atTop hc hinv).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (show 1 < s from hs))
    field_simp [hne]
  exact Real.tendsto_log_atTop.comp hf

/-- The logarithm of the zeta partition function diverges as `s` decreases to `1`. -/
theorem partition_log_tendsto_atTop :
    Tendsto (fun s : ℝ => Real.log (partitionFunction s).toReal)
      (nhdsWithin 1 (Ioi 1)) atTop := by
  let Z : ℝ → ℝ := fun s => ∑' n : ℕ, 1 / (n : ℝ) ^ s
  have hprod : Tendsto (fun s : ℝ => (s - 1) * Z s) (𝓝[>] 1) (𝓝 1) := by
    simpa only [Z] using tendsto_sub_mul_tsum_nat_rpow
  simpa only [Z, partition_toReal_eq_tsum_rpow] using
    log_tendsto_atTop_of_pos_simple_pole Z 1 zero_lt_one hprod

/-- The zeta law's Shannon entropy diverges as the inverse temperature decreases to `1`.
The `dite` is an arbitrary extension off the right-hand domain and is ignored by the filter. -/
theorem zeta_entropy_tendsto_atTop :
    Tendsto
      (fun s : ℝ => if hs : 1 < s then countableEntropy (zetaDist s hs) else 0)
      (nhdsWithin 1 (Ioi 1)) atTop := by
  apply tendsto_atTop_mono' _ ?_ partition_log_tendsto_atTop
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < s := hs
  rw [show (if hs : 1 < s then countableEntropy (zetaDist s hs) else 0) =
      countableEntropy (zetaDist s hs') by simp [hs']]
  rw [zeta_entropy_eq s hs']
  exact le_add_of_nonneg_left
    (mul_nonneg (le_trans zero_le_one hs'.le) (expectedLog_zeta_nonneg s hs'))

/-- Each fixed prime marginal has a finite entropy limit at the critical temperature. -/
theorem primeExponent_entropy_tendsto_critical (p : Nat.Primes) :
    Tendsto
      (fun s : ℝ => if hs : 1 < s then
        countableEntropy (primeExponentPMF s hs p) else 0)
      (nhdsWithin 1 (Ioi 1))
      (𝓝 (-Real.log (1 - (p.1 : ℝ) ^ (-(1 : ℝ))) +
        Real.log p.1 * ((p.1 : ℝ) ^ (-(1 : ℝ)) /
          (1 - (p.1 : ℝ) ^ (-(1 : ℝ)))))) := by
  let F : ℝ → ℝ := fun s =>
    -Real.log (1 - (p.1 : ℝ) ^ (-s)) +
      s * Real.log p.1 * ((p.1 : ℝ) ^ (-s) / (1 - (p.1 : ℝ) ^ (-s)))
  have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  let q : ℝ → ℝ := fun s => (p.1 : ℝ) ^ (-s)
  have hq : Continuous q :=
    (Real.continuous_const_rpow (ne_of_gt (zero_lt_one.trans hpR))).comp continuous_neg
  have hden : 1 - (p.1 : ℝ) ^ (-(1 : ℝ)) ≠ 0 := by
    exact (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hpR (by norm_num))).ne'
  have hF : ContinuousAt F 1 := by
    dsimp [F]
    have hqAt : ContinuousAt (fun s : ℝ => (p.1 : ℝ) ^ (-s)) 1 := by
      simpa only [q] using hq.continuousAt
    have hd : ContinuousAt (fun s : ℝ => 1 - (p.1 : ℝ) ^ (-s)) 1 :=
      continuousAt_const.sub hqAt
    exact (hd.log hden).neg.add
      ((continuousAt_id.mul continuousAt_const).mul (hqAt.div hd hden))
  have hlim : Tendsto F (nhdsWithin 1 (Ioi 1)) (𝓝 (F 1)) :=
    hF.tendsto.mono_left nhdsWithin_le_nhds
  have heq : F =ᶠ[nhdsWithin 1 (Ioi 1)]
      (fun s : ℝ => if hs : 1 < s then
        countableEntropy (primeExponentPMF s hs p) else 0) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < s := hs
    rw [show (if hs : 1 < s then countableEntropy (primeExponentPMF s hs p) else 0) =
        countableEntropy (primeExponentPMF s hs' p) by simp [hs']]
    rw [primeExponent_entropy_eq s hs' p]
  have hlim' : Tendsto
      (fun s : ℝ => if hs : 1 < s then
        countableEntropy (primeExponentPMF s hs p) else 0)
      (nhdsWithin 1 (Ioi 1)) (𝓝 (F 1)) := hlim.congr' heq
  simpa [F] using hlim'

end

end D5.S3.Analytic.Zeta.ZetaEntropyDivergence
