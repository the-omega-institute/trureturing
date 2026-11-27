/- GID: D5/S3/Zeros/GRH/New/Curve/KatzDivisibility
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/KatzDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.KatzDivisibility. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/KatzDivisibility.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.CM.LocalHeight.EulerAdditionFormula
import D5.S3.Zeros.GRH.New.Curve.FormalParameter
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known results stated on this proof's data: Sharpness of Katz's divisibility for invariant
derivatives on a CM formal group (known result; see Lib.General.Algebra.DepthBounds).

This file: Sharpness of Katz's divisibility, by a multiplicative inequality between jets. -/

open Nat Finset IsLocalRing PowerSeries Real

/-- A limit to Katz's divisibility of jets (superadditivity). For d a prime ≡ 7 mod 8, every prime
p, ring map ι : ℂ → ℂ_p and n, some f ∈ 𝔬[[φ]] has |f⁽ⁿ⁾(0)|_p ≥ p^{(ρ_p − 1/(p−1))n}.

Known result: Sharpness of Katz's divisibility for invariant derivatives on a CM formal group. -/
lemma CMLattice.katz_divisibility_limit {d} [PrimeSevenModEight d] (C :
  CMLattice d) {p} [Fact p.Prime] [PadicPlace p] n : ∃ f ∈ C.phiSeriesRing,
  (p ^ (nonsplitWeight d p - 1 / (p - 1))) ^ n ≤ ‖n ! * f.coeff n‖ := by_contra fun _ ↦ by
  obtain ⟨⟨⟩, m, e, ϖ, θ, S, _, ⟨he, hϖ, -, π2, -, E, _, hT, hS⟩, -⟩ :=
    Prime.one_lt' p, C.phiSeriesRing.pow_mem C.isSeriesGenerator_translatedWpDeriv.generator_mem,
    C.exists_formal_parameter
  choose j _ H using (exists_monomial_max_norm_coeff C.phiSeriesRing rfl 1 <| .single () ·)
  let c n := ‖n ! * (taylorVia ιₚ C.translatedWpDeriv ^ j n ()).coeff n‖ /
    (p ^ (nonsplitWeight d p - 1 / (p - 1))) ^ n
  have hc k n : c (n + k) ≤ c n * c k
  have h i := (exists_monomial_max_norm_coeff _ rfl 1 (.single 0 n + .single 1 k)).choose_spec.2 _
    (pow_mem C.translatedWpDeriv_add_mem_multiPhiRing i); simp_all [← subst_pow, ↓Finsupp.prod_pow,
    (· ∘ ·)]
  rw [MvPowerSeries.coeff_mul, sum_eq_single_of_mem (_, _) (by simp; rfl)] at h <;>
    simp [field, Finsupp.ext_iff] at *
  grw [h, H, H k]; ring; repeat tauto
  omega
  have ⟨l, hl⟩ := Metric.tendsto_atTop.1 (@summable_of_sum_range_le c _ (by bound) fun _ ↦
    (le_div_iff₀' (by simp_all [field] : 0 < 1 - c n)).2 (by grw [one_sub_mul, sub_le_iff_le_add,
    mul_sum, ← hc, ← sum_range_add, ← le_add_self])).tendsto_atTop_zero ‖ϖ‖ (hϖ ▸ by bound)
  absurd (trunc l (S.map (residue _))).natDegree_comp (p := .X - .X ^ p ^ e)
  rw [eq_comm, (_ : Polynomial.comp .. = .X)] <;> simp_all [← Polynomial.coe_inj, ne_of_gt,
    Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
  rw [← (_ : _ = Polynomial.toPowerSeries _)]
  simpa [smul_eq_C_mul, (residue_eq_zero_iff _).2, π2.ne] using congr(map (residue _) $E)
  ext k; simp [coeff_trunc]; peel hl k; contrapose this
  apply_fun (‖coeff k ·‖) at hS; simp [*, c, ← rpow_mul_natCast, ← PowerSeries.map.eq_1] at *
  grw [← hS, H, ← rpow_le_norm_factorial, mul_div_right_comm, ← rpow_sub] <;> (try ring) <;> bound
