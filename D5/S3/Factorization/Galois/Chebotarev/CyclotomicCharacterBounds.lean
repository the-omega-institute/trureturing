/- GID: D5/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/Chebotarev/CyclotomicCharacterBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nontrivial cyclotomic character prime sums are bounded near one. -/
module

public import D5.S3.Analytic.Zeta.NumberField.ZetaProduct
public import D5.S3.Factorization.Galois.Chebotarev.CyclotomicNormResidue
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Chebotarev's theorem: cyclotomic case

For a number field `K`, an integer `m ≥ 1`, and the cyclotomic extension
`L = K(μ_m)`, the Dirichlet density of primes `𝔭` of `𝓞 K` (unramified in `L`)
whose Frobenius equals a given `σ ∈ Gal(L/K)` is `1 / |Gal(L/K)|`.

The proof is the direct generalisation of Dirichlet's theorem (Sharifi
§7.2.1; Stevenhagen–Lenstra Appendix paragraph 3). The argument:

1. By Frobenius reciprocity for cyclotomic extensions, `χ(σ_𝔭)` depends only
   on `N𝔭 mod m` for every character `χ` of `Gal(L/K)`.
2. The orthogonality relation `Σ_χ χ(σ)^{-1} χ(σ_𝔭) = |G|` if `σ_𝔭 = σ` (and
   `0` otherwise) holds character-by-character.
3. Combining the two and using `log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`,
   `log L(χ, s)` bounded for `χ ≠ 1`, and `L(χ, 1) ≠ 0` from
   `ZetaProduct.artinLSeries_one_ne_zero`, the Dirichlet density of
   `{𝔭 : σ_𝔭 = σ}` equals `1 / |G|`.

## Main results

* `Chebotarev.cyclotomic_density_from_two_sided_asymp` — the density of
  primes of `K` unramified in `K(μ_m)` with Frobenius equal to `σ` is
  `1 / |Gal(K(μ_m)/K)|`.

## References

* Sharifi, *Algebraic Number Theory*, §7.2.1 (`docs/algnum.pdf`, p. 142).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  paragraph 3 (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open NumberField Filter Topology

open scoped nonZeroDivisors

namespace Chebotarev

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Complex-analytic core of the cyclotomic χ≠1 bound

These `private` helpers carry out the pure complex analysis behind
`artinLSeries_prime_sum_bounded_of_analytic_extension`. They are stated abstractly over an index
type `ι` with a "norm exponent base" `N : ι → ℕ` (`2 ≤ N i`) and a unit-norm coefficient
`c : ι → ℂ`. The substrate is `g(s) = Σ_i -Log(1 - c i · N i⁻ˢ)` (the "log sum") and the per-term
weight `w i s = c i · N i⁻ˢ`. -/

/-- The log sum `g(s) = Σ_i -Log(1 - c i · N i⁻ˢ)` is differentiable at each `s₀ > 1`. -/
private theorem differentiableAt_logSum_of_two_le
    {ι : Type*} (N : ι → ℕ) (c : ι → ℂ) (s₀ : ℝ) (hs₀ : 1 < s₀)
    (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1)
    (hsummr : ∀ r : ℝ, 1 < r → Summable (fun i ↦ (N i : ℝ) ^ (-r))) :
    DifferentiableAt ℝ
      (fun s : ℝ ↦ ∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) s₀ := by
  set ε : ℝ := (s₀ - 1) / 2 with hε
  set t : Set ℝ := Set.Ioi (1 + ε) with ht
  have htopen : IsOpen t := isOpen_Ioi
  have htconn : IsPreconnected t := (convex_Ioi _).isPreconnected
  have hs₀t : s₀ ∈ t := by rw [ht]; simp only [Set.mem_Ioi]; rw [hε]; linarith
  set g : ι → ℝ → ℂ := fun i s ↦ -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) with hg
  set g' : ι → ℝ → ℂ := fun i s ↦
    -((-(c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1)))) /
        (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) with hg'
  set u : ι → ℝ := fun i ↦ 2 * Real.log (N i) * (N i : ℝ) ^ (-(1 + ε)) with hu
  have hNRpos : ∀ i, (0 : ℝ) < N i := fun i ↦ by have := hN i; positivity
  have hN1 : ∀ i, (1 : ℝ) ≤ N i := fun i ↦ by have := hN i; exact_mod_cast Nat.one_le_of_lt this
  have hlog0 : ∀ i, 0 ≤ Real.log (N i) := fun i ↦ Real.log_nonneg (hN1 i)
  have hwn : ∀ i, ∀ s : ℝ, ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ = (N i : ℝ) ^ (-s) := fun i s ↦ by
    rw [norm_mul, hc, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN i; lia),
      Complex.neg_re, Complex.ofReal_re]
  have hN2s : ∀ i, ∀ s : ℝ, 1 ≤ s → (2 : ℝ) ≤ (N i : ℝ) ^ s := fun i s hs ↦ by
    have h2N : (2 : ℝ) ≤ N i := by have := hN i; exact_mod_cast this
    exact h2N.trans (Real.self_le_rpow_of_one_le (by linarith) hs)
  have hwle : ∀ i, ∀ s ∈ t, ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ ≤ 1 / 2 := by
    intro i s hst
    simp only [ht, Set.mem_Ioi] at hst
    rw [hwn, Real.rpow_neg (hNRpos i).le,
      inv_le_comm₀ (Real.rpow_pos_of_pos (hNRpos i) _) (by norm_num)]
    linarith [hN2s i s (by linarith)]
  have hslit : ∀ i, ∀ s ∈ t, (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) ∈ Complex.slitPlane := by
    intro i s hst
    have hlt : ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ < 1 := lt_of_le_of_lt (hwle i s hst) (by norm_num)
    rw [sub_eq_add_neg]
    exact Complex.mem_slitPlane_of_norm_lt_one
      (z := -(c i * (N i : ℂ) ^ (-(s : ℂ)))) (by simpa using hlt)
  have husum : Summable u := by
    have hδpos : 0 < ε / 2 := by linarith
    have hr'1 : 1 < (1 + ε) - ε / 2 := by linarith
    refine Summable.of_nonneg_of_le ?_ ?_ ((hsummr ((1 + ε) - ε / 2) hr'1).mul_left (2 / (ε / 2)))
    · intro i; rw [hu]; have := hlog0 i; positivity
    · intro i
      rw [hu]
      set n : ℝ := (N i : ℝ)
      have hlog : Real.log n ≤ n ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div (hNRpos i).le hδpos
      calc 2 * Real.log n * n ^ (-(1 + ε)) ≤ 2 * (n ^ (ε / 2) / (ε / 2)) * n ^ (-(1 + ε)) := by
            gcongr
        _ = (2 / (ε / 2)) * n ^ (-((1 + ε) - ε / 2)) := by
              rw [show -((1 + ε) - ε / 2) = (ε / 2) + (-(1 + ε)) by ring, Real.rpow_add (hNRpos i)]
              field_simp
              ring
  have hderiv : ∀ i, ∀ s ∈ t, HasDerivAt (g i) (g' i s) s := by
    intro i s hst
    have hN0 : (N i : ℂ) ≠ 0 := by exact_mod_cast (by have := hN i; lia : N i ≠ 0)
    have hpow : HasDerivAt (fun z : ℂ ↦ (N i : ℂ) ^ (-z))
        ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1)) (s : ℂ) := by
      have houter : HasDerivAt (fun z : ℂ ↦ (N i : ℂ) ^ z)
          ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ)) (-(s : ℂ)) :=
        (Complex.hasStrictDerivAt_const_cpow (Or.inl hN0)).hasDerivAt
      exact houter.comp (s : ℂ) (hasDerivAt_neg' (s : ℂ))
    have hin : HasDerivAt (fun z : ℂ ↦ 1 - c i * (N i : ℂ) ^ (-z))
        (-(c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1)))) (s : ℂ) := by
      simpa using (hpow.const_mul (c i)).const_sub 1
    have hlog : HasDerivAt (fun z : ℂ ↦ Complex.log (1 - c i * (N i : ℂ) ^ (-z)))
        ((-(c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1)))) /
          (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) (s : ℂ) := hin.clog (by simpa using hslit i s hst)
    exact (hlog.neg).comp_ofReal
  have hbound : ∀ i, ∀ s ∈ t, ‖g' i s‖ ≤ u i := by
    intro i s hst
    simp only [ht, Set.mem_Ioi] at hst
    set w : ℂ := c i * (N i : ℂ) ^ (-(s : ℂ)) with hw
    have hwlei : ‖w‖ ≤ 1 / 2 := hwle i s (by simp [ht, hst])
    have hden : (1 : ℝ) / 2 ≤ ‖1 - w‖ := by
      have := norm_sub_norm_le (1 : ℂ) w; rw [norm_one] at this; linarith
    have hdenpos : 0 < ‖1 - w‖ := by linarith
    have hnum : ‖(-(c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1))))‖
        = (N i : ℝ) ^ (-s) * Real.log (N i) := by
      rw [show c i * ((N i : ℂ) ^ (-(s : ℂ)) * Complex.log (N i : ℂ) * (-1))
          = -(c i * (N i : ℂ) ^ (-(s : ℂ))) * Complex.log (N i : ℂ) by ring]
      rw [norm_neg, norm_mul, norm_neg, ← hw, hwn,
        show Complex.log (N i : ℂ) = ((Real.log (N i) : ℝ) : ℂ) by
          rw [← Complex.ofReal_natCast, Complex.ofReal_log (hNRpos i).le],
        Complex.norm_real, Real.norm_of_nonneg (hlog0 i)]
    rw [hg', norm_neg, norm_div, hnum, hu, div_le_iff₀ hdenpos]
    have hrns : 0 ≤ (N i : ℝ) ^ (-s) := Real.rpow_nonneg (hNRpos i).le _
    have hmono : (N i : ℝ) ^ (-s) ≤ (N i : ℝ) ^ (-(1 + ε)) := by
      apply Real.rpow_le_rpow_of_exponent_le (hN1 i); linarith
    have hrn1 : 0 ≤ (N i : ℝ) ^ (-(1 + ε)) := Real.rpow_nonneg (hNRpos i).le _
    nlinarith [hden, hlog0 i, hrns, hmono, mul_nonneg hrns (hlog0 i), mul_nonneg hrn1 (hlog0 i)]
  have hg0 : Summable fun i ↦ g i s₀ := by
    have hbase : Summable (fun i ↦ (N i : ℝ) ^ (-s₀)) := hsummr s₀ hs₀
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _) (fun i ↦ ?_) (hbase.mul_left 2)
    set w : ℂ := c i * (N i : ℂ) ^ (-(s₀ : ℂ)) with hw
    have hwlei : ‖w‖ ≤ 1 / 2 := hwle i s₀ hs₀t
    have hkey : ‖Complex.log (1 - w)‖ ≤ 3 / 2 * ‖w‖ := by
      simpa [sub_eq_add_neg] using
        Complex.norm_log_one_add_half_le_self (z := -w) (by simpa using hwlei)
    rw [hg, norm_neg]
    calc ‖Complex.log (1 - w)‖ ≤ 3 / 2 * ‖w‖ := hkey
      _ ≤ 2 * ‖w‖ := by nlinarith [norm_nonneg w]
      _ = 2 * (N i : ℝ) ^ (-s₀) := by rw [hwn i s₀]
  exact (hasDerivAt_tsum_of_isPreconnected husum htopen htconn hderiv hbound hs₀t hg0
    hs₀t).differentiableAt

/-- The twisted prime sum `∑'_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ` over the unramified primes, as a complex function of
`s`. The `χ = 1` value is the real prime sum `∑'_𝔭 N𝔭⁻ˢ`; the `χ ≠ 1` values are bounded near
`s = 1`. -/
noncomputable def twistedPrimeSum
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (χ : galoisCharacter K L) (s : ℝ) : ℂ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
    (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))

/-- The log sum `G(s) = Σ_i -log(1 - c i N i⁻ˢ)` is bounded as `s ↓ 1`, given an analytic extension
`Lf` of `exp ∘ G` to an open set `D ⊇ [1, ∞)` with `Lf 1 ≠ 0`. Packages phases 1–3 of the bridge:
`G` is real-differentiable with logarithmic derivative `Lf'/Lf` (continuous on `[1,2]`), so the
mean-value bound applies. -/
private theorem norm_logSum_bounded_nhdsGT_aux
    {ι : Type*} (N : ι → ℕ) (c : ι → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1)
    (hsummr : ∀ r : ℝ, 1 < r → Summable (fun i ↦ (N i : ℝ) ^ (-r)))
    (Lf : ℂ → ℂ) (D : Set ℂ) (hDopen : IsOpen D) (hmemD : ∀ s : ℝ, 1 ≤ s → (s : ℂ) ∈ D)
    (hLf_an : AnalyticOn ℂ Lf D) (hLf0 : Lf 1 ≠ 0)
    (hexpeq : ∀ s : ℝ, 1 < s →
      Complex.exp (∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) = Lf (s : ℂ)) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))‖ ≤ C := by
  set G : ℝ → ℂ := fun s ↦ ∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) with hGdef
  have hLf_ne : ∀ s : ℝ, 1 ≤ s → Lf (s : ℂ) ≠ 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs with hs1 | hs1
    · rw [← hs1]; simpa using hLf0
    · rw [← hexpeq s hs1]; exact Complex.exp_ne_zero _
  have hanNhd : AnalyticOnNhd ℂ Lf D := (hDopen.analyticOn_iff_analyticOnNhd).mp hLf_an
  have hLfdiff : ∀ s : ℝ, 1 ≤ s → DifferentiableAt ℂ Lf (s : ℂ) := fun s hs ↦
    (hanNhd (s : ℂ) (hmemD s hs)).differentiableAt
  set F : ℝ → ℂ := fun s ↦ deriv Lf (s : ℂ) / Lf (s : ℂ) with hF
  have hFcont : ContinuousOn F (Set.Icc 1 2) := by
    have hLfca : ∀ s : ℝ, 1 ≤ s → ContinuousAt (fun s : ℝ ↦ Lf (s : ℂ)) s := fun s hs ↦
      ((hanNhd (s : ℂ) (hmemD s hs)).continuousAt).comp Complex.continuous_ofReal.continuousAt
    have hdLfca : ∀ s : ℝ, 1 ≤ s → ContinuousAt (fun s : ℝ ↦ deriv Lf (s : ℂ)) s := fun s hs ↦
      (((hanNhd (s : ℂ) (hmemD s hs)).deriv).continuousAt).comp
        Complex.continuous_ofReal.continuousAt
    refine ContinuousOn.div ?_ ?_ (fun s hs ↦ hLf_ne s hs.1)
    · exact fun s hs ↦ (hdLfca s hs.1).continuousWithinAt
    · exact fun s hs ↦ (hLfca s hs.1).continuousWithinAt
  have hGderiv : ∀ s : ℝ, 1 < s → HasDerivAt G (F s) s := by
    intro s hs
    have hGdiff : DifferentiableAt ℝ G s :=
      differentiableAt_logSum_of_two_le N c s hs hN hc hsummr
    have hval : deriv G s = F s :=
      (show ∀ (G : ℝ → ℂ) (G' : ℂ) (s₀ : ℝ) (hs₀ : 1 < s₀) (Lf : ℂ → ℂ) (hG : HasDerivAt G G' s₀) (hLfdiff : DifferentiableAt ℂ Lf (s₀ : ℂ)) (heq : ∀ s : ℝ, 1 < s → Complex.exp (G s) = Lf (s : ℂ)) (hLf0 : Lf (s₀ : ℂ) ≠ 0), (G' = deriv Lf (s₀ : ℂ) / Lf (s₀ : ℂ)) from by
        intro G G' s₀ hs₀ Lf hG hLfdiff heq hLf0
        classical
        have hexpG : HasDerivAt (fun s : ℝ ↦ Complex.exp (G s)) (G' * Complex.exp (G s₀)) s₀ := by
          simpa [mul_comm] using hG.cexp
        have hLfreal : HasDerivAt (fun s : ℝ ↦ Lf (s : ℂ)) (deriv Lf (s₀ : ℂ)) s₀ :=
          (hLfdiff.hasDerivAt).comp_ofReal
        have hev : (fun s : ℝ ↦ Complex.exp (G s)) =ᶠ[𝓝 s₀] (fun s : ℝ ↦ Lf (s : ℂ)) := by
          filter_upwards [Ioi_mem_nhds hs₀] with s hs using heq s hs
        have hdereq : G' * Complex.exp (G s₀) = deriv Lf (s₀ : ℂ) :=
          hexpG.unique (hLfreal.congr_of_eventuallyEq hev)
        rw [heq s₀ hs₀] at hdereq
        field_simp at hdereq ⊢
        linear_combination hdereq) G (deriv G s) s hs Lf hGdiff.hasDerivAt
        (hLfdiff s hs.le) hexpeq (hLf_ne s hs.le)
    rw [hF] at hval ⊢
    rw [← hval]
    exact hGdiff.hasDerivAt
  exact (show ∀ (G : ℝ → ℂ) (F : ℝ → ℂ) (hGderiv : ∀ s : ℝ, 1 < s → HasDerivAt G (F s) s) (hFcont : ContinuousOn F (Set.Icc 1 2)), (∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖G s‖ ≤ C) from by
    intro G F hGderiv hFcont
    classical
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s ∈ Set.Icc (1 : ℝ) 2, ‖F s‖ ≤ M :=
      isCompact_Icc.exists_bound_of_continuousOn hFcont
    refine ⟨‖G 2‖ + M, ?_⟩
    have h2 : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, h2] with s hs1 hs2
    simp only [Set.mem_Ioi] at hs1
    have hsub : Set.Icc s 2 ⊆ Set.Icc (1 : ℝ) 2 := Set.Icc_subset_Icc hs1.le le_rfl
    have hdiff : ∀ x ∈ Set.Icc s 2, DifferentiableAt ℝ G x := fun x hx ↦
      (hGderiv x (lt_of_lt_of_le hs1 hx.1)).differentiableAt
    have hbnd : ∀ x ∈ Set.Icc s 2, ‖deriv G x‖ ≤ M := fun x hx ↦ by
      rw [(hGderiv x (lt_of_lt_of_le hs1 hx.1)).deriv]; exact hM x (hsub hx)
    have hmvt : ‖G s - G 2‖ ≤ M * ‖s - 2‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd (convex_Icc s 2)
        (Set.right_mem_Icc.mpr hs2.le) (Set.left_mem_Icc.mpr hs2.le)
    have hsm : ‖s - 2‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 1 (by norm_num))
    calc ‖G s‖ ≤ ‖G s - G 2‖ + ‖G 2‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖G 2‖ + M := by nlinarith [hsm]) G F hGderiv hFcont

/-- **Complex-analytic bridge of Dirichlet's argument (the substantive content of the cyclotomic
case).** Given the analytic extension `Lf` of `L(χ,·)` — analytic on `Z(1-[K:ℚ]⁻¹)` and agreeing
with the ideal Dirichlet series on `Re s > 1` (the `artinLSeries_analytic_extension` / LF4 leaf) —
which is nonzero at `s = 1` (`artinLSeries_one_ne_zero` / LF5), the twisted prime sum
`Σ_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ` stays bounded as `s ↓ 1`. -/
private theorem artinLSeries_prime_sum_bounded_of_analytic_extension
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [hAb : IsMulCommutative Gal(L/K)] (χ : galoisCharacter K L)
    (_hχ : χ ≠ 1) (Lf : ℂ → ℂ)
    (hLf_an : AnalyticOn ℂ Lf {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re})
    (hLf_eq : ∀ s : ℂ, 1 < s.re →
      Lf s = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥},
        galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s))
    (hLf0 : Lf 1 ≠ 0) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  classical
  set ι := {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}
  set N : ι → ℕ := fun 𝔭 ↦ Ideal.absNorm 𝔭.1
  set c : ι → ℂ := fun 𝔭 ↦ (χ (frobeniusClass K L 𝔭.1).out : ℂ) with hc
  set G : ℝ → ℂ := fun s ↦ ∑' 𝔭 : ι, -Complex.log (1 - c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))) with hGdef
  have hc1 : ∀ 𝔭 : ι, ‖c 𝔭‖ = 1 := fun 𝔭 ↦
    (((Units.coeHom ℂ).comp χ).isOfFinOrder
      (isOfFinOrder_of_finite (frobeniusClass K L 𝔭.1).out)).norm_eq_one
  have hN2 : ∀ 𝔭 : ι, 2 ≤ N 𝔭 := by
    intro 𝔭
    change 2 ≤ Ideal.absNorm 𝔭.1
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦ 𝔭.2.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
    have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h ↦ 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
    lia
  have hsummr : ∀ r : ℝ, 1 < r → Summable (fun 𝔭 : ι ↦ (N 𝔭 : ℝ) ^ (-r)) := fun r hr ↦
    (((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
      intro S s hs
      exact (((show Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
        (((show HasSum (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta K (s : ℂ)) from by
          have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
          classical
          haveI (n : ℕ) : Finite {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} :=
            Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
              ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
              (fun _ _ _ _ ↦ Subtype.ext)
          have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
            classical
            have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity K k : ℝ))
                =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
              classical
              have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal K | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                Set.Finite.preimage (f := fun I : NonzeroIdeal K ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) b)
              have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity K k =
                  Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal K ↦
                  Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                rw [show ((fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                    {I : NonzeroIdeal K | Ideal.absNorm I.1 ≤ n} by
                  ext ⟨I, hI⟩
                  simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                  exact ⟨fun h ↦ h.2, fun h ↦
                    ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                exact key.symm
              have h_card_bridge : ∀ n : ℕ,
                  Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} =
                  Nat.card {I : (Ideal (𝓞 K))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                fun n ↦ Nat.card_congr
                  { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                      ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                    invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                      ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                    left_inv := fun _ ↦ rfl
                    right_inv := fun _ ↦ rfl }
              refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
                  tendsto_natCast_atTop_atTop).congr' ?_)
              filter_upwards with n
              simp only [Function.comp_apply, Real.rpow_one]
              rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
              push_cast
              rfl
            have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) s :=
              LSeriesSummable_of_sum_norm_bigO_and_nonneg
                (f := fun n ↦ (idealNormMultiplicity K n : ℝ))
                hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                (by exact_mod_cast hcondition)
            have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) (s : ℂ) =
                fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
              funext n
              simp only [LSeries.term]
              split_ifs with hn
              · subst hn
                have hzero : idealNormMultiplicity K 0 = 0 := by
                    unfold idealNormMultiplicity
                    rw [Nat.card_eq_zero]
                    exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                simp [hzero]
              · simp [Complex.cpow_neg, div_eq_mul_inv]
            exact (h_term_eq ▸ h_lss :
              Summable fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
          have hzeta : NumberField.dedekindZeta K (s : ℂ) =
              ∑' n : ℕ, (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
            unfold NumberField.dedekindZeta LSeries
            refine tsum_congr fun n ↦ ?_
            unfold LSeries.term
            rcases Nat.eq_zero_or_pos n with rfl | hn
            · have hs0 : (s : ℂ) ≠ 0 := by
                intro hzero
                have hre := congrArg Complex.re hzero
                simp only [Complex.zero_re] at hre
                rw [hre] at hcondition
                norm_num at hcondition
              have hzero : idealNormMultiplicity K 0 = 0 := by
                  unfold idealNormMultiplicity
                  rw [Nat.card_eq_zero]
                  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
              simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
            · simp only [hn.ne', ↓reduceIte]
              rw [Complex.cpow_neg, div_eq_mul_inv]
              congr 1
              unfold idealNormMultiplicity
              have hequiv : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ≃
                  {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} := by
                refine {
                  toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                  invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                  left_inv := fun _ ↦ rfl
                  right_inv := fun _ ↦ rfl }
                intro h
                rw [h, Ideal.absNorm_bot] at hI
                lia
              exact_mod_cast Nat.card_congr hequiv
          set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1)
          have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
              (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
            fun n ↦ by
              rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                  (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity K n • (n : ℂ) ^ (-(s : ℂ)) from
                (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                  (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
          have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
              ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
            fun n ↦ by
              rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                  ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity K n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                  (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                Complex.norm_natCast]
          have hsummable : Summable fun I : NonzeroIdeal K ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
            rw [← e.summable_iff]
            refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
            exact hseries.congr fun n ↦ (hnorm n).symm
          have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
              (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
            (e.summable_iff (f := fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
              hsummable.of_norm
          have hval_sum : (∑' I : NonzeroIdeal K, (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
              = NumberField.dedekindZeta K s := by
            rw [hzeta,
              ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
            exact tsum_congr hval
          exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
          fun I ↦ (Complex.norm_natCast_cpow_of_pos
            (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
        (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
          (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K))
        fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) _ hr).comp_injective
      (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
        (⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, (𝔭.2.2).1⟩ :
          {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}))
      (fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))).congr fun 𝔭 ↦ rfl
  have hwn : ∀ 𝔭 : ι, ∀ s : ℝ, ‖c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))‖ = (N 𝔭 : ℝ) ^ (-s) := by
    intro 𝔭 s
    rw [norm_mul, hc1, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN2 𝔭; lia),
      Complex.neg_re, Complex.ofReal_re]
  have hslit : ∀ 𝔭 : ι, ∀ s : ℝ, 1 < s →
      (1 - c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))) ∈ Complex.slitPlane := by
    intro 𝔭 s hs
    have h1N : (1 : ℝ) < N 𝔭 := by have := hN2 𝔭; exact_mod_cast (by lia : 1 < N 𝔭)
    have hlt : ‖c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))‖ < 1 := by
      rw [hwn]; exact Real.rpow_lt_one_of_one_lt_of_neg h1N (by linarith)
    rw [sub_eq_add_neg]
    exact Complex.mem_slitPlane_of_norm_lt_one
      (z := -(c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ)))) (by simpa using hlt)
  have hexpeq : ∀ s : ℝ, 1 < s → Complex.exp (G s) = Lf (s : ℂ) := by
    intro s hs
    have hsc : 1 < ((s : ℂ)).re := by simpa using hs
    have hsumw : Summable (fun 𝔭 : ι ↦ c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ))) :=
      (show ∀ (χ : galoisCharacter K L) {s : ℝ} (hs : 1 < s), (Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦ (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))) from by
        intro χ s hs
        classical
        have hs0 : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
          (((show ∀ (S : Set (Ideal (𝓞 K))) {s : ℝ}, 1 < s → Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) from by
            intro S s hs
            exact (((show Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) from
              (((show HasSum (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))) (NumberField.dedekindZeta K (s : ℂ)) from by
                have hcondition : 1 < ((s : ℂ)).re := (by simpa using hs)
                classical
                haveI (n : ℕ) : Finite {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} :=
                  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal K ↦ I.1)
                    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
                    (fun _ _ _ _ ↦ Subtype.ext)
                have hseries : Summable fun n : ℕ ↦ ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ := by
                  classical
                  have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity K k : ℝ))
                      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
                    classical
                    have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal K | Ideal.absNorm I.1 = b}.Finite := fun b ↦
                      Set.Finite.preimage (f := fun I : NonzeroIdeal K ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
                        (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) b)
                    have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity K k =
                        Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
                      have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal K ↦
                        Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
                      rw [show ((fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
                          {I : NonzeroIdeal K | Ideal.absNorm I.1 ≤ n} by
                        ext ⟨I, hI⟩
                        simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
                        exact ⟨fun h ↦ h.2, fun h ↦
                          ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
                      exact key.symm
                    have h_card_bridge : ∀ n : ℕ,
                        Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ n} =
                        Nat.card {I : (Ideal (𝓞 K))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
                      fun n ↦ Nat.card_congr
                        { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                            ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
                          invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
                            ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
                          left_inv := fun _ ↦ rfl
                          right_inv := fun _ ↦ rfl }
                    refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
                      (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
                        tendsto_natCast_atTop_atTop).congr' ?_)
                    filter_upwards with n
                    simp only [Function.comp_apply, Real.rpow_one]
                    rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
                    push_cast
                    rfl
                  have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) s :=
                    LSeriesSummable_of_sum_norm_bigO_and_nonneg
                      (f := fun n ↦ (idealNormMultiplicity K n : ℝ))
                      hbig (fun _ ↦ Nat.cast_nonneg _) zero_le_one
                      (by exact_mod_cast hcondition)
                  have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity K n : ℝ) : ℂ)) (s : ℂ) =
                      fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                    funext n
                    simp only [LSeries.term]
                    split_ifs with hn
                    · subst hn
                      have hzero : idealNormMultiplicity K 0 = 0 := by
                          unfold idealNormMultiplicity
                          rw [Nat.card_eq_zero]
                          exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                      simp [hzero]
                    · simp [Complex.cpow_neg, div_eq_mul_inv]
                  exact (h_term_eq ▸ h_lss :
                    Summable fun n ↦ (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))).norm
                have hzeta : NumberField.dedekindZeta K (s : ℂ) =
                    ∑' n : ℕ, (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) := by
                  unfold NumberField.dedekindZeta LSeries
                  refine tsum_congr fun n ↦ ?_
                  unfold LSeries.term
                  rcases Nat.eq_zero_or_pos n with rfl | hn
                  · have hs0 : (s : ℂ) ≠ 0 := by
                      intro hzero
                      have hre := congrArg Complex.re hzero
                      simp only [Complex.zero_re] at hre
                      rw [hre] at hcondition
                      norm_num at hcondition
                    have hzero : idealNormMultiplicity K 0 = 0 := by
                        unfold idealNormMultiplicity
                        rw [Nat.card_eq_zero]
                        exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
                    simp [hzero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
                  · simp only [hn.ne', ↓reduceIte]
                    rw [Complex.cpow_neg, div_eq_mul_inv]
                    congr 1
                    unfold idealNormMultiplicity
                    have hequiv : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ≃
                        {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} := by
                      refine {
                        toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
                        invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
                        left_inv := fun _ ↦ rfl
                        right_inv := fun _ ↦ rfl }
                      intro h
                      rw [h, Ideal.absNorm_bot] at hI
                      lia
                    exact_mod_cast Nat.card_congr hequiv
                set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1)
                have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                    (Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))) = (idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
                  fun n ↦ by
                    rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                        (Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))) = idealNormMultiplicity K n • (n : ℂ) ^ (-(s : ℂ)) from
                      (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                        (tsum_const ((n : ℂ) ^ (-(s : ℂ)))), nsmul_eq_mul]
                have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                    ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-(s : ℂ))‖) = ‖(idealNormMultiplicity K n : ℂ) * (n : ℂ) ^ (-(s : ℂ))‖ :=
                  fun n ↦ by
                    rw [show (∑' y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n},
                        ‖(Ideal.absNorm y.1.1 : ℂ) ^ (-(s : ℂ))‖) = idealNormMultiplicity K n • ‖(n : ℂ) ^ (-(s : ℂ))‖ from
                      (tsum_congr fun y : {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
                        (tsum_const ‖(n : ℂ) ^ (-(s : ℂ))‖), nsmul_eq_mul, norm_mul,
                      Complex.norm_natCast]
                have hsummable : Summable fun I : NonzeroIdeal K ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))‖ := by
                  rw [← e.summable_iff]
                  refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
                  exact hseries.congr fun n ↦ (hnorm n).symm
                have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal K // Ideal.absNorm I.1 = n} ↦
                    (Ideal.absNorm (e p).1 : ℂ) ^ (-(s : ℂ)) :=
                  (e.summable_iff (f := fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))).mpr
                    hsummable.of_norm
                have hval_sum : (∑' I : NonzeroIdeal K, (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ)))
                    = NumberField.dedekindZeta K s := by
                  rw [hzeta,
                    ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-(s : ℂ))), hsummable_sigma.tsum_sigma]
                  exact tsum_congr hval
                exact hval_sum ▸ hsummable.of_norm.hasSum)).summable.norm).congr
                fun I ↦ (Complex.norm_natCast_cpow_of_pos
                  (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp)).comp_injective
              (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
                (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K))
              fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl) _ hs).comp_injective
            (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ↦
              (⟨𝔭.1, ⟨𝔭.2.1, 𝔭.2.2⟩, 𝔭.2.1, (𝔭.2.2).1⟩ :
                {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ {𝔭 | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}))
            (fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))).congr fun 𝔭 ↦ rfl
        have hnorm1 : ∀ c : ConjClasses Gal(L/K), ‖(χ c.out : ℂ)‖ = 1 := fun c ↦
          (((Units.coeHom ℂ).comp χ).isOfFinOrder (isOfFinOrder_of_finite c.out)).norm_eq_one
        have hnormterm : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
            ‖(χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ =
              (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 ↦ by
          have hpos : 0 < Ideal.absNorm 𝔭.1 := by
            have hne : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦
              (𝔭.2.2).1 (Ideal.absNorm_eq_zero_iff.mp h)
            lia
          rw [norm_mul, hnorm1, one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
            Complex.ofReal_re]
        exact Summable.of_norm (hs0.congr fun 𝔭 ↦ (hnormterm 𝔭).symm)) χ hs
    rw [hGdef, (show ∀ (w : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ) (hsumw : Summable w) (hslit : ∀ i, (1 - w i) ∈ Complex.slitPlane), (Complex.exp (∑' i, -Complex.log (1 - w i)) = ∏' i, (1 - w i)⁻¹) from by
      intro w hsumw hslit
      classical
      set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ := fun i ↦ (1 - w i)⁻¹ with hf
      have hfn : ∀ i, f i ≠ 0 := fun i ↦ inv_ne_zero (Complex.slitPlane_ne_zero (hslit i))
      have hlogf : ∀ i, Complex.log (f i) = -Complex.log (1 - w i) := fun i ↦ by
        rw [hf, Complex.log_inv _ (Complex.slitPlane_arg_ne_pi (hslit i))]
      have hsumlog : Summable (fun i ↦ Complex.log (f i)) :=
        (hsumw.clog_one_sub.neg).congr fun i ↦ (hlogf i).symm
      simp_rw [← hlogf]
      exact Complex.cexp_tsum_eq_tprod hfn hsumlog) _ hsumw (fun 𝔭 ↦ hslit 𝔭 s hs)]
    rw [show (fun 𝔭 : ι ↦ (1 - c 𝔭 * (N 𝔭 : ℂ) ^ (-(s : ℂ)))⁻¹)
        = (fun 𝔭 : ι ↦ (1 - (χ (frobeniusClass K L 𝔭.1).out : ℂ)
            * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))⁻¹) from rfl,
      exists_artinLSeries_eulerProduct_abelian K L χ (s : ℂ) hsc, ← hLf_eq (s : ℂ) hsc]
  set D : Set ℂ := {s : ℂ | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} with hD
  have hDopen : IsOpen D := by rw [hD]; exact isOpen_lt continuous_const Complex.continuous_re
  have hmemD : ∀ s : ℝ, 1 ≤ s → (s : ℂ) ∈ D := fun s hs ↦ by
    rw [hD]; simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    have hfr : 0 < Module.finrank ℚ K := Module.finrank_pos
    have : (0 : ℝ) < (Module.finrank ℚ K : ℝ)⁻¹ := by positivity
    linarith
  exact (show ∀ (N : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℕ) (c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1) (hsummr : ∀ r : ℝ, 1 < r → Summable (fun i ↦ (N i : ℝ) ^ (-r))) (hGbdd : ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))‖ ≤ C), (∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖∑' i, c i * (N i : ℂ) ^ (-(s : ℂ))‖ ≤ C) from by
    intro N c hN hc hsummr hGbdd
    classical
    obtain ⟨Cg, hCg⟩ := hGbdd
    have hsumN2 : Summable (fun i ↦ (N i : ℝ) ^ (-(2 : ℝ))) := hsummr 2 one_lt_two
    have hwn : ∀ i, ∀ s : ℝ, ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ = (N i : ℝ) ^ (-s) := fun i s ↦ by
      rw [norm_mul, hc, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN i; lia),
        Complex.neg_re, Complex.ofReal_re]
    have hsumlin : ∀ s : ℝ, 1 < s → Summable (fun i ↦ c i * (N i : ℂ) ^ (-(s : ℂ))) := fun s hs ↦
      Summable.of_norm ((hsummr s hs).congr fun i ↦ (hwn i s).symm)
    have hsumtail : ∀ s : ℝ, 1 < s →
        Summable (fun i ↦ -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))
          - c i * (N i : ℂ) ^ (-(s : ℂ))) := fun s hs ↦
      Summable.of_norm (Summable.of_nonneg_of_le (fun i ↦ norm_nonneg _)
        (fun i ↦ (show ∀ (N : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℕ) (c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ) (s : ℝ) (hs : 1 < s) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1) (i : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}), (‖-Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) - c i * (N i : ℂ) ^ (-(s : ℂ))‖ ≤ (N i : ℝ) ^ (-(2 : ℝ))) from by
          intro N c s hs hN hc i
          classical
          have hNRpos : (0 : ℝ) < N i := by have := hN i; positivity
          have hwn : ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ = (N i : ℝ) ^ (-s) := by
            rw [norm_mul, hc, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN i; lia),
              Complex.neg_re, Complex.ofReal_re]
          have hslit : (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) ∈ Complex.slitPlane := by
            have h1N : (1 : ℝ) < N i := by have := hN i; exact_mod_cast (by lia : 1 < N i)
            have hlt : ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ < 1 := by
              rw [hwn]; exact Real.rpow_lt_one_of_one_lt_of_neg h1N (by linarith)
            rw [sub_eq_add_neg]
            exact Complex.mem_slitPlane_of_norm_lt_one
              (z := -(c i * (N i : ℂ) ^ (-(s : ℂ)))) (by simpa using hlt)
          set w : ℂ := c i * (N i : ℂ) ^ (-(s : ℂ)) with hw
          have h2N : (2 : ℝ) ≤ N i := by have := hN i; exact_mod_cast this
          have hwle : ‖w‖ ≤ 1 / 2 := by
            rw [hw, hwn]
            have hNs : (2 : ℝ) ≤ (N i : ℝ) ^ s :=
              le_trans h2N ((Real.rpow_one (N i : ℝ)).symm.trans_le
                (Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le))
            rw [Real.rpow_neg hNRpos.le, inv_le_comm₀ (Real.rpow_pos_of_pos hNRpos _) (by norm_num)]
            linarith
          have hlt : ‖w‖ < 1 := by linarith
          have hkey := Complex.norm_log_one_sub_inv_sub_self_le hlt
          rw [Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)] at hkey
          have h1 : (1 - ‖w‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
          have hsq : ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 := by
            refine hkey.trans ?_; nlinarith [sq_nonneg ‖w‖, h1, norm_nonneg w]
          have hwsq : ‖w‖ ^ 2 = (N i : ℝ) ^ (-(2 * s)) := by
            rw [hw, hwn, ← Real.rpow_natCast ((N i : ℝ) ^ (-s)) 2, ← Real.rpow_mul hNRpos.le]
            ring_nf
          exact hsq.trans (hwsq.trans_le (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)))) N c s hs hN hc i) hsumN2)
    refine ⟨Cg + ∑' i, (N i : ℝ) ^ (-(2 : ℝ)), ?_⟩
    filter_upwards [hCg, self_mem_nhdsWithin] with s hCgs hs1
    simp only [Set.mem_Ioi] at hs1
    have hsumG : Summable (fun i ↦ -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))) := by
      simpa using (hsumtail s hs1).add (hsumlin s hs1)
    have hPsub : (∑' i, c i * (N i : ℂ) ^ (-(s : ℂ)))
        = (∑' i, -Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))))
          - ∑' i, (-Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ)))
            - c i * (N i : ℂ) ^ (-(s : ℂ))) := by
      rw [← hsumG.tsum_sub ((hsumG.sub (hsumlin s hs1)).congr fun i ↦ rfl)]
      exact tsum_congr fun i ↦ by ring
    rw [hPsub]
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact (norm_tsum_le_tsum_norm (hsumtail s hs1).norm).trans
      (((hsumtail s hs1).norm.tsum_le_tsum
        (fun i ↦ (show ∀ (N : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℕ) (c : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭} → ℂ) (s : ℝ) (hs : 1 < s) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ = 1) (i : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭}), (‖-Complex.log (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) - c i * (N i : ℂ) ^ (-(s : ℂ))‖ ≤ (N i : ℝ) ^ (-(2 : ℝ))) from by
          intro N c s hs hN hc i
          classical
          have hNRpos : (0 : ℝ) < N i := by have := hN i; positivity
          have hwn : ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ = (N i : ℝ) ^ (-s) := by
            rw [norm_mul, hc, one_mul, Complex.norm_natCast_cpow_of_pos (by have := hN i; lia),
              Complex.neg_re, Complex.ofReal_re]
          have hslit : (1 - c i * (N i : ℂ) ^ (-(s : ℂ))) ∈ Complex.slitPlane := by
            have h1N : (1 : ℝ) < N i := by have := hN i; exact_mod_cast (by lia : 1 < N i)
            have hlt : ‖c i * (N i : ℂ) ^ (-(s : ℂ))‖ < 1 := by
              rw [hwn]; exact Real.rpow_lt_one_of_one_lt_of_neg h1N (by linarith)
            rw [sub_eq_add_neg]
            exact Complex.mem_slitPlane_of_norm_lt_one
              (z := -(c i * (N i : ℂ) ^ (-(s : ℂ)))) (by simpa using hlt)
          set w : ℂ := c i * (N i : ℂ) ^ (-(s : ℂ)) with hw
          have h2N : (2 : ℝ) ≤ N i := by have := hN i; exact_mod_cast this
          have hwle : ‖w‖ ≤ 1 / 2 := by
            rw [hw, hwn]
            have hNs : (2 : ℝ) ≤ (N i : ℝ) ^ s :=
              le_trans h2N ((Real.rpow_one (N i : ℝ)).symm.trans_le
                (Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le))
            rw [Real.rpow_neg hNRpos.le, inv_le_comm₀ (Real.rpow_pos_of_pos hNRpos _) (by norm_num)]
            linarith
          have hlt : ‖w‖ < 1 := by linarith
          have hkey := Complex.norm_log_one_sub_inv_sub_self_le hlt
          rw [Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hslit)] at hkey
          have h1 : (1 - ‖w‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
          have hsq : ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 := by
            refine hkey.trans ?_; nlinarith [sq_nonneg ‖w‖, h1, norm_nonneg w]
          have hwsq : ‖w‖ ^ 2 = (N i : ℝ) ^ (-(2 * s)) := by
            rw [hw, hwn, ← Real.rpow_natCast ((N i : ℝ) ^ (-s)) 2, ← Real.rpow_mul hNRpos.le]
            ring_nf
          exact hsq.trans (hwsq.trans_le (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)))) N c s hs1 hN hc i) hsumN2))) N c hN2 hc1 hsummr
    (norm_logSum_bounded_nhdsGT_aux N c hN2 hc1 hsummr Lf D hDopen hmemD hLf_an hLf0 hexpeq)

/-- **Analytic input of the cyclotomic case (Dirichlet's argument).** For a nontrivial abelian
character `χ`, the twisted prime sum `Σ_𝔭 χ(Frob 𝔭) N𝔭⁻ˢ` stays bounded as `s ↓ 1`. Now discharged
modulo the complex-analytic bridge: produce the analytic extension `Lf` (LF4
`artinLSeries_analytic_extension`, itself ⟸ the geometry-of-numbers leaf
`character_sum_geometry_of_numbers_bound`), note `Lf 1 ≠ 0` (LF5 `artinLSeries_one_ne_zero`), and
feed both to `artinLSeries_prime_sum_bounded_of_analytic_extension`. So this gap is **downstream of
the same geometry-of-numbers leaf** as LF4/LF5; its only extra content is the bridge. -/
theorem artinLSeries_prime_sum_bounded_of_ne_one
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    [hAb : IsMulCommutative Gal(L/K)] (hm : m % 4 ≠ 2) (χ : galoisCharacter K L) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      ‖∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭},
          (χ (frobeniusClass K L 𝔭.1).out : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  obtain ⟨Lf, hLf_an, hLf_eq⟩ := artinLSeries_analytic_extension K L m hm χ hχ
  exact artinLSeries_prime_sum_bounded_of_analytic_extension K L χ hχ Lf hLf_an hLf_eq
    (artinLSeries_one_ne_zero K L m hm χ hχ Lf hLf_an hLf_eq)

end Chebotarev
