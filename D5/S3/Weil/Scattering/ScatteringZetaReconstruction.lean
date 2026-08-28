/- GID: D5/S3/Weil/Scattering/ScatteringZetaReconstruction
   generality: I
   mirror-B: D5/B/S3/Weil/Scattering/ScatteringZetaReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Shifted normalized scattering readings telescope to the Riemann zeta function. -/

import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace D5.S3.Weil.Scattering.ScatteringZetaReconstruction

open Filter

/-!
Search receipt (2026-08-28): pinned Mathlib supplies `LSeries.tendsto_atTop`,
`LSeries.abscissaOfAbsConv_le_of_le_const`, `Complex.cpow_add`, and zeta nonvanishing on
`re s > 1`. No D5 or Mathlib theorem states this scattering reconstruction product.
-/

private lemma riemann_zeta_tendsto_one_along_nat (z : ℂ) :
    Tendsto (fun n : ℕ => riemannZeta (z + n)) atTop (nhds 1) := by
  let f : ℕ → ℂ := fun n => (n : ℂ) ^ (-Complex.I * z.im)
  have hf_bounded : ∃ C : ℝ, ∀ n ≠ 0, ‖f n‖ ≤ C := by
    refine ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    simp only [f, Complex.norm_natCast_cpow_of_pos hnpos]
    norm_num
  have habscissa : LSeries.abscissaOfAbsConv f < ⊤ :=
    (LSeries.abscissaOfAbsConv_le_of_le_const hf_bounded).trans_lt (EReal.coe_lt_top 1)
  have hL : Tendsto (fun x : ℝ => LSeries f x) atTop (nhds 1) := by
    simpa [f] using LSeries.tendsto_atTop habscissa
  have heq (x : ℝ) (hx : 1 < x) :
      LSeries f x = riemannZeta ((x : ℂ) + Complex.I * z.im) := by
    rw [← LSeries_one_eq_riemannZeta (by simpa using hx)]
    unfold LSeries
    apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp only [LSeries.term_of_ne_zero hn, f, Pi.one_apply]
      rw [show -Complex.I * (z.im : ℂ) = -(Complex.I * (z.im : ℂ)) by ring,
        Complex.cpow_neg, Complex.cpow_add _ _ hncast]
      have hxpow : (n : ℂ) ^ (x : ℂ) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hncast)
      have hypow : (n : ℂ) ^ (Complex.I * (z.im : ℂ)) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hncast)
      field_simp
  have heventual : (fun x : ℝ => LSeries f x) =ᶠ[atTop]
      (fun x : ℝ => riemannZeta ((x : ℂ) + Complex.I * z.im)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact heq x hx
  have hvertical : Tendsto
      (fun x : ℝ => riemannZeta ((x : ℂ) + Complex.I * z.im)) atTop (nhds 1) :=
    hL.congr' heventual
  have hnat : Tendsto (fun n : ℕ => (z.re + n : ℝ)) atTop atTop := by
    simpa [add_comm] using
      tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => z.re) atTop (nhds z.re))
  convert hvertical.comp hnat using 1
  · funext n
    congr 1
    apply Complex.ext <;> simp

private lemma archimedean_scattering_factor (s : ℂ) (hs : 1 / 2 < s.re)
    (hszeta : 1 < (2 * s).re) :
    (((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.Gamma (s - 1 / 2) /
        Complex.Gamma s *
        (riemannZeta (2 * s - 1) / riemannZeta (2 * s))) *
        Complex.Gamma s /
        ((((Real.sqrt Real.pi : ℝ) : ℂ)) * Complex.Gamma (s - 1 / 2)) =
      riemannZeta (2 * s - 1) / riemannZeta (2 * s) := by
  have hgamma : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    linarith
  have hgammaShift : Complex.Gamma (s - 1 / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simpa using hs
  have hgammaShift' : Complex.Gamma (-1 / 2 + s) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num at ⊢
    linarith
  have hgammaNorm : Complex.Gamma ((-1 + 2 * s) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num at ⊢
    linarith
  have hsqrt : (((Real.sqrt Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hzeta : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hszeta
  have hzeta' : riemannZeta (s * 2) ≠ 0 := by simpa [mul_comm] using hzeta
  field_simp [hgamma, hgammaShift, hgammaShift', hgammaNorm, hsqrt, hzeta, hzeta']
  ring_nf
  field_simp [hgammaShift', hgammaNorm]

/-- On `re z > 1`, both the normalized zeta-ratio product and its fully expanded modular
scattering form have partial products converging to `ζ(z)`. -/
theorem scattering_zeta_reconstruction (z : ℂ) (hz : 1 < z.re) :
    Tendsto
      (fun N : ℕ => ∏ j ∈ Finset.range N,
        riemannZeta (2 * ((z + j + 1) / 2) - 1) /
          riemannZeta (2 * ((z + j + 1) / 2)))
      atTop (nhds (riemannZeta z)) ∧
    Tendsto
      (fun N : ℕ => ∏ j ∈ Finset.range N,
        ((((Real.sqrt Real.pi : ℝ) : ℂ) *
            Complex.Gamma (((z + j + 1) / 2) - 1 / 2) /
            Complex.Gamma ((z + j + 1) / 2) *
            (riemannZeta (2 * ((z + j + 1) / 2) - 1) /
              riemannZeta (2 * ((z + j + 1) / 2)))) *
          Complex.Gamma ((z + j + 1) / 2) /
          ((((Real.sqrt Real.pi : ℝ) : ℂ)) * Complex.Gamma ((z + j) / 2))))
      atTop (nhds (riemannZeta z)) := by
  have hpartial (N : ℕ) :
      (∏ j ∈ Finset.range N,
        riemannZeta (2 * ((z + j + 1) / 2) - 1) /
          riemannZeta (2 * ((z + j + 1) / 2))) =
        riemannZeta z / riemannZeta (z + N) := by
    calc
      _ = ∏ j ∈ Finset.range N,
          riemannZeta (z + j) / riemannZeta (z + (j + 1)) := by
        apply Finset.prod_congr rfl
        intro j hj
        congr 2 <;> ring
      _ = riemannZeta z / riemannZeta (z + N) := by
        have hnonzero (k : ℕ) : riemannZeta (z + k) ≠ 0 := by
          apply riemannZeta_ne_zero_of_one_lt_re
          have hre : z.re ≤ z.re + (k : ℝ) :=
            le_add_of_nonneg_right (Nat.cast_nonneg k)
          simpa using hz.trans_le hre
        induction N with
        | zero =>
            simpa only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, add_zero] using
              (div_self (by simpa using hnonzero 0)).symm
        | succ N ih =>
            rw [Finset.prod_range_succ, ih]
            simp only [Nat.cast_add, Nat.cast_one]
            field_simp [hnonzero N, hnonzero (N + 1)]
  have htail := riemann_zeta_tendsto_one_along_nat z
  have hratio : Tendsto (fun N : ℕ => riemannZeta z / riemannZeta (z + N))
      atTop (nhds (riemannZeta z)) := by
    have hconst : Tendsto (fun _ : ℕ => riemannZeta z) atTop (nhds (riemannZeta z)) :=
      tendsto_const_nhds
    have ht := hconst.div htail one_ne_zero
    rw [div_one] at ht
    refine ht.congr' ?_
    exact Filter.Eventually.of_forall fun N => rfl
  have hfirst : Tendsto
      (fun N : ℕ => ∏ j ∈ Finset.range N,
        riemannZeta (2 * ((z + j + 1) / 2) - 1) /
          riemannZeta (2 * ((z + j + 1) / 2)))
      atTop (nhds (riemannZeta z)) :=
    hratio.congr' (Filter.Eventually.of_forall fun N => (hpartial N).symm)
  refine ⟨hfirst, hfirst.congr' (Filter.Eventually.of_forall fun N => ?_)⟩
  apply Finset.prod_congr rfl
  intro j hj
  have hjnonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hs : (1 / 2 : ℝ) < ((z + j + 1) / 2).re := by
    norm_num at ⊢
    linarith
  have hszeta : 1 < (2 * ((z + j + 1) / 2)).re := by
    norm_num at ⊢
    linarith
  symm
  convert archimedean_scattering_factor ((z + j + 1) / 2) hs hszeta using 1
  all_goals ring_nf

end D5.S3.Weil.Scattering.ScatteringZetaReconstruction
