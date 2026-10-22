/-
Source-only continuation r4056, retaining the r4039 analytic bodies.
UNCOMPILED throughout; no native acceptance is claimed.
The sealed r4033 file is evidence, not an import: its false image split,
whole-line periodic carrier, and placeholder bridges are deliberately replaced.
Original definitions/owners and all signed modes are retained below.

The general weighted-lattice theorem consumed here was inspected in immutable
5860a2489d25479eed8a8fc3ee91719f543189ff, PeriodicEnergyTransport.lean.
Mathlib API inspection is at 56a005855ea17e0b0958f73ec801ae140b0a1679.
-/
import D5.S3.Weil.ZetaCore.Defs
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport
import D5.S3.Weil.ZetaGamma.FormCore.DomainPassage
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier
import D5.S3.Weil.ZetaGamma.FormCore.LogGraph
import D5.S3.Weil.ZetaGamma.FormCore.Carleman
import D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound
import D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation.BoundaryMuEntry
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal Topology BigOperators

namespace D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation

open D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport

def positiveFrequency {d : ℕ} (i : Fin d) : ℝ := ((i.1 + 1 : ℕ) : ℝ)

def finiteHilbertKernel {d : ℕ} (i j : Fin d) : ℂ :=
  ((1 / (positiveFrequency i + positiveFrequency j) : ℝ) : ℂ)

theorem finite_scaled_hilbert_bound (d : ℕ) (a : Fin d → ℂ) :
    ‖∑ i, ∑ j, (a i * conj (a j)) * finiteHilbertKernel i j‖ ≤
      Real.pi * ∑ i, ‖a i‖ ^ 2 := by
  let p : Fin d → ℝ := fun i => 1 / Real.sqrt (positiveFrequency i)
  let weight : Fin d → ℝ := fun _ => 1
  have hp : ∀ i, 0 < p i := by
    intro i
    dsimp [p, positiveFrequency]
    positivity
  have hsym : ∀ (i j : Fin d), ‖finiteHilbertKernel i j‖ =
      ‖finiteHilbertKernel j i‖ := by
    intro i j
    dsimp [finiteHilbertKernel]
    simp [add_comm]
  have hrow : ∀ i,
      (∑ j, ‖finiteHilbertKernel i j‖ * p j) ≤
        Real.pi * weight i * p i := by
    intro i
    have hi : 0 < i.1 + 1 := by omega
    have hscalar :=
      D5.S3.Weil.ZetaGamma.FormCore.Carleman.finite_row_sum_le_pi_fin
        (m := i.1 + 1) (d := d) hi
    have hpoint (j : Fin d) :
        ‖finiteHilbertKernel i j‖ * p j =
          p i * D5.S3.Weil.ZetaGamma.FormCore.Carleman.rowKernel
            (positiveFrequency i) (positiveFrequency j) := by
      have hi0 : 0 < positiveFrequency i := by
        dsimp [positiveFrequency]
        positivity
      have hj0 : 0 < positiveFrequency j := by
        dsimp [positiveFrequency]
        positivity
      have hsi : Real.sqrt (positiveFrequency i) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hi0)
      have hsj : Real.sqrt (positiveFrequency j) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hj0)
      have hij : positiveFrequency i + positiveFrequency j ≠ 0 :=
        ne_of_gt (add_pos hi0 hj0)
      dsimp [finiteHilbertKernel, p,
        D5.S3.Weil.ZetaGamma.FormCore.Carleman.rowKernel]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos zero_lt_one (add_pos hi0 hj0))]
      -- Only cancellation of positive square roots is needed in this identity.
      field_simp [hsi, hsj, hij] <;> ring
    calc
      ∑ j, ‖finiteHilbertKernel i j‖ * p j =
          p i * ∑ j,
            D5.S3.Weil.ZetaGamma.FormCore.Carleman.rowKernel
              (positiveFrequency i) (positiveFrequency j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact hpoint j
      _ ≤ p i * Real.pi :=
        mul_le_mul_of_nonneg_left (by simpa only [positiveFrequency] using hscalar) (hp i).le
      _ = Real.pi * weight i * p i := by
        simp [weight]
        ring
  simpa only [weight, one_mul] using
    (D5.S3.Weil.ProjectiveRayleigh.ScaledComplexQuadraticRowBound.norm_complex_quadratic_le_scaled_rows
      a finiteHilbertKernel weight p Real.pi hp hsym hrow)

def boundarySummand (L : ℝ) (j : ℕ) (m n : ℤ) : ℝ :=
  (2 / L) * (-1 : ℝ) ^ (m + n) *
    ((1 - Real.exp (-rate j * L)) *
      (rate j ^ 2 - omega L m * omega L n) /
      ((rate j ^ 2 + omega L m ^ 2) *
        (rate j ^ 2 + omega L n ^ 2)))

def boundaryEntryPartial (L : ℝ) (d : ℕ) (m n : ℤ) : ℝ :=
  ∑ j ∈ Finset.range d, boundarySummand L j m n

def finiteBoundaryQuadratic (L : ℝ) (d : ℕ) (v : ℤ → ℂ)
    (S : Finset ℤ) : ℂ :=
  ∑ m ∈ S, ∑ n ∈ S,
    (conj (v m) * v n) * (boundaryEntryPartial L d m n : ℂ)

def boundaryQuadratic (L : ℝ) (v : ℤ → ℂ) (S : Finset ℤ) : ℂ :=
  ∑ m ∈ S, ∑ n ∈ S,
    (conj (v m) * v n) * (boundaryEntry L m n : ℂ)

/-- The odd scalar kernel. Its diagonal is retained without division by `u-v`. -/
private def oddRateKernel (u v b : ℝ) : ℝ :=
  u * v / ((b ^ 2 + u ^ 2) * (b ^ 2 + v ^ 2))

private lemma oddRateKernel_nonneg {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (b : ℝ) :
    0 ≤ oddRateKernel u v b := by
  dsimp [oddRateKernel]
  positivity

private lemma oddRateKernel_antitone {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    AntitoneOn (oddRateKernel u v) (Ici 0) := by
  intro x hx y hy hxy
  have hs : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx hy).2 hxy
  dsimp [oddRateKernel]
  apply div_le_div_of_nonneg_left (mul_pos hu hv).le (by positivity)
  calc
    (x ^ 2 + u ^ 2) * (x ^ 2 + v ^ 2) ≤
        (y ^ 2 + u ^ 2) * (x ^ 2 + v ^ 2) :=
      mul_le_mul_of_nonneg_right (add_le_add_left hs _) (by positivity)
    _ ≤ (y ^ 2 + u ^ 2) * (y ^ 2 + v ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hs _) (by positivity)

/-- Full positive-half-line integral, including the tied-frequency branch. -/
private lemma oddRateKernel_integrable_integral {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntegrableOn (oddRateKernel u v) (Ioi 0) ∧
      (∫ b in Ioi (0 : ℝ), oddRateKernel u v b) = Real.pi / (2 * (u + v)) := by
  have hatan (c : ℝ) (hc : 0 < c) :
      Tendsto (fun b : ℝ => Real.arctan (b / c)) atTop (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      ((tendsto_div_const_atTop_of_pos hc).2 tendsto_id)
  by_cases huv : u = v
  · subst v
    let G : ℝ → ℝ := fun b =>
      b / (2 * (b ^ 2 + u ^ 2)) + Real.arctan (b / u) / (2 * u)
    have hder (b : ℝ) : HasDerivAt G (oddRateKernel u u b) b := by
      have hd : b ^ 2 + u ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have hd2 : 2 * (b ^ 2 + u ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hd
      have hda : 1 + (b / u) ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have ha := (hasDerivAt_id b).div
        ((((hasDerivAt_id b).pow 2).add_const (u ^ 2)).const_mul 2) hd2
      have hb := ((hasDerivAt_id b).div_const u).arctan.div_const (2 * u)
      convert ha.add hb using 1 <;> try rfl
      dsimp [oddRateKernel]
      field_simp [hu.ne', hd, hd2, hda] <;> ring
    have hinv : Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    have hden : Tendsto (fun b : ℝ => 2 * (1 + (u * b⁻¹) ^ 2)) atTop (𝓝 2) := by
      simpa using (((tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add
          ((hinv.const_mul u).pow 2)).const_mul 2)
    have hrat : Tendsto (fun b : ℝ => b / (2 * (b ^ 2 + u ^ 2))) atTop (𝓝 0) := by
      have hlim := hinv.div hden (by norm_num : (2 : ℝ) ≠ 0)
      have heq : (fun b : ℝ => b⁻¹ / (2 * (1 + (u * b⁻¹) ^ 2))) =ᶠ[atTop]
          (fun b : ℝ => b / (2 * (b ^ 2 + u ^ 2))) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
        have hd : b ^ 2 + u ^ 2 ≠ 0 := ne_of_gt (by positivity)
        have hda : 1 + (u * b⁻¹) ^ 2 ≠ 0 := ne_of_gt (by positivity)
        field_simp [hb.ne', hd, hda] <;> ring
      simpa using hlim.congr' heq
    have hlim : Tendsto G atTop (𝓝 (Real.pi / (4 * u))) := by
      convert hrat.add ((hatan u hu).div_const (2 * u)) using 1 <;>
        (try congr 1) <;> (try dsimp [G]) <;> field_simp [hu.ne'] <;> ring
    have hi := integrableOn_Ioi_deriv_of_nonneg' (a := 0)
      (fun b _ => hder b) (fun b _ => oddRateKernel_nonneg hu hu b) hlim
    refine ⟨hi, ?_⟩
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun b _ => hder b) hi hlim]
    simp only [G, zero_div, Real.arctan_zero, add_zero, sub_zero]
    congr 1
    ring
  · have hdiff : v ^ 2 - u ^ 2 ≠ 0 := by
      intro hh
      have hh' : v ^ 2 = u ^ 2 := sub_eq_zero.mp hh
      have hsq : v = u := (sq_eq_sq₀ hv.le hu.le).mp hh'
      exact huv hsq.symm
    let G : ℝ → ℝ := fun b =>
      (v * Real.arctan (b / u) - u * Real.arctan (b / v)) / (v ^ 2 - u ^ 2)
    have hder (b : ℝ) : HasDerivAt G (oddRateKernel u v b) b := by
      have hdu : b ^ 2 + u ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have hdv : b ^ 2 + v ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have hdau : 1 + (b / u) ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have hdav : 1 + (b / v) ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have ha := (((hasDerivAt_id b).div_const u).arctan).const_mul v
      have hb := (((hasDerivAt_id b).div_const v).arctan).const_mul u
      convert (ha.sub hb).div_const (v ^ 2 - u ^ 2) using 1 <;>
        simp [G, oddRateKernel, id_eq] <;>
        (try funext x) <;>
        field_simp [hu.ne', hv.ne', hdiff, hdu, hdv, hdau, hdav] <;> ring
    have hlim : Tendsto G atTop (𝓝 (Real.pi / (2 * (u + v)))) := by
      have hh := (((hatan u hu).const_mul v).sub
        ((hatan v hv).const_mul u)).div_const (v ^ 2 - u ^ 2)
      convert hh using 1 <;> congr 1
      field_simp [hdiff, (add_pos hu hv).ne'] <;> ring
    have hi := integrableOn_Ioi_deriv_of_nonneg' (a := 0)
      (fun b _ => hder b) (fun b _ => oddRateKernel_nonneg hu hv b) hlim
    refine ⟨hi, ?_⟩
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun b _ => hder b) hi hlim]
    simp [G]

/-- Complete rate comparison. The full tail is dominated before any finite
rate cutoff is used, and `u=v` is covered by the integral theorem above. -/
private lemma oddRateKernel_complete_bound {L u v : ℝ}
    (hL : 0 < L) (hu : 0 < u) (hv : 0 < v) :
    Summable (fun j : ℕ => (1 - Real.exp (-rate j * L)) * oddRateKernel u v (rate j)) ∧
      (∑' j : ℕ, (1 - Real.exp (-rate j * L)) * oddRateKernel u v (rate j)) ≤
        oddRateKernel u v (1 / 2) + Real.pi / (4 * (u + v)) := by
  let g : ℝ → ℝ := fun b => oddRateKernel u v (2 * b)
  have hanti : AntitoneOn g (Ici 0) := by
    intro x hx y hy hxy
    change oddRateKernel u v (2 * y) ≤ oddRateKernel u v (2 * x)
    exact oddRateKernel_antitone hu hv
      (show 2 * x ∈ Ici (0 : ℝ) from
        mul_nonneg (by norm_num) (show 0 ≤ x from hx))
      (show 2 * y ∈ Ici (0 : ℝ) from
        mul_nonneg (by norm_num) (show 0 ≤ y from hy))
      (by linarith)
  have hi : IntegrableOn g (Ioi 0) := by
    have hh := (integrableOn_Ioi_comp_mul_left_iff
      (oddRateKernel u v) 0 (by norm_num : (0 : ℝ) < 2)).2
        (by simpa using (oddRateKernel_integrable_integral hu hv).1)
    simpa only [mul_zero] using hh
  have hnonneg (b : ℝ) (_ : b ∈ Ioi (0 : ℝ)) : 0 ≤ g b :=
    oddRateKernel_nonneg hu hv _
  have hg : Summable (fun j : ℕ => g j) :=
    hanti.summable_of_integrableOn_Ioi_zero hi hnonneg
  have hweight (j : ℕ) : 0 ≤ 1 - Real.exp (-rate j * L) ∧
      1 - Real.exp (-rate j * L) ≤ 1 := by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [rate_pos j]))
    · exact sub_le_self _ (Real.exp_pos _).le
  have hpoint (j : ℕ) :
      (1 - Real.exp (-rate j * L)) * oddRateKernel u v (rate j) ≤ g j := by
    calc
      _ ≤ oddRateKernel u v (rate j) :=
        mul_le_of_le_one_left (oddRateKernel_nonneg hu hv _) (hweight j).2
      _ ≤ g j := by
        change oddRateKernel u v (rate j) ≤ oddRateKernel u v (2 * (j : ℝ))
        have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
        exact oddRateKernel_antitone hu hv
          (show 0 ≤ 2 * (j : ℝ) from mul_nonneg (by norm_num) hj)
          (show rate j ∈ Ici (0 : ℝ) from (rate_pos j).le)
          (by dsimp [rate]; linarith)
  have hs : Summable (fun j : ℕ =>
      (1 - Real.exp (-rate j * L)) * oddRateKernel u v (rate j)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (hweight j).1 (oddRateKernel_nonneg hu hv _)) hpoint hg
  have htail : (∑' j : ℕ,
      (1 - Real.exp (-rate (j + 1) * L)) * oddRateKernel u v (rate (j + 1))) ≤
        ∫ b in Ioi (0 : ℝ), g b := by
    exact (((summable_nat_add_iff 1).2 hs).tsum_le_tsum
      (fun j => by simpa only [Nat.cast_add, Nat.cast_one] using hpoint (j + 1))
      ((summable_nat_add_iff 1).2 hg)).trans
        (hanti.tsum_add_one_le_integral hi hnonneg)
  have hint : (∫ b in Ioi (0 : ℝ), g b) = Real.pi / (4 * (u + v)) := by
    dsimp [g]
    rw [integral_comp_mul_left_Ioi (oddRateKernel u v) 0 (by norm_num : (0 : ℝ) < 2)]
    simp only [mul_zero, smul_eq_mul]
    rw [(oddRateKernel_integrable_integral hu hv).2]
    field_simp [(add_pos hu hv).ne'] <;> ring
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_zero_add]
  have hfirst : (1 - Real.exp (-rate 0 * L)) * oddRateKernel u v (rate 0) ≤
      oddRateKernel u v (1 / 2) := by
    simpa only [rate, Nat.cast_zero, mul_zero, zero_add] using
      (mul_le_of_le_one_left (oddRateKernel_nonneg hu hv (rate 0)) (hweight 0).2)
  rw [hint] at htail
  linarith

/-- The rank-one part is paid by the original complete reciprocal-square
supplier, with zero completion below the unchanged high threshold. -/
private lemma finite_high_rank_one_bound
    (L : ℝ) (hL : 0 < L) (M : ℕ) (hM : 2 ≤ M)
    (D : ℕ) (a : Fin D → ℂ) (hlow : ∀ i, i.1 + 1 < M → a i = 0) :
    (4 / L) * (∑ i : Fin D, ‖a i‖ *
      (omega L ((i.1 + 1 : ℕ) : ℤ) /
        (1 / 4 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2))) ^ 2 ≤
      (L / (Real.pi ^ 2 * ((M : ℝ) - 1))) * ∑ i : Fin D, ‖a i‖ ^ 2 := by
  classical
  let δ : ℝ := (M : ℝ) - 1
  have hδ : 0 < δ := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    dsimp [δ]
    linarith
  let f : ℕ → ℝ := fun k => ((δ + (k : ℝ) + 1)⁻¹) ^ 2
  have hf : Summable f :=
    D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage.inverse_square_summable hδ
  have hfull : (∑' k : ℕ, f k) ≤ δ⁻¹ :=
    Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _)
      (D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage.inverse_square_partial_le hδ)
  let r : Fin D → ℝ := fun i => omega L ((i.1 + 1 : ℕ) : ℤ) /
    (1 / 4 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2)
  let t : Fin D → ℝ := fun i => if M ≤ i.1 + 1 then r i else 0
  let A : Finset (Fin D) := Finset.univ.filter (fun i => M ≤ i.1 + 1)
  let J : Finset ℕ := A.image (fun i => i.1 + 1 - M)
  let C : ℝ := (L / (2 * Real.pi)) ^ 2
  have hJinj : ∀ i ∈ A, ∀ j ∈ A,
      i.1 + 1 - M = j.1 + 1 - M → i = j := by
    intro i hi j hj hij
    have him : M ≤ i.1 + 1 := (Finset.mem_filter.mp hi).2
    have hjm : M ≤ j.1 + 1 := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    omega
  have hpoint (i : Fin D) (hi : i ∈ A) : (r i) ^ 2 ≤ C * f (i.1 + 1 - M) := by
    have hiM : M ≤ i.1 + 1 := (Finset.mem_filter.mp hi).2
    have hu : 0 < omega L ((i.1 + 1 : ℕ) : ℤ) := by dsimp [omega]; positivity
    have hr : 0 ≤ r i := by
      dsimp [r]
      exact div_nonneg (le_of_lt hu) (by positivity)
    have hle : r i ≤ 1 / omega L ((i.1 + 1 : ℕ) : ℤ) := by
      let x : ℝ := omega L ((i.1 + 1 : ℕ) : ℤ)
      have hx : 0 < x := by dsimp [x]; exact hu
      have hxx : x / (1 / 4 + x ^ 2) ≤ 1 / x := by
        apply (div_le_div_iff₀ (by positivity) hx).2
        nlinarith [sq_nonneg x]
      simpa [r, x] using hxx
    calc
      (r i) ^ 2 ≤ (1 / omega L ((i.1 + 1 : ℕ) : ℤ)) ^ 2 :=
        (sq_le_sq₀ hr (by positivity)).2 hle
      _ = C * f (i.1 + 1 - M) := by
        have hcast : ((i.1 + 1 - M : ℕ) : ℝ) =
            ((i.1 + 1 : ℕ) : ℝ) - (M : ℝ) := Nat.cast_sub hiM
        have hn : (((i.1 + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt (by positivity)
        dsimp [C, f, δ, omega]
        rw [hcast]
        push_cast
        have hn' : (i.1 : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
        field_simp [hL.ne', Real.pi_ne_zero, hn, hn'] <;> ring
  have ht : (∑ i : Fin D, (t i) ^ 2) ≤ C * δ⁻¹ := by
    calc
      (∑ i : Fin D, (t i) ^ 2) = ∑ i ∈ A, (r i) ^ 2 := by
        simp only [A, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : M ≤ i.1 + 1 <;> simp [t, hi]
      _ ≤ C * ∑ k ∈ J, f k := by
        rw [Finset.mul_sum, Finset.sum_image hJinj]
        exact Finset.sum_le_sum (fun i hi => hpoint i hi)
      _ ≤ C * ∑' k : ℕ, f k :=
        mul_le_mul_of_nonneg_left (hf.sum_le_tsum _ (fun _ _ => sq_nonneg _)) (sq_nonneg _)
      _ ≤ C * δ⁻¹ := mul_le_mul_of_nonneg_left hfull (sq_nonneg _)
  have heq : (∑ i : Fin D, ‖a i‖ * r i) = ∑ i : Fin D, ‖a i‖ * t i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : M ≤ i.1 + 1
    · simp only [t, if_pos hi]
    · rw [hlow i (by omega)]
      simp
  change (4 / L) * (∑ i : Fin D, ‖a i‖ * r i) ^ 2 ≤ _
  rw [heq]
  calc
    _ ≤ (4 / L) * ((∑ i : Fin D, ‖a i‖ ^ 2) * ∑ i : Fin D, (t i) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖a i‖) t) (by positivity)
    _ ≤ (4 / L) * ((∑ i : Fin D, ‖a i‖ ^ 2) * (C * δ⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ht (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
        (by positivity)
    _ = _ := by
      dsimp [C, δ]
      field_simp [hL.ne', Real.pi_ne_zero, hδ.ne'] <;> ring

/-- Exact finite rank-two factorization with the conjugate in the first slot.
This identity uses both moments before any lower estimate is taken. -/
private lemma finite_signed_moment_factorization
    (S : Finset ℤ) (z : ℤ → ℂ) (b : ℝ) (ξ : ℤ → ℝ) :
    (∑ m ∈ S, ∑ n ∈ S, (conj (z m) * z n) *
      (((b ^ 2 - ξ m * ξ n) /
        ((b ^ 2 + ξ m ^ 2) * (b ^ 2 + ξ n ^ 2)) : ℝ) : ℂ)) =
      ((b ^ 2 : ℝ) : ℂ) *
        (conj (∑ n ∈ S, z n / ((b ^ 2 + ξ n ^ 2 : ℝ) : ℂ)) *
          (∑ n ∈ S, z n / ((b ^ 2 + ξ n ^ 2 : ℝ) : ℂ))) -
        conj (∑ n ∈ S, z n * (ξ n : ℂ) / ((b ^ 2 + ξ n ^ 2 : ℝ) : ℂ)) *
          (∑ n ∈ S, z n * (ξ n : ℂ) / ((b ^ 2 + ξ n ^ 2 : ℝ) : ℂ)) := by
  classical
  have heven : ((b ^ 2 : ℝ) : ℂ) *
        (conj (∑ n ∈ S, z n / ((b ^ 2 + ξ n ^ 2 : ℝ) : ℂ)) *
          (∑ n ∈ S, z n / ((b ^ 2 + ξ n ^ 2 : ℝ) : ℂ))) =
      ∑ m ∈ S, ∑ n ∈ S, (conj (z m) * z n) *
        (((b ^ 2) / ((b ^ 2 + ξ m ^ 2) * (b ^ 2 + ξ n ^ 2)) : ℝ) : ℂ) := by
    rw [map_sum, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    simp only [map_div₀, Complex.conj_ofReal]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hodd :
      conj (∑ n ∈ S, z n * (ξ n : ℂ) / ((b ^ 2 + ξ n ^ 2 : ℝ) : ℂ)) *
          (∑ n ∈ S, z n * (ξ n : ℂ) / ((b ^ 2 + ξ n ^ 2 : ℝ) : ℂ)) =
      ∑ m ∈ S, ∑ n ∈ S, (conj (z m) * z n) *
        (((ξ m * ξ n) / ((b ^ 2 + ξ m ^ 2) * (b ^ 2 + ξ n ^ 2)) : ℝ) : ℂ) := by
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    simp only [map_div₀, map_mul, Complex.conj_ofReal]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heven, hodd, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  push_cast
  ring

/-- Zero completion of an arbitrary signed support into both frequency copies.
The dimension bounds frequencies only; it has no relation to the rate cutoff. -/
private lemma sum_signed_zero_complete {A : Type*} [AddCommMonoid A]
    (S : Finset ℤ) (D : ℕ) (hD : ∀ n ∈ S, Int.natAbs n ≤ D)
    (hzero : (0 : ℤ) ∉ S) (f : ℤ → A) (hf : ∀ n ∉ S, f n = 0) :
    (∑ n ∈ S, f n) =
      (∑ i : Fin D, f ((i.1 + 1 : ℕ) : ℤ)) +
        ∑ i : Fin D, f (-((i.1 + 1 : ℕ) : ℤ)) := by
  classical
  let pos : Fin D → ℤ := fun i => ((i.1 + 1 : ℕ) : ℤ)
  let neg : Fin D → ℤ := fun i => -((i.1 + 1 : ℕ) : ℤ)
  let P : Finset ℤ := Finset.univ.image pos
  let N : Finset ℤ := Finset.univ.image neg
  have hpos : Function.Injective pos := by
    intro i j hij
    apply Fin.ext
    dsimp [pos] at hij
    omega
  have hneg : Function.Injective neg := by
    intro i j hij
    apply hpos
    exact neg_injective hij
  have hdisj : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro n hp hn
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hn
    dsimp [pos, neg] at hi hj
    omega
  have hsub : S ⊆ P ∪ N := by
    intro n hn
    have hbound := hD n hn
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
    · have hkD : k ≤ D := by simpa using hbound
      have hk0 : 0 < k := by
        by_contra h
        have hk : k = 0 := by omega
        subst k
        exact hzero hn
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr
        ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, by dsimp [pos]; omega⟩
    · have hkD : k ≤ D := by simpa using hbound
      have hk0 : 0 < k := by
        by_contra h
        have hk : k = 0 := by omega
        subst k
        exact hzero (by simpa using hn)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr
        ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, by dsimp [neg]; omega⟩
  calc
    (∑ n ∈ S, f n) = ∑ n ∈ P ∪ N, f n :=
      Finset.sum_subset hsub (fun n _ hn => hf n hn)
    _ = (∑ n ∈ P, f n) + ∑ n ∈ N, f n := Finset.sum_union hdisj
    _ = _ := by
      rw [Finset.sum_image (fun i _ j _ hij => hpos hij),
        Finset.sum_image (fun i _ j _ hij => hneg hij)]

/- The exact signed finite estimate, with a support-derived frequency bound
   independent of the arbitrary rate cutoff. No elaboration was executed. -/
theorem finite_odd_boundary_lower_bound
    (L : ℝ) (hL : 0 < L) (M : ℕ) (hM : 2 ≤ M)
    (d : ℕ) (v : ℤ → ℂ) (S : Finset ℤ)
    (hv : ∀ n ∉ S, v n = 0)
    (hhigh : ∀ n ∈ S, M ≤ Int.natAbs n) :
    -(Real.pi / 2 + L / (Real.pi ^ 2 * (M - 1))) *
        ∑ n ∈ S, ‖v n‖ ^ 2 ≤
      (finiteBoundaryQuadratic L d v S).re := by
  classical
  let phase : ℤ → ℂ := fun n => (((-1 : ℝ) ^ n : ℝ) : ℂ)
  let w : ℤ → ℂ := fun n => phase n * v n
  have hphase_norm (n : ℤ) : ‖phase n‖ = 1 := by
    dsimp [phase]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg_one_zpow]
  have hmass : (∑ n ∈ S, ‖w n‖ ^ 2) = ∑ n ∈ S, ‖v n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [w]
    rw [norm_mul, hphase_norm]
    simp
  let D : ℕ := S.sup Int.natAbs
  have hD (n : ℤ) (hn : n ∈ S) : Int.natAbs n ≤ D :=
    Finset.le_sup hn
  have hzero : (0 : ℤ) ∉ S := by
    intro hz
    have hh := hhigh 0 hz
    simp only [Int.natAbs_zero] at hh
    omega
  have hw (n : ℤ) (hn : n ∉ S) : w n = 0 := by
    simp [w, hv n hn]
  let even : Fin D → ℂ := fun i =>
    (w ((i.1 + 1 : ℕ) : ℤ) + w (-((i.1 + 1 : ℕ) : ℤ))) / Real.sqrt 2
  let odd : Fin D → ℂ := fun i =>
    (w ((i.1 + 1 : ℕ) : ℤ) - w (-((i.1 + 1 : ℕ) : ℤ))) / Real.sqrt 2
  have hparallelogram :
      ∀ n : ℕ,
        ‖(w ((n + 1 : ℕ) : ℤ) + w (-((n + 1 : ℕ) : ℤ))) /
            Real.sqrt 2‖ ^ 2 +
          ‖(w ((n + 1 : ℕ) : ℤ) - w (-((n + 1 : ℕ) : ℤ))) /
            Real.sqrt 2‖ ^ 2 =
        ‖w ((n + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖w (-((n + 1 : ℕ) : ℤ))‖ ^ 2 := by
    intro n
    have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hn : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = (2 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hs
    simp only [norm_div, div_pow, hn]
    have hp := parallelogram_law_with_norm ℂ
      (w ((n + 1 : ℕ) : ℤ)) (w (-((n + 1 : ℕ) : ℤ)))
    linarith
  have hpairedMass : (∑ i : Fin D, ‖even i‖ ^ 2) +
      (∑ i : Fin D, ‖odd i‖ ^ 2) = ∑ n ∈ S, ‖v n‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [show ∀ i : Fin D, ‖even i‖ ^ 2 + ‖odd i‖ ^ 2 =
        ‖w ((i.1 + 1 : ℕ) : ℤ)‖ ^ 2 +
          ‖w (-((i.1 + 1 : ℕ) : ℤ))‖ ^ 2 from fun i => hparallelogram i.1]
    rw [Finset.sum_add_distrib,
      ← sum_signed_zero_complete S D hD hzero
        (fun n => ‖w n‖ ^ 2) (by intro n hn; rw [hw n hn]; simp), hmass]
  have hoddMass : (∑ i : Fin D, ‖odd i‖ ^ 2) ≤ ∑ n ∈ S, ‖v n‖ ^ 2 := by
    have heven : 0 ≤ ∑ i : Fin D, ‖even i‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  have hscaled := finite_scaled_hilbert_bound D (fun i => (‖odd i‖ : ℂ))
  have hHilbert :
      (∑ i : Fin D, ∑ j : Fin D,
        ‖odd i‖ * ‖odd j‖ / (positiveFrequency i + positiveFrequency j)) ≤
          Real.pi * ∑ i : Fin D, ‖odd i‖ ^ 2 := by
    have hid : (∑ i : Fin D, ∑ j : Fin D,
        (((‖odd i‖ : ℝ) : ℂ) * conj ((‖odd j‖ : ℝ) : ℂ)) *
          finiteHilbertKernel i j) =
        ((∑ i : Fin D, ∑ j : Fin D,
          ‖odd i‖ * ‖odd j‖ / (positiveFrequency i + positiveFrequency j) : ℝ) : ℂ) := by
      simp only [finiteHilbertKernel, Complex.conj_ofReal]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
        dsimp [positiveFrequency]
        positivity)))] at hscaled
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hscaled
  have hphasePair (m n : ℤ) :
      conj (w m) * w n = (conj (v m) * v n) *
        (((-1 : ℝ) ^ (m + n) : ℝ) : ℂ) := by
    dsimp only [w, phase]
    rw [map_mul, Complex.conj_ofReal, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    push_cast
    ring
  have hPhaseForm (q : ℕ) : finiteBoundaryQuadratic L q v S =
      ((2 / L : ℝ) : ℂ) * ∑ k ∈ Finset.range q,
        ((1 - Real.exp (-rate k * L) : ℝ) : ℂ) *
          ∑ m ∈ S, ∑ n ∈ S, (conj (w m) * w n) *
            (((rate k ^ 2 - omega L m * omega L n) /
              ((rate k ^ 2 + omega L m ^ 2) *
                (rate k ^ 2 + omega L n ^ 2)) : ℝ) : ℂ) := by
    simp only [finiteBoundaryQuadratic, boundaryEntryPartial, Complex.ofReal_sum,
      Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := S) (t := Finset.range q)]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    rw [hphasePair]
    dsimp [boundarySummand]
    push_cast
    ring
  have hωneg (n : ℤ) : omega L (-n) = -omega L n := by
    dsimp [omega]
    push_cast
    ring
  have hsqrtC : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  have hEvenMoment (b : ℝ) (hb : 0 < b) :
      (∑ n ∈ S, w n / ((b ^ 2 + omega L n ^ 2 : ℝ) : ℂ)) =
        ((Real.sqrt 2 : ℝ) : ℂ) * ∑ i : Fin D,
          even i / ((b ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2 : ℝ) : ℂ) := by
    rw [sum_signed_zero_complete S D hD hzero
      (fun n => w n / ((b ^ 2 + omega L n ^ 2 : ℝ) : ℂ))
      (by intro n hn; rw [hw n hn]; simp)]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hd : ((b ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by positivity :
        0 < b ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2))
    rw [hωneg, neg_sq]
    dsimp only [even]
    field_simp [hsqrtC, hd] <;> ring
  have hOddMoment (b : ℝ) (hb : 0 < b) :
      (∑ n ∈ S, w n * (omega L n : ℂ) /
        ((b ^ 2 + omega L n ^ 2 : ℝ) : ℂ)) =
        ((Real.sqrt 2 : ℝ) : ℂ) * ∑ i : Fin D,
          odd i * (omega L ((i.1 + 1 : ℕ) : ℤ) : ℂ) /
            ((b ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2 : ℝ) : ℂ) := by
    rw [sum_signed_zero_complete S D hD hzero
      (fun n => w n * (omega L n : ℂ) / ((b ^ 2 + omega L n ^ 2 : ℝ) : ℂ))
      (by intro n hn; rw [hw n hn]; simp)]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hd : ((b ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by positivity :
        0 < b ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2))
    simp only [hωneg, neg_sq, Complex.ofReal_neg]
    dsimp only [odd]
    field_simp [hsqrtC, hd] <;> ring
  have hMomentFactor (b : ℝ) :
      (∑ m ∈ S, ∑ n ∈ S, (conj (w m) * w n) *
        (((b ^ 2 - omega L m * omega L n) /
          ((b ^ 2 + omega L m ^ 2) * (b ^ 2 + omega L n ^ 2)) : ℝ) : ℂ)) =
        ((b ^ 2 : ℝ) : ℂ) *
          (conj (∑ n ∈ S, w n / ((b ^ 2 + omega L n ^ 2 : ℝ) : ℂ)) *
            (∑ n ∈ S, w n / ((b ^ 2 + omega L n ^ 2 : ℝ) : ℂ))) -
          conj (∑ n ∈ S, w n * (omega L n : ℂ) /
            ((b ^ 2 + omega L n ^ 2 : ℝ) : ℂ)) *
            (∑ n ∈ S, w n * (omega L n : ℂ) /
              ((b ^ 2 + omega L n ^ 2 : ℝ) : ℂ)) :=
    finite_signed_moment_factorization S w b (omega L)
  have hFactor (q : ℕ) : (finiteBoundaryQuadratic L q v S).re =
      (4 / L) * ∑ k ∈ Finset.range q,
        (1 - Real.exp (-rate k * L)) *
          (rate k ^ 2 *
            ‖∑ i : Fin D, even i /
              ((rate k ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2 : ℝ) : ℂ)‖ ^ 2 -
            ‖∑ i : Fin D, odd i * (omega L ((i.1 + 1 : ℕ) : ℤ) : ℂ) /
              ((rate k ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2 : ℝ) : ℂ)‖ ^ 2) := by
    have hnormsqrt : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = (2 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sq_sqrt (by norm_num)
    have hnorm_mul (z : ℂ) : ‖((Real.sqrt 2 : ℝ) : ℂ) * z‖ ^ 2 = 2 * ‖z‖ ^ 2 := by
      rw [norm_mul, mul_pow, hnormsqrt]
    have hcomplex : finiteBoundaryQuadratic L q v S =
        (((4 / L) * ∑ k ∈ Finset.range q,
          (1 - Real.exp (-rate k * L)) *
            (rate k ^ 2 *
              ‖∑ i : Fin D, even i /
                ((rate k ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2 : ℝ) : ℂ)‖ ^ 2 -
              ‖∑ i : Fin D, odd i * (omega L ((i.1 + 1 : ℕ) : ℤ) : ℂ) /
                ((rate k ^ 2 + omega L ((i.1 + 1 : ℕ) : ℤ) ^ 2 : ℝ) : ℂ)‖ ^ 2) : ℝ) : ℂ) := by
      rw [hPhaseForm]
      -- Keep the cast of the rational matrix entry intact for hMomentFactor.
      simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sub,
        Complex.ofReal_pow]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hMomentFactor]
      simp_rw [hEvenMoment (rate k) (rate_pos k), hOddMoment (rate k) (rate_pos k)]
      simp only [Complex.conj_mul', ← Complex.ofReal_pow, hnorm_mul]
      push_cast
      ring
    simpa only [Complex.ofReal_re] using congrArg Complex.re hcomplex
  have hlow (i : Fin D) (hi : i.1 + 1 < M) : odd i = 0 := by
    have hp : ((i.1 + 1 : ℕ) : ℤ) ∉ S := by
      intro hn
      have hh := hhigh _ hn
      simp only [Int.natAbs_natCast] at hh
      omega
    have hn : (-((i.1 + 1 : ℕ) : ℤ)) ∉ S := by
      intro hn
      have hh := hhigh _ hn
      simp only [Int.natAbs_neg, Int.natAbs_natCast] at hh
      omega
    change (w ((i.1 + 1 : ℕ) : ℤ) - w (-((i.1 + 1 : ℕ) : ℤ))) /
      ((Real.sqrt 2 : ℝ) : ℂ) = 0
    rw [hw _ hp, hw _ hn]
    simp
  have hRankOne := finite_high_rank_one_bound L hL M hM D odd hlow
  have hfinite :
      ∀ q : ℕ, -(Real.pi / 2 + L / (Real.pi ^ 2 * (M - 1))) *
          ∑ n ∈ S, ‖v n‖ ^ 2 ≤
        (finiteBoundaryQuadratic L q v S).re := by
    intro q
    have hRateBounds (i j : Fin D) :
        (∑ k ∈ Finset.range q,
          (1 - Real.exp (-rate k * L)) *
            oddRateKernel (omega L ((i.1 + 1 : ℕ) : ℤ))
              (omega L ((j.1 + 1 : ℕ) : ℤ)) (rate k)) ≤
          oddRateKernel (omega L ((i.1 + 1 : ℕ) : ℤ))
              (omega L ((j.1 + 1 : ℕ) : ℤ)) (1 / 2) +
            Real.pi / (4 * (omega L ((i.1 + 1 : ℕ) : ℤ) +
              omega L ((j.1 + 1 : ℕ) : ℤ))) := by
      have hui : 0 < omega L ((i.1 + 1 : ℕ) : ℤ) := by dsimp [omega]; positivity
      have huj : 0 < omega L ((j.1 + 1 : ℕ) : ℤ) := by dsimp [omega]; positivity
      have hb := oddRateKernel_complete_bound hL hui huj
      exact (hb.1.sum_le_tsum _ (fun k _ => by
        apply mul_nonneg
        · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [rate_pos k]))
        · exact oddRateKernel_nonneg hui huj _)).trans hb.2
    let u : Fin D → ℝ := fun i => omega L ((i.1 + 1 : ℕ) : ℤ)
    let r : ℝ → Fin D → ℝ := fun b i => u i / (b ^ 2 + u i ^ 2)
    let A : Fin D → ℝ := fun i => ‖odd i‖
    have hu (i : Fin D) : 0 < u i := by dsimp [u, omega]; positivity
    have hr (b : ℝ) (i : Fin D) : 0 ≤ r b i := by
      dsimp [r]
      exact div_nonneg (le_of_lt (hu i)) (by positivity)
    have hwgt (k : ℕ) : 0 ≤ 1 - Real.exp (-rate k * L) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [rate_pos k]))
    have htriangle (k : ℕ) :
        ‖∑ i : Fin D, odd i * (u i : ℂ) /
          ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2 ≤
          (∑ i : Fin D, A i * r (rate k) i) ^ 2 := by
      apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
        (fun i _ => mul_nonneg (norm_nonneg _) (hr _ i)))).2
      calc
        _ ≤ ∑ i : Fin D, ‖odd i * (u i : ℂ) /
            ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          have hd : 0 < rate k ^ 2 + u i ^ 2 :=
            add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hu i))
          simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (hu i), abs_of_pos hd]
          dsimp [A, r]
          ring
    have hexpand (k : ℕ) :
        (1 - Real.exp (-rate k * L)) * (∑ i : Fin D, A i * r (rate k) i) ^ 2 =
          ∑ i : Fin D, ∑ j : Fin D, A i * A j *
            ((1 - Real.exp (-rate k * L)) * oddRateKernel (u i) (u j) (rate k)) := by
      rw [pow_two, Finset.sum_mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [r, oddRateKernel]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    have hentry (i j : Fin D) :
        (4 / L) * (∑ k ∈ Finset.range q,
          (1 - Real.exp (-rate k * L)) * oddRateKernel (u i) (u j) (rate k)) ≤
          (4 / L) * r (1 / 2) i * r (1 / 2) j +
            1 / (2 * (positiveFrequency i + positiveFrequency j)) := by
      have hb := mul_le_mul_of_nonneg_left (hRateBounds i j)
        (by positivity : 0 ≤ (4 : ℝ) / L)
      have hfirst : oddRateKernel (u i) (u j) (1 / 2) =
          r (1 / 2) i * r (1 / 2) j := by
        dsimp [oddRateKernel, r]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      have htail : (4 / L) * (Real.pi / (4 * (u i + u j))) =
          1 / (2 * (positiveFrequency i + positiveFrequency j)) := by
        have hi : 0 < positiveFrequency i := by dsimp [positiveFrequency]; positivity
        have hj : 0 < positiveFrequency j := by dsimp [positiveFrequency]; positivity
        have hs : positiveFrequency i + positiveFrequency j ≠ 0 := (add_pos hi hj).ne'
        have huval (i : Fin D) : u i = (2 * Real.pi / L) * positiveFrequency i := by
          dsimp [u, omega, positiveFrequency]
          push_cast
          ring
        rw [huval i, huval j, ← mul_add]
        field_simp [hL.ne', Real.pi_ne_zero, hs] <;> ring
      change (4 / L) * _ ≤ (4 / L) *
        (oddRateKernel (u i) (u j) (1 / 2) + Real.pi / (4 * (u i + u j))) at hb
      rw [mul_add, hfirst, htail] at hb
      simpa only [mul_assoc] using hb
    have hoddBound :
        (4 / L) * (∑ k ∈ Finset.range q,
          (1 - Real.exp (-rate k * L)) *
            ‖∑ i : Fin D, odd i * (u i : ℂ) /
              ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2) ≤
          (Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1))) *
            ∑ i : Fin D, ‖odd i‖ ^ 2 := by
      calc
        _ ≤ (4 / L) * ∑ k ∈ Finset.range q,
            (1 - Real.exp (-rate k * L)) * (∑ i : Fin D, A i * r (rate k) i) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun k _ =>
            mul_le_mul_of_nonneg_left (htriangle k) (hwgt k))
        _ = ∑ i : Fin D, ∑ j : Fin D, A i * A j *
            ((4 / L) * ∑ k ∈ Finset.range q,
              (1 - Real.exp (-rate k * L)) * oddRateKernel (u i) (u j) (rate k)) := by
          simp_rw [hexpand, Finset.mul_sum]
          rw [Finset.sum_comm (s := Finset.range q) (t := (Finset.univ : Finset (Fin D)))]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm (s := Finset.range q) (t := (Finset.univ : Finset (Fin D)))]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ ≤ ∑ i : Fin D, ∑ j : Fin D, A i * A j *
            ((4 / L) * r (1 / 2) i * r (1 / 2) j +
              1 / (2 * (positiveFrequency i + positiveFrequency j))) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hentry i j)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = (4 / L) * (∑ i : Fin D, A i * r (1 / 2) i) ^ 2 +
            (1 / 2 : ℝ) * ∑ i : Fin D, ∑ j : Fin D,
              A i * A j / (positiveFrequency i + positiveFrequency j) := by
          rw [pow_two, Finset.sum_mul_sum]
          simp_rw [Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ ≤ (L / (Real.pi ^ 2 * ((M : ℝ) - 1))) * (∑ i : Fin D, ‖odd i‖ ^ 2) +
            (1 / 2 : ℝ) * (Real.pi * ∑ i : Fin D, ‖odd i‖ ^ 2) := by
          apply add_le_add
          · simpa only [A, r, u, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num] using hRankOne
          · exact mul_le_mul_of_nonneg_left hHilbert (by norm_num)
        _ = _ := by ring
    rw [hFactor q]
    have hδ : 0 < (M : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have hC : 0 ≤ Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1)) := by positivity
    have hmassBound := mul_le_mul_of_nonneg_left hoddMass hC
    have heven : 0 ≤ (4 / L) * ∑ k ∈ Finset.range q,
        (1 - Real.exp (-rate k * L)) * rate k ^ 2 *
          ‖∑ i : Fin D, even i /
            ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2 := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (mul_nonneg (hwgt k) (sq_nonneg _)) (sq_nonneg _))
    have hdecomp :
        (4 / L) * (∑ k ∈ Finset.range q, (1 - Real.exp (-rate k * L)) *
          (rate k ^ 2 * ‖∑ i : Fin D, even i /
            ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2 -
            ‖∑ i : Fin D, odd i * (u i : ℂ) /
              ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2)) =
          (4 / L) * (∑ k ∈ Finset.range q,
            (1 - Real.exp (-rate k * L)) * rate k ^ 2 *
              ‖∑ i : Fin D, even i / ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2) -
            (4 / L) * ∑ k ∈ Finset.range q,
              (1 - Real.exp (-rate k * L)) *
                ‖∑ i : Fin D, odd i * (u i : ℂ) /
                  ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      ring
    change -(Real.pi / 2 + L / (Real.pi ^ 2 * ((M : ℝ) - 1))) * _ ≤
      (4 / L) * (∑ k ∈ Finset.range q, (1 - Real.exp (-rate k * L)) *
        (rate k ^ 2 * ‖∑ i : Fin D, even i / ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2 -
          ‖∑ i : Fin D, odd i * (u i : ℂ) / ((rate k ^ 2 + u i ^ 2 : ℝ) : ℂ)‖ ^ 2))
    rw [hdecomp]
    linarith
  exact hfinite d

/- The complete consumer targets the literal original `boundaryEntry`.
   Absolute summability and finite-sum continuity carry every finite partial
   lower bound to that complete series. Native acceptance remains open. -/
theorem boundaryEntry_odd_lower_bound
    (L : ℝ) (hL : 0 < L) (M : ℕ) (hM : 2 ≤ M)
    (v : ℤ → ℂ) (S : Finset ℤ)
    (hv : ∀ n ∉ S, v n = 0)
    (hhigh : ∀ n ∈ S, M ≤ Int.natAbs n) :
    -(Real.pi / 2 + L / (Real.pi ^ 2 * (M - 1))) *
        ∑ n ∈ S, ‖v n‖ ^ 2 ≤
      (boundaryQuadratic L v S).re := by
  classical
  have hpartial := fun d => finite_odd_boundary_lower_bound
    L hL M hM d v S hv hhigh
  have hentry (m n : ℤ) :
      Tendsto (fun d : ℕ => boundaryEntryPartial L d m n) atTop
        (𝓝 (boundaryEntry L m n)) := by
    have hraw : Summable (fun j : ℕ =>
        (1 - Real.exp (-rate j * L)) *
          (rate j ^ 2 - omega L m * omega L n) /
          ((rate j ^ 2 + omega L m ^ 2) *
            (rate j ^ 2 + omega L n ^ 2))) :=
      Summable.of_norm (by
        simpa only [Real.norm_eq_abs] using
          boundary_series_absolutely_summable L hL m n)
    have hsum := hraw.mul_left ((2 / L) * (-1 : ℝ) ^ (m + n))
    have hlim := hsum.hasSum.tendsto_sum_nat
    simpa only [boundaryEntryPartial, boundarySummand, boundaryEntry,
      tsum_mul_left] using hlim
  have hq : Tendsto (fun d : ℕ => finiteBoundaryQuadratic L d v S) atTop
      (𝓝 (boundaryQuadratic L v S)) := by
    apply tendsto_finsetSum S
    intro m hm
    apply tendsto_finsetSum S
    intro n hn
    exact tendsto_const_nhds.mul
      ((Complex.ofRealCLM.continuous.tendsto _).comp (hentry m n))
  have hre : Tendsto (fun d : ℕ => (finiteBoundaryQuadratic L d v S).re) atTop
      (𝓝 (boundaryQuadratic L v S).re) :=
    (Complex.continuous_re.tendsto _).comp hq
  exact ge_of_tendsto' hre hpartial


end D5.S3.Weil.ZetaGamma.OriginalComplexMatrix.Continuation
