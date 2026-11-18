/- GID: D5/S3/AnalyticClosure/ThreePunctureResidue
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/ThreePunctureResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-puncture residue balance and its two coordinate changes. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Liouville

/-! Finite Laurent expansions at the three punctures of the Riemann sphere. -/

open Filter Set
open scoped BigOperators Topology

namespace D5.S3.AnalyticClosure.ThreePunctureResidue

/-- The principal part centered at `a`, ordered from the simple pole upwards. -/
noncomputable def principalPart (a : ℂ) (n : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, c j * (z - a)⁻¹ ^ (j + 1)

/-- The coefficient at exponent `-1`, including an empty principal part. -/
def simpleCoeff (n : ℕ) (c : ℕ → ℂ) : ℂ :=
  if 0 < n then c 0 else 0

private theorem analyticAt_principalPart {a x : ℂ} (h : x ≠ a) (n : ℕ) (c : ℕ → ℂ) :
    AnalyticAt ℂ (principalPart a n c) x := by
  apply Finset.analyticAt_fun_sum
  intro j _
  have hbase : AnalyticAt ℂ (fun z : ℂ ↦ z - a) x := by fun_prop
  exact analyticAt_const.mul ((hbase.inv (sub_ne_zero.mpr h)).pow _)

private theorem hasDerivAt_sum_powers {f : ℂ → ℂ} {d : ℂ}
    (hf : HasDerivAt f d 0) (hf0 : f 0 = 0) (n : ℕ) (c : ℕ → ℂ) :
    HasDerivAt (fun u ↦ ∑ j ∈ Finset.range n, c j * f u ^ (j + 1))
      (simpleCoeff n c * d) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.range n)
    (fun j _ ↦ (hf.pow (j + 1)).const_mul (c j))
  convert h using 1
  simp only [hf0, Nat.add_sub_cancel]
  cases n with
  | zero => simp [simpleCoeff]
  | succ n =>
    rw [Finset.sum_range_succ']
    simp [simpleCoeff, add_comm]

/-- The scalar inverse-chart remainder has first Taylor coefficient equal to the sum of
the finite residues. The hypotheses are punctured-neighborhood Laurent expansions. -/
theorem deriv_inverse_remainder
    {G h0 h1 hInf : ℂ → ℂ} {n0 n1 nInf : ℕ} {c0 c1 cInf : ℕ → ℂ}
    (hG : ∀ z, z ≠ 0 → z ≠ 1 → DifferentiableAt ℂ G z)
    (ha0 : AnalyticAt ℂ h0 0) (ha1 : AnalyticAt ℂ h1 1)
    (haInf : AnalyticAt ℂ hInf 0)
    (hex0 : G =ᶠ[𝓝[≠] 0] fun z ↦ principalPart 0 n0 c0 z + h0 z)
    (hex1 : G =ᶠ[𝓝[≠] 1] fun z ↦ principalPart 1 n1 c1 z + h1 z)
    (hexInf : (fun u : ℂ ↦ G u⁻¹) =ᶠ[𝓝[≠] 0]
      fun u ↦ principalPart 0 nInf cInf u + hInf u) :
    deriv hInf 0 = simpleCoeff n0 c0 + simpleCoeff n1 c1 := by
  let P0 := principalPart 0 n0 c0
  let P1 := principalPart 1 n1 c1
  let P : ℂ → ℂ := fun z ↦ ∑ j ∈ Finset.range nInf, cInf j * z ^ (j + 1)
  let H0 : ℂ → ℂ := fun z ↦ h0 z - P1 z - P z
  let H1 : ℂ → ℂ := fun z ↦ h1 z - P0 z - P z
  let H : ℂ → ℂ := fun z ↦
    if z = 0 then H0 0 else if z = 1 then H1 1 else G z - P0 z - P1 z - P z
  have hP (z : ℂ) : AnalyticAt ℂ P z := by
    apply Finset.analyticAt_fun_sum
    intro j _
    fun_prop
  have hH0 : H =ᶠ[𝓝 0] H0 := by
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · filter_upwards [hex0, self_mem_nhdsWithin,
        eventually_ne_nhdsWithin (s := ({0}ᶜ : Set ℂ)) (zero_ne_one' ℂ)] with
        z hz hz0 hz1
      have hz0' : z ≠ 0 := hz0
      simp only [H, P0, H0, ite_eq_right hz0', ite_eq_right hz1, hz, add_sub_cancel_left]
    · simp [H]
  have hH1 : H =ᶠ[𝓝 1] H1 := by
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · filter_upwards [hex1, self_mem_nhdsWithin,
        eventually_ne_nhdsWithin (s := ({1}ᶜ : Set ℂ)) (one_ne_zero' ℂ)] with
        z hz hz1 hz0
      have hz1' : z ≠ 1 := hz1
      simp only [H, P1, H1, ite_eq_right hz0, ite_eq_right hz1', hz]
      ring
    · simp [H]
  have hH : Differentiable ℂ H := by
    intro z
    by_cases hz0 : z = 0
    · subst z
      exact ((ha0.sub (analyticAt_principalPart (zero_ne_one' ℂ) n1 c1)).sub
        (hP 0) |>.congr hH0.symm).differentiableAt
    by_cases hz1 : z = 1
    · subst z
      exact ((ha1.sub (analyticAt_principalPart (one_ne_zero' ℂ) n0 c0)).sub
        (hP 1) |>.congr hH1.symm).differentiableAt
    have hEq : H =ᶠ[𝓝 z] fun w ↦ G w - P0 w - P1 w - P w := by
      filter_upwards [eventually_ne_nhds hz0, eventually_ne_nhds hz1] with w hw0 hw1
      simp [H, hw0, hw1]
    exact ((((hG z hz0 hz1).sub
      (analyticAt_principalPart hz0 n0 c0).differentiableAt).sub
      (analyticAt_principalPart hz1 n1 c1).differentiableAt).sub
      (hP z).differentiableAt).congr_of_eventuallyEq hEq
  let q : ℂ → ℂ := fun u ↦ u / (1 - u)
  let S0 : ℂ → ℂ := fun u ↦ ∑ j ∈ Finset.range n0, c0 j * u ^ (j + 1)
  let S1 : ℂ → ℂ := fun u ↦ ∑ j ∈ Finset.range n1, c1 j * q u ^ (j + 1)
  let K : ℂ → ℂ := fun u ↦ hInf u - S0 u - S1 u
  have hq : HasDerivAt q 1 0 := by
    have hden := (hasDerivAt_id (0 : ℂ)).const_sub 1
    simpa [q] using (hasDerivAt_id (0 : ℂ)).fun_div hden (by simp)
  have hq0 : q 0 = 0 := by simp [q]
  have hKderiv : HasDerivAt K
      (deriv hInf 0 - simpleCoeff n0 c0 - simpleCoeff n1 c1) 0 := by
    simpa [K, S0, S1] using
      (haInf.differentiableAt.hasDerivAt.fun_sub
        (hasDerivAt_sum_powers (hasDerivAt_id (0 : ℂ)) rfl n0 c0)).fun_sub
        (hasDerivAt_sum_powers hq hq0 n1 c1)
  have hK0 : K 0 = hInf 0 := by simp [K, S0, S1, hq0]
  have hK : (fun u : ℂ ↦ H u⁻¹) =ᶠ[𝓝[≠] 0] K := by
    filter_upwards [hexInf, self_mem_nhdsWithin,
      eventually_ne_nhdsWithin (s := ({0}ᶜ : Set ℂ)) (zero_ne_one' ℂ)] with
      u hu hu0 hu1
    have hu0' : u ≠ 0 := hu0
    have hinv0 : u⁻¹ ≠ 0 := inv_ne_zero hu0'
    have hinv1 : u⁻¹ ≠ 1 := by simpa using hu1
    have hinvSub : (u⁻¹ - 1)⁻¹ = q u := by
      have hsub : u⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hinv1
      have hden : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
      dsimp [q]
      field_simp [hu0', hsub, hden]
    simp only [H, ite_eq_right hinv0, ite_eq_right hinv1, hu, K, P0, P1, principalPart, P,
      S0, S1, sub_zero, inv_inv, hinvSub]
    ring
  have hinv := Filter.tendsto_inv₀_cobounded' (α := ℂ)
  have hlim : Tendsto H (cocompact ℂ) (𝓝 (hInf 0)) := by
    rw [← Metric.cobounded_eq_cocompact]
    have hlimK : Tendsto K (𝓝[≠] 0) (𝓝 (hInf 0)) :=
      hK0 ▸ hKderiv.continuousAt.continuousWithinAt
    have heq : H =ᶠ[Bornology.cobounded ℂ] fun z ↦ K z⁻¹ := by
      filter_upwards [hinv.eventually hK] with z hz
      simpa using hz
    exact (hlimK.comp hinv).congr' heq.symm
  have hconst := hH.eq_const_of_tendsto_cocompact hlim
  have hKconst : K =ᶠ[𝓝 0] fun _ ↦ hInf 0 := by
    apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    · simpa [hconst, Function.const] using hK.symm
    · exact hK0
  have hd := (hKderiv.congr_of_eventuallyEq hKconst.symm).deriv
  simp at hd
  linear_combination -hd

/-- The infinity residue of `G(z) dz` is `-deriv hInf 0` because the inverse chart
pulls the differential back to `-u⁻² * G(u⁻¹) du`. -/
theorem residue_sum
    {G h0 h1 hInf : ℂ → ℂ} {n0 n1 nInf : ℕ} {c0 c1 cInf : ℕ → ℂ}
    (hG : ∀ z, z ≠ 0 → z ≠ 1 → DifferentiableAt ℂ G z)
    (ha0 : AnalyticAt ℂ h0 0) (ha1 : AnalyticAt ℂ h1 1)
    (haInf : AnalyticAt ℂ hInf 0)
    (hex0 : G =ᶠ[𝓝[≠] 0] fun z ↦ principalPart 0 n0 c0 z + h0 z)
    (hex1 : G =ᶠ[𝓝[≠] 1] fun z ↦ principalPart 1 n1 c1 z + h1 z)
    (hexInf : (fun u : ℂ ↦ G u⁻¹) =ᶠ[𝓝[≠] 0]
      fun u ↦ principalPart 0 nInf cInf u + hInf u) :
    simpleCoeff n0 c0 + simpleCoeff n1 c1 + (-deriv hInf 0) = 0 := by
  rw [deriv_inverse_remainder hG ha0 ha1 haInf hex0 hex1 hexInf, add_neg_cancel]

/-- Taylor splitting after clearing a pole of order at most `n`. -/
theorem principalPart_of_analytic_numerator {f F : ℂ → ℂ} (n : ℕ)
    (hf : AnalyticAt ℂ f 0)
    (he : F =ᶠ[𝓝[≠] 0] fun u ↦ (u ^ n)⁻¹ * f u) :
    ∃ c : ℕ → ℂ, ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      (F =ᶠ[𝓝[≠] 0] fun u ↦ principalPart 0 n c u + h u) ∧
      simpleCoeff n c = if 0 < n then
        iteratedDeriv (n - 1) f 0 / ((n - 1).factorial : ℂ) else 0 := by
  let a : ℕ → ℂ := fun i ↦ iteratedDeriv i f 0 / (i.factorial : ℂ)
  let c : ℕ → ℂ := fun j ↦ a (n - 1 - j)
  obtain ⟨h, hah, ht⟩ := hf.exists_eventuallyEq_sum_add_pow_mul n
  refine ⟨c, h, hah, ?_, by simp [simpleCoeff, c, a]⟩
  filter_upwards [he, ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hut hu0
  have hne : u ≠ 0 := hu0
  have hut' : f u = (∑ i ∈ Finset.range n, u ^ i * a i) + u ^ n * h u := by
    simpa [a, smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc] using hut
  rw [hu, hut', mul_add, Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hne),
    one_mul, principalPart]
  congr 1
  rw [← Finset.sum_range_reflect (fun i ↦ (u ^ n)⁻¹ * (u ^ i * a i)) n]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have hpower : n - (n - 1 - j) = j + 1 := by omega
  have hi : n - 1 - j ≤ n := by omega
  dsimp only [c]
  rw [sub_zero, ← mul_assoc, ← inv_pow_sub₀ hne hi, hpower, mul_comm]

/-- The pullback of `G(z) dz` to the inverse chart has simple coefficient
`-deriv hInf 0`. Its pole bound is the scalar pole bound plus two. -/
theorem inverse_differential_principalPart
    {G hInf : ℂ → ℂ} {n : ℕ} {c : ℕ → ℂ}
    (ha : AnalyticAt ℂ hInf 0)
    (he : (fun u : ℂ ↦ G u⁻¹) =ᶠ[𝓝[≠] 0]
      fun u ↦ principalPart 0 n c u + hInf u) :
    ∃ b : ℕ → ℂ, ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      ((fun u : ℂ ↦ G u⁻¹ * deriv (fun v : ℂ ↦ v⁻¹) u) =ᶠ[𝓝[≠] 0]
        fun u ↦ principalPart 0 (n + 2) b u + h u) ∧
      simpleCoeff (n + 2) b = -deriv hInf 0 := by
  obtain ⟨R, hR, ht⟩ := ha.exists_eventuallyEq_sum_add_pow_mul 2
  let b : ℕ → ℂ := fun j ↦ if j = 0 then -deriv hInf 0 else
    if j = 1 then -hInf 0 else -c (j - 2)
  refine ⟨b, fun u ↦ -R u, hR.neg, ?_, by simp [simpleCoeff, b]⟩
  filter_upwards [he, ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hut hu0
  have hne : u ≠ 0 := hu0
  have ht' : hInf u = hInf 0 + u * deriv hInf 0 + u ^ 2 * R u := by
    simpa [Finset.sum_range_succ, iteratedDeriv_one] using hut
  have hPow : (u ^ 2)⁻¹ * u = u⁻¹ := by
    simpa using (inv_pow_sub₀ hne (show 1 ≤ 2 by decide)).symm
  simp only [(hasDerivAt_inv hne).deriv, hu, ht', principalPart, sub_zero]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hb (j : ℕ) : b (j + 1 + 1) = -c j := by
    simp [b]
  simp only [hb, show b 1 = -hInf 0 by simp [b], show b 0 = -deriv hInf 0 by simp [b]]
  have hsum :
      (∑ j ∈ Finset.range n, -c j * u⁻¹ ^ (j + 1 + 1 + 1)) =
        (∑ j ∈ Finset.range n, c j * u⁻¹ ^ (j + 1)) * (-(u ^ 2)⁻¹) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show j + 1 + 1 + 1 = (j + 1) + 2 by omega, pow_add, inv_pow u 2]
    ring
  rw [hsum]
  simp only [zero_add, pow_one, inv_pow u 2]
  have hcancel : u ^ 2 * (u ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hne)
  linear_combination -deriv hInf 0 * hPow - R u * hcancel

/-- The channel A coordinate as a function of the coordinate `u = z - 1`. -/
noncomputable def aChart (u : ℂ) : ℂ := -u / (1 + u)

private theorem hasDerivAt_aChart {u : ℂ} (hu : 1 + u ≠ 0) :
    HasDerivAt aChart (-((1 + u) ^ 2)⁻¹) u := by
  have hd := (hasDerivAt_id u).neg.fun_div ((hasDerivAt_id u).const_add 1) hu
  convert hd using 1
  · ext y
    simp [aChart]
  change -((1 + u) ^ 2)⁻¹ = (-1 * (1 + u) - (-u) * 1) / (1 + u) ^ 2
  rw [div_eq_mul_inv]
  ring

private theorem analyticAt_aChart : AnalyticAt ℂ aChart 0 := by
  have h : AnalyticAt ℂ (fun u : ℂ ↦ 1 + u) 0 := by fun_prop
  exact (analyticAt_id.neg.div h (by simp))

/-- The coefficient contributed by a pole of order `k + 2` at the corresponding
output poles. The exponent selected by `i` is `-(i + 1)`. -/
private noncomputable def higherPoleCoeff (k i : ℕ) : ℂ :=
  if i = 0 ∨ k + 2 ≤ i then 0
  else (-1 : ℂ) ^ (k + 1) * (k.choose (k + 1 - i) : ℂ)

private theorem aChart_higher_pole {u : ℂ} (hu : u ≠ 0) (hden : 1 + u ≠ 0)
    (k n : ℕ) (hn : k + 2 ≤ n) :
    (aChart u)⁻¹ ^ (k + 2) * deriv aChart u =
      principalPart 0 n (higherPoleCoeff k) u := by
  have hp : (aChart u)⁻¹ ^ (k + 2) * deriv aChart u =
      (-1 : ℂ) ^ (k + 1) * ((1 + u) ^ k * (u⁻¹ ^ (k + 2))) := by
    have ht : (aChart u)⁻¹ = ((-1 : ℂ) * (1 + u)) * u⁻¹ := by
      rw [aChart, inv_div, div_eq_mul_inv, inv_neg]
      ring
    rw [(hasDerivAt_aChart hden).deriv, ht, mul_pow, mul_pow,
      pow_add (-1 : ℂ) k 2, pow_add (1 + u) k 2, pow_succ (-1 : ℂ) k]
    have hinv := mul_inv_cancel₀ (pow_ne_zero 2 hden)
    norm_num only [show (-1 : ℂ) ^ 2 = 1 by norm_num, mul_one]
    linear_combination -((-1 : ℂ) ^ k * (1 + u) ^ k * u⁻¹ ^ (k + 2)) * hinv
  have hpadded : principalPart 0 n (higherPoleCoeff k) u =
      principalPart 0 (k + 2) (higherPoleCoeff k) u := by
    symm
    apply Finset.sum_subset (Finset.range_mono hn)
    intro i _ hi
    have hi' : k + 2 ≤ i := Nat.le_of_not_lt (fun h ↦ hi (Finset.mem_range.mpr h))
    simp [higherPoleCoeff, hi']
  rw [hp, hpadded, principalPart, Finset.sum_range_succ']
  simp only [sub_zero, higherPoleCoeff, true_or, ite_true, zero_mul, add_zero]
  rw [add_comm (1 : ℂ) u, add_pow, Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_range_reflect
    (fun i ↦ (-1 : ℂ) ^ (k + 1) * (u ^ i * 1 ^ (k - i) * (k.choose i : ℂ) *
      u⁻¹ ^ (k + 2))) (k + 1)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  have hle : k + 1 - 1 - i ≤ k + 2 := by omega
  have he : k + 2 - (k + 1 - 1 - i) = i + 1 + 1 := by omega
  have hc : k + 1 - 1 - i = k + 1 - (i + 1) := by omega
  have hn' : ¬ k + 2 ≤ i + 1 := by omega
  have hfactor := inv_pow_sub₀ hu hle
  rw [he, ← inv_pow] at hfactor
  simp only [hc, one_pow, mul_one, Nat.succ_ne_zero, hn', or_self, ite_false] at *
  linear_combination ((-1 : ℂ) ^ (k + 1) * (k.choose (k + 1 - (i + 1)) : ℂ)) * -hfactor

private theorem aChart_simple_pole {u : ℂ} (hu : u ≠ 0) (hden : 1 + u ≠ 0) :
    (aChart u)⁻¹ * deriv aChart u = u⁻¹ - (1 + u)⁻¹ := by
  rw [(hasDerivAt_aChart hden).deriv]
  simp only [aChart, inv_div]
  field_simp [hu, hden]
  ring

/-- The channel A Möbius pullback preserves the simple coefficient of a differential.
Every input pole of order at least two becomes a finite sum of poles of order
at least two. The pullback of the analytic remainder stays analytic. -/
theorem aChart_residue_invariant {F h : ℂ → ℂ} {n : ℕ} {c : ℕ → ℂ}
    (ha : AnalyticAt ℂ h 0)
    (he : F =ᶠ[𝓝[≠] 0] fun t ↦ principalPart 0 n c t + h t) :
    ∃ b : ℕ → ℂ, ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ((fun u ↦ F (aChart u) * deriv aChart u) =ᶠ[𝓝[≠] 0]
        fun u ↦ principalPart 0 n b u + R u) ∧
      simpleCoeff n b = simpleCoeff n c := by
  have hden : AnalyticAt ℂ (fun u : ℂ ↦ (1 + u)⁻¹) 0 := by
    have hbase : AnalyticAt ℂ (fun u : ℂ ↦ 1 + u) 0 := by fun_prop
    exact hbase.inv (by simp)
  have hchart0 : aChart 0 = 0 := by simp [aChart]
  have hJac : AnalyticAt ℂ (fun u : ℂ ↦ deriv aChart u) 0 := analyticAt_aChart.deriv
  have ha' : AnalyticAt ℂ h (aChart 0) := by simpa only [hchart0] using ha
  have hcomp : AnalyticAt ℂ (fun u ↦ h (aChart u)) 0 :=
    ha'.fun_comp analyticAt_aChart
  have hreg := hcomp.mul hJac
  have ht : Tendsto aChart (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    have hcont : Tendsto aChart (𝓝[≠] 0) (𝓝 (aChart 0)) :=
      analyticAt_aChart.continuousAt.continuousWithinAt
    refine ⟨by simpa only [hchart0] using hcont, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      eventually_ne_nhdsWithin (s := ({0}ᶜ : Set ℂ)) (show (0 : ℂ) ≠ -1 by norm_num)]
      with u hu0 hu1
    have hu : u ≠ 0 := hu0
    have hd : 1 + u ≠ 0 := by
      intro hh
      apply hu1
      linear_combination hh
    exact div_ne_zero (neg_ne_zero.mpr hu) hd
  have he' := ht.eventually he
  cases n with
  | zero =>
    refine ⟨c, fun u ↦ h (aChart u) * deriv aChart u, hreg, ?_, rfl⟩
    filter_upwards [he'] with u hu
    simpa [principalPart] using congrArg (fun v ↦ v * deriv aChart u) hu
  | succ n =>
    let b : ℕ → ℂ := fun i ↦
      (if i = 0 then c 0 else 0) + ∑ k ∈ Finset.range n, c (k + 1) * higherPoleCoeff k i
    let R : ℂ → ℂ := fun u ↦ h (aChart u) * deriv aChart u - c 0 * (1 + u)⁻¹
    refine ⟨b, R, hreg.sub (analyticAt_const.mul hden), ?_,
      by simp [simpleCoeff, b, higherPoleCoeff]⟩
    filter_upwards [he', self_mem_nhdsWithin,
      eventually_ne_nhdsWithin (s := ({0}ᶜ : Set ℂ)) (show (0 : ℂ) ≠ -1 by norm_num)]
      with u hu hu0 hu1
    have hu' : u ≠ 0 := hu0
    have hd : 1 + u ≠ 0 := by
      intro hh
      apply hu1
      linear_combination hh
    change F (aChart u) * deriv aChart u = _
    rw [hu]
    have hpp :
        principalPart 0 (n + 1) c (aChart u) * deriv aChart u =
          (∑ k ∈ Finset.range n, c (k + 1) *
            principalPart 0 (n + 1) (higherPoleCoeff k) u) +
              c 0 * (u⁻¹ - (1 + u)⁻¹) := by
      simp only [principalPart] at ⊢
      rw [Finset.sum_range_succ', add_mul, Finset.sum_mul]
      simp only [sub_zero, zero_add, pow_one]
      congr 1
      · refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk' : k + 2 ≤ n + 1 := by have := Finset.mem_range.mp hk; omega
        rw [mul_assoc, aChart_higher_pole hu' hd k (n + 1) hk']
        simp [principalPart]
      · rw [mul_assoc, aChart_simple_pole hu' hd]
    have hb : principalPart 0 (n + 1) b u =
        c 0 * u⁻¹ +
          ∑ k ∈ Finset.range n, c (k + 1) *
            principalPart 0 (n + 1) (higherPoleCoeff k) u := by
      simp only [principalPart, b, sub_zero, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.range (n + 1)) (t := Finset.range n)]
      simp only [mul_assoc, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range,
        Nat.zero_lt_succ, ite_true, zero_add, pow_one]
    rw [add_mul, hpp, hb]
    dsimp [R]
    ring

/-- The numerator of a Laurent expansion after clearing a pole with a positive
common bound has normalized Taylor coefficient equal to its simple coefficient. -/
private theorem numerator_simpleCoeff (n m : ℕ) (hm : m ≤ n + 1)
    (c : ℕ → ℂ) {h : ℂ → ℂ} (ha : AnalyticAt ℂ h 0) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧
      (f =ᶠ[𝓝[≠] 0] fun u ↦ u ^ (n + 1) * (principalPart 0 m c u + h u)) ∧
      iteratedDeriv n f 0 = (n.factorial : ℂ) * simpleCoeff m c := by
  let S : ℂ → ℂ := fun u ↦ ∑ j ∈ Finset.range m, c j * u ^ (n - j)
  let T : ℂ → ℂ := fun u ↦ u ^ (n + 1) * h u
  have haS : AnalyticAt ℂ S 0 := by
    apply Finset.analyticAt_fun_sum
    intro j _
    fun_prop
  have haT : AnalyticAt ℂ T 0 := (analyticAt_id.pow (n + 1)).mul ha
  refine ⟨fun u ↦ S u + T u, haS.add haT, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : u ≠ 0 := hu
    simp only [S, T, principalPart, sub_zero, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j + 1 ≤ n + 1 := (Finset.mem_range.mp hj).trans_le hm
    have hp := pow_sub₀ u hu' hj'
    rw [show n + 1 - (j + 1) = n - j by omega, ← inv_pow] at hp
    rw [hp]
    ring
  · have hvanish : iteratedDeriv n T 0 = 0 := by
      have horder := (natCast_le_analyticOrderAt haT (n := n + 1)).mpr
        ⟨h, ha, by simp [T, smul_eq_mul]⟩
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero haT).mp horder n
        (Nat.lt_succ_self n)
    rw [iteratedDeriv_fun_add haS.contDiffAt haT.contDiffAt, hvanish, add_zero]
    dsimp only [S]
    rw [iteratedDeriv_fun_sum (fun j _ ↦ by fun_prop)]
    cases m with
    | zero => simp [simpleCoeff]
    | succ m =>
      rw [Finset.sum_range_succ']
      have hz (j : ℕ) (hj : j ∈ Finset.range m) :
          iteratedDeriv n (fun u : ℂ ↦ c (j + 1) * u ^ (n - (j + 1))) 0 = 0 := by
        have hj' := Finset.mem_range.mp hj
        rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
        simp [show n ≠ n - (j + 1) by omega]
      rw [Finset.sum_eq_zero hz]
      simp [simpleCoeff, Nat.descFactorial_self, mul_comm]

/-- The simple coefficient is independent of the Laurent presentation and of its
chosen finite pole bound. -/
theorem simpleCoeff_unique {F h h' : ℂ → ℂ} {m m' : ℕ} {c c' : ℕ → ℂ}
    (ha : AnalyticAt ℂ h 0) (ha' : AnalyticAt ℂ h' 0)
    (he : F =ᶠ[𝓝[≠] 0] fun u ↦ principalPart 0 m c u + h u)
    (he' : F =ᶠ[𝓝[≠] 0] fun u ↦ principalPart 0 m' c' u + h' u) :
    simpleCoeff m c = simpleCoeff m' c' := by
  let n := max m m'
  obtain ⟨f, hf, hEq, hd⟩ :=
    numerator_simpleCoeff n m ((le_max_left m m').trans (Nat.le_succ n)) c ha
  obtain ⟨f', hf', hEq', hd'⟩ :=
    numerator_simpleCoeff n m' ((le_max_right m m').trans (Nat.le_succ n)) c' ha'
  have hsame : f =ᶠ[𝓝[≠] 0] f' := by
    filter_upwards [hEq, hEq', he, he'] with u hu hu' heu heu'
    rw [hu, hu', ← heu, ← heu']
  have hfull := (hf.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hf'.continuousAt).mp hsame
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    (hd.symm.trans ((hfull.iteratedDeriv_eq n).trans hd'))

/-- The residue sum using any finite Laurent expansion of the pulled-back
differential at infinity. -/
theorem residue_sum_of_pullback_expansion
    {G h0 h1 hInf rInf : ℂ → ℂ} {n0 n1 nInf mInf : ℕ}
    {c0 c1 cInf bInf : ℕ → ℂ}
    (hG : ∀ z, z ≠ 0 → z ≠ 1 → DifferentiableAt ℂ G z)
    (ha0 : AnalyticAt ℂ h0 0) (ha1 : AnalyticAt ℂ h1 1)
    (haInf : AnalyticAt ℂ hInf 0) (hrInf : AnalyticAt ℂ rInf 0)
    (hex0 : G =ᶠ[𝓝[≠] 0] fun z ↦ principalPart 0 n0 c0 z + h0 z)
    (hex1 : G =ᶠ[𝓝[≠] 1] fun z ↦ principalPart 1 n1 c1 z + h1 z)
    (hexInf : (fun u : ℂ ↦ G u⁻¹) =ᶠ[𝓝[≠] 0]
      fun u ↦ principalPart 0 nInf cInf u + hInf u)
    (hr : (fun u : ℂ ↦ G u⁻¹ * deriv (fun v : ℂ ↦ v⁻¹) u) =ᶠ[𝓝[≠] 0]
      fun u ↦ principalPart 0 mInf bInf u + rInf u) :
    simpleCoeff n0 c0 + simpleCoeff n1 c1 + simpleCoeff mInf bInf = 0 := by
  obtain ⟨_, _, hh, he, hc⟩ := inverse_differential_principalPart haInf hexInf
  rw [simpleCoeff_unique hrInf hh hr he, hc]
  exact residue_sum hG ha0 ha1 haInf hex0 hex1 hexInf

/-- The three local expansions may be supplied directly for the differential.
At infinity the scalar pole bound follows by multiplying the pullback by
`-u²` on the punctured neighborhood. -/
theorem residue_sum_of_differential_expansions
    {G h0 h1 rInf : ℂ → ℂ} {n0 n1 mInf : ℕ} {c0 c1 bInf : ℕ → ℂ}
    (hG : ∀ z, z ≠ 0 → z ≠ 1 → DifferentiableAt ℂ G z)
    (ha0 : AnalyticAt ℂ h0 0) (ha1 : AnalyticAt ℂ h1 1) (hrInf : AnalyticAt ℂ rInf 0)
    (hex0 : G =ᶠ[𝓝[≠] 0] fun z ↦ principalPart 0 n0 c0 z + h0 z)
    (hex1 : G =ᶠ[𝓝[≠] 1] fun z ↦ principalPart 1 n1 c1 z + h1 z)
    (hr : (fun u : ℂ ↦ G u⁻¹ * deriv (fun v : ℂ ↦ v⁻¹) u) =ᶠ[𝓝[≠] 0]
      fun u ↦ principalPart 0 mInf bInf u + rInf u) :
    simpleCoeff n0 c0 + simpleCoeff n1 c1 + simpleCoeff mInf bInf = 0 := by
  obtain ⟨f, hf, he, _⟩ := numerator_simpleCoeff mInf mInf (Nat.le_succ _) bInf hrInf
  let A : ℂ → ℂ := fun u ↦ -(u ^ 2 * f u)
  have ha : AnalyticAt ℂ A 0 := ((analyticAt_id.pow 2).mul hf).neg
  have hA : (fun u : ℂ ↦ G u⁻¹) =ᶠ[𝓝[≠] 0] fun u ↦ (u ^ (mInf + 1))⁻¹ * A u := by
    filter_upwards [he, hr, self_mem_nhdsWithin] with u hu hru hu0
    have hne : u ≠ 0 := hu0
    change G u⁻¹ = _
    rw [show A u = -(u ^ 2 * f u) by rfl, hu, ← hru, (hasDerivAt_inv hne).deriv]
    have hpow (k : ℕ) : (u ^ k)⁻¹ * u ^ k = 1 := inv_mul_cancel₀ (pow_ne_zero _ hne)
    calc
      _ = ((u ^ (mInf + 1))⁻¹ * u ^ (mInf + 1)) *
          ((u ^ 2)⁻¹ * u ^ 2) * G u⁻¹ := by rw [hpow, hpow, one_mul, one_mul]
      _ = _ := by ring
  obtain ⟨_, _, hh, hExp, _⟩ := principalPart_of_analytic_numerator (mInf + 1) ha hA
  exact residue_sum_of_pullback_expansion hG ha0 ha1 hh hrInf hex0 hex1 hExp hr

end D5.S3.AnalyticClosure.ThreePunctureResidue
