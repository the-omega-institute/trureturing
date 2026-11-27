/- GID: D5/S3/Zeros/Jensen/ActualJensenCanonicalProduct
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/ActualJensenCanonicalProduct
   mirror-E: none(waiver:unbounded-analytic-construction)
   anchors: []
   utility: none
   digest: The actual xi-square product constructs every fixed-shift Jensen polynomial by real-root-preserving differential operators. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Topology.MetricSpace.Algebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct

open Polynomial Complex Filter Set Metric
open scoped BigOperators Topology
open D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
open D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.ActualZeroGeometry
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open private repeatedIndex squareReciprocal squareCanonicalProduct
  actual_xi_square_complete_product square_product_locally_uniform
  from D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open private source_coefficients source_weighted_summable source_polynomial_at_zero
  from D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
open private coefficient_derivative_series
  from D5.S3.Zeros.Jensen.JensenAnalyticCoefficientRemainder

private theorem root_logarithmic_sum_im (z : ℂ) (s : Multiset ℂ)
    (hs : ∀ r ∈ s, r.im = 0) :
    ((s.map fun r => 1 / (z - r)).sum).im =
      -z.im * (s.map fun r => 1 / Complex.normSq (z - r)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr := hs r (Multiset.mem_cons_self _ _)
    have hrest : ∀ t ∈ s, t.im = 0 := fun t ht => hs t (Multiset.mem_cons_of_mem ht)
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im, ih hrest]
    rw [one_div, Complex.inv_im, Complex.sub_im, hr, sub_zero]
    ring

/-- A real first-order constant-coefficient differential operator preserves
polynomials having only real roots, including all multiplicities. -/
theorem firstOrder_preserves_real (p : ℂ[X]) (hp : AllRootsReal p) (a : ℝ) :
    ∀ z : ℂ, (p - C (a : ℂ) * p.derivative).eval z = 0 → z.im = 0 := by
  classical
  intro z hz
  by_contra hzi
  have hpz : p.eval z ≠ 0 := fun h => hzi (hp _ h)
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hpz
  simp only [eval_sub, eval_mul, eval_C] at hz
  by_cases ha : a = 0
  · simp [ha] at hz
    exact hpz hz
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hpeq : p.eval z = (a : ℂ) * p.derivative.eval z := sub_eq_zero.mp hz
  have hder : p.derivative.eval z = (a : ℂ)⁻¹ * p.eval z := by
    calc
      _ = (a : ℂ)⁻¹ * ((a : ℂ) * p.derivative.eval z) := by
        rw [← mul_assoc, inv_mul_cancel₀ haC, one_mul]
      _ = _ := by rw [← hpeq]
  have hquot : p.derivative.eval z / p.eval z = (a : ℂ)⁻¹ := by
    rw [hder, mul_div_assoc, div_self hpz, mul_one]
  have hsplit := IsAlgClosed.splits p
  have hsum := hsplit.eval_derivative_div_eval_of_ne_zero hpz
  rw [hquot] at hsum
  have hroots : ∀ r ∈ p.roots, r.im = 0 := by
    intro r hr
    exact hp r ((mem_roots hp0).mp hr)
  have hnorm (r : ℂ) (hr : r ∈ p.roots) :
      0 < Complex.normSq (z - r) := by
    apply Complex.normSq_pos.mpr
    intro he
    have heq := sub_eq_zero.mp he
    exact hzi (by simpa [heq] using hroots r hr)
  have himsum := congrArg Complex.im hsum
  rw [Complex.inv_im, Complex.ofReal_im, neg_zero, zero_div,
    root_logarithmic_sum_im z p.roots hroots] at himsum
  let vals := p.roots.map fun r => 1 / Complex.normSq (z - r)
  have hvals : vals.sum = 0 := by
    exact (mul_eq_zero.mp (show -z.im * vals.sum = 0 from himsum.symm)).resolve_left
      (neg_ne_zero.mpr hzi)
  have hnonempty : p.roots ≠ 0 := by
    intro hzero
    simp [hzero, haC] at hsum
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hnonempty
  have hpositive : 0 < 1 / Complex.normSq (z - r) := div_pos zero_lt_one (hnorm r hr)
  have hnonnegative : ∀ x ∈ vals, 0 ≤ x := by
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨t, ht, rfl⟩
    exact (div_pos zero_lt_one (hnorm t ht)).le
  have hmem : 1 / Complex.normSq (z - r) ∈ vals := Multiset.mem_map.mpr ⟨r, hr, rfl⟩
  have hbound := Multiset.single_le_sum hnonnegative _ hmem
  rw [hvals] at hbound
  exact (not_lt_of_ge hbound) hpositive

/-- Polynomial functional calculus of the formal derivative. -/
private def appell (d : ℕ) (p : ℂ[X]) : ℂ[X] :=
  (aeval (Polynomial.derivative : Module.End ℂ ℂ[X]) p) (X ^ d)

private theorem appell_linear_factor (d : ℕ) (p : ℂ[X]) (a : ℂ) :
    appell d ((1 - C a * X) * p) =
      appell d p - C a * (appell d p).derivative := by
  simp only [appell, map_mul, Module.End.mul_apply, map_sub, map_one,
    aeval_C, aeval_X, LinearMap.sub_apply, Module.End.one_apply,
    Module.algebraMap_end_apply, smul_eq_C_mul]

/-- The exact finite product acts on a single monomial through the preceding
real first-order operators. -/
private theorem finite_appell_real {ι : Type*} (a : ι → ℂ)
    (ha : ∀ i, (a i).im = 0) (d : ℕ) (s : Finset ι) :
    AllRootsReal (appell d (∏ i ∈ s, (1 - C (a i) * X))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z hz
    by_contra hzi
    have hz0 : z ≠ 0 := by intro h; simp [h] at hzi
    exact pow_ne_zero d hz0 (by simpa [appell] using hz)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, appell_linear_factor]
    have hcast : a i = ((a i).re : ℂ) := by apply Complex.ext <;> simp [ha]
    rw [hcast]
    exact firstOrder_preserves_real _ ih _

/-- The finite-degree differential calculus is exactly the falling-factorial
coefficient truncation, with no asymptotic factor in the degree. -/
private theorem appell_eq_sum (d : ℕ) (p : ℂ[X]) :
    appell d p = ∑ k ∈ Finset.range (d + 1),
      C (p.coeff k * (d.descFactorial k : ℂ)) * X ^ (d - k) := by
  classical
  let m := max p.natDegree d + 1
  have hm : p.natDegree < m := by dsimp [m]; omega
  have hp := p.as_sum_range_C_mul_X_pow' hm
  have heq : appell d p = ∑ k ∈ Finset.range m,
      C (p.coeff k * (d.descFactorial k : ℂ)) * X ^ (d - k) := by
    conv_lhs => rw [appell, hp]
    simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X,
      LinearMap.sum_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.End.pow_apply, iterate_derivative_X_pow_eq_C_mul, smul_eq_C_mul]
    simp only [← mul_assoc, ← C_mul]
  rw [heq]
  symm
  apply Finset.sum_subset (Finset.range_mono (by dsimp [m]; omega))
  intro k _ hk
  have hdk : d < k := by
    have h := Finset.mem_range.not.mp hk
    omega
  simp [Nat.descFactorial_of_lt hdk]

private def finiteJensen (d : ℕ) (p : ℂ[X]) : ℂ[X] :=
  coefficientPolynomial p.coeff d

private theorem finiteJensen_reciprocal (d : ℕ) (hd : 1 ≤ d) (p : ℂ[X]) (z : ℂ)
    (hz : z ≠ 0) :
    (finiteJensen d p).eval z = (z / (d : ℂ)) ^ d * (appell d p).eval ((d : ℂ) / z) := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  simp only [finiteJensen, coefficientPolynomial, appell_eq_sum, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := by
    have h := Finset.mem_range.mp hk
    omega
  have hpow : (z / (d : ℂ)) ^ d * ((d : ℂ) / z) ^ (d-k) =
      (z / (d : ℂ)) ^ k := by
    calc
      _ = (z / (d : ℂ)) ^ k *
            ((z / (d : ℂ)) ^ (d-k) * ((d : ℂ) / z) ^ (d-k)) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hkd]
      _ = _ := by
        rw [← mul_pow, show z / (d : ℂ) * ((d : ℂ) / z) = 1 by field_simp [hz, hd0],
          one_pow, mul_one]
  calc
    _ = (p.coeff k * (d.descFactorial k : ℂ)) * (z / (d : ℂ)) ^ k := by rw [div_pow]; ring
    _ = _ := by rw [← hpow]; ring

private theorem finiteJensen_real_of_appell (d : ℕ) (hd : 1 ≤ d) (p : ℂ[X])
    (hp : AllRootsReal (appell d p)) : AllRootsReal (finiteJensen d p) := by
  intro z hz
  by_contra hzi
  have hz0 : z ≠ 0 := by intro h; simp [h] at hzi
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [finiteJensen_reciprocal d hd p z hz0] at hz
  have hroot := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (div_ne_zero hz0 hd0))
  have him := hp _ hroot
  rw [Complex.div_im, Complex.natCast_im, Complex.natCast_re, zero_mul, zero_div, zero_sub] at him
  have hnz : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  exact (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hnz hzi)
    (Complex.normSq_pos.mpr hz0).ne')) him

private theorem iteratedDeriv_eval (p : ℂ[X]) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun t => p.eval t) z = (Polynomial.derivative^[n] p).eval z := by
  have hcomm : Function.Semiconj (fun q : ℂ[X] => fun t => q.eval t)
      Polynomial.derivative deriv := by
    intro q
    funext t
    exact (q.deriv).symm
  rw [iteratedDeriv_eq_iterate, ← hcomm.iterate_right n p]

private theorem source_jet (k : ℕ) :
    iteratedDeriv k sourceF 0 = sourceA k * (k.factorial : ℂ) := by
  have hs := coefficient_derivative_series sourceA sourceF source_coefficients.2.2.2
    source_weighted_summable k (0 : ℂ)
  let f : ℕ → ℂ := fun j => sourceA j * (j.descFactorial k : ℂ) * (0 : ℂ) ^ (j-k)
  have hs0 : HasSum f (∑ j ∈ ({k} : Finset ℕ), f j) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hne : j ≠ k := by simpa using hj
    by_cases hjk : j < k
    · simp [f, Nat.descFactorial_of_lt hjk]
    · have hpos : j - k ≠ 0 := by omega
      simp [f, zero_pow hpos]
  simpa only [f, Finset.sum_singleton, Nat.descFactorial_self, Nat.sub_self, pow_zero,
    mul_one] using hs.unique hs0

private theorem source_coeff_limit {ι : Type*} {l : Filter ι} (p : ι → ℂ[X])
    (h : TendstoLocallyUniformlyOn (fun i z => (p i).eval z) sourceF l univ)
    (k : ℕ) : Tendsto (fun i => (p i).coeff k) l (𝓝 (sourceA k)) := by
  have hd (n : ℕ) : TendstoLocallyUniformlyOn
      (fun i => iteratedDeriv n (fun z => (p i).eval z))
      (iteratedDeriv n sourceF) l univ := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have hpoly : ∀ᶠ i in l, DifferentiableOn ℂ
          (iteratedDeriv n (fun z => (p i).eval z)) univ := by
        filter_upwards with i
        have heq : iteratedDeriv n (fun z => (p i).eval z) =
            fun z => (Polynomial.derivative^[n] (p i)).eval z :=
          funext (iteratedDeriv_eval (p i) n)
        rw [heq]
        exact (Polynomial.derivative^[n] (p i)).differentiable.differentiableOn
      simpa only [Function.comp_def, iteratedDeriv_succ] using
        ih.deriv hpoly isOpen_univ
  have hj := (hd k).tendsto_at (mem_univ (0 : ℂ))
  have hj' := hj.div_const (k.factorial : ℂ)
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpolyjet (i : ι) :
      iteratedDeriv k (fun z => (p i).eval z) 0 / (k.factorial : ℂ) = (p i).coeff k := by
    rw [iteratedDeriv_eval, ← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul]
    field_simp [hfac]
  simpa only [hpolyjet, source_jet, mul_div_cancel_right₀ _ hfac] using hj'

private theorem sourceJensen_coeff_limit {ι : Type*} {l : Filter ι} (p : ι → ℂ[X])
    (h : ∀ k, Tendsto (fun i => (p i).coeff k) l (𝓝 (sourceA k))) (d : ℕ) :
    TendstoLocallyUniformlyOn (fun i z => (finiteJensen d (p i)).eval z)
      (fun z => (sourcePolynomial d).eval z) l univ := by
  classical
  have hterm (k : ℕ) : TendstoLocallyUniformlyOn
      (fun i (z : ℂ) => ((d.descFactorial k : ℂ) / (d : ℂ)^k * (p i).coeff k) * z^k)
      (fun z : ℂ => ((d.descFactorial k : ℂ) / (d : ℂ)^k * sourceA k) * z^k) l univ := by
    let c : ℂ := (d.descFactorial k : ℂ) / (d : ℂ)^k
    have hconst := ((h k).const_mul c).tendstoUniformlyOn_const (univ : Set ℂ)
    have hpow : TendstoUniformlyOn (fun (_ : ι) (z : ℂ) => z^k)
        (fun z : ℂ => z^k) l univ := by
      rw [tendstoUniformlyOn_iff]
      intro e he
      exact Eventually.of_forall (by simp [he])
    exact hconst.tendstoLocallyUniformlyOn.mul₀ hpow.tendstoLocallyUniformlyOn
      continuous_const.continuousOn (by fun_prop)
  have hsum (s : Finset ℕ) : TendstoLocallyUniformlyOn
      (fun i z => ∑ k ∈ s, ((d.descFactorial k : ℂ) / (d : ℂ)^k * (p i).coeff k) * z^k)
      (fun z => ∑ k ∈ s, ((d.descFactorial k : ℂ) / (d : ℂ)^k * sourceA k) * z^k) l univ := by
    induction s using Finset.induction_on with
    | empty =>
      apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
      rw [tendstoUniformlyOn_iff]
      intro e he
      exact Eventually.of_forall (by simp [he])
    | insert k s hk ih =>
      have hh := (hterm k).add ih
      convert hh using 1
      · funext i z
        simp [Finset.sum_insert hk]
      · funext z
        simp [Finset.sum_insert hk]
  simpa only [finiteJensen, source_coefficients.2.2.1 d, coefficientPolynomial,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] using hsum (Finset.range (d+1))

/-- The all-order real-rootedness follows from the actual canonical zero geometry,
using finite differential products at each arbitrary degree. -/
theorem actual_jensen_tower_of_zero_line :
    let coordinate : ℂ → ℝ := Complex.re
    (∀ s : ℂ, Zeta23.IsNontrivialZero s → coordinate s = (1 : ℝ) / 2) →
    ∀ d : ℕ, 1 ≤ d → ∀ z : ℂ, (sourceJensenPolynomial d).eval z = 0 →
      coordinate ⟨z.im, z.re⟩ = 0 := by
  intro coordinate hline
  change ∀ d : ℕ, 1 ≤ d → AllRootsReal (sourceJensenPolynomial d)
  classical
  let Z := zetaZeroData
  let a : repeatedIndex Z → ℂ := squareReciprocal Z
  let p : Finset (repeatedIndex Z) → ℂ[X] := fun s => ∏ i ∈ s, (1 - C (a i) * X)
  have hreal (i : repeatedIndex Z) : (a i).im = 0 := by
    have hgamma : (Z.gamma i.1).im = 0 := by
      have h := congrArg Complex.re (Z.zero_eq_critical_add_I_mul_gamma i.1)
      simp only [D5.S3.Weil.Convention.criticalAbscissa, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, Complex.ofReal_re] at h
      linarith [hline (Z.zero i.1) (zetaZeroData_isNontrivial i.1)]
    have hcast : Z.gamma i.1 = ((Z.gamma i.1).re : ℂ) := by
      apply Complex.ext <;> simp [hgamma]
    dsimp [a, squareReciprocal]
    split
    · rw [hcast]
      simp [← Complex.ofReal_pow, ← Complex.ofReal_inv]
    · simp
  have hproduct : TendstoLocallyUniformlyOn (fun s z => (p s).eval z) sourceF atTop univ := by
    rw [sourceF_eq_xiSquareSource, actual_xi_square_complete_product Z]
    simpa only [p, a, HasProdLocallyUniformlyOn, eval_prod, eval_sub, eval_one, eval_mul,
      eval_C, eval_X, mul_comm]
      using (square_product_locally_uniform Z)
  intro d hd
  have hconv := sourceJensen_coeff_limit p (fun k => source_coeff_limit p hproduct k) d
  have hroot : ∀ᶠ s : Finset (repeatedIndex Z) in atTop, AllRootsReal (finiteJensen d (p s)) :=
    Eventually.of_forall (fun s => finiteJensen_real_of_appell d hd _ (finite_appell_real a hreal d s))
  have hF : AnalyticOnNhd ℂ (fun z => (sourcePolynomial d).eval z) univ :=
    (sourcePolynomial d).differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : (sourcePolynomial d).eval 0 ≠ 0 := by
    rw [source_polynomial_at_zero]
    exact one_ne_zero
  apply (sourceJensen_real_iff_reflected d).mpr
  exact allZerosReal_of_locallyUniform (fun s => finiteJensen d (p s))
    (fun z => (sourcePolynomial d).eval z) hF h0 hconv hroot

/-- Every fixed-shift actual Jensen polynomial is real-rooted exactly under RH. -/
theorem rh_iff_actual_jensen_tower :
    RiemannHypothesis ↔ ∀ d : ℕ, 1 ≤ d →
      ∀ z : ℂ, (sourceJensenPolynomial d).eval z = 0 → z.im = 0 :=
  ⟨fun hRH => actual_jensen_tower_of_zero_line (rh_iff_nontrivial_zeros_on_line.mp hRH),
    rh_of_actual_jensen_tower⟩

end D5.S3.Zeros.Jensen.ActualJensenCanonicalProduct
