/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetGerm
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetGerm
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreNormalizedJet]
   utility: none
   digest: Formal quotient coefficients give physical Taylor expansions of normalized marginal entries along the polynomial chart paths. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreNormalizedJet
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
# Physical readouts and the formal quotient along polynomial chart paths
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreNormalizedJet

open PeriodicMPSUniformHardCoreJetElimination
open PeriodicMPSUniformHardCoreFirstJet (entry component cores)
open PeriodicMPSUniformHardCoreHigherJet (pathChart pathCoordinate pathRaw_eval)
open PeriodicMPSUniformHardCoreTransferRecurrence (hardCoreChart)
open PeriodicMPSUniformHardCoreQuarticSign (G_pos quartic)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open Polynomial Filter Asymptotics
open scoped Topology

noncomputable section

/-- The actual chart coordinates along the polynomial path. -/
def coordinates (n : ℕ) (x : Path) (ε : ℝ) : Fin 4 → ℂ :=
  fun i => (pathCoordinate (parameters n x) i).eval (ε : ℂ)

theorem numerator_eval (s : ℕ) (x : Path) (row : Fin 8) (ε : ℝ) :
    (numerator (s+4) x row).eval (ε : ℂ) =
      rawTwo (cores (coordinates (s+4) x ε)) s (entry row).1 (entry row).2 := by
  rw [numerator, pathRaw_eval]
  congr 1
  funext i
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [pathChart, hardCoreChart, cores, coordinates, RingHom.mapMatrix_apply]

theorem mass_eval (s : ℕ) (x : Path) (ε : ℝ) :
    (mass (s+4) x).eval (ε : ℂ) =
      (rawTwo (cores (coordinates (s+4) x ε)) s).trace := by
  simp [mass, numerator_eval, Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
    Fin.sum_univ_two, entry]
  ring

private def project (imag : Bool) : ℂ →+ ℝ :=
  if imag then Complex.imCLM.toLinearMap.toAddMonoidHom else
    Complex.reCLM.toLinearMap.toAddMonoidHom

private theorem project_apply (imag : Bool) (z : ℂ) :
    project imag z = if imag then z.im else z.re := by
  cases imag <;> rfl

private theorem project_mul (imag : Bool) (z : ℂ) (r : ℝ) :
    project imag (z * (r : ℂ)) = project imag z * r := by
  cases imag <;> simp [project_apply, Complex.mul_re, Complex.mul_im]

/-- Coefficientwise real or imaginary projection of a complex polynomial. -/
private def realPolynomial (imag : Bool) (p : Polynomial ℂ) : Polynomial ℝ :=
  p.sum fun k a => monomial k (project imag a)

@[simp] private theorem coeff_realPolynomial (imag : Bool) (p : Polynomial ℂ) (k : ℕ) :
    (realPolynomial imag p).coeff k = project imag (p.coeff k) := by
  classical
  unfold realPolynomial Polynomial.sum
  rw [finsetSum_coeff]
  by_cases hk : k ∈ p.support
  · rw [Finset.sum_eq_single_of_mem k hk]
    · simp
    · intro b _ hb
      simp [coeff_monomial, hb]
  · rw [notMem_support_iff.mp hk, map_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hn : b ≠ k := fun h => hk (h ▸ hb)
    simp [coeff_monomial, hn]

private theorem eval_realPolynomial (imag : Bool) (p : Polynomial ℂ) (ε : ℝ) :
    (realPolynomial imag p).eval ε = project imag (p.eval (ε : ℂ)) := by
  rw [realPolynomial, Polynomial.sum, eval_finsetSum, eval_eq_sum (p := p)]
  simp only [eval_monomial, Polynomial.sum, map_sum, ← Complex.ofReal_pow, project_mul]

private def realMass (n : ℕ) (x : Path) : Polynomial ℝ :=
  realPolynomial false (mass n x)

private def realEntry (imag : Bool) (n : ℕ) (x : Path) (row : Fin 8) : Polynomial ℝ :=
  realPolynomial imag (numerator n x row)

private theorem coeff_realMass (n : ℕ) (x : Path) (k : ℕ) :
    (realMass n x).coeff k = massCoeff n x k := by
  simp [realMass, project_apply, massCoeff]

private theorem coeff_realEntry (imag : Bool) (n : ℕ) (x : Path) (row : Fin 8) (k : ℕ) :
    (realEntry imag n x row).coeff k = rawCoeff imag n x row k := by
  simp [realEntry, project_apply, rawCoeff]

private theorem component_eq_quotient (imag : Bool) (s : ℕ) (x : Path) (row : Fin 8) (ε : ℝ) :
    component imag s row (coordinates (s+4) x ε) =
      (realEntry imag (s+4) x row).eval ε / (realMass (s+4) x).eval ε := by
  rw [realEntry, realMass, eval_realPolynomial, eval_realPolynomial,
    numerator_eval, mass_eval, project_apply, project_apply]
  cases imag
  · change ((((rawTwo (cores (coordinates (s+4) x ε)) s).trace.re)⁻¹ •
      rawTwo (cores (coordinates (s+4) x ε)) s) (entry row).1 (entry row).2).re = _
    simp only [Matrix.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Bool.false_eq_true, ite_false, div_eq_mul_inv]
    exact mul_comm _ _
  · change ((((rawTwo (cores (coordinates (s+4) x ε)) s).trace.re)⁻¹ •
      rawTwo (cores (coordinates (s+4) x ε)) s) (entry row).1 (entry row).2).im = _
    simp only [Matrix.smul_apply, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Bool.false_eq_true, ite_false, ite_true,
      div_eq_mul_inv]
    exact mul_comm _ _

private theorem massCoeff_ne_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    massCoeff n x 0 ≠ 0 := by
  rw [mass_zero n hn]
  exact mul_ne_zero (G_pos hn).ne' (ratio_add_two_ne_zero n hn)

/-- The recurrence defining normalized coefficients is exact power-series division. -/
theorem normalized_series_mul (imag : Bool) (n : ℕ) (hn : 7 ≤ n) (x : Path) (row : Fin 8) :
    PowerSeries.mk (normalizedCoeff imag n x row) *
      ((realMass n x : Polynomial ℝ) : PowerSeries ℝ) =
      ((realEntry imag n x row : Polynomial ℝ) : PowerSeries ℝ) := by
  ext k
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Nat.sub_self]
  simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe, coeff_realMass, coeff_realEntry]
  have h := normalizedCoeff.eq_1 imag n x row k
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [mul_comm (_ : ℝ) (massCoeff n x _)]
  rw [h]
  field_simp [massCoeff_ne_zero n hn x]
  ring

private theorem mass_eventually_ne_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), (realMass n x).eval ε ≠ 0 := by
  refine ((realMass n x).continuous.continuousAt.eventually_ne ?_)
  rw [← coeff_zero_eq_eval_zero, coeff_realMass]
  exact massCoeff_ne_zero n hn x

/-- Eventual equality along the actual polynomial chart paths implies
equality of all the formal normalized coefficients of the chosen row. -/
theorem coefficients_of_equal_polynomial_germs (imag : Bool) (s : ℕ) (hs : 3 ≤ s)
    (x : Path) (row : Fin 8)
    (h : (fun ε => component imag s row (coordinates (s+4) x ε)) =ᶠ[𝓝 0]
      (fun ε => component imag s row (coordinates (s+4) original ε))) :
    normalizedCoeff imag (s+4) x row = normalizedCoeff imag (s+4) original row := by
  let n := s+4
  have hn : 7 ≤ n := by dsimp [n]; omega
  have he : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (realEntry imag n x row * realMass n original).eval ε =
        (realEntry imag n original row * realMass n x).eval ε := by
    filter_upwards [h, mass_eventually_ne_zero n hn x, mass_eventually_ne_zero n hn original]
      with ε he hx hy
    rw [component_eq_quotient, component_eq_quotient] at he
    simpa only [eval_mul] using (div_eq_div_iff hx hy).mp he
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp he
  have hinf : Set.Infinite {ε | (realEntry imag n x row * realMass n original).eval ε =
      (realEntry imag n original row * realMass n x).eval ε} := by
    apply (Set.Ioo_infinite (show -δ < δ by linarith)).mono
    intro ε hε
    apply hsub
    simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using hε
  have heq := Polynomial.eq_of_infinite_eval_eq _ _ hinf
  have hp := congrArg (fun p : Polynomial ℝ => (p : PowerSeries ℝ)) heq
  push_cast at hp
  rw [← normalized_series_mul imag n hn x row, ← normalized_series_mul imag n hn original row] at hp
  have hx : ((realMass n x : Polynomial ℝ) : PowerSeries ℝ) ≠ 0 := by
    intro hx
    have hc := congrArg (PowerSeries.coeff 0) hx
    have hc' : massCoeff n x 0 = 0 := by simpa [coeff_realMass] using hc
    exact massCoeff_ne_zero n hn x hc'
  have hy : ((realMass n original : Polynomial ℝ) : PowerSeries ℝ) ≠ 0 := by
    intro hy
    have hc := congrArg (PowerSeries.coeff 0) hy
    have hc' : massCoeff n original 0 = 0 := by simpa [coeff_realMass] using hc
    exact massCoeff_ne_zero n hn original hc'
  rw [mul_assoc, mul_assoc, mul_comm (_ : PowerSeries ℝ) (↑(realMass n x))] at hp
  have hp' := mul_right_cancel₀ (mul_ne_zero hx hy) hp
  funext k
  simpa only [PowerSeries.coeff_mk] using congrArg (PowerSeries.coeff k) hp'

/-- The regular physical readouts together with the forbidden diagonal
exclude eventual equality at the opposite slope. -/
theorem no_equal_polynomial_readout_germs (s : ℕ) (hs : 3 ≤ s) (x : Path)
    (ht : x.t = oppositeSlope (s+4))
    (hR : (fun ε => PeriodicMPSUniformHardCoreFirstJet.regularReadout s
        (coordinates (s+4) x ε)) =ᶠ[𝓝 0]
      (fun ε => PeriodicMPSUniformHardCoreFirstJet.regularReadout s
        (coordinates (s+4) original ε)))
    (hj : (fun ε => component false s 6 (coordinates (s+4) x ε)) =ᶠ[𝓝 0]
      (fun ε => component false s 6 (coordinates (s+4) original ε))) : False := by
  have hn : 7 ≤ s+4 := by omega
  have hreal (i : Fin 4) := hR.mono fun _ he => congrFun (congrArg Prod.fst he) i
  have himag (i : Fin 3) := hR.mono fun _ he => congrFun (congrArg Prod.snd he) i
  have hp := coefficients_of_equal_polynomial_germs false s hs x 1 (hreal 0)
  have hq := coefficients_of_equal_polynomial_germs false s hs x 2 (hreal 1)
  have hw := coefficients_of_equal_polynomial_germs false s hs x 4 (hreal 2)
  have hv := coefficients_of_equal_polynomial_germs false s hs x 5 (hreal 3)
  have hz := coefficients_of_equal_polynomial_germs true s hs x 3 (himag 0)
  have hw' := coefficients_of_equal_polynomial_germs true s hs x 4 (himag 1)
  have hv' := coefficients_of_equal_polynomial_germs true s hs x 5 (himag 2)
  have hr (k : ℕ) : regularCoeff (s+4) x k = regularCoeff (s+4) original k := by
    unfold regularCoeff
    rw [hp, hq, hw, hv, hz, hw', hv']
  have hsep := (opposite_forbidden_first_difference (s+4) hn x ht (fun k _ => hr k)).2.2.2
  exact hsep (congrFun (coefficients_of_equal_polynomial_germs false s hs x 6 hj) 4)

def truncatedReadout (d : ℕ) (imag : Bool) (n : ℕ) (x : Path)
    (row : Fin 8) : Polynomial ℝ :=
  PowerSeries.trunc d (PowerSeries.mk (normalizedCoeff imag n x row))

set_option maxHeartbeats 1000000 in
/-- The normalized readout minus its order-(d-1) jet is a multiple of
ε^d with a coefficient continuous at zero. -/
theorem polynomial_readout_remainder (d : ℕ) (imag : Bool) (s : ℕ) (hs : 3 ≤ s)
    (x : Path) (row : Fin 8) :
    ∃ g : ℝ → ℝ, ContinuousAt g 0 ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ), component imag s row (coordinates (s+4) x ε) -
        (truncatedReadout d imag (s+4) x row).eval ε = ε^d * g ε := by
  let n := s+4
  have hn : 7 ≤ n := by dsimp [n]; omega
  let p := truncatedReadout d imag n x row
  let m := realMass n x
  let v := realEntry imag n x row
  have htrunc : PowerSeries.trunc d (↑(p*m) : PowerSeries ℝ) =
      PowerSeries.trunc d (↑v : PowerSeries ℝ) := by
    push_cast
    unfold p truncatedReadout
    rw [PowerSeries.trunc_trunc_mul, normalized_series_mul imag n hn]
  have hdiv : (X : Polynomial ℝ)^d ∣ v - p*m := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    have hh := congrArg (fun q : Polynomial ℝ => q.coeff i) htrunc
    simp only [PowerSeries.coeff_trunc, ite_eq_left hi, Polynomial.coeff_coe] at hh
    rw [coeff_sub, hh, sub_self]
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨fun ε => q.eval ε / m.eval ε, ?_, ?_⟩
  · refine q.continuous.continuousAt.div m.continuous.continuousAt ?_
    change (realMass n x).eval 0 ≠ 0
    rw [← coeff_zero_eq_eval_zero, coeff_realMass]
    exact massCoeff_ne_zero n hn x
  · filter_upwards [mass_eventually_ne_zero n hn x] with ε hm
    rw [component_eq_quotient]
    change v.eval ε / m.eval ε - p.eval ε = ε^d * (q.eval ε / m.eval ε)
    have hh := congrArg (Polynomial.eval ε) hq
    simp only [eval_sub, eval_mul, eval_pow, eval_X] at hh
    change m.eval ε ≠ 0 at hm
    field_simp
    linear_combination hh

/-- The exact physical forbidden readout along the matched polynomial paths has
the certified fourth-order expansion, with a little-o remainder. -/
theorem opposite_polynomial_forbidden_expansion (s : ℕ) (hs : 3 ≤ s) (x : Path)
    (ht : x.t = oppositeSlope (s+4))
    (hr : ∀ k ≤ 3, regularCoeff (s+4) x k = regularCoeff (s+4) original k) :
    (fun ε => component false s 6 (coordinates (s+4) x ε) -
      component false s 6 (coordinates (s+4) original ε) - quartic (s+4) * ε^4)
      =o[𝓝 (0 : ℝ)] (fun ε => ε^4) := by
  let n := s+4
  have hn : 7 ≤ n := by dsimp [n]; omega
  obtain ⟨hlo, hfour, _, _⟩ := opposite_forbidden_first_difference n hn x ht hr
  obtain ⟨g, hg, hx⟩ := polynomial_readout_remainder 5 false s hs x 6
  obtain ⟨g₀, hg₀, hx₀⟩ := polynomial_readout_remainder 5 false s hs original 6
  have hd : truncatedReadout 5 false n x 6 - truncatedReadout 5 false n original 6 =
      monomial 4 (quartic n) := by
    ext k
    simp only [truncatedReadout, coeff_sub, PowerSeries.coeff_trunc, PowerSeries.coeff_mk]
    by_cases hk : k < 5
    · rw [ite_eq_left hk, ite_eq_left hk]
      by_cases h : k = 4
      · subst k
        simpa using hfour
      · rw [hlo k (by omega)]
        simp [coeff_monomial, Ne.symm h]
    · simp [hk, coeff_monomial, show 4 ≠ k by omega]
  have heq : (fun ε => component false s 6 (coordinates n x ε) -
      component false s 6 (coordinates n original ε) - quartic n * ε^4) =ᶠ[𝓝 0]
      fun ε => (ε * (g ε - g₀ ε))*ε^4 := by
    filter_upwards [hx, hx₀] with ε h₁ h₀
    have he := congrArg (Polynomial.eval ε) hd
    simp only [eval_sub, eval_monomial] at he
    rw [pow_succ] at h₁ h₀
    linear_combination h₁ - h₀ + he
  apply Asymptotics.IsLittleO.congr' _ heq.symm (Filter.EventuallyEq.rfl)
  have hcont : ContinuousAt (fun ε => ε * (g ε - g₀ ε)) (0 : ℝ) :=
    continuous_id.continuousAt.mul (hg.sub hg₀)
  have hzero : Tendsto (fun ε => ε * (g ε - g₀ ε)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [ContinuousAt] using hcont
  have hl : (fun ε : ℝ => ε * (g ε - g₀ ε)) =o[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff _).mpr hzero
  simpa using hl.mul_isBigO (isBigO_refl (fun ε : ℝ => ε^4) (𝓝 0))

end

#print axioms no_equal_polynomial_readout_germs
#print axioms opposite_polynomial_forbidden_expansion

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreNormalizedJet
