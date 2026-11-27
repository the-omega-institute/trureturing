/- GID: D5/S3/CharacterSums/DirichletTrivialZeros
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletTrivialZeros
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separate the simple Gamma zeros from the completed Dirichlet zero divisor. -/

import D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic
import D5.S3.CharacterSums.NonprincipalCharacterGrowth
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Real.Pi.Bounds
import D5.S3.Weil.ZetaExplicit.GammaRBracket
import D5.S3.Weil.ZetaSeam.ZetaReflect
import D5.S3.Weil.ZetaExplicit.XiLogDeriv
import D5.S3.Analytic.Resolvent.EntireLogDerivPowers
import D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds


/-! # The complete Dirichlet zero divisor

The reciprocal Gamma recurrence proves simplicity at every nonpositive integer.
The resulting divisor identity includes the zero at zero for even characters.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory
open scoped ComplexConjugate
open D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
open scoped Classical
namespace D5.S3.CharacterSums.DirichletTrivialZeros

private theorem invGamma_deriv_ne_zero (n : ℕ) :
    deriv (fun z : ℂ => (Gamma z)⁻¹) (-(n : ℂ)) ≠ 0 := by
  let H : ℂ → ℂ := fun z => (Gamma z)⁻¹
  have hfun :
      D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit.reciprocalGamma = H := rfl
  have hder (z : ℂ) : deriv H z = H (z + 1) + z * deriv H (z + 1) := by
    have hd :=
      D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit.reciprocal_gamma_deriv_shift
        (z + 1)
    rw [hfun] at hd
    simpa only [add_sub_cancel_right] using hd
  change deriv H (-(n : ℂ)) ≠ 0
  induction n with
  | zero =>
    rw [Nat.cast_zero, neg_zero, hder]
    norm_num [H]
  | succ n ih =>
    rw [hder]
    have hz : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
    rw [hz]
    have hH : H (-(n : ℂ)) = 0 := by simp [H, Gamma_neg_nat_eq_zero]
    rw [hH, zero_add]
    exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) ih

private theorem invGamma_order (z : ℂ) :
    analyticOrderAt (fun z : ℂ => (Gamma z)⁻¹) z =
      if ∃ n : ℕ, z = -(n : ℂ) then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨n, rfl⟩ := h
    exact AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (differentiable_one_div_Gamma.analyticAt _)
      (by simp [Gamma_neg_nat_eq_zero]) (invGamma_deriv_ne_zero n)
  · apply (differentiable_one_div_Gamma.analyticAt z).analyticOrderAt_eq_zero.mpr
    exact inv_ne_zero (Gamma_ne_zero (by simpa only [not_exists] using h))

private theorem invGammaReal_order (z : ℂ) :
    analyticOrderAt (fun z : ℂ => (Gammaℝ z)⁻¹) z =
      if ∃ n : ℕ, z = -(2 * (n : ℂ)) then 1 else 0 := by
  classical
  let A : ℂ → ℂ := fun z => ((Real.pi : ℂ) ^ (-z / 2))⁻¹
  let H : ℂ → ℂ := fun z => (Gamma (z / 2))⁻¹
  have hA : Differentiable ℂ A := by
    intro z
    apply DifferentiableAt.inv
    · exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · simp [Real.pi_ne_zero]
  have hH : Differentiable ℂ H :=
    differentiable_one_div_Gamma.comp (differentiable_id.div_const 2)
  have he : (fun z : ℂ => (Gammaℝ z)⁻¹) = A * H := by
    funext z; simp [Gammaℝ_def, A, H, mul_comm]
  rw [he, analyticOrderAt_mul (hA.analyticAt z) (hH.analyticAt z)]
  have hAz : A z ≠ 0 := by simp [A, Real.pi_ne_zero]
  rw [(hA.analyticAt z).analyticOrderAt_eq_zero.mpr hAz, zero_add]
  have hc := analyticOrderAt_comp_of_deriv_ne_zero
    (f := fun z : ℂ => (Gamma z)⁻¹) (g := fun z : ℂ => z / 2) (z₀ := z)
    (by fun_prop) (by norm_num)
  change analyticOrderAt H z = _ at hc
  rw [hc, invGamma_order]
  have hi : (∃ n : ℕ, z / 2 = -(n : ℂ)) ↔
      ∃ n : ℕ, z = -(2 * (n : ℂ)) := by
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by linear_combination 2 * hn⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by ring⟩
  simp only [hi]

/-- The Gamma lattice attached to the parity of a Dirichlet character. -/
def trivialPoint {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  -(if χ.Even then 0 else 1) - 2 * (n : ℂ)

private theorem invGammaFactor_order {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    analyticOrderAt (fun z => (χ.gammaFactor z)⁻¹) s =
      if ∃ n : ℕ, s = trivialPoint χ n then 1 else 0 := by
  classical
  unfold DirichletCharacter.gammaFactor trivialPoint
  by_cases h : χ.Even
  · simp only [if_pos h]
    simpa using invGammaReal_order s
  · simp only [if_neg h]
    have hc := analyticOrderAt_comp_of_deriv_ne_zero
      (f := fun z : ℂ => (Gammaℝ z)⁻¹) (g := fun z : ℂ => z + 1) (z₀ := s)
      (by fun_prop) (by simp)
    change analyticOrderAt (fun z : ℂ => (Gammaℝ (z + 1))⁻¹) s = _ at hc
    rw [hc, invGammaReal_order]
    have hi : (∃ n : ℕ, s + 1 = -(2 * (n : ℂ))) ↔
        ∃ n : ℕ, s = -(1 : ℂ) - 2 * (n : ℂ) := by
      constructor
      · rintro ⟨n, hn⟩; exact ⟨n, by linear_combination hn⟩
      · rintro ⟨n, hn⟩; exact ⟨n, by linear_combination hn⟩
    simp only [hi]

/-- At regular centers, the zero divisor is the completed divisor plus the parity lattice. -/
theorem LFunction_zero_divisor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (h0 : s ≠ 0 ∨ q ≠ 1) (h1 : s ≠ 1 ∨ χ ≠ 1) :
    (χ.LFunction s = 0 ↔ χ.completedLFunction s = 0 ∨
      ∃ n : ℕ, s = trivialPoint χ n) ∧
    analyticOrderAt χ.LFunction s = analyticOrderAt χ.completedLFunction s +
      if ∃ n : ℕ, s = trivialPoint χ n then 1 else 0 := by
  classical
  have hloc : ∀ᶠ z in 𝓝 s, z ≠ 0 ∨ q ≠ 1 := by
    rcases h0 with h0 | hq
    · filter_upwards [isOpen_ne.mem_nhds h0] with z hz using Or.inl hz
    · exact Filter.Eventually.of_forall fun _ => Or.inr hq
  have hloc1 : ∀ᶠ z in 𝓝 s, z ≠ 1 ∨ χ ≠ 1 := by
    rcases h1 with h1 | hχ
    · filter_upwards [isOpen_ne.mem_nhds h1] with z hz using Or.inl hz
    · exact Filter.Eventually.of_forall fun _ => Or.inr hχ
  have hc : AnalyticAt ℂ χ.completedLFunction s := by
    apply analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [hloc, hloc1] with z hz0 hz1
    exact χ.differentiableAt_completedLFunction z hz0 hz1
  have he : χ.LFunction =ᶠ[𝓝 s]
      χ.completedLFunction * (fun z => (χ.gammaFactor z)⁻¹) := by
    filter_upwards [hloc] with z hz
    rw [χ.LFunction_eq_completed_div_gammaFactor z hz]
    rfl
  have hg : Differentiable ℂ (fun z => (χ.gammaFactor z)⁻¹) := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact differentiable_Gammaℝ_inv
    · exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
  refine ⟨?_, ?_⟩
  · rw [he.eq_of_nhds, Pi.mul_apply, mul_eq_zero]
    rw [← (hg.analyticAt s).analyticOrderAt_ne_zero, invGammaFactor_order]
    split_ifs <;> simp_all
  · rw [analyticOrderAt_congr he, analyticOrderAt_mul hc (hg.analyticAt s),
      invGammaFactor_order]

private theorem norm_Gamma_le {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  have he := norm_Gamma_sq_eq hz z.im
  have hp := one_le_gammaVertProd z.re z.im
  have hz' : (z.re : ℂ) + I * z.im = z := by
    apply Complex.ext <;> simp
  rw [hz'] at he
  have hb : ‖Complex.Gamma z‖ ^ 2 ≤ Real.Gamma z.re ^ 2 := by
    rw [he]
    exact div_le_self (sq_nonneg _) hp
  nlinarith [norm_nonneg (Complex.Gamma z), Real.Gamma_pos_of_pos hz]
private theorem Gamma_le_max_factorial {u : ℝ} (hu : 1 / 4 ≤ u) :
    Real.Gamma u ≤ max (Real.Gamma (1 / 4)) (Nat.factorial (⌈u⌉₊ - 1) : ℝ) := by
  have hn : 0 < ⌈u⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc
    (by norm_num : (1 / 4 : ℝ) ∈ Ioi 0)
    (show (⌈u⌉₊ : ℝ) ∈ Ioi 0 by
      change 0 < (⌈u⌉₊ : ℝ)
      exact_mod_cast hn)
    (show u ∈ Icc (1 / 4) (⌈u⌉₊ : ℝ) from ⟨hu, Nat.le_ceil u⟩)
  have he : (⌈u⌉₊ : ℝ) = ((⌈u⌉₊ - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hn).symm
  simpa only [he, Real.Gamma_nat_eq_factorial] using h
private theorem Gamma_le_exp_bound {u : ℝ} (hu : 1 / 4 ≤ u) :
    Real.Gamma u ≤ Real.Gamma (1 / 4) ∨
      Real.Gamma u < Real.exp ((u + 1) * Real.log (u + 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have hup : 0 < u + 1 := by linarith
  have hn : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
  have hl : 0 < Real.log (u + 1) := Real.log_pos (by linarith)
  have hfac : (Nat.factorial (⌈u⌉₊ - 1) : ℝ) <
      Real.exp ((u + 1) * Real.log (u + 1)) := by
    calc
      _ ≤ (Nat.factorial ⌈u⌉₊ : ℝ) := by
        exact_mod_cast Nat.factorial_le (Nat.sub_le ⌈u⌉₊ 1)
      _ ≤ (⌈u⌉₊ : ℝ) ^ ⌈u⌉₊ := by exact_mod_cast Nat.factorial_le_pow ⌈u⌉₊
      _ ≤ (u + 1) ^ ⌈u⌉₊ := pow_le_pow_left₀ (by positivity) hn.le _
      _ = Real.exp (Real.log (u + 1) * (⌈u⌉₊ : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hup]
      _ < _ := Real.exp_lt_exp.mpr (by nlinarith)
  rcases le_max_iff.mp (Gamma_le_max_factorial hu) with h | h
  · exact .inl h
  · exact .inr (h.trans_lt hfac)
private theorem norm_GammaReal_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp only [div_ofNat_re, neg_re]
  have hg := norm_Gamma_le (z := s / 2) (by simpa using div_pos hs two_pos)
  simpa only [div_ofNat_re] using mul_le_mul_of_nonneg_left hg
    (Real.rpow_nonneg Real.pi_pos.le _)
def completion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * s) * χ.completedLFunction s
private theorem differentiable_completion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) : Differentiable ℂ (completion χ) := by
  exact ((differentiable_const _).mul differentiable_id).cexp.mul
    (DirichletCharacter.differentiable_completedLFunction hne)
private theorem completion_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    completion χ (1 - s) = χ.rootNumber * completion χ⁻¹ s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hc : Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * (1 - s)) *
      (q : ℂ) ^ (s - 1 / 2) =
      Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero hq,
      ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q),
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp only [completion]
  rw [hχ.completedLFunction_one_sub]
  calc
    _ = (Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * (1 - s)) *
        (q : ℂ) ^ (s - 1 / 2)) * χ.rootNumber * χ⁻¹.completedLFunction s := by ring
    _ = _ := by rw [hc]; ring
private theorem completion_ne_zero_of_one_le_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1 ∨ q = 1) (hs : 1 ≤ s.re) :
    completion χ s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hL : χ.LFunction s ≠ 0 := by
    rcases hχs with hne | hs1 | hq1
    · exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) hs
    · exact χ.LFunction_ne_zero_of_one_le_re (.inr hs1) hs
    · subst q
      rw [DirichletCharacter.LFunction_modOne_eq]
      by_cases hs1 : s = 1
      · simpa [hs1] using riemannZeta_one_ne_zero
      · exact riemannZeta_ne_zero_of_one_le_re hs
  apply mul_ne_zero (Complex.exp_ne_zero _)
  intro h
  exact hL (by rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0), h, zero_div])
private theorem rootNumber_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h
  have he := completion_one_sub hχ (-1)
  rw [h, zero_mul] at he
  have hn := completion_ne_zero_of_one_le_re χ (s := 2) (.inr (.inl (by norm_num)))
    (by norm_num)
  exact hn (by convert he using 1 <;> norm_num)
private theorem completion_ne_zero_of_re_le_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : s.re ≤ 0) : completion χ s ≠ 0 := by
  have hni : χ⁻¹ ≠ 1 ∨ 1 - s ≠ 1 ∨ q = 1 := by
    by_cases hne : χ = 1
    · right; right
      simpa only [DirichletCharacter.IsPrimitive, hne,
        DirichletCharacter.conductor_one] using hχ.symm
    · exact .inl (inv_ne_one.mpr hne)
  have hn := completion_ne_zero_of_one_le_re χ⁻¹ (s := 1 - s) hni
    (by simp only [sub_re, one_re]; linarith)
  have he := completion_one_sub hχ (1 - s)
  rw [sub_sub_cancel] at he
  rw [he]
  exact mul_ne_zero (rootNumber_ne_zero hχ) hn
private theorem gammaFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  classical
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith
private theorem completed_eq_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    χ.completedLFunction s = χ.gammaFactor s * χ.LFunction s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have he := (div_eq_iff (gammaFactor_ne_zero χ hs)).mp
    (χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0)).symm
  exact he.trans (mul_comm _ _)
private theorem mellin_conj_real (f : ℝ → ℂ) (hf : ∀ t, conj (f t) = f t)
    (s : ℂ) : mellin f (conj s) = conj (mellin f s) := by
  rw [mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul, map_mul]
  rw [hf]
  have htarg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  rw [show conj s - 1 = conj (s - 1) by simp,
    cpow_conj (t : ℂ) (s - 1) htarg]
  simp
private theorem hurwitz_conj (a : UnitAddCircle) (s : ℂ) :
    HurwitzZeta.completedHurwitzZetaEven a (conj s) =
      conj (HurwitzZeta.completedHurwitzZetaEven a s) ∧
    HurwitzZeta.completedHurwitzZetaOdd a (conj s) =
      conj (HurwitzZeta.completedHurwitzZetaOdd a s) := by
  have he (z : ℂ) :
      (HurwitzZeta.hurwitzEvenFEPair a).Λ₀ (conj z) =
        conj ((HurwitzZeta.hurwitzEvenFEPair a).Λ₀ z) := by
    apply mellin_conj_real
    intro t
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      Function.comp_apply, smul_eq_mul, one_mul]
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> by_cases hu : t ∈ Ioo (0 : ℝ) 1 <;>
      by_cases ha : a = 0 <;> simp [ht, hu, ha]
  have ho (z : ℂ) :
      (HurwitzZeta.hurwitzOddFEPair a).Λ₀ (conj z) =
        conj ((HurwitzZeta.hurwitzOddFEPair a).Λ₀ z) := by
    apply mellin_conj_real
    intro t
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzOddFEPair,
      Function.comp_apply, smul_eq_mul, one_mul, sub_zero, mul_zero]
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> by_cases hu : t ∈ Ioo (0 : ℝ) 1 <;>
      simp [ht, hu]
  constructor
  · unfold HurwitzZeta.completedHurwitzZetaEven WeakFEPair.Λ
    rw [show conj s / 2 = conj (s / 2) by simp [map_ofNat], he]
    by_cases ha : a = 0 <;> simp [map_ofNat, HurwitzZeta.hurwitzEvenFEPair, ha]
  · unfold HurwitzZeta.completedHurwitzZetaOdd WeakFEPair.Λ
    rw [show (conj s + 1) / 2 = conj ((s + 1) / 2) by simp [map_ofNat], ho]
    simp [map_ofNat, HurwitzZeta.hurwitzOddFEPair]
private theorem completion_inv_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) : completion χ⁻¹ (conj s) = conj (completion χ s) := by
  have hqarg : (q : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg q)]
    exact Real.pi_pos.ne
  have hc : (q : ℂ) ^ (-conj s) = conj ((q : ℂ) ^ (-s)) := by
    simpa using Complex.cpow_conj (q : ℂ) (-s) hqarg
  unfold completion DirichletCharacter.completedLFunction ZMod.completedLFunction
  rw [show (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * conj s) =
      conj (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * s) by rw [map_mul, Complex.conj_ofReal],
    Complex.exp_conj, hc]
  simp only [map_mul, map_add, map_sum]
  congr 2 <;> congr 1 <;> apply Finset.sum_congr rfl <;> intro j _
  · rw [(MulChar.star_apply' χ j).symm, (hurwitz_conj _ s).1]
    rfl
  · rw [(MulChar.star_apply' χ j).symm, (hurwitz_conj _ s).2]
    rfl
private theorem norm_rootNumber {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : ‖χ.rootNumber‖ = 1 := by
  by_cases hne : χ = 1
  · have hq : q = 1 := by
      simpa only [DirichletCharacter.IsPrimitive, hne,
        DirichletCharacter.conductor_one] using hχ.symm
    subst q
    rw [DirichletCharacter.rootNumber_modOne, norm_one]
  have hi (t : ℝ) : ‖completion χ⁻¹ t‖ = ‖completion χ t‖ := by
    have h := congrArg norm (completion_inv_conj χ (t : ℂ))
    simpa using h
  have ha := congrArg norm (completion_one_sub hχ (-1))
  have hb := congrArg norm (completion_one_sub hχ 2)
  norm_num only [show (1 : ℂ) - -1 = 2 by norm_num,
    show (1 : ℂ) - 2 = -1 by norm_num, norm_mul] at ha hb
  have him : ‖completion χ⁻¹ (-1)‖ = ‖completion χ (-1)‖ := by simpa using hi (-1)
  have hi2 : ‖completion χ⁻¹ 2‖ = ‖completion χ 2‖ := by simpa using hi 2
  rw [him] at ha
  rw [hi2] at hb
  have hp : 0 < ‖completion χ (-1)‖ := norm_pos_iff.mpr
    (completion_ne_zero_of_re_le_zero hχ (by norm_num))
  have hsq : ‖χ.rootNumber‖ ^ 2 = 1 := by
    have he : (‖χ.rootNumber‖ ^ 2 - 1) * ‖completion χ (-1)‖ = 0 := by
      rw [ha] at hb
      nlinarith only [hb]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hp.ne')
  nlinarith [norm_nonneg χ.rootNumber]
def gammaConstant : ℝ := max 1 (Real.Gamma (1 / 4))
def growthConstant (q : ℕ) : ℝ :=
  max (Real.log (gammaConstant * (q.totient : ℝ)) +
    Real.log (q : ℝ) / 2 + 2 * Real.log 2) 3
private theorem gamma_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} {R : ℝ} (hs : 1 / 2 ≤ s.re) (hn : ‖s‖ ≤ R) :
    ‖χ.gammaFactor s‖ ≤ gammaConstant *
      Real.exp (((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
  classical
  have hR : 1 / 2 ≤ R := hs.trans ((Complex.re_le_norm s).trans hn)
  have hB : 0 ≤ gammaConstant := (zero_le_one.trans (le_max_left _ _))
  have hb (t : ℂ) (ht : 1 / 2 ≤ t.re) (htR : t.re ≤ R + 1) :
      ‖Complex.Gammaℝ t‖ ≤ gammaConstant *
        Real.exp (((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
    have ht0 : 0 < t.re := by linarith
    have hp : Real.pi ^ (-t.re / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi) (by linarith)
    have hx : 1 ≤ t.re / 2 + 1 := by linarith
    have hU : t.re / 2 + 1 ≤ (R + 3) / 2 := by linarith
    have hl := Real.log_le_log (by linarith : 0 < t.re / 2 + 1) hU
    have hg := Gamma_le_exp_bound
      (u := t.re / 2) (by linarith)
    have hg' : Real.Gamma (t.re / 2) ≤ gammaConstant *
        Real.exp ((t.re / 2 + 1) * Real.log (t.re / 2 + 1)) := by
      have hmax := hg.elim (fun h => h.trans (le_max_left _ _))
        (fun h => h.le.trans (le_max_right _ _))
      refine hmax.trans (max_le ?_ ?_)
      · exact (le_max_right 1 _).trans (le_mul_of_one_le_right
          (show 0 ≤ gammaConstant from hB) (Real.one_le_exp
            (mul_nonneg (by linarith) (Real.log_nonneg hx))))
      · exact le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
    calc
      _ ≤ Real.pi ^ (-t.re / 2) * Real.Gamma (t.re / 2) :=
        norm_GammaReal_le ht0
      _ ≤ Real.Gamma (t.re / 2) :=
        mul_le_of_le_one_left (Real.Gamma_pos_of_pos (by linarith)).le hp
      _ ≤ _ := hg'.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul hU hl (Real.log_nonneg hx)
          (by linarith))) hB)
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact hb s hs ((Complex.re_le_norm s).trans (hn.trans (by linarith)))
  · apply hb (s + 1)
    · simp only [add_re, one_re]; linarith
    · simp only [add_re, one_re]; linarith [Complex.re_le_norm s]
private theorem right_growth_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {s : ℂ} {R : ℝ}
    (hs : 1 / 2 ≤ s.re) (hn : ‖s‖ ≤ R) :
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * R *
      Real.exp (Real.log (q : ℝ) / 2 * R +
        ((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
  have hp : 0 < s.re := by linarith
  have hq : 0 ≤ Real.log (q : ℝ) / 2 := by
    apply div_nonneg _ (by norm_num)
    exact Real.log_nonneg (by exact_mod_cast NeZero.one_le (n := q))
  have hL : ‖χ.LFunction s‖ < (q.totient : ℝ) * R := by
    refine (NonprincipalCharacterGrowth.nonprincipal_growth χ hne hp).trans_le ?_
    calc
      _ ≤ (q.totient : ℝ) * ‖s‖ := by
        apply (div_le_iff₀ hp).mpr
        have hh := mul_nonneg (Nat.cast_nonneg q.totient) (norm_nonneg s)
        nlinarith only [mul_nonneg hh (sub_nonneg.mpr hs)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
  have hE : Real.exp (Real.log (q : ℝ) / 2 * s.re) ≤
      Real.exp (Real.log (q : ℝ) / 2 * R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((Complex.re_le_norm s).trans hn) hq)
  have hG := gamma_bound χ hs hn
  have hG0 : 0 < ‖χ.gammaFactor s‖ := norm_pos_iff.mpr (gammaFactor_ne_zero χ hp)
  rw [completion, completed_eq_mul χ hp, norm_mul, norm_mul, Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  calc
    _ < (Real.exp (Real.log (q : ℝ) / 2 * s.re) * ‖χ.gammaFactor s‖) *
        ((q.totient : ℝ) * R) := by
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left hL
        (mul_pos (Real.exp_pos _) hG0)
    _ ≤ (Real.exp (Real.log (q : ℝ) / 2 * R) *
        (gammaConstant * Real.exp (((R + 3) / 2) * Real.log ((R + 3) / 2)))) *
        ((q.totient : ℝ) * R) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hE hG (norm_nonneg _)
        (Real.exp_pos _).le) (mul_nonneg (Nat.cast_nonneg _)
          (by linarith [hs.trans ((Complex.re_le_norm s).trans hn)]))
    _ = _ := by rw [Real.exp_add]; ring
private theorem completion_growth_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (R : ℝ)
    (hside : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) (hn : 1 / 2 ≤ s.re → ‖s‖ ≤ R)
    (href : s.re < 1 / 2 → ‖1 - s‖ ≤ R) :
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * R *
      Real.exp (Real.log (q : ℝ) / 2 * R +
        ((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
  by_cases hs : 1 / 2 ≤ s.re
  · exact right_growth_radius χ hne hs (hn hs)
  · have hχ := hside.resolve_left hs
    have ht : 1 / 2 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
    have hb := right_growth_radius χ⁻¹ (inv_ne_one.mpr hne) ht (href (lt_of_not_ge hs))
    have he := congrArg norm (completion_one_sub hχ (1 - s))
    rw [sub_sub_cancel, norm_mul, norm_rootNumber hχ, one_mul] at he
    rwa [he]
private theorem completion_growth_explicit {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (s : ℂ) (hχ : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) :
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * (1 + ‖s‖) *
      Real.exp (Real.log (q : ℝ) / 2 * (1 + ‖s‖) +
        ((‖s‖ + 4) / 2) * Real.log ((‖s‖ + 4) / 2)) := by
  convert completion_growth_radius χ hne s (1 + ‖s‖) hχ
    (fun _ => by linarith) (fun _ => by simpa using norm_sub_le (1 : ℂ) s) using 1 <;> ring_nf
private theorem completion_growth_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (s : ℂ) (hχ : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) :
    ‖completion χ s‖ < Real.exp
      (growthConstant q * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖))) := by
  let R := 1 + ‖s‖
  let A := gammaConstant * (q.totient : ℝ)
  let b := Real.log (q : ℝ) / 2
  let U := (‖s‖ + 4) / 2
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg s]
  have hRp : 0 < R := by linarith
  have hA : 1 ≤ A := by
    apply one_le_mul_of_one_le_of_one_le
    · exact le_max_left _ _
    · exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hAp : 0 < A := by linarith
  have hlA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hU : 1 ≤ U := by dsimp [U, R] at *; linarith
  have hUR : U ≤ 2 * R := by dsimp [U, R] at *; linarith
  have hlU : Real.log U ≤ Real.log 2 + Real.log R := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRp.ne']
    exact Real.log_le_log (by linarith) hUR
  have hUl : U * Real.log U ≤ 2 * R * (Real.log 2 + Real.log R) :=
    mul_le_mul hUR hlU (Real.log_nonneg hU) (by linarith)
  have hC : Real.log A + b + 2 * Real.log 2 ≤ growthConstant q := le_max_left _ _
  have hC3 : 3 ≤ growthConstant q := le_max_right _ _
  have hAlog : Real.log A ≤ Real.log A * R := le_mul_of_one_le_right hlA hR
  have hRlog : Real.log R ≤ R * Real.log R := le_mul_of_one_le_left hlR hR
  have he : Real.log A + Real.log R + (b * R + U * Real.log U) ≤
      growthConstant q * R * (1 + Real.log R) := by
    calc
      _ ≤ (Real.log A + b + 2 * Real.log 2) * R + 3 * (R * Real.log R) := by
        nlinarith only [hUl, hAlog, hRlog]
      _ ≤ growthConstant q * R + growthConstant q * (R * Real.log R) :=
        add_le_add (mul_le_mul_of_nonneg_right hC hRp.le)
          (mul_le_mul_of_nonneg_right hC3 (mul_nonneg hRp.le hlR))
      _ = _ := by ring
  refine (completion_growth_explicit hne s hχ).trans_le ?_
  change A * R * Real.exp (b * R + U * Real.log U) ≤ _
  calc
    _ = Real.exp (Real.log A + Real.log R + (b * R + U * Real.log U)) := by
      simp only [Real.exp_add, Real.exp_log hAp, Real.exp_log hRp]
    _ ≤ _ := Real.exp_le_exp.mpr he
theorem completion_power_growth {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (s : ℂ) (hside : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) :
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * (1 + ‖s‖) *
      Real.exp (Real.log (q : ℝ) / 2 * (1 + ‖s‖) +
        ((‖s‖ + 4) / 2) * Real.log ((‖s‖ + 4) / 2)) ∧
    ‖completion χ s‖ < Real.exp
      (growthConstant q * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖))) ∧
    ‖completion χ s‖ < Real.exp (3 * growthConstant q * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  refine ⟨completion_growth_explicit hne s hside, completion_growth_log hne s hside, ?_⟩
  let R := 1 + ‖s‖
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg s]
  have hp : 0 < R := by linarith
  have hroot : 1 ≤ R ^ (1 / 2 : ℝ) := Real.one_le_rpow hR (by norm_num)
  have hl : Real.log R ≤ 2 * R ^ (1 / 2 : ℝ) := by
    have hh := Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hC : 0 ≤ growthConstant q := (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_right _ _)
  refine (completion_growth_log hne s hside).trans_le (Real.exp_le_exp.mpr ?_)
  change growthConstant q * R * (1 + Real.log R) ≤ _
  have he : R ^ (3 / 2 : ℝ) = R * R ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one]
  change _ ≤ 3 * growthConstant q * R ^ (3 / 2 : ℝ)
  rw [he]
  nlinarith [mul_nonneg (mul_nonneg hC hp.le) (by linarith :
    0 ≤ 3 * R ^ (1 / 2 : ℝ) - (1 + Real.log R))]
theorem completion_zero_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {ρ : ℂ} (hρ : completion χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra! h
    exact completion_ne_zero_of_re_le_zero hχ h hρ
  · by_contra! h
    have hn : χ ≠ 1 ∨ ρ ≠ 1 ∨ q = 1 := by
      by_cases hc : χ = 1
      · right; right
        simpa only [DirichletCharacter.IsPrimitive, hc,
          DirichletCharacter.conductor_one] using hχ.symm
      · exact .inl hc
    exact completion_ne_zero_of_one_le_re χ hn h hρ
private theorem completion_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    completion χ (1 - conj s) = χ.rootNumber * conj (completion χ s) := by
  rw [completion_one_sub hχ, completion_inv_conj]
private theorem completion_reflect_order {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    (completion χ (1 - conj s) = 0 ↔ completion χ s = 0) ∧
    analyticOrderAt (completion χ) (1 - conj s) =
      analyticOrderAt (completion χ) s := by
  have hFi := differentiable_completion χ⁻¹ (inv_ne_one.mpr hne)
  have hi : analyticOrderAt (completion χ⁻¹) (conj s) =
      analyticOrderAt (completion χ) s := by
    have he : completion χ⁻¹ = fun z => conj (completion χ (conj z)) := by
      funext z
      simpa using completion_inv_conj χ (conj z)
    rw [he]
    exact Zeta23.analyticOrderAt_conj_conj (completion χ) s
  have heq : (fun z : ℂ => completion χ (1 - z)) =
      fun z => χ.rootNumber * completion χ⁻¹ z := funext (completion_one_sub hχ)
  have hc := analyticOrderAt_comp_of_deriv_ne_zero (f := completion χ)
    (g := fun z : ℂ => 1 - z) (z₀ := conj s) (by fun_prop) (by simp)
  have hm := analyticOrderAt_mul (f := fun _ : ℂ => χ.rootNumber)
    analyticAt_const (hFi.analyticAt (conj s))
  change analyticOrderAt (fun z => χ.rootNumber * completion χ⁻¹ z) (conj s) = _ at hm
  have hr : analyticOrderAt (fun _ : ℂ => χ.rootNumber) (conj s) = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (rootNumber_ne_zero hχ)
  have ho : analyticOrderAt (completion χ) (1 - conj s) =
      analyticOrderAt (completion χ) s := by
    rw [Function.comp_def, heq, hm, hr, zero_add] at hc
    exact hc.symm.trans hi
  refine ⟨?_, ho⟩
  rw [completion_reflect hχ, mul_eq_zero]
  simp [rootNumber_ne_zero hχ]
private theorem logDeriv_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (completion χ) (1 - conj s) = -conj (logDeriv (completion χ) s) := by
  have hF := differentiable_completion χ hne
  have heq : completion χ⁻¹ = conj ∘ completion χ ∘ conj := by
    funext z; simpa using completion_inv_conj χ (conj z)
  have hd : deriv (completion χ⁻¹) (conj s) = conj (deriv (completion χ) s) := by
    rw [heq, deriv_conj_conj]
    simp only [Function.comp_apply, conj_conj]
  have hl : logDeriv (completion χ⁻¹) (conj s) = conj (logDeriv (completion χ) s) := by
    simp only [logDeriv_apply, hd, completion_inv_conj, map_div₀]
  have he : (completion χ) ∘ (fun z : ℂ => 1 - z) =
      fun z => χ.rootNumber * completion χ⁻¹ z := funext (completion_one_sub hχ)
  have hh := logDeriv_comp (x := conj s) (f := completion χ)
    (g := fun z : ℂ => 1 - z) (hF _) (by fun_prop)
  rw [he, logDeriv_const_mul _ _ (rootNumber_ne_zero hχ), hl] at hh
  have hh' : conj (logDeriv (completion χ) s) =
      logDeriv (completion χ) (1 - conj s) * (-1) := by simpa using hh
  linear_combination hh'
theorem completion_vertical_resolvent {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (σ t : ℝ)
    (hcenter : completion χ ((σ : ℂ) + t * I) ≠ 0) :
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * (σ - ρ.1.re) /
        ((σ - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2))
      (logDeriv (completion χ) ((σ : ℂ) + t * I)).re := by
  let F := completion χ
  let s : ℂ := σ + t * I
  let a : ℂ := 1 - conj s
  let k := fun ρ : {z : ℂ // F z = 0} =>
    (analyticOrderNatAt F ρ.1 : ℝ) * (σ - ρ.1.re) /
      ((σ - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2)
  let e : {z : ℂ // F z = 0} ≃ {z : ℂ // F z = 0} :=
    { toFun := fun ρ => ⟨1 - conj ρ.1, (completion_reflect_order hχ hne ρ.1).1.mpr ρ.2⟩
      invFun := fun ρ => ⟨1 - conj ρ.1, (completion_reflect_order hχ hne ρ.1).1.mpr ρ.2⟩
      left_inv := by intro ρ; apply Subtype.ext; simp
      right_inv := by intro ρ; apply Subtype.ext; simp }
  have ho (ρ : {z : ℂ // F z = 0}) :
      analyticOrderNatAt F (e ρ).1 = analyticOrderNatAt F ρ.1 :=
    congrArg ENat.toNat (completion_reflect_order hχ hne ρ.1).2
  have hs : F s ≠ 0 := hcenter
  have ha : F a ≠ 0 := fun h => hs ((completion_reflect_order hχ hne s).1.mp h)
  have hF := differentiable_completion χ hne
  have hg := fun z => (completion_power_growth hne z (.inr hχ)).2.2.le
  have hsq : Summable (fun ρ : {z : ℂ // F z = 0} =>
      (analyticOrderNatAt F ρ.1 : ℝ) * ‖(s - ρ.1)⁻¹‖ ^ 2) := by
    simpa only [norm_mul, norm_pow, Complex.norm_natCast] using
      (D5.S3.Analytic.Resolvent.EntireLogDerivPowers.entire_logDeriv_power_hasSum
        hF (by norm_num : (3 / 2 : ℝ) < 2) hg 1 le_rfl hs).summable.norm
  have hks : Summable k := by
    apply Summable.of_norm_bounded
      (hsq.mul_left (|σ| + 1))
    intro ρ
    have hr := completion_zero_strip hχ ρ.2
    have hd : |σ - ρ.1.re| ≤ |σ| + 1 := by
      calc
        _ ≤ |σ| + |ρ.1.re| := abs_sub _ _
        _ ≤ |σ| + 1 := by rw [abs_of_pos hr.1]; linarith [hr.2]
    have hkform : k ρ = (analyticOrderNatAt F ρ.1 : ℝ) * (σ - ρ.1.re) *
        ‖(s - ρ.1)⁻¹‖ ^ 2 := by
      have hn : ‖s - ρ.1‖ ^ 2 = (σ - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq]
        simp [s, Complex.normSq_apply, pow_two]
      dsimp only [k]
      rw [norm_inv, inv_pow, hn, div_eq_mul_inv]
    rw [hkform, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (analyticOrderNatAt F ρ.1)),
      abs_of_nonneg (sq_nonneg ‖(s - ρ.1)⁻¹‖)]
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd
        (Nat.cast_nonneg (analyticOrderNatAt F ρ.1)))
      (sq_nonneg ‖(s - ρ.1)⁻¹‖)]
  have hh := Complex.hasSum_re
    (D5.S3.Analytic.Resolvent.EntireLogDerivDifference.entire_logDeriv_difference_hasSum
      (differentiable_completion χ hne) (by norm_num : (3 / 2 : ℝ) < 2)
      (fun z => (completion_power_growth hne z (.inr hχ)).2.2.le) ha hs)
  have hv : (logDeriv F s - logDeriv F a).re = 2 * (logDeriv F s).re := by
    rw [show logDeriv F a = -conj (logDeriv F s) from logDeriv_reflect hχ hne s]
    simp
    <;> ring
  have hp (ρ : {z : ℂ // F z = 0}) :
      ((analyticOrderNatAt F ρ.1 : ℂ) * ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)).re =
        k ρ + k (e ρ) := by
    dsimp only [k]
    rw [ho]
    simp [e, a, s, Complex.inv_re, Complex.normSq_apply]
    ring_nf
  change HasSum (fun ρ : {z : ℂ // F z = 0} =>
    ((analyticOrderNatAt F ρ.1 : ℂ) * ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)).re)
    (logDeriv F s - logDeriv F a).re at hh
  have hh' : HasSum (fun ρ => k ρ + k (e ρ)) (2 * (logDeriv F s).re) := by
    simpa only [hp, hv] using hh
  have he : HasSum (fun ρ => k (e ρ)) (∑' ρ, k ρ) := e.hasSum_iff.mpr hks.hasSum
  have heq := (hks.hasSum.add he).unique hh'
  have hval : (∑' ρ, k ρ) = (logDeriv F s).re := by linarith
  exact hval ▸ hks.hasSum
theorem completion_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    logDeriv (completion χ) s = ((Real.log (q : ℝ) - Real.log Real.pi) / 2 : ℝ) +
      (1 / 2 : ℂ) * Complex.digamma ((s + (if χ.Even then 0 else 1)) / 2) +
      logDeriv χ.LFunction s := by
  classical
  let b : ℂ := (Real.log (q : ℝ) / 2 : ℝ)
  have hpos : 0 < s.re := hs
  have hdG : DifferentiableAt ℂ χ.gammaFactor s := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Zeta23.WeilEF.differentiableAt_Gammaℝ hpos
    · exact (Zeta23.WeilEF.differentiableAt_Gammaℝ
        (by simp only [add_re, one_re]; linarith)).comp s (by fun_prop)
  have hlocal : completion χ =ᶠ[𝓝 s] fun z => Complex.exp (b * z) *
      (χ.gammaFactor z * χ.LFunction z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hpos] with z hz
    exact congrArg (fun w => Complex.exp (b * z) * w) (completed_eq_mul χ hz)
  rw [(logDeriv_congr_nhds hlocal).eq_of_nhds,
    logDeriv_fun_mul (f := fun z : ℂ => Complex.exp (b * z))
      (g := fun z => χ.gammaFactor z * χ.LFunction z) s
      (Complex.exp_ne_zero _) (mul_ne_zero (gammaFactor_ne_zero χ hpos) hL)
      (by fun_prop) (hdG.mul (χ.differentiableAt_LFunction s hpole)),
    logDeriv_fun_mul (f := χ.gammaFactor) (g := χ.LFunction) s
      (gammaFactor_ne_zero χ hpos) hL hdG
      (χ.differentiableAt_LFunction s hpole)]
  have hexp : logDeriv (fun z : ℂ => Complex.exp (b * z)) s = b := by
    have hd : HasDerivAt (fun z : ℂ => Complex.exp (b * z))
        (Complex.exp (b * s) * b) s := by
      simpa using ((hasDerivAt_id s).const_mul b).cexp
    rw [logDeriv_apply, hd.deriv]
    exact mul_div_cancel_left₀ b (Complex.exp_ne_zero _)
  rw [hexp]
  unfold DirichletCharacter.gammaFactor
  split_ifs with heven
  · rw [Zeta23.WeilEF.logDeriv_Gammaℝ hpos]
    simp only [add_zero]
    dsimp [b]
    push_cast
    ring
  · have hc := logDeriv_comp (x := s) (f := Complex.Gammaℝ)
      (g := fun z : ℂ => z + 1)
      (Zeta23.WeilEF.differentiableAt_Gammaℝ (by simp only [add_re, one_re]; linarith))
      (by fun_prop)
    simp only [Function.comp_def, deriv_add_const, deriv_id'', mul_one] at hc
    rw [hc, Zeta23.WeilEF.logDeriv_Gammaℝ (by simp only [add_re, one_re]; linarith)]
    dsimp [b]
    push_cast
    ring
theorem gamma_growth_bounds :
    (∀ {z : ℂ}, 0 < z.re → ‖Complex.Gamma z‖ ≤ Real.Gamma z.re) ∧
    (∀ {u : ℝ}, 1 / 4 ≤ u → Real.Gamma u ≤ Real.Gamma (1 / 4) ∨
      Real.Gamma u < Real.exp ((u + 1) * Real.log (u + 1))) ∧
    (∀ {u : ℝ}, 1 / 4 ≤ u → Real.Gamma u ≤
      max (Real.Gamma (1 / 4)) (Nat.factorial (⌈u⌉₊ - 1) : ℝ)) :=
  ⟨fun hz => norm_Gamma_le hz, fun hu => Gamma_le_exp_bound hu,
    fun hu => Gamma_le_max_factorial hu⟩


end D5.S3.CharacterSums.DirichletTrivialZeros
