/- GID: D5/S3/Weil/EulerProduct
   generality: I
   mirror-B: D5/B/S3/Weil/EulerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Connect finite Euler windows and single-address weights to classical zeta. -/

import D5.S3.Weil.PrimePoleTerms
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace D5.S3.Weil.EulerProduct

open Filter
open D5.S3.Weil.Convention
open scoped BigOperators Topology

/-- The single-address ledger reading, indexed by its decoded natural value. -/
noncomputable def singleAddressReading (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/-- Prime powers carry `log p`, while values with more than one prime address carry zero. -/
theorem single_address_reading_spec :
    (∀ p k, p.Prime → k ≠ 0 →
      singleAddressReading (p ^ k) = Real.log p) ∧
    (∀ n, ¬IsPrimePow n → singleAddressReading n = 0) := by
  constructor
  · intro p k hp hk
    rw [singleAddressReading, ArithmeticFunction.vonMangoldt_apply_pow hk,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  · intro n hn
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn

/-- The Dirichlet heat trace of the single-address reading. -/
noncomputable def singleAddressHeatTrace (s : ℂ) : ℂ :=
  LSeries (fun n => (singleAddressReading n : ℂ)) s

/-- In the convergence half-plane, the single-address trace is `-zeta'/zeta`. -/
theorem single_address_heat_trace_eq_log_derivative {s : ℂ} (hs : 1 < s.re) :
    singleAddressHeatTrace s =
      -deriv classicalZeta s / classicalZeta s := by
  simpa [singleAddressHeatTrace, singleAddressReading, classicalZeta] using
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- One local denominator in a finite Euler product. -/
noncomputable def finiteEulerDenominator (p : ℕ) (s : ℂ) : ℂ :=
  1 - (p : ℂ) ^ (-s)

/-- The local singular locus is the imaginary lattice with period `2 * pi / log p`. -/
theorem finite_euler_denominator_eq_zero_iff {p : ℕ} (hp : p.Prime) (s : ℂ) :
    finiteEulerDenominator p s = 0 ↔
      ∃ k : ℤ,
        s = (k : ℂ) * (2 * Real.pi * Complex.I) / (Real.log p : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlog : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  constructor
  · intro h
    have hpow : (p : ℂ) ^ (-s) = 1 := by
      simpa [finiteEulerDenominator] using (sub_eq_zero.mp h).symm
    rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log] at hpow
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hpow
    refine ⟨-k, ?_⟩
    apply (eq_div_iff hlog).2
    calc
      s * (Real.log p : ℂ) = -((Real.log p : ℂ) * -s) := by ring
      _ = -((k : ℂ) * (2 * Real.pi * Complex.I)) := by rw [hk]
      _ = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by simp
  · rintro ⟨k, rfl⟩
    apply sub_eq_zero.mpr
    symm
    rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨-k, ?_⟩
    field_simp
    simp

/-- The finite Euler product, totalized by Lean's field inverse at singular points. -/
noncomputable def finiteEulerProduct (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ S, (finiteEulerDenominator p s)⁻¹

/-- A finite Euler product is regular when none of its local denominators vanish. -/
def FiniteEulerRegular (S : Finset ℕ) (s : ℂ) : Prop :=
  ∀ p ∈ S, finiteEulerDenominator p s ≠ 0

/-- Finite Euler products are zero-free on their regular locus, with exactly the expected
imaginary denominator-zero lattice. -/
theorem finite_euler_zero_free_and_pole_locus
    (S : Finset ℕ) (hPrime : ∀ p ∈ S, p.Prime) (s : ℂ) :
    (finiteEulerProduct S s ≠ 0 ↔ FiniteEulerRegular S s) ∧
    (¬ FiniteEulerRegular S s ↔
      ∃ p ∈ S, ∃ k : ℤ,
        s = (k : ℂ) * (2 * Real.pi * Complex.I) / (Real.log p : ℂ)) := by
  classical
  constructor
  · simp only [finiteEulerProduct, FiniteEulerRegular, Finset.prod_ne_zero_iff,
      ne_eq, inv_eq_zero]
  · constructor
    · intro h
      simp only [FiniteEulerRegular] at h
      push Not at h
      obtain ⟨p, hpS, hzero⟩ := h
      obtain ⟨k, hk⟩ :=
        (finite_euler_denominator_eq_zero_iff (hPrime p hpS) s).mp hzero
      exact ⟨p, hpS, k, hk⟩
    · rintro ⟨p, hpS, k, hk⟩ hRegular
      exact hRegular p hpS
        ((finite_euler_denominator_eq_zero_iff (hPrime p hpS) s).mpr ⟨k, hk⟩)

/-- The residue of the repository's classical zeta reading at one is exactly one. -/
theorem riemann_zeta_residue_one :
    Tendsto (fun s : ℂ => (s - 1) * classicalZeta s) (𝓝[≠] 1) (𝓝 1) := by
  simpa [classicalZeta] using riemannZeta_residue_one

/-- The natural-number Dirichlet series equals the repository's zeta reading in its
absolute-convergence half-plane. -/
theorem riemann_zeta_dirichlet_sum (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, (n : ℂ) ^ (-s)) = classicalZeta s := by
  simpa [riemannZetaSummandHom, classicalZeta] using tsum_riemannZetaSummand hs

/-- The prime-indexed Euler product equals the same zeta reading in the
absolute-convergence half-plane. -/
theorem riemann_zeta_euler_product (s : ℂ) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) = classicalZeta s := by
  simpa [classicalZeta] using riemannZeta_eulerProduct_tprod hs

end D5.S3.Weil.EulerProduct
