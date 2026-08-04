/- GID: D5/S3/Midline/ZetaHeatTraceBridge
   generality: I
   mirror-B: D5/B/S3/Midline/ZetaHeatTraceBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive the labeled-zeta Hilbert criterion from the universal heat-abscissa theorem. -/

import D5.S3.Midline.UniversalHeatTrace
import D5.S3.Weil.SpectralHilbert

namespace D5.S3.Midline.ZetaHeatTraceBridge

open D5.S1.Digit
open D5.S3.Weil.Convention
open D5.S3.Weil.SpectralHilbert
open D5.S3.Midline.UniversalHeatTrace

/-- The logarithmic length attached to a prime-axis address. -/
noncomputable def primeAxisLogLength (a : PrimeAxisTable) : ℝ :=
  Real.log (((primeAxisEncoding a : ℕ+) : ℕ) : ℝ)

private noncomputable def addressEquivNat : ℕ ≃ PrimeAxisTable :=
  (primeAxisEncoding.trans Equiv.pnatEquivNat).symm

private theorem addressEquivNat_encode (n : ℕ) :
    ((primeAxisEncoding (addressEquivNat n) : ℕ+) : ℕ) = n + 1 := by
  have h := Equiv.apply_symm_apply (primeAxisEncoding.trans Equiv.pnatEquivNat) n
  change (primeAxisEncoding (addressEquivNat n)).natPred = n at h
  calc
    ((primeAxisEncoding (addressEquivNat n) : ℕ+) : ℕ) =
        (primeAxisEncoding (addressEquivNat n)).natPred + 1 :=
      (PNat.natPred_add_one _).symm
    _ = n + 1 := by rw [h]

noncomputable local instance : Zero PrimeAxisTable := ⟨addressEquivNat 0⟩
noncomputable local instance : Countable PrimeAxisTable :=
  Countable.of_equiv ℕ addressEquivNat

/-- The universal heat coefficient at logarithmic length is the labeled-zeta coefficient. -/
theorem coefficient_eq (s : ℂ) (a : PrimeAxisTable) :
    heatCoefficient primeAxisLogLength s a = labeledZetaCoefficient s a := by
  let n : ℕ := ((primeAxisEncoding a : ℕ+) : ℕ)
  have hn : 0 < n := (primeAxisEncoding a).pos
  rw [heatCoefficient, primeAxisLogLength, labeledZetaCoefficient]
  change Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) = 1 / (n : ℂ) ^ s
  rw [Complex.cpow_def, if_neg (by exact_mod_cast hn.ne')]
  rw [Complex.ofReal_log (by positivity : 0 ≤ (n : ℝ))]
  rw [div_eq_mul_inv, one_mul, ← Complex.exp_neg]
  congr 1
  simp [n]
  ring

private theorem heat_term_eq (σ : ℝ) (n : ℕ) :
    Real.exp (-σ * primeAxisLogLength (addressEquivNat n)) =
      1 / ((n + 1 : ℕ) : ℝ) ^ σ := by
  rw [primeAxisLogLength, addressEquivNat_encode,
    Real.rpow_def_of_pos (by positivity)]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  ring

theorem primeAxisLogLength_zero : primeAxisLogLength (0 : PrimeAxisTable) = 0 := by
  rw [primeAxisLogLength]
  change Real.log (((primeAxisEncoding (addressEquivNat 0) : ℕ+) : ℕ) : ℝ) = 0
  rw [addressEquivNat_encode]
  norm_num

theorem primeAxisLogLength_nonneg (a : PrimeAxisTable) : 0 ≤ primeAxisLogLength a := by
  apply Real.log_nonneg
  exact_mod_cast (primeAxisEncoding a).pos

theorem primeAxisLogLength_nonzero : ∃ a, primeAxisLogLength a ≠ 0 := by
  refine ⟨addressEquivNat 1, ?_⟩
  rw [primeAxisLogLength, addressEquivNat_encode]
  exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num)

/-- The logarithmic heat series converges strictly to the right of one. -/
theorem primeAxisLogLength_summable_of_one_lt (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun a => Real.exp (-σ * primeAxisLogLength a)) := by
  rw [← addressEquivNat.summable_iff]
  refine (summable_congr (heat_term_eq σ)).mpr ?_
  have habs (n : ℕ) : |(n : ℝ) + 1| = ((n + 1 : ℕ) : ℝ) := by
    rw [abs_of_pos (by positivity), Nat.cast_add, Nat.cast_one]
  exact (summable_congr (fun n => by rw [habs n])).mp
    ((Real.summable_one_div_nat_add_rpow 1 σ).2 hσ)

/-- The logarithmic heat series diverges strictly to the left of one. -/
theorem primeAxisLogLength_not_summable_of_lt_one (σ : ℝ) (hσ : σ < 1) :
    ¬Summable (fun a => Real.exp (-σ * primeAxisLogLength a)) := by
  rw [← addressEquivNat.summable_iff]
  intro h
  have hp : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ σ) :=
    (summable_congr (heat_term_eq σ)).mp h
  have habs (n : ℕ) : |(n : ℝ) + 1| = ((n + 1 : ℕ) : ℝ) := by
    rw [abs_of_pos (by positivity), Nat.cast_add, Nat.cast_one]
  exact (Real.summable_one_div_nat_add_rpow 1 σ).not.mpr (by linarith)
    (by simpa only [habs] using hp)

/-- At one the logarithmic heat series is the shifted harmonic series and diverges. -/
theorem primeAxisLogLength_not_summable_at_one :
    ¬Summable (fun a => Real.exp (-(1 : ℝ) * primeAxisLogLength a)) := by
  rw [← addressEquivNat.summable_iff]
  intro h
  have hp : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (1 : ℝ)) :=
    (summable_congr (heat_term_eq 1)).mp h
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    simpa only [Real.rpow_one] using hp
  exact Real.not_summable_one_div_natCast (summable_nat_add_iff 1 |>.mp hs)

/-- Prime-axis logarithmic length has boundary-divergent heat abscissa one. -/
theorem primeAxisLogLength_boundary_divergent :
    BoundaryDivergentAbscissa primeAxisLogLength 1 := by
  exact ⟨⟨primeAxisLogLength_summable_of_one_lt,
      primeAxisLogLength_not_summable_of_lt_one⟩,
    primeAxisLogLength_not_summable_at_one⟩

/-- The labeled-zeta Hilbert criterion derived from the universal strict theorem,
the coefficient identification, and the prime-axis boundary-divergent abscissa. -/
theorem zeta_mem_iff_from_universal_heat_trace (s : ℂ) :
    Memℓp (labeledZetaCoefficient s) 2 ↔ criticalAbscissa < s.re := by
  have h := (universal_heat_trace_midline_of_boundary_divergent primeAxisLogLength 1
    primeAxisLogLength_zero primeAxisLogLength_nonneg primeAxisLogLength_nonzero
    (by norm_num) primeAxisLogLength_boundary_divergent).1 s
  rw [show heatCoefficient primeAxisLogLength s = labeledZetaCoefficient s from
    funext (coefficient_eq s)] at h
  simpa only [criticalAbscissa] using h

end D5.S3.Midline.ZetaHeatTraceBridge
