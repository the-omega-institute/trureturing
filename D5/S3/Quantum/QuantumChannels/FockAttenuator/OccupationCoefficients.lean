/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/OccupationCoefficients
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/OccupationCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual beam-splitter occupation coordinates for arbitrary completed Fock inputs. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedKernel

/-! Number conservation is extended from the frozen occupation expansion to
every completed input through continuous linear coordinate maps. -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter

private theorem tensor_number (a : Fock) (n : ℕ) :
    tensor a (lp.single 2 n (1 : ℂ)) = (lp.single 2 n a : TwoMode) := by
  apply lp.ext
  apply funext
  intro j
  by_cases h : j = n <;> simp [tensor, lp.single_apply, h, Pi.single_apply]

theorem fock_pair_coordinate (m n j i : ℕ) :
    fockPair m n j i = if j = n ∧ i = m then 1 else 0 := by
  simp only [fockPair, tensor_number, lp.single_apply, Pi.single_apply]
  by_cases hj : j = n <;> by_cases hi : i = m <;> simp [hj, hi]

/-- The existing finite beam-splitter expansion vanishes away from the
conserved total occupation. This helper is used to extend the coordinate law. -/
private theorem fock_expansion_coordinate_zero (t r : ℝ) (m n j i : ℕ)
    (hN : i+j ≠ m+n) : fockExpansion t r m n j i = 0 := by
  classical
  simp only [fockExpansion, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  have hab : ¬ (j = m-a+(n-b) ∧ i = a+b) := by
    rintro ⟨hj, hi⟩
    apply hN
    have ha : (a : ℕ) ≤ m := Nat.le_of_lt_succ a.isLt
    have hb : (b : ℕ) ≤ n := Nat.le_of_lt_succ b.isLt
    omega
  rw [fock_pair_coordinate, if_neg hab, mul_zero]

private def outputCoordinate (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (n j i : ℕ) : Fock →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i).comp
    ((lp.evalCLM ℂ (fun _ : ℕ => Fock) 2 j).comp
      ((beamSplitter η hη).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => Fock) 2 n)))

private theorem output_coordinate_apply (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (n j i : ℕ) (a : Fock) :
    outputCoordinate η hη n j i a =
      beamSplitter η hη (tensor a (lp.single 2 n (1 : ℂ))) j i := by
  rw [tensor_number]
  rfl

private theorem output_coordinate_basis (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (n j i m : ℕ) :
    outputCoordinate η hη n j i (lp.single 2 m (1 : ℂ)) =
      fockExpansion (Real.sqrt η) (Real.sqrt (1-η)) m n j i := by
  rw [output_coordinate_apply]
  change beamUnitary _ _ _ (fockPair m n) j i = _
  rw [beamUnitary_fock]

/-- Below the environment occupation the actual coefficient vanishes for
every completed input, including inputs with arbitrary infinite support. -/
theorem occupation_coefficient_below_environment
    (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (n j i : ℕ)
    (hN : i+j < n) (a : Fock) :
    beamSplitter η hη (tensor a (lp.single 2 n (1 : ℂ))) j i = 0 := by
  have hmap : outputCoordinate η hη n j i = 0 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro m
    apply ContinuousLinearMap.ext
    intro c
    have hc : (lp.single 2 m c : Fock) = c • lp.single 2 m (1 : ℂ) := by
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : ℕ => ℂ) 2 m c (1 : ℂ))
    change outputCoordinate η hη n j i (lp.single 2 m c) = 0
    rw [hc, map_smul, output_coordinate_basis,
      fock_expansion_coordinate_zero _ _ _ _ _ _ (by omega), smul_zero]
  rw [← output_coordinate_apply, hmap, ContinuousLinearMap.zero_apply]

/-- Every actual completed coefficient is the unique input coefficient of
the conserved total occupation times its frozen occupation transition
amplitude. This identity is proved on continuous maps, rather than by
assuming that an arbitrary input has finite support. -/
theorem occupation_coefficient_of_total
    (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (n j i : ℕ)
    (hN : n ≤ i+j) (a : Fock) :
    beamSplitter η hη (tensor a (lp.single 2 n (1 : ℂ))) j i =
      a (i+j-n) *
        fockExpansion (Real.sqrt η) (Real.sqrt (1-η)) (i+j-n) n j i := by
  let d := fockExpansion (Real.sqrt η) (Real.sqrt (1-η)) (i+j-n) n j i
  let L : Fock →L[ℂ] ℂ := d • lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 (i+j-n)
  have hmap : outputCoordinate η hη n j i = L := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro m
    apply ContinuousLinearMap.ext
    intro c
    have hc : (lp.single 2 m c : Fock) = c • lp.single 2 m (1 : ℂ) := by
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : ℕ => ℂ) 2 m c (1 : ℂ))
    change outputCoordinate η hη n j i (lp.single 2 m c) = L (lp.single 2 m c)
    rw [hc, map_smul, map_smul, output_coordinate_basis]
    by_cases hm : m = i+j-n
    · subst m
      change c * d = c * (d * (lp.single 2 (i+j-n) (1 : ℂ) : Fock) (i+j-n))
      rw [lp.single_apply_self, mul_one]
    · rw [fock_expansion_coordinate_zero _ _ _ _ _ _ (by omega)]
      change c * 0 = c * (d * (lp.single 2 m (1 : ℂ) : Fock) (i+j-n))
      simp only [lp.single_apply_ne _ _ _ (Ne.symm hm), mul_zero]
  rw [← output_coordinate_apply, hmap]
  change d * a (i+j-n) = a (i+j-n) * d
  exact mul_comm _ _

#print axioms occupation_coefficient_below_environment
#print axioms occupation_coefficient_of_total

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
