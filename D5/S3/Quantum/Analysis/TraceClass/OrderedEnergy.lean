/- GID: D5/S3/Quantum/Analysis/TraceClass/OrderedEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/OrderedEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Noncommuting ordered logarithmic increments and a global positive extended energy decomposition. -/

import D5.S3.Quantum.Analysis.TraceClass.SpectralEnergy

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal
open Filter Topology
namespace QuantumLogEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem positive_shift {a : ℝ} (ha : 0 < a) {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    IsStrictlyPositive (T + algebraMap ℝ (H →L[ℂ] H) a) :=
  IsStrictlyPositive.nonneg_add hT (isStrictlyPositive_algebraMap ha)

/-- A single-operator functional-calculus identity on an actually positive spectrum.
No product law for noncommuting logarithms occurs. -/
theorem log_add_sub_log_eq_log_inverse {A : H →L[ℂ] H} (hA : IsStrictlyPositive A)
    {c : ℝ} (hc : 0 ≤ c) :
    CFC.log (A + algebraMap ℝ (H →L[ℂ] H) c) - CFC.log A =
      CFC.log (1 + c • Ring.inverse A) := by
  have hx : ∀ x ∈ spectrum ℝ A, 0 < x := fun x hx => hA.spectrum_pos hx
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (spectrum ℝ A) :=
    continuousOn_id.inv₀ (fun x hx' => (hx x hx').ne')
  have hlog : ContinuousOn Real.log (spectrum ℝ A) :=
    continuousOn_id.log (fun x hx' => (hx x hx').ne')
  have hplus : ContinuousOn Real.log ((fun x : ℝ => x + c) '' spectrum ℝ A) := by
    apply continuousOn_id.log
    rintro y ⟨x, hx', rfl⟩
    exact (add_pos_of_pos_of_nonneg (hx x hx') hc).ne'
  have hratio : ContinuousOn Real.log ((fun x : ℝ => 1 + c * x⁻¹) '' spectrum ℝ A) := by
    apply continuousOn_id.log
    rintro y ⟨x, hx', rfl⟩
    exact (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hc (inv_nonneg.mpr (hx x hx').le))).ne'
  have hadd : cfc (fun x : ℝ => x + c) A = A + algebraMap ℝ (H →L[ℂ] H) c := by
    calc
      cfc (fun x : ℝ => x + c) A = cfc id A + algebraMap ℝ (H →L[ℂ] H) c :=
        cfc_add_const c id A continuousOn_id hA.isSelfAdjoint
      _ = A + algebraMap ℝ (H →L[ℂ] H) c := by
        rw [cfc_id ℝ A hA.isSelfAdjoint]
  have hinside : cfc (fun x : ℝ => 1 + c * x⁻¹) A = 1 + c • Ring.inverse A := by
    rw [cfc_const_add 1 (fun x : ℝ => c * x⁻¹) A (continuousOn_const.mul hinv) hA.isSelfAdjoint,
      map_one, cfc_const_mul c _ A hinv, cfc_ringInverse_id A hA.isUnit hA.isSelfAdjoint]
  rw [← hadd, ← hinside, CFC.log, CFC.log, CFC.log,
    ← cfc_comp' Real.log (fun x : ℝ => x + c) A hplus
      (continuousOn_id.add continuousOn_const) hA.isSelfAdjoint,
    ← cfc_comp' Real.log (fun x : ℝ => 1 + c * x⁻¹) A hratio
      (continuousOn_const.add (continuousOn_const.mul hinv)) hA.isSelfAdjoint,
    ← cfc_sub (fun x : ℝ => Real.log (x+c)) Real.log A (hplus.comp (continuousOn_id.add continuousOn_const) (by intro x h; exact ⟨x,h,rfl⟩)) hlog]
  apply cfc_congr
  intro x hx'
  dsimp only
  rw [← Real.log_div (add_pos_of_pos_of_nonneg (hx x hx') hc).ne' (hx x hx').ne']
  congr 1
  rw [add_div, div_self (hx x hx').ne', div_eq_mul_inv]

/-- The bounded nonnegative logarithmic difference for ordered references. -/
def orderedIncrement (e : ℝ) (P Q : H →L[ℂ] H) : H →L[ℂ] H :=
  CFC.log (Q + algebraMap ℝ (H →L[ℂ] H) e) -
    CFC.log (P + algebraMap ℝ (H →L[ℂ] H) e)

theorem orderedIncrement_nonneg {e : ℝ} (he : 0 < e)
    {P Q : H →L[ℂ] H} (hP : 0 ≤ P) (hPQ : P ≤ Q) :
    0 ≤ orderedIncrement e P Q := by
  exact sub_nonneg.mpr (CFC.log_le_log (add_le_add hPQ le_rfl) (positive_shift he hP))

/-- Ordered increments increase as a positive epsilon decreases, even when P and Q do not commute. -/
theorem orderedIncrement_parameter_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {P Q : H →L[ℂ] H} (hP : 0 ≤ P) (hPQ : P ≤ Q) :
    orderedIncrement b P Q ≤ orderedIncrement a P Q := by
  let A := P + algebraMap ℝ (H →L[ℂ] H) a
  let B := Q + algebraMap ℝ (H →L[ℂ] H) a
  have hA : IsStrictlyPositive A := positive_shift ha hP
  have hB : IsStrictlyPositive B := positive_shift ha (hP.trans hPQ)
  have hc : 0 ≤ b - a := sub_nonneg.mpr hab
  have hinv := CStarAlgebra.ringInverse_le_ringInverse (show A ≤ B from add_le_add hPQ le_rfl) hA
  have hpos : IsStrictlyPositive (1 + (b-a) • Ring.inverse B) := by
    have hIB : 0 ≤ Ring.inverse B := by
      rw [← cfc_ringInverse_id B hB.isUnit hB.isSelfAdjoint (R := ℝ)]
      exact cfc_nonneg (fun x hx => inv_nonneg.mpr (hB.spectrum_pos hx).le)
    exact IsStrictlyPositive.add_nonneg isStrictlyPositive_one (smul_nonneg hc hIB)
  have hlog := CFC.log_le_log
    (show 1 + (b-a) • Ring.inverse B ≤ 1 + (b-a) • Ring.inverse A from
      add_le_add le_rfl (smul_le_smul_of_nonneg_left hinv hc)) hpos
  rw [← log_add_sub_log_eq_log_inverse hB hc, ← log_add_sub_log_eq_log_inverse hA hc] at hlog
  have hshift (T : H →L[ℂ] H) :
      (T + algebraMap ℝ (H →L[ℂ] H) a) + algebraMap ℝ (H →L[ℂ] H) (b-a) =
        T + algebraMap ℝ (H →L[ℂ] H) b := by
    rw [add_assoc, ← map_add, show a + (b-a) = b by ring]
  dsimp [A, B] at hlog
  rw [hshift, hshift] at hlog
  dsimp [orderedIncrement]
  apply sub_le_sub_iff.mpr
  simpa only [add_comm] using sub_le_sub_iff.mp hlog

/-- The nonnegative extended trace-pairing supremum of the actual ordered increments. -/
def orderedEnergy (P Q : Reference H) (rho : TraceClass H) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal
    (TraceClass.tracePairing (orderedIncrement ((n : ℝ) + 1)⁻¹ P.1.1 Q.1.1) rho).re

private theorem monotone_orderedEnergy_grid (P Q : Reference H) (hPQ : P.1.1 ≤ Q.1.1)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    Monotone (fun n : ℕ => ENNReal.ofReal
      (TraceClass.tracePairing (orderedIncrement ((n : ℝ) + 1)⁻¹ P.1.1 Q.1.1) rho).re) := by
  intro m n hmn
  apply ENNReal.ofReal_le_ofReal
  apply tracePairing_mono _ rho hrho
  exact orderedIncrement_parameter_antitone (by positivity)
    (inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)) P.2.1 hPQ

/-- The ordered-energy functional is lower semicontinuous in the actual first-slot trace norm. -/
theorem lowerSemicontinuous_orderedEnergy (P Q : Reference H) :
    LowerSemicontinuous (orderedEnergy P Q) := by
  apply lowerSemicontinuous_iSup
  intro n
  exact (ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp
    (TraceClass.tracePairing (orderedIncrement ((n : ℝ) + 1)⁻¹ P.1.1 Q.1.1)).continuous)).lowerSemicontinuous

/-- The global positive decomposition holds in ENNReal, including infinite energies.
No infinite value is subtracted, and no commutativity hypothesis is imposed. -/
theorem spectralEnergy_eq_orderedEnergy_add (P Q : Reference H) (hPQ : P.1.1 ≤ Q.1.1)
    (rho : TraceClass H) (hrho : 0 ≤ rho.1) :
    spectralEnergy P rho = orderedEnergy P Q rho + spectralEnergy Q rho := by
  have hop (e : ℝ) : logRegularization e P.1.1 =
      orderedIncrement e P.1.1 Q.1.1 + logRegularization e Q.1.1 := by
    unfold logRegularization orderedIncrement
    abel
  have hreal (e : ℝ) : regularizedEnergy e P.1.1 rho =
      (TraceClass.tracePairing (orderedIncrement e P.1.1 Q.1.1) rho).re +
        regularizedEnergy e Q.1.1 rho := by
    unfold regularizedEnergy
    rw [hop]
    change (TraceClass.tracePairingContinuousLinearMap (_ + _) rho).re = _
    rw [map_add, ContinuousLinearMap.add_apply, Complex.add_re]
    rfl
  rw [spectralEnergy_eq_regularizedSupremum P rho hrho,
    spectralEnergy_eq_regularizedSupremum Q rho hrho]
  unfold regularizedSupremum orderedEnergy
  rw [ENNReal.iSup_add_iSup_of_monotone (monotone_orderedEnergy_grid P Q hPQ rho hrho)
    (fun m n h => ENNReal.ofReal_le_ofReal (monotone_regularizedEnergy Q rho hrho h))]
  congr 1
  funext n
  rw [hreal, ENNReal.ofReal_add
    (tracePairing_nonneg (orderedIncrement_nonneg (by positivity) P.2.1 hPQ) rho hrho)
    (regularizedEnergy_nonneg (by positivity) Q rho hrho)]

/-- Equal references have exactly zero ordered energy, also on their common singular fibers. -/
theorem orderedEnergy_self (P : Reference H) (rho : TraceClass H) : orderedEnergy P P rho = 0 := by
  unfold orderedEnergy orderedIncrement
  simp only [sub_self]
  change (⨆ _ : ℕ, ENNReal.ofReal ((TraceClass.tracePairingContinuousLinearMap 0) rho).re) = 0
  simp

#print axioms log_add_sub_log_eq_log_inverse
#print axioms orderedIncrement_parameter_antitone
#print axioms spectralEnergy_eq_orderedEnergy_add
end QuantumLogEnergy
