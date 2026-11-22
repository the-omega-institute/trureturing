/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Replay
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedActualSeedBounds.existsUnique_zero_closedBall; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Bounds.row_bounds
   digest: The order-73 integer replay closes the numerical premises of the root certificate. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73Bounds
import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedFiniteBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

open scoped BigOperators

def rawY : Matrix (Fin m) (Fin m) ChirpedFinite.Dyadic := fun i j => yEntry i.val j.val
def A : Matrix (Fin m) (Fin m) ℤ := fun i j => a i.val j.val
noncomputable def center (i : Fin m) : ℝ := decodeDyadic (centerEntry i.val)

theorem exponent_eq : ChirpedReplay.dyadicExponent rawY = commonExponent :=
  dyadicExponent_eq rawY commonExponent (fun i j => (normalizeChecked i.val i.isLt j).2)
    exponentWitnessRow exponentWitnessCol exponent_attained

theorem D_eq : ChirpedReplay.dyadicDenominator rawY = D := by
  rw [ChirpedReplay.dyadicDenominator, exponent_eq] <;> rfl

theorem A_eq : A = ChirpedReplay.dyadicNumerators rawY := by
  funext i j
  simp only [ChirpedReplay.dyadicNumerators, exponent_eq]
  exact (normalizeChecked i.val i.isLt j).1

theorem preconditioner_exact (i j : Fin m) :
    ChirpedReplay.scaledMatrix A D i j = decodeDyadic (rawY i j) := by
  rw [A_eq, ← D_eq, ChirpedReplay.scaledMatrix_dyadic] <;> rfl

theorem radius_exact : ChirpedReplay.radius = (2 : ℝ) ^ radiusExponent := by
  norm_num [ChirpedReplay.radius, ChirpedReplay.radiusDen, radiusExponent]

theorem rootAt_error (j : Fin n) :
    ‖ChirpedReplay.IntComplex.decode scale (rootAt j.val) - exactRoot n j.val‖ ≤
      45 / (scale : ℝ) := by
  rw [root_spec j.val j.isLt]
  exact ChirpedFinite.root_error j

theorem phaseSlope_error (j : Fin m) :
    ‖ChirpedReplay.IntComplex.decode scale (phaseAt j.val) -
      ChirpedReplay.cayley (center j) (signEntry j.val)‖ ≤ 2 / (scale : ℝ) ∧
    ‖ChirpedReplay.IntComplex.decode scale (slopeAt j.val) -
      ChirpedReplay.cayleySlope (center j) (signEntry j.val)‖ ≤ 2 / (scale : ℝ) := by
  have h := ChirpedFinite.cayley_error (centerEntry j.val) (signEntry j.val)
  rw [← cayley_spec j.val j.isLt] at h
  exact h

def pick (i : Fin m) : Constraint := constraint (equation i.val).1
def imag (i : Fin m) : Bool := (equation i.val).2

def rows : ChirpedReplay.CorrelationRows (Fin m) n Gaussian :=
  selectRows inverseMultiplier pick seedAt seedSlopeAt

noncomputable def exactPhase (x : Fin m → ℝ) (j : ℕ) : ℂ :=
  if h : j < m then ChirpedReplay.cayley (x ⟨j, h⟩) (signEntry j) else 0

noncomputable def exactSlope (x : Fin m → ℝ) (j : ℕ) : ℂ :=
  if h : j < m then ChirpedReplay.cayleySlope (x ⟨j, h⟩) (signEntry j) else 0

noncomputable def exactRows (x : Fin m → ℝ) : ChirpedReplay.CorrelationRows (Fin m) n ℂ :=
  selectRows inverseMultiplier pick
    (fun s d => exactSeedValue n (exactPhase x) d (seed s))
    (fun s d j => exactSeedSlope n (exactSlope x) d j (seed s))

noncomputable def F (x : Fin m → ℝ) : Fin m → ℝ := (exactRows x).exactResidual imag

theorem residual_eq : rows.residual imag = fun i : Fin m => fAt i.val := by
  funext i
  exact (selectRows_residual inverseMultiplier pick seedAt seedSlopeAt imag i).trans
    (f_spec i).symm

theorem jacobian_eq : rows.jacobian imag = fun i j : Fin m => jAt i.val j.val := by
  funext i j
  exact (selectRows_jacobian inverseMultiplier pick seedAt seedSlopeAt imag i j).trans
    (j_spec i j).symm

theorem denominator_eq :
    ChirpedReplay.denominator (ChirpedReplay.dyadicDenominator rawY) ChirpedReplay.scale = H := by
  rw [D_eq] <;> rfl

/-- The integer checks supply all three row bounds and both strict inequalities.
    The remaining arguments concern the exact, explicitly defined system. -/
theorem existsUnique_zero
    (DF : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))
    (hseed : ChirpedReplay.CorrelationRows.SeedBounds rows (exactRows center))
    (hslope : LinearMap.toMatrix' (DF center).toLinearMap = (exactRows center).exactJacobian imag)
    (hder : ∀ x ∈ Metric.closedBall center ChirpedReplay.radius, HasFDerivAt F (DF x) x)
    (hdrift : ∀ x ∈ Metric.closedBall center ChirpedReplay.radius, ‖DF x - DF center‖ ≤ 16 * ‖x - center‖) :
    ∃! x, x ∈ Metric.closedBall center ChirpedReplay.radius ∧ F x = 0 := by
  obtain ⟨hE, hdelta, hM⟩ := bounds_nonnegative
  refine ChirpedReplay.existsUnique_zero_of_seed_replay .n73 rows (exactRows center) hseed imag
    rawY E delta M hE hdelta hM F DF center rfl hslope ?_ ?_ ?_ ?_ ?_ hder hdrift
  · intro i
    change ChirpedReplay.stepRow ChirpedReplay.scale n (ChirpedReplay.dyadicNumerators rawY)
      (rows.residual imag) (i : Fin m) ≤ E
    rw [← A_eq, residual_eq]
    exact (stepRow_fin n m a fAt i).le.trans (row_bounds i).1
  · intro i
    change ChirpedReplay.defectRow (ChirpedReplay.dyadicDenominator rawY) ChirpedReplay.scale n
      (ChirpedReplay.dyadicNumerators rawY) (rows.jacobian imag) (i : Fin m) ≤ delta
    rw [D_eq, ← A_eq, jacobian_eq]
    exact (defectRow_fin D n m a jAt i).le.trans (row_bounds i).2.2
  · intro i
    change ChirpedReplay.rowWeight (ChirpedReplay.dyadicNumerators rawY) (i : Fin m) ≤ M
    rw [← A_eq]
    exact (rowWeight_fin m a i).le.trans (row_bounds i).2.1
  · change ChirpedReplay.contractionNumerator delta M <
      ChirpedReplay.denominator (ChirpedReplay.dyadicDenominator rawY) ChirpedReplay.scale
    rw [denominator_eq]
    exact strict_contraction
  · change E * ChirpedReplay.radiusDen + ChirpedReplay.contractionNumerator delta M <
      ChirpedReplay.denominator (ChirpedReplay.dyadicDenominator rawY) ChirpedReplay.scale
    rw [denominator_eq]
    exact strict_inclusion

end Chirped73
