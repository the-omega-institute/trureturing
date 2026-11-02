/- GID: D5/S3/Quantum/Measurements/LudersEntropySaturationSIC
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/LudersEntropySaturationSIC
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Entropy saturation of a Lüders MIC channel forces the source SIC structure. -/

import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import D5.S3.Quantum.Divergence.SpectralCeilingRelativeEntropy
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner

/-! DeBrota--Stacey's saturation implication for Lüders MIC channels. -/

open scoped BigOperators ComplexOrder Matrix MatrixOrder
open MeasureTheory TopologicalSpace

noncomputable section

namespace D5.S3.Quantum.Measurements.LudersEntropySaturationSIC

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

set_option autoImplicit false
set_option relaxedAutoImplicit false

def IsMIC (d : ℕ)
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ i, (e i).PosSemidef) ∧
    (∑ i, e i = 1) ∧ LinearIndependent ℂ e

def IsSIC (d : ℕ)
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  IsMIC d e ∧
    (∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p) ∧
    ∃ a b : ℂ, ∀ i j, (e i * e j).trace = if i = j then a else b

def ludersChannel {d : ℕ}
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (x : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, CFC.sqrt (e i) * x * CFC.sqrt (e i)

private def baseProjector {d : ℕ} [NeZero d] : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single 0 0 1

private def inputProjector {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  u.1 * baseProjector * u.1ᴴ

private noncomputable def ludersState {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (u : Matrix.unitaryGroup (Fin d) ℂ) :
    DensityState (Fin d) := by
  classical
  by_cases he : IsMIC d e
  · refine ⟨ludersChannel e (inputProjector u), ?_, ?_⟩
    · sorry
    · sorry
  · refine ⟨baseProjector, ?_, ?_⟩
    · sorry
    · sorry

private noncomputable def sigmaState {d : ℕ} [NeZero d]
    (u : Matrix.unitaryGroup (Fin d) ℂ) : DensityState (Fin d) := by
  sorry

noncomputable def typicalEntropy (d : ℕ) [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∫ u : Matrix.unitaryGroup (Fin d) ℂ,
    vonNeumannEntropy (ludersState e u) ∂
      (Measure.haarMeasure
        (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))

private theorem luders_state_density {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (u : Matrix.unitaryGroup (Fin d) ℂ) (he : IsMIC d e) :
    (ludersState e u).1 = ludersChannel e (inputProjector u) := by
  sorry

private theorem entropy_gap {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (u : Matrix.unitaryGroup (Fin d) ℂ) (he : IsMIC d e) :
    Real.log (d + 1) - 2 / (d + 1) * Real.log 2 -
        vonNeumannEntropy (ludersState e u) =
      quantumRelativeEntropy (ludersState e u) (sigmaState u) +
        ((Matrix.trace (inputProjector u * ludersChannel e (inputProjector u))).re -
          2 / (d + 1)) * Real.log 2 := by
  sorry

private theorem haar_second_moment {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ) :
    (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
        (Matrix.trace (inputProjector u * ludersChannel e (inputProjector u))).re ∂
          (Measure.haarMeasure
            (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
      ((∑ i, (Matrix.trace (CFC.sqrt (e i))).re ^ 2) + d) /
        (d * (d + 1)) := by
  sorry

private theorem rank_one_forcing {d : ℕ}
    (a : Matrix (Fin d) (Fin d) ℂ) (ha : a.PosSemidef) :
    (a.trace.re) ^ 2 ≥ (a * a).trace.re := by
  let h : HermitianMat (Fin d) ℂ := ⟨a, ha.isHermitian⟩
  have hh : 0 ≤ h := HermitianMat.zero_le_iff.mpr ha
  have hi := HermitianMat.inner_le_mul_trace hh hh
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.trace_eq_re_trace] at hi
  change (a * a).trace.re ≤ a.trace.re * a.trace.re at hi
  simpa [pow_two] using hi

private theorem rank_one_from_equality {d : ℕ}
    (a : Matrix (Fin d) (Fin d) ℂ) (ha : a.PosSemidef) (ha0 : a ≠ 0)
    (heq : (a.trace.re) ^ 2 = (a * a).trace.re) :
    ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ a = (c : ℂ) • p := by
  sorry

private theorem saturation_forces_rank_one {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p := by
  sorry

private theorem saturation_ae_luders_eq_sigma {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ᵐ u ∂(Measure.haarMeasure
      (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))),
      ludersChannel e (inputProjector u) = (sigmaState u).1 := by
  sorry

private theorem saturation_everywhere_luders_eq_sigma {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
      ludersChannel e (inputProjector u) = (sigmaState u).1 := by
  sorry

private theorem depolarizing_identity {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hsat : typicalEntropy d e = Real.log (d + 1) -
      2 / (d + 1) * Real.log 2) :
    ∀ x : Matrix (Fin d) (Fin d) ℂ,
      ludersChannel e x =
        (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d + 1) := by
  sorry

private theorem sic_coefficients {d : ℕ} [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
    (he : IsMIC d e)
    (hrank : ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
      p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p)
    (hdepol : ∀ x : Matrix (Fin d) (Fin d) ℂ,
      ludersChannel e x =
        (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d + 1)) :
    IsSIC d e := by
  sorry

def claim : Prop :=
  ∀ (d : ℕ) [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ),
    IsMIC d e →
    typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
    ∃ f : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ, IsSIC d f

private theorem route_result_from
    (_hstate : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
      (u : Matrix.unitaryGroup (Fin d) ℂ), IsMIC d e →
      (ludersState e u).1 = ludersChannel e (inputProjector u))
    (_hgap : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ)
      (u : Matrix.unitaryGroup (Fin d) ℂ), IsMIC d e →
      Real.log (d + 1) - 2 / (d + 1) * Real.log 2 -
          vonNeumannEntropy (ludersState e u) =
        quantumRelativeEntropy (ludersState e u) (sigmaState u) +
          ((Matrix.trace (inputProjector u * ludersChannel e (inputProjector u))).re -
            2 / (d + 1)) * Real.log 2)
    (_hmoment : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ),
      (∫ u : Matrix.unitaryGroup (Fin d) ℂ,
          (Matrix.trace (inputProjector u * ludersChannel e (inputProjector u))).re ∂(Measure.haarMeasure
              (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ)))) =
        ((∑ i, (Matrix.trace (CFC.sqrt (e i))).re ^ 2) + d) /
          (d * (d + 1)))
    (_hforce : ∀ {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ), a.PosSemidef →
      (a.trace.re) ^ 2 ≥ (a * a).trace.re)
    (_hequality : ∀ {d : ℕ} (a : Matrix (Fin d) (Fin d) ℂ), a.PosSemidef →
      a ≠ 0 → (a.trace.re) ^ 2 = (a * a).trace.re →
      ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ a = (c : ℂ) • p)
    (hrank : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p)
    (_hae : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ᵐ u ∂(Measure.haarMeasure
        (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin d) ℂ))),
        ludersChannel e (inputProjector u) = (sigmaState u).1)
    (_hevery : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
        ludersChannel e (inputProjector u) = (sigmaState u).1)
    (hdepol : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
      ∀ x : Matrix (Fin d) (Fin d) ℂ,
        ludersChannel e x =
          (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d + 1))
    (hsic : ∀ {d : ℕ} [NeZero d]
      (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ), IsMIC d e →
      (∀ i, ∃ c : ℝ, ∃ p : Matrix (Fin d) (Fin d) ℂ,
        p.IsHermitian ∧ p * p = p ∧ p.trace = 1 ∧ e i = (c : ℂ) • p) →
      (∀ x : Matrix (Fin d) (Fin d) ℂ,
        ludersChannel e x =
          (x + Matrix.trace x • (1 : Matrix (Fin d) (Fin d) ℂ)) / (d + 1)) →
      IsSIC d e) : claim := by
  intro d inst e he hsat
  have hrank' := hrank e he hsat
  have hdepol' := hdepol e he hsat
  exact ⟨e, hsic e he hrank' hdepol'⟩

private theorem route_result : claim :=
  route_result_from luders_state_density entropy_gap haar_second_moment
    rank_one_forcing rank_one_from_equality saturation_forces_rank_one
    saturation_ae_luders_eq_sigma saturation_everywhere_luders_eq_sigma
    depolarizing_identity sic_coefficients

theorem result : claim := route_result

end D5.S3.Quantum.Measurements.LudersEntropySaturationSIC
