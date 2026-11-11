/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Literal six-row ordered purity and exact equality, and arbitrary density upper bound for n >= 23. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowPhysicalExtraction
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowConcentration
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
import Mathlib.Tactic

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowLiteralUpper
open QutritPerturbationAttainment
open SixRowScalarData (PhysicalScalarHyp theta)
open SixRowConcentration (centralSpectrum)

/-- Exact equality for the entire original ordered vector in the literal
APPT class. This theorem does not assert APPT of any concentrated vector. -/
theorem literal_upper_and_equality (n : ℕ) (hn : 23 ≤ n)
    (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ)
    (ho : Antitone l) (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1)
    (happt : APPT (diagonal (fun z => (l (e z) : ℂ)))) :
    (∑ i, (l i)^2 ≤ theta n) ∧ ((∑ i, (l i)^2 = theta n) ↔ l = centralSpectrum n) := by
  let hN : 36 ≤ 6*n := by omega
  have hActual : 0 < SixRowConcentration.U hN l ∧
      SixRowConcentration.heads hN l 14 = 0 ∧ SixRowConcentration.tails hN l 0 = 0 ∧
      PhysicalScalarHyp (SixRowConcentration.r hN l) (SixRowConcentration.H hN l)
        (SixRowConcentration.D hN l) (SixRowConcentration.a hN l)
        (SixRowConcentration.q hN l) := by
    -- Each Fin index unfolds to the same value; only its bound proof can differ.
    simpa only [SixRowConcentration.U, SixRowConcentration.B, SixRowConcentration.V,
      SixRowConcentration.r, SixRowConcentration.heads, SixRowConcentration.tails,
      SixRowConcentration.H, SixRowConcentration.D, SixRowConcentration.a, SixRowConcentration.q,
      SixRowPhysicalMoments.u, SixRowPhysicalMoments.v, SixRowPhysicalMoments.heads,
      SixRowPhysicalMoments.tails] using
      (SixRowPhysicalExtraction.literal_physical n hn e l ho hl hs happt)
  exact SixRowConcentration.original_upper_and_equality n hn hN l ho hl hs
    hActual.1 hActual.2.2.2

/-- Arbitrary complex PSD trace-one APPT densities have the same parity bound.
One existing reduction supplies the actual APPT diagonal and preserves purity. -/
theorem density_upper (n : ℕ) (hn : 23 ≤ n)
    (rho : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ)
    (hpos : rho.PosSemidef) (htrace : rho.trace = 1) (happt : APPT rho) :
    (rho * rho).trace.re ≤ theta n := by
  let e : (Fin 6 × Fin n) ≃ Fin (6*n) := finProdFinEquiv
  obtain ⟨l, ho, hl, hs, hdiag, hpur⟩ :=
    QuadbitQuintitMaximumPurity.diagonal_spectral_reduction e rho hpos htrace happt
  rw [hpur]
  exact (literal_upper_and_equality n hn e l ho hl hs hdiag).1

end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowLiteralUpper
