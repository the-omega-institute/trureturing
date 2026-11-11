/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Actual six-row APPT central maximum, ordered-spectrum equality and least eventual threshold. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowLiteralUpper
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowAttainment
import Mathlib.Data.Nat.Find
import Mathlib.Order.Bounds.Basic

/-!
CentralOptimal expresses the maximum over all complex PSD trace-one APPT
matrices, including attainment. A separate theorem characterizes equality for
the original ordered spectrum. The physical obstruction at dimension 22
establishes that the eventual threshold is least.
-/

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SixRowMaximumPurity
open Bipartite (APPT)
open SchmidtStar
open SixRowScalarData (theta)
open SixRowConcentration (centralSpectrum)

/-- Universal actual-density maximum and actual attainment, without uniqueness. -/
def CentralOptimal (n : ℕ) : Prop :=
  (∀ rho : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ,
    rho.PosSemidef → rho.trace = 1 → APPT rho →
      (rho * rho).trace.re ≤ theta n) ∧
  (∃ rho : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ,
    rho.PosSemidef ∧ rho.trace = 1 ∧ APPT rho ∧
      (rho * rho).trace.re = theta n)

/-- Every admissible dimension at or above k has the actual central maximum. -/
def EventualCentralFrom (k : ℕ) : Prop :=
  ∀ n : ℕ, 6 ≤ n → k ≤ n → CentralOptimal n

/-- The central spectrum attains the actual maximum and is the unique ordered maximizer. -/
def UniqueCentralOptimal (n : ℕ) : Prop :=
  let rho : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ :=
    diagonal (fun p => (centralSpectrum n (finProdFinEquiv p) : ℂ))
  CentralOptimal n ∧
    (Antitone (centralSpectrum n) ∧ (∀ i, 0 ≤ centralSpectrum n i) ∧
      (∑ i, centralSpectrum n i = 1) ∧ (∑ i, (centralSpectrum n i)^2 = theta n) ∧
      rho.PosSemidef ∧ rho.trace = 1 ∧ APPT rho ∧
      (rho * rho).trace.re = theta n) ∧
    (∀ (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ),
      Antitone l → (∀ i, 0 ≤ l i) → (∑ i, l i = 1) →
      APPT (diagonal (fun p => (l (e p) : ℂ))) →
      (∑ i, (l i)^2 = theta n) → l = centralSpectrum n)

/-- Tran's eventual unique central-spectrum maximality condition for six rows. -/
def EventualUniqueCentralFrom (k : ℕ) : Prop :=
  ∀ n : ℕ, 6 ≤ n → k ≤ n → UniqueCentralOptimal n

theorem central_optimal (n : ℕ) (hn : 23 ≤ n) : CentralOptimal n := by
  constructor
  · intro rho hpos htrace happt
    exact SixRowLiteralUpper.density_upper n hn rho hpos htrace happt
  · exact ⟨SixRowAttainment.centralDensity n,
      (SixRowAttainment.central_attainment n hn).2⟩

/-- Equality characterizes the entire original ordered APPT spectrum. -/
theorem ordered_spectrum_upper_and_equality (n : ℕ) (hn : 23 ≤ n)
    (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ)
    (ho : Antitone l) (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1)
    (happt : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    (∑ i, (l i)^2 ≤ theta n) ∧
      ((∑ i, (l i)^2 = theta n) ↔ l = centralSpectrum n) := by
  exact SixRowLiteralUpper.literal_upper_and_equality n hn e l ho hl hs happt

/-- The named central spectrum itself has an actual physical diagonal attainer. -/
theorem central_spectrum_attainment (n : ℕ) (hn : 23 ≤ n) :
    let rho : Matrix (Fin 6 × Fin n) (Fin 6 × Fin n) ℂ :=
      diagonal (fun p => (centralSpectrum n (finProdFinEquiv p) : ℂ))
    Antitone (centralSpectrum n) ∧ (∀ i, 0 ≤ centralSpectrum n i) ∧
      (∑ i, centralSpectrum n i = 1) ∧ (∑ i, (centralSpectrum n i)^2 = theta n) ∧
      rho.PosSemidef ∧ rho.trace = 1 ∧ APPT rho ∧
      (rho * rho).trace.re = theta n := by
  have hspec : Antitone (centralSpectrum n) ∧ (∀ i, 0 ≤ centralSpectrum n i) ∧
      (∑ i, centralSpectrum n i = 1) ∧ ∑ i, (centralSpectrum n i)^2 = theta n := by
    unfold centralSpectrum
    exact SixRowAttainment.central_spectrum_data n hn
  have hdiag : SixRowAttainment.centralDensity n =
      diagonal (fun p : Fin 6 × Fin n =>
        (centralSpectrum n (finProdFinEquiv p) : ℂ)) := by
    simpa only [centralSpectrum] using (SixRowAttainment.central_density_diagonal n)
  refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2, ?_⟩
  simpa only [hdiag] using (SixRowAttainment.central_attainment n hn).2

theorem unique_central_optimal (n : ℕ) (hn : 23 ≤ n) : UniqueCentralOptimal n := by
  refine ⟨central_optimal n hn, central_spectrum_attainment n hn, ?_⟩
  intro e l ho hl hs happt hpur
  exact (ordered_spectrum_upper_and_equality n hn e l ho hl hs happt).2.mp hpur

/-- Necessity uses an actual six-by-twenty-two APPT density beating theta(22). -/
theorem eventual_central_iff (k : ℕ) : EventualCentralFrom k ↔ 23 ≤ k := by
  constructor
  · intro hk
    by_contra h
    have hk22 : k ≤ 22 := by omega
    have h22 := hk 22 (by norm_num) hk22
    obtain ⟨hpos, htrace, happt, _hpur, _htheta, _hdiff, hstrict⟩ :=
      SixRowAttainment.n22_obstruction
    exact (not_le_of_gt hstrict)
      (h22.1 SixRowAttainment.ray22Density hpos htrace happt)
  · intro hk n _hn hkn
    exact central_optimal n (by omega)

theorem eventual_threshold_is_least : IsLeast {k : ℕ | EventualCentralFrom k} 23 := by
  refine ⟨(eventual_central_iff 23).2 le_rfl, ?_⟩
  intro k hk
  exact (eventual_central_iff k).1 hk

theorem eventual_unique_central_iff (k : ℕ) : EventualUniqueCentralFrom k ↔ 23 ≤ k := by
  constructor
  · intro hk
    apply (eventual_central_iff k).1
    intro n hn hkn
    exact (hk n hn hkn).1
  · intro hk n _hn hkn
    exact unique_central_optimal n (le_trans hk hkn)

theorem eventual_unique_threshold_is_least :
    IsLeast {k : ℕ | EventualUniqueCentralFrom k} 23 := by
  refine ⟨(eventual_unique_central_iff 23).2 le_rfl, ?_⟩
  intro k hk
  exact (eventual_unique_central_iff k).1 hk

/-- The least eventual threshold for the central spectrum to be the unique maximizer. -/
noncomputable def n0 : ℕ := by
  classical
  exact Nat.find (show ∃ k : ℕ, EventualUniqueCentralFrom k from
    ⟨23, (eventual_unique_central_iff 23).2 le_rfl⟩)

theorem n0_eq : n0 = 23 := by
  classical
  unfold n0
  apply Nat.le_antisymm
  · exact Nat.find_min' _ ((eventual_unique_central_iff 23).2 le_rfl)
  · exact (eventual_unique_central_iff _).1 (Nat.find_spec _)

/-- Full actual maximum and attainment, original ordered equality, exact parity
value and least eventual threshold for unique central-spectrum maximality.
No maximum below 23 is asserted. -/
theorem result :
    (∀ n : ℕ, 23 ≤ n → CentralOptimal n) ∧
    (∀ (n : ℕ) (hn : 23 ≤ n)
      (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ)
      (ho : Antitone l) (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1)
      (happt : APPT (diagonal (fun p => (l (e p) : ℂ)))),
      (∑ i, (l i)^2 ≤ theta n) ∧
        ((∑ i, (l i)^2 = theta n) ↔ l = centralSpectrum n)) ∧
    (∀ n : ℕ, theta n = if n%2 = 0 then 6/(35*(n : ℝ))
      else 6*(35*(n : ℝ)+2)/(35*(n : ℝ)+1)^2) ∧
    IsLeast {k : ℕ | EventualCentralFrom k} 23 ∧ n0 = 23 ∧
    (∀ n : ℕ, 23 ≤ n → UniqueCentralOptimal n) ∧
    IsLeast {k : ℕ | EventualUniqueCentralFrom k} 23 := by
  exact ⟨central_optimal, ordered_spectrum_upper_and_equality,
    fun _ => rfl, eventual_threshold_is_least, n0_eq,
    unique_central_optimal, eventual_unique_threshold_is_least⟩

end D5.S3.Quantum.Entanglement.AbsolutePPT.SixRowMaximumPurity
