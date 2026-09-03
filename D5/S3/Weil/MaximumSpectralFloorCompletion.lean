/- GID: D5/S3/Weil/MaximumSpectralFloorCompletion
   generality: G
   mirror-B: D5/B/S3/Weil/MaximumSpectralFloorCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Residual positivity and full-spectrum white-floor feasibility have the same maximum. -/

import Mathlib.Data.NNReal.Defs

/- Library-search audit trail (2026-09-03):
   * Six-route repository searches covered maximum spectral floors, white spectra,
     positive residual extensions, supremum bodies, digestion receipts, and all
     in-flight lane commits. No existing theorem states this completion equivalence.
   * The closest frozen results concern budgeted Haar-floor attainment after Cayley
     compactification; they do not identify local residual feasibility with full-spectrum
     decomposition at each floor.
   * Pinned Mathlib has no theorem specific to spectral completion. The proof uses
     `AddMonoidHom.map_add`, `sub_add_cancel`, `eq_sub_iff_add_eq`, `Set.ext`, and
     `congrArg` for `sSup` directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.MaximumSpectralFloorCompletion

/-- A floor is locally feasible when the source after removing its white component
is the reading of a positive residual spectrum. -/
def ResidualFeasible
    {Spectrum Reading : Type*}
    [AddCommMonoid Spectrum] [AddCommGroup Reading] [Module Real Reading]
    (check : Spectrum →+ Reading) (delta source : Reading) (floor : NNReal) : Prop :=
  ∃ residual : Spectrum,
    check residual = source - (floor : Real) • delta

/-- A floor is globally feasible when a full positive spectrum decomposes into a
positive residual plus its normalized white component. -/
def FullSpectrumFeasible
    {Spectrum Reading : Type*}
    [AddCommMonoid Spectrum] [AddCommGroup Reading] [Module Real Reading]
    (check : Spectrum →+ Reading) (white : NNReal → Spectrum)
    (source : Reading) (floor : NNReal) : Prop :=
  ∃ full residual : Spectrum,
    check full = source ∧ full = residual + white floor

/-- Once normalized white spectrum reads as the corresponding multiple of the
origin atom, local residual feasibility and full-spectrum floor feasibility have
explicit witnesses in both directions. Consequently their floor suprema agree. -/
theorem maximum_spectral_floor_completion
    {Spectrum Reading : Type*}
    [AddCommMonoid Spectrum] [AddCommGroup Reading] [Module Real Reading]
    (check : Spectrum →+ Reading) (white : NNReal → Spectrum)
    (delta source : Reading)
    (whiteReading : ∀ floor, check (white floor) = (floor : Real) • delta) :
    (∀ floor,
      ResidualFeasible check delta source floor ↔
        FullSpectrumFeasible check white source floor) ∧
      sSup {floor : NNReal | ResidualFeasible check delta source floor} =
        sSup {floor : NNReal | FullSpectrumFeasible check white source floor} := by
  have feasibleIff : ∀ floor,
      ResidualFeasible check delta source floor ↔
        FullSpectrumFeasible check white source floor := by
    intro floor
    constructor
    · rintro ⟨residual, residualReading⟩
      refine ⟨residual + white floor, residual, ?_, rfl⟩
      calc
        check (residual + white floor) =
            check residual + check (white floor) := check.map_add _ _
        _ = (source - (floor : Real) • delta) +
            (floor : Real) • delta := by rw [residualReading, whiteReading]
        _ = source := sub_add_cancel _ _
    · rintro ⟨full, residual, fullReading, decomposition⟩
      refine ⟨residual, ?_⟩
      apply eq_sub_iff_add_eq.mpr
      calc
        check residual + (floor : Real) • delta =
            check residual + check (white floor) := by rw [whiteReading]
        _ = check (residual + white floor) := (check.map_add _ _).symm
        _ = check full := by rw [decomposition]
        _ = source := fullReading
  refine ⟨feasibleIff, ?_⟩
  apply congrArg sSup
  ext floor
  exact feasibleIff floor

#print axioms maximum_spectral_floor_completion

end D5.S3.Weil.MaximumSpectralFloorCompletion
