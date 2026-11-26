import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate

/-! The strict comparison in the ordinary matrix-level Wu bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope
open _root_.D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate

namespace Reg.D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate

local notation "certificateSpectrum" =>
  _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope.spectrum

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => y < x) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ρ : Matrix (Fin 4) (Fin 4) ℂ}
      (hρ : ρ.PosDef) (htr : ρ.trace = 1)
      (_hspectrum : eigenvalue hρ.isHermitian = certificateSpectrum),
    let α := (9 / 2 : ℝ) * Real.sinh (temperature / 3) * Real.sinh (2 * temperature / 3) /
      (2 * temperature * Real.sinh temperature)
    R.readout () () (1 / 8000) (4 * Real.cosh temperature / 9 *
      (physicalCubicEnergy ρ - α * physicalRelativeEntropy ρ hρ htr))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let descendingSpectrum : Fin 4 → ℝ :=
    ![certificateSpectrum 3, certificateSpectrum 2, certificateSpectrum 1, certificateSpectrum 0]
  let ρ := Matrix.diagonal (fun i => (descendingSpectrum i : ℂ))
  have hρ : ρ.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    have hi : 0 < descendingSpectrum i := by
      fin_cases i <;> norm_num [descendingSpectrum,
        _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope.spectrum, spectrumOf, roots]
    exact_mod_cast hi
  have htr : ρ.trace = 1 := by
    dsimp only [ρ]
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum]
    norm_num [Fin.sum_univ_four, descendingSpectrum,
      _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope.spectrum, spectrumOf, roots]
  have hmono : Antitone descendingSpectrum := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;>
      norm_num [descendingSpectrum,
        _root_.D5.S3.Quantum.Semigroups.WuCubicOccupationEnvelope.spectrum, spectrumOf, roots]
  have hroots : ρ.charpoly.roots.map Complex.re = (List.ofFn descendingSpectrum : Multiset ℝ) := by
    dsimp only [ρ]
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp [Fin.univ_val_map]
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsorted :
      (List.ofFn descendingSpectrum : Multiset ℝ).sort (· ≥ ·) = List.ofFn descendingSpectrum := by
    rw [Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using hmono.sortedGE_ofFn
  have hdiag : (fun i : Fin 4 =>
      hρ.isHermitian.eigenvalues₀ (i.cast (Fintype.card_fin 4).symm)) = descendingSpectrum := by
    apply List.ofFn_injective
    rw [← List.ofFn_congr (Fintype.card_fin 4) hρ.isHermitian.eigenvalues₀,
      ← hρ.isHermitian.sort_roots_charpoly_eq_eigenvalues₀]
    change (ρ.charpoly.roots.map Complex.re).sort (· ≥ ·) = _
    rw [hroots, hsorted]
  have hspectrum : eigenvalue hρ.isHermitian = certificateSpectrum := by
    funext i
    calc
      eigenvalue hρ.isHermitian i = hρ.isHermitian.eigenvalues₀
          (i.rev.cast (Fintype.card_fin 4).symm) := by
        simp [eigenvalue, ascendingIndex, Matrix.IsHermitian.eigenvalues]
      _ = descendingSpectrum i.rev := congrFun hdiag i.rev
      _ = certificateSpectrum i := by fin_cases i <;> rfl
  exact (lt_asymm (matrix_level_Wu_cubic_lower_bound hρ htr hspectrum)) (h hρ htr hspectrum)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (lt_irrefl (1 : ℝ)) (Eq.mp (congrFun h 1) (by norm_num : (0 : ℝ) < 1))

def family : Registration arena (type_of% @matrix_level_Wu_cubic_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@matrix_level_Wu_cubic_lower_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@matrix_level_Wu_cubic_lower_bound) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate.matrix_level_Wu_cubic_lower_bound.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0, functionOperand := true, stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate
