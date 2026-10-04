import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SpectralFamilyGeometry
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry
open _root_.D5.S3.TotalVariation.Hellinger
open _root_.D5.S3.TotalVariation.Bhattacharyya
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry
universe u v

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => 1 - x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {Sector : Type u} {Coord : Type v}
    [Fintype Sector] [Fintype Coord] [Nonempty Sector]
    (spectrum : Sector → Coord → ℝ)
    (_hnonneg : ∀ s j, 0 ≤ spectrum s j)
    (_hnormal : ∀ s, ∑ j, spectrum s j = 1),
    (∀ p ∈ stdSimplex ℝ Sector,
      spectralPairVariance spectrum p =
        2 * R.readout () () (spectralGramEnergy spectrum p)) ∧
    ∃ p ∈ stdSimplex ℝ Sector, ∃ s t : Sector,
      (∀ r ∈ stdSimplex ℝ Sector,
        spectralPairVariance spectrum r ≤ spectralPairVariance spectrum p) ∧
      (∀ a b : Sector, spectralGap spectrum a b ≤ spectralGap spectrum s t) ∧
      spectralGap spectrum s t / 2 ≤ spectralPairVariance spectrum p ∧
      spectralPairVariance spectrum p ≤ spectralGap spectrum s t ∧
      (spectralPairVariance spectrum p = 0 ↔
        ∀ a b : Sector, spectrum a = spectrum b) ∧
      (∀ a : Sector,
        spectralGramEnergy spectrum p ≤
          ∑ t, p t * bhattacharyya (spectrum a) (spectrum t) ∧
        (0 < p a → spectralGramEnergy spectrum p =
          ∑ t, p t * bhattacharyya (spectrum a) (spectrum t))) ∧
      (∀ r ∈ stdSimplex ℝ Sector,
        (∀ w ∈ stdSimplex ℝ Sector,
          spectralGramEnergy spectrum r ≤ spectralGramEnergy spectrum w) ↔
        ∀ a : Sector,
          spectralGramEnergy spectrum r ≤
            ∑ t, r t * bhattacharyya (spectrum a) (spectrum t) ∧
          (0 < r a → spectralGramEnergy spectrum r =
            ∑ t, r t * bhattacharyya (spectrum a) (spectrum t)))

theorem actual_law : arena.{u, v}.Law actual := by
  intro Sector Coord _ _ _ spectrum hnonneg hnormal
  exact finite_spectral_family_geometry spectrum hnonneg hnormal

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let spectrum : ULift.{u} Unit → ULift.{v} Unit → ℝ := fun _ _ => 1
  let p : ULift.{u} Unit → ℝ := Pi.single ⟨()⟩ 1
  have hp : p ∈ stdSimplex ℝ (ULift.{u} Unit) :=
    single_mem_stdSimplex ℝ (⟨()⟩ : ULift.{u} Unit)
  have hnonneg : ∀ s j, 0 ≤ spectrum s j := by simp [spectrum]
  have hnormal : ∀ s : ULift.{u} Unit, ∑ j : ULift.{v} Unit, spectrum s j = 1 := by
    simp [spectrum]
  have heq := (h spectrum hnonneg hnormal).1 p hp
  have hzero : spectralPairVariance spectrum p = 0 := by
    simp [spectralPairVariance, spectrum, hellinger_sq_self]
  have hbad : rejected.readout () () (spectralGramEnergy spectrum p) = 1 := rfl
  rw [hzero, hbad] at heq
  norm_num at heq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.finite_spectral_family_geometry.{u_1, u_2}) (type_of% (arena.{u_1, u_2})) (type_of% (arena.{u_1, u_2})) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 1 - x) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "SpectralFamilyGeometry") "finite_spectral_family_geometry") "Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry/Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena.{u_1, u_2})⟩,
  objectArena := ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => 1 - x) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.SpectralFamilyGeometry, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end Reg.D5.S3.Quantum.Entanglement.SpectralFamilyGeometry
