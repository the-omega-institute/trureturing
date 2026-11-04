import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences

/-! # Registration mirror for `HannaA352700CatalanCongruences` -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.PowerSeries

noncomputable section

def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ n => coeffA n) (fun e => nomatch e)

def seriesOf (R : DependentFamily.Realization signature) : PowerSeries ℤ :=
  PowerSeries.mk (R.readout () ())

def seriesModOf (R : DependentFamily.Realization signature) (p : ℕ) : PowerSeries (ZMod p) :=
  (seriesOf R).map (Int.castRingHom (ZMod p))

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R =>
    (seriesModOf R 3 ^ 3 = (seriesModOf R 3).subst (X ^ 3)) ∧
    (seriesModOf R 3 = catalanMod 3 + X ^ 2 * catalanMod 3 ^ 3 ∧
      catalanMod 3 + X ^ 2 * catalanMod 3 ^ 3 = (2 - X) * catalanMod 3 - 1) ∧
    (seriesModOf R 2 = catalanMod 2) ∧
    (∀ n : ℕ, Int.ModEq 3 (R.readout () () n)
      (((Nat.choose (2 * n + 1) n / (2 * n + 1) : ℕ) : ℤ) + (raneyTerm n : ℤ))) ∧
    (∀ n : ℕ, 1 ≤ n → Int.ModEq 3 (R.readout () () n)
      (2 * (catalan n : ℤ) - (catalan (n - 1) : ℤ))) ∧
    (∀ n : ℕ, Int.ModEq 2 (R.readout () () n) (catalan n : ℤ))

abbrev sourceScope := type_of% (@result)

lemma source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

lemma actual_law : arena.Law actual := source_bridge.mp result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h.2.2.2.2.2 0
  change Int.ModEq 2 (0 : ℤ) (catalan 0 : ℤ) at h0
  rw [catalan_zero] at h0
  exact absurd h0 (by decide)

lemma dependence : DependentFamily.ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
  intro he
  change coeffA 1 = coeffA 2 at he
  have h1 := result.2.2.2.1 1
  have h2 := result.2.2.2.1 2
  have hr1 : (((Nat.choose (2 * 1 + 1) 1 / (2 * 1 + 1) : ℕ) : ℤ) + (raneyTerm 1 : ℤ)) = 1 := by
    decide
  have hr2 : (((Nat.choose (2 * 2 + 1) 2 / (2 * 2 + 1) : ℕ) : ℤ) + (raneyTerm 2 : ℤ)) = 3 := by
    decide
  rw [hr1, he] at h1
  rw [hr2] at h2
  exact absurd (h1.symm.trans h2) (by decide)

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (by cases j; cases i; rfl)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (DependentFamily.Realization signature) Type Unit where
  unitName :=
    `D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ n => coeffA n) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences
