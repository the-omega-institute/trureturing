import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
import Reg.Support.UniverseSingleReadout

/-! Observations of graded counts, geometric series, and positive directions. -/

namespace Reg.D5.S3.Combinatorics.MatrixOrbits.IdentityCycle

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.A333886
open LeanInformationAudit PowerSeries
open scoped BigOperators

noncomputable section

local notation "x" => (PowerSeries.X : PowerSeries ℚ)

private abbrev singletonGrade : Graded where
  Space := Unit
  weight _ := 0
  finite_fiber _ := inferInstance

private abbrev emptyGrade : Graded where
  Space := Empty
  weight _ := 0
  finite_fiber _ := inferInstance

private theorem singleton_series : singletonGrade.series = 1 := by
  ext n
  rw [Graded.coeff_series, coeff_one]
  split
  · subst n
    let e : singletonGrade.Fiber 0 ≃ Unit :=
      { toFun := Subtype.val, invFun := fun u => ⟨u, rfl⟩
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    simp
  · rename_i hn
    let : IsEmpty (singletonGrade.Fiber n) := ⟨fun v => hn v.property.symm⟩
    simp

private theorem empty_series : emptyGrade.series = 0 := by
  ext n
  let : IsEmpty (emptyGrade.Fiber n) := ⟨fun v => nomatch v.val⟩
  simp

private theorem geom_ne : geom 1 ≠ geom 2 := by
  intro h
  have h₁ := geom_mul 1 (by decide)
  have h₂ := geom_mul 2 (by decide)
  rw [← h] at h₂
  have hf : (1 - x ^ 1) = (1 - x ^ 2) := by
    calc
      (1 - x ^ 1) = (1 - x ^ 1) * ((1 - x ^ 2) * geom 1) := by rw [h₂, mul_one]
      _ = (1 - x ^ 2) * ((1 - x ^ 1) * geom 1) := by ring
      _ = (1 - x ^ 2) := by rw [h₁, mul_one]
  have he := congrArg (PowerSeries.coeff (R := ℚ) 1) hf
  norm_num [map_sub, coeff_one, coeff_X_pow] at he

namespace CountCoefficients

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature (ℕ → ℕ) (fun _ => ℕ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ a n => coeff n (countSeries a)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ → ℕ) (n : ℕ), R.readout () a n = (a n : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (fun _ => 1) 0
  norm_num [rejected, realize] at he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨id, 0, 1, ?_⟩
  change coeff 0 (countSeries id) ≠ coeff 1 (countSeries id)
  simp

def family : Registration arena (type_of% @coeff_countSeries) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coeff_countSeries, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coeff_countSeries) (Realization signature) Unit Unit where
  unitName := `A333886.coeff_countSeries.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a n => coeff n (countSeries a)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CountCoefficients

namespace FiberCoefficients

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Graded (fun _ => ℕ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ A n => coeff n A.series) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Graded) (n : ℕ), R.readout () A n = (Nat.card (A.Fiber n) : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := h singletonGrade 0
  rw [← Graded.coeff_series, singleton_series] at hc
  norm_num [rejected, realize] at hc

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨singletonGrade, 0, 1, ?_⟩
  change coeff 0 singletonGrade.series ≠ coeff 1 singletonGrade.series
  simp [singleton_series, coeff_one]

def family : Registration arena (type_of% @Graded.coeff_series) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Graded.coeff_series, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Graded.coeff_series) (Realization signature) Unit Unit where
  unitName := `A333886.Graded.coeff_series.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ A n => coeff n A.series) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiberCoefficients

namespace ProductSeries

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Graded) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ A => A.series) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ A B : Graded, (A.prod B).series = R.readout () () A * B.series

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h singletonGrade singletonGrade
  rw [Graded.series_prod, singleton_series] at he
  simpa [rejected, realize] using he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), singletonGrade, emptyGrade, ?_⟩
  change singletonGrade.series ≠ emptyGrade.series
  simp [singleton_series, empty_series]

def family : Registration arena (type_of% @Graded.series_prod) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Graded.series_prod, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Graded.series_prod) (Realization signature) Unit Unit where
  unitName := `A333886.Graded.series_prod.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A.series) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ProductSeries

namespace SumSeries

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Graded) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ A => A.series) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ A B : Graded, (A.sum B).series = R.readout () () A + B.series

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h singletonGrade emptyGrade
  rw [Graded.series_sum, singleton_series, empty_series] at he
  simpa [rejected, realize] using he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), singletonGrade, emptyGrade, ?_⟩
  change singletonGrade.series ≠ emptyGrade.series
  simp [singleton_series, empty_series]

def family : Registration arena (type_of% @Graded.series_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Graded.series_sum, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Graded.series_sum) (Realization signature) Unit Unit where
  unitName := `A333886.Graded.series_sum.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A.series) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SumSeries

namespace ShiftSeries

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Graded) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ A => A.series) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Graded) (d : ℕ), (A.shift d).series = x ^ d * R.readout () () A

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h singletonGrade 0
  rw [Graded.series_shift, singleton_series] at he
  simpa [rejected, realize] using he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), singletonGrade, emptyGrade, ?_⟩
  change singletonGrade.series ≠ emptyGrade.series
  simp [singleton_series, empty_series]

def family : Registration arena (type_of% @Graded.series_shift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Graded.series_shift, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Graded.series_shift) (Realization signature) Unit Unit where
  unitName := `A333886.Graded.series_shift.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A.series) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ShiftSeries

namespace TransportedSeries

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Graded) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ B => B.series) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type} (B : Graded) (e : α ≃ B.Space), (B.ofEquiv e).series = R.readout () () B

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h singletonGrade (Equiv.refl Unit)
  rw [Graded.series_ofEquiv, singleton_series] at he
  simpa [rejected, realize] using he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), singletonGrade, emptyGrade, ?_⟩
  change singletonGrade.series ≠ emptyGrade.series
  simp [singleton_series, empty_series]

def family : Registration arena (type_of% @Graded.series_ofEquiv) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Graded.series_ofEquiv, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Graded.series_ofEquiv) (Realization signature) Unit Unit where
  unitName := `A333886.Graded.series_ofEquiv.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ B => B.series) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TransportedSeries

namespace GeometricInverse

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ d => geom d) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : ℕ, 0 < d → (1 - x ^ d) * R.readout () () d = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 (by decide)
  simpa [rejected, realize] using he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 1, 2, geom_ne⟩

def family : Registration arena (type_of% @geom_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@geom_mul, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@geom_mul) (Realization signature) Unit Unit where
  unitName := `A333886.geom_mul.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => geom d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeometricInverse

namespace GeometricCount

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ d => geom d) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (hd : 0 < d), (Graded.nats d hd).series = R.readout () () d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 (by decide)
  rw [Graded.series_nats] at he
  have hm := geom_mul 1 (by decide)
  change geom 1 = 0 at he
  rw [he, mul_zero] at hm
  exact zero_ne_one hm

private theorem depends : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 1, 2, geom_ne⟩

def family : Registration arena (type_of% @Graded.series_nats) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Graded.series_nats, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Graded.series_nats) (Realization signature) Unit Unit where
  unitName := `A333886.Graded.series_nats.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => geom d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeometricCount

namespace PositiveSize

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Bool (fun _ => ℕ) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ b a => size (positiveDir b a)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b : Bool) (a : ℕ), R.readout () b a = a + 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h false 0
  simp [rejected, realize] at he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨false, 0, 1, ?_⟩
  cases role
  decide

def family : Registration arena (type_of% @positiveDir_size) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positiveDir_size, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@positiveDir_size) (Realization signature) Unit Unit where
  unitName := `A333886.positiveDir_size.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ b a => size (positiveDir b a)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveSize

namespace PositiveReconstruction

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Dir) (fun _ => Dir)

private def actual : Realization signature :=
  realize signature (fun _ _ d => positiveDir (reversed d) (size d - 1)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Sum.inl 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ d : Dir, size d ≠ 0 → R.readout () () d = d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (Sum.inl 1) (by decide)
  change (Sum.inl 0 : Dir) = Sum.inl 1 at he
  cases he

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), Sum.inl 1, Sum.inr 0, ?_⟩
  cases role
  decide

def family : Registration arena (type_of% @positiveDir_rebuild) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positiveDir_rebuild, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@positiveDir_rebuild) (Realization signature) Unit Unit where
  unitName := `A333886.positiveDir_rebuild.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => positiveDir (reversed d) (size d - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveReconstruction

namespace CycleSeries

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Fin 5) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ k => cycleMultiplicity k) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := (∑ k : Fin 5, (R.readout () () k : PowerSeries ℚ) * twistSeries (rep k)) =
    24 * countSeries a333886

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simp only [rejected, realize, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at h
  have hc : a333886 0 ≠ 0 := by
    intro hz
    have he := cycle_count 0
    rw [hz, mul_zero] at he
    have hpos : 0 < Nat.card (TwistMat (rep 0) 0) := by
      let zero : TwistMat (rep 0) 0 :=
        (pattern0.equiv 0).symm ⟨fun _ => 0, by intro i; simp⟩
      letI : Nonempty (TwistMat (rep 0) 0) := ⟨zero⟩
      exact Nat.card_pos
    have hle := Finset.single_le_sum (f := fun k : Fin 5 =>
      cycleMultiplicity k * Nat.card (TwistMat (rep k) 0))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ (0 : Fin 5))
    rw [he] at hle
    have hmult : cycleMultiplicity (0 : Fin 5) = 1 := rfl
    rw [hmult, one_mul] at hle
    exact (not_lt_of_ge hle) hpos
  have he := congrArg (PowerSeries.coeff (R := ℚ) 0) h
  rw [map_zero, ← Nat.cast_ofNat (n := 24) (R := PowerSeries ℚ), ← map_natCast PowerSeries.C,
    coeff_C_mul, coeff_countSeries] at he
  exact hc (by exact_mod_cast (mul_eq_zero.mp he.symm).resolve_left (by norm_num))

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  cases role
  decide

def family : Registration arena (type_of% @cycle_series) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cycle_series, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cycle_series) (Realization signature) Unit Unit where
  unitName := `A333886.cycle_series.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => cycleMultiplicity k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CycleSeries

private abbrev twistGrade : Graded where
  Space := Σ n : ℕ, TwistMat rep0 n
  weight a := a.1
  finite_fiber n := Finite.of_injective
    (fun a => a.property ▸ a.val.2 : {a : Σ i : ℕ, TwistMat rep0 i // a.1 = n} → TwistMat rep0 n)
    (by rintro ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩; dsimp at hi hj; subst i; subst j; simp)

private def twistGradeEquiv (n : ℕ) : TwistMat rep0 n ≃ twistGrade.Fiber n where
  toFun a := ⟨⟨n, a⟩, rfl⟩
  invFun a := a.property ▸ a.val.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨i, a⟩, hi⟩; change i = n at hi; subst i; rfl

private theorem geom_const (d : ℕ) (hd : 0 < d) : constantCoeff (geom d) = 1 := by
  simp [geom, Nat.ne_of_gt hd]

namespace TwistedFibers

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Graded) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ S => S.series) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : P) (S : Graded) (_ : ∀ n, TwistMat p n ≃ S.Fiber n),
    twistSeries p = R.readout () () S

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : twistSeries rep0 = 0 := h rep0 twistGrade twistGradeEquiv
  rw [twist0_series] at he
  have hz := congrArg (constantCoeff (R := ℚ)) he
  norm_num [geom_const] at hz

private theorem depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), singletonGrade, emptyGrade, ?_⟩
  change singletonGrade.series ≠ emptyGrade.series
  simp [singleton_series, empty_series]

def family : Registration arena (type_of% @twist_series_from_fibers) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@twist_series_from_fibers, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@twist_series_from_fibers) (Realization signature) Unit Unit where
  unitName := `A333886.twist_series_from_fibers.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => S.series) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwistedFibers

namespace IdentityGeometricFactor

private abbrev signature :=
  Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => PowerSeries ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ d => geom d) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := twistSeries rep0 = (R.readout () () 1)^4 * (((1+x)*geom 1)^3 +
    4*(x^2*geom 2*(1-x^3)*geom 1^3-(x*geom 1)^3))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := congrArg (constantCoeff (R := ℚ)) twist0_series
  have he : twistSeries rep0 = 0 := by simpa [rejected, realize] using h
  rw [he] at hz
  norm_num [geom_const] at hz

private theorem depends : ObservationalDependence signature actual := by
  intro role
  exact ⟨(), 1, 2, geom_ne⟩

def family : Registration arena (type_of% @twist0_series) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@twist0_series, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@twist0_series) (Realization signature) Unit Unit where
  unitName := `A333886.twist0_series.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => geom d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IdentityGeometricFactor

end
end Reg.D5.S3.Combinatorics.MatrixOrbits.IdentityCycle
