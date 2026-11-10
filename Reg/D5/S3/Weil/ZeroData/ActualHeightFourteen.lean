import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZeroData.ActualHeightFourteen
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZeroData.ActualHeightFourteen
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZeroSum
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open LeanInformationAudit
open scoped BigOperators

namespace HeightFourteen

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ rho => |rho.im|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep the original complex variable and its genuine nontrivial-zero premise. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (rho : ℂ) (_hrho : IsNontrivialZero rho),
    14 < R.readout () () rho

private theorem source_reconstruction :
    (type_of% (@actual_height_gt_fourteen)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := hall (actualData.zero 0) (actualData.zero_isNontrivial 0)
  norm_num [rejected, realize] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), Complex.I, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% (@actual_height_gt_fourteen)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_height_gt_fourteen, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/- Select the absolute ordinate on the original strict inequality's RHS.
The lexical state is rho (binder 0); its zero premise (binder 1) remains literal. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_height_gt_fourteen) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.actual_height_gt_fourteen.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualHeightFourteen.HeightFourteen.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ rho => |rho.im|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualHeightFourteen
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

end HeightFourteen

namespace MassFourteen

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ k => ((actualZero k).im)⁻¹ ^ 2)
    (fun e => nomatch e)

/-- An intervention on the summand, with a genuine finite sum of mass four. -/
def rejected : Realization signature :=
  realize signature (fun _ _ k => if k = 0 then 4 else 0)
    (fun e => nomatch e)

/-- The original full natural-index sum and exact first Li mass remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := (∑' k : ℕ, R.readout () () k) ≤ (197 / 196 : ℝ) * firstLiMass

private theorem source_reconstruction :
    (type_of% (@actual_inverse_square_mass_le_height_fourteen)) ↔ arena.Law actual :=
  Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro hall
  have hbad : (4 : ℝ) ≤ (197 / 196 : ℝ) * firstLiMass := by
    simpa [rejected, realize] using hall
  linarith [firstLiMass_lt_one]

/- A summable natural sequence whose zeroth term is nonzero cannot be constant.
This proves actual observation dependence without assuming distinct zeros have
different absolute ordinates or discarding any multiplicity fiber. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  classical
  intro i
  by_contra h
  have hc : ∀ k : ℕ, actual.readout i () k = actual.readout i () 0 := by
    intro k
    by_contra hk
    exact h ⟨(), k, 0, hk⟩
  have hs : Summable (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2) := by
    simpa only [actualZero, Function.comp_def] using
      (actualOccurrenceEquiv.summable_iff).2 actual_sigma_inverse_square_summable
  have hsconst : Summable (fun _ : ℕ => actual.readout i () 0) := by
    apply hs.congr
    intro k
    exact hc k
  have hz : actual.readout i () 0 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hsconst.tendsto_atTop_zero
  have hi : (actualZero 0).im ≠ 0 := by
    intro hzero
    have hgt := actual_ordinate_sq_gt_one (actualOccurrenceEquiv 0).1
    change 1 < (actualZero 0).im ^ 2 at hgt
    rw [hzero] at hgt
    norm_num at hgt
  change ((actualZero 0).im)⁻¹ ^ 2 = 0 at hz
  exact (pow_ne_zero 2 (inv_ne_zero hi)) hz

def family : Registration arena
    (type_of% (@actual_inverse_square_mass_le_height_fourteen)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_inverse_square_mass_le_height_fourteen, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/- Enter the LHS of LE, the function argument of tsum before its summation
filter, and its original k lambda. Select the full original summand. The lexical
state is k (binder 0); the domain is the entire Nat and the RHS stays literal. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_inverse_square_mass_le_height_fourteen) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds.actual_inverse_square_mass_le_height_fourteen.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ActualHeightFourteen.MassFourteen.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ k => ((actualZero k).im)⁻¹ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ActualHeightFourteen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MassFourteen

end Reg.D5.S3.Weil.ZeroData.ActualHeightFourteen
