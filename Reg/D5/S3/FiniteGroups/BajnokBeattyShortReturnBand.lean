import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyShortReturnBand
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Full original telescope and actual two-return-family observations.
The original actualReturn, rejectedReturn and checked observational-dependence
proof are reused.  The new arena contains the actual n+2r band equation,
with every source parameter and hypothesis retained.  The outer record is
one faithful attempt, not a claim of successful contract discovery.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyShortReturnBand

open _root_.D5.S3.FiniteGroups.BajnokBeattyShortReturnBand
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev bandArena : Arena where
  signature := returnSignature
  Law R := ∀ (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t)
    (r : ℕ) (hr : (r : ℤ) < p),
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let n : ℕ := (p*(m-3)).toNat
    R.readout 1 ⟨p,t⟩ (n+2*r) = R.readout 0 ⟨p,t⟩ (n+2*r) +
      2 * (Nat.choose (n+2*r) r)^2

private theorem actual_law : bandArena.Law actualReturn := by
  exact short_return_band

private theorem rejected_law (i : Fin 2) : ¬ bandArena.Law (rejectedReturn i) := by
  intro h
  have hh := h 3 2 (by norm_num) (by decide) (by norm_num) 0 (by norm_num)
  have hd : returns33 3 2 24 = returns19 3 2 24 + 2 :=
    short_return_band 3 2 (by norm_num) (by decide) (by norm_num) 0 (by norm_num)
  fin_cases i
  · change returns33 3 2 24 = (returns19 3 2 24 + 1) + 2 at hh
    omega
  · change returns33 3 2 24 + 1 = returns19 3 2 24 + 2 at hh
    omega

noncomputable def bandSource : Registration bandArena
    (type_of% short_return_band) where
  actual := actualReturn
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedReturn 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedReturn i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext pt l
      simp [rejectedReturn, realize, hj]
    · intro e
      exact nomatch e
  dependence := returnSource.dependence

noncomputable def bandRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@short_return_band)
      (Realization returnSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyShortReturnBand.short_return_band.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyShortReturnBand.bandSource
  realizationSource := none
  generated := false
  arena := .source ⟨bandArena⟩
  objectArena := .source ⟨bandArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bandArena ⟨bandSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize returnSignature
    (fun i pt l => if i = 0 then returns19 pt.1 pt.2 l else returns33 pt.1 pt.2 l)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattyShortReturnBand
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","body","body","body",
        "arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body","body","body","body","body","body","body",
        "body","body","body","body","body","body","body","body","body","body",
        "fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyShortReturnBand
