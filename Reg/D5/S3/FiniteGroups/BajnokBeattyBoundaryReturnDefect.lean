import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful full-telescope four-slot attempt for the first strict reversal.
The existing actual two-return observations and observational-dependence proof
are reused. Successful Lean compilation is proof evidence, not a claim that
the audit inspector validates the source reconstruction or scoped dependence.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect
open _root_.D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev reversalArena : Arena where
  signature := returnSignature
  Law R := ∀ (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t),
    let m : ℤ := 6*t-1
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 := Submodule.span ℤ (Set.range ![v133, v233])
    let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
    let L : ℕ := (p*(m-1)).toNat
    let P : ℕ := p.toNat
    (∀ l : ℕ, l < L → R.readout 0 ⟨p,t⟩ l ≤ R.readout 1 ⟨p,t⟩ l) ∧
      R.readout 1 ⟨p,t⟩ L + 2 * Nat.choose L (4*P) = R.readout 0 ⟨p,t⟩ L + 2 * (Nat.choose L P)^2 ∧
      R.readout 1 ⟨p,t⟩ L < R.readout 0 ⟨p,t⟩ L

private theorem actual_law : reversalArena.Law actualReturn := by
  exact first_return_reversal

private theorem rejected_law (i : Fin 2) : ¬ reversalArena.Law (rejectedReturn i) := by
  intro h
  have hh := (h 3 2 (by norm_num) (by decide) (by norm_num)).2.1
  have hd := (first_return_reversal 3 2 (by norm_num) (by decide) (by norm_num)).2.1
  change returns33 3 2 30 + 2 * Nat.choose 30 12 =
    returns19 3 2 30 + 2 * (Nat.choose 30 3)^2 at hd
  fin_cases i
  · change returns33 3 2 30 + 2 * Nat.choose 30 12 =
      (returns19 3 2 30 + 1) + 2 * (Nat.choose 30 3)^2 at hh
    omega
  · change (returns33 3 2 30 + 1) + 2 * Nat.choose 30 12 =
      returns19 3 2 30 + 2 * (Nat.choose 30 3)^2 at hh
    omega

noncomputable def reversalSource : Registration reversalArena
    (type_of% first_return_reversal) where
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

noncomputable def reversalRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@first_return_reversal)
      (Realization returnSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect.first_return_reversal.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect.reversalSource
  realizationSource := none
  generated := false
  arena := .source ⟨reversalArena⟩
  objectArena := .source ⟨reversalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reversalArena ⟨reversalSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize returnSignature
    (fun i pt l => if i = 0 then returns19 pt.1 pt.2 l else returns33 pt.1 pt.2 l)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect
