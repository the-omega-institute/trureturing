import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Hankel.SunA006077Result

/-! Two source observations retain both residue branches of the complete assertion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Hankel.SunA006077Result

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Hankel.SunA006077

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ n => W n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (n % 3 = 1 → R.readout false () n = 0) ∧
    (n % 3 ≠ 1 → ∃ z : ℤ, 0 < z ∧ Odd z ∧
      (-1 : ℤ)^((n+1)/3)*R.readout true () n=6^n*z)

private def rejected (i : Bool) : Realization signature :=
  realize signature (fun j _ n => if j=i then (if i then 0 else 1) else W n)
    (fun e => nomatch e)

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejected i) := by
  cases i
  · intro h
    have heq := (h 1).1 (by decide)
    norm_num [rejected,realize] at heq
  · intro h
    obtain ⟨z,hz,_,heq⟩ := (h 0).2 (by decide)
    norm_num [rejected,realize] at heq
    omega

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result,rejected false,rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i,?_,rfl,rejected_law i⟩
      intro j hj
      funext p n
      simp [actual,rejected,realize,hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    change W 0 ≠ W 1
    have hz : W 1=0 := zero_branch 0
    rw [hz]
    change (Matrix.of fun i j : Fin 1 => w (i.val+j.val)).det ≠ 0
    rw [Matrix.det_fin_one]
    norm_num [w]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Hankel.SunA006077.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Hankel.SunA006077.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Hankel.SunA006077Result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => W n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Hankel.SunA006077Result
    definition := some {
      owner := `D5.S3.Combinatorics.Hankel.SunA006077Result
      name := `D5.S3.Combinatorics.Hankel.SunA006077.claim
      path := #[]}
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false},{
      path := #["body","arg","body","arg","body","arg","arg","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Hankel.SunA006077Result
