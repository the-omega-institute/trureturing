import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Dependent observations of the exact five-row defect counts. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal (Col)
open LeanInformationAudit
open scoped BigOperators
noncomputable section
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip
attribute [local irreducible] a
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected (k : ℕ) : Realization signature :=
  realize signature (fun _ _ n => a n + if n = k+19 then 1 else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (R.readout () () (n + 19) : ℤ) = 32 * (R.readout () () (n + 18) : ℤ) - 384 * (R.readout () () (n + 17) : ℤ) + 2200 * (R.readout () () (n + 16) : ℤ) - 6494 * (R.readout () () (n + 15) : ℤ) + 9016 * (R.readout () () (n + 14) : ℤ) - 816 * (R.readout () () (n + 13) : ℤ) - 14888 * (R.readout () () (n + 12) : ℤ) + 18879 * (R.readout () () (n + 11) : ℤ) - 5464 * (R.readout () () (n + 10) : ℤ) - 7472 * (R.readout () () (n + 9) : ℤ) + 8336 * (R.readout () () (n + 8) : ℤ) - 3648 * (R.readout () () (n + 7) : ℤ) + 768 * (R.readout () () (n + 6) : ℤ) - 64 * (R.readout () () (n + 5) : ℤ)
private theorem rejected_at (k : ℕ) (h : arena.Law (rejected k)) : False := by
  have hb := h k
  have ha := result k
  have h5 : k+5 ≠ k+19 := by omega
  have h6 : k+6 ≠ k+19 := by omega
  have h7 : k+7 ≠ k+19 := by omega
  have h8 : k+8 ≠ k+19 := by omega
  have h9 : k+9 ≠ k+19 := by omega
  have h10 : k+10 ≠ k+19 := by omega
  have h11 : k+11 ≠ k+19 := by omega
  have h12 : k+12 ≠ k+19 := by omega
  have h13 : k+13 ≠ k+19 := by omega
  have h14 : k+14 ≠ k+19 := by omega
  have h15 : k+15 ≠ k+19 := by omega
  have h16 : k+16 ≠ k+19 := by omega
  have h17 : k+17 ≠ k+19 := by omega
  have h18 : k+18 ≠ k+19 := by omega
  simp only [rejected, realize, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    ↓reduceIte, Nat.add_zero, Nat.cast_add, Nat.cast_one] at hb
  linarith only [ha, hb]
private theorem rejected_law : ¬ arena.Law (rejected 0) := fun h => rejected_at 0 h
private theorem count_zero : a 0 = 0 := by
  unfold a
  decide +kernel
private theorem count_two_pos : 0 < a 2 := by
  unfold a
  unfold _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  apply Finset.card_pos.mpr
  refine ⟨(fun x => if x.2 = 0 then 0 else if x.1 = 4 then 0 else 1), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by decide +kernel⟩
def family : Registration arena (type_of% @result) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨result, rejected 0, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout (rejected 0) rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change a 0 ≠ a 2
    rw [count_zero]
    exact Nat.ne_of_lt count_two_pos

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.A229590Recurrence.auditUnit
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
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Polynomial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 14) (fun _ => ℤ)
def readout : Realization signature :=
  realize signature (fun _ _ j => (![-64,768,-3648,8336,-7472,-5464,18879,-14888,-816,9016,-6494,2200,-384,32] j : ℤ)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A :=
    (∀ p (d : Fin 2) (s : Fin 41 ⊕ Fin 41),
      (∑ r : Fin 5 → Fin 3, if cross p r ≤ d.val ∧
        cl (boundary r) (d.val - cross p r) = s then (1 : ℤ) else 0) = T (cl p d.val) s) ∧
    (∀ s : Fin 41 ⊕ Fin 41,
      (∑ r : Fin 5 → Fin 3, if cl (boundary r) 1 = s then (1 : ℤ) else 0) = initial s) ∧
    (T ^ (4+14)).mulVec terminal =
      ∑ j : Fin 14, A.readout () () j • (T ^ (4+j.val)).mulVec terminal
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h.2.2 (Sum.inl 0)
  simp only [rejected, realize, zero_smul, Finset.sum_const_zero, Pi.zero_apply] at hb
  rw [show 4+14 = (18 : Fin 19).val from rfl,
    _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers.powers_table] at hb
  change U 18 0 = 0 at hb
  exact (by decide +kernel : U 18 0 ≠ 0) hb
def family : Registration arena (type_of% @finite_certificate) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (-64 : ℤ) ≠ 768
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.A229590HardinA229590StripPolynomial.auditUnit
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
  readout := some (realize signature (fun _ _ j => (![-64,768,-3648,8336,-7472,-5464,18879,-14888,-816,9016,-6494,2200,-384,32] j : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Polynomial
end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip
