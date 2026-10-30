import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.NativeSeedChains
import Reg.Support.DependentFamily

/-! # Source-bound native-chain registration -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ExpandingSourcePath
open _root_.D5.S3.Combinatorics.Circle.NativeSeedChains

namespace Reg.D5.S3.Combinatorics.Circle.NativeSeedChains
noncomputable section
abbrev signature : Signature where
  Params := ℕ × ℕ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => actualSource p.1 p.2 i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℤ)) (fun e => nomatch e)

/-- The complete native law, varying only the dyadic weight operand. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k t : ℕ} (hk : 3 ≤ k)
    (hsmall : ∀ i : Fin k, |actualSource k t i| < quarter k →
      0 < actualSource k t i)
    (n : Fin k) (hn : actualSource k t n < 0),
    let a := phase (by omega) n 1
    ∃ r : ℕ,
      let root := phase (by omega) a r
      let neg := phase (by omega) a (r + 1)
      let next := phase (by omega) a (r + 2)
      let s := path (by omega) a r
      r + 2 ≤ k ∧ (s ++ [root, neg]).Nodup ∧
      0 < actualSource k t a ∧ actualSource k t a % 4 = 1 ∧
      (∀ j < r, 0 < actualSource k t (phase (by omega) a j) ∧
        actualSource k t (phase (by omega) a j) < quarter k) ∧
      Dyadic (R.readout () (k, t)) (actualSource k t a) s ∧
      actualSource k t root = (2 : ℤ) ^ r * actualSource k t a ∧
      quarter k ≤ actualSource k t root ∧ 3 * actualSource k t root ≤ modulus k ∧
      actualSource k t neg = 2 * actualSource k t root - modulus k ∧
      actualSource k t neg < 0 ∧
      actualSource k t next = 4 * actualSource k t root - modulus k ∧
      0 < actualSource k t next ∧ actualSource k t next % 4 = 1 ∧
      (s.map (actualSource k t)).sum = actualSource k t root - actualSource k t a ∧
      0 ≤ -actualSource k t neg - actualSource k t root ∧
      (s.map (actualSource k t)).sum -
        (-actualSource k t neg - actualSource k t root) =
          actualSource k t next - actualSource k t a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hsmall (i : Fin 4) : |actualSource 4 1 i| < quarter 4 →
      0 < actualSource 4 1 i := by
    fin_cases i <;> norm_num [actualSource, centered, modulus, quarter]
  have hn : actualSource 4 1 (3 : Fin 4) < 0 := by
    norm_num [actualSource, centered, modulus]
  obtain ⟨r, _, _, _, _, _, hd, _, hr, _⟩ := @hall 4 1 (by norm_num) hsmall 3 hn
  have hrne : r ≠ 0 := by
    intro hz
    subst r
    norm_num [phase, actualSource, centered, modulus, quarter] at hr
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrne
  rw [path, List.range_succ_eq_map, List.map_cons] at hd
  have hb := hd.1
  norm_num [rejected, realize, actualSource, centered, modulus, phase] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(3, 1), 0, 1, ?_⟩
  norm_num [actual, realize, actualSource, centered, modulus]

def family : Registration arena (type_of% (@native_chain_extraction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_chain_extraction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_chain_extraction) (type_of% actual) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.NativeSeedChains.native_chain_extraction.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.NativeSeedChains.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => actualSource p.1 p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.NativeSeedChains
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Circle.NativeSeedChains
