import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle
import Reg.Support.DependentFamily

/-! Source-bound registration for the native adjacent-depth physical cycle. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ExpandingSourcePath
open _root_.D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle

namespace Reg.D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle
noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

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
  realize signature
    (fun _ p i => if i.val = 0 then -quarter p.1 else 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k t : ℕ} (hk : 3 ≤ k)
    (hsmall : ∀ i : Fin k, |R.readout () (k, t) i| < quarter k →
      0 < R.readout () (k, t) i)
    (n : Fin k) (hn : R.readout () (k, t) n < 0),
    ∃ (a root neg next : Fin k) (r : ℕ),
      r + 2 ≤ k ∧ root = phase (by omega) a r ∧
        quarter k ≤ R.readout () (k, t) root ∧
        (2 ≤ r → ∃ h : ℕ,
        1 ≤ h ∧ r = h + 1 ∧
          root = phase (by omega) a r ∧
          neg = phase (by omega) a (r + 1) ∧
          next = phase (by omega) a (r + 2) ∧
          0 < R.readout () (k, t) a ∧
          R.readout () (k, t) root = (2 : ℤ) ^ r * R.readout () (k, t) a ∧
          quarter k ≤ R.readout () (k, t) root ∧
          3 * R.readout () (k, t) root ≤ modulus k ∧
          R.readout () (k, t) neg = 2 * R.readout () (k, t) root - modulus k ∧
          R.readout () (k, t) neg < 0 ∧
          R.readout () (k, t) next = 4 * R.readout () (k, t) root - modulus k ∧
          0 < R.readout () (k, t) next ∧
          (∃ e : Equiv.Perm (Fin k),
            (e root = next ∧ e neg = root ∧ e next = neg ∧
              e.symm root = neg ∧ e.symm neg = next ∧ e.symm next = root)) ∧
          (let N := modulus k
           let U := fun z : ℤ => z + if z < 0 then N else 0
           U (R.readout () (k, t) neg) - U (R.readout () (k, t) root) =
             R.readout () (k, t) root ∧
           U (R.readout () (k, t) next) - U (R.readout () (k, t) neg) =
             R.readout () (k, t) neg))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hsmall : ∀ i : Fin 3,
      |rejected.readout () (3, 1) i| < quarter 3 →
        0 < rejected.readout () (3, 1) i := by
    intro i hi
    fin_cases i
    · norm_num [rejected, realize, quarter] at hi
    · norm_num [rejected, realize, quarter]
    · norm_num [rejected, realize, quarter]
  have hn : rejected.readout () (3, 1) (0 : Fin 3) < 0 := by
    norm_num [rejected, realize, quarter]
  obtain ⟨a, root, neg, next, r, _, _, hrootQ, _⟩ :=
    hall (k := 3) (t := 1) (by norm_num) hsmall 0 hn
  fin_cases root <;> norm_num [rejected, realize, quarter] at hrootQ

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(3, 1), 0, 1, ?_⟩
  change actualSource 3 1 (0 : Fin 3) ≠ actualSource 3 1 (1 : Fin 3)
  decide

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle.native_long_seed_three_cycle)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle.native_long_seed_three_cycle,
    rejected, rejected_law⟩
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
    (@_root_.D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle.native_long_seed_three_cycle)
    (type_of% actual) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle.native_long_seed_three_cycle.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms audit

end
end Reg.D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle
