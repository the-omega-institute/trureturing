import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.ExpandingSourcePath
open _root_.D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
open _root_.D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource

namespace Reg.D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource
noncomputable section

/-- Only the returned strip's weight operand varies; native hypotheses,
prefixes, total, legality and LARGE order keep the original source. -/
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
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ} (hk : 3 ≤ k) (t : ℕ)
    (hthree : (Finset.univ.filter (fun i : Fin k =>
      |actualSource k t i| < quarter k)).card = 3)
    (hsame : (∀ i : Fin k, |actualSource k t i| < quarter k → 0 ≤ actualSource k t i) ∨
      (∀ i : Fin k, |actualSource k t i| < quarter k → actualSource k t i ≤ 0)),
    ∃ L : List (Fin k),
      L.Perm (List.ofFn (fun q : Fin k => q)) ∧
      L.Nodup ∧ L.toFinset = Finset.univ ∧
      InStrip (R.readout () (k, t)) (half k) 0 L ∧
      (∀ n : ℕ, 0 ≤ mass (actualSource k t) (L.take n) ∧
        mass (actualSource k t) (L.take n) ≤ half k) ∧
      mass (actualSource k t) L = 0 ∧ Legal k t L ∧
      (L.filter (fun i => decide (quarter k ≤ |actualSource k t i|))).IsRotated
        ((List.finRange k).filter (fun i => decide (quarter k ≤ |actualSource k t i|)))

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hthree : (Finset.univ.filter (fun i : Fin 3 =>
      |actualSource 3 0 i| < quarter 3)).card = 3 := by decide
  have hsame : ∀ i : Fin 3, |actualSource 3 0 i| < quarter 3 →
      0 ≤ actualSource 3 0 i := by decide
  obtain ⟨word, hp, _, _, hs, _⟩ := h (by decide : 3 ≤ 3) 0 hthree (Or.inl hsame)
  have hmem : (0 : Fin 3) ∈ word := hp.mem_iff.mpr (List.mem_ofFn.mpr ⟨0, rfl⟩)
  change InStrip (fun _ : Fin 3 => (-1 : ℤ)) (half 3) 0 word at hs
  cases word with
  | nil => simpa using hmem
  | cons a tail =>
    have hh := (inStrip_prefix hs 1).1
    norm_num at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro r
  cases r
  refine ⟨(3, 1), 0, 1, ?_⟩
  change actualSource 3 1 (0 : Fin 3) ≠ actualSource 3 1 (1 : Fin 3)
  decide

def source_registration : Registration arena
    (type_of% (@actualSource_three_small_same_sign_full_completion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actualSource_three_small_same_sign_full_completion, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

def audit : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource.actualSource_three_small_same_sign_full_completion)
    (type_of% (realize signature (fun _ p i => actualSource p.1 p.2 i) (fun e => nomatch e)))
    Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource.actualSource_three_small_same_sign_full_completion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => actualSource p.1 p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "arg", "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end
end Reg.D5.S3.Combinatorics.Circle.ThreeSmallSameSignSource
