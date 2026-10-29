import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FactorialRatio.DyadicBinomialCancellation
import Reg.Support.DependentFamily

/-! # Dependent-family audit of the all-index reduced-fraction formula

The kernel-checked family proof below is an attempted registration, not a
validated escape audit. The tuple readout has no literal source occurrence;
lawful source selection and complete source reconstruction remain missing.
See https://github.com/the-omega-institute/trureturing/issues/23314.
-/

namespace Reg.D5.S3.Arith.FactorialRatio.DyadicBinomialCancellation

open _root_.D5.S3.Arith.FactorialRatio.DyadicBinomialCancellation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ × ℕ × ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => ((g n).num, (f n / g n).den, (f n / g n).num))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    let m := n - n / 2
    let B := n.choose (n / 2)
    let v := B.factorization 2
    let b := B / 2 ^ v
    let G := (2 ^ n - B) / 2 ^ v
    R.readout () () n = ((G : ℤ), G / Nat.gcd m G,
      ((m * b / Nat.gcd m G : ℕ) : ℤ))

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0, 0)) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide)
  norm_num [rejected, realize, Nat.choose] at hh
  have h0 := congrArg Prod.fst hh
  norm_num at h0

def registration : Registration arena (type_of% @denominator_formula) where
  actual := actual
  bridge := by
    simp only [actual, realize, Prod.mk.injEq]
  variation := ⟨(by
    intro n hn
    simpa [actual, realize] using denominator_formula n hn), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), 1, 3, ?_⟩
    change ((g 1).num, (f 1 / g 1).den, (f 1 / g 1).num) ≠
      ((g 3).num, (f 3 / g 3).den, (f 3 / g 3).num)
    have hg1 : (g 1).num = 1 := by norm_num [g]
    have hg3 : (g 3).num = 5 := by
      have hq : g 3 = (5 : ℚ) / 4 := by norm_num [g, Nat.choose]
      rw [hq]
      exact Rat.num_div_eq_of_coprime (by norm_num) (by decide)
    intro h
    have hh := congrArg Prod.fst h
    rw [hg1, hg3] at hh
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@denominator_formula) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.FactorialRatio.DyadicBinomialCancellation.denominator_formula.audit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.DyadicBinomialCancellation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => ((g n).num, (f n / g n).den, (f n / g n).num))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.FactorialRatio.DyadicBinomialCancellation
