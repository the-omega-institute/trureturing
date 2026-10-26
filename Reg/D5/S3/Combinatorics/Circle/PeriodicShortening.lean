import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.PeriodicShortening
import Reg.Support.DependentFamily

/-! # Source-family attempt for the charged periodic transport -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.PeriodicShortening
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
open _root_.D5.S3.Combinatorics.Circle.PeriodicShortening

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := Fin k → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d w m : ℕ) (hd : 2 ≤ d) (_hw0 : 1 ≤ w)
    (_hw : w ≤ 2 ^ (d - 1) - 1) (hm : 2 ≤ m)
    (alpha : List (Fin d)) (beta : List (Fin (d + 1))),
    OriginalOrder d w alpha → OriginalOrder (d + 1) w beta →
    let k := d * m + 1
    let U := w * geom d m
    let f := R.readout () k U
    let L := chargedWord d m hm alpha beta
    let P := fun h => ((L.take h).map f).sum
    let D := modulus k / 2 - ((2 : ℤ) ^ (d - 1) - w) * (geom d (m - 1) : ℤ)
    L.Perm (List.finRange k) ∧ (L.map f).sum = 0 ∧ D < modulus k / 2 ∧
    (∀ i j : ℕ, P i - P j ≤ D) ∧
    ∃ ell : ℕ, ell < k ∧ (∀ h, P ell ≤ P h) ∧
      (L.rotate ell).Perm (List.finRange k) ∧ ((L.rotate ell).map f).sum = 0 ∧
      ∀ h : ℕ, (((L.rotate ell).take h).map f).sum ∈ Set.Icc (0 : ℤ) (modulus k / 2)

private theorem alpha_good : OriginalOrder 3 3 [0, 1, 2] := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := inStrip_prefix (f := actualSource 3 3) (B := 3) (h := 0)
    (l := [0, 1, 2]) (by norm_num [InStrip, actualSource, centered, modulus]) h
  simpa [modulus] using hh

private theorem beta_good : OriginalOrder 4 3 [0, 2, 1, 3] := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have hh := inStrip_prefix (f := actualSource 4 3) (B := 7) (h := 0)
    (l := [0, 2, 1, 3]) (by norm_num [InStrip, actualSource, centered, modulus]) h
  simpa [modulus] using hh

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 3 3 2 (by omega) (by omega) (by norm_num) (by omega)
    [0, 1, 2] [0, 2, 1, 3] alpha_good beta_good
  have hz := hh.2.1
  norm_num [rejected, realize, chargedWord, List.finRange_succ, earlyLabel, lastLabel] at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  intro he
  have hh := congrFun he (0 : Fin 3)
  norm_num [actual, realize, actualSource, centered, modulus] at hh

def source_registration : Registration arena (type_of% (@periodic_shortening_transport)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨periodic_shortening_transport, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- The source-family proof is complete; exact compiler source selection remains unbound. -/
def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.PeriodicShortening.periodic_shortening_transport)
    (type_of% (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e)))
    Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.PeriodicShortening.periodic_shortening_transport.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.PeriodicShortening.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k t => actualSource k t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit

end Reg.D5.S3.Combinatorics.Circle.PeriodicShortening
