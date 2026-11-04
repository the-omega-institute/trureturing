/- Dependent-family registration for the complete original
all-odd-p,q actual-count theorem. This is not declared_validated.
issue25856: https://github.com/the-omega-institute/trureturing/issues/25856
The full source-selection coordinates, exact occurrence reconstruction and
State=Nat source tie remain unencoded/unverified. No judge change is proposed.
The native zero interventions below preserve all other readout families.
The Law includes uniqueness, the original lower guard and the late upper bound.
No threshold or count/sign premise is supplied as an input. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
import Reg.Support.DependentFamily

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev squareCrossingSignature : Signature where
  Params := {p : ℤ // 3 ≤ p ∧ Odd p} × {q : ℤ // 3 ≤ q ∧ Odd q}
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def squareCrossingActual : Realization squareCrossingSignature :=
  realize squareCrossingSignature
    (fun i pq t => if i = 0 then (square_return_pair pq.1.1 pq.2.1 t).1
      else (square_return_pair pq.1.1 pq.2.1 t).2)
    (fun e => nomatch e)

noncomputable def squareCrossingKilled (i : Fin 2) :
    Realization squareCrossingSignature :=
  realize squareCrossingSignature
    (fun j pq t => if j = i then 0 else squareCrossingActual.readout j pq t)
    (fun e => nomatch e)

abbrev squareCrossingArena : Arena where
  signature := squareCrossingSignature
  Law R := ∀ (p q : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q),
    let pq : squareCrossingSignature.Params := ⟨⟨p,hp3,hpo⟩,⟨q,hq3,hqo⟩⟩
    let tmin : ℕ := ((q+1)/2).toNat
    let tlate : ℕ := ((q*p+1)/2).toNat
    ∃! T : ℕ, tmin < T ∧
      (∀ t : ℕ, tmin ≤ t → t < T → R.readout 1 pq t < R.readout 0 pq t) ∧
      R.readout 0 pq T ≤ R.readout 1 pq T ∧
      (∀ t : ℕ, T < t → R.readout 0 pq t < R.readout 1 pq t) ∧ T ≤ tlate

private theorem squareCrossing_actual_law : squareCrossingArena.Law squareCrossingActual := by
  exact actual_square_displacement_single_crossing

private theorem squareCrossing_killed_law (i : Fin 2) :
    ¬ squareCrossingArena.Law (squareCrossingKilled i) := by
  intro h
  obtain ⟨T,hT,_⟩ := h 3 3 (by norm_num) (by decide) (by norm_num) (by decide)
  fin_cases i
  · have hh := hT.2.1 2 (by norm_num) hT.1
    change (square_return_pair 3 3 2).2 < 0 at hh
    omega
  · have hh := hT.2.2.2.1 (T+1) (by omega)
    change (square_return_pair 3 3 (T+1)).1 < 0 at hh
    omega

set_option maxRecDepth 10000 in
private theorem squareCrossing_dependence :
    ObservationalDependence squareCrossingSignature squareCrossingActual := by
  intro i
  let pq : squareCrossingSignature.Params := ⟨⟨3,by decide⟩,⟨3,by decide⟩⟩
  refine ⟨pq,2,3,?_⟩
  have h33 := actual_odd_wrap_counts 3 2 (by norm_num) (by decide) (by norm_num)
  have h51 := actual_odd_wrap_counts 3 3 (by norm_num) (by decide) (by norm_num)
  fin_cases i
  · change (original_return_pair 3 2).1 ≠ (original_return_pair 3 3).1
    have hc33 : (original_return_pair 3 2).1 =
        2*(Nat.choose 33 18+Nat.choose 33 30) := h33.1
    have hc51 : (original_return_pair 3 3).1 =
        2*(Nat.choose 51 27+Nat.choose 51 39) := h51.1
    rw [hc33,hc51]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 18 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 27 ≤ 51),
      Nat.choose_eq_factorial_div_factorial (by decide : 39 ≤ 51),Nat.factorial]
  · change (original_return_pair 3 2).2 ≠ (original_return_pair 3 3).2
    have hc33 : (original_return_pair 3 2).2 = 4*Nat.choose 33 21 := h33.2
    have hc51 : (original_return_pair 3 3).2 = 4*Nat.choose 51 30 := h51.2
    rw [hc33,hc51]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 21 ≤ 33),
      Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 51),Nat.factorial]

noncomputable def squareCrossingSource : Registration squareCrossingArena
    (type_of% actual_square_displacement_single_crossing) where
  actual := squareCrossingActual
  bridge := Iff.rfl
  variation := ⟨squareCrossing_actual_law,squareCrossingKilled 0,squareCrossing_killed_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨squareCrossingKilled i,?_,rfl,squareCrossing_killed_law i⟩
      intro j hj
      funext pq t
      simp [squareCrossingKilled,realize,hj]
    · intro e
      exact nomatch e
  dependence := squareCrossing_dependence

noncomputable def squareCrossingRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@actual_square_displacement_single_crossing)
      (Realization squareCrossingSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing.actual_square_displacement_single_crossing.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing.squareCrossingSource
  realizationSource := none
  generated := false
  arena := .source ⟨squareCrossingArena⟩
  objectArena := .source ⟨squareCrossingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareCrossingArena ⟨squareCrossingSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize squareCrossingSignature
    (fun i pq t => if i = 0 then (square_return_pair pq.1.1 pq.2.1 t).1
      else (square_return_pair pq.1.1 pq.2.1 t).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
