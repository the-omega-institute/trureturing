/-
   Faithful dependent-family registration attempt.
   The signed infinite parameter family, all natural states and both original
   count roles are retained. Finite states below witness only whole-law failure
   or actual variation. They do not replace the seven-clause Law.
   No declared_validated or new-helper source-binding claim is made.
   Source reconstruction/selection remains unfinished under issue 25856:
   https://github.com/the-omega-institute/trureturing/issues/25856 . -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket
import Reg.Support.DependentFamily

set_option autoImplicit false
namespace Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev logTwoSignature : Signature where
  Params := {p : ℤ // 5 ≤ p ∧ Odd p} × {q : ℤ // 3 ≤ q ∧ Odd q}
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def logTwoActual : Realization logTwoSignature :=
  realize logTwoSignature
    (fun i pq t => if i = 0 then (square_return_pair pq.1.1 pq.2.1 t).1
      else (square_return_pair pq.1.1 pq.2.1 t).2)
    (fun e => nomatch e)

noncomputable def logTwoKilled (i : Fin 2) : Realization logTwoSignature :=
  realize logTwoSignature
    (fun j pq t => if j = i then 0 else logTwoActual.readout j pq t)
    (fun e => nomatch e)

abbrev logTwoArena : Arena where
  signature := logTwoSignature
  Law R := ∀ (p q : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q),
    let pq : logTwoSignature.Params := ⟨⟨p,hp5,hpo⟩,⟨q,hq3,hqo⟩⟩
    let tG : ℝ := ((q : ℝ)^2-1)*(p : ℝ)/(4*(q : ℝ)*Real.log 2)+
      1/(2*(q : ℝ))-1/(2*(q : ℝ)*(p : ℝ))
    let tmin : ℕ := ((q+1)/2).toNat
    let tlate : ℕ := ((q*p+1)/2).toNat
    ∃! T : ℕ, tmin < T ∧
      (∀ t : ℕ, tmin ≤ t → t < T → R.readout 1 pq t < R.readout 0 pq t) ∧
      R.readout 0 pq T ≤ R.readout 1 pq T ∧
      (∀ t : ℕ, T < t → R.readout 0 pq t < R.readout 1 pq t) ∧
      T ≤ tlate ∧ tG < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil ((p : ℝ)*(q : ℝ)/(4*Real.log 2))

private theorem actual_law : logTwoArena.Law logTwoActual := by
  exact actual_square_displacement_log_two_bracket

private theorem killed_law (i : Fin 2) : ¬ logTwoArena.Law (logTwoKilled i) := by
  intro h
  obtain ⟨T,hT,_⟩ := h 5 3 (by norm_num) (by decide) (by norm_num) (by decide)
  fin_cases i
  · have hh := hT.2.1 2 (by norm_num) hT.1
    change (square_return_pair 5 3 2).2 < 0 at hh
    omega
  · have hh := hT.2.2.2.1 (T+1) (by omega)
    change (square_return_pair 5 3 (T+1)).1 < 0 at hh
    omega

/-- The original state-data supplier, evaluated at two actual admissible states. -/
private theorem actual_samples :
    (square_return_pair 5 3 2).1 = 2*(Nat.choose 55 30+Nat.choose 55 50) ∧
    (square_return_pair 5 3 2).2 = 4*Nat.choose 55 35 ∧
    (square_return_pair 5 3 3).1 = 2*(Nat.choose 85 45+Nat.choose 85 65) ∧
    (square_return_pair 5 3 3).2 = 4*Nat.choose 85 50 := by
  obtain ⟨n,a,r,hN,hna,hr,_,hWa,hWq⟩ :=
    _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket.state_data
      5 3 2 (by norm_num) (by decide) (by norm_num) (by decide) (by norm_num)
  have hn : n = 55 := by norm_num at hN; exact_mod_cast hN
  subst n
  have ha : a = 30 := by norm_num at hna; omega
  have hrr : r = 5 := by norm_num at hr; omega
  subst a
  subst r
  obtain ⟨n,a,r,hN,hna,hr,_,hWa',hWq'⟩ :=
    _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdBracket.state_data
      5 3 3 (by norm_num) (by decide) (by norm_num) (by decide) (by norm_num)
  have hn : n = 85 := by norm_num at hN; exact_mod_cast hN
  subst n
  have ha : a = 45 := by norm_num at hna; omega
  have hrr : r = 5 := by norm_num at hr; omega
  subst a
  subst r
  exact ⟨by simpa using hWa,by simpa using hWq,by simpa using hWa',by simpa using hWq'⟩

set_option maxRecDepth 10000 in
private theorem actual_dependence : ObservationalDependence logTwoSignature logTwoActual := by
  intro i
  let pq : logTwoSignature.Params := ⟨⟨5,by decide⟩,⟨3,by decide⟩⟩
  refine ⟨pq,2,3,?_⟩
  obtain ⟨hA,hB,hA',hB'⟩ := actual_samples
  fin_cases i
  · change (square_return_pair 5 3 2).1 ≠ (square_return_pair 5 3 3).1
    rw [hA,hA']
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 30 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 45 ≤ 85),
      Nat.choose_eq_factorial_div_factorial (by decide : 65 ≤ 85),Nat.factorial]
  · change (square_return_pair 5 3 2).2 ≠ (square_return_pair 5 3 3).2
    rw [hB,hB']
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 35 ≤ 55),
      Nat.choose_eq_factorial_div_factorial (by decide : 50 ≤ 85),Nat.factorial]

noncomputable def logTwoSource : Registration logTwoArena
    (type_of% actual_square_displacement_log_two_bracket) where
  actual := logTwoActual
  bridge := Iff.rfl
  variation := ⟨actual_law,logTwoKilled 0,killed_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨logTwoKilled i,?_,rfl,killed_law i⟩
      intro j hj
      funext pq t
      simp [logTwoKilled,realize,hj]
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def logTwoRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@actual_square_displacement_log_two_bracket)
      (Realization logTwoSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket.actual_square_displacement_log_two_bracket.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket.logTwoSource
  realizationSource := none
  generated := false
  arena := .source ⟨logTwoArena⟩
  objectArena := .source ⟨logTwoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logTwoArena ⟨logTwoSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize logTwoSignature
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

end Reg.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementLogTwoBracket
