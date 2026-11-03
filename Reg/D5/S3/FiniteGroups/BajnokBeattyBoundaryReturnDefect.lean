import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Faithful full-telescope four-slot attempt for the first strict reversal.
The existing actual two-return observations and observational-dependence proof
are reused. Successful Lean compilation is proof evidence, not a claim that
the audit inspector validates the source reconstruction or scoped dependence.
The final even pre-wrap band uses its own admissible offset states and
within-band dependence witnesses at lengths 30 and 32.
The sourceSelection := none boundary is unfinished; see
https://github.com/the-omega-institute/trureturing/issues/25856 .
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



open _root_.D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev prewrapSignature : Signature where
  Params := {pt : (Σ _p : ℤ, ℤ) // 3 ≤ pt.1 ∧ Odd pt.1 ∧ 2 ≤ pt.2}
  State pt := {s : ℕ // 2*s < pt.1.1.toNat}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def prewrapActual : Realization prewrapSignature :=
  realize prewrapSignature
    (fun i pt s => actualReturn.readout i pt.1
      ((pt.1.1*((6*pt.1.2-1)-1)).toNat+2*s.1))
    (fun e => nomatch e)

noncomputable def prewrapRejected (i : Fin 2) : Realization prewrapSignature :=
  realize prewrapSignature
    (fun j pt s => if j = i then prewrapActual.readout j pt s + 1
      else prewrapActual.readout j pt s)
    (fun e => nomatch e)

abbrev prewrapArena : Arena where
  signature := prewrapSignature
  Law R := ∀ (p t : ℤ) (s : ℕ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) (hs : 2*s < p.toNat),
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
    let l : ℕ := L+2*s
    let pt : prewrapSignature.Params := ⟨⟨p,t⟩,hp3,hpo,ht⟩
    R.readout 0 pt ⟨s,hs⟩ =
        (Nat.choose l (l/2))^2 + 2*(Nat.choose l (4*P+s)*Nat.choose l s) ∧
    R.readout 1 pt ⟨s,hs⟩ =
        (Nat.choose l (l/2))^2 + 2*(Nat.choose l (P+s))^2 ∧
    R.readout 1 pt ⟨s,hs⟩ + 2*(Nat.choose l (4*P+s)*Nat.choose l s) =
      R.readout 0 pt ⟨s,hs⟩ + 2*(Nat.choose l (P+s))^2 ∧
    R.readout 1 pt ⟨s,hs⟩ < R.readout 0 pt ⟨s,hs⟩

private theorem prewrap_actual_law : prewrapArena.Law prewrapActual := by
  exact prewrap_return_reversal

private theorem prewrap_rejected_law (i : Fin 2) :
    ¬ prewrapArena.Law (prewrapRejected i) := by
  intro h
  have hh := h 3 2 0 (by norm_num) (by decide) (by norm_num) (by norm_num)
  have hd := prewrap_return_reversal 3 2 0
    (by norm_num) (by decide) (by norm_num) (by norm_num)
  fin_cases i
  · have bad := hh.1
    have good := hd.1
    change returns19 3 2 30 + 1 =
      (Nat.choose 30 15)^2 + 2*(Nat.choose 30 12*Nat.choose 30 0) at bad
    change returns19 3 2 30 =
      (Nat.choose 30 15)^2 + 2*(Nat.choose 30 12*Nat.choose 30 0) at good
    omega
  · have bad := hh.2.1
    have good := hd.2.1
    change returns33 3 2 30 + 1 =
      (Nat.choose 30 15)^2 + 2*(Nat.choose 30 3)^2 at bad
    change returns33 3 2 30 =
      (Nat.choose 30 15)^2 + 2*(Nat.choose 30 3)^2 at good
    omega

private theorem prewrap_actual_dependence :
    ObservationalDependence prewrapSignature prewrapActual := by
  intro i
  let pt : prewrapSignature.Params := ⟨⟨3,2⟩,by decide⟩
  refine ⟨pt, ⟨0,by decide⟩, ⟨1,by decide⟩, ?_⟩
  have h30 := prewrap_return_reversal 3 2 0
    (by norm_num) (by decide) (by norm_num) (by norm_num)
  have h32 := prewrap_return_reversal 3 2 1
    (by norm_num) (by decide) (by norm_num) (by norm_num)
  fin_cases i
  · change returns19 3 2 30 ≠ returns19 3 2 32
    have hc30 : returns19 3 2 30 =
        (Nat.choose 30 15)^2 + 2*(Nat.choose 30 12*Nat.choose 30 0) := h30.1
    have hc32 : returns19 3 2 32 =
        (Nat.choose 32 16)^2 + 2*(Nat.choose 32 13*Nat.choose 32 1) := h32.1
    rw [hc30,hc32]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 15 ≤ 30),
      Nat.choose_eq_factorial_div_factorial (by decide : 12 ≤ 30),
      Nat.choose_eq_factorial_div_factorial (by decide : 16 ≤ 32),
      Nat.choose_eq_factorial_div_factorial (by decide : 13 ≤ 32), Nat.factorial]
  · change returns33 3 2 30 ≠ returns33 3 2 32
    have hc30 : returns33 3 2 30 =
        (Nat.choose 30 15)^2 + 2*(Nat.choose 30 3)^2 := h30.2.1
    have hc32 : returns33 3 2 32 =
        (Nat.choose 32 16)^2 + 2*(Nat.choose 32 4)^2 := h32.2.1
    rw [hc30,hc32]
    norm_num [Nat.choose_eq_factorial_div_factorial (by decide : 15 ≤ 30),
      Nat.choose_eq_factorial_div_factorial (by decide : 3 ≤ 30),
      Nat.choose_eq_factorial_div_factorial (by decide : 16 ≤ 32),
      Nat.choose_eq_factorial_div_factorial (by decide : 4 ≤ 32), Nat.factorial]

noncomputable def prewrapSource : Registration prewrapArena
    (type_of% prewrap_return_reversal) where
  actual := prewrapActual
  bridge := Iff.rfl
  variation := ⟨prewrap_actual_law, prewrapRejected 0, prewrap_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨prewrapRejected i, ?_, rfl, prewrap_rejected_law i⟩
      intro j hj
      funext pt s
      simp [prewrapRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := prewrap_actual_dependence

noncomputable def prewrapRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@prewrap_return_reversal)
      (Realization prewrapSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect.prewrap_return_reversal.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect.prewrapSource
  realizationSource := none
  generated := false
  arena := .source ⟨prewrapArena⟩
  objectArena := .source ⟨prewrapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prewrapArena ⟨prewrapSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize prewrapSignature
    (fun i pt s => actualReturn.readout i pt.1
      ((pt.1.1*((6*pt.1.2-1)-1)).toNat+2*s.1))
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
