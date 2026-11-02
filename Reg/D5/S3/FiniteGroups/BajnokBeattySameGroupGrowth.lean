import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth
import Reg.Support.DependentFamily

set_option maxRecDepth 4000

namespace Reg.D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth

open _root_.D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth
open _root_.D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev growthSignature : Signature where
  Params := Σ _p : ℤ, ℤ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def growth19 (p t : ℤ) (r : ℕ) : ℕ :=
    let m : ℤ := 6*t-1
    let D : ℤ := (m^2-9)/2
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v133, v233])
    let G19 := Plane ⧸ K19
    let G33 := Plane ⧸ K33
    let F19 : Plane →+ G19 := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ G33 := K33.mkQ.toAddMonoidHom
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let f19 : (ℤ × ℤ) →+ G19 := F19.comp E.symm.toLinearMap.toAddMonoidHom
    let f33 : (ℤ × ℤ) →+ G33 := F33.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    ((leeDiamond r).image f19).card

noncomputable def growth33 (p t : ℤ) (r : ℕ) : ℕ :=
    let m : ℤ := 6*t-1
    let D : ℤ := (m^2-9)/2
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v133, v233])
    let G19 := Plane ⧸ K19
    let G33 := Plane ⧸ K33
    let F19 : Plane →+ G19 := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ G33 := K33.mkQ.toAddMonoidHom
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let f19 : (ℤ × ℤ) →+ G19 := F19.comp E.symm.toLinearMap.toAddMonoidHom
    let f33 : (ℤ × ℤ) →+ G33 := F33.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    ((leeDiamond r).image f33).card

noncomputable def actualGrowth : Realization growthSignature :=
  realize growthSignature
    (fun i pt r => if i = 0 then growth19 pt.1 pt.2 r else growth33 pt.1 pt.2 r)
    (fun e => nomatch e)

noncomputable def rejectedGrowth (i : Fin 2) : Realization growthSignature :=
  realize growthSignature
    (fun j pt r => if j = i then 0 else actualGrowth.readout j pt r)
    (fun e => nomatch e)

abbrev growthArena : Arena where
  signature := growthSignature
  Law R := ∀ (p t : ℤ) (_hp3 : 3 ≤ p) (_hpo : Odd p) (_ht : 2 ≤ t),
    let m : ℤ := 6*t-1
    let D : ℤ := (m^2-9)/2
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v133, v233])
    let G19 := Plane ⧸ K19
    let G33 := Plane ⧸ K33
    let F19 : Plane →+ G19 := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ G33 := K33.mkQ.toAddMonoidHom
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let f19 : (ℤ × ℤ) →+ G19 := F19.comp E.symm.toLinearMap.toAddMonoidHom
    let f33 : (ℤ × ℤ) →+ G33 := F33.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    let c19 : ℕ → ℕ := fun r => R.readout 0 ⟨p,t⟩ r
    let c33 : ℕ → ℕ := fun r => R.readout 1 ⟨p,t⟩ r
    let gap : ℕ → ℤ := fun r => (c19 r : ℤ)-(c33 r : ℤ)
    ∃ (e19 : G19 ≃+ H) (e33 : G33 ≃+ H),
      (∀ z : Plane, e19 (F19 z) =
        (((-z 0+z 1 : ℤ) : ZMod p.natAbs),
          ((-(3*t)*z 0+(3*t-1)*z 1 : ℤ) : ZMod (p*D).natAbs))) ∧
      (∀ z : Plane, e33 (F33 z) =
        (((t*z 0+(1-t)*z 1 : ℤ) : ZMod p.natAbs),
          ((-(3*t+1)*z 0+(3*t-2)*z 1 : ℤ) : ZMod (p*D).natAbs))) ∧
      ¬ IsAddCyclic H ∧
      (∀ R : ℕ, LeeCovers F19 (R : ℤ) ↔ s ≤ R) ∧
      (∀ R : ℕ, LeeCovers F33 (R : ℤ) ↔ s ≤ R) ∧
      (∀ r : ℕ, c33 r ≤ c19 r ∧
        (c33 r < c19 r ↔ p*(m-3)/2 ≤ (r : ℤ) ∧ r < s)) ∧
      (∀ r : ℕ, s ≤ r →
        (c19 r : ℤ) = p^2*D ∧ (c33 r : ℤ) = p^2*D) ∧
      (∀ r : ℕ, gap r ≤ 2*p^2-2*p+1) ∧
      (∀ r : ℕ, gap r = 2*p^2-2*p+1 ↔
        (r : ℤ) = p*(m-1)/2-1) ∧
      (∃! r : ℕ, gap r = 2*p^2-2*p+1) ∧
      (((leeDiamond (s-1)).image f19).card : ℤ) -
        (((leeDiamond (s-1)).image f33).card : ℤ) = 4*p ∧
      ¬ ∃ q : G19 ≃+ G33,
        q (F19 ![1, 0]) = F33 ![1, 0] ∧
        q (F19 ![0, 1]) = F33 ![0, 1]

private theorem rejected_law (i : Fin 2) :
    ¬ growthArena.Law (rejectedGrowth i) := by
  intro h
  obtain ⟨e19, e33, he19, he33, hn, hd19, hd33, ho, hfull, rest⟩ :=
    h 3 2 (by norm_num) (by decide) (by norm_num)
  have hb := hfull 16 (by norm_num)
  fin_cases i
  · have hb0 := hb.1
    norm_num [rejectedGrowth, realize] at hb0
  · have hb1 := hb.2
    norm_num [rejectedGrowth, realize] at hb1

private theorem actual_law : growthArena.Law actualGrowth := by
  exact same_group_different_growth

noncomputable def growthSource : Registration growthArena
    (type_of% same_group_different_growth) where
  actual := actualGrowth
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedGrowth 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedGrowth i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext pt r
      simp [rejectedGrowth, realize, hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨e19, e33, he19, he33, hn, hd19, hd33, ho, hfull, rest⟩ :=
      same_group_different_growth 3 2 (by norm_num) (by decide) (by norm_num)
    have hb := hfull 16 (by norm_num)
    norm_num only at hb
    refine ⟨⟨3,2⟩, 0, 16, ?_⟩
    fin_cases i
    · simp [actualGrowth, realize]
      have hz : growth19 3 2 0 = 1 := by simp [growth19, leeDiamond, Finset.filter_singleton]
      have hs : growth19 3 2 16 = 504 := by exact_mod_cast hb.1
      rw [hz, hs]
      norm_num
    · simp [actualGrowth, realize]
      have hz : growth33 3 2 0 = 1 := by simp [growth33, leeDiamond, Finset.filter_singleton]
      have hs : growth33 3 2 16 = 504 := by exact_mod_cast hb.2
      rw [hz, hs]
      norm_num

noncomputable def growthRegistration :
    Contract.Registration same_group_different_growth
      (Realization growthSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth.same_group_different_growth.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth.growthSource
  realizationSource := none
  generated := false
  arena := .source ⟨growthArena⟩
  objectArena := .source ⟨growthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source growthArena ⟨growthSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize growthSignature
    (fun i pt r => if i = 0 then growth19 pt.1 pt.2 r else growth33 pt.1 pt.2 r)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
        stateBinder := 0, functionOperand := true,
        stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
        stateBinder := 0, functionOperand := true,
        stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth
