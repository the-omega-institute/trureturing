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

/- Source audit for the existing coordinate supplier's public exposure.
The Law retains its complete integer/vector telescope and original hypotheses.
Exact source occurrence binding remains unfinished under issue #25856. -/

structure CoordinateParameters where
  p : ℤ
  D : ℤ
  x : ℤ
  y : ℤ
  u : ℤ
  v : ℤ
  alpha : ℤ
  beta : ℤ
  v1 : Plane
  v2 : Plane

abbrev coordinateSignature : Signature where
  Params := CoordinateParameters
  State _ := Plane
  Role := Fin 1
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := ZMod d.p.natAbs × ZMod (d.p*d.D).natAbs
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def coordinateActual : Realization coordinateSignature :=
  realize coordinateSignature
    (fun _ d z =>
      (((d.alpha*z 0+d.beta*z 1 : ℤ) : ZMod d.p.natAbs),
        ((-d.y*z 0+d.x*z 1 : ℤ) : ZMod (d.p*d.D).natAbs)))
    (fun e => nomatch e)

noncomputable def coordinateRejected (i : Fin 1) : Realization coordinateSignature :=
  realize coordinateSignature
    (fun j d z => if j = i then 0 else coordinateActual.readout j d z)
    (fun e => nomatch e)

abbrev coordinateArena : Arena where
  signature := coordinateSignature
  Law R := ∀ (p D x y u v alpha beta : ℤ) (v1 v2 : Plane),
    0 < p → 0 < D → alpha*x+beta*y = 1 → x*v-y*u = -D →
    v1 = ![p*x, p*y] → v2 = ![p*u, p*v] →
    (Nat.card (Plane ⧸ Submodule.span ℤ (Set.range ![v1, v2])) : ℤ) = p^2*D →
    let K : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1, v2])
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    ∃ e : (Plane ⧸ K) ≃+ H, ∀ z : Plane,
      e (K.mkQ z) = R.readout 0 ⟨p,D,x,y,u,v,alpha,beta,v1,v2⟩ z

private theorem coordinate_actual_law : coordinateArena.Law coordinateActual := by
  exact same_group_coordinate_descent

private theorem coordinate_rejected_zero : ¬ coordinateArena.Law (coordinateRejected 0) := by
  intro h
  let K : Submodule ℤ Plane := Submodule.span ℤ
    (Set.range ![(![15,18] : Plane), (![3,-30] : Plane)])
  have hcard : (Nat.card (Plane ⧸ K) : ℤ) = (3 : ℤ)^2*56 := by
    obtain ⟨_hf, _hn, hc, _hcount, _hcov, _hncov, _hdiam⟩ :=
      _root_.D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth.asymmetric_quotient_growth
        3 11 1 9 (by norm_num) (by decide) (by decide)
        (by decide) (by decide) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    convert hc using 1 <;> norm_num [K]
  obtain ⟨e, he⟩ := h 3 56 5 6 1 (-10) (-1) 1 ![15,18] ![3,-30]
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hcard
  let H := ZMod ((3 : ℤ).natAbs) × ZMod ((3*56 : ℤ).natAbs)
  have hzero (g : H) : g = 0 := by
    obtain ⟨a, ha⟩ := e.surjective g
    obtain ⟨z, hz⟩ := (Submodule.mkQ_surjective K) a
    have hw := he z
    simp only [coordinateRejected, realize, ite_true] at hw
    change e (K.mkQ z) = 0 at hw
    rw [hz, ha] at hw
    exact hw
  have hbad : (1 : ZMod 3) = 0 := congrArg Prod.fst (hzero (1,0))
  exact (one_ne_zero : (1 : ZMod 3) ≠ 0) hbad

private theorem coordinate_rejected_law (i : Fin 1) :
    ¬ coordinateArena.Law (coordinateRejected i) := by
  have hi : i = 0 := Fin.eq_zero i
  simpa only [hi] using coordinate_rejected_zero

private def coordinateWitness : CoordinateParameters :=
  ⟨3,56,5,6,1,-10,-1,1,![15,18],![3,-30]⟩

private theorem coordinate_actual_dependence :
    ObservationalDependence coordinateSignature coordinateActual := by
  intro i
  refine ⟨coordinateWitness, 0, ![1,0], ?_⟩
  intro he
  have h := congrArg Prod.fst he
  change (0 : ZMod 3) = -1 at h
  exact (by decide : (0 : ZMod 3) ≠ -1) h

noncomputable def coordinateSource : Registration coordinateArena
    (type_of% (@same_group_coordinate_descent)) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨coordinate_actual_law, coordinateRejected 0, coordinate_rejected_zero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coordinateRejected i, ?_, rfl, coordinate_rejected_law i⟩
      intro j hj
      funext d z
      simp [coordinateRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := coordinate_actual_dependence

noncomputable def coordinateRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@same_group_coordinate_descent)
      (Realization coordinateSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth.same_group_coordinate_descent.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth.coordinateSource
  realizationSource := none
  generated := false
  arena := .source ⟨coordinateArena⟩
  objectArena := .source ⟨coordinateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coordinateArena ⟨coordinateSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some coordinateActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth
