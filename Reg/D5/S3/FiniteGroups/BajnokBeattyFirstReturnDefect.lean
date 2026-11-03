import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Complete original-telescope DependentFamily proof evidence.
The attempted outer Contract.Registration compiled, but scoped contract discovery
rejected returnRegistration with contract.discovery:rigid_universes.
The four-slot audit is UNFINISHED under CLAUDE 3.9, issue #24448:
https://github.com/the-omega-institute/trureturing/issues/24448
No declared_validated status is claimed by this proof-evidence module.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev returnSignature : Signature where
  Params := Σ _p : ℤ, ℤ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def returns19 (p t : ℤ) (l : ℕ) : ℕ :=
  let m : ℤ := 6*t-1
  let v1 : Plane := ![p*(m-1)/2,p*(m+1)/2]
  let v2 : Plane := ![p*(m-9)/2,-(p*(m+9)/2)]
  let K := Submodule.span ℤ (Set.range ![v1,v2])
  W K.mkQ.toAddMonoidHom l

noncomputable def returns33 (p t : ℤ) (l : ℕ) : ℕ :=
  let m : ℤ := 6*t-1
  let v1 : Plane := ![p*(m-3)/2,p*(m+3)/2]
  let v2 : Plane := ![p*(m-3)/2,-(p*(m+3)/2)]
  let K := Submodule.span ℤ (Set.range ![v1,v2])
  W K.mkQ.toAddMonoidHom l

noncomputable def actualReturn : Realization returnSignature :=
  realize returnSignature
    (fun i pt l => if i = 0 then returns19 pt.1 pt.2 l else returns33 pt.1 pt.2 l)
    (fun e => nomatch e)

noncomputable def rejectedReturn (i : Fin 2) : Realization returnSignature :=
  realize returnSignature
    (fun j pt l => if j = i then actualReturn.readout j pt l + 1 else actualReturn.readout j pt l)
    (fun e => nomatch e)

abbrev returnArena : Arena where
  signature := returnSignature
  Law R := ∀ (p t : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t),
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
    let n : ℕ := (p*(m-3)).toNat
    ∃ (e19 : G19 ≃+ H) (e33 : G33 ≃+ H),
      (∀ z : Plane, e19 (F19 z) =
        (((-z 0+z 1 : ℤ) : ZMod p.natAbs),
          ((-(3*t)*z 0+(3*t-1)*z 1 : ℤ) : ZMod (p*D).natAbs))) ∧
      (∀ z : Plane, e33 (F33 z) =
        (((t*z 0+(1-t)*z 1 : ℤ) : ZMod p.natAbs),
          ((-(3*t+1)*z 0+(3*t-2)*z 1 : ℤ) : ZMod (p*D).natAbs))) ∧
      (∀ l : ℕ, l < n → R.readout 0 ⟨p,t⟩ l = R.readout 1 ⟨p,t⟩ l) ∧
      R.readout 1 ⟨p,t⟩ n = R.readout 0 ⟨p,t⟩ n + 2

private theorem actual_law : returnArena.Law actualReturn := by
  exact first_return_defect

private theorem rejected_law (i : Fin 2) : ¬ returnArena.Law (rejectedReturn i) := by
  intro h
  obtain ⟨e19,e33,he19,he33,hshort,hdiff⟩ := h 3 2 (by norm_num) (by decide) (by norm_num)
  obtain ⟨_,_,_,_,_,hd⟩ := first_return_defect 3 2 (by norm_num) (by decide) (by norm_num)
  have hd' : returns33 3 2 24 = returns19 3 2 24 + 2 := hd
  fin_cases i
  · change returns33 3 2 24 = (returns19 3 2 24 + 1) + 2 at hdiff
    omega
  · change returns33 3 2 24 + 1 = returns19 3 2 24 + 2 at hdiff
    omega

private theorem two_returns {G : Type} [AddCommGroup G] (F : Plane →+ G) :
    2 ≤ W F 2 := by
  classical
  have hz : (![0, 0] : Plane) = 0 := by
    ext j
    fin_cases j <;> rfl
  let f : Fin 2 → ReturnWords F 2 := fun j =>
    ⟨if j = 0 then ![0,1] else ![1,0], by
      fin_cases j <;> simp [endpoint, Fin.sum_univ_two, step, hz]⟩
  have hi : Function.Injective f := by
    intro i j h
    have he := congrFun (congrArg Subtype.val h) 0
    fin_cases i <;> fin_cases j <;> simp [f] at he ⊢
  have : Finite (ReturnWords F 2) := by unfold ReturnWords; infer_instance
  simpa [W] using Nat.card_le_card_of_injective f hi

private theorem zero_returns {G : Type} [AddCommGroup G] (F : Plane →+ G) :
    W F 0 = 1 := by
  classical
  simp [W, ReturnWords, endpoint]

noncomputable def returnSource : Registration returnArena
    (type_of% first_return_defect) where
  actual := actualReturn
  bridge := Iff.rfl
  variation := ⟨actual_law,rejectedReturn 0,rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedReturn i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext pt l
      simp [rejectedReturn, realize, hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨3,2⟩, 0, 2, ?_⟩
    fin_cases i
    · change returns19 3 2 0 ≠ returns19 3 2 2
      have hz : returns19 3 2 0 = 1 := zero_returns _
      have ht : 2 ≤ returns19 3 2 2 := two_returns _
      omega
    · change returns33 3 2 0 ≠ returns33 3 2 2
      have hz : returns33 3 2 0 = 1 := zero_returns _
      have ht : 2 ≤ returns33 3 2 2 := two_returns _
      omega


end Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
