import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Recurrence.FiniteTransferSeries

/-! The first walks readout in the full finite-transfer resolvent statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Recurrence.FiniteTransferSeries

open _root_.D5.S1.Recurrence.FiniteTransferSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open PowerSeries (C X coeff)

universe w

abbrev Inputs := Σ ι : Type w, Σ _ : Fintype ι, Σ _ : DecidableEq ι,
  Σ _ : Matrix ι ι ℚ, (ι → ℚ)

abbrev signature : Signature where
  Params := Inputs.{w}
  State p := p.1 → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PowerSeries ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{w} :=
  realize signature (fun _ p u => @walks p.1 p.2.1 p.2.2.1 p.2.2.2.1 u p.2.2.2.2)
    (fun e => nomatch e)

noncomputable def erased : Realization signature.{w} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

noncomputable def arena : Arena where
  signature := signature.{w}
  Law R := ∀ {ι : Type w} [fi : Fintype ι] [de : DecidableEq ι]
      (M : Matrix ι ι ℚ) (u v : ι → ℚ),
    let A : Matrix ι ι (Polynomial ℚ) :=
      1 - (Polynomial.X : Polynomial ℚ) • M.map (Polynomial.C (R := ℚ))
    let B : Matrix ι ι (PowerSeries ℚ) := 1 - (X : PowerSeries ℚ) • M.map C
    A.det.coeff 0 = 1 ∧
    R.readout () ⟨ι, fi, de, M, v⟩ u = X * dotProduct (C ∘ u) (B⁻¹.mulVec (C ∘ v)) ∧
    (A.det : PowerSeries ℚ) * walks M u v =
      (↑((Polynomial.X : Polynomial ℚ) * dotProduct (Polynomial.C (R := ℚ) ∘ u)
        (A.adjugate.mulVec (Polynomial.C ∘ v))) : PowerSeries ℚ)

private abbrev Singleton := ULift.{w} Unit

private theorem one_coeff (a : ℚ) :
    coeff 1 (walks (0 : Matrix Singleton.{w} Singleton.{w} ℚ) (fun _ => a) (fun _ => 1)) =
      a := by
  simp [walks, dotProduct]

private theorem erased_law : ¬ arena.{w}.Law erased := by
  intro h
  let M : Matrix Singleton.{w} Singleton.{w} ℚ := 0
  let u : Singleton.{w} → ℚ := fun _ => 1
  let v : Singleton.{w} → ℚ := fun _ => 1
  have bad := (h M u v).2.1
  have good := (walks_resolvent M u v).2.1
  have impossible : walks M u v = 0 := good.trans bad.symm
  have hc := congrArg (coeff 1) impossible
  have hc' : (1 : ℚ) = 0 := by
    simpa only [M, u, v, one_coeff, map_zero] using hc
  exact one_ne_zero hc'

noncomputable def source : Registration arena.{w} (type_of% (@walks_resolvent.{w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@walks_resolvent.{w}, erased, erased_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Singleton.{w}, inferInstance, inferInstance, 0, fun _ => 1⟩,
      (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have hc := congrArg (coeff 1) h
    have hc' : (0 : ℚ) = 1 := by
      simpa only [actual, realize, signature, one_coeff] using hc
    exact zero_ne_one hc'

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@walks_resolvent.{w}) (Realization signature.{w}) Unit Unit where
  unitName := `D5.S1.Recurrence.FiniteTransferSeries.walks_resolvent.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.FiniteTransferSeries.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{w}⟩
  objectArena := .source ⟨arena.{w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{w} ⟨source.{w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{w}
    (fun _ p u => @walks p.1 p.2.1 p.2.2.1 p.2.2.2.1 u p.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.FiniteTransferSeries
    definition := none
    coordinates := #[0, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.FiniteTransferSeries
