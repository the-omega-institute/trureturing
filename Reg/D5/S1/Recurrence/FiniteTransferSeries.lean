import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Recurrence.FiniteTransferSeries

/-! Source observations of the two pencils and both uses of the matrix-power series.
The series observations are the original partial applications `walks M`.
Each returns the full function of both endpoint vectors at the carrier universe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Recurrence.FiniteTransferSeries

open _root_.D5.S1.Recurrence.FiniteTransferSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open PowerSeries (C X coeff)

universe w

abbrev Inputs := Σ ι : Type w, Σ _ : Fintype ι, DecidableEq ι

inductive Role
  | polynomialPencil
  | seriesPencil
  | resolventWalks
  | adjugateWalks
  deriving DecidableEq

@[instance_reducible] private def finiteRole : Fintype Role where
  elems := ⟨[Role.polynomialPencil, .seriesPencil, .resolventWalks, .adjugateWalks], by simp⟩
  complete := by intro role; cases role <;> simp

abbrev signature : Signature where
  Params := Inputs.{w}
  State p := Matrix p.1 p.1 ℚ
  Role := Role
  finiteRole := finiteRole
  nonemptyRole := ⟨.polynomialPencil⟩
  Output role p := match role with
    | .polynomialPencil => Matrix p.1 p.1 (Polynomial ℚ)
    | .seriesPencil => Matrix p.1 p.1 (PowerSeries ℚ)
    | .resolventWalks | .adjugateWalks => (p.1 → ℚ) → (p.1 → ℚ) → PowerSeries ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

private noncomputable def observe : ∀ role p, signature.{w}.State p → signature.{w}.Output role p
  | .polynomialPencil, p, M =>
    letI := p.2.2
    1 - (Polynomial.X : Polynomial ℚ) • M.map (Polynomial.C (R := ℚ))
  | .seriesPencil, p, M =>
    letI := p.2.2
    1 - (X : PowerSeries ℚ) • M.map C
  | .resolventWalks, p, M => @walks p.1 p.2.1 p.2.2 M
  | .adjugateWalks, p, M => @walks p.1 p.2.1 p.2.2 M

noncomputable def actual : Realization signature.{w} :=
  realize signature observe (fun e => nomatch e)

private noncomputable def erased (changed : Role) : Realization signature.{w} :=
  realize signature
    (fun role p M => if role = changed then
      (match role with
        | .polynomialPencil => 0
        | .seriesPencil => 0
        | .resolventWalks => fun _ _ => 0
        | .adjugateWalks => fun _ _ => 0)
      else observe role p M)
    (fun e => nomatch e)

noncomputable def arena : Arena where
  signature := signature.{w}
  Law R := ∀ {ι : Type w} [fi : Fintype ι] [de : DecidableEq ι]
      (M : Matrix ι ι ℚ) (u v : ι → ℚ),
    let A := R.readout .polynomialPencil ⟨ι, fi, de⟩ M
    let B := R.readout .seriesPencil ⟨ι, fi, de⟩ M
    A.det.coeff 0 = 1 ∧
    R.readout .resolventWalks ⟨ι, fi, de⟩ M u v =
      X * dotProduct (C ∘ u) (B⁻¹.mulVec (C ∘ v)) ∧
    (A.det : PowerSeries ℚ) * R.readout .adjugateWalks ⟨ι, fi, de⟩ M u v =
      (↑((Polynomial.X : Polynomial ℚ) * dotProduct (Polynomial.C (R := ℚ) ∘ u)
        (A.adjugate.mulVec (Polynomial.C ∘ v))) : PowerSeries ℚ)

private abbrev Singleton := ULift.{w} Unit
private abbrev entry : Singleton.{w} := ⟨()⟩
private abbrev ones : Singleton.{w} → ℚ := fun _ => 1
private abbrev sample : Inputs.{w} := ⟨Singleton.{w}, inferInstance, inferInstance⟩

private theorem walks_zero_ne : walks (0 : Matrix Singleton.{w} Singleton.{w} ℚ) ones ones ≠ 0 := by
  intro h
  have hc := congrArg (coeff 1) h
  simp [walks, dotProduct, ones] at hc

private theorem erased_law (changed : Role) : ¬ arena.{w}.Law (erased changed) := by
  intro h
  let M : Matrix Singleton.{w} Singleton.{w} ℚ := 0
  have bad := h M ones ones
  have good := walks_resolvent M ones ones
  cases changed
  · have hz : (0 : Matrix Singleton.{w} Singleton.{w} (Polynomial ℚ)).det.coeff 0 = 1 :=
      bad.1
    simp at hz
  · have hz : walks M ones ones =
        X * dotProduct (C ∘ ones)
          ((0 : Matrix Singleton.{w} Singleton.{w} (PowerSeries ℚ))⁻¹.mulVec (C ∘ ones)) :=
      bad.2.1
    exact walks_zero_ne (by simpa [Matrix.inv_zero] using hz)
  · exact walks_zero_ne (good.2.1.trans bad.2.1.symm)
  · have hz := good.2.2.trans bad.2.2.symm
    exact walks_zero_ne (by
      change ((1 - (Polynomial.X : Polynomial ℚ) • M.map Polynomial.C :
        Matrix Singleton.{w} Singleton.{w} (Polynomial ℚ)).det : PowerSeries ℚ) *
        walks M ones ones = _ * (0 : PowerSeries ℚ) at hz
      simpa [M, Matrix.map_zero] using hz)

private theorem observed : ObservationalDependence signature.{w} actual := by
  intro role
  refine ⟨sample, 0, 1, ?_⟩
  intro h
  cases role
  · have hc := congrArg
      (fun A : Matrix Singleton.{w} Singleton.{w} (Polynomial ℚ) => (A entry entry).coeff 1) h
    simp [actual, realize, observe, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul] at hc
    linarith
  · have hc := congrArg
      (fun B : Matrix Singleton.{w} Singleton.{w} (PowerSeries ℚ) => coeff 1 (B entry entry)) h
    simp [actual, realize, observe, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul] at hc
    linarith
  all_goals
    have hc := congrArg (coeff 2) (congrFun (congrFun h ones) ones)
    simp [actual, realize, observe, walks, dotProduct, ones] at hc

noncomputable def source : Registration arena.{w} (type_of% (@walks_resolvent.{w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@walks_resolvent.{w}, erased .polynomialPencil, erased_law .polynomialPencil⟩
  sensitivity := by
    constructor
    · intro changed
      refine ⟨erased changed, ?_, rfl, erased_law changed⟩
      intro role h
      funext p M
      simp only [actual, erased, realize]
      split
      · rename_i equal
        exact (h equal).elim
      · rfl
    · intro e
      exact nomatch e
  dependence := observed

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
  readout := some (realize signature.{w} observe (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.FiniteTransferSeries
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "value"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg", "arg", "fn", "arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "value"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg", "arg", "fn", "arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "fn", "arg", "fn", "arg", "fn", "fn"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "arg", "fn", "arg", "arg", "fn", "fn"]
        stateBinder := 0
        functionOperand := false
        stateOperand := some #["arg"]
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.FiniteTransferSeries
