import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement
import Reg.Support.SingleDependentReadout

/-! Source binding for the looplessness premise in the stabilization conjecture. -/

namespace Reg.D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement

open _root_.D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ)
    (fun p => Matrix (Fin p.2) (Fin p.1) ℤ) (fun _ => Bool)

private def actual : Realization signature :=
  realize signature (fun _ _ M => @decide (HasLoops M) (Classical.propDecidable _)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

/-- Vary the loop premise at its occurrence in the full stabilization claim. -/
private abbrev arena : Arena where
  signature := signature
  Law R := ¬ (∀ r : ℕ, 0 < r →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ M : Matrix (Fin m) (Fin r) ℤ,
        (∀ i : Fin m, ∃ j : Fin r, M i j ≠ 0) →
        ¬ IsBipartite M → ¬ (R.readout () ⟨r, m⟩ M = true) → chromaticNumber M = 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  exact fun _ _ => ⟨0, fun _ _ _ _ _ hloop => (hloop rfl).elim⟩

private theorem loop_readout_dependence : ObservationalDependence signature actual := by
  intro i
  let I : Matrix (Fin 1) (Fin 1) ℤ := 1
  let Z : Matrix (Fin 1) (Fin 1) ℤ := 0
  refine ⟨⟨1, 1⟩, I, Z, ?_⟩
  have hI : HasLoops I := by
    refine ⟨0, Or.inl ?_⟩
    have hm : Pi.single (0 : Fin 1) 1 ∈ relations I :=
      ⟨Pi.single 0 1, by simp [I]⟩
    rw [← QuotientAddGroup.ker_mk' (relations I)] at hm
    exact hm.symm
  have hZ : ¬ HasLoops Z := by
    rintro ⟨j, hj | hj⟩
    all_goals
      have hzero : QuotientAddGroup.mk' (relations Z) (Pi.single j 1) = 0 := by
        first | exact hj.symm | exact neg_eq_zero.mp hj.symm
      have hm : Pi.single j (1 : ℤ) ∈ relations Z := by
        rw [← QuotientAddGroup.ker_mk' (relations Z)]
        exact hzero
      obtain ⟨a, ha⟩ : ∃ a, Z.mulVecLin a = Pi.single j 1 := hm
      simpa [Z, Matrix.mulVecLin_apply] using congrFun ha j

  simp [actual, realize, hI, hZ]

def sourceRegistration : Registration arena (¬ claim) where
  actual := actual
  bridge := by simp [arena, actual, realize, claim]
  variation := ⟨by simpa [arena, actual, realize, claim] using result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := loop_readout_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => @decide (HasLoops M) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement
    definition := some {
      owner := `D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement
      name := `D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement.claim
      path := #["arg"] }
    coordinates := #[0, 3]
    readouts := #[{
      path := #["arg", "body", "body", "arg", "body", "body", "body", "body",
        "body", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Coloring.KrebsC12Settlement
