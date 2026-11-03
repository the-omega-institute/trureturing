import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition
import Reg.Support.DependentFamily

/-! Source-bound audit of the homogeneous Nambu Kahan--Cremona factorization. -/

namespace Reg.D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition

open _root_.D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Σ _A : Matrix (Fin 3) (Fin 3) ℝ, Σ _B : Matrix (Fin 3) (Fin 3) ℝ, ℝ
  State _p := Fin 4 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p X => kahan p.1 p.2.1 p.2.2 X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ A B : Matrix (Fin 3) (Fin 3) ℝ, A.PosDef → B.PosDef →
      (∀ t : ℝ, 2 ≤ (B - t • A).rank) →
        ∀ h : ℝ, 0 < h →
          ∃ l₁ l₂ : Matrix (Fin 4) (Fin 4) ℂ,
            IsUnit l₁.det ∧ IsUnit l₂.det ∧
              ∀ X : Fin 4 → ℂ,
                R.readout () ⟨A, ⟨B, h⟩⟩ X = l₂ *ᵥ cremona (l₁ *ᵥ X)) ∧
    (∀ (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) (X : Fin 4 → ℂ),
      R.readout () ⟨A, ⟨B, h⟩⟩ X = kahan A B h X)

def zeroInput : Fin 4 → ℂ := fun _ => 1

private theorem zero_kahan_ne_zero :
    kahan (0 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 zeroInput ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [Fin.snoc_castSucc, kahan, kahanMatrix, nambuLinearPart, zeroInput] using h0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.2 (0 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 zeroInput
  apply zero_kahan_ne_zero
  simpa [rejected, realize] using hbad.symm

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, ⟨0, 0⟩⟩, zeroInput, (fun _ => 0), ?_⟩
  intro he
  have h0 := congrFun he 0
  simpa [Fin.snoc_castSucc, actual, realize, zeroInput, kahan, kahanMatrix,
    nambuLinearPart] using h0

theorem actual_law : arena.Law actual := by
  constructor
  · intro A B hA hB hrank h hh
    obtain ⟨l₁, l₂, hl₁, hl₂, hmap⟩ := result A B hA hB hrank h hh
    refine ⟨l₁, l₂, hl₁, hl₂, ?_⟩
    intro X
    simpa [actual, realize] using hmap X
  · intro A B h X
    rfl

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    constructor
    · intro hclaim
      constructor
      · intro A B hA hB hrank h hh
        obtain ⟨l₁, l₂, hl₁, hl₂, hmap⟩ := hclaim A B hA hB hrank h hh
        refine ⟨l₁, l₂, hl₁, hl₂, ?_⟩
        intro X
        simpa [actual, realize] using hmap X
      · intro A B h X
        rfl
    · intro hlaw A B hA hB hrank hpos hh
      obtain ⟨l₁, l₂, hl₁, hl₂, hmap⟩ := hlaw.1 A B hA hB hrank hpos hh
      refine ⟨l₁, l₂, hl₁, hl₂, ?_⟩
      intro X
      simpa [actual, realize] using hmap X
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition.unit
  realizationName :=
    `Reg.D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p X => kahan p.1 p.2.1 p.2.2 X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition
    definition := some {
      owner := `D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition
      name := `D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition.claim
      path := #[] }
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #[("body"), ("body"), ("body"), ("body"), ("body"), ("body"),
        ("body"), ("body"), ("arg"), ("body"), ("arg"), ("body"),
        ("arg"), ("arg"), ("body"), ("fn"), ("arg")]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition.result
#print _root_.D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition
