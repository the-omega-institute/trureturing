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
  realize signature
    (fun _ p X => kahan (Sigma.fst p) (Sigma.fst (Sigma.snd p))
      (Sigma.snd (Sigma.snd p)) X)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ A B : Matrix (Fin 3) (Fin 3) ℝ, A.PosDef → B.PosDef →
      (∀ t : ℝ, 2 ≤ (B - t • A).rank) →
        ∀ h : ℝ, 0 < h →
          ∃ l₁ l₂ : Matrix (Fin 4) (Fin 4) ℂ,
            IsUnit l₁.det ∧ IsUnit l₂.det ∧
              ∀ X : Fin 4 → ℂ,
                R.readout () ⟨A, ⟨B, h⟩⟩ X = l₂ *ᵥ cremona (l₁ *ᵥ X)

def zeroInput : Fin 4 → ℂ := fun _ => 1

private theorem pencil_rank (t : ℝ) :
    2 ≤ (diagonal ![1, 2, 3] - t • (1 : Matrix (Fin 3) (Fin 3) ℝ)).rank := by
  have he : diagonal ![1, 2, 3] - t • (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      diagonal (fun i => (![1, 2, 3] : Fin 3 → ℝ) i - t) := by
    ext i j
    by_cases hij : i = j <;> simp [diagonal, hij]
  rw [he, Matrix.rank_diagonal, Fintype.card_subtype]
  simp only [Fin.card_filter_univ_succ, Finset.univ_eq_empty, Finset.filter_empty,
    Finset.card_empty, Matrix.cons_val_zero, Matrix.cons_val_succ]
  split_ifs <;> norm_num at * <;> linarith

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hB : (diagonal (![1, 2, 3] : Fin 3 → ℝ)).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num
  obtain ⟨l₁, l₂, hl₁, hl₂, hmap⟩ :=
    h 1 (diagonal ![1, 2, 3]) Matrix.PosDef.one hB pencil_rank 1 (by norm_num)
  have hpre : l₁ *ᵥ (l₁⁻¹ *ᵥ zeroInput) = zeroInput := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hl₁, Matrix.one_mulVec]
  have hc : cremona zeroInput = zeroInput := by
    ext i
    fin_cases i <;> norm_num [cremona, zeroInput]
  have hbad := hmap (l₁⁻¹ *ᵥ zeroInput)
  change 0 = l₂ *ᵥ cremona (l₁ *ᵥ (l₁⁻¹ *ᵥ zeroInput)) at hbad
  rw [hpre, hc] at hbad
  have hz : zeroInput = 0 := Matrix.mulVec_injective_of_isUnit
    (l₂.isUnit_iff_isUnit_det.mpr hl₂) (by simpa using hbad.symm)
  have h0 := congrFun hz 0
  norm_num [zeroInput] at h0

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, ⟨0, 0⟩⟩, zeroInput, (fun _ => 0), ?_⟩
  intro he
  have h0 := congrFun he 0
  simp [actual, realize, zeroInput, kahan, kahanMatrix] at h0

theorem actual_law : arena.Law actual := by
  exact result

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
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
    (realize signature
      (fun _ p X => kahan (Sigma.fst p) (Sigma.fst (Sigma.snd p))
        (Sigma.snd (Sigma.snd p)) X)
      (fun e => nomatch e))
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
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #[("body"), ("body"), ("body"), ("body"), ("body"), ("body"),
        ("body"), ("arg"), ("body"), ("arg"), ("body"),
        ("arg"), ("arg"), ("body"), ("fn"), ("arg")]
      stateBinder := 9
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
