import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Codes.BinaryEAShorteningLengthSeven
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the code-dimension hypothesis in the length-seven obstruction. -/

namespace Reg.D5.S3.Quantum.Codes.BinaryEAShorteningLengthSeven

open _root_.D5.S3.Quantum.Codes.BinaryEAShortening
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (spForm)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false

noncomputable section

local notation "F₂" => ZMod 2
local notation "Word" => ((Fin 7 → F₂) × (Fin 7 → F₂))
local notation "Code" => Submodule F₂ Word
local notation "Symbols" => (F₂ × F₂) × (F₂ × F₂)

/-- Observe the dimension of the actual length-seven code. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Code) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ U => Module.finrank F₂ U) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 8) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ H U : Code, H ≤ U → Module.finrank F₂ H = 4 →
    R.readout () () U = 8 →
    (∀ h ∈ H, ∀ u ∈ U, spForm 7 h u = 0) →
    (∀ x ∈ U, x ∉ H → (zeroSites Finset.univ x).card ≤ 3) →
    ∀ i : Fin 7, Function.Surjective ((site i).domRestrict H) → False

-- Repeating each symbol on two sites gives an isotropic four-dimensional code.
private def doubled : Symbols →ₗ[F₂] Word where
  toFun p := (![p.1.1,p.1.1,p.2.1,p.2.1,0,0,0], ![p.1.2,p.1.2,p.2.2,p.2.2,0,0,0])
  map_add' p q := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' a p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

private lemma doubled_dim : Module.finrank F₂ doubled.range = 4 := by
  have h : ∀ p q : Symbols, doubled p = doubled q → p = q := by decide
  rw [LinearMap.finrank_range_of_inj (show Function.Injective doubled from fun _ _ => h _ _)]
  simp [Module.finrank_prod]

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd : ∀ p q : Symbols, spForm 7 (doubled p) (doubled q) = 0 := by decide
  have ho : ∀ x ∈ doubled.range, ∀ y ∈ doubled.range, spForm 7 x y = 0 := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact hd p q
  have hz : ∀ x ∈ doubled.range, x ∉ doubled.range → (zeroSites Finset.univ x).card ≤ 3 :=
    fun _ hx hn => (hn hx).elim
  apply h doubled.range doubled.range le_rfl doubled_dim rfl ho hz 0
  intro p
  exact ⟨⟨doubled (p, 0), LinearMap.mem_range_self _ _⟩, rfl⟩

def evidence : Registration arena (type_of% @length_seven_no_rank_two_site) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨length_seven_no_rank_two_site, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), ⊥, doubled.range, ?_⟩
    change Module.finrank F₂ (⊥ : Code) ≠ Module.finrank F₂ doubled.range
    rw [finrank_bot, doubled_dim]
    decide

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@length_seven_no_rank_two_site) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Codes.BinaryEAShorteningLengthSeven.unit
  realizationName := `Reg.D5.S3.Quantum.Codes.BinaryEAShorteningLengthSeven.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ U => Module.finrank F₂ U) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Codes.BinaryEAShorteningLengthSeven
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end
end Reg.D5.S3.Quantum.Codes.BinaryEAShorteningLengthSeven
