import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap
import Reg.Support.DependentFamily

/-! Source-bound audit of the Hamming-weight pattern spectral gap. -/

namespace Reg.D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap

open _root_.D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Erdos7.CommonTreeUnion (Choice)
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ × ℕ
  State p := List (Fin p.2 × Fin p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Choice p.2 p.1) (Choice p.2 p.1) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p pat => patternMatrix (k := p.1) pat) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _p _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (k c a : ℕ), 1 ≤ k → ∀ pat : (n : ℕ) → List (Fin n × Fin n),
      (∀ n, 2 ≤ n → connectedPattern (pat n) ∧ (pat n).length ≤ c * n ^ a) →
      ∃ d : ℝ, 0 < d ∧ ∃ b : ℕ, ∀ n, k < n → 2 ≤ n →
        ∀ (μ : ℂ) (v : Choice n k → ℂ), v ≠ 0 → ∑ s, v s = 0 →
        (R.readout () (k, n) (pat n)).map (fun x : ℝ => (x : ℂ)) *ᵥ v = μ • v →
        ‖μ‖ ≤ 1 - d / (n : ℝ) ^ b) ∧
    (∀ (k n : ℕ) (pat : List (Fin n × Fin n)),
      R.readout () (k, n) pat = patternMatrix (k := k) pat)

theorem bridge : claim ↔ arena.Law actual := by
  constructor
  · intro h
    constructor
    · intro k c a hk pat hp
      simpa only [actual, realize] using h k c a hk pat hp
    · intro k n pat
      rfl
  · intro h
    intro k c a hk pat hp
    have hmain := h.1 k c a hk pat hp
    simpa only [actual, realize] using hmain

theorem actual_law : arena.Law actual := bridge.mp result

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let s : Choice 2 1 := ⟨{0}, by simp⟩
  have he := h.2 1 2 [((0 : Fin 2), (1 : Fin 2))]
  have he' : (1 : Matrix (Choice 2 1) (Choice 2 1) ℝ) =
      patternMatrix (k := 1) [((0 : Fin 2), (1 : Fin 2))] := by
    simpa [rejected, realize] using he
  have hswap : swapConfig (0 : Fin 2) 1 s ≠ s := by
    intro hs
    have hm : (0 : Fin 2) ∈ (swapConfig (0 : Fin 2) 1 s).val := by
      rw [hs]
      simp [s]
    change (0 : Fin 2) ∈ s.val.map (Equiv.swap (0 : Fin 2) 1).toEmbedding at hm
    rw [Finset.mem_map_equiv] at hm
    simpa [s] using hm
  have hentry := congrArg (fun M => M s s) he'
  have hswap' : s ≠ swapConfig (0 : Fin 2) 1 s := hswap.symm
  simp [patternMatrix, gateMatrix, Matrix.one_apply, hswap'] at hentry

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  let s : Choice 2 1 := ⟨{0}, by simp⟩
  refine ⟨(1, 2), [], [((0 : Fin 2), (1 : Fin 2))], ?_⟩
  intro he
  have he' : patternMatrix (k := 1) [] =
      patternMatrix (k := 1) [((0 : Fin 2), (1 : Fin 2))] := by
    simpa [actual, realize] using he
  have hswap : swapConfig (0 : Fin 2) 1 s ≠ s := by
    intro hs
    have hm : (0 : Fin 2) ∈ (swapConfig (0 : Fin 2) 1 s).val := by
      rw [hs]
      simp [s]
    change (0 : Fin 2) ∈ s.val.map (Equiv.swap (0 : Fin 2) 1).toEmbedding at hm
    rw [Finset.mem_map_equiv] at hm
    simpa [s] using hm
  have hentry := congrArg (fun M => M s s) he'
  have hswap' : s ≠ swapConfig (0 : Fin 2) 1 s := hswap.symm
  simp [patternMatrix, gateMatrix, Matrix.one_apply, hswap'] at hentry

def source_registration : Registration arena claim where
  actual := actual
  bridge := bridge
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
      (@_root_.D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.unit
  realizationName :=
    `Reg.D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.source_registration
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
    (realize signature (fun _ p pat => patternMatrix (k := p.1) pat) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap
    definition := some {
      owner := `D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap
      name := `D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "domain",
        "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap
