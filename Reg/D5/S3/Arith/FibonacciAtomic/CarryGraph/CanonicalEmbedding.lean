import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding
import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding

open _root_.D5.S3.Arith.FibonacciAtomic CarryGraphEmbedding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := ℕ
  State m := Fin m → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m →
    (∀ s : State, IsState m s → ∃ a : Action, Legal m s a) ∧
    (∀ (s : State) (a : Action), Legal m s a → s.r = 0 →
      a.b = 0 ∧ a.h = 0 ∧ a.c = 0 ∧ successor s a = s) ∧
    (∀ (s : State) (a : Action), Legal m s a → s.e = 1 → a.h = 0) ∧
    (∀ p : Fin m → ℝ, (∀ i, 0 < p i) → (∑ i, p i = 1) →
      ∃ k : Fin m, (∀ i, p k ≤ p i) ∧ ∃ γ : Path,
        IsRootPath m γ ∧ anchorValue γ = p k ∧
        anchorValue γ = sInf (Set.range p) ∧ pathCost γ = R.readout () m p ∧
        (∀ d, (γ.state d).r = (2 : ℤ)^d - ∑ i, ⌊(2 : ℝ)^d*p i⌋) ∧
        (∀ d, (γ.state d).e = ((Finset.univ.filter
          (fun i => ⌊(2 : ℝ)^d*p i⌋ = ⌊(2 : ℝ)^d*p k⌋)).card : ℤ)))

def actual : Realization signature :=
  realize signature (fun _ _ p => DyadicSupportLines.cost p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Fin 2 → ℝ := fun _ => 1 / 2
  have hp : ∀ i, 0 < p i := by intro i; norm_num [p]
  have hs : ∑ i, p i = 1 := by norm_num [p]
  obtain ⟨k, hk, γ, hγ, ha, hi, hc, hr, he⟩ := (h 2 (by decide)).2.2.2 p hp hs
  have nn : 0 ≤ pathCost γ := by
    apply tsum_nonneg
    intro d
    exact div_nonneg (by exact_mod_cast (hγ.2 d).1.1.1) (by positivity)
  change pathCost γ = -1 at hc
  linarith

def proof_record : Registration arena
    (∀ (m : ℕ), 2 ≤ m →
    (∀ s : State, IsState m s → ∃ a : Action, Legal m s a) ∧
    (∀ (s : State) (a : Action), Legal m s a → s.r = 0 →
      a.b = 0 ∧ a.h = 0 ∧ a.c = 0 ∧ successor s a = s) ∧
    (∀ (s : State) (a : Action), Legal m s a → s.e = 1 → a.h = 0) ∧
    (∀ p : Fin m → ℝ, (∀ i, 0 < p i) → (∑ i, p i = 1) →
      ∃ k : Fin m, (∀ i, p k ≤ p i) ∧ ∃ γ : Path,
        IsRootPath m γ ∧ anchorValue γ = p k ∧
        anchorValue γ = sInf (Set.range p) ∧ pathCost γ = DyadicSupportLines.cost p ∧
        (∀ d, (γ.state d).r = (2 : ℤ)^d - ∑ i, ⌊(2 : ℝ)^d*p i⌋) ∧
        (∀ d, (γ.state d).e = ((Finset.univ.filter
          (fun i => ⌊(2 : ℝ)^d*p i⌋ = ⌊(2 : ℝ)^d*p k⌋)).card : ℤ)))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding.result,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, (fun _ => 0), (fun _ => 1 / 2), ?_⟩
    have hz : DyadicSupportLines.cost (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
      simp [DyadicSupportLines.cost, DyadicSupportLines.residual]
    have H := OptimalLawStrictSlope.cost_ge_one 2 (by decide)
      (fun _ => 1 / 2) (by norm_num) (by norm_num)
    change DyadicSupportLines.cost (fun _ : Fin 2 => (0 : ℝ)) ≠
      DyadicSupportLines.cost (fun _ : Fin 2 => 1 / 2)
    rw [hz]
    exact ne_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) H)

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding.result)
    (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding.result "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => DyadicSupportLines.cost p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "arg", "arg", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.FibonacciAtomic.CarryGraph.CanonicalEmbedding
