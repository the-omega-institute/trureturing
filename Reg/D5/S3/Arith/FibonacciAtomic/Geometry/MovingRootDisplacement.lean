import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Arith.FibonacciAtomic.SourceDensityMonotonicity
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)

def expansionActual : Realization signature :=
  realize signature (fun _ p t => H p.1 p.2 t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev expansionArena : Arena where
  signature := signature
  Law r := ∀ (k : ℕ), 1 ≤ k → ∀ (j : ℕ) (t : ℝ), 2 * ((j : ℝ) + 1) ≤ t →
    |Real.log (r.readout () ⟨k, j⟩ t / c k) - B k j / t| ≤
      2 * (D k : ℝ) * ((j : ℝ) + 1) ^ 2 / t ^ 2

private theorem expansion_rejected : ¬ expansionArena.Law rejected := by
  intro h
  have hh := h 1 (by decide) 0 100 (by norm_num)
  norm_num [rejected, realize, B, sigma, kappa, E, A, D, L, Nat.fib] at hh

def expansionProof : Registration expansionArena (expansionArena.Law expansionActual) where
  actual := expansionActual
  bridge := Iff.rfl
  variation := ⟨quantitative_expansion, rejected, expansion_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ expansion_rejected
  dependence := by
    intro role
    refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
    change H 1 0 0 ≠ H 1 0 1
    norm_num [H, rising, a, b, n, E, A, D, L, Nat.fib, Finset.prod_range_succ]

def rootActual : Realization signature :=
  realize signature (fun _ p t => q p.2 p.1 t) (fun e => nomatch e)

/-- The root existence observation varies; all remaining source clauses retain their operands. -/
abbrev rootArena : Arena where
  signature := signature
  Law r := ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 1 ≤ K ∧ ∀ k : ℕ, K ≤ k →
    ∃ τ : ℝ, (j : ℝ) + 1 ≤ τ ∧ r.readout () ⟨j, k⟩ τ = 1 ∧
      (∀ x : ℝ, (j : ℝ) + 1 ≤ x → q k j x = 1 → x = τ) ∧
      |τ - (((j : ℝ) + 1) / c k + j - B k j)| ≤ C * D k * c k ∧
      |Real.log ((τ - j) / (((j : ℝ) + 1) / c k)) + B k j / τ| ≤
        2 * (D k : ℝ) * ((j : ℝ) + 1) ^ 2 / τ ^ 2

private theorem root_rejected : ¬ rootArena.Law rejected := by
  intro h
  obtain ⟨C, _, K, _, hK⟩ := h 0
  obtain ⟨τ, _, hτ, _⟩ := hK K le_rfl
  norm_num [rejected, realize] at hτ

def rootProof : Registration rootArena (rootArena.Law rootActual) where
  actual := rootActual
  bridge := Iff.rfl
  variation := ⟨root_displacement, rejected, root_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ root_rejected
  dependence := by
    intro role
    refine ⟨⟨0, 1⟩, 0, 1, ?_⟩
    change q 1 0 0 ≠ q 1 0 1
    norm_num [q, H, rising, a, b, n, E, A, D, L, Nat.fib, Finset.prod_range_succ]

noncomputable def expansionRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement.quantitative_expansion)
      (type_of% (realize.{0,0,0,0,0} signature
        (fun _ p t => H p.1 p.2 t) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement.quantitative_expansion.informationUnit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement.expansionProof,
  realizationSource := none,
  generated := false,
  arena := .source ⟨expansionArena⟩,
  objectArena := .source ⟨expansionArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source expansionArena ⟨expansionProof⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ p t => H p.1 p.2 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement,
    definition := none,
    coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg",
        "fn", "arg", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `relaxedAutoImplicit, value := .bool false }] }

noncomputable def rootRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement.root_displacement)
      (type_of% (realize.{0,0,0,0,0} signature
        (fun _ p t => q p.2 p.1 t) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement.root_displacement.informationUnit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement.rootProof,
  realizationSource := none,
  generated := false,
  arena := .source ⟨rootArena⟩,
  objectArena := .source ⟨rootArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source rootArena ⟨rootProof⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ p t => q p.2 p.1 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement,
    definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "body", "arg", "body",
        "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `relaxedAutoImplicit, value := .bool false }] }


end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.MovingRootDisplacement
