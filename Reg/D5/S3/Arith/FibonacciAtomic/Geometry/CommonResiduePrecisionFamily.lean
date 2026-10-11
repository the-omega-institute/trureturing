import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k t => ratio k t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (k B : ℕ), 1 ≤ k → 2 ≤ B →
    ∃ t j : ℕ → ℕ,
      Function.Injective (fun N => (t N, j N)) ∧
      (∀ N : ℕ, 1 ≤ t N ∧ j N < t N ∧ 1 < r.readout () k (t N) (j N + 1) ∧
        (ratio k (t N) (j N + 1) : ℝ) =
          SourceDensityCrossing.sourceDensity k (t N) (j N + 1) /
            SourceDensityCrossing.sourceDensity k (t N) (j N) ∧
        ∀ p : ℕ, p.Prime → p ∣ B →
          (padicValNat p B : ℤ) ≤ padicValRat p (ratio k (t N) (j N + 1) - 1)) ∧
      Filter.Tendsto (fun N => (ratio k (t N) (j N + 1) : ℝ)) Filter.atTop (nhds 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, j, _, heach, _⟩ := h 1 2 (by decide) (by decide)
  have hbad := (heach 0).2.2.1
  norm_num [rejected, realize] at hbad

def registration : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 1
    norm_num [actual, realize, ratio, numerator, denominator,
      SourceDensityMonotonicity.E, SourceDensityMonotonicity.A,
      SourceDensityMonotonicity.D, SourceDensityMonotonicity.L,
      Finset.prod_range_succ] at h

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily.result)
      (type_of% (realize signature (fun _ k t => ratio k t) (fun e => nomatch e)))
      (Type) (Unit) := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily.result.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ k t => ratio k t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some ℕ,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg",
        "fn", "arg", "body", "arg", "arg", "fn", "arg", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily
