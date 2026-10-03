import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold

open _root_.D5.S1.Scale
open _root_.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => goldenLucas n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law x := ∀ (r n : ℕ) (_hr : 119 ≤ r) (_hn : 2 * r + 1 ≤ n),
    128 * (6 : ℤ) ^ r + 4 < (x.readout () r n) ^ 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 119 239 (by decide) (by decide)
  change (128 : ℤ) * 6 ^ 119 + 4 < (0 : ℤ) ^ 2 at hbad
  have hpos : 0 < (6 : ℤ) ^ 119 := pow_pos (by norm_num) _
  nlinarith

def registration : Registration arena
    (∀ (r n : ℕ) (_hr : 119 ≤ r) (_hn : 2 * r + 1 ≤ n),
      128 * (6 : ℤ) ^ r + 4 < goldenLucas n ^ 2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_lucas_nonsquare_threshold, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨0, (0 : ℕ), (1 : ℕ), ?_⟩
    change goldenLucas 0 ≠ goldenLucas 1
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold) (type_of% (arena)) (type_of% (arena)) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => goldenLucas n)
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "GoldenLucasNonsquareThreshold") "golden_lucas_nonsquare_threshold") "Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold/Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => goldenLucas n)
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Arith.Primes.GoldenLucasNonsquareThreshold
