import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient

open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := ℕ
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ b => OrientedQuotient b
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ b n => scalarMap b n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ b _ => (0 : OrientedQuotient b)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (b : ℕ) (_hb : Odd b),
    (∀ n : ℤ, orientedFactor b ∣ (QuadraticAlgebra.C n : EisensteinOrder) ↔
      (blockNorm b : ℤ) ∣ n) ∧
    ∃ e : ZMod (blockNorm b) ≃+* OrientedQuotient b,
      ∀ n : ℤ, e (n : ZMod (blockNorm b)) = R.readout () b n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, he⟩ := (h 1 (by decide)).2
  have hzero := he 0
  have hone := he 1
  change e (0 : ZMod (blockNorm 1)) = 0 at hzero
  change e (1 : ZMod (blockNorm 1)) = 0 at hone
  have hcontr : (0 : ZMod (blockNorm 1)) = 1 :=
    e.injective (hzero.trans hone.symm)
  exact (by decide : (0 : ZMod (blockNorm 1)) ≠ 1) hcontr

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro b hb
    exact eisenstein_odd_scalar_quotient b hb
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (b : ℕ) (x y : ℤ), scalarMap b x ≠ scalarMap b y
    refine ⟨1, (0 : ℤ), 1, ?_⟩
    intro heq
    obtain ⟨_, e, he⟩ := eisenstein_odd_scalar_quotient 1 (by decide)
    change scalarMap 1 0 = scalarMap 1 1 at heq
    have h01 : e (0 : ZMod (blockNorm 1)) =
        e (1 : ZMod (blockNorm 1)) := by
      calc
        e (0 : ZMod (blockNorm 1)) = scalarMap 1 0 := by
          simpa only [Int.cast_zero] using he 0
        _ = scalarMap 1 1 := heq
        _ = e (1 : ZMod (blockNorm 1)) := by
          simpa only [Int.cast_one] using (he 1).symm
    have hcontr : (0 : ZMod (blockNorm 1)) = 1 := e.injective h01
    exact (by decide : (0 : ZMod (blockNorm 1)) ≠ 1) hcontr

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.eisenstein_odd_scalar_quotient) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ b n => scalarMap b n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "QuadraticIdeals") "EisensteinOddQuotient") "eisenstein_odd_scalar_quotient") "Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient/Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ b n => scalarMap b n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "arg", "arg", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
