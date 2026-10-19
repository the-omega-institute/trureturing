/-
SOURCE_ONLY_UNCOMPILED. New universal-mean target only. The eleven historical
public targets have no supplied T3 Reg mirror and are not registered here.
This candidate uses the actual mean occurrence and the full original telescope.
All source paths, enrollment, reconstruction and proof terms require real checks.
-/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolResonance.UniformMean

/-- No source coordinates are frozen: the original c binder is the state.
Every natural c, including 0,1,2, remains in the signature. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ c => mean c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- The original lower-cutoff condition stays an implication premise, and
is not used to restrict the signature's state type. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c),
    (Real.log (2 : ℝ)) ^ 2 / 4 ≤ r.readout () () c

private theorem source_reconstruction :
    (type_of% (@prime_symbol_mean_lower_bound)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : LeanInformationAudit.Analysis.Reconstruction
    (type_of% (@prime_symbol_mean_lower_bound)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := by
  intro c hc
  exact prime_symbol_mean_lower_bound hc

/-- One witness rejects the universally quantified law; it does not replace
that law by a single instance. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hh := hall (c := 3) (by decide)
  change (Real.log (2 : ℝ)) ^ 2 / 4 ≤ (-1 : ℝ) at hh
  nlinarith [sq_nonneg (Real.log (2 : ℝ))]

/-- Actual nonconstancy uses an evaluated degenerate fiber and proved positive
mean at c=3. Neither a premise nor a synthetic observation supplies dependence. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  have hzero : mean 2 = 0 := by
    simp [mean, primeSquareMass, resonantMass, primeIndices]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 < mean 3 :=
    lt_of_lt_of_le (div_pos (sq_pos_of_pos hlog) (by norm_num))
      (prime_symbol_mean_lower_bound (c := 3) (by decide))
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change mean 2 ≠ mean 3
  rw [hzero]
  exact ne_of_lt hpos

def familyRegistration : Registration arena
    (type_of% (@prime_symbol_mean_lower_bound)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Source proposal: two original forall binders (implicit c, explicit hc),
then the right operand of LE.le is exactly mean c. c has lexical ordinal 0.
Zero selected coordinates pack to Unit in pinned CompiledSourceScope.packedType.
The sole original state is c, not a law-restricted subtype. This is a raw path
proposal and has not been inspected by the compiled producer or judge. -/
noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_symbol_mean_lower_bound) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolResonance.UniformMean.prime_symbol_mean_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolResonance.UniformMean.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => mean c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyRegistration
#print axioms registration_1
end Reg.D5.S3.Weil.ZetaBridge.PrimeSymbolResonance.UniformMean
