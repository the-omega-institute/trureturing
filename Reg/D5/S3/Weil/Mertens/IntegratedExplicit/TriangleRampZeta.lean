import D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Complete variation for the conditional arithmetic laws requires RH. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => smoothedMangoldt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 3, ?_⟩
  have hv := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  change smoothedMangoldt 0 ≠ smoothedMangoldt 3
  norm_num [smoothedMangoldt, Finset.sum_range_succ, hv]

namespace Error

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x),
    |R.readout () () x -
      (x / 2 - (3 / 2 + Real.eulerMascheroniConstant) / x - Real.log (2 * Real.pi) +
        2 * Real.log (2 * Real.pi) / x -
        _root_.D5.S3.Weil.Mertens.IntegratedExplicit.trivialT (Real.log x) +
        2 / x * (∫ t in (1 : ℝ)..x,
          _root_.D5.S3.Weil.Mertens.IntegratedExplicit.trivialT (Real.log t)))| ≤
      7 / 3 * firstLiMass * Real.sqrt x - 4 / 3 * firstLiMass / x

def rejectedError : Realization signature :=
  realize signature (fun _ _ x =>
    (x / 2 - (3 / 2 + Real.eulerMascheroniConstant) / x - Real.log (2 * Real.pi) +
      2 * Real.log (2 * Real.pi) / x -
      _root_.D5.S3.Weil.Mertens.IntegratedExplicit.trivialT (Real.log x) +
      2 / x * (∫ t in (1 : ℝ)..x,
        _root_.D5.S3.Weil.Mertens.IntegratedExplicit.trivialT (Real.log t))) +
      |7 / 3 * firstLiMass * Real.sqrt x - 4 / 3 * firstLiMass / x| + 1)
    (fun e => nomatch e)

private theorem rejected_law (hRH : RiemannHypothesis) : ¬ arena.Law rejectedError := by
  intro h
  have he := h hRH (x := 2) (by norm_num)
  dsimp only [rejectedError, realize] at he
  have he' : |7 / 3 * firstLiMass * Real.sqrt 2 - 4 / 3 * firstLiMass / 2| + 1 ≤
      7 / 3 * firstLiMass * Real.sqrt 2 - 4 / 3 * firstLiMass / 2 := by
    have he' : |(|7 / 3 * firstLiMass * Real.sqrt 2 -
        4 / 3 * firstLiMass / 2| + 1)| ≤
        7 / 3 * firstLiMass * Real.sqrt 2 - 4 / 3 * firstLiMass / 2 := by
      convert he using 1 <;> congr 1 <;> ring
    simpa only [abs_of_pos (by positivity : 0 <
      |7 / 3 * firstLiMass * Real.sqrt 2 - 4 / 3 * firstLiMass / 2| + 1)] using he'
  linarith [le_abs_self (7 / 3 * firstLiMass * Real.sqrt 2 - 4 / 3 * firstLiMass / 2)]

def family (hRH : RiemannHypothesis) :
    Registration arena (type_of% @smoothedMangoldt_explicit_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@smoothedMangoldt_explicit_bound, rejectedError, rejected_law hRH⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejectedError (rejected_law hRH)
  dependence := dependence

end Error

namespace Explicit

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x),
    x / 2 - (7 / 3 * firstLiMass) * Real.sqrt x - (1 + Real.log Real.pi) -
      (3 / 2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.pi) -
        4 / 3 * firstLiMass) / x ≤ R.readout () () x

private theorem source_bridge :
    (type_of% @smoothedMangoldt_explicit_lower) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law (hRH : RiemannHypothesis) : ¬arena.Law rejected := by
  intro h
  have he := h hRH (x := 1) (by norm_num)
  change (1 : ℝ) / 2 - (7 / 3 * firstLiMass) * Real.sqrt 1 -
    (1 + Real.log Real.pi) -
    (3 / 2 + Real.eulerMascheroniConstant - 2 * Real.log (2 * Real.pi) -
      4 / 3 * firstLiMass) / 1 ≤ -1 at he
  norm_num only [Real.sqrt_one, mul_one, div_one] at he
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero] at he
  linarith [firstLiMass_split, firstLiMass_lt_third]

def family (hRH : RiemannHypothesis) :
    Registration arena (type_of% @smoothedMangoldt_explicit_lower) where
  actual := actual
  bridge := source_bridge
  variation := ⟨@smoothedMangoldt_explicit_lower, rejected, rejected_law hRH⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected (rejected_law hRH)
  dependence := dependence

end Explicit

namespace Uniform

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ} (hRH : 10 ≤ x → RiemannHypothesis),
    x / 2 - Real.sqrt x ≤ R.readout () () x

private theorem source_bridge :
    (type_of% @smoothedMangoldt_lower) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have he := h (x := 0) (fun ht => (by norm_num at ht))
  norm_num [rejected, realize] at he

def family :
    Registration arena (type_of% @smoothedMangoldt_lower) where
  actual := actual
  bridge := source_bridge
  variation := ⟨@smoothedMangoldt_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected (rejected_law)
  dependence := dependence

def audit :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@smoothedMangoldt_lower) (Realization signature) Unit Unit where
  unitName := (`D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta.smoothedMangoldt_lower).str
    "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta.Uniform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Uniform

namespace Principal

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ} (hp : p.Prime)
    (hRH : 10 ≤ (p : ℝ) → RiemannHypothesis),
    (p : ℝ) / 2 - Real.sqrt p ≤ R.readout () ()
      (_root_.D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothedCharacterSum p 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h Nat.prime_two (fun ht => (by norm_num at ht))
  change (2 : ℝ) / 2 - Real.sqrt 2 ≤ -1 at he
  have hs : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @principal_smoothedCharacterSum_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@principal_smoothedCharacterSum_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@principal_smoothedCharacterSum_lower) (Realization signature) Unit Unit where
  unitName := ((`D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta).str
    "principal_smoothedCharacterSum_lower").str "__information_unit"
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta.Principal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Principal

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
