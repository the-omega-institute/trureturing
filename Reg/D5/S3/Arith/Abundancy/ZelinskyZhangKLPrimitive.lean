import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
import Reg.Support.SingleDependentReadout

/-! The complete unbounded source law with the witness as the selected observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open LeanInformationAudit Real Finset
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ B : ℕ, ∃ n : ℕ,
    B < R.readout () () n ∧ 0 < n ∧ Deficient n ∧ KLPrimitive n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn, hpos, hdef, hprimitive⟩ := h 0
  change 0 < 0 at hn
  exact (Nat.lt_irrefl 0) hn

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    exact Nat.zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.result.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace SigmaPrimeMul

/-- Observe the original arithmetic function on the entire natural domain. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => sig n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p n : ℕ}, p.Prime → p.Coprime n →
    R.readout () () (p * n) = ((p : ℝ) + 1) * sig n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (p := 2) (n := 1) Nat.prime_two (by simp)
  norm_num [rejected, realize, sig] at bad

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.sig_prime_mul) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.sig_prime_mul,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change sig 0 ≠ sig 1
    norm_num [sig]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.sig_prime_mul)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.sig_prime_mul.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.SigmaPrimeMul.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SigmaPrimeMul

namespace KLPrimeMul

/-- Observe the original arithmetic function on the entire natural domain. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => KL n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p n : ℕ}, p.Prime → p.Coprime n →
    R.readout () () (p * n) = ((p : ℝ) + 1) * KL n +
      (p : ℝ) * sig n * Real.log ((p : ℝ) / (p - 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (p := 2) (n := 1) Nat.prime_two (by simp)
  norm_num [rejected, realize, KL, sig, Real.log_div] at bad
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.kl_prime_mul) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.kl_prime_mul,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change KL 0 ≠ KL 1
    norm_num [KL, Real.log_div] <;>
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.kl_prime_mul)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.kl_prime_mul.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.KLPrimeMul.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end KLPrimeMul

namespace RoughCore

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => exp t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ B : ℕ,
    ∃ K : ℝ, 0 < K ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ∃ s : Finset ℕ,
        let h := ∏ p ∈ s, (1 + 1 / (p : ℝ))
        let a := h / (2 - h)
        (∀ p ∈ s, p.Prime ∧ B < p) ∧ h < 2 ∧
          exp t ≤ a ∧ a ≤ 3 * R.readout () () t ∧
          (∀ p ∈ s, (p : ℝ) < 2 * a) ∧
          (∑ p ∈ s, log (p : ℝ)) ≤ K * t ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K, hK, T, hT⟩ := h 0
  obtain ⟨s, hs⟩ := hT T le_rfl
  have hlo := hs.2.2.1
  have hhi := hs.2.2.2.1
  change _ ≤ 3 * (0 : ℝ) at hhi
  linarith [exp_pos T]

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.rough_deficient_core) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.rough_deficient_core,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change exp (0 : ℝ) ≠ exp 1
    exact Real.exp_injective.ne zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.rough_deficient_core)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.rough_deficient_core.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.RoughCore.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "body", "body", "body",
        "arg", "body", "body", "body", "arg", "arg", "arg", "fn", "arg",
        "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RoughCore

namespace FBounds

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ p => f p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, 2 ≤ p →
    2 / (3 * (p : ℝ)) ≤ R.readout () () p ∧ f p ≤ 2 / (p : ℝ) ∧
      0 < f p ∧ f p < Real.log 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := (h (p := 2) (by decide)).1
  norm_num [rejected, realize] at hp

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.f_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.f_bounds,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 2, ?_⟩
    change f 0 ≠ f 2
    have hpos := (f_bounds (p := 2) (by decide)).2.2.1
    simpa [f] using hpos.ne.symm

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.f_bounds)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.f_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.FBounds.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FBounds

namespace TailMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ Q k : ℕ,
    ∃ s : Finset ℕ, (∀ q ∈ s, q.Prime ∧ Q < q) ∧
      R.readout () () ((k : ℝ) / 3) (∑ q ∈ s, f q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, hs, hfalse⟩ := h 0 0
  exact hfalse

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.tail_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.tail_mass,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh := congrFun he (0 : ℝ)
    change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
    have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
    norm_num at hbad

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.tail_mass)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.tail_mass.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.TailMass.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailMass

namespace DeficientOfDvd

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ d => Deficient d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d n : ℕ}, 0 < n → 0 < d → d ∣ n → Deficient n →
    R.readout () () d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (d := 1) (n := 1) (by decide) (by decide) (by decide)
    (by norm_num [Deficient])

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.deficient_of_dvd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.deficient_of_dvd,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change Deficient 0 ≠ Deficient 1
    norm_num [Deficient]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.deficient_of_dvd)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.deficient_of_dvd.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive.DeficientOfDvd.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeficientOfDvd

end Reg.D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
