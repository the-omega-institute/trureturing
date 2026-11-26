import D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients
import Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyFixedPoints
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Whole-family exponential coefficient readouts with independent ambient markers. -/

namespace Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients

open _root_.D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients
open _root_.D5.S1.Recurrence.Algebraic.MarkedAssemblyFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset PowerSeries
open scoped BigOperators

noncomputable section

abbrev Input := _root_.Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyFixedPoints.Input

def total (I : Input) : ℚ := by
  letI := I.finiteV
  letI := I.finiteC
  exact ((∑ E : Assembly (k := I.d) I.allowed I.S I.T, weight I.sign E.val : ℤ) : ℚ)

def coefficient (I : Input) : ℚ := by
  letI := I.finiteC
  exact (I.S.card.factorial : ℚ) * coeff I.S.card
    ((exp ℚ).subst (C ((I.T.card : ℚ) ^ I.d) * colorSeries I.allowed I.sign))

abbrev signature : Signature where
  Params := Unit
  State _ := Input
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ I => total I) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ I => total I + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ I : Input, R.readout () () I = coefficient I

private theorem actual_law : arena.Law actual := by
  intro I
  letI := I.finiteV
  letI := I.finiteC
  exact assembly_sum_coefficient (d := I.d) I.allowed I.S I.T I.sign

private def emptyInput : Input where
  d := 3
  V := Unit
  C := Empty
  finiteV := inferInstance
  finiteC := inferInstance
  decV := inferInstance
  allowed _ _ := False
  S := ∅
  T := ∅
  g := Equiv.refl _
  sign e := nomatch e

private def blockedInput : Input where
  d := 3
  V := Unit
  C := Empty
  finiteV := inferInstance
  finiteC := inferInstance
  decV := inferInstance
  allowed _ _ := False
  S := univ
  T := ∅
  g := Equiv.refl _
  sign e := nomatch e

private theorem total_empty : total emptyInput = 1 := by
  let e : Assembly (k := emptyInput.d) emptyInput.allowed emptyInput.S emptyInput.T := ⟨∅, by
    constructor <;> intro b hb <;> exact False.elim (notMem_empty b hb)⟩
  have he (E : Assembly (k := emptyInput.d) emptyInput.allowed emptyInput.S emptyInput.T) : E = e := by
    apply Subtype.ext
    ext b
    exact b.2.1.elim
  unfold total
  rw [sum_eq_single e]
  · simp [e, weight]
  · intro E _ hne
    exact False.elim (hne (he E))
  · simp

private theorem total_blocked : total blockedInput = 0 := by
  letI := blockedInput.finiteV
  letI := blockedInput.finiteC
  unfold total
  have hz : (∑ E : Assembly (k := blockedInput.d) blockedInput.allowed blockedInput.S blockedInput.T,
      weight blockedInput.sign E.val) = 0 := by
    apply sum_eq_zero
    intro E _
    obtain ⟨b, _, _⟩ := E.property.cover () (mem_univ ())
    exact b.2.1.elim
  rw [hz]
  rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h emptyInput
  have hg := actual_law emptyInput
  change total emptyInput + 1 = coefficient emptyInput at hb
  change total emptyInput = coefficient emptyInput at hg
  linarith

def family : Registration arena (type_of% @assembly_sum_coefficient) where
  actual := actual
  bridge := by
    constructor
    · intro h I
      letI := I.finiteV
      letI := I.finiteC
      exact h (d := I.d) I.allowed I.S I.T I.sign
    · intro h d V C fV fC allowed S T sign
      exact h ⟨d, V, C, fV, fC, Classical.decEq V, allowed, S, T, Equiv.refl V, sign⟩
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact False.elim (hj (Subsingleton.elim _ _))
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), emptyInput, blockedInput, ?_⟩
    change total emptyInput ≠ total blockedInput
    rw [total_empty, total_blocked]
    norm_num

/-- Aggregate finite-sum source selection is unresolved. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 1, 0, 0, 0, 0}
    (@assembly_sum_coefficient) (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients.assembly_sum_coefficient.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ I => total I) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

structure ResidualInput where
  d : ℕ
  N : ℕ
  a : ℕ → ℤ
  p : ℕ

def residual (I : ResidualInput) : ℚ :=
  let H := (exp ℚ).subst (C ((I.N : ℚ) ^ I.d) * prefixSeries I.N I.a)
  coeff I.N H - (I.N : ℚ) ^ I.d * coeff (I.N - 1) H

abbrev residualSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ResidualInput) (fun _ => ℚ)

def residualActual : Realization residualSignature :=
  realize residualSignature (fun _ _ I => residual I) (fun e => nomatch e)

def residualRejected : Realization residualSignature :=
  realize residualSignature (fun _ _ _ => (1 / 2 : ℚ)) (fun e => nomatch e)

abbrev residualArena : Arena where
  signature := residualSignature
  Law R := ∀ I : ResidualInput, 1 ≤ I.N → I.p.Prime → ¬I.p ∣ I.N →
    (∀ f : ℕ, 1 ≤ f → f < I.N →
      let H := (exp ℚ).subst (C ((f : ℚ) ^ I.d) * prefixSeries I.N I.a)
      coeff f H = (f : ℚ) ^ I.d * coeff (f - 1) H) →
    0 ≤ padicValRat I.p (R.readout () () I)

private theorem residual_rejected : ¬ residualArena.Law residualRejected := by
  intro h
  have hh := h ⟨3, 1, fun _ => 0, 2⟩ (by exact le_rfl) (by decide) (by norm_num)
    (by intro f hf hlt; dsimp at hf hlt; omega)
  change 0 ≤ padicValRat 2 (1 / 2 : ℚ) at hh
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [padicValRat.div (by norm_num) (by norm_num), padicValRat.one,
    show padicValRat 2 (2 : ℚ) = 1 from padicValRat.self (by decide)] at hh
  norm_num at hh

private theorem zero_prefix (N : ℕ) : prefixSeries N (fun _ => 0) = 0 := by
  ext j
  simp [prefixSeries]

def residualFamily : Registration residualArena (type_of% signed_prefix_residual_local_integral) where
  actual := residualActual
  bridge := by
    constructor
    · intro h I hN hp hpn hlower
      exact h I.d I.N I.a hN I.p hp hpn hlower
    · intro h d N a hN p hp hpn hlower
      exact h ⟨d, N, a, p⟩ hN hp hpn hlower
  variation := ⟨by
      intro I hN hp hpn hlower
      exact signed_prefix_residual_local_integral I.d I.N I.a hN I.p hp hpn hlower,
    residualRejected, residual_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    residualArena.Law residualActual residualRejected residual_rejected
  dependence := by
    intro i
    refine ⟨(), ⟨3, 1, fun _ => 0, 2⟩, ⟨3, 2, fun _ => 0, 3⟩, ?_⟩
    norm_num [residualActual, realize, residual, zero_prefix, subst_zero_eq_C_constantCoeff]

/-- The aggregate residual source selection and reconstruction are unresolved. -/
def residualAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    signed_prefix_residual_local_integral (Realization residualSignature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients.signed_prefix_residual_local_integral.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients.residualFamily
  realizationSource := none
  generated := false
  arena := .source ⟨residualArena⟩
  objectArena := .source ⟨residualArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source residualArena ⟨residualFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize residualSignature (fun _ _ I => residual I) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients
