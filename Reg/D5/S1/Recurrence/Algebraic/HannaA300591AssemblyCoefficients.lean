import D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients
import Reg.D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Whole-family exponential coefficient readouts with independent ambient markers. -/

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients

open _root_.D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients
open _root_.D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset PowerSeries
open scoped BigOperators

noncomputable section

abbrev Input := _root_.Reg.D5.S1.Recurrence.Algebraic.HannaA300591FixedAssemblies.Input

def total (I : Input) : ℚ := by
  letI := I.finiteV
  letI := I.finiteC
  exact ((∑ E : Assembly I.allowed I.S I.T, weight I.sign E.val : ℤ) : ℚ)

def coefficient (I : Input) : ℚ := by
  letI := I.finiteC
  exact (I.S.card.factorial : ℚ) * coeff I.S.card
    ((exp ℚ).subst (C ((I.T.card : ℚ) ^ 2) * colorSeries I.allowed I.sign))

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
  exact assembly_sum_coefficient I.allowed I.S I.T I.sign

private def emptyInput : Input where
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
  let e : Assembly emptyInput.allowed emptyInput.S emptyInput.T := ⟨∅, by
    constructor <;> intro b hb <;> exact False.elim (notMem_empty b hb)⟩
  have he (E : Assembly emptyInput.allowed emptyInput.S emptyInput.T) : E = e := by
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
  have hz : (∑ E : Assembly blockedInput.allowed blockedInput.S blockedInput.T,
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
      exact h I.allowed I.S I.T I.sign
    · intro h V C fV fC allowed S T sign
      exact h ⟨V, C, fV, fC, Classical.decEq V, allowed, S, T, Equiv.refl V, sign⟩
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
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients.assembly_sum_coefficient.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients.family
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

structure PrefixInput where
  V : Type
  finiteV : Fintype V
  N : ℕ
  a : ℕ → ℤ
  S : Finset V
  T : Finset V

def prefixTotal (I : PrefixInput) : ℚ := by
  letI := I.finiteV
  exact ((∑ E : Assembly (prefixAllowed I.N I.a) I.S I.T,
    weight (prefixSign I.N I.a) E.val : ℤ) : ℚ)

def prefixCoefficient (I : PrefixInput) : ℚ :=
  (I.S.card.factorial : ℚ) * coeff I.S.card
    ((exp ℚ).subst (C ((I.T.card : ℚ) ^ 2) * prefixSeries I.N I.a))

abbrev prefixSignature : Signature where
  Params := Unit
  State _ := PrefixInput
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ _ I => prefixTotal I) (fun e => nomatch e)

def prefixRejected : Realization prefixSignature :=
  realize prefixSignature (fun _ _ I => prefixTotal I + 1) (fun e => nomatch e)

abbrev prefixArena : Arena where
  signature := prefixSignature
  Law R := ∀ I : PrefixInput,
    (∀ c : PrefixColor I.N I.a, prefixSign I.N I.a c = 1 ∨ prefixSign I.N I.a c = -1) ∧
      R.readout () () I = prefixCoefficient I

private theorem prefix_actual_law : prefixArena.Law prefixActual := by
  intro I
  letI := I.finiteV
  exact signed_prefix_assembly_coefficient I.N I.a I.S I.T

private def prefixEmpty : PrefixInput where
  V := Unit
  finiteV := inferInstance
  N := 0
  a _ := 0
  S := ∅
  T := ∅

private def prefixBlocked : PrefixInput where
  V := Unit
  finiteV := inferInstance
  N := 0
  a _ := 0
  S := univ
  T := ∅

private theorem prefix_total_empty : prefixTotal prefixEmpty = 1 := by
  let e : Assembly (prefixAllowed 0 (fun _ => 0)) (∅ : Finset Unit) ∅ := ⟨∅, by
    constructor <;> intro b hb <;> exact False.elim (notMem_empty b hb)⟩
  have he (E : Assembly (prefixAllowed 0 (fun _ => 0)) (∅ : Finset Unit) ∅) : E = e := by
    apply Subtype.ext
    ext b
    exact Fin.elim0 b.2.1.1
  unfold prefixTotal
  change ((∑ E : Assembly (prefixAllowed 0 (fun _ => 0)) (∅ : Finset Unit) ∅,
    weight (prefixSign 0 (fun _ => 0)) E.val : ℤ) : ℚ) = 1
  rw [sum_eq_single e]
  · simp [e, weight]
  · intro E _ hne
    exact False.elim (hne (he E))
  · simp

private theorem prefix_total_blocked : prefixTotal prefixBlocked = 0 := by
  letI := prefixBlocked.finiteV
  unfold prefixTotal
  have hz : (∑ E : Assembly (prefixAllowed prefixBlocked.N prefixBlocked.a)
      prefixBlocked.S prefixBlocked.T, weight (prefixSign prefixBlocked.N prefixBlocked.a) E.val) = 0 := by
    apply sum_eq_zero
    intro E _
    obtain ⟨b, _, _⟩ := E.property.cover () (mem_univ ())
    exact Fin.elim0 b.2.1.1
  rw [hz]
  rfl

private theorem prefix_rejected_law : ¬ prefixArena.Law prefixRejected := by
  intro h
  have hb := (h prefixEmpty).2
  have hg := (prefix_actual_law prefixEmpty).2
  change prefixTotal prefixEmpty + 1 = prefixCoefficient prefixEmpty at hb
  change prefixTotal prefixEmpty = prefixCoefficient prefixEmpty at hg
  linarith

def prefixFamily : Registration prefixArena (type_of% @signed_prefix_assembly_coefficient) where
  actual := prefixActual
  bridge := by
    constructor
    · intro h I
      letI := I.finiteV
      exact h I.N I.a I.S I.T
    · intro h V fV N a S T
      exact h ⟨V, fV, N, a, S, T⟩
  variation := ⟨prefix_actual_law, prefixRejected, prefix_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨prefixRejected, ?_, ?_, prefix_rejected_law⟩
      · intro j hj
        exact False.elim (hj (Subsingleton.elim _ _))
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), prefixEmpty, prefixBlocked, ?_⟩
    change prefixTotal prefixEmpty ≠ prefixTotal prefixBlocked
    rw [prefix_total_empty, prefix_total_blocked]
    norm_num

/-- The exact finite-palette family is retained without a source-selection certificate. -/
def prefixAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 1, 0, 0, 0, 0}
    (@signed_prefix_assembly_coefficient) (Realization prefixSignature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients.signed_prefix_assembly_coefficient.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients.prefixFamily
  realizationSource := none
  generated := false
  arena := .source ⟨prefixArena⟩
  objectArena := .source ⟨prefixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prefixArena ⟨prefixFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize prefixSignature (fun _ _ I => prefixTotal I) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

structure ResidualInput where
  N : ℕ
  a : ℕ → ℤ
  p : ℕ

def residual (I : ResidualInput) : ℚ :=
  let H := (exp ℚ).subst (C ((I.N : ℚ) ^ 2) * prefixSeries I.N I.a)
  coeff I.N H - (I.N : ℚ) ^ 2 * coeff (I.N - 1) H

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
      let H := (exp ℚ).subst (C ((f : ℚ) ^ 2) * prefixSeries I.N I.a)
      coeff f H = (f : ℚ) ^ 2 * coeff (f - 1) H) →
    _root_.D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.IsRIntegralRat I.p
      (R.readout () () I)

private theorem residual_rejected : ¬ residualArena.Law residualRejected := by
  intro h
  have hh := h ⟨1, fun _ => 0, 2⟩ (by exact le_rfl) (by decide) (by norm_num)
    (by intro f hf hlt; dsimp at hf hlt; omega)
  norm_num [residualRejected, realize,
    _root_.D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.IsRIntegralRat] at hh

private theorem zero_prefix (N : ℕ) : prefixSeries N (fun _ => 0) = 0 := by
  ext j
  simp [prefixSeries]

def residualFamily : Registration residualArena (type_of% signed_prefix_residual_local_integral) where
  actual := residualActual
  bridge := by
    constructor
    · intro h I hN hp hpn hlower
      exact h I.N I.a hN I.p hp hpn hlower
    · intro h N a hN p hp hpn hlower
      exact h ⟨N, a, p⟩ hN hp hpn hlower
  variation := ⟨by
      intro I hN hp hpn hlower
      exact signed_prefix_residual_local_integral I.N I.a hN I.p hp hpn hlower,
    residualRejected, residual_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    residualArena.Law residualActual residualRejected residual_rejected
  dependence := by
    intro i
    refine ⟨(), ⟨1, fun _ => 0, 2⟩, ⟨2, fun _ => 0, 3⟩, ?_⟩
    norm_num [residualActual, realize, residual, zero_prefix, subst_zero_eq_C_constantCoeff]

/-- The aggregate residual source selection and reconstruction are unresolved. -/
def residualAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    signed_prefix_residual_local_integral (Realization residualSignature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients.signed_prefix_residual_local_integral.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients.residualFamily
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

end Reg.D5.S1.Recurrence.Algebraic.HannaA300591AssemblyCoefficients
