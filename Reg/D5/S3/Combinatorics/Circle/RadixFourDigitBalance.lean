import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.RadixFourDigitBalance
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.RadixFourDigitBalance

open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance
open _root_.D5.S3.Combinatorics.Circle.RadixFourNonunitZeroSubsets
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Full-source bindings use the enrolled dependent-family realization. The
digit law observes its literal trace; the spectrum and zero-count laws observe
their complete cardinalities, including every residue seed in each filter. -/

abbrev digitSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def digitActual : Realization digitSignature :=
  realize digitSignature (fun _ n t => evenTrace n t) (fun e => nomatch e)

def digitRejected : Realization digitSignature :=
  realize digitSignature (fun _ _ _ => (1 : ℤ)) (fun e => nomatch e)

abbrev digitArena : Arena where
  signature := digitSignature
  Law R := ∀ {n : ℕ} (hn : 0 < n) (t : ℕ),
    3 * R.readout () n t = modulus (2 * n) *
      (((Finset.univ.filter (fun i : Fin n =>
        ((t % (4 ^ n - 1)) / 4 ^ i.val) % 4 = 1)).card : ℤ) -
       ((Finset.univ.filter (fun i : Fin n =>
        ((t % (4 ^ n - 1)) / 4 ^ i.val) % 4 = 2)).card : ℤ))

private theorem digitRejectedLaw : ¬ digitArena.Law digitRejected := by
  intro h
  have hh := h (n := 1) (by decide) 0
  norm_num [digitRejected, realize, modulus, evenTrace, actualSource, centered,
    evenLabel] at hh

def digitRegistration : Registration digitArena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.actual_even_digit_balance)) where
  actual := digitActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.actual_even_digit_balance,
    digitRejected, digitRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨digitRejected, ?_, rfl, digitRejectedLaw⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change evenTrace 1 0 ≠ evenTrace 1 1
    norm_num [evenTrace, actualSource, centered, modulus, evenLabel]

abbrev spectrumSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def spectrumActual : Realization spectrumSignature :=
  realize spectrumSignature (fun _ n r =>
    (Finset.univ.filter (fun t : Fin (4 ^ n - 1) =>
      3 * evenTrace n t.val = modulus (2 * n) * ((r : ℤ) - (n : ℤ)))).card)
    (fun e => nomatch e)

def spectrumRejected : Realization spectrumSignature :=
  realize spectrumSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev spectrumArena : Arena where
  signature := spectrumSignature
  Law R := ∀ {n : ℕ} (hn : 0 < n) (r : ℕ),
    R.readout () n r + (if r = n then 1 else 0) = Nat.choose (2 * n) r

private theorem spectrumRejectedLaw : ¬ spectrumArena.Law spectrumRejected := by
  intro h
  have hh := h (n := 1) (by decide) 0
  norm_num [spectrumRejected, realize] at hh

def spectrumRegistration : Registration spectrumArena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.even_trace_seed_spectrum)) where
  actual := spectrumActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.even_trace_seed_spectrum,
    spectrumRejected, spectrumRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨spectrumRejected, ?_, rfl, spectrumRejectedLaw⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 3, ?_⟩
    have h0 := even_trace_seed_spectrum (n := 1) (by decide) 0
    have h3 := even_trace_seed_spectrum (n := 1) (by decide) 3
    change spectrumActual.readout () 1 0 + 0 = 1 at h0
    change spectrumActual.readout () 1 3 + 0 = 0 at h3
    change spectrumActual.readout () 1 0 ≠ spectrumActual.readout () 1 3
    simp only [Nat.add_zero] at h0 h3
    intro heq
    have hbad : (1 : ℕ) = 0 := h0.symm.trans (heq.trans h3)
    exact Nat.one_ne_zero hbad

abbrev zeroSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def zeroActual : Realization zeroSignature :=
  realize zeroSignature (fun _ _ n =>
    (Finset.univ.filter (fun t : Fin (4 ^ n - 1) => evenTrace n t.val = 0)).card)
    (fun e => nomatch e)

def zeroRejected : Realization zeroSignature :=
  realize zeroSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev zeroArena : Arena where
  signature := zeroSignature
  Law R := ∀ {n : ℕ} (hn : 0 < n),
    R.readout () () n + 1 = Nat.choose (2 * n) n

private theorem zeroRejectedLaw : ¬ zeroArena.Law zeroRejected := by
  intro h
  have hh := h (n := 1) (by decide)
  norm_num [zeroRejected, realize] at hh

def zeroRegistration : Registration zeroArena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.zero_even_trace_seed_count)) where
  actual := zeroActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.zero_even_trace_seed_count,
    zeroRejected, zeroRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroRejected, ?_, rfl, zeroRejectedLaw⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    have h1 := zero_even_trace_seed_count (n := 1) (by decide)
    have h2 := zero_even_trace_seed_count (n := 2) (by decide)
    change zeroActual.readout () () 1 + 1 = 2 at h1
    change zeroActual.readout () () 2 + 1 = 6 at h2
    change zeroActual.readout () () 1 ≠ zeroActual.readout () () 2
    intro heq
    have hbad : (2 : ℕ) = 6 :=
      h1.symm.trans ((congrArg (fun x : ℕ => x + 1) heq).trans h2)
    exact (by decide : (2 : ℕ) ≠ 6) hbad

noncomputable def digitAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.actual_even_digit_balance)
    (type_of% digitActual) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.RadixFourDigitBalance.actual_even_digit_balance.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.digitRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨digitArena⟩
  objectArena := .source ⟨digitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source digitArena ⟨digitRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize digitSignature (fun _ n t => evenTrace n t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.RadixFourDigitBalance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def spectrumAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.even_trace_seed_spectrum)
    (type_of% spectrumActual) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.RadixFourDigitBalance.even_trace_seed_spectrum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.spectrumRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨spectrumArena⟩
  objectArena := .source ⟨spectrumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source spectrumArena ⟨spectrumRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize spectrumSignature (fun _ n r =>
    (Finset.univ.filter (fun t : Fin (4 ^ n - 1) =>
      3 * evenTrace n t.val = modulus (2 * n) * ((r : ℤ) - (n : ℤ)))).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.RadixFourDigitBalance
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def zeroAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.zero_even_trace_seed_count)
    (type_of% zeroActual) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.RadixFourDigitBalance.zero_even_trace_seed_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.RadixFourDigitBalance.zeroRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨zeroArena⟩
  objectArena := .source ⟨zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroArena ⟨zeroRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize zeroSignature (fun _ _ n =>
    (Finset.univ.filter (fun t : Fin (4 ^ n - 1) => evenTrace n t.val = 0)).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.RadixFourDigitBalance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms digitRegistration
#print axioms spectrumRegistration
#print axioms zeroRegistration

end Reg.D5.S3.Combinatorics.Circle.RadixFourDigitBalance
