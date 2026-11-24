import Reg.Support.SingleDependentReadout
import D5.S3.Arith.PrimitiveRoot.SieveThreshold
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The feasibility readout is sensitive to the actual integer. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.PrimitiveRoot.SieveThreshold
open _root_.D5.S3.Arith.PrimitiveRoot.SieveThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.PrimitiveRoot.CharacterSieve
open _root_.D5.S3.Arith.PrimitiveRoot.CharacterExpansion
open scoped BigOperators

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℕ) (_hx : 4100000 ≤ x), Feasible (R.readout () () x)

private theorem not_feasible_zero : ¬ Feasible 0 := by
  rintro ⟨e, T, he, hcover, hδ, hpos⟩
  norm_num at hpos

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact not_feasible_zero (h 4100000 le_rfl)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% feasible_of_ge_4100000) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨feasible_of_ge_4100000, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    feasible_of_ge_4100000 (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThreshold.feasible_of_ge_4100000.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThreshold.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThreshold
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
  options := #[]



namespace MarginMono
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x y A : ℝ} (_hx : Real.exp 2 ≤ x) (_hxy : x ≤ y)
    (_h : 2 + 3 * A * Real.log x < Real.sqrt x),
    2 + 3 * A * Real.log y < R.readout () () y
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (x := 16) (y := 16) (A := 0) (exp_two_le (by norm_num))
    le_rfl (by norm_num)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @margin_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@margin_mono, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@margin_mono) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThreshold.margin_mono.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThreshold.MarginMono.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end MarginMono

namespace ExpTwo
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ} (_hx : 7.4 ≤ x), Real.exp 2 ≤ R.readout () () x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (x := 16) (by norm_num)
  have hp := Real.exp_pos 2
  norm_num [rejected, realize] at hh
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @exp_two_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exp_two_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exp_two_le) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThreshold.exp_two_le.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThreshold.ExpTwo.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThreshold
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
  options := #[]
end ExpTwo

namespace Split
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x r s : ℕ) (_hx : 1 < x)
    (hc : (x - 1).primeFactors.card = r + s),
    ∃ (e : ℕ) (T : Finset ℕ), e ≠ 0 ∧ e ∣ x - 1 ∧
      (∀ p : ℕ, p.Prime → p ∣ x - 1 → p ∣ e ∨ p ∈ T) ∧
      e.primeFactors.card = r ∧ T.card = s ∧
      e = ∏ i : Fin r,
        (x - 1).primeFactors.orderEmbOfFin hc (i.castAdd s) ∧
      T = Finset.univ.image (fun i : Fin s =>
        (x - 1).primeFactors.orderEmbOfFin hc (Fin.natAdd r i)) ∧
      sievePrimes (R.readout () () x) e T = T ∧
      delta T = 1 - ∑ i : Fin s,
        ((x - 1).primeFactors.orderEmbOfFin hc (Fin.natAdd r i) : ℝ)⁻¹
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, T, _, _, _, _, hs, _, _, hU, _⟩ :=
    h 3 0 1 (by decide) (by decide +kernel)
  have hz : sievePrimes 2 e T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨_, hprime, hd, _⟩ := Finset.mem_filter.mp hp
    exact hprime.not_dvd_one (by simpa using hd)
  change sievePrimes 2 e T = T at hU
  rw [hz] at hU
  rw [← hU] at hs
  simp at hs
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @split_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@split_support, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@split_support) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThreshold.split_support.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThreshold.Split.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Split

namespace Signed
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ x => x / 2 - Real.sqrt x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x d K A : ℝ} (_hx : 1 ≤ x) (_hd : 0 < d)
    (_hK : K ≤ d * A) (_h : 2 + 3 * A * Real.log x < Real.sqrt x),
    K * ((3 / 2 : ℝ) * Real.sqrt x * Real.log x) < d * R.readout () () x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (x := 16) (d := 1) (K := 0) (A := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 16, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @signed_margin) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signed_margin, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signed_margin) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThreshold.signed_margin.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThreshold.Signed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x / 2 - Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Signed

namespace CoveringParameters
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ N => N) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℕ) (_hx1 : 1 < x) (M N : ℝ)
    (_hsmall : ∀ d K : ℝ, 0 < d → K ≤ d * (4417 / 100) → K * M < d * N)
    (_hlarge : ∀ m : ℕ, (9699690 : ℝ) * 16 ^ m ≤ x → ∀ d K : ℝ,
      (610847 / 1616615 : ℝ) ≤ d →
      K = d * (2 ^ (m + 2) - 1) + (5 + d) * 2 ^ (m + 2) → K * M < d * N),
    ∃ (e : ℕ) (T : Finset ℕ), e ≠ 0 ∧
      (∀ q : ℕ, q.Prime → q ∣ x - 1 → q ∣ e ∨ q ∈ T) ∧
      0 < delta (sievePrimes x e T) ∧
      errorCoefficient (Nat.gcd e (x - 1)) (sievePrimes x e T) * M <
        delta (sievePrimes x e T) * R.readout () () N
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hsmall : ∀ d K : ℝ, 0 < d → K ≤ d * (4417 / 100) → K * 0 < d * 1 := by
    intro d K hd hK
    simpa using hd
  have hlarge : ∀ m : ℕ, (9699690 : ℝ) * 16 ^ m ≤ (2 : ℕ) → ∀ d K : ℝ,
      (610847 / 1616615 : ℝ) ≤ d →
      K = d * (2 ^ (m + 2) - 1) + (5 + d) * 2 ^ (m + 2) → K * 0 < d * 1 := by
    intro m hm
    have hp := one_le_pow₀ (show (1 : ℝ) ≤ 16 by norm_num) (n := m)
    norm_num only [Nat.cast_ofNat] at hm
    nlinarith
  obtain ⟨e, T, he, hc, hd, hm⟩ := h 2 (by decide) 0 1 hsmall hlarge
  norm_num [rejected, realize] at hm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% covering_parameters) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨covering_parameters, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    covering_parameters (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThreshold.covering_parameters.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThreshold.CoveringParameters.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CoveringParameters

end Reg.D5.S3.Arith.PrimitiveRoot.SieveThreshold
