import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport

open _root_.D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := ℕ
  State a := Fin (2 ^ a + 1) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ (a : ℕ), 3 ≤ a → ∀ (p : Fin (2 ^ a + 1) → ℝ),
    (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
    let t := Finset.univ.inf' (by exact ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩) p
    t ≤ ((2 : ℝ) ^ a - 1) / ((2 : ℝ) ^ a) ^ 2 →
      ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) * t -
        2 * ((2 : ℝ) ^ a - 1) ≤ R.readout () a p

def actual : Realization signature :=
  realize signature (fun _ _ p => cost p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -100) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  let p : Fin (2 ^ 3 + 1) → ℝ := fun i => if i = 0 then 1 else 0
  have hp : ∀ i, 0 ≤ p i := by intro i; simp only [p]; split_ifs <;> norm_num
  have hs : ∑ i, p i = 1 := by simp [p]
  let t := Finset.univ.inf' (by exact ⟨0, Finset.mem_univ _⟩) p
  have ht : t = 0 := by
    apply le_antisymm
    · have H := Finset.inf'_le p (Finset.mem_univ (1 : Fin (2 ^ 3 + 1)))
      simpa [p, t] using H
    · exact Finset.le_inf' _ p (fun i _ => hp i)
  have H := h 3 (by decide) p hp hs
  change t ≤ ((2 : ℝ) ^ 3 - 1) / ((2 : ℝ) ^ 3) ^ 2 →
    ((2 : ℝ) ^ 3 * ((3 : ℝ) + 2) + 2 * ((2 : ℝ) ^ 3) ^ 2) * t -
      2 * ((2 : ℝ) ^ 3 - 1) ≤ -100 at H
  norm_num [ht] at H

def proof_record : Registration arena
    (∀ (a : ℕ), 3 ≤ a → ∀ (p : Fin (2 ^ a + 1) → ℝ),
      (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      let t := Finset.univ.inf' (by exact ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩) p
      t ≤ ((2 : ℝ) ^ a - 1) / ((2 : ℝ) ^ a) ^ 2 →
        ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) * t -
          2 * ((2 : ℝ) ^ a - 1) ≤ cost p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.result,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨0, (fun _ => 0), (fun _ => 1 / 2), ?_⟩
    have hz : cost (fun _ : Fin (2 ^ 0 + 1) => (0 : ℝ)) = 0 := by
      simp [cost, _root_.D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual]
    have H := _root_.D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope.cost_ge_one
      2 (by decide) (fun _ => 1 / 2) (by norm_num) (by norm_num)
    change cost (fun _ : Fin (2 ^ 0 + 1) => (0 : ℝ)) ≠ cost (fun _ => 1 / 2)
    rw [hz]
    exact ne_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) H)

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.result)
    (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.result
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => cost p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Global

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ (a : ℕ), 3 ≤ a → ∀ (p : Fin (2 ^ a + 1) → ℝ),
    (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) *
        Finset.univ.inf' (by exact ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩) p -
          2 * ((2 : ℝ) ^ a - 1) ≤ R.readout () a p

theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  exact _root_.Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.rejected_law
    (fun a ha p hp hs _ => H a ha p hp hs)

def proof_record : Registration arena
    (∀ (a : ℕ), 3 ≤ a → ∀ (p : Fin (2 ^ a + 1) → ℝ),
      (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
        ((2 : ℝ) ^ a * ((a : ℝ) + 2) + 2 * ((2 : ℝ) ^ a) ^ 2) *
          Finset.univ.inf' (by exact ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩) p -
            2 * ((2 : ℝ) ^ a - 1) ≤ cost p) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.global_support,
    rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence :=
    _root_.Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.proof_record.dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.global_support)
    (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.global_support
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.Global.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => cost p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Global

namespace Uniform

open _root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ (a : ℕ), 3 ≤ a → R.readout () a (fun _ => 1 / ((2 : ℝ) ^ a + 1)) = 0

def actual : Realization signature :=
  realize signature (fun _ a p => support_gap a p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro H
  have bad := H 3 (by decide)
  norm_num [rejected, realize] at bad

theorem gap_dependence : ∀ i : Unit, ∃ (a : ℕ) (p q : Fin (2 ^ a + 1) → ℝ),
    actual.readout i a p ≠ actual.readout i a q := by
  intro i
  refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
  have hz : cost (fun _ : Fin (2 ^ 0 + 1) => (0 : ℝ)) = 0 := by
    simp [cost, _root_.D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual]
  have ho : cost (fun _ : Fin (2 ^ 0 + 1) => (1 : ℝ)) = 0 := by
    unfold cost _root_.D5.S3.Arith.FibonacciAtomic.DyadicSupportLines.residual
    have H (d : ℕ) : ⌊(2 : ℝ) ^ d⌋ = (2 : ℤ) ^ d := by
      exact_mod_cast Int.floor_natCast (2 ^ d)
    simp only [mul_one, H, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    change (∑' d : ℕ, ((2 : ℝ) ^ d - 2 * (2 : ℝ) ^ d) / (2 : ℝ) ^ d) = 0
    have E (d : ℕ) : ((2 : ℝ) ^ d - 2 * (2 : ℝ) ^ d) / (2 : ℝ) ^ d = -1 := by
      field_simp
      ring
    simp [E, tsum_const]
  change support_gap 0 (fun _ => 0) ≠ support_gap 0 (fun _ => 1)
  norm_num [support_gap, hz, ho, Finset.inf'_const]

def proof_record : Registration arena
    (∀ (a : ℕ), 3 ≤ a → support_gap a (fun _ => 1 / ((2 : ℝ) ^ a + 1)) = 0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨uniform_gap_zero, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := gap_dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.uniform_gap_zero)
    (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.uniform_gap_zero
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.Uniform.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a p => support_gap a p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Uniform

namespace High
open _root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
local notation "B" => (fun a : ℕ => (2 : ℝ) ^ a)
local notation "t0" => (fun a : ℕ => (B a - 1) / B a ^ 2)
local notation "H0" => (fun a : ℕ => (a : ℝ) + 2 - a / B a - 2 / B a ^ 2)
local notation "mn" => (fun (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) =>
  Finset.univ.inf' Finset.univ_nonempty p)

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ (a : ℕ), 3 ≤ a → ∀ (p : Fin (2 ^ a + 1) → ℝ),
    (∑ i, p i = 1) → t0 a < mn a p →
      (∀ i, 0 < high_transform a p i) ∧ (∑ i, high_transform a p i = 1) ∧
        R.readout () a p = H0 a + cost (high_transform a p) / B a ^ 2 ∧
        support_gap a p = support_gap a (high_transform a p) / B a ^ 2

def actual : Realization signature :=
  realize signature (fun _ _ p => cost p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -100) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let u : Fin (2 ^ 3 + 1) → ℝ := fun _ => 1 / 9
  have hs : ∑ i, u i = 1 := by norm_num [u]
  have ht : t0 3 < mn 3 u := by norm_num [u, Finset.inf'_const]
  have actual_high := high_scaling 3 (by decide) u hs ht
  have hc := (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope.law_data
    _ (high_transform 3 u) actual_high.2.1).2.2
  have hd : 0 ≤ cost (high_transform 3 u) / B 3 ^ 2 := div_nonneg hc (by positivity)
  have E := (h 3 (by decide) u hs ht).2.2.1
  change -100 = H0 3 + cost (high_transform 3 u) / B 3 ^ 2 at E
  norm_num at E hd
  linarith

def proof_record : Registration arena (type_of% (@high_scaling)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨high_scaling, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence :=
    _root_.Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.proof_record.dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.high_scaling) (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.high_scaling
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.High.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a p => cost p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end High

namespace Exit
open _root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
local notation "B" => (fun a : ℕ => (2 : ℝ) ^ a)
local notation "t0" => (fun a : ℕ => (B a - 1) / B a ^ 2)
local notation "H0" => (fun a : ℕ => (a : ℝ) + 2 - a / B a - 2 / B a ^ 2)
local notation "mn" => (fun (a : ℕ) (p : Fin (2 ^ a + 1) → ℝ) =>
  Finset.univ.inf' Finset.univ_nonempty p)

abbrev arena : Arena.{0, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ (a : ℕ), 3 ≤ a → ∀ (p : Fin (2 ^ a + 1) → ℝ),
    (∑ i, p i = 1) → t0 a < mn a p → (p ≠ fun _ => 1 / (B a + 1)) →
      ∃ n : ℕ, 0 < n ∧ (∀ k < n, t0 a < mn a (scaled_iterate a p k)) ∧
        (∀ i, 0 < scaled_iterate a p n i) ∧ (∑ i, scaled_iterate a p n i = 1) ∧
        0 < mn a (scaled_iterate a p n) ∧ mn a (scaled_iterate a p n) ≤ t0 a ∧
        R.readout () a p = support_gap a (scaled_iterate a p n) / (B a ^ 2) ^ n

def actual : Realization signature :=
  realize signature (fun _ a p => support_gap a p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -100) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  let p : Fin (2 ^ 3 + 1) → ℝ := fun i => if i = 0 then 72 / 640 else 71 / 640
  have hs : ∑ i, p i = 1 := by norm_num [p, Fin.sum_univ_succ]
  have ht : t0 3 < mn 3 p := by
    apply (Finset.lt_inf'_iff _).mpr
    intro i _
    dsimp [p]
    split_ifs <;> norm_num
  have hu : p ≠ fun _ => 1 / (B 3 + 1) := by
    intro H
    have E := congrFun H 0
    norm_num [p] at E
  obtain ⟨n, _, _, hp, hsn, _, _, he⟩ := h 3 (by decide) p hs ht hu
  have H := global_support 3 (by decide) (scaled_iterate 3 p n)
    (fun i => (hp i).le) hsn
  have HG : 0 ≤ support_gap 3 (scaled_iterate 3 p n) := by
    unfold support_gap
    linarith
  have HD : 0 ≤ support_gap 3 (scaled_iterate 3 p n) / (B 3 ^ 2) ^ n :=
    div_nonneg HG (by positivity)
  change -100 = support_gap 3 (scaled_iterate 3 p n) / (B 3 ^ 2) ^ n at he
  linarith

def proof_record : Registration arena (type_of% (@finite_exit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_exit, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence :=
    _root_.Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.Uniform.gap_dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.finite_exit) (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.finite_exit
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport.Exit.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a p => support_gap a p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Exit

end
end Reg.D5.S3.Arith.FibonacciAtomic.Dyadic.ComplementaryDyadicSecondSupport
