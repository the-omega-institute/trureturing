import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the full weighted reciprocal-floor comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants

open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

abbrev signature : Signature where
  Params := List ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a X =>
    (smoothSum (fun m => scale / (a.2 * m)) a.1 X 1 : ℝ) / scale)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ps : List ℕ), (∀ p ∈ ps, p.Prime) → ps.Nodup →
    ∀ {X d : ℕ}, (ps = [] → 1 ≤ X ∨ scale / d = 0) →
    R.readout () (ps, d) X ≤
      ∑ m ∈ factoredMultiples ps.toFinset X 1, 1 / ((d : ℝ) * m)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := h [] (by simp) (by simp) (X := 1) (d := 1) (fun _ => Or.inl le_rfl)
  have hset : factoredMultiples ∅ 1 1 = {1} := by decide +kernel
  norm_num [rejected, realize, hset] at hh

def family : Registration arena (type_of% (@smooth_floor_sum_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨smooth_floor_sum_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨([2], 1), 0, 1, ?_⟩
    have hz : powSum 64 (fun m => scale / (1 * m)) 2 0 1 = 0 := by rfl
    have ho : powSum 64 (fun m => scale / (1 * m)) 2 1 1 = scale := by decide +kernel
    change ((powSum 64 (fun m => scale / (1 * m)) 2 0 1 : ℕ) : ℝ) / scale ≠
      ((powSum 64 (fun m => scale / (1 * m)) 2 1 1 : ℕ) : ℝ) / scale
    rw [hz, ho]
    norm_num [scale]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smooth_floor_sum_le) (Realization signature)
    ((ℕ → ℕ) → List ℕ → ℕ → ℕ → ℕ) Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.smooth_floor_sum_le.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a X =>
    (smoothSum (fun m => scale / (a.2 * m)) a.1 X 1 : ℝ) / scale)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev eulerSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def eulerActual : Realization eulerSignature :=
  realize eulerSignature (fun _ _ p => LongGapsBetweenPrimes.eulerProduct p 1)
    (fun e => nomatch e)

def eulerRejected : Realization eulerSignature :=
  realize eulerSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev eulerArena : Arena where
  signature := eulerSignature
  Law R := ∀ {p : ℕ},
    R.readout () () p = ((tailData p).1 : ℝ) / (tailData p).2.1 ↔ p ≤ 100

private theorem eulerRejected_law : ¬eulerArena.Law eulerRejected := by
  intro h
  have hh := (h (p := 3)).mpr (by decide)
  norm_num [eulerRejected, realize, tailData, allPrimes, oddPrimes] at hh

def eulerFamily : Registration eulerArena (type_of% (@tail_euler_ratio)) where
  actual := eulerActual
  bridge := Iff.rfl
  variation := ⟨tail_euler_ratio, eulerRejected, eulerRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eulerRejected, ?_, rfl, eulerRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    have hzero : Nat.primesLE 0 = ∅ := by decide
    have htwo : Nat.primesLE 2 = {2} := by decide
    norm_num [eulerActual, realize, LongGapsBetweenPrimes.eulerProduct, hzero, htwo,
      Real.rpow_neg_one]

def eulerAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tail_euler_ratio) (Realization eulerSignature) (ℕ → ℝ → ℝ) Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.tail_euler_ratio.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants.eulerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨eulerArena⟩
  objectArena := .source ⟨eulerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source eulerArena ⟨eulerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eulerSignature
    (fun _ _ p => LongGapsBetweenPrimes.eulerProduct p 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def floorActual : Realization eulerSignature :=
  realize eulerSignature (fun _ _ p => ((tailData p).2.2 : ℝ) / scale)
    (fun e => nomatch e)

def floorRejected : Realization eulerSignature :=
  realize eulerSignature (fun _ _ _ => 1000000) (fun e => nomatch e)

abbrev floorArena : Arena where
  signature := eulerSignature
  Law R := ∀ (p : ℕ), R.readout () () p ≤
    ∑ m ∈ factoredMultiples (allPrimes.filter (· ≤ p)).toFinset
      (bound / (2 * p)) 1, 1 / (2 * (p : ℝ) * m)

private theorem floorRejected_law : ¬floorArena.Law floorRejected := by
  intro h
  let S := factoredMultiples (allPrimes.filter (· ≤ 3)).toFinset (bound / (2 * 3)) 1
  have hh := h 3
  change (1000000 : ℝ) ≤ ∑ m ∈ S, 1 / (2 * (3 : ℝ) * m) at hh
  have hcard : S.card ≤ 166666 := by
    have hsub := card_le_card
      (show S ⊆ Icc 1 (bound / (2 * 3)) from filter_subset _ _)
    have hsub' : S.card ≤ bound / (2 * 3) := by
      simpa only [S, Nat.card_Icc, Nat.add_sub_cancel] using hsub
    exact hsub'.trans (by norm_num [bound])
  have hcard' : (S.card : ℝ) ≤ 166666 := by exact_mod_cast hcard
  have hsum : (∑ m ∈ S, 1 / (2 * (3 : ℝ) * m)) ≤ S.card := by
    calc
      _ ≤ ∑ _m ∈ S, (1 : ℝ) := by
        apply sum_le_sum
        intro m hm
        have hm1 : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hm).1).1
        have hden : (1 : ℝ) ≤ 2 * (3 : ℝ) * m := by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          linarith
        rw [one_div]
        exact inv_le_one_of_one_le₀ hden
      _ = _ := by simp
  linarith

def floorFamily : Registration floorArena (type_of% (@tail_floor_sum_le)) where
  actual := floorActual
  bridge := Iff.rfl
  variation := ⟨tail_floor_sum_le, floorRejected, floorRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨floorRejected, ?_, rfl, floorRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [floorActual, realize, tailData, allPrimes, oddPrimes, smoothSum, scale]

def floorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tail_floor_sum_le) (Realization eulerSignature) (ℕ → ℕ × ℕ × ℕ) Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.tail_floor_sum_le.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants.floorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨floorArena⟩
  objectArena := .source ⟨floorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source floorArena ⟨floorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eulerSignature
    (fun _ _ p => ((tailData p).2.2 : ℝ) / scale) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev tailSignature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def tailActual : Realization tailSignature :=
  realize tailSignature (fun _ _ T => ∑ q ∈ T, 1 / (q : ℝ)) (fun e => nomatch e)

def tailRejected : Realization tailSignature :=
  realize tailSignature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev tailArena : Arena where
  signature := tailSignature
  Law R := ∀ {p b fs : ℕ}, 0 < p → ∀ T : Finset ℕ,
    (∀ q ∈ T, ∃ m : ℕ, b < m ∧ q = 2 * p * m + 1 ∧
      m ∈ Nat.smoothNumbers (p + 1)) →
    ((fs : ℝ) / scale ≤
      ∑ m ∈ (Icc 1 b).filter (fun m => m ∈ Nat.smoothNumbers (p + 1)),
        1 / (2 * (p : ℝ) * m)) →
    R.readout () () T ≤
      LongGapsBetweenPrimes.eulerProduct p 1 / (2 * (p : ℝ)) - (fs : ℝ) / scale ∧
    (T.Nonempty → R.readout () () T <
      LongGapsBetweenPrimes.eulerProduct p 1 / (2 * (p : ℝ)) - (fs : ℝ) / scale)

private theorem tailRejected_law : ¬tailArena.Law tailRejected := by
  intro h
  have hh := (h (p := 1) (b := 0) (fs := 0) (by decide) ∅ (by simp) (by simp)).1
  have he : Nat.primesLE 1 = ∅ := by decide
  change (2 : ℝ) ≤ LongGapsBetweenPrimes.eulerProduct 1 1 /
    (2 * ((1 : ℕ) : ℝ)) - ((0 : ℕ) : ℝ) / scale at hh
  have heuler : LongGapsBetweenPrimes.eulerProduct 1 1 = 1 := by
    simp only [LongGapsBetweenPrimes.eulerProduct, he, Finset.prod_empty]
  rw [heuler] at hh
  norm_num at hh

def tailFamily : Registration tailArena (type_of% (@reciprocal_tail_bound)) where
  actual := tailActual
  bridge := Iff.rfl
  variation := ⟨reciprocal_tail_bound, tailRejected, tailRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨tailRejected, ?_, rfl, tailRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(), ∅, {1}, ?_⟩
    change (∑ q ∈ (∅ : Finset ℕ), 1 / (q : ℝ)) ≠
      ∑ q ∈ ({1} : Finset ℕ), 1 / (q : ℝ)
    simp only [Finset.sum_empty, Finset.sum_singleton, Nat.cast_one, div_one]
    exact zero_ne_one

def tailAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reciprocal_tail_bound) (Realization tailSignature) Type Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.reciprocal_tail_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants.tailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source tailArena ⟨tailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tailSignature (fun _ _ T => ∑ q ∈ T, 1 / (q : ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.TailConstants
