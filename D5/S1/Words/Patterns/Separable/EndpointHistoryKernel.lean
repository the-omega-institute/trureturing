/- GID: D5/S1/Words/Patterns/Separable/EndpointHistoryKernel
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointHistoryKernel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual endpoint histories preserve minimum cuts, counts, and absolute cylinders. -/

import D5.S1.Words.Patterns.Separable.MinimumCutKernel
import Mathlib.Data.List.OfFn

/-!
Histories describe subsets of actual avoiding permutations. A blocked sign means
absence of that proper-cut sign, including the genuine singleton convention.
Left endpoints reset to the whole actual class; right endpoints condition the
remaining actual factor to be indecomposable for the current sign. No limiting
probability or count asymptotic is an input. All statements are symbolic and
unbounded, rather than bounded enumeration or certified finite instances.
-/

namespace D5.S1.Words.Patterns.Separable.EndpointHistoryKernel

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.ProperCut (pattern2413 pattern3142)

def Allowed {length : ℕ} (state : Option Bool) (π : Avoider length) : Prop :=
  match state with
  | none => True
  | some sign => ¬HasProperCut sign π.val

abbrev Carrier (state : Option Bool) (length : ℕ) :=
  {π : Avoider length // Allowed state π}

def indecomposableWitness (sign : Bool) (length : ℕ) : Indecomposable sign length := by
  cases sign
  · have avoids : Avoids (Fin.revPerm : Equiv.Perm (Fin length)) := by
      constructor
      · rintro ⟨embedding, order⟩
        have increasing := (order 0 1).mp
          (show pattern2413 (0 : Fin 4) < pattern2413 1 by decide)
        exact lt_asymm increasing
          (Fin.rev_strictAnti (embedding.strictMono (show (0 : Fin 4) < 1 by decide)))
      · rintro ⟨embedding, order⟩
        have increasing := (order 1 2).mp
          (show pattern3142 (1 : Fin 4) < pattern3142 2 by decide)
        exact lt_asymm increasing
          (Fin.rev_strictAnti (embedding.strictMono (show (1 : Fin 4) < 2 by decide)))
    refine ⟨⟨Fin.revPerm, avoids⟩, ?_⟩
    rintro ⟨cut, hpositive, hproper, comparison⟩
    let first : Fin length := ⟨0, by omega⟩
    let last : Fin length := ⟨length - 1, by omega⟩
    have increasing := comparison first last (by dsimp [first]; omega)
      (by dsimp [last]; omega)
    exact lt_asymm increasing (Fin.rev_strictAnti (show first < last by
      change (0 : ℕ) < length - 1; omega))
  · refine ⟨identityAvoider length, ?_⟩
    rintro ⟨cut, hpositive, hproper, comparison⟩
    let first : Fin length := ⟨0, by omega⟩
    let last : Fin length := ⟨length - 1, by omega⟩
    have decreasing := comparison first last (by dsimp [first]; omega)
      (by dsimp [last]; omega)
    exact lt_asymm decreasing (show first < last by change (0 : ℕ) < length - 1; omega)

def carrierWitness (state : Option Bool) (length : ℕ) : Carrier state length := by
  cases state with
  | none => exact ⟨identityAvoider length, trivial⟩
  | some sign => exact indecomposableWitness sign length

inductive EndpointHistory : Option Bool → ℕ → Type where
  | stop (state : Option Bool) (length : ℕ) : EndpointHistory state length
  | emit {state : Option Bool} {left right : ℕ} (sign : Bool)
      (hleft : 0 < left) (hright : 0 < right)
      (compatible : state = none ∨ state = some (!sign))
      (shape : Indecomposable sign left) (tail : EndpointHistory none right) :
      EndpointHistory state (left + right)
  | discard {state : Option Bool} {left right : ℕ} (sign : Bool)
      (hleft : 0 < left) (hright : 0 < right)
      (compatible : state = none ∨ state = some (!sign))
      (shape : Avoider right) (tail : EndpointHistory (some sign) left) :
      EndpointHistory state (left + right)

namespace EndpointHistory

def remaining {state length} : EndpointHistory state length → ℕ
  | .stop _ length => length
  | .emit _ _ _ _ _ tail => tail.remaining
  | .discard _ _ _ _ _ tail => tail.remaining

def remainingState {state length} : EndpointHistory state length → Option Bool
  | .stop state _ => state
  | .emit _ _ _ _ _ tail => tail.remainingState
  | .discard _ _ _ _ _ tail => tail.remainingState

abbrev Leaf {state length} (history : EndpointHistory state length) :=
  Carrier history.remainingState history.remaining

def assemble {state length} (history : EndpointHistory state length) :
    history.Leaf → Avoider length :=
  match history with
  | .stop _ _ => fun sample => sample.val
  | .emit sign _ _ _ shape tail => fun sample =>
      ⟨blockSum sign shape.val.val (tail.assemble sample).val,
        (avoids_block_sum_iff sign _ _).mpr ⟨shape.val.property, (tail.assemble sample).property⟩⟩
  | .discard sign _ _ _ shape tail => fun sample =>
      ⟨blockSum sign (tail.assemble sample).val shape.val,
        (avoids_block_sum_iff sign _ _).mpr ⟨(tail.assemble sample).property, shape.property⟩⟩

def Trace {state length} : (history : EndpointHistory state length) → history.Leaf → Prop
  | .stop _ _, _ => True
  | .emit (left := left) sign _ _ _ shape tail, sample =>
      MinimumCut sign (blockSum sign shape.val.val (tail.assemble sample).val) left ∧
        tail.Trace sample
  | .discard (left := left) sign _ _ _ shape tail, sample =>
      MinimumCut sign (blockSum sign (tail.assemble sample).val shape.val) left ∧
        tail.Trace sample

def Event {state length} (history : EndpointHistory state length) (π : Avoider length) : Prop :=
  ∃ sample : history.Leaf, history.assemble sample = π

def EventFor {state length} (history : EndpointHistory state length)
    (terminalEvent : history.Leaf → Prop) (π : Avoider length) : Prop :=
  ∃ sample : history.Leaf, terminalEvent sample ∧ history.assemble sample = π

noncomputable def weight {state length} : EndpointHistory state length → ℝ
  | .stop _ _ => 1
  | .emit (state := state) (left := left) (right := right) _ _ _ _ _ tail =>
      ((Nat.card (Carrier none right) : ℝ) / Nat.card (Carrier state (left + right))) * tail.weight
  | .discard (state := state) (left := left) (right := right) sign _ _ _ _ tail =>
      ((Nat.card (Carrier (some sign) left) : ℝ) /
        Nat.card (Carrier state (left + right))) * tail.weight

def emitted {state length} : EndpointHistory state length → ℕ
  | .stop _ _ => 0
  | .emit (left := left) _ _ _ _ _ tail => left + tail.emitted
  | .discard _ _ _ _ _ tail => tail.emitted

def steps {state length} : EndpointHistory state length → ℕ
  | .stop _ _ => 0
  | .emit _ _ _ _ _ tail => 1 + tail.steps
  | .discard _ _ _ _ _ tail => 1 + tail.steps

def removed {state length} : EndpointHistory state length → ℕ
  | .stop _ _ => 0
  | .emit (left := left) _ _ _ _ _ tail => left + tail.removed
  | .discard (right := right) _ _ _ _ _ tail => right + tail.removed

def Capped {state length} (cap : ℕ) : EndpointHistory state length → Prop
  | .stop _ _ => True
  | .emit (left := left) _ _ _ _ _ tail => left ≤ cap ∧ tail.Capped cap
  | .discard (right := right) _ _ _ _ _ tail => right ≤ cap ∧ tail.Capped cap

def label (alphabet value : ℕ) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

def word {state length} (history : EndpointHistory state length) (alphabet low : ℕ) :
    List (Option (Fin alphabet)) :=
  match history with
  | .stop _ _ => []
  | .emit (left := left) sign _ _ _ shape tail =>
      (if sign then List.replicate left none
        else List.ofFn (fun position => label alphabet (low + (shape.val.val position).val))) ++
        tail.word alphabet (low + if sign then 0 else left)
  | .discard (right := right) sign _ _ _ _ tail =>
      tail.word alphabet (low + if sign then right else 0)

def literal {length} (π : Avoider length) (alphabet low : ℕ) : List (Option (Fin alphabet)) :=
  List.ofFn (fun position => label alphabet (low + (π.val position).val))

def AbsoluteNoFixed {length} (positions : ℕ) (π : Avoider length) : Prop :=
  ∀ position : Fin length, position.val < positions → π.val position ≠ position

def NoFixedWord (positions : ℕ) (record : List (Option (Fin positions))) : Prop :=
  ∀ position : Fin positions, record[position.val]? ≠ some (some position)

end EndpointHistory

open Classical in
theorem endpoint_history_count_kernel {state : Option Bool} {length : ℕ}
    (history : EndpointHistory state length) :
    (∀ sample : history.Leaf,
      Allowed state (history.assemble sample) ∧ history.Trace sample) ∧
    Function.Injective history.assemble ∧
    Nat.card {π : Avoider length // history.Event π} = Nat.card history.Leaf ∧
    actualMass length history.Event / actualMass length (Allowed state) = history.weight ∧
    history.emitted + history.remaining ≤ length ∧
    history.removed + history.remaining = length ∧
    (∀ cap, history.Capped cap → history.removed ≤ history.steps * cap) ∧
    (∀ terminalEvent : history.Leaf → Prop,
      Nat.card {π : Avoider length // history.EventFor terminalEvent π} =
        Nat.card {sample : history.Leaf // terminalEvent sample} ∧
      actualMass length (history.EventFor terminalEvent) / actualMass length history.Event =
        (Nat.card {sample : history.Leaf // terminalEvent sample} : ℝ) /
          Nat.card history.Leaf) ∧
    (∀ sign, 2 ≤ length → ∀ π : Avoider length,
      Allowed (some (!sign)) π ↔ HasProperCut sign π.val) := by
  classical
  have incompatible {size : ℕ} (sign : Bool) (π : Equiv.Perm (Fin size)) :
      HasProperCut sign π → ¬HasProperCut (!sign) π := by
    rintro ⟨firstCut, hfirst, hfirstBound, firstComparison⟩
      ⟨lastCut, hlast, hlastBound, lastComparison⟩
    let first : Fin size := ⟨0, by omega⟩
    let last : Fin size := ⟨size - 1, by omega⟩
    have firstOrder := firstComparison first last (by dsimp [first]; omega)
      (by dsimp [last]; omega)
    have lastOrder := lastComparison first last (by dsimp [first]; omega)
      (by dsimp [last]; omega)
    cases sign <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at firstOrder lastOrder <;> exact lt_asymm firstOrder lastOrder
  have structural : ∀ {root size} (path : EndpointHistory root size),
      (∀ sample : path.Leaf, Allowed root (path.assemble sample) ∧ path.Trace sample) ∧
      Function.Injective path.assemble ∧ path.emitted + path.remaining ≤ size ∧
      path.removed + path.remaining = size ∧
      (∀ cap, path.Capped cap → path.removed ≤ path.steps * cap) := by
    intro root size path
    induction path with
    | stop root size =>
      exact ⟨fun sample => ⟨sample.property, trivial⟩, Subtype.val_injective,
        by simp [EndpointHistory.emitted, EndpointHistory.remaining],
        by simp [EndpointHistory.removed, EndpointHistory.remaining],
        by simp [EndpointHistory.removed, EndpointHistory.steps]⟩
    | @emit root left right sign hleft hright compatible shape tail induction =>
      obtain ⟨equivalence, reconstruction, _, _, _⟩ :=
        minimum_cut_cartesian_kernel sign left right hleft hright
      have minimal (sample : tail.Leaf) :
          MinimumCut sign (blockSum sign shape.val.val (tail.assemble sample).val) left := by
        have certificate := (equivalence (shape, tail.assemble sample)).property
        rw [reconstruction] at certificate
        exact certificate
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro sample
        refine ⟨?_, minimal sample, (induction.1 sample).2⟩
        rcases compatible with rfl | rfl
        · trivial
        · exact incompatible sign _ ⟨left, hleft, by omega, (minimal sample).1⟩
      · intro first last equality
        have fiberEq : equivalence (shape, tail.assemble first) =
            equivalence (shape, tail.assemble last) := by
          apply Subtype.ext
          apply Subtype.ext
          rw [reconstruction, reconstruction]
          exact congrArg Subtype.val equality
        exact induction.2.1 (congrArg Prod.snd (equivalence.injective fiberEq))
      · dsimp [EndpointHistory.emitted, EndpointHistory.remaining]
        have := induction.2.2.1
        omega
      · dsimp [EndpointHistory.removed, EndpointHistory.remaining]
        have := induction.2.2.2.1
        omega
      · intro cap hcap
        obtain ⟨hsmall, htail⟩ := hcap
        have bound := induction.2.2.2.2 cap htail
        dsimp [EndpointHistory.removed, EndpointHistory.steps]
        rw [Nat.add_mul, one_mul]
        omega
    | @discard root left right sign hleft hright compatible shape tail induction =>
      obtain ⟨equivalence, reconstruction, _, _, _⟩ :=
        minimum_cut_cartesian_kernel sign left right hleft hright
      let remainingFactor (sample : tail.Leaf) : Indecomposable sign left :=
        ⟨tail.assemble sample, (induction.1 sample).1⟩
      have minimal (sample : tail.Leaf) :
          MinimumCut sign (blockSum sign (tail.assemble sample).val shape.val) left := by
        have certificate := (equivalence (remainingFactor sample, shape)).property
        rw [reconstruction] at certificate
        exact certificate
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro sample
        refine ⟨?_, minimal sample, (induction.1 sample).2⟩
        rcases compatible with rfl | rfl
        · trivial
        · exact incompatible sign _ ⟨left, hleft, by omega, (minimal sample).1⟩
      · intro first last equality
        have fiberEq : equivalence (remainingFactor first, shape) =
            equivalence (remainingFactor last, shape) := by
          apply Subtype.ext
          apply Subtype.ext
          rw [reconstruction, reconstruction]
          exact congrArg Subtype.val equality
        have factorEq := congrArg Prod.fst (equivalence.injective fiberEq)
        exact induction.2.1 (congrArg Subtype.val factorEq)
      · dsimp [EndpointHistory.emitted, EndpointHistory.remaining]
        have := induction.2.2.1
        omega
      · dsimp [EndpointHistory.removed, EndpointHistory.remaining]
        have := induction.2.2.2.1
        omega
      · intro cap hcap
        obtain ⟨hsmall, htail⟩ := hcap
        have bound := induction.2.2.2.2 cap htail
        dsimp [EndpointHistory.removed, EndpointHistory.steps]
        rw [Nat.add_mul, one_mul]
        omega
  have data := structural history
  have counts : Nat.card {π : Avoider length // history.Event π} = Nat.card history.Leaf := by
    let mapping : history.Leaf → {π : Avoider length // history.Event π} :=
      fun sample => ⟨history.assemble sample, sample, rfl⟩
    have bijective : Function.Bijective mapping := by
      constructor
      · intro first last equality
        exact data.2.1 (congrArg Subtype.val equality)
      · rintro ⟨π, sample, equality⟩
        exact ⟨sample, Subtype.ext equality⟩
    exact (Nat.card_congr (Equiv.ofBijective mapping bijective)).symm
  have mass {size : ℕ} (event : Avoider size → Prop) : actualMass size event =
      (Nat.card {π : Avoider size // event π} : ℝ) / Nat.card (Avoider size) := by
    let : Nonempty (Avoider size) := ⟨identityAvoider size⟩
    change ((PMF.uniformOfFintype (Avoider size)).toOuterMeasure {π | event π}).toReal = _
    rw [PMF.toOuterMeasure_uniformOfFintype_apply]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.card_eq_fintype_card]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight
      (fun π : Avoider size => show (π ∈ {π | event π}) ↔ event π from Iff.rfl))]
  have telescope : ∀ {root size} (path : EndpointHistory root size),
      (Nat.card path.Leaf : ℝ) / Nat.card (Carrier root size) = path.weight := by
    intro root size path
    induction path with
    | stop root size =>
      let : Nonempty (Carrier root size) := ⟨carrierWitness root size⟩
      have positive : (Nat.card (Carrier root size) : ℝ) ≠ 0 :=
        by exact_mod_cast (Nat.card_pos (α := Carrier root size)).ne'
      simpa [EndpointHistory.Leaf, EndpointHistory.remaining,
        EndpointHistory.remainingState, EndpointHistory.weight] using div_self positive
    | @emit root left right sign hleft hright compatible shape tail induction =>
      let : Nonempty (Carrier none right) := ⟨carrierWitness none right⟩
      have positive : (Nat.card (Carrier none right) : ℝ) ≠ 0 :=
        by exact_mod_cast (Nat.card_pos (α := Carrier none right)).ne'
      dsimp [EndpointHistory.weight, EndpointHistory.Leaf, EndpointHistory.remaining,
        EndpointHistory.remainingState]
      rw [← induction]
      field_simp
    | @discard root left right sign hleft hright compatible shape tail induction =>
      let : Nonempty (Carrier (some sign) left) := ⟨carrierWitness (some sign) left⟩
      have positive : (Nat.card (Carrier (some sign) left) : ℝ) ≠ 0 :=
        by exact_mod_cast (Nat.card_pos (α := Carrier (some sign) left)).ne'
      dsimp [EndpointHistory.weight, EndpointHistory.Leaf, EndpointHistory.remaining,
        EndpointHistory.remainingState]
      rw [← induction]
      field_simp
  refine ⟨data.1, data.2.1, counts, ?_, data.2.2.1, data.2.2.2.1,
    data.2.2.2.2, ?_, ?_⟩
  · rw [mass, mass, counts]
    let : Nonempty (Avoider length) := ⟨identityAvoider length⟩
    have positive : (Nat.card (Avoider length) : ℝ) ≠ 0 :=
      by exact_mod_cast (Nat.card_pos (α := Avoider length)).ne'
    rw [div_div_div_cancel_right₀ positive]
    exact telescope history
  · intro terminalEvent
    let mapping : {sample : history.Leaf // terminalEvent sample} →
        {π : Avoider length // history.EventFor terminalEvent π} :=
      fun sample => ⟨history.assemble sample.val, sample.val, sample.property, rfl⟩
    have bijective : Function.Bijective mapping := by
      constructor
      · intro first last equality
        exact Subtype.ext (data.2.1 (congrArg Subtype.val equality))
      · rintro ⟨π, sample, hsample, equality⟩
        exact ⟨⟨sample, hsample⟩, Subtype.ext equality⟩
    have restrictedCount := (Nat.card_congr (Equiv.ofBijective mapping bijective)).symm
    refine ⟨restrictedCount, ?_⟩
    rw [mass, mass, counts, restrictedCount]
    let : Nonempty (Avoider length) := ⟨identityAvoider length⟩
    have positive : (Nat.card (Avoider length) : ℝ) ≠ 0 :=
      by exact_mod_cast (Nat.card_pos (α := Avoider length)).ne'
    rw [div_div_div_cancel_right₀ positive]
  · intro sign hlength π
    constructor
    · intro absent
      obtain ⟨cut, hpositive, hproper, comparison⟩ :=
        D5.S1.Words.Patterns.Separable.ProperCut.avoidance_proper_cut hlength
          π.val π.property.1 π.property.2
      cases sign <;> rcases comparison with direct | skew
      · exact ⟨cut, by omega, hproper, direct⟩
      · exact (absent ⟨cut, by omega, hproper, skew⟩).elim
      · exact (absent ⟨cut, by omega, hproper, direct⟩).elim
      · exact ⟨cut, by omega, hproper, skew⟩
    · exact incompatible sign π.val

open Classical in
theorem endpoint_history_literal_cylinder {state : Option Bool} {length : ℕ}
    (history : EndpointHistory state length) :
    (∀ alphabet low (sample : history.Leaf), alphabet < history.remaining →
      (EndpointHistory.literal (history.assemble sample) alphabet low).take history.emitted =
        history.word alphabet low) ∧
    (∀ alphabet positions, alphabet < history.remaining → positions ≤ history.emitted →
      ∀ test : List (Option (Fin alphabet)) → Prop,
        actualMass length (fun π => history.Event π ∧
          test ((EndpointHistory.literal π alphabet 0).take positions)) =
          if test ((history.word alphabet 0).take positions)
          then actualMass length history.Event else 0) ∧
    (∀ alphabet horizon cap, history.steps ≤ horizon → history.Capped cap →
      horizon * cap + alphabet < length →
      ∀ low (sample : history.Leaf),
        (EndpointHistory.literal (history.assemble sample) alphabet low).take history.emitted =
          history.word alphabet low) ∧
    (∀ positions, positions < history.remaining → positions ≤ history.emitted →
      actualMass length (fun π => history.Event π ∧ EndpointHistory.AbsoluteNoFixed positions π) =
        if EndpointHistory.NoFixedWord positions ((history.word positions 0).take positions)
        then actualMass length history.Event else 0) := by
  classical
  have leftval {left right : ℕ} (sign : Bool) (α : Equiv.Perm (Fin left))
      (β : Equiv.Perm (Fin right)) (position : Fin left) :
      (blockSum sign α β (Fin.castAdd right position)).val =
        (if sign then right else 0) + (α position).val := by
    cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
  have rightval {left right : ℕ} (sign : Bool) (α : Equiv.Perm (Fin left))
      (β : Equiv.Perm (Fin right)) (position : Fin right) :
      (blockSum sign α β (Fin.natAdd left position)).val =
        (if sign then 0 else left) + (β position).val := by
    cases sign <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
  have splitList {left right : ℕ} (sign : Bool) (α : Avoider left) (β : Avoider right)
      (alphabet low : ℕ) :
      EndpointHistory.literal
          ⟨blockSum sign α.val β.val,
            (avoids_block_sum_iff sign _ _).mpr ⟨α.property, β.property⟩⟩ alphabet low =
        EndpointHistory.literal α alphabet (low + if sign then right else 0) ++
          EndpointHistory.literal β alphabet (low + if sign then 0 else left) := by
    unfold EndpointHistory.literal
    rw [List.ofFn_add]
    have leftCast (position : Fin left) :
        position.castLE (Nat.le_add_right left right) = Fin.castAdd right position := Fin.ext rfl
    simp_rw [leftCast, leftval, rightval, Nat.add_assoc]
  have transport : ∀ {root size} (path : EndpointHistory root size),
      ∀ alphabet low (sample : path.Leaf), alphabet < path.remaining →
        (EndpointHistory.literal (path.assemble sample) alphabet low).take path.emitted =
          path.word alphabet low := by
    intro root size path
    induction path with
    | stop root size =>
      intro alphabet low sample hremaining
      simp [EndpointHistory.emitted, EndpointHistory.word]
    | @emit root left right sign hleft hright compatible shape tail induction =>
      intro alphabet low sample hremaining
      change tail.Leaf at sample
      change alphabet < tail.remaining at hremaining
      have bounds := (endpoint_history_count_kernel tail).2.2.2.2.1
      have high (position : Fin left) :
          EndpointHistory.label alphabet (low + right + (shape.val.val position).val) = none := by
        apply dif_neg
        omega
      change (EndpointHistory.literal
        ⟨blockSum sign shape.val.val (tail.assemble sample).val, _⟩ alphabet low).take
          (left + tail.emitted) = _
      rw [splitList, List.take_append]
      have firstLength : (EndpointHistory.literal shape.val alphabet
          (low + if sign then right else 0)).length = left := by
        simp [EndpointHistory.literal]
      rw [firstLength, Nat.add_sub_cancel_left,
        List.take_of_length_le (by rw [firstLength]; omega),
        induction alphabet _ sample hremaining]
      cases sign
      · simp [EndpointHistory.word, EndpointHistory.literal]
      · simp only [EndpointHistory.word, ↓reduceIte, Nat.add_zero]
        unfold EndpointHistory.literal
        simp_rw [high]
        rw [List.ofFn_const]
    | @discard root left right sign hleft hright compatible shape tail induction =>
      intro alphabet low sample hremaining
      change tail.Leaf at sample
      change alphabet < tail.remaining at hremaining
      have bounds := (endpoint_history_count_kernel tail).2.2.2.2.1
      change (EndpointHistory.literal
        ⟨blockSum sign (tail.assemble sample).val shape.val, _⟩ alphabet low).take
          tail.emitted = _
      rw [splitList, List.take_append_of_le_length (by
        simp only [EndpointHistory.literal, List.length_ofFn]; omega)]
      exact induction alphabet _ sample hremaining
  have cylinders : ∀ alphabet positions, alphabet < history.remaining →
      positions ≤ history.emitted → ∀ test : List (Option (Fin alphabet)) → Prop,
        actualMass length (fun π => history.Event π ∧
          test ((EndpointHistory.literal π alphabet 0).take positions)) =
          if test ((history.word alphabet 0).take positions)
          then actualMass length history.Event else 0 := by
    intro alphabet positions hremaining hemitted test
    have constantWord (π : Avoider length) (hevent : history.Event π) :
        (EndpointHistory.literal π alphabet 0).take positions =
          (history.word alphabet 0).take positions := by
      obtain ⟨sample, rfl⟩ := hevent
      have agreement := congrArg (List.take positions)
        (transport history alphabet 0 sample hremaining)
      simpa only [List.take_take, Nat.min_eq_left hemitted] using agreement
    by_cases htest : test ((history.word alphabet 0).take positions)
    · rw [if_pos htest]
      congr 1
      funext π
      apply propext
      constructor
      · exact And.left
      · intro hevent
        exact ⟨hevent, by rw [constantWord π hevent]; exact htest⟩
    · rw [if_neg htest]
      have emptyEvent : (fun π : Avoider length => history.Event π ∧
          test ((EndpointHistory.literal π alphabet 0).take positions)) = fun _ => False := by
        funext π
        apply propext
        constructor
        · rintro ⟨hevent, htestActual⟩
          rw [constantWord π hevent] at htestActual
          exact htest htestActual
        · exact False.elim
      rw [emptyEvent]
      unfold actualMass
      simp
  refine ⟨transport history, cylinders, ?_, ?_⟩
  · intro alphabet horizon cap hsteps hcap hlength low sample
    have counts := endpoint_history_count_kernel history
    have removed := counts.2.2.2.2.2.2.1 cap hcap
    have lengthEq := counts.2.2.2.2.2.1
    have scaled : history.steps * cap ≤ horizon * cap := Nat.mul_le_mul_right cap hsteps
    exact transport history alphabet low sample (by omega)
  · intro positions hremaining hemitted
    have sourceBound := (endpoint_history_count_kernel history).2.2.2.2.1
    have hpositions : positions ≤ length := by omega
    have labelEq (value : ℕ) (position : Fin positions) :
        EndpointHistory.label positions value = some position ↔ value = position.val := by
      unfold EndpointHistory.label
      split_ifs with bounded
      · simp [Fin.ext_iff]
      · simp only [false_iff]
        intro equality
        apply bounded
        rw [equality]
        exact position.isLt
    have dictionary (π : Avoider length) : EndpointHistory.AbsoluteNoFixed positions π ↔
        EndpointHistory.NoFixedWord positions
          ((EndpointHistory.literal π positions 0).take positions) := by
      have read (position : Fin positions) :
          ((EndpointHistory.literal π positions 0).take positions)[position.val]? =
            some (EndpointHistory.label positions
              (π.val ⟨position.val, by omega⟩).val) := by
        have inLength : position.val < length := by omega
        simp [EndpointHistory.literal, position.isLt, inLength]
      constructor
      · intro noFixed position equality
        have encoded := Option.some.inj ((read position).symm.trans equality)
        exact noFixed ⟨position.val, by omega⟩ position.isLt (Fin.ext ((labelEq _ _).mp encoded))
      · intro wordFree position hposition equality
        let index : Fin positions := ⟨position.val, hposition⟩
        apply wordFree index
        rw [read index]
        apply congrArg some
        apply (labelEq _ index).mpr
        have indexEq : (⟨index.val, by omega⟩ : Fin length) = position := Fin.ext rfl
        rw [indexEq, equality]
    have eventEq :
        (fun π : Avoider length => history.Event π ∧ EndpointHistory.AbsoluteNoFixed positions π) =
          (fun π => history.Event π ∧ EndpointHistory.NoFixedWord positions
            ((EndpointHistory.literal π positions 0).take positions)) := by
      funext π
      apply propext
      exact and_congr_right (fun _ => dictionary π)
    rw [eventEq]
    exact cylinders positions positions hremaining hemitted (EndpointHistory.NoFixedWord positions)

#print axioms endpoint_history_count_kernel
#print axioms endpoint_history_literal_cylinder

end D5.S1.Words.Patterns.Separable.EndpointHistoryKernel
