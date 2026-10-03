/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionPairing
   mirror-E: none(waiver:combinatorial-pairing)
   anchors: [mathlib/module/Mathlib.Data.List.Basic]
   utility: none
   digest: Odd-time pairing of even-strip Dyck paths with two-colored Motzkin paths. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs
import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionPairing

open CiglerStripExpansionDefs

def expandBlocks : List (Bool × Bool) → List Bool
  | [] => []
  | block :: rest => block.1 :: block.2 :: expandBlocks rest

def pairBlocks : List Bool → List (Bool × Bool)
  | first :: second :: rest => (first, second) :: pairBlocks rest
  | _ => []

def expandPath (blocks : List (Bool × Bool)) : List Bool :=
  true :: (expandBlocks blocks ++ [false])

def coarseHeight (blocks : List (Bool × Bool)) (index : ℕ) : ℤ :=
  ((blocks.take index).map fun block =>
    if block.1 then (if block.2 then (1 : ℤ) else 0)
    else (if block.2 then 0 else -1)).sum

def IsMotzkinStrip (bound : ℕ) (blocks : List (Bool × Bool)) : Prop :=
  (∀ index ≤ blocks.length,
    0 ≤ coarseHeight blocks index ∧ coarseHeight blocks index ≤ bound) ∧
    coarseHeight blocks blocks.length = 0

noncomputable def motzkinWeight (signed : Bool) (height : ℕ) :
    List (Bool × Bool) → Polynomial ℤ
  | [] => 1
  | (true, true) :: rest => motzkinWeight signed (height + 1) rest
  | (false, false) :: rest =>
    (if signed then -Polynomial.X else Polynomial.X) *
      motzkinWeight signed (height - 1) rest
  | (true, false) :: rest =>
    (if signed then Polynomial.C ((-1 : ℤ) ^ height) else 1) * Polynomial.X *
      motzkinWeight signed height rest
  | (false, true) :: rest =>
    (if signed then Polynomial.C ((-1 : ℤ) ^ height) else 1) *
      motzkinWeight signed height rest

theorem pairing_bijection (bound size : ℕ) (positive : 1 ≤ bound) :
    ∃ correspondence :
      {path : List Bool // path.length = 2 * (size + 1) ∧ IsStripDyck (2 * bound) path} ≃
      {blocks : List (Bool × Bool) //
        blocks.length = size ∧ IsMotzkinStrip (bound - 1) blocks},
      (∀ path, expandPath (correspondence path).val = path.val) ∧
      (∀ blocks, (correspondence.symm blocks).val = expandPath blocks.val) := by
  have expanded_length (blocks : List (Bool × Bool)) :
      (expandBlocks blocks).length = 2 * blocks.length := by
    induction blocks with
    | nil => rfl
    | cons block rest induction_hyp =>
      simp only [expandBlocks, List.length_cons, induction_hyp]
      omega
  have pair_expand (blocks : List (Bool × Bool)) :
      pairBlocks (expandBlocks blocks) = blocks := by
    induction blocks with
    | nil => rfl
    | cons block rest induction_hyp =>
      simp only [expandBlocks, pairBlocks, induction_hyp, Prod.mk.eta]
  have expand_pair (path : List Bool) (even : path.length % 2 = 0) :
      expandBlocks (pairBlocks path) = path := by
    induction path using pairBlocks.induct with
    | case1 first second rest induction_hyp =>
      have rest_even : rest.length % 2 = 0 := by
        simp only [List.length_cons] at even
        omega
      simp only [pairBlocks, expandBlocks, induction_hyp rest_even]
    | case2 path no_pair =>
      cases path with
      | nil => rfl
      | cons first rest =>
        cases rest with
        | nil => simp at even
        | cons second rest => exact False.elim (no_pair first second rest rfl)
  have sampled_height (blocks : List (Bool × Bool)) (index : ℕ) :
      heightAfter (expandBlocks blocks) (2 * index) = 2 * coarseHeight blocks index := by
    induction blocks generalizing index with
    | nil => simp [expandBlocks, heightAfter, coarseHeight]
    | cons block rest induction_hyp =>
      cases index with
      | zero => simp [heightAfter, coarseHeight]
      | succ index =>
        have index_eq : 2 * (index + 1) = 2 * index + 2 := by omega
        rw [index_eq]
        simp only [expandBlocks, heightAfter, List.take_succ_cons, List.map_cons,
          List.sum_cons]
        have tail_eq := induction_hyp index
        simp only [heightAfter] at tail_eq
        rw [tail_eq]
        cases block with
        | mk first second =>
          cases first <;> cases second <;>
            simp [coarseHeight, List.take_succ_cons] <;> omega
  have intermediate_height (blocks : List (Bool × Bool)) (index : ℕ)
      (inside : index < blocks.length) :
      heightAfter (expandBlocks blocks) (2 * index + 1) =
        2 * coarseHeight blocks index +
          (if (blocks.getD index (true, true)).1 then 1 else -1) := by
    induction blocks generalizing index with
    | nil => simp at inside
    | cons block rest induction_hyp =>
      cases index with
      | zero => simp [expandBlocks, heightAfter, coarseHeight]
      | succ index =>
        have rest_inside : index < rest.length := by simpa using inside
        have index_eq : 2 * (index + 1) + 1 = (2 * index + 1) + 2 := by omega
        rw [index_eq]
        simp only [expandBlocks, heightAfter, List.take_succ_cons, List.map_cons,
          List.sum_cons]
        have tail_eq := induction_hyp index rest_inside
        simp only [heightAfter] at tail_eq
        rw [tail_eq]
        cases block with
        | mk first second =>
          cases first <;> cases second <;>
            simp [coarseHeight, List.take_succ_cons] <;> omega
  have inner_prefix (blocks : List (Bool × Bool)) (index : ℕ)
      (inside : index ≤ 2 * blocks.length) :
      heightAfter (expandPath blocks) (index + 1) =
        1 + heightAfter (expandBlocks blocks) index := by
    simp only [expandPath, heightAfter, List.take_succ_cons, List.map_cons,
      if_true, List.sum_cons]
    rw [List.take_append_of_le_length (by simpa [expanded_length] using inside)]
  have total_height (blocks : List (Bool × Bool)) :
      heightAfter (expandPath blocks) (expandPath blocks).length =
        2 * coarseHeight blocks blocks.length := by
    simp only [expandPath, heightAfter, List.take_length, List.map_cons, List.map_append,
      List.map_nil, List.sum_cons, List.sum_append, List.sum_nil, if_true,
      Bool.false_eq_true, if_false]
    have tail_eq := sampled_height blocks blocks.length
    have full_take : (expandBlocks blocks).take (2 * blocks.length) = expandBlocks blocks := by
      rw [← expanded_length blocks, List.take_length]
    simp only [heightAfter, full_take] at tail_eq
    omega
  have strip_equivalence (blocks : List (Bool × Bool)) :
      IsStripDyck (2 * bound) (expandPath blocks) ↔
        IsMotzkinStrip (bound - 1) blocks := by
    constructor
    · intro original
      constructor
      · intro index inside
        have limit : 2 * index + 1 ≤ (expandPath blocks).length := by
          simp only [expandPath, List.length_cons, List.length_append,
            List.length_nil, expanded_length]
          omega
        have vertex := original.1 (2 * index + 1) limit
        rw [inner_prefix blocks (2 * index) (by omega), sampled_height] at vertex
        push_cast at vertex
        omega
      · have endpoint := original.2
        rw [total_height] at endpoint
        omega
    · intro coarse
      constructor
      · intro index inside
        have length_eq : (expandPath blocks).length = 2 * blocks.length + 2 := by
          simp only [expandPath, List.length_cons, List.length_append,
            List.length_nil, expanded_length]
        by_cases at_end : index = (expandPath blocks).length
        · rw [at_end, total_height, coarse.2]
          simp
        · cases index with
          | zero => simp [heightAfter]
          | succ index =>
            have inner : index ≤ 2 * blocks.length := by omega
            rw [inner_prefix blocks index inner]
            have division : index = 2 * (index / 2) + index % 2 := by omega
            have sample_inside : index / 2 ≤ blocks.length := by omega
            have vertex := coarse.1 (index / 2) sample_inside
            push_cast at vertex ⊢
            rcases Nat.mod_two_eq_zero_or_one index with parity | parity
            · have index_eq : index = 2 * (index / 2) := by omega
              rw [index_eq, sampled_height]
              omega
            · have index_eq : index = 2 * (index / 2) + 1 := by omega
              have strict : index / 2 < blocks.length := by omega
              rw [index_eq, intermediate_height blocks (index / 2) strict]
              split <;> omega
      · rw [total_height, coarse.2]
        simp
  have outer_steps (path : List Bool) (length_eq : path.length = 2 * (size + 1))
      (strip : IsStripDyck (2 * bound) path) :
      ∃ inner : List Bool, path = true :: (inner ++ [false]) ∧ inner.length = 2 * size := by
    cases path with
    | nil => simp at length_eq
    | cons first rest =>
      have first_up : first = true := by
        have initial := (strip.1 1 (by simp)).1
        cases first <;> simp [heightAfter] at initial ⊢
      subst first
      have last_down : (true :: rest).getLast? = some false := by
        induction rest using List.reverseRecOn with
        | nil => simp [IsStripDyck, heightAfter] at strip
        | append_singleton inner last induction_hyp =>
          have final := strip.2
          have before := (strip.1 (inner.length + 1) (by simp)).1
          have before_height : heightAfter (true :: (inner ++ [last])) (inner.length + 1) =
              1 + ((inner.map fun step => if step then (1 : ℤ) else -1).sum) := by
            simp [heightAfter]
          rw [before_height] at before
          simp only [heightAfter, List.take_length, List.map_cons, List.map_append,
            List.map_nil, List.sum_cons, List.sum_append, List.sum_nil, if_true] at final
          cases last with
          | false => exact List.getLast?_eq_some_iff.mpr ⟨true :: inner, rfl⟩
          | true => simp only [if_true] at final; omega
      obtain ⟨initial, initial_eq⟩ := List.getLast?_eq_some_iff.mp last_down
      cases initial with
      | nil => simp at initial_eq
      | cons first inner =>
        simp only [List.cons_append, List.cons.injEq] at initial_eq
        refine ⟨inner, ?_, ?_⟩
        · simpa [initial_eq.1] using congrArg (List.cons true) initial_eq.2
        · simp only [List.length_cons, initial_eq.2, List.length_append,
            List.length_nil] at length_eq
          omega
  let encode (path : List Bool) := pairBlocks path.tail.dropLast
  have encode_inverse (path : List Bool)
      (valid : path.length = 2 * (size + 1) ∧ IsStripDyck (2 * bound) path) :
      expandPath (encode path) = path := by
    obtain ⟨inner, path_eq, inner_length⟩ := outer_steps path valid.1 valid.2
    rw [path_eq]
    simp only [encode, List.tail_cons, List.dropLast_append_cons, List.dropLast_singleton,
      List.append_nil]
    rw [expandPath, expand_pair inner (by omega)]
  have decode_inverse (blocks : List (Bool × Bool)) :
      encode (expandPath blocks) = blocks := by
    simp only [encode, expandPath, List.tail_cons, List.dropLast_append_cons,
      List.dropLast_singleton, List.append_nil, pair_expand]
  let correspondence :
      {path : List Bool // path.length = 2 * (size + 1) ∧ IsStripDyck (2 * bound) path} ≃
      {blocks : List (Bool × Bool) //
        blocks.length = size ∧ IsMotzkinStrip (bound - 1) blocks} :=
    { toFun := fun path => ⟨encode path.val, by
        have recovered := encode_inverse path.val path.property
        constructor
        · have lengths := congrArg List.length recovered
          simp only [expandPath, List.length_cons, List.length_append,
            List.length_nil, expanded_length, path.property.1] at lengths
          omega
        · exact (strip_equivalence _).mp (recovered.symm ▸ path.property.2)⟩
      invFun := fun blocks => ⟨expandPath blocks.val, by
        constructor
        · simp only [expandPath, List.length_cons, List.length_append,
            List.length_nil, expanded_length, blocks.property.1]
          omega
        · exact (strip_equivalence _).mpr blocks.property.2⟩
      left_inv := fun path => Subtype.ext (encode_inverse path.val path.property)
      right_inv := fun blocks => Subtype.ext (decode_inverse blocks.val) }
  exact ⟨correspondence, fun path => encode_inverse path.val path.property, fun _ => rfl⟩

theorem pairing_weights (bound : ℕ) (blocks : List (Bool × Bool))
    (valid : IsMotzkinStrip bound blocks) :
    weight tauPlus (expandPath blocks) = motzkinWeight false 0 blocks ∧
      weight tauMinus (expandPath blocks) = motzkinWeight true 0 blocks := by
  let weight_from (weights : ℕ → Polynomial ℤ) (height : ℤ) (path : List Bool) :=
    ((List.range path.length).map fun index =>
      if path.getD index true then 1
      else weights (height + heightAfter path (index + 1)).toNat).prod
  have cons_weight (weights : ℕ → Polynomial ℤ) (height : ℤ) (first : Bool)
      (rest : List Bool) :
      weight_from weights height (first :: rest) =
        (if first then 1 else weights (height + (if first then 1 else -1)).toNat) *
          weight_from weights (height + (if first then 1 else -1)) rest := by
    simp only [weight_from, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.prod_cons, List.getD_cons_zero, Function.comp_def,
      Nat.succ_eq_add_one, List.getD_cons_succ, heightAfter, List.take_succ_cons,
      List.take_zero, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
  have sign_power (height : ℕ) : (-1 : ℤ) ^ height = (-1 : ℤ) ^ (height % 2) := by
    calc
      (-1 : ℤ) ^ height = (-1 : ℤ) ^ (2 * (height / 2) + height % 2) := by
        congr 1
        omega
      _ = (-1 : ℤ) ^ (height % 2) := by simp [pow_add, pow_mul]
  have signed_landing (height : ℕ) :
      tauMinus (2 * height) = Polynomial.C ((-1 : ℤ) ^ height) ∧
        tauMinus (2 * height + 1) =
          Polynomial.C ((-1 : ℤ) ^ height) * Polynomial.X := by
    rw [sign_power]
    rcases Nat.mod_two_eq_zero_or_one height with parity | parity
    · have even_mod : (2 * height) % 4 = 0 := by omega
      have odd_mod : (2 * height + 1) % 4 = 1 := by omega
      simp [tauMinus, even_mod, odd_mod, parity]
    · have even_mod : (2 * height) % 4 = 2 := by omega
      have odd_mod : (2 * height + 1) % 4 = 3 := by omega
      simp [tauMinus, even_mod, odd_mod, parity]
  have pair_weights (signed : Bool) (height : ℕ) (path : List (Bool × Bool))
      (nonnegative : ∀ index ≤ path.length, 0 ≤ (height : ℤ) + coarseHeight path index)
      (endpoint : (height : ℤ) + coarseHeight path path.length = 0) :
      weight_from (if signed then tauMinus else tauPlus) (2 * height + 1)
          (expandBlocks path ++ [false]) = motzkinWeight signed height path := by
    induction path generalizing height with
    | nil =>
      have height_zero : height = 0 := by simp [coarseHeight] at endpoint; omega
      subst height
      cases signed <;> simp [expandBlocks, motzkinWeight, weight_from, heightAfter,
        tauPlus, tauMinus]
    | cons block rest induction_hyp =>
      have rest_nonnegative :
          ∀ index ≤ rest.length,
            0 ≤ (height : ℤ) + coarseHeight (block :: rest) (index + 1) := by
        intro index inside
        exact nonnegative (index + 1) (by simpa using inside)
      have tail_height (index : ℕ) : coarseHeight (block :: rest) (index + 1) =
          (if block.1 then (if block.2 then (1 : ℤ) else 0)
            else (if block.2 then 0 else -1)) + coarseHeight rest index := by
        simp [coarseHeight]
      simp only [List.length_cons, tail_height] at endpoint
      simp only [tail_height] at rest_nonnegative
      rcases block with ⟨first, second⟩
      cases first <;> cases second
      · have height_positive : 1 ≤ height := by
          have lower := nonnegative 1 (by simp)
          simp [coarseHeight] at lower
          omega
        have height_cast : ((height - 1 : ℕ) : ℤ) = (height : ℤ) - 1 := by omega
        have lower : ∀ index ≤ rest.length,
            0 ≤ ((height - 1 : ℕ) : ℤ) + coarseHeight rest index := by
          intro index inside
          have lower := rest_nonnegative index inside
          simp only [Bool.false_eq_true, if_false] at lower
          omega
        have end_rest : ((height - 1 : ℕ) : ℤ) + coarseHeight rest rest.length = 0 := by
          simp only [Bool.false_eq_true, if_false] at endpoint
          omega
        have recurse := induction_hyp (height - 1) lower end_rest
        simp only [expandBlocks, List.cons_append, cons_weight, Bool.false_eq_true,
          if_false]
        have landing_even : (2 * (height : ℤ) + 1 + -1).toNat = 2 * height := by omega
        have landing_odd : (2 * (height : ℤ) + 1 + -1 + -1).toNat =
            2 * (height - 1) + 1 := by omega
        have next_height : 2 * (height : ℤ) + 1 + -1 + -1 =
            2 * ((height - 1 : ℕ) : ℤ) + 1 := by omega
        rw [landing_even, landing_odd, next_height, recurse]
        cases signed
        · simp [tauPlus, motzkinWeight, Nat.add_mod]
        · have sign_product : tauMinus (2 * height) * tauMinus (2 * (height - 1) + 1) =
              -Polynomial.X := by
            have successor : height = (height - 1) + 1 := by omega
            rw [(signed_landing height).1, (signed_landing (height - 1)).2]
            have power_next : (-1 : ℤ) ^ height = -((-1 : ℤ) ^ (height - 1)) := by
              rw [successor, pow_succ]
              simp
            rw [power_next, ← mul_assoc, ← Polynomial.C_mul]
            rw [sign_power (height - 1)]
            rcases Nat.mod_two_eq_zero_or_one (height - 1) with parity | parity <;>
              simp [parity]
          simp only [if_true, motzkinWeight]
          rw [← mul_assoc, sign_product]
      · have lower : ∀ index ≤ rest.length,
            0 ≤ (height : ℤ) + coarseHeight rest index := by
          simpa using rest_nonnegative
        have end_rest : (height : ℤ) + coarseHeight rest rest.length = 0 := by
          simpa using endpoint
        have recurse := induction_hyp height lower end_rest
        simp only [expandBlocks, List.cons_append, cons_weight, Bool.false_eq_true,
          if_false, if_true, one_mul]
        have landing : (2 * (height : ℤ) + 1 + -1).toNat = 2 * height := by omega
        have next_height : 2 * (height : ℤ) + 1 + -1 + 1 = 2 * (height : ℤ) + 1 := by omega
        rw [landing, next_height, recurse]
        cases signed
        · simp [tauPlus, motzkinWeight]
        · simp only [if_true, motzkinWeight]
          rw [(signed_landing height).1]
      · have lower : ∀ index ≤ rest.length,
            0 ≤ (height : ℤ) + coarseHeight rest index := by
          simpa using rest_nonnegative
        have end_rest : (height : ℤ) + coarseHeight rest rest.length = 0 := by
          simpa using endpoint
        have recurse := induction_hyp height lower end_rest
        simp only [expandBlocks, List.cons_append, cons_weight, Bool.false_eq_true,
          if_false, if_true, one_mul]
        have landing : (2 * (height : ℤ) + 1 + 1 + -1).toNat = 2 * height + 1 := by omega
        have next_height : 2 * (height : ℤ) + 1 + 1 + -1 = 2 * (height : ℤ) + 1 := by omega
        rw [landing, next_height, recurse]
        cases signed
        · simp [tauPlus, motzkinWeight, Nat.add_mod]
        · simp only [if_true, motzkinWeight]
          rw [(signed_landing height).2]
      · have lower : ∀ index ≤ rest.length,
            0 ≤ ((height + 1 : ℕ) : ℤ) + coarseHeight rest index := by
          simpa [add_assoc] using rest_nonnegative
        have end_rest : ((height + 1 : ℕ) : ℤ) + coarseHeight rest rest.length = 0 := by
          simpa [add_assoc] using endpoint
        have recurse := induction_hyp (height + 1) lower end_rest
        simp only [expandBlocks, List.cons_append, cons_weight, if_true, one_mul]
        have next_height : 2 * (height : ℤ) + 1 + 1 + 1 =
            2 * ((height + 1 : ℕ) : ℤ) + 1 := by omega
        rw [next_height, recurse]
        rfl
  have initial (signed : Bool) :
      weight (if signed then tauMinus else tauPlus) (expandPath blocks) =
        motzkinWeight signed 0 blocks := by
    have weighted := pair_weights signed 0 blocks (by
      intro index inside
      simpa using (valid.1 index inside).1) (by
      simpa using valid.2)
    have original_weight (path : List Bool) :
        weight (if signed then tauMinus else tauPlus) path =
          weight_from (if signed then tauMinus else tauPlus) 0 path := by
      simp only [weight, weight_from, zero_add]
    rw [original_weight, expandPath]
    rw [cons_weight]
    simpa using weighted
  exact ⟨initial false, initial true⟩

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionPairing
