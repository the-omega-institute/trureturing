/- GID: D5/S3/Factorization/Automata/PrimeHistoryNormalForm
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/PrimeHistoryNormalForm
   mirror-E: none(waiver:all-command-words-all-capacities)
   anchors: []
   utility: none
   digest: Prefix extrema and displacement give the exact partial map of every
     guarded prime history; every admissible interval translation has a word. -/

import D5.S3.Factorization.Automata.BoundedPrimeWalk

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.PrimeHistoryNormalForm

open D5.S0.Automata.TypedPartialDFAOOverBase
open BoundedPrimeWalk

/-- True is multiplication by the fixed prime, false is exact division. -/
def jump (b : Bool) : Int := if b then 1 else -1

/-- Unrestricted displacement; legality is not inferred from this number alone. -/
def displacement : List Bool → Int
  | [] => 0
  | b :: w => jump b + displacement w

/-- Least prefix displacement, including the empty prefix. -/
def low : List Bool → Int
  | [] => 0
  | b :: w => min 0 (jump b + low w)

/-- Greatest prefix displacement, including the empty prefix. -/
def high : List Bool → Int
  | [] => 0
  | b :: w => max 0 (jump b + high w)

/-- The visited interval contains both the initial and final displacement. -/
theorem excursion_bounds (w : List Bool) :
    low w ≤ 0 ∧ 0 ≤ high w ∧ low w ≤ displacement w ∧ displacement w ≤ high w := by
  induction w with
  | nil => simp [low, high, displacement]
  | cons b w ih =>
      simp only [low, high, displacement]
      omega

/-- Chronological concatenation translates the second visited interval by the
first displacement before taking the two extrema. -/
theorem append_signature (v w : List Bool) :
    displacement (v ++ w) = displacement v + displacement w ∧
    low (v ++ w) = min (low v) (displacement v + low w) ∧
    high (v ++ w) = max (high v) (displacement v + high w) := by
  induction v with
  | nil =>
      have hb := excursion_bounds w
      simp only [List.nil_append, displacement, low, high]
      constructor
      · omega
      constructor <;> omega
  | cons b v ih =>
      simp only [List.cons_append, displacement, low, high]
      rcases ih with ⟨hd, hl, hh⟩
      rw [hd, hl, hh]
      constructor
      · omega
      constructor <;> omega

/-- Exact relation to the existing guarded runner. The two inequalities include
every intermediate guard, and the equation gives the actual final exponent. -/
theorem run_spec (a : Nat) (w : List Bool) (e f : Fin (a + 1)) :
    run a e w = some f ↔
      0 ≤ (e.val : Int) + low w ∧ (e.val : Int) + high w ≤ (a : Int) ∧
        (f.val : Int) = (e.val : Int) + displacement w := by
  induction w generalizing e f with
  | nil =>
      have he := e.isLt
      simp only [run, runTransition, Option.some.injEq, low, high, displacement,
        add_zero]
      constructor
      · intro h
        subst f
        omega
      · rintro ⟨_, _, h⟩
        apply Fin.ext
        omega
  | cons b w ih =>
      have he := e.isLt
      rcases excursion_bounds w with ⟨hlo, hhi, hld, hdh⟩
      cases b with
      | false =>
          by_cases hpos : 0 < e.val
          · let next : Fin (a + 1) := ⟨e.val - 1, by omega⟩
            have hr : run a e (false :: w) = run a next w := by
              simp [run, runTransition, step, hpos, next]
            rw [hr, ih]
            simp only [low, high, displacement, jump, reduceCtorEq,
              if_false]
            dsimp [next]
            omega
          · have hr : run a e (false :: w) = none := by
              simp [run, runTransition, step, hpos]
            rw [hr]
            simp only [reduceCtorEq, low, high, displacement,
              jump, reduceCtorEq, if_false]
            omega
      | true =>
          by_cases hroom : e.val < a
          · let next : Fin (a + 1) := ⟨e.val + 1, by omega⟩
            have hr : run a e (true :: w) = run a next w := by
              simp [run, runTransition, step, hroom, next]
            rw [hr, ih]
            simp only [low, high, displacement, jump, reduceCtorEq, if_true]
            dsimp [next]
            omega
          · have hr : run a e (true :: w) = none := by
              simp [run, runTransition, step, hroom]
            rw [hr]
            simp only [reduceCtorEq, low, high, displacement, jump, reduceCtorEq, if_true]
            omega

/-- Nonempty partial translation inside the actual capacity interval.
The record does not encode an unconstrained history or claim to preserve cost. -/
@[ext] structure IntervalMap (a : Nat) where
  lo : Int
  hi : Int
  shift : Int
  lo_nonneg : 0 ≤ lo
  ordered : lo ≤ hi
  hi_le : hi ≤ (a : Int)
  image_lo : 0 ≤ lo + shift
  image_hi : hi + shift ≤ (a : Int)

/-- The empty map is a separate normal form, so all everywhere-failing histories
are identified and no meaningless displacement of an empty map is retained. -/
def normal (a : Nat) (w : List Bool) : Option (IntervalMap a) :=
  if h : high w - low w ≤ (a : Int) then
    some {
      lo := -low w
      hi := (a : Int) - high w
      shift := displacement w
      lo_nonneg := by have := (excursion_bounds w).1; omega
      ordered := by omega
      hi_le := by have := (excursion_bounds w).2.1; omega
      image_lo := by have := (excursion_bounds w).2.2.1; omega
      image_hi := by have := (excursion_bounds w).2.2.2; omega }
  else none

/-- Evaluation on integers; every defined input and output is in [0,a]. -/
def evaluate {a : Nat} (q : Option (IntervalMap a)) (x : Int) : Option Int :=
  q.bind fun t => if t.lo ≤ x ∧ x ≤ t.hi then some (x + t.shift) else none

/-- The executable normal form retains exactly the original prefix constraints. -/
theorem evaluate_normal (a : Nat) (w : List Bool) (x : Int) :
    evaluate (normal a w) x =
      if 0 ≤ x + low w ∧ x + high w ≤ (a : Int)
      then some (x + displacement w) else none := by
  unfold normal
  split
  · rename_i h
    have hc : (-low w ≤ x ∧ x ≤ (a : Int) - high w) ↔
        (0 ≤ x + low w ∧ x + high w ≤ (a : Int)) := by omega
    simp [evaluate, hc]
  · rename_i h
    have hc : ¬ (0 ≤ x + low w ∧ x + high w ≤ (a : Int)) := by omega
    simp [evaluate, hc]

/-- All successes and failures of the existing arithmetic-transported runner
are preserved. The output is the actual final exponent, not just acceptance. -/
theorem normal_correct (a : Nat) (w : List Bool) (e : Fin (a + 1)) :
    (run a e w).map (fun f => (f.val : Int)) =
      evaluate (normal a w) (e.val : Int) := by
  rw [evaluate_normal]
  by_cases h : 0 ≤ (e.val : Int) + low w ∧ (e.val : Int) + high w ≤ (a : Int)
  · rw [if_pos h]
    have hb := excursion_bounds w
    let z : Int := (e.val : Int) + displacement w
    have hz0 : 0 ≤ z := by dsimp [z]; omega
    have hza : z ≤ (a : Int) := by dsimp [z]; omega
    let f : Fin (a + 1) := ⟨z.toNat, by omega⟩
    have hf : (f.val : Int) = z := by dsimp [f]; omega
    have hr : run a e w = some f := (run_spec a w e f).mpr ⟨h.1, h.2, hf⟩
    rw [hr]
    exact congrArg some hf
  · rw [if_neg h]
    cases hr : run a e w with
    | none => rfl
    | some f =>
        have hs := (run_spec a w e f).mp hr
        exact False.elim (h ⟨hs.1, hs.2.1⟩)

/-- Extensional uniqueness of nonempty interval translations and the empty map. -/
theorem evaluate_injective (a : Nat) :
    Function.Injective (evaluate (a := a)) := by
  intro q r heq
  cases q with
  | none =>
      cases r with
      | none => rfl
      | some t =>
          have h := congrFun heq t.lo
          simp [evaluate, t.ordered] at h
  | some s =>
      cases r with
      | none =>
          have h := congrFun heq s.lo
          simp [evaluate, s.ordered] at h
      | some t =>
          have domain (x : Int) :
              (s.lo ≤ x ∧ x ≤ s.hi) ↔ (t.lo ≤ x ∧ x ≤ t.hi) := by
            have hx := congrArg Option.isSome (congrFun heq x)
            by_cases hs : s.lo ≤ x ∧ x ≤ s.hi <;>
              by_cases ht : t.lo ≤ x ∧ x ≤ t.hi <;>
              simp [evaluate, hs, ht] at hx ⊢
          have hstlo := (domain s.lo).mp ⟨le_rfl, s.ordered⟩
          have hsthi := (domain s.hi).mp ⟨s.ordered, le_rfl⟩
          have htslo := (domain t.lo).mpr ⟨le_rfl, t.ordered⟩
          have htshi := (domain t.hi).mpr ⟨t.ordered, le_rfl⟩
          have hlo : s.lo = t.lo := le_antisymm htslo.1 hstlo.1
          have hhi : s.hi = t.hi := le_antisymm hsthi.2 htshi.2
          have hout := congrFun heq s.lo
          simp [evaluate, s.ordered, hstlo] at hout
          have hd : s.shift = t.shift := by omega
          exact congrArg some (IntervalMap.ext hlo hhi hd)

/-- Exact signatures of the two monotone words, used in the realization theorem. -/
private theorem replicate_signature (n : Nat) :
    displacement (List.replicate n false) = -(n : Int) ∧
    low (List.replicate n false) = -(n : Int) ∧
    high (List.replicate n false) = 0 ∧
    displacement (List.replicate n true) = (n : Int) ∧
    low (List.replicate n true) = 0 ∧
    high (List.replicate n true) = (n : Int) := by
  induction n with
  | zero => simp [displacement, low, high]
  | succ n ih =>
      rcases ih with ⟨hd, hl, hh, hu, hul, huh⟩
      simp only [List.replicate_succ, displacement, low, high, jump,
        reduceCtorEq, if_false, if_true, hd, hl, hh, hu, hul, huh]
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega

/-- A concrete word: go to the least displacement, then the greatest, then
back to the specified final displacement. All lengths are proved nonnegative. -/
def realize {a : Nat} (t : IntervalMap a) : List Bool :=
  (List.replicate t.lo.toNat false ++
    List.replicate ((a : Int) - t.hi + t.lo).toNat true) ++
    List.replicate ((a : Int) - t.hi - t.shift).toNat false

/-- Every proposed nonempty interval map is induced by an actual finite command
word. The theorem derives all three word coordinates, including both extrema. -/
theorem realize_signature {a : Nat} (t : IntervalMap a) :
    low (realize t) = -t.lo ∧
    high (realize t) = (a : Int) - t.hi ∧
    displacement (realize t) = t.shift := by
  have ht0 := t.lo_nonneg
  have ht1 := t.ordered
  have ht2 := t.hi_le
  have ht3 := t.image_lo
  have ht4 := t.image_hi
  have h0 : (t.lo.toNat : Int) = t.lo := by omega
  have h1 : (((a : Int) - t.hi + t.lo).toNat : Int) = (a : Int) - t.hi + t.lo := by omega
  have h2 : (((a : Int) - t.hi - t.shift).toNat : Int) = (a : Int) - t.hi - t.shift := by omega
  rcases replicate_signature t.lo.toNat with ⟨d0, l0, u0, _, _, _⟩
  rcases replicate_signature ((a : Int) - t.hi + t.lo).toNat with ⟨_, _, _, d1, l1, u1⟩
  rcases replicate_signature ((a : Int) - t.hi - t.shift).toNat with ⟨d2, l2, u2, _, _, _⟩
  rcases append_signature
    (List.replicate t.lo.toNat false)
    (List.replicate ((a : Int) - t.hi + t.lo).toNat true) with ⟨d01, l01, u01⟩
  rcases append_signature
    (List.replicate t.lo.toNat false ++ List.replicate ((a : Int) - t.hi + t.lo).toNat true)
    (List.replicate ((a : Int) - t.hi - t.shift).toNat false) with ⟨d012, l012, u012⟩
  unfold realize
  constructor
  · omega
  constructor <;> omega

/-- Surjectivity includes the empty partial map, realized by capacity+1
multiplications. It therefore does not merely give an upper bound on behaviors. -/
theorem normal_surjective (a : Nat) : Function.Surjective (normal a) := by
  intro q
  cases q with
  | none =>
      refine ⟨List.replicate (a + 1) true, ?_⟩
      have h := replicate_signature (a + 1)
      simp only [normal, h.2.2.2.2.1, h.2.2.2.2.2]
      have hn : ¬ ((a + 1 : Nat) : Int) - 0 ≤ (a : Int) := by omega
      simp [hn]
  | some t =>
      refine ⟨realize t, ?_⟩
      rcases realize_signature t with ⟨hl, hh, hd⟩
      have hc : high (realize t) - low (realize t) ≤ (a : Int) := by
        rw [hl, hh]
        have := t.ordered
        omega
      unfold normal
      rw [dif_pos hc]
      apply congrArg some
      apply IntervalMap.ext <;> simp [hl, hh, hd]

#print axioms run_spec
#print axioms normal_correct
#print axioms realize_signature
#print axioms normal_surjective

end D5.S3.Factorization.Automata.PrimeHistoryNormalForm
