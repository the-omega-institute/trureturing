/- GID: D5/S3/Factorization/Automata/PrimeHistoryNormalForm
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/PrimeHistoryNormalForm
   mirror-E: none(waiver:all-command-words-all-capacities)
   anchors: []
   utility: none
   digest: Frozen excursion coordinates encode guarded histories and realize every admissible interval translation. -/

import D5.S3.Factorization.Automata.WordExcursionLowerBound

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.PrimeHistoryNormalForm

open WordExcursionLowerBound

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
  have bounds :
      low w ≤ 0 ∧ 0 ≤ high w ∧ low w ≤ displacement w ∧ displacement w ≤ high w := by
    induction w with
    | nil => simp [low, high, displacement]
    | cons b w ih => simp only [low, high, displacement]; omega
  if h : high w - low w ≤ (a : Int) then
    some {
      lo := -low w
      hi := (a : Int) - high w
      shift := displacement w
      lo_nonneg := by omega
      ordered := by omega
      hi_le := by omega
      image_lo := by omega
      image_hi := by omega }
  else none

/-- Evaluation on integers; every defined input and output is in [0,a]. -/
def evaluate {a : Nat} (q : Option (IntervalMap a)) (x : Int) : Option Int :=
  q.bind fun t => if t.lo ≤ x ∧ x ≤ t.hi then some (x + t.shift) else none

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
          have hstlo := (domain s.lo).mp ⟨by omega, s.ordered⟩
          have hsthi := (domain s.hi).mp ⟨s.ordered, by omega⟩
          have htslo := (domain t.lo).mpr ⟨by omega, t.ordered⟩
          have htshi := (domain t.hi).mpr ⟨t.ordered, by omega⟩
          have hlo : s.lo = t.lo := by omega
          have hhi : s.hi = t.hi := by omega
          have hout := congrFun heq s.lo
          simp [evaluate, s.ordered, hstlo] at hout
          have hd : s.shift = t.shift := by omega
          exact congrArg some (IntervalMap.ext hlo hhi hd)

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
  have excursion_bounds : ∀ w : List Bool,
      low w ≤ 0 ∧ 0 ≤ high w ∧ low w ≤ displacement w ∧ displacement w ≤ high w := by
    intro w
    induction w with
    | nil => simp [low, high, displacement]
    | cons b w ih => simp only [low, high, displacement]; omega
  have append_signature (v w : List Bool) :
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
  have replicate_signature (n : Nat) :
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
        simp only [List.replicate_succ, displacement, low, high,
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
  have replicate_signature (n : Nat) :
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
        simp only [List.replicate_succ, displacement, low, high,
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
  intro q
  cases q with
  | none =>
      refine ⟨List.replicate (a + 1) true, ?_⟩
      have h := replicate_signature (a + 1)
      have hn : ¬ high (List.replicate (a + 1) true) -
          low (List.replicate (a + 1) true) ≤ (a : Int) := by
        rw [h.2.2.2.2.1, h.2.2.2.2.2]
        omega
      simp [normal, hn]
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
      apply IntervalMap.ext
      · change -low (realize t) = t.lo
        omega
      · change (a : Int) - high (realize t) = t.hi
        omega
      · change displacement (realize t) = t.shift
        exact hd

#print axioms evaluate_injective
#print axioms realize_signature
#print axioms normal_surjective

end D5.S3.Factorization.Automata.PrimeHistoryNormalForm
