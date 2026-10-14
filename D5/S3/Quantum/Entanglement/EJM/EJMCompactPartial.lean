/- Prepared compact-partial candidate only.  The source partial assignment is
represented by a prefix depth and one low-index-first base-4 Nat.  This file
does not replace the original Function.update checker and is not compiled.

The important boundary is semantic: `decode` returns `none` at every unknown
coordinate, and all four recursive values remain explicit in `checkPacked`.
The dominance function therefore receives the complete actual decoded partial
assignment, including every known coordinate and every unknown suffix.
-/

import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry
import D5.S3.Quantum.Entanglement.EJM.EJMCacheState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData

abbrev Coord := Fin 20
abbrev Value := Fin 4

abbrev base : ℕ := 4

/-- A finite low-coordinate prefix.  `digits` stores digit `g` at the
`base ^ g` place; the representation is deliberately a Nat, not a fixed
machine word. -/
structure PackedPartial where
  depth : ℕ
  digits : ℕ

def WellFormed (q : PackedPartial) : Prop :=
  q.depth ≤ 20 ∧ q.digits < base ^ q.depth

/-- The exact original partial assignment recovered from a packed prefix. -/
def decode (q : PackedPartial) : Partial Coord Value :=
  fun g =>
    if h : g.val < q.depth then
      some ⟨q.digits / base ^ g.val % base, by
        exact Nat.mod_lt _ (by decide : 0 < base)⟩
    else none

theorem decode_known (q : PackedPartial) (g : Coord) (h : g.val < q.depth) :
    decode q g = some ⟨q.digits / base ^ g.val % base,
      Nat.mod_lt _ (by decide : 0 < base)⟩ := by
  simp only [decode, h, dite_true]

theorem decode_unknown (q : PackedPartial) (g : Coord) (h : q.depth ≤ g.val) :
    decode q g = none := by
  simp only [decode, Nat.not_lt_of_ge h, dite_false]

/-- Add one actual value at the next unknown coordinate. -/
def append (q : PackedPartial) (a : Value) : PackedPartial :=
  ⟨q.depth + 1, q.digits + a.val * base ^ q.depth⟩

theorem append_depth (q : PackedPartial) (a : Value) :
    (append q a).depth = q.depth + 1 := rfl

private theorem pow_base_succ (n : ℕ) :
    base ^ (n + 1) = base ^ n * base := by
  exact pow_succ base n

private theorem append_div_old
    (q : PackedPartial) (a : Value) (g : Coord)
    (hwell : q.digits < base ^ q.depth) (hg : g.val < q.depth) :
    (q.digits + a.val * base ^ q.depth) / base ^ g.val =
      q.digits / base ^ g.val + a.val * base ^ (q.depth - g.val) := by
  have hle : g.val ≤ q.depth := Nat.le_of_lt hg
  have hpow : base ^ q.depth = base ^ g.val * base ^ (q.depth - g.val) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  calc
    (q.digits + a.val * base ^ q.depth) / base ^ g.val =
        (q.digits + base ^ g.val * (a.val * base ^ (q.depth - g.val))) /
          base ^ g.val := by rw [hpow]; congr 1; ac_rfl
    _ = q.digits / base ^ g.val + a.val * base ^ (q.depth - g.val) :=
      Nat.add_mul_div_left _ _ (pow_pos (by decide : 0 < base) _)

private theorem append_digit_old
    (q : PackedPartial) (a : Value) (g : Coord)
    (hwell : q.digits < base ^ q.depth) (hg : g.val < q.depth) :
    (q.digits + a.val * base ^ q.depth) /
        base ^ g.val % base = q.digits / base ^ g.val % base := by
  have hdiv := append_div_old q a g hwell hg
  rw [hdiv]
  have hpositive : 0 < q.depth - g.val := Nat.sub_pos_of_lt hg
  have hfour : base ∣ a.val * base ^ (q.depth - g.val) := by
    refine ⟨a.val * base ^ (q.depth - g.val - 1), ?_⟩
    have hs : q.depth - g.val = (q.depth - g.val - 1) + 1 := by omega
    have hp : base ^ (q.depth - g.val) =
        base ^ (q.depth - g.val - 1) * base := by
      calc
        _ = base ^ ((q.depth - g.val - 1) + 1) := congrArg (base ^ ·) hs
        _ = _ := pow_succ _ _
    rw [hp]
    ac_rfl
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hfour, add_zero, Nat.mod_mod]

private theorem append_digit_at
    (q : PackedPartial) (a : Value)
    (hwell : q.digits < base ^ q.depth) :
    (q.digits + a.val * base ^ q.depth) / base ^ q.depth % base = a.val := by
  have hsmall : q.digits / base ^ q.depth = 0 :=
    Nat.div_eq_of_lt hwell
  have hdiv : (q.digits + a.val * base ^ q.depth) / base ^ q.depth =
      q.digits / base ^ q.depth + a.val := by
    calc
      (q.digits + a.val * base ^ q.depth) / base ^ q.depth =
          (q.digits + base ^ q.depth * a.val) / base ^ q.depth := by
        rw [Nat.mul_comm a.val]
      _ = q.digits / base ^ q.depth + a.val :=
        Nat.add_mul_div_left _ _ (pow_pos (by decide : 0 < base) _)
  rw [hdiv]
  calc
    (q.digits / base ^ q.depth + a.val) % base = a.val := by
      simp only [hsmall, zero_add, Nat.mod_eq_of_lt a.isLt]

theorem append_wellFormed (q : PackedPartial) (a : Value)
    (hwell : WellFormed q) (hdepth : q.depth < 20) :
    WellFormed (append q a) := by
  rcases hwell with ⟨hdepth', hdigits⟩
  constructor
  · dsimp [append]
    omega
  · have halt := a.isLt
    have ha : a.val ≤ 3 := by omega
    have hmul : a.val * base ^ q.depth ≤ 3 * base ^ q.depth := by
      exact Nat.mul_le_mul_right _ ha
    have hd : q.digits ≤ base ^ q.depth - 1 := Nat.le_pred_of_lt hdigits
    have hsum : q.digits + a.val * base ^ q.depth < 4 * base ^ q.depth := by
      omega
    change q.digits + a.val * base ^ q.depth < base ^ (q.depth + 1)
    rw [pow_base_succ]
    simpa only [base, Nat.mul_comm] using hsum

theorem append_decode_update
    (q : PackedPartial) (a : Value) (g : Coord)
    (hwell : WellFormed q) (hg : g.val = q.depth) :
    decode (append q a) = Function.update (decode q) g (some a) := by
  funext j
  by_cases hj : j.val < q.depth
  · have hnew : j.val < (append q a).depth := by
      dsimp [append]
      omega
    have hne : j ≠ g := by
      intro hEq
      have : j.val = q.depth := by simpa [hEq, hg]
      omega
    rw [Function.update_of_ne hne, decode_known (append q a) j hnew,
      decode_known q j hj]
    congr 1
    apply Fin.ext
    exact append_digit_old q a j hwell.2 hj
  · by_cases hEq : j = g
    · subst j
      have hnew : g.val < (append q a).depth := by
        dsimp [append]
        omega
      rw [Function.update_same, decode_known (append q a) g hnew]
      congr 1
      apply Fin.ext
      change (q.digits + a.val * base ^ q.depth) / base ^ g.val % base = a.val
      rw [hg]
      exact append_digit_at q a hwell.2
    · have hafter : (append q a).depth ≤ j.val := by
        dsimp [append]
        have hj' : q.depth ≤ j.val := Nat.le_of_not_gt hj
        have hjg : j.val ≠ g.val := fun h => hEq (Fin.ext h)
        omega
      rw [decode_unknown (append q a) j hafter]
      rw [Function.update_of_ne hEq, decode_unknown q j (Nat.le_of_not_gt hj)]

/-- A compact checker uses the packed prefix at every dominance call.  At a
positive-fuel split `advance` appends exactly the actual split value.  At the
zero-fuel child the original checker is definitionally false, so no fake
coordinate/value update is introduced. -/
def advance (fuel : ℕ) (q : PackedPartial) (i : Coord) (a : Value) : PackedPartial :=
  if 0 < fuel then append q a else q

def checkPacked
    (nodes : ℕ → Fin EJMGlobalDAGData.Size → Node EJMGlobalDAGData.Size Coord Value
      EJMGlobalScoreSymmetry.Cut)
    (step : EJMCacheState.Cache → Coord → Value → EJMCacheState.Cache)
    (lower : EJMCacheState.Cache → ℤ)
    (dominates : EJMGlobalScoreSymmetry.Cut → Partial Coord Value → Bool)
    (gap : ℤ) :
    ℕ → Fin EJMGlobalDAGData.Size → EJMCacheState.Cache → PackedPartial → Bool
  | 0, _, _, _ => false
  | fuel + 1, index, cache, q =>
    match nodes (fuel + 1) index with
    | .bound => decide (gap ≤ lower cache)
    | .symmetry s => dominates s (decode q)
    | .split i children => decide (∀ a,
        checkPacked nodes step lower dominates gap fuel (children a)
          (step cache i a) (advance fuel q i a) = true)

/-- The actual split nodes consume the coordinates in prefix order.  This
contract is proved from the source `nodes` formula, rather than supplied by a
producer table. -/
theorem actual_split_coordinate
    (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (i : Coord) (children : Value → Fin EJMGlobalDAGData.Size)
    (hfuel : 0 < fuel) (hbound : fuel + 1 ≤ 21)
    (hnode : EJMGlobalDAGData.nodes (fuel + 1) index = .split i children) :
    i.val + fuel + 1 = 21 := by
  unfold EJMGlobalDAGData.nodes at hnode
  split_ifs at hnode
  · cases hnode
  · cases hnode
  · have hcoord : i.val = (21 - (fuel + 1)) % 20 := by
      cases hnode
      rfl
    have hlt : 21 - (fuel + 1) < 20 := by omega
    rw [Nat.mod_eq_of_lt hlt] at hcoord
    omega

theorem checkPacked_eq_original
    (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size)
    (cache : EJMCacheState.Cache) (q : PackedPartial)
    (hwell : WellFormed q) (hinv : q.depth + fuel = 21) :
    checkPacked EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
        EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
        fuel index cache q =
      check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
        EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
        fuel index cache (decode q) := by
  induction fuel generalizing index cache q with
  | zero => rfl
  | succ fuel ih =>
    cases hn : EJMGlobalDAGData.nodes (fuel + 1) index with
    | bound =>
      simp only [checkPacked, check, hn]
    | symmetry s =>
      simp only [checkPacked, check, hn]
    | split i children =>
      simp only [checkPacked, check, hn]
      cases fuel with
      | zero =>
        simp [advance, checkPacked, check]
      | succ fuel =>
        have hcoord := actual_split_coordinate (fuel + 1) index i children
          (by omega) (by omega) hn
        have hdepth : q.depth = i.val := by omega
        have hqnext (a : Value) : WellFormed (append q a) :=
          append_wellFormed q a hwell (by omega)
        have hnextinv (a : Value) : (append q a).depth + (fuel + 1) = 21 := by
          dsimp [append]
          omega
        have hchild (a : Value) :
            checkPacked EJMGlobalDAGData.nodes EJMCacheState.step
              EJMCacheState.lower EJMGlobalScoreSymmetry.dominates
              EJMPartialBoundData.scale (fuel + 1) (children a) (EJMCacheState.step cache i a)
              (advance (fuel + 1) q i a) =
            check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
              EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale (fuel + 1)
              (children a) (EJMCacheState.step cache i a)
              (Function.update (decode q) i (some a)) := by
          rw [show advance (fuel + 1) q i a = append q a by
            simp only [advance, Nat.zero_lt_succ, ↓reduceIte]]
          rw [ih _ _ _ (hqnext a) (hnextinv a)]
          rw [append_decode_update q a i hwell (by simpa [hdepth])]
        simp only [hchild]
        rfl

def actualPacked : PackedPartial := ⟨0, 0⟩

theorem actualPacked_wellFormed : WellFormed actualPacked := by
  constructor <;> decide

theorem actualPacked_invariant : actualPacked.depth + 21 = 21 := by decide

theorem actualPacked_decode : decode actualPacked = (fun _ => none) := by
  funext g
  simp [actualPacked, decode]

theorem actual_checkPacked_eq_original :
    checkPacked EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      21 EJMGlobalDAGData.root EJMCacheState.initial actualPacked =
    check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      21 EJMGlobalDAGData.root EJMCacheState.initial (decode actualPacked) := by
  exact checkPacked_eq_original 21 EJMGlobalDAGData.root EJMCacheState.initial
    actualPacked actualPacked_wellFormed actualPacked_invariant

theorem actual_checkPacked_eq_original_zero :
    checkPacked EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      21 EJMGlobalDAGData.root EJMCacheState.initial actualPacked =
    check EJMGlobalDAGData.nodes EJMCacheState.step EJMCacheState.lower
      EJMGlobalScoreSymmetry.dominates EJMPartialBoundData.scale
      21 EJMGlobalDAGData.root EJMCacheState.initial (fun _ => none) := by
  rw [actual_checkPacked_eq_original, actualPacked_decode]

#print axioms append_decode_update
#print axioms actual_split_coordinate
#print axioms checkPacked_eq_original
#print axioms actualPacked_decode
#print axioms actual_checkPacked_eq_original
#print axioms actual_checkPacked_eq_original_zero

end D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
