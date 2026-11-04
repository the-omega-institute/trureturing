/- GID: D5/S3/Combinatorics/XorTriangle/ReversibleSideMap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/XorTriangle/ReversibleSideMap
   mirror-E: none(waiver:finite-xor-triangle-rotation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bits, mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: none
   digest: The retained right-edge map of every finite binary XOR triangle has cube equal to the identity and gives a permutation at each width. -/

import D5.S3.Combinatorics.XorTriangle.ValueOne
set_option autoImplicit false
namespace D5.S3.Combinatorics.XorTriangle.ReversibleSideMap
open D5.S3.Combinatorics.XorTriangle.ValueOne

private def cell (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, j => f j
  | d + 1, j => cell f d j ^^ cell f d (j + 1)

private def turn (n : ℕ) (f : ℕ → Bool) (j : ℕ) : Bool := cell f j (n-j)

private theorem cell_turn (n : ℕ) (f : ℕ → Bool) (a b c : ℕ)
    (h : a+b+c=n) : cell (turn n f) a b = cell f b c := by
  induction a generalizing b c with
  | zero =>
    simp only [cell, turn]
    congr 1
    omega
  | succ a ih =>
    rw [cell, ih b (c+1) (by omega), ih (b+1) c (by omega), cell]
    cases cell f b c <;> cases cell f b (c+1) <;> rfl

private theorem turn_cube (n : ℕ) (f : ℕ → Bool) (j : ℕ) (hj : j≤n) :
    turn n (turn n (turn n f)) j = f j := by
  change cell (turn n (turn n f)) j (n-j) = f j
  rw [cell_turn n (turn n f) j (n-j) 0 (by omega)]
  rw [cell_turn n f (n-j) 0 j (by omega)]
  rfl
end D5.S3.Combinatorics.XorTriangle.ReversibleSideMap
namespace D5.S3.Combinatorics.XorTriangle.ReversibleSideMap
open D5.S3.Combinatorics.XorTriangle.ValueOne

private def word (xs : List Bool) (j : ℕ) : Bool := xs[j]?.getD false

private lemma differences_length (xs : List Bool) :
    (differences xs).length = xs.length-1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases xs with
    | nil => rfl
    | cons c xs => simpa [differences] using ih

private lemma differences_word (xs : List Bool) (j : ℕ) (h : j+1<xs.length) :
    word (differences xs) j = (word xs j ^^ word xs (j+1)) := by
  induction xs generalizing j with
  | nil => simp at h
  | cons a xs ih =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases j with
      | zero => rfl
      | succ j =>
        simpa only [differences, word, List.getElem?_cons_succ] using
          ih j (by simpa using h)

private lemma cell_congr (n : ℕ) (f g : ℕ → Bool)
    (h : ∀ j≤n, f j=g j) (a b : ℕ) (hab : a+b≤n) :
    cell f a b = cell g a b := by
  induction a generalizing b with
  | zero => exact h b (by omega)
  | succ a ih => rw [cell, cell, ih b (by omega), ih (b+1) (by omega)]

private lemma cell_delta (f : ℕ → Bool) (a b : ℕ) :
    cell (fun j => f j ^^ f (j+1)) a b = cell f (a+1) b := by
  induction a generalizing b with
  | zero => rfl
  | succ a ih => simp only [cell, ih]

private lemma leftEdge_length (n : ℕ) (xs : List Bool) :
    (leftEdge n xs).length = n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [leftEdge, ih]

private lemma leftEdge_word (n : ℕ) (xs : List Bool) (hn : n≤xs.length)
    (j : ℕ) (hj : j<n) : word (leftEdge n xs) j = cell (word xs) j 0 := by
  induction n generalizing xs j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
      cases xs with
      | nil => simp at hn
      | cons b xs => rfl
    | succ j =>
      change word (leftEdge n (differences xs)) j = cell (word xs) (j+1) 0
      rw [ih (differences xs) (by rw [differences_length]; omega) j (by omega)]
      calc
        cell (word (differences xs)) j 0 =
            cell (fun k => word xs k ^^ word xs (k+1)) j 0 :=
          cell_congr j _ _ (fun k hk => differences_word xs k (by omega)) j 0 (by omega)
        _ = cell (word xs) (j+1) 0 := cell_delta _ _ _

private lemma cell_mirror (n : ℕ) (f g : ℕ → Bool)
    (h : ∀ j≤n, g j=f (n-j)) (a b c : ℕ) (habc : a+b+c=n) :
    cell g a b = cell f a c := by
  induction a generalizing b c with
  | zero => simpa only [cell, show n-b=c by omega] using h b (by omega)
  | succ a ih =>
    rw [cell, ih b (c+1) (by omega), ih (b+1) c (by omega), cell]
    exact Bool.xor_comm _ _

private lemma rightEdge_word (xs : List Bool) (j : ℕ) (hj : j<xs.length) :
    word (rightEdge xs) j = turn (xs.length-1) (word xs) j := by
  rw [rightEdge, leftEdge_word xs.length xs.reverse (by simp) j hj]
  exact cell_mirror (xs.length-1) (word xs) (word xs.reverse)
    (by
      intro k hk
      unfold word
      rw [List.getElem?_reverse (by omega)]) j 0 (xs.length-1-j) (by omega)
end D5.S3.Combinatorics.XorTriangle.ReversibleSideMap
namespace D5.S3.Combinatorics.XorTriangle.ReversibleSideMap
open D5.S3.Combinatorics.XorTriangle.ValueOne

private lemma rightEdge_length (xs : List Bool) : (rightEdge xs).length=xs.length :=
  leftEdge_length _ _

private lemma rightEdge_represents (n : ℕ) (xs : List Bool) (f : ℕ → Bool)
    (hlen : xs.length=n+1) (h : ∀j≤n, word xs j=f j) :
    ∀j≤n, word (rightEdge xs) j=turn n f j := by
  intro j hj
  rw [rightEdge_word xs j (by omega), hlen]
  change cell (word xs) j (n-j) = cell f j (n-j)
  exact cell_congr n _ _ h _ _ (by omega)

/-- Three clockwise side changes recover every finite binary row, including the empty row.
The rotation argument follows Ilya Bogdanov's MathOverflow answer 359278,
revision 5, https://mathoverflow.net/a/359278 (CC BY-SA 4.0). -/
theorem rightEdge_cube (xs : List Bool) :
    rightEdge (rightEdge (rightEdge xs)) = xs := by
  cases hx : xs.length with
  | zero =>
    have : xs=[] := List.length_eq_zero_iff.mp hx
    subst xs
    rfl
  | succ n =>
    have h₁ := rightEdge_represents n xs (word xs) hx (fun _ _ => rfl)
    have h₂ := rightEdge_represents n (rightEdge xs) (turn n (word xs))
      (by rw [rightEdge_length,hx]) h₁
    have h₃ := rightEdge_represents n (rightEdge (rightEdge xs))
      (turn n (turn n (word xs))) (by rw [rightEdge_length,rightEdge_length,hx]) h₂
    apply List.ext_getElem
    · simp only [rightEdge_length]
    · intro j hj hj'
      have he := (h₃ j (by omega)).trans (turn_cube n (word xs) j (by omega))
      simpa only [word, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hj', Option.getD_some] using he

/-- The retained right edge is a permutation at every width; its inverse is two turns. -/
def rightEdgeEquiv (n : ℕ) : {xs : List Bool // xs.length=n} ≃
    {xs : List Bool // xs.length=n} where
  toFun xs := ⟨rightEdge xs.val, (rightEdge_length xs.val).trans xs.property⟩
  invFun xs := ⟨rightEdge (rightEdge xs.val), (by rw [rightEdge_length,rightEdge_length]; exact xs.property)⟩
  left_inv xs := Subtype.ext (rightEdge_cube xs.val)
  right_inv xs := Subtype.ext (rightEdge_cube xs.val)
end D5.S3.Combinatorics.XorTriangle.ReversibleSideMap
