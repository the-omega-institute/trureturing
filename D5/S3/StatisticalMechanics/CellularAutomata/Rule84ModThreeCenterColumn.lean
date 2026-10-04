/- GID: D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rule 84 has center column 1, then (1, 2, 2) modulo three for all time. -/

/-
proof_shape: result: content
escape_witness: invariant_all: every length-seven window starting at x >= -5 lies
  in the phase language and the boundary window is 0000021, 0000011 or 0000020.
  Its all-time induction uses the finite bulk and boundary closure certificates.
  The center value is obtained from the sixth letter on the live proof path.
admission_basis: open-problem-resolution (#12485; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
Private theorems:
  zero_left: content; escape_witness: the zero half-plane, by induction on time.
  invariant_all: content; escape_witness: the forward-invariant window languages,
    by induction on time with distinct boundary and bulk cases.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.StatisticalMechanics.CellularAutomata.Rule84ModThreeCenterColumn

/-- The canonical positive-coefficient ANF lift of Rule 84. -/
private def rule84 (a b c : ZMod 3) : ZMod 3 := (a + b + a*b) * (1 + c)

/-- The synchronous integer-lattice orbit from the single seed at zero. -/
def A : ℕ → ℤ → ZMod 3
  | 0, x => if x = 0 then 1 else 0
  | t + 1, x => rule84 (A t (x-1)) (A t x) (A t (x+1))

def claim : Prop := A 0 0 = 1 ∧ ∀ s : ℕ,
  A (3*s+1) 0 = 1 ∧ A (3*s+2) 0 = 2 ∧ A (3*s+3) 0 = 2

private abbrev Word := Fin 7 → ZMod 3

/-- The common 31-word window language. -/
private def K : Finset Word := ⟨(([![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 2, 1, 1, 1, 0],
    ![0, 0, 2, 1, 1, 2, 2],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 1, 0],
    ![0, 1, 1, 0, 0, 2, 1],
    ![0, 2, 1, 1, 1, 0, 0],
    ![0, 2, 1, 1, 2, 2, 0],
    ![1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 0, 0],
    ![1, 0, 0, 2, 1, 1, 1],
    ![1, 0, 0, 2, 1, 1, 2],
    ![1, 0, 1, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0, 1],
    ![1, 0, 1, 1, 0, 0, 2],
    ![1, 1, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 1, 0, 0],
    ![1, 1, 0, 0, 2, 1, 1],
    ![1, 1, 1, 0, 0, 0, 0],
    ![1, 1, 2, 2, 0, 1, 0],
    ![1, 2, 2, 0, 1, 0, 0],
    ![1, 2, 2, 0, 1, 0, 1],
    ![2, 0, 1, 0, 0, 0, 0],
    ![2, 0, 1, 0, 1, 1, 0],
    ![2, 1, 1, 1, 0, 0, 0],
    ![2, 1, 1, 2, 2, 0, 1],
    ![2, 2, 0, 1, 0, 0, 0],
    ![2, 2, 0, 1, 0, 1, 1]] : List Word) : Multiset Word), by decide +kernel⟩

/-- The three languages, indexed by time modulo three. -/
private def L (r : Fin 3) : Finset Word := match r.val with
  | 0 => ⟨K.val + (([![0, 0, 0, 0, 0, 2, 1],
    ![0, 0, 0, 0, 2, 1, 1],
    ![0, 0, 0, 2, 1, 1, 1],
    ![0, 0, 0, 2, 1, 1, 2]] : List Word) : Multiset Word), by decide +kernel⟩
  | 1 => ⟨K.val + (([![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 2]] : List Word) : Multiset Word), by decide +kernel⟩
  | _ => ⟨K.val + (([![0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 2, 0, 1],
    ![0, 0, 0, 2, 0, 1, 0],
    ![0, 0, 2, 0, 1, 0, 0],
    ![0, 0, 2, 0, 1, 0, 1],
    ![0, 2, 0, 1, 0, 0, 0],
    ![0, 2, 0, 1, 0, 1, 1]] : List Word) : Multiset Word), by decide +kernel⟩

/-- The boundary window at position -5. -/
private def boundary (r : Fin 3) : Word := match r.val with
  | 0 => ![0, 0, 0, 0, 0, 2, 1]
  | 1 => ![0, 0, 0, 0, 0, 1, 1]
  | _ => ![0, 0, 0, 0, 0, 2, 0]


private def window (t : ℕ) (x : ℤ) : Word := fun i => A t (x + (i.val : ℤ))

private def slice (z : Fin 9 → ZMod 3) (j : Fin 3) : Word := fun i =>
  z ⟨j.val + i.val, by omega⟩

private def image (z : Fin 9 → ZMod 3) : Word := fun i =>
  rule84 (z ⟨i.val, by omega⟩) (z ⟨i.val+1, by omega⟩) (z ⟨i.val+2, by omega⟩)

private def boundaryImage (w : Word) (a : ZMod 3) : Word := fun i =>
  rule84 (if h : 0 < i.val then w ⟨i.val-1, by omega⟩ else 0)
    (w i) (if h : i.val+1 < 7 then w ⟨i.val+1, h⟩ else a)

private theorem zero_left (t : ℕ) : ∀ x : ℤ, x < 0 → A t x = 0 := by
  induction t with
  | zero =>
      intro x hx
      simp [A, show x ≠ 0 by omega]
  | succ t ih =>
      intro x hx
      simp only [A]
      rw [ih (x-1) (by omega), ih x hx]
      simp [rule84]

/-- All admissible windows and the distinguished boundary window. -/
private def Invariant (t : ℕ) : Prop :=
  (∀ x : ℤ, -5 ≤ x → window t x ∈ L (Fin.ofNat 3 t)) ∧
  window t (-5) = boundary (Fin.ofNat 3 t)

private theorem invariant_all (n : ℕ) : Invariant (n+1) := by
  have bulk_closed : ∀ r : Fin 3, ∀ w ∈ L r, ∀ a b : ZMod 3,
      slice (Fin.append w ![a, b]) 1 ∈ L r → slice (Fin.append w ![a, b]) 2 ∈ L r →
      image (Fin.append w ![a, b]) ∈ L (Fin.ofNat 3 (r.val + 1)) := by
    decide +kernel

  have boundary_closed : ∀ r : Fin 3, ∀ a : ZMod 3,
      Fin.snoc (Fin.tail (boundary r)) a ∈ L r →
      boundaryImage (boundary r) a = boundary (Fin.ofNat 3 (r.val + 1)) := by
    decide +kernel

  have invariant_base : Invariant 1 := by
    constructor
    · intro x hx
      by_cases h : x ≤ 1
      · have hc : x = -5 ∨ x = -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 := by omega
        rcases hc with hc | hc | hc | hc | hc | hc | hc <;> subst x <;> decide +kernel
      · have hw : window 1 x = ![0, 0, 0, 0, 0, 0, 0] := by
          funext i
          dsimp [window, A, rule84]
          have h₁ : x + (i.val : ℤ) - 1 ≠ 0 := by omega
          have h₂ : x + (i.val : ℤ) ≠ 0 := by omega
          have h₃ : x + (i.val : ℤ) + 1 ≠ 0 := by omega
          simp [h₁, h₂, h₃]
          fin_cases i <;> rfl
        rw [hw]
        decide +kernel
    · decide

  have invariant_step (t : ℕ) (ht : Invariant t) : Invariant (t+1) := by
    have hphase : Fin.ofNat 3 (t+1) = Fin.ofNat 3 ((Fin.ofNat 3 t).val + 1) := by
      apply Fin.ext
      dsimp [Fin.ofNat]
      omega
    have hb : window (t+1) (-5) = boundary (Fin.ofNat 3 ((Fin.ofNat 3 t).val + 1)) := by
      have hs : Fin.snoc (Fin.tail (window t (-5))) (A t 2) = window t (-4) := by
        funext i
        fin_cases i <;> simp [Fin.snoc, Fin.tail, window]
      have hm : Fin.snoc (Fin.tail (boundary (Fin.ofNat 3 t))) (A t 2) ∈ L (Fin.ofNat 3 t) := by
        rw [← ht.2, hs]
        exact ht.1 (-4) (by omega)
      have he : window (t+1) (-5) = boundaryImage (window t (-5)) (A t 2) := by
        funext i
        dsimp [window, boundaryImage]
        simp only [A]
        congr 1
        · split_ifs with hi
          · congr 1
            omega
          · have hv : i.val = 0 := by omega
            simp [hv, zero_left t (-6) (by omega)]
        · split_ifs with hi
          · congr 1
            omega
          · have hv : i.val = 6 := by omega
            simp [hv]
      rw [he, ht.2]
      exact boundary_closed (Fin.ofNat 3 t) (A t 2) hm
    constructor
    · intro x hx
      by_cases hxb : x = -5
      · subst x
        rw [hphase, hb]
        have hmem : ∀ r : Fin 3, boundary r ∈ L r := by decide +kernel
        exact hmem _
      · let z := Fin.append (window t (x-1)) ![A t (x+6), A t (x+7)]
        have hz (i : Fin 9) : z i = A t (x - 1 + (i.val : ℤ)) := by
          fin_cases i <;> simp [z, Fin.append, Fin.addCases, window] <;> congr 1 <;> omega
        have hs (j : Fin 3) : slice z j = window t (x-1+(j.val : ℤ)) := by
          funext i
          dsimp [slice, window]
          rw [hz]
          congr 1
          simp only [Nat.cast_add]
          omega
        have hout : image z = window (t+1) x := by
          funext i
          dsimp [image, window]
          rw [hz, hz, hz]
          simp only [A]
          congr 1 <;> congr 1 <;>
            (try simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]) <;> omega
        rw [hphase, ← hout]
        exact bulk_closed (Fin.ofNat 3 t) (window t (x-1))
          (ht.1 (x-1) (by omega)) (A t (x+6)) (A t (x+7))
          (by rw [hs]; exact ht.1 _ (by dsimp; omega))
          (by rw [hs]; exact ht.1 _ (by dsimp; omega))
    · rw [hphase]
      exact hb

  induction n with
  | zero => exact invariant_base
  | succ n ih => exact invariant_step (n+1) ih


theorem result : claim := by
  constructor
  · decide
  · intro s
    have h₁ := congrFun (invariant_all (3*s)).2 (5 : Fin 7)
    have h₂ := congrFun (invariant_all (3*s+1)).2 (5 : Fin 7)
    have h₃ := congrFun (invariant_all (3*s+2)).2 (5 : Fin 7)
    have p₁ : Fin.ofNat 3 (3*s+1) = 1 := by
      apply Fin.ext
      dsimp [Fin.ofNat]
      omega
    have p₂ : Fin.ofNat 3 (3*s+2) = 2 := by
      apply Fin.ext
      dsimp [Fin.ofNat]
      omega
    have p₃ : Fin.ofNat 3 (3*s+3) = 0 := by
      apply Fin.ext
      dsimp [Fin.ofNat]
      omega
    constructor
    · simpa [window, p₁, boundary] using h₁
    · constructor
      · simpa [window, Nat.add_assoc, p₂, boundary] using h₂
      · simpa [window, Nat.add_assoc, p₃, boundary] using h₃

end D5.S3.StatisticalMechanics.CellularAutomata.Rule84ModThreeCenterColumn
