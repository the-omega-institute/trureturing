/- GID: D5/S3/Combinatorics/Polyomino/SquareSpiralShells
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Polyomino/SquareSpiralShells
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every positive index of the reflected square spiral belongs to its computed shell and side. -/

import OmegaBuild.Commands
import Mathlib.Tactic
import Mathlib.Data.Nat.Find
import D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum

compile_only_with_mathlib

namespace SpiralQueens

open D5.S3.Combinatorics.Polyomino.IrwinA138099HookSum (WalkState walk frame layer_walk)

def shellPoint (r d : ℤ) : ℤ × ℤ :=
  if d < 2*r then (r, d-r+1)
  else if d < 4*r then (3*r-1-d, r)
  else if d < 6*r then (-r, 5*r-1-d)
  else (d-7*r+1, -r)

private def reflected (p : ℤ × ℤ) : ℤ × ℤ := (-p.1, p.2)

-- The upstream walk uses west, north, east, south in integer coordinates.
-- Reflecting x makes its directions right, up, left, down.
def spiral (n : ℕ) : ℤ × ℤ := reflected (walk n).cell

private def OddState (k : ℕ) : Prop :=
  walk ((2*k+1)*(2*k+1)-1) = ⟨(-(k : ℤ), -(k : ℤ)), 4*k, 2*k⟩

private def EvenState (k : ℕ) : Prop :=
  walk ((2*k+2)*(2*k+2)-1) = ⟨((k : ℤ), (k : ℤ)+1), 4*k+2, 2*k+1⟩

private theorem layer_end_index (m : ℕ) :
    m*m+m+m = (m+1)*(m+1)-1 := by
  rw [show (m+1)*(m+1) = m*m+m+m+1 by ring]
  omega

private theorem odd_layer (k : ℕ) (h : OddState k) :
    (∀ t < 2*k+1, walk ((2*k+1)*(2*k+1)+t) =
      ⟨(-(k : ℤ)-1, -(k : ℤ)+(t : ℤ)), 4*k+1, t⟩) ∧
    (∀ t ≤ 2*k+1, walk ((2*k+1)*(2*k+1)+(2*k+1)+t) =
      ⟨(-(k : ℤ)+(t : ℤ)-1, (k : ℤ)+1), 4*k+2, t⟩) := by
  have h' : walk ((2*k+1)*(2*k+1)-1) =
      ⟨(-(k : ℤ), -(k : ℤ)), 2*(2*k+1)-2, (2*k+1)-1⟩ := by
    unfold OddState at h
    rw [h, show 2*(2*k+1)-2 = 4*k by omega, show 2*k+1-1 = 2*k by omega]
  obtain ⟨h₁, h₂⟩ := layer_walk (2*k+1) (by omega) _ h'
  constructor
  · intro t ht
    rw [h₁ t ht]
    unfold frame
    simp [show 2*(2*k+1)-1 = 4*k+1 by omega]
    ring
  · intro t ht
    rw [h₂ t ht]
    unfold frame
    simp [show 2*(2*k+1) = 4*k+2 by omega]
    constructor <;> ring

private theorem even_layer (k : ℕ) (h : EvenState k) :
    (∀ t < 2*k+2, walk ((2*k+2)*(2*k+2)+t) =
      ⟨((k : ℤ)+1, (k : ℤ)+1-(t : ℤ)), 4*k+3, t⟩) ∧
    (∀ t ≤ 2*k+2, walk ((2*k+2)*(2*k+2)+(2*k+2)+t) =
      ⟨((k : ℤ)+1-(t : ℤ), -(k : ℤ)-1), 4*k+4, t⟩) := by
  have h' : walk ((2*k+2)*(2*k+2)-1) =
      ⟨((k : ℤ), (k : ℤ)+1), 2*(2*k+2)-2, (2*k+2)-1⟩ := by
    unfold EvenState at h
    rw [h, show 2*(2*k+2)-2 = 4*k+2 by omega, show 2*k+2-1 = 2*k+1 by omega]
  obtain ⟨h₁, h₂⟩ := layer_walk (2*k+2) (by omega) _ h'
  have hp : (2*k+2)%2 = 0 := by omega
  constructor
  · intro t ht
    rw [h₁ t ht]
    unfold frame
    simp [hp, show 2*(2*k+2)-1 = 4*k+3 by omega]
    ring
  · intro t ht
    rw [h₂ t ht]
    unfold frame
    simp [hp, show 2*(2*k+2) = 4*k+4 by omega]
    constructor <;> ring

private theorem even_of_odd (k : ℕ) (h : OddState k) : EvenState k := by
  have he := (odd_layer k h).2 (2*k+1) (le_refl _)
  rw [layer_end_index, show 2*k+1+1 = 2*k+2 by omega] at he
  unfold EvenState
  rw [he]
  push_cast
  congr 2
  ring

private theorem odd_succ_of_even (k : ℕ) (h : EvenState k) : OddState (k+1) := by
  have he := (even_layer k h).2 (2*k+2) (le_refl _)
  rw [layer_end_index, show 2*k+2+1 = 2*(k+1)+1 by omega] at he
  unfold OddState
  rw [he]
  push_cast
  congr 2 <;> ring

private theorem odd_state (k : ℕ) : OddState k := by
  induction k with
  | zero => rfl
  | succ k ih => exact odd_succ_of_even k (even_of_odd k ih)

private theorem even_state (k : ℕ) : EvenState k :=
  even_of_odd k (odd_state k)

private def base (k : ℕ) : ℕ := (2*k+1)*(2*k+1)

private theorem base_succ (k : ℕ) : base (k+1) = base k + 8*(k+1) := by
  unfold base
  ring

-- This radius uses the shifted natural index k = r - 1. The four blocks
-- start at the two successive squares and at the corresponding half turns.
private theorem spiral_shell (k d : ℕ) (hd : d < 8*(k+1)) :
    spiral (base k+d) = shellPoint ((k : ℤ)+1) (d : ℤ) := by
  let m := 2*k+1
  let l := 2*k+2
  have hbase : l*l = base k + 2*m + 1 := by
    unfold base
    dsimp [m, l]
    ring
  by_cases h₁ : d < m
  · have hw := (odd_layer k (odd_state k)).1 d h₁
    unfold spiral base
    rw [hw]
    unfold reflected shellPoint
    dsimp only
    split_ifs <;> (dsimp [m] at h₁; apply Prod.ext <;> dsimp only <;> omega)
  by_cases h₂ : d ≤ 2*m
  · let t := d-m
    have ht : t ≤ m := by dsimp [t]; omega
    have htd : d = m+t := by dsimp [t]; omega
    have hw := (odd_layer k (odd_state k)).2 t ht
    have hidx : base k+d = (2*k+1)*(2*k+1)+(2*k+1)+t := by
      change base k+d = base k+m+t
      omega
    unfold spiral
    rw [hidx, hw]
    unfold reflected shellPoint
    dsimp only
    have ht' : (d:ℤ) = (m:ℤ)+(t:ℤ) := by exact_mod_cast htd
    dsimp [m] at ht' h₁ h₂ ht
    split_ifs <;> (apply Prod.ext <;> dsimp only <;> omega)
  by_cases h₃ : d < 2*m+1+l
  · let t := d-(2*m+1)
    have ht : t < l := by dsimp [t]; omega
    have htd : d = 2*m+1+t := by dsimp [t]; omega
    have hw := (even_layer k (even_state k)).1 t ht
    have hidx : base k+d = (2*k+2)*(2*k+2)+t := by
      change base k+d = l*l+t
      omega
    unfold spiral
    rw [hidx, hw]
    unfold reflected shellPoint
    dsimp only
    have ht' : (d:ℤ) = 2*(m:ℤ)+1+(t:ℤ) := by exact_mod_cast htd
    dsimp [m, l] at ht' h₁ h₂ h₃ ht
    split_ifs <;> (apply Prod.ext <;> dsimp only <;> omega)
  · let t := d-(2*m+1+l)
    have ht : t ≤ l := by
      dsimp [t, m, l] at *
      omega
    have htd : d = 2*m+1+l+t := by dsimp [t]; omega
    have hw := (even_layer k (even_state k)).2 t ht
    have hidx : base k+d = (2*k+2)*(2*k+2)+(2*k+2)+t := by
      change base k+d = l*l+l+t
      omega
    unfold spiral
    rw [hidx, hw]
    unfold reflected shellPoint
    dsimp only
    have ht' : (d:ℤ) = 2*(m:ℤ)+1+(l:ℤ)+(t:ℤ) := by exact_mod_cast htd
    dsimp [m, l] at ht' h₁ h₂ h₃ ht
    split_ifs <;> (apply Prod.ext <;> dsimp only <;> omega)

private theorem decompose_label {n : ℕ} (hn : 0 < n) :
    ∃ k d : ℕ, n = base k+d ∧ d < 8*(k+1) := by
  have hex : ∃ k, n < base (k+1) := by
    refine ⟨n, ?_⟩
    unfold base
    have hmul : 2*(n+1)+1 ≤ (2*(n+1)+1)*(2*(n+1)+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  let k := Nat.find hex
  have hhi : n < base (k+1) := Nat.find_spec hex
  have hlo : base k ≤ n := by
    by_cases hz : k = 0
    · rw [hz]
      exact hn
    · have hk : k-1 < Nat.find hex := by change k-1 < k; omega
      have hm := Nat.find_min hex hk
      have hs : k-1+1 = k := by omega
      rw [hs] at hm
      omega
  rw [base_succ] at hhi
  exact ⟨k, n-base k, by omega, by omega⟩

/-- Every positive label lies on a half-open side of a square shell. -/
theorem spiral_shells {n : ℕ} (hn : 0 < n) :
    ∃ k d : ℕ, n = (2*k+1)*(2*k+1)+d ∧ d < 8*(k+1) ∧
      spiral n = shellPoint ((k : ℤ)+1) (d : ℤ) := by
  obtain ⟨k, d, h, hd⟩ := decompose_label hn
  refine ⟨k, d, h, hd, ?_⟩
  rw [h]
  exact spiral_shell k d hd

end SpiralQueens
