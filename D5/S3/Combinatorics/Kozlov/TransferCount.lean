/- GID: D5/S3/Combinatorics/Kozlov/TransferCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Kozlov/TransferCount
   mirror-E: none(waiver:finite-state-chain-counting)
   anchors: [mathlib/module/Mathlib.Data.Matrix.Mul]
   utility: none
   digest: A finite-state transition matrix counts tuples satisfying adjacent transitions. -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.Tuple.Basic

-- Source: https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Lattice/TransferEhrhart.lean
/-
Upstream pins: Lean v4.34.0-rc2, Mathlib 3a8a89422e16d67b7ae57698f6d96e389e4d4202.
When the project's pinned Mathlib provides an equivalent declaration,
replace the transplanted declaration with a direct import and use that result.

MIT License

Copyright (c) 2026 Jan Snellman

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

open Finset Matrix
open scoped BigOperators

namespace D5.S3.Combinatorics.Kozlov

section Generic

variable {α : Type*} {m : ℕ} (X : Finset α) (σ : α → Fin m)
  (cond : Fin m → α → Prop) [∀ k x, Decidable (cond k x)]

/-- Initial vector: `uG[k] = #{x ∈ X : σ x = k}`. -/
def uG : Fin m → ℕ := fun k => #(X.filter fun x => σ x = k)

/-- The transfer matrix counts allowed next values by state. The row is
the previous state, the column the current one. -/
def TG : Matrix (Fin m) (Fin m) ℕ :=
  Matrix.of fun k k' => #(X.filter fun x => σ x = k' ∧ cond k x)

/-- A chained `(r+1)`-tuple: consecutive elements satisfy the transition. -/
def ChainG {r : ℕ} (q : Fin (r + 1) → α) : Prop :=
  ∀ i : Fin r, cond (σ (q i.castSucc)) (q i.succ)

instance {r : ℕ} (q : Fin (r + 1) → α) : Decidable (ChainG σ cond q) := by
  unfold ChainG; infer_instance

/-- The chained tuples over `X`, as a `Finset`. -/
def chainG (r : ℕ) : Finset (Fin (r + 1) → α) :=
  (Fintype.piFinset fun _ => X).filter (ChainG σ cond)

/-- Chained tuples refined by the state of their last element. -/
def chainTopG (r : ℕ) (k : Fin m) : ℕ :=
  #((chainG X σ cond r).filter fun q => σ (q (Fin.last r)) = k)

variable {X σ cond}

omit [∀ k x, Decidable (cond k x)] in
theorem chainG_snoc_iff {r : ℕ} {q : Fin (r + 1) → α} {x : α} :
    ChainG σ cond (Fin.snoc q x) ↔
      ChainG σ cond q ∧ cond (σ (q (Fin.last r))) x := by
  have e : ∀ i : Fin r, (i.castSucc.succ : Fin (r + 2)) = i.succ.castSucc := fun i => Fin.ext rfl
  unfold ChainG
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, e, Fin.succ_last, Fin.snoc_last]

theorem chainTopG_zero (k : Fin m) : chainTopG X σ cond 0 k = uG X σ k := by
  unfold chainTopG uG chainG
  refine Finset.card_bij' (fun q _ => q 0) (fun x _ => fun _ => x) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, Fintype.mem_piFinset] at hq ⊢
    exact ⟨hq.1.1 0, hq.2⟩
  · intro x hx
    simp only [mem_filter, Fintype.mem_piFinset] at hx ⊢
    exact ⟨⟨fun _ => hx.1, fun i => i.elim0⟩, hx.2⟩
  · intro q _
    funext i
    rw [show i = 0 from Fin.ext (by have := i.isLt; simp)]
  · intro x _; rfl

theorem chainTopG_succ (r : ℕ) (k' : Fin m) :
    chainTopG X σ cond (r + 1) k' =
      ∑ k, chainTopG X σ cond r k * TG X σ cond k k' := by
  unfold chainTopG
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q => σ (q (Fin.last r).castSucc))
    (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TG, Matrix.of_apply, ← Finset.card_product]
  refine Finset.card_bij' (fun q _ => (Fin.init q, q (Fin.last (r + 1))))
    (fun p _ => Fin.snoc p.1 p.2) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [chainG, mem_filter, Fintype.mem_piFinset] at hq
    obtain ⟨⟨⟨hX, hc⟩, hlast⟩, hk⟩ := hq
    rw [← Fin.snoc_init_self q] at hc
    obtain ⟨hc', hl⟩ := chainG_snoc_iff.mp hc
    simp only [chainG, mem_product, mem_filter, Fintype.mem_piFinset]
    refine ⟨⟨⟨fun i => hX _, hc'⟩, hk⟩, hX _, hlast, ?_⟩
    have : Fin.init q (Fin.last r) = q (Fin.last r).castSucc := rfl
    rw [this, hk] at hl
    exact hl
  · rintro ⟨q', x⟩ hp
    simp only [chainG, mem_product, mem_filter, Fintype.mem_piFinset] at hp
    obtain ⟨⟨⟨hX, hc⟩, hk⟩, hx, hxk, hcx⟩ := hp
    simp only [chainG, mem_filter, Fintype.mem_piFinset, Fin.snoc_last, Fin.snoc_castSucc]
    refine ⟨⟨⟨fun i => ?_, chainG_snoc_iff.mpr ⟨hc, by rw [hk]; exact hcx⟩⟩, hxk⟩, hk⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]; exact hx
    · rw [Fin.snoc_castSucc]; exact hX j
  · intro q _; exact Fin.snoc_init_self q
  · rintro ⟨q', x⟩ _
    simp only [Fin.init_snoc, Fin.snoc_last]

theorem chainTopG_eq (r : ℕ) :
    chainTopG X σ cond r = uG X σ ᵥ* TG X σ cond ^ r := by
  induction r with
  | zero =>
    funext k
    rw [pow_zero, Matrix.vecMul_one, chainTopG_zero]
  | succ r ih =>
    funext k'
    rw [chainTopG_succ, pow_succ, ← Matrix.vecMul_vecMul, ← ih]
    rfl

/-- **The generic transfer-matrix count**: `#(chained tuples) = u · TG(g₀)⋯TG(g_{r−1}) · 𝟙`. -/
theorem card_chainG (r : ℕ) :
    #(chainG X σ cond r) = uG X σ ᵥ* TG X σ cond ^ r ⬝ᵥ (fun _ => 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q => σ (q (Fin.last r)))
    (t := univ) (fun _ _ => mem_univ _), ← chainTopG_eq]
  simp [dotProduct, chainTopG]


end Generic

end D5.S3.Combinatorics.Kozlov
