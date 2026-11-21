/- GID: D5/S3/Combinatorics/Kozlov/LexShadowSize
   generality: G
   mirror-B: none(waiver:probe-support)
   mirror-E: none(waiver:finite-lex-shadow-theory)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: Lex upper shadow sizes satisfy two-component exchange inequalities. -/

import Mathlib.Data.Nat.Choose.Basic

-- Source: https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/ModuleKK/GreedyPQ.lean
/-
Upstream pins: Lean v4.34.0-rc2, Mathlib 3a8a89422e16d67b7ae57698f6d96e389e4d4202.
Retire these declarations when the project's pinned Mathlib supplies equivalent results.

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

def sig : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, 0, t => if t = 0 then 0 else 1 + sig n 0 t
  | n+1, k+1, t => if t ≤ n.choose k then sig n k t
      else n.choose (k+1) + sig n (k+1) (t - n.choose k)
lemma sig_zero (n k : ℕ) : sig n k 0 = 0 := by
  induction n generalizing k with
  | zero => simp [sig]
  | succ n ih => cases k <;> simp [sig, ih]

lemma sig_n0_one (n : ℕ) : sig n 0 1 = n := by
  induction n with
  | zero => simp [sig]
  | succ n ih => simp [sig, ih]; omega

lemma sig_full (n k : ℕ) : sig n k (n.choose k) = n.choose (k+1) := by
  induction n generalizing k with
  | zero => cases k <;> simp [sig]
  | succ n ih =>
    cases k with
    | zero => simp [sig, sig_n0_one]; omega
    | succ k =>
      rw [Nat.choose_succ_succ]
      simp only [sig]
      by_cases h : n.choose k + n.choose (k+1) ≤ n.choose k
      · have h0 : n.choose (k+1) = 0 := by omega
        have hlt : n < k + 1 := Nat.choose_eq_zero_iff.mp h0
        rw [ite_eq_left h, h0, Nat.add_zero, ih, h0, Nat.choose_succ_succ, h0,
          Nat.choose_eq_zero_of_lt (by omega : n < k + 2)]
      · rw [ite_eq_right h, Nat.add_sub_cancel_left, ih, Nat.choose_succ_succ]

lemma sig_R1 {n k t : ℕ} (h : t ≤ n.choose k) : sig (n+1) (k+1) t = sig n k t := by
  simp [sig, h]

lemma sig_R2 {n k t : ℕ} (h : n.choose k ≤ t) :
    sig (n+1) (k+1) t = n.choose (k+1) + sig n (k+1) (t - n.choose k) := by
  by_cases h' : t ≤ n.choose k
  · have : t = n.choose k := le_antisymm h' h
    subst this; simp [sig, sig_full, sig_zero]
  · simp [sig, h']

lemma sig_incr (n k t : ℕ) (ht : t < n.choose k) : sig n k (t+1) ≤ sig n k t + (n - k) := by
  induction n generalizing k t with
  | zero => simp [sig]
  | succ n ih =>
    cases k with
    | zero =>
      have : t = 0 := by simp at ht; omega
      subst this; simp [sig, sig_n0_one]; omega
    | succ k =>
      rw [Nat.choose_succ_succ] at ht
      by_cases h1 : t + 1 ≤ n.choose k
      · rw [sig_R1 h1, sig_R1 (by omega)]
        have := ih k t (by omega); omega
      · rw [sig_R2 (by omega), sig_R2 (by omega)]
        have := ih (k+1) (t - n.choose k) (by simp only [Nat.succ_eq_add_one] at *; omega)
        rw [show t + 1 - n.choose k = t - n.choose k + 1 by omega]; omega

lemma sig_R2' {n k t u : ℕ} (h : t = n.choose k + u) :
    sig (n+1) (k+1) t = n.choose (k+1) + sig n (k+1) u := by
  rw [sig_R2 (by omega)]; congr 2; omega

/-- P(n), with the sum supplied as a separate argument `s` (to keep terms syntactic). -/
def PP (n : ℕ) : Prop := ∀ k k' x y s, k' ≤ k → s = x + y → s ≤ n.choose k → y ≤ n.choose k' →
  sig n k s ≤ sig n k x + sig n k' y

/-- Q(n), with the overflow `w` supplied as a separate argument. -/
def QQ (n : ℕ) : Prop := ∀ k k' x y w, k' ≤ k → x ≤ n.choose k → y ≤ n.choose k' →
  x + y = n.choose k + w → n.choose (k+1) + sig n k' w ≤ sig n k x + sig n k' y

lemma PQ_zero : PP 0 ∧ QQ 0 := by
  constructor
  · intro k k' x y s _ _ _ _; simp [sig]
  · intro k k' x y w _ _ _ _; simp [sig]

lemma PQ_succ_k'0 (n k : ℕ) :
    (∀ x y s, s = x + y → s ≤ (n+1).choose k → y ≤ (n+1).choose 0 →
      sig (n+1) k s ≤ sig (n+1) k x + sig (n+1) 0 y) ∧
    (∀ x y w, x ≤ (n+1).choose k → y ≤ (n+1).choose 0 → x + y = (n+1).choose k + w →
      (n+1).choose (k+1) + sig (n+1) 0 w ≤ sig (n+1) k x + sig (n+1) 0 y) := by
  have h01 := sig_n0_one (n+1)
  constructor
  · intro x y s hs h1 hy
    simp at hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl
    · subst hs; simp [sig_zero]
    · subst hs; have := sig_incr (n+1) k x (by omega); omega
  · intro x y w hx hy hw
    simp at hy
    have hf := sig_full (n+1) k
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl
    · have : x = (n+1).choose k := by omega
      have : w = 0 := by omega
      subst_vars; rw [hf, sig_zero]
    · rcases Nat.lt_or_ge x ((n+1).choose k) with hlt | hge
      · have hw0 : w = 0 := by omega
        have hx' : x + 1 = (n+1).choose k := by omega
        have := sig_incr (n+1) k x hlt
        rw [hx', hf] at this; subst hw0; rw [sig_zero]; omega
      · have : x = (n+1).choose k := by omega
        have : w = 1 := by omega
        subst_vars; rw [hf]

theorem PQ_all (n : ℕ) : PP n ∧ QQ n := by
  induction n with
  | zero => exact PQ_zero
  | succ n ih =>
    obtain ⟨hP, hQ⟩ := ih
    have fA := fun k => sig_full n k
    constructor
    · intro K K' x y s hk hs hsC hyC
      rcases K' with _ | k'
      · exact (PQ_succ_k'0 n K).1 x y s hs hsC hyC
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      have hk' : k' ≤ k := by omega
      rw [Nat.choose_succ_succ'] at hsC hyC
      subst hs
      rcases le_or_gt (x+y) (n.choose k) with hA | hA
      · -- case A
        rw [sig_R1 hA, sig_R1 (by omega : x ≤ n.choose k)]
        rcases le_or_gt y (n.choose k') with hY | hY
        · rw [sig_R1 hY]; exact hP k k' x y (x+y) hk' rfl hA hY
        · obtain ⟨y2, rfl⟩ : ∃ y2, y = n.choose k' + y2 := ⟨y - n.choose k', by omega⟩
          rw [sig_R2' rfl]
          rcases Nat.lt_or_ge k' k with hkk | hkk
          · have h1 := hP k k' (x+y2) (n.choose k') (x + (n.choose k' + y2)) hk' (by omega) hA le_rfl
            have h2 := hP k (k'+1) x y2 (x+y2) hkk rfl (by omega) (by omega)
            rw [fA] at h1; omega
          · have : k = k' := by omega
            subst this; omega
      · rcases le_or_gt (n.choose k) x with hB | hB
        · -- case B
          obtain ⟨x0, rfl⟩ : ∃ x0, x = n.choose k + x0 := ⟨x - n.choose k, by omega⟩
          rw [sig_R2' rfl, sig_R2' (by omega : n.choose k + x0 + y = n.choose k + (x0 + y))]
          rcases le_or_gt y (n.choose k') with hY | hY
          · rw [sig_R1 hY]
            have := hP (k+1) k' x0 y (x0+y) (by omega) rfl (by omega) hY; omega
          · obtain ⟨y2, rfl⟩ : ∃ y2, y = n.choose k' + y2 := ⟨y - n.choose k', by omega⟩
            rw [sig_R2' rfl]
            have h1 := hP (k+1) k' (x0+y2) (n.choose k') (x0 + (n.choose k' + y2)) (by omega)
              (by omega) (by omega) le_rfl
            have h2 := hP (k+1) (k'+1) x0 y2 (x0+y2) (by omega) rfl (by omega) (by omega)
            rw [fA] at h1; omega
        · -- case C
          obtain ⟨z, hz⟩ : ∃ z, x + y = n.choose k + z := ⟨x + y - n.choose k, by omega⟩
          rw [sig_R2' hz, sig_R1 (by omega : x ≤ n.choose k)]
          rcases le_or_gt y (n.choose k') with hY | hY
          · rw [sig_R1 hY]
            have h1 := hQ k k' x y z hk' (by omega) hY hz
            have h2 := hP (k+1) k' 0 z z (by omega) (by omega) (by omega) (by omega)
            rw [sig_zero] at h2; omega
          · obtain ⟨y2, rfl⟩ : ∃ y2, y = n.choose k' + y2 := ⟨y - n.choose k', by omega⟩
            rw [sig_R2' rfl]
            rcases le_or_gt (n.choose k) (x + n.choose k') with hw | hw
            · obtain ⟨w0, hw0⟩ : ∃ w0, x + n.choose k' = n.choose k + w0 :=
                ⟨x + n.choose k' - n.choose k, by omega⟩
              have h1 := hQ k k' x (n.choose k') w0 hk' (by omega) le_rfl hw0
              have h2 := hP (k+1) (k'+1) w0 y2 z (by omega) (by omega) (by omega) (by omega)
              have h3 := hP (k+1) k' 0 w0 w0 (by omega) (by omega) (by omega) (by omega)
              rw [fA] at h1; rw [sig_zero] at h3; omega
            · rcases Nat.lt_or_ge k' k with hkk | hkk
              · have h1 := hP k k' x (n.choose k') (x + n.choose k') hk' rfl (by omega) le_rfl
                have h2 := hQ k (k'+1) (x + n.choose k') y2 z hkk (by omega) (by omega) (by omega)
                have h3 := hP (k+1) (k'+1) 0 z z (by omega) (by omega) (by omega) (by omega)
                rw [fA] at h1; rw [sig_zero] at h3; omega
              · have : k = k' := by omega
                subst this; omega
    · intro K K' x y w hk hxC hyC hw
      rcases K' with _ | k'
      · exact (PQ_succ_k'0 n K).2 x y w hxC hyC hw
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      have hk' : k' ≤ k := by omega
      rw [Nat.choose_succ_succ'] at hxC hyC hw
      rw [Nat.choose_succ_succ' n (k+1)]
      have fB := fA (k+1)
      rcases le_or_gt (n.choose k) x with hB | hB
      · -- case A'
        obtain ⟨x0, rfl⟩ : ∃ x0, x = n.choose k + x0 := ⟨x - n.choose k, by omega⟩
        rw [sig_R2' rfl]
        rcases le_or_gt y (n.choose k') with hY | hY
        · rw [sig_R1 hY, sig_R1 (by omega : w ≤ n.choose k')]
          have := hQ (k+1) k' x0 y w (by omega) (by omega) hY (by omega); omega
        · obtain ⟨u, rfl⟩ : ∃ u, y = n.choose k' + u := ⟨y - n.choose k', by omega⟩
          rw [sig_R2' rfl]
          rcases le_or_gt (n.choose k') w with hW | hW
          · obtain ⟨w2, rfl⟩ : ∃ w2, w = n.choose k' + w2 := ⟨w - n.choose k', by omega⟩
            rw [sig_R2' rfl]
            have := hQ (k+1) (k'+1) x0 u w2 (by omega) (by omega) (by omega) (by omega); omega
          · rw [sig_R1 hW.le]
            have h1 := hP (k+1) (k'+1) x0 u (x0+u) (by omega) rfl (by omega) (by omega)
            have h2 := hQ (k+1) k' (x0+u) (n.choose k') w (by omega) (by omega) le_rfl (by omega)
            rw [fA] at h2; omega
      · -- case B'
        rw [sig_R1 hB.le]
        rcases le_or_gt y (n.choose k') with hY | hY
        · rw [sig_R1 hY, sig_R1 (by omega : w ≤ n.choose k')]
          have h1 := hQ k k' x y (w + n.choose (k+1)) hk' hB.le hY (by omega)
          have h2 := hQ (k+1) k' 0 (w + n.choose (k+1)) w (by omega) (by omega) (by omega) (by omega)
          rw [sig_zero] at h2; omega
        · obtain ⟨u, rfl⟩ : ∃ u, y = n.choose k' + u := ⟨y - n.choose k', by omega⟩
          rw [sig_R2' rfl]
          rcases le_or_gt (n.choose k') w with hW | hW
          · obtain ⟨w2, rfl⟩ : ∃ w2, w = n.choose k' + w2 := ⟨w - n.choose k', by omega⟩
            rw [sig_R2' rfl]
            rcases Nat.lt_or_ge k' k with hkk | hkk
            · have h1 := hQ k (k'+1) x u (w2 + n.choose (k+1)) hkk hB.le (by omega) (by omega)
              have h2 := hQ (k+1) (k'+1) 0 (w2 + n.choose (k+1)) w2 (by omega) (by omega)
                (by omega) (by omega)
              rw [sig_zero] at h2; omega
            · have : k = k' := by omega
              subst this; omega
          · rw [sig_R1 hW.le]
            rcases Nat.lt_or_ge k' k with hkk | hkk
            · rcases le_or_gt (n.choose k) (x + u) with hq | hq
              · obtain ⟨q, hqq⟩ : ∃ q, x + u = n.choose k + q := ⟨x + u - n.choose k, by omega⟩
                have h1 := hQ k (k'+1) x u q hkk hB.le (by omega) hqq
                have h2 := hP (k+1) (k'+1) 0 q q (by omega) (by omega) (by omega) (by omega)
                have h3 := hQ (k+1) k' q (n.choose k') w (by omega) (by omega) le_rfl (by omega)
                rw [sig_zero] at h2; rw [fA] at h3; omega
              · have h1 := hP k (k'+1) x u (x+u) hkk rfl hq.le (by omega)
                have h2 := hQ k k' (x+u) (n.choose k') (w + n.choose (k+1)) hk' hq.le le_rfl
                  (by omega)
                have h3 := hQ (k+1) k' 0 (w + n.choose (k+1)) w (by omega) (by omega) (by omega)
                  (by omega)
                rw [fA] at h2; rw [sig_zero] at h3; omega
            · have : k = k' := by omega
              subst this
              have h1 := hQ (k+1) k u x w (by omega) (by omega) hB.le (by omega)
              omega

/-- The two-component greedy inequalities (Proposition 3 of the note), for all n. -/
theorem sig_P (n k k' x y : ℕ) (hk : k' ≤ k) (h1 : x + y ≤ n.choose k) (h2 : y ≤ n.choose k') :
    sig n k (x + y) ≤ sig n k x + sig n k' y :=
  (PQ_all n).1 k k' x y (x+y) hk rfl h1 h2

theorem sig_Q (n k k' x y : ℕ) (hk : k' ≤ k) (hx : x ≤ n.choose k) (hy : y ≤ n.choose k')
    (h : n.choose k ≤ x + y) :
    n.choose (k+1) + sig n k' (x + y - n.choose k) ≤ sig n k x + sig n k' y :=
  (PQ_all n).2 k k' x y _ hk hx hy (by omega)
