/- GID: D5/S3/Quantum/Information/TorpedoGamePerfectClassical
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/TorpedoGamePerfectClassical
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Torpedo Game has a perfect classical strategy (value 1) for every d >= 5. -/

/-
proof_shape: result: content
escape_witness: form (1): the private proposition `exists_perfect` (for every d ≥ 5 a
  deterministic strategy wins on every input and question), proved from the explicit colouring
  `enc` and decoding `dec` (row pairs, a three-row block for odd d, the Fig. 9 table for d = 5)
  class by class, on the live path of `result`
admission_basis: open-problem-resolution (issue #11350)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Convex.StdSimplex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.TorpedoGamePerfectClassical

open Finset

/-- The answer that Bob must avoid for question `q` on input `(x, z)`: `x` for `q = ∞` (`none`)
and `q x - z` for `q ∈ ℤ_d`. The winning set is `w_q(x, z) = {a | a ≠ label q x z}`. -/
def label {d : ℕ} : Option (ZMod d) → ZMod d → ZMod d → ZMod d
  | none, x, _ => x
  | some q, x, z => q * x - z

/-- The winning probability of a classical strategy for the dimension-`d` Torpedo Game with
uniform referee inputs: shared randomness `l : Fin n` drawn from `μ`, encoding `e l x z j` (the
probability that Alice sends `j`) and decoding `f l j q c` (the probability that Bob answers `c`
to question `q` on message `j`). -/
noncomputable def winProb {d : ℕ} [NeZero d] {n : ℕ} (μ : Fin n → ℝ)
    (e : Fin n → ZMod d → ZMod d → ZMod d → ℝ)
    (f : Fin n → ZMod d → Option (ZMod d) → ZMod d → ℝ) : ℝ :=
  1 / ((d : ℝ) ^ 2 * (d + 1)) *
    ∑ x : ZMod d, ∑ z : ZMod d, ∑ q : Option (ZMod d), ∑ l : Fin n,
      μ l * ∑ j : ZMod d, e l x z j * ∑ c ∈ univ.filter (fun c => c ≠ label q x z), f l j q c

/-- The winning probabilities of all classical strategies. -/
def classicalValues (d : ℕ) [NeZero d] : Set ℝ :=
  {v | ∃ (n : ℕ) (μ : Fin n → ℝ) (e : Fin n → ZMod d → ZMod d → ZMod d → ℝ)
      (f : Fin n → ZMod d → Option (ZMod d) → ZMod d → ℝ),
      μ ∈ stdSimplex ℝ (Fin n) ∧ (∀ l x z, e l x z ∈ stdSimplex ℝ (ZMod d)) ∧
        (∀ l j q, f l j q ∈ stdSimplex ℝ (ZMod d)) ∧
        winProb μ e f = v}

/-- Eq. (11) of arXiv:2007.15643: the classical value `θ^C_d` of the Torpedo Game is `1` for
every `d ≥ 5`, i.e. `1` is the greatest winning probability of a classical strategy. -/
def claim : Prop := ∀ (d : ℕ) [NeZero d], 5 ≤ d → IsGreatest (classicalValues d) 1

private def decA {d : ℕ} (r : ZMod d) : Option (ZMod d) → ZMod d
  | none => r + 2
  | some q => if q = 0 ∨ q = -1 then q * (r + 1) - 2 else q * (r + 1)

private def decB {d : ℕ} (r : ZMod d) : Option (ZMod d) → ZMod d
  | none => r + 2
  | some q => if q = 0 ∨ q = 2 then q * r - 1 else q * r

private def decP {d : ℕ} (r : ZMod d) : Option (ZMod d) → ZMod d
  | none => r + 2
  | some q => q * r + if q = 1 ∨ q = 4 then 2 else if q = 2 then 3 else 1

private def decQ {d : ℕ} (r : ZMod d) : Option (ZMod d) → ZMod d
  | none => r
  | some q => q * (r + 1) - if q = 0 ∨ q = 3 then 1 else if q = 2 then 3 else 0

private def decR {d : ℕ} (r : ZMod d) : Option (ZMod d) → ZMod d
  | none => r + 1
  | some q => q * (r + 2) - if 2 * q = 1 ∨ 2 * q = 2 ∨ 2 * q = 3 then 3 else 0

/-- Rows paired into two classes: every row for even `d`, rows below `d - 3` for odd `d`. -/
private abbrev paired (d v : ℕ) : Prop := d % 2 = 0 ∨ v + 3 < d

/-- The message (colour class) of input `(x, z)`. -/
private def enc (d : ℕ) (x z : ZMod d) : ZMod d :=
  if paired d x.val then
    if x.val % 2 = 0 then (if z = 0 ∨ z = 1 then x else x + 1)
    else (if z = 0 ∨ z = 2 then x else x - 1)
  else if x.val + 3 = d then (if z = -1 ∨ z = -2 ∨ z = -3 then x + 2 else x)
  else if x.val + 2 = d then (if z = 0 ∨ z = 1 ∨ z = 3 then x - 1 else x)
  else (if z = 0 ∨ z = 2 ∨ z = 3 then x - 1 else x)

/-- Bob's answer to question `q` on message `j`. -/
private def dec (d : ℕ) (j : ZMod d) (q : Option (ZMod d)) : ZMod d :=
  if paired d j.val then
    if j.val % 2 = 0 then decA j q else decB (j - 1) q
  else if j.val + 3 = d then decP j q
  else if j.val + 2 = d then decQ (j - 1) q
  else decR (j - 2) q

/-- The Fig. 9 colouring for `d = 5` (rows `x`, columns `z`). -/
private def enc5 (x z : ZMod 5) : ZMod 5 :=
  ![![0, 1, 0, 4, 0], ![0, 3, 2, 4, 2], ![2, 4, 1, 1, 3], ![1, 1, 3, 3, 2], ![4, 0, 4, 2, 3]] x z

/-- A decoding for the Fig. 9 colouring. -/
private def dec5 : ZMod 5 → Option (ZMod 5) → ZMod 5
  | j, none => ![2, 1, 0, 0, 3] j
  | j, some q =>
    ![![2, 2, 4, 2, 2], ![1, 1, 3, 0, 3], ![4, 0, 1, 2, 1], ![0, 2, 2, 0, 1], ![1, 0, 0, 1, 0]] j q

/-- For every `d ≥ 5` some deterministic strategy wins on every input and question. -/
private theorem exists_perfect (d : ℕ) [NeZero d] (hd5 : 5 ≤ d) :
    ∃ (E : ZMod d → ZMod d → ZMod d) (D : ZMod d → Option (ZMod d) → ZMod d),
      ∀ x z q, D (E x z) q ≠ label q x z := by
  rcases Nat.lt_or_ge d 6 with h5 | hd
  · obtain rfl : d = 5 := by omega
    exact ⟨enc5, dec5, by decide⟩
  refine ⟨enc d, dec d, fun x z q => ?_⟩
  -- the constants `1, …, 5` are nonzero in `ZMod d`
  have hne : ∀ k : ℕ, 0 < k → k < d → (k : ZMod d) ≠ 0 := fun k hk hkd => by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd hk h) (by omega)
  have h1 : (1 : ZMod d) ≠ 0 := by exact_mod_cast hne 1 (by omega) (by omega)
  have h2 : (2 : ZMod d) ≠ 0 := by exact_mod_cast hne 2 (by omega) (by omega)
  have h3 : (3 : ZMod d) ≠ 0 := by exact_mod_cast hne 3 (by omega) (by omega)
  have h4 : (4 : ZMod d) ≠ 0 := by exact_mod_cast hne 4 (by omega) (by omega)
  have h5 : (5 : ZMod d) ≠ 0 := by exact_mod_cast hne 5 (by omega) (by omega)
  have sub : ∀ {a b c : ZMod d}, a - b = c → c ≠ 0 → a ≠ b :=
    fun h hc hab => hc (by rw [← h, hab, sub_self])
  -- each class leaves the decoded answer free, row by row
  have decA_row0 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z = 0 ∨ z = 1) → decA r q ≠ label q r z := by
    intro r q z hz
    cases q with
    | none =>
      refine sub (c := 2) ?_ h2
      simp only [decA, label]; ring
    | some q =>
      simp only [decA, label]
      split_ifs with hq
      · rcases hq with rfl | rfl <;> rcases hz with rfl | rfl
        · exact sub (c := -2) (by ring) (neg_ne_zero.mpr h2)
        · exact sub (c := -1) (by ring) (neg_ne_zero.mpr h1)
        · exact sub (c := -3) (by ring) (neg_ne_zero.mpr h3)
        · exact sub (c := -2) (by ring) (neg_ne_zero.mpr h2)
      · rcases hz with rfl | rfl
        · exact sub (c := q) (by ring) fun h => hq (Or.inl h)
        · exact sub (c := q + 1) (by ring) fun h => hq (Or.inr (by linear_combination h))
  have decA_row1 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z ≠ 0) → (z ≠ 2) → decA r q ≠ label q (r + 1) z := by
    intro r q z hz0 hz2
    cases q with
    | none =>
      refine sub (c := 1) ?_ h1
      simp only [decA, label]; ring
    | some q =>
      simp only [decA, label]
      split_ifs
      · exact sub (c := z - 2) (by ring) (sub_ne_zero.mpr hz2)
      · exact sub (c := z) (by ring) hz0
  have decB_row0 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z ≠ 0) → (z ≠ 1) → decB r q ≠ label q r z := by
    intro r q z hz0 hz1
    cases q with
    | none =>
      refine sub (c := 2) ?_ h2
      simp only [decB, label]; ring
    | some q =>
      simp only [decB, label]
      split_ifs
      · exact sub (c := z - 1) (by ring) (sub_ne_zero.mpr hz1)
      · exact sub (c := z) (by ring) hz0
  have decB_row1 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z = 0 ∨ z = 2) → decB r q ≠ label q (r + 1) z := by
    intro r q z hz
    cases q with
    | none =>
      refine sub (c := 1) ?_ h1
      simp only [decB, label]; ring
    | some q =>
      simp only [decB, label]
      split_ifs with hq
      · rcases hq with rfl | rfl <;> rcases hz with rfl | rfl
        · exact sub (c := -1) (by ring) (neg_ne_zero.mpr h1)
        · exact sub (c := 1) (by ring) h1
        · exact sub (c := -3) (by ring) (neg_ne_zero.mpr h3)
        · exact sub (c := -1) (by ring) (neg_ne_zero.mpr h1)
      · rcases hz with rfl | rfl
        · exact sub (c := -q) (by ring) (neg_ne_zero.mpr fun h => hq (Or.inl h))
        · exact sub (c := 2 - q) (by ring)
            fun h => hq (Or.inr (by linear_combination -h))
  have decP_row0 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z ≠ -1) → (z ≠ -2) → (z ≠ -3) → decP r q ≠ label q r z := by
    intro r q z hz1 hz2 hz3
    cases q with
    | none =>
      refine sub (c := 2) ?_ h2
      simp only [decP, label]; ring
    | some q =>
      simp only [decP, label]
      split_ifs
      · exact sub (c := z + 2) (by ring) fun h => hz2 (by linear_combination h)
      · exact sub (c := z + 3) (by ring) fun h => hz3 (by linear_combination h)
      · exact sub (c := z + 1) (by ring) fun h => hz1 (by linear_combination h)
  have decP_row1 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z = 0 ∨ z = 1 ∨ z = 3) → decP r q ≠ label q (r + 1) z := by
    intro r q z hz
    cases q with
    | none =>
      refine sub (c := 1) ?_ h1
      simp only [decP, label]; ring
    | some q =>
      simp only [decP, label]
      split_ifs with hq hq2
      · rcases hq with rfl | rfl <;> rcases hz with rfl | rfl | rfl
        · exact sub (c := 1) (by ring) h1
        · exact sub (c := 2) (by ring) h2
        · exact sub (c := 4) (by ring) h4
        · exact sub (c := -2) (by ring) (neg_ne_zero.mpr h2)
        · exact sub (c := -1) (by ring) (neg_ne_zero.mpr h1)
        · exact sub (c := 1) (by ring) h1
      · subst hq2
        rcases hz with rfl | rfl | rfl
        · exact sub (c := 1) (by ring) h1
        · exact sub (c := 2) (by ring) h2
        · exact sub (c := 4) (by ring) h4
      · rcases hz with rfl | rfl | rfl
        · exact sub (c := 1 - q) (by ring)
            fun h => hq (Or.inl (by linear_combination -h))
        · exact sub (c := 2 - q) (by ring) fun h => hq2 (by linear_combination -h)
        · exact sub (c := 4 - q) (by ring)
            fun h => hq (Or.inr (by linear_combination -h))
  have decQ_row1 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z ≠ 0) → (z ≠ 1) → (z ≠ 3) → decQ r q ≠ label q (r + 1) z := by
    intro r q z hz0 hz1 hz3
    cases q with
    | none =>
      refine sub (c := -1) ?_ (neg_ne_zero.mpr h1)
      simp only [decQ, label]; ring
    | some q =>
      simp only [decQ, label]
      split_ifs
      · exact sub (c := z - 1) (by ring) (sub_ne_zero.mpr hz1)
      · exact sub (c := z - 3) (by ring) (sub_ne_zero.mpr hz3)
      · exact sub (c := z) (by ring) hz0
  have decQ_row2 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z = 0 ∨ z = 2 ∨ z = 3) → decQ r q ≠ label q (r + 2) z := by
    intro r q z hz
    cases q with
    | none =>
      refine sub (c := -2) ?_ (neg_ne_zero.mpr h2)
      simp only [decQ, label]; ring
    | some q =>
      simp only [decQ, label]
      split_ifs with hq hq2
      · rcases hq with rfl | rfl <;> rcases hz with rfl | rfl | rfl
        · exact sub (c := -1) (by ring) (neg_ne_zero.mpr h1)
        · exact sub (c := 1) (by ring) h1
        · exact sub (c := 2) (by ring) h2
        · exact sub (c := -4) (by ring) (neg_ne_zero.mpr h4)
        · exact sub (c := -2) (by ring) (neg_ne_zero.mpr h2)
        · exact sub (c := -1) (by ring) (neg_ne_zero.mpr h1)
      · subst hq2
        rcases hz with rfl | rfl | rfl
        · exact sub (c := -5) (by ring) (neg_ne_zero.mpr h5)
        · exact sub (c := -3) (by ring) (neg_ne_zero.mpr h3)
        · exact sub (c := -2) (by ring) (neg_ne_zero.mpr h2)
      · rcases hz with rfl | rfl | rfl
        · exact sub (c := -q) (by ring) (neg_ne_zero.mpr fun h => hq (Or.inl h))
        · exact sub (c := 2 - q) (by ring) fun h => hq2 (by linear_combination -h)
        · exact sub (c := 3 - q) (by ring)
            fun h => hq (Or.inr (by linear_combination -h))
  have decR_row0 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z = -1 ∨ z = -2 ∨ z = -3) → decR r q ≠ label q r z := by
    intro r q z hz
    cases q with
    | none =>
      refine sub (c := 1) ?_ h1
      simp only [decR, label]; ring
    | some q =>
      simp only [decR, label]
      split_ifs with hq
      · rcases hq with hq | hq | hq <;> rcases hz with rfl | rfl | rfl
        · exact sub (c := -3) (by linear_combination hq) (neg_ne_zero.mpr h3)
        · exact sub (c := -4) (by linear_combination hq) (neg_ne_zero.mpr h4)
        · exact sub (c := -5) (by linear_combination hq) (neg_ne_zero.mpr h5)
        · exact sub (c := -2) (by linear_combination hq) (neg_ne_zero.mpr h2)
        · exact sub (c := -3) (by linear_combination hq) (neg_ne_zero.mpr h3)
        · exact sub (c := -4) (by linear_combination hq) (neg_ne_zero.mpr h4)
        · exact sub (c := -1) (by linear_combination hq) (neg_ne_zero.mpr h1)
        · exact sub (c := -2) (by linear_combination hq) (neg_ne_zero.mpr h2)
        · exact sub (c := -3) (by linear_combination hq) (neg_ne_zero.mpr h3)
      · rcases hz with rfl | rfl | rfl
        · exact sub (c := 2 * q - 1) (by ring)
            fun h => hq (Or.inl (by linear_combination h))
        · exact sub (c := 2 * q - 2) (by ring)
            fun h => hq (Or.inr (Or.inl (by linear_combination h)))
        · exact sub (c := 2 * q - 3) (by ring)
            fun h => hq (Or.inr (Or.inr (by linear_combination h)))
  have decR_row2 : ∀ (r : ZMod d) (q : Option (ZMod d)) (z : ZMod d),
      (z ≠ 0) → (z ≠ 3) → decR r q ≠ label q (r + 2) z := by
    intro r q z hz0 hz3
    cases q with
    | none =>
      refine sub (c := -1) ?_ (neg_ne_zero.mpr h1)
      simp only [decR, label]; ring
    | some q =>
      simp only [decR, label]
      split_ifs
      · exact sub (c := z - 3) (by ring) (sub_ne_zero.mpr hz3)
      · exact sub (c := z) (by ring) hz0
  -- values of the row index after a shift
  have hval1 : (1 : ZMod d).val = 1 := by rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  have hval2 : (2 : ZMod d).val = 2 := by
    rw [show (2 : ZMod d) = ((2 : ℕ) : ZMod d) by norm_cast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
  have hv := ZMod.val_lt x
  unfold enc
  by_cases hp : paired d x.val
  · rw [if_pos hp]
    by_cases hev : x.val % 2 = 0
    · rw [if_pos hev]
      split_ifs with hz
      · have hdec : dec d x q = decA x q := by simp only [dec]; rw [if_pos hp, if_pos hev]
        rw [hdec]; exact decA_row0 x q z hz
      · have hx1 : (x + 1).val = x.val + 1 := by
          rw [ZMod.val_add_of_lt (by rw [hval1]; omega), hval1]
        have hdec : dec d (x + 1) q = decB x q := by
          simp only [dec]
          rw [if_pos (by rw [hx1]; omega), if_neg (by rw [hx1]; omega), add_sub_cancel_right]
        rw [hdec]; exact decB_row0 x q z (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
    · rw [if_neg hev]
      split_ifs with hz
      · have hdec : dec d x q = decB (x - 1) q := by simp only [dec]; rw [if_pos hp, if_neg hev]
        rw [hdec]
        have h := decB_row1 (x - 1) q z hz
        rwa [sub_add_cancel] at h
      · have hx1 : (x - 1).val = x.val - 1 := by
          rw [ZMod.val_sub (by rw [hval1]; omega), hval1]
        have hdec : dec d (x - 1) q = decA (x - 1) q := by
          simp only [dec]
          rw [if_pos (by rw [hx1]; omega), if_pos (by rw [hx1]; omega)]
        rw [hdec]
        have h := decA_row1 (x - 1) q z (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
        rwa [sub_add_cancel] at h
  · rw [if_neg hp]
    by_cases h3d : x.val + 3 = d
    · rw [if_pos h3d]
      split_ifs with hz
      · have hx2 : (x + 2).val = x.val + 2 := by
          rw [ZMod.val_add_of_lt (by rw [hval2]; omega), hval2]
        have hdec : dec d (x + 2) q = decR x q := by
          simp only [dec]
          rw [if_neg (by rw [hx2]; omega), if_neg (by rw [hx2]; omega),
            if_neg (by rw [hx2]; omega), add_sub_cancel_right]
        rw [hdec]; exact decR_row0 x q z hz
      · have hdec : dec d x q = decP x q := by simp only [dec]; rw [if_neg hp, if_pos h3d]
        rw [hdec]
        exact decP_row0 x q z (fun h => hz (Or.inl h)) (fun h => hz (Or.inr (Or.inl h)))
          (fun h => hz (Or.inr (Or.inr h)))
    · rw [if_neg h3d]
      by_cases h2d : x.val + 2 = d
      · rw [if_pos h2d]
        split_ifs with hz
        · have hx1 : (x - 1).val = x.val - 1 := by
            rw [ZMod.val_sub (by rw [hval1]; omega), hval1]
          have hdec : dec d (x - 1) q = decP (x - 1) q := by
            simp only [dec]
            rw [if_neg (by rw [hx1]; omega), if_pos (by rw [hx1]; omega)]
          rw [hdec]
          have h := decP_row1 (x - 1) q z hz
          rwa [sub_add_cancel] at h
        · have hdec : dec d x q = decQ (x - 1) q := by
            simp only [dec]; rw [if_neg hp, if_neg h3d, if_pos h2d]
          rw [hdec]
          have h := decQ_row1 (x - 1) q z (fun h => hz (Or.inl h)) (fun h => hz (Or.inr (Or.inl h)))
            (fun h => hz (Or.inr (Or.inr h)))
          rwa [sub_add_cancel] at h
      · rw [if_neg h2d]
        split_ifs with hz
        · have hx1 : (x - 1).val = x.val - 1 := by
            rw [ZMod.val_sub (by rw [hval1]; omega), hval1]
          have hdec : dec d (x - 1) q = decQ (x - 1 - 1) q := by
            simp only [dec]
            rw [if_neg (by rw [hx1]; omega), if_neg (by rw [hx1]; omega),
              if_pos (by rw [hx1]; omega)]
          rw [hdec]
          have h := decQ_row2 (x - 1 - 1) q z hz
          rwa [show x - 1 - 1 + 2 = x by ring] at h
        · have hdec : dec d x q = decR (x - 2) q := by
            simp only [dec]; rw [if_neg hp, if_neg h3d, if_neg h2d]
          rw [hdec]
          have h := decR_row2 (x - 2) q z (fun h => hz (Or.inl h)) (fun h => hz (Or.inr (Or.inr h)))
          rwa [sub_add_cancel] at h

/-- The classical value of the Torpedo Game is `1` for every `d ≥ 5`. -/
theorem result : claim := by
  intro d _ hd
  obtain ⟨E, D, hED⟩ := exists_perfect d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK : ((d : ℝ) ^ 2 * (d + 1)) ≠ 0 := by positivity
  have hcard : ∑ _x : ZMod d, ∑ _z : ZMod d, ∑ _q : Option (ZMod d), (1 : ℝ) =
      (d : ℝ) ^ 2 * (d + 1) := by
    simp only [sum_const, card_univ, ZMod.card, Fintype.card_option, nsmul_eq_mul, mul_one]
    push_cast; ring
  constructor
  · refine ⟨1, fun _ => 1, fun _ x z j => if j = E x z then 1 else 0,
      fun _ j q c => if c = D j q then 1 else 0, ⟨fun _ => zero_le_one, by simp⟩,
      fun _ x z => ⟨fun j => by by_cases h : j = E x z <;> simp [h], by simp⟩,
      fun _ j q => ⟨fun c => by by_cases h : c = D j q <;> simp [h], by simp⟩, ?_⟩
    have hin : ∀ x z q, (∑ _l : Fin 1, (1 : ℝ) * ∑ j : ZMod d, (if j = E x z then (1 : ℝ) else 0) *
        ∑ c ∈ univ.filter (fun c => c ≠ label q x z), (if c = D j q then (1 : ℝ) else 0)) = 1 := by
      intro x z q
      simp only [one_mul, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true, mem_filter, true_and]
      rw [if_pos (hED x z q)]
      simp
    simp only [winProb, hin, hcard]
    field_simp
  · rintro v ⟨n, μ, e, f, hμ, he, hf, rfl⟩
    have hin : ∀ x z q, ∑ l, μ l * ∑ j, e l x z j *
        ∑ c ∈ univ.filter (fun c => c ≠ label q x z), f l j q c ≤ 1 := by
      intro x z q
      calc _ ≤ ∑ l, μ l * ∑ j, e l x z j * 1 := by
            gcongr with l _ j _
            · exact hμ.1 l
            · exact (he l x z).1 j
            · calc _ ≤ ∑ c, f l j q c :=
                    sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                      (fun c _ _ => (hf l j q).1 c)
                _ = 1 := (hf l j q).2
        _ = 1 := by simp [(he _ x z).2, hμ.2]
    calc winProb μ e f ≤ 1 / ((d : ℝ) ^ 2 * (d + 1)) *
          ∑ _x : ZMod d, ∑ _z : ZMod d, ∑ _q : Option (ZMod d), (1 : ℝ) := by
          unfold winProb
          gcongr with x _ z _ q _
          exact hin x z q
      _ = 1 := by rw [hcard]; field_simp

end D5.S3.Quantum.Information.TorpedoGamePerfectClassical
