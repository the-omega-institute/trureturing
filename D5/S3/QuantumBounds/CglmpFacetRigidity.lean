/- GID: D5/S3/QuantumBounds/CglmpFacetRigidity
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/CglmpFacetRigidity
   mirror-E: none(waiver:non-computational-content)
   anchors: []
   utility: none
   digest: CGLMP saturation determines every bipartite local functional up to a scalar. -/
/-
proof_shape: bipartite_rigidity, cycle_rigidity: content.
proof_shape: val_neg_sub_one: bind-only (consumers: J2_formula, cycle_rigidity,
  MerminCglmpFacet.neg_pred_pair_val).
proof_shape: val_sub_wrap, J2_formula: bind-only (consumer: cycle_rigidity).
proof_shape: sat_of_dist_eq: bind-only (consumers: short_sat, cycle_rigidity).
proof_shape: short_sat: bind-only (consumer: cycle_rigidity).
proof_shape: J2_relabelled: bind-only (consumer: bipartite_rigidity).
escape_witness: cycle_rigidity constructs the short-arc potential and wrap coefficient.
admission_basis: escape-witness
Utility: uniform algebraic rigidity, without enumeration, checker, numeric reduction or instance.
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.QuantumBounds.CglmpFacetRigidity

variable {K : ℕ} [NeZero K]

private def J2 (a b c d : ZMod K) : ℕ :=
  (a - b).val + (b - c).val + (c - d).val + (d - a - 1).val

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license; the full source license and locator are retained in
Library/QuantumBounds/blore2026cglmp.md.
The residue lemma below is reused from that source with its proof unchanged.
When the pinned Mathlib supplies this equivalent lemma, use that owner directly.
-/
lemma val_neg_sub_one {d : ℕ} [NeZero d] (r : ZMod d) :
    (-r - 1 : ZMod d).val = d - 1 - r.val := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hlt : r.val < d := ZMod.val_lt r
  have hle : r.val ≤ d - 1 := by omega
  have hlt2 : d - 1 - r.val < d := by omega
  have hcast : (-r - 1 : ZMod d) = ((d - 1 - r.val : ℕ) : ZMod d) := by
    rw [Nat.cast_sub hle, Nat.cast_sub hd1, ZMod.natCast_self, Nat.cast_one,
      ZMod.natCast_zmod_val]
    ring
  rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt2]

/-- proof_shape: bind-only; consumer: cycle_rigidity. -/
private theorem val_sub_wrap (x y : ZMod K) :
    ((x - y).val : ℝ) = (x.val : ℝ) - y.val + (K : ℝ) * (if x.val < y.val then 1 else 0) := by
  by_cases h : x.val < y.val
  · have hy : y ≠ 0 := by intro hz; simp [hz] at h
    have : NeZero y := ⟨hy⟩
    have hv : (x - y).val = x.val + (K - y.val) := by
      rw [sub_eq_add_neg, ZMod.val_add, ZMod.val_neg_of_ne_zero]
      exact Nat.mod_eq_of_lt (by have := ZMod.val_lt y; omega)
    rw [hv, if_pos h]
    push_cast
    have := ZMod.val_lt y
    rw [Nat.cast_sub (by omega)]
    ring
  · rw [ZMod.val_sub (by omega), if_neg h, Nat.cast_sub (by omega)]
    ring

/-- proof_shape: bind-only; consumer: sat_of_dist_eq, cycle_rigidity. -/
private theorem J2_formula (a b c d : ZMod K) :
    (J2 a b c d : ℝ) - ((K : ℝ) - 1) =
      ((a - b).val : ℝ) + (b - c).val + (c - d).val - (a - d).val := by
  have hid : d - a - 1 = -(a - d) - 1 := by ring
  have hv := val_neg_sub_one (a - d)
  have hab := ZMod.val_lt (a - d)
  have hk : 0 < K := NeZero.pos K
  simp only [J2, hid, hv, Nat.cast_add]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  ring

end D5.S3.QuantumBounds.CglmpFacetRigidity

namespace D5.S3.QuantumBounds.CglmpFacetRigidity
variable {K : ℕ} [NeZero K]

/-- proof_shape: bind-only; consumer: short_sat, cycle_rigidity. -/
private theorem sat_of_dist_eq (a b c d : ZMod K)
    (h : (a - b).val + (b - c).val + (c - d).val = (a - d).val) :
    J2 a b c d = K - 1 := by
  have hk : 0 < K := NeZero.pos K
  have hf := J2_formula a b c d
  have hr : ((a - b).val : ℝ) + (b - c).val + (c - d).val = ((a - d).val : ℝ) := by
    exact_mod_cast h
  have he : (J2 a b c d : ℝ) = ((K - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    linarith
  exact_mod_cast he

/-- proof_shape: bind-only; consumer: cycle_rigidity. -/
private theorem short_sat (x y z : ZMod K) (h : (x - y).val + (y - z).val < K) :
    J2 x y z z = K - 1 := by
  apply sat_of_dist_eq
  have he : (x - y) + (y - z) = x - z := by ring
  have hv := ZMod.val_add_of_lt h
  rw [he] at hv
  simpa using hv.symm

private def CycleLocal (U V W T : ZMod K → ZMod K → ℝ) (a b c d : ZMod K) : ℝ :=
  U a b + V b c + W c d + T d a

/-- proof_shape: content; consumer: bipartite_rigidity. -/
private theorem cycle_rigidity (U V W T : ZMod K → ZMod K → ℝ)
    (hs : ∀ a b c d, J2 a b c d = K - 1 → CycleLocal U V W T a b c d = 0) :
    ∃ lam : ℝ, ∀ a b c d,
      CycleLocal U V W T a b c d = lam * ((J2 a b c d : ℝ) - ((K : ℝ) - 1)) := by
  have h1 (x y : ZMod K) : U x x + V x x + W x y + T y x = 0 := by
    apply hs
    apply sat_of_dist_eq
    simp
  have h2 (x y : ZMod K) : U x x + V x y + W y y + T y x = 0 := by
    apply hs
    apply sat_of_dist_eq
    simp
  have h3 (x y : ZMod K) : U x y + V y y + W y y + T y x = 0 := by
    apply hs
    apply sat_of_dist_eq
    simp
  let H : ZMod K → ZMod K → ℝ := fun x y => W x y - W y y
  have hd (x : ZMod K) : H x x = 0 := by simp [H]
  have rep (a b c d : ZMod K) :
      CycleLocal U V W T a b c d = H a b + H b c + H c d - H a d := by
    have ht := h1 a d
    have hv := h2 b c
    have ht' := h1 b c
    have hu := h3 a b
    have ht'' := h1 a b
    dsimp [CycleLocal, H]
    linarith only [ht, hv, ht', hu, ht'']
  have short (x y z : ZMod K) (h : (x - y).val + (y - z).val < K) :
      H x y + H y z = H x z := by
    have hg := hs x y z z (short_sat x y z h)
    rw [rep, hd] at hg
    linarith
  let P : ZMod K → ℝ := fun x => H x 0
  let m : ZMod K := -1
  let S : ℝ := H 0 m + P m
  have hm : m.val = K - 1 := by
    dsimp [m]
    simpa using val_neg_sub_one (0 : ZMod K)
  have hK : 0 < K := NeZero.pos K
  have down (x y : ZMod K) (h : y.val ≤ x.val) : H x y = P x - P y := by
    have hs' := short x y 0 (by
      rw [ZMod.val_sub h]
      simp only [sub_zero]
      have hx := ZMod.val_lt x
      omega)
    dsimp [P]
    linarith
  have tozero (y : ZMod K) (h : 0 < y.val) : H 0 y = S - P y := by
    have hy := ZMod.val_lt y
    have hym : y.val ≤ m.val := by omega
    have h0m : (0 - m).val = 1 := by
      have hm0 : m ≠ 0 := by
        intro hh
        have hv : m.val = 0 := by rw [hh]; simp
        -- K=1 is excluded by h in this use.
        omega
      rw [zero_sub, ZMod.neg_val, if_neg hm0, hm]
      omega
    have hs' := short 0 m y (by rw [h0m, ZMod.val_sub hym]; omega)
    rw [down m y hym] at hs'
    dsimp [S]
    linarith
  have form (x y : ZMod K) :
      H x y = P x - P y + S * (if x.val < y.val then 1 else 0) := by
    by_cases h : x.val < y.val
    · have hy : 0 < y.val := by omega
      have h0y : (0 - y).val = K - y.val := by
        rw [zero_sub, ZMod.neg_val, if_neg (by
          intro hz; rw [hz, ZMod.val_zero] at hy; omega)]
      have hs' := short x 0 y (by
        simp only [sub_zero]
        rw [h0y]
        have := ZMod.val_lt y
        omega)
      rw [tozero y hy] at hs'
      rw [if_pos h]
      dsimp [P] at *
      linarith
    · rw [if_neg h, mul_zero, add_zero]
      exact down x y (by omega)
  refine ⟨S / K, ?_⟩
  intro a b c d
  rw [rep, form a b, form b c, form c d, form a d]
  rw [J2_formula, val_sub_wrap a b, val_sub_wrap b c, val_sub_wrap c d,
    val_sub_wrap a d]
  have hkR : (K : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K)
  field_simp
  ring

def BipLocal (f : Fin 2 → Fin 2 → ZMod K → ZMod K → ℝ)
    (a A b B : ZMod K) : ℝ :=
  ∑ x : Fin 2, ∑ y : Fin 2, f x y (if x = 0 then a else A) (if y = 0 then b else B)

def J2AB (a A b B : ZMod K) : ℕ :=
  (A - b).val + (a + B).val + (-a + b).val + (-A - B - 1).val

omit [NeZero K] in
/-- proof_shape: bind-only; consumer: bipartite_rigidity. -/
private theorem J2_relabelled (a A b B : ZMod K) : J2AB a A b B = J2 A b a (-B) := by
  have h1 : a - (-B) = a + B := by ring
  have h2 : b - a = -a + b := by ring
  have h3 : -B - A - 1 = -A - B - 1 := by ring
  simp only [J2AB, J2, h1, h2, h3]
  omega

theorem bipartite_rigidity (f : Fin 2 → Fin 2 → ZMod K → ZMod K → ℝ)
    (hs : ∀ a A b B, J2AB a A b B = K - 1 → BipLocal f a A b B = 0) :
    ∃ lam : ℝ, ∀ a A b B,
      BipLocal f a A b B = lam * ((J2AB a A b B : ℝ) - ((K : ℝ) - 1)) := by
  let U := f 1 0
  let V : ZMod K → ZMod K → ℝ := fun b a => f 0 0 a b
  let W : ZMod K → ZMod K → ℝ := fun a d => f 0 1 a (-d)
  let T : ZMod K → ZMod K → ℝ := fun d A => f 1 1 A (-d)
  have hrep (a b c d : ZMod K) :
      CycleLocal U V W T a b c d = BipLocal f c a b (-d) := by
    simp [CycleLocal, U, V, W, T, BipLocal, Fin.sum_univ_two]
    ring
  obtain ⟨lam, hlam⟩ := cycle_rigidity U V W T (by
    intro a b c d hd
    rw [hrep]
    apply hs
    rw [J2_relabelled, neg_neg]
    exact hd)
  refine ⟨lam, ?_⟩
  intro a A b B
  have h := hlam A b a (-B)
  rw [hrep, neg_neg, ← J2_relabelled] at h
  exact h

end D5.S3.QuantumBounds.CglmpFacetRigidity
