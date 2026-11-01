/- GID: D5/S3/Geometry/Polygons/PolygonEarSlideGeometry
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarSlideGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual polygon carrier and cyclic crossing transport for the local vertex exchange. -/

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/cluster-algebras-polygon-third-party.md.
Authors: Ashvin A. Swaminathan.

The polygon carrier below is a minimal adaptation of the definitions and the
crossing endpoint lemma from AxiomMath/ClusterAlgebras, revision
a9174706bce3bcb0fa342b4614f98ef2acb7f91c.  This repository's pinned Mathlib
supplies the finite-set and symmetric-square operations used by the adaptation.
The cyclic translation adaptations are owned by `PolygonEarSlide.lean`.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Circular.ZMod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.Geometry.Polygons.PolygonEarSlide

namespace Carrier

variable {n : ℕ} [NeZero n]

instance instDecidableSbtw (a b c : ZMod n) : Decidable (sbtw a b c) := by
  match n, ‹NeZero n›, a, b, c with
  | (k + 1), _, a, b, c => exact decidable_of_iff _ Fin.sbtw_iff.symm

def IsSegment (e : Sym2 (ZMod n)) : Prop := ¬e.IsDiag

def IsSide (e : Sym2 (ZMod n)) : Prop := ∃ i : ZMod n, e = s(i, i + 1)

def IsDiagonal (e : Sym2 (ZMod n)) : Prop := IsSegment e ∧ ¬IsSide e

instance instDecidablePredIsSegment : DecidablePred (IsSegment (n := n)) :=
  fun _ => by unfold IsSegment; infer_instance

instance instDecidablePredIsSide : DecidablePred (IsSide (n := n)) :=
  fun _ => by unfold IsSide; infer_instance

instance instDecidablePredIsDiagonal : DecidablePred (IsDiagonal (n := n)) :=
  fun _ => by unfold IsDiagonal; infer_instance

def Cross (e f : Sym2 (ZMod n)) : Prop :=
  ∃ a b c d : ZMod n, e = s(a, b) ∧ f = s(c, d) ∧ sbtw a c b ∧ sbtw b d a

instance instDecidableCross (e f : Sym2 (ZMod n)) : Decidable (Cross e f) := by
  unfold Cross
  infer_instance

structure IsTriangulation (T : Finset (Sym2 (ZMod n))) : Prop where
  isDiagonal : ∀ e ∈ T, IsDiagonal e
  noncrossing : ∀ e ∈ T, ∀ f ∈ T, ¬Cross e f
  maximal : ∀ e, IsDiagonal e → e ∉ T → ∃ f ∈ T, Cross e f

private theorem sbtw_rotate_four {k : ℕ} {a b c d : Fin k}
    (h1 : sbtw a c b) (h2 : sbtw b d a) :
    sbtw c b d ∧ sbtw d a c := by
  rw [Fin.sbtw_iff] at h1 h2
  refine ⟨?_, ?_⟩ <;> rw [Fin.sbtw_iff] <;>
    simp only [Fin.lt_def] at h1 h2 ⊢ <;> omega

theorem cross_symm {e f : Sym2 (ZMod n)} (h : Cross e f) : Cross f e := by
  obtain ⟨a, b, c, d, rfl, rfl, h1, h2⟩ := h
  refine ⟨c, d, b, a, rfl, Sym2.eq_swap, ?_⟩
  match n, ‹NeZero n›, a, b, c, d, h1, h2 with
  | (k + 1), _, a, b, c, d, h1, h2 =>
      exact sbtw_rotate_four h1 h2

theorem not_cross_self (e : Sym2 (ZMod n)) : ¬Cross e e := by
  rintro ⟨a, b, c, d, he, hfe, hab, hcd⟩
  rw [he] at hfe
  rw [Sym2.eq_iff] at hfe
  rcases hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst c
    subst d
    exact sbtw_irrefl_left hab
  · subst d
    subst c
    exact sbtw_irrefl_right hcd

end Carrier

open Carrier


namespace Actual

variable {n : ℕ} [NeZero n]

lemma sbtw_val (hn : 6 ≤ n) (a b c : ZMod n) :
    sbtw a b c ↔ (a.val < b.val ∧ b.val < c.val) ∨
      (b.val < c.val ∧ c.val < a.val) ∨ (c.val < a.val ∧ a.val < b.val) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact Fin.sbtw_iff

def vertexSwap (n : ℕ) [NeZero n] : Equiv.Perm (ZMod n) :=
  Equiv.swap (1 : ZMod n) (2 : ZMod n)

def chordSwap (e : Sym2 (ZMod n)) : Sym2 (ZMod n) := e.map (vertexSwap n)

lemma vertexSwap_val (hn : 6 ≤ n) (x : ZMod n) :
    (vertexSwap n x).val = if x = 1 then 2 else if x = 2 then 1 else x.val := by
  have h1 : (1 : ZMod n).val = 1 := by
    simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
  have h2 : (2 : ZMod n).val = 2 := by
    simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
  rcases eq_or_ne x 1 with rfl | hx1
  · simp [vertexSwap, h2]
  rcases eq_or_ne x 2 with rfl | hx2
  · have h21 : (2 : ZMod n) ≠ 1 := by
      intro h
      have hv := congrArg ZMod.val h
      simp [h1, h2] at hv
    simp [vertexSwap, h1, h21]
  · have hs := Equiv.swap_apply_of_ne_of_ne hx1 hx2
    simp [vertexSwap, hx1, hx2, hs]


lemma vertexSwap_val_of_ne_two (hn : 6 ≤ n) (x : ZMod n) (hx : x ≠ 2) :
    (vertexSwap n x).val = if x = 1 then 2 else x.val := by
  rw [vertexSwap_val hn x]
  simp [hx]

lemma sbtw_swap_of_avoid_two (hn : 6 ≤ n) {a b c : ZMod n}
    (ha : a ≠ 2) (hb : b ≠ 2) (hc : c ≠ 2) :
    sbtw (vertexSwap n a) (vertexSwap n b) (vertexSwap n c) ↔ sbtw a b c := by
  rw [sbtw_val hn, sbtw_val hn]
  rw [vertexSwap_val_of_ne_two hn a ha, vertexSwap_val_of_ne_two hn b hb,
    vertexSwap_val_of_ne_two hn c hc]
  have h1 : (1 : ZMod n).val = 1 := by
    have h : 1 < n := by omega
    simpa using (ZMod.val_natCast_of_lt h)
  have h2 : (2 : ZMod n).val = 2 := by
    have h : 2 < n := by omega
    simpa using (ZMod.val_natCast_of_lt h)
  have h0 : (0 : ZMod n).val = 0 := ZMod.val_zero
  have h01 : (0 : ZMod n) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    simp [h0, h1] at hv
  have h10 : (1 : ZMod n) ≠ 0 := by
    intro h
    exact h01 h.symm
  have hvalone (x : ZMod n) : x.val = 1 ↔ x = 1 := by
    constructor
    · intro hx
      apply ZMod.val_injective n
      simpa [hx, h1]
    · intro hx
      simpa [hx, h1]
  have hvalzero (x : ZMod n) : x.val = 0 ↔ x = 0 := ZMod.val_eq_zero x
  have hvaltwo (x : ZMod n) : x.val = 2 ↔ x = 2 := by
    constructor
    · intro hx
      apply ZMod.val_injective n
      simpa [hx, h2]
    · intro hx
      simpa [hx, h2]
  have hvalleone (x : ZMod n) : x.val ≤ 1 ↔ x = 0 ∨ x = 1 := by
    constructor
    · intro hx
      have hcases : x.val = 0 ∨ x.val = 1 := by omega
      rcases hcases with h | h
      · exact Or.inl (hvalzero x |>.mp h)
      · exact Or.inr (hvalone x |>.mp h)
    · rintro (rfl | rfl) <;> simp [h1]
  have hav2 : a.val ≠ 2 := fun h => ha ((hvaltwo a).mp h)
  have hbv2 : b.val ≠ 2 := fun h => hb ((hvaltwo b).mp h)
  have hcv2 : c.val ≠ 2 := fun h => hc ((hvaltwo c).mp h)
  by_cases ha1 : a = 1 <;> by_cases hb1 : b = 1 <;> by_cases hc1 : c = 1 <;>
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> by_cases hc0 : c = 0 <;>
      skip
  all_goals try have hav1eq : a.val = 1 := (hvalone a).mpr ha1
  all_goals try have hbv1eq : b.val = 1 := (hvalone b).mpr hb1
  all_goals try have hcv1eq : c.val = 1 := (hvalone c).mpr hc1
  all_goals try have hav1ne : a.val ≠ 1 := by simpa [hvalone] using ha1
  all_goals try have hbv1ne : b.val ≠ 1 := by simpa [hvalone] using hb1
  all_goals try have hcv1ne : c.val ≠ 1 := by simpa [hvalone] using hc1
  all_goals simp [ha, hb, hc, ha1, hb1, hc1, ha0, hb0, hc0, h01, h10, h0, h1, h2,
    hvalzero, hvaltwo, hvalleone] <;> omega

@[simp] theorem vertexSwap_apply_one (hn : 6 ≤ n) : vertexSwap n 1 = 2 := by
  simp [vertexSwap]

@[simp] theorem vertexSwap_apply_two (hn : 6 ≤ n) : vertexSwap n 2 = 1 := by
  simp [vertexSwap]

@[simp] theorem vertexSwap_apply_apply (x : ZMod n) : vertexSwap n (vertexSwap n x) = x := by
  simp [vertexSwap]

@[simp] theorem chordSwap_involutive (e : Sym2 (ZMod n)) :
    chordSwap (chordSwap e) = e := by
  induction e using Sym2.ind with | _ a b => simp [chordSwap, vertexSwap_apply_apply]

@[simp] theorem chordSwap_mk (a b : ZMod n) :
    chordSwap s(a, b) = s(vertexSwap n a, vertexSwap n b) := by
  simp [chordSwap]

end Actual


namespace Actual

variable {n : ℕ} [NeZero n]

def ear (i : ZMod n) : Sym2 (ZMod n) := s(i - 1, i + 1)

def e₀ : Sym2 (ZMod n) := ear 0
def sEar : Sym2 (ZMod n) := ear 1
def tEar : Sym2 (ZMod n) := ear 2
def uEar : Sym2 (ZMod n) := ear 3

@[simp] theorem ear_zero : ear (0 : ZMod n) = s(-1, 1) := by
  change s((0 : ZMod n) - 1, (0 : ZMod n) + 1) = s(-1, 1)
  rw [zero_sub, zero_add]
@[simp] theorem ear_one : ear (1 : ZMod n) = s(0, 2) := by
  change s((1 : ZMod n) - 1, (1 : ZMod n) + 1) = s(0, 2)
  rw [sub_self, show (1 : ZMod n) + 1 = 2 by ring]
@[simp] theorem ear_two : ear (2 : ZMod n) = s(1, 3) := by
  change s((2 : ZMod n) - 1, (2 : ZMod n) + 1) = s(1, 3)
  rw [show (2 : ZMod n) - 1 = 1 by ring, show (2 : ZMod n) + 1 = 3 by ring]
@[simp] theorem ear_three : ear (3 : ZMod n) = s(2, 4) := by
  change s((3 : ZMod n) - 1, (3 : ZMod n) + 1) = s(2, 4)
  rw [show (3 : ZMod n) - 1 = 2 by ring, show (3 : ZMod n) + 1 = 4 by ring]

lemma val_neg_one_of_ge (hn : 1 ≤ n) : (-1 : ZMod n).val = n - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simpa using (ZMod.val_neg_one k)

lemma sbtw_const (hn : 6 ≤ n) :
    sbtw (1 : ZMod n) 2 3 ∧ sbtw (3 : ZMod n) 4 1 ∧
      sbtw (3 : ZMod n) 0 1 ∧ sbtw (0 : ZMod n) 1 2 ∧
      sbtw (2 : ZMod n) (-1 : ZMod n) 0 := by
  rw [sbtw_val hn, sbtw_val hn, sbtw_val hn, sbtw_val hn, sbtw_val hn]
  have h0 : (0 : ZMod n).val = 0 := ZMod.val_zero
  have h1 : (1 : ZMod n).val = 1 := by
    simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
  have h2 : (2 : ZMod n).val = 2 := by
    simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
  have h3 : (3 : ZMod n).val = 3 := by
    simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
  have h4 : (4 : ZMod n).val = 4 := by
    simpa using (ZMod.val_natCast_of_lt (show 4 < n by omega))
  have hm : (-1 : ZMod n).val = n - 1 := val_neg_one_of_ge (by omega)
  simp only [h0, h1, h2, h3, h4, hm]
  omega

lemma local_crossings (hn : 6 ≤ n) :
    Cross (tEar (n := n)) (sEar (n := n)) ∧
      Cross (tEar (n := n)) (uEar (n := n)) ∧
      Cross (sEar (n := n)) (e₀ (n := n)) := by
  obtain ⟨h123, h341, h301, h012, h2m0⟩ := sbtw_const hn
  refine ⟨?_, ?_, ?_⟩
  · simpa only [tEar, sEar, ear_two, ear_one] using
      (show Cross s(1, 3) s(0, 2) from ⟨1, 3, 2, 0, rfl, Sym2.eq_swap, h123, h301⟩)
  · simpa only [tEar, uEar, ear_two, ear_three] using
      (show Cross s(1, 3) s(2, 4) from ⟨1, 3, 2, 4, rfl, rfl, h123, h341⟩)
  · simpa only [sEar, e₀, ear_one, ear_zero] using
      (show Cross s(0, 2) s(-1, 1) from ⟨0, 2, 1, -1, rfl, Sym2.eq_swap, h012, h2m0⟩)

def AvoidTwo (e : Sym2 (ZMod n)) : Prop := ∀ x : ZMod n, e ≠ s(2, x)

lemma avoidTwo_mk_iff (a b : ZMod n) :
    AvoidTwo (s(a, b)) ↔ a ≠ 2 ∧ b ≠ 2 := by
  constructor
  · intro h
    constructor
    · intro ha
      exact h b (by simp [ha])
    · intro hb
      exact h a (by simp [hb, Sym2.eq_swap])
  · rintro ⟨ha, hb⟩ x he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨ha2, hbx⟩ | ⟨hax, hb2⟩
    · exact ha ha2
    · exact hb hb2

lemma cross_chordSwap_of_avoidTwo (hn : 6 ≤ n) {e f : Sym2 (ZMod n)}
    (he : AvoidTwo e) (hf : AvoidTwo f) :
    Cross (chordSwap e) (chordSwap f) ↔ Cross e f := by
  constructor
  · intro h
    obtain ⟨a, b, c, d, heq, hfeq, hab, hcd⟩ := h
    have heq' : e = s(vertexSwap n a, vertexSwap n b) := by
      calc
        e = chordSwap (chordSwap e) := by simp
        _ = chordSwap s(a, b) := congrArg chordSwap heq
        _ = s(vertexSwap n a, vertexSwap n b) := by simp [chordSwap]
    have hfeq' : f = s(vertexSwap n c, vertexSwap n d) := by
      calc
        f = chordSwap (chordSwap f) := by simp
        _ = chordSwap s(c, d) := congrArg chordSwap hfeq
        _ = s(vertexSwap n c, vertexSwap n d) := by simp [chordSwap]
    have he' : AvoidTwo s(vertexSwap n a, vertexSwap n b) := heq'.symm ▸ he
    have hf' : AvoidTwo s(vertexSwap n c, vertexSwap n d) := hfeq'.symm ▸ hf
    have ha : vertexSwap n a ≠ 2 := (avoidTwo_mk_iff _ _).1 he' |>.1
    have hb : vertexSwap n b ≠ 2 := (avoidTwo_mk_iff _ _).1 he' |>.2
    have hc : vertexSwap n c ≠ 2 := (avoidTwo_mk_iff _ _).1 hf' |>.1
    have hd : vertexSwap n d ≠ 2 := (avoidTwo_mk_iff _ _).1 hf' |>.2
    refine ⟨vertexSwap n a, vertexSwap n b, vertexSwap n c, vertexSwap n d,
      heq', hfeq', ?_, ?_⟩
    · have hab' : sbtw (vertexSwap n (vertexSwap n a))
          (vertexSwap n (vertexSwap n c)) (vertexSwap n (vertexSwap n b)) := by
        simpa only [vertexSwap_apply_apply] using hab
      simpa only [vertexSwap_apply_apply] using
        (sbtw_swap_of_avoid_two hn ha hc hb).mp hab'
    · have hcd' : sbtw (vertexSwap n (vertexSwap n b))
          (vertexSwap n (vertexSwap n d)) (vertexSwap n (vertexSwap n a)) := by
        simpa only [vertexSwap_apply_apply] using hcd
      simpa only [vertexSwap_apply_apply] using
        (sbtw_swap_of_avoid_two hn hb hd ha).mp hcd'
  · intro h
    obtain ⟨a, b, c, d, heq, hfeq, hab, hcd⟩ := h
    have he' : AvoidTwo s(a, b) := heq ▸ he
    have hf' : AvoidTwo s(c, d) := hfeq ▸ hf
    have ha : a ≠ 2 := (avoidTwo_mk_iff _ _).1 he' |>.1
    have hb : b ≠ 2 := (avoidTwo_mk_iff _ _).1 he' |>.2
    have hc : c ≠ 2 := (avoidTwo_mk_iff _ _).1 hf' |>.1
    have hd : d ≠ 2 := (avoidTwo_mk_iff _ _).1 hf' |>.2
    refine ⟨vertexSwap n a, vertexSwap n b, vertexSwap n c, vertexSwap n d,
      ?_, ?_, ?_, ?_⟩
    · calc
        chordSwap e = chordSwap s(a, b) := congrArg chordSwap heq
        _ = s(vertexSwap n a, vertexSwap n b) := by simp [chordSwap]
    · calc
        chordSwap f = chordSwap s(c, d) := congrArg chordSwap hfeq
        _ = s(vertexSwap n c, vertexSwap n d) := by simp [chordSwap]
    · exact (sbtw_swap_of_avoid_two hn ha hc hb).mpr hab
    · exact (sbtw_swap_of_avoid_two hn hb hd ha).mpr hcd

lemma cross_incident_two (hn : 6 ≤ n) {x : ZMod n}
    (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    Cross s(2, x) (tEar (n := n)) := by
  have h0 : (0 : ZMod n).val = 0 := ZMod.val_zero
  have h1 : (1 : ZMod n).val = 1 := by
    simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
  have h2 : (2 : ZMod n).val = 2 := by
    simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
  have h3 : (3 : ZMod n).val = 3 := by
    simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
  have hxv : x.val < n := ZMod.val_lt x
  have hx0 : x.val = 0 ↔ x = 0 := ZMod.val_eq_zero x
  have hx1v : x.val ≠ 1 := by
    intro h
    apply hx1
    apply ZMod.val_injective n
    simpa [h, h1]
  have hx2v : x.val ≠ 2 := by
    intro h
    apply hx2
    apply ZMod.val_injective n
    simpa [h, h2]
  have hx3v : x.val ≠ 3 := by
    intro h
    apply hx3
    apply ZMod.val_injective n
    simpa [h, h3]
  rw [tEar, ear_two]
  by_cases hx0 : x = 0
  · subst x
    refine ⟨0, 2, 1, 3, Sym2.eq_swap, rfl, ?_, ?_⟩
    · rw [sbtw_val hn]
      simp [h0, h1, h2, h3]
    · rw [sbtw_val hn]
      simp [h0, h1, h2, h3]
  have hxv0 : x.val ≠ 0 := by
    intro h
    exact hx0 ((ZMod.val_eq_zero x).mp h)
  have hxvpos : 1 ≤ x.val := by omega
  have hxv4 : 4 ≤ x.val := by
    by_contra hlt
    have : x.val = 1 ∨ x.val = 2 ∨ x.val = 3 := by omega
    rcases this with h | h | h
    · exact hx1v h
    · exact hx2v h
    · exact hx3v h
  refine ⟨x, 2, 1, 3, ?_, rfl, ?_, ?_⟩
  · simp [Sym2.eq_swap]
  · rw [sbtw_val hn]
    right
    left
    omega
  · rw [sbtw_val hn]
    left
    omega

lemma cross_incident_one (hn : 6 ≤ n) {x : ZMod n}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx2 : x ≠ 2) :
    Cross s(1, x) (sEar (n := n)) := by
  have h0 : (0 : ZMod n).val = 0 := ZMod.val_zero
  have h1 : (1 : ZMod n).val = 1 := by
    simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
  have h2 : (2 : ZMod n).val = 2 := by
    simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
  have hxv : x.val < n := ZMod.val_lt x
  have hx0v : x.val ≠ 0 := by
    intro h
    exact hx0 ((ZMod.val_eq_zero x).mp h)
  have hx1v : x.val ≠ 1 := by
    intro h
    apply hx1
    apply ZMod.val_injective n
    simpa [h, h1]
  have hx2v : x.val ≠ 2 := by
    intro h
    apply hx2
    apply ZMod.val_injective n
    simpa [h, h2]
  have hxv3 : 3 ≤ x.val := by omega
  rw [sEar, ear_one]
  refine ⟨1, x, 2, 0, rfl, Sym2.eq_swap, ?_, ?_⟩
  · rw [sbtw_val hn]
    left
    omega
  · rw [sbtw_val hn]
    right
    left
    omega

lemma cross_s_implies_incident_one {e : Sym2 (ZMod n)} (hn : 6 ≤ n)
    (h : Cross (sEar (n := n)) e) : ∃ x : ZMod n, e = s(1, x) := by
  obtain ⟨a, b, c, d, he, hde, hab, hcd⟩ := h
  rw [sEar, ear_one] at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · subst a
    subst b
    have hc1 : c = 1 := by
      rw [sbtw_val hn] at hab
      have h0v : (0 : ZMod n).val = 0 := ZMod.val_zero
      have h1v : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      have h2v : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      have hcv : c.val < n := ZMod.val_lt c
      apply ZMod.val_injective n
      simp only [h0v, h1v, h2v] at hab ⊢
      omega
    exact ⟨d, by simpa [hde, hc1]⟩
  · subst a
    subst b
    have hd1 : d = 1 := by
      rw [sbtw_val hn] at hcd
      have h0v : (0 : ZMod n).val = 0 := ZMod.val_zero
      have h1v : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      have h2v : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      have hdv : d.val < n := ZMod.val_lt d
      apply ZMod.val_injective n
      simp only [h0v, h1v, h2v] at hcd ⊢
      omega
    exact ⟨c, by simpa [hde, hd1, Sym2.eq_swap]⟩

lemma cross_t_implies_incident_two {e : Sym2 (ZMod n)} (hn : 6 ≤ n)
    (h : Cross (tEar (n := n)) e) : ∃ x : ZMod n, e = s(2, x) := by
  obtain ⟨a, b, c, d, he, hde, hab, hcd⟩ := h
  rw [tEar, ear_two] at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · subst a
    subst b
    have hc2 : c = 2 := by
      rw [sbtw_val hn] at hab
      have h1v : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      have h2v : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      have h3v : (3 : ZMod n).val = 3 := by
        simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
      have hcv : c.val < n := ZMod.val_lt c
      apply ZMod.val_injective n
      simp only [h1v, h2v, h3v] at hab ⊢
      omega
    exact ⟨d, by simpa [hde, hc2]⟩
  · subst a
    subst b
    have hd2 : d = 2 := by
      rw [sbtw_val hn] at hcd
      have h1v : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      have h2v : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      have h3v : (3 : ZMod n).val = 3 := by
        simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
      have hdv : d.val < n := ZMod.val_lt d
      apply ZMod.val_injective n
      simp only [h1v, h2v, h3v] at hcd ⊢
      omega
    exact ⟨c, by simpa [hde, hd2, Sym2.eq_swap]⟩

lemma not_cross_t_of_avoidTwo {e : Sym2 (ZMod n)} (hn : 6 ≤ n)
    (he : AvoidTwo e) : ¬Cross e (tEar (n := n)) := by
  intro h
  obtain ⟨x, hx⟩ := cross_t_implies_incident_two hn (cross_symm h)
  rw [hx] at he
  exact (avoidTwo_mk_iff _ _).1 he |>.1 rfl

lemma avoidTwo_of_diagonal_not_cross_t {e : Sym2 (ZMod n)} (hn : 6 ≤ n)
    (he : IsDiagonal e) (het : e ≠ tEar (n := n))
    (hcross : ¬Cross e (tEar (n := n))) : AvoidTwo e := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [avoidTwo_mk_iff]
    constructor
    · intro ha
      have hb1 : b ≠ 1 := by
        intro hb
        apply he.2
        refine ⟨1, ?_⟩
        rw [Sym2.eq_iff]
        exact Or.inr ⟨by rw [ha]; ring, by rw [hb]⟩
      have hb3 : b ≠ 3 := by
        intro hb
        apply he.2
        refine ⟨2, ?_⟩
        rw [Sym2.eq_iff]
        exact Or.inl ⟨by rw [ha], by rw [hb]; ring⟩
      apply hcross
      simpa [ha] using cross_incident_two hn hb1
        (by
          intro hb2
          exact he.1 (by simp [ha, hb2, IsSegment, Sym2.mk_isDiag_iff])) hb3
    · intro hb
      have ha1 : a ≠ 1 := by
        intro ha
        apply he.2
        refine ⟨1, ?_⟩
        rw [Sym2.eq_iff]
        exact Or.inl ⟨by rw [ha], by rw [hb]; ring⟩
      have ha3 : a ≠ 3 := by
        intro ha
        apply he.2
        refine ⟨2, ?_⟩
        rw [Sym2.eq_iff]
        exact Or.inr ⟨by rw [ha]; ring, by rw [hb]⟩
      apply hcross
      simpa [hb, Sym2.eq_swap] using cross_incident_two hn ha1
        (by
          intro ha2
          exact he.1 (by simp [ha2, hb, IsSegment, Sym2.mk_isDiag_iff])) ha3

lemma not_cross_s_of_avoidOne {e : Sym2 (ZMod n)} (hn : 6 ≤ n)
    (he : ∀ x : ZMod n, e ≠ s(1, x)) : ¬Cross e (sEar (n := n)) := by
  intro h
  obtain ⟨x, hx⟩ := cross_s_implies_incident_one hn (cross_symm h)
  exact he x hx

lemma avoidOne_of_diagonal_not_cross_s {e : Sym2 (ZMod n)}
    (hn : 6 ≤ n) (he : IsDiagonal e) (hcross : ¬Cross e (sEar (n := n))) :
    ∀ x : ZMod n, e ≠ s(1, x) := by
  induction e using Sym2.ind with
  | _ a b =>
    intro x hx
    have hside : ¬IsSide s(a, b) := he.2
    have ha : a ≠ b := by
      simpa [IsSegment, Sym2.mk_isDiag_iff] using he.1
    rw [Sym2.eq_iff] at hx
    rcases hx with ⟨ha1, hbx⟩ | ⟨hax, hb1⟩
    · subst a
      have hb0 : b ≠ 0 := by
        intro hb
        apply hside
        exact ⟨0, by simp [hb, Sym2.eq_swap]⟩
      have hb1 : b ≠ 1 := by
        intro hb
        exact ha (by simpa [hb])
      have hb2 : b ≠ 2 := by
        intro hb
        apply hside
        refine ⟨1, ?_⟩
        rw [hb, Sym2.eq_iff]
        exact Or.inl ⟨rfl, by ring⟩
      exact hcross (cross_incident_one hn hb0 hb1 hb2)
    · subst b
      have ha0 : a ≠ 0 := by
        intro ha0
        apply hside
        exact ⟨0, by simp [ha0]⟩
      have ha1 : a ≠ 1 := by
        intro ha1
        exact ha (by simpa [ha1])
      have ha2 : a ≠ 2 := by
        intro ha2
        apply hside
        refine ⟨1, ?_⟩
        rw [ha2, Sym2.eq_iff]
        exact Or.inr ⟨by ring, rfl⟩
      exact hcross (by simpa [Sym2.eq_swap] using cross_incident_one hn ha0 ha1 ha2)

lemma avoidTwo_of_chordSwap_of_avoidOne {e : Sym2 (ZMod n)}
    (hn : 6 ≤ n) (he : ∀ x : ZMod n, e ≠ s(1, x)) : AvoidTwo (chordSwap e) := by
  induction e using Sym2.ind with
  | _ a b =>
    change AvoidTwo s(vertexSwap n a, vertexSwap n b)
    rw [avoidTwo_mk_iff]
    have ha : a ≠ 1 := by
      intro h
      exact he b (by simp [h])
    have hb : b ≠ 1 := by
      intro h
      exact he a (by simp [h, Sym2.eq_swap])
    have hswap (x : ZMod n) (hx : x ≠ 1) : vertexSwap n x ≠ 2 := by
      intro htwo
      apply hx
      calc
        x = vertexSwap n (vertexSwap n x) := by simp
        _ = vertexSwap n 2 := congrArg (vertexSwap n) htwo
        _ = 1 := by simp [vertexSwap]
    exact ⟨hswap a ha, hswap b hb⟩

lemma chordSwap_not_incident_one_of_avoidTwo {e : Sym2 (ZMod n)}
    (he : AvoidTwo e) : ∀ x : ZMod n, chordSwap e ≠ s(1, x) := by
  induction e using Sym2.ind with
  | _ a b =>
    intro x hx
    have ha2 : a ≠ 2 := (avoidTwo_mk_iff _ _).1 he |>.1
    have hb2 : b ≠ 2 := (avoidTwo_mk_iff _ _).1 he |>.2
    have hswap_one (y : ZMod n) (hy : y ≠ 2) : vertexSwap n y ≠ 1 := by
      intro h
      apply hy
      calc
        y = vertexSwap n (vertexSwap n y) := by simp
        _ = vertexSwap n 1 := congrArg (vertexSwap n) h
        _ = 2 := by simp [vertexSwap]
    have ha1 : vertexSwap n a ≠ 1 := hswap_one a ha2
    have hb1 : vertexSwap n b ≠ 1 := hswap_one b hb2
    change s(vertexSwap n a, vertexSwap n b) = s(1, x) at hx
    rw [Sym2.eq_iff] at hx
    rcases hx with ⟨h, _⟩ | ⟨_, h⟩
    · exact ha1 h
    · exact hb1 h

lemma avoidOne_of_chordSwap_of_avoidTwo {e : Sym2 (ZMod n)}
    (he : AvoidTwo e) : ∀ x : ZMod n, chordSwap e ≠ s(1, x) :=
  chordSwap_not_incident_one_of_avoidTwo he

lemma chordSwap_not_incident_two_of_avoidOne {e : Sym2 (ZMod n)}
    (he : ∀ x : ZMod n, e ≠ s(1, x)) : ∀ x : ZMod n, chordSwap e ≠ s(2, x) := by
  induction e using Sym2.ind with
  | _ a b =>
    intro x hx
    have ha : a ≠ 1 := by
      intro h
      exact he b (by simp [h])
    have hb : b ≠ 1 := by
      intro h
      exact he a (by simp [h, Sym2.eq_swap])
    have hswap_two (y : ZMod n) (hy : y ≠ 1) : vertexSwap n y ≠ 2 := by
      intro h
      apply hy
      calc
        y = vertexSwap n (vertexSwap n y) := by simp
        _ = vertexSwap n 2 := congrArg (vertexSwap n) h
        _ = 1 := by simp [vertexSwap]
    have ha2 := hswap_two a ha
    have hb2 := hswap_two b hb
    change s(vertexSwap n a, vertexSwap n b) = s(2, x) at hx
    rw [Sym2.eq_iff] at hx
    rcases hx with ⟨h, _⟩ | ⟨_, h⟩
    · exact ha2 h
    · exact hb2 h

lemma cross_chordSwap_of_avoidOne (hn : 6 ≤ n) {e f : Sym2 (ZMod n)}
    (he : ∀ x : ZMod n, e ≠ s(1, x))
    (hf : ∀ x : ZMod n, f ≠ s(1, x)) :
    Cross (chordSwap e) (chordSwap f) ↔ Cross e f := by
  have he' : AvoidTwo (chordSwap e) := avoidTwo_of_chordSwap_of_avoidOne hn he
  have hf' : AvoidTwo (chordSwap f) := avoidTwo_of_chordSwap_of_avoidOne hn hf
  constructor
  · intro h
    simpa using (cross_chordSwap_of_avoidTwo hn he' hf').mpr h
  · intro h
    apply (cross_chordSwap_of_avoidTwo hn he' hf').mp
    simpa using h


end Actual

end D5.S3.Geometry.Polygons.PolygonEarSlide
