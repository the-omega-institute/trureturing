/- GID: D5/S3/Geometry/Polygons/PolygonEarSlide
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarSlide
   mirror-E: none(waiver:faithful-dependent-family-registration-pending)
   anchors: []
   utility: none
   digest: Concrete actual polygon carrier, adjacent vertex swap, ear exclusion, crossing transport, and raw erase-insert inverse laws for the pending condition-preserving fibre bridge. -/

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/cluster-algebras-polygon-third-party.md.
Authors: Ashvin A. Swaminathan.

The polygon carrier below is a minimal adaptation of the definitions and the
crossing endpoint lemma from AxiomMath/ClusterAlgebras, revision
a9174706bce3bcb0fa342b4614f98ef2acb7f91c.  The ear-slide declarations are new
and use the carrier directly.  This repository's pinned Mathlib supplies the
finite-set and symmetric-square operations used by the adaptation.
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

end Carrier

open Carrier


namespace Actual

variable {n : ℕ} [NeZero n]

lemma sbtw_val (hn : 6 ≤ n) (a b c : ZMod n) :
    sbtw a b c ↔ (a.val < b.val ∧ b.val < c.val) ∨
      (b.val < c.val ∧ c.val < a.val) ∨ (c.val < a.val ∧ a.val < b.val) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
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
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
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

lemma isDiagonal_chordSwap_of_ne (hn : 6 ≤ n) {e : Sym2 (ZMod n)}
    (he : IsDiagonal e) (hes : e ≠ sEar (n := n)) (het : e ≠ tEar (n := n)) :
    IsDiagonal (chordSwap e) := by
  refine ⟨?_, ?_⟩
  · change ¬(chordSwap e).IsDiag
    have hseg := he.1
    change ¬e.IsDiag at hseg
    change ¬(Sym2.map (vertexSwap n) e).IsDiag
    rw [Sym2.isDiag_map (Equiv.injective (vertexSwap n))]
    exact hseg
  · intro hs
    have h01 : (0 : ZMod n) ≠ 1 := by
      have h1 : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (0 : ℕ) = 1 := by simpa [ZMod.val_zero, h1] using hv
      omega
    have h02 : (0 : ZMod n) ≠ 2 := by
      have h2 : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (0 : ℕ) = 2 := by simpa [ZMod.val_zero, h2] using hv
      omega
    have h12 : (1 : ZMod n) ≠ 2 := by
      have h1 : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      have h2 : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (1 : ℕ) = 2 := by simpa [h1, h2] using hv
      omega
    have h31 : (3 : ZMod n) ≠ 1 := by
      have h1 : (1 : ZMod n).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
      have h3 : (3 : ZMod n).val = 3 := by
        simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (3 : ℕ) = 1 := by simpa [h1, h3] using hv
      omega
    have h32 : (3 : ZMod n) ≠ 2 := by
      have h2 : (2 : ZMod n).val = 2 := by
        simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
      have h3 : (3 : ZMod n).val = 3 := by
        simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
      intro h
      have hv := congrArg ZMod.val h
      have : (3 : ℕ) = 2 := by simpa [h2, h3] using hv
      omega
    have hswap0 : vertexSwap n 0 = 0 := by
      simp [vertexSwap, Equiv.swap_apply_def, h01, h02]
    have hswap1 : vertexSwap n 1 = 2 := by simp [vertexSwap]
    have hswap2 : vertexSwap n 2 = 1 := by simp [vertexSwap, h12]
    have hswap3 : vertexSwap n 3 = 3 := by
      simp [vertexSwap, Equiv.swap_apply_def, h31, h32]
    have h11 : (1 : ZMod n) + 1 = 2 := by ring
    have h23 : (2 : ZMod n) + 1 = 3 := by ring
    rcases hs with ⟨i, hi⟩
    have heq : e = chordSwap s(i, i + 1) := by
      calc
        e = chordSwap (chordSwap e) := by simp
        _ = chordSwap s(i, i + 1) := congrArg chordSwap hi
    by_cases h0 : i = 0
    · apply hes
      simpa [sEar, ear_one, h0, chordSwap, hswap0, hswap1] using heq
    by_cases h1 : i = 1
    · apply he.2
      refine ⟨1, ?_⟩
      simpa [h1, chordSwap, hswap1, hswap2, h11, Sym2.eq_swap] using heq
    by_cases h2i : i = 2
    · apply het
      simpa [tEar, ear_two, h2i, chordSwap, hswap2, hswap3, h23] using heq
    apply he.2
    refine ⟨i, ?_⟩
    have hi1 : i + 1 ≠ 1 := by
      intro h
      apply h0
      calc
        i = (i + 1) - 1 := by ring
        _ = 1 - 1 := congrArg (fun z : ZMod n => z - 1) h
        _ = 0 := by ring
    have hi2 : i + 1 ≠ 2 := by
      intro h
      apply h1
      calc
        i = (i + 1) - 1 := by ring
        _ = 2 - 1 := congrArg (fun z : ZMod n => z - 1) h
        _ = 1 := by ring
    have hswapi : vertexSwap n i = i := by
      simp [vertexSwap, Equiv.swap_apply_def, h0, h1, h2i]
    have hswapi1 : vertexSwap n (i + 1) = i + 1 := by
      simp [vertexSwap, Equiv.swap_apply_def, hi1, hi2]
    simpa [chordSwap, hswapi, hswapi1] using heq

lemma avoidTwo_of_mem_triangulation (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T) {e : Sym2 (ZMod n)}
    (he : e ∈ T) : AvoidTwo e := by
  have hdiag : IsDiagonal e := hT.isDiagonal e he
  induction e using Sym2.ind with
  | _ a b =>
      rw [avoidTwo_mk_iff]
      constructor
      · intro ha
        have hside : ¬IsSide s(a, b) := by
          intro hs
          exact hdiag.2 hs
        have hb1 : b ≠ 1 := by
          intro hb
          apply hside
          refine ⟨1, ?_⟩
          norm_num [ha, hb, Sym2.eq_swap]
        have hb3 : b ≠ 3 := by
          intro hb
          apply hside
          refine ⟨2, ?_⟩
          norm_num [ha, hb, Sym2.eq_swap]
        have hc := cross_incident_two hn hb1 (by
          intro hb2
          exact hdiag.1 (by simp [ha, hb2, IsSegment, Sym2.mk_isDiag_iff])) hb3
        exact hT.noncrossing (s(a, b)) he (tEar (n := n)) ht
          (by simpa [ha] using hc)
      · intro hb
        have hside : ¬IsSide s(a, b) := by
          intro hs
          exact hdiag.2 hs
        have ha1 : a ≠ 1 := by
          intro ha
          apply hside
          refine ⟨1, ?_⟩
          norm_num [ha, hb, Sym2.eq_swap]
        have ha3 : a ≠ 3 := by
          intro ha
          apply hside
          refine ⟨2, ?_⟩
          norm_num [ha, hb, Sym2.eq_swap]
        have hc := cross_incident_two hn ha1 (by
          intro ha2
          exact hdiag.1 (by simp [ha2, hb, IsSegment, Sym2.mk_isDiag_iff])) ha3
        exact hT.noncrossing (s(a, b)) he (tEar (n := n)) ht
          (by simpa [hb, Sym2.eq_swap] using hc)

lemma isDiagonal_sEar (hn : 6 ≤ n) : IsDiagonal (sEar (n := n)) := by
  rw [sEar, ear_one]
  have h02 : (0 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [ZMod.val_zero, h2] using hv
  have h21 : (2 : ZMod n) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [h1, h2] using hv
  have h03 : (0 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [ZMod.val_zero, h3] using hv
  refine ⟨?_, ?_⟩
  · simp [IsSegment, Sym2.mk_isDiag_iff, h02]
  · rintro ⟨i, hi⟩
    rw [Sym2.eq_iff] at hi
    rcases hi with ⟨h0, h2⟩ | ⟨h0, h2⟩
    · subst i
      apply h21
      simpa using h2
    · subst i
      apply h03
      calc
        (0 : ZMod n) = 2 + 1 := h0
        _ = 3 := by ring

lemma chordSwap_sEar (hn : 6 ≤ n) : chordSwap (sEar (n := n)) = s(0, 1) := by
  have h01 : (0 : ZMod n) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    simpa [ZMod.val_zero, h1] using hv
  have h02 : (0 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [ZMod.val_zero, h2] using hv
  simp [sEar, ear_one, chordSwap, vertexSwap, Equiv.swap_apply_def, h01, h02]

lemma chordSwap_tEar (hn : 6 ≤ n) : chordSwap (tEar (n := n)) = s(2, 3) := by
  have h31 : (3 : ZMod n) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h1, h3] using hv
  have h32 : (3 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h2, h3] using hv
  simp [tEar, ear_two, chordSwap, vertexSwap, Equiv.swap_apply_def, h31, h32]

def phi (T : Finset (Sym2 (ZMod n))) : Finset (Sym2 (ZMod n)) :=
  insert (sEar (n := n)) (image chordSwap (T.erase (tEar (n := n))))

def psi (U : Finset (Sym2 (ZMod n))) : Finset (Sym2 (ZMod n)) :=
  insert (tEar (n := n)) (image chordSwap (U.erase (sEar (n := n))))

lemma chordSwap_ne_sEar_of_diagonal {e : Sym2 (ZMod n)}
    (hn : 6 ≤ n) (he : IsDiagonal e) (h : chordSwap e = sEar (n := n)) : False := by
  have heq : e = chordSwap (sEar (n := n)) := by
    calc
      e = chordSwap (chordSwap e) := by simp
      _ = chordSwap (sEar (n := n)) := congrArg chordSwap h
  rw [chordSwap_sEar hn] at heq
  apply he.2
  exact ⟨0, by simpa using heq⟩

lemma phi_erase_s (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hdiag : ∀ e ∈ T, IsDiagonal e) (ht : tEar (n := n) ∈ T) :
    (phi T).erase (sEar (n := n)) = image chordSwap (T.erase (tEar (n := n))) := by
  apply erase_insert
  intro hs
  rw [mem_image] at hs
  obtain ⟨e, he, hse⟩ := hs
  exact chordSwap_ne_sEar_of_diagonal hn (hdiag e (mem_of_mem_erase he)) hse

lemma psi_phi (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hdiag : ∀ e ∈ T, IsDiagonal e) (ht : tEar (n := n) ∈ T)
    (hs : sEar (n := n) ∉ T) : psi (phi T) = T := by
  rw [psi, phi_erase_s hn hdiag ht]
  rw [image_image]
  simp only [Function.comp_def]
  ext e
  simp [Function.comp_def, chordSwap_involutive, ht]

lemma phi_injective (hn : 6 ≤ n) {T U : Finset (Sym2 (ZMod n))}
    (hdiagT : ∀ e ∈ T, IsDiagonal e) (hdiagU : ∀ e ∈ U, IsDiagonal e)
    (htT : tEar (n := n) ∈ T) (htU : tEar (n := n) ∈ U)
    (hsT : sEar (n := n) ∉ T) (hsU : sEar (n := n) ∉ U)
    (h : phi T = phi U) : T = U := by
  apply (psi_phi hn hdiagT htT hsT).symm.trans
  rw [h]
  exact psi_phi hn hdiagU htU hsU

lemma phi_image_members_are_diagonal (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T)
    {e : Sym2 (ZMod n)} (he : e ∈ image chordSwap (T.erase (tEar (n := n)))) :
    IsDiagonal e := by
  obtain ⟨d, hd, rfl⟩ := mem_image.mp he
  have hdt : d ≠ tEar (n := n) := (mem_erase.mp hd).1
  have hdiag : IsDiagonal d := hT.isDiagonal d (mem_erase.mp hd).2
  have hds : d ≠ sEar (n := n) := by
    intro hds
    have hsT : sEar (n := n) ∈ T := by
      simpa [hds] using (mem_erase.mp hd).2
    exact hT.noncrossing (tEar (n := n)) ht (sEar (n := n)) hsT
      (local_crossings hn).1
  exact isDiagonal_chordSwap_of_ne hn hdiag hds hdt

end Actual

end D5.S3.Geometry.Polygons.PolygonEarSlide
