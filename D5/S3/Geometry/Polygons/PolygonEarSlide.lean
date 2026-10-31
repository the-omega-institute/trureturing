/- GID: D5/S3/Geometry/Polygons/PolygonEarSlide
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonEarSlide
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Concrete actual polygon carrier, condition-preserving ear-slide equivalence, and its cyclic translates for every admissible forced/forbidden ear fibre. -/

/- proof_shape: result: content
   admission_basis: escape-witness
   escape_witness: actual triangulation preservation, full Finset inverse laws, and exact observed-ear trace transport.
   Direct frozen dependencies: none (pinned Mathlib and the adapted polygon carrier).
   The equivalence preserves all actual completions, including empty fibres. -/

/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/cluster-algebras-polygon-third-party.md.
Authors: Ashvin A. Swaminathan.

The polygon carrier below is a minimal adaptation of the definitions and the
crossing endpoint lemma from AxiomMath/ClusterAlgebras, revision
a9174706bce3bcb0fa342b4614f98ef2acb7f91c.  The ear-slide declarations are new
and use the carrier directly.  This repository's pinned Mathlib supplies the
finite-set and symmetric-square operations used by the adaptation.

The cyclic translation lemmas are adapted from the rotation proof in
`ClusterAlgebras/TypeA/Polygon.lean` and
`ClusterAlgebras/Plabic/CornerTriangulation.lean` at the same revision.
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

lemma avoidOne_of_mem_triangulation (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (hs : sEar (n := n) ∈ T) {e : Sym2 (ZMod n)}
    (he : e ∈ T) : ∀ x : ZMod n, e ≠ s(1, x) := by
  have hdiag : IsDiagonal e := hT.isDiagonal e he
  induction e using Sym2.ind with
  | _ a b =>
      intro x hx
      have hside : ¬IsSide s(a, b) := hdiag.2
      have hab : a ≠ b := by
        simpa [IsSegment, Sym2.mk_isDiag_iff] using hdiag.1
      rw [Sym2.eq_iff] at hx
      rcases hx with ⟨ha1, hbx⟩ | ⟨hax, hb1⟩
      · subst a
        have hb0 : b ≠ 0 := by
          intro hb
          apply hside
          exact ⟨0, by simp [hb, Sym2.eq_swap]⟩
        have hb1' : b ≠ 1 := by
          intro hb
          exact hab (by simpa [hb])
        have hb2 : b ≠ 2 := by
          intro hb
          apply hside
          refine ⟨1, ?_⟩
          rw [hb, Sym2.eq_iff]
          exact Or.inl ⟨rfl, by ring⟩
        exact hT.noncrossing (s(1, b)) (by simpa using he)
          (sEar (n := n)) hs (cross_incident_one hn hb0 hb1' hb2)
      · subst b
        have ha0 : a ≠ 0 := by
          intro ha
          apply hside
          exact ⟨0, by simp [ha]⟩
        have ha1' : a ≠ 1 := by
          intro ha
          exact hab (by simpa [ha])
        have ha2 : a ≠ 2 := by
          intro ha
          apply hside
          refine ⟨1, ?_⟩
          rw [ha, Sym2.eq_iff]
          exact Or.inr ⟨by ring, rfl⟩
        exact hT.noncrossing (s(a, 1)) (by simpa [Sym2.eq_swap] using he)
          (sEar (n := n)) hs
          (by simpa [Sym2.eq_swap] using cross_incident_one hn ha0 ha1' ha2)

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

lemma phi_isTriangulation (hn : 6 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T) :
    IsTriangulation (phi T) := by
  have hsT : sEar (n := n) ∉ T := by
    intro hs
    exact hT.noncrossing (tEar (n := n)) ht (sEar (n := n)) hs
      (local_crossings hn).1
  have hdiag : ∀ e ∈ phi T, IsDiagonal e := by
    intro e he
    simp only [phi, mem_insert] at he
    rcases he with rfl | he
    · exact isDiagonal_sEar hn
    · exact phi_image_members_are_diagonal hn hT ht he
  refine ⟨hdiag, ?_, ?_⟩
  · intro e he f hf hcross
    simp only [phi, mem_insert] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · exact not_cross_self _ hcross
      · obtain ⟨x, hx⟩ := cross_s_implies_incident_one hn hcross
        obtain ⟨d, hd, hde⟩ := mem_image.mp hf
        exact chordSwap_not_incident_one_of_avoidTwo
          (avoidTwo_of_mem_triangulation hn hT ht (mem_of_mem_erase hd)) x
          (by simpa [hde] using hx)
    · rcases hf with rfl | hf
      · exfalso
        obtain ⟨x, hx⟩ := cross_s_implies_incident_one hn (cross_symm hcross)
        obtain ⟨d, hd, hde⟩ := mem_image.mp he
        exact chordSwap_not_incident_one_of_avoidTwo
          (avoidTwo_of_mem_triangulation hn hT ht (mem_of_mem_erase hd)) x
          (by simpa [hde] using hx)
      · obtain ⟨d, hd, hde⟩ := mem_image.mp he
        obtain ⟨g, hg, hgf⟩ := mem_image.mp hf
        have hdT : d ∈ T := mem_of_mem_erase hd
        have hgT : g ∈ T := mem_of_mem_erase hg
        have hcross0 : Cross (chordSwap d) (chordSwap g) := by
          simpa [hde, hgf] using hcross
        have hcross' := (cross_chordSwap_of_avoidTwo hn
          (avoidTwo_of_mem_triangulation hn hT ht hdT)
          (avoidTwo_of_mem_triangulation hn hT ht hgT)).mp hcross0
        exact hT.noncrossing d hdT g hgT hcross'
  · intro e he hnot
    by_cases hcross : Cross e (sEar (n := n))
    · exact ⟨sEar (n := n), by simp [phi], hcross⟩
    have hes : e ≠ sEar (n := n) := by
      intro hes
      apply hnot
      rw [hes]
      simp [phi]
    have het : e ≠ tEar (n := n) := by
      intro het
      apply hcross
      simpa [het] using (local_crossings hn).1
    have havoidOne := avoidOne_of_diagonal_not_cross_s hn he hcross
    let g := chordSwap e
    have hgdiag : IsDiagonal g := isDiagonal_chordSwap_of_ne hn he hes het
    have hgavoid : AvoidTwo g := avoidTwo_of_chordSwap_of_avoidOne hn havoidOne
    have hgt : g ≠ tEar (n := n) := by
      intro hgt
      have heq : e = chordSwap (tEar (n := n)) := by
        calc
          e = chordSwap (chordSwap e) := by simp [g]
          _ = chordSwap (tEar (n := n)) := congrArg chordSwap hgt
      rw [chordSwap_tEar hn] at heq
      apply he.2
      rw [heq]
      refine ⟨2, ?_⟩
      rw [Sym2.eq_iff]
      exact Or.inl ⟨rfl, by ring⟩
    have hgnT : g ∉ T := by
      intro hgin
      apply hnot
      apply mem_insert_of_mem
      apply mem_image.mpr
      refine ⟨g, mem_erase.mpr ⟨hgt, hgin⟩, ?_⟩
      simp [g]
    obtain ⟨f, hfT, hgf⟩ := hT.maximal g hgdiag hgnT
    have hft : f ≠ tEar (n := n) := by
      intro hft
      subst f
      exact not_cross_t_of_avoidTwo hn hgavoid hgf
    refine ⟨chordSwap f, mem_insert_of_mem (mem_image.mpr
      ⟨f, mem_erase.mpr ⟨hft, hfT⟩, rfl⟩), ?_⟩
    have hfavoid := avoidTwo_of_mem_triangulation hn hT ht hfT
    have hmap := (cross_chordSwap_of_avoidTwo hn hgavoid hfavoid).mpr hgf
    simpa [g] using hmap

lemma isDiagonal_tEar (hn : 6 ≤ n) : IsDiagonal (tEar (n := n)) := by
  rw [tEar, ear_two]
  have h13 : (1 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h1, h3] using hv
  have h12 : (1 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [h1, h2] using hv
  have h32 : (3 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h2, h3] using hv
  have h23 : (2 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h2, h3] using hv
  have h41 : (3 : ZMod n) + 1 ≠ 1 := by
    intro h
    have h4 : (4 : ZMod n).val = 4 := by
      simpa using (ZMod.val_natCast_of_lt (show 4 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have hv := congrArg ZMod.val h
    rw [show (3 : ZMod n) + 1 = 4 by ring] at hv
    have : (4 : ℕ) = 1 := by simpa [h1, h3, h4] using hv
    omega
  refine ⟨?_, ?_⟩
  · simp [IsSegment, Sym2.mk_isDiag_iff, h13]
  · rintro ⟨i, hi⟩
    rw [Sym2.eq_iff] at hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply h23
      calc
        (2 : ZMod n) = 1 + 1 := by ring
        _ = i + 1 := by rw [h1]
        _ = 3 := h2.symm
    · apply h41
      calc
        (3 : ZMod n) + 1 = i + 1 := by rw [h2]
        _ = 1 := h1.symm

lemma psi_image_members_are_diagonal (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hU : IsTriangulation U) (hs : sEar (n := n) ∈ U)
    {e : Sym2 (ZMod n)} (he : e ∈ image chordSwap (U.erase (sEar (n := n)))) :
    IsDiagonal e := by
  obtain ⟨d, hd, rfl⟩ := mem_image.mp he
  have hds : d ≠ sEar (n := n) := (mem_erase.mp hd).1
  have hdiag : IsDiagonal d := hU.isDiagonal d (mem_erase.mp hd).2
  have hdt : d ≠ tEar (n := n) := by
    intro hdt
    have htU : tEar (n := n) ∈ U := by simpa [hdt] using (mem_erase.mp hd).2
    exact hU.noncrossing (sEar (n := n)) hs (tEar (n := n)) htU
      (cross_symm (local_crossings hn).1)
  exact isDiagonal_chordSwap_of_ne hn hdiag hds hdt

lemma psi_isTriangulation (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hU : IsTriangulation U) (hs : sEar (n := n) ∈ U) :
    IsTriangulation (psi U) := by
  have htU : tEar (n := n) ∉ U := by
    intro ht
    exact hU.noncrossing (sEar (n := n)) hs (tEar (n := n)) ht
      (cross_symm (local_crossings hn).1)
  have hdiag : ∀ e ∈ psi U, IsDiagonal e := by
    intro e he
    simp only [psi, mem_insert] at he
    rcases he with rfl | he
    · exact isDiagonal_tEar hn
    · exact psi_image_members_are_diagonal hn hU hs he
  refine ⟨hdiag, ?_, ?_⟩
  · intro e he f hf hcross
    simp only [psi, mem_insert] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · exact not_cross_self _ hcross
      · obtain ⟨x, hx⟩ := cross_t_implies_incident_two hn hcross
        obtain ⟨d, hd, hde⟩ := mem_image.mp hf
        exact chordSwap_not_incident_two_of_avoidOne
          (avoidOne_of_mem_triangulation hn hU hs (mem_of_mem_erase hd)) x
          (by simpa [hde] using hx)
    · rcases hf with rfl | hf
      · exfalso
        obtain ⟨x, hx⟩ := cross_t_implies_incident_two hn (cross_symm hcross)
        obtain ⟨d, hd, hde⟩ := mem_image.mp he
        exact chordSwap_not_incident_two_of_avoidOne
          (avoidOne_of_mem_triangulation hn hU hs (mem_of_mem_erase hd)) x
          (by simpa [hde] using hx)
      · obtain ⟨d, hd, hde⟩ := mem_image.mp he
        obtain ⟨g, hg, hgf⟩ := mem_image.mp hf
        have hdU : d ∈ U := mem_of_mem_erase hd
        have hgU : g ∈ U := mem_of_mem_erase hg
        have hcross0 : Cross (chordSwap d) (chordSwap g) := by
          simpa [hde, hgf] using hcross
        have hcross' := (cross_chordSwap_of_avoidOne hn
          (avoidOne_of_mem_triangulation hn hU hs hdU)
          (avoidOne_of_mem_triangulation hn hU hs hgU)).mp hcross0
        exact hU.noncrossing d hdU g hgU hcross'
  · intro e he hnot
    by_cases hcross : Cross e (tEar (n := n))
    · exact ⟨tEar (n := n), by simp [psi], hcross⟩
    have het : e ≠ tEar (n := n) := by
      intro het
      apply hnot
      rw [het]
      simp [psi]
    have hes : e ≠ sEar (n := n) := by
      intro hes
      apply hcross
      rw [hes]
      exact (cross_symm (local_crossings hn).1)
    have havoidTwo := avoidTwo_of_diagonal_not_cross_t hn he het hcross
    let g := chordSwap e
    have hgdiag : IsDiagonal g := isDiagonal_chordSwap_of_ne hn he hes het
    have hgavoid : ∀ x : ZMod n, g ≠ s(1, x) :=
      avoidOne_of_chordSwap_of_avoidTwo havoidTwo
    have hgnU : g ∉ U := by
      intro hgin
      apply hnot
      apply mem_insert_of_mem
      apply mem_image.mpr
      refine ⟨g, mem_erase.mpr ⟨?_, hgin⟩, ?_⟩
      · intro hgt
        have : e = chordSwap (sEar (n := n)) := by
          calc
            e = chordSwap (chordSwap e) := by simp [g]
            _ = chordSwap (sEar (n := n)) := congrArg chordSwap hgt
        rw [chordSwap_sEar hn] at this
        exact he.2 (by rw [this]; exact ⟨0, by simp⟩)
      · simp [g]
    obtain ⟨f, hfU, hgf⟩ := hU.maximal g hgdiag hgnU
    have hfs : f ≠ sEar (n := n) := by
      intro hfs
      subst f
      exact not_cross_s_of_avoidOne hn hgavoid hgf
    refine ⟨chordSwap f, mem_insert_of_mem (mem_image.mpr
      ⟨f, mem_erase.mpr ⟨hfs, hfU⟩, rfl⟩), ?_⟩
    have hfavoid := avoidOne_of_mem_triangulation hn hU hs hfU
    have hmap := (cross_chordSwap_of_avoidOne hn hgavoid hfavoid).mpr hgf
    simpa [g] using hmap

def IsRemote (i : ZMod n) : Prop := i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3

def EarCenters (T : Finset (Sym2 (ZMod n))) : Finset (ZMod n) :=
  univ.filter (fun i => ear i ∈ T)

@[simp] lemma mem_earCenters {T : Finset (Sym2 (ZMod n))} {i : ZMod n} :
    i ∈ EarCenters T ↔ ear i ∈ T := by simp [EarCenters]

def E_K (K : Finset (ZMod n)) : Finset (ZMod n) :=
  univ.filter (fun i => i ∉ K ∧ ∀ k ∈ K, ¬Cross (ear i) (ear k))

def ConditionFiber (P Q J X : Finset (ZMod n)) : Type :=
  {T : Finset (Sym2 (ZMod n)) //
    IsTriangulation T ∧ P ⊆ EarCenters T ∧
      Disjoint Q (EarCenters T) ∧ EarCenters T ∩ J = X}

lemma remote_of_K (hn : 6 ≤ n) {K J : Finset (ZMod n)}
    (hJ : J ⊆ E_K K) (h1 : (1 : ZMod n) ∈ J) (h2 : (2 : ZMod n) ∈ J)
    {i : ZMod n} (hi : i ∈ K) : IsRemote i := by
  have h1E := mem_filter.mp (hJ h1)
  have h2E := mem_filter.mp (hJ h2)
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    exact h1E.2.2 0 hi (by
      simpa [sEar, e₀, ear, ear_one, ear_zero] using (local_crossings hn).2.2)
  have hi1 : i ≠ 1 := by
    intro hi1
    subst i
    exact h1E.2.1 hi
  have hi2 : i ≠ 2 := by
    intro hi2
    subst i
    exact h2E.2.1 hi
  have hi3 : i ≠ 3 := by
    intro hi3
    subst i
    exact h2E.2.2 3 hi (by
      simpa [tEar, uEar, ear, ear_two, ear_three] using (local_crossings hn).2.1)
  exact ⟨hi0, hi1, hi2, hi3⟩

lemma chordSwap_ear_remote (hn : 14 ≤ n) {i : ZMod n} (hi : IsRemote i) :
    chordSwap (ear i) = ear i := by
  have hm1 : i - 1 ≠ 1 := by
    intro h
    apply hi.2.2.1
    calc
      i = (i - 1) + 1 := by ring
      _ = 1 + 1 := congrArg (fun z : ZMod n => z + 1) h
      _ = 2 := by ring
  have hm2 : i - 1 ≠ 2 := by
    intro h
    apply hi.2.2.2
    calc
      i = (i - 1) + 1 := by ring
      _ = 2 + 1 := congrArg (fun z : ZMod n => z + 1) h
      _ = 3 := by ring
  have hp1 : i + 1 ≠ 1 := by
    intro h
    apply hi.1
    calc
      i = (i + 1) - 1 := by ring
      _ = 1 - 1 := congrArg (fun z : ZMod n => z - 1) h
      _ = 0 := by ring
  have hp2 : i + 1 ≠ 2 := by
    intro h
    apply hi.2.1
    calc
      i = (i + 1) - 1 := by ring
      _ = 2 - 1 := congrArg (fun z : ZMod n => z - 1) h
      _ = 1 := by ring
  simp [ear, chordSwap, vertexSwap, Equiv.swap_apply_def, hm1, hm2, hp1, hp2]

lemma earCenters_remote_phi (hn : 14 ≤ n) {T : Finset (Sym2 (ZMod n))}
    {i : ZMod n} (hi : IsRemote i) :
    i ∈ EarCenters (phi T) ↔ i ∈ EarCenters T := by
  rw [mem_earCenters, mem_earCenters]
  constructor
  · intro h
    simp only [phi, mem_insert] at h
    rcases h with h | h
    · have hfix := chordSwap_ear_remote hn hi
      rw [h] at hfix
      rw [chordSwap_sEar (show 6 ≤ n by omega)] at hfix
      exfalso
      apply (isDiagonal_sEar (show 6 ≤ n by omega)).2
      exact ⟨0, by simpa using hfix.symm⟩
    · obtain ⟨d, hd, hde⟩ := mem_image.mp h
      have hde' : d = ear i := by
        calc
          d = chordSwap (chordSwap d) := by simp
          _ = chordSwap (ear i) := congrArg chordSwap hde
          _ = ear i := chordSwap_ear_remote hn hi
      simpa [hde'] using mem_of_mem_erase hd
  · intro h
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨ear i, ?_, ?_⟩
    · apply mem_erase.mpr
      constructor
      · intro hti
        have hfix := chordSwap_ear_remote hn hi
        rw [hti] at hfix
        rw [chordSwap_tEar (show 6 ≤ n by omega)] at hfix
        exfalso
        apply (isDiagonal_tEar (show 6 ≤ n by omega)).2
        exact ⟨2, by
          calc
            tEar (n := n) = s(2, 3) := hfix.symm
            _ = s(2, (2 : ZMod n) + 1) := by rw [show (2 : ZMod n) + 1 = 3 by ring]⟩
      · exact h
    · exact chordSwap_ear_remote hn hi

lemma earCenters_remote_psi (hn : 14 ≤ n) {T : Finset (Sym2 (ZMod n))}
    {i : ZMod n} (hi : IsRemote i) :
    i ∈ EarCenters (psi T) ↔ i ∈ EarCenters T := by
  rw [mem_earCenters, mem_earCenters]
  constructor
  · intro h
    simp only [psi, mem_insert] at h
    rcases h with h | h
    · have hfix := chordSwap_ear_remote hn hi
      rw [h] at hfix
      rw [chordSwap_tEar (show 6 ≤ n by omega)] at hfix
      exfalso
      apply (isDiagonal_tEar (show 6 ≤ n by omega)).2
      exact ⟨2, by
        calc
          tEar (n := n) = s(2, 3) := hfix.symm
          _ = s(2, (2 : ZMod n) + 1) := by
            rw [show (2 : ZMod n) + 1 = 3 by ring]⟩
    · obtain ⟨d, hd, hde⟩ := mem_image.mp h
      have hde' : d = ear i := by
        calc
          d = chordSwap (chordSwap d) := by simp
          _ = chordSwap (ear i) := congrArg chordSwap hde
          _ = ear i := chordSwap_ear_remote hn hi
      simpa [hde'] using mem_of_mem_erase hd
  · intro h
    apply mem_insert_of_mem
    apply mem_image.mpr
    refine ⟨ear i, ?_, chordSwap_ear_remote hn hi⟩
    apply mem_erase.mpr
    constructor
    · intro hsi
      have hfix := chordSwap_ear_remote hn hi
      rw [hsi] at hfix
      rw [chordSwap_sEar (show 6 ≤ n by omega)] at hfix
      exfalso
      apply (isDiagonal_sEar (show 6 ≤ n by omega)).2
      exact ⟨0, by simpa using hfix.symm⟩
    · exact h

lemma trace_phi (hn : 14 ≤ n) {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T)
    {J R : Finset (ZMod n)} (hJ0 : (0 : ZMod n) ∉ J)
    (hJ1 : (1 : ZMod n) ∈ J) (hJ2 : (2 : ZMod n) ∈ J)
    (hR : R ⊆ ((J.erase 1).erase 2).erase 3)
    (htrace : EarCenters T ∩ J = insert 2 R) :
    EarCenters (phi T) ∩ (J.erase 2).erase 3 = insert 1 R := by
  have h12 : (1 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [h1, h2] using hv
  have h13 : (1 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h1, h3] using hv
  have hsT : sEar (n := n) ∉ T := by
    intro hs
    exact hT.noncrossing (tEar (n := n)) ht (sEar (n := n)) hs
      (local_crossings (show 6 ≤ n by omega)).1
  have huT : ear (3 : ZMod n) ∉ T := by
    intro hu
    exact hT.noncrossing (tEar (n := n)) ht (uEar (n := n)) hu
      (local_crossings (show 6 ≤ n by omega)).2.1
  ext i
  constructor
  · intro hi
    rcases mem_inter.mp hi with ⟨hiPhi, hiDom⟩
    rcases mem_erase.mp hiDom with ⟨hi3, hiDom2⟩
    rcases mem_erase.mp hiDom2 with ⟨hi2, hiJ⟩
    by_cases hi1 : i = 1
    · exact mem_insert.mpr (Or.inl hi1)
    · apply mem_insert.mpr
      right
      have hi0 : i ≠ 0 := by intro h; apply hJ0; simpa [h] using hiJ
      have hrem : IsRemote i := ⟨hi0, hi1, hi2, hi3⟩
      have hiT : i ∈ EarCenters T := (earCenters_remote_phi hn hrem).mp hiPhi
      have hiR : i ∈ insert 2 R := by
        apply (Finset.ext_iff.mp htrace i).mp
        exact mem_inter.mpr ⟨hiT, hiJ⟩
      simpa [hi2] using hiR
  · intro hi
    rcases mem_insert.mp hi with hi1 | hiR
    · subst i
      apply mem_inter.mpr
      constructor
      · rw [mem_earCenters]
        simpa [sEar, ear_one, phi] using (mem_insert_self :
          sEar (n := n) ∈ phi T)
      · apply mem_erase.mpr
        exact ⟨h13, mem_erase.mpr ⟨h12, hJ1⟩⟩
    · have hiR' := hR hiR
      rcases mem_erase.mp hiR' with ⟨hi3, hiR2⟩
      rcases mem_erase.mp hiR2 with ⟨hi2, hiR1⟩
      rcases mem_erase.mp hiR1 with ⟨hi1, hiJ⟩
      have hi0 : i ≠ 0 := by intro h; apply hJ0; simpa [h] using hiJ
      have hrem : IsRemote i := ⟨hi0, hi1, hi2, hi3⟩
      apply mem_inter.mpr
      constructor
      · apply (earCenters_remote_phi hn hrem).mpr
        exact (mem_inter.mp ((Finset.ext_iff.mp htrace i).mpr
          (mem_insert_of_mem hiR))).1
      · exact mem_erase.mpr ⟨hi3, mem_erase.mpr ⟨hi2, hiJ⟩⟩

lemma s_not_mem_psi (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hU : IsTriangulation U) (hs : sEar (n := n) ∈ U) :
    sEar (n := n) ∉ psi U := by
  intro h
  simp only [psi, mem_insert] at h
  rcases h with h | h
  · exact not_cross_self _ ((by simpa [h] using (local_crossings hn).1))
  · obtain ⟨d, hd, hde⟩ := mem_image.mp h
    exact chordSwap_ne_sEar_of_diagonal hn
      (hU.isDiagonal d (mem_of_mem_erase hd)) hde

lemma trace_psi (hn : 14 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hU : IsTriangulation U) (hs : sEar (n := n) ∈ U)
    {J R : Finset (ZMod n)} (hJ0 : (0 : ZMod n) ∉ J)
    (hJ1 : (1 : ZMod n) ∈ J) (hJ2 : (2 : ZMod n) ∈ J)
    (hR : R ⊆ ((J.erase 1).erase 2).erase 3)
    (htrace : EarCenters U ∩ (J.erase 2).erase 3 = insert 1 R) :
    EarCenters (psi U) ∩ J = insert 2 R := by
  have htU : tEar (n := n) ∉ U := by
    intro ht
    exact hU.noncrossing (sEar (n := n)) hs (tEar (n := n)) ht
      (cross_symm (local_crossings (show 6 ≤ n by omega)).1)
  have huPsi : ear (3 : ZMod n) ∉ psi U := by
    intro hu
    have hpsi := psi_isTriangulation (show 6 ≤ n by omega) hU hs
    exact hpsi.noncrossing (tEar (n := n)) (by simp [psi])
      (uEar (n := n)) hu (local_crossings (show 6 ≤ n by omega)).2.1
  ext i
  constructor
  · intro hi
    rcases mem_inter.mp hi with ⟨hiPsi, hiJ⟩
    by_cases hi2 : i = 2
    · exact mem_insert.mpr (Or.inl hi2)
    · apply mem_insert.mpr
      right
      have hi3 : i ≠ 3 := by
        intro hi3
        subst i
        exact huPsi (by simpa [uEar, ear_three] using hiPsi)
      have hi1 : i ≠ 1 := by
        intro hi1
        subst i
        exact s_not_mem_psi (show 6 ≤ n by omega) hU hs
          (by simpa [sEar, ear_one] using hiPsi)
      have hi0 : i ≠ 0 := by intro h; apply hJ0; simpa [h] using hiJ
      have hrem : IsRemote i := ⟨hi0, hi1, hi2, hi3⟩
      have hiU : i ∈ EarCenters U := (earCenters_remote_psi hn hrem).mp hiPsi
      have hiR : i ∈ insert 1 R := by
        apply (Finset.ext_iff.mp htrace i).mp
        exact mem_inter.mpr ⟨hiU, mem_erase.mpr ⟨hi3, mem_erase.mpr ⟨hi2, hiJ⟩⟩⟩
      simpa [hi1] using hiR
  · intro hi
    rcases mem_insert.mp hi with hi2 | hiR
    · subst i
      apply mem_inter.mpr
      constructor
      · rw [mem_earCenters]
        simp [psi, tEar, ear_two]
      · exact hJ2
    · have hiR' := hR hiR
      rcases mem_erase.mp hiR' with ⟨hi3, hiR2⟩
      rcases mem_erase.mp hiR2 with ⟨hi2, hiR1⟩
      rcases mem_erase.mp hiR1 with ⟨hi1, hiJ⟩
      have hi0 : i ≠ 0 := by intro h; apply hJ0; simpa [h] using hiJ
      have hrem : IsRemote i := ⟨hi0, hi1, hi2, hi3⟩
      apply mem_inter.mpr
      constructor
      · apply (earCenters_remote_psi hn hrem).mpr
        exact (mem_inter.mp ((Finset.ext_iff.mp htrace i).mpr
          (mem_insert_of_mem hiR))).1
      · exact hiJ

lemma chordSwap_ne_tEar_of_diagonal {e : Sym2 (ZMod n)}
    (hn : 6 ≤ n) (he : IsDiagonal e) (h : chordSwap e = tEar (n := n)) : False := by
  have heq : e = chordSwap (tEar (n := n)) := by
    calc
      e = chordSwap (chordSwap e) := by simp
      _ = chordSwap (tEar (n := n)) := congrArg chordSwap h
  rw [chordSwap_tEar hn] at heq
  apply he.2
  exact ⟨2, by
    rw [heq, Sym2.eq_iff]
    exact Or.inl ⟨rfl, by ring⟩⟩

lemma psi_erase_t (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hdiag : ∀ e ∈ U, IsDiagonal e) (hs : sEar (n := n) ∈ U) :
    (psi U).erase (tEar (n := n)) = image chordSwap (U.erase (sEar (n := n))) := by
  apply erase_insert
  intro ht
  rw [mem_image] at ht
  obtain ⟨e, he, hte⟩ := ht
  exact chordSwap_ne_tEar_of_diagonal hn (hdiag e (mem_of_mem_erase he)) hte

lemma phi_psi (hn : 6 ≤ n) {U : Finset (Sym2 (ZMod n))}
    (hdiag : ∀ e ∈ U, IsDiagonal e) (hs : sEar (n := n) ∈ U)
    (ht : tEar (n := n) ∉ U) : phi (psi U) = U := by
  rw [phi, psi_erase_t hn hdiag hs]
  rw [image_image]
  simp only [Function.comp_def]
  ext e
  simp [Function.comp_def, chordSwap_involutive, hs, ht]

/-! Cyclic translations are used to remove the temporary choice of the block origin. -/

def rotationBasePos (c v : ZMod n) : ℤ := ((v - c).val : ℤ)

lemma rotationBasePos_eq_ite (c v : ZMod n) :
    rotationBasePos c v =
      if c.val ≤ v.val then (v.val : ℤ) - c.val
      else (v.val : ℤ) - c.val + n := by
  unfold rotationBasePos
  split_ifs with h
  · rw [ZMod.val_sub h]
    push_cast [h]
    ring
  · have hv : v - c + c = v := by ring
    have h1 : n ≤ (v - c).val + c.val := by
      by_contra h2
      have h3 := ZMod.val_add_of_lt (not_le.mp h2)
      rw [hv] at h3
      have h4 := ZMod.val_lt (v - c)
      omega
    have h3 := ZMod.val_add_of_le h1
    rw [hv] at h3
    have h4 := ZMod.val_lt (v - c)
    omega

lemma rotation_sbtw_iff_val (x y z : ZMod n) :
    sbtw x y z ↔ (x.val < y.val ∧ y.val < z.val) ∨
      (y.val < z.val ∧ z.val < x.val) ∨ (z.val < x.val ∧ x.val < y.val) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact Fin.sbtw_iff

lemma rotation_sbtw_iff_basePos (c x y z : ZMod n) :
    sbtw x y z ↔ sbtw (rotationBasePos c x)
      (rotationBasePos c y) (rotationBasePos c z) := by
  rw [rotation_sbtw_iff_val, Int.sbtw_iff, rotationBasePos_eq_ite,
    rotationBasePos_eq_ite, rotationBasePos_eq_ite]
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hz := ZMod.val_lt z
  split_ifs <;> omega

lemma sbtw_add_right_iff_actual (a x y z : ZMod n) :
    sbtw (x + a) (y + a) (z + a) ↔ sbtw x y z := by
  rw [rotation_sbtw_iff_basePos a, rotation_sbtw_iff_basePos 0]
  simp [rotationBasePos]

lemma cross_map_add_actual {e f : Sym2 (ZMod n)} (h : Cross e f) (a : ZMod n) :
    Cross (e.map (fun x => x + a)) (f.map (fun x => x + a)) := by
  obtain ⟨x, y, z, w, rfl, rfl, hxy, hzw⟩ := h
  exact ⟨x + a, y + a, z + a, w + a, rfl, rfl,
    (sbtw_add_right_iff_actual a _ _ _).2 hxy,
    (sbtw_add_right_iff_actual a _ _ _).2 hzw⟩

lemma chord_map_add_neg_map_add (e : Sym2 (ZMod n)) (a : ZMod n) :
    (e.map (fun x => x + a)).map (fun x => x + -a) = e := by
  induction e using Sym2.ind with
  | _ x y => simp [Sym2.map_map, Function.comp_def, add_assoc]

lemma isDiagonal_map_add {e : Sym2 (ZMod n)} (h : IsDiagonal e) (a : ZMod n) :
    IsDiagonal (e.map (fun x => x + a)) := by
  refine ⟨?_, ?_⟩
  · rw [IsSegment, Sym2.isDiag_map (add_left_injective a)]
    exact h.1
  · intro hs
    obtain ⟨i, hi⟩ := hs
    apply h.2
    refine ⟨i + -a, ?_⟩
    apply (chord_map_add_neg_map_add e a).symm.trans
    rw [hi, Sym2.map_mk]
    congr 1
    ring

lemma isTriangulation_map_add {T : Finset (Sym2 (ZMod n))}
    (hT : IsTriangulation T) (a : ZMod n) :
    IsTriangulation (T.image (fun e => e.map (fun x => x + a))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    exact isDiagonal_map_add (hT.isDiagonal d hd) a
  · intro e he f hf hcross
    obtain ⟨d, hd, rfl⟩ := mem_image.mp he
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
    have hback := cross_map_add_actual (a := -a) hcross
    have hback' : Cross d g := by
      simpa [Sym2.map_map, Function.comp_def, add_assoc] using hback
    exact hT.noncrossing d hd g hg hback'
  · intro e he hnot
    have he' : IsDiagonal (e.map (fun x => x + -a)) :=
      isDiagonal_map_add he (-a)
    have heT' : e.map (fun x => x + -a) ∉ T := by
      intro heT
      apply hnot
      exact mem_image.mpr ⟨e.map (fun x => x + -a), heT, by
        simp [Sym2.map_map, Function.comp_def, add_assoc]⟩
    obtain ⟨d, hd, hcross⟩ := hT.maximal _ he' heT'
    refine ⟨d.map (fun x => x + a), mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    simpa [Sym2.map_map, Function.comp_def, add_assoc] using cross_map_add_actual hcross a

def shiftSet (S : Finset (ZMod n)) (a : ZMod n) : Finset (ZMod n) :=
  S.image (fun x => x + a)

def shiftChords (T : Finset (Sym2 (ZMod n))) (a : ZMod n) :
    Finset (Sym2 (ZMod n)) := T.image (fun e => e.map (fun x => x + a))

lemma shiftSet_mem_iff {S : Finset (ZMod n)} {a x : ZMod n} :
    x + a ∈ shiftSet S a ↔ x ∈ S := by
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := mem_image.mp h
    have : y = x := by
      apply add_right_cancel
      exact hxy
    simpa [this] using hy
  · intro h
    exact mem_image.mpr ⟨x, h, rfl⟩

lemma mem_shiftSet_iff {S : Finset (ZMod n)} {a x : ZMod n} :
    x ∈ shiftSet S a ↔ x + -a ∈ S := by
  have h := shiftSet_mem_iff (S := S) (a := a) (x := x + -a)
  simpa [add_assoc] using h

lemma shiftSet_add_neg (S : Finset (ZMod n)) (a : ZMod n) :
    shiftSet (shiftSet S a) (-a) = S := by
  ext x
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := mem_image.mp h
    obtain ⟨z, hz, hyz⟩ := mem_image.mp hy
    have : z = x := by
      calc z = (z + a) + -a := by simp [add_assoc]
           _ = y + -a := by rw [hyz]
           _ = x := hxy
    simpa [this] using hz
  · intro h
    apply mem_image.mpr
    refine ⟨x + a, ?_, ?_⟩
    · exact mem_image.mpr ⟨x, h, rfl⟩
    · simp [add_assoc]

lemma shiftChords_add_neg (T : Finset (Sym2 (ZMod n))) (a : ZMod n) :
    shiftChords (shiftChords T a) (-a) = T := by
  ext e
  constructor
  · intro h
    obtain ⟨f, hf, hfe⟩ := mem_image.mp h
    obtain ⟨d, hd, hdf⟩ := mem_image.mp hf
    have hfe' : f = e.map (fun x => x + a) := by
      have h := congrArg (fun q => q.map (fun x => x + a)) hfe
      simpa [Sym2.map_map, Function.comp_def, add_assoc] using h
    have : d = e := by
      apply Sym2.map.injective (add_left_injective a)
      exact hdf.trans hfe'
    simpa [this] using hd
  · intro h
    apply mem_image.mpr
    refine ⟨e.map (fun x => x + a), ?_, ?_⟩
    · exact mem_image.mpr ⟨e, h, rfl⟩
    · simp [Sym2.map_map, Function.comp_def, add_assoc]

lemma ear_add (i a : ZMod n) :
    ear (i + a) = (ear i).map (fun x => x + a) := by
  rw [ear, ear, Sym2.map_mk, Sym2.eq_iff]
  left
  constructor <;> ring

lemma ear_mem_shift_iff {T : Finset (Sym2 (ZMod n))} {i a : ZMod n} :
    i + a ∈ EarCenters (shiftChords T a) ↔ i ∈ EarCenters T := by
  rw [mem_earCenters, mem_earCenters, ear_add]
  constructor
  · intro h
    obtain ⟨d, hd, hde⟩ := mem_image.mp h
    have : d = ear i := Sym2.map.injective (add_left_injective a) hde
    simpa [this] using hd
  · intro h
    exact mem_image.mpr ⟨ear i, h, rfl⟩

lemma earCenters_shift_iff {T : Finset (Sym2 (ZMod n))} {i a : ZMod n} :
    i + a ∈ EarCenters (shiftChords T a) ↔ i ∈ EarCenters T :=
  ear_mem_shift_iff

lemma earCenters_shift_mem_iff {T : Finset (Sym2 (ZMod n))} {i a : ZMod n} :
    i ∈ EarCenters (shiftChords T a) ↔ i + -a ∈ EarCenters T := by
  have h := ear_mem_shift_iff (T := T) (i := i + -a) (a := a)
  simpa [add_assoc] using h

lemma cross_ear_shift_iff {i j a : ZMod n} :
    Cross (ear (i + a)) (ear (j + a)) ↔ Cross (ear i) (ear j) := by
  constructor
  · intro h
    have h' := cross_map_add_actual (a := -a) h
    simpa [ear_add, Sym2.map_map, Function.comp_def, add_assoc] using h'
  · intro h
    simpa [ear_add] using cross_map_add_actual (a := a) h

lemma mem_E_K_shift_iff {K : Finset (ZMod n)} {i a : ZMod n} :
    i + a ∈ E_K (shiftSet K a) ↔ i ∈ E_K K := by
  simp only [E_K, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hi, hcross⟩
    refine ⟨?_, ?_⟩
    · intro hiK
      apply hi
      exact mem_image.mpr ⟨i, hiK, rfl⟩
    · intro k hk hcrossik
      apply hcross (k + a)
      · exact mem_image.mpr ⟨k, hk, rfl⟩
      · exact (cross_ear_shift_iff (i := i) (j := k) (a := a)).mpr hcrossik
  · rintro ⟨hi, hcross⟩
    refine ⟨?_, ?_⟩
    · intro hiK
      obtain ⟨k, hk, hki⟩ := mem_image.mp hiK
      apply hi
      have : k = i := by
        apply add_right_cancel
        exact hki
      simpa [this] using hk
    · intro k hk hcrossik
      obtain ⟨j, hj, hkj⟩ := mem_image.mp hk
      have hjk : j + a = k := hkj
      have hcross' : Cross (ear i) (ear j) := by
        apply (cross_ear_shift_iff (i := i) (j := j) (a := a)).mp
        simpa [hjk] using hcrossik
      exact hcross j hj hcross'

lemma shiftSet_disjoint_shiftSet {S U : Finset (ZMod n)} {a : ZMod n}
    (h : Disjoint S U) : Disjoint (shiftSet S a) (shiftSet U a) := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxU
  obtain ⟨s, hs, hxs⟩ := mem_image.mp hxS
  obtain ⟨u, hu, hxu⟩ := mem_image.mp hxU
  have : s = u := by
    apply add_right_cancel
    exact hxs.trans hxu.symm
  exact (Finset.disjoint_left.mp h) hs (this ▸ hu)

lemma shiftSet_card (S : Finset (ZMod n)) (a : ZMod n) :
    (shiftSet S a).card = S.card := by
  exact card_image_of_injective _ (add_left_injective a)

lemma shiftSet_erase (S : Finset (ZMod n)) (x a : ZMod n) :
    shiftSet (S.erase x) a = (shiftSet S a).erase (x + a) := by
  unfold shiftSet
  rw [image_erase (add_left_injective a)]

lemma shiftSet_insert (S : Finset (ZMod n)) (x a : ZMod n) :
    shiftSet (insert x S) a = insert (x + a) (shiftSet S a) := by
  simp [shiftSet]

lemma shiftSet_union (S U : Finset (ZMod n)) (a : ZMod n) :
    shiftSet (S ∪ U) a = shiftSet S a ∪ shiftSet U a := by
  simp [shiftSet]

def shift_condition_fibre_equiv (a : ZMod n)
    {P Q J X : Finset (ZMod n)} :
    ConditionFiber P Q J X ≃
      ConditionFiber (shiftSet P a) (shiftSet Q a) (shiftSet J a) (shiftSet X a) := by
  refine
    { toFun := fun x => ?_
      invFun := fun y => ?_
      left_inv := ?_
      right_inv := ?_ }
  · rcases x with ⟨T, hT, hP, hQ, htrace⟩
    refine ⟨shiftChords T a, isTriangulation_map_add hT a, ?_, ?_, ?_⟩
    · rintro i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      exact (earCenters_shift_iff (T := T) (i := j) (a := a)).mpr (hP hj)
    · apply Finset.disjoint_left.mpr
      intro i hiQ hiT
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hiQ
      exact (Finset.disjoint_left.mp hQ) hj
        ((earCenters_shift_iff (T := T) (i := j) (a := a)).mp hiT)
    · ext i
      constructor
      · intro hi
        have hiT := (mem_inter.mp hi).1
        have hiJ := (mem_inter.mp hi).2
        have hiT' := (earCenters_shift_mem_iff (T := T) (i := i) (a := a)).mp hiT
        have hiJ' := (mem_shiftSet_iff (S := J) (a := a) (x := i)).mp hiJ
        have hiX' := (Finset.ext_iff.mp htrace (i + -a)).mp
          (mem_inter.mpr ⟨hiT', hiJ'⟩)
        exact (mem_shiftSet_iff (S := X) (a := a) (x := i)).mpr hiX'
      · intro hi
        have hiX' := (mem_shiftSet_iff (S := X) (a := a) (x := i)).mp hi
        have hiT'J' := (Finset.ext_iff.mp htrace (i + -a)).mpr
          ((mem_shiftSet_iff (S := X) (a := a) (x := i)).mp hi)
        have hiT' := (mem_inter.mp hiT'J').1
        have hiJ' := (mem_inter.mp hiT'J').2
        exact mem_inter.mpr
          ⟨(earCenters_shift_mem_iff (T := T) (i := i) (a := a)).mpr hiT',
            (mem_shiftSet_iff (S := J) (a := a) (x := i)).mpr hiJ'⟩
  · rcases y with ⟨U, hU, hP, hQ, htrace⟩
    refine ⟨shiftChords U (-a), isTriangulation_map_add hU (-a), ?_, ?_, ?_⟩
    · rintro i hi
      have hi' : i + a ∈ shiftSet P a := mem_image.mpr ⟨i, hi, rfl⟩
      exact (earCenters_shift_mem_iff (T := U) (i := i) (a := -a)).mpr
        (by simpa [neg_neg] using hP hi')
    · apply Finset.disjoint_left.mpr
      intro i hiQ hiU
      have hi' : i + a ∈ shiftSet Q a := mem_image.mpr ⟨i, hiQ, rfl⟩
      have hc := (earCenters_shift_mem_iff (T := U) (i := i) (a := -a)).mp hiU
      exact (Finset.disjoint_left.mp hQ) hi' (by simpa [neg_neg] using hc)
    · ext i
      constructor
      · intro hi
        have hiU := (mem_inter.mp hi).1
        have hiJ := (mem_inter.mp hi).2
        have hiU' := (earCenters_shift_mem_iff (T := U) (i := i) (a := -a)).mp hiU
        have hiJ' : i + a ∈ shiftSet J a := mem_image.mpr ⟨i, hiJ, rfl⟩
        have hiX' := (Finset.ext_iff.mp htrace (i + a)).mp
          (mem_inter.mpr ⟨by simpa [neg_neg] using hiU', hiJ'⟩)
        have hiX'' := (mem_shiftSet_iff (S := X) (a := a) (x := i + a)).mp hiX'
        simpa [add_assoc] using hiX''
      · intro hi
        have hiX' : i + a ∈ shiftSet X a := mem_image.mpr ⟨i, hi, rfl⟩
        have hiUJ' := (Finset.ext_iff.mp htrace (i + a)).mpr hiX'
        have hiU' := (mem_inter.mp hiUJ').1
        have hiJ'' := (mem_inter.mp hiUJ').2
        have hiJ : i ∈ J :=
          by
            simpa [add_assoc] using
              (mem_shiftSet_iff (S := J) (a := a) (x := i + a)).mp hiJ''
        exact mem_inter.mpr
          ⟨(earCenters_shift_mem_iff (T := U) (i := i) (a := -a)).mpr
              (by simpa [neg_neg] using hiU'), hiJ⟩
  · intro x
    rcases x with ⟨T, hT, hP, hQ, htrace⟩
    exact Subtype.ext (shiftChords_add_neg T a)
  · intro y
    rcases y with ⟨U, hU, hP, hQ, htrace⟩
    exact Subtype.ext (by simpa [neg_neg] using shiftChords_add_neg U (-a))

def condition_fibre_equiv (hn : 14 ≤ n)
    {P Q J R : Finset (ZMod n)}
    (hJ : J ⊆ E_K (P ∪ Q))
    (hJ0 : (0 : ZMod n) ∉ J) (hJ1 : (1 : ZMod n) ∈ J)
    (hJ2 : (2 : ZMod n) ∈ J)
    (hR : R ⊆ ((J.erase 1).erase 2).erase 3) :
    ConditionFiber P Q J (insert 2 R) ≃
      ConditionFiber P Q ((J.erase 2).erase 3) (insert 1 R) := by
  have h6 : 6 ≤ n := by omega
  have hPrem : ∀ i ∈ P, IsRemote i := by
    intro i hi
    apply remote_of_K h6 hJ hJ1 hJ2
    exact mem_union_left Q hi
  have hQrem : ∀ i ∈ Q, IsRemote i := by
    intro i hi
    apply remote_of_K h6 hJ hJ1 hJ2
    exact mem_union_right P hi
  have h12 : (1 : ZMod n) ≠ 2 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h2 : (2 : ZMod n).val = 2 := by
      simpa using (ZMod.val_natCast_of_lt (show 2 < n by omega))
    simpa [h1, h2] using hv
  have h13 : (1 : ZMod n) ≠ 3 := by
    intro h
    have hv := congrArg ZMod.val h
    have h1 : (1 : ZMod n).val = 1 := by
      simpa using (ZMod.val_natCast_of_lt (show 1 < n by omega))
    have h3 : (3 : ZMod n).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (show 3 < n by omega))
    simpa [h1, h3] using hv
  have hsource_s {T : Finset (Sym2 (ZMod n))}
      (hT : IsTriangulation T) (ht : tEar (n := n) ∈ T) :
      sEar (n := n) ∉ T := by
    intro hs
    exact hT.noncrossing (tEar (n := n)) ht (sEar (n := n)) hs
      (local_crossings h6).1
  have htarget_s {U : Finset (Sym2 (ZMod n))}
      (hU : IsTriangulation U) (htrace : EarCenters U ∩
        ((J.erase 2).erase 3) = insert 1 R) :
      sEar (n := n) ∈ U := by
    have hdom : (1 : ZMod n) ∈ (J.erase 2).erase 3 :=
      mem_erase.mpr ⟨h13, mem_erase.mpr ⟨h12, hJ1⟩⟩
    have hmem := (Finset.ext_iff.mp htrace (1 : ZMod n)).mpr
      (by simp : (1 : ZMod n) ∈ insert 1 R)
    have hcenter : (1 : ZMod n) ∈ EarCenters U := (mem_inter.mp hmem).1
    exact (mem_earCenters.mp hcenter)
  have hsource_t {T : Finset (Sym2 (ZMod n))}
      (htrace : EarCenters T ∩ J = insert 2 R) :
      tEar (n := n) ∈ T := by
    have hmem := (Finset.ext_iff.mp htrace (2 : ZMod n)).mpr
      (by simp : (2 : ZMod n) ∈ insert 2 R)
    have hcenter : (2 : ZMod n) ∈ EarCenters T := (mem_inter.mp hmem).1
    exact (mem_earCenters.mp hcenter)
  refine
    { toFun := fun x =>
        ⟨phi x.1, ?_⟩
      invFun := fun y =>
        ⟨psi y.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rcases x with ⟨T, hT, hP, hQ, htrace⟩
    have ht := hsource_t htrace
    have hphiT := phi_isTriangulation h6 hT ht
    refine ⟨hphiT, ?_, ?_, ?_⟩
    · intro i hi
      exact (earCenters_remote_phi hn (hPrem i hi)).mpr (hP hi)
    · apply Finset.disjoint_left.mpr
      intro i hiP hiPhi
      exact (Finset.disjoint_left.mp hQ) hiP
        ((earCenters_remote_phi hn (hQrem i hiP)).mp hiPhi)
    · exact trace_phi hn hT ht hJ0 hJ1 hJ2 hR htrace
  · rcases y with ⟨U, hU, hP, hQ, htrace⟩
    have hsU := htarget_s hU htrace
    have hpsiU := psi_isTriangulation h6 hU hsU
    refine ⟨hpsiU, ?_, ?_, ?_⟩
    · intro i hi
      exact (earCenters_remote_psi hn (hPrem i hi)).mpr (hP hi)
    · apply Finset.disjoint_left.mpr
      intro i hiP hiPsi
      exact (Finset.disjoint_left.mp hQ) hiP
        ((earCenters_remote_psi hn (hQrem i hiP)).mp hiPsi)
    · exact trace_psi hn hU hsU hJ0 hJ1 hJ2 hR htrace
  · intro x
    rcases x with ⟨T, hT, hP, hQ, htrace⟩
    have ht : tEar (n := n) ∈ T := hsource_t htrace
    have hs : sEar (n := n) ∉ T := hsource_s hT ht
    exact Subtype.ext (psi_phi h6 (fun e he => hT.isDiagonal e he) ht hs)
  · intro y
    rcases y with ⟨U, hU, hP, hQ, htrace⟩
    have hs : sEar (n := n) ∈ U := htarget_s hU htrace
    have ht : tEar (n := n) ∉ U := by
      intro ht
      exact hU.noncrossing (sEar (n := n)) hs (tEar (n := n)) ht
        (cross_symm (local_crossings h6).1)
    exact Subtype.ext (phi_psi h6 (fun e he => hU.isDiagonal e he) hs ht)

def condition_fibre_equiv_at (hn : 14 ≤ n) (a : ZMod n)
    {P Q J R : Finset (ZMod n)}
    (hJ : J ⊆ E_K (P ∪ Q))
    (ha0 : a ∉ J) (ha1 : a + 1 ∈ J) (ha2 : a + 2 ∈ J)
    (hR : R ⊆ ((J.erase (a + 1)).erase (a + 2)).erase (a + 3)) :
    ConditionFiber P Q J (insert (a + 2) R) ≃
      ConditionFiber P Q ((J.erase (a + 2)).erase (a + 3)) (insert (a + 1) R) := by
  let P0 := shiftSet P (-a)
  let Q0 := shiftSet Q (-a)
  let J0 := shiftSet J (-a)
  let R0 := shiftSet R (-a)
  have hJ0sub : J0 ⊆ E_K (P0 ∪ Q0) := by
    intro i hi
    obtain ⟨i0, hi0, rfl⟩ := mem_image.mp hi
    have hiE := (mem_E_K_shift_iff (K := P ∪ Q) (i := i0) (a := -a)).mpr (hJ hi0)
    simpa [P0, Q0, shiftSet_union] using hiE
  have hJ00 : (0 : ZMod n) ∉ J0 := by
    intro hz
    have := (mem_shiftSet_iff (S := J) (a := -a) (x := 0)).mp hz
    exact ha0 (by simpa using this)
  have hJ01 : (1 : ZMod n) ∈ J0 := by
    apply (mem_shiftSet_iff (S := J) (a := -a) (x := 1)).mpr
    simpa [add_assoc, add_comm] using ha1
  have hJ02 : (2 : ZMod n) ∈ J0 := by
    apply (mem_shiftSet_iff (S := J) (a := -a) (x := 2)).mpr
    simpa [add_assoc, add_comm] using ha2
  have hR0 : R0 ⊆ ((J0.erase 1).erase 2).erase 3 := by
    intro i hi
    obtain ⟨i0, hi0, rfl⟩ := mem_image.mp hi
    have hi0' := hR hi0
    have htrip :
        shiftSet (((J.erase (a + 1)).erase (a + 2)).erase (a + 3)) (-a) =
          ((J0.erase 1).erase 2).erase 3 := by
      rw [shiftSet_erase, shiftSet_erase, shiftSet_erase]
      simp [J0, add_assoc]
    rw [← htrip]
    exact mem_image.mpr ⟨i0, hi0', rfl⟩
  let e0 := shift_condition_fibre_equiv (n := n) (-a)
    (P := P) (Q := Q) (J := J) (X := insert (a + 2) R)
  let ef := condition_fibre_equiv (n := n) hn hJ0sub
    hJ00 hJ01 hJ02 hR0
  let e1 := shift_condition_fibre_equiv (n := n) a
    (P := P0) (Q := Q0) (J := (J0.erase 2).erase 3) (X := insert 1 R0)
  have hPshift : shiftSet P0 a = P := by
    simpa [P0, neg_neg] using shiftSet_add_neg P (-a)
  have hQshift : shiftSet Q0 a = Q := by
    simpa [Q0, neg_neg] using shiftSet_add_neg Q (-a)
  have hX0 : shiftSet (insert (a + 2) R) (-a) = insert 2 R0 := by
    rw [shiftSet_insert]
    simp [R0, add_assoc]
  have htarget :
      shiftSet ((J0.erase 2).erase 3) a =
        (J.erase (a + 2)).erase (a + 3) := by
    rw [shiftSet_erase, shiftSet_erase]
    have hJshift : shiftSet J0 a = J := by
      simpa [J0, neg_neg] using shiftSet_add_neg J (-a)
    rw [hJshift]
    simp [add_comm, add_left_comm, add_assoc]
  have hRshift : shiftSet R0 a = R := by
    simpa [R0, neg_neg] using shiftSet_add_neg R (-a)
  have hsrcR : shiftSet (insert 1 R0) a = insert (a + 1) R := by
    rw [shiftSet_insert, hRshift]
    simp [add_comm, add_left_comm, add_assoc]
  have e0' : ConditionFiber P Q J (insert (a + 2) R) ≃
      ConditionFiber P0 Q0 J0 (insert 2 R0) := by
    simpa only [P0, Q0, J0, R0, hX0] using e0
  have e1' : ConditionFiber P0 Q0 ((J0.erase 2).erase 3) (insert 1 R0) ≃
      ConditionFiber P Q ((J.erase (a + 2)).erase (a + 3)) (insert (a + 1) R) := by
    simpa only [hPshift, hQshift, htarget, hsrcR] using e1
  exact e0'.trans (ef.trans e1')

end Actual

end D5.S3.Geometry.Polygons.PolygonEarSlide
