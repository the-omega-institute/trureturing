/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression
   mirror-E: none(waiver:registration-pending)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Fin.Basic]
   utility: none
   digest: Empty radius-four buffers preserve incident neighborhoods under cyclic column deletion. -/

import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression

open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree (externalBoundary)
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
  (columns occupiedVertices)

/-- The inverse of deletion, on the surviving vertices. -/
def insertVertex {m : Nat} (t : Fin (m + 1)) (v : Bool × Fin m) :
    Bool × Fin (m + 1) := (v.1, t.succAbove v.2)

/-- No selected column is within four cyclic steps of the removed column. -/
def EmptyBuffer {n : Nat} [NeZero n] (t : Fin n)
    (X : Finset (Bool × Fin n)) : Prop :=
  ∀ x ∈ X, ∀ d : Nat, d ≤ 4 →
    x.2 ≠ t + Fin.ofNat n d ∧ x.2 ≠ t - Fin.ofNat n d

private theorem forward_four {m : Nat} [NeZero m] (hm : 108 ≤ m)
    (t : Fin (m + 1)) (i : Fin m) (k : Nat) (hk : k ≤ 4)
    (hbuffer : ∀ d : Nat, 1 ≤ d → d ≤ 4 →
      t.succAbove i ≠ t - Fin.ofNat (m + 1) d) :
    t.succAbove (i + Fin.ofNat m k) =
      t.succAbove i + Fin.ofNat (m + 1) k := by
  have hins (j : Fin m) : (t.succAbove j).val =
      if j.val < t.val then j.val else j.val + 1 := by
    by_cases h : j.val < t.val <;> simp [Fin.succAbove, Fin.lt_def, h]
  have havoid (d : Nat) (hd0 : 1 ≤ d) (hd4 : d ≤ 4) :
      ((t.succAbove i).val + d) % (m + 1) ≠ t.val := by
    intro he
    apply hbuffer d hd0 hd4
    apply (eq_sub_iff_add_eq).mpr
    apply Fin.ext
    simpa [Fin.val_add, Fin.val_ofNat,
      Nat.mod_eq_of_lt (show d < m + 1 by omega)] using he
  have hclear : (t.succAbove i).val < t.val →
      (t.succAbove i).val + k < t.val := by
    intro hlt
    by_contra hcross
    have hd0 : 1 ≤ t.val - (t.succAbove i).val := by omega
    have hd4 : t.val - (t.succAbove i).val ≤ 4 := by omega
    have h := havoid (t.val - (t.succAbove i).val) hd0 hd4
    have he : (t.succAbove i).val + (t.val - (t.succAbove i).val) =
        t.val := by omega
    exact h (by rw [he, Nat.mod_eq_of_lt t.isLt])
  have hclearWrap : (t.succAbove i).val + k < m + 1 + t.val := by
    by_contra hcross
    have hd0 : 1 ≤ m + 1 + t.val - (t.succAbove i).val := by
      have := (t.succAbove i).isLt
      omega
    have hd4 : m + 1 + t.val - (t.succAbove i).val ≤ 4 := by omega
    have h := havoid (m + 1 + t.val - (t.succAbove i).val) hd0 hd4
    have he : (t.succAbove i).val +
        (m + 1 + t.val - (t.succAbove i).val) = m + 1 + t.val := by
      have := (t.succAbove i).isLt
      omega
    exact h (by rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt t.isLt])
  have hnew : (i + Fin.ofNat m k).val = (i.val + k) % m := by
    simp [Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt (show k < m by omega)]
  have hold : (t.succAbove i + Fin.ofNat (m + 1) k).val =
      ((t.succAbove i).val + k) % (m + 1) := by
    simp [Fin.val_add, Fin.val_ofNat,
      Nat.mod_eq_of_lt (show k < m + 1 by omega)]
  apply Fin.ext
  rw [hins, hnew, hold, hins]
  rw [hins] at hclear hclearWrap
  by_cases hit : i.val < t.val
  · have hc : i.val + k < t.val := by
      simpa [hit] using hclear (by simpa only [if_pos hit] using hit)
    simp only [if_pos hit]
    rw [Nat.mod_eq_of_lt (show i.val + k < m by omega), if_pos hc,
      Nat.mod_eq_of_lt (show i.val + k < m + 1 by omega)]
  · simp only [if_neg hit] at *
    by_cases hw : i.val + k < m
    · rw [Nat.mod_eq_of_lt hw, if_neg (by omega),
        Nat.mod_eq_of_lt (show i.val + 1 + k < m + 1 by omega)]
      omega
    · have hn : (i.val + k) % m = i.val + k - m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have ho : (i.val + 1 + k) % (m + 1) = i.val + k - m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [hn, if_pos (by omega), ho]

private theorem backward_four {m : Nat} [NeZero m] (hm : 108 ≤ m)
    (t : Fin (m + 1)) (i : Fin m) (k : Nat) (hk : k ≤ 4)
    (hbuffer : ∀ d : Nat, 1 ≤ d → d ≤ 4 →
      t.succAbove i ≠ t + Fin.ofNat (m + 1) d) :
    t.succAbove (i - Fin.ofNat m k) =
      t.succAbove i - Fin.ofNat (m + 1) k := by
  have hrevsub {q : Nat} [NeZero q] (a b : Fin q) :
      (a - b).rev = a.rev + b := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    rw [← Fin.last_sub, ← Fin.last_sub]
    abel
  have hrevadd {q : Nat} [NeZero q] (a b : Fin q) :
      (a + b).rev = a.rev - b := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    rw [← Fin.last_sub, ← Fin.last_sub]
    abel
  have hb (d : Nat) (hd0 : 1 ≤ d) (hd4 : d ≤ 4) :
      t.rev.succAbove i.rev ≠ t.rev - Fin.ofNat (m + 1) d := by
    rw [← Fin.rev_succAbove, ← hrevadd]
    intro he
    have he' := congrArg Fin.rev he
    exact hbuffer d hd0 hd4 (by simpa only [Fin.rev_rev] using he')
  have hf := forward_four hm t.rev i.rev k hk hb
  apply Fin.rev_injective
  rw [Fin.rev_succAbove t (i - Fin.ofNat m k),
    hrevsub i (Fin.ofNat m k),
    hrevsub (t.succAbove i) (Fin.ofNat (m + 1) k),
    Fin.rev_succAbove t i]
  exact hf

private theorem neighbors (q : Nat) [NeZero q] (hq : 108 ≤ q)
    (v w : Bool × Fin q) :
    (gp q 4).Adj v w ↔
      (if v.1 then
        w = (false, v.2) ∨ w = (true, v.2 + Fin.ofNat q 4) ∨
          w = (true, v.2 - Fin.ofNat q 4)
       else w = (true, v.2) ∨ w = (false, v.2 + Fin.ofNat q 1) ∨
          w = (false, v.2 - Fin.ofNat q 1)) := by
  have hstep (k : Nat) (hk : k < q) (hpos : 0 < k) (i : Fin q) :
      i + Fin.ofNat q k ≠ i := by
    intro h
    have hz : (Fin.ofNat q k : Fin q) = 0 := by
      apply add_left_cancel (a := i)
      simpa using h
    have := congrArg Fin.val hz
    simp [Nat.mod_eq_of_lt hk] at this
    omega
  have hreverse (k : Nat) (x y : Fin q) :
      x = y + Fin.ofNat q k ↔ y = x - Fin.ofNat q k := by
    constructor <;> intro h <;> rw [h] <;> simp
  have hcycle (k : Nat) (hk : k < q) (hpos : 0 < k) (x y : Fin q) :
      (x ≠ y ∧ (y = x + Fin.ofNat q k ∨ x = y + Fin.ofNat q k)) ↔
        y = x + Fin.ofNat q k ∨ y = x - Fin.ofNat q k := by
    rw [← hreverse k x y]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      intro hxy
      subst y
      rcases h with h | h <;> exact hstep k hk hpos x h.symm
  rcases v with ⟨vb, vi⟩
  rcases w with ⟨wb, wi⟩
  cases vb <;> cases wb
  · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add,
      Fin.val_ofNat, Nat.add_mod_mod] using hcycle 1 (by omega) (by omega) vi wi
  · simpa [gp, SimpleGraph.fromRel_adj] using (eq_comm : vi = wi ↔ wi = vi)
  · simp [gp, SimpleGraph.fromRel_adj]
  · simpa [gp, SimpleGraph.fromRel_adj, Fin.ext_iff, Fin.val_add,
      Fin.val_ofNat, Nat.add_mod_mod] using hcycle 4 (by omega) (by omega) vi wi

private theorem incident_iff {m : Nat} [NeZero m] (hm : 108 ≤ m)
    (t : Fin (m + 1)) (u v : Bool × Fin m)
    (hb : ∀ d : Nat, d ≤ 4 →
      (insertVertex t u).2 ≠ t + Fin.ofNat (m + 1) d ∧
      (insertVertex t u).2 ≠ t - Fin.ofNat (m + 1) d) :
    (gp m 4).Adj u v ↔
      (gp (m + 1) 4).Adj (insertVertex t u) (insertVertex t v) := by
  have hf (d : Nat) (hd : d ≤ 4) :
      t.succAbove (u.2 + Fin.ofNat m d) =
        t.succAbove u.2 + Fin.ofNat (m + 1) d :=
    forward_four hm t u.2 d hd (fun k _ hk => (hb k hk).2)
  have hr (d : Nat) (hd : d ≤ 4) :
      t.succAbove (u.2 - Fin.ofNat m d) =
        t.succAbove u.2 - Fin.ofNat (m + 1) d :=
    backward_four hm t u.2 d hd (fun k _ hk => (hb k hk).1)
  rw [neighbors m hm u v,
    neighbors (m + 1) (by omega) (insertVertex t u) (insertVertex t v)]
  rcases u with ⟨b, i⟩
  rcases v with ⟨c, j⟩
  cases b <;> cases c
  all_goals simp only [insertVertex, Bool.false_eq_true, Bool.true_eq_false,
    ite_false, ite_true, Prod.mk.injEq, true_and, false_and, false_or]
  all_goals try simp only [← hf 1 (by omega), ← hr 1 (by omega),
    ← hf 4 (by omega), ← hr 4 (by omega)]
  all_goals simp only [Fin.succAbove_right_inj]

/-- Deletion inside an empty radius-four buffer preserves every selected incident
edge and recovers the selected set and its entire external boundary by insertion. -/
theorem buffered_deletion {m : Nat} [NeZero m] (hm : 108 ≤ m)
    (t : Fin (m + 1)) (X : Finset (Bool × Fin (m + 1)))
    (hbuffer : EmptyBuffer t X) :
    ∃ Y : Finset (Bool × Fin m),
      Y.card = X.card ∧
      (externalBoundary (gp m 4) Y).card =
        (externalBoundary (gp (m + 1) 4) X).card ∧
      Y.image (insertVertex t) = X ∧
      (externalBoundary (gp m 4) Y).image (insertVertex t) =
        externalBoundary (gp (m + 1) 4) X ∧
      (columns Y).image t.succAbove = columns X ∧
      ∀ u ∈ Y, ∀ v : Bool × Fin m,
        (gp m 4).Adj u v ↔
          (gp (m + 1) 4).Adj (insertVertex t u) (insertVertex t v) := by
  let e := insertVertex t
  let Y : Finset (Bool × Fin m) := Finset.univ.filter fun v => e v ∈ X
  have heinj : Function.Injective e := by
    intro a b hab
    have hfst : a.1 = b.1 := congrArg (fun w : Bool × Fin (m + 1) => w.1) hab
    have hsnd : t.succAbove a.2 = t.succAbove b.2 :=
      congrArg (fun w : Bool × Fin (m + 1) => w.2) hab
    exact Prod.ext hfst (Fin.succAbove_right_injective hsnd)
  have hnoX (x : Bool × Fin (m + 1)) (hx : x ∈ X) : x.2 ≠ t := by
    simpa [EmptyBuffer] using (hbuffer x hx 0 (by omega)).1
  have hYimage : Y.image e = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hu).2
    · intro hx
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (hnoX x hx)
      refine Finset.mem_image.mpr ⟨(x.1, j), ?_, Prod.ext rfl hj⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [e, insertVertex, hj] using hx⟩
  have hnoBoundary (w : Bool × Fin (m + 1))
      (hw : w ∈ externalBoundary (gp (m + 1) 4) X) : w.2 ≠ t := by
    obtain ⟨x, hx, hadj⟩ := (Finset.mem_filter.mp hw).2.2
    have hb (d : Nat) (hd : d ≤ 4) := hbuffer x hx d hd
    have hz : x.2 ≠ t := hnoX x hx
    rcases x with ⟨b, i⟩
    cases b
    · rcases (neighbors (m + 1) (by omega) (false, i) w).mp hadj with hs | hp | hn
      · rw [hs]; exact hz
      · rw [hp]; intro he
        exact (hb 1 (by omega)).2 ((eq_sub_iff_add_eq).mpr he)
      · rw [hn]; intro he
        exact (hb 1 (by omega)).1 ((sub_eq_iff_eq_add).mp he)
    · rcases (neighbors (m + 1) (by omega) (true, i) w).mp hadj with hs | hp | hn
      · rw [hs]; exact hz
      · rw [hp]; intro he
        exact (hb 4 (by omega)).2 ((eq_sub_iff_add_eq).mpr he)
      · rw [hn]; intro he
        exact (hb 4 (by omega)).1 ((sub_eq_iff_eq_add).mp he)
  have hBimage : (externalBoundary (gp m 4) Y).image e =
      externalBoundary (gp (m + 1) 4) X := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨_, hvnot, u, hu, huv⟩ := Finset.mem_filter.mp hv
      have huX : e u ∈ X := (Finset.mem_filter.mp hu).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, e u, huX, ?_⟩
      · intro h
        exact hvnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact (incident_iff hm t u v (fun k hk => hbuffer (e u) huX k hk)).mp huv
    · intro hw
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (hnoBoundary w hw)
      let v : Bool × Fin m := (w.1, j)
      have hvw : e v = w := Prod.ext rfl hj
      obtain ⟨_, hnot, x, hx, hadj⟩ := Finset.mem_filter.mp hw
      obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp (hYimage.symm ▸ hx)
      refine Finset.mem_image.mpr ⟨v, ?_, hvw⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, u, hu, ?_⟩
      · intro hv
        exact hnot (hvw ▸ (Finset.mem_filter.mp hv).2)
      · apply (incident_iff hm t u v
          (fun k hk => hbuffer (e u) ((Finset.mem_filter.mp hu).2) k hk)).mpr
        change (gp (m + 1) 4).Adj (e u) (e v)
        rw [hux, hvw]
        exact hadj
  have hcardY : Y.card = X.card := by
    have h : (Y.image e).card = Y.card := Finset.card_image_iff.mpr heinj.injOn
    rw [hYimage] at h
    exact h.symm
  have hcardB : (externalBoundary (gp m 4) Y).card =
      (externalBoundary (gp (m + 1) 4) X).card := by
    have h : ((externalBoundary (gp m 4) Y).image e).card =
        (externalBoundary (gp m 4) Y).card := Finset.card_image_iff.mpr heinj.injOn
    rw [hBimage] at h
    exact h.symm
  have hcolumns : (columns Y).image t.succAbove = columns X := by
    ext j
    simp only [columns, Finset.mem_image]
    constructor
    · rintro ⟨i, ⟨u, hu, hui⟩, rfl⟩
      exact ⟨e u, (Finset.mem_filter.mp hu).2,
        by simpa [e, insertVertex] using congrArg t.succAbove hui⟩
    · rintro ⟨x, hx, hxi⟩
      obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp (hYimage.symm ▸ hx)
      refine ⟨u.2, ⟨u, hu, rfl⟩, ?_⟩
      simpa [e, insertVertex] using (congrArg Prod.snd hux).trans hxi
  refine ⟨Y, hcardY, hcardB, hYimage, hBimage, hcolumns, ?_⟩
  intro u hu v
  exact incident_iff hm t u v (fun d hd => hbuffer (e u) ((Finset.mem_filter.mp hu).2) d hd)

private theorem small_boundary_columns {n : Nat} (X : Finset (Bool × Fin n))
    (hX : X.card = 16) (hB : (externalBoundary (gp n 4) X).card ≤ 9) :
    (columns X).card ≤ 12 := by
  have hsub : X ⊆ occupiedVertices X := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  have hmiss : occupiedVertices X \ X ⊆ externalBoundary (gp n 4) X := by
    intro v hv
    obtain ⟨hvocc, hvnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp (Finset.mem_product.mp hvocc).2
    have hne : u ≠ v := by intro h; exact hvnot (h ▸ hu)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hvnot, u, hu, ?_⟩
    rcases u with ⟨b, i⟩
    rcases v with ⟨c, j⟩
    simp only [Prod.snd] at huv
    subst j
    cases b <;> cases c <;> simp_all [gp, SimpleGraph.fromRel_adj]
  have hcardOcc : (occupiedVertices X).card = 2 * (columns X).card := by
    simp [occupiedVertices]
  have hcard := Finset.card_le_card hmiss
  rw [Finset.card_sdiff_of_subset hsub, hcardOcc, hX] at hcard
  omega

private theorem empty_center {n : Nat} [NeZero n] (hn : 108 < n)
    (X : Finset (Bool × Fin n)) (hc : (columns X).card ≤ 12) :
    ∃ t : Fin n, EmptyBuffer t X := by
  let blocked := ((columns X).product (Finset.range 9)).image
    (fun p => p.1 + Fin.ofNat n p.2 - Fin.ofNat n 4)
  have hcard : blocked.card ≤ 108 := by
    calc
      blocked.card ≤ ((columns X).product (Finset.range 9)).card := Finset.card_image_le
      _ = (columns X).card * 9 := by simp
      _ ≤ 108 := by omega
  have hnot : ¬ (Finset.univ : Finset (Fin n)) ⊆ blocked := by
    intro h
    have := Finset.card_le_card h
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨t, _, ht⟩ := Finset.not_subset.mp hnot
  refine ⟨t, ?_⟩
  intro x hx d hd
  have hxC : x.2 ∈ columns X := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hcast (a b : Nat) : Fin.ofNat n (a + b) = Fin.ofNat n a + Fin.ofNat n b := by
    apply Fin.ext
    simp [Fin.val_add, Nat.add_mod]
  have hm : Fin.ofNat n (4 - d) = Fin.ofNat n 4 - Fin.ofNat n d := by
    apply (eq_sub_iff_add_eq).mpr
    rw [← hcast]
    congr 1
    omega
  constructor
  · intro he
    apply ht
    refine Finset.mem_image.mpr ⟨(x.2, 4 - d),
      Finset.mem_product.mpr ⟨hxC, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    rw [he, hm]
    rw [add_assoc, add_comm (Fin.ofNat n d) (Fin.ofNat n 4 - Fin.ofNat n d),
      sub_add_cancel, add_sub_cancel_right]
  · intro he
    apply ht
    refine Finset.mem_image.mpr ⟨(x.2, 4 + d),
      Finset.mem_product.mpr ⟨hxC, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    rw [he, hcast]
    rw [add_comm (Fin.ofNat n 4) (Fin.ofNat n d), ← add_assoc,
      sub_add_cancel, add_sub_cancel_right]

/-- Any hypothetical sixteen-set with at most nine boundary vertices above
108 columns compresses to exactly 108 columns with identical boundary size. -/
theorem compression_to_108 (n : Nat) (hn : 108 < n)
    (X : Finset (Bool × Fin n)) (hX : X.card = 16)
    (hB : (externalBoundary (gp n 4) X).card ≤ 9) :
    ∃ Y : Finset (Bool × Fin 108), Y.card = 16 ∧
      (externalBoundary (gp 108 4) Y).card = (externalBoundary (gp n 4) X).card := by
  suffices h : ∀ q : Nat, 108 ≤ q → ∀ Z : Finset (Bool × Fin q),
      Z.card = 16 → (externalBoundary (gp q 4) Z).card ≤ 9 →
      ∃ Y : Finset (Bool × Fin 108), Y.card = 16 ∧
        (externalBoundary (gp 108 4) Y).card = (externalBoundary (gp q 4) Z).card from
    h n (by omega) X hX hB
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq Z hZ hBZ
    by_cases heq : q = 108
    · subst q
      exact ⟨Z, hZ, rfl⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      letI : NeZero m := ⟨by omega⟩
      obtain ⟨t, ht⟩ := empty_center (by omega : 108 < m + 1) Z
        (small_boundary_columns Z hZ hBZ)
      obtain ⟨Z', hcard, hboundary, _⟩ := buffered_deletion (by omega : 108 ≤ m) t Z ht
      have hBZ' : (externalBoundary (gp m 4) Z').card ≤ 9 := by
        rw [hboundary]
        exact hBZ
      obtain ⟨Y, hY, hBY⟩ := ih m (by omega) (by omega) Z'
        (hcard.trans hZ) hBZ'
      exact ⟨Y, hY, hBY.trans hboundary⟩

#print axioms buffered_deletion
#print axioms compression_to_108

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingFourCompression
