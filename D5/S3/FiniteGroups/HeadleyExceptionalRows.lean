/- GID: D5/S3/FiniteGroups/HeadleyExceptionalRows
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyExceptionalRows
   mirror-E: none(waiver:pure-mathematical-exceptional-product)
   anchors: []
   utility: none
   digest: Shifted orthomorphism rows and the original seven-column cylinder. -/

import D5.S3.FiniteGroups.HeadleyOddRows
import D5.S3.FiniteGroups.HeadleyExtension

/-! Shared live rows for the two exceptional order-eight factors.
The column chart is a set equivalence, never an additive transport of differences. -/

noncomputable section
namespace D5.S3.FiniteGroups.HeadleyExceptionalRows
open HeadleyExtension
open D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch

variable {H K : Type*} [AddCommGroup H] [Finite H] [AddCommGroup K]
attribute [local instance] Classical.propDecidable

/-- Doubling on the original group, transported only through Gordon's additive box. -/
def doublingH (hH : Odd (Nat.card H)) :
    {b : Equiv.Perm H // ∀ h, b h = h + h} := by
  letI := Fintype.ofFinite H
  let ds := Classical.choose (HeadleyOddRows.odd_box hH)
  let e := Classical.choice (Classical.choose_spec (HeadleyOddRows.odd_box hH))
  refine ⟨e.symm.toEquiv.permCongr (HeadleyOddRows.doubling ds), ?_⟩
  intro h
  change e.symm (e h + e h) = h + h
  rw [← e.map_add, e.symm_apply_apply]

def deltaNeg (hH : Odd (Nat.card H)) : Equiv.Perm H :=
  (doublingH hH).val.trans (Equiv.neg H)

private theorem deltaNeg_spec (hH : Odd (Nat.card H)) (h : H) :
    deltaNeg hH h = -h - h := by
  change -((doublingH hH).val h) = _
  rw [(doublingH hH).property]
  abel

private theorem difference_zero (r : RCycle H) : r.difference 0 = 0 := by
  rw [r.difference_spec, r.successor_zero, sub_self]

private theorem successor_ne_zero (r : RCycle H) (h : H) :
    r.successor h ≠ 0 ↔ h ≠ 0 := by
  simpa only [r.successor_zero] using
    (r.successor.injective.ne_iff : r.successor h ≠ r.successor 0 ↔ h ≠ 0)

private theorem difference_ne_zero (r : RCycle H) (h : H) :
    r.difference h ≠ 0 ↔ h ≠ 0 := by
  simpa only [difference_zero r] using
    (r.difference.injective.ne_iff : r.difference h ≠ r.difference 0 ↔ h ≠ 0)

theorem successor_ne_self (r : RCycle H) {h : H} (hh : h ≠ 0) :
    r.successor h ≠ h := by
  intro he
  apply (difference_ne_zero r h).2 hh
  rw [r.difference_spec, he, sub_self]

def row (r : RCycle H) (last a : K) : Equiv.Perm H :=
  if a = 0 ∨ a = last then r.successor else Equiv.neg H

def rowDifference (r : RCycle H) (hH : Odd (Nat.card H)) (last a : K) :
    Equiv.Perm H :=
  if a = 0 ∨ a = last then r.difference else deltaNeg hH

theorem row_zero (r : RCycle H) (last a : K) : row r last a 0 = 0 := by
  simp only [row]
  split_ifs <;> simp [r.successor_zero]

private theorem row_difference (r : RCycle H) (hH : Odd (Nat.card H))
    (last a : K) (h : H) : rowDifference r hH last a h = row r last a h - h := by
  by_cases ha : a = 0 ∨ a = last
  · simp [rowDifference, row, ha, r.difference_spec]
  · simp [rowDifference, row, ha, deltaNeg_spec]

/-- Every stage is an equivalence, with its actual inverse composed in reverse order. -/
def shiftedSuccessor (r : RCycle H) (P : Equiv.Perm K) (s : K → H) (last : K) :
    Equiv.Perm (K × H) :=
  (Equiv.prodCongrRight (fun a => Equiv.addRight (-s a))).trans
    ((Equiv.prodCongrRight (row r last)).trans
      ((Equiv.prodCongr P (Equiv.refl H)).trans
        (Equiv.prodCongrRight (fun a => Equiv.addLeft (s a)))))

def shiftedDifference (r : RCycle H) (hH : Odd (Nat.card H))
    (P Q : Equiv.Perm K) (s : K → H) (last : K) : Equiv.Perm (K × H) :=
  (Equiv.prodCongrRight (fun a => Equiv.addRight (-s a))).trans
    ((Equiv.prodCongrRight (rowDifference r hH last)).trans
      ((Equiv.prodCongrRight (fun a => Equiv.addRight (s (P a) - s a))).trans
        (Equiv.prodCongr Q (Equiv.refl H))))

theorem shiftedSuccessor_apply (r : RCycle H) (P : Equiv.Perm K) (s : K → H)
    (last a : K) (h : H) :
    shiftedSuccessor r P s last (a, h) = (P a, s (P a) + row r last a (h - s a)) := by
  simp [shiftedSuccessor, sub_eq_add_neg]

private theorem shiftedDifference_apply (r : RCycle H) (hH : Odd (Nat.card H))
    (P Q : Equiv.Perm K) (s : K → H) (last a : K) (h : H) :
    shiftedDifference r hH P Q s last (a, h) =
      (Q a, rowDifference r hH last a (h - s a) + s (P a) - s a) := by
  simp [shiftedDifference, sub_eq_add_neg, add_assoc]

theorem shifted_difference_spec (r : RCycle H) (hH : Odd (Nat.card H))
    (P Q : Equiv.Perm K) (s : K → H) (last : K)
    (hQ : ∀ a, Q a = P a - a) (x : K × H) :
    shiftedDifference r hH P Q s last x = shiftedSuccessor r P s last x - x := by
  rcases x with ⟨a, h⟩
  rw [shiftedDifference_apply, shiftedSuccessor_apply]
  apply Prod.ext
  · exact hQ a
  · change rowDifference r hH last a (h - s a) + s (P a) - s a =
      (s (P a) + row r last a (h - s a)) - h
    rw [row_difference]
    abel

/-- Parity gauge; all seven possible column indices are retained. -/
def gauge (i : Fin 7) : Equiv.Perm H :=
  if i.val % 2 = 0 then Equiv.refl H else Equiv.neg H

theorem gauge_zero (i : Fin 7) : gauge (H := H) i 0 = 0 := by
  simp only [gauge]
  split_ifs <;> simp

private theorem gauge_twice (i : Fin 7) (h : H) : gauge i (gauge i h) = h := by
  simp only [gauge]
  split_ifs <;> simp

/-- Explicit chart and inverse in the original product coordinates. -/
def chart (c : Fin 7 ≃ {a : K // a ≠ 0}) (s : K → H) :
    H ⊕ (Fin 7 × H) ≃ K × H where
  toFun
    | .inl h => (0, h)
    | .inr (i, h) => ((c i).val, s (c i).val + gauge i h)
  invFun x := if ha : x.1 = 0 then .inl x.2 else
    let i := c.symm ⟨x.1, ha⟩
    .inr (i, gauge i (x.2 - s x.1))
  left_inv x := by
    cases x with
    | inl h => simp
    | inr x =>
      rcases x with ⟨i, h⟩
      simp only [dite_eq_right (c i).property]
      congr 1
      simp [gauge_twice]
  right_inv x := by
    rcases x with ⟨a, h⟩
    dsimp
    split_ifs with ha
    · simp [ha]
    · have hc : (c (c.symm ⟨a, ha⟩)).val = a :=
        congrArg Subtype.val (c.apply_symm_apply ⟨a, ha⟩)
      simp only [hc, gauge_twice]
      congr 1
      abel

theorem chart_inr (c : Fin 7 ≃ {a : K // a ≠ 0}) (s : K → H)
    (i : Fin 7) (h : H) : chart c s (.inr (i, h)) =
    ((c i).val, s (c i).val + gauge i h) := rfl

/-- The explicit chart conjugates the original cylinder; it does not carry differences. -/
private theorem pretrade_conjugacy (r : RCycle H) (P : Equiv.Perm K) (s : K → H)
    (c : Fin 7 ≃ {a : K // a ≠ 0}) (hP0 : P 0 = 0) (hs0 : s 0 = 0)
    (hP : ∀ i, P (c i).val = (c (finRotate 7 i)).val) :
    shiftedSuccessor r P s (c 6).val =
      (chart c s).permCongr (Equiv.sumCongr r.successor (cylinder r.successor 4)) := by
  have hci (i j : Fin 7) : (c i).val = (c j).val ↔ i = j :=
    ⟨fun h => c.injective (Subtype.ext h), fun h => congrArg (fun i => (c i).val) h⟩
  have hc0 (i : Fin 7) : (c i).val ≠ 0 := (c i).property
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (chart c s).surjective x
  cases x with
  | inl h => simp [chart, shiftedSuccessor_apply, row, hP0, hs0]
  | inr x =>
    rcases x with ⟨i, h⟩
    fin_cases i <;>
      simp [chart, shiftedSuccessor_apply, row, hP, hci, gauge, cylinder,
        hc0, r.successor_zero]

/-- The three old components, joined using the original two different-cycle swaps. -/
theorem joined_nonzero_cycle [Finite K] (r : RCycle H)
    (P : Equiv.Perm K) (s : K → H) (c : Fin 7 ≃ {a : K // a ≠ 0})
    (hP0 : P 0 = 0) (hs0 : s 0 = 0)
    (hP : ∀ i, P (c i).val = (c (finRotate 7 i)).val)
    (v : H) (hv : v ≠ 0) (iy iz iw : Fin 7) (u : H) (hu : u ≠ 0) :
    let V := chart c s
    let S := shiftedSuccessor r P s (c 6).val
    let X := V (.inl v)
    let Y := V (.inr (iy, 0))
    let Z := V (.inr (iz, 0))
    let W := V (.inr (iw, u))
    (S * Equiv.swap X Y * Equiv.swap Z W).IsCycleOn {x | x ≠ 0} := by
  classical
  dsimp only
  let V := chart c s
  let f := shiftedSuccessor r P s (c 6).val
  let g := f * Equiv.swap (V (.inl v)) (V (.inr (iy, 0)))
  let h := g * Equiv.swap (V (.inr (iz, 0))) (V (.inr (iw, u)))
  let base := Equiv.sumCongr r.successor (cylinder r.successor 4)
  have hf : f = V.permCongr base := pretrade_conjugacy r P s c hP0 hs0 hP
  let L : K × H → Prop := fun x => (V.symm x).isLeft
  let N : K × H → Prop := fun x => match V.symm x with
    | .inl _ => False
    | .inr (_, a) => a ≠ 0
  have hL : ∀ x, L (f x) ↔ L x := by
    intro x
    obtain ⟨x, rfl⟩ := V.surjective x
    rw [hf]
    cases x <;> simp [L, base]
  have hN : ∀ x, N (f x) ↔ N x := by
    intro x
    obtain ⟨x, rfl⟩ := V.surjective x
    rw [hf]
    cases x with
    | inl a => simp [N, base]
    | inr x =>
      rcases x with ⟨i, a⟩
      simp only [N, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      change ((if i = Fin.last 6 then r.successor else 1 : Equiv.Perm H) a) ≠ 0 ↔ a ≠ 0
      split_ifs <;> simp [successor_ne_zero]
  have hxy : ¬ f.SameCycle (V (.inl v)) (V (.inr (iy, 0))) := by
    intro hc
    have he := (cycle_invariant f L hL hc).mp (by simp [L])
    simpa [L] using he
  obtain ⟨hxy, preserve1⟩ := swap_joins f (V (.inl v)) (V (.inr (iy, 0))) hxy
  have hNg : ∀ x, N (g x) ↔ N x := by
    intro x
    change N (f (Equiv.swap _ _ x)) ↔ N x
    rw [hN]
    apply swap_invariant
    simp [N]
  have hzw : ¬ g.SameCycle (V (.inr (iz, 0))) (V (.inr (iw, u))) := by
    intro hc
    have he := cycle_invariant g N hNg hc
    simpa [N, hu] using he
  obtain ⟨hzw, preserve2⟩ := swap_joins g (V (.inr (iz, 0))) (V (.inr (iw, u))) hzw
  have left (a b : H) (ha : a ≠ 0) (hb : b ≠ 0) :
      f.SameCycle (V (.inl a)) (V (.inl b)) := by
    rw [hf]
    exact (same_cycle_perm_congr V base _ _).2
      (sum_sameCycle_left r.successor _ (r.nonzero_cycle.2 ha hb))
  have right (i j : Fin 7) (a b : H) (hab : r.successor.SameCycle a b) :
      f.SameCycle (V (.inr (i, a))) (V (.inr (j, b))) := by
    rw [hf]
    exact (same_cycle_perm_congr V base _ _).2
      (sum_sameCycle_right r.successor _ (cylinder_connect r.successor 4 i j a b hab))
  have hxz : g.SameCycle (V (.inl v)) (V (.inr (iz, 0))) :=
    hxy.trans (preserve1 _ _ (right iy iz 0 0 (.refl _ _)))
  have all (x : K × H) (hx : x ≠ 0) : h.SameCycle (V (.inl v)) x := by
    obtain ⟨x, rfl⟩ := V.surjective x
    cases x with
    | inl a =>
      have ha : a ≠ 0 := by rintro rfl; exact hx rfl
      exact preserve2 _ _ (preserve1 _ _ (left v a hv ha))
    | inr x =>
      rcases x with ⟨i, a⟩
      by_cases ha : a = 0
      · subst a
        exact preserve2 _ _ (hxy.trans (preserve1 _ _ (right iy i 0 0 (.refl _ _))))
      · exact (preserve2 _ _ hxz).trans
          (hzw.trans (preserve2 _ _ (preserve1 _ _
            (right iw i u a (r.nonzero_cycle.2 hu ha)))))
  have hz : h 0 = 0 := by
    have h0 : V (.inl 0) = 0 := rfl
    have hX : V (.inl 0) ≠ V (.inl v) := by simpa using hv.symm
    have hY : V (.inl 0) ≠ V (.inr (iy, 0)) := by simp
    have hZ : V (.inl 0) ≠ V (.inr (iz, 0)) := by simp
    have hW : V (.inl 0) ≠ V (.inr (iw, u)) := by simp
    rw [← h0]
    change f (Equiv.swap _ _ (Equiv.swap _ _ (V (.inl 0)))) = _
    rw [Equiv.swap_apply_of_ne_of_ne hZ hW,
      Equiv.swap_apply_of_ne_of_ne hX hY, hf]
    simp [base, r.successor_zero]
  exact ⟨bijOn_complement h 0 hz, fun x hx y hy => (all x hx).symm.trans (all y hy)⟩

end D5.S3.FiniteGroups.HeadleyExceptionalRows
