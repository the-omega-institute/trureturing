/- GID: D5/S3/FiniteGroups/HeadleyCubeOddProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyCubeOddProduct
   mirror-E: none(waiver:pure-mathematical-exceptional-product)
   anchors: []
   utility: none
   digest: The complete R-only exceptional odd product in original coordinates. -/

import D5.S3.FiniteGroups.HeadleyOddRows
import D5.S3.FiniteGroups.HeadleyExtension
import Mathlib.Data.ZMod.Basic

/-! The order-eight table is a consumed coefficient of an unbounded odd-group construction.
Successor swaps and label-source swaps have different pairings. -/

noncomputable section
namespace D5.S3.FiniteGroups.HeadleyCubeOddProduct
open HeadleyExtension

section Rows
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

/-- The given nonzero cycle, indexed by its actual bounded sigma orbit. -/
private def nonzeroOrbit (r : RCycle H) (a : H) (ha : a ≠ 0) :
    Fin (Nat.card H - 1) ≃ {h : H // h ≠ 0} := by
  classical
  letI := Fintype.ofFinite H
  let s : Finset H := Finset.univ.erase 0
  have hs : r.successor.IsCycleOn (s : Set H) := by
    have he : (s : Set H) = {h : H | h ≠ 0} := by ext h; simp [s]
    rw [he]
    exact r.nonzero_cycle
  have hcard : s.card = Nat.card H - 1 := by
    simp [s, Nat.card_eq_fintype_card]
  have hzero (n : ℕ) : (r.successor ^ n) 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [pow_succ', Equiv.Perm.mul_apply, ih, r.successor_zero]
  refine Equiv.ofBijective (fun j : Fin (Nat.card H - 1) =>
    ⟨(r.successor ^ j.val) a, fun he =>
      ha ((r.successor ^ j.val).injective (he.trans (hzero j.val).symm))⟩) ?_
  constructor
  · intro i j hij
    apply Fin.ext
    exact hs.injOn_pow_apply (a := a) (by simp [s, ha])
      (by simpa only [Set.mem_Iio, hcard] using i.isLt)
      (by simpa only [Set.mem_Iio, hcard] using j.isLt)
      (congrArg Subtype.val hij)
  · intro b
    obtain ⟨j, hj, he⟩ := hs.exists_pow_eq (a := a) (b := b.val) (by simp [s, ha])
      (by simp [s, b.property])
    refine ⟨⟨j, by simpa only [hcard] using hj⟩, ?_⟩
    exact Subtype.ext he

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
  have input_connection (a b : H) (ha : a ≠ 0) (hb : b ≠ 0) :
      r.successor.SameCycle a b := by
    letI := Fintype.ofFinite H
    let s : Finset H := Finset.univ.erase 0
    have hs : r.successor.IsCycleOn (s : Set H) := by
      have he : (s : Set H) = {h : H | h ≠ 0} := by ext h; simp [s]
      rw [he]
      exact r.nonzero_cycle
    have hcard : s.card = Nat.card H - 1 := by
      simp [s, Nat.card_eq_fintype_card]
    have hpos : 0 < Nat.card H - 1 := by
      rw [← hcard]
      exact Finset.card_pos.mpr ⟨a, by simp [s, ha]⟩
    let O := nonzeroOrbit r (r.successor a) ((successor_ne_zero r a).2 ha)
    let last : Fin (Nat.card H - 1) := ⟨Nat.card H - 1 - 1, by omega⟩
    have closing : (O last).val = a := by
      change (r.successor ^ (Nat.card H - 1 - 1)) (r.successor a) = a
      rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)]
      simpa only [hcard] using hs.pow_card_apply (a := a) (by simp [s, ha])
    have endpoint : r.successor.SameCycle (r.successor a) a :=
      ⟨(last.val : ℤ), by rw [zpow_natCast]; exact closing⟩
    obtain ⟨j, hj⟩ := O.surjective ⟨b, hb⟩
    have path : r.successor.SameCycle (r.successor a) b :=
      ⟨(j.val : ℤ), by rw [zpow_natCast]; exact congrArg Subtype.val hj⟩
    exact endpoint.symm.trans path
  have left (a b : H) (ha : a ≠ 0) (hb : b ≠ 0) :
      f.SameCycle (V (.inl a)) (V (.inl b)) := by
    rw [hf]
    exact (same_cycle_perm_congr V base _ _).2
      (sum_sameCycle_left r.successor _ (input_connection a b ha hb))
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
            (right iw i u a (input_connection u a hu ha)))))
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

end Rows


private abbrev K := ZMod 2 × ZMod 2 × ZMod 2
private def e : K := (1, 0, 0)
private def b : K := (0, 1, 0)
private def c : K := (0, 0, 1)
private def t : K := (1, 1, 0)
private def p : K := (0, 1, 1)
private def k : K := (1, 1, 1)
private def l : K := (1, 0, 1)

private def column (i : Fin 7) : K := ![e, b, c, t, p, k, l] i

private def columns : Fin 7 ≃ {x : K // x ≠ 0} where
  toFun i := ⟨column i, by fin_cases i <;> decide⟩
  invFun x := if x.val = e then 0 else
    if x.val = b then 1 else
    if x.val = c then 2 else
    if x.val = t then 3 else
    if x.val = p then 4 else
    if x.val = k then 5 else 6
  left_inv := by decide
  right_inv := by decide

private def P : Equiv.Perm K where
  toFun x := if x = e then b else
    if x = b then c else
    if x = c then t else
    if x = t then p else
    if x = p then k else
    if x = k then l else
    if x = l then e else 0
  invFun x := if x = b then e else
    if x = c then b else
    if x = t then c else
    if x = p then t else
    if x = k then p else
    if x = l then k else
    if x = e then l else 0
  left_inv := by decide
  right_inv := by decide

private def Q : Equiv.Perm K where
  toFun x := P x - x
  invFun x := if x = t then e else
    if x = p then b else
    if x = k then c else
    if x = l then t else
    if x = e then p else
    if x = b then k else
    if x = c then l else 0
  left_inv := by decide
  right_inv := by decide

private theorem P_zero : P 0 = 0 := by decide
private theorem P_column : ∀ i, P (columns i).val =
    (columns (finRotate 7 i)).val := by decide

private def coefficientCycle : RCycle K where
  successor := P
  successor_zero := P_zero
  difference := Q
  difference_spec _ := rfl
  nonzero_cycle := by
    have orbit : ∀ i : Fin 7, (P ^ i.val) e = (columns i).val := by decide
    have all (x : K) (hx : x ≠ 0) : P.SameCycle e x := by
      obtain ⟨i, hi⟩ := columns.surjective ⟨x, hx⟩
      refine ⟨(i.val : ℤ), ?_⟩
      rw [zpow_natCast, orbit]
      exact congrArg Subtype.val hi
    exact ⟨bijOn_complement P 0 P_zero, fun x hx y hy => (all x hx).symm.trans (all y hy)⟩

variable {H : Type*} [AddCommGroup H] [Finite H]
attribute [local instance] Classical.propDecidable
local instance : DecidableEq K := fun _ _ => Classical.propDecidable _

private def q (r : RCycle H) (v : H) : H :=
  r.successor.symm (r.successor v - v)

private theorem q_ne_zero (r : RCycle H) {v : H} (hv : v ≠ 0) : q r v ≠ 0 := by
  intro he
  apply successor_ne_self r hv
  have hd := congrArg r.successor he
  have hd0 : r.successor v - v = 0 := by simpa [q, r.successor_zero] using hd
  exact sub_eq_zero.mp hd0

private def shift (r : RCycle H) (v : H) (x : K) : H :=
  if x = 0 then 0 else if x = e then v else if x = b then r.successor v
  else if x = c then v else if x = t then r.successor v
  else if x = p then 0 else if x = k then 0 else v - q r v

private def S0 (r : RCycle H) (v : H) : Equiv.Perm (K × H) :=
  shiftedSuccessor r P (shift r v) l

private def successor (r : RCycle H) (v : H) : Equiv.Perm (K × H) :=
  S0 r v * Equiv.swap (0, v) (c, v) * Equiv.swap (e, v) (l, v)

private def labelSources (v : H) : Equiv.Perm (K × H) :=
  Equiv.swap (0, v) (e, v) * Equiv.swap (c, v) (l, v)

private def difference (r : RCycle H) (hH : Odd (Nat.card H)) (v : H) :
    Equiv.Perm (K × H) :=
  (labelSources v).trans (shiftedDifference r hH P Q (shift r v) l)

private theorem S0_X (r : RCycle H) (v : H) : S0 r v (0, v) = (0, r.successor v) := by
  simp [S0, shiftedSuccessor_apply, shift, row, P_zero]

private theorem S0_Y (r : RCycle H) (v : H) :
    S0 r v (c, v) = (t, r.successor v) := by
  simp [S0, shiftedSuccessor_apply, shift, row, P, e, b, c, t, p, k, l, r.successor_zero]

private theorem S0_Z (r : RCycle H) (v : H) :
    S0 r v (e, v) = (b, r.successor v) := by
  simp [S0, shiftedSuccessor_apply, shift, row, P, e, b, c, t, p, k, l, r.successor_zero]

private theorem S0_W (r : RCycle H) (v : H) :
    S0 r v (l, v) = (e, r.successor v) := by
  simp only [S0, shiftedSuccessor_apply]
  apply Prod.ext
  · norm_num [P, e, b, c, t, p, k, l]
  · change shift r v (P l) + row r l l (v - shift r v l) = r.successor v
    have hp : P l = e := by norm_num [P, e, b, c, t, p, k, l]
    rw [hp]
    have hs : shift r v e = v := by simp [shift, e, b, c, t, p, k, l]
    have hl : shift r v l = v - q r v := by simp [shift, e, b, c, t, p, k, l]
    rw [hs, hl]
    have hr : row r l l = r.successor := by simp [row]
    rw [hr, sub_sub_cancel, q, r.successor.apply_symm_apply]
    abel

private theorem difference_spec (r : RCycle H) (hH : Odd (Nat.card H)) (v : H)
    (x : K × H) : difference r hH v x = successor r v x - x := by
  change shiftedDifference r hH P Q (shift r v) l (labelSources v x) = _
  rw [shifted_difference_spec r hH P Q (shift r v) l (fun _ => rfl)]
  change S0 r v (labelSources v x) - labelSources v x = successor r v x - x
  have h0Y : (0 : K) ≠ c := by norm_num [c, Prod.ext_iff]
  have h0Z : (0 : K) ≠ e := by norm_num [e, Prod.ext_iff]
  have h0W : (0 : K) ≠ l := by norm_num [l, Prod.ext_iff]
  have hYZ : c ≠ e := by norm_num [c, e, Prod.ext_iff]
  have hYW : c ≠ l := by norm_num [c, l, Prod.ext_iff]
  have hZW : e ≠ l := by norm_num [e, l, Prod.ext_iff]
  by_cases hX : x = (0, v)
  · subst x
    simp [labelSources, successor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Prod.mk.injEq, h0Y, h0Z, h0W, hYZ, hYW, hZW,
      h0Y.symm, h0Z.symm, h0W.symm, hYZ.symm, hYW.symm, hZW.symm,
      S0_X, S0_Y, S0_Z, S0_W] <;>
      norm_num [e, b, c, t, p, k, l, Prod.ext_iff] <;> decide
  by_cases hY : x = (c, v)
  · subst x
    simp [labelSources, successor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Prod.mk.injEq, h0Y, h0Z, h0W, hYZ, hYW, hZW,
      h0Y.symm, h0Z.symm, h0W.symm, hYZ.symm, hYW.symm, hZW.symm,
      S0_X, S0_Y, S0_Z, S0_W] <;>
      norm_num [e, b, c, t, p, k, l, Prod.ext_iff] <;> decide
  by_cases hZ : x = (e, v)
  · subst x
    simp [labelSources, successor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Prod.mk.injEq, h0Y, h0Z, h0W, hYZ, hYW, hZW,
      h0Y.symm, h0Z.symm, h0W.symm, hYZ.symm, hYW.symm, hZW.symm,
      S0_X, S0_Y, S0_Z, S0_W] <;>
      norm_num [e, b, c, t, p, k, l, Prod.ext_iff] <;> decide
  by_cases hW : x = (l, v)
  · subst x
    simp [labelSources, successor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Prod.mk.injEq, h0Y, h0Z, h0W, hYZ, hYW, hZW,
      h0Y.symm, h0Z.symm, h0W.symm, hYZ.symm, hYW.symm, hZW.symm,
      S0_X, S0_Y, S0_Z, S0_W] <;>
      norm_num [e, b, c, t, p, k, l, Prod.ext_iff] <;> decide
  · simp [labelSources, successor, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hX hY, Equiv.swap_apply_of_ne_of_ne hZ hW,
      Equiv.swap_apply_of_ne_of_ne hX hZ, Equiv.swap_apply_of_ne_of_ne hY hW,
      Equiv.swap_apply_of_ne_of_ne hX hW, Equiv.swap_apply_of_ne_of_ne hY hZ]

private theorem successor_zero (r : RCycle H) {v : H} (hv : v ≠ 0) :
    successor r v 0 = 0 := by
  have hX : (0 : K × H) ≠ (0, v) := by simpa [Prod.ext_iff] using hv.symm
  have hY : (0 : K × H) ≠ (c, v) := by simp [Prod.ext_iff, c]
  have hZ : (0 : K × H) ≠ (e, v) := by simp [Prod.ext_iff, e]
  have hW : (0 : K × H) ≠ (l, v) := by simp [Prod.ext_iff, l]
  simp only [successor, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hZ hW, Equiv.swap_apply_of_ne_of_ne hX hY]
  change S0 r v (0, 0) = 0
  simp [S0, shiftedSuccessor_apply, shift, row_zero, P_zero]

private theorem nonzero_cycle (r : RCycle H) {v : H} (hv : v ≠ 0) :
    (successor r v).IsCycleOn {x | x ≠ 0} := by
  let V := chart columns (shift r v)
  have hX : V (.inl v) = (0, v) := rfl
  have hY : V (.inr (2, 0)) = (c, v) := by
    simp [V, chart_inr, columns, column, shift, gauge_zero, e, b, c, t, p, k, l]
  have hZ : V (.inr (0, 0)) = (e, v) := by
    simp [V, chart_inr, columns, column, shift, gauge_zero, e, b, c, t, p, k, l]
  have hW : V (.inr (6, q r v)) = (l, v) := by
    rw [show V (.inr (6, q r v)) =
      ((columns 6).val, shift r v (columns 6).val + gauge 6 (q r v)) from rfl]
    change (l, shift r v l + q r v) = (l, v)
    simp [shift, e, b, c, t, p, k, l]
  have hc := joined_nonzero_cycle r P (shift r v) columns P_zero
    (by simp [shift]) P_column v hv 2 0 6 (q r v) (q_ne_zero r hv)
  dsimp only at hc
  rw [show (columns 6).val = l by rfl] at hc
  change (S0 r v * Equiv.swap (V (.inl v)) (V (.inr (2, 0))) *
    Equiv.swap (V (.inr (0, 0))) (V (.inr (6, q r v)))).IsCycleOn {x | x ≠ 0} at hc
  rw [hX, hY, hZ, hW] at hc
  exact hc

/-- An ordinary R-cycle suffices for every finite odd factor, including the trivial group. -/
def cube_odd_product (r : RCycle H) (hH : Odd (Nat.card H)) :
    RCycle ((ZMod 2 × ZMod 2 × ZMod 2) × H) := by
  classical
  letI := Fintype.ofFinite H
  by_cases hn : ∃ v : H, v ≠ 0
  · let v := Classical.choose hn
    have hv : v ≠ 0 := Classical.choose_spec hn
    exact {
      successor := successor r v
      successor_zero := successor_zero r hv
      nonzero_cycle := nonzero_cycle r hv
      difference := difference r hH v
      difference_spec := difference_spec r hH v
    }
  · have hz (h : H) : h = 0 := by by_contra hne; exact hn ⟨h, hne⟩
    letI : Subsingleton H := ⟨fun x y => (hz x).trans (hz y).symm⟩
    letI : Unique H := { default := 0, uniq := hz }
    exact transportCycle (AddEquiv.prodUnique : K × H ≃+ K).symm coefficientCycle

end D5.S3.FiniteGroups.HeadleyCubeOddProduct
