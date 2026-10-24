/- GID: D5/S3/FiniteGroups/HeadleyCubeOddProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyCubeOddProduct
   mirror-E: none(waiver:pure-mathematical-exceptional-product)
   anchors: []
   utility: none
   digest: The complete R-only exceptional odd product in original coordinates. -/

import D5.S3.FiniteGroups.HeadleyExceptionalRows
import Mathlib.Data.ZMod.Basic

/-! The order-eight table is a consumed coefficient of an unbounded odd-group construction.
Successor swaps and label-source swaps have different pairings. -/

noncomputable section
namespace D5.S3.FiniteGroups.HeadleyCubeOddProduct
open HeadleyExtension HeadleyExceptionalRows

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
