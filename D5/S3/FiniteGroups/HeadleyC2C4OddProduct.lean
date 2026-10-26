/- GID: D5/S3/FiniteGroups/HeadleyC2C4OddProduct
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/HeadleyC2C4OddProduct
   mirror-E: none(waiver:pure-mathematical-exceptional-product)
   anchors: []
   utility: none
   digest: The complete R-only exceptional odd product in original coordinates. -/

import D5.S3.FiniteGroups.HeadleyCubeOddProduct
import Mathlib.Data.ZMod.Basic

/-! The order-eight table is a consumed coefficient of an unbounded odd-group construction.
Successor swaps and label-source swaps have different pairings. -/

noncomputable section
namespace D5.S3.FiniteGroups.HeadleyC2C4OddProduct
open HeadleyExtension HeadleyCubeOddProduct

private abbrev K := ZMod 2 × ZMod 4
private def a : K := (0, 2)
private def b : K := (1, 3)
private def c : K := (0, 3)
private def d : K := (1, 1)
private def e : K := (1, 0)
private def f : K := (1, 2)
private def g : K := (0, 1)

private theorem residue01 : (0 : ZMod 4) ≠ 1 := by decide
private theorem residue10 : (1 : ZMod 4) ≠ 0 := by decide
private theorem residue03 : (0 : ZMod 4) ≠ 3 := by decide
private theorem residue12 : (1 : ZMod 4) ≠ 2 := by decide
private theorem residue13 : (1 : ZMod 4) ≠ 3 := by decide
private theorem residue20 : (2 : ZMod 4) ≠ 0 := by decide
private theorem residue21 : (2 : ZMod 4) ≠ 1 := by decide
private theorem residue23 : (2 : ZMod 4) ≠ 3 := by decide
attribute [local simp] residue01 residue10 residue03 residue12 residue13 residue20 residue21 residue23

private def column (i : Fin 7) : K := ![f, g, a, b, c, d, e] i

private def columns : Fin 7 ≃ {x : K // x ≠ 0} where
  toFun i := ⟨column i, by fin_cases i <;> decide⟩
  invFun x := if x.val = f then 0 else
    if x.val = g then 1 else
    if x.val = a then 2 else
    if x.val = b then 3 else
    if x.val = c then 4 else
    if x.val = d then 5 else 6
  left_inv := by decide
  right_inv := by decide

private def P : Equiv.Perm K where
  toFun x := if x = a then b else
    if x = b then c else
    if x = c then d else
    if x = d then e else
    if x = e then f else
    if x = f then g else
    if x = g then a else 0
  invFun x := if x = b then a else
    if x = c then b else
    if x = d then c else
    if x = e then d else
    if x = f then e else
    if x = g then f else
    if x = a then g else 0
  left_inv := by decide
  right_inv := by decide

private def Q : Equiv.Perm K where
  toFun x := P x - x
  invFun x := if x = d then a else
    if x = e then b else
    if x = f then c else
    if x = c then d else
    if x = a then e else
    if x = b then f else
    if x = g then g else 0
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
    have orbit : ∀ i : Fin 7, (P ^ i.val) f = (columns i).val := by decide
    have all (x : K) (hx : x ≠ 0) : P.SameCycle f x := by
      obtain ⟨i, hi⟩ := columns.surjective ⟨x, hx⟩
      refine ⟨(i.val : ℤ), ?_⟩
      rw [zpow_natCast, orbit]
      exact congrArg Subtype.val hi
    exact ⟨bijOn_complement P 0 P_zero, fun x hx y hy => (all x hx).symm.trans (all y hy)⟩

variable {H : Type*} [AddCommGroup H] [Finite H]
attribute [local instance] Classical.propDecidable
local instance : DecidableEq K := fun _ _ => Classical.propDecidable _

private def q (r : RCycle H) (v : H) : H :=
  -(r.successor v - v)

private theorem q_ne_zero (r : RCycle H) {v : H} (hv : v ≠ 0) : q r v ≠ 0 := by
  intro he
  apply successor_ne_self r hv
  have hd0 : r.successor v - v = 0 :=
    neg_eq_zero.mp (show -(r.successor v - v) = 0 from he)
  exact sub_eq_zero.mp hd0

private def shift (r : RCycle H) (v : H) (x : K) : H :=
  if x = 0 then 0 else if x = a then r.successor v else if x = b then 0
  else if x = c then 0 else if x = d then v else if x = e then r.successor v
  else if x = f then r.successor v - r.successor (q r v) else v

private def S0 (r : RCycle H) (v : H) : Equiv.Perm (K × H) :=
  shiftedSuccessor r P (shift r v) e

private def successor (r : RCycle H) (v : H) : Equiv.Perm (K × H) :=
  S0 r v * Equiv.swap (0, v) (g, v) * Equiv.swap (d, v) (e, v)

private def labelSources (v : H) : Equiv.Perm (K × H) :=
  Equiv.swap (0, v) (e, v) * Equiv.swap (g, v) (d, v)

private def difference (r : RCycle H) (hH : Odd (Nat.card H)) (v : H) :
    Equiv.Perm (K × H) :=
  (labelSources v).trans (shiftedDifference r hH P Q (shift r v) e)

private theorem S0_X (r : RCycle H) (v : H) : S0 r v (0, v) = (0, r.successor v) := by
  simp [S0, shiftedSuccessor_apply, shift, row, P_zero]

private theorem S0_Y (r : RCycle H) (v : H) :
    S0 r v (g, v) = (a, r.successor v) := by
  simp [S0, shiftedSuccessor_apply, shift, row, P, a, b, c, d, e, f, g, r.successor_zero]

private theorem S0_Z (r : RCycle H) (v : H) :
    S0 r v (d, v) = (e, r.successor v) := by
  simp [S0, shiftedSuccessor_apply, shift, row, P, a, b, c, d, e, f, g, r.successor_zero]

private theorem S0_W (r : RCycle H) (v : H) :
    S0 r v (e, v) = (f, r.successor v) := by
  simp only [S0, shiftedSuccessor_apply]
  apply Prod.ext
  · norm_num [P, a, b, c, d, e, f, g]
  · change shift r v (P e) + row r e e (v - shift r v e) = r.successor v
    have hp : P e = f := by norm_num [P, a, b, c, d, e, f, g]
    rw [hp]
    have hs : shift r v f = r.successor v - r.successor (q r v) := by
      simp [shift, a, b, c, d, e, f, g]
    have he : shift r v e = r.successor v := by simp [shift, a, b, c, d, e, f, g]
    rw [hs, he]
    have hr : row r e e = r.successor := by simp [row]
    rw [hr]
    have hq : v - r.successor v = q r v := by dsimp [q]; abel
    rw [hq]
    abel

private theorem difference_spec (r : RCycle H) (hH : Odd (Nat.card H)) (v : H)
    (x : K × H) : difference r hH v x = successor r v x - x := by
  change shiftedDifference r hH P Q (shift r v) e (labelSources v x) = _
  rw [shifted_difference_spec r hH P Q (shift r v) e (fun _ => rfl)]
  change S0 r v (labelSources v x) - labelSources v x = successor r v x - x
  have h0Y : (0 : K) ≠ g := by norm_num [g, Prod.ext_iff]
  have h0Z : (0 : K) ≠ d := by norm_num [d, Prod.ext_iff]
  have h0W : (0 : K) ≠ e := by norm_num [e, Prod.ext_iff]
  have hYZ : g ≠ d := by norm_num [g, d, Prod.ext_iff]
  have hYW : g ≠ e := by norm_num [g, e, Prod.ext_iff]
  have hZW : d ≠ e := by norm_num [d, e, Prod.ext_iff]
  by_cases hX : x = (0, v)
  · subst x
    simp [labelSources, successor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Prod.mk.injEq, h0Y, h0Z, h0W, hYZ, hYW, hZW,
      h0Y.symm, h0Z.symm, h0W.symm, hYZ.symm, hYW.symm, hZW.symm,
      S0_X, S0_Y, S0_Z, S0_W] <;>
      norm_num [a, b, c, d, e, f, g, Prod.ext_iff] <;> decide
  by_cases hY : x = (g, v)
  · subst x
    simp [labelSources, successor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Prod.mk.injEq, h0Y, h0Z, h0W, hYZ, hYW, hZW,
      h0Y.symm, h0Z.symm, h0W.symm, hYZ.symm, hYW.symm, hZW.symm,
      S0_X, S0_Y, S0_Z, S0_W] <;>
      norm_num [a, b, c, d, e, f, g, Prod.ext_iff] <;> decide
  by_cases hZ : x = (d, v)
  · subst x
    simp [labelSources, successor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Prod.mk.injEq, h0Y, h0Z, h0W, hYZ, hYW, hZW,
      h0Y.symm, h0Z.symm, h0W.symm, hYZ.symm, hYW.symm, hZW.symm,
      S0_X, S0_Y, S0_Z, S0_W] <;>
      norm_num [a, b, c, d, e, f, g, Prod.ext_iff] <;> decide
  by_cases hW : x = (e, v)
  · subst x
    simp [labelSources, successor, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Prod.mk.injEq, h0Y, h0Z, h0W, hYZ, hYW, hZW,
      h0Y.symm, h0Z.symm, h0W.symm, hYZ.symm, hYW.symm, hZW.symm,
      S0_X, S0_Y, S0_Z, S0_W] <;>
      norm_num [a, b, c, d, e, f, g, Prod.ext_iff] <;> decide
  · simp [labelSources, successor, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hX hY, Equiv.swap_apply_of_ne_of_ne hZ hW,
      Equiv.swap_apply_of_ne_of_ne hX hZ, Equiv.swap_apply_of_ne_of_ne hY hW,
      Equiv.swap_apply_of_ne_of_ne hX hW, Equiv.swap_apply_of_ne_of_ne hY hZ]

private theorem successor_zero (r : RCycle H) {v : H} (hv : v ≠ 0) :
    successor r v 0 = 0 := by
  have hX : (0 : K × H) ≠ (0, v) := by simpa [Prod.ext_iff] using hv.symm
  have hY : (0 : K × H) ≠ (g, v) := by simp [Prod.ext_iff, g]
  have hZ : (0 : K × H) ≠ (d, v) := by simp [Prod.ext_iff, d]
  have hW : (0 : K × H) ≠ (e, v) := by simp [Prod.ext_iff, e]
  simp only [successor, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hZ hW, Equiv.swap_apply_of_ne_of_ne hX hY]
  change S0 r v (0, 0) = 0
  simp [S0, shiftedSuccessor_apply, shift, row_zero, P_zero]

private theorem nonzero_cycle (r : RCycle H) {v : H} (hv : v ≠ 0) :
    (successor r v).IsCycleOn {x | x ≠ 0} := by
  let V := chart columns (shift r v)
  have hX : V (.inl v) = (0, v) := rfl
  have hY : V (.inr (1, 0)) = (g, v) := by
    simp [V, chart_inr, columns, column, shift, gauge_zero, a, b, c, d, e, f, g]
  have hZ : V (.inr (5, 0)) = (d, v) := by
    simp [V, chart_inr, columns, column, shift, gauge_zero, a, b, c, d, e, f, g]
  have hW : V (.inr (6, q r v)) = (e, v) := by
    rw [show V (.inr (6, q r v)) =
      ((columns 6).val, shift r v (columns 6).val + gauge 6 (q r v)) from rfl]
    change (e, shift r v e + q r v) = (e, v)
    have hs : shift r v e = r.successor v := by simp [shift, a, b, c, d, e, f, g]
    rw [hs]
    congr 1
    dsimp [q]
    abel
  have hc := joined_nonzero_cycle r P (shift r v) columns P_zero
    (by simp [shift]) P_column v hv 1 5 6 (q r v) (q_ne_zero r hv)
  dsimp only at hc
  rw [show (columns 6).val = e by rfl] at hc
  change (S0 r v * Equiv.swap (V (.inl v)) (V (.inr (1, 0))) *
    Equiv.swap (V (.inr (5, 0))) (V (.inr (6, q r v)))).IsCycleOn {x | x ≠ 0} at hc
  rw [hX, hY, hZ, hW] at hc
  exact hc

/-- An ordinary R-cycle suffices for every finite odd factor, including the trivial group. -/
def c2c4_odd_product (r : RCycle H) (hH : Odd (Nat.card H)) :
    RCycle ((ZMod 2 × ZMod 4) × H) := by
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

end D5.S3.FiniteGroups.HeadleyC2C4OddProduct
