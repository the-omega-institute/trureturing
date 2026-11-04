/- GID: D5/S3/Combinatorics/Circle/PhysicalJointRepetition/Source
   generality: I
   mirror-B: none(waiver:private-consumed-foundations)
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical block labels, repetition permutation and old-source block scaling. -/

import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.ThreeRowSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.PhysicalJointRepetition

open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators

def blockLabel (d r j : ℕ) (hj : j < r) (i : Fin d) : Fin (d * r) :=
  ⟨j * d + i.val, by
    calc
      j * d + i.val < j * d + d := Nat.add_lt_add_left i.isLt _
      _ = (j + 1) * d := by rw [Nat.succ_mul]
      _ ≤ r * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hj)
      _ = d * r := Nat.mul_comm _ _⟩

def repeatWord (d r : ℕ) (hr : 0 < r) (tau : List (Fin d)) : List (Fin (d * r)) :=
  (List.finRange r).reverse.flatMap (fun j =>
    tau.map (blockLabel d r j.val j.isLt))

private theorem list_prefix_strip {α : Type*} (f : α → ℤ) (B h : ℤ) (l : List α)
    (hl : ∀ n, 0 ≤ h + ((l.take n).map f).sum ∧
      h + ((l.take n).map f).sum ≤ B) :
    InStrip f B h l := by
  induction l generalizing h with
  | nil =>
      simpa [InStrip] using hl 0
  | cons x xs ih =>
      simp only [InStrip]
      refine ⟨?_, ?_, ih (h + f x) ?_⟩
      · simpa using (hl 0).1
      · simpa using (hl 0).2
      intro n
      simpa [List.take_succ_cons, add_assoc] using hl (n + 1)

private theorem map_sum_linear {α : Type*} (l : List α) (f g : α → ℤ) (u v : ℤ) :
    (l.map (fun x => u * f x + v * g x)).sum =
      u * (l.map f).sum + v * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem prefix_nonneg_le {α : Type*} (l : List α) (f : α → ℤ)
    (hf : ∀ x ∈ l, 0 ≤ f x) (n : ℕ) :
    0 ≤ ((l.take n).map f).sum ∧
      ((l.take n).map f).sum ≤ (l.map f).sum := by
  have hleft : 0 ≤ ((l.take n).map f).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf x (List.mem_of_mem_take hx)
  have hright : 0 ≤ ((l.drop n).map f).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf x (List.mem_of_mem_drop hx)
  have hsplit := congrArg (fun s : List α => (s.map f).sum) (List.take_append_drop n l)
  simp only [List.map_append, List.sum_append] at hsplit
  exact ⟨hleft, by omega⟩

private theorem block_perm (d r : ℕ) (hd : 0 < d) (hr : 0 < r) (tau : List (Fin d))
    (htau : tau.Perm (List.finRange d)) :
    (repeatWord d r hr tau).Perm (List.finRange (d * r)) := by
  classical
  let θ : Fin r × Fin d → Fin (d * r) := fun p => blockLabel d r p.1.val p.1.isLt p.2
  have hθ : Function.Injective θ := by
    rintro ⟨j, i⟩ ⟨k, h⟩ he
    have hv := congrArg Fin.val he
    dsimp [θ, blockLabel] at hv
    have hjk : j.val = k.val := by
      have hdivj : (j.val * d + i.val) / d = j.val := by
        apply Nat.div_eq_of_lt_le
        · omega
        · calc
            j.val * d + i.val < j.val * d + d := Nat.add_lt_add_left i.isLt _
            _ = (j.val + 1) * d := by rw [Nat.succ_mul]
      have hdivk : (k.val * d + h.val) / d = k.val := by
        apply Nat.div_eq_of_lt_le
        · omega
        · calc
            k.val * d + h.val < k.val * d + d := Nat.add_lt_add_left h.isLt _
            _ = (k.val + 1) * d := by rw [Nat.succ_mul]
      have hv' := congrArg (fun n => n / d) hv
      rw [hdivj, hdivk] at hv'
      exact hv'
    rw [hjk] at hv
    have hik : i.val = h.val := by omega
    exact Prod.ext (Fin.ext hjk) (Fin.ext hik)
  let row : Fin r → List (Fin (d * r)) := fun j =>
    (List.finRange d).map (fun i => θ (j, i))
  have hcomplete : ((List.finRange r).flatMap row).Perm (List.finRange (d * r)) := by
    have hflatten : (List.finRange r).flatMap (fun j =>
        row j) =
        ((List.finRange r).product (List.finRange d)).map θ := by
      simp only [row, List.product, List.map_flatMap, List.map_map, Function.comp_def]
    rw [hflatten]
    apply (List.perm_ext_iff_of_nodup
      (((List.nodup_finRange r).product (List.nodup_finRange d)).map hθ)
      (List.nodup_finRange _)).mpr
    intro x
    simp only [List.mem_finRange, iff_true]
    let j : Fin r := ⟨x.val / d, by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).2
      simpa [Nat.mul_comm] using x.isLt⟩
    let i : Fin d := ⟨x.val % d, Nat.mod_lt _ hd⟩
    have hdiv := Nat.mod_add_div x.val d
    have hv : θ (j, i) = x := by
      apply Fin.ext
      simpa [θ, blockLabel, j, i, Nat.add_comm, Nat.mul_comm] using hdiv
    exact List.mem_map.mpr ⟨(j, i), by simp, hv⟩
  have hbase : ((List.finRange r).reverse.flatMap row).Perm (List.finRange (d * r)) := by
    exact ((List.reverse_perm _).flatMap_right _).trans hcomplete
  have hblocks : (repeatWord d r hr (List.finRange d)).Perm (List.finRange (d * r)) := by
    change ((List.finRange r).reverse.flatMap
      (fun j => (List.finRange d).map (fun i => θ (j, i)))).Perm _
    exact hbase
  exact (List.Perm.flatMap_left _ (fun j _ => (htau.map _))).trans hblocks

private theorem multiplier_eq_geom (d r : ℕ) (hd : 0 < d) :
    ThreeRowSource.multiplier d r = geom d r := by
  rw [ThreeRowSource.multiplier_quotient d r hd]
  simp [geom, pow_mul, Nat.mul_comm]

private theorem old_value (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (j : Fin r) (i : Fin d) :
    actualSource (d * r) (w * geom d r)
        (blockLabel d r j.val j.isLt i) =
      (geom d r : ℤ) * actualSource d w i := by
  have hmult := ThreeRowSource.repeated_source d r w (by omega) (by omega)
    ⟨(blockLabel d r j.val j.isLt i).val, by
      simpa [Nat.mul_comm] using (blockLabel d r j.val j.isLt i).isLt⟩
  have hmg : ThreeRowSource.multiplier d r = geom d r := multiplier_eq_geom d r (by omega)
  rw [hmg] at hmult
  have hprod := ThreeRowSource.multiplier_identity d r
  rw [hmg] at hprod
  have hG : 0 < geom d r := by
    have hmono := geom_mono d (by omega) (show 1 ≤ r by omega)
    have h1 : geom d 1 = 1 := by
      simp only [geom, pow_one]
      have hp : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
      exact Nat.div_self (by omega)
    have hge : 1 ≤ geom d r := by simpa [h1] using hmono
    exact lt_of_lt_of_le Nat.zero_lt_one hge
  have hwt : w < modulus d := by
    unfold modulus
    have hw' : (w : ℤ) + 1 ≤ (2 : ℤ) ^ (d - 1) := by
      have hp0 : 0 < 2 ^ (d - 1) := pow_pos (by omega) _
      exact_mod_cast (show w + 1 ≤ 2 ^ (d - 1) by omega)
    have hpEq : (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ d := by
      calc
        (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ ((d - 1) + 1) := by
          rw [pow_succ]
        _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
    have hp : (2 : ℤ) ^ (d - 1) ≤ (2 : ℤ) ^ d := by nlinarith [hpEq]
    nlinarith [hp]
  have hlt : w * geom d r < modulus (r * d) := by
    have hh := Int.mul_lt_mul_of_pos_right (show (w : ℤ) < modulus d by exact_mod_cast hwt)
      (by exact_mod_cast hG : (0 : ℤ) < geom d r)
    have heq : modulus d * geom d r = modulus (r * d) := by
      simpa [mul_comm] using hprod
    rw [heq] at hh
    exact hh
  have hltNat : w * geom d r < 2 ^ (r * d) - 1 := by
    have hlt' : (w : ℤ) * (geom d r : ℤ) < (2 : ℤ) ^ (r * d) - 1 := by
      simpa [modulus] using hlt
    have hcast : ((2 ^ (r * d) - 1 : ℕ) : ℤ) =
        (2 : ℤ) ^ (r * d) - 1 := by
      have hp0 : 0 < 2 ^ (r * d) := pow_pos (by omega) _
      rw [Nat.cast_sub hp0]
      norm_num
    rw [← hcast] at hlt'
    exact_mod_cast hlt'
  have hmod : (w * geom d r) % (2 ^ (r * d) - 1) = w * geom d r :=
    Nat.mod_eq_of_lt hltNat
  have hi : ((blockLabel d r j.val j.isLt i).val % d) = i.val := by
    dsimp [blockLabel]
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  have hmod' : (w * geom d r) % (2 ^ (d * r) - 1) = w * geom d r := by
    simpa [Nat.mul_comm] using hmod
  simpa [Nat.mul_comm, hmod, hmod', hi, actualSource] using hmult

private theorem old_block (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (tau : List (Fin d))
    (htau : OriginalOrder d w tau) (j : Fin r) :
    let f := actualSource (d * r) (w * geom d r)
    let B := modulus (d * r) / 2
    InStrip f B 0 (tau.map (blockLabel d r j.val j.isLt)) ∧
      ((tau.map (blockLabel d r j.val j.isLt)).map f).sum = 0 := by
  classical
  dsimp only
  let f := actualSource (d * r) (w * geom d r)
  let a := actualSource d w
  let G : ℤ := geom d r
  have hval (i : Fin d) :
      f (blockLabel d r j.val j.isLt i) = G * a i := by
    exact old_value d r w hd hr hw j i
  have hmodprod : (modulus d : ℤ) * G = modulus (d * r) := by
    have hh := ThreeRowSource.multiplier_identity d r
    have hm := multiplier_eq_geom d r (by omega)
    rw [hm] at hh
    exact_mod_cast (by simpa [G, mul_comm, mul_left_comm, mul_assoc] using hh)
  have hhalfD : 2 * (modulus d / 2) = modulus d - 1 := by
    have ho := (TwoRunSource.modulus_positive_odd d (by omega)).2
    have he := Int.emod_add_mul_ediv (modulus d) 2
    omega
  have hhalfR : 2 * (modulus (d * r) / 2) = modulus (d * r) - 1 := by
    have ho := (TwoRunSource.modulus_positive_odd (d * r)
      (Nat.mul_pos (by omega) (by omega))).2
    have he := Int.emod_add_mul_ediv (modulus (d * r)) 2
    omega
  have hcap : G * (modulus d / 2) ≤ modulus (d * r) / 2 := by
    have hG : 1 ≤ G := by
      have := geom_mono d (by omega) (show 1 ≤ r by omega)
      have h1 : geom d 1 = 1 := by
        simp only [geom, pow_one]
        exact Nat.div_self (by
          have : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
          omega)
      dsimp [G]; omega
    have hB : 0 ≤ (modulus d / 2 : ℤ) := by
      have := (TwoRunSource.modulus_positive_odd d (by omega)).1
      omega
    nlinarith [hmodprod]
  have hstrip : InStrip f (modulus (d * r) / 2) 0
      (tau.map (blockLabel d r j.val j.isLt)) := by
    apply list_prefix_strip f (modulus (d * r) / 2) 0 _
    intro n
    rw [← List.map_take]
    simp only [List.map_map, Function.comp_def]
    have hm : ((tau.take n).map (fun i => f (blockLabel d r j.val j.isLt i))) =
        (tau.take n).map (fun i => G * a i) := by
      apply List.map_congr_left
      intro i hi
      exact hval i
    rw [hm, List.sum_map_mul_left]
    have hs := htau.2.2 n
    simp only [zero_add]
    change 0 ≤ G * ((tau.take n).map a).sum ∧
      G * ((tau.take n).map a).sum ≤ modulus (d * r) / 2
    constructor
    · have hG : 0 ≤ G := by positivity
      nlinarith [hs.1]
    · have hG : 0 ≤ G := by positivity
      have hB0 := hs.2
      change ((tau.take n).map a).sum ≤ modulus d / 2 at hB0
      nlinarith [hcap]
  have hsum : ((tau.map (blockLabel d r j.val j.isLt)).map f).sum = 0 := by
    simp only [List.map_map, Function.comp_def]
    have hmap : tau.map (fun i => f (blockLabel d r j.val j.isLt i)) =
        tau.map (fun i => G * a i) := by
      apply List.map_congr_left
      intro i hi
      exact hval i
    rw [hmap, List.sum_map_mul_left, htau.2.1]
    ring
  exact ⟨hstrip, hsum⟩

end D5.S3.Combinatorics.Circle.PhysicalJointRepetition
