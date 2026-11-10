/- GID: D5/S3/Combinatorics/Circle/PhysicalJointRepetition/Repetition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PhysicalJointRepetition/Repetition
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Explicit descending charged repetition with one literal first-block ear. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.PhysicalJointRepetition

open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators

open private list_prefix_strip map_sum_linear prefix_nonneg_le block_perm old_block
  from D5.S3.Combinatorics.Circle.PhysicalJointRepetition.Source

private theorem shift_source (k t : ℕ) (i : Fin k) :
    actualSource (k + 1) (2 * t) i.castSucc =
      actualSource (k + 1) t ⟨i.val + 1, by omega⟩ := by
  unfold actualSource
  congr 1
  simp only [Fin.val_castSucc, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  ring

private theorem new_regular_value (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (j : Fin r) (i : Fin d) :
    actualSource (d * r + 1) (2 * (w * geom d r))
        (blockLabel d r j.val j.isLt i).castSucc =
        2 * (geom d r : ℤ) * actualSource d w i -
        ((2 : ℤ) ^ i.val * (w : ℤ) * (geom d j.val : ℤ) + charge d w i) := by
  obtain ⟨hdigit, hesum, hx0, hy0, hx, hfsum, hlast⟩ :=
    periodic_source_equations d w r hd hw hr
  have hs := shift_source (d * r) (w * geom d r)
    (blockLabel d r j.val j.isLt i)
  have hh := hx j.val j.isLt i (by
    simpa [blockLabel, Nat.add_comm, Nat.mul_comm] using
      Nat.succ_lt_succ (blockLabel d r j.val j.isLt i).isLt)
  have hcast :
      (⟨(blockLabel d r j.val j.isLt i).val + 1,
        Nat.succ_lt_succ (blockLabel d r j.val j.isLt i).isLt⟩ : Fin (d * r + 1)) =
        ⟨j.val * d + i.val + 1, by
          simpa [blockLabel] using
            Nat.succ_lt_succ (blockLabel d r j.val j.isLt i).isLt⟩ := by
    apply Fin.ext
    rfl
  rw [hs, hcast]
  simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

private theorem new_top_value (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (j : Fin d) :
    actualSource (d * r + 1) (2 * (w * geom d r))
        (blockLabel d r (r - 1) (by omega) j).castSucc =
      ((2 : ℤ) ^ d) ^ (r - 1) *
          actualSource (d + 1) (2 * w) j.castSucc +
        (geom d (r - 1) : ℤ) * actualSource d w j := by
  obtain ⟨hdigit, hesum, hx0, hy0, hx, hfsum, hlast⟩ :=
    periodic_source_equations d w r hd hw hr
  have hs := shift_source (d * r) (w * geom d r)
    (blockLabel d r (r - 1) (by omega) j)
  have hh := hlast j (by
    simpa [blockLabel, Nat.add_comm, Nat.mul_comm] using
      Nat.succ_lt_succ (blockLabel d r (r - 1) (by omega) j).isLt)
  have hcast :
      (⟨(blockLabel d r (r - 1) (by omega) j).val + 1,
        Nat.succ_lt_succ (blockLabel d r (r - 1) (by omega) j).isLt⟩ : Fin (d * r + 1)) =
        ⟨(r - 1) * d + j.val + 1, by
          simpa [blockLabel] using
            Nat.succ_lt_succ (blockLabel d r (r - 1) (by omega) j).isLt⟩ := by
    apply Fin.ext
    dsimp [blockLabel]
  rw [hs, hcast]
  have hshift : actualSource (d + 1) w ⟨j.val + 1, by omega⟩ =
      actualSource (d + 1) (2 * w) j.castSucc := by
    exact (shift_source d w j).symm
  simpa [hshift, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

private def rowCharge (d w j : ℕ) (i : Fin d) : ℤ :=
  (2 : ℤ) ^ i.val * (w : ℤ) * (geom d j : ℤ) + charge d w i

private theorem rowCharge_nonneg (d w j : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (i : Fin d) :
    0 ≤ rowCharge d w j i := by
  dsimp [rowCharge]
  exact add_nonneg (by positivity) (digit_data d w hd hw i).1

private theorem rowCharge_sum (d w j : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) :
    (∑ i : Fin d, rowCharge d w j i) =
      (w : ℤ) * ((2 : ℤ) ^ d) ^ j := by
  have hpow : (∑ i : Fin d, (2 : ℤ) ^ i.val) = (2 : ℤ) ^ d - 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    have h := geom_sum_mul (2 : ℤ) d
    norm_num at h
    exact h
  dsimp [rowCharge]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hpow,
    charge_sum d w hd hw]
  have hg := geom_mul d j (by omega)
  change ((2 : ℤ) ^ d - 1) * (geom d j : ℤ) = ((2 : ℤ) ^ d) ^ j - 1 at hg
  nlinarith

private theorem regular_block (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (tau : List (Fin d))
    (htau : OriginalOrder d w tau) (j : Fin r) (hj : j.val + 1 < r) :
    let f := actualSource (d * r + 1) (2 * (w * geom d r))
    let G : ℤ := geom d r
    let start : ℤ := (w : ℤ) * geom d (j.val + 1)
    let block := (tau.map (blockLabel d r j.val j.isLt)).map Fin.castSucc
    InStrip f (modulus (d * r + 1) / 2) start block ∧
      (block.map f).sum = -(w : ℤ) * ((2 : ℤ) ^ d) ^ j.val := by
  classical
  dsimp only
  let f := actualSource (d * r + 1) (2 * (w * geom d r))
  let G : ℤ := geom d r
  let start : ℤ := (w : ℤ) * geom d (j.val + 1)
  let block := (tau.map (blockLabel d r j.val j.isLt)).map Fin.castSucc
  let a := actualSource d w
  have hval (i : Fin d) :
      f (blockLabel d r j.val j.isLt i).castSucc =
        2 * G * a i - rowCharge d w j.val i := by
    simpa [G, rowCharge] using new_regular_value d r w hd hr hw j i
  have hsumF : (∑ i : Fin d, rowCharge d w j.val i) =
      (w : ℤ) * ((2 : ℤ) ^ d) ^ j.val :=
    rowCharge_sum d w j.val hd hw
  have hnonneg (i : Fin d) : 0 ≤ rowCharge d w j.val i :=
    rowCharge_nonneg d w j.val hd hw i
  have hpartial (n : ℕ) :
      0 ≤ ((tau.take n).map (rowCharge d w j.val)).sum ∧
      ((tau.take n).map (rowCharge d w j.val)).sum ≤
        (w : ℤ) * ((2 : ℤ) ^ d) ^ j.val := by
    have hp := prefix_nonneg_le tau (rowCharge d w j.val)
      (fun i hi => hnonneg i) n
    have htotal :
        (tau.map (rowCharge d w j.val)).sum =
          (w : ℤ) * ((2 : ℤ) ^ d) ^ j.val := by
      rw [(htau.1.map (rowCharge d w j.val)).sum_eq]
      rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
      exact hsumF
    refine ⟨hp.1, ?_⟩
    rw [← htotal]
    exact hp.2
  have hprefix (n : ℕ) :
      ((block.take n).map f).sum =
        2 * G * ((tau.take n).map a).sum -
          ((tau.take n).map (rowCharge d w j.val)).sum := by
    have htake : block.take n =
        (tau.take n).map (fun i => (blockLabel d r j.val j.isLt i).castSucc) := by
      simpa only [block, ← List.map_take, List.map_map, Function.comp_def]
    rw [htake]
    rw [List.map_map]
    simp only [Function.comp_def]
    have hmap : (tau.take n).map (fun i => f (blockLabel d r j.val j.isLt i).castSucc) =
        (tau.take n).map (fun i => 2 * G * a i - rowCharge d w j.val i) := by
      apply List.map_congr_left
      intro i hi
      exact hval i
    rw [hmap]
    have hm := map_sum_linear (tau.take n) a (rowCharge d w j.val) (2 * G) (-1)
    simpa [sub_eq_add_neg, mul_assoc] using hm
  have hbase := htau.2.2
  have hstrip : InStrip f (modulus (d * r + 1) / 2) start block := by
    apply list_prefix_strip f (modulus (d * r + 1) / 2) start block
    intro n
    rw [hprefix]
    have hs := hbase n
    have hf := hpartial n
    have hB : modulus d / 2 = (2 : ℤ) ^ (d - 1) - 1 := by
      unfold modulus
      have hp : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
        conv_lhs => rw [show d = d - 1 + 1 by omega, pow_succ]
        ring
      rw [hp]
      omega
    have hG : 0 ≤ G := by positivity
    have hq : (4 : ℤ) ≤ (2 : ℤ) ^ d := by
      exact_mod_cast (show 4 ≤ 2 ^ d by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hd
        norm_num at this
        exact this)
    have hH : 0 ≤ start := by dsimp [start]; positivity
    have hcap :
        start + 2 * G * (modulus d / 2) ≤ modulus (d * r + 1) / 2 := by
      have hmod := (periodic_source_equations d w r hd hw hr).2.2.1
      have hgeom := geom_mul d r (by omega)
      have hhalf : modulus (d * r + 1) / 2 =
          ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) := by
        rw [modulus]
        have hp : (2 : ℤ) ^ (d * r + 1) = 2 * ((2 : ℤ) ^ d) ^ r := by
          rw [pow_succ, pow_mul]
          ring
        rw [hp]
        change (2 * ((2 : ℤ) ^ d) ^ r - 1) / 2 = _
        change ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) = _ at hgeom
        have hQ : ((2 : ℤ) ^ d) ^ r =
            ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) + 1 := by
          nlinarith [hgeom]
        rw [hQ]
        omega
      rw [hhalf]
      dsimp [start, G]
      have hmono := geom_mono d (by omega)
        (show j.val + 1 ≤ r - 1 by omega)
      have hsucc := geom_succ d (r - 1) (by omega)
      rw [show r - 1 + 1 = r by omega] at hsucc
      have hw0 : 0 ≤ (w : ℤ) := Int.natCast_nonneg _
      have hwq : (w : ℤ) ≤ (2 : ℤ) ^ d - 1 := by
        have hw' : (w : ℤ) ≤ (2 : ℤ) ^ (d - 1) - 1 := by
          have hwNat : w ≤ 2 ^ (d - 1) - 1 := hw
          have hwCast : (w : ℤ) ≤ ((2 ^ (d - 1) - 1 : ℕ) : ℤ) := by
            exact_mod_cast hwNat
          have hcast : ((2 ^ (d - 1) - 1 : ℕ) : ℤ) =
              (2 : ℤ) ^ (d - 1) - 1 := by
            have hp0 : 0 < 2 ^ (d - 1) := pow_pos (by omega) _
            rw [Nat.cast_sub (by omega)]
            norm_num
          rwa [hcast] at hwCast
        have hp : (2 : ℤ) ^ (d - 1) ≤ (2 : ℤ) ^ d := by
          have he : (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ d := by
            calc
              (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ ((d - 1) + 1) := by rw [pow_succ]
              _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
          nlinarith [he]
        omega
      have hrel : (geom d r : ℤ) =
          (geom d (r - 1) : ℤ) + ((2 : ℤ) ^ d) ^ (r - 1) := hsucc
      have hB : 2 * ((2 : ℤ) ^ (d - 1) - 1) = (2 : ℤ) ^ d - 2 := by
        have he : (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ d := by
          calc
            (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ ((d - 1) + 1) := by rw [pow_succ]
            _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
        nlinarith [he]
      have hp : (2 : ℤ) ^ (d - 1) ≤ (2 : ℤ) ^ d := by
        have he : (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ d := by
          calc
            (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ ((d - 1) + 1) := by rw [pow_succ]
            _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
        nlinarith [he]
      have hwB : (w : ℤ) + (2 : ℤ) ^ (d - 1) - 1 ≤ (2 : ℤ) ^ d - 2 := by
        have hw' : (w : ℤ) ≤ (2 : ℤ) ^ (d - 1) - 1 := by
          have hwNat : w ≤ 2 ^ (d - 1) - 1 := hw
          have hwCast : (w : ℤ) ≤ ((2 ^ (d - 1) - 1 : ℕ) : ℤ) := by exact_mod_cast hwNat
          have hcast : ((2 ^ (d - 1) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (d - 1) - 1 := by
            have hp0 : 0 < 2 ^ (d - 1) := pow_pos (by omega) _
            rw [Nat.cast_sub (by omega)]; norm_num
          rwa [hcast] at hwCast
        nlinarith [hw', hp]
      have hstart : (w : ℤ) * geom d (j.val + 1) ≤
          (w : ℤ) * geom d (r - 1) := by
        have hmono' : (geom d (j.val + 1) : ℤ) ≤ geom d (r - 1) := by
          exact_mod_cast hmono
        exact mul_le_mul_of_nonneg_left hmono' hw0
      have hBmod : modulus d / 2 = (2 : ℤ) ^ (d - 1) - 1 := by
        unfold modulus
        have he : (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ d := by
          calc
            (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ ((d - 1) + 1) := by rw [pow_succ]
            _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
        omega
      have hgeom_prev : ((2 : ℤ) ^ d - 1) * (geom d (r - 1) : ℤ) =
          ((2 : ℤ) ^ d) ^ (r - 1) - 1 := by
        have hh := geom_mul d (r - 1) (by omega)
        change ((2 : ℤ) ^ d - 1) * (geom d (r - 1) : ℤ) =
          ((2 : ℤ) ^ d) ^ (r - 1) - 1 at hh
        exact hh
      have hAq : (2 : ℤ) * (2 : ℤ) ^ (d - 1) = (2 : ℤ) ^ d := by
        calc
          (2 : ℤ) * (2 : ℤ) ^ (d - 1) = (2 : ℤ) ^ ((d - 1) + 1) := by
            rw [pow_succ]
            ring
          _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
      have hwA : (w : ℤ) ≤ (2 : ℤ) ^ (d - 1) - 1 := by
        have hwNat : w ≤ 2 ^ (d - 1) - 1 := hw
        have hwCast : (w : ℤ) ≤ ((2 ^ (d - 1) - 1 : ℕ) : ℤ) := by
          exact_mod_cast hwNat
        have hcast : ((2 ^ (d - 1) - 1 : ℕ) : ℤ) =
            (2 : ℤ) ^ (d - 1) - 1 := by
          have hp0 : 0 < 2 ^ (d - 1) := by positivity
          rw [Nat.cast_sub (by omega)]
          norm_num
        rwa [hcast] at hwCast
      have hwh : (w : ℤ) * (geom d (r - 1) : ℤ) ≤
          (geom d r : ℤ) := by
        have hH0 : 0 ≤ (geom d (r - 1) : ℤ) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hwA hH0
        nlinarith [hmul, hgeom_prev, hAq, hrel]
      nlinarith [hstart, hwh, hB, hBmod]
    constructor
    · have hG0 : 0 ≤ 2 * G := by positivity
      have hterm : 0 ≤ 2 * G * ((tau.take n).map a).sum :=
        mul_nonneg hG0 hs.1
      have hstart0 : 0 ≤ start := by dsimp [start]; positivity
      have hgeomj := geom_succ d j.val (by omega)
      have hstart_charge : (w : ℤ) * ((2 : ℤ) ^ d) ^ j.val ≤ start := by
        dsimp [start]
        have hw0 : 0 ≤ (w : ℤ) := by positivity
        have hgeomj' : (geom d (j.val + 1) : ℤ) =
            (geom d j.val : ℤ) + ((2 : ℤ) ^ d) ^ j.val := by
          simpa using hgeomj
        nlinarith
      have hsub : 0 ≤ start -
          ((tau.take n).map (rowCharge d w j.val)).sum := by
        nlinarith [hstart_charge, hf.2]
      nlinarith [hterm, hsub]
    · have hG0 : 0 ≤ 2 * G := by positivity
      have hterm := mul_le_mul_of_nonneg_left hs.2 hG0
      nlinarith [hterm, hf.1, hcap]
  have hsum : (block.map f).sum = -(w : ℤ) * ((2 : ℤ) ^ d) ^ j.val := by
    have hmapfull : block.map f =
        tau.map (fun i => f (blockLabel d r j.val j.isLt i).castSucc) := by
      simp [block, List.map_map, Function.comp_def]
    rw [hmapfull]
    have hm := map_sum_linear tau a (rowCharge d w j.val) (2 * G) (-1)
    have hmap : tau.map (fun i => f (blockLabel d r j.val j.isLt i).castSucc) =
        tau.map (fun i => 2 * G * a i - rowCharge d w j.val i) := by
      apply List.map_congr_left
      intro i hi
      exact hval i
    rw [hmap]
    rw [show (fun i => 2 * G * a i - rowCharge d w j.val i) =
      (fun i => (2 * G) * a i + (-1) * rowCharge d w j.val i) by
        funext i; ring]
    rw [hm]
    have hbase0 : (tau.map a).sum = 0 := by
      simpa [a] using htau.2.1
    have hcharges : (tau.map (rowCharge d w j.val)).sum =
        (∑ i : Fin d, rowCharge d w j.val i) := by
      rw [(htau.1.map (rowCharge d w j.val)).sum_eq]
      rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    rw [hbase0, hcharges, hsumF]
    ring
  exact ⟨hstrip, hsum⟩

private theorem ear_prefix_formula (d : ℕ) (sigma : List (Fin d)) (cut : ℕ)
    (hcut : cut ≤ sigma.length) (f : Fin (d + 1) → ℤ) (n : ℕ) :
    (((earWord d sigma cut).take n).map f).sum =
      ((sigma.take (if n ≤ cut then n else n - 1)).map
        (fun i => f i.castSucc)).sum +
        (if n ≤ cut then 0 else f (Fin.last d)) := by
  induction sigma generalizing cut n with
  | nil =>
      have : cut = 0 := by simpa using hcut
      subst cut
      cases n <;> simp [earWord]
  | cons x xs ih =>
      cases cut with
      | zero =>
          cases n with
          | zero => simp [earWord]
          | succ n => simp [earWord, List.map_map, Function.comp_def, add_comm]
      | succ cut =>
          have hcut' : cut ≤ xs.length := by simpa using hcut
          cases n with
          | zero => simp [earWord]
          | succ n =>
              have he := ih cut hcut' n
              simp only [earWord, List.take_succ_cons, List.drop_succ_cons,
                List.map_cons, List.cons_append, List.sum_cons] at he ⊢
              split_ifs with hn
              · have hn' : n ≤ cut := by omega
                simpa [hn', List.take_succ_cons, List.sum_cons, add_assoc] using
                  congrArg (f x.castSucc + ·) he
              · have hn' : ¬ n ≤ cut := by omega
                simpa [hn', show n + 1 - 1 = (n - 1) + 1 by omega,
                  List.take_succ_cons, List.sum_cons, add_assoc] using
                  congrArg (f x.castSucc + ·) he

private theorem blocks_concat {α β : Type*} (f : β → ℤ) (B : ℤ)
    (rows : List α) (block : α → List β)
    (hB : 0 ≤ B)
    (hstrip : ∀ x ∈ rows, InStrip f B 0 (block x))
    (hsum : ∀ x ∈ rows, ((block x).map f).sum = 0) :
    InStrip f B 0 (rows.flatMap block) := by
  induction rows with
  | nil => exact ⟨by omega, hB⟩
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      have htail := ih
        (fun y hy => hstrip y (by simp [hy]))
        (fun y hy => hsum y (by simp [hy]))
      have htail' : InStrip f B (0 + ((block x).map f).sum)
          (xs.flatMap block) := by
        simpa [hsum x (by simp)] using htail
      exact inStrip_append (hstrip x (by simp)) htail'

private theorem blocks_sum {α β : Type*} (f : β → ℤ) (rows : List α)
    (block : α → List β) (hsum : ∀ x ∈ rows, ((block x).map f).sum = 0) :
    ((rows.flatMap block).map f).sum = 0 := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      rw [hsum x (by simp), ih (fun y hy => hsum y (by simp [hy]))]
      ring

private theorem centered_nat_value (k t : ℕ) (hk : 0 < k)
    (ht0 : 0 ≤ (t : ℤ)) (hthalf : (t : ℤ) ≤ modulus k / 2) :
    centered (modulus k) (t : ℤ) = (t : ℤ) := by
  obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd k hk
  apply centered_unique hN ho (centered_bounds hN ho _) ?_ ?_
  · exact ⟨by omega, hthalf⟩
  · rw [centered_mod]

private theorem base_fresh_value (d w : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) :
    actualSource (d + 1) (2 * w) (Fin.last d) = (w : ℤ) := by
  change centered (modulus (d + 1)) ((2 : ℤ) ^ d * (2 * (w : ℕ))) = (w : ℤ)
  have hpow : (2 : ℤ) ^ d * (2 * (w : ℕ)) =
      (2 : ℤ) ^ (d + 1) * (w : ℕ) := by
    rw [pow_succ]
    ring
  rw [hpow, centered_full_period]
  have hhalf : modulus (d + 1) / 2 = (2 : ℤ) ^ d - 1 := by
    unfold modulus
    rw [pow_succ]
    omega
  apply centered_nat_value (d + 1) w (by omega) (by positivity)
  rw [hhalf]
  have hw' : (w : ℤ) ≤ (2 : ℤ) ^ (d - 1) - 1 := by
    have hwNat : w ≤ 2 ^ (d - 1) - 1 := hw
    have hwCast : (w : ℤ) ≤ ((2 ^ (d - 1) - 1 : ℕ) : ℤ) := by
      exact_mod_cast hwNat
    have hcast : ((2 ^ (d - 1) - 1 : ℕ) : ℤ) =
        (2 : ℤ) ^ (d - 1) - 1 := by
      have hp0 : 0 < 2 ^ (d - 1) := by positivity
      rw [Nat.cast_sub (by omega)]
      norm_num
    rwa [hcast] at hwCast
  have hpow : (2 : ℤ) ^ (d - 1) ≤ (2 : ℤ) ^ d := by
    have hp : (0 : ℤ) ≤ (2 : ℤ) ^ (d - 1) := by positivity
    have he : (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ d := by
      calc
        (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ ((d - 1) + 1) := by rw [pow_succ]
        _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
    nlinarith [he]
  omega

private theorem top_block (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (tau : List (Fin d)) (cut : ℕ)
    (htau : OriginalOrder d w tau)
    (hnew : OriginalOrder (d + 1) (2 * w) (earWord d tau cut))
    (hcut : cut ≤ d) :
    let f := actualSource (d * r + 1) (2 * (w * geom d r))
    let top := tau.map (blockLabel d r (r - 1) (by omega))
    let block := earWord (d * r) top cut
    InStrip f (modulus (d * r + 1) / 2) 0 block ∧
      (block.map f).sum = (w : ℤ) * geom d (r - 1) := by
  classical
  dsimp only
  let f := actualSource (d * r + 1) (2 * (w * geom d r))
  let top := tau.map (blockLabel d r (r - 1) (by omega))
  let block := earWord (d * r) top cut
  let a := actualSource d w
  let g := actualSource (d + 1) (2 * w)
  let R : ℤ := ((2 : ℤ) ^ d) ^ (r - 1)
  let H : ℤ := geom d (r - 1)
  let G : ℤ := geom d r
  have htau_len : tau.length = d := by simpa using htau.1.length_eq
  have htop (i : Fin d) :
      f (blockLabel d r (r - 1) (by omega) i).castSucc = R * g i.castSucc + H * a i := by
    simpa [R, H, G] using new_top_value d r w hd hr hw i
  have htopfresh : f (Fin.last (d * r)) = (w : ℤ) * G := by
    unfold f
    change centered (modulus (d * r + 1))
      ((2 : ℤ) ^ (d * r) * (2 * (w * geom d r : ℕ))) = (w : ℤ) * G
    have hp : (2 : ℤ) ^ (d * r) * (2 * (w * geom d r : ℕ)) =
        (2 : ℤ) ^ (d * r + 1) * (w * geom d r : ℕ) := by
      rw [pow_succ]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hp, centered_full_period]
    have hhalf : modulus (d * r + 1) / 2 =
        ((2 : ℤ) ^ d) ^ r - 1 := by
      unfold modulus
      rw [pow_succ, pow_mul]
      omega
    have hG0 : 0 ≤ (w : ℤ) * (geom d r : ℤ) := by positivity
    have hGcap : (w : ℤ) * (geom d r : ℤ) ≤ ((2 : ℤ) ^ d) ^ r - 1 := by
      have hprod := geom_mul d r (by omega)
      have hwlt : (w : ℤ) < (2 : ℤ) ^ d - 1 := by
        have hp0Nat : 0 < 2 ^ (d - 1) := by positivity
        have hpNat : 1 ≤ 2 ^ (d - 1) := by omega
        have hwNat : w + 1 ≤ 2 ^ (d - 1) := by omega
        have hw' : (w : ℤ) + 1 ≤ (2 : ℤ) ^ (d - 1) := by
          exact_mod_cast hwNat
        have hp2 : (2 : ℤ) ^ (d - 1) ≤ (2 : ℤ) ^ d := by
          have he : (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ d := by
            calc
              (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ ((d - 1) + 1) := by rw [pow_succ]
              _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
          nlinarith [he]
        have hApos : (0 : ℤ) < (2 : ℤ) ^ (d - 1) := by positivity
        have hplt : (2 : ℤ) ^ (d - 1) < (2 : ℤ) ^ d := by
          have he : (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ d := by
            calc
              (2 : ℤ) ^ (d - 1) * 2 = (2 : ℤ) ^ ((d - 1) + 1) := by rw [pow_succ]
              _ = (2 : ℤ) ^ d := by rw [show d - 1 + 1 = d by omega]
          nlinarith [he]
        omega
      have hgeompos : (0 : ℤ) < (geom d r : ℤ) := by
        have hmono := geom_mono d (by omega) (show 1 ≤ r by omega)
        have h1 : geom d 1 = 1 := by
          simp only [geom, pow_one]
          exact Nat.div_self (by
            have : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
            omega)
        have hge : 1 ≤ geom d r := by simpa [h1] using hmono
        exact_mod_cast (show 0 < geom d r by omega)
      have hmul := Int.mul_lt_mul_of_pos_right hwlt hgeompos
      have hprod' : ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) =
          ((2 : ℤ) ^ d) ^ r - 1 := hprod
      nlinarith [hmul, hprod']
    apply centered_nat_value (d * r + 1) (w * geom d r) (by omega) (by positivity)
    rw [hhalf]
    simpa [Nat.cast_mul] using hGcap
  have hformula (n : ℕ) :
      ((block.take n).map f).sum =
        R * (((earWord d tau cut).take n).map (actualSource (d + 1) (2 * w))).sum +
        H * ((tau.take (if n ≤ cut then n else n - 1)).map a).sum +
        (if n ≤ cut then 0 else H * (w : ℤ)) := by
    rw [ear_prefix_formula (d * r) top cut (by simpa [top, htau_len] using hcut) f n]
    rw [htopfresh]
    rw [ear_prefix_formula d tau cut (by simpa [htau_len] using hcut) g n]
    have hfresh : g (Fin.last d) = (w : ℤ) := by
      simpa [g] using base_fresh_value d w hd hw
    rw [hfresh]
    rw [← List.map_take, List.map_map]
    simp only [Function.comp_def]
    have hmap :
        (tau.take (if n ≤ cut then n else n - 1)).map
            (fun i => f (blockLabel d r (r - 1) (by omega) i).castSucc) =
          (tau.take (if n ≤ cut then n else n - 1)).map
            (fun i => R * g i.castSucc + H * a i) := by
      apply List.map_congr_left
      intro i hi
      exact htop i
    rw [hmap]
    rw [map_sum_linear]
    -- The two projections are exactly the corresponding prefix of `tau`.
    have hrel0 : G = R + H := by
      have hh := geom_succ d (r - 1) (by omega)
      rw [show r - 1 + 1 = r by omega] at hh
      dsimp [G, R, H]
      nlinarith
    by_cases hn : n ≤ cut <;> simp [hn] <;> nlinarith [hrel0]
  have hstrip : InStrip f (modulus (d * r + 1) / 2) 0 block := by
    apply list_prefix_strip f (modulus (d * r + 1) / 2) 0 block
    intro n
    rw [hformula]
    have hn := hnew.2.2 n
    have ho := htau.2.2 (if n ≤ cut then n else n - 1)
    have hnewB : modulus (d + 1) / 2 = (2 : ℤ) ^ d - 1 := by
      unfold modulus
      rw [pow_succ]
      omega
    rw [hnewB] at hn
    have holdB : modulus d / 2 = (2 : ℤ) ^ (d - 1) - 1 := by
      unfold modulus
      have hp : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
        conv_lhs => rw [show d = d - 1 + 1 by omega, pow_succ]
        ring
      rw [hp]
      omega
    have htopB : modulus (d * r + 1) / 2 =
        ((2 : ℤ) ^ d - 1) * G := by
      unfold modulus
      have hp : (2 : ℤ) ^ (d * r + 1) = 2 * ((2 : ℤ) ^ d) ^ r := by
        rw [pow_succ, pow_mul]
        ring
      rw [hp]
      have hg := geom_mul d r (by omega)
      change ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) = ((2 : ℤ) ^ d) ^ r - 1 at hg
      have hQ : ((2 : ℤ) ^ d) ^ r =
          ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) + 1 := by
        nlinarith [hg]
      dsimp [G]
      rw [hQ]
      omega
    rw [htopB]
    have hR : 0 ≤ R := by positivity
    have hH : 0 ≤ H := by positivity
    have hG : 0 ≤ G := by positivity
    have hsumh : ((tau.take (if n ≤ cut then n else n - 1)).map a).sum ≤
        (2 : ℤ) ^ (d - 1) - 1 := by simpa [holdB] using ho.2
    have hrel : G = R + H := by
      have hh := geom_succ d (r - 1) (by omega)
      rw [show r - 1 + 1 = r by omega] at hh
      dsimp [G, R, H]
      nlinarith
    have hq : (4 : ℤ) ≤ (2 : ℤ) ^ d := by
      have hqNat := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hd
      norm_num at hqNat
      exact_mod_cast hqNat
    have hellw : (2 : ℤ) ^ (d - 1) - 1 + (w : ℤ) ≤ (2 : ℤ) ^ d - 2 := by
      have hp : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
        conv_lhs => rw [show d = d - 1 + 1 by omega, pow_succ]
        ring
      have hw' : (w : ℤ) ≤ (2 : ℤ) ^ (d - 1) - 1 := by
        have hwNat : w ≤ 2 ^ (d - 1) - 1 := hw
        have hwCast : (w : ℤ) ≤ ((2 ^ (d - 1) - 1 : ℕ) : ℤ) := by
          exact_mod_cast hwNat
        have hcast : ((2 ^ (d - 1) - 1 : ℕ) : ℤ) =
            (2 : ℤ) ^ (d - 1) - 1 := by
          have hp0 : 0 < 2 ^ (d - 1) := by positivity
          rw [Nat.cast_sub (by omega)]
          norm_num
        rwa [hcast] at hwCast
      rw [hp]
      omega
    have hcap : R * ((2 : ℤ) ^ d - 1) +
          H * ((2 : ℤ) ^ (d - 1) - 1 + (w : ℤ)) ≤
          ((2 : ℤ) ^ d - 1) * G := by
      have hcoef : (2 : ℤ) ^ (d - 1) - 1 + (w : ℤ) ≤
          (2 : ℤ) ^ d - 1 := by omega
      have hmul := mul_le_mul_of_nonneg_left hcoef hH
      nlinarith [hrel, hmul]
    by_cases hnc : n ≤ cut
    · simp only [if_pos hnc]
      have hnewlo : 0 ≤ R *
          (((earWord d tau cut).take n).map (actualSource (d + 1) (2 * w))).sum :=
        mul_nonneg hR hn.1
      have holdlo : 0 ≤ H *
          ((tau.take (if n ≤ cut then n else n - 1)).map a).sum :=
        mul_nonneg hH ho.1
      have hnewhi : R *
          (((earWord d tau cut).take n).map (actualSource (d + 1) (2 * w))).sum ≤
          R * ((2 : ℤ) ^ d - 1) :=
        mul_le_mul_of_nonneg_left hn.2 hR
      have holdhi : H *
          ((tau.take (if n ≤ cut then n else n - 1)).map a).sum ≤
          H * ((2 : ℤ) ^ (d - 1) - 1) := by
        have hh := mul_le_mul_of_nonneg_left ho.2 hH
        simpa [holdB] using hh
      simp only [if_pos hnc] at holdlo holdhi
      constructor <;> nlinarith [hnewlo, holdlo, hnewhi, holdhi, hcap]
    · simp only [if_neg hnc]
      have hnewlo : 0 ≤ R *
          (((earWord d tau cut).take n).map (actualSource (d + 1) (2 * w))).sum :=
        mul_nonneg hR hn.1
      have holdlo : 0 ≤ H *
          ((tau.take (if n ≤ cut then n else n - 1)).map a).sum :=
        mul_nonneg hH ho.1
      have hHw : 0 ≤ H * (w : ℤ) := mul_nonneg hH (by positivity)
      have hnewhi : R *
          (((earWord d tau cut).take n).map (actualSource (d + 1) (2 * w))).sum ≤
          R * ((2 : ℤ) ^ d - 1) :=
        mul_le_mul_of_nonneg_left hn.2 hR
      have holdhi : H *
          ((tau.take (if n ≤ cut then n else n - 1)).map a).sum ≤
          H * ((2 : ℤ) ^ (d - 1) - 1) := by
        have hh := mul_le_mul_of_nonneg_left ho.2 hH
        simpa [holdB] using hh
      simp only [if_neg hnc] at holdlo holdhi
      constructor <;> nlinarith [hnewlo, holdlo, hHw, hnewhi, holdhi, hcap]
  have hsum : (block.map f).sum = (w : ℤ) * H := by
    have htop_len : top.length = d := by
      simpa [top] using htau.1.length_eq
    have hblock_len : block.length = d + 1 := by
      simp only [block, earWord, List.length_append, List.length_map,
        List.length_cons, List.length_nil, List.length_take, List.length_drop]
      omega
    have hear_len : (earWord d tau cut).length = d + 1 := by
      simp only [earWord, List.length_append, List.length_map,
        List.length_cons, List.length_nil, List.length_take, List.length_drop,
        htau_len]
      omega
    have htake_block : block.take (d + 1) = block := by
      simpa [hblock_len] using (List.take_length block)
    have htake_ear : (earWord d tau cut).take (d + 1) = earWord d tau cut := by
      simpa [hear_len] using (List.take_length (earWord d tau cut))
    have hf := hformula (d + 1)
    have hformula_full :
        (block.map f).sum =
          R * ((earWord d tau cut).map g).sum +
            H * ((tau.take d).map a).sum + H * (w : ℤ) := by
      simpa [htake_block, htake_ear, show ¬ d + 1 ≤ cut by omega,
        show d + 1 - 1 = d by omega] using hf
    rw [hformula_full, hnew.2.1]
    have holdsum : ((tau.take d).map a).sum = 0 := by
      have htake : tau.take d = tau := by
        simpa [show tau.length = d by simpa using htau.1.length_eq] using
          (List.take_length tau)
      rw [htake]
      simpa [a] using htau.2.1
    rw [holdsum]
    ring
  exact ⟨hstrip, hsum⟩

private def lowerBlocks (d r : ℕ) (hr : 2 ≤ r) (tau : List (Fin d)) :
    List (Fin (d * r)) :=
  (List.finRange (r - 1)).reverse.flatMap (fun j =>
    tau.map (blockLabel d r j.val (by omega)))

private theorem lower_aux (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (tau : List (Fin d))
    (htau : OriginalOrder d w tau) :
    ∀ (n : ℕ) (hnr : n + 1 < r) (hn : n + 2 ≤ r),
      let f := actualSource (d * r + 1) (2 * (w * geom d r))
      let rows := (List.finRange (n + 1)).reverse
      let block := fun j : Fin (n + 1) =>
        (tau.map (blockLabel d r j.val
          (lt_trans j.isLt hnr))).map Fin.castSucc
      InStrip f (modulus (d * r + 1) / 2)
        ((w : ℤ) * geom d (n + 1)) (rows.flatMap block) ∧
      ((rows.flatMap block).map f).sum =
        -(w : ℤ) * geom d (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro hnr hn
      dsimp only
      have hj0 : (0 : ℕ) < r := by omega
      have hjr : (0 : ℕ) + 1 < r := by omega
      have hb := regular_block d r w hd hr hw tau htau
        ⟨0, hj0⟩ hjr
      rw [List.finRange_succ_last (n := 0), List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.flatMap_cons,
        List.flatMap_nil, List.map_nil, List.append_nil]
      refine ⟨?_, ?_⟩
      · simpa using hb.1
      · have hgeom1 : geom d 1 = 1 := by
          simp only [geom, pow_one]
          exact Nat.div_self (by
            have : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
            omega)
        simpa [hgeom1] using hb.2
  | succ n ih =>
      intro hnr hn
      dsimp only
      have hb := regular_block d r w hd hr hw tau htau
        ⟨n + 1, by omega⟩ (by omega)
      have htail := ih (by omega) (by omega)
      rw [List.finRange_succ_last (n := n + 1), List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.flatMap_cons]
      have hgeom : (geom d (n + 2) : ℤ) =
          (geom d (n + 1) : ℤ) + ((2 : ℤ) ^ d) ^ (n + 1) := by
        have hh := geom_succ d (n + 1) (by omega)
        simpa [show n + 1 + 1 = n + 2 by omega] using hh
      have hstart :
          (w : ℤ) * geom d (n + 2) +
              (-(w : ℤ) * ((2 : ℤ) ^ d) ^ (n + 1)) =
            (w : ℤ) * geom d (n + 1) := by
        rw [hgeom]
        ring
      have hbSum :
          (tau.map (fun x =>
            actualSource (d * r + 1) (2 * (w * geom d r))
              ((blockLabel d r (n + 1) (by omega) x).castSucc))).sum =
            -(w : ℤ) * ((2 : ℤ) ^ d) ^ (n + 1) := by
        simpa only [List.map_map, Function.comp_def, Fin.val_last] using hb.2
      constructor
      · apply inStrip_append hb.1
        rw [← List.map_reverse, List.flatMap_map]
        simp only [List.map_map, Function.comp_def, Fin.val_last]
        rw [hbSum, hstart]
        simpa only [List.map_reverse, List.flatMap_map, List.map_map,
          Function.comp_def, Fin.val_castSucc] using htail.1
      · simp only [List.map_append, List.sum_append]
        rw [← List.map_reverse, List.flatMap_map]
        have htailSum := htail.2
        simp only [List.map_map, Function.comp_def, Fin.val_castSucc] at htailSum
        simp only [List.map_map, Function.comp_def, Fin.val_last]
        have htailSum' :
            (List.map (actualSource (d * r + 1) (2 * (w * geom d r)))
              (List.flatMap
                (fun a => List.map
                  (fun x => (blockLabel d r a.castSucc.val (by omega) x).castSucc)
                  tau)
                (List.finRange (n + 1)).reverse)).sum =
              -(w : ℤ) * geom d (n + 1) := by
          simpa only [Fin.val_castSucc] using htailSum
        rw [hbSum]
        rw [htailSum', hgeom]
        ring

private theorem repeat_split (d r : ℕ) (hr : 2 ≤ r) (tau : List (Fin d)) :
    repeatWord d r (by omega) tau =
      tau.map (blockLabel d r (r - 1) (by omega)) ++
        lowerBlocks d r hr tau := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  unfold repeatWord lowerBlocks
  have hfr : List.finRange (s + 1) =
      (List.finRange s).map Fin.castSucc ++
        [Fin.last s] := List.finRange_succ_last
  rw [hfr, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append, List.flatMap_cons,
    List.flatMap_nil, List.map_nil, List.append_nil]
  rw [← List.map_reverse, List.flatMap_map]
  simp [Fin.val_castSucc]

private theorem earWord_append (k : ℕ) (sigma rho : List (Fin k)) (cut : ℕ)
    (hcut : cut ≤ sigma.length) :
    earWord k (sigma ++ rho) cut = earWord k sigma cut ++ rho.map Fin.castSucc := by
  unfold earWord
  rw [List.take_append_of_le_length hcut, List.drop_append_of_le_length hcut]
  simp only [List.map_append, List.append_assoc]

private theorem ear_perm_local (k : ℕ) (sigma : List (Fin k)) (cut : ℕ)
    (hsigma : sigma.Perm (List.finRange k)) :
    (earWord k sigma cut).Perm (List.finRange (k + 1)) := by
  have he : (earWord k sigma cut).Perm (sigma.map Fin.castSucc ++ [Fin.last k]) := by
    unfold earWord
    rw [List.map_take, List.map_drop]
    have hp := (List.perm_append_comm :
        ([Fin.last k] ++ (sigma.map Fin.castSucc).drop cut).Perm
          ((sigma.map Fin.castSucc).drop cut ++ [Fin.last k])).append_left
            ((sigma.map Fin.castSucc).take cut)
    have hj : (sigma.map Fin.castSucc).take cut ++
        ((sigma.map Fin.castSucc).drop cut ++ [Fin.last k]) =
        sigma.map Fin.castSucc ++ [Fin.last k] := by
      rw [← List.append_assoc, List.take_append_drop]
    rw [hj] at hp
    simpa only [List.append_assoc] using hp
  exact he.trans (by simpa [List.finRange_succ_last] using
    (hsigma.map Fin.castSucc).append_right [Fin.last k])

private theorem lower_blocks_result (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (tau : List (Fin d))
    (htau : OriginalOrder d w tau) :
    let f := actualSource (d * r + 1) (2 * (w * geom d r))
    let lower := (lowerBlocks d r hr tau).map Fin.castSucc
    InStrip f (modulus (d * r + 1) / 2)
      ((w : ℤ) * geom d (r - 1)) lower ∧
      (lower.map f).sum = -(w : ℤ) * geom d (r - 1) := by
  dsimp only
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have hh := lower_aux d (s + 2) w hd (by omega) hw tau htau s (by omega) (by omega)
  simpa [lowerBlocks, List.flatMap_map, List.map_flatMap, List.map_map,
    Function.comp_def, Fin.val_castSucc] using hh

/- The common descending block transport.  The base order and its literal ear
are reused verbatim; only the source values are charged by the geometric row. -/
public theorem physical_joint_repetition
    (d w r cut : ℕ) (hd : 2 ≤ d) (hw0 : 1 ≤ w)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (hcut : cut ≤ d)
    (tau : List (Fin d))
    (hold : OriginalOrder d w tau)
    (hnew : OriginalOrder (d + 1) (2 * w) (earWord d tau cut)) :
    OriginalOrder (d * r) (w * geom d r) (repeatWord d r (by omega) tau) ∧
    OriginalOrder (d * r + 1) (2 * (w * geom d r))
      (earWord (d * r) (repeatWord d r (by omega) tau) cut) := by
  classical
  let oldf := actualSource (d * r) (w * geom d r)
  let newf := actualSource (d * r + 1) (2 * (w * geom d r))
  let rows := (List.finRange r).reverse
  let oldBlock := fun j : Fin r => tau.map (blockLabel d r j.val j.isLt)
  have hold_block (j : Fin r) :
      InStrip oldf (modulus (d * r) / 2) 0 (oldBlock j) ∧
        ((oldBlock j).map oldf).sum = 0 := by
    simpa [oldf, oldBlock] using old_block d r w hd hr hw tau hold j
  have hold_strip : InStrip oldf (modulus (d * r) / 2) 0
      (rows.flatMap oldBlock) := by
    apply blocks_concat oldf (modulus (d * r) / 2) rows oldBlock
      (by
        have hN := (TwoRunSource.modulus_positive_odd (d * r)
          (Nat.mul_pos (by omega) (by omega))).1
        omega)
      (fun j hj => (hold_block j).1)
      (fun j hj => (hold_block j).2)
  have hold_sum : ((rows.flatMap oldBlock).map oldf).sum = 0 := by
    exact blocks_sum oldf rows oldBlock (fun j hj => (hold_block j).2)
  have hperm_old : (repeatWord d r (by omega) tau).Perm (List.finRange (d * r)) := by
    exact block_perm d r (by omega) (by omega) tau hold.1
  have hold_order : OriginalOrder (d * r) (w * geom d r)
      (repeatWord d r (by omega) tau) := by
    refine ⟨hperm_old, ?_, ?_⟩
    · simpa [repeatWord, rows, oldBlock, oldf] using hold_sum
    · intro n
      simpa [repeatWord, rows, oldBlock, oldf] using
        (inStrip_prefix hold_strip n)
  have hsplit := repeat_split d r hr tau
  let top := tau.map (blockLabel d r (r - 1) (by omega))
  let topEar := earWord (d * r) top cut
  let lower := (lowerBlocks d r hr tau).map Fin.castSucc
  have htau_len : tau.length = d := by simpa using hold.1.length_eq
  have hsplit_new :
      earWord (d * r) (repeatWord d r (by omega) tau) cut = topEar ++ lower := by
    rw [hsplit]
    rw [earWord_append (d * r) top
      (lowerBlocks d r hr tau) cut
      (by simpa [top, htau_len] using hcut)]
  have htop := top_block d r w hd hr hw tau cut hold hnew hcut
  have hlower := lower_blocks_result d r w hd hr hw tau hold
  have hnew_strip : InStrip newf (modulus (d * r + 1) / 2)
      0 (earWord (d * r) (repeatWord d r (by omega) tau) cut) := by
    rw [hsplit_new]
    apply inStrip_append htop.1
    simpa [topEar, htop.2, hlower.2] using hlower.1
  have hnew_perm :
      (earWord (d * r) (repeatWord d r (by omega) tau) cut).Perm
        (List.finRange (d * r + 1)) := by
    exact ear_perm_local (d * r) _ cut hperm_old
  have hnew_sum :
      ((earWord (d * r) (repeatWord d r (by omega) tau) cut).map newf).sum = 0 := by
    exact (hnew_perm.map newf).sum_eq.trans
      ((ZeroSumSubsets.source_cycle (by omega) (2 * (w * geom d r))).2.1)
  refine ⟨hold_order, ?_⟩
  exact ⟨hnew_perm, hnew_sum, by
    intro n
    simpa [newf] using (inStrip_prefix hnew_strip n)⟩

end D5.S3.Combinatorics.Circle.PhysicalJointRepetition
