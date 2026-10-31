/- GID: D5/S3/Combinatorics/Circle/PhysicalJointRepetition
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PhysicalJointRepetition
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Explicit descending charged repetition with one literal first-block ear. -/

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
  ⟨j * d + i.val, by omega⟩

def repeatWord (d r : ℕ) (hr : 0 < r) (tau : List (Fin d)) : List (Fin (d * r)) :=
  (List.finRange r).reverse.flatMap (fun j =>
    tau.map (blockLabel d r j.val j.isLt))

private theorem list_prefix_strip {α : Type*} (f : α → ℤ) (B h : ℤ) (l : List α)
    (hl : ∀ n, 0 ≤ h + ((l.take n).map f).sum ∧
      h + ((l.take n).map f).sum ≤ B) :
    InStrip f B h l := by
  induction l generalizing h with
  | nil => simpa [InStrip] using hl 0
  | cons x xs ih =>
      refine ⟨by simpa using hl 0, by simpa using (hl 0).2, ih (h + f x) ?_⟩
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

private theorem block_perm (d r : ℕ) (hr : 0 < r) (tau : List (Fin d))
    (htau : tau.Perm (List.finRange d)) :
    (repeatWord d r hr tau).Perm (List.finRange (d * r)) := by
  classical
  let θ : Fin r × Fin d → Fin (d * r) := fun p => blockLabel d r p.1.val p.1.isLt p.2
  have hθ : Function.Injective θ := by
    rintro ⟨j, i⟩ ⟨k, h⟩ he
    have hv := congrArg Fin.val he
    dsimp [θ, blockLabel] at hv
    have hjk : j.val = k.val := by omega
    have hik : i.val = h.val := by omega
    exact Prod.ext (Fin.ext hjk) (Fin.ext hik)
  have hcomplete : ((List.finRange r).flatMap (fun j =>
      (List.finRange d).map (θ (j, ·)))).Perm (List.finRange (d * r)) := by
    have hflatten : (List.finRange r).flatMap (fun j =>
        (List.finRange d).map (θ (j, ·))) =
        ((List.finRange r).product (List.finRange d)).map θ := by
      simp only [List.product, List.map_flatMap, List.map_map, Function.comp_def]
    rw [hflatten]
    apply (List.perm_ext_iff_of_nodup
      (((List.nodup_finRange r).product (List.nodup_finRange d)).map hθ)
      (List.nodup_finRange _)).mpr
    intro x
    simp only [List.mem_finRange, iff_true]
    let j : Fin r := ⟨x.val / d, by omega⟩
    let i : Fin d := ⟨x.val % d, Nat.mod_lt _ (by omega)⟩
    have hdiv := Nat.mod_add_div x.val d
    have hv : θ (j, i) = x := by
      apply Fin.ext
      dsimp [θ, blockLabel, j, i]
      omega
    exact List.mem_map.mpr ⟨(j, i), by simp, hv⟩
  have hbase : (List.finRange r).reverse.flatMap (fun j =>
      (List.finRange d).map (θ (j, ·))).Perm (List.finRange (d * r)) := by
    exact ((List.Perm.reverse (List.Perm.refl _)).flatMap_right _).trans hcomplete
  have hblocks : (repeatWord d r hr (List.finRange d)).Perm (List.finRange (d * r)) := by
    simpa [repeatWord, θ, blockLabel] using hbase
  exact (List.Perm.flatMap_left _ (fun j _ => (htau.map _))).trans hblocks

private theorem multiplier_eq_geom (d r : ℕ) (hd : 0 < d) :
    ThreeRowSource.multiplier d r = geom d r := by
  rw [ThreeRowSource.multiplier_quotient d r hd]
  simp only [geom, pow_mul]
  rfl

private theorem old_value (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (j : Fin r) (i : Fin d) :
    actualSource (d * r) (w * geom d r)
        (blockLabel d r j.val j.isLt i) =
      (geom d r : ℤ) * actualSource d w i := by
  have hmult := ThreeRowSource.repeated_source d r w (by omega) (by omega)
    (blockLabel d r j.val j.isLt i)
  have hmg : ThreeRowSource.multiplier d r = geom d r := multiplier_eq_geom d r (by omega)
  rw [hmg] at hmult
  have hprod := ThreeRowSource.multiplier_identity d r
  rw [hmg] at hprod
  have hG : 0 < geom d r := by
    have := geom_mono d (by omega) (show 1 ≤ r by omega)
    have h1 : geom d 1 = 1 := by
      simp only [geom, pow_one]
      exact Nat.div_self (by
        have : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
        omega)
    omega
  have hwt : w < modulus d := by
    unfold modulus
    have : w + 1 ≤ 2 ^ (d - 1) := by omega
    have hp : 2 ^ (d - 1) ≤ 2 ^ d := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hlt : w * geom d r < modulus (r * d) := by
    have hh := Nat.mul_lt_mul_of_pos_right hwt hG
    have heq : modulus d * geom d r = modulus (r * d) := by
      simpa [Nat.mul_comm] using hprod
    rw [← heq] at hh
    exact hh
  have hmod : (w * geom d r) % (2 ^ (r * d) - 1) = w * geom d r := by
    have hmpos : 0 < modulus (r * d) :=
      (TwoRunSource.modulus_positive_odd (r * d) (by omega)).1
    have heq : modulus (r * d) = 2 ^ (r * d) - 1 := rfl
    rw [← heq]
    exact Nat.mod_eq_of_lt hlt
  have hi : ((blockLabel d r j.val j.isLt i).val % d) = i.val := by
    dsimp [blockLabel]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  simpa [Nat.mul_comm, hmod, hi] using hmult

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
    exact_mod_cast (by simpa [Nat.mul_comm] using hh)
  have hhalfD : 2 * (modulus d / 2) = modulus d - 1 := by
    have ho := (TwoRunSource.modulus_positive_odd d (by omega)).2
    have he := Int.emod_add_mul_ediv (modulus d) 2
    omega
  have hhalfR : 2 * (modulus (d * r) / 2) = modulus (d * r) - 1 := by
    have ho := (TwoRunSource.modulus_positive_odd (d * r) (by omega)).2
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
    have hm : ((tau.take n).map f) =
        (tau.take n).map (fun i => G * a i) := by
      apply List.map_congr_left
      intro i hi
      exact hval i
    rw [hm, List.sum_map_mul_left]
    have hs := inStrip_prefix htau.2.2 n
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
    rw [List.map_map]
    have hm : (tau.map (fun i => f (blockLabel d r j.val j.isLt i))).sum =
        (tau.map (fun i => G * a i)).sum := by
      apply List.map_congr_left
      intro i hi
      exact hval i
    rw [hm, List.sum_map_mul_left]
    have hbase := ((htau.1.map a).sum_eq).trans htau.2.1
    rw [hbase]
    ring
  exact ⟨hstrip, hsum⟩

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
  have hh := hx j.val (by omega) i (by
    dsimp [blockLabel]
    omega)
  have hcast :
      (⟨(blockLabel d r j.val j.isLt i).val + 1, by omega⟩ : Fin (d * r + 1)) =
        ⟨j.val * d + i.val + 1, by omega⟩ := by
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
    dsimp [blockLabel]
    omega)
  have hcast :
      (⟨(blockLabel d r (r - 1) (by omega) j).val + 1, by omega⟩ : Fin (d * r + 1)) =
        ⟨(r - 1) * d + j.val + 1, by omega⟩ := by
    apply Fin.ext
    dsimp [blockLabel]
    omega
  rw [hs, hcast]
  have hshift : actualSource (d + 1) w ⟨j.val + 1, by omega⟩ =
      actualSource (d + 1) (2 * w) j.castSucc := by
    exact (shift_source d w j).symm
  rw [hshift]
  simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

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
    rw [← List.map_take, List.map_map]
    simp only [Function.comp_def]
    apply map_sum_linear
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
        rw [hp]
        change (2 * ((2 : ℤ) ^ d) ^ r - 1) / 2 = _
        change ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) = _ at hgeom
        omega
      rw [hhalf]
      dsimp [start, G]
      have hmono := geom_mono d (by omega)
        (show j.val + 1 ≤ r - 1 by omega)
      have hsucc := geom_succ d (r - 1) (by omega)
      rw [show r - 1 + 1 = r by omega] at hsucc
      have hw0 : 0 ≤ (w : ℤ) := Int.natCast_nonneg _
      have hwq : (w : ℤ) ≤ (2 : ℤ) ^ d - 1 := by
        have hw' : (w : ℤ) ≤ (2 : ℤ) ^ (d - 1) - 1 := by exact_mod_cast hw
        have hp : (2 : ℤ) ^ (d - 1) ≤ (2 : ℤ) ^ d := by
          rw [show d = d - 1 + 1 by omega, pow_succ]
          nlinarith
        omega
      nlinarith [hs.2, hmono, hsucc]
    constructor
    · have hG0 : 0 ≤ 2 * G := by positivity
      nlinarith [hs.1, hf.2, hf.1]
    · have hG0 : 0 ≤ 2 * G := by positivity
      nlinarith [hs.2, hf.1, hcap]
  have hsum : (block.map f).sum = -(w : ℤ) * ((2 : ℤ) ^ d) ^ j.val := by
    rw [← List.map_map]
    simp only [Function.comp_def]
    rw [map_sum_linear]
    have hbase0 := ((htau.1.map a).sum_eq).trans htau.2.1
    rw [hbase0, hsumF]
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

private theorem blocks_concat {α β : Type*} (f : β → ℤ) (B : ℤ) (start : ℤ)
    (rows : List α) (block : α → List β)
    (hstrip : ∀ x ∈ rows, InStrip f B 0 (block x))
    (hsum : ∀ x ∈ rows, (block x).map f |>.sum = 0) :
    InStrip f B start (rows.flatMap block) := by
  induction rows generalizing start with
  | nil => simp [InStrip]
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      apply inStrip_append (hstrip x (by simp))
      simpa [hsum x (by simp)] using
        ih (start := start + (block x).map f |>.sum)
          (fun y hy => hstrip y (by simp [hy]))
          (fun y hy => hsum y (by simp [hy]))

private theorem blocks_sum {α β : Type*} (f : β → ℤ) (rows : List α)
    (block : α → List β) (hsum : ∀ x ∈ rows, (block x).map f |>.sum = 0) :
    ((rows.flatMap block).map f).sum = 0 := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      rw [hsum x (by simp), ih]
      ring

private theorem base_fresh_value (d w : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) :
    actualSource (d + 1) (2 * w) (Fin.last d) = (w : ℤ) := by
  unfold actualSource
  have hpow : (2 : ℤ) ^ d * (2 * (w : ℕ)) =
      (2 : ℤ) ^ (d + 1) * (w : ℕ) := by
    rw [pow_succ]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hpow, centered_full_period]
  obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd (d + 1) (by omega)
  apply centered_unique hN ho (centered_bounds hN ho _) ?_ rfl
  have hhalf : modulus (d + 1) / 2 = (2 : ℤ) ^ d - 1 := by
    unfold modulus
    rw [pow_succ]
    omega
  rw [hhalf]
  constructor <;> omega

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
  have htop (i : Fin d) :
      f (blockLabel d r (r - 1) (by omega) i).castSucc = R * g i.castSucc + H * a i := by
    simpa [R, H, G] using new_top_value d r w hd hr hw i
  have htopfresh : f (Fin.last (d * r)) = (w : ℤ) * G := by
    unfold f
    unfold actualSource
    have hp : (2 : ℤ) ^ (d * r) * (2 * (w * geom d r : ℕ)) =
        (2 : ℤ) ^ (d * r + 1) * (w * geom d r : ℕ) := by
      rw [pow_succ]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hp, centered_full_period]
    obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd (d * r + 1) (by omega)
    apply centered_unique hN ho (centered_bounds hN ho _) ?_ rfl
    have hhalf : modulus (d * r + 1) / 2 =
        ((2 : ℤ) ^ d) ^ r - 1 := by
      unfold modulus
      rw [pow_succ, pow_mul]
      omega
    rw [hhalf]
    have hG0 : 0 ≤ (w : ℤ) * (geom d r : ℤ) := by positivity
    have hGcap : (w : ℤ) * (geom d r : ℤ) ≤ ((2 : ℤ) ^ d) ^ r - 1 := by
      have hprod := geom_mul d r (by omega)
      have hwlt : (w : ℤ) < (2 : ℤ) ^ d - 1 := by
        have : (w : ℤ) + 1 ≤ (2 : ℤ) ^ (d - 1) := by exact_mod_cast (by omega)
        have hp2 : (2 : ℤ) ^ (d - 1) ≤ (2 : ℤ) ^ d := by
          rw [show d = d - 1 + 1 by omega, pow_succ]
          nlinarith
        omega
      have hmul := mul_lt_mul_of_nonneg_right hwlt
        (by positivity : 0 ≤ (geom d r : ℤ))
      have hprod' : ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) =
          ((2 : ℤ) ^ d) ^ r - 1 := hprod
      nlinarith [hmul, hprod']
    constructor <;> omega
  have hformula (n : ℕ) :
      ((block.take n).map f).sum =
        R * (((earWord d tau cut).take n).map (actualSource (d + 1) (2 * w))).sum +
        H * ((tau.take (if n ≤ cut then n else n - 1)).map a).sum +
        (if n ≤ cut then 0 else H * (w : ℤ)) := by
    rw [ear_prefix_formula (d * r) top cut (by simpa [top] using hcut) f n]
    simp only [List.map_map, Function.comp_def]
    rw [htopfresh]
    rw [ear_prefix_formula d tau cut (by simpa using hcut) g n]
    rw [base_fresh_value d w hd hw]
    rw [← List.map_take, List.map_map]
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
    simp only [top, List.map_map, Function.comp_def]
    ring
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
      rw [hp]
      have hg := geom_mul d r (by omega)
      change ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) = (2 : ℤ) ^ d ^ r - 1 at hg
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
      exact_mod_cast (show 4 ≤ 2 ^ d by omega)
    have hellw : (2 : ℤ) ^ (d - 1) - 1 + (w : ℤ) ≤ (2 : ℤ) ^ d - 2 := by
      have hp : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
        conv_lhs => rw [show d = d - 1 + 1 by omega, pow_succ]
        ring
      have hw' : (w : ℤ) ≤ (2 : ℤ) ^ (d - 1) - 1 := by exact_mod_cast hw
      rw [hp]
      omega
    have hcap : R * ((2 : ℤ) ^ d - 1) +
          H * ((2 : ℤ) ^ (d - 1) - 1 + (w : ℤ)) ≤
          ((2 : ℤ) ^ d - 1) * G := by
      nlinarith [hrel, hellw]
    by_cases hnc : n ≤ cut
    · simp only [if_pos hnc]
      constructor <;> nlinarith [hn.1, hn.2, hsumh, ho.1, hcap]
    · simp only [if_neg hnc]
      constructor <;> nlinarith [hn.1, hn.2, hsumh, ho.1, hcap]
  have hsum : (block.map f).sum = (w : ℤ) * H := by
    have htop_len : top.length = d := by
      simpa [top] using htau.1.length_eq
    have hblock_len : block.length = d + 1 := by
      simp only [block, earWord, List.length_append, List.length_map,
        List.length_cons, List.length_nil, List.length_take, List.length_drop]
      omega
    have hear_len : (earWord d tau cut).length = d + 1 := by
      have htau_len : tau.length = d := by simpa using htau.1.length_eq
      simp only [earWord, List.length_append, List.length_map,
        List.length_cons, List.length_nil, List.length_take, List.length_drop,
        htau_len]
      omega
    have hf := hformula (d + 1)
    have hformula_full :
        (block.map f).sum =
          R * ((earWord d tau cut).map g).sum +
            H * ((tau.take d).map a).sum + H * (w : ℤ) := by
      simpa [hblock_len, hear_len, List.take_length,
        show ¬ d + 1 ≤ cut by omega] using hf
    rw [hformula_full, hnew.2.1]
    have holdsum : ((tau.take d).map a).sum = 0 := by
      simpa [show tau.length = d by simpa using htau.1.length_eq] using htau.2.1
    rw [holdsum]
    ring
  exact ⟨hstrip, hsum⟩

private def lowerBlocks (d r : ℕ) (hr : 0 < r) (tau : List (Fin d)) :
    ℕ → List (Fin (d * r))
  | n => (List.finRange n).reverse.flatMap (fun j =>
      tau.map (blockLabel d r j.val j.isLt))

private theorem lower_aux (d r w : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hw : w ≤ 2 ^ (d - 1) - 1) (tau : List (Fin d))
    (htau : OriginalOrder d w tau) :
    ∀ n : ℕ, n + 2 ≤ r →
      let f := actualSource (d * r + 1) (2 * (w * geom d r))
      let rows := (List.finRange (n + 1)).reverse
      let block := fun j : Fin (n + 1) =>
        (tau.map (blockLabel d r j.val (by omega))).map Fin.castSucc
      InStrip f (modulus (d * r + 1) / 2)
        ((w : ℤ) * geom d (n + 1)) (rows.flatMap block) ∧
      ((rows.flatMap block).map f).sum =
        -(w : ℤ) * geom d (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro hn
      dsimp only
      have hb := regular_block d r w hd hr hw tau htau
        ⟨0, by omega⟩ (by omega)
      simp only [List.finRange_succ_last, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.flatMap_cons, List.flatMap_nil,
        List.map_nil, List.append_nil]
      refine ⟨?_, ?_⟩
      · simpa using hb.1
      · simpa using hb.2
  | succ n ih =>
      intro hn
      dsimp only
      have hb := regular_block d r w hd hr hw tau htau
        ⟨n + 1, by omega⟩ (by omega)
      have htail := ih (by omega)
      simp only [List.finRange_succ_last, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.flatMap_cons, List.flatMap_nil,
        List.map_nil, List.append_nil]
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
      constructor
      · apply inStrip_append hb.1
        simpa [hstart] using htail.1
      · simp only [List.map_append, List.sum_append]
        rw [hb.2, htail.2]
        rw [hgeom]
        ring

private theorem repeat_split (d r : ℕ) (hr : 2 ≤ r) (tau : List (Fin d)) :
    repeatWord d r (by omega) tau =
      tau.map (blockLabel d r (r - 1) (by omega)) ++
        lowerBlocks d r (by omega) tau (r - 1) := by
  unfold repeatWord lowerBlocks
  have hfr : List.finRange r =
      List.finRange (r - 1) ++ [⟨r - 1, by omega⟩] := by
    simpa [show r = (r - 1) + 1 by omega] using
      (List.finRange_succ_last (r - 1))
  rw [hfr, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append, List.flatMap_cons,
    List.flatMap_append, List.flatMap_singleton]
  rfl

private theorem earWord_append (k : ℕ) (sigma rho : List (Fin k)) (cut : ℕ)
    (hcut : cut ≤ sigma.length) :
    earWord k (sigma ++ rho) cut = earWord k sigma cut ++ rho.map Fin.castSucc := by
  unfold earWord
  rw [take_append_of_le_length hcut, drop_append_of_le_length hcut]
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
    let lower := (lowerBlocks d r (by omega) tau (r - 1)).map Fin.castSucc
    InStrip f (modulus (d * r + 1) / 2)
      ((w : ℤ) * geom d (r - 1)) lower ∧
      (lower.map f).sum = -(w : ℤ) * geom d (r - 1) := by
  dsimp only
  have hh := lower_aux d r w hd hr hw tau htau (r - 2) (by omega)
  simpa [lowerBlocks, List.map_flatMap, List.map_map, Function.comp_def] using hh

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
        (oldBlock j).map oldf |>.sum = 0 := by
    simpa [oldf, oldBlock] using old_block d r w hd hr hw tau hold j
  have hold_strip : InStrip oldf (modulus (d * r) / 2) 0
      (rows.flatMap oldBlock) := by
    apply blocks_concat oldf (modulus (d * r) / 2) 0 rows oldBlock
      (fun j hj => (hold_block j).1)
      (fun j hj => (hold_block j).2)
  have hold_sum : ((rows.flatMap oldBlock).map oldf).sum = 0 := by
    exact blocks_sum oldf rows oldBlock (fun j hj => (hold_block j).2)
  have hperm_old : (repeatWord d r (by omega) tau).Perm (List.finRange (d * r)) := by
    exact block_perm d r (by omega) tau hold.1
  have hold_order : OriginalOrder (d * r) (w * geom d r)
      (repeatWord d r (by omega) tau) := by
    refine ⟨hperm_old, ?_, ?_⟩
    · simpa [repeatWord, rows, oldBlock, oldf] using hold_sum
    · simpa [repeatWord, rows, oldBlock, oldf] using hold_strip
  have hsplit := repeat_split d r hr tau
  let top := tau.map (blockLabel d r (r - 1) (by omega))
  let topEar := earWord (d * r) top cut
  let lower := (lowerBlocks d r (by omega) tau (r - 1)).map Fin.castSucc
  have hsplit_new :
      earWord (d * r) (repeatWord d r (by omega) tau) cut = topEar ++ lower := by
    rw [hsplit, earWord_append (d * r) top
      (lowerBlocks d r (by omega) tau (r - 1)) cut]
    · rfl
    · simpa [top] using hcut
  have htop := top_block d r w hd hr hw tau cut hold hnew hcut
  have hlower := lower_blocks_result d r w hd hr hw tau hold
  have hnew_strip : InStrip newf (modulus (d * r + 1) / 2)
      0 (earWord (d * r) (repeatWord d r (by omega) tau) cut) := by
    rw [hsplit_new]
    apply inStrip_append htop.1
    simpa [topEar, hlower.2] using hlower.1
  have hnew_perm :
      (earWord (d * r) (repeatWord d r (by omega) tau) cut).Perm
        (List.finRange (d * r + 1)) := by
    exact ear_perm_local (d * r) _ cut hperm_old
  have hnew_sum :
      ((earWord (d * r) (repeatWord d r (by omega) tau) cut).map newf).sum = 0 := by
    exact (hnew_perm.map newf).sum_eq.trans
      ((ZeroSumSubsets.source_cycle (by omega) (2 * (w * geom d r))).2.1)
  refine ⟨hold_order, ?_⟩
  exact ⟨hnew_perm, hnew_sum, by simpa [newf] using hnew_strip⟩

end D5.S3.Combinatorics.Circle.PhysicalJointRepetition
