/- GID: D5/S3/Combinatorics/Circle/PeriodicShortening
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PeriodicShortening
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.Rotate]
   utility: none
   digest: Charged physical block transport from two independent shorter orders. -/
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import D5.S1.Words.Compositions.ZeroSumWordCount

/-! # Charged physical transport and attained-minimum rotation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.PeriodicShortening
open SourceWidth PeriodicShorteningArithmetic
open scoped BigOperators

def OriginalOrder (k t : ℕ) (word : List (Fin k)) : Prop :=
  word.Perm (List.finRange k) ∧ (word.map (actualSource k t)).sum = 0 ∧
    ∀ h : ℕ, ((word.take h).map (actualSource k t)).sum ∈ Set.Icc (0 : ℤ) (modulus k / 2)

def Good (k t : ℕ) : Prop := ∃ word, OriginalOrder k t word

def earlyLabel (d m : ℕ) (hm : 2 ≤ m) (r : Fin (m - 1)) (i : Fin d) :
    Fin (d * m + 1) :=
  ⟨r.val * d + i.val + 1, by
    have hr : r.val + 1 ≤ m := by omega
    have hh := Nat.mul_le_mul_right d hr
    nlinarith [i.isLt]⟩

def lastLabel (d m : ℕ) (hm : 2 ≤ m) (j : Fin (d + 1)) : Fin (d * m + 1) :=
  ⟨if j.val = 0 then 0 else (m - 1) * d + j.val, by
    have hmd : m = (m - 1) + 1 := by omega
    have he : d * m = (m - 1) * d + d := by
      calc
        d * m = d * ((m - 1) + 1) := congrArg (d * ·) hmd
        _ = (m - 1) * d + d := by ring
    split_ifs <;> nlinarith [j.isLt]⟩

def chargedWord (d m : ℕ) (hm : 2 ≤ m)
    (alpha : List (Fin d)) (beta : List (Fin (d + 1))) : List (Fin (d * m + 1)) :=
  (List.finRange (m - 1)).flatMap (fun r => alpha.map (earlyLabel d m hm r)) ++
    beta.map (lastLabel d m hm)

set_option maxHeartbeats 2000000 in
private theorem chargedWord_perm (d m : ℕ) (hd : 0 < d) (hm : 2 ≤ m)
    (alpha : List (Fin d)) (beta : List (Fin (d + 1)))
    (ha : alpha.Perm (List.finRange d)) (hb : beta.Perm (List.finRange (d + 1))) :
    (chargedWord d m hm alpha beta).Perm (List.finRange (d * m + 1)) := by
  classical
  let early := fun r => (List.finRange d).map (earlyLabel d m hm r)
  let tail := (List.finRange (d + 1)).map (lastLabel d m hm)
  have hinj : Function.Injective (fun ri : Fin (m - 1) × Fin d => earlyLabel d m hm ri.1 ri.2) := by
    rintro ⟨r, i⟩ ⟨s, j⟩ he
    have he' := congrArg Fin.val he
    change r.val * d + i.val + 1 = s.val * d + j.val + 1 at he'
    have hrs : r = s := by
      apply Fin.ext
      by_contra hn
      rcases lt_or_gt_of_ne hn with h | h
      · have := Nat.mul_le_mul_right d (show r.val + 1 ≤ s.val by omega)
        nlinarith [i.isLt, j.isLt]
      · have := Nat.mul_le_mul_right d (show s.val + 1 ≤ r.val by omega)
        nlinarith [i.isLt, j.isLt]
    subst s
    have hij : i = j := Fin.ext (by omega)
    subst j; rfl
  have htinj : Function.Injective (lastLabel d m hm) := by
    intro i j he
    have h := congrArg Fin.val he
    dsimp [lastLabel] at h
    apply Fin.ext
    split_ifs at h <;> omega
  have hend : ∀ r (i : Fin d), (earlyLabel d m hm r i).val ≤ (m - 1) * d := by
    intro r i
    have hh := Nat.mul_le_mul_right d (show r.val + 1 ≤ m - 1 by omega)
    dsimp [earlyLabel]; nlinarith [i.isLt]
  have hnd : ((List.finRange (m - 1)).flatMap early).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro r _
      exact (List.nodup_finRange d).map (fun i j hij => by
        have := hinj (a₁ := (r,i)) (a₂ := (r,j)) hij; exact congrArg Prod.snd this)
    · apply (List.nodup_finRange (m - 1)).imp
      intro r s hrs
      apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
      obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
      exact hrs (congrArg Prod.fst (hinj (a₁ := (r,i)) (a₂ := (s,j)) (hi.trans hj.symm)))
  have hdis : List.Disjoint ((List.finRange (m - 1)).flatMap early) tail := by
    apply List.disjoint_left.mpr
    intro x hx hy
    obtain ⟨r, _, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
    have h := congrArg Fin.val (hi.trans hj.symm)
    have hbnd := hend r i
    dsimp [earlyLabel] at hbnd
    dsimp [earlyLabel, lastLabel] at h
    split_ifs at h <;> omega
  have hfull : (((List.finRange (m - 1)).flatMap early) ++ tail).Perm
      (List.finRange (d * m + 1)) := by
    apply (List.perm_ext_iff_of_nodup (hnd.append ((List.nodup_finRange _).map htinj) hdis) (List.nodup_finRange _)).mpr
    intro p
    simp only [List.mem_finRange, iff_true]
    by_cases hp0 : p.val = 0
    · apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨⟨0, by omega⟩, List.mem_finRange _, Fin.ext (by simp [lastLabel, hp0])⟩
    by_cases hp : p.val ≤ (m - 1) * d
    · let r := (p.val - 1) / d
      let i := (p.val - 1) % d
      have hr : r < m - 1 := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
      have hi : i < d := Nat.mod_lt _ hd
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      refine ⟨⟨r, hr⟩, List.mem_finRange _, List.mem_map.mpr ?_⟩
      refine ⟨⟨i, hi⟩, List.mem_finRange _, Fin.ext ?_⟩
      have h := Nat.mod_add_div (p.val - 1) d
      have hcomm : d * ((p.val - 1) / d) = ((p.val - 1) / d) * d := Nat.mul_comm _ _
      rw [hcomm] at h
      dsimp [earlyLabel, r, i]; omega
    · let j := p.val - (m - 1) * d
      have hmd : d * m = (m - 1) * d + d := by
        calc
          d * m = d * ((m - 1) + 1) := congrArg (d * ·) (by omega)
          _ = (m - 1) * d + d := by ring
      have hj : j < d + 1 := by dsimp [j]; have := p.isLt; omega
      have hj0 : j ≠ 0 := by dsimp [j]; omega
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨⟨j, hj⟩, List.mem_finRange _, Fin.ext (by simp [lastLabel, hj0, j]; omega)⟩
  apply List.Perm.trans ?_ hfull
  apply List.Perm.append
  · apply List.Perm.flatMap_left
    intro r _; exact ha.map _
  · exact hb.map _

private theorem sum_linear {α : Type*} (l : List α) (f g : α → ℤ) (u v : ℤ) :
    (l.map (fun x => u * f x + v * g x)).sum =
      u * (l.map f).sum + v * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem prefix_nonneg_le {α : Type*} (l : List α) (f : α → ℤ)
    (hf : ∀ x ∈ l, 0 ≤ f x) (h : ℕ) :
    0 ≤ ((l.take h).map f).sum ∧ ((l.take h).map f).sum ≤ (l.map f).sum := by
  have ht : 0 ≤ ((l.take h).map f).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf x (List.mem_of_mem_take hx)
  have hd : 0 ≤ ((l.drop h).map f).sum := by
    apply List.sum_nonneg
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf x (List.mem_of_mem_drop hx)
  have he := congrArg (fun s : List α => (s.map f).sum) (List.take_append_drop h l)
  simp only [List.map_append, List.sum_append] at he
  exact ⟨ht, by omega⟩

private theorem strip_of_prefix {α : Type*} (f : α → ℤ) (B h : ℤ) (l : List α)
    (hl : ∀ n, 0 ≤ h + ((l.take n).map f).sum ∧ h + ((l.take n).map f).sum ≤ B) :
    InStrip f B h l := by
  induction l generalizing h with
  | nil => simpa [InStrip] using hl 0
  | cons x xs ih =>
    have hh := hl 0
    refine ⟨by simpa using hh.1, by simpa using hh.2, ih (h + f x) ?_⟩
    intro n
    simpa [List.take_succ_cons, add_assoc] using hl (n + 1)

set_option maxHeartbeats 2000000 in
/-- The last block uses beta's own prefixes, without a sign condition on survivors. -/
private theorem beta_prefix_bound (d w m : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hm : 2 ≤ m)
    (beta : List (Fin (d + 1))) (hb : OriginalOrder (d + 1) w beta) (h : ℕ) :
    let H : ℤ := geom d (m - 1);
    let R : ℤ := ((2 : ℤ) ^ d) ^ (m - 1);
    let f := actualSource (d * m + 1) (w * geom d m);
    -(w : ℤ) * H ≤ -(w : ℤ) * H + (((beta.map (lastLabel d m hm)).take h).map f).sum ∧
    -(w : ℤ) * H + (((beta.map (lastLabel d m hm)).take h).map f).sum ≤
      R * ((2 : ℤ) ^ d - 1) + (modulus d / 2) * H := by
  classical
  dsimp only
  let H : ℤ := geom d (m - 1)
  let R : ℤ := ((2 : ℤ) ^ d) ^ (m - 1)
  let a : Fin (d + 1) → ℤ := fun j => if hz : j.val = 0 then 0 else
    actualSource d w ⟨j.val - 1, by omega⟩
  let e : Fin (d + 1) → ℤ := fun j => if hz : j.val = 0 then 0 else
    charge d w ⟨j.val - 1, by omega⟩
  let z : Fin (d + 1) → ℤ := fun j => if j.val = 0 then 1 else 0
  let pref := beta.take h
  let A := (pref.map a).sum
  let E := (pref.map e).sum
  let Z := (pref.map z).sum
  let Y := (pref.map (actualSource (d + 1) w)).sum
  let Q := A + (w : ℤ) * Z - w
  obtain ⟨hdigit, hesum, hx0, hy0, hx, hfsum, hlast⟩ :=
    periodic_source_equations d w m hd hw hm
  have he0 : ∀ j : Fin (d + 1), 0 ≤ e j := by
    intro j; dsimp [e]; split_ifs <;> first | omega | exact (hdigit _).1
  have hesum' : (beta.map e).sum = (w : ℤ) := by
    rw [(hb.1.map e).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    rw [Fin.sum_univ_succ]
    simpa [e, Fin.val_succ] using hesum
  have hE : 0 ≤ E ∧ E ≤ w := by
    have := prefix_nonneg_le beta e (fun j _ => he0 j) h
    simpa [E, pref, hesum'] using this
  have hzsum : (beta.map z).sum = 1 := by
    rw [(hb.1.map z).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    simp [z, Fin.sum_univ_succ]
  have hZ : 0 ≤ Z ∧ Z ≤ 1 := by
    have := prefix_nonneg_le beta z (by intro j _; dsimp [z]; split_ifs <;> norm_num) h
    simpa [Z, pref, hzsum] using this
  have hY : 0 ≤ Y ∧ Y ≤ (2 : ℤ) ^ d - 1 := by
    have hh : modulus (d + 1) / 2 = (2 : ℤ) ^ d - 1 := by
      rw [modulus, pow_succ]; omega
    simpa [Y, pref, hh] using hb.2.2 h
  have hrow : ∀ j : Fin (d + 1), actualSource (d + 1) w j = 2 * a j - e j + w * z j := by
    intro j
    by_cases hj : j.val = 0
    · have hj0 : j = (0 : Fin (d + 1)) := Fin.ext hj
      subst j
      simpa [a, e, z] using hy0
    · have hi : j.val - 1 < d := by omega
      have hj' : (⟨(j.val - 1) + 1, Nat.succ_lt_succ hi⟩ : Fin (d + 1)) = j :=
        Fin.ext (by simp; omega)
      dsimp only [a, e, z]
      simp only [dif_neg hj, if_neg hj, mul_zero, add_zero]
      simpa only [hj'] using (hdigit ⟨j.val - 1, hi⟩).2.2
  have hjoint : Y = 2 * A - E + w * Z := by
    change (pref.map (actualSource (d + 1) w)).sum =
      2 * (pref.map a).sum - (pref.map e).sum + w * (pref.map z).sum
    have hmap : pref.map (actualSource (d + 1) w) =
        pref.map (fun j => 2 * a j - e j + w * z j) := List.map_congr_left (by intro j _; exact hrow j)
    rw [hmap]
    have hlin := sum_linear pref (fun j => 2 * a j - e j) z 1 w
    have hlin' : (pref.map (fun j => 2 * a j - e j)).sum =
        2 * (pref.map a).sum - (pref.map e).sum := by
      simpa only [neg_one_mul, sub_eq_add_neg] using sum_linear pref a e 2 (-1)
    simp only [one_mul] at hlin
    simpa only [sub_eq_add_neg, neg_mul, one_mul] using hlin.trans (by rw [hlin']; ring)
  have hQ : -(w : ℤ) ≤ Q ∧ Q ≤ modulus d / 2 := by
    have hhalf : 2 * (modulus d / 2) = (2 : ℤ) ^ d - 2 := by
      rw [modulus, show d = (d - 1) + 1 by omega, pow_succ]; omega
    have hw0 : 0 ≤ (w : ℤ) := Int.natCast_nonneg _
    dsimp [Q]
    constructor <;> nlinarith [mul_nonneg hw0 hZ.1,
      mul_le_mul_of_nonneg_left hZ.2 hw0]
  have hsource : ∀ j : Fin (d + 1),
      actualSource (d * m + 1) (w * geom d m) (lastLabel d m hm j) =
        R * actualSource (d + 1) w j + H * (a j + w * z j) := by
    intro j
    by_cases hj : j.val = 0
    · have hg := geom_succ d (m - 1) (by omega)
      rw [show m - 1 + 1 = m by omega] at hg
      have hj0 : j = (0 : Fin (d + 1)) := Fin.ext hj
      subst j
      change actualSource (d * m + 1) (w * geom d m) ⟨0, _⟩ =
        R * actualSource (d + 1) w ⟨0, _⟩ + H * (0 + w * 1)
      rw [hx0, hy0, Nat.cast_mul]
      dsimp [H, R]; nlinarith
    · have hi : j.val - 1 < d := by omega
      have hj' : (⟨(j.val - 1) + 1, Nat.succ_lt_succ hi⟩ : Fin (d + 1)) = j := Fin.ext (by simp; omega)
      have hh := hlast ⟨j.val - 1, hi⟩ (show (m - 1) * d + (j.val - 1) + 1 < d * m + 1 by
        have := (lastLabel d m hm j).isLt; dsimp [lastLabel] at this; simp [hj] at this; omega)
      dsimp only [lastLabel, a, z]
      simp only [if_neg hj, dif_neg hj, mul_zero, add_zero]
      simpa only [hj', H, R, Nat.add_assoc, Nat.sub_add_cancel (show 1 ≤ j.val by omega)] using hh
  have hheight : -(w : ℤ) * H +
      (((beta.map (lastLabel d m hm)).take h).map (actualSource (d * m + 1) (w * geom d m))).sum =
        R * Y + H * Q := by
    rw [← List.map_take, List.map_map]
    simp only [Function.comp_def, hsource]
    rw [sum_linear]
    have hh := sum_linear pref a z 1 w
    dsimp [pref, Y, Q, A, Z] at *
    simp only [one_mul] at hh
    rw [hh]; ring
  rw [hheight]
  have hH : 0 ≤ H := Int.natCast_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  constructor <;> nlinarith [mul_nonneg hR hY.1,
    mul_le_mul_of_nonneg_left hY.2 hR,
    mul_le_mul_of_nonneg_left hQ.1 hH, mul_le_mul_of_nonneg_left hQ.2 hH]


set_option maxHeartbeats 2000000 in
private theorem early_blocks (d w m : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hm : 2 ≤ m)
    (alpha : List (Fin d)) (ha : OriginalOrder d w alpha)
    (V : ℤ) (hV : 2 * (geom d m : ℤ) * (modulus d / 2) ≤ V)
    (n : ℕ) (hn : n ≤ m - 1) :
    let H : ℤ := geom d (m - 1)
    let blocks := (List.finRange n).flatMap (fun r =>
      alpha.map (earlyLabel d m hm ⟨r.val, lt_of_lt_of_le r.isLt hn⟩))
    (blocks.map (actualSource (d * m + 1) (w * geom d m))).sum =
      -(w : ℤ) * (geom d n : ℤ) ∧
    InStrip (actualSource (d * m + 1) (w * geom d m))
      (V + w * H) (w * H) blocks := by
  classical
  let f := actualSource (d * m + 1) (w * geom d m)
  let G : ℤ := geom d m
  let H : ℤ := geom d (m - 1)
  obtain ⟨hdigit, hesum, hx0, hy0, hx, hfsum, hlast⟩ :=
    periodic_source_equations d w m hd hw hm
  let corr := fun r (i : Fin d) => (2 : ℤ) ^ i.val * w * (geom d r : ℤ) + charge d w i
  have hc0 (r : ℕ) (i : Fin d) : 0 ≤ corr r i :=
    add_nonneg (by positivity) (hdigit i).1
  have hcsum (r : ℕ) (hr : r < m) : (alpha.map (corr r)).sum = (w : ℤ) * ((2 : ℤ) ^ d) ^ r := by
    rw [(ha.1.map _).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact hfsum r hr
  have hblock (r : Fin (m - 1)) :
      ((alpha.map (earlyLabel d m hm r)).map f).sum =
        -(w : ℤ) * ((2 : ℤ) ^ d) ^ r.val ∧
      InStrip f (V + w * H) (w * H - w * (geom d r.val : ℤ))
        (alpha.map (earlyLabel d m hm r)) := by
    have hr : r.val < m := by omega
    have hrow (i : Fin d) : f (earlyLabel d m hm r i) =
        2 * G * actualSource d w i - corr r.val i := hx r.val hr i _
    have hsum : ((alpha.map (earlyLabel d m hm r)).map f).sum =
        -(w : ℤ) * ((2 : ℤ) ^ d) ^ r.val := by
      rw [List.map_map]
      simp only [Function.comp_def, hrow]
      have hh := sum_linear alpha (actualSource d w) (corr r.val) (2 * G) (-1)
      simp only [neg_one_mul] at hh
      simpa [sub_eq_add_neg, ha.2.1, hcsum r.val hr] using hh
    refine ⟨hsum, strip_of_prefix _ _ _ _ ?_⟩
    intro h
    have hA := ha.2.2 h
    have hF := prefix_nonneg_le alpha (corr r.val) (fun i _ => hc0 r.val i) h
    rw [hcsum r.val hr] at hF
    have hsumh : (((alpha.map (earlyLabel d m hm r)).take h).map f).sum =
        2 * G * ((alpha.take h).map (actualSource d w)).sum -
          ((alpha.take h).map (corr r.val)).sum := by
      rw [← List.map_take, List.map_map]
      simp only [Function.comp_def, hrow]
      simpa only [neg_one_mul, sub_eq_add_neg] using
        sum_linear (alpha.take h) (actualSource d w) (corr r.val) (2 * G) (-1)
    rw [hsumh]
    have hgm := geom_mono d (by omega) (show r.val + 1 ≤ m - 1 by omega)
    rw [geom_succ d r.val (by omega)] at hgm
    have hG : 0 ≤ G := Int.natCast_nonneg _
    have hw0 : 0 ≤ (w : ℤ) := Int.natCast_nonneg _
    have hgn : 0 ≤ (geom d r.val : ℤ) := Int.natCast_nonneg _
    change (geom d r.val : ℤ) + ((2 : ℤ) ^ d) ^ r.val ≤ H at hgm
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hgm hw0,
      mul_nonneg hw0 hgn, mul_nonneg hG hA.1,
      mul_le_mul_of_nonneg_left hA.2 (show 0 ≤ 2 * G by omega)]
  induction n with
  | zero =>
    have hH : 0 ≤ (w : ℤ) * H := by dsimp [H]; positivity
    have hV0 : 0 ≤ V := by
      have hb : 0 ≤ modulus d / 2 := by
        have := (TwoRunSource.modulus_positive_odd d (by omega)).1; omega
      have hG : 0 ≤ (geom d m : ℤ) := Int.natCast_nonneg _
      nlinarith
    have hg0 : geom d 0 = 0 := by simp [geom]
    simp only [List.finRange_zero, List.flatMap_nil, List.map_nil, List.sum_nil, hg0,
      Nat.cast_zero, mul_zero, neg_zero, InStrip, and_self, true_and]
    exact ⟨hH, by omega⟩
  | succ n ih =>
    have hn' : n ≤ m - 1 := by omega
    have hnr : n < m - 1 := by omega
    obtain ⟨hisum, histrip⟩ := ih hn'
    obtain ⟨hbsum, hbstrip⟩ := hblock ⟨n, hnr⟩
    simp only [List.finRange_succ_last, List.flatMap_append, List.flatMap_map,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, Fin.val_castSucc, Fin.val_last]
    constructor
    · simp only [List.map_append, List.sum_append]
      change _ + ((alpha.map (earlyLabel d m hm ⟨n, hnr⟩)).map f).sum = _
      rw [hisum, hbsum, geom_succ d n (by omega)]
      ring
    · apply inStrip_append histrip
      simpa only [hisum, sub_eq_add_neg, neg_mul, f, H] using hbstrip


set_option maxHeartbeats 2000000 in
/-- Independent original witnesses yield the charged physical word and its minimum rotation. -/
theorem periodic_shortening_transport
    (d w m : ℕ) (hd : 2 ≤ d) (hw0 : 1 ≤ w)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hm : 2 ≤ m)
    (alpha : List (Fin d)) (beta : List (Fin (d + 1)))
    (ha : OriginalOrder d w alpha) (hb : OriginalOrder (d + 1) w beta) :
    let k := d * m + 1
    let U := w * geom d m
    let f := actualSource k U
    let L := chargedWord d m hm alpha beta
    let P := fun h => ((L.take h).map f).sum
    let D := modulus k / 2 - ((2 : ℤ) ^ (d - 1) - w) * (geom d (m - 1) : ℤ)
    L.Perm (List.finRange k) ∧ (L.map f).sum = 0 ∧ D < modulus k / 2 ∧
    (∀ i j : ℕ, P i - P j ≤ D) ∧
    ∃ ell : ℕ, ell < k ∧ (∀ h, P ell ≤ P h) ∧
      (L.rotate ell).Perm (List.finRange k) ∧ ((L.rotate ell).map f).sum = 0 ∧
      ∀ h : ℕ, (((L.rotate ell).take h).map f).sum ∈ Set.Icc (0 : ℤ) (modulus k / 2) := by
  classical
  dsimp only
  let k := d * m + 1
  let U := w * geom d m
  let f := actualSource k U
  let L := chargedWord d m hm alpha beta
  let P := fun h => ((L.take h).map f).sum
  let q : ℤ := 2 ^ d
  let G : ℤ := geom d m
  let H : ℤ := geom d (m - 1)
  let R : ℤ := q ^ (m - 1)
  let B := modulus d / 2
  let C := modulus k / 2
  let D := C - ((2 : ℤ) ^ (d - 1) - w) * H
  let V := R * (q - 1) + B * H
  have hd1 : 1 ≤ d := by omega
  have hq : q = 2 * ((2 : ℤ) ^ (d - 1)) := by
    dsimp [q]; conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
    ring
  have hB : B = (2 : ℤ) ^ (d - 1) - 1 := by
    change (q - 1) / 2 = _
    rw [hq]; omega
  have hq4 : 4 ≤ q := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
    norm_num at this; exact this
  have hG : G = H + R := by
    have := geom_succ d (m - 1) hd1
    rw [show m - 1 + 1 = m by omega] at this
    exact this
  have hR : R = (q - 1) * H + 1 := by
    have := geom_mul d (m - 1) hd1; dsimp [R, q, H]; omega
  have hC : C = (q - 1) * G := by
    have hg := geom_mul d m hd1
    have hk : modulus k = 2 * q ^ m - 1 := by
      dsimp [k, modulus, q]; rw [pow_succ, pow_mul]; ring
    dsimp [C]; rw [hk]
    change (q - 1) * G = q ^ m - 1 at hg
    omega
  have hH : 1 ≤ H := by
    have he : geom d 1 = 1 := by
      simp only [geom, pow_one]; exact Nat.div_self (by
        have := Nat.one_lt_two_pow (by omega : d ≠ 0); omega)
    have := geom_mono d hd1 (show 1 ≤ m - 1 by omega)
    rw [he] at this; exact this
  have hwB : (w : ℤ) ≤ B := by
    rw [hB]
    have hh : (w : ℤ) + 1 ≤ (2 : ℤ) ^ (d - 1) := by
      exact_mod_cast (show w + 1 ≤ 2 ^ (d - 1) by have := Nat.one_le_two_pow (n := d - 1); omega)
    omega
  have hwpos : 0 ≤ (w : ℤ) := Int.natCast_nonneg _
  have hV : 2 * G * B ≤ V := by
    dsimp [V]; rw [hG, hB]; nlinarith [mul_nonneg (by omega : 0 ≤ q) (by omega : 0 ≤ H)]
  have hD : V + w * H = D := by
    dsimp [D, V]; rw [hC, hG, hB]; linear_combination -H * hq
  have hstrict : D < C := by
    have hgap : 1 ≤ (2 : ℤ) ^ (d - 1) - w := by rw [hB] at hwB; omega
    dsimp [D]; nlinarith
  have hp : L.Perm (List.finRange k) := chargedWord_perm d m (by omega) hm alpha beta ha.1 hb.1
  have hlen : L.length = k := by have := hp.length_eq; simpa using this
  have hsum : (L.map f).sum = 0 := by
    rw [(hp.map f).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact (ZeroSumSubsets.source_cycle (by dsimp [k]; omega) U).2.1
  have hearly := early_blocks d w m hd hw hm alpha ha V hV (m - 1) le_rfl
  have hstrip : InStrip f D (w * H) L := by
    dsimp [L, chargedWord]
    rw [← hD]
    apply inStrip_append hearly.2
    have hstart : (w : ℤ) * H +
        (((List.finRange (m - 1)).flatMap (fun r => alpha.map (earlyLabel d m hm r))).map f).sum = 0 := by
      rw [hearly.1]; ring
    rw [hstart]
    apply strip_of_prefix
    intro h
    have hh := beta_prefix_bound d w m hd hw hm beta hb h
    dsimp [H, V, R, q, B, f, k, U] at *
    constructor <;> linarith [hh.1, hh.2]
  have hrange (h : ℕ) : -(w : ℤ) * H ≤ P h ∧ P h ≤ V := by
    have hh := inStrip_prefix hstrip h
    rw [← hD] at hh
    dsimp [P]; constructor <;> linarith
  have hspan (i j : ℕ) : P i - P j ≤ D := by
    rw [← hD]; linarith [(hrange i).2, (hrange j).1]
  obtain ⟨ell, hell, hmin⟩ := Finset.exists_min_image (Finset.range k) P
    ⟨0, Finset.mem_range.mpr (by dsimp [k]; omega)⟩
  have hell' : ell < k := Finset.mem_range.mp hell
  have hminall (h : ℕ) : P ell ≤ P h := by
    by_cases hh : h < k
    · exact hmin h (Finset.mem_range.mpr hh)
    · have ht : L.take h = L := List.take_of_length_le (by omega)
      have hz : P h = P 0 := by
        change ((L.take h).map f).sum = ((L.take 0).map f).sum
        rw [ht, hsum]; simp
      rw [hz]; exact hmin 0 (Finset.mem_range.mpr (by dsimp [k]; omega))
  have hrotperm := (List.rotate_perm L ell).trans hp
  have hrotsum : ((L.rotate ell).map f).sum = 0 := by
    rw [((List.rotate_perm L ell).map f).sum_eq, hsum]
  refine ⟨hp, hsum, hstrict, hspan, ell, hell', hminall, hrotperm, hrotsum, ?_⟩
  intro h
  have hnonneg : 0 ≤ (((L.rotate ell).take h).map f).sum := by
    have hh := D5.S1.Words.Compositions.ZeroSumWordCount.nonnegative_rotate_of_minimum
      (w := L.map f) hsum (j := ell) (by simp [hlen]; omega)
      (fun j _ => by simpa [P, List.map_take] using hminall j) h
    simpa [List.map_rotate, List.map_take] using hh
  refine ⟨hnonneg, ?_⟩
  by_cases hlong : k ≤ h
  · rw [List.take_of_length_le (by rw [List.length_rotate, hlen]; exact hlong), hrotsum]
    have hC0 := (TwoRunSource.modulus_positive_odd k (by dsimp [k]; omega)).1
    change 0 ≤ C
    dsimp [C]; omega
  have hseg (j n : ℕ) : P j + (((L.drop j).take n).map f).sum = P (j + n) := by
    have hh := D5.S1.Words.Compositions.ZeroSumWordCount.prefix_segment_sum (L.map f) j n
    simpa [P, List.map_take, List.map_drop] using hh
  have hsplit : P ell + ((L.drop ell).map f).sum = 0 := by
    have hh := congrArg (fun l => (l.map f).sum) (List.take_append_drop ell L)
    simpa [P, hsum] using hh
  rw [List.rotate_eq_drop_append_take (by omega : ell ≤ L.length), List.take_append,
    List.map_append, List.sum_append]
  by_cases hh : h ≤ k - ell
  · have hz : h - (L.drop ell).length = 0 := by simp [List.length_drop, hlen]; omega
    rw [hz, List.take_zero, List.map_nil, List.sum_nil, add_zero]
    have hs := hseg ell h
    have hbnd := hspan (ell + h) ell
    change _ ≤ C
    linarith
  · rw [List.take_of_length_le (by simp [List.length_drop, hlen]; omega)]
    rw [List.take_take]
    have hbnd := hspan (min (h - (L.drop ell).length) ell) ell
    change _ ≤ C
    dsimp [P] at hbnd
    linarith

#check @periodic_shortening_transport
#print axioms periodic_shortening_transport

end D5.S3.Combinatorics.Circle.PeriodicShortening
