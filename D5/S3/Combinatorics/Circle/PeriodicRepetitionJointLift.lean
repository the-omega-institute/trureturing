/- GID: D5/S3/Combinatorics/Circle/PeriodicRepetitionJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PeriodicRepetitionJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Last-cycle-first repetition preserves every supplied joint physical order and ear cut. -/
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.ThreeRowSource

/-! # Physical periodic repetition with the identical literal ear -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators

open private PeriodicShortening.chargedWord_perm PeriodicShortening.beta_prefix_bound
  PeriodicShortening.early_blocks PeriodicShortening.strip_of_prefix
  from D5.S3.Combinatorics.Circle.PeriodicShortening
open private RunFirstEarTransport.ear_perm
  from D5.S3.Combinatorics.Circle.RunFirstEarTransport

/-- Distinct physical copies retain the base phase without quotienting occurrences. -/
def blockLabel (d m : ℕ) (r : Fin m) (i : Fin d) : Fin (d * m) :=
  ⟨r.val * d + i.val, by nlinarith [r.isLt, i.isLt]⟩

/-- The final physical cycle comes first, followed by cycles zero through m-2. -/
def cycles (m : ℕ) (hm : 2 ≤ m) : List (Fin m) :=
  ⟨m - 1, by omega⟩ :: (List.finRange (m - 1)).map (fun r => ⟨r.val, by omega⟩)

def repeatedWord (d m : ℕ) (hm : 2 ≤ m) (alpha : List (Fin d)) : List (Fin (d * m)) :=
  (cycles m hm).flatMap (fun r => alpha.map (blockLabel d m r))

private theorem cycles_perm (m : ℕ) (hm : 2 ≤ m) :
    (cycles m hm).Perm (List.finRange m) := by
  cases m with
  | zero => omega
  | succ n =>
    simpa [cycles, List.finRange_succ_last] using
      (List.perm_append_comm : ([Fin.last n] ++ (List.finRange n).map Fin.castSucc).Perm
        ((List.finRange n).map Fin.castSucc ++ [Fin.last n]))

private theorem repeated_perm (d m : ℕ) (hm : 2 ≤ m) (alpha : List (Fin d))
    (ha : alpha.Perm (List.finRange d)) :
    (repeatedWord d m hm alpha).Perm (List.finRange (d * m)) := by
  classical
  let theta : Fin m × Fin d ≃ Fin (d * m) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm m d))
  have he : (List.finRange m).flatMap (fun r => (List.finRange d).map (blockLabel d m r)) =
      ((List.finRange m).product (List.finRange d)).map theta := by
    simp only [List.product, List.map_flatMap, List.map_map, Function.comp_def]
    rfl
  apply (List.Perm.flatMap (cycles_perm m hm) (fun r => ha.map (blockLabel d m r))).trans
  rw [he]
  apply (List.perm_ext_iff_of_nodup
    (((List.nodup_finRange m).product (List.nodup_finRange d)).map theta.injective)
    (List.nodup_finRange _)).mpr
  intro x
  simp only [List.mem_finRange, iff_true]
  exact List.mem_map.mpr ⟨theta.symm x, List.mem_product.mpr ⟨by simp, by simp⟩,
    theta.apply_symm_apply x⟩

private theorem source_successor (n t : ℕ) (i : Fin (n + 1)) :
    actualSource (n + 1) (2 * t) i = actualSource (n + 1) t (finRotate (n + 1) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [finRotate_last]
    unfold actualSource
    have he : (2 : ℤ) ^ (Fin.last n).val * (2 * t : ℕ) = (2 : ℤ) ^ (n + 1) * t := by
      simp only [Fin.val_last, Nat.cast_mul, Nat.cast_ofNat, pow_succ]; ring
    rw [he, centered_full_period]
    simp
  · rw [finRotate_of_lt j.isLt]
    unfold actualSource
    congr 1
    simp only [Fin.val_castSucc, Fin.val_mk, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    ring

private theorem successor_order (n t : ℕ) (l : List (Fin (n + 1))) :
    OriginalOrder (n + 1) (2 * t) l ↔
      OriginalOrder (n + 1) t (l.map (finRotate (n + 1))) := by
  have hmap : ∀ xs : List (Fin (n + 1)),
      ((xs.map (finRotate (n + 1))).map (actualSource (n + 1) t)) =
        xs.map (actualSource (n + 1) (2 * t)) := by
    intro xs
    simp only [List.map_map, Function.comp_def, ← source_successor]
  constructor
  · rintro ⟨hp, hz, hs⟩
    refine ⟨(hp.map _).trans (finRotate (n + 1)).map_finRange_perm, ?_, ?_⟩
    · simpa [hmap] using hz
    · intro h
      simpa only [← List.map_take, hmap] using hs h
  · rintro ⟨hp, hz, hs⟩
    refine ⟨?_, by simpa only [hmap] using hz, ?_⟩
    · have hh := hp.map (finRotate (n + 1)).symm
      simpa only [List.map_map, Equiv.symm_comp_self, List.map_id] using
        hh.trans (finRotate (n + 1)).symm.map_finRange_perm
    · intro h
      simpa only [← List.map_take, hmap] using hs h

/-- The explicit tail boundary, rather than an arbitrary minimum rotation, is legal. -/
private theorem tail_first_order (d w m : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hm : 2 ≤ m)
    (alpha : List (Fin d)) (beta : List (Fin (d + 1)))
    (ha : OriginalOrder d w alpha) (hb : OriginalOrder (d + 1) w beta) :
    OriginalOrder (d * m + 1) (w * geom d m)
      (beta.map (lastLabel d m hm) ++
        (List.finRange (m - 1)).flatMap (fun r => alpha.map (earlyLabel d m hm r))) := by
  classical
  let f := actualSource (d * m + 1) (w * geom d m)
  let q : ℤ := 2 ^ d
  let G : ℤ := geom d m
  let H : ℤ := geom d (m - 1)
  let R : ℤ := q ^ (m - 1)
  let B := modulus d / 2
  let C := modulus (d * m + 1) / 2
  let V := R * (q - 1) + B * H
  let D := V + w * H
  let tail := beta.map (lastLabel d m hm)
  let early := (List.finRange (m - 1)).flatMap (fun r => alpha.map (earlyLabel d m hm r))
  have hq : q = 2 * ((2 : ℤ) ^ (d - 1)) := by
    dsimp [q]; rw [show d = (d - 1) + 1 by omega, pow_succ]; ring
  have hB : B = (2 : ℤ) ^ (d - 1) - 1 := by
    change (q - 1) / 2 = _
    rw [hq]; omega
  have hG : G = H + R := by
    simpa [G, H, R, q, show m - 1 + 1 = m by omega] using geom_succ d (m - 1) (by omega)
  have hR : R = (q - 1) * H + 1 := by
    have := geom_mul d (m - 1) (by omega)
    dsimp [R, q, H]; omega
  have hC : C = (q - 1) * G := by
    have hg := geom_mul d m (by omega)
    have hk : modulus (d * m + 1) = 2 * q ^ m - 1 := by
      dsimp [modulus, q]; rw [pow_succ, pow_mul]; ring
    dsimp [C]; rw [hk]
    change (q - 1) * G = q ^ m - 1 at hg
    omega
  have hH : 0 ≤ H := Int.natCast_nonneg _
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hV : 2 * G * B ≤ V := by
    dsimp [V]; rw [hG, hB]
    nlinarith [mul_nonneg hq0 hH]
  have hwB : (w : ℤ) ≤ B := by
    rw [hB]
    have hh : (w : ℤ) + 1 ≤ (2 : ℤ) ^ (d - 1) := by
      exact_mod_cast (show w + 1 ≤ 2 ^ (d - 1) by have := Nat.one_le_two_pow (n := d - 1); omega)
    omega
  have hDC : D ≤ C := by
    dsimp [D, V]
    rw [hC, hG, hB] at *
    nlinarith [mul_nonneg (show 0 ≤ (2 : ℤ) ^ (d - 1) - w by omega) hH]
  have hp : (tail ++ early).Perm (List.finRange (d * m + 1)) :=
    List.perm_append_comm.trans (chargedWord_perm d m (by omega) hm alpha beta ha.1 hb.1)
  have hz : ((tail ++ early).map f).sum = 0 := by
    rw [(hp.map f).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact (ZeroSumSubsets.source_cycle (by omega : 2 ≤ d * m + 1) (w * geom d m)).2.1
  have he := early_blocks d w m hd hw hm alpha ha V hV (m - 1) le_rfl
  have htail : (tail.map f).sum = (w : ℤ) * H := by
    simp only [List.map_append, List.sum_append] at hz
    have hes : (early.map f).sum = -(w : ℤ) * H := he.1
    linarith
  have ht : InStrip f D 0 tail := by
    apply strip_of_prefix
    intro h
    have hh := beta_prefix_bound d w m hd hw hm beta hb h
    change -(w : ℤ) * H ≤ -(w : ℤ) * H + ((tail.take h).map f).sum ∧
      -(w : ℤ) * H + ((tail.take h).map f).sum ≤ V at hh
    change 0 ≤ 0 + ((tail.take h).map f).sum ∧ 0 + ((tail.take h).map f).sum ≤ D
    dsimp [D]; constructor <;> linarith [hh.1, hh.2]
  have hs : InStrip f D 0 (tail ++ early) := by
    apply inStrip_append ht
    simpa only [htail, zero_add] using he.2
  refine ⟨hp, hz, ?_⟩
  intro h
  have hh := inStrip_prefix hs h
  exact ⟨by simpa using hh.1, by dsimp only [C] at hDC; linarith [hh.2]⟩

private theorem literal_ear_identity (d m : ℕ) (hm : 2 ≤ m) (alpha : List (Fin d))
    (j : ℕ) (hj : j ≤ alpha.length) :
    (earWord (d * m) (repeatedWord d m hm alpha) j).map (finRotate (d * m + 1)) =
      ((earWord d alpha j).map (finRotate (d + 1))).map (lastLabel d m hm) ++
        (List.finRange (m - 1)).flatMap (fun r => alpha.map (earlyLabel d m hm r)) := by
  have hlast (i : Fin d) :
      finRotate (d * m + 1) (blockLabel d m ⟨m - 1, by omega⟩ i).castSucc =
        lastLabel d m hm (finRotate (d + 1) i.castSucc) := by
    rw [finRotate_of_lt i.isLt, finRotate_of_lt (blockLabel d m ⟨m - 1, by omega⟩ i).isLt]
    apply Fin.ext
    simp [lastLabel, blockLabel]
  have hearly (r : Fin (m - 1)) (i : Fin d) :
      finRotate (d * m + 1) (blockLabel d m ⟨r.val, by omega⟩ i).castSucc =
        earlyLabel d m hm r i := by
    rw [finRotate_of_lt (blockLabel d m ⟨r.val, by omega⟩ i).isLt]
    rfl
  have hear : finRotate (d * m + 1) (Fin.last (d * m)) =
      lastLabel d m hm (finRotate (d + 1) (Fin.last d)) := by
    simp [lastLabel]
  have hlen : j ≤ (alpha.map (blockLabel d m ⟨m - 1, by omega⟩)).length := by simpa using hj
  simp only [repeatedWord, cycles, List.flatMap_cons, List.flatMap_map, Function.comp_def]
  simp only [earWord, List.take_append, List.drop_append, List.take_of_length_le hlen,
    Nat.sub_eq_zero_of_le hlen, List.take_zero, List.drop_zero, List.append_nil,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    ← List.map_take, ← List.map_drop, hlast, hearly, hear, List.map_flatMap]
  simp only [List.append_assoc]

set_option maxHeartbeats 2000000 in
/-- Every supplied base joint witness repeats with its identical ear cut in the last-first word. -/
theorem periodic_repetition_joint_lift (d w m : ℕ) (hd : 2 ≤ d) (hw0 : 1 ≤ w)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hm : 2 ≤ m)
    (alpha : List (Fin d)) (j : ℕ) (hj : j ≤ d)
    (hold : OriginalOrder d w alpha)
    (hnew : OriginalOrder (d + 1) (2 * w) (earWord d alpha j)) :
    OriginalOrder (d * m) (w * geom d m) (repeatedWord d m hm alpha) ∧
      OriginalOrder (d * m + 1) (2 * (w * geom d m))
        (earWord (d * m) (repeatedWord d m hm alpha) j) := by
  classical
  have hlen : alpha.length = d := by simpa using hold.1.length_eq
  have hbeta := (successor_order d w (earWord d alpha j)).mp hnew
  have htarget := tail_first_order d w m hd hw hm alpha _ hold hbeta
  have hn : OriginalOrder (d * m + 1) (2 * (w * geom d m))
      (earWord (d * m) (repeatedWord d m hm alpha) j) := by
    apply (successor_order (d * m) (w * geom d m) _).mpr
    rw [literal_ear_identity d m hm alpha j (by omega)]
    exact htarget
  refine ⟨?_, hn⟩
  let f := actualSource (d * m) (w * geom d m)
  let G : ℤ := geom d m
  have hmult : ThreeRowSource.multiplier d m = geom d m := by
    rw [ThreeRowSource.multiplier_quotient d m (by omega)]
    simp only [geom, Nat.mul_comm, ← pow_mul]
  have hG1 : 1 ≤ G := by
    dsimp [G]
    rw [← hmult]
    exact_mod_cast ThreeRowSource.multiplier_positive d m (by omega)
  have hN : (2 ^ (d * m) - 1 : ℕ) = geom d m * (2 ^ d - 1) := by
    have hh := ThreeRowSource.multiplier_identity d m
    rw [hmult, Nat.mul_comm m d] at hh
    unfold modulus at hh
    exact_mod_cast hh.symm
  have hwN : w < 2 ^ d - 1 := by
    have hp := Nat.one_le_two_pow (n := d - 1)
    rw [show d = (d - 1) + 1 by omega, pow_succ]
    omega
  have hseed : (ThreeRowSource.multiplier d m * w) % (2 ^ (m * d) - 1) = w * geom d m := by
    rw [hmult, Nat.mul_comm m d, hN, Nat.mod_eq_of_lt]
    · omega
    · exact Nat.mul_lt_mul_of_pos_left hwN (by exact_mod_cast hG1)
  have hphysical (r : Fin m) (i : Fin d) : f (blockLabel d m r i) = G * actualSource d w i := by
    have hh := ThreeRowSource.repeated_source d m w (by omega) (by omega)
      (Fin.cast (Nat.mul_comm d m) (blockLabel d m r i))
    have hi : (⟨(blockLabel d m r i).val % d, Nat.mod_lt _ (by omega)⟩ : Fin d) = i := by
      apply Fin.ext
      simp [blockLabel, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
    simpa only [Fin.val_cast, hseed, hmult, hi, Nat.mul_comm m d] using hh
  have hcap : G * (modulus d / 2) ≤ modulus (d * m) / 2 := by
    have hb : 2 * (modulus d / 2) = modulus d - 1 := by
      have := (TwoRunSource.modulus_positive_odd d (by omega)).2
      omega
    have hk : 2 * (modulus (d * m) / 2) = modulus (d * m) - 1 := by
      have := (TwoRunSource.modulus_positive_odd (d * m) (by positivity)).2
      omega
    have hh := ThreeRowSource.multiplier_identity d m
    rw [hmult, Nat.mul_comm m d] at hh
    nlinarith
  have hbase : InStrip (actualSource d w) (modulus d / 2) 0 alpha :=
    strip_of_prefix _ _ _ _ (by intro n; simpa using hold.2.2 n)
  have hzero (r : Fin m) : ((alpha.map (blockLabel d m r)).map f).sum = 0 := by
    rw [ThreeRowSource.scaled_sum _ _ _ G alpha (fun i _ => hphysical r i), hold.2.1]
    ring
  have hstrip (r : Fin m) : InStrip f (modulus (d * m) / 2) 0 (alpha.map (blockLabel d m r)) := by
    simpa using ThreeRowSource.scale_strip _ _ _ G _ _ 0 (by omega) hcap alpha
      (fun i _ => hphysical r i) hbase
  refine ⟨repeated_perm d m hm alpha hold.1, ?_, ?_⟩
  · change (((cycles m hm).flatMap (fun r => alpha.map (blockLabel d m r))).map f).sum = 0
    induction cycles m hm with
    | nil => simp
    | cons r rs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, hzero, zero_add]; exact ih
  · intro n
    have hs := TwoRunSource.concatenate_zero _ _ (by
      have := (TwoRunSource.modulus_positive_odd (d * m) (by positivity)).1; omega)
      (cycles m hm) (fun r => alpha.map (blockLabel d m r))
      (fun r _ => hzero r) (fun r _ => hstrip r)
    simpa only [zero_add] using inStrip_prefix hs n

#check @periodic_repetition_joint_lift
#print axioms periodic_repetition_joint_lift

end D5.S3.Combinatorics.Circle.PeriodicRepetitionJointLift
