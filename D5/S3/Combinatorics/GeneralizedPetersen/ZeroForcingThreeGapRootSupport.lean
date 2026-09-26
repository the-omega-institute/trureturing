/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.canonical_support_facts
   digest: Exceptional gap leaves reconstruct fourteen-column supports. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapLong
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData56A
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData56B
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7A
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData7B
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8A
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8B
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapData8C
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
import Mathlib.Data.Nat.Digits.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapSupport
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRotation
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary

/-- Every proper gap prefix is shorter than the full circumference. -/
private theorem proper_gap_prefix {n : Nat} [NeZero n] (C : Finset (Fin n))
    (r : Fin C.card) (k : Nat) (hk : k < C.card) :
    positivePrefix (gapWord C) r k < n := by
  have hpositive (j : Fin C.card) : 0 < gapWord C j := by
    have hi : j.val < C.card := j.isLt
    have hnext : j.val + 1 ≤ C.card := by omega
    have hlt : extendedColumn C j.val < extendedColumn C (j.val + 1) := by
      by_cases hj : j.val + 1 < C.card
      · simp only [extendedColumn, dif_pos hi, dif_pos hj]
        exact Fin.lt_def.mp ((C.orderEmbOfFin rfl).strictMono
          (Fin.mk_lt_mk.mpr (by omega)))
      · have heq : j.val + 1 = C.card := by omega
        simp only [extendedColumn, dif_pos hi, dif_neg hj]
        exact (sortedColumn C ⟨j.val, hi⟩).isLt
    unfold gapWord
    omega
  have hfull : positivePrefix (gapWord C) r C.card = n := by
    rw [positivePrefix_lifted C r C.card le_rfl]
    simp [liftedColumn, extendedColumn, r.isLt]
  have hsub : Finset.range (k + 1) ⊆ Finset.range C.card :=
    Finset.range_mono (by omega)
  have hle : positivePrefix (gapWord C) r (k + 1) ≤ n := by
    calc
      positivePrefix (gapWord C) r (k + 1) ≤
          positivePrefix (gapWord C) r C.card :=
            Finset.sum_le_sum_of_subset hsub
      _ = n := hfull
  have hstep : positivePrefix (gapWord C) r (k + 1) =
      positivePrefix (gapWord C) r k + gapWord C (cyclicIndex r k) := by
    simp [positivePrefix, Finset.sum_range_succ]
  have hpos := hpositive (cyclicIndex r k)
  omega

/-- Translating a support by its chosen root column gives its gap-prefix positions. -/
theorem support_from_gaps {n : Nat} [NeZero n] (C : Finset (Fin n))
    (r : Fin C.card) :
    C.image (fun x => x - sortedColumn C r) =
      Finset.univ.image (fun i : Fin C.card =>
        Fin.ofNat n (positivePrefix (rotateWord (gapWord C) r)
          ⟨0, by have := r.isLt; omega⟩ i.val)) := by
  letI : NeZero C.card := ⟨by have := r.isLt; omega⟩
  let base := sortedColumn C r
  have hpoint (i : Fin C.card) :
      sortedColumn C (r + i) - base =
        Fin.ofNat n (positivePrefix (rotateWord (gapWord C) r) 0 i.val) := by
    have hpre : positivePrefix (rotateWord (gapWord C) r) 0 i.val =
        positivePrefix (gapWord C) r i.val := by
      have hindex (x : Fin C.card) (j : Nat) :
          cyclicIndex x j = x + Fin.ofNat C.card j := by
        apply Fin.ext
        simp [cyclicIndex, Fin.val_add, Fin.val_ofNat, Nat.add_mod]
      unfold positivePrefix
      apply Finset.sum_congr rfl
      intro j _
      simp [rotateWord, hindex, add_assoc]
    by_cases hi : i.val = 0
    · have iz : i = 0 := Fin.ext hi
      subst i
      simp [base, positivePrefix]
    · have hend := positivePrefix_endpoint C r i.val
        (positivePrefix (gapWord C) r i.val) (by omega) i.isLt.le
        (proper_gap_prefix C r i.val i.isLt) rfl
      have hidx : cyclicIndex r i.val = r + i := by
        apply Fin.ext
        simp [cyclicIndex, Fin.val_add]
      rw [hidx] at hend
      rw [hpre]
      simpa [base] using congrArg (fun x : Fin n => x - base) hend
  calc
    C.image (fun x => x - base) =
        ((Finset.univ : Finset (Fin C.card)).image (sortedColumn C)).image
          (fun x => x - base) := by
            exact congrArg (fun S : Finset (Fin n) => S.image (fun x => x - base))
              (Finset.image_orderEmbOfFin_univ C rfl).symm
    _ = (Finset.univ : Finset (Fin C.card)).image
          (fun i => sortedColumn C i - base) := by
            rw [Finset.image_image]
            rfl
    _ = (Finset.univ : Finset (Fin C.card)).image
          (fun i => sortedColumn C (r + i) - base) := by
            have hrot : (Finset.univ : Finset (Fin C.card)).image
                (ZeroForcingThreeGapRotation.rotation r) = Finset.univ :=
              Finset.image_univ_of_surjective
                (ZeroForcingThreeGapRotation.rotation r).surjective
            calc
              _ = ((Finset.univ : Finset (Fin C.card)).image
                    (ZeroForcingThreeGapRotation.rotation r)).image
                    (fun i => sortedColumn C i - base) := by rw [hrot]
              _ = _ := by rw [Finset.image_image]; rfl
    _ = Finset.univ.image (fun i : Fin C.card =>
          Fin.ofNat n (positivePrefix (rotateWord (gapWord C) r) 0 i.val)) := by
            congr 1
            funext i
            exact hpoint i

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapClassify
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapMaskBridge
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRotation

/-- A bounded cyclic word above the parity threshold rotates to a checked leaf. -/
theorem bounded_gap_exception (c : Nat) (hc5 : 5 ≤ c) (hc8 : c ≤ 8)
    (h : Fin c → Nat) (hlo : ∀ i, 1 ≤ h i) (hhi : ∀ i, h i ≤ 7)
    (hsum : 14 ≤ ∑ i : Fin c, h i) (hlarge : 4 * c + 6 ≤ T h) :
    ∃ r : Fin c, ∃ e ∈ exceptionalRoots, e.length = c ∧
      (∀ i : Fin c, ∀ hi : i.val < e.length, rotateWord h r i = e[i.val]) := by
  letI : NeZero c := ⟨by omega⟩
  obtain ⟨r, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin c)) h
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let m := h r
  have hmlo : 1 ≤ m := hlo r
  have hmhi : m ≤ 7 := hhi r
  have hroot (d q : Nat) (hd5 : 5 ≤ d) (hd8 : d ≤ 8)
      (hq1 : 1 ≤ q) (hq7 : q ≤ 7) : maskCheck d (d - 1) q [q] = true := by
    interval_cases d
    · exact ZeroForcingThreeGapData56A.roots5 q hq1 hq7
    · by_cases hq5 : q ≤ 5
      · exact ZeroForcingThreeGapData56A.roots6 q hq1 hq5
      · exact ZeroForcingThreeGapData56B.roots6 q (by omega) hq7
    · by_cases hq4 : q ≤ 4
      · exact ZeroForcingThreeGapData7A.roots7 q hq1 hq4
      · by_cases hq6 : q ≤ 6
        · exact ZeroForcingThreeGapData7B.roots7 q (by omega) hq6
        · exact ZeroForcingThreeGapData7A.roots7_top q (by omega) hq7
    · by_cases hq4 : q ≤ 4
      · exact ZeroForcingThreeGapData8A.roots8 q hq1 hq4
      · by_cases hq5 : q ≤ 5
        · exact ZeroForcingThreeGapData8B.roots8 q (by omega) hq5
        · by_cases hq6 : q ≤ 6
          · exact ZeroForcingThreeGapData8C.roots8 q (by omega) hq6
          · exact ZeroForcingThreeGapData8C.roots8_top q (by omega) hq7
  let g := rotateWord h r
  have hprefix : ∀ j : Fin c, ∀ hj : j.val < [m].length, g j = [m][j.val] := by
    intro j hj
    have hj0 : j = 0 := Fin.ext (by simp at hj; omega)
    subst j
    simp [g, rotateWord, m]
  have hglo : ∀ j, 1 ≤ g j := by
    intro j
    exact hlo _
  have hghi : ∀ j, g j ≤ m := by
    intro j
    exact hmax _ (Finset.mem_univ _)
  have hgSum : 14 ≤ ∑ j : Fin c, g j := by
    have hr : (∑ j : Fin c, rotateWord h r j) = ∑ j : Fin c, h j := by
      change (∑ j : Fin c, h ((rotation r) j)) = ∑ j : Fin c, h j
      exact (rotation r).sum_comp h
    simpa [g, hr] using hsum
  have hT (g : Fin c → Nat) (s : Fin c) : T (rotateWord g s) = T g := by
    classical
    have le_rot (a : Fin c → Nat) (t : Fin c) : T (rotateWord a t) ≤ T a := by
      let rot : Bool × Fin c ≃ Bool × Fin c :=
        { toFun := fun v => (v.1, t + v.2)
          invFun := fun v => (v.1, v.2 - t)
          left_inv := by intro ⟨b, i⟩; simp [add_comm]
          right_inv := by intro ⟨b, i⟩; simp [add_comm] }
      have hscore (v : Bool × Fin c) :
          (if v.1 then B (rotateWord a t) v.2 else A (rotateWord a t) v.2) =
            (if (rot v).1 then B a (rot v).2 else A a (rot v).2) := by
        rcases v with ⟨b, i⟩
        have hindex (x : Fin c) (j : Nat) :
            cyclicIndex x j = x + Fin.ofNat c j := by
          apply Fin.ext
          simp [cyclicIndex, Fin.val_add, Fin.val_ofNat, Nat.add_mod]
        have ha : A (rotateWord a t) i = A a (t + i) := by
          simp [A, rotateWord, hindex, add_assoc]
        have hb : B (rotateWord a t) i = B a (t + i) := by
          unfold B prefixScore
          have hp (k : Nat) :
              positivePrefix (rotateWord a t) i k = positivePrefix a (t + i) k := by
            unfold positivePrefix
            apply Finset.sum_congr rfl
            intro j _
            simp [rotateWord, hindex, add_assoc]
          have hn (k : Nat) :
              negativePrefix (rotateWord a t) i k = negativePrefix a (t + i) k := by
            unfold negativePrefix
            apply Finset.sum_congr rfl
            intro j _
            simp [rotateWord, hindex, add_assoc]
          simp_rw [hp, hn]
          split_ifs <;> rfl
        cases b <;> simp [rot, ha, hb]
      unfold T
      apply Finset.sup_le
      intro Y hY
      obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.mp hY
      let Z := Y.image rot
      have hzcard : Z.card = 10 := by
        rw [Finset.card_image_of_injective _ rot.injective]
        exact hcard
      have hzmem : Z ∈ (Finset.univ : Finset (Bool × Fin c)).powersetCard 10 :=
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hzcard⟩
      have hsum :
          (∑ v ∈ Y, (if v.1 then B (rotateWord a t) v.2 else A (rotateWord a t) v.2)) =
            ∑ v ∈ Z, (if v.1 then B a v.2 else A a v.2) := by
        change (∑ v ∈ Y, (if v.1 then B (rotateWord a t) v.2 else A (rotateWord a t) v.2)) =
          ∑ v ∈ Y.image rot, (if v.1 then B a v.2 else A a v.2)
        rw [Finset.sum_image rot.injective.injOn]
        exact Finset.sum_congr rfl (fun v _ => hscore v)
      exact hsum.le.trans (Finset.le_sup
        (f := fun Y : Finset (Bool × Fin c) =>
          ∑ v ∈ Y, (if v.1 then B a v.2 else A a v.2)) hzmem)
    apply Nat.le_antisymm (le_rot g s)
    have hback : rotateWord (rotateWord g s) (-s) = g := by
      funext i
      simp [rotateWord, add_assoc]
    simpa [hback] using le_rot (rotateWord g s) (-s)
  have hgLarge : 4 * c + 6 ≤ T g := by
    simpa [g, hT] using hlarge
  obtain ⟨e, he, helen, heq⟩ := maskCheck_sound
    (by omega : 0 < c) (c - 1) m [m] g
    (by simp; omega) hprefix hglo hghi
    (hroot c m hc5 hc8 hmlo hmhi) hgSum hgLarge
  refine ⟨r, e, he, helen, ?_⟩
  intro j hj
  exact heq j hj

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapClassify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExactBridge
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests

def layerDigit (X : Finset (Bool × Fin 14)) (p : Fin 14) : Nat :=
  if (false, p) ∈ X then (if (true, p) ∈ X then 2 else 0) else 1

def layerDigits (positions : List Nat) (X : Finset (Bool × Fin 14)) : List Nat :=
  List.ofFn fun j : Fin positions.length =>
    layerDigit X (Fin.ofNat 14 positions[j.val])

def layerCode (positions : List Nat) (X : Finset (Bool × Fin 14)) : Nat :=
  Nat.ofDigits 3 (layerDigits positions X)

def supportSet (positions : List Nat) : Finset (Fin 14) :=
  Finset.univ.image fun j : Fin positions.length => Fin.ofNat 14 positions[j.val]

/-- Every ten-set on a stated support is recovered by its base-three layer code. -/
theorem labelledSupport_layerCode (positions : List Nat)
    (hpos : ∀ j : Fin positions.length, positions[j.val] < 14)
    (X : Finset (Bool × Fin 14)) (hC : columns X = supportSet positions) :
    labelledSupport positions (layerCode positions X) = X := by
  have hocc (j : Fin positions.length) :
      (false, Fin.ofNat 14 positions[j.val]) ∈ X ∨
        (true, Fin.ofNat 14 positions[j.val]) ∈ X := by
    have hj : Fin.ofNat 14 positions[j.val] ∈ columns X := by
      rw [hC]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hj
    rcases v with ⟨b, p⟩
    change p = Fin.ofNat 14 positions[j.val] at heq
    cases b
    · left
      exact heq ▸ hv
    · right
      exact heq ▸ hv
  have hbit (j : Fin positions.length) (b : Bool) :
      (if b then labelDigit (layerCode positions X) j.val ≠ 0
        else labelDigit (layerCode positions X) j.val ≠ 1) ↔
      (b, Fin.ofNat 14 positions[j.val]) ∈ X := by
    have hsmall : ∀ d ∈ layerDigits positions X, d < 3 := by
      intro d hd
      simp only [layerDigits, List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      unfold layerDigit
      split_ifs <;> omega
    have hj : j.val < (layerDigits positions X).length := by
      simp [layerDigits, j.isLt]
    have hdecode (digits : List Nat) (hdigits : ∀ d ∈ digits, d < 3)
        (k : Nat) (hk : k < digits.length) :
        labelDigit (Nat.ofDigits 3 digits) k = digits[k] := by
      have hleft := (Nat.setInvOn_digitsAppend_ofDigits (by omega : 1 < 3)
        digits.length).1 (show digits ∈ {L : List Nat | L.length = digits.length ∧
          ∀ d ∈ L, d < 3} from ⟨rfl, hdigits⟩)
      have hget := congrArg (fun l : List Nat => l.getD k 0) hleft
      have hpad (l : List Nat) (t q : Nat) :
          (l ++ List.replicate t 0).getD q 0 = l.getD q 0 := by
        by_cases hq : q < l.length
        · exact List.getD_append l _ 0 q hq
        · rw [List.getD_append_right l _ 0 q (by omega)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq, hq]
      simp only [Nat.digitsAppend, hpad] at hget
      rw [Nat.getD_digits _ _ (by omega : 2 ≤ 3)] at hget
      simpa [labelDigit, List.getD_eq_getElem?_getD, hk] using hget
    have hlabel : labelDigit (layerCode positions X) j.val =
        layerDigit X (Fin.ofNat 14 positions[j.val]) := by
      simpa [layerCode, layerDigits] using
        hdecode (layerDigits positions X) hsmall j.val hj
    rw [hlabel]
    change (if b then layerDigit X (Fin.ofNat 14 positions[j.val]) ≠ 0
      else layerDigit X (Fin.ofNat 14 positions[j.val]) ≠ 1) ↔
        (b, Fin.ofNat 14 positions[j.val]) ∈ X
    have hboth := hocc j
    by_cases ho : (false, Fin.ofNat 14 positions[j.val]) ∈ X
    · by_cases hi : (true, Fin.ofNat 14 positions[j.val]) ∈ X
      · cases b <;> simp only [layerDigit, ho, hi, ↓reduceIte] <;> decide
      · cases b <;> simp only [layerDigit, ho, hi, ↓reduceIte] <;> decide
    · have hi : (true, Fin.ofNat 14 positions[j.val]) ∈ X := hboth.resolve_left ho
      cases b <;> simp only [layerDigit, ho, hi, ↓reduceIte] <;> decide
  ext v
  rcases v with ⟨b, p⟩
  simp only [labelledSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, htest⟩
    have hj' : j < positions.length := List.mem_range.mp hj
    let k : Fin positions.length := ⟨j, hj'⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htest
    have hval : p.val = positions[j] := by
      simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj'] using htest.1
    have hcol : p = Fin.ofNat 14 positions[k.val] := by
      apply Fin.ext
      simpa [k, hpos k, Nat.mod_eq_of_lt (hpos k)] using hval
    have hb : (if b then labelDigit (layerCode positions X) k.val ≠ 0
        else labelDigit (layerCode positions X) k.val ≠ 1) := by
      cases b <;> simpa [k] using htest.2
    simpa [hcol] using (hbit k b).mp hb
  · intro hv
    have hvcol : p ∈ supportSet positions := by
      rw [← hC]
      exact Finset.mem_image.mpr ⟨(b, p), hv, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hvcol
    refine ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · have hval := congrArg Fin.val hj
      simpa [hpos j, Nat.mod_eq_of_lt (hpos j), List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem j.isLt] using hval.symm
    · have hmem : (b, Fin.ofNat 14 positions[j.val]) ∈ X := by
        rw [hj]
        exact hv
      have hb' := (hbit j b).mpr hmem
      cases b <;> simpa [hj] using hb'

/-- The direct finite scan counts exactly the requests and empty collisions. -/
theorem directScore_eq (X : Finset (Bool × Fin 14)) :
    directScore X = ZeroForcingThreeRequests.I 14 X +
      ZeroForcingThreeRequests.K 14 X := by
  let C := columns X
  let O := occupiedVertices X
  let P := positiveRequests 14 X
  let M := negativeRequests 14 X
  have hcount (e : Bool × Fin 14 ≃ Bool × Fin 14)
      (S : Finset (Bool × Fin 14)) :
      (X.filter fun x => e x ∈ S).card = (X.image e ∩ S).card := by
    have himage : (X.filter fun x => e x ∈ S).image e = X.image e ∩ S := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hxs⟩
      · rintro ⟨⟨x, hx, rfl⟩, hxs⟩
        exact ⟨x, ⟨hx, hxs⟩, rfl⟩
    rw [← himage]
    exact (Finset.card_image_iff.mpr e.injective.injOn).symm
  have hp :
      (X.filter fun v => (positiveShift 14 v).2 ∈ C).card = (P ∩ O).card := by
    have h := hcount (positiveShift 14) O
    simpa [C, O, P, positiveRequests, occupiedVertices] using h
  have hm :
      (X.filter fun v => (negativeShift 14 v).2 ∈ C).card = (M ∩ O).card := by
    have h := hcount (negativeShift 14) O
    simpa [C, O, M, negativeRequests, occupiedVertices] using h
  have hmemP (v : Bool × Fin 14) : v ∈ P ↔ negativeShift 14 v ∈ X := by
    change v ∈ X.image (positiveShift 14) ↔ _
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      simpa [negativeShift] using hx
    · intro hv
      exact Finset.mem_image.mpr ⟨negativeShift 14 v, hv, by simp [negativeShift]⟩
  have hmemM (v : Bool × Fin 14) : v ∈ M ↔ positiveShift 14 v ∈ X := by
    change v ∈ X.image (negativeShift 14) ↔ _
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      simpa [negativeShift] using hx
    · intro hv
      exact Finset.mem_image.mpr ⟨positiveShift 14 v, hv, by simp [negativeShift]⟩
  have hk :
      (Finset.univ.filter fun v : Bool × Fin 14 =>
        v.2 ∉ C ∧ negativeShift 14 v ∈ X ∧ positiveShift 14 v ∈ X).card =
        ((P \ O) ∩ (M \ O)).card := by
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter, Finset.mem_sdiff]
    rw [hmemP, hmemM]
    have ho : v ∈ O ↔ v.2 ∈ C := by
      simp [O, occupiedVertices, C]
    tauto
  unfold directScore ZeroForcingThreeRequests.I ZeroForcingThreeRequests.K
  change (X.filter fun v => (positiveShift 14 v).2 ∈ C).card +
    (X.filter fun v => (negativeShift 14 v).2 ∈ C).card +
    (Finset.univ.filter fun v : Bool × Fin 14 =>
      v.2 ∉ C ∧ negativeShift 14 v ∈ X ∧ positiveShift 14 v ∈ X).card =
    (P ∩ O).card + (M ∩ O).card + ((P \ O) ∩ (M \ O)).card
  rw [hp, hm, hk]

/-- A checked interval validates its semantic score for every code it contains. -/
private theorem exactChunk_sound (positions : List Nat) (start count code : Nat)
    (hcheck : exactChunk positions start count = true)
    (hlo : start ≤ code) (hhi : code < start + count)
    (hcard : (labelledSupport positions code).card = 10) :
    ZeroForcingThreeRequests.I 14 (labelledSupport positions code) +
      ZeroForcingThreeRequests.K 14 (labelledSupport positions code) ≤
        2 * positions.length + 2 := by
  have hj : code - start ∈ List.range count := by
    simp only [List.mem_range]
    omega
  have hrow := (List.all_eq_true.mp hcheck) (code - start) hj
  have hadd : start + (code - start) = code := by omega
  change exactRow positions (start + (code - start)) = true at hrow
  rw [hadd] at hrow
  simp only [exactRow, decide_eq_true_eq] at hrow
  rcases hrow with hbad | hgood
  · exact (hbad hcard).elim
  · simpa [directScore_eq] using hgood

/-- The four canonical supports have distinct in-range columns; the other two reflect to them. -/
theorem canonical_support_facts :
    (∀ p ∈ [positions6, positions7a, positions7b, positions8],
      (∀ j : Fin p.length, p[j.val] < 14) ∧
        (supportSet p).card = p.length) ∧
    (supportSet positions7r).image (fun i : Fin 14 => (3 : Fin 14) - i) =
      supportSet positions7a ∧
    (supportSet positions8r).image (fun i : Fin 14 => (3 : Fin 14) - i) =
      supportSet positions8 := by
  constructor
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals constructor
    all_goals decide
  · constructor <;> decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExactBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRootSupport
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRotation
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapSupport
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExactBridge

/-- Each surviving search leaf has total circumference fourteen. -/
private theorem exceptionalRoot_sum (e : List Nat) (he : e ∈ exceptionalRoots) :
    e.sum = 14 := by
  simp only [exceptionalRoots, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with he | he | he | he | he | he <;> subst e <;> decide

/-- A rooted leaf fixes the graph circumference at fourteen. -/
theorem exceptionalRoot_circumference {n : Nat} [NeZero n]
    (C : Finset (Fin n)) (r : Fin C.card)
    (e : List Nat) (he : e ∈ exceptionalRoots) (hlen : e.length = C.card)
    (hword : ∀ i : Fin C.card, ∀ hi : i.val < e.length,
      rotateWord (gapWord C) r i = e[i.val]) : n = 14 := by
  letI : NeZero C.card := ⟨by have := r.isLt; omega⟩
  have hlist : List.ofFn (rotateWord (gapWord C) r) = e := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro j hj1 hj2
      have hj : j < C.card := by simpa using hj1
      simpa using hword ⟨j, hj⟩ hj2
  have hC : C.Nonempty := Finset.card_pos.mp (by have := r.isLt; omega)
  have hsum : e.sum = n := by
    calc
      e.sum = (List.ofFn (rotateWord (gapWord C) r)).sum := by rw [hlist]
      _ = ∑ i : Fin C.card, rotateWord (gapWord C) r i := List.sum_ofFn
      _ = ∑ i : Fin C.card, gapWord C i := by
        change (∑ i : Fin C.card, gapWord C ((rotation r) i)) =
          ∑ i : Fin C.card, gapWord C i
        exact (rotation r).sum_comp (gapWord C)
      _ = n := by
        let z : Fin C.card := ⟨0, Finset.card_pos.mpr hC⟩
        have h := positivePrefix_lifted C z C.card le_rfl
        have hz : positivePrefix (gapWord C) z C.card =
            ∑ i : Fin C.card, gapWord C i := by
          calc
            positivePrefix (gapWord C) z C.card =
                ∑ j ∈ Finset.range C.card, gapWord C (Fin.ofNat C.card j) := by
              unfold positivePrefix
              apply Finset.sum_congr rfl
              intro j hj
              congr 1
              apply Fin.ext
              simp [cyclicIndex, z, Fin.val_ofNat,
                Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
            _ = ∑ i : Fin C.card, gapWord C i := by
              rw [← Fin.sum_univ_eq_sum_range]
              simp
        rw [hz] at h
        simpa [liftedColumn, extendedColumn, z, hC] using h
  have h14 := exceptionalRoot_sum e he
  omega

def wordSupport {c : Nat} [NeZero c] (h : Fin c → Nat) : Finset (Fin 14) :=
  Finset.univ.image fun i : Fin c => Fin.ofNat 14 (positivePrefix h 0 i.val)

/-- The six rooted leaves give six explicit translated support sets. -/
theorem exceptionalRoot_support {c : Nat} [NeZero c]
    (h : Fin c → Nat) (e : List Nat) (he : e ∈ exceptionalRoots)
    (hlen : e.length = c)
    (heq : ∀ i : Fin c, ∀ hi : i.val < e.length, h i = e[i.val]) :
    ∃ p ∈ [positions6, positions7r, positions7a, positions7b, positions8r, positions8],
      wordSupport h = supportSet p := by
  have hfun : h = fun i : Fin c => e[i.val]?.getD 0 := by
    funext i
    have hi : i.val < e.length := by omega
    rw [heq i hi]
    simp [List.getElem?_eq_getElem hi]
  simp only [exceptionalRoots, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with he | he | he | he | he | he
  · subst e
    have hc : c = 6 := by simpa using hlen.symm
    subst c
    refine ⟨positions6, by decide, ?_⟩
    rw [hfun]
    letI : NeZero 6 := ⟨by omega⟩
    change wordSupport (fun i : Fin 6 => [6, 2, 1, 2, 1, 2][i.val]?.getD 0) =
      supportSet positions6
    decide
  · subst e
    have hc : c = 7 := by simpa using hlen.symm
    subst c
    refine ⟨positions7r, by decide, ?_⟩
    rw [hfun]
    letI : NeZero 7 := ⟨by omega⟩
    change wordSupport (fun i : Fin 7 => [3, 2, 1, 2, 1, 2, 3][i.val]?.getD 0) =
      supportSet positions7r
    decide
  · subst e
    have hc : c = 7 := by simpa using hlen.symm
    subst c
    refine ⟨positions7a, by decide, ?_⟩
    rw [hfun]
    letI : NeZero 7 := ⟨by omega⟩
    change wordSupport (fun i : Fin 7 => [3, 3, 2, 1, 2, 1, 2][i.val]?.getD 0) =
      supportSet positions7a
    decide
  · subst e
    have hc : c = 7 := by simpa using hlen.symm
    subst c
    refine ⟨positions7b, by decide, ?_⟩
    rw [hfun]
    letI : NeZero 7 := ⟨by omega⟩
    change wordSupport (fun i : Fin 7 => [6, 2, 1, 1, 1, 1, 2][i.val]?.getD 0) =
      supportSet positions7b
    decide
  · subst e
    have hc : c = 8 := by simpa using hlen.symm
    subst c
    refine ⟨positions8r, by decide, ?_⟩
    rw [hfun]
    letI : NeZero 8 := ⟨by omega⟩
    change wordSupport (fun i : Fin 8 => [3, 2, 1, 1, 1, 1, 2, 3][i.val]?.getD 0) =
      supportSet positions8r
    decide
  · subst e
    have hc : c = 8 := by simpa using hlen.symm
    subst c
    refine ⟨positions8, by decide, ?_⟩
    rw [hfun]
    letI : NeZero 8 := ⟨by omega⟩
    change wordSupport (fun i : Fin 8 => [3, 3, 2, 1, 1, 1, 1, 2][i.val]?.getD 0) =
      supportSet positions8
    decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRootSupport
