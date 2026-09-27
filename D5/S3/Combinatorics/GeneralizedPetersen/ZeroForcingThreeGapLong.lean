/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong.long_gap_score
   digest: The rooted long-gap compositions at circumference fourteen obey the slot bound. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapMaskBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRotation
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests

def rotateWord {c : Nat} (h : Fin c → Nat) (r : Fin c) (i : Fin c) : Nat :=
  h (r + i)

def rotation {c : Nat} [NeZero c] (r : Fin c) : Fin c ≃ Fin c where
  toFun i := r + i
  invFun i := i - r
  left_inv := by intro i; simp [add_comm]
  right_inv := by intro i; simp [add_comm]

private def vertexRotation {c : Nat} [NeZero c] (r : Fin c) :
    Bool × Fin c ≃ Bool × Fin c where
  toFun v := (v.1, r + v.2)
  invFun v := (v.1, v.2 - r)
  left_inv := by intro ⟨b, i⟩; simp [add_comm]
  right_inv := by intro ⟨b, i⟩; simp [add_comm]

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapLong
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCompute
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapMaskBridge
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapRotation

private def positiveCompositions (total : Nat) : Nat → List (List Nat)
  | 0 => if total = 0 then [[]] else []
  | k + 1 => (List.range total).flatMap fun j =>
      (positiveCompositions (total - (j + 1)) k).map (List.cons (j + 1))

private def longWords (c : Nat) : List (List Nat) :=
  (List.range 7).flatMap fun j =>
    (positiveCompositions (14 - (j + 8)) (c - 1)).map (List.cons (j + 8))

private theorem positiveCompositions_complete (total k : Nat) (l : List Nat)
    (hlen : l.length = k) (hsum : l.sum = total)
    (hpos : ∀ x ∈ l, 1 ≤ x) : l ∈ positiveCompositions total k := by
  induction k generalizing total l with
  | zero =>
      have hl : l = [] := List.length_eq_zero_iff.mp hlen
      subst l
      simp at hsum
      simp [positiveCompositions, hsum]
  | succ k ih =>
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < l.length)
      have ha : 1 ≤ a := hpos a (by simp)
      have hat : a ≤ total := by
        simp only [List.sum_cons] at hsum
        omega
      have htail : t ∈ positiveCompositions (total - a) k := by
        apply ih (total - a) t
        · simpa using hlen
        · simp only [List.sum_cons] at hsum
          omega
        · intro x hx
          exact hpos x (by simp [hx])
      simp only [positiveCompositions, List.mem_flatMap]
      refine ⟨a - 1, List.mem_range.mpr (by omega), ?_⟩
      simpa [Nat.sub_add_cancel ha] using htail

private theorem longWords_complete (c : Nat) (h : Fin c → Nat)
    (hc : 0 < c) (hsum : (∑ i : Fin c, h i) = 14)
    (hpos : ∀ i, 1 ≤ h i) (hfirst : 8 ≤ h ⟨0, hc⟩) :
    (List.ofFn h) ∈ longWords c := by
  have hlist : (List.ofFn h).length = c := by simp
  have hsumList : (List.ofFn h).sum = 14 := by simpa [List.sum_ofFn] using hsum
  have hpList : ∀ x ∈ List.ofFn h, 1 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hpos i
  cases hlist0 : List.ofFn h with
  | nil => simp [hlist0] at hlist; omega
  | cons a t =>
      have ha : a = h ⟨0, hc⟩ := by
        have hget := congrArg (fun l : List Nat => l[0]?) hlist0
        have hget0 : (List.ofFn h)[0]? = some (h ⟨0, hc⟩) := by simp [hc]
        simpa [hget0] using hget.symm
      have hamin : 8 ≤ a := ha ▸ hfirst
      have hamax : a ≤ 14 := by
        rw [hlist0] at hsumList
        simp only [List.sum_cons] at hsumList
        omega
      have htail : t ∈ positiveCompositions (14 - a) (c - 1) := by
        apply positiveCompositions_complete
        · simp [hlist0] at hlist
          omega
        · rw [hlist0] at hsumList
          simp only [List.sum_cons] at hsumList
          omega
        · intro x hx
          exact hpList x (by rw [hlist0]; simp [hx])
      unfold longWords
      apply List.mem_flatMap.mpr
      refine ⟨a - 8, List.mem_range.mpr (by omega), ?_⟩
      simpa [Nat.sub_add_cancel hamin, hlist0] using htail

private theorem longWords_score (c : Nat) (hc5 : 5 ≤ c) (hc8 : c ≤ 8)
    (l : List Nat) (hl : l ∈ longWords c) :
    maskUpper c 14 l ≤ 4 * c + 5 := by
  have hchecked : (longWords c).all
      (fun w => decide (maskUpper c 14 w ≤ 4 * c + 5)) = true := by
    interval_cases c <;> decide
  exact of_decide_eq_true ((List.all_eq_true.mp hchecked) l hl)

theorem long_gap_score (c : Nat) (hc5 : 5 ≤ c) (hc8 : c ≤ 8)
    (h : Fin c → Nat) (hpos : ∀ i, 1 ≤ h i)
    (hsum : (∑ i : Fin c, h i) = 14)
    (r : Fin c) (hr : 8 ≤ h r) : T h ≤ 4 * c + 5 := by
  letI : NeZero c := ⟨by omega⟩
  let g := rotateWord h r
  have gsum : (∑ i : Fin c, g i) = 14 := by
    change (∑ i : Fin c, h ((rotation r) i)) = 14
    simpa using (rotation r).sum_comp h |>.trans hsum
  have gp : ∀ i, 1 ≤ g i := fun i => hpos _
  have gf : 8 ≤ g ⟨0, by omega⟩ := by simpa [g, rotateWord] using hr
  have gl := longWords_complete c g (by omega) gsum gp gf
  have hmax : ∀ i : Fin c, g i ≤ 14 := by
    intro i
    have := Finset.sum_le_sum_of_subset (f := g)
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    simp only [Finset.sum_singleton] at this
    omega
  have hprefix : ∀ j : Fin c, ∀ hj : j.val < (List.ofFn g).length,
      g j = (List.ofFn g)[j.val] := by
    intro j hj
    simp
  have hupper : T g ≤ maskUpper c 14 (List.ofFn g) := by
    unfold maskUpper
    apply (le_min_iff).2
    constructor
    · exact T_le_maskPrice (by omega) 14 (List.ofFn g) g hprefix gp hmax 0
    apply (le_min_iff).2
    constructor
    · exact T_le_maskPrice (by omega) 14 (List.ofFn g) g hprefix gp hmax 1
    apply (le_min_iff).2
    constructor
    · exact T_le_maskPrice (by omega) 14 (List.ofFn g) g hprefix gp hmax 2
    apply (le_min_iff).2
    exact ⟨T_le_maskPrice (by omega) 14 (List.ofFn g) g hprefix gp hmax 3,
      T_le_maskPrice (by omega) 14 (List.ofFn g) g hprefix gp hmax 4⟩
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
  rw [← hT h r]
  exact hupper.trans (longWords_score c hc5 hc8 _ gl)

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapLong
