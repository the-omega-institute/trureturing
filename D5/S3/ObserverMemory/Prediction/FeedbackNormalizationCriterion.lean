/- GID: D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Feedback normalization iff prefix causality and sequential stochastic kernels. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.List.TFAE
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section
namespace D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion

/-- A dependent word restricted to the rounds with index strictly below `n`. -/
abbrev Prefix {T : ℕ} (X : Fin T → Type*) (n : ℕ) :=
  (i : {i : Fin T // i.val < n}) → X i.1

/-- Restrict a complete dependent word to its first `n` coordinates. -/
def restrictPrefix {T : ℕ} {X : Fin T → Type*}
    (x : ∀ t, X t) (n : ℕ) : Prefix X n :=
  fun i => x i.1

/-- Join a prefix to a suffix whose coordinates begin at the cut `n`. -/
def spliceWords {T : ℕ} {X : Fin T → Type*} (n : ℕ)
    (u : Prefix X n) (v : (i : {i : Fin T // n ≤ i.val}) → X i.1) :
    ∀ t, X t := by
  classical
  exact fun t => if h : t.val < n then u ⟨t, h⟩ else v ⟨t, Nat.le_of_not_gt h⟩

/-- The action word selected by a deterministic causal strategy on an output word. -/
def feedbackActions {T : ℕ} {A Y : Fin T → Type*}
    (f : (t : Fin T) → Prefix Y t.val → A t) (y : ∀ t, Y t) :
    ∀ t, A t :=
  fun t => f t (restrictPrefix y t.val)

/-- The total mass obtained after substituting a causal strategy into a response table. -/
def feedbackMass {T : ℕ} {A Y : Fin T → Type*}
    [∀ t, Fintype (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ)
    (f : (t : Fin T) → Prefix Y t.val → A t) : ℝ :=
  ∑ y, P y (feedbackActions f y)

/-- The mass of one fixed output prefix under a complete action word. -/
def prefixMarginal {T : ℕ} {A Y : Fin T → Type*}
    [∀ t, Fintype (Y t)] [∀ t, DecidableEq (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ)
    (n : ℕ) (x : Prefix Y n) (a : ∀ t, A t) : ℝ := by
  classical
  exact ∑ y, if restrictPrefix y n = x then P y a else 0

/-- The mass of an event of output prefixes under a complete action word. -/
def prefixEventMarginal {T : ℕ} {A Y : Fin T → Type*}
    [∀ t, Fintype (Y t)] [∀ t, DecidableEq (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ)
    (n : ℕ) (E : Set (Prefix Y n)) (a : ∀ t, A t) : ℝ := by
  classical
  exact ∑ y, if restrictPrefix y n ∈ E then P y a else 0

/-- A single-cut strategy follows `u` before the cut and selects suffix `v` or `w`
according to whether the observed prefix belongs to `E`. -/
def singleCutSwitch {T : ℕ} {A Y : Fin T → Type*} (n : ℕ)
    (u : Prefix A n)
    (v w : (i : {i : Fin T // n ≤ i.val}) → A i.1)
    (E : Set (Prefix Y n)) :
    (t : Fin T) → Prefix Y t.val → A t := by
  classical
  intro t history
  by_cases ht : t.val < n
  · exact u ⟨t, ht⟩
  · let x : Prefix Y n := fun i =>
      history ⟨i.1, lt_of_lt_of_le i.2 (Nat.le_of_not_gt ht)⟩
    exact if x ∈ E then v ⟨t, Nat.le_of_not_gt ht⟩
      else w ⟨t, Nat.le_of_not_gt ht⟩

/-- For a normalized nonnegative finite response table, universal deterministic-feedback
normalization, normalization of all single-cut event switches, future-action independence of every
prefix marginal, and factorization into normalized sequential kernels are equivalent. -/
theorem feedback_normalization_prefix_causality_sequential_kernels
    (T : ℕ) (hT : 1 ≤ T)
    (A Y : Fin T → Type*)
    [∀ t, Fintype (A t)] [∀ t, Nonempty (A t)] [∀ t, DecidableEq (A t)]
    [∀ t, Fintype (Y t)] [∀ t, Nonempty (Y t)] [∀ t, DecidableEq (Y t)]
    (P : (∀ t, Y t) → (∀ t, A t) → ℝ)
    (hP : ∀ y a, 0 ≤ P y a)
    (hPsum : ∀ a, ∑ y, P y a = 1) :
    List.TFAE [
      ∀ f : (t : Fin T) → Prefix Y t.val → A t, feedbackMass P f = 1,
      ∀ n, 1 ≤ n → n < T →
        ∀ (u : Prefix A n)
          (v w : (i : {i : Fin T // n ≤ i.val}) → A i.1)
          (E : Set (Prefix Y n)),
          feedbackMass P (singleCutSwitch n u v w E) = 1,
      ∀ n, n ≤ T → ∀ (x : Prefix Y n) (a b : ∀ t, A t),
        (∀ i, i.val < n → a i = b i) →
          prefixMarginal P n x a = prefixMarginal P n x b,
      ∃ q : (t : Fin T) → Prefix A (t.val + 1) → Prefix Y t.val → Y t → ℝ,
        (∀ t a x y, 0 ≤ q t a x y) ∧
        (∀ t a x, ∑ y, q t a x y = 1) ∧
        ∀ y a, P y a = ∏ t, q t (restrictPrefix a (t.val + 1))
          (restrictPrefix y t.val) (y t)] := by
  classical
  tfae_have 1 → 2 := by
    intro h n hn0 hnT u v w E
    exact h (singleCutSwitch n u v w E)
  tfae_have 2 → 3 := by
    intro hswitch n hn x a b hab
    have switchIdentity (m : ℕ) (hm : m ≤ T)
        (u : Prefix A m)
        (v w : (i : {i : Fin T // m ≤ i.val}) → A i.1)
        (E : Set (Prefix Y m)) :
        feedbackMass P (singleCutSwitch m u v w E) =
          1 + prefixEventMarginal P m E (spliceWords m u v) -
            prefixEventMarginal P m E (spliceWords m u w) := by
      have actionIdentity (y : ∀ t, Y t) :
          feedbackActions (singleCutSwitch m u v w E) y =
            if restrictPrefix y m ∈ E then spliceWords m u v else spliceWords m u w := by
        funext t
        by_cases ht : t.val < m
        · by_cases hE : restrictPrefix y m ∈ E
          · simp [feedbackActions, singleCutSwitch, spliceWords, ht, hE]
          · simp [feedbackActions, singleCutSwitch, spliceWords, ht, hE]
        · have hpref :
              (fun i : {i : Fin T // i.val < m} =>
                restrictPrefix y t.val
                  ⟨i.1, lt_of_lt_of_le i.2 (Nat.le_of_not_gt ht)⟩) =
                restrictPrefix y m := by
            rfl
          by_cases hE : restrictPrefix y m ∈ E
          · simp [feedbackActions, singleCutSwitch, spliceWords, ht, hpref, hE]
          · simp [feedbackActions, singleCutSwitch, spliceWords, ht, hpref, hE]
      rw [feedbackMass]
      simp_rw [actionIdentity]
      calc
        (∑ y, P y (if restrictPrefix y m ∈ E then spliceWords m u v
            else spliceWords m u w)) =
            ∑ y, (P y (spliceWords m u w) +
              (if restrictPrefix y m ∈ E then P y (spliceWords m u v) else 0) -
              (if restrictPrefix y m ∈ E then P y (spliceWords m u w) else 0)) := by
                apply Finset.sum_congr rfl
                intro y hy
                by_cases hE : restrictPrefix y m ∈ E <;> simp [hE]
        _ = 1 + prefixEventMarginal P m E (spliceWords m u v) -
              prefixEventMarginal P m E (spliceWords m u w) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  hPsum (spliceWords m u w)]
                rfl
    by_cases hn0 : n = 0
    · subst n
      have hx (c : ∀ t, A t) : prefixMarginal P 0 x c = 1 := by
        rw [prefixMarginal]
        have hall : ∀ y : ∀ t, Y t, restrictPrefix y 0 = x := by
          intro y
          funext i
          exact (Nat.not_lt_zero i.1.val i.2).elim
        calc
          (∑ y, if restrictPrefix y 0 = x then P y c else 0) =
              ∑ y, P y c := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [if_pos (hall y)]
          _ = 1 := hPsum c
      rw [hx a, hx b]
    · by_cases hnT : n = T
      · have hab' : a = b := by
          funext i
          exact hab i (hnT ▸ i.isLt)
        rw [hab']
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hnlt : n < T := lt_of_le_of_ne hn hnT
        let u : Prefix A n := restrictPrefix a n
        let v : (i : {i : Fin T // n ≤ i.val}) → A i.1 := fun i => a i.1
        let w : (i : {i : Fin T // n ≤ i.val}) → A i.1 := fun i => b i.1
        have huv : spliceWords n u v = a := by
          funext i
          by_cases hi : i.val < n <;> simp [spliceWords, u, v, hi, restrictPrefix]
        have huw : spliceWords n u w = b := by
          funext i
          by_cases hi : i.val < n
          · simp [spliceWords, u, hi, restrictPrefix, hab i hi]
          · simp [spliceWords, w, hi]
        have hevent (c : ∀ t, A t) :
            prefixEventMarginal P n ({x} : Set (Prefix Y n)) c =
              prefixMarginal P n x c := by
          rw [prefixEventMarginal, prefixMarginal]
          apply Finset.sum_congr rfl
          intro y hy
          simp only [Set.mem_singleton_iff]
        have hm := switchIdentity n hn u v w ({x} : Set (Prefix Y n))
        rw [hswitch n hnpos hnlt u v w ({x} : Set (Prefix Y n)), huv, huw,
          hevent a, hevent b] at hm
        linarith
  tfae_have 3 → 4 := by
    intro hcausal
    let defaultA : ∀ t, A t := fun t => Classical.choice (inferInstance : Nonempty (A t))
    let defaultY : ∀ t, Y t := fun t => Classical.choice (inferInstance : Nonempty (Y t))
    let extendA (n : ℕ) (u : Prefix A n) : ∀ t, A t := fun t =>
      if ht : t.val < n then u ⟨t, ht⟩ else defaultA t
    let takeA (n m : ℕ) (hnm : n ≤ m) (u : Prefix A m) : Prefix A n :=
      fun i => u ⟨i.1, lt_of_lt_of_le i.2 hnm⟩
    let takeY (n m : ℕ) (hnm : n ≤ m) (x : Prefix Y m) : Prefix Y n :=
      fun i => x ⟨i.1, lt_of_lt_of_le i.2 hnm⟩
    let snocY (n : ℕ) (hn : n < T) (x : Prefix Y n) (z : Y ⟨n, hn⟩) :
        Prefix Y (n + 1) := fun i =>
      if hi : i.1.val < n then x ⟨i.1, hi⟩ else by
        have hle : n ≤ i.1.val := Nat.le_of_not_gt hi
        have hge : i.1.val ≤ n := Nat.lt_succ_iff.mp i.2
        have hit : i.1 = (⟨n, hn⟩ : Fin T) := Fin.ext (Nat.le_antisymm hge hle)
        exact hit.symm ▸ z
    have snocYLast (n : ℕ) (hn : n < T) (x : Prefix Y n) (z : Y ⟨n, hn⟩) :
        snocY n hn x z ⟨(⟨n, hn⟩ : Fin T), Nat.lt_succ_self n⟩ = z := by
      simp [snocY]
    have takeSnocY (n : ℕ) (hn : n < T) (x : Prefix Y n) (z : Y ⟨n, hn⟩) :
        takeY n (n + 1) (Nat.le_succ n) (snocY n hn x z) = x := by
      funext i
      simp [takeY, snocY, i.2]
    have restrictSnocY (n : ℕ) (hn : n < T) (y : ∀ t, Y t) :
        restrictPrefix y (n + 1) =
          snocY n hn (restrictPrefix y n) (y ⟨n, hn⟩) := by
      funext i
      rcases i with ⟨⟨k, hkT⟩, hkSucc⟩
      by_cases hi : k < n
      · simp [restrictPrefix, snocY, hi]
      · have hle : n ≤ k := Nat.le_of_not_gt hi
        have hge : k ≤ n := Nat.lt_succ_iff.mp hkSucc
        have hk : k = n := Nat.le_antisymm hge hle
        subst k
        simp [restrictPrefix, snocY]
    have marginalRec (n : ℕ) (hn : n < T) (x : Prefix Y n) (a : ∀ t, A t) :
        (∑ z : Y ⟨n, hn⟩, prefixMarginal P (n + 1) (snocY n hn x z) a) =
          prefixMarginal P n x a := by
      simp only [prefixMarginal]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hparent : restrictPrefix y n = x
      · let z0 : Y ⟨n, hn⟩ := y ⟨n, hn⟩
        have hchild : restrictPrefix y (n + 1) = snocY n hn x z0 := by
          rw [restrictSnocY, hparent]
        rw [Finset.sum_eq_single z0]
        · rw [if_pos hchild, if_pos hparent]
        · intro z hz hne
          rw [if_neg]
          intro heq
          have hsame : snocY n hn x z0 = snocY n hn x z := hchild.symm.trans heq
          have hvalue := congrFun hsame
            ⟨(⟨n, hn⟩ : Fin T), Nat.lt_succ_self n⟩
          rw [snocYLast, snocYLast] at hvalue
          exact hne hvalue.symm
        · intro hz0
          exact (hz0 (Finset.mem_univ z0)).elim
      · rw [if_neg hparent]
        apply Finset.sum_eq_zero
        intro z hz
        rw [if_neg]
        intro heq
        apply hparent
        funext i
        have hvalue := congrFun heq
          ⟨i.1, lt_trans i.2 (Nat.lt_succ_self n)⟩
        simpa [restrictPrefix, snocY, i.2] using hvalue
    let p (n : ℕ) (x : Prefix Y n) (u : Prefix A n) : ℝ :=
      prefixMarginal P n x (extendA n u)
    have pNonneg (n : ℕ) (x : Prefix Y n) (u : Prefix A n) : 0 ≤ p n x u := by
      dsimp [p, prefixMarginal]
      exact Finset.sum_nonneg fun y hy => by split_ifs <;> simp_all
    have pRec (t : Fin T) (u : Prefix A (t.val + 1)) (x : Prefix Y t.val) :
        (∑ z : Y t, p (t.val + 1) (snocY t.val t.isLt x z) u) =
          p t.val x (takeA t.val (t.val + 1) (Nat.le_succ t.val) u) := by
      change (∑ z : Y t,
          prefixMarginal P (t.val + 1) (snocY t.val t.isLt x z)
            (extendA (t.val + 1) u)) =
        prefixMarginal P t.val x
          (extendA t.val (takeA t.val (t.val + 1) (Nat.le_succ t.val) u))
      rw [marginalRec t.val t.isLt x (extendA (t.val + 1) u)]
      apply hcausal t.val (Nat.le_of_lt t.isLt) x
      intro i hi
      simp [extendA, takeA, hi, lt_trans hi (Nat.lt_succ_self t.val)]
    let q : (t : Fin T) → Prefix A (t.val + 1) → Prefix Y t.val → Y t → ℝ :=
      fun t u x z =>
        if p t.val x (takeA t.val (t.val + 1) (Nat.le_succ t.val) u) = 0 then
          if z = defaultY t then 1 else 0
        else p (t.val + 1) (snocY t.val t.isLt x z) u /
          p t.val x (takeA t.val (t.val + 1) (Nat.le_succ t.val) u)
    have qNonneg (t : Fin T) (u : Prefix A (t.val + 1))
        (x : Prefix Y t.val) (z : Y t) : 0 ≤ q t u x z := by
      by_cases hp0 : p t.val x
          (takeA t.val (t.val + 1) (Nat.le_succ t.val) u) = 0
      · by_cases hz : z = defaultY t <;> simp [q, hp0, hz]
      · have hpPos : 0 < p t.val x
            (takeA t.val (t.val + 1) (Nat.le_succ t.val) u) :=
          lt_of_le_of_ne (pNonneg _ _ _) (Ne.symm hp0)
        simp only [q, hp0, ↓reduceIte]
        exact div_nonneg (pNonneg _ _ _) hpPos.le
    have qSum (t : Fin T) (u : Prefix A (t.val + 1)) (x : Prefix Y t.val) :
        ∑ z, q t u x z = 1 := by
      by_cases hp0 : p t.val x
          (takeA t.val (t.val + 1) (Nat.le_succ t.val) u) = 0
      · simp [q, hp0]
      · simp only [q, hp0, ↓reduceIte]
        rw [← Finset.sum_div, pRec, div_self hp0]
    have pStep (t : Fin T) (u : Prefix A (t.val + 1))
        (x : Prefix Y t.val) (z : Y t) :
        p (t.val + 1) (snocY t.val t.isLt x z) u =
          p t.val x (takeA t.val (t.val + 1) (Nat.le_succ t.val) u) * q t u x z := by
      by_cases hp0 : p t.val x
          (takeA t.val (t.val + 1) (Nat.le_succ t.val) u) = 0
      · have hchild : p (t.val + 1) (snocY t.val t.isLt x z) u = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun z _ => pNonneg _ _ _).mp
            ((pRec t u x).trans hp0) z (Finset.mem_univ z)
        simp [q, hp0, hchild]
      · simp only [q, hp0, ↓reduceIte]
        field_simp
    have pZero (x : Prefix Y 0) (u : Prefix A 0) : p 0 x u = 1 := by
      change prefixMarginal P 0 x (extendA 0 u) = 1
      simp only [prefixMarginal]
      calc
        (∑ y, if restrictPrefix y 0 = x then P y (extendA 0 u) else 0) =
            ∑ y, P y (extendA 0 u) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [if_pos]
              funext i
              exact (Nat.not_lt_zero i.1.val i.2).elim
        _ = 1 := hPsum (extendA 0 u)
    let kernelProduct (n : ℕ) (hn : n ≤ T) (u : Prefix A n) (x : Prefix Y n) : ℝ :=
      ∏ k : Fin n,
        q (Fin.castLE hn k)
          (takeA (k.val + 1) n (Nat.succ_le_iff.mpr k.isLt) u)
          (takeY k.val n (Nat.le_of_lt k.isLt) x)
          (x ⟨Fin.castLE hn k, k.isLt⟩)
    have pFactor (n : ℕ) (hn : n ≤ T) (x : Prefix Y n) (u : Prefix A n) :
        p n x u = kernelProduct n hn u x := by
      induction n with
      | zero =>
          rw [pZero]
          simp [kernelProduct]
      | succ n ih =>
          have hnT : n < T := Nat.lt_of_succ_le hn
          let t : Fin T := ⟨n, hnT⟩
          let xp : Prefix Y n := takeY n (n + 1) (Nat.le_succ n) x
          let up : Prefix A n := takeA n (n + 1) (Nat.le_succ n) u
          let z : Y t := x ⟨t, Nat.lt_succ_self n⟩
          have hxsnoc : snocY n hnT xp z = x := by
            funext i
            rcases i with ⟨⟨k, hkT⟩, hkSucc⟩
            by_cases hi : k < n
            · simp [snocY, xp, takeY, hi]
            · have hle : n ≤ k := Nat.le_of_not_gt hi
              have hge : k ≤ n := Nat.lt_succ_iff.mp hkSucc
              have hk : k = n := Nat.le_antisymm hge hle
              subst k
              simp [snocY, z, t]
          have hstep := pStep t u xp z
          have hparent := ih (Nat.le_of_lt hnT) xp up
          calc
            p (n + 1) x u = p (n + 1) (snocY n hnT xp z) u := by rw [hxsnoc]
            _ = p n xp up * q t u xp z := hstep
            _ = kernelProduct n (Nat.le_of_lt hnT) up xp * q t u xp z := by rw [hparent]
            _ = kernelProduct (n + 1) hn u x := by
              dsimp [kernelProduct]
              rw [Fin.prod_univ_castSucc]
              congr 1
    refine ⟨q, qNonneg, qSum, ?_⟩
    intro y a
    have hextend : extendA T (restrictPrefix a T) = a := by
      funext t
      simp [extendA, restrictPrefix, t.isLt]
    have hfull : prefixMarginal P T (restrictPrefix y T) a = P y a := by
      simp only [prefixMarginal]
      rw [Finset.sum_eq_single y]
      · rw [if_pos rfl]
      · intro y' hy' hne
        rw [if_neg]
        intro hpref
        apply hne
        funext t
        exact congrFun hpref ⟨t, t.isLt⟩
      · intro hy
        exact (hy (Finset.mem_univ y)).elim
    have hpfull : p T (restrictPrefix y T) (restrictPrefix a T) = P y a := by
      change prefixMarginal P T (restrictPrefix y T)
        (extendA T (restrictPrefix a T)) = P y a
      rw [hextend, hfull]
    calc
      P y a = p T (restrictPrefix y T) (restrictPrefix a T) := hpfull.symm
      _ = kernelProduct T le_rfl (restrictPrefix a T) (restrictPrefix y T) :=
        pFactor T le_rfl (restrictPrefix y T) (restrictPrefix a T)
      _ = ∏ t, q t (restrictPrefix a (t.val + 1))
          (restrictPrefix y t.val) (y t) := by
        apply Finset.prod_congr rfl
        intro t ht
        congr 1
  tfae_have 4 → 1 := by
    rintro ⟨q, hqnonneg, hqsum, hfactor⟩ f
    let takeY (n m : ℕ) (hnm : n ≤ m) (x : Prefix Y m) : Prefix Y n :=
      fun i => x ⟨i.1, lt_of_lt_of_le i.2 hnm⟩
    let snocY (n : ℕ) (hn : n < T) (x : Prefix Y n) (z : Y ⟨n, hn⟩) :
        Prefix Y (n + 1) := fun i =>
      if hi : i.1.val < n then x ⟨i.1, hi⟩ else by
        have hle : n ≤ i.1.val := Nat.le_of_not_gt hi
        have hge : i.1.val ≤ n := Nat.lt_succ_iff.mp i.2
        have hit : i.1 = (⟨n, hn⟩ : Fin T) := Fin.ext (Nat.le_antisymm hge hle)
        exact hit.symm ▸ z
    have snocYLast (n : ℕ) (hn : n < T) (x : Prefix Y n) (z : Y ⟨n, hn⟩) :
        snocY n hn x z ⟨(⟨n, hn⟩ : Fin T), Nat.lt_succ_self n⟩ = z := by
      simp [snocY]
    have takeSnocY (n : ℕ) (hn : n < T) (x : Prefix Y n) (z : Y ⟨n, hn⟩) :
        takeY n (n + 1) (Nat.le_succ n) (snocY n hn x z) = x := by
      funext i
      simp [takeY, snocY, i.2]
    have snocTakeY (n : ℕ) (hn : n < T) (x : Prefix Y (n + 1)) :
        snocY n hn (takeY n (n + 1) (Nat.le_succ n) x)
          (x ⟨(⟨n, hn⟩ : Fin T), Nat.lt_succ_self n⟩) = x := by
      funext i
      rcases i with ⟨⟨k, hkT⟩, hkSucc⟩
      by_cases hi : k < n
      · simp [snocY, takeY, hi]
      · have hle : n ≤ k := Nat.le_of_not_gt hi
        have hge : k ≤ n := Nat.lt_succ_iff.mp hkSucc
        have hk : k = n := Nat.le_antisymm hge hle
        subst k
        simp [snocY]
    let snocEquivY (n : ℕ) (hn : n < T) :
        Prefix Y (n + 1) ≃ Prefix Y n × Y ⟨n, hn⟩ :=
      { toFun := fun x => (takeY n (n + 1) (Nat.le_succ n) x,
          x ⟨(⟨n, hn⟩ : Fin T), Nat.lt_succ_self n⟩)
        invFun := fun x => snocY n hn x.1 x.2
        left_inv := fun x => snocTakeY n hn x
        right_inv := by
          rintro ⟨x, z⟩
          exact Prod.ext (takeSnocY n hn x z) (snocYLast n hn x z) }
    let actionPrefix (n : ℕ) (hn : n < T) (x : Prefix Y n) : Prefix A (n + 1) :=
      fun i => f i.1 (fun j =>
        x ⟨j.1, lt_of_lt_of_le j.2 (Nat.lt_succ_iff.mp i.2)⟩)
    let pathProduct (n : ℕ) (hn : n ≤ T) (x : Prefix Y n) : ℝ :=
      ∏ k : Fin n,
        let t : Fin T := Fin.castLE hn k
        let past : Prefix Y k.val := takeY k.val n (Nat.le_of_lt k.isLt) x
        q t (actionPrefix k.val t.isLt past) past (x ⟨t, k.isLt⟩)
    have pathSnoc (n : ℕ) (hn : n < T) (x : Prefix Y n) (z : Y ⟨n, hn⟩) :
        pathProduct (n + 1) (Nat.succ_le_of_lt hn) (snocY n hn x z) =
          pathProduct n (Nat.le_of_lt hn) x * q ⟨n, hn⟩ (actionPrefix n hn x) x z := by
      dsimp [pathProduct]
      rw [Fin.prod_univ_castSucc]
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro k hk
        dsimp
        have hpast :
            takeY k.val (n + 1) (Nat.le_of_lt (Fin.castSucc k).isLt)
                (snocY n hn x z) =
              takeY k.val n (Nat.le_of_lt k.isLt) x := by
          funext i
          simp [takeY, snocY, lt_trans i.2 k.isLt]
        rw [hpast]
        simp [snocY]
      · dsimp
        rw [takeSnocY n hn x z]
        simp only [snocY]
        congr 1
        split
        · rename_i hbad
          simp at hbad
        · rfl
    have totalPrefix (n : ℕ) (hn : n ≤ T) :
        ∑ x : Prefix Y n, pathProduct n hn x = 1 := by
      induction n with
      | zero =>
          let emptyY : Prefix Y 0 := fun i => (Nat.not_lt_zero i.1.val i.2).elim
          have heq (x : Prefix Y 0) : x = emptyY := by
            funext i
            exact (Nat.not_lt_zero i.1.val i.2).elim
          rw [Finset.sum_eq_single emptyY]
          · simp [pathProduct]
          · intro x hx hne
            exact (hne (heq x)).elim
          · intro h
            exact (h (Finset.mem_univ emptyY)).elim
      | succ n ih =>
          have hnT : n < T := Nat.lt_of_succ_le hn
          rw [← (snocEquivY n hnT).symm.sum_comp, Fintype.sum_prod_type]
          change (∑ x : Prefix Y n, ∑ z : Y ⟨n, hnT⟩,
            pathProduct (n + 1) hn (snocY n hnT x z)) = 1
          simp_rw [pathSnoc]
          calc
            (∑ x : Prefix Y n, ∑ z : Y ⟨n, hnT⟩,
                pathProduct n (Nat.le_of_lt hnT) x *
                  q ⟨n, hnT⟩ (actionPrefix n hnT x) x z) =
                ∑ x : Prefix Y n, pathProduct n (Nat.le_of_lt hnT) x := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [← Finset.mul_sum, hqsum, mul_one]
            _ = 1 := ih (Nat.le_of_lt hnT)
    have pathFull (y : ∀ t, Y t) :
        pathProduct T le_rfl (restrictPrefix y T) =
          ∏ t, q t (restrictPrefix (feedbackActions f y) (t.val + 1))
            (restrictPrefix y t.val) (y t) := by
      dsimp [pathProduct]
      apply Finset.prod_congr rfl
      intro t ht
      congr 1
    let fullPrefixEquiv : ((t : Fin T) → Y t) ≃ Prefix Y T :=
      { toFun := fun y => restrictPrefix y T
        invFun := fun x t => x ⟨t, t.isLt⟩
        left_inv := fun y => rfl
        right_inv := fun x => rfl }
    rw [feedbackMass]
    simp_rw [hfactor, ← pathFull]
    change (∑ y, pathProduct T le_rfl (fullPrefixEquiv y)) = 1
    rw [fullPrefixEquiv.sum_comp]
    exact totalPrefix T le_rfl
  tfae_finish

#print axioms feedback_normalization_prefix_causality_sequential_kernels

end D5.S3.ObserverMemory.Prediction.FeedbackNormalizationCriterion
