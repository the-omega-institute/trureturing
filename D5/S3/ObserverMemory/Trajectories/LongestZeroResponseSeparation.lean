/- GID: D5/S3/ObserverMemory/Trajectories/LongestZeroResponseSeparation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/LongestZeroResponseSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Sqrt]
   utility: none
   digest: Uniform actual-history separation and exact persistent-state bit lower bounds. -/

import D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Base
import D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality

namespace D5.S3.ObserverMemory.Trajectories.LongestZeroResponseSeparation

open D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry
open D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse

set_option autoImplicit false

/-- Equality of the original finite direction responses recovers every filler parameter.
The two words may have different lengths and different left padding. -/
theorem response_separates (r : ℕ) (h g : ℕ → ℕ) (p p' R : ℕ)
    (hh : span (familyGaps r h) + 1 ≤ R)
    (hg : span (familyGaps r g) + 1 ≤ R)
    (heq : ∀ n, n ≤ R - 5 →
      direction (ones (familyGaps r h) p) R (p + span (familyGaps r h) + 1 + n) =
      direction (ones (familyGaps r g) p') R (p' + span (familyGaps r g) + 1 + n)) :
    ∀ i, i < r → h i = g i := by
  have hstep : ∀ r h, span (familyGaps (r + 1) h) =
      2 * (r + 1) + 4 + 4 * h 0 + span (familyGaps r (fun i => h (i + 1))) := by
    intro r h
    simp [familyGaps, span, List.sum_replicate]; omega
  have hmin : ∀ r h, 4 ≤ span (familyGaps r h) := by
    intro r h
    have hm := (family_head_dominates r h 0).1
    have hb := ((interval_geometry _ 0).1 _ hm).2.2.1
    dsimp at hb
    omega
  have hon : ∀ r h R n, span (familyGaps r h) + 1 + n ≤ R →
      responseModel r h R n = (r + n) % 2 := by
    intro r h R n hn
    cases r with
    | zero => simpa [familyGaps, span, responseModel] using
        (if_pos (show 5 + n ≤ R by simpa [familyGaps, span] using hn) :
          (if 5 + n ≤ R then n % 2 else 0) = n % 2)
    | succ r => exact if_pos hn
  have hdep : ∀ r h g, (∀ i, i < r → h i = g i) → familyGaps r h = familyGaps r g := by
    intro r
    induction r with
    | zero => intros; rfl
    | succ r ih =>
      intro h g he
      simp only [familyGaps, he 0 (by omega)]
      rw [ih (fun i => h (i + 1)) (fun i => g (i + 1)) (by
        intro i hi; exact he (i + 1) (by omega))]
  have hmodel : ∀ r h g R,
      span (familyGaps r h) + 1 ≤ R → span (familyGaps r g) + 1 ≤ R →
      (∀ n, n ≤ R - 5 → responseModel r h R n = responseModel r g R n) →
      ∀ i, i < r → h i = g i := by
    intro r
    induction r with
    | zero => intros; omega
    | succ r ih =>
      intro h g R hh hg heq
      have hnot : ∀ (u v : ℕ → ℕ),
          span (familyGaps (r + 1) u) + 1 ≤ R →
          span (familyGaps (r + 1) v) + 1 ≤ R →
          (∀ n, n ≤ R - 5 → responseModel (r + 1) u R n =
            responseModel (r + 1) v R n) →
          ¬ span (familyGaps (r + 1) u) < span (familyGaps (r + 1) v) := by
        intro u v hu hv huv hlt
        let n := R - (span (familyGaps (r + 1) v) + 1) + 1
        have hsu := hstep r u
        have hsv := hstep r v
        have hmv := hmin r (fun i => v (i + 1))
        have hn : n ≤ R - 5 := by dsimp [n]; omega
        have hun : span (familyGaps (r + 1) u) + 1 + n ≤ R := by
          dsimp [n]; omega
        have hvn : ¬ span (familyGaps (r + 1) v) + 1 + n ≤ R := by
          dsimp [n]; omega
        have hvtn : span (familyGaps r (fun i => v (i + 1))) + 1 + n ≤ R := by
          dsimp [n]; omega
        have ho := huv n hn
        rw [hon _ _ _ _ hun] at ho
        simp only [responseModel, if_neg hvn] at ho
        rw [hon _ _ _ _ hvtn] at ho
        omega
      have hlen : span (familyGaps (r + 1) h) = span (familyGaps (r + 1) g) := by
        have h₁ := hnot h g hh hg heq
        have h₂ := hnot g h hg hh (fun n hn => (heq n hn).symm)
        omega
      have hsh := hstep r h
      have hsg := hstep r g
      have hht : span (familyGaps r (fun i => h (i + 1))) + 1 ≤ R := by omega
      have hgt : span (familyGaps r (fun i => g (i + 1))) + 1 ≤ R := by omega
      have htail : ∀ n, n ≤ R - 5 →
          responseModel r (fun i => h (i + 1)) R n =
          responseModel r (fun i => g (i + 1)) R n := by
        intro n hn
        by_cases hl : span (familyGaps (r + 1) h) + 1 + n ≤ R
        · rw [hon _ _ _ _ (by omega), hon _ _ _ _ (by omega)]
        · have ho := heq n hn
          have hl' : ¬ span (familyGaps (r + 1) g) + 1 + n ≤ R := by omega
          simpa only [responseModel, if_neg hl, if_neg hl'] using ho
      have ht := ih (fun i => h (i + 1)) (fun i => g (i + 1)) R hht hgt htail
      have hts := congrArg span (hdep r (fun i => h (i + 1)) (fun i => g (i + 1)) ht)
      have hzero : h 0 = g 0 := by omega
      intro i hi
      cases i with
      | zero => exact hzero
      | succ i => exact ht i (by omega)
  apply hmodel r h g R hh hg
  intro n hn
  simpa only [direction_family] using heq n hn

/-- The source's exact real square-root parameter. -/
noncomputable def sourceQ (R : ℕ) : ℕ := ⌊Real.sqrt ((R : ℝ) / 5)⌋₊

/-- Extending the finite tuple by zero changes none of its source parameters. -/
def parameters (q : ℕ) (h : Fin (q - 1) → Fin (q + 1)) (i : ℕ) : ℕ :=
  if hi : i < q - 1 then h ⟨i, hi⟩ else 0

/-- Ones of the original family, with zeros on the left up to length `R`. -/
def windowOnes (R q : ℕ) (h : Fin (q - 1) → Fin (q + 1)) : Finset ℕ :=
  let gs := familyGaps (q - 1) (parameters q h)
  ones gs (R - (span gs + 1))

/-- Zero extension to an actual two-sided binary source. -/
def twoSided (s : Finset ℕ) (t : ℤ) : Bool := decide (0 ≤ t ∧ t.toNat ∈ s)

/-- The actual direction response to the same `R-5` new zero inputs. -/
noncomputable def finiteResponse (R q : ℕ) (h : Fin (q - 1) → Fin (q + 1))
    (n : Fin (R - 4)) : ℕ := direction (windowOnes R q h) R (R + n.val)

/-- A legal actual past in physical coordinates. The unread part is canonically
zero-filled, not supplied as future information. Negative positions are unrestricted.
The frame contains the whole current window; it is not an input to state updates. -/
structure History (R k : ℕ) where
  bits : ℤ → Bool
  current : ℕ
  window_fits : R ≤ current
  unread : ∀ t : ℤ, (current : ℤ) ≤ t → bits t = false
  lawful : ∀ t : ℤ, ∃ i : Fin k, bits (t + i.val) = false

/-- Appending the always-legal zero reads the next physical position. -/
def appendZero {R k : ℕ} (H : History R k) : History R k where
  bits := H.bits
  current := H.current + 1
  window_fits := by have := H.window_fits; omega
  unread := by intro t ht; exact H.unread t (by omega)
  lawful := H.lawful

/-- One legal input extension, with no access to any unread input. -/
def Extends {R k : ℕ} (H : History R k) (x : Bool) (H' : History R k) : Prop :=
  H'.current = H.current + 1 ∧
  ∀ t : ℤ, H'.bits t = if t = H.current then x else H.bits t

/-- The original window selector on an actual history. All candidate endpoints
lie in [current-R,current); negative earlier history cannot enter the window. -/
noncomputable def historyReadout {R k : ℕ} (H : History R k) : ℕ :=
  direction ((Finset.range H.current).filter fun a => H.bits a = true) R H.current

/-- Uniform source-family separation with the original square-root parameter,
legal two-sided histories, common grammar state one, and a common zero future. -/
theorem source_family_separates (R k : ℕ) (hR : 20 ≤ R) (hk : 2 ≤ k) :
    let q := sourceQ R
    2 ≤ q ∧
    (∀ h : Fin (q - 1) → Fin (q + 1),
      (∀ t : ℤ, ∃ i : Fin k, twoSided (windowOnes R q h) (t + i.val) = false) ∧
      R - 1 ∈ windowOnes R q h ∧ R - 2 ∉ windowOnes R q h ∧
      (∀ n : ℕ, twoSided (windowOnes R q h) (R + n) = false) ∧
      (∀ n, finiteResponse R q h n < 2)) ∧
    Function.Injective (finiteResponse R q) ∧
    ((Finset.univ : Finset (Fin (q - 1) → Fin (q + 1))).image
      (finiteResponse R q)).card = (q + 1) ^ (q - 1) ∧
    (∀ (S : Type) [Fintype S] (M : History R k → S)
      (T : Bool → S → S) (o : S → ℕ),
      (∀ H, o (M H) = historyReadout H) →
      (∀ H x H', Extends H x H' → M H' = T x (M H)) →
      (q + 1) ^ (q - 1) ≤ Nat.card (Set.range M) ∧
      (q - 1 : ℕ) * Real.logb 2 (q + 1) ≤
        Real.logb 2 (Nat.card (Set.range M)) ∧
      (q - 1 : ℕ) * Real.logb 2 (q + 1) ≤
        (⌈Real.logb 2 (Nat.card (Set.range M))⌉₊ : ℝ)) := by
  classical
  let q := sourceQ R
  have hq : 2 ≤ q := by
    apply (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr
    apply Real.le_sqrt_of_sq_le
    have hR' : (20 : ℝ) ≤ R := by exact_mod_cast hR
    norm_num
    linarith
  have hqR : 5 * q ^ 2 ≤ R := by
    have hfl : (q : ℝ) ≤ Real.sqrt ((R : ℝ) / 5) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have hs := Real.sq_sqrt (show 0 ≤ (R : ℝ) / 5 by positivity)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hh : (5 : ℝ) * (q : ℝ) ^ 2 ≤ R := by nlinarith
    exact_mod_cast hh
  have hfit : ∀ h : Fin (q - 1) → Fin (q + 1),
      span (familyGaps (q - 1) (parameters q h)) + 1 ≤ R := by
    have hb : ∀ (r H : ℕ) (h : ℕ → ℕ), (∀ i, i < r → h i ≤ H) →
        span (familyGaps r h) + 1 ≤ (r + 1) ^ 2 + 3 * (r + 1) + 1 + 4 * r * H := by
      intro r
      induction r with
      | zero => intro H h hh; simp [familyGaps, span]
      | succ r ih =>
        intro H h hh
        have ht := ih H (fun i => h (i + 1)) (by intro i hi; exact hh _ (by omega))
        have h0 := hh 0 (by omega)
        have hs : span (familyGaps (r + 1) h) =
            2 * (r + 1) + 4 + 4 * h 0 + span (familyGaps r (fun i => h (i + 1))) := by
          simp [familyGaps, span, List.sum_replicate]; omega
        nlinarith
    intro h
    have hh := hb (q - 1) q (parameters q h) (by
      intro i hi
      simp only [parameters, dif_pos hi]
      exact Nat.le_of_lt_succ (h ⟨i, hi⟩).isLt)
    have hqq : q - 1 + 1 = q := by omega
    rw [hqq] at hh
    nlinarith
  have hpositive : ∀ r h l, l ∈ familyGaps r h → 0 < l := by
    intro r
    induction r with
    | zero => intro h l hl; simp [familyGaps] at hl; omega
    | succ r ih =>
      intro h l hl
      simp only [familyGaps, List.mem_cons, List.mem_append] at hl
      rcases hl with rfl | hl | hl
      · omega
      · have := List.eq_of_mem_replicate hl; omega
      · exact ih _ _ hl
  have hspacing : ∀ (ls : List ℕ), (∀ l ∈ ls, 0 < l) → ∀ p a b,
      a ∈ ones ls p → b ∈ ones ls p → a < b → a + 2 ≤ b := by
    intro ls
    induction ls with
    | nil => intro hl p a b ha hb hab; simp [ones] at ha hb; omega
    | cons l ls ih =>
      intro hl p a b ha hb hab
      have hl0 := hl l (by simp)
      have ht : ∀ l ∈ ls, 0 < l := by intro l hm; exact hl l (by simp [hm])
      simp only [ones, Finset.mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · omega
      · have := ((ones_geometry ls (p + l + 1)).1 b hb).1; omega
      · have := ((ones_geometry ls (p + l + 1)).1 a ha).1; omega
      · exact ih ht _ _ _ ha hb hab
  have hlegal : ∀ h : Fin (q - 1) → Fin (q + 1),
      (∀ t : ℤ, ∃ i : Fin k, twoSided (windowOnes R q h) (t + i.val) = false) ∧
      R - 1 ∈ windowOnes R q h ∧ R - 2 ∉ windowOnes R q h ∧
      (∀ n : ℕ, twoSided (windowOnes R q h) (R + n) = false) ∧
      (∀ n, finiteResponse R q h n < 2) := by
    intro h
    let gs := familyGaps (q - 1) (parameters q h)
    let p := R - (span gs + 1)
    have hfits : span gs + 1 ≤ R := hfit h
    have hend : p + span gs = R - 1 := by dsimp [p]; omega
    have hsp : ∀ a ∈ windowOnes R q h, ∀ b ∈ windowOnes R q h,
        a < b → a + 2 ≤ b := by
      intro a ha b hb hab
      exact hspacing gs (hpositive _ _) p a b ha hb hab
    have hlast : R - 1 ∈ windowOnes R q h := by
      change R - 1 ∈ ones gs p
      rw [← hend]
      exact (ones_geometry gs p).2.2.2
    have hbefore : R - 2 ∉ windowOnes R q h := by
      intro hm
      have := hsp _ hm _ hlast (by omega)
      omega
    have hno11 : ∀ t : ℤ, ¬(twoSided (windowOnes R q h) t = true ∧
        twoSided (windowOnes R q h) (t + 1) = true) := by
      intro t hh
      simp only [twoSided, decide_eq_true_eq] at hh
      have := hsp _ hh.1.2 _ hh.2.2 (by omega)
      omega
    refine ⟨?_, hlast, hbefore, ?_, ?_⟩
    · intro t
      by_cases ht : twoSided (windowOnes R q h) t = false
      · exact ⟨⟨0, by omega⟩, by simpa using ht⟩
      · refine ⟨⟨1, by omega⟩, ?_⟩
        have ht' : twoSided (windowOnes R q h) t = true := by
          cases hbit : twoSided (windowOnes R q h) t <;> simp_all
        have hf := hno11 t
        simpa [ht'] using hf
    · intro n
      simp only [twoSided, decide_eq_false_iff_not]
      rintro ⟨_, hm⟩
      have hm' : R + n ∈ ones gs p := by
        simpa only [windowOnes, gs, p, q, ← Nat.cast_add, Int.toNat_natCast] using hm
      have := ((ones_geometry gs p).1 _ hm').2
      omega
    · intro n
      unfold finiteResponse direction
      split
      · decide
      · exact Nat.mod_lt _ (by decide)
  have hinj : Function.Injective (finiteResponse R q) := by
    intro h g heq
    apply funext
    intro i
    let sh := span (familyGaps (q - 1) (parameters q h))
    let sg := span (familyGaps (q - 1) (parameters q g))
    have hh := hfit h
    have hg := hfit g
    have hs := response_separates (q - 1) (parameters q h) (parameters q g)
      (R - (sh + 1)) (R - (sg + 1)) R hh hg (by
        intro n hn
        have hn' : n < R - 4 := by omega
        have ho := congrFun heq ⟨n, hn'⟩
        have heh : R - (sh + 1) + sh + 1 + n = R + n := by dsimp [sh]; omega
        have heg : R - (sg + 1) + sg + 1 + n = R + n := by dsimp [sg]; omega
        change direction (windowOnes R q h) R (R - (sh + 1) + sh + 1 + n) =
          direction (windowOnes R q g) R (R - (sg + 1) + sg + 1 + n)
        rw [heh, heg]
        exact ho)
    have hi := hs i.val i.isLt
    apply Fin.ext
    have hil : i.val < q - 1 := i.isLt
    simpa only [parameters, dif_pos hil] using hi
  refine ⟨hq, hlegal, hinj, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp [q]
  · intro S _ M T o hread hstep
    let realize : (Fin (q - 1) → Fin (q + 1)) → ℕ → History R k := fun h n =>
      { bits := twoSided (windowOnes R q h)
        current := R + n
        window_fits := by omega
        unread := by
          intro t ht
          have ht0 : 0 ≤ t := by omega
          have heq : t = (R + (t.toNat - R) : ℕ) := by omega
          rw [heq]
          exact (hlegal h).2.2.2.1 _
        lawful := (hlegal h).1 }
    have hzero : ∀ H : History R k, Extends H false (appendZero H) := by
      intro H
      refine ⟨rfl, ?_⟩
      intro t
      change H.bits t = _
      split_ifs with ht
      · subst t; exact H.unread _ le_rfl
      · rfl
    obtain ⟨completion, hcompletion⟩ :=
      D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality.prediction_completion_universality
        appendZero historyReadout M (T false) o
        (by funext H; exact hstep H false (appendZero H) (hzero H))
        (by funext H; exact (hread H).symm)
    have hsource : ∀ h n, (appendZero^[n]) (realize h 0) = realize h n := by
      intro h n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        rfl
    have hactual : ∀ h n, historyReadout (realize h n) =
        direction (windowOnes R q h) R (R + n) := by
      intro h n
      have hset : ((Finset.range (R + n)).filter fun (a : ℕ) =>
          twoSided (windowOnes R q h) (a : ℤ) = true) = windowOnes R q h := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, twoSided, decide_eq_true_eq,
          Int.natCast_nonneg, Int.toNat_natCast, true_and]
        constructor
        · exact fun ha => ha.2
        · intro ha
          have hb := ((ones_geometry (familyGaps (q - 1) (parameters q h))
            (R - (span (familyGaps (q - 1) (parameters q h)) + 1))).1 a ha).2
          have hf := hfit h
          exact ⟨by omega, ha⟩
      change direction _ R (R + n) = _
      rw [hset]
    let state : (Fin (q - 1) → Fin (q + 1)) → Set.range M :=
      fun h => ⟨M (realize h 0), ⟨realize h 0, rfl⟩⟩
    have hstate : Function.Injective state := by
      intro h g heq
      apply hinj
      funext n
      have he : M (realize h 0) = M (realize g 0) := congrArg Subtype.val heq
      have hh := congrFun (congrFun hcompletion (realize h 0)) n.val
      have hg := congrFun (congrFun hcompletion (realize g 0)) n.val
      change historyReadout ((appendZero^[n.val]) (realize h 0)) =
        completion (M (realize h 0)) n.val at hh
      change historyReadout ((appendZero^[n.val]) (realize g 0)) =
        completion (M (realize g 0)) n.val at hg
      rw [hsource, hactual] at hh hg
      exact hh.trans ((congrArg (fun s => completion s n.val) he).trans hg.symm)
    letI := Fintype.ofFinite (Set.range M)
    have hcard : (q + 1) ^ (q - 1) ≤ Nat.card (Set.range M) := by
      have hc := Fintype.card_le_of_injective state hstate
      simpa [Nat.card_eq_fintype_card] using hc
    have hlog : (q - 1 : ℕ) * Real.logb 2 (q + 1) ≤
        Real.logb 2 (Nat.card (Set.range M)) := by
      have hc : ((q + 1 : ℕ) : ℝ) ^ (q - 1) ≤ (Nat.card (Set.range M) : ℝ) := by
        exact_mod_cast hcard
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by positivity : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) ^ (q - 1)) hc
      simpa only [Real.logb_pow, Nat.cast_add, Nat.cast_one] using hl
    exact ⟨hcard, hlog, hlog.trans (Nat.le_ceil _)⟩

end D5.S3.ObserverMemory.Trajectories.LongestZeroResponseSeparation
