/- GID: D5/S1/Digit/Infinite/SharpErrorThreshold
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SharpErrorThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp closed and open noise thresholds with residual decision margins. -/

import D5.S1.Digit.Infinite.CriticalPrefixSeparation
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SharpErrorThreshold

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.CriticalPrefixSeparation
open Set

/-- Actual full-source records for a fixed incoming guard and an open or closed radius. -/
def records (s : Bool) (h : ℕ) (ε : ℝ) (strict : Bool) : Set (Fin (h + 1) → ℝ) :=
  {r | ∃ x : LegalDigits, stateAddress s x ∧
    if strict then dist r (response h x) < ε else dist r (response h x) ≤ ε}

/-- Every compatible full source must have the decoded prefix. -/
def recovers (s : Bool) (h : ℕ) (ε : ℝ) (strict : Bool)
    (decode : records s h ε strict → (Fin h → Label)) : Prop :=
  ∀ (r : records s h ε strict) (x : LegalDigits), stateAddress s x →
    (if strict then dist r.val (response h x) < ε else dist r.val (response h x) ≤ ε) →
    decode r = windowPrefix h x

/-- The adjacent-sample residual at an observed window. -/
noncomputable def sampleResidual (h : ℕ) (r : Fin (h + 1) → ℝ) (j : Fin h) : ℝ :=
  r ⟨j.val, by omega⟩ + g * r ⟨j.val + 1, by omega⟩

/-- Choose a translation with least distance to the residual. -/
noncomputable def nearest (d : ℝ) : Label := by
  letI : Finite Label := Finite.of_injective (fun l : Label => l.val) Subtype.val_injective
  letI : Nonempty Label := ⟨nullLabel⟩
  exact Classical.choose (Finite.exists_min (fun l : Label => |d - offset l|))

/-- Decode each observed residual by its nearest translation. -/
noncomputable def residualDecode (h : ℕ) (r : Fin (h + 1) → ℝ) : Fin h → Label :=
  fun j => nearest (sampleResidual h r j)

private theorem nearest_le (d : ℝ) (l : Label) :
    |d - offset (nearest d)| ≤ |d - offset l| := by
  have : Finite Label := Finite.of_injective (fun l : Label => l.val) Subtype.val_injective
  have : Nonempty Label := ⟨nullLabel⟩
  exact Classical.choose_spec (Finite.exists_min (fun l : Label => |d - offset l|)) l

private theorem residual_error (h : ℕ) (r : Fin (h + 1) → ℝ)
    (x : LegalDigits) (j : Fin h) :
    |sampleResidual h r j - offset (window x j)| ≤ 2 * t * dist r (response h x) := by
  have h0 := dist_le_pi_dist r (response h x) ⟨j.val, by omega⟩
  have h1 := dist_le_pi_dist r (response h x) ⟨j.val + 1, by omega⟩
  have hg : 0 ≤ g := (pow_pos golden_facts.1 3).le
  have he : sampleResidual h r j - offset (window x j) =
      (r ⟨j.val, by omega⟩ - response h x ⟨j.val, by omega⟩) +
      g * (r ⟨j.val + 1, by omega⟩ - response h x ⟨j.val + 1, by omega⟩) := by
    dsimp only [sampleResidual, response]
    linarith only [residual x j]
  rw [Real.dist_eq] at h0 h1
  rw [he]
  calc
    _ ≤ |r ⟨j.val, by omega⟩ - response h x ⟨j.val, by omega⟩| +
        |g * (r ⟨j.val + 1, by omega⟩ - response h x ⟨j.val + 1, by omega⟩)| := abs_add_le _ _
    _ ≤ dist r (response h x) + g * dist r (response h x) := by
      rw [abs_mul, abs_of_nonneg hg]
      exact add_le_add h0 (mul_le_mul_of_nonneg_left h1 hg)
    _ = 2 * t * dist r (response h x) := by
      nlinarith [congrArg (fun z : ℝ => z * dist r (response h x)) golden_facts.2.2.2]

private theorem nearest_strict (d : ℝ) (l : Label) (he : |d - offset l| < t ^ 2 / 2) :
    nearest d = l ∧ ∀ k : Label, k ≠ l → |d - offset l| < |d - offset k| := by
  have hs (k : Label) (hk : k ≠ l) : |d - offset l| < |d - offset k| := by
    have hg := label_gap l k hk.symm
    have hu := abs_sub_le (offset l) d (offset k)
    rw [abs_sub_comm (offset l) d] at hu
    linarith
  refine ⟨?_, hs⟩
  by_contra hn
  exact (not_lt_of_ge (nearest_le d l)) (hs (nearest d) hn)

private theorem boundary_margin (d : ℝ) (l k : Label) (hk : k ≠ l) (B : ℝ)
    (he : |d - offset l| ≤ B) :
    t ^ 2 / 2 - B ≤ |d - (offset l + offset k) / 2| := by
  have hg := label_gap l k hk.symm
  have hu : |offset l - offset k| ≤
      2 * |d - (offset l + offset k) / 2| + 2 * |d - offset l| := by
    calc
      _ = |2 * (d - (offset l + offset k) / 2) - 2 * (d - offset l)| := by
        congr 1
        ring
      _ ≤ |2 * (d - (offset l + offset k) / 2)| + |2 * (d - offset l)| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_mul]; norm_num
  linarith

private theorem decode_closed (h : ℕ) (r : Fin (h + 1) → ℝ) (x : LegalDigits)
    (ε : ℝ) (he : ε < t / 4) (hr : dist r (response h x) ≤ ε) :
    residualDecode h r = windowPrefix h x := by
  funext j
  change nearest (sampleResidual h r j) = window x j
  apply (nearest_strict _ _ ?_).1
  have hb := (residual_error h r x j).trans
    (mul_le_mul_of_nonneg_left hr (by have := golden_facts.1; positivity : 0 ≤ 2 * t))
  have ht := mul_lt_mul_of_pos_left he (by have := golden_facts.1; positivity : 0 < 2 * t)
  nlinarith

private theorem decode_open (h : ℕ) (r : Fin (h + 1) → ℝ) (x : LegalDigits)
    (ε : ℝ) (he : ε ≤ t / 4) (hr : dist r (response h x) < ε) :
    residualDecode h r = windowPrefix h x := by
  funext j
  change nearest (sampleResidual h r j) = window x j
  apply (nearest_strict _ _ ?_).1
  have hb := (residual_error h r x j).trans_lt
    (mul_lt_mul_of_pos_left hr (by have := golden_facts.1; positivity : 0 < 2 * t))
  have ht := mul_le_mul_of_nonneg_left he (by have := golden_facts.1; positivity : 0 ≤ 2 * t)
  nlinarith

private theorem critical_collision (h : ℕ) (hh : 1 ≤ h) (s : Bool) :
    ∃ (r : Fin (h + 1) → ℝ) (x y : LegalDigits),
      stateAddress s x ∧ stateAddress s y ∧ windowPrefix h x ≠ windowPrefix h y ∧
      dist r (response h x) = t / 4 ∧ dist r (response h y) = t / 4 := by
  have hf := (D5.S1.Digit.Infinite.CriticalPrefixSeparation.result h hh).2.2.1
  refine ⟨fun _ => t / 4, fiveRun 0, fiveStream,
    (hf.2.2.2 s).1, (hf.2.2.2 s).2, hf.2.2.1, ?_, ?_⟩
  · rw [hf.1, dist_pi_const, Real.dist_eq, sub_zero,
      abs_of_pos (div_pos golden_facts.1 (by norm_num))]
  · rw [hf.2.1, dist_pi_const, Real.dist_eq]
    have he : t / 4 - t / 2 = -(t / 4) := by ring
    rw [he, abs_neg, abs_of_pos (div_pos golden_facts.1 (by norm_num))]

private theorem closed_necessary (h : ℕ) (hh : 1 ≤ h) (s : Bool) (ε : ℝ)
    (decode : records s h ε false → (Fin h → Label)) (hd : recovers s h ε false decode) :
    ε < t / 4 := by
  by_contra hn
  have he : t / 4 ≤ ε := le_of_not_gt hn
  obtain ⟨r,x,y,hx,hy,hp,hrx,hry⟩ := critical_collision h hh s
  let R : records s h ε false := ⟨r,x,hx,by simpa only [Bool.false_eq_true, ↓reduceIte, hrx] using he⟩
  exact hp ((hd R x hx (by change dist r (response h x) ≤ ε; rwa [hrx])).symm.trans
    (hd R y hy (by change dist r (response h y) ≤ ε; rwa [hry])))

private theorem open_necessary (h : ℕ) (hh : 1 ≤ h) (s : Bool) (ε : ℝ)
    (decode : records s h ε true → (Fin h → Label)) (hd : recovers s h ε true decode) :
    ε ≤ t / 4 := by
  by_contra hn
  have he : t / 4 < ε := lt_of_not_ge hn
  obtain ⟨r,x,y,hx,hy,hp,hrx,hry⟩ := critical_collision h hh s
  let R : records s h ε true := ⟨r,x,hx,by simpa only [↓reduceIte, hrx] using he⟩
  exact hp ((hd R x hx (by change dist r (response h x) < ε; rwa [hrx])).symm.trans
    (hd R y hy (by change dist r (response h y) < ε; rwa [hry])))

private theorem closed_accuracy (h : ℕ) (r : Fin (h + 1) → ℝ) (x : LegalDigits)
    (ε : ℝ) (he : ε < t / 4) (hr : dist r (response h x) ≤ ε) (j : Fin h) :
    |sampleResidual h r j - offset (window x j)| ≤ 2 * t * ε ∧
    (∀ l : Label, l ≠ window x j →
      |sampleResidual h r j - offset (window x j)| < |sampleResidual h r j - offset l|) ∧
    (∀ l : Label, l ≠ window x j → t ^ 2 / 2 - 2 * t * ε ≤
      |sampleResidual h r j - (offset (window x j) + offset l) / 2|) := by
  have hb := (residual_error h r x j).trans
    (mul_le_mul_of_nonneg_left hr (by have := golden_facts.1; positivity))
  have ht := mul_lt_mul_of_pos_left he (by have := golden_facts.1; positivity : 0 < 2 * t)
  have hs : |sampleResidual h r j - offset (window x j)| < t ^ 2 / 2 := by nlinarith
  exact ⟨hb, (nearest_strict _ _ hs).2, fun l hl => boundary_margin _ _ l hl _ hb⟩

private theorem rational_approximation (h : ℕ) (r : Fin (h + 1) → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ p : Fin (h + 1) → ℚ, dist (fun j => (p j : ℝ)) r ≤ ρ := by
  choose p hp using fun j : Fin (h + 1) => exists_rat_near (r j) hρ
  refine ⟨p, (dist_pi_le_iff hρ.le).mpr ?_⟩
  intro j
  rw [Real.dist_eq, abs_sub_comm]
  exact (hp j).le

/-- Full-source prefix recovery has a strict closed threshold and an inclusive
positive open threshold, with nearest-residual margins and rational approximation stability. -/
theorem result (h : ℕ) (hh : 1 ≤ h) (s : Bool) (ε : ℝ) (hε : 0 ≤ ε) :
    ((∃ decode : records s h ε false → (Fin h → Label), recovers s h ε false decode) ↔
      ε < t / 4) ∧
    ((0 < ε ∧ ∃ decode : records s h ε true → (Fin h → Label), recovers s h ε true decode) ↔
      0 < ε ∧ ε ≤ t / 4) ∧
    (ε < t / 4 →
      0 < t ^ 2 / 2 - 2 * t * ε ∧
      t ^ 2 / 2 - 2 * t * ε = 2 * t * (t / 4 - ε) ∧
      recovers s h ε false (fun r => residualDecode h r.val) ∧
      ∀ (r : Fin (h + 1) → ℝ) (x : LegalDigits), stateAddress s x →
        dist r (response h x) ≤ ε → ∀ j : Fin h,
          |sampleResidual h r j - offset (window x j)| ≤ 2 * t * ε ∧
          (∀ l : Label, l ≠ window x j →
            |sampleResidual h r j - offset (window x j)| < |sampleResidual h r j - offset l|) ∧
          (∀ l : Label, l ≠ window x j → t ^ 2 / 2 - 2 * t * ε ≤
            |sampleResidual h r j - (offset (window x j) + offset l) / 2|)) ∧
    (0 < ε → ε ≤ t / 4 →
      recovers s h ε true (fun r => residualDecode h r.val) ∧
      ∀ (r : Fin (h + 1) → ℝ) (x : LegalDigits), stateAddress s x →
        dist r (response h x) < ε → ∀ j : Fin h,
          |sampleResidual h r j - offset (window x j)| < 2 * t * ε ∧
          0 < t ^ 2 / 2 - |sampleResidual h r j - offset (window x j)| ∧
          (∀ l : Label, l ≠ window x j →
            |sampleResidual h r j - offset (window x j)| < |sampleResidual h r j - offset l|) ∧
          (∀ l : Label, l ≠ window x j →
            t ^ 2 / 2 - |sampleResidual h r j - offset (window x j)| ≤
            |sampleResidual h r j - (offset (window x j) + offset l) / 2|)) ∧
    (∀ ρ : ℝ, 0 < ρ → ε + ρ < t / 4 → ∀ r : Fin (h + 1) → ℝ,
      (∃ p : Fin (h + 1) → ℚ, dist (fun j => (p j : ℝ)) r ≤ ρ) ∧
      ∀ (p : Fin (h + 1) → ℚ), dist (fun j => (p j : ℝ)) r ≤ ρ →
        ∀ x : LegalDigits, stateAddress s x → dist r (response h x) ≤ ε →
          residualDecode h (fun j => (p j : ℝ)) = windowPrefix h x ∧
          ∀ j : Fin h, |sampleResidual h (fun j => (p j : ℝ)) j - offset (window x j)| ≤
            2 * t * (ε + ρ) ∧ 2 * t * (ε + ρ) < t ^ 2 / 2) ∧
    (records s h ε false).Nonempty := by
  have hp : 0 < 2 * t := by have := golden_facts.1; positivity
  have hclosed (he : ε < t / 4) : recovers s h ε false (fun r => residualDecode h r.val) := by
    intro r x _ hr
    exact decode_closed h r.val x ε he hr
  have hopen (he : ε ≤ t / 4) : recovers s h ε true (fun r => residualDecode h r.val) := by
    intro r x _ hr
    exact decode_open h r.val x ε he hr
  refine ⟨⟨?_,fun he => ⟨_,hclosed he⟩⟩,⟨?_,?_⟩,?_,?_,?_,?_⟩
  · rintro ⟨decode,hd⟩
    exact closed_necessary h hh s ε decode hd
  · rintro ⟨he,decode,hd⟩
    exact ⟨he,open_necessary h hh s ε decode hd⟩
  · rintro ⟨he,ht⟩
    exact ⟨he,_,hopen ht⟩
  · intro he
    have hm : 0 < t ^ 2 / 2 - 2 * t * ε := by
      have ht := mul_lt_mul_of_pos_left he hp
      nlinarith
    refine ⟨hm,by ring,hclosed he,?_⟩
    intro r x _ hr j
    exact closed_accuracy h r x ε he hr j
  · intro _ he
    refine ⟨hopen he,?_⟩
    intro r x _ hr j
    have hb := (residual_error h r x j).trans_lt (mul_lt_mul_of_pos_left hr hp)
    have ht := mul_le_mul_of_nonneg_left he hp.le
    have hs : |sampleResidual h r j - offset (window x j)| < t ^ 2 / 2 := by nlinarith
    exact ⟨hb,by linarith,(nearest_strict _ _ hs).2,
      fun l hl => boundary_margin _ _ l hl _ le_rfl⟩
  · intro ρ hρ he r
    refine ⟨rational_approximation h r ρ hρ,?_⟩
    intro p hr x _ hx
    have hd : dist (fun j => (p j : ℝ)) (response h x) ≤ ε + ρ := by
      have hu := dist_triangle (fun j => (p j : ℝ)) r (response h x)
      linarith
    refine ⟨decode_closed h _ x (ε + ρ) he hd,?_⟩
    intro j
    have hb := (residual_error h _ x j).trans (mul_le_mul_of_nonneg_left hd hp.le)
    have ht := mul_lt_mul_of_pos_left he hp
    exact ⟨hb,by nlinarith⟩
  · have hs := ((D5.S1.Digit.Infinite.CriticalPrefixSeparation.result h hh).2.2.1.2.2.2 s).1
    refine ⟨response h (fiveRun 0),fiveRun 0,hs,?_⟩
    simpa only [Bool.false_eq_true, ↓reduceIte, dist_self] using hε

end D5.S1.Digit.Infinite.SharpErrorThreshold
