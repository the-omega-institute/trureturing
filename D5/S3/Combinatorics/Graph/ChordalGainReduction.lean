/- GID: D5/S3/Combinatorics/Graph/ChordalGainReduction
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lifting short additive gain residuals through a modulus -/

import OmegaBuild.Commands
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Combinatorics.SimpleGraph.Basic

compile_only_with_mathlib

/-! # Lifting short additive gain residuals through a modulus -/

namespace SimpleGraph.GainReduction

variable {V I A : Type*} {G : SimpleGraph V}

/-- An additive residual uses at most `k` generators when zero belongs to the generator set. -/
def Short [AddCommMonoid A] (U : Set A) (k : ℕ) (r : A) : Prop :=
  ∃ terms : Fin k → A, (∀ t, terms t ∈ U) ∧ ∑ t, terms t = r

/-- Reduction of each integer coordinate modulo the same modulus. -/
def reduce (q : ℕ) : (I → ℤ) →+ (I → ZMod q) where
  toFun x i := x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; exact Int.cast_add (x i) (y i)

theorem Short.map [AddCommMonoid A] {B : Type*} [AddCommMonoid B] (f : A →+ B)
    {U : Set A} {k : ℕ} {r : A} (h : Short U k r) : Short (f '' U) k (f r) := by
  obtain ⟨terms, hterms, hsum⟩ := h
  exact ⟨fun t => f (terms t), fun t => ⟨terms t, hterms t, rfl⟩,
    by rw [← map_sum, hsum]⟩

theorem Short.exists_lift [AddCommMonoid A] {B : Type*} [AddCommMonoid B] (f : A →+ B)
    {U : Set A} {k : ℕ} {r : B} (h : Short (f '' U) k r) :
    ∃ b, Short U k b ∧ f b = r := by
  classical
  obtain ⟨terms, hterms, hsum⟩ := h
  choose lifts hlifts hmap using hterms
  refine ⟨∑ t, lifts t, ⟨lifts, hlifts, rfl⟩, ?_⟩
  simpa only [map_sum, hmap] using hsum

theorem Short.neg {U : Set (I → ℤ)} {k : ℕ} {r : I → ℤ}
    (h : Short U k r) (hsymm : ∀ u ∈ U, -u ∈ U) : Short U k (-r) := by
  obtain ⟨terms, hterms, hsum⟩ := h
  exact ⟨fun t => -terms t, fun t => hsymm _ (hterms t), by rw [Finset.sum_neg_distrib, hsum]⟩

private theorem short_coordinate_bound {U : Set (I → ℤ)} {k : ℕ} {r : I → ℤ} {B : ℕ}
    (h : Short U k r) (hU : ∀ u ∈ U, ∀ i, |u i| ≤ B) (i : I) :
    |r i| ≤ (k : ℤ) * B := by
  obtain ⟨terms, hterms, rfl⟩ := h
  simp only [Finset.sum_apply]
  exact (Finset.abs_sum_le_sum_abs _ _).trans <|
    (Finset.sum_le_sum fun t _ => hU _ (hterms t) i).trans_eq (by simp)

open Classical in
/-- An oriented choice of representatives yields skew integral residuals. Their triangle
sums agree with the original gains because the coordinate discrepancies are too short
to be nonzero multiples of the modulus. -/
theorem exists_integral_residuals_of_bounded_modular_potential [LinearOrder V]
    (g : V → V → I → ℤ) (hrev : ∀ v w, G.Adj v w → g w v = -g v w)
    (U : Set (I → ℤ)) (hsymm : ∀ u ∈ U, -u ∈ U)
    {B : ℕ} (hU : ∀ u ∈ U, ∀ i, |u i| ≤ B)
    (htri : ∀ v w x, G.Adj v w → G.Adj w x → G.Adj v x →
      ∀ i, |g v w i + g w x i - g v x i| ≤ B)
    {k q : ℕ} (hq : (3 * k + 1) * B < q) (p : V → I → ZMod q)
    (hp : ∀ v w, G.Adj v w →
      Short (reduce q '' U) k (reduce q (g v w) - (p w - p v))) :
    ∃ r : V → V → I → ℤ,
      (∀ v w, G.Adj v w → r w v = -r v w) ∧
      (∀ v w, G.Adj v w → Short U k (r v w)) ∧
      ∀ v w x, G.Adj v w → G.Adj w x → G.Adj v x →
        r v w + r w x - r v x = g v w + g w x - g v x := by
  have lift (v w : V) (h : G.Adj v w) :=
    (hp v w h).exists_lift (reduce q)
  let forward (v w : V) := if h : G.Adj v w then (lift v w h).choose else 0
  have hf (v w : V) (h : G.Adj v w) :
      Short U k (forward v w) ∧ reduce q (forward v w) = reduce q (g v w) - (p w - p v) := by
    simpa only [forward, dite_eq_left h] using (lift v w h).choose_spec
  let r (v w : V) := if v < w then forward v w else -forward w v
  have hskew (v w : V) (h : G.Adj v w) : r w v = -r v w := by
    rcases lt_or_gt_of_ne h.ne with hlt | hlt
    · simp [r, hlt, hlt.not_gt]
    · simp [r, hlt, hlt.not_gt]
  have hr (v w : V) (h : G.Adj v w) : Short U k (r v w) := by
    by_cases hlt : v < w
    · simpa [r, hlt] using (hf v w h).1
    · simpa [r, hlt] using (hf w v h.symm).1.neg hsymm
  have hmod (v w : V) (h : G.Adj v w) :
      reduce q (r v w) = reduce q (g v w) - (p w - p v) := by
    by_cases hlt : v < w
    · simpa [r, hlt] using (hf v w h).2
    · simp only [r, ite_eq_right hlt]
      rw [map_neg, (hf w v h.symm).2, hrev v w h, map_neg]
      abel
  refine ⟨r, hskew, hr, fun v w x hvw hwx hvx => ?_⟩
  let delta := r v w + r w x - r v x - (g v w + g w x - g v x)
  have hz : reduce q delta = 0 := by
    simp only [delta, map_sub, map_add, hmod v w hvw, hmod w x hwx, hmod v x hvx]
    abel
  funext i
  have hdvd : (q : ℤ) ∣ delta i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hz i)
  have hbound : |delta i| < (q : ℤ) := by
    change |r v w i + r w x i - r v x i - (g v w i + g w x i - g v x i)| < _
    have h1 := abs_add_le (r v w i + r w x i - r v x i) (-(g v w i + g w x i - g v x i))
    have h2 := abs_add_le (r v w i + r w x i) (-(r v x i))
    simp only [abs_neg, ← sub_eq_add_neg] at h1 h2
    have h3 := abs_add_le (r v w i) (r w x i)
    have hq' : ((3 : ℤ) * k + 1) * B < q := by exact_mod_cast hq
    linarith [short_coordinate_bound (hr v w hvw) hU i,
      short_coordinate_bound (hr w x hwx) hU i, short_coordinate_bound (hr v x hvx) hU i,
      htri v w x hvw hwx hvx i]
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd hbound)

/-- The lifting bound specialized to unit-coordinate generators and defects. -/
theorem exists_integral_residuals_of_modular_potential [LinearOrder V]
    (g : V → V → I → ℤ) (hrev : ∀ v w, G.Adj v w → g w v = -g v w)
    (U : Set (I → ℤ)) (hsymm : ∀ u ∈ U, -u ∈ U)
    (hU : ∀ u ∈ U, ∀ i, |u i| ≤ 1)
    (htri : ∀ v w x, G.Adj v w → G.Adj w x → G.Adj v x →
      ∀ i, |g v w i + g w x i - g v x i| ≤ 1)
    {k q : ℕ} (hq : 3 * k + 1 < q) (p : V → I → ZMod q)
    (hp : ∀ v w, G.Adj v w →
      Short (reduce q '' U) k (reduce q (g v w) - (p w - p v))) :
    ∃ r : V → V → I → ℤ,
      (∀ v w, G.Adj v w → r w v = -r v w) ∧
      (∀ v w, G.Adj v w → Short U k (r v w)) ∧
      ∀ v w x, G.Adj v w → G.Adj w x → G.Adj v x →
        r v w + r w x - r v x = g v w + g w x - g v x :=
  exists_integral_residuals_of_bounded_modular_potential g hrev U hsymm hU htri
    (by simpa only [mul_one] using hq) p hp

end SimpleGraph.GainReduction
