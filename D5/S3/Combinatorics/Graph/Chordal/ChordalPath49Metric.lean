/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalPath49Metric
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The order-49 Cayley metric converts word-budget obstructions on path powers to metric obstructions. -/

import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.ChordalPath49
import OmegaMath.Combinatorics.Graph.GroupWordMetric
import D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
import Mathlib.Tactic.Abel

compile_only_with_mathlib

/-!
Omega original.

The cyclic width-three witness in its bi-invariant Cayley word metric.
-/

namespace ChordalPath49

open SimpleGraph.BanachPathPower GroupWordMetric

abbrev M := Multiplicative H

def letters : Set M := {v | Multiplicative.toAdd v ∈ generators}

theorem word_iff (n : ℕ) (x : H) :
    Fits letters n (Multiplicative.ofAdd x) ↔ WordBudget n x := by
  constructor
  · rintro ⟨l, hmem, hl, hp⟩
    refine ⟨l.map Multiplicative.toAdd, ?_, by simpa, ?_⟩
    · intro y hy
      have he : ∃ v : M, v ∈ l ∧ Multiplicative.toAdd v = y := List.mem_map.mp hy
      obtain ⟨v, hv, he⟩ := he
      rw [← he]
      exact hmem v hv
    · have he (q : List M) : (q.map Multiplicative.toAdd).sum = Multiplicative.toAdd q.prod := by
        induction q with
        | nil => rfl
        | cons a q ih => simpa only [List.map_cons, List.sum_cons, List.prod_cons, ih] using
            (show Multiplicative.toAdd a + Multiplicative.toAdd q.prod =
              Multiplicative.toAdd (a * q.prod) from rfl)
      rw [he, hp]
      rfl
  · rintro ⟨l, hmem, hl, hp⟩
    refine ⟨l.map Multiplicative.ofAdd, ?_, by simpa, ?_⟩
    · intro y hy
      have he : ∃ v : H, v ∈ l ∧ Multiplicative.ofAdd v = y := List.mem_map.mp hy
      obtain ⟨v, hv, he⟩ := he
      rw [← he]
      exact hmem v hv
    · have he (q : List H) : (q.map Multiplicative.ofAdd).prod = Multiplicative.ofAdd q.sum := by
        induction q with
        | nil => rfl
        | cons a q ih =>
          simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
          rfl
      rw [he, hp]

theorem letters_inv : ∀ u ∈ letters, u⁻¹ ∈ letters :=
  fun _ hu => generators_neg hu

theorem letters_conj (a : M) : ∀ u ∈ letters, a * u * a⁻¹ ∈ letters := by
  intro u hu
  rwa [mul_comm a u, mul_assoc, mul_inv_cancel, mul_one]

theorem letters_generate : Generates letters := by
  have h1 : Fits letters 2 (Multiplicative.ofAdd (1 : H)) := (word_iff _ _).2
    ⟨[3, -2], by decide, by decide, by decide⟩
  have hn (n : ℕ) : Fits letters (2 * n) (Multiplicative.ofAdd (n : H)) := by
    induction n with
    | zero => exact Fits.one
    | succ n ih =>
      have he : Multiplicative.ofAdd (n : H) * Multiplicative.ofAdd (1 : H) =
          Multiplicative.ofAdd (↑(n + 1) : H) := by
        rw [Nat.cast_succ]
        rfl
      rw [Nat.mul_succ, ← he]
      exact ih.mul h1
  intro x
  refine ⟨2 * x.toAdd.val, ?_⟩
  have hx : Multiplicative.ofAdd (↑x.toAdd.val : H) = x :=
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val x.toAdd)
  exact Eq.mp (congrArg (Fits letters (2 * x.toAdd.val)) hx) (hn x.toAdd.val)

@[instance_reducible]
noncomputable def cayleyMetric : MetricSpace M := metric letters_generate letters_inv

theorem cayley_left : letI := cayleyMetric; IsIsometricSMul M M :=
  left_isometric letters_generate letters_inv

theorem cayley_right : letI := cayleyMetric; IsIsometricSMul Mᵐᵒᵖ M :=
  right_isometric letters_generate letters_inv letters_conj

theorem word_iff_distance (n : ℕ) (x y : H) :
    letI := cayleyMetric
    Dist.dist (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) ≤ (n : ℝ) ↔
      WordBudget n (x - y) := by
  let := cayleyMetric
  change (length letters_generate (Multiplicative.ofAdd (-x + y)) : ℝ) ≤ (n : ℝ) ↔ _
  rw [← length_inv letters_generate letters_inv (Multiplicative.ofAdd (-x + y))]
  have he : (Multiplicative.ofAdd (-x + y))⁻¹ = Multiplicative.ofAdd (x - y) := by
    change -(-x + y) = x - y
    abel
  rw [he, Nat.cast_le, length_le_iff, word_iff]

/-- Extend the gains on increasing pairs to a skew gain. -/
def skew {n : ℕ} (f : ℕ → ℕ → H) (i j : Fin n) : H :=
  if i.val < j.val then f i.val j.val else -f j.val i.val

theorem skew_rev {n : ℕ} (f : ℕ → ℕ → H) {i j : Fin n} (hne : i ≠ j) :
    skew f j i = -skew f i j := by
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · simp [skew, h, h.not_gt]
  · simp [skew, h, h.not_gt]

theorem skew_triangles {n k : ℕ} (f : ℕ → ℕ → H)
    (ht : ∀ i j l : ℕ, i < j → j < l → l ≤ i + k → f i j + f j l - f i l ∈ alphabet)
    {a b c : Fin n} (hab : (pathPower n k).Adj a b)
    (hbc : (pathPower n k).Adj b c) (hac : (pathPower n k).Adj a c) :
    skew f a b + skew f b c - skew f a c ∈ alphabet := by
  have split (a b c : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val)
      (hc : c.val ≤ a.val + k) :
      (skew f a b + skew f b c - skew f a c ∈ alphabet) ∧
      (skew f a c + skew f c b - skew f a b ∈ alphabet) ∧
      (skew f b a + skew f a c - skew f b c ∈ alphabet) ∧
      (skew f b c + skew f c a - skew f b a ∈ alphabet) ∧
      (skew f c a + skew f a b - skew f c b ∈ alphabet) ∧
      (skew f c b + skew f b a - skew f c a ∈ alphabet) := by
    have hac := hab.trans hbc
    have hs := ht a.val b.val c.val hab hbc hc
    have hn := alphabet_neg hs
    simp only [skew, ite_eq_left hab, ite_eq_left hbc, ite_eq_left hac,
      ite_eq_right hab.not_gt, ite_eq_right hbc.not_gt, ite_eq_right hac.not_gt]
    refine ⟨hs, ?_, ?_, ?_, ?_, ?_⟩
    · convert hn using 1
      abel
    · convert hn using 1
      abel
    · convert hs using 1
      abel
    · convert hs using 1
      abel
    · convert hn using 1
      abel
  have hne₁ : a.val ≠ b.val := fun h => hab.ne (Fin.ext h)
  have hne₂ : b.val ≠ c.val := fun h => hbc.ne (Fin.ext h)
  have hne₃ : a.val ≠ c.val := fun h => hac.ne (Fin.ext h)
  by_cases h₁ : a.val < b.val
  · by_cases h₂ : b.val < c.val
    · exact (split a b c h₁ h₂ hac.2.2).1
    · by_cases h₃ : a.val < c.val
      · exact (split a c b h₃ (by omega) hab.2.2).2.1
      · exact (split c a b (by omega) h₁ hbc.2.1).2.2.2.1
  · by_cases h₃ : a.val < c.val
    · exact (split b a c (by omega) h₃ hbc.2.2).2.2.1
    · by_cases h₂ : b.val < c.val
      · exact (split b c a h₂ (by omega) hab.2.1).2.2.2.2.1
      · exact (split c b a (by omega) (by omega) hac.2.1).2.2.2.2.2

/-- A word-budget obstruction gives an actual metric gain obstruction. -/
theorem metric_obstruction_from_words {n k : ℕ} (f : ℕ → ℕ → H)
    (ht : ∀ i j l : ℕ, i < j → j < l → l ≤ i + k → f i j + f j l - f i l ∈ alphabet)
    (hobs : ¬ ∃ p : Fin n → H, ∀ i j, i.val < j.val → j.val ≤ i.val + k →
      WordBudget 1 (f i.val j.val - (p j - p i))) :
    letI := cayleyMetric
    ∃ g : Fin n → Fin n → M,
      (∀ a b, (pathPower n k).Adj a b → g b a = (g a b)⁻¹) ∧
      (∀ a b c, (pathPower n k).Adj a b → (pathPower n k).Adj b c →
        (pathPower n k).Adj a c → Dist.dist (g a b * g b c) (g a c) ≤ 1) ∧
      ∀ p : Fin n → M, ∃ a b, (pathPower n k).Adj a b ∧
        2 ≤ Dist.dist (g a b) ((p a)⁻¹ * p b) := by
  let := cayleyMetric
  refine ⟨fun i j => Multiplicative.ofAdd (skew f i j), fun a b h => skew_rev f h.ne,
    fun a b c hab hbc hac => ?_, fun p => ?_⟩
  · change Dist.dist (Multiplicative.ofAdd (skew f a b + skew f b c))
      (Multiplicative.ofAdd (skew f a c)) ≤ 1
    simpa only [Nat.cast_one] using (word_iff_distance 1 _ _).2
      ((wordBudget_one_iff _).2 (skew_triangles f ht hab hbc hac))
  · by_contra! h
    apply hobs
    refine ⟨fun i => Multiplicative.toAdd (p i), fun i j hij hspan => ?_⟩
    have hadj : (pathPower n k).Adj i j :=
      ⟨fun he => by subst j; omega, by omega, hspan⟩
    have he := h i j hadj
    simp only [skew, ite_eq_left hij] at he
    change (length letters_generate ((Multiplicative.ofAdd (f i.val j.val))⁻¹ *
      ((p i)⁻¹ * p j)) : ℝ) < 2 at he
    have hl : length letters_generate ((Multiplicative.ofAdd (f i.val j.val))⁻¹ *
        ((p i)⁻¹ * p j)) < 2 := by exact_mod_cast he
    have hd : Dist.dist (Multiplicative.ofAdd (f i.val j.val)) ((p i)⁻¹ * p j) ≤ (1 : ℝ) := by
      change (length letters_generate ((Multiplicative.ofAdd (f i.val j.val))⁻¹ *
        ((p i)⁻¹ * p j)) : ℝ) ≤ 1
      exact_mod_cast (show length letters_generate ((Multiplicative.ofAdd (f i.val j.val))⁻¹ *
        ((p i)⁻¹ * p j)) ≤ 1 by omega)
    apply (word_iff_distance 1 _ _).mp
    have hmul : Multiplicative.ofAdd ((p j).toAdd - (p i).toAdd) = (p i)⁻¹ * p j := by
      change (p j).toAdd - (p i).toAdd = -(p i).toAdd + (p j).toAdd
      abel
    simpa only [Nat.cast_one, hmul] using hd

end ChordalPath49
