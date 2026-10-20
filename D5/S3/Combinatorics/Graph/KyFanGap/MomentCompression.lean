/- GID: D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/MomentCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Caratheodory, mathlib/module/Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional, mathlib/module/Mathlib.LinearAlgebra.Dimension.Constructions, mathlib/module/Mathlib.Data.Sym.Card, mathlib/module/Mathlib.Data.Fintype.Option, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Fixed-size fourth-moment compression preserves polynomial averages and separately quartic product averages. -/

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

/-! Fourth-degree monomials are represented by four coordinates, with a dummy
coordinate of value one. Thus lower degrees use the same finite index type. -/

noncomputable section
open scoped BigOperators
open Finset

namespace D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression

/-- A degree-at-most-four monomial, padded by copies of the constant coordinate. -/
abbrev Monomial (k : ℕ) := Sym (Option (Fin k)) 4

/-- Evaluation of a padded monomial on a real coordinate vector. -/
def monomial {k : ℕ} (a : Monomial k) (x : Fin k → ℝ) : ℝ :=
  (a.val.map (fun i => i.elim 1 x)).prod

/-- The fixed number of weighted nodes used in fourth-moment compression. -/
def nodeCount (k : ℕ) : ℕ := (k + 4).choose 4 + 1

/-- A real polynomial of total degree at most four in its coefficient form. -/
def quartic {k : ℕ} (c : Monomial k → ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ a, c a * monomial a x

/-- A nonempty finite point family has a probability-weighted representation
on exactly `choose (k+4) 4 + 1` nodes from the original family, preserving every
monomial of degree at most four. Zero weights pad shorter representations. -/
theorem exists_moment_compression {k n : ℕ} (hn : 0 < n)
    (x : Fin n → Fin k → ℝ) :
    ∃ (p : Fin (nodeCount k) → ℝ) (y : Fin (nodeCount k) → Fin k → ℝ),
      (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
      (∀ a, y a ∈ Set.range x) ∧
      ∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
        ∑ b, p b * monomial a (y b) := by
  classical
  let feature : (Fin k → ℝ) → Monomial k → ℝ := fun x a => monomial a x
  let v : Fin n → Monomial k → ℝ := fun r => feature (x r)
  let mean : Monomial k → ℝ := ∑ r, (1 / (n : ℝ)) • v r
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw : (∑ _ : Fin n, (1 / (n : ℝ))) = 1 := by simp [hn0]
  have hmean : mean ∈ convexHull ℝ (Set.range v) :=
    (convex_convexHull ℝ _).sum_mem
      (fun _ _ => by positivity) hw
      (fun r _ => subset_convexHull ℝ _ (Set.mem_range_self r))
  obtain ⟨J, inst, z, w, hz, hind, hwpos, hwtotal, hwmean⟩ :=
    eq_pos_convex_span_of_mem_convexHull hmean
  letI : Fintype J := inst
  have hcard : Fintype.card J ≤ nodeCount k := by
    calc
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
        hind.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (Monomial k → ℝ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = _ := by simp [Monomial, Sym.card_sym_eq_choose, nodeCount]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card J ≤ Fintype.card (Fin (nodeCount k)) by simpa using hcard)
  choose source hsource using fun j => hz (Set.mem_range_self j)
  let p : Fin (nodeCount k) → ℝ := Function.extend e w 0
  let y : Fin (nodeCount k) → (Fin k → ℝ) :=
    Function.extend e (fun j => x (source j)) (fun _ => x ⟨0, hn⟩)
  have hp : ∀ a, 0 ≤ p a := by
    intro a
    by_cases ha : ∃ j, e j = a
    · obtain ⟨j, rfl⟩ := ha
      simpa only [p, e.injective.extend_apply] using (hwpos j).le
    · simp [p, Function.extend_apply' _ _ _ ha]
  have hsum : (∑ a, p a) = 1 := by
    rw [← hwtotal]
    exact (Fintype.sum_of_injective e e.injective w p
      (fun a ha => by
        simpa only [p, Pi.zero_apply] using
          Function.extend_apply' (f := e) w (0 : Fin (nodeCount k) → ℝ) a ha)
      (fun j => by simp only [p, e.injective.extend_apply])).symm
  refine ⟨p, y, hp, hsum, ?_, ?_⟩
  · intro a
    by_cases ha : ∃ j, e j = a
    · obtain ⟨j, rfl⟩ := ha
      simp only [y, e.injective.extend_apply]
      exact Set.mem_range_self _
    · rw [show y a = x ⟨0, hn⟩ from Function.extend_apply' _ _ _ ha]
      exact Set.mem_range_self _
  · intro i
    have heq : (∑ j, w j * z j i) = mean i := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hwmean i
    calc
      (∑ r, feature (x r) i) / n = mean i := by
        simp [mean, v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
          mul_comm, Finset.mul_sum]
      _ = ∑ j, w j * z j i := heq.symm
      _ = ∑ a, p a * feature (y a) i := by
        apply Fintype.sum_of_injective e e.injective
        · intro a ha
          simp [p, Function.extend_apply' _ _ _ ha]
        · intro j
          simp only [p, y, e.injective.extend_apply]
          rw [← hsource j]

/-- Matching the monomial moments matches every polynomial of degree at most four. -/
theorem quartic_average_eq {k n R : ℕ} (x : Fin n → Fin k → ℝ)
    (p : Fin R → ℝ) (y : Fin R → Fin k → ℝ)
    (h : ∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
      ∑ b, p b * monomial a (y b)) (c : Monomial k → ℝ) :
    (∑ r, quartic c (x r)) / n = ∑ b, p b * quartic c (y b) := by
  simp only [quartic, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  simp_rw [← Finset.mul_sum, mul_div_assoc, h]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Separately quartic products, and arbitrary finite sums of such products,
have the same double average after moment compression. The total degree in
both arguments together can be eight. -/
theorem product_average_eq {k n R : ℕ} (x : Fin n → Fin k → ℝ)
    (p : Fin R → ℝ) (y : Fin R → Fin k → ℝ)
    (h : ∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
      ∑ b, p b * monomial a (y b))
    {T : Type} [Fintype T] (f g : T → Monomial k → ℝ) :
    (∑ r, ∑ s, ∑ t, quartic (f t) (x r) * quartic (g t) (x s)) / (n : ℝ)^2 =
      ∑ a, ∑ b, p a * p b *
        ∑ t, quartic (f t) (y a) * quartic (g t) (y b) := by
  have hf := fun t => quartic_average_eq x p y h (f t)
  have hg := fun t => quartic_average_eq x p y h (g t)
  calc
    _ = ∑ t, ((∑ r, quartic (f t) (x r)) / n) *
        ((∑ s, quartic (g t) (x s)) / n) := by
      have hswap : (∑ r, ∑ s, ∑ t,
          quartic (f t) (x r) * quartic (g t) (x s)) =
          ∑ t, ∑ r, ∑ s, quartic (f t) (x r) * quartic (g t) (x s) := by
        calc
          _ = ∑ r, ∑ t, ∑ s, quartic (f t) (x r) * quartic (g t) (x s) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_comm]
          _ = _ := Finset.sum_comm
      rw [hswap, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.sum_mul_sum]
      ring
    _ = ∑ t, (∑ a, p a * quartic (f t) (y a)) *
        (∑ b, p b * quartic (g t) (y b)) := by simp_rw [hf, hg]
    _ = _ := by
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

end D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression
