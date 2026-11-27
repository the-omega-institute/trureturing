/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/HuangTranslationObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/Translation/HuangTranslationObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity, mathlib/module/Mathlib.Data.Finset.Prod]
   utility: none
   digest: The square of the signed translation lift obstructs Huang-balanced cube periods. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent
import Mathlib.Data.Finset.Prod

/-! The FALSE-prefix coefficients of Huang's actual matrix determine the sign
of translating twice along a period of a balanced support. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced switching_sq)
open BalancedCubeGirth (adjacent_exists_flip)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_flip_prefix from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent

private abbrev translate {n : ℕ} (a x : Q n) : Q n := fun i => Bool.xor (a i) (x i)

private theorem translate_translate {n : ℕ} (a x : Q n) :
    translate a (translate a x) = x := by
  funext i
  cases ha : a i <;> cases hx : x i <;> simp [translate, ha, hx]

private theorem translate_flip {n : ℕ} (a x : Q n) (i : Fin n) :
    translate a (flip x i) = flip (translate a x) i := by
  funext j
  by_cases hj : j = i
  · subst j
    cases a i <;> cases x i <;> simp [translate, *]
  · simp [translate, BalancedCriticalSpectrum.flip, hj]

private def diagonalSign {n : ℕ} (a x : Q n) : ℝ :=
  ∏ p : Fin n × Fin n, if p.1 < p.2 ∧ a p.1 = true ∧ x p.2 = true then -1 else 1

private theorem diagonalSign_sq {n : ℕ} (a x : Q n) : diagonalSign a x ^ 2 = 1 := by
  rw [diagonalSign, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro p _
  split <;> norm_num

private theorem diagonalSign_translate {n : ℕ} (a x : Q n) :
    diagonalSign a x * diagonalSign a (translate a x) =
      (-1 : ℝ) ^ ((Finset.univ.filter fun i => a i = true).card.choose 2) := by
  let S : Finset (Fin n) := Finset.univ.filter fun i => a i = true
  change _ = (-1 : ℝ) ^ S.card.choose 2
  have hpairs : Finset.univ.filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ a p.1 = true ∧ a p.2 = true) =
      (S ×ˢ S).filter (fun p => p.1 < p.2) := by
    ext p
    simp [S, and_comm]
  rw [diagonalSign, diagonalSign, ← Finset.prod_mul_distrib,
    ← Finset.card_product_filter_lt (s := S), ← Finset.prod_const, ← hpairs, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p _
  by_cases h : p.1 < p.2 <;>
    cases h₁ : a p.1 <;> cases h₂ : a p.2 <;> cases hx : x p.2 <;>
    norm_num [translate, h, h₁, h₂, hx]

private theorem diagonalSign_flip {n : ℕ} (a x : Q n) (i : Fin n) :
    diagonalSign a x * diagonalSign a (flip x i) =
      ∏ j : Fin n, if j < i ∧ a j = true then (-1 : ℝ) else 1 := by
  rw [diagonalSign, diagonalSign, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_prod_type_right]
  rw [Finset.prod_eq_single i]
  · apply Finset.prod_congr rfl
    intro j _
    by_cases h : j < i ∧ a j = true <;> cases hx : x i <;> norm_num [h, hx]
  · intro k _ hk
    apply Finset.prod_eq_one
    intro j _
    rw [show flip x i k = x k from Function.update_of_ne hk _ _]
    split <;> norm_num
  · simp

private theorem edge_covariance {n : ℕ} (a x : Q n) (i : Fin n) :
    huangMatrix n x (flip x i) * huangMatrix n (translate a x) (translate a (flip x i)) =
      diagonalSign a x * diagonalSign a (flip x i) := by
  rw [translate_flip, matrix_flip_prefix, matrix_flip_prefix, diagonalSign_flip,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j < i <;> cases ha : a j <;> cases hx : x j <;>
    norm_num [translate, h, ha, hx]

/-- A translation preserving a balanced support has even quadratic weight
if it takes a vertex into its own induced connected component. -/
theorem even_choose_two_of_reachable_translation {n : ℕ} {C : Finset (Q n)} {a x : Q n}
    (hC : IsBalanced C)
    (hT : ∀ y ∈ C, (fun i => Bool.xor (a i) (y i)) ∈ C)
    (hx : x ∈ C)
    (hreach : ((hypercube n).induce (C : Set (Q n))).Reachable
      ⟨x, hx⟩ ⟨(fun i => Bool.xor (a i) (x i)), hT x hx⟩) :
    Even ((Finset.univ.filter fun i => a i = true).card.choose 2) := by
  obtain ⟨sigma, hs⟩ := hC
  let ratio (y : Q n) := diagonalSign a y * sigma y * sigma (translate a y)
  have ratio_sq {y : Q n} (hy : y ∈ C) : ratio y ^ 2 = 1 := by
    simp only [ratio, mul_pow, diagonalSign_sq, switching_sq hs hy,
      switching_sq hs (hT y hy), mul_one]
  have edge_ratio {y z : Q n} (hy : y ∈ C) (hz : z ∈ C) (h : (hypercube n).Adj y z) :
      ratio y = ratio z := by
    obtain ⟨i, rfl⟩ := adjacent_exists_flip h
    have ht : (hypercube n).Adj (translate a y) (translate a (flip y i)) := by
      rw [translate_flip]
      exact flip_adj _ _
    have he := edge_covariance a y i
    rw [hs.2 y hy (flip y i) hz h,
      hs.2 (translate a y) (hT y hy) (translate a (flip y i)) (hT _ hz) ht] at he
    have hp : ratio y * ratio (flip y i) = 1 := by
      dsimp [ratio]
      calc
        _ = (diagonalSign a y * diagonalSign a (flip y i)) *
            (sigma y * sigma (flip y i) *
              (sigma (translate a y) * sigma (translate a (flip y i)))) := by ring
        _ = (diagonalSign a y * diagonalSign a (flip y i)) ^ 2 := by rw [he, pow_two]
        _ = 1 := by rw [mul_pow, diagonalSign_sq, diagonalSign_sq, mul_one]
    calc
      ratio y = ratio y * ratio (flip y i) ^ 2 := by rw [ratio_sq hz, mul_one]
      _ = ratio (flip y i) := by rw [pow_two, ← mul_assoc, hp, one_mul]
  let G := (hypercube n).induce (C : Set (Q n))
  have walk_ratio {u v : C} (p : G.Walk u v) : ratio u.val = ratio v.val := by
    induction p with
    | nil => rfl
    | @cons u v _ h _ ih => exact (edge_ratio u.property v.property h).trans ih
  obtain ⟨p⟩ := hreach
  have hr : ratio x = ratio (translate a x) := walk_ratio p
  have hp : diagonalSign a x * diagonalSign a (translate a x) = 1 := by
    calc
      _ = ratio x * ratio (translate a x) := by
        dsimp only [ratio]
        rw [translate_translate]
        calc
          _ = (diagonalSign a x * diagonalSign a (translate a x)) *
              (sigma x ^ 2 * sigma (translate a x) ^ 2) := by
            rw [switching_sq hs hx, switching_sq hs (hT x hx), mul_one, mul_one]
          _ = _ := by ring
      _ = 1 := by rw [← hr, ← pow_two, ratio_sq hx]
  rw [diagonalSign_translate] at hp
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hp

end D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
