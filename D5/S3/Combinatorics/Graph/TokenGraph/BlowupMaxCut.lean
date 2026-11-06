/- GID: D5/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/TokenGraph/BlowupMaxCut
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Independent uniform blow-ups multiply the ordinary maximum cut by the square of block size. -/

import D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation

open Finset
open scoped BigOperators
set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut
namespace C := CutBoundRefutation

/-- Vertices are encoded pairs, with independent fibres of size s. -/
def blowup {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℕ) : SimpleGraph (Fin (n*s)) :=
  H.comap (fun u => (finProdFinEquiv.symm u).1)

private noncomputable def score {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ)
    (x : Fin n → ℤ) : ℤ := by
  classical
  exact ∑ i, ∑ j, if H.Adj i j then x i * (s - x j) else 0

private lemma score_interpolate {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ)
    (x : Fin n → ℤ) (i : Fin n) :
    s * score H s x = (s-x i) * score H s (Function.update x i 0) +
      x i * score H s (Function.update x i s) := by
  classical
  simp only [score, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : H.Adj u v
  · have huv : u ≠ v := H.ne_of_adj h
    by_cases hu : u = i <;> by_cases hv : v = i
    · exact False.elim (huv (hu.trans hv.symm))
    all_goals simp [h, Function.update, hu, hv]; ring
  · simp [h]

private lemma score_endpoint {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ)
    (hs : 0 < s) (x : Fin n → ℤ) (i : Fin n) (hx : 0 ≤ x i ∧ x i ≤ s) :
    ∃ t : ℤ, (t = 0 ∨ t = s) ∧ score H s x ≤ score H s (Function.update x i t) := by
  have h := score_interpolate H s x i
  by_cases h0 : score H s x ≤ score H s (Function.update x i 0)
  · exact ⟨0, Or.inl rfl, h0⟩
  · refine ⟨s, Or.inr rfl, ?_⟩
    by_contra h1
    have hp := mul_pos hs (show 0 < score H s x -
      score H s (Function.update x i s) by omega)
    have hn := mul_nonneg (show 0 ≤ s-x i by omega)
      (show 0 ≤ score H s (Function.update x i s) -
        score H s (Function.update x i 0) by omega)
    nlinarith

/-- Finite coordinate rounding constructs a dominating endpoint occupancy. -/
private theorem round_score {n : ℕ} (H : SimpleGraph (Fin n)) (s : ℤ) (hs : 0 < s)
    (x : Fin n → ℤ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ s) :
    ∃ y : Fin n → ℤ, (∀ i, y i = 0 ∨ y i = s) ∧ score H s x ≤ score H s y := by
  classical
  have go : ∀ t : Finset (Fin n), ∀ x : Fin n → ℤ,
      (∀ i, 0 ≤ x i ∧ x i ≤ s) →
      ∃ y : Fin n → ℤ, (∀ i, 0 ≤ y i ∧ y i ≤ s) ∧
        score H s x ≤ score H s y ∧ (∀ i ∈ t, y i = 0 ∨ y i = s) ∧
        (∀ i ∉ t, y i = x i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx
      exact ⟨x, hx, le_rfl, by simp, by simp⟩
    | @insert a t ha ih =>
      intro x hx
      obtain ⟨v, hv, hle⟩ := score_endpoint H s hs x a (hx a)
      have hb : ∀ i, 0 ≤ Function.update x a v i ∧ Function.update x a v i ≤ s := by
        intro i
        by_cases hi : i = a
        · subst i; simp only [Function.update_same]; rcases hv with rfl | rfl <;> omega
        · simpa [Function.update_of_ne hi] using hx i
      obtain ⟨y, hy, hxy, hend, hfix⟩ := ih (Function.update x a v) hb
      refine ⟨y, hy, hle.trans hxy, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa [hfix a ha] using hv
        · exact hend i hi
      · intro i hi
        have hit : i ∉ t := fun h => hi (Finset.mem_insert_of_mem h)
        have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a t)
        rw [hfix i hit, Function.update_of_ne hia]
  obtain ⟨y, _, hle, hy, _⟩ := go Finset.univ x hx
  exact ⟨y, fun i => hy i (Finset.mem_univ i), hle⟩

end D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut
