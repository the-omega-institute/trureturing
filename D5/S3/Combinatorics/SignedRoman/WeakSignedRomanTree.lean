/- GID: D5/S3/Combinatorics/SignedRoman/WeakSignedRomanTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedRoman/WeakSignedRomanTree
   mirror-E: none(waiver:tree-weight-bound)
   anchors: [mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: A graph weight inequality proves Volkmann's weak signed Roman tree conjecture. -/

import D5.S3.Combinatorics.SignedRoman.WeakSignedRomanDefs
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SignedRoman.WeakSignedRomanTree

open WeakSignedRomanDefs

open scoped Classical in
/-- Every weak signed Roman 3-dominating function satisfies a vertex-edge weight bound. -/
theorem weight_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : V → ℤ)
    (hf : IsWeakSignedRoman G 3 f) :
    11 * (Fintype.card V : ℤ) - 7 * (G.edgeFinset.card : ℤ) ≤ 5 * ∑ v, f v := by
  classical
  let l : ℤ → ℤ := fun r => if r = -1 then 4 else if r = 1 then 3 else 1
  have hl (v : V) : 0 ≤ l (f v) := by
    rcases hf.1 v with h | h | h <;> norm_num [l, h]
  have hid (v : V) : l (f v) * (3 - f v) = 11 - 5 * f v := by
    rcases hf.1 v with h | h | h <;> norm_num [l, h]
  have hp (v u : V) : l (f v) * f u + l (f u) * f v ≤ 7 := by
    rcases hf.1 v with hv | hv | hv <;>
      rcases hf.1 u with hu | hu | hu <;> norm_num [l, hv, hu]
  have hlocal (v : V) :
      l (f v) * (3 - f v) ≤ ∑ u ∈ G.neighborFinset v, l (f v) * f u := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (by linarith [hf.2 v]) (hl v)
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hlocal v)
  have hleft : (∑ v, l (f v) * (3 - f v)) =
      11 * (Fintype.card V : ℤ) - 5 * ∑ v, f v := by
    simp_rw [hid]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, ← Finset.mul_sum]
    omega
  have hswap : (∑ v, ∑ u ∈ G.neighborFinset v, l (f u) * f v) =
      ∑ v, ∑ u ∈ G.neighborFinset v, l (f v) * f u := by
    simp_rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have hpair := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) =>
    Finset.sum_le_sum (fun u (_ : u ∈ G.neighborFinset v) => hp v u))
  have hdegree : (∑ v, ∑ _u ∈ G.neighborFinset v, (7 : ℤ)) =
      14 * (G.edgeFinset.card : ℤ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
    rw [← Finset.sum_mul]
    have hd : (∑ v, (G.degree v : ℤ)) = 2 * (G.edgeFinset.card : ℤ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [hd]
    omega
  simp only [Finset.sum_add_distrib] at hpair
  rw [hswap, hdegree] at hpair
  rw [hleft] at hsum
  linarith

/-- Volkmann's conjecture for every tree of order at least two. -/
theorem result : WeakSignedRomanDefs.claim := by
  intro n T _ hn hT
  classical
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let W : Set ℤ := {w | ∃ f : Fin n → ℤ, IsWeakSignedRoman T 3 f ∧ w = ∑ v, f v}
  have htwo : IsWeakSignedRoman T 3 (fun _ => 2) := by
    refine ⟨fun _ => Or.inr (Or.inr rfl), fun v => ?_⟩
    have hd := hT.connected.preconnected.degree_pos_of_nontrivial v
    simp only [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hne : W.Nonempty := ⟨∑ _v : Fin n, (2 : ℤ), fun _ => 2, htwo, rfl⟩
  have hb : BddBelow W := by
    refine ⟨-(n : ℤ), ?_⟩
    rintro w ⟨f, hf, rfl⟩
    have hs : (∑ _v : Fin n, (-1 : ℤ)) ≤ ∑ v, f v := by
      refine Finset.sum_le_sum fun v _ => ?_
      rcases hf.1 v with h | h | h <;> omega
    simpa using hs
  obtain ⟨f, hf, hmin⟩ := Int.csInf_mem hne hb
  have hw := weight_bound T f hf
  have he := hT.card_edgeFinset
  simp only [Fintype.card_fin] at he
  have heZ : (T.edgeFinset.card : ℤ) + 1 = n := by exact_mod_cast he
  change weakSignedRomanNumber T 3 = ∑ v, f v at hmin
  rw [hmin]
  simp only [Fintype.card_fin] at hw
  omega

#print axioms result

end D5.S3.Combinatorics.SignedRoman.WeakSignedRomanTree
