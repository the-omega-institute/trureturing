/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalEightVertexMetric
   generality: I
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.not_subtwo_finite_group; premises=D5/S3/Combinatorics/Graph/Chordal/ChordalEightVertex.exists_nonunit_residual
   digest: The eight-vertex split-graph certificate gives a residual of at least two in its bi-invariant Cayley metric. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.ChordalEightVertex
import D5.S3.Combinatorics.Graph.CayleyGraphs.GroupWordMetric

compile_only_with_mathlib

/-! Omega original.

The bi-invariant word metric for the eight-vertex split-graph obstruction.
-/

namespace ChordalEightVertex

open GroupWordMetric

abbrev M := Multiplicative H

private def letters : Set M := {x | Unit x.toAdd}

private theorem letters_inv : ∀ x ∈ letters, x⁻¹ ∈ letters := by
  rintro x ⟨a, ha⟩
  change Unit (-x.toAdd)
  rw [← ha]
  exact ball_neg a

private theorem letters_generate : Generates letters := by
  let S : AddSubgroup H :=
    { carrier := {x | ∃ n, Fits letters n (Multiplicative.ofAdd x)}
      zero_mem' := ⟨0, Fits.one⟩
      add_mem' := fun ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, hm.mul hn⟩
      neg_mem' := fun ⟨n, hn⟩ => ⟨n, hn.inv letters_inv⟩ }
  have hload : Set.range generator ⊆ S := by
    rintro x ⟨i, rfl⟩
    refine ⟨1, Fits.of_mem ?_⟩
    refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
    fin_cases i <;> decide
  have hS : ⊤ ≤ S := generators_generate ▸ (AddSubgroup.closure_le (K := S)).2 hload
  intro x
  exact hS (show x.toAdd ∈ (⊤ : AddSubgroup H) by simp)

private theorem letters_conj (a : M) : ∀ x ∈ letters, a * x * a⁻¹ ∈ letters := by
  intro x hx
  rwa [mul_comm a x, mul_assoc, mul_inv_cancel, mul_one]

@[instance_reducible]
noncomputable def cayleyMetric : MetricSpace M := metric letters_generate letters_inv

theorem cayley_left : letI := cayleyMetric; IsIsometricSMul M M :=
  left_isometric letters_generate letters_inv

theorem cayley_right : letI := cayleyMetric; IsIsometricSMul Mᵐᵒᵖ M :=
  right_isometric letters_generate letters_inv letters_conj

private theorem unit_of_subtwo (x y : H)
    (h : letI := cayleyMetric; Dist.dist (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) < 2) :
    Unit (x - y) := by
  have h₀ : (length letters_generate (Multiplicative.ofAdd (-x + y)) : ℝ) < 2 := h
  have h₁ : length letters_generate (Multiplicative.ofAdd (-x + y)) < 2 := by
    exact_mod_cast h₀
  have h₂ := (length_le_iff letters_generate 1 (Multiplicative.ofAdd (-x + y))).mp
    (show length letters_generate (Multiplicative.ofAdd (-x + y)) ≤ 1 by omega)
  obtain ⟨l, hmem, hlen, hprod⟩ := h₂
  have hsmall : Unit (-x + y) := by
    cases l with
    | nil =>
      have he := congrArg Multiplicative.toAdd hprod
      change (0 : H) = -x + y at he
      exact ⟨0, he⟩
    | cons a tail =>
      change tail.length + 1 ≤ 1 at hlen
      have he : tail = [] := List.length_eq_zero_iff.mp (by omega)
      subst tail
      have ha : a = Multiplicative.ofAdd (-x + y) := by simpa using hprod
      subst a
      exact hmem (Multiplicative.ofAdd (-x + y)) (List.mem_cons_self ..)
  have hinv := letters_inv (Multiplicative.ofAdd (-x + y)) hsmall
  change Unit (-(-x + y)) at hinv
  convert hinv using 1
  abel

theorem triangle_metric (u v w : V) (huv : graph.Adj u v) (hvw : graph.Adj v w)
    (huw : graph.Adj u w) :
    letI := cayleyMetric
    Dist.dist (Multiplicative.ofAdd (gain u v + gain v w))
      (Multiplicative.ofAdd (gain u w)) ≤ 1 := by
  letI := cayleyMetric
  have h := all_triangle_defects_unit u v w huv hvw huw
  have h' := letters_inv (Multiplicative.ofAdd (gain u v + gain v w - gain u w)) h
  change (length letters_generate
    (Multiplicative.ofAdd (-(gain u v + gain v w) + gain u w)) : ℝ) ≤ 1
  have he : -(gain u v + gain v w) + gain u w = -(gain u v + gain v w - gain u w) := by abel
  rw [he]
  exact_mod_cast (length_le_iff letters_generate 1 _).2 (Fits.of_mem h')

theorem exists_metric_residual_ge_two (p : V → M) :
    letI := cayleyMetric
    ∃ u v, graph.Adj u v ∧
      2 ≤ Dist.dist (Multiplicative.ofAdd (gain u v)) ((p u)⁻¹ * p v) := by
  letI := cayleyMetric
  obtain ⟨u, v, huv, hbad⟩ := exists_nonunit_residual (fun a => (p a).toAdd)
  refine ⟨u, v, huv, le_of_not_gt fun hlt => hbad ?_⟩
  have hlt' : Dist.dist (Multiplicative.ofAdd (gain u v))
      (Multiplicative.ofAdd (-(p u).toAdd + (p v).toAdd)) < 2 := hlt
  simpa [sub_eq_add_neg, add_comm] using unit_of_subtwo _ _ hlt'

end ChordalEightVertex
