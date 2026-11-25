module

import D5.S3.Topology.SeparatedLimsupMeagre
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.NormNum

/-! Exact transient applications of separated dense limsup classes. -/

open Set Filter
open scoped Topology

universe u

local instance : TopologicalSpace (Fin 2) := ⊥
local instance : DiscreteTopology (Fin 2) := ⟨rfl⟩

example {X : Type u} [TopologicalSpace X] [BaireSpace X]
    (U : ℕ → X → ℝ) (hU : ∀ n, Continuous (U n))
    (A B : Set X) (hA : Dense A) (hB : Dense B) (a b : ℝ) (hab : a ≠ b)
    (ha : ∀ x ∈ A, Filter.limsup (fun n => U n x) atTop = a)
    (hb : ∀ x ∈ B, Filter.limsup (fun n => U n x) atTop = b) :
    IsMeagre {x | ∃ L : ℝ, Tendsto (fun n => U n x) atTop (𝓝 L)} ∧
      Dense {x | ¬ ∃ L : ℝ, Tendsto (fun n => U n x) atTop (𝓝 L)} := by
  have h := separated_limsup_isMeagre U hU A B hA hB a b hab ha hb
  exact ⟨h, dense_of_mem_residual h⟩

-- All hypotheses of the binary-product instance are established here.
example :
    IsMeagre {x : ℕ → Fin 2 | ∃ L : ℝ,
      Tendsto (fun n : ℕ => ((x n).val : ℝ)) atTop (𝓝 L)} := by
  let S (c : Fin 2) : Set (ℕ → Fin 2) := {x | ∀ᶠ n in atTop, x n = c}
  have hd (c : Fin 2) : Dense (S c) := by
    intro x
    rw [mem_closure_iff]
    intro O hO hx
    obtain ⟨I, hI⟩ := exists_finset_piecewise_mem_of_mem_nhds (hO.mem_nhds hx)
      (fun _ : ℕ => c)
    refine ⟨I.piecewise x (fun _ => c), hI, ?_⟩
    change ∀ᶠ n in atTop, I.piecewise x (fun _ => c) n = c
    filter_upwards [eventually_gt_atTop (I.sup id)] with n hn
    have hnI : n ∉ I := by
      intro h
      exact (not_le_of_gt hn) (Finset.le_sup (f := id) h)
    simp [Finset.piecewise, hnI]
  have hl (c : Fin 2) (x : ℕ → Fin 2) (hx : x ∈ S c) :
      Filter.limsup (fun n => ((x n).val : ℝ)) atTop = (c.val : ℝ) := by
    apply Filter.Tendsto.limsup_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with n hn
    simp [hn]
  exact separated_limsup_isMeagre (X := ℕ → Fin 2)
    (fun (n : ℕ) (x : ℕ → Fin 2) => ((x n).val : ℝ))
    (fun n => (continuous_of_discreteTopology : Continuous (fun k : Fin 2 => (k.val : ℝ))).comp
      (continuous_apply n))
    (S 0) (S 1) (hd 0) (hd 1) 0 1 (by norm_num)
    (by simpa using hl 0) (by simpa using hl 1)

-- Exact Theorem A averages, with the empty-sum convention at n=0.
example {X : Type u} [MetricSpace X] [CompactSpace X]
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : Continuous φ)
    (A B : Set X) (hA : Dense A) (hB : Dense B) (a b : ℝ) (hab : a ≠ b)
    (ha : ∀ x ∈ A, Filter.limsup
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (T^[k] x)) atTop = a)
    (hb : ∀ x ∈ B, Filter.limsup
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (T^[k] x)) atTop = b) :
    {x | ¬ ∃ L : ℝ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (T^[k] x)) atTop (𝓝 L)} ∈ residual X ∧
    Dense {x | ¬ ∃ L : ℝ, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (T^[k] x)) atTop (𝓝 L)} := by
  let U : ℕ → X → ℝ := fun n x => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (T^[k] x)
  have hzero : U 0 = fun _ => 0 := by funext x; simp [U]
  have hU (n : ℕ) : Continuous (U n) := by
    apply continuous_const.mul
    exact continuous_finsetSum _ fun k _ => hφ.comp (hT.iterate k)
  have h := separated_limsup_isMeagre U hU A B hA hB a b hab ha hb
  exact ⟨h, dense_of_mem_residual h⟩

#print separated_limsup_isMeagre
#print axioms separated_limsup_isMeagre
