/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/BornFiveMode
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/BornFiveMode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Born marginal at a degree-two blocked center is a five-mode law recovered from occupations and the empty-neighborhood probability. -/

import D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical ComplexOrder

namespace D5.S3.Quantum.Fibers.BipartiteBlockade

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The order is vacuum, left, center, right, both ends. -/
def localMode (G : SimpleGraph V) (u v w : V) (S : Configuration G) : Fin 5 :=
  if v ∈ S.val then 2 else if u ∈ S.val then
    if w ∈ S.val then 4 else 1
  else if w ∈ S.val then 3 else 0

/-- The diagonal Born marginal, without an independence assumption on the state. -/
def bornModeLaw (G : SimpleGraph V) (u v w : V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (k : Fin 5) : ℝ :=
  ∑ S, if localMode G u v w S = k then (ρ S S).re else 0

/-- Occupation expectation of the actual graph projector. -/
def occupationMean (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (x : V) : ℝ :=
  (Matrix.trace (ρ * number G x)).re

/-- Empty-neighborhood expectation of the actual graph projector. -/
def blockadeMean (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (x : V) : ℝ :=
  (Matrix.trace (ρ * blockade G x)).re

private theorem occupationMean_sum (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (x : V) :
    occupationMean G ρ x = ∑ S, if x ∈ S.val then (ρ S S).re else 0 := by
  simp [occupationMean, number, Matrix.trace, Matrix.mul_diagonal]

private theorem blockadeMean_sum (G : SimpleGraph V)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ) (x : V) :
    blockadeMean G ρ x = ∑ S, if clear G x S then (ρ S S).re else 0 := by
  simp [blockadeMean, blockade, Matrix.trace, Matrix.mul_diagonal]

private theorem local_blocking (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w) (S : Configuration G) :
    clear G v S ↔ u ∉ S.val ∧ w ∉ S.val := by
  constructor
  · intro h
    exact ⟨fun hu => h u hu ((hN u).2 (Or.inl rfl)),
      fun hw => h w hw ((hN w).2 (Or.inr rfl))⟩
  · rintro ⟨hu, hw⟩ x hx hadj
    rcases (hN x).1 hadj with rfl | rfl
    · exact hu hx
    · exact hw hx

private theorem local_legality (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w) (S : Configuration G)
    (hv : v ∈ S.val) : u ∉ S.val ∧ w ∉ S.val := by
  exact ⟨fun hu => S.property v hv u hu ((hN u).2 (Or.inl rfl)),
    fun hw => S.property v hv w hw ((hN w).2 (Or.inr rfl))⟩

/-- A degree-two center's Born marginal is an actual probability law. Its five
masses, including the joint endpoint mass, follow from the three occupations
and the empty-neighborhood expectation, for arbitrary initial coherence. -/
theorem born_five_mode_reconstruction (G : SimpleGraph V) (u v w : V)
    (hN : ∀ x, G.Adj v x ↔ x = u ∨ x = w)
    (ρ : Matrix (Configuration G) (Configuration G) ℂ)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ = 1) :
    (∀ k, 0 ≤ bornModeLaw G u v w ρ k) ∧
    (∑ k, bornModeLaw G u v w ρ k) = 1 ∧
    bornModeLaw G u v w ρ =
      ![blockadeMean G ρ v - occupationMean G ρ v,
        1 - blockadeMean G ρ v - occupationMean G ρ w,
        occupationMean G ρ v,
        1 - blockadeMean G ρ v - occupationMean G ρ u,
        blockadeMean G ρ v - 1 + occupationMean G ρ u + occupationMean G ρ w] := by
  have hs : (∑ S : Configuration G, (ρ S S).re) = 1 := by
    simpa [Matrix.trace] using congrArg Complex.re ht
  have hp (k : Fin 5) : 0 ≤ bornModeLaw G u v w ρ k := by
    apply Finset.sum_nonneg
    intro S _
    split_ifs
    · exact (Complex.nonneg_iff.mp hρ.diag_nonneg).1
    · rfl
  have partition (S : Configuration G) :
      (∑ k : Fin 5, if localMode G u v w S = k then (ρ S S).re else 0) =
        (ρ S S).re := by simp
  have htotal : (∑ k, bornModeLaw G u v w ρ k) = 1 := by
    rw [bornModeLaw, Finset.sum_comm]
    simpa only [partition] using hs
  have hlocal (S : Configuration G) :
      (if v ∈ S.val then (ρ S S).re else 0) =
        (if localMode G u v w S = 2 then (ρ S S).re else 0) ∧
      (if u ∈ S.val then (ρ S S).re else 0) =
        (if localMode G u v w S = 1 then (ρ S S).re else 0) +
        (if localMode G u v w S = 4 then (ρ S S).re else 0) ∧
      (if w ∈ S.val then (ρ S S).re else 0) =
        (if localMode G u v w S = 3 then (ρ S S).re else 0) +
        (if localMode G u v w S = 4 then (ρ S S).re else 0) ∧
      (if clear G v S then (ρ S S).re else 0) =
        (if localMode G u v w S = 0 then (ρ S S).re else 0) +
        (if localMode G u v w S = 2 then (ρ S S).re else 0) := by
    rw [local_blocking G u v w hN]
    by_cases hv : v ∈ S.val
    · obtain ⟨hu, hw⟩ := local_legality G u v w hN S hv
      simp [localMode, hv, hu, hw]
    · by_cases hu : u ∈ S.val <;> by_cases hw : w ∈ S.val <;>
        simp [localMode, hv, hu, hw]
  have hm : occupationMean G ρ v = bornModeLaw G u v w ρ 2 := by
    rw [occupationMean_sum]
    exact Finset.sum_congr rfl (fun S _ => (hlocal S).1)
  have hu : occupationMean G ρ u =
      bornModeLaw G u v w ρ 1 + bornModeLaw G u v w ρ 4 := by
    rw [occupationMean_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => (hlocal S).2.1)
  have hw : occupationMean G ρ w =
      bornModeLaw G u v w ρ 3 + bornModeLaw G u v w ρ 4 := by
    rw [occupationMean_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => (hlocal S).2.2.1)
  have hb : blockadeMean G ρ v =
      bornModeLaw G u v w ρ 0 + bornModeLaw G u v w ρ 2 := by
    rw [blockadeMean_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => (hlocal S).2.2.2)
  refine ⟨hp, htotal, ?_⟩
  rw [Fin.sum_univ_five] at htotal
  funext k
  fin_cases k <;> simp <;> linarith

#print axioms born_five_mode_reconstruction

end D5.S3.Quantum.Fibers.BipartiteBlockade
