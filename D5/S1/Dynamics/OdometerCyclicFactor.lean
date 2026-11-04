/- GID: D5/S1/Dynamics/OdometerCyclicFactor
   generality: G
   mirror-B: D5/B/S1/Dynamics/OdometerCyclicFactor
   mirror-E: none(waiver:canonical-profinite-symbolic-factor)
   anchors: []
   utility: none
   digest: Continuous symbolic factors of the p-adic odometer use one canonical finite cyclic quotient. -/

import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-!
This is a formal coverage bridge, not a mathematical novelty claim. Compact
p-adic topology makes one discrete observation depend on a canonical residue
quotient; equivariance transports that same quotient to every integer time.
The complete two-sided formula, rather than a generic local-constancy claim,
is the public result.
-/

noncomputable section

open Set Metric

namespace D5.S1.Dynamics.OdometerCyclicFactor

variable (p : ℕ) [Fact p.Prime]

private theorem exists_residue_factor {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : ℤ_[p] → A) (hc : Continuous c) :
    ∃ (N : ℕ) (w : ZMod (p ^ N) → A),
      ∀ x : ℤ_[p], c x = w (PadicInt.toZModPow N x) := by
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hc
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (s := (Set.univ : Set ℤ_[p])) (c := fun a : A => {x | c x = a})
    isCompact_univ (fun a => hlc.isOpen_fiber a) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨c x, rfl⟩)
  obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hδ
  have hfiber {x y : ℤ_[p]}
      (hxy : PadicInt.toZModPow N x = PadicInt.toZModPow N y) : c x = c y := by
    obtain ⟨a, ha⟩ := hball x (Set.mem_univ x)
    have hdist : dist y x < δ := by
      apply lt_of_le_of_lt _ hN
      rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
        ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hxy, sub_self]
    exact (ha (Metric.mem_ball_self hδ)).trans (ha hdist).symm
  letI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
  refine ⟨N, fun a => c (a.val : ℤ_[p]), ?_⟩
  intro x
  apply hfiber
  simp only [map_natCast, ZMod.natCast_zmod_val]

private theorem equivariant_coordinate {A : Type*} (Φ : ℤ_[p] → ℤ → A)
    (hshift : ∀ (x : ℤ_[p]) (n : ℤ), Φ (x + 1) n = Φ x (n + 1))
    (n : ℤ) : ∀ x : ℤ_[p], Φ x n = Φ (x + (n : ℤ_[p])) 0 := by
  refine Int.induction_on n ?_ ?_ ?_
  · intro x
    simp
  · intro k ih x
    change Φ x ((k : ℤ) + 1) = Φ (x + (((k : ℤ) + 1 : ℤ) : ℤ_[p])) 0
    rw [← hshift, ih]
    congr 1
    push_cast
    ring
  · intro k ih x
    change Φ x (-(k : ℤ) - 1) = Φ (x + ((-(k : ℤ) - 1 : ℤ) : ℤ_[p])) 0
    have h := hshift (x - 1) (-(k : ℤ) - 1)
    have hx : x - 1 + 1 = x := by ring
    have hk : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
    rw [hx, hk, ih] at h
    calc
      Φ x (-(k : ℤ) - 1) = Φ (x - 1 + ((-(k : ℤ) : ℤ) : ℤ_[p])) 0 := h
      _ = Φ (x + ((-(k : ℤ) - 1 : ℤ) : ℤ_[p])) 0 := by
        congr 1
        push_cast
        ring

/-- One canonical residue quotient reconstructs every coordinate of every
continuous two-sided symbolic factor of the p-adic adding machine. The target
alphabet only needs to be discrete, and need not be finite. -/
theorem exists_cyclic_factor_of_shift_equivariant
    {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (Φ : ℤ_[p] → ℤ → A) (hΦ : Continuous Φ)
    (hshift : ∀ (x : ℤ_[p]) (n : ℤ), Φ (x + 1) n = Φ x (n + 1)) :
    ∃ (N : ℕ) (w : ZMod (p ^ N) → A),
      ∀ (x : ℤ_[p]) (n : ℤ),
        Φ x n = w (PadicInt.toZModPow N x + (n : ZMod (p ^ N))) := by
  obtain ⟨N, w, hw⟩ := exists_residue_factor p (fun x => Φ x 0)
    ((continuous_apply 0).comp hΦ)
  refine ⟨N, w, ?_⟩
  intro x n
  rw [equivariant_coordinate p Φ hshift n x, hw, map_add, map_intCast]

end D5.S1.Dynamics.OdometerCyclicFactor
