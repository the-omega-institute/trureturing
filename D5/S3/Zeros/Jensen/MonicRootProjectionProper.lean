/- GID: D5/S3/Zeros/Jensen/MonicRootProjectionProper
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/MonicRootProjectionProper
   mirror-E: none(waiver:qualitative-polynomial-properness)
   anchors: [mathlib/module/Mathlib.Topology.Maps.Proper.CompactlyGenerated]
   utility: none
   digest: The zero graph of a continuous fixed-degree monic family projects properly. -/

import D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.MonicRootProjectionProper

open Polynomial Filter Topology Set Metric
open D5.S3.Zeros.Jensen.CompactSeparatedRealContinuation (monic_root_bound_by_coefficient_sum)

/-- No root labeling, simple-root premise, global root bound, or compact parameter space is
required. Degree zero is included. Coefficient continuity only through the fixed degree is used. -/
theorem monic_fixed_degree_root_projection_isProper
    {A : Type*} [TopologicalSpace A] [T2Space A] [CompactlyCoherentSpace A]
    (P : A → Polynomial ℂ) (q : ℕ)
    (hmonic : ∀ t, (P t).Monic)
    (hdegree : ∀ t, (P t).natDegree = q)
    (hc : ∀ i ≤ q, Continuous (fun t => (P t).coeff i)) :
    IsProperMap (fun e : {p : A × ℂ // (P p.1).eval p.2 = 0} => e.1.1) := by
  let F : A × ℂ → ℂ := fun p => (P p.1).eval p.2
  have hFformula (p : A × ℂ) :
      F p = ∑ i ∈ Finset.range (q+1), (P p.1).coeff i * p.2^i := by
    dsimp [F]
    rw [Polynomial.eval_eq_sum_range, hdegree p.1]
  have hF : Continuous F := by
    have hsum : Continuous (fun p : A × ℂ =>
        ∑ i ∈ Finset.range (q+1), (P p.1).coeff i*p.2^i) := by
      apply continuous_finsetSum
      intro i hi
      have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact ((hc i hiq).comp continuous_fst).mul (continuous_snd.pow i)
    exact hsum.congr (fun p => (hFformula p).symm)
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨by fun_prop, ?_⟩
  intro K hK
  let S : A → ℝ := fun t => ∑ i ∈ Finset.range q, ‖(P t).coeff i‖
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro i hi
    exact (hc i (Nat.le_of_lt (Finset.mem_range.mp hi))).norm
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hS.continuousOn
  let R : ℝ := max C 0 + 1
  have hrootbound (t : A) (ht : t ∈ K) (z : ℂ)
      (hz : (P t).eval z = 0) : ‖z‖ ≤ R := by
    have hr := monic_root_bound_by_coefficient_sum (P t) (hmonic t) z hz
    rw [hdegree t] at hr
    change ‖z‖ ≤ S t+1 at hr
    have hb : S t ≤ C := (le_abs_self (S t)).trans (by simpa using hC t ht)
    apply hr.trans
    dsimp [R]
    linarith [le_max_left C 0]
  let ZK : Set (A × ℂ) := {p | p.1 ∈ K ∧ F p = 0}
  have hclosed : IsClosed ZK :=
    (hK.isClosed.preimage continuous_fst).inter
      (isClosed_singleton.preimage hF)
  have hsubset : ZK ⊆ K ×ˢ closedBall (0 : ℂ) R := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    rw [mem_closedBall_zero_iff]
    exact hrootbound p.1 hp.1 p.2 hp.2
  have hcompact : IsCompact ZK :=
    (hK.prod (isCompact_closedBall (0 : ℂ) R)).of_isClosed_subset hclosed hsubset
  apply Subtype.isCompact_iff.mpr
  have himage : (Subtype.val ''
      ((fun e : {p : A × ℂ // (P p.1).eval p.2 = 0} => e.1.1) ⁻¹' K)) = ZK := by
    ext p
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨he,e.2⟩
    · intro hp
      exact ⟨⟨p,hp.2⟩,hp.1,rfl⟩
  rwa [himage]

#print axioms monic_fixed_degree_root_projection_isProper

end D5.S3.Zeros.Jensen.MonicRootProjectionProper
