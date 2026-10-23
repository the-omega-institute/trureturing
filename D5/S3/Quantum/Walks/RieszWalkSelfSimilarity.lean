/- GID: D5/S3/Quantum/Walks/RieszWalkSelfSimilarity
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/RieszWalkSelfSimilarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Riesz moment and CMV identities for scale-four self-similarity. -/

/- admission_basis: open-problem-resolution (#15758; Proved)
   Module witness: none
   Direct frozen dependencies:
   D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail
     declaration statement_id: sha256:866d2544f66c1d06437a72737a30260611f3d3ad3546581a69fd50db1c634bb4
   D5.S3.Weil.Szego.CanonicalTransfer.szegoRho
     declaration statement_id: sha256:8155eeaa9dd1f2640bb6365ddd75a4cc9fdb1ac7d21883d8cba593787c925834
   D5.S3.Weil.Szego.CanonicalTransfer.szego_rho_pos
     declaration statement_id: sha256:b440986d62bb484d69935806c23cf6449a0f9f409fcb9c6371e31974b2b92c99
   result: proof_shape: content; escape_witness: none
     Direct frozen dependencies: tail, szegoRho, szego_rho_pos; consumers: terminal settling result.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15854
-/

import D5.S3.Quantum.Walks.CMV.Representation
import D5.S3.Quantum.Walks.Riesz.Decimation

open LaurentPolynomial
noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.RieszWalkSelfSimilarity
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.Riesz.Decimation.Parity D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk
def prob (t : ℕ) (S : Set ℚ) : ℝ :=
  by
    classical
    exact ∑' y : ℕ, if ((y : ℚ) / t) ∈ S then mu t y else 0

def Tset (n k : ℕ) : Set ℚ :=
  if k = 0 then {0} else Set.Ioc (((k : ℚ)-1)/n) ((k : ℚ)/n)

def claim : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ k : ℕ, k ≤ t →
    prob (2*t) (Tset t k) = prob (8*t) (Tset t k)


end D5.S3.Quantum.Walks.RieszWalkSelfSimilarity
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.ProbabilityBlocks
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.Riesz.Decimation.Parity D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.RieszWalkSelfSimilarity
open Classical
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.RieszWalkSelfSimilarity D5.S3.Quantum.Walks.CMV.Representation.WalkCore

/-- Finite propagation justifies every infinite probability sum without a
convergence assumption. -/
private theorem prob_finite (t : ℕ) (S : Set ℚ) :
    prob t S = ∑ y ∈ Finset.range (t+1), if ((y:ℚ)/t)∈S then mu t y else 0 := by
  classical
  apply tsum_eq_sum
  intro y hy
  have hty : t<y := by
    have h : ¬y<t+1 := by simpa only [Finset.mem_range] using hy
    omega
  simp [mu_outside t y hty]

/-- The origin block is exactly the origin site for positive time. -/
private theorem prob_origin (n t : ℕ) (hn : 1≤n) (ht : 1≤t) :
    prob n (Tset t 0)=mu n 0 := by
  classical
  rw [prob_finite]
  have hnQ : (n:ℚ)≠0 := by exact_mod_cast (by omega : n≠0)
  simp only [Tset,ite_true,Set.mem_singleton_iff,div_eq_zero_iff,hnQ,or_false,
    Nat.cast_eq_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro y hy hy0; simp [hy0]
  · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim

/-- Rational interval membership for either time scale. -/
private theorem block_membership (a t k y : ℕ) (ha : 1≤a) (ht : 1≤t) (hk : 1≤k) :
    ((y:ℚ)/(a*t))∈Tset t k ↔ a*(k-1)<y ∧ y≤a*k := by
  have haQ : (0:ℚ)<a := by exact_mod_cast (by omega : 0<a)
  have htQ : (0:ℚ)<t := by exact_mod_cast (by omega : 0<t)
  simp only [Tset,show k≠0 by omega,ite_false,Set.mem_Ioc]
  rw [div_lt_div_iff₀ htQ (mul_pos haQ htQ),
    div_le_div_iff₀ (mul_pos haQ htQ) htQ]
  have hkQ : ((k-1:ℕ):ℚ)=(k:ℚ)-1 := by rw [Nat.cast_sub hk]; norm_num
  constructor
  · intro h
    constructor
    · have h' : (a:ℚ)*((k:ℚ)-1)<y := by nlinarith [h.1]
      rw [←hkQ] at h'
      exact_mod_cast h'
    · have h' : (y:ℚ)≤(a:ℚ)*k := by nlinarith [h.2]
      exact_mod_cast h'
  · intro h
    have hl : (a:ℚ)*((k:ℚ)-1)<y := by
      have h0 : (a:ℚ)*((k-1:ℕ):ℚ)<y := by exact_mod_cast h.1
      simpa only [hkQ] using h0
    have hu : (y:ℚ)≤(a:ℚ)*k := by exact_mod_cast h.2
    constructor <;> nlinarith

/-- Truncating a prefix indicator does not alter its finite sum. -/
private theorem sum_prefix (f : ℕ → ℝ) (N Y : ℕ) (hY : Y≤N) :
    (∑ y ∈ Finset.range (N+1), if y≤Y then f y else 0) =
      ∑ y ∈ Finset.range (Y+1), f y := by
  classical
  symm
  calc
    (∑ y ∈ Finset.range (Y+1), f y) =
        ∑ y ∈ Finset.range (Y+1), if y≤Y then f y else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      simp [show y≤Y by have := Finset.mem_range.mp hy; omega]
    _ = _ := by
      apply Finset.sum_subset
      · exact Finset.range_mono (by omega)
      · intro y hy hyY
        simp [show ¬y≤Y by have h := hyY; simp only [Finset.mem_range] at h; omega]

/-- Interval blocks are differences of inclusive cumulative probabilities. -/
private theorem prob_block (a t k : ℕ) (ha : 1≤a) (ht : 1≤t) (hk : 1≤k) (hkt : k≤t) :
    prob (a*t) (Tset t k) =
      (∑ y ∈ Finset.range (a*k+1), mu (a*t) y) -
      (∑ y ∈ Finset.range (a*(k-1)+1), mu (a*t) y) := by
  classical
  rw [prob_finite]
  simp only [Nat.cast_mul,block_membership a t k _ ha ht hk]
  have hb : a*(k-1)≤a*k := Nat.mul_le_mul_left _ (by omega)
  have hu : a*k≤a*t := Nat.mul_le_mul_left _ hkt
  calc
    (∑ y ∈ Finset.range (a*t+1), if a*(k-1)<y ∧ y≤a*k then mu (a*t) y else 0) =
        ∑ y ∈ Finset.range (a*t+1),
          ((if y≤a*k then mu (a*t) y else 0) -
            (if y≤a*(k-1) then mu (a*t) y else 0)) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyb : y≤a*(k-1)
      · have hyc : y≤a*k := hyb.trans hb
        have hlt : ¬a*(k-1)<y := by omega
        simp only [hyb,hyc,hlt,false_and,ite_true,ite_false,sub_self]
      · by_cases hyc : y≤a*k
        · have hlt : a*(k-1)<y := by omega
          simp only [hyb,hyc,hlt,and_self,ite_true,ite_false,sub_zero]
        · simp only [hyb,hyc,and_false,ite_true,ite_false,sub_zero]
    _ = _ := by
      rw [Finset.sum_sub_distrib,sum_prefix _ _ _ hu,sum_prefix _ _ _ (hb.trans hu)]

end D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.ProbabilityBlocks
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.Scaling
open D5.S3.Quantum.Walks.Riesz.Decimation.FiniteScaling
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.Riesz.Decimation.Parity D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.RieszWalkSelfSimilarity
/-- The complete cumulative identity conditional solely on the Schur/CMV
identification supplied by SpectralBridge. -/
private theorem cumulative_scale_four {chi : ℕ → (LaurentPolynomial ℝ)} (hb : SpectralBridge chi) (t x : ℕ) :
    cumulative (2*t) (2*x) = cumulative (8*t) (8*x) := by
  obtain ⟨h,hh,hn⟩ := cumulative_projection hb (2*t) (2*x)
  obtain ⟨k,hk,kn⟩ := cumulative_projection hb (8*t) (8*x)
  have heq := projection_norm_scale_four x t hh hk
  simpa only [hn,kn] using heq


end D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.Scaling
end

noncomputable section
namespace D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.ConditionalClaim
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.Riesz.Decimation.Parity D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.RieszWalkSelfSimilarity D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.Scaling
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.RieszWalkSelfSimilarity D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.ProbabilityBlocks

/-- The last combinatorial step: cumulative scale-four equality gives exactly
Conjecture 4.2, including the origin block and rational interval endpoints. -/
private theorem claim_of_cumulative
    (hc : ∀ t x : ℕ, cumulative (2*t) (2*x)=cumulative (8*t) (8*x)) : claim := by
  intro t ht k hkt
  by_cases hk : k=0
  · subst k
    rw [prob_origin (2*t) t (by omega) ht,prob_origin (8*t) t (by omega) ht]
    simpa [cumulative] using hc t 0
  · have hk1 : 1≤k := by omega
    rw [prob_block 2 t k (by omega) ht hk1 hkt,
      prob_block 8 t k (by omega) ht hk1 hkt]
    change cumulative (2*t) (2*k)-cumulative (2*t) (2*(k-1)) =
      cumulative (8*t) (8*k)-cumulative (8*t) (8*(k-1))
    rw [hc t k,hc t (k-1)]


end D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.ConditionalClaim
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.RieszWalkSelfSimilarity
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.Riesz.Decimation.Parity D5.S3.Quantum.Walks.CMV.Representation.SpectralReduction D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Representation.Walk D5.S3.Quantum.Walks.RieszWalkSelfSimilarity D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.Scaling D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.ConditionalClaim
private theorem cumulative_scale_four (t x : ℕ) :
    cumulative (2*t) (2*x) = cumulative (8*t) (8*x) :=
  D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.Scaling.cumulative_scale_four
    ⟨chi_zero,chi_orthonormal,chi_window,
      D5.S3.Quantum.Walks.CMV.Representation.BandedBridge.one_step_of_pair_relations
        (D5.S3.Quantum.Walks.CMV.Representation.CMVFromGramParameters.pair_relations_of_parameters D5.S3.Quantum.Walks.CMV.Geronimus.schur_equals_gram)⟩ t x

theorem result : claim :=
  D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.ConditionalClaim.claim_of_cumulative cumulative_scale_four

end D5.S3.Quantum.Walks.RieszWalkSelfSimilarity
end
