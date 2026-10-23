/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Lift
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Exact five-row middle-gap concentration and unequal-mass norm lift. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
set_option autoImplicit false
open Finset
open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift
open UniformSpectralBound.SharedSpectral
noncomputable section

def middle (N : ℕ) : Finset (Fin N) :=
  univ.filter (fun i => 9 ≤ i.val ∧ i.val < N-15)
def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ := ∑ i ∈ middle N, g i
def frozen {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ :=
  ∑ i ∈ univ.filter (fun i => i ∉ middle N), g i • step N (i.val+1)
def concentrated {N : ℕ} (g : Fin N → ℝ) (j : Fin N) : Fin N → ℝ :=
  frozen g+middleMass g • step N (j.val+1)

private theorem split_gaps {N : ℕ} (g : Fin N → ℝ) :
    frozen g+∑ i ∈ middle N, g i • step N (i.val+1) =
      ∑ i, g i • step N (i.val+1) := by
  classical
  have hs : (∑ i ∈ middle N, g i • step N (i.val+1)) =
      ∑ i, if i ∈ middle N then g i • step N (i.val+1) else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  rw [hs]
  simp only [frozen,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ middle N <;> simp [hi]

/-- Reconstructed concentrated vectors remain nonnegative. This follows
from genuine nonnegative gaps, not from a target moment inequality. -/
theorem concentrated_nonnegative {N : ℕ} (l : Fin N → ℝ) (ho : Antitone l)
    (hn : ∀ i,0 ≤ l i) (j : Fin N) :
    ∀ k,0 ≤ concentrated (spectralGap l) j k := by
  have hg := spectralGap_nonneg l ho hn
  have hstep (i k : Fin N) : 0 ≤ step N (i.val+1) k := by
    unfold step
    split_ifs <;> norm_num
  intro k
  have hm : 0 ≤ middleMass (spectralGap l) := sum_nonneg (fun i _ => hg i)
  unfold concentrated frozen
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  exact add_nonneg (sum_nonneg (fun i _ => mul_nonneg (hg i) (hstep i k)))
    (mul_nonneg hm (hstep j k))

/-- The actual middle mass is lambda_10-lambda_(N-14) in one-based notation. -/
theorem middle_mass_actual {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) :
    middleMass (spectralGap l) = l ⟨9,by omega⟩-l ⟨N-15,by omega⟩ := by
  classical
  unfold middleMass middle
  simp only [Finset.sum_filter,spectralGap]
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ =>
    if 9 ≤ i ∧ i < N-15 then extend l i-extend l (i+1) else 0)]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,add_zero]
  have hf : (range N).filter (fun i => 9 ≤ i ∧ i < N-15) = Ico 9 (N-15) := by
    ext i
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [hf,gap_telescope l 9 (N-15) (by omega)]
  simp [extend,show 9 < N by omega,show N-15 < N by omega]

/-- Every concentrated spectrum has EXACTLY the original top ten and bottom
fifteen labelled values. The middle values need not be equal in the input. -/
theorem concentrated_boundary {N : ℕ} (l : Fin N → ℝ) (j : Fin N)
    (hj : j ∈ middle N) (k : Fin N) (hk : k.val < 10 ∨ N-15 ≤ k.val) :
    concentrated (spectralGap l) j k = l k := by
  classical
  have hsplit := split_gaps (spectralGap l)
  rw [gap_reconstruct l] at hsplit
  have hstep (i : Fin N) (hi : i ∈ middle N) :
      step N (i.val+1) k = step N (j.val+1) k := by
    have hmi : 9 ≤ i.val ∧ i.val < N-15 := (mem_filter.mp hi).2
    have hmj : 9 ≤ j.val ∧ j.val < N-15 := (mem_filter.mp hj).2
    rcases hk with hk | hk
    · simp [step,show k.val < i.val+1 by omega,show k.val < j.val+1 by omega]
    · simp [step,show ¬ k.val < i.val+1 by omega,show ¬ k.val < j.val+1 by omega]
  have hsum : (∑ i ∈ middle N, spectralGap l i • step N (i.val+1)) k =
      middleMass (spectralGap l)*step N (j.val+1) k := by
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,middleMass]
    rw [Finset.sum_mul]
    exact sum_congr rfl (fun i hi => by rw [hstep i hi])
  have hv := congrFun hsplit k
  simpa [concentrated,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hsum] using hv

/-- Reuse the canonical norm cone; no equal-mass or squared-Jensen premise. -/
theorem concentration_transfer {N : ℕ} (hN : 25 ≤ N) (theta : ℝ) (ht : 0 ≤ theta)
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hc : ∀ j ∈ middle N,
      0 ≤ ∑ i, concentrated (spectralGap l) j i)
    (hb : ∀ j ∈ middle N,
      ∑ i, (concentrated (spectralGap l) j i)^2 ≤
        theta*(∑ i, concentrated (spectralGap l) j i)^2) :
    ∑ i, (l i)^2 ≤ theta*(∑ i, l i)^2 := by
  have hm : (middle N).Nonempty := by
    refine ⟨⟨9,by omega⟩,?_⟩
    simp [middle]
    omega
  have hg := spectralGap_nonneg l ho hn
  have hg0 : 0 ≤ middleMass (spectralGap l) := sum_nonneg (fun i _ => hg i)
  have hgood : spectralGood (Real.sqrt theta) l := by
    have hfixed (j : Fin N) (hj : j ∈ middle N) :
        spectralGood (Real.sqrt theta) (concentrated (spectralGap l) j) := by
      apply spectralGood_of_square _ _ (Real.sqrt_nonneg _) (hc j hj)
      simpa [Real.sq_sqrt ht] using hb j hj
    have hmix := mixture_transfer (spectralGood (Real.sqrt theta))
      (spectralGood_zero N _) (fun x y hx hy => spectralGood_add _ x y hx hy)
      (fun t x ht' hx => spectralGood_smul _ t x ht' hx)
      (middle N) hm (spectralGap l) (fun i => step N (i.val+1))
      (frozen (spectralGap l)) (fun i _ => hg i) hfixed
    rwa [split_gaps,gap_reconstruct] at hmix
  have h := spectralGood_square (Real.sqrt theta) l (Real.sqrt_nonneg _)
    (sum_nonneg (fun i _ => hn i)) hgood
  simpa [Real.sq_sqrt ht] using h

/-- Augmented Euclidean triangle inequality for an arbitrary finite convex
mixture and a common loss c. This retains c and UNEQUAL individual masses. -/
theorem augmented_norm_lift {I J : Type*} [Fintype I] [Fintype J]
    (p : I → ℝ) (x : I → J → ℝ) (l : J → ℝ) (theta c : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) (ht : 0 ≤ theta) (hc : 0 ≤ c)
    (hm : ∀ i, 0 ≤ ∑ j, x i j)
    (hr : ∀ j, l j=∑ i, p i*x i j)
    (hb : ∀ i, (∑ j, (x i j)^2)+c ≤ theta*(∑ j, x i j)^2) :
    (∑ j, (l j)^2)+c ≤ theta*(∑ j, l j)^2 := by
  classical
  let X : I → EuclideanSpace ℝ (J ⊕ Unit) := fun i =>
    WithLp.toLp 2 (Sum.elim (x i) (fun _ => Real.sqrt c))
  let L : EuclideanSpace ℝ (J ⊕ Unit) :=
    WithLp.toLp 2 (Sum.elim l (fun _ => Real.sqrt c))
  have hX (i : I) : ‖X i‖^2=(∑ j, (x i j)^2)+c := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [X,Fintype.sum_sum_type,Real.sq_sqrt hc]
  have hL : ‖L‖^2=(∑ j, (l j)^2)+c := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [L,Fintype.sum_sum_type,Real.sq_sqrt hc]
  have hid : L=∑ i, p i • X i := by
    ext j
    cases j with
    | inl j => simpa [L,X] using hr j
    | inr j => simp [L,X,← sum_mul,hs]
  have hterm (i : I) : ‖X i‖ ≤ Real.sqrt theta*(∑ j, x i j) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (hm i))).mp
    rw [hX,mul_pow,Real.sq_sqrt ht]
    exact hb i
  have hmass : (∑ j,l j)=∑ i,p i*(∑ j,x i j) := by
    simp_rw [hr,Finset.mul_sum]
    exact Finset.sum_comm
  have hmL : 0 ≤ ∑ j,l j := by
    rw [hmass]
    exact sum_nonneg (fun i _ => mul_nonneg (hp i) (hm i))
  have hnorm : ‖L‖ ≤ Real.sqrt theta*(∑ j,l j) := by
    rw [hid,hmass,Finset.mul_sum]
    calc
      _ ≤ ∑ i, ‖p i • X i‖ := norm_sum_le _ _
      _ = ∑ i, p i*‖X i‖ := by simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg,hp]
      _ ≤ ∑ i, Real.sqrt theta*(p i*(∑ j,x i j)) := by
        apply sum_le_sum
        intro i _
        nlinarith [mul_le_mul_of_nonneg_left (hterm i) (hp i)]
  have hsquare := (sq_le_sq₀ (norm_nonneg L)
    (mul_nonneg (Real.sqrt_nonneg theta) hmL)).mpr hnorm
  rw [hL,mul_pow,Real.sq_sqrt ht] at hsquare
  exact hsquare
end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift
