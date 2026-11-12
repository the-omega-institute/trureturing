/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairLowArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairLowArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine low-root divisibility and coprime completion on actual four-prime ideal graphs. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairRootArithmetic
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairTailSpectrum
import D5.S3.Combinatorics.SpectralGraph.Nikandish.BalancedPairSpectrum
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairFourEndpoints
import Mathlib.RingTheory.Coprime.Lemmas

/-! Sources: PR9 four-prime-low-root-divisibility, four-prime-coprime-completion
and four-prime-root-valuation, revision 6d491f77b35dec808fc777b69939c56cdae5dc02.
The original eleven quadratic rows are retained. Two additional exact
quadratic rows handle a=7 directly, replacing only that proof's modular
branch; the full general-index modular theorem remains a distinct obligation.
Every final conclusion below concerns the actual ideal-intersection graph.
Passing a necessary root-divisibility condition never proves integrality. -/
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.PairLowArithmetic
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open PairedIdealIntersectionLift IdealIntersectionSupport IdealIntersectionObstructions

/-- Actual integrality forces a genuine integer root two or three of the
full K; no scalar compression or assumed integer-root condition is used. -/
theorem actual_low_root (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 5≤a) (hb : a≤b) (hc : a≤c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    (tensorK (a:ℤ) b c-(2:ℤ) • 1).det=0 ∨
      (tensorK (a:ℤ) b c-(3:ℤ) • 1).det=0 := by
  obtain ⟨e,hel,heu,v,hv,hS⟩:=BalancedPairSpectrum.repeated_minimum_low
    (a:ℝ) b c (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
  obtain ⟨h,hh,hT⟩:=tensor_eigenpair_of_symmetric (a:ℝ) b c
    (by exact_mod_cast (show 0<b by omega)) (by exact_mod_cast (show 0<c by omega))
    e v hv hS
  obtain ⟨z,hz⟩:=PairTailSpectrum.integer_tensor_root p hp hinj a b c
    (by omega) (by omega) (by omega) H e h hh hT
  have hzl : (1:ℤ)<z := by exact_mod_cast (hz ▸ hel)
  have hzu : z<(4:ℤ) := by exact_mod_cast (hz ▸ heu)
  have hd:=PairTailSpectrum.integer_det_zero a b c (z-a-1) e
    (by push_cast; linarith) h hh hT
  have ht : (a:ℤ)+1+(z-a-1)=z := by ring
  rw [ht] at hd
  rcases (show z=2 ∨ z=3 by omega) with rfl | rfl
  · exact Or.inl hd
  · exact Or.inr hd

/-- Full necessary low-root disjunction, with unrestricted ordering of tails. -/
theorem actual_divisibility (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 5≤a) (hb : a≤b) (hc : a≤c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    ((a:ℤ)-1)∣3*(b:ℤ)^2*(c:ℤ)^2 ∨ ((a:ℤ)-2)∣20*(b:ℤ)^2*(c:ℤ)^2 := by
  rcases actual_low_root p hp hinj a b c ha hb hc H with h2 | h3
  · left
    convert PairRootArithmetic.root_divides (a:ℤ) b c 2 h2 using 1 <;> ring
  · right
    convert PairRootArithmetic.root_divides (a:ℤ) b c 3 h3 using 1 <;> ring

/-- The full empty/full principal-minor cutoff is strict even when a tail
equals 2a-2. This supplies both the coprime and resonant-family consumers. -/
theorem large_tail_low (a b c : ℝ) (ha : 2≤a) (hb : 2*a-2≤b) (hc : 2*a-2≤c) :
    ∃ e : ℝ, 1<e ∧ e<3 ∧ ∃ v : Fin 2 × Fin 2 → ℝ,
      v≠0 ∧ symmetricK a b c*ᵥv=e • v := by
  let M:=symmetricK a b c-(3:ℝ) • 1
  have hM : M.IsHermitian := (symmetric_hermitian a b c).sub (by simp)
  have hno : ¬M.PosSemidef := by
    intro hp
    let j : Fin 2 → Fin 2 × Fin 2 := fun i => if i=0 then (0,0) else (1,1)
    have hd:=(hp.submatrix j).det_nonneg
    have he : (M.submatrix j j).det =
        -(a+2)*(b-(2*a-2))*(c-(2*a-2))-
        (a^2+3*a-2)*((b-(2*a-2))+(c-(2*a-2)))-2*(a-1)*(3*a+2) := by
      simp [M,j,symmetricK,E,H,det_fin_two,submatrix,kroneckerMap_apply]
      ring_nf
      simp [Real.sq_sqrt (by linarith : 0≤b),Real.sq_sqrt (by linarith : 0≤c)]
      ring
    rw [he] at hd
    have h1 : 0≤(a+2)*(b-(2*a-2))*(c-(2*a-2)) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have h2 : 0≤(a^2+3*a-2)*((b-(2*a-2))+(c-(2*a-2))) := by
      have he : 0≤a^2+3*a-2 := by nlinarith [sq_nonneg a]
      exact mul_nonneg he (by linarith)
    have h3 : 0<2*(a-1)*(3*a+2) :=
      mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    linarith
  obtain ⟨e,he,v,hv,hE⟩:=negative_eigenpair_of_not_posSemidef M hM hno
  have hS : symmetricK a b c*ᵥv=(e+3) • v := by
    dsimp [M] at hE
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hE
    ext q
    have ht:=congrFun hE q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht ⊢
    linarith
  exact ⟨e+3,symmetric_eigenvalue_gt_one a b c (by linarith)
    (by linarith) (by linarith) _ v hv hS,by linarith,v,hv,hS⟩

end D5.S3.Combinatorics.SpectralGraph.PairLowArithmetic
