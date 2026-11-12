/- GID: D5/S3/Combinatorics/SpectralGraph/BalancedPairSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/BalancedPairSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full balanced-region and repeated-minimum spectral bounds with actual graph lifts. -/
import D5.S3.Combinatorics.SpectralGraph.BalancedPairDeterminant
import D5.S3.Combinatorics.SpectralGraph.PairedTensorMinimum
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift

/-! Source: four-prime-single-pair-balanced, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. All boundaries and the
full three independent real parameters are included. The separate upper
bound on all repeated minima is not itself a nonintegrality theorem.
General Q3 and the neighboring-boundary limitations remain unchanged. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.BalancedPairSpectrum
open PairedIdealIntersectionObstructions PairedIdealIntersectionLift IdealIntersectionSupport

/-- A negative two-cell principal determinant gives the upper bound four on
all repeated minima, without an ordering assumption between the tails. -/
theorem repeated_minimum_low (a b c : ℝ) (ha : 5≤a) (hb : a≤b) (hc : a≤c) :
    ∃ e : ℝ, 1<e ∧ e<4 ∧ ∃ v : Fin 2 × Fin 2 → ℝ,
      v≠0 ∧ symmetricK a b c*ᵥv=e • v := by
  let M:=symmetricK a b c-(4:ℝ) • 1
  have hM : M.IsHermitian := (symmetric_hermitian a b c).sub (by simp)
  have hno : ¬M.PosSemidef := by
    intro hp
    let j : Fin 2 → Fin 2 × Fin 2 := fun i => if i=0 then (0,0) else (1,1)
    have hd:= (hp.submatrix j).det_nonneg
    have he : (M.submatrix j j).det =
        -(2*a+3)*(b-a)*(c-a)-(a^2+5*a+3)*((b-a)+(c-a))-5*a^2-15*a+9 := by
      simp [M,j,symmetricK,E,H,Matrix.det_fin_two,Matrix.submatrix,
        kroneckerMap_apply]
      ring_nf
      simp [Real.sq_sqrt (by linarith : 0≤b),Real.sq_sqrt (by linarith : 0≤c)]
      ring
    rw [he] at hd
    have h1 : 0≤(2*a+3)*(b-a)*(c-a) := by positivity
    have h2 : 0≤(a^2+5*a+3)*((b-a)+(c-a)) := by positivity
    nlinarith [sq_nonneg a]
  obtain ⟨e,he,v,hv,hve⟩ := negative_eigenpair_of_not_posSemidef M hM hno
  have hS : symmetricK a b c*ᵥv=(e+4) • v := by
    dsimp [M] at hve
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hve
    ext q
    have ht:=congrFun hve q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht ⊢
    linarith
  exact ⟨e+4,symmetric_eigenvalue_gt_one a b c (by linarith)
    (by linarith) (by linarith) _ v hv hS,by linarith,v,hv,hS⟩

/-- The full source interval on the genuine four-dimensional restriction. -/
theorem balanced_eigenpair (a b c : ℝ) (hab : a≤b) (hbc : b≤c)
    (hca : c≤2*a-6) :
    ∃ e : ℝ, 3<e ∧ e<4 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h≠0 ∧ tensorK a b c*ᵥh=e • h := by
  have ha : 6≤a := by linarith
  obtain ⟨e,_,he,v,hv,hE⟩ := repeated_minimum_low a b c (by linarith) hab (by linarith)
  obtain ⟨h,hh,hT⟩ := tensor_eigenpair_of_symmetric a b c (by linarith) (by linarith) e v hv hE
  exact ⟨e,BalancedPairDeterminant.eigenvalue_gt_three a b c e hab hbc hca h hh hT,
    he,h,hh,hT⟩

/-- Every positive integer vector in the whole balanced region has an actual
ideal-graph eigenvalue in the original strict unit interval. -/
theorem actual_balanced_interval (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (hab : a≤b) (hbc : b≤c)
    (hca : c+6≤2*a) :
    let V : ℕ := (a+1)^2*(b+1)*(c+1)-2
    ∃ ell : ℝ, IdealIntersectionObstructions.HasActualEigenvalue
      (modulus p (pairExponents a b c)) ell ∧ (V:ℝ)-3<ell ∧ ell<(V:ℝ)-2 := by
  dsimp only
  have ha : 6≤a := by omega
  have hb : 0<b := by omega
  have hc : 0<c := by omega
  have haR : (6:ℝ)≤a := by exact_mod_cast ha
  have hcaR : (c:ℝ)+6≤2*(a:ℝ) := by exact_mod_cast hca
  obtain ⟨e,hel,heu,h,hh,hE⟩ := balanced_eigenpair (a:ℝ) (b:ℝ) (c:ℝ)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) (by linarith)
  have ht:=actual_paired_eigenvalue p hp hinj a b c (by omega) hb hc e h hh hE
  exact ⟨_,ht,by linarith,by linarith⟩

/-- Entire balanced-domain actual graph nonintegrality, including equality
at either tail boundary. No finite exponent base is used. -/
theorem actual_nonintegral (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (hab : a≤b) (hbc : b≤c)
    (hca : c+6≤2*a) :
    ¬IdealIntersectionObstructions.ActualLaplacianIntegral
      (modulus p (pairExponents a b c)) := by
  obtain ⟨ell,he,hl,hu⟩:=actual_balanced_interval p hp hinj a b c hab hbc hca
  intro H
  obtain ⟨z,hz⟩:=H ell he
  rw [hz] at hl hu
  have hlI : (((a+1)^2*(b+1)*(c+1)-2:ℕ):ℤ)-3<z := by exact_mod_cast hl
  have huI : z<(((a+1)^2*(b+1)*(c+1)-2:ℕ):ℤ)-2 := by exact_mod_cast hu
  omega

/-- The smallest full-operator eigenpair, including comparison against all
real eigenpairs, has exactly the original balanced open interval. -/
theorem minimum_window (a b c : ℝ) (hab : a≤b) (hbc : b≤c)
    (hca : c≤2*a-6) :
    ∃ e : ℝ, 3<e ∧ e<4 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h≠0 ∧ tensorK a b c*ᵥh=e • h ∧
      ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z≠0 → tensorK a b c*ᵥz=r • z → e≤r := by
  have ha : 6≤a := by linarith
  obtain ⟨e,_,h,hh,hE,hmin⟩:=PairedTensorMinimum.minimum a b c
    (by linarith) (by linarith) (by linarith)
  obtain ⟨r,_,hr,z,hz,hR⟩:=balanced_eigenpair a b c hab hbc hca
  exact ⟨e,BalancedPairDeterminant.eigenvalue_gt_three a b c e hab hbc hca h hh hE,
    lt_of_le_of_lt (hmin r z hz hR) hr,h,hh,hE,hmin⟩

end D5.S3.Combinatorics.SpectralGraph.BalancedPairSpectrum
