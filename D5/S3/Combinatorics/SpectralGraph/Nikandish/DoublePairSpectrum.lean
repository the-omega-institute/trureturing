/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/DoublePairSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/DoublePairSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete positive double-pair obstruction on actual ideal graphs. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.DoublePairCubic
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift

/-! Source: four-prime-double-pair-completion, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. All positive exponent pairs
and coordinate permutations are retained. The lower bound and actual
graph lift reuse the delivered paired owners. The full four-prime and
higher-prime Q3 outside proved families remains open. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.DoublePairSpectrum
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open PairedIdealIntersectionLift IdealIntersectionSupport IdealIntersectionObstructions

/-- Full real ordered double-pair domain, including both boundaries. -/
theorem low_eigenpair (a b : ℝ) (ha : 2≤a) (hab : a≤b) :
    ∃ e : ℝ, 1<e ∧ e<4 ∧ ∃ v : Fin 2 × Fin 2 → ℝ,
      v≠0 ∧ symmetricK a b b*ᵥv=e • v := by
  let M:=symmetricK a b b-(4:ℝ) • 1
  have hM : M.IsHermitian := (symmetric_hermitian a b b).sub (by simp)
  have hdet : M.det<0 := by
    rw [show M=symmetricK a b b-(4:ℝ) • 1 from rfl,
      tensor_symmetric_det_shift a b b 4 (by linarith) (by linarith),
      DoublePairCubic.factorization]
    exact mul_neg_of_neg_of_pos (by linarith) (DoublePairCubic.four_positive a b ha hab)
  have hno : ¬M.PosSemidef := fun hp => (not_le_of_gt hdet) hp.det_nonneg
  obtain ⟨e,he,v,hv,hve⟩ := negative_eigenpair_of_not_posSemidef M hM hno
  have hS : symmetricK a b b*ᵥv=(e+4) • v := by
    dsimp [M] at hve
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hve
    ext q
    have ht:=congrFun hve q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht ⊢
    linarith
  exact ⟨e+4,symmetric_eigenvalue_gt_one a b b (by linarith) (by linarith)
    (by linarith) _ v hv hS,by linarith,v,hv,hS⟩

private theorem eigenvalue_ne_of_det_ne (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (e r : ℝ) (h : Fin 2 × Fin 2 → ℝ) (hh : h≠0) (he : M*ᵥh=e • h)
    (hd : (M-r • 1).det≠0) : e≠r := by
  intro her
  apply hh
  apply Matrix.eq_zero_of_mulVec_eq_zero hd
  rw [sub_mulVec,he,smul_mulVec,one_mulVec,her,sub_self]

/-- No bounded exponent enumeration or scalar proxy is used. -/
theorem noninteger_eigenpair (a b : ℕ) (ha : 2≤a) (hab : a≤b) :
    ∃ e : ℝ, 1<e ∧ e<4 ∧ (¬∃ z : ℤ, e=z) ∧
      ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧ tensorK (a:ℝ) (b:ℝ) (b:ℝ)*ᵥh=e • h := by
  have haR : (2:ℝ)≤a := by exact_mod_cast ha
  have habR : (a:ℝ)≤b := by exact_mod_cast hab
  have hb : 0<b := by omega
  obtain ⟨e,hel,heu,v,hv,hS⟩ := low_eigenpair (a:ℝ) (b:ℝ) haR habR
  obtain ⟨h,hh,hE⟩ := tensor_eigenpair_of_symmetric (a:ℝ) (b:ℝ) (b:ℝ)
    (by positivity) (by positivity) e v hv hS
  have he2 : e≠2 := eigenvalue_ne_of_det_ne _ e 2 h hh hE (by
    rw [DoublePairCubic.factorization,DoublePairCubic.endpoint_two]
    exact mul_ne_zero (by linarith) (DoublePairCubic.two_nonzero a b ha hb))
  have he3 : e≠3 := eigenvalue_ne_of_det_ne _ e 3 h hh hE (by
    rw [DoublePairCubic.factorization,DoublePairCubic.endpoint_three]
    exact mul_ne_zero (by linarith) (DoublePairCubic.three_nonzero a b ha hab))
  refine ⟨e,hel,heu,?_,h,hh,hE⟩
  rintro ⟨z,hz⟩
  have hzl : (1:ℤ)<z := by exact_mod_cast (hz ▸ hel)
  have hzu : z<(4:ℤ) := by exact_mod_cast (hz ▸ heu)
  have hz23 : z=2 ∨ z=3 := by omega
  rcases hz23 with rfl | rfl
  · apply he2; simpa using hz
  · apply he3; simpa using hz

private theorem ordered_actual (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0<a) (hab : a≤b) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b b)) := by
  have hb : 0<b := by omega
  have hk (i : Fin 4) : 0<pairExponents a b b i := by
    fin_cases i <;> simp [pairExponents] <;> assumption
  by_cases ha1 : a=1
  · exact (unit_exponent_obstruction p hp hinj _ hk (by norm_num) 0
      (by simp [pairExponents,ha1])).choose_spec.2.2.2
  obtain ⟨e,_,_,hne,h,hh,hE⟩ := noninteger_eigenpair a b (by omega) hab
  have hactual := actual_paired_eigenvalue p hp hinj a b b ha hb hb e h hh hE
  intro H
  obtain ⟨z,hz⟩ := H _ hactual
  apply hne
  refine ⟨((((a+1)^2*(b+1)*(b+1))-2 : ℕ):ℤ)+1-z,?_⟩
  push_cast
  linarith

/-- Every positive double pair, without an ordering assumption, is
nonintegral on the actual graph of nonzero proper ideals. -/
theorem actual_nonintegral (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b b)) := by
  rcases le_total a b with hab | hba
  · exact ordered_actual p hp hinj a b ha hab
  · let τ : Equiv.Perm (Fin 4) := (Equiv.swap 0 2).trans (Equiv.swap 1 3)
    let q : Fin 4 → ℕ := fun i => p (τ i)
    have hqp (i : Fin 4) : Nat.Prime (q i) := hp (τ i)
    have hqi : Function.Injective q := hinj.comp τ.injective
    have hm : modulus q (pairExponents b a a)=modulus p (pairExponents a b b) := by
      simp [modulus,pairExponents,q,τ,Fin.prod_univ_four,Equiv.swap_apply_def]
      ring
    rw [←hm]
    exact ordered_actual q hqp hqi b a hb hba

/-- Arbitrary coordinate permutations retain distinct primes and every
positive exponent; the all-equal diagonal is included. -/
theorem double_pair_obstruction (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (σ : Equiv.Perm (Fin 4))
    (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    ¬ActualLaplacianIntegral (modulus p (fun i => pairExponents a b b (σ i))) := by
  let q:=fun i=>p (σ.symm i)
  have hqp (i : Fin 4) : Nat.Prime (q i) := hp (σ.symm i)
  have hqi : Function.Injective q := hinj.comp σ.symm.injective
  have hm : modulus q (pairExponents a b b)=
      modulus p (fun i => pairExponents a b b (σ i)) := by
    unfold modulus
    simpa [q] using (Equiv.prod_comp σ (fun i => p (σ.symm i)^pairExponents a b b i)).symm
  rw [←hm]
  exact actual_nonintegral q hqp hqi a b ha hb

end D5.S3.Combinatorics.SpectralGraph.DoublePairSpectrum
