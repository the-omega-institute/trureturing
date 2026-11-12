/- GID: D5/S3/Combinatorics/SpectralGraph/PairFourSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairFourSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full repeated-four nonintegrality on actual ideal-intersection graphs. -/
import D5.S3.Combinatorics.SpectralGraph.PairFourEndpoints
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift
import D5.S3.Combinatorics.SpectralGraph.FourPrimeIdealIntersectionObstructions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! Source: four-prime-pair-four, supplied PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. The actual four-dimensional
operator and graph lift are reused at their original scope. The exceptional
pair has a cubic root in (7,8); passing necessary endpoint tests is never
asserted sufficient for graph integrality. General Q3 remains open. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.PairFourSpectrum
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open PairedIdealIntersectionLift IdealIntersectionSupport IdealIntersectionObstructions

/-- A real eigenvalue lies in the full source window for every b,c>=2. -/
theorem low_eigenpair (b c : ℝ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    ∃ e : ℝ, 1 < e ∧ e < 4 ∧ ∃ v : Fin 2 × Fin 2 → ℝ,
      v ≠ 0 ∧ symmetricK 4 b c *ᵥ v=e • v := by
  let M := symmetricK 4 b c-(4:ℝ) • 1
  have hM : M.IsHermitian := (symmetric_hermitian 4 b c).sub (by simp)
  have hno : ¬M.PosSemidef := by
    intro hp
    let z : Fin 2 × Fin 2 → ℝ := fun q =>
      if q=(0,0) then 1 else if q=(1,1) then -4*Real.sqrt b*Real.sqrt c else 0
    have hn := hp.dotProduct_mulVec_nonneg z
    have he : star z ⬝ᵥ (M*ᵥ z) = -11*b*c+5*b+5*c+5 := by
      simp [M,z,symmetricK,E,H,mulVec,dotProduct,Fintype.sum_prod_type,
        Fin.sum_univ_succ,kroneckerMap_apply]
      ring_nf
      simp [Real.sq_sqrt (by linarith : 0≤b),Real.sq_sqrt (by linarith : 0≤c)]
      ring
    rw [he] at hn
    have hpos : 0 ≤ (b-2)*(c-2) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  obtain ⟨e,he,v,hv,hve⟩ := negative_eigenpair_of_not_posSemidef M hM hno
  have hS : symmetricK 4 b c*ᵥv=(e+4) • v := by
    dsimp [M] at hve
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hve
    ext q
    have ht:=congrFun hve q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht ⊢
    linarith
  exact ⟨e+4,symmetric_eigenvalue_gt_one 4 b c (by norm_num)
    (by linarith) (by linarith) _ v hv hS,by linarith,v,hv,hS⟩

private theorem symmetric_index (a b c e : ℝ)
    (v : Fin 2 × Fin 2 → ℝ) (hv : v≠0) (he : symmetricK a b c*ᵥv=e • v) :
    ∃ q, (symmetric_hermitian a b c).eigenvalues q=e := by
  have hspec : e ∈ spectrum ℝ (symmetricK a b c) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    change (symmetricK a b c).charpoly.eval e=0
    rw [Matrix.eval_charpoly]
    by_contra hd
    apply hv
    apply Matrix.eq_zero_of_mulVec_eq_zero hd
    rw [sub_mulVec,he]
    ext q
    simp [Matrix.scalar,Matrix.mulVec_diagonal]
  rw [(symmetric_hermitian a b c).spectrum_real_eq_range_eigenvalues] at hspec
  exact hspec

private theorem tensor_index (a b c e : ℝ) (hb : 0<b) (hc : 0<c)
    (h : Fin 2 × Fin 2 → ℝ) (hh : h≠0) (he : tensorK a b c*ᵥh=e • h) :
    ∃ q, (symmetric_hermitian a b c).eigenvalues q=e := by
  have hd : (tensorK a b c-e • 1).det=0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨h,hh,?_⟩
    rw [sub_mulVec,he,smul_mulVec,one_mulVec,sub_self]
  have hs : (symmetricK a b c-e • 1).det=0 := by
    rw [tensor_symmetric_det_shift a b c e hb hc]
    exact hd
  obtain ⟨v,hv,hve⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hs
  have hE : symmetricK a b c*ᵥv=e • v := by
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hve
    exact sub_eq_zero.mp hve
  exact symmetric_index a b c e v hv hE

/-- The actual smallest eigenvalue of the full four-cell K, with comparison
against every real eigenpair, lies strictly between one and four. -/
theorem minimum_window (b c : ℝ) (hb : 2≤b) (hc : 2≤c) :
    ∃ e : ℝ, 1<e ∧ e<4 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h≠0 ∧ tensorK 4 b c*ᵥh=e • h ∧
      ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z≠0 → tensorK 4 b c*ᵥz=r • z → e≤r := by
  obtain ⟨q,_,hq⟩ := (univ : Finset (Fin 2 × Fin 2)).exists_min_image
    (symmetric_hermitian 4 b c).eigenvalues univ_nonempty
  let e := (symmetric_hermitian 4 b c).eigenvalues q
  let v : Fin 2 × Fin 2 → ℝ := (symmetric_hermitian 4 b c).eigenvectorBasis q
  have hv : v≠0 :=
    (WithLp.ofLp_eq_zero 2).ne.mpr ((symmetric_hermitian 4 b c).eigenvectorBasis.orthonormal.ne_zero q)
  have hE : symmetricK 4 b c*ᵥv=e • v := (symmetric_hermitian 4 b c).mulVec_eigenvectorBasis q
  obtain ⟨h,hh,hhe⟩ := tensor_eigenpair_of_symmetric 4 b c (by linarith) (by linarith) e v hv hE
  obtain ⟨r,_,hr,z,hz,hze⟩ := low_eigenpair b c hb hc
  obtain ⟨u,hu⟩ := symmetric_index 4 b c r z hz hze
  have heu : e≤r := by simpa only [hu] using hq u (mem_univ u)
  refine ⟨e,symmetric_eigenvalue_gt_one 4 b c (by norm_num) (by linarith)
    (by linarith) e v hv hE,lt_of_le_of_lt heu hr,h,hh,hhe,?_⟩
  intro r z hz hze
  obtain ⟨u,hu⟩ := tensor_index 4 b c r (by linarith) (by linarith) z hz hze
  simpa only [hu] using hq u (mem_univ u)

private theorem eigenvalue_ne_of_det_ne (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (e r : ℝ) (h : Fin 2 × Fin 2 → ℝ) (hh : h ≠ 0) (he : M*ᵥh=e • h)
    (hd : (M-r • 1).det ≠ 0) : e ≠ r := by
  intro her
  apply hh
  apply Matrix.eq_zero_of_mulVec_eq_zero hd
  rw [sub_mulVec,he,smul_mulVec,one_mulVec,her,sub_self]

/-- Outside the exact exchanged exceptional pair, the actual witness is
in (V-3,V) and avoids V-1 and V-2. The min construction uses the whole K. -/
theorem actual_nonexception_window (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 2≤b) (hc : 2≤c)
    (hex : ¬((b=2 ∧ c=6) ∨ (b=6 ∧ c=2))) :
    let V : ℕ := (4+1)^2*(b+1)*(c+1)-2
    ∃ ell : ℝ, HasActualEigenvalue (modulus p (pairExponents 4 b c)) ell ∧
      (V:ℝ)-3<ell ∧ ell<(V:ℝ) ∧ ell≠(V:ℝ)-1 ∧ ell≠(V:ℝ)-2 := by
  dsimp only
  obtain ⟨e,hel,heu,h,hh,hE,_⟩ := minimum_window (b:ℝ) (c:ℝ)
    (by exact_mod_cast hb) (by exact_mod_cast hc)
  have hi2:=PairFourEndpoints.two_nonzero (b:ℤ) (c:ℤ) (by omega) (by omega)
  have hi3 : PairFourEndpoints.P3 (b:ℤ) (c:ℤ)≠0 := by
    intro hz
    apply hex
    exact_mod_cast (PairFourEndpoints.three_zero_iff (b:ℤ) (c:ℤ) (by omega) (by omega)).mp hz
  have hr2 : PairFourEndpoints.P2 (b:ℝ) (c:ℝ)≠0 := by
    unfold PairFourEndpoints.P2 at *
    exact_mod_cast hi2
  have hr3 : PairFourEndpoints.P3 (b:ℝ) (c:ℝ)≠0 := by
    unfold PairFourEndpoints.P3 at *
    exact_mod_cast hi3
  have he2 : e≠2 := eigenvalue_ne_of_det_ne _ e 2 h hh hE (by
    rwa [PairFourEndpoints.determinant_two])
  have he3 : e≠3 := eigenvalue_ne_of_det_ne _ e 3 h hh hE (by
    rwa [PairFourEndpoints.determinant_three])
  let V : ℕ := (4+1)^2*(b+1)*(c+1)-2
  let ell : ℝ := (V:ℝ)+1-e
  have hactual : HasActualEigenvalue (modulus p (pairExponents 4 b c)) ell :=
    actual_paired_eigenvalue p hp hinj 4 b c (by norm_num) (by omega) (by omega) e h hh hE
  refine ⟨ell,hactual,?_,?_,?_,?_⟩
  · change (V:ℝ)-3<ell
    dsimp only [ell]
    linarith
  · change ell<(V:ℝ)
    dsimp only [ell]
    linarith
  · change ell≠(V:ℝ)-1
    intro heq
    apply he2
    dsimp [ell] at heq
    linarith
  · change ell≠(V:ℝ)-2
    intro heq
    apply he3
    dsimp [ell] at heq
    linarith

theorem exception_eigenpair (b c : ℕ)
    (hex : (b=2 ∧ c=6) ∨ (b=6 ∧ c=2)) :
    ∃ e : ℝ, 7 < e ∧ e < 8 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h ≠ 0 ∧ tensorK 4 (b:ℝ) (c:ℝ)*ᵥh=e • h := by
  let f : ℝ → ℝ := fun x => x^3-161*x^2+5775*x-35343
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hl : f 7<0 := by norm_num [f]
  have hu : 0<f 8 := by norm_num [f]
  obtain ⟨e,he,hfe⟩ := intermediate_value_Icc (by norm_num : (7:ℝ)≤8) hf.continuousOn
    (show (0:ℝ)∈Set.Icc (f 7) (f 8) from ⟨hl.le,hu.le⟩)
  have hel : 7<e := by
    have hn : 7≠e := by intro hh; rw [←hh] at hfe; linarith
    exact lt_of_le_of_ne he.1 hn
  have heu : e<8 := by
    have hn : e≠8 := by intro hh; rw [hh] at hfe; linarith
    exact lt_of_le_of_ne he.2 hn
  have hd : (tensorK 4 (b:ℝ) (c:ℝ)-e • 1).det=0 := by
    have hid : (tensorK 4 (b:ℝ) (c:ℝ)-e • 1).det=(e-3)*f e := by
      rcases hex with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        rw [det_tensorK_sub_scalar] <;> dsimp [f] <;> norm_num <;> ring
    rw [hid,hfe,mul_zero]
  obtain ⟨h,hh,heh⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hE : tensorK 4 (b:ℝ) (c:ℝ)*ᵥh=e • h := by
    rw [sub_mulVec,smul_mulVec,one_mulVec] at heh
    exact sub_eq_zero.mp heh
  exact ⟨e,hel,heu,h,hh,hE⟩

/-- Every positive pair of tails admits an actual noninteger tensor eigenvalue.
The ordinary window excludes two and three; the exceptional pair uses (7,8). -/
theorem noninteger_eigenpair (b c : ℕ) (hb : 2≤b) (hc : 2≤c) :
    ∃ e : ℝ, (¬∃ z : ℤ, e=z) ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h ≠ 0 ∧ tensorK 4 (b:ℝ) (c:ℝ)*ᵥh=e • h := by
  by_cases hex : (b=2 ∧ c=6) ∨ (b=6 ∧ c=2)
  · obtain ⟨e,hel,heu,h,hh,hE⟩ := exception_eigenpair b c hex
    refine ⟨e,?_,h,hh,hE⟩
    rintro ⟨z,hz⟩
    have hzl : (7:ℤ)<z := by exact_mod_cast (hz ▸ hel)
    have hzu : z<(8:ℤ) := by exact_mod_cast (hz ▸ heu)
    omega
  have h2i := PairFourEndpoints.two_nonzero (b:ℤ) (c:ℤ) (by omega) (by omega)
  have h3i : PairFourEndpoints.P3 (b:ℤ) (c:ℤ)≠0 := by
    intro hz
    apply hex
    exact_mod_cast (PairFourEndpoints.three_zero_iff (b:ℤ) (c:ℤ) (by omega) (by omega)).mp hz
  have h2 : PairFourEndpoints.P2 (b:ℝ) (c:ℝ)≠0 := by
    unfold PairFourEndpoints.P2 at *
    exact_mod_cast h2i
  have h3 : PairFourEndpoints.P3 (b:ℝ) (c:ℝ)≠0 := by
    unfold PairFourEndpoints.P3 at *
    exact_mod_cast h3i
  obtain ⟨e,hel,heu,v,hv,hS⟩ := low_eigenpair (b:ℝ) (c:ℝ)
    (by exact_mod_cast hb) (by exact_mod_cast hc)
  obtain ⟨h,hh,hE⟩ := tensor_eigenpair_of_symmetric 4 (b:ℝ) (c:ℝ)
    (by positivity) (by positivity) e v hv hS
  have he2 : e≠2 := eigenvalue_ne_of_det_ne _ e 2 h hh hE (by
    rwa [PairFourEndpoints.determinant_two])
  have he3 : e≠3 := eigenvalue_ne_of_det_ne _ e 3 h hh hE (by
    rwa [PairFourEndpoints.determinant_three])
  refine ⟨e,?_,h,hh,hE⟩
  rintro ⟨z,hz⟩
  have hzl : (1:ℤ)<z := by exact_mod_cast (hz ▸ hel)
  have hzu : z<(4:ℤ) := by exact_mod_cast (hz ▸ heu)
  have hz23 : z=2 ∨ z=3 := by omega
  rcases hz23 with rfl | rfl
  · apply he2; simpa using hz
  · apply he3; simpa using hz

/-- Every (4,4,b,c), with positive natural tails and distinct primes,
is nonintegral on the actual graph. Unit tails use the existing unit theorem. -/
theorem actual_nonintegral (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 0<b) (hc : 0<c) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents 4 b c)) := by
  have hk (i : Fin 4) : 0<pairExponents 4 b c i := by
    fin_cases i <;> simp [pairExponents] <;> assumption
  by_cases hb1 : b=1
  · exact (unit_exponent_obstruction p hp hinj _ hk (by norm_num) 2
      (by simp [pairExponents,hb1])).choose_spec.2.2.2
  by_cases hc1 : c=1
  · exact (unit_exponent_obstruction p hp hinj _ hk (by norm_num) 3
      (by simp [pairExponents,hc1])).choose_spec.2.2.2
  obtain ⟨e,hne,h,hh,hE⟩ := noninteger_eigenpair b c (by omega) (by omega)
  have hactual := actual_paired_eigenvalue p hp hinj 4 b c (by norm_num) hb hc e h hh hE
  intro H
  obtain ⟨z,hz⟩ := H _ hactual
  apply hne
  refine ⟨((((4+1)^2*(b+1)*(c+1))-2 : ℕ):ℤ)+1-z,?_⟩
  push_cast
  norm_num only [Nat.reduceAdd,Nat.reducePow] at hz
  linarith

/-- Coordinate permutations retain the original distinct-prime domain. -/
theorem four_equal_obstruction (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (σ : Equiv.Perm (Fin 4))
    (b c : ℕ) (hb : 0<b) (hc : 0<c) :
    ¬ActualLaplacianIntegral (modulus p (fun i => pairExponents 4 b c (σ i))) := by
  let q := fun i => p (σ.symm i)
  have hqp (i : Fin 4) : Nat.Prime (q i) := hp (σ.symm i)
  have hqi : Function.Injective q := hinj.comp σ.symm.injective
  have hm : modulus q (pairExponents 4 b c)=
      modulus p (fun i => pairExponents 4 b c (σ i)) := by
    unfold modulus
    simpa [q] using (Equiv.prod_comp σ (fun i => p (σ.symm i)^pairExponents 4 b c i)).symm
  rw [←hm]
  exact actual_nonintegral q hqp hqi b c hb hc

end D5.S3.Combinatorics.SpectralGraph.PairFourSpectrum
