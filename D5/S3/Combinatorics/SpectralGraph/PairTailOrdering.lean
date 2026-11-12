/- GID: D5/S3/Combinatorics/SpectralGraph/PairTailOrdering
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairTailOrdering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered second-smallest eigenvalue windows of the entire paired tensor. -/
import D5.S3.Combinatorics.SpectralGraph.PairTailSpectrum
import D5.S3.Combinatorics.SpectralGraph.RepeatedPairBinaryPolynomial

/-! Source: full four-prime large-tail and harmonic-tail manuscripts, PR9
6d491f77b35dec808fc777b69939c56cdae5dc02. The ordered eigenvalues here
belong to the full four-dimensional symmetric representative, similar to
its weighted tensor. Determinant signs alone are supplemented by the trace
and second elementary coefficient to exclude three roots below the lower
endpoint. No unordered eigenpair is identified as second by assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Polynomial Finset
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.PairTailOrdering
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants

private theorem lower_four (r : Fin 4 → ℝ) (ho : Antitone r)
    (hp : r 0*r 1*r 2*r 3<0)
    (ht : 0<r 0+r 1+r 2+r 3)
    (he : 0≤r 0*r 1+r 0*r 2+r 0*r 3+r 1*r 2+r 1*r 3+r 2*r 3) :
    0<r 2 ∧ r 3<0 := by
  have h01 : r 1≤r 0 := ho (by decide)
  have h12 : r 2≤r 1 := ho (by decide)
  have h23 : r 3≤r 2 := ho (by decide)
  have h3 : r 3<0 := by
    by_contra hn
    have h3n : 0≤r 3 := le_of_not_gt hn
    have h0n : 0≤r 0 := le_trans h3n (le_trans h23 (le_trans h12 h01))
    have h1n : 0≤r 1 := le_trans h3n (le_trans h23 h12)
    have h2n : 0≤r 2 := le_trans h3n h23
    exact (not_le_of_gt hp) (mul_nonneg (mul_nonneg (mul_nonneg h0n h1n) h2n) h3n)
  refine ⟨?_,h3⟩
  by_contra hn
  have h2n : r 2≤0 := le_of_not_gt hn
  have h2 : r 2<0 := lt_of_le_of_ne h2n (by
    intro hz
    rw [hz,mul_zero,zero_mul] at hp
    exact lt_irrefl _ hp)
  have hprod : (r 0*r 1)*(r 2*r 3)<0 := by nlinarith only [hp]
  have htop : r 0*r 1<0 := by
    by_contra hn
    have hh := mul_nonneg (le_of_not_gt hn) (mul_pos_of_neg_of_neg h2 h3).le
    exact (not_le_of_gt hprod) hh
  rcases mul_neg_iff.mp htop with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · have hs : r 1+r 2+r 3<0 := by linarith
    have hm := mul_neg_of_pos_of_neg ht hs
    have hq12 : 0≤r 1*r 2 := mul_nonneg_of_nonpos_of_nonpos h1.le h2.le
    have hq13 : 0≤r 1*r 3 := mul_nonneg_of_nonpos_of_nonpos h1.le h3.le
    have hq23 : 0≤r 2*r 3 := mul_nonneg_of_nonpos_of_nonpos h2.le h3.le
    nlinarith [sq_nonneg (r 1),sq_nonneg (r 2),sq_nonneg (r 3)]
  · linarith

private theorem upper_four (r : Fin 4 → ℝ) (ho : Antitone r)
    (u : ℝ) (h3 : r 3<u)
    (hp : 0<(r 0-u)*(r 1-u)*(r 2-u)*(r 3-u)) : r 2<u := by
  by_contra hn
  have h2 : 0≤r 2-u := by linarith
  have h1 : 0≤r 1-u := by have h:=ho (show (1:Fin 4)≤2 by decide); linarith
  have h0 : 0≤r 0-u := by have h:=ho (show (0:Fin 4)≤2 by decide); linarith
  have h3n : r 3-u≤0 := by linarith
  exact (not_le_of_gt hp) (mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg h0 h1) h2) h3n)

/-- The complete four-dimensional symmetric representative. -/
def symmetricFour (a b c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (symmetricK a b c)

private theorem hermitian_four (a b c : ℝ) : (symmetricFour a b c).IsHermitian :=
  (symmetric_hermitian a b c).submatrix finProdFinEquiv.symm

/-- All four eigenvalues, in decreasing order and with multiplicity. -/
def values (a b c : ℝ) : Fin 4 → ℝ := (hermitian_four a b c).eigenvalues₀

theorem values_antitone (a b c : ℝ) : Antitone (values a b c) :=
  (hermitian_four a b c).eigenvalues₀_antitone

/-- This is the characteristic polynomial of the entire tensor. -/
theorem polynomial (a b c : ℝ) (hb : 0<b) (hc : 0<c) :
    (tensorK a b c).charpoly=∏ i : Fin 4, (X-C (values a b c i)) := by
  have hs := tensor_symmetric_charpoly a b c 0 hb hc
  simp only [zero_smul,sub_zero] at hs
  rw [←hs, ←Matrix.charpoly_reindex finProdFinEquiv]
  change (symmetricFour a b c).charpoly=_
  rw [(hermitian_four a b c).charpoly_eq]
  let σ : Fin (Fintype.card (Fin 4)) ≃ Fin 4 :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  change (∏ i : Fin 4, (X-C ((hermitian_four a b c).eigenvalues₀ (σ.symm i))))=
    ∏ i : Fin (Fintype.card (Fin 4)), (X-C ((hermitian_four a b c).eigenvalues₀ i))
  exact Equiv.prod_comp σ.symm
    (fun i : Fin (Fintype.card (Fin 4)) =>
      (X-C ((hermitian_four a b c).eigenvalues₀ i) : ℝ[X]))

/-- Every sorted value has a nonzero full-operator eigenvector. -/
theorem eigenpair (a b c : ℝ) (hb : 0<b) (hc : 0<c) (i : Fin 4) :
    ∃ v : Fin 2 × Fin 2 → ℝ, v≠0 ∧
      tensorK a b c*ᵥv=values a b c i • v := by
  have hz : (tensorK a b c).charpoly.eval (values a b c i)=0 := by
    rw [polynomial a b c hb hc,Polynomial.eval_prod]
    apply Finset.prod_eq_zero (mem_univ i)
    simp
  rw [Matrix.eval_charpoly] at hz
  have hd : (tensorK a b c-values a b c i • 1).det=0 := by
    have hm : Matrix.scalar (Fin 2 × Fin 2) (values a b c i)-tensorK a b c=
        -(tensorK a b c-values a b c i • 1) := by
      ext q t
      by_cases h : q=t <;> simp [Matrix.scalar,h]
    rw [hm,Matrix.det_neg] at hz
    simpa using hz
  obtain ⟨v,hv,hE⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr hd
  rw [sub_mulVec,smul_mulVec,one_mulVec] at hE
  exact ⟨v,hv,sub_eq_zero.mp hE⟩

/-- Full shifted determinant, retaining the complete ordered spectrum. -/
theorem determinant (a b c x : ℝ) (hb : 0<b) (hc : 0<c) :
    (tensorK a b c-x • 1).det=
      (values a b c 0-x)*(values a b c 1-x)*
      (values a b c 2-x)*(values a b c 3-x) := by
  have hz:=congrArg (fun f : ℝ[X] => f.eval x) (polynomial a b c hb hc)
  rw [Matrix.eval_charpoly] at hz
  have hm : Matrix.scalar (Fin 2 × Fin 2) x-tensorK a b c=
      -(tensorK a b c-x • 1) := by
    ext q t
    by_cases h : q=t <;> simp [Matrix.scalar,h]
  rw [hm,Matrix.det_neg] at hz
  norm_num [Fin.prod_univ_succ] at hz
  nlinarith only [hz]

private def trace_shift (a b c l : ℝ) : ℝ := (a+1)*(b+2)*(c+2)+a-4*l

private def pair_shift (a b c l : ℝ) : ℝ :=
  let d0:=(a+1)*(b+1)*(c+1)+a-l
  let d1:=(a+1)*(b+1)-l
  let d2:=(a+1)*(c+1)-l
  let d3:=a+1-l
  d0*d1+d0*d2+d0*d3+d1*d2+d1*d3+d2*d3-a^2*(b+c+2*b*c)

private theorem trace_identity (a b c l : ℝ) (hb : 0<b) (hc : 0<c) :
    (values a b c 0-l)+(values a b c 1-l)+
      (values a b c 2-l)+(values a b c 3-l)=trace_shift a b c l := by
  have h2:=determinant a b c (l+2) hb hc
  have hm2:=determinant a b c (l-2) hb hc
  have h1:=determinant a b c (l+1) hb hc
  have hm1:=determinant a b c (l-1) hb hc
  rw [det_tensorK_sub_scalar] at h2 hm2 h1 hm1
  dsimp [trace_shift]
  linear_combination (1/12)*h2-(1/12)*hm2-(1/6)*h1+(1/6)*hm1

private theorem pair_identity (a b c l : ℝ) (hb : 0<b) (hc : 0<c) :
    (values a b c 0-l)*(values a b c 1-l)+
      (values a b c 0-l)*(values a b c 2-l)+
      (values a b c 0-l)*(values a b c 3-l)+
      (values a b c 1-l)*(values a b c 2-l)+
      (values a b c 1-l)*(values a b c 3-l)+
      (values a b c 2-l)*(values a b c 3-l)=pair_shift a b c l := by
  have h0:=determinant a b c l hb hc
  have h1:=determinant a b c (l+1) hb hc
  have hm1:=determinant a b c (l-1) hb hc
  rw [det_tensorK_sub_scalar] at h0 h1 hm1
  dsimp [pair_shift]
  linear_combination h0-(1/2)*h1-(1/2)*hm1

private theorem window (a b c l u : ℝ) (hb : 0<b) (hc : 0<c)
    (hlu : l<u) (ht : 0<trace_shift a b c l) (he : 0≤pair_shift a b c l)
    (hl : (tensorK a b c-l • 1).det<0)
    (hu : 0<(tensorK a b c-u • 1).det) :
    l<values a b c 2 ∧ values a b c 2<u := by
  let r : Fin 4 → ℝ := fun i => values a b c i-l
  have ho : Antitone r := fun i j hij => sub_le_sub_right (values_antitone a b c hij) l
  have hpr : r 0*r 1*r 2*r 3<0 := by
    simpa only [r,determinant a b c l hb hc] using hl
  have htr : 0<r 0+r 1+r 2+r 3 := by
    dsimp [r]
    rw [trace_identity a b c l hb hc]
    exact ht
  have her : 0≤r 0*r 1+r 0*r 2+r 0*r 3+r 1*r 2+r 1*r 3+r 2*r 3 := by
    dsimp [r]
    rw [pair_identity a b c l hb hc]
    exact he
  obtain ⟨h2,h3⟩:=lower_four r ho hpr htr her
  have h3u : values a b c 3<u := by dsimp [r] at h3; linarith
  refine ⟨by dsimp [r] at h2; linarith,?_⟩
  apply upper_four (values a b c) (values_antitone a b c) u h3u
  rwa [←determinant a b c u hb hc]

/-- The second-smallest eigenvalue of the full four-dimensional operator
is in the original strict bounded-tail window. -/
theorem bounded_window (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 1≤c) :
    a+1<values a b c 2 ∧ values a b c 2<(a+1)*(b+1) := by
  have hc0 : 0<c := by linarith
  apply window a b c _ _ hb hc0 (by nlinarith)
  · have hi : trace_shift a b c (a+1)=
        (a+1)*b*c+2*(a+1)*b+2*(a+1)*c+a := by dsimp [trace_shift]; ring
    rw [hi]
    positivity
  · have hi : pair_shift a b c (a+1)=a^2*b^2*c + a^2*b^2 + a^2*b*c^2 + a^2*b*c + a^2*c^2 + 2*a*b^2*c + 2*a*b^2 + 2*a*b*c^2 + 6*a*b*c + a*b + 2*a*c^2 + a*c + b^2*c + b^2 + b*c^2 + 3*b*c + c^2 := by dsimp [pair_shift]; ring
    rw [hi]
    positivity
  · have hi : (tensorK a b c-(a+1) • 1).det= -a^2*b^2*c^2*(2*a+1) := by
      rw [det_tensorK_sub_scalar]
      ring
    rw [hi]
    have hp : 0<a^2*b^2*c^2*(2*a+1) := by positivity
    linarith
  · exact PairTailSpectrum.upper_endpoint a b c ha hb hc

/-- On the entire original unequal positive-integer-sized domain, the
second-smallest eigenvalue is in the strict harmonic window. -/
theorem harmonic_window (a b c : ℝ) (ha : 1≤a) (hb : 1≤b) (hbc : b<c) :
    a+b+1<values a b c 2 ∧ values a b c 2<a+1+2*b*c/(b+c) ∧
      values a b c 2<a+2*b+1 := by
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := by linarith
  have hc0 : 0<c := by linarith
  have hs : 0<b+c := by linarith
  have hlu : a+b+1<a+1+2*b*c/(b+c) := by
    have hi : b<2*b*c/(b+c) := (lt_div_iff₀ hs).mpr (by nlinarith)
    linarith
  let A:=a-1
  let B:=b-1
  let D:=c-b
  have hA : 0≤A := by dsimp [A]; linarith
  have hB : 0≤B := by dsimp [B]; linarith
  have hD : 0≤D := by dsimp [D]; linarith
  have ht : 0<trace_shift a b c (a+b+1) := by
    have hi : trace_shift a b c (a+b+1)=A*B^2 + A*B*D + 6*A*B + 3*A*D + 6*A + 2*B^2 + 2*B*D + 8*B + 6*D + 7 := by
      dsimp [trace_shift,A,B,D]
      ring
    rw [hi]
    positivity
  have he : 0≤pair_shift a b c (a+b+1) := by
    have hi : pair_shift a b c (a+b+1)=2*A^2*B^3 + 3*A^2*B^2*D + 9*A^2*B^2 + A^2*B*D^2 + 9*A^2*B*D + 12*A^2*B + 2*A^2*D^2 + 6*A^2*D + 5*A^2 + 5*A*B^3 + 9*A*B^2*D + 19*A*B^2 + 4*A*B*D^2 + 28*A*B*D + 22*A*B + 8*A*D^2 + 20*A*D + 8*A + 2*B^3 + 6*B^2*D + 6*B^2 + 4*B*D^2 + 18*B*D + 5*B + 8*D^2 + 13*D + 1 := by
      dsimp [pair_shift,A,B,D]
      ring
    rw [hi]
    positivity
  obtain ⟨hl,hu⟩:=window a b c _ _ hb0 hc0 hlu ht he
    (PairGapSigns.unequal_lower_negative a b c ha0 hb hbc)
    (PairTailSpectrum.harmonic_endpoint a b c ha0 hb0 hbc)
  have hi : 2*b*c/(b+c)<2*b := (div_lt_iff₀ hs).mpr (by nlinarith)
  exact ⟨hl,hu,by linarith⟩

/-- The ordered second value is an actual ideal-intersection graph
Laplacian eigenvalue after the original paired lift, for every distinct
prime assignment and every positive natural parameter. -/
theorem actual_ordered_value (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    IdealIntersectionObstructions.HasActualEigenvalue
      (IdealIntersectionSupport.modulus p (PairedIdealIntersectionLift.pairExponents a b c))
      ((((a+1)^2*(b+1)*(c+1)-2 : ℕ) : ℝ)+1-values (a:ℝ) (b:ℝ) (c:ℝ) 2) := by
  obtain ⟨v,hv,hE⟩:=eigenpair (a:ℝ) (b:ℝ) (c:ℝ) (by positivity) (by positivity) 2
  exact PairedIdealIntersectionLift.actual_paired_eigenvalue p hp hinj a b c ha hb hc _ v hv hE

end D5.S3.Combinatorics.SpectralGraph.PairTailOrdering
