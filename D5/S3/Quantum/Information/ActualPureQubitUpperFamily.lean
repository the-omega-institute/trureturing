/- GID: D5/S3/Quantum/Information/ActualPureQubitUpperFamily
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualPureQubitUpperFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: Normalized effect families yield actual pure-qubit programs with a matching cost limit. -/

import D5.S3.Quantum.Information.ActualPureQubitGeometry
open scoped InnerProductSpace ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.ActualPureQubitCostInfimum

theorem actual_effect_family : ∀ {ι : Type} [Fintype ι]
      (p d : ι → ℝ) (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j=1) (hd0 : ∑ j, d j=0) (hd : ∑ j, d j^2/p j=1)
      (B : ℝ) (hB : 0 < B),
      let α := -2*∑ j, d j^3/(p j)^2
      ∃ w t : ℝ → ℝ, w 0=1 ∧ t 0=0 ∧
        Tendsto (fun R => (extendedCost B α w ((t R)^2)-B)/R^2) (𝓝[>] 0)
          (𝓝 (B^2/4*(∑ j, d j^4/(p j)^3-1-(∑ j, d j^3/(p j)^2)^2))) ∧
        (∀ᶠ R in 𝓝[>] 0,
          0<R ∧ 0<t R ∧ t R<1 ∧ 0<w ((t R)^2) ∧
          (∑ j, root (p j) (d j) α ((t R)^2) (w ((t R)^2))=1) ∧
          (∀ j, (effect (p j) (d j) α ((t R)^2) (w ((t R)^2))).PosSemidef) ∧
          (∑ j, effect (p j) (d j) α ((t R)^2) (w ((t R)^2))=1) ∧
          radiusMap B α w (t R)=R ∧
          (∀ j, 0<p j-α*(t R)^2*w ((t R)^2)*d j ∧
            0<(p j-α*(t R)^2*w ((t R)^2)*d j)^2-
              4*(t R)^2*(1-(t R)^2)*(w ((t R)^2))^2*d j^2) ∧
          (∀ j, R*(1+t R)*|Real.sqrt B*d j| < p j)) := by
  classical
  have normalized_effect_family : ∀ {ι : Type} [Fintype ι]
      (p d : ι → ℝ) (α : ℝ) (hp : ∀ j, 0 < p j)
      (hp1 : ∑ j, p j = 1) (hd0 : ∑ j, d j = 0) (hd : ∑ j, d j^2/p j = 1),
      ∃ w : ℝ → ℝ, w 0 = 1 ∧
        HasStrictDerivAt w ((1 - ∑ j, d j^4/(p j)^3 - α*∑ j, d j^3/(p j)^2)/2) 0 ∧
        (∀ᶠ e in 𝓝 0, 0 < w e ∧ (∑ j, root (p j) (d j) α e (w e) = 1) ∧
          (∀ j, (effect (p j) (d j) α e (w e)).PosSemidef) ∧
          (∑ j, effect (p j) (d j) α e (w e) = 1)) := by
    classical
    have blochMatrix_properties (a : ℝ) (r : (EuclideanSpace ℝ (Fin 3))) :
        (blochMatrix a r).IsHermitian ∧
        Matrix.trace (blochMatrix a r) = (a : ℂ) ∧
        bloch (blochMatrix a r) = r ∧
        (Matrix.det (blochMatrix a r)).re = (a^2 - ‖r‖^2) / 4 ∧
        ((blochMatrix a r).PosSemidef ↔ ‖r‖ ≤ a) := by
      have hh : (blochMatrix a r).IsHermitian := by
        apply Matrix.IsHermitian.ext
        intro i j
        fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochMatrix]
      have ht : Matrix.trace (blochMatrix a r) = (a : ℂ) := by
        apply Complex.ext <;> simp [blochMatrix, Matrix.trace, Fin.sum_univ_two] <;> ring
      have hb : bloch (blochMatrix a r) = r := by
        ext i
        fin_cases i <;> simp [bloch, blochMatrix] <;> ring
      have hd : (Matrix.det (blochMatrix a r)).re = (a^2 - ‖r‖^2)/4 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [blochMatrix, Matrix.det_fin_two, Fin.sum_univ_three]
        ring
      refine ⟨hh, ht, hb, hd, ?_⟩
      constructor
      · intro hp
        have htpos := (Complex.nonneg_iff.mp hp.trace_nonneg).1
        have hdpos := (Complex.nonneg_iff.mp hp.det_nonneg).1
        rw [ht] at htpos
        rw [hd] at hdpos
        simp only [Complex.ofReal_re] at htpos
        nlinarith [norm_nonneg r]
      · intro hbound
        apply hh.posSemidef_iff_eigenvalues_nonneg.mpr
        have hs := congrArg Complex.re hh.trace_eq_sum_eigenvalues
        rw [ht] at hs
        simp only [Fin.sum_univ_two, Complex.add_re, Complex.ofReal_re] at hs
        have hp := congrArg Complex.re hh.det_eq_prod_eigenvalues
        rw [hd] at hp
        simp only [Fin.prod_univ_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero] at hp
        change a = hh.eigenvalues 0 + hh.eigenvalues 1 at hs
        change (a^2 - ‖r‖^2) / 4 = hh.eigenvalues 0 * hh.eigenvalues 1 - 0*0 at hp
        simp only [mul_zero, sub_zero] at hp
        have htr : 0 ≤ a := (norm_nonneg r).trans hbound
        have hdet : 0 ≤ hh.eigenvalues 0 * hh.eigenvalues 1 := by nlinarith [norm_nonneg r]
        intro i
        fin_cases i
        · by_contra h
          have hi : hh.eigenvalues 0 < 0 := lt_of_not_ge h
          have hj : 0 < hh.eigenvalues 1 := by linarith
          exact (not_lt_of_ge hdet) (mul_neg_of_neg_of_pos hi hj)
        · by_contra h
          have hi : hh.eigenvalues 1 < 0 := lt_of_not_ge h
          have hj : 0 < hh.eigenvalues 0 := by linarith
          exact (not_lt_of_ge hdet) (mul_neg_of_pos_of_neg hj hi)

    have normalized_branch {ι : Type} [Fintype ι]
        (p d : ι → ℝ) (α : ℝ) (hp : ∀ j, 0 < p j)
        (hd : ∑ j, d j ^ 2 / p j = 1) :
        ∃ w : ℝ → ℝ, w 0 = 1 ∧ DifferentiableAt ℝ w 0 ∧
          HasStrictDerivAt w (deriv w 0) 0 ∧
          (∀ᶠ e in 𝓝 0, 0 < w e ∧ ∑ j, root (p j) (d j) α e (w e) = 1) := by
      let F : ℝ × ℝ → ℝ := fun x => ∑ j, root (p j) (d j) α x.1 x.2
      have hroot (j : ι) : ContDiffAt ℝ 1
          (fun x : ℝ × ℝ => root (p j) (d j) α x.1 x.2) (0,1) := by
        unfold root
        apply ContDiffAt.div
        · fun_prop
        · apply ContDiffAt.add
          · fun_prop
          · apply ContDiffAt.sqrt
            · fun_prop
            · simpa using pow_ne_zero 2 (hp j).ne'
        · simpa [Real.sqrt_sq (hp j).le] using (by linarith [hp j] : p j + p j ≠ 0)
      have hF : ContDiffAt ℝ 1 F (0,1) := by
        exact ContDiffAt.sum fun j _ => hroot j
      have hstrict := hF.hasStrictFDerivAt (by norm_num)
      have hzero (w : ℝ) : F (0,w) = w^2 := by
        dsimp [F, root]
        simp only [mul_zero, zero_mul, sub_zero, one_mul, mul_one, Real.sqrt_sq (hp _).le]
        calc
          (∑ j, 2*w^2*d j^2 / (p j+p j)) = ∑ j, w^2 * (d j^2/p j) := by
            apply Finset.sum_congr rfl
            intro j _
            field_simp
            <;> ring
          _ = w^2 := by rw [← Finset.mul_sum, hd, mul_one]
      have hder : fderiv ℝ F (0,1) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
          (2:ℝ) • ContinuousLinearMap.id ℝ ℝ := by
        have h := hstrict.hasFDerivAt.comp (1:ℝ)
          ((hasFDerivAt_const (0:ℝ) (1:ℝ)).prodMk (hasFDerivAt_id (1:ℝ)))
        have h' : HasFDerivAt (fun w : ℝ => F (0,w))
            ((2:ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 := by
          simp only [hzero]
          simpa using ((hasFDerivAt_id (𝕜 := ℝ) (1:ℝ)).pow 2)
        convert h.unique h' using 1
        ext x
        rfl
      have hinv : (fderiv ℝ F (0,1) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
        rw [hder]
        apply ContinuousLinearMap.IsInvertible.of_inverse (g := (1/2:ℝ) • ContinuousLinearMap.id ℝ ℝ)
        · ext x; simp
        · ext x; simp
      let w := hstrict.implicitFunctionOfProdDomain hinv
      have hw0 : w 0 = 1 :=
        (hstrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
      have hwd : DifferentiableAt ℝ w 0 :=
        (hstrict.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.differentiableAt
      have hws := (hstrict.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasStrictDerivAt
      change HasStrictDerivAt w _ 0 at hws
      have hws' : HasStrictDerivAt w (deriv w 0) 0 := by
        simpa only [hws.hasDerivAt.deriv] using hws
      refine ⟨w, hw0, hwd, hws', ?_⟩
      filter_upwards [hstrict.eventually_apply_implicitFunctionOfProdDomain hinv,
        hwd.continuousAt.eventually (lt_mem_nhds (show 0 < w 0 by rw [hw0]; norm_num))] with e he hpw
      exact ⟨hpw, he.trans (by simpa using hzero 1)⟩

    have root_deriv (p d α : ℝ) (hp : 0 < p) (w : ℝ → ℝ) (k : ℝ)
        (hw : w 0 = 1) (hk : HasDerivAt w k 0) :
        HasDerivAt (fun e => root p d α e (w e))
          ((-1+2*k)*d^2/p + α*d^3/p^2 + d^4/p^3) 0 := by
      have he := hasDerivAt_id (0:ℝ)
      have hA : HasDerivAt (fun e : ℝ => p-α*e*w e*d) (-α*d) 0 := by
        convert (hasDerivAt_const (0:ℝ) p).sub (((he.const_mul α).mul hk).mul_const d) using 1 <;> first | rfl | (simp [hw] <;> ring) | (funext e; simp; ring)
      have hD : HasDerivAt (fun e : ℝ => (p-α*e*w e*d)^2-4*e*(1-e)*(w e)^2*d^2)
          (-2*p*α*d-4*d^2) 0 := by
        convert (hA.pow 2).sub (((((he.const_mul 4).mul
          ((hasDerivAt_const (0:ℝ) 1).sub he)).mul (hk.pow 2)).mul_const (d^2))) using 1 <;> first | rfl | (simp [hw] <;> ring) | (funext e; simp; ring) <;> ring
      have hS := hD.sqrt (by simpa using pow_ne_zero 2 hp.ne')
      have hN := ((((hasDerivAt_const (0:ℝ) 1).sub he).const_mul 2).mul (hk.pow 2)).mul_const (d^2)
      have h := hN.div (hA.add hS) (by simpa [Real.sqrt_sq hp.le] using (by linarith : p+p ≠ 0))
      change HasDerivAt (fun e => root p d α e (w e)) _ 0 at h
      convert h using 1
      try dsimp
      simp only [hw, mul_zero, zero_mul, sub_zero, one_pow, mul_one, one_mul,
        Real.sqrt_sq hp.le]
      field_simp
      <;> ring

    have branch_with_derivative {ι : Type} [Fintype ι]
        (p d : ι → ℝ) (α : ℝ) (hp : ∀ j, 0 < p j)
        (hd : ∑ j, d j ^ 2 / p j = 1) :
        ∃ w : ℝ → ℝ, w 0 = 1 ∧
          HasStrictDerivAt w ((1 - ∑ j, d j^4/(p j)^3 - α*∑ j, d j^3/(p j)^2)/2) 0 ∧
          (∀ᶠ e in 𝓝 0, 0 < w e ∧ ∑ j, root (p j) (d j) α e (w e) = 1) := by
      obtain ⟨w, hw, hwd, hws, hnorm⟩ := normalized_branch p d α hp hd
      have hq := HasDerivAt.fun_sum (u := Finset.univ)
        (fun j _ => root_deriv (p j) (d j) α (hp j) w (deriv w 0) hw hwd.hasDerivAt)
      have hconst : HasDerivAt (fun e => ∑ j, root (p j) (d j) α e (w e)) 0 0 := by
        apply (hasDerivAt_const (0:ℝ) (1:ℝ)).congr_of_eventuallyEq
        filter_upwards [hnorm] with e he
        exact he.2
      have heq := hq.unique hconst
      have hk : deriv w 0 = (1 - ∑ j, d j^4/(p j)^3 - α*∑ j, d j^3/(p j)^2)/2 := by
        simp only [Finset.sum_add_distrib, mul_div_assoc, ← Finset.mul_sum, hd] at heq
        linarith
      exact ⟨w, hw, hk ▸ hws, hnorm⟩

    have root_facts (p d α e w : ℝ) (he : e < 1)
        (hA : 0 < p-α*e*w*d)
        (hD : 0 < (p-α*e*w*d)^2-4*e*(1-e)*w^2*d^2) :
        0 < upperDiag p d α e w ∧ 0 ≤ root p d α e w ∧
        upperDiag p d α e w * root p d α e w = (w*d)^2 ∧
        (1-e)*upperDiag p d α e w + e*root p d α e w + α*e*w*d = p := by
      let A := p-α*e*w*d
      let S := Real.sqrt (A^2-4*e*(1-e)*w^2*d^2)
      have hS : 0 ≤ S := Real.sqrt_nonneg _
      have hSS : S^2=A^2-4*e*(1-e)*w^2*d^2 := Real.sq_sqrt hD.le
      have hden : A+S ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hA hS)
      have he' : 1-e ≠ 0 := ne_of_gt (sub_pos.mpr he)
      change 0 < (A+S)/(2*(1-e)) ∧ 0 ≤ 2*(1-e)*w^2*d^2/(A+S) ∧
        (A+S)/(2*(1-e))*(2*(1-e)*w^2*d^2/(A+S))=(w*d)^2 ∧
        (1-e)*((A+S)/(2*(1-e)))+e*(2*(1-e)*w^2*d^2/(A+S))+α*e*w*d=p
      refine ⟨div_pos (by linarith) (by linarith), div_nonneg (by positivity) (by linarith), ?_, ?_⟩
      · field_simp
        <;> ring
      · field_simp
        dsimp only [A] at hSS ⊢
        nlinarith only [hSS]

    have effects_are_povm {ι : Type} [Fintype ι]
        (p d : ι → ℝ) (α e w : ℝ)
        (hp : ∀ j, 0 < p j) (hp1 : ∑ j, p j = 1) (hd0 : ∑ j, d j = 0)
        (he : e < 1)
        (hA : ∀ j, 0 < p j-α*e*w*d j)
        (hD : ∀ j, 0 < (p j-α*e*w*d j)^2-4*e*(1-e)*w^2*d j^2)
        (hq : ∑ j, root (p j) (d j) α e w = 1) :
        (∀ j, (effect (p j) (d j) α e w).PosSemidef) ∧
        (∑ j, effect (p j) (d j) α e w = 1) := by
      have hf j := root_facts (p j) (d j) α e w he (hA j) (hD j)
      have ha : ∑ j, upperDiag (p j) (d j) α e w = 1 := by
        have h := congrArg (fun f : ι → ℝ => ∑ j, f j) (funext fun j => (hf j).2.2.2)
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hd0, hq, mul_zero, add_zero] at h
        nlinarith
      refine ⟨?_, ?_⟩
      · intro j
        let a := upperDiag (p j) (d j) α e w
        let q := root (p j) (d j) α e w
        let b := w*d j
        have heq : effect (p j) (d j) α e w = blochMatrix (a+q) (WithLp.toLp 2 ![2*b,0,a-q]) := by
          ext i k
          fin_cases i <;> fin_cases k <;> apply Complex.ext <;> simp [effect, blochMatrix, a,q,b] <;> ring
        rw [heq, (blochMatrix_properties _ _).2.2.2.2]
        have hn : ‖(WithLp.toLp 2 ![2*b,0,a-q] : (EuclideanSpace ℝ (Fin 3)))‖^2 = (a+q)^2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [Fin.sum_univ_three]
          have hmul : a*q=b^2 := (hf j).2.2.1
          nlinarith
        have hpos : 0 ≤ a+q := add_nonneg (hf j).1.le (hf j).2.1
        nlinarith [norm_nonneg (WithLp.toLp 2 ![2*b,0,a-q] : (EuclideanSpace ℝ (Fin 3)))]
      · ext i k
        fin_cases i <;> fin_cases k <;> simp [Matrix.sum_apply, effect, ← Complex.ofReal_sum, ha, hq,
          ← Finset.mul_sum, hd0]

    intro ι inst p d α hp hp1 hd0 hd
    obtain ⟨w, hw, hwd, hn⟩ := branch_with_derivative p d α hp hd
    have hcont : ContinuousAt w 0 := hwd.hasDerivAt.continuousAt
    have hcoeff : ∀ᶠ e in 𝓝 (0:ℝ), ∀ j,
        0<p j-α*e*w e*d j ∧
        0<(p j-α*e*w e*d j)^2-4*e*(1-e)*(w e)^2*d j^2 := by
      apply eventually_all.mpr
      intro j
      have hA : ContinuousAt (fun e : ℝ => p j-α*e*w e*d j) 0 := by fun_prop
      have hD : ContinuousAt (fun e : ℝ => (p j-α*e*w e*d j)^2-4*e*(1-e)*(w e)^2*d j^2) 0 := by fun_prop
      exact (hA.eventually (lt_mem_nhds (by simpa using hp j))).and
        (hD.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos (hp j))))
    refine ⟨w,hw,hwd,?_⟩
    filter_upwards [hn,hcoeff,gt_mem_nhds (by norm_num : (0:ℝ)<1)] with e hn he he1
    obtain ⟨hN,hN1⟩ := effects_are_povm p d α e (w e) hp hp1 hd0 he1
      (fun j => (he j).1) (fun j => (he j).2) hn.2
    exact ⟨hn.1,hn.2,hN,hN1⟩

  have radius_branch (B α : ℝ) (hB : 0 < B) (w : ℝ → ℝ) (k : ℝ)
      (hw : w 0 = 1) (hk : HasStrictDerivAt w k 0) :
      ∃ t : ℝ → ℝ, t 0 = 0 ∧ HasDerivAt t (Real.sqrt B/2) 0 ∧
        (∀ᶠ R in 𝓝 0, radiusMap B α w (t R) = R) := by
    have he := hasStrictDerivAt_id (0:ℝ)
    have hs := (((hasStrictDerivAt_const (0:ℝ) (1:ℝ)).sub (he.pow 2)).sqrt (by norm_num))
    have hkk : HasStrictDerivAt w k ((id ^ 2) (0:ℝ)) := by simpa using hk
    have hc := hkk.comp (0:ℝ) (he.pow 2)
    have hf : HasStrictDerivAt (radiusMap B α w) (2/Real.sqrt B) 0 := by
      have h := ((((he.const_mul 2).mul hs).sub ((he.pow 2).const_mul |α|)).mul hc).div
        (((hasStrictDerivAt_const (0:ℝ) (1:ℝ)).add he).mul_const (Real.sqrt B))
        (by simpa using (Real.sqrt_pos.mpr hB).ne')
      convert h using 1 <;> first | rfl | (simp [hw] <;> field_simp <;> ring)
    have hn : 2/Real.sqrt B ≠ 0 := div_ne_zero (by norm_num) (Real.sqrt_pos.mpr hB).ne'
    let t := hf.localInverse (radiusMap B α w) (2/Real.sqrt B) 0 hn
    have hzero : radiusMap B α w 0 = 0 := by simp [radiusMap]
    have ht0 : t 0 = 0 := by
      simpa only [hzero] using (hf.hasStrictFDerivAt_equiv hn).localInverse_apply_image
    have htd : HasDerivAt t (Real.sqrt B/2) 0 := by
      simpa only [hzero, inv_div] using (hf.to_localInverse hn).hasDerivAt
    exact ⟨t, ht0, htd, by simpa only [hzero] using hf.eventually_right_inverse hn⟩

  have cost_derivative (B α : ℝ) (w : ℝ → ℝ) (k : ℝ)
      (hw : w 0=1) (hk : HasDerivAt w k 0) :
      extendedCost B α w 0 = B ∧
      HasDerivAt (extendedCost B α w) (B*(-2*k+α^2/4)) 0 := by
    refine ⟨by simp [extendedCost,hw], ?_⟩
    have he := hasDerivAt_id (0:ℝ)
    have hone := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub he
    have hnum := ((hasDerivAt_const (0:ℝ) B).div (hk.pow 2) (by simp [hw])).mul (hone.const_mul 4)
    have hden := (hone.const_mul 4).sub (he.const_mul (α^2))
    have h := hnum.div hden (by norm_num)
    change HasDerivAt (extendedCost B α w) _ 0 at h
    convert h using 1 <;> first | rfl | (simp [hw] <;> ring)

  intro ι inst p d hp hp1 hd0 hd B hB
  dsimp only
  let α := -2*∑ j, d j^3/(p j)^2
  let k := (1-∑ j, d j^4/(p j)^3-α*∑ j, d j^3/(p j)^2)/2
  obtain ⟨w, hw, hkw, hn⟩ := normalized_effect_family p d α hp hp1 hd0 hd
  change HasStrictDerivAt w k 0 at hkw
  have hwcont := hkw.hasDerivAt.continuousAt
  obtain ⟨t, ht, htd, hrad⟩ := radius_branch B α hB w k hw hkw
  have htlim : Tendsto t (𝓝[>] 0) (𝓝 0) := by
    simpa [ht] using htd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have helim : Tendsto (fun R => (t R)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using htlim.pow 2
  have hwlim : Tendsto (fun R => w ((t R)^2)) (𝓝[>] 0) (𝓝 1) := by
    simpa [hw,Function.comp_def] using hkw.hasDerivAt.continuousAt.tendsto.comp helim
  have hratio : Tendsto (fun R => t R/R) (𝓝[>] 0) (𝓝 (Real.sqrt B/2)) := by
    simpa [ht, div_eq_mul_inv, mul_comm] using htd.tendsto_slope_zero_right
  have htp : ∀ᶠ R in 𝓝[>] 0, 0 < t R := by
    filter_upwards [hratio.eventually (lt_mem_nhds (by positivity : 0 < Real.sqrt B/2)),
      self_mem_nhdsWithin] with R hq hR
    exact (div_pos_iff_of_pos_right hR).mp hq
  have hepunct : Tendsto (fun R => (t R)^2) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨helim, ?_⟩
    filter_upwards [htp] with R hR
    exact pow_ne_zero 2 hR.ne'
  obtain ⟨hq0,hqd⟩ := cost_derivative B α w k hw hkw.hasDerivAt
  have hqs : Tendsto (fun R => (extendedCost B α w ((t R)^2)-B)/(t R)^2)
      (𝓝[>] 0) (𝓝 (B*(-2*k+α^2/4))) := by
    simpa [Function.comp_def, slope, hq0, div_eq_mul_inv, mul_comm] using hqd.tendsto_slope.comp hepunct
  have hlimit : Tendsto (fun R => (extendedCost B α w ((t R)^2)-B)/R^2)
      (𝓝[>] 0) (𝓝 (B^2/4*(∑ j, d j^4/(p j)^3-1-(∑ j, d j^3/(p j)^2)^2))) := by
    have h := hqs.mul (hratio.pow 2)
    have hv : B*(-2*k+α^2/4)*(Real.sqrt B/2)^2 =
        B^2/4*(∑ j, d j^4/(p j)^3-1-(∑ j, d j^3/(p j)^2)^2) := by
      rw [div_pow, Real.sq_sqrt hB.le]
      dsimp [α,k]
      ring
    rw [hv] at h
    apply h.congr'
    filter_upwards [htp, self_mem_nhdsWithin] with R htR hR
    try dsimp
    field_simp
  have hcoeff : ∀ᶠ e in 𝓝 (0:ℝ), ∀ j,
      0<p j-α*e*w e*d j ∧
      0<(p j-α*e*w e*d j)^2-4*e*(1-e)*(w e)^2*d j^2 := by
    apply (eventually_all).mpr
    intro j
    have hcA : ContinuousAt (fun e : ℝ => p j-α*e*w e*d j) 0 := by fun_prop
    have hcD : ContinuousAt (fun e : ℝ =>
        (p j-α*e*w e*d j)^2-4*e*(1-e)*(w e)^2*d j^2) 0 := by fun_prop
    exact (hcA.eventually (lt_mem_nhds (by simpa using hp j))).and
      (hcD.eventually (lt_mem_nhds (by simpa using sq_pos_of_pos (hp j))))
  have hprob : ∀ᶠ R in 𝓝[>] (0:ℝ), ∀ j,
      R*(1+t R)*|Real.sqrt B*d j| < p j := by
    apply eventually_all.mpr
    intro j
    have h : Tendsto (fun R : ℝ => R*(1+t R)*|Real.sqrt B*d j|) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds).mul
        (tendsto_const_nhds.add htlim)).mul_const |Real.sqrt B*d j|
    exact h.eventually (gt_mem_nhds (hp j))
  refine ⟨w,t,hw,ht,hlimit,?_⟩
  filter_upwards [self_mem_nhdsWithin, htp, htlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    helim.eventually hn, hrad.filter_mono nhdsWithin_le_nhds, helim.eventually hcoeff, hprob]
    with R hR htp ht1 hnorm hr hc hp'
  exact ⟨hR,htp,ht1,hnorm.1,hnorm.2.1,hnorm.2.2.1,hnorm.2.2.2,hr,hc,hp'⟩

theorem actual_upper_family : ∀ {m : ℕ}
      (p d : Fin m → ℝ) (hp : ∀ j, 0<p j) (hp1 : ∑ j, p j=1)
      (hd0 : ∑ j, d j=0) (hd : ∑ j, d j^2/p j=1) (B : ℝ) (hB : 0<B),
      ∃ (N : ℝ → Fin m → Matrix (Fin 2) (Fin 2) ℂ)
        (rho : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (I : ℝ → Set ℝ) (Q : ℝ → ℝ),
        Tendsto (fun R => (Q R-B)/R^2) (𝓝[>] 0)
          (𝓝 (B^2/4*(∑ j, d j^4/(p j)^3-1-(∑ j, d j^3/(p j)^2)^2))) ∧
        (∀ᶠ R in 𝓝[>] 0, IsProgram p (fun j => Real.sqrt B*d j) R
          (N R) (rho R) (I R) (Q R)) := by
  classical
  have blochMatrix_properties (a : ℝ) (r : (EuclideanSpace ℝ (Fin 3))) :
      (blochMatrix a r).IsHermitian ∧
      Matrix.trace (blochMatrix a r) = (a : ℂ) ∧
      bloch (blochMatrix a r) = r ∧
      (Matrix.det (blochMatrix a r)).re = (a^2 - ‖r‖^2) / 4 ∧
      ((blochMatrix a r).PosSemidef ↔ ‖r‖ ≤ a) := by
    have hh : (blochMatrix a r).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [blochMatrix]
    have ht : Matrix.trace (blochMatrix a r) = (a : ℂ) := by
      apply Complex.ext <;> simp [blochMatrix, Matrix.trace, Fin.sum_univ_two] <;> ring
    have hb : bloch (blochMatrix a r) = r := by
      ext i
      fin_cases i <;> simp [bloch, blochMatrix] <;> ring
    have hd : (Matrix.det (blochMatrix a r)).re = (a^2 - ‖r‖^2)/4 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [blochMatrix, Matrix.det_fin_two, Fin.sum_univ_three]
      ring
    refine ⟨hh, ht, hb, hd, ?_⟩
    constructor
    · intro hp
      have htpos := (Complex.nonneg_iff.mp hp.trace_nonneg).1
      have hdpos := (Complex.nonneg_iff.mp hp.det_nonneg).1
      rw [ht] at htpos
      rw [hd] at hdpos
      simp only [Complex.ofReal_re] at htpos
      nlinarith [norm_nonneg r]
    · intro hbound
      apply hh.posSemidef_iff_eigenvalues_nonneg.mpr
      have hs := congrArg Complex.re hh.trace_eq_sum_eigenvalues
      rw [ht] at hs
      simp only [Fin.sum_univ_two, Complex.add_re, Complex.ofReal_re] at hs
      have hp := congrArg Complex.re hh.det_eq_prod_eigenvalues
      rw [hd] at hp
      simp only [Fin.prod_univ_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] at hp
      change a = hh.eigenvalues 0 + hh.eigenvalues 1 at hs
      change (a^2 - ‖r‖^2) / 4 = hh.eigenvalues 0 * hh.eigenvalues 1 - 0*0 at hp
      simp only [mul_zero, sub_zero] at hp
      have htr : 0 ≤ a := (norm_nonneg r).trans hbound
      have hdet : 0 ≤ hh.eigenvalues 0 * hh.eigenvalues 1 := by nlinarith [norm_nonneg r]
      intro i
      fin_cases i
      · by_contra h
        have hi : hh.eigenvalues 0 < 0 := lt_of_not_ge h
        have hj : 0 < hh.eigenvalues 1 := by linarith
        exact (not_lt_of_ge hdet) (mul_neg_of_neg_of_pos hi hj)
      · by_contra h
        have hi : hh.eigenvalues 1 < 0 := lt_of_not_ge h
        have hj : 0 < hh.eigenvalues 0 := by linarith
        exact (not_lt_of_ge hdet) (mul_neg_of_pos_of_neg hj hi)

  have root_facts (p d α e w : ℝ) (he : e < 1)
      (hA : 0 < p-α*e*w*d)
      (hD : 0 < (p-α*e*w*d)^2-4*e*(1-e)*w^2*d^2) :
      0 < upperDiag p d α e w ∧ 0 ≤ root p d α e w ∧
      upperDiag p d α e w * root p d α e w = (w*d)^2 ∧
      (1-e)*upperDiag p d α e w + e*root p d α e w + α*e*w*d = p := by
    let A := p-α*e*w*d
    let S := Real.sqrt (A^2-4*e*(1-e)*w^2*d^2)
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hSS : S^2=A^2-4*e*(1-e)*w^2*d^2 := Real.sq_sqrt hD.le
    have hden : A+S ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hA hS)
    have he' : 1-e ≠ 0 := ne_of_gt (sub_pos.mpr he)
    change 0 < (A+S)/(2*(1-e)) ∧ 0 ≤ 2*(1-e)*w^2*d^2/(A+S) ∧
      (A+S)/(2*(1-e))*(2*(1-e)*w^2*d^2/(A+S))=(w*d)^2 ∧
      (1-e)*((A+S)/(2*(1-e)))+e*(2*(1-e)*w^2*d^2/(A+S))+α*e*w*d=p
    refine ⟨div_pos (by linarith) (by linarith), div_nonneg (by positivity) (by linarith), ?_, ?_⟩
    · field_simp
      <;> ring
    · field_simp
      dsimp only [A] at hSS ⊢
      nlinarith only [hSS]

  have arc_valid (e x c : ℝ) (I : Set ℝ) (hI : IsOpen I) (h0 : 0 ∈ I)
      (hinside : ∀ u ∈ I, (x+c*u)^2 < 4*e*(1-e)) :
      ContDiffOn ℝ 1 (arc e x c) I ∧
      (∀ u ∈ I, (arc e x c u).PosSemidef ∧ trace (arc e x c u) = 1 ∧
        arc e x c u * arc e x c u = arc e x c u) ∧
      (∀ h : (arc e x c 0).PosSemidef,
        spectralQFI (arc e x c 0) (deriv (arc e x c) 0) h =
        c^2*(4*e*(1-e))/(4*e*(1-e)-x^2)) := by
    have hr (u : ℝ) (hu : u ∈ I) :
        (Real.sqrt (4*e*(1-e)-(x+c*u)^2))^2 = 4*e*(1-e)-(x+c*u)^2 :=
      Real.sq_sqrt (sub_nonneg.mpr (hinside u hu).le)
    have hc : ContDiffOn ℝ 1 (arc e x c) I := by
      have hx : ContDiffOn ℝ 1 (fun u : ℝ => x+c*u) I := by fun_prop
      have hy : ContDiffOn ℝ 1 (fun u : ℝ => Real.sqrt (4*e*(1-e)-(x+c*u)^2)) I := by
        apply ContDiffOn.sqrt
        · fun_prop
        · intro u hu
          exact ne_of_gt (sub_pos.mpr (hinside u hu))
      have hxC := Complex.ofRealCLM.contDiff.comp_contDiffOn hx
      have hyC := Complex.ofRealCLM.contDiff.comp_contDiffOn hy
      apply contDiffOn_pi.mpr
      intro i
      apply contDiffOn_pi.mpr
      intro j
      fin_cases i <;> fin_cases j
      · simp [arc,blochMatrix]; fun_prop
      · simpa [arc,blochMatrix] using (hxC.sub (hyC.mul contDiffOn_const)).div_const (2:ℂ)
      · simpa [arc,blochMatrix] using (hxC.add (hyC.mul contDiffOn_const)).div_const (2:ℂ)
      · simp [arc,blochMatrix]; fun_prop
    have hpure (u : ℝ) (hu : u ∈ I) :
        (arc e x c u).PosSemidef ∧ trace (arc e x c u) = 1 ∧
        arc e x c u * arc e x c u = arc e x c u := by
      have hn : ‖(WithLp.toLp 2 ![x+c*u,Real.sqrt (4*e*(1-e)-(x+c*u)^2),1-2*e] : (EuclideanSpace ℝ (Fin 3)))‖ = 1 := by
        have hsq : ‖(WithLp.toLp 2 ![x+c*u,Real.sqrt (4*e*(1-e)-(x+c*u)^2),1-2*e] : (EuclideanSpace ℝ (Fin 3)))‖^2 = 1 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [Fin.sum_univ_three, hr u hu]
          ring
        nlinarith [norm_nonneg (WithLp.toLp 2 ![x+c*u,Real.sqrt (4*e*(1-e)-(x+c*u)^2),1-2*e] : (EuclideanSpace ℝ (Fin 3)))]
      refine ⟨(blochMatrix_properties _ _).2.2.2.2.mpr hn.le,
        (blochMatrix_properties _ _).2.1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [arc, blochMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
        nlinarith [hr u hu]
    refine ⟨hc,hpure,?_⟩
    intro h
    have spectral_energy {n : Type} [Fintype n] [DecidableEq n] (rho B L : Matrix n n ℂ) (hp : rho.PosSemidef)
        (hL : L.IsHermitian) (hsolve : L * rho + rho * L = (2 : ℂ) • B) :
        (L * rho * L).trace.re = spectralQFI rho B hp := by
      classical
      let U := hp.isHermitian.eigenvectorUnitary
      let d : n → ℂ := fun i => (hp.isHermitian.eigenvalues i : ℂ)
      let M := star (U : Matrix n n ℂ) * B * U
      let N := star (U : Matrix n n ℂ) * L * U
      have hs : rho = (U : Matrix n n ℂ) * diagonal d * star (U : Matrix n n ℂ) := by
        simpa [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def] using hp.isHermitian.spectral_theorem
      have hN : N.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul _ hL
      have hu : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := U.property.1
      have hu' : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := U.property.2
      have hdiag : star (U : Matrix n n ℂ) * rho * (U : Matrix n n ℂ) = diagonal d := by
        rw [hs]
        simp only [← Matrix.mul_assoc, hu, one_mul]
        simp only [Matrix.mul_assoc, hu, mul_one]
      have hentry (i j : n) : N i j * (d i + d j) = 2 * M i j := by
        have he := congrArg (fun X : Matrix n n ℂ =>
          (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j) hsolve
        have heq : star (U : Matrix n n ℂ) * (L * rho + rho * L) * U =
            N * diagonal d + diagonal d * N := by
          rw [← hdiag]
          dsimp only [N]
          simp only [mul_add, add_mul, Matrix.mul_assoc, ← mul_assoc (U : Matrix n n ℂ), hu', one_mul]
        rw [heq] at he
        change (N * diagonal d + diagonal d * N) i j = _ at he
        simp only [Matrix.add_apply, mul_diagonal, diagonal_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at he
        change N i j * d j + d i * N i j = 2 * M i j at he
        linear_combination he
      have hterm (i j : n) :
          2 * Complex.normSq (M i j) /
            (hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j) =
          (hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j) / 2 *
            Complex.normSq (N i j) := by
        have he := hentry i j
        have hm : M i j = ((d i + d j) / 2) * N i j := by linear_combination -he / 2
        rw [hm, map_mul]
        have hd : (d i + d j) / 2 =
            (((hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j) / 2 : ℝ) : ℂ) := by
          simp [d]
        rw [hd, Complex.normSq_ofReal]
        by_cases hz : hp.isHermitian.eigenvalues i + hp.isHermitian.eigenvalues j = 0
        · simp [hz]
        · field_simp
          <;> ring
      have heTrace : (L * rho * L).trace = (N * diagonal d * N).trace := by
        rw [← hdiag]
        dsimp only [N]
        simp only [Matrix.mul_assoc, ← mul_assoc (U : Matrix n n ℂ), hu', one_mul]
        rw [trace_mul_comm (star (U : Matrix n n ℂ))]
        simp only [Matrix.mul_assoc, hu', mul_one]
      have heSum : (L * rho * L).trace.re =
          ∑ i, ∑ j, hp.isHermitian.eigenvalues j * Complex.normSq (N i j) := by
        rw [heTrace]
        simp only [Matrix.trace, Matrix.diag]
        simp only [Matrix.mul_apply (M := N * diagonal d) (N := N), mul_diagonal, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hn : N j i = star (N i j) := by simpa using (hN.apply j i).symm
        rw [hn]
        have : N i j * d j * star (N i j) = d j * (Complex.normSq (N i j) : ℂ) := by
          rw [Complex.normSq_eq_conj_mul_self]
          change _ = d j * (star (N i j) * N i j)
          ring
        rw [this]
        simp [d]
      have hswap : (∑ i, ∑ j, hp.isHermitian.eigenvalues i * Complex.normSq (N i j)) =
          ∑ i, ∑ j, hp.isHermitian.eigenvalues j * Complex.normSq (N i j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [← hN.apply i j]
        simp only [Complex.star_def, Complex.normSq_conj]
      rw [heSum]
      unfold spectralQFI
      change _ = ∑ i, ∑ j, 2 * Complex.normSq (M i j) / _
      simp_rw [hterm, add_div, add_mul]
      simp only [Finset.sum_add_distrib, div_mul_eq_mul_div, ← Finset.sum_div]
      rw [hswap]
      ring

    have energy (r d : Matrix (Fin 2) (Fin 2) ℂ) (h : d*r+r*d=d) :
        (Matrix.trace (((2:ℂ) • d)*r*((2:ℂ) • d))).re =
          2*(Matrix.trace (d*d)).re := by
      have ht := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (Matrix.trace (M*d)).re) h
      simp only [add_mul, Matrix.trace_add, Complex.add_re] at ht
      rw [← Matrix.trace_mul_cycle r d d] at ht
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re]
      norm_num
      rw [← Matrix.trace_mul_cycle r d d]
      linarith
    let y := Real.sqrt (4*e*(1-e)-x^2)
    have hinside0 : x^2 < 4*e*(1-e) := by simpa only [mul_zero, add_zero] using hinside 0 h0
    have hy : 0 < y := Real.sqrt_pos.mpr (sub_pos.mpr hinside0)
    have hy2 : y^2=4*e*(1-e)-x^2 := Real.sq_sqrt (sub_nonneg.mpr hinside0.le)
    let D := blochMatrix 0 (WithLp.toLp 2 ![c,-x*c/y,0])
    have hx : HasDerivAt (fun u : ℝ => x+c*u) c 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_mul c).const_add x
    have hys : HasDerivAt (fun u : ℝ => Real.sqrt (4*e*(1-e)-(x+c*u)^2))
        (-x*c/y) 0 := by
      have hh := ((hasDerivAt_const (0:ℝ) (4*e*(1-e))).sub (hx.pow 2)).sqrt
        (by simpa using ne_of_gt (sub_pos.mpr hinside0))
      convert hh using 1 <;> first | rfl | (dsimp [y]; ring)
    have hxC : HasDerivAt (fun u : ℝ => ((x+c*u : ℝ):ℂ)) (c:ℂ) 0 :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hx
    have hyC : HasDerivAt (fun u : ℝ => ((Real.sqrt (4*e*(1-e)-(x+c*u)^2):ℝ):ℂ))
        ((-x*c/y:ℝ):ℂ) 0 := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hys
    have hd : HasDerivAt (arc e x c) D 0 := by
      apply hasDerivAt_pi.mpr
      intro i
      apply hasDerivAt_pi.mpr
      intro j
      fin_cases i <;> fin_cases j
      · simpa [arc,blochMatrix,D] using hasDerivAt_const (0:ℝ) (((1+(1-2*e):ℝ):ℂ)/2)
      · simpa [arc,blochMatrix,D] using (hxC.sub (hyC.mul_const Complex.I)).div_const 2
      · simpa [arc,blochMatrix,D] using (hxC.add (hyC.mul_const Complex.I)).div_const 2
      · simpa [arc,blochMatrix,D] using hasDerivAt_const (0:ℝ) (((1-(1-2*e):ℝ):ℂ)/2)
    have hD : D.IsHermitian := (blochMatrix_properties _ _).1
    have he (i j : Fin 2) : HasDerivAt (fun u => arc e x c u i j) (D i j) 0 :=
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
    have hprod : HasDerivAt (fun u => arc e x c u * arc e x c u)
        (D*arc e x c 0+arc e x c 0*D) 0 := by
      apply hasDerivAt_pi.mpr
      intro i
      apply hasDerivAt_pi.mpr
      intro j
      simp only [Matrix.mul_apply, Matrix.add_apply]
      rw [← Finset.sum_add_distrib]
      exact HasDerivAt.fun_sum fun k _ => (he i k).mul (he k j)
    have htan : D*arc e x c 0+arc e x c 0*D=D := by
      apply hprod.unique
      apply hd.congr_of_eventuallyEq
      filter_upwards [hI.mem_nhds h0] with u hu
      exact (hpure u hu).2.2
    have hSLD : ((2:ℂ) • D)*arc e x c 0+arc e x c 0*((2:ℂ) • D)=(2:ℂ) • D := by
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, htan]
    have hQ := spectral_energy (arc e x c 0) D ((2:ℂ) • D)
      h (hD.smul (by norm_num)) hSLD
    have hdd : 2*(Matrix.trace (D*D)).re = c^2+(x*c/y)^2 := by
      simp [D, blochMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hderiv : deriv (arc e x c) 0 = D := hd.deriv
    calc
      spectralQFI (arc e x c 0) (deriv (arc e x c) 0) h = spectralQFI (arc e x c 0) D h :=
        congrArg (fun d => spectralQFI (arc e x c 0) d h) hderiv
      _ = 2*(Matrix.trace (D*D)).re := hQ.symm.trans (energy _ _ htan)
      _ = c^2+(x*c/y)^2 := hdd
      _ = _ := by
        rw [div_pow, hy2]
        field_simp [ne_of_gt (sub_pos.mpr hinside0)]
        <;> ring

  have born_exact (p d α e w c u : ℝ) (he : e < 1)
      (hA : 0 < p-α*e*w*d)
      (hD : 0 < (p-α*e*w*d)^2-4*e*(1-e)*w^2*d^2) :
      trace (effect p d α e w * arc e (α*e) c u) = ((p+u*(c*w*d):ℝ):ℂ) := by
    have h := (root_facts p d α e w he hA hD).2.2.2
    apply Complex.ext <;>
      simp [effect, arc, blochMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im] <;> nlinarith [h]

  intro m p d hp hp1 hd0 hd B hB
  let α := -2*∑ j, d j^3/(p j)^2
  obtain ⟨w,t,hw,ht,hlim,hgood⟩ := actual_effect_family p d hp hp1 hd0 hd B hB
  change Tendsto (fun R => (extendedCost B α w ((t R)^2)-B)/R^2) _ _ at hlim
  let N := fun R j => effect (p j) (d j) α ((t R)^2) (w ((t R)^2))
  let rho := fun R => arc ((t R)^2) (α*(t R)^2) (Real.sqrt B/w ((t R)^2))
  let I := fun R => Ioo (-R*(1+t R)) (R*(1+t R))
  refine ⟨N,rho,I,fun R => extendedCost B α w ((t R)^2),hlim,?_⟩
  filter_upwards [hgood] with R hg
  rcases hg with ⟨hR,hT,hT1,hW,hq,hN,hN1,hr,hcoeff,hprob⟩
  let T := t R
  let W := w (T^2)
  let c := Real.sqrt B/W
  have hBroot : 0<Real.sqrt B := Real.sqrt_pos.mpr hB
  have hc : 0<c := div_pos hBroot hW
  have he : T^2<1 := by dsimp [T]; nlinarith only [hT,hT1]
  have hep : 0<T^2 := sq_pos_of_pos hT
  have hLs : R<R*(1+T) := by nlinarith only [mul_pos hR hT]
  have hrad : |α| *T^2+c*(R*(1+T))=2*T*Real.sqrt (1-T^2) := by
    change radiusMap B α w T=R at hr
    unfold radiusMap at hr
    have hh := (div_eq_iff (ne_of_gt (mul_pos (by linarith : 0<1+T) hBroot))).mp hr
    dsimp [c,W]
    field_simp [show w (T^2) ≠ 0 from hW.ne']
    nlinarith only [hh]
  have hinside (u : ℝ) (hu : u ∈ I R) : (α*T^2+c*u)^2<4*T^2*(1-T^2) := by
    have huabs : |u|<R*(1+T) := abs_lt.mpr (by simpa [I,T,neg_mul] using hu)
    have hab : |α*T^2+c*u| < 2*T*Real.sqrt (1-T^2) := by
      calc
        |α*T^2+c*u| ≤ |α*T^2|+|c*u| := abs_add_le _ _
        _ = |α| *T^2+c*|u| := by simp only [abs_mul,abs_of_pos hc,abs_of_nonneg (sq_nonneg T)]
        _ < |α| *T^2+c*(R*(1+T)) := add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left huabs hc)
        _ = _ := hrad
    have hs := Real.sq_sqrt (sub_nonneg.mpr he.le)
    have hp : 0≤2*T*Real.sqrt (1-T^2) := by positivity
    have hsq := (sq_lt_sq₀ (abs_nonneg (α*T^2+c*u)) hp).mpr hab
    rw [sq_abs] at hsq
    have heq : (2*T*Real.sqrt (1-T^2))^2 = 4*T^2*(1-T^2) := by
      rw [mul_pow, hs]
      ring
    rwa [heq] at hsq
  have h0 : 0∈I R := by
    change -R*(1+T)<0 ∧ 0<R*(1+T)
    have hpos := mul_pos hR (show 0<1+T by linarith only [hT])
    constructor <;> linarith only [hpos]
  obtain ⟨hsmooth,hpure,hcost⟩ := arc_valid (T^2) (α*T^2) c (I R) isOpen_Ioo h0 hinside
  change IsProgram p (fun j => Real.sqrt B*d j) R (N R) (rho R) (I R) _
  refine ⟨isOpen_Ioo, isPreconnected_Ioo, ?_,hN,hN1,hsmooth,?_,?_,?_⟩
  · intro u hu
    change -R*(1+T)<u ∧ u<R*(1+T)
    constructor <;> linarith only [hu.1,hu.2,hLs]
  · intro u hu
    let r := densityBridge (arc (T^2) (α*T^2) c u) (hpure u hu).1 (hpure u hu).2.1
    exact ⟨(hpure u hu).1,(hpure u hu).2.1,(hpure u hu).2.2,r.1,r.2⟩
  · intro u hu j
    have hcW : c*W=Real.sqrt B := div_mul_cancel₀ _ hW.ne'
    have hb := born_exact (p j) (d j) α (T^2) W c u he (hcoeff j).1 (hcoeff j).2
    rw [← mul_assoc, hcW] at hb
    refine ⟨by simpa only [mul_assoc] using hb,?_⟩
    have huabs : |u|<R*(1+T) := abs_lt.mpr (by simpa [I,T,neg_mul] using hu)
    have hbound : |u*(Real.sqrt B*d j)|<p j := by
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right huabs.le (abs_nonneg _)) (hprob j)
    linarith only [hbound, neg_abs_le (u*(Real.sqrt B*d j))]
  · intro h
    rw [hcost h]
    change (Real.sqrt B/W)^2*(4*T^2*(1-T^2))/(4*T^2*(1-T^2)-(α*T^2)^2) =
      B/W^2*(4*(1-T^2))/(4*(1-T^2)-α^2*T^2)
    rw [div_pow, Real.sq_sqrt hB.le]
    rw [show 4*T^2*(1-T^2)-(α*T^2)^2 = T^2*(4*(1-T^2)-α^2*T^2) by ring]
    calc
      B/W^2*(4*T^2*(1-T^2))/(T^2*(4*(1-T^2)-α^2*T^2)) =
          (T^2*(B/W^2*(4*(1-T^2))))/(T^2*(4*(1-T^2)-α^2*T^2)) := by ring
      _ = _ := mul_div_mul_left _ _ hep.ne'
end D5.S3.Quantum.Information.ActualPureQubitCostInfimum
