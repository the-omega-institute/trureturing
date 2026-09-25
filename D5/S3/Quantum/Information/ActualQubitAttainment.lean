/- GID: D5/S3/Quantum/Information/ActualQubitAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualQubitAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed CPTP qubit processor with exact spectral information and noncommuting full-rank programs. -/

import D5.S3.Quantum.Information.ActualPureQubitFisherRank
import D5.S3.Quantum.Foundation.FiniteKrausChannel

open scoped ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix Set Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Information.ActualQubitAttainment

def rho (a u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  blochMatrix 1 (WithLp.toLp 2 ![a*(1-u)/Real.sqrt (1-a^2),0,u])
def controls (a : ℝ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![(a:ℂ), (Real.sqrt (1-a^2):ℂ); (Real.sqrt (1-a^2):ℂ), -(a:ℂ)],
    !![1,0;0,-1]]
def controlled (a : ℝ) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  fun p q => if p.1=q.1 then controls a p.1 p.2 q.2 else 0
def kraus (a : ℝ) (r : Fin 2) : Matrix (Fin 3) (Fin 3 × Fin 2) ℂ :=
  fun i p => if i=p.1 then controls a i r p.2 else 0

theorem result (a : ℝ) (ha : 0<a) (ha1 : a<1) :
    (∀ i, (controls a i)ᴴ * controls a i = 1) ∧
    (controlled a)ᴴ * controlled a = 1 ∧ controlled a * (controlled a)ᴴ = 1 ∧
    (∀ u v : ℝ, u ≠ v →
      rho a u * rho a v - rho a v * rho a u =
        (Complex.I * ((a*(u-v)/(2*Real.sqrt (1-a^2)):ℝ):ℂ)) •
          !![0,-Complex.I;Complex.I,0] ∧
      rho a u * rho a v - rho a v * rho a u ≠ 0) ∧
    ∃ G : QuantumChannel (Fin 3 × Fin 2) (Fin 3),
      (∀ Ω : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ,
        CStarMatrix.ofMatrix.symm (G.toCompletelyPositiveMap (CStarMatrix.ofMatrix Ω)) =
          (fun i j => ∑ r : Fin 2,
            (controlled a * Ω * (controlled a)ᴴ) (i,r) (j,r))) ∧
      (∀ u : ℝ, ∀ ω : Matrix (Fin 3) (Fin 3) ℂ,
        CStarMatrix.ofMatrix.symm (G.toCompletelyPositiveMap
          (CStarMatrix.ofMatrix (Matrix.kronecker ω (rho a u)))) =
        fun i j => ω i j * (!![1,(a:ℂ),(u:ℂ);a,1,a;u,a,1]) i j) ∧
      (∀ (k : ℕ) (u : ℝ)
        (Ω : CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin 3) (Fin 3) ℂ)),
        (Ω.map (fun ω => CStarMatrix.ofMatrix
          (Matrix.kronecker (CStarMatrix.ofMatrix.symm ω) (rho a u)))).map
            G.toCompletelyPositiveMap =
        Ω.map (fun ω => CStarMatrix.ofMatrix (fun i j =>
          CStarMatrix.ofMatrix.symm ω i j * (!![1,(a:ℂ),(u:ℂ);a,1,a;u,a,1]) i j))) ∧
      ContDiff ℝ 1 (rho a) ∧
      (∀ u ∈ Ioo (2*a-1) 1, (rho a u).PosDef ∧ trace (rho a u)=1 ∧
        (rho a u).det = (((1-u)*(1+u-2*a^2)/(4*(1-a^2)):ℝ):ℂ) ∧
        IsUnit (rho a u) ∧
        (∃ state : DensityState (Fin 2), CStarMatrix.ofMatrix.symm state.1 = rho a u) ∧
        ∀ hp : (rho a u).PosSemidef,
          spectralQFI (rho a u) (deriv (rho a) u) hp =
            (1-a^2)/((1-u)*(1+u-2*a^2))) := by
  classical
  have hd : 0 < 1-a^2 := by nlinarith
  have hs : 0 < Real.sqrt (1-a^2) := Real.sqrt_pos.2 hd
  have hs0 := ne_of_gt hs
  have hs2 : (Real.sqrt (1-a^2))^2=1-a^2 := Real.sq_sqrt hd.le
  have hsc : (Real.sqrt (1-a^2):ℂ)^2=1-(a:ℂ)^2 := by exact_mod_cast hs2
  have hdc : 1-(a:ℂ)^2 ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hsc0 : (Real.sqrt (1-a^2):ℂ) ≠ 0 := by exact_mod_cast hs0
  have hunit : ∀ i, (controls a i)ᴴ * controls a i = 1 := by
    intro i
    fin_cases i
    · simp [controls]
    · ext p q
      fin_cases p <;> fin_cases q <;>
        simp [controls, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
        ring_nf <;> (try simp only [hsc]) <;> ring
    · ext p q
      fin_cases p <;> fin_cases q <;>
        norm_num [controls, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  have hK : (∑ r, (kraus a r)ᴴ * kraus a r)=1 := by
    ext ⟨i,p⟩ ⟨j,q⟩
    by_cases hij : i=j
    · subst j
      simpa [kraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply] using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M p q) (hunit i)
    · simp [kraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, hij, Ne.symm hij]
  obtain ⟨G,hG⟩ := finite_kraus_quantum_channel (kraus a) hK
  have hW : (controlled a)ᴴ * controlled a = 1 := by
    ext ⟨i,p⟩ ⟨j,q⟩
    by_cases hij : i=j
    · subst j
      simpa [controlled, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply] using
        congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M p q) (hunit i)
    · simp [controlled, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.one_apply, hij, Ne.symm hij, mul_ite, ite_mul]
  have hphysical (Ω : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
      CStarMatrix.ofMatrix.symm (G.toCompletelyPositiveMap (CStarMatrix.ofMatrix Ω)) =
        (fun i j => ∑ r : Fin 2,
          (controlled a * Ω * (controlled a)ᴴ) (i,r) (j,r)) := by
    rw [hG]
    ext i j
    simp [controlled,kraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum,mul_ite,ite_mul,Fin.sum_univ_two]
  have hcoeff (u : ℝ) (i j : Fin 3) :
      trace (controls a i * rho a u * (controls a j)ᴴ) =
        (!![1,(a:ℂ),(u:ℂ);a,1,a;u,a,1]) i j := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [controls,rho,blochMatrix] <;>
      field_simp [hsc0]
    all_goals try ring_nf
    all_goals try simp only [hsc]
    all_goals ring
  have haction (u : ℝ) (ω : Matrix (Fin 3) (Fin 3) ℂ) :
      CStarMatrix.ofMatrix.symm (G.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.kronecker ω (rho a u)))) =
      fun i j => ω i j * (!![1,(a:ℂ),(u:ℂ);a,1,a;u,a,1]) i j := by
    rw [hG]
    ext i j
    rw [← hcoeff u i j]
    simp [kraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.trace, Fintype.sum_prod_type, Finset.sum_mul,Finset.mul_sum,
      mul_ite,ite_mul,apply_ite,Fin.sum_univ_two]
    ring
  have hcomm (u v : ℝ) :
      rho a u * rho a v - rho a v * rho a u =
        (Complex.I * ((a*(u-v)/(2*Real.sqrt (1-a^2)):ℝ):ℂ)) •
          !![0,-Complex.I;Complex.I,0] := by
    ext i j
    simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.smul_apply,Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [rho,blochMatrix,div_eq_mul_inv] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  have hnoncomm (u v : ℝ) (huv : u≠v) :
      rho a u * rho a v - rho a v * rho a u ≠ 0 := by
    rw [hcomm]
    intro hz
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hz
    have huvC : (u:ℂ)-(v:ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr huv
    have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
    simp [Matrix.smul_apply, smul_eq_mul, mul_assoc, Complex.I_sq,
      haC,huvC,hsc0] at hh
  refine ⟨hunit, hW, mul_eq_one_comm.mp hW,
    (fun u v huv => ⟨hcomm u v,hnoncomm u v huv⟩), G, hphysical, haction, ?_, ?_, ?_⟩
  · intro k u Ω
    apply CStarMatrix.ext
    intro r s
    exact haction u (CStarMatrix.ofMatrix.symm (Ω r s))
  · have hc : ContDiff ℝ 1 (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    fin_cases i <;> fin_cases j <;> simp [rho,blochMatrix] <;> fun_prop (disch := positivity)
  · intro u hu
    have hA : 0 < (1-u)*(1+u-2*a^2) := mul_pos (by linarith [hu.2]) (by nlinarith [hu.1])
    have hherm : (rho a u).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [rho,blochMatrix]
    have ht : trace (rho a u)=1 := by
      simp [rho,blochMatrix,Matrix.trace,Fin.sum_univ_two]
      ring
    have hdet : (rho a u).det = (((1-u)*(1+u-2*a^2)/(4*(1-a^2)):ℝ):ℂ) := by
      simp [rho,blochMatrix,Matrix.det_fin_two]
      push_cast
      field_simp [hsc0, hdc]
      ring_nf
      simp only [hsc]
      ring
    have hdetpos : 0 < (rho a u).det.re := by
      rw [hdet,Complex.ofReal_re]
      exact div_pos hA (mul_pos (by norm_num) hd)
    have hpd : (rho a u).PosDef := by
      apply hherm.posDef_iff_eigenvalues_pos.mpr
      have hsum := congrArg Complex.re hherm.trace_eq_sum_eigenvalues
      rw [ht] at hsum
      simp only [Fin.sum_univ_two, Complex.add_re, Complex.ofReal_re, Complex.one_re] at hsum
      have hprod := congrArg Complex.re hherm.det_eq_prod_eigenvalues
      simp only [Fin.prod_univ_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] at hprod
      change 1 = hherm.eigenvalues 0 + hherm.eigenvalues 1 at hsum
      change (rho a u).det.re = hherm.eigenvalues 0*hherm.eigenvalues 1-0*0 at hprod
      simp only [mul_zero,sub_zero] at hprod
      rw [hprod] at hdetpos
      intro i
      fin_cases i
      · by_contra h
        have h0 : hherm.eigenvalues 0 ≤ 0 := le_of_not_gt h
        have h1 : 0 < hherm.eigenvalues 1 := by linarith
        have := mul_nonpos_of_nonpos_of_nonneg h0 h1.le
        linarith
      · by_contra h
        have h1 : hherm.eigenvalues 1 ≤ 0 := le_of_not_gt h
        have h0 : 0 < hherm.eigenvalues 0 := by linarith
        have := mul_nonpos_of_nonneg_of_nonpos h0.le h1
        linarith
    refine ⟨hpd,ht,hdet,hpd.isUnit,
      ⟨(densityBridge (rho a u) hpd.posSemidef ht).1,
        (densityBridge (rho a u) hpd.posSemidef ht).2⟩,?_⟩
    intro hp
    let D : Matrix (Fin 2) (Fin 2) ℂ :=
      blochMatrix 0 (WithLp.toLp 2 ![-a/Real.sqrt (1-a^2),0,1])
    have hder : HasDerivAt (rho a) D u := by
      have hx : HasDerivAt (fun t : ℝ => a*(1-t)/Real.sqrt (1-a^2))
          (-a/Real.sqrt (1-a^2)) u := by
        convert! (((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).const_mul a).div_const
          (Real.sqrt (1-a^2)) using 1 <;> norm_num
      have hxC := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u hx
      have huC := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_id u)
      apply hasDerivAt_pi.mpr
      intro i
      apply hasDerivAt_pi.mpr
      intro j
      fin_cases i <;> fin_cases j
      · simpa [rho,blochMatrix,D] using (huC.const_add 1).div_const 2
      · simpa [rho,blochMatrix,D] using hxC.div_const 2
      · simpa [rho,blochMatrix,D] using hxC.div_const 2
      · simpa [rho,blochMatrix,D] using ((hasDerivAt_const u (1:ℂ)).sub huC).div_const 2
    let L : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(((1-a^2)/(1+u-2*a^2):ℝ):ℂ), ((-a*Real.sqrt (1-a^2)/(1+u-2*a^2):ℝ):ℂ);
        ((-a*Real.sqrt (1-a^2)/(1+u-2*a^2):ℝ):ℂ),
        ((a^2/(1+u-2*a^2)-1/(1-u):ℝ):ℂ)]
    have hL : L.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      fin_cases i <;> fin_cases j <;> exact Complex.conj_ofReal _
    have huc : 1-(u:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0<1-u by linarith [hu.2]))
    have hbc : 1+(u:ℂ)-2*(a:ℂ)^2 ≠ 0 := by
      exact_mod_cast (ne_of_gt (show 0<1+u-2*a^2 by nlinarith [hu.1]))
    have hbc2 : 1-(a:ℂ)^2*2+(u:ℂ) ≠ 0 := by convert hbc using 1 <;> ring
    have hbc3 : 1+(u:ℂ)-(a:ℂ)^2*2 ≠ 0 := by convert hbc using 1 <;> ring
    have hsolve : L*rho a u+rho a u*L=(2:ℂ) • D := by
      ext i j
      simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.smul_apply,Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp [L,D,rho,blochMatrix] <;>
        push_cast <;> field_simp [hsc0,huc,hbc]
      all_goals try ring_nf
      all_goals try simp only [hsc]
      all_goals field_simp [hbc2,hbc3]
      all_goals ring
    have hdv : deriv (rho a) u = D := hder.deriv
    rw [hdv, ← spectral_energy (rho a u) D L hp hL hsolve]
    have htrace : (L*rho a u*L).trace.re = (D*L).trace.re := by
      have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M*L).trace.re) hsolve
      simp only [add_mul, Matrix.trace_add, Complex.add_re, smul_mul_assoc,
        Matrix.trace_smul, smul_eq_mul, Complex.mul_re] at hh
      have hcyc : (rho a u*L*L).trace=(L*rho a u*L).trace := by
        rw [Matrix.trace_mul_cycle]
      rw [hcyc] at hh
      norm_num at hh
      linarith
    rw [htrace]
    simp [L,D,blochMatrix,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two,
      ← Complex.ofReal_div, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      ← Complex.ofReal_sub, ← Complex.ofReal_neg]
    have hbr : 1+u-2*a^2 ≠ 0 := by nlinarith [hu.1]
    have hcr : 1-u ≠ 0 := by linarith [hu.2]
    field_simp [hs0,hbr,hcr]
    ring

end D5.S3.Quantum.Information.ActualQubitAttainment
