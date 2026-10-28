/- GID: D5/S3/Observer/CubicGain/InteriorPrefixClassification
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/InteriorPrefixClassification
   mirror-E: none(waiver:full-interior-prefix-parameters)
   anchors: [mathlib/module/Mathlib.RingTheory.Coprime.Lemmas]
   utility: none
   digest: Necessary interior parameters retain their actual chronological prefix. -/

import D5.S3.Observer.CubicGain.InteriorNormalForm

/-! The two consecutive integer multipliers and their primitive parameters. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace D5.S3.Observer.CubicGain.InteriorPrefixClassification

open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open D5.S3.Observer.CubicGain.LegalMatrixMonoid
open D5.S3.Observer.CubicGain.PrefixKernelSigns
open D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open D5.S3.Observer.CubicGain.PhaseRigidity
open D5.S3.Observer.CubicGain.InteriorNormalForm
open scoped Matrix

/-- The rank obstruction is kept explicit: the forbidden equality would make
the three chronological prefix differences linearly dependent. -/
theorem two_transition_parameters (K H : ZMat) (x y d c j h : ℤ)
    (hK : ∀ i k, 0 ≤ K i k) (hH : ∀ i k, 0 ≤ H i k)
    (hdK : K.det = 1 ∨ K.det = -1) (hdH : H.det = 1 ∨ H.det = -1)
    (hx : d < x) (hy : 0 < y) (hd : 0 < d) (hc : 0 < c)
    (hxy : IsCoprime x y) (hcd : IsCoprime d c)
    (ht : 0 < x*c-y*d) (hj : 1 ≤ j) (hh : 1 ≤ h)
    (hvK : K *ᵥ ![x,y] = ![x+j*d,y+j*c])
    (hvH : H *ᵥ ![x+j*d,y+j*c] = ![x+(j+h)*d,y+(j+h)*c])
    (hind : H*K ≠ (2:ℤ) • K - 1) :
    j = 1 ∧ y = d ∧ IsCoprime x d ∧ ∃ n σ : ℤ,
      1 ≤ n ∧ (σ = 1 ∨ σ = -1) ∧
      h = n*(x+d)+σ ∧ c = x+h*d ∧
      2 ≤ 1+n*d ∧ K = !![1,1;1+n*d,1+n*d+σ] ∧ H = !![0,1;1,h] := by
  obtain ⟨hj1,hyd,hcx,hHeq⟩ := last_transition_rigidity K H x y d c j h
    hK hH hdK hdH hx hy hd hc hxy hcd ht hj hh hvK hvH
  subst j
  subst y
  have hv0 := congrFun hvK 0
  have hv1 := congrFun hvK 1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hv0 hv1
  have hx0 : 0 < x := lt_trans hd hx
  have h00le : K 0 0 ≤ 1 := by
    by_contra hn
    have hge : 2 ≤ K 0 0 := by omega
    have hp := mul_nonneg (sub_nonneg.mpr hge) hx0.le
    have hp' := mul_nonneg (hK 0 1) hd.le
    nlinarith only [hv0,hx,hp,hp']
  have h00 : K 0 0 = 1 := by
    by_contra hn
    have hz : K 0 0 = 0 := by have hn0 := hK 0 0; omega
    have hprod : K 0 1*K 1 0 = 1 := by
      rcases hdK with he | he
      · simp only [Matrix.det_fin_two,hz,zero_mul,zero_sub] at he
        have hp := mul_nonneg (hK 0 1) (hK 1 0)
        linarith only [he,hp]
      · simpa [Matrix.det_fin_two,hz] using he
    have h01pos : 1 ≤ K 0 1 := by
      have hn := hK 0 1
      by_contra hh
      have hz : K 0 1 = 0 := by omega
      simp [hz] at hprod
    have h10pos : 1 ≤ K 1 0 := by
      have hn := hK 1 0
      by_contra hh
      have hz : K 1 0 = 0 := by omega
      simp [hz] at hprod
    have h01 : K 0 1 = 1 := by nlinarith only [hprod,h01pos,h10pos]
    rw [hz,h01] at hv0
    simp at hv0
    omega
  have h01 : K 0 1 = 1 := by
    rw [h00] at hv0
    nlinarith only [hv0,hd]
  have h11 : K 1 1 = K 1 0+K.det := by
    simp only [Matrix.det_fin_two,h00,h01]
    ring
  have hQ : K 1 0*(x+d) = c+(1-K.det)*d := by
    rw [h11] at hv1
    nlinarith only [hv1]
  have hcgt : x < c := by nlinarith only [hcx,hh,hd]
  have hQpos : 1 ≤ K 1 0 := by
    have hnon := hK 1 0
    by_contra hn
    have hz : K 1 0 = 0 := by omega
    rw [hz] at hQ
    rcases hdK with he | he <;> rw [he] at hQ <;> nlinarith only [hQ,hcgt,hx,hd]
  have hQtwo : 2 ≤ K 1 0 := by
    by_contra hn
    have heQ : K 1 0 = 1 := by omega
    rcases hdK with he | he
    · have hec : c = x+d := by rw [heQ,he] at hQ; linarith only [hQ]
      have heh : h = 1 := by nlinarith only [hec,hcx,hd]
      apply hind
      rw [hHeq,heh]
      have hKeq : K = !![1,1;1,2] := by
        ext i k
        fin_cases i <;> fin_cases k <;> simp [h00,h01,heQ,h11,he]
      rw [hKeq]
      ext i k
      fin_cases i <;> fin_cases k <;>
        norm_num [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
    · rw [heQ,he] at hQ
      nlinarith only [hQ,hcgt,hd]
  have hrel : (K 1 0-1)*x = (h+1-K.det-K 1 0)*d := by
    nlinarith only [hQ,hcx]
  have hdiv : d ∣ K 1 0-1 := hxy.symm.dvd_of_dvd_mul_right
    ⟨h+1-K.det-K 1 0,by nlinarith only [hrel]⟩
  obtain ⟨n,hn⟩ := hdiv
  have hnpos : 1 ≤ n := by nlinarith only [hn,hQtwo,hd]
  have heh : h = n*(x+d)+K.det := by
    have hd0 : d ≠ 0 := ne_of_gt hd
    apply mul_right_cancel₀ hd0
    nlinarith only [hn,hQ]
  refine ⟨rfl,rfl,hxy,n,K.det,hnpos,hdK,heh,hcx,?_,?_,hHeq⟩
  · nlinarith only [hn,hQtwo]
  · ext i k
    fin_cases i <;> fin_cases k <;> simp [h00,h01,h11] <;> nlinarith only [hn]

private theorem integer_word (u : List Bool) : ∃ A : ZMat,
    (∀ i j, 0 ≤ A i j) ∧ (A.det = 1 ∨ A.det = -1) ∧ real A = futureProduct u := by
  obtain ⟨he,hd⟩ := (legal_matrix_monoid (futureProduct u)).mp ⟨u,rfl⟩
  choose A hA using fun i j => (he i j).2
  have hreal : real A = futureProduct u := by
    ext i j
    exact (hA i j).symm
  refine ⟨A,fun i j => ?_,?_,hreal⟩
  · have hh := (he i j).1
    rw [hA i j] at hh
    exact_mod_cast hh
  · rw [←hreal] at hd
    rcases hd with hd | hd
    · left; exact_mod_cast (show ((A 0 0:ℝ)*A 1 1-(A 0 1:ℝ)*A 1 0) = 1 by
        simpa [real,Matrix.det_fin_two] using hd)
    · right; exact_mod_cast (show ((A 0 0:ℝ)*A 1 1-(A 0 1:ℝ)*A 1 0) = -1 by
        simpa [real,Matrix.det_fin_two] using hd)

/-- Parameters of the positive branch, with the original words, primitive
coordinates, first-endpoint equation and rank filter all retained. -/
def ParameterForm (w : Fin 3 → List Bool) (p : PrimitiveCoordinates)
    (m : Fin 4 → ℤ) : Prop :=
  (0 < p.a ∧ 0 < p.b ∧ 0 < p.c ∧ 0 < p.d) ∧
  ∃ x n σ : ℤ, (p.d:ℤ) < x ∧ IsCoprime x (p.d:ℤ) ∧
    1 ≤ m 1 ∧ 1 ≤ n ∧ (σ = 1 ∨ σ = -1) ∧
    (p.a:ℤ) = x-m 1*p.d ∧ (p.b:ℤ) = m 1*p.c-p.d ∧
    (p.c:ℤ) = x+(n*(x+p.d)+σ)*p.d ∧
    2 ≤ 1+n*p.d ∧
    prefixMatrix w 1 *ᵥ p.column = ![(x:ℝ),(p.d:ℝ)] ∧
    futureProduct (w 1) = !![1,1;((1+n*p.d:ℤ):ℝ),((1+n*p.d+σ:ℤ):ℝ)] ∧
    futureProduct (w 2) = !![0,1;1,((n*(x+p.d)+σ:ℤ):ℝ)] ∧
    m 2 = m 1+1 ∧ m 3 = m 1+1+(n*(x+p.d)+σ) ∧
    Module.finrank ℝ (LinearMap.range (prefixDifference w)) = 3

private theorem positive_phase_parameters (w : Fin 3 → List Bool) (p : PrimitiveCoordinates)
    (m : Fin 4 → ℤ)
    (hp : 0 < p.a ∧ 0 < p.b ∧ 0 < p.c ∧ 0 < p.d)
    (hphase : StrictPhase w p m)
    (hrank : Module.finrank ℝ (LinearMap.range (prefixDifference w)) = 3) :
    ParameterForm w p m := by
  obtain ⟨ha,hb,hc,hd⟩ := hp
  obtain ⟨hm0,hm,hpos,hm1,hm12,hm23⟩ := hphase
  let x : ℤ := (p.a:ℤ)+m 1*p.d
  let y : ℤ := -(p.b:ℤ)+m 1*p.c
  let j : ℤ := m 2-m 1
  let h : ℤ := m 3-m 2
  obtain ⟨K,hK,hdK,hKr⟩ := integer_word (w 1)
  obtain ⟨H,hH,hdH,hHr⟩ := integer_word (w 2)
  have himage (i : Fin 4) : prefixMatrix w i *ᵥ p.column =
      ![(((p.a:ℤ)+m i*p.d:ℤ):ℝ),((-(p.b:ℤ)+m i*p.c:ℤ):ℝ)] := by
    rw [hm i]
    ext k
    fin_cases k <;> simp [PrimitiveCoordinates.column,PrimitiveCoordinates.direction]
  have hfirst : prefixMatrix w 1 *ᵥ p.column = ![(x:ℝ),(y:ℝ)] := himage 1
  have hxy : IsCoprime x y := by
    have hi := word_primitive (prefixWord w 1) p.column
      ⟨p.a,-(p.b:ℤ),rfl,by simp [PrimitiveCoordinates.column],p.column_primitive.isCoprime.neg_right⟩
    change Primitive (prefixMatrix w 1 *ᵥ p.column) at hi
    rw [hfirst] at hi
    obtain ⟨X,Y,hX,hY,hcop⟩ := hi
    have hX' : x = X := by exact_mod_cast (show (x:ℝ) = X by simpa using hX)
    have hY' : y = Y := by exact_mod_cast (show (y:ℝ) = Y by simpa using hY)
    simpa [hX',hY'] using hcop
  have hvK : K *ᵥ ![x,y] = ![x+j*p.d,y+j*p.c] := by
    have he := hm 2
    have hs := prefix_step w 1
    change prefixMatrix w 2 = futureProduct (w 1)*prefixMatrix w 1 at hs
    rw [hs,←Matrix.mulVec_mulVec,hfirst,←hKr] at he
    ext i
    have he' := congrFun he i
    fin_cases i <;>
      simp [real,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
        PrimitiveCoordinates.column,PrimitiveCoordinates.direction] at he' ⊢ <;>
      dsimp [x,y,j] <;> exact_mod_cast (by linear_combination he')
  have hvH : H *ᵥ ![x+j*p.d,y+j*p.c] =
      ![x+(j+h)*p.d,y+(j+h)*p.c] := by
    have he := hm 3
    have hs := prefix_step w 2
    change prefixMatrix w 3 = futureProduct (w 2)*prefixMatrix w 2 at hs
    rw [hs,←Matrix.mulVec_mulVec,himage 2,←hHr] at he
    ext i
    have he' := congrFun he i
    fin_cases i <;>
      simp [real,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
        PrimitiveCoordinates.column,PrimitiveCoordinates.direction] at he' ⊢ <;>
      dsimp [x,y,j,h] <;> exact_mod_cast (by linear_combination he')
  have hind : H*K ≠ (2:ℤ) • K-1 := by
    intro he
    have heR : real H * real K = (2:ℝ) • real K-1 := by
      ext i k
      have he' := congrFun (congrFun he i) k
      simp [real,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply] at he' ⊢
      exact_mod_cast he'
    have hs1 := prefix_step w 1
    have hs2 := prefix_step w 2
    change prefixMatrix w 2 = futureProduct (w 1)*prefixMatrix w 1 at hs1
    change prefixMatrix w 3 = futureProduct (w 2)*prefixMatrix w 2 at hs2
    have heA : prefixMatrix w 3 = (2:ℝ) • prefixMatrix w 2-prefixMatrix w 1 := by
      rw [hs2,hs1,←hHr,←hKr,←Matrix.mul_assoc,heR,Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul]
    have hsur : Function.Surjective (prefixDifference w) :=
      LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by simpa using hrank))
    obtain ⟨X,hX⟩ := hsur ![0,0,1]
    have h0 := congrFun hX 0
    have h1 := congrFun hX 1
    have h2 := congrFun hX 2
    change Matrix.trace (prefixMatrix w 1*X)-Matrix.trace X = 0 at h0
    change Matrix.trace (prefixMatrix w 2*X)-Matrix.trace X = 0 at h1
    change Matrix.trace (prefixMatrix w 3*X)-Matrix.trace X = 1 at h2
    rw [heA,Matrix.sub_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_smul] at h2
    change 2*Matrix.trace (prefixMatrix w 2*X)-Matrix.trace (prefixMatrix w 1*X)-Matrix.trace X = 1 at h2
    linarith only [h0,h1,h2]
  have hx : (p.d:ℤ) < x := by
    dsimp [x]
    have ha' : (0:ℤ) < p.a := by exact_mod_cast ha
    have hd' : (0:ℤ) < p.d := by exact_mod_cast hd
    nlinarith only [ha',hd',hm1]
  have hy : 0 < y := by
    have he := (hpos 0).2
    change 0 < (prefixMatrix w 1 *ᵥ p.column) 1 at he
    rw [hfirst] at he
    exact_mod_cast (show (0:ℝ) < (y:ℝ) by simpa using he)
  have ht : 0 < x*(p.c:ℤ)-y*p.d := by
    have hp' : (0:ℤ) < (p.a:ℤ)*p.c+(p.b:ℤ)*p.d := by exact_mod_cast p.trace_pos
    dsimp [x,y]
    nlinarith only [hp']
  obtain ⟨hj1,hyd,hcop,n,σ,hn,hσ,heh,hec,hQ,hKeq,hHeq⟩ :=
    two_transition_parameters K H x y p.d p.c j h hK hH hdK hdH hx hy
      (by exact_mod_cast hd) (by exact_mod_cast hc) hxy p.row_primitive.isCoprime.symm ht
      (by dsimp [j]; omega) (by dsimp [h]; omega) hvK hvH hind
  refine ⟨⟨ha,hb,hc,hd⟩,x,n,σ,hx,hcop,hm1,hn,hσ,?_,?_,?_,hQ,?_,?_,?_,?_,?_,hrank⟩
  · dsimp [x]; ring
  · dsimp [y] at hyd; linarith only [hyd]
  · rw [←heh]; exact hec
  · simpa [hyd] using hfirst
  · rw [←hKr,hKeq]; ext i k; fin_cases i <;> fin_cases k <;> simp [real]
  · rw [←hHr,hHeq,heh]; ext i k; fin_cases i <;> fin_cases k <;> simp [real]
  · dsimp [j] at hj1; omega
  · dsimp [j,h] at hj1 heh; omega

private theorem rank_of_trace_surjective (w : Fin 3 → List Bool)
    (hs : Function.Surjective (prefixTrace w)) :
    Module.finrank ℝ (LinearMap.range (prefixDifference w)) = 3 := by
  have hd : Function.Surjective (prefixDifference w) := by
    intro z
    obtain ⟨X,hX⟩ := hs ![0,z 0,z 1,z 2]
    refine ⟨X,?_⟩
    ext i
    have h0 := congrFun hX 0
    have hi := congrFun hX i.succ
    change Matrix.trace X = 0 at h0
    change Matrix.trace (prefixMatrix w i.succ*X) = _ at hi
    change Matrix.trace (prefixMatrix w i.succ*X)-Matrix.trace X = z i
    rw [h0,sub_zero,hi]
    fin_cases i <;> rfl
  rw [LinearMap.range_eq_top.mpr hd]
  simp

/-- Every original four-nonzero-entry prefix has precisely the displayed
integer parameter form, either on its given history or on its full J conjugate.
The kernel scale stays positive and every recorded index is unchanged. -/
theorem interior_necessity (w : Fin 3 → List Bool) (N : Mat)
    (hG : OrientedKernelGenerator w N) (hn : ∀ i j, N i j ≠ 0) :
    ∃ (p : PrimitiveCoordinates) (scale : ℝ) (m : Fin 4 → ℤ),
      0 < scale ∧ N = scale • p.matrix ∧ m 0 = 0 ∧
      (∀ i, prefixMatrix w i *ᵥ p.column = p.column+(m i:ℝ) • p.direction) ∧
      (∀ i, prefixMatrix (conjugateHistory w) i = actionJ*prefixMatrix w i*actionJ) ∧
      actionJ*N*actionJ = scale • (swapCoordinates p).matrix ∧
      (ParameterForm w p m ∨
        ParameterForm (conjugateHistory w) (swapCoordinates p) (fun i => -m i)) := by
  obtain ⟨p,scale,m,hs,hN,hp,hm0,hm,hconj,hNconj,hphase⟩ := phase_rigidity w N hG hn
  have hsur := (kernel_signs_positive_trace_invertible w N hG).2.2.2
  have hrank := rank_of_trace_surjective w hsur
  have hrank' : Module.finrank ℝ
      (LinearMap.range (prefixDifference (conjugateHistory w))) = 3 := by
    apply rank_of_trace_surjective
    intro z
    obtain ⟨X,hX⟩ := hsur z
    refine ⟨actionJ*X*actionJ,?_⟩
    ext i
    change Matrix.trace (prefixMatrix (conjugateHistory w) i*(actionJ*X*actionJ)) = z i
    rw [hconj]
    have he : Matrix.trace ((actionJ*prefixMatrix w i*actionJ)*(actionJ*X*actionJ)) =
        Matrix.trace (prefixMatrix w i*X) := by
      simp [actionJ,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]
      ring
    rw [he]
    exact congrFun hX i
  refine ⟨p,scale,m,hs,hN,hm0,hm,hconj,hNconj,?_⟩
  rcases hphase with hphase | hphase
  · exact Or.inl (positive_phase_parameters w p m hp hphase hrank)
  · exact Or.inr (positive_phase_parameters _ _ _
      ⟨hp.2.1,hp.1,hp.2.2.2,hp.2.2.1⟩ hphase hrank')

#print axioms two_transition_parameters
#print axioms interior_necessity

end D5.S3.Observer.CubicGain.InteriorPrefixClassification
