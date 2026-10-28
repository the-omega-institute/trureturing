/- GID: D5/S3/Observer/CubicGain/InteriorNormalForm
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/InteriorNormalForm
   mirror-E: none(waiver:chronological-interior-transition-classification)
   anchors: [mathlib/module/Mathlib.RingTheory.Coprime.Lemmas]
   utility: none
   digest: Integer transition rigidity in the interior signed lattice. -/

import D5.S3.Observer.CubicGain.PhaseRigidity

/-! Primitive transition coefficients and consecutive interior rigidity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace D5.S3.Observer.CubicGain.InteriorNormalForm

open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open D5.S3.Observer.CubicGain.LegalMatrixMonoid
open D5.S3.Observer.CubicGain.PrefixKernelSigns
open D5.S3.Observer.CubicGain.PrimitiveKernelLattice
open D5.S3.Observer.CubicGain.PhaseRigidity
open scoped Matrix

abbrev ZMat := Matrix (Fin 2) (Fin 2) ℤ
def real (A : ZMat) : Mat := A.map (Int.castRingHom ℝ)

private theorem real_action (A : ZMat) (x y : ℤ) :
    real A *ᵥ ![(x:ℝ),(y:ℝ)] =
      ![((A 0 0*x+A 0 1*y:ℤ):ℝ),((A 1 0*x+A 1 1*y:ℤ):ℝ)] := by
  ext i
  fin_cases i <;> simp [real,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

private theorem legal_integer (A : ZMat) (hA : ∀ i j, 0 ≤ A i j)
    (hd : A.det = 1 ∨ A.det = -1) : ∃ u, futureProduct u = real A := by
  apply (legal_matrix_monoid _).mpr
  refine ⟨fun i j => ⟨by change (0:ℝ) ≤ (A i j:ℝ); exact_mod_cast hA i j, A i j, rfl⟩, ?_⟩
  rcases hd with hd | hd
  · left; simpa [real,Matrix.det_fin_two] using congrArg (Int.cast : ℤ → ℝ) hd
  · right; simpa [real,Matrix.det_fin_two] using congrArg (Int.cast : ℤ → ℝ) hd

/-- A legal positive primitive transition has an integral positive shear
coefficient, with both determinant signs and the undivided entry identities. -/
theorem transition_certificate (A : ZMat) (x y d c j : ℤ)
    (hA : ∀ i k, 0 ≤ A i k) (hdet : A.det = 1 ∨ A.det = -1)
    (hx : 0 < x) (hy : 0 < y) (hd : 0 < d) (hc : 0 < c)
    (hxy : IsCoprime x y) (_hcd : IsCoprime d c)
    (ht : 0 < x*c-y*d) (hj : 1 ≤ j)
    (hv : A *ᵥ ![x,y] = ![x+j*d,y+j*c]) :
    ∃ l : ℤ, 1 ≤ l ∧
      A *ᵥ ![d,c] = A.det • ![d,c] + l • ![x+j*d,y+j*c] ∧
      (x*c-y*d)*A 1 0 = c*(y+j*c-A.det*y)-l*y*(y+j*c) ∧
      (x*c-y*d)*A 0 0 = c*(x+j*d)-A.det*d*y-l*y*(x+j*d) ∧
      (A.det = 1 → (l:ℝ) ≤ (j:ℝ)*c^2/((y:ℝ)*(y+j*c))) ∧
      (A.det = -1 → (l:ℝ) ≤ (c:ℝ)*(1/(y:ℝ)+1/(y+j*c))) ∧
      (A.det = 1 → y < c) ∧ y < 2*c := by
  obtain ⟨u,hu⟩ := legal_integer A hA hdet
  have hv0 := congrFun hv 0
  have hv1 := congrFun hv 1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hv0 hv1
  have hprim := word_primitive u ![(x:ℝ),(y:ℝ)] ⟨x,y,rfl,rfl,hxy⟩
  rw [hu,real_action] at hprim
  obtain ⟨X,Y,hX,hY,hcop⟩ := hprim
  have hX' : X = x+j*d := by
    have hh : ((A 0 0*x+A 0 1*y:ℤ):ℝ) = (X:ℝ) := by simpa using hX
    have hhZ : X = A 0 0*x+A 0 1*y := by exact_mod_cast hh.symm
    exact hhZ.trans hv0
  have hY' : Y = y+j*c := by
    have hh : ((A 1 0*x+A 1 1*y:ℤ):ℝ) = (Y:ℝ) := by simpa using hY
    have hhZ : Y = A 1 0*x+A 1 1*y := by exact_mod_cast hh.symm
    exact hhZ.trans hv1
  rw [hX',hY'] at hcop
  obtain ⟨α,β,hbez⟩ := hcop
  let z0 := A 0 0*d+A 0 1*c-A.det*d
  let z1 := A 1 0*d+A 1 1*c-A.det*c
  have hparallel : (x+j*d)*z1 = (y+j*c)*z0 := by
    dsimp [z0,z1]
    simp only [Matrix.det_fin_two]
    linear_combination -(A 1 0*d+A 1 1*c)*hv0 +
      (A 0 0*d+A 0 1*c)*hv1
  let l := α*z0+β*z1
  have hz0 : z0 = l*(x+j*d) := by
    dsimp [l]
    linear_combination -z0*hbez - β*hparallel
  have hz1 : z1 = l*(y+j*c) := by
    dsimp [l]
    linear_combination -z1*hbez + α*hparallel
  have hwr : A *ᵥ ![d,c] = A.det • ![d,c] + l • ![x+j*d,y+j*c] := by
    ext i
    fin_cases i
    · simpa [z0,Matrix.mulVec,dotProduct,Fin.sum_univ_two,sub_eq_iff_eq_add,add_comm]
        using hz0
    · simpa [z1,Matrix.mulVec,dotProduct,Fin.sum_univ_two,sub_eq_iff_eq_add,add_comm]
        using hz1
  have hl : 1 ≤ l := by
    rcases hdet with he | he
    · have hp : Positive (![(d:ℝ),(c:ℝ)]) := ⟨by change (0:ℝ) < (d:ℝ); exact_mod_cast hd,by change (0:ℝ) < (c:ℝ); exact_mod_cast hc⟩
      obtain ⟨_,hs,heq⟩ := positive_sum u _ hp
      have hne : futureProduct u ≠ 1 ∧ futureProduct u ≠ actionJ := by
        constructor
        · intro hh
          have h0 := congrFun (show real A *ᵥ ![(x:ℝ),(y:ℝ)] = ![(x:ℝ),(y:ℝ)] by rw [←hu,hh]; simp) 0
          rw [real_action] at h0
          have hh' : A 0 0*x+A 0 1*y = x := by
            change ((A 0 0*x+A 0 1*y:ℤ):ℝ) = (x:ℝ) at h0
            exact_mod_cast h0
          nlinarith
        · intro hh
          have h0 := congrFun (show real A *ᵥ ![(x:ℝ),(y:ℝ)] = ![(y:ℝ),(x:ℝ)] by
            rw [←hu,hh]; ext i; fin_cases i <;> simp [actionJ,Matrix.mulVec,dotProduct,Fin.sum_univ_two]) 0
          have h1 := congrFun (show real A *ᵥ ![(x:ℝ),(y:ℝ)] = ![(y:ℝ),(x:ℝ)] by
            rw [←hu,hh]; ext i; fin_cases i <;> simp [actionJ,Matrix.mulVec,dotProduct,Fin.sum_univ_two]) 1
          rw [real_action] at h0 h1
          have hh0 : A 0 0*x+A 0 1*y = y := by
            change ((A 0 0*x+A 0 1*y:ℤ):ℝ) = (y:ℝ) at h0
            exact_mod_cast h0
          have hh1 : A 1 0*x+A 1 1*y = x := by
            change ((A 1 0*x+A 1 1*y:ℤ):ℝ) = (x:ℝ) at h1
            exact_mod_cast h1
          nlinarith
      have hstrict : (d:ℝ)+c < (futureProduct u *ᵥ ![(d:ℝ),(c:ℝ)]) 0+
          (futureProduct u *ᵥ ![(d:ℝ),(c:ℝ)]) 1 := by
        apply lt_of_le_of_ne hs
        intro hh
        rcases heq hh with hh | hh
        · exact hne.1 hh
        · exact hne.2 hh
      rw [hu,real_action] at hstrict
      have hh : d+c < A 0 0*d+A 0 1*c+(A 1 0*d+A 1 1*c) := by exact_mod_cast (show (d:ℝ)+c < ((A 0 0*d+A 0 1*c:ℤ):ℝ)+((A 1 0*d+A 1 1*c:ℤ):ℝ) by simpa using hstrict)
      dsimp [z0,z1] at hz0 hz1
      rw [he] at hz0 hz1
      have hsum : 0 < x+j*d+(y+j*c) := by nlinarith
      have hmul : 0 < l*(x+j*d+(y+j*c)) := by nlinarith only [hz0,hz1,hh]
      have hpos : 0 < l := by
        by_contra hn
        have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hsum.le
        linarith only [hmul,hp]
      omega
    · dsimp [z0] at hz0
      rw [he] at hz0
      have hz : 0 < A 0 0*d+A 0 1*c+d := by
        nlinarith [mul_nonneg (hA 0 0) hd.le,mul_nonneg (hA 0 1) hc.le]
      have hxp : 0 < x+j*d := by nlinarith only [hx,hd,hj]
      have hmul : 0 < l*(x+j*d) := by linarith only [hz0,hz]
      have hpos : 0 < l := by
        by_contra hn
        have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hxp.le
        linarith only [hmul,hp]
      omega
  have h10 : (x*c-y*d)*A 1 0 = c*(y+j*c-A.det*y)-l*y*(y+j*c) := by
    dsimp [z1] at hz1
    linear_combination c*hv1-y*hz1
  have h00 : (x*c-y*d)*A 0 0 = c*(x+j*d)-A.det*d*y-l*y*(x+j*d) := by
    dsimp [z0] at hz0
    linear_combination c*hv0-y*hz0
  have hbound : l*y*(y+j*c) ≤ c*(y+j*c-A.det*y) := by
    nlinarith only [h10,mul_nonneg ht.le (hA 1 0)]
  have hy' : 0 < y+j*c := by nlinarith
  have hplus : A.det = 1 → y < c := by
    intro he
    rw [he] at hbound
    by_contra hh
    have hcy : c ≤ y := le_of_not_gt hh
    have hprod : j*c*c ≤ j*c*y := mul_le_mul_of_nonneg_left hcy (by positivity)
    have hyy : y*(y+j*c) ≤ l*y*(y+j*c) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (mul_pos hy hy').le]
    nlinarith only [hbound,hprod,hyy,sq_pos_of_pos hy]
  have htwice : y < 2*c := by
    rcases hdet with he | he
    · linarith [hplus he]
    · rw [he] at hbound
      by_contra hh
      have hcy : 2*c ≤ y := le_of_not_gt hh
      have hprod : 2*c*(y+j*c) ≤ y*(y+j*c) :=
        mul_le_mul_of_nonneg_right hcy hy'.le
      have hyy : y*(y+j*c) ≤ l*y*(y+j*c) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (mul_pos hy hy').le]
      have hpos : 0 < c*(j*c) := by positivity
      nlinarith only [hbound,hprod,hyy,hpos]
  refine ⟨l,hl,hwr,h10,h00,?_,?_,hplus,htwice⟩
  · intro he
    have hb : (l:ℝ)*(y:ℝ)*(y+j*c) ≤ (j:ℝ)*(c:ℝ)^2 := by
      rw [he] at hbound
      exact_mod_cast (show l*y*(y+j*c) ≤ j*c^2 by nlinarith only [hbound])
    apply (le_div_iff₀ (show (0:ℝ) < (y:ℝ)*(y+j*c) by exact_mod_cast mul_pos hy hy')).mpr
    simpa only [mul_assoc] using hb
  · intro he
    have hb : (l:ℝ)*(y:ℝ)*(y+j*c) ≤ (c:ℝ)*((y:ℝ)+j*c+y) := by
      rw [he] at hbound
      exact_mod_cast (show l*y*(y+j*c) ≤ c*(y+j*c+y) by nlinarith only [hbound])
    have heq : (c:ℝ)*(1/(y:ℝ)+1/(y+j*c)) =
        ((c:ℝ)*((y:ℝ)+j*c+y))/((y:ℝ)*(y+j*c)) := by
      have hyR : (0:ℝ) < y := by exact_mod_cast hy
      have hyR' : (0:ℝ) < (y:ℝ)+j*c := by exact_mod_cast hy'
      field_simp [ne_of_gt hyR,ne_of_gt hyR']
      <;> ring
    rw [heq]
    apply (le_div_iff₀ (show (0:ℝ) < (y:ℝ)*(y+j*c) by exact_mod_cast mul_pos hy hy')).mpr
    simpa only [mul_assoc] using hb

/-- Two consecutive legal positive lattice increments force the last multiplier
to exchange the first coordinate, and force the preceding increment to be one. -/
theorem last_transition_rigidity (K H : ZMat) (x y d c j h : ℤ)
    (hK : ∀ i k, 0 ≤ K i k) (hH : ∀ i k, 0 ≤ H i k)
    (hdK : K.det = 1 ∨ K.det = -1) (hdH : H.det = 1 ∨ H.det = -1)
    (hx : d < x) (hy : 0 < y) (hd : 0 < d) (hc : 0 < c)
    (hxy : IsCoprime x y) (hcd : IsCoprime d c)
    (ht : 0 < x*c-y*d) (hj : 1 ≤ j) (hh : 1 ≤ h)
    (hvK : K *ᵥ ![x,y] = ![x+j*d,y+j*c])
    (hvH : H *ᵥ ![x+j*d,y+j*c] = ![x+(j+h)*d,y+(j+h)*c]) :
    j = 1 ∧ y = d ∧ c = x+h*d ∧ H = !![0,1;1,h] := by
  obtain ⟨u,hu⟩ := legal_integer K hK hdK
  have hprim := word_primitive u ![(x:ℝ),(y:ℝ)] ⟨x,y,rfl,rfl,hxy⟩
  rw [hu,real_action] at hprim
  obtain ⟨X,Y,hX,hY,hcop⟩ := hprim
  have hvK0 := congrFun hvK 0
  have hvK1 := congrFun hvK 1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hvK0 hvK1
  have hX' : X = x+j*d := by
    have he : ((K 0 0*x+K 0 1*y:ℤ):ℝ) = (X:ℝ) := by simpa using hX
    have heZ : X = K 0 0*x+K 0 1*y := by exact_mod_cast he.symm
    exact heZ.trans hvK0
  have hY' : Y = y+j*c := by
    have he : ((K 1 0*x+K 1 1*y:ℤ):ℝ) = (Y:ℝ) := by simpa using hY
    have heZ : Y = K 1 0*x+K 1 1*y := by exact_mod_cast he.symm
    exact heZ.trans hvK1
  rw [hX',hY'] at hcop
  have hvH' : H *ᵥ ![x+j*d,y+j*c] = ![x+j*d+h*d,y+j*c+h*c] := by
    convert hvH using 1 <;> ext i <;> fin_cases i <;> simp <;> ring
  obtain ⟨l,hl,hwr,h10,h00,hplus,hminus,hsmall,hbound⟩ :=
    transition_certificate H (x+j*d) (y+j*c) d c h hH hdH
      (by nlinarith) (by nlinarith) hd hc hcop hcd (by nlinarith [ht]) hh hvH'
  have he : H.det = -1 := by
    rcases hdH with he | he
    · have hs := hsmall he
      nlinarith
    · exact he
  have hj1 : j = 1 := by
    by_contra hn
    have hj2 : 2 ≤ j := by omega
    have hp := mul_nonneg (sub_nonneg.mpr hj2) hc.le
    nlinarith
  subst j
  have hl1 : l = 1 := by
    have hb : l*(y+c)*(y+c+h*c) ≤ c*((y+c+h*c)+(y+c)) := by
      rw [he] at h10
      nlinarith [mul_nonneg (by nlinarith [ht] : 0 ≤ (x+d)*c-(y+c)*d) (hH 1 0)]
    by_contra hn
    have hl2 : 2 ≤ l := by omega
    have hY : 0 < y+c := by omega
    have hZ : c < y+c+h*c := by nlinarith
    have hYZ : 0 < (y+c)*(y+c+h*c) := by positivity
    have hp := mul_nonneg (sub_nonneg.mpr hl2) hYZ.le
    have hp1 := mul_pos hy (show 0 < y+c+h*c by linarith)
    have hp2 := mul_pos hY (show 0 < y+c+h*c-c by linarith)
    nlinarith
  rw [hl1,he] at hwr h00
  have hH00 : H 0 0 = 0 := by
    have hupper : ((x+d)*c-(y+c)*d)*H 0 0 < (x+d)*c-(y+c)*d := by
      have hp1 := mul_pos hc (sub_pos.mpr hx)
      have hp2 := mul_pos (show 0 < x by omega) hy
      have hp3 := mul_nonneg (sub_nonneg.mpr hh) (mul_pos hd hy).le
      nlinarith only [h00,hp1,hp2,hp3]
    have hlt : H 0 0 < 1 := by nlinarith only [ht,hupper]
    have hnon := hH 0 0
    omega
  have hprod : H 0 1*H 1 0 = 1 := by
    simpa [Matrix.det_fin_two,hH00] using he
  have h01 : H 0 1 = 1 := by
    have h01pos : 1 ≤ H 0 1 := by
      have hnon := hH 0 1
      by_contra hn
      have hz : H 0 1 = 0 := by omega
      simp [hz] at hprod
    have h10pos : 1 ≤ H 1 0 := by
      have hnon := hH 1 0
      by_contra hn
      have hz : H 1 0 = 0 := by omega
      simp [hz] at hprod
    nlinarith only [hprod,h01pos,h10pos]
  have h10' : H 1 0 = 1 := by rw [h01] at hprod; simpa using hprod
  have hw0 := congrFun hwr 0
  have hw1 := congrFun hwr 1
  have hv0 := congrFun hvH 0
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,hH00,h01,h10'] at hw0 hw1 hv0
  have hyd : y = d := by linarith
  have hcx : c = x+h*d := by nlinarith
  have h11 : H 1 1 = h := by nlinarith
  refine ⟨rfl,hyd,hcx,?_⟩
  ext i k
  fin_cases i <;> fin_cases k <;> simp [hH00,h01,h10',h11]

#print axioms transition_certificate
#print axioms last_transition_rigidity

end D5.S3.Observer.CubicGain.InteriorNormalForm
