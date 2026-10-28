/- GID: D5/S3/Observer/CubicGain/InteriorNormalForm
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/InteriorNormalForm
   mirror-E: none(waiver:chronological-interior-transition-classification)
   anchors: [mathlib/module/Mathlib.RingTheory.Coprime.Lemmas]
   utility: none
   digest: Integer transition rigidity in the interior signed lattice. -/

import D5.S3.Observer.CubicGain.PhaseRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
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
  refine ⟨fun i j => ⟨by exact_mod_cast hA i j, A i j, rfl⟩, ?_⟩
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
      (x*c-y*d)*A 0 0 = c*(x+j*d-A.det*x)-l*y*(x+j*d) ∧
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
    exact_mod_cast (hh.symm.trans (by exact_mod_cast hv0))
  have hY' : Y = y+j*c := by
    have hh : ((A 1 0*x+A 1 1*y:ℤ):ℝ) = (Y:ℝ) := by simpa using hY
    exact_mod_cast (hh.symm.trans (by exact_mod_cast hv1))
  rw [hX',hY'] at hcop
  obtain ⟨α,β,hbez⟩ := hcop
  let z0 := A 0 0*d+A 0 1*c-A.det*d
  let z1 := A 1 0*d+A 1 1*c-A.det*c
  have hparallel : (x+j*d)*z1 = (y+j*c)*z0 := by
    dsimp [z0,z1]
    simp only [Matrix.det_fin_two]
    linear_combination (A 1 0*d+A 1 1*c)*hv0 -
      (A 0 0*d+A 0 1*c)*hv1
  let l := α*z0+β*z1
  have hz0 : z0 = l*(x+j*d) := by
    dsimp [l]
    linear_combination -z0*hbez + β*hparallel
  have hz1 : z1 = l*(y+j*c) := by
    dsimp [l]
    linear_combination -z1*hbez - α*hparallel
  have hwr : A *ᵥ ![d,c] = A.det • ![d,c] + l • ![x+j*d,y+j*c] := by
    ext i
    fin_cases i
    · simpa [z0,Matrix.mulVec,dotProduct,Fin.sum_univ_two,sub_eq_iff_eq_add,add_comm]
        using hz0
    · simpa [z1,Matrix.mulVec,dotProduct,Fin.sum_univ_two,sub_eq_iff_eq_add,add_comm]
        using hz1
  have hl : 1 ≤ l := by
    rcases hdet with he | he
    · have hp : Positive (![(d:ℝ),(c:ℝ)]) := ⟨by exact_mod_cast hd,by exact_mod_cast hc⟩
      obtain ⟨_,hs,heq⟩ := positive_sum u _ hp
      have hne : futureProduct u ≠ 1 ∧ futureProduct u ≠ actionJ := by
        constructor
        · intro hh
          have h0 := congrFun (show real A *ᵥ ![(x:ℝ),(y:ℝ)] = ![(x:ℝ),(y:ℝ)] by rw [←hu,hh]; simp) 0
          rw [real_action] at h0
          have hh' : A 0 0*x+A 0 1*y = x := by exact_mod_cast h0
          nlinarith
        · intro hh
          have h0 := congrFun (show real A *ᵥ ![(x:ℝ),(y:ℝ)] = ![(y:ℝ),(x:ℝ)] by
            rw [←hu,hh]; ext i; fin_cases i <;> simp [actionJ,Matrix.mulVec,dotProduct,Fin.sum_univ_two]) 0
          have h1 := congrFun (show real A *ᵥ ![(x:ℝ),(y:ℝ)] = ![(y:ℝ),(x:ℝ)] by
            rw [←hu,hh]; ext i; fin_cases i <;> simp [actionJ,Matrix.mulVec,dotProduct,Fin.sum_univ_two]) 1
          rw [real_action] at h0 h1
          have hh0 : A 0 0*x+A 0 1*y = y := by exact_mod_cast h0
          have hh1 : A 1 0*x+A 1 1*y = x := by exact_mod_cast h1
          nlinarith
      have hstrict : (d:ℝ)+c < (futureProduct u *ᵥ ![(d:ℝ),(c:ℝ)]) 0+
          (futureProduct u *ᵥ ![(d:ℝ),(c:ℝ)]) 1 := by
        apply lt_of_le_of_ne hs
        intro hh
        rcases heq hh with hh | hh
        · exact hne.1 hh
        · exact hne.2 hh
      rw [hu,real_action] at hstrict
      have hh : d+c < A 0 0*d+A 0 1*c+(A 1 0*d+A 1 1*c) := by exact_mod_cast hstrict
      dsimp [z0,z1] at hz0 hz1
      rw [he] at hz0 hz1
      have hsum : 0 < x+j*d+(y+j*c) := by nlinarith
      have hpos : 0 < l := by nlinarith
      omega
    · dsimp [z0] at hz0
      rw [he] at hz0
      have hz : 0 < A 0 0*d+A 0 1*c+d := by
        nlinarith [mul_nonneg (hA 0 0) hd.le,mul_nonneg (hA 0 1) hc.le]
      have hpos : 0 < l := by nlinarith
      omega
  have h10 : (x*c-y*d)*A 1 0 = c*(y+j*c-A.det*y)-l*y*(y+j*c) := by
    dsimp [z1] at hz1
    linear_combination c*hv1-y*hz1
  have h00 : (x*c-y*d)*A 0 0 = c*(x+j*d-A.det*x)-l*y*(x+j*d) := by
    dsimp [z0] at hz0
    linear_combination c*hv0-y*hz0
  have hbound : l*y*(y+j*c) ≤ c*(y+j*c-A.det*y) := by
    nlinarith [mul_nonneg ht.le (hA 1 0)]
  have hy' : 0 < y+j*c := by nlinarith
  have hplus : A.det = 1 → y < c := by
    intro he
    rw [he] at hbound
    by_contra hh
    have hcy : c ≤ y := le_of_not_gt hh
    have hprod : j*c*c ≤ j*c*y := mul_le_mul_of_nonneg_left hcy (by positivity)
    have hyy : y*(y+j*c) ≤ l*y*(y+j*c) := by nlinarith
    nlinarith [sq_pos_of_pos hy]
  have htwice : y < 2*c := by
    rcases hdet with he | he
    · linarith [hplus he]
    · rw [he] at hbound
      by_contra hh
      have hcy : 2*c ≤ y := le_of_not_gt hh
      have hprod : 2*c*(y+j*c) ≤ y*(y+j*c) :=
        mul_le_mul_of_nonneg_right hcy hy'.le
      have hyy : y*(y+j*c) ≤ l*y*(y+j*c) := by nlinarith
      have hpos : 0 < c*(j*c) := by positivity
      nlinarith
  refine ⟨l,hl,hwr,h10,h00,?_,?_,hplus,htwice⟩
  · intro he
    have hb : (l:ℝ)*(y:ℝ)*(y+j*c) ≤ (j:ℝ)*(c:ℝ)^2 := by
      rw [he] at hbound
      exact_mod_cast (show l*y*(y+j*c) ≤ j*c^2 by nlinarith [hbound])
    apply (le_div_iff₀ (show (0:ℝ) < (y:ℝ)*(y+j*c) by exact_mod_cast mul_pos hy hy')).mpr
    nlinarith [hb]
  · intro he
    have hb : (l:ℝ)*(y:ℝ)*(y+j*c) ≤ (c:ℝ)*((y:ℝ)+j*c+y) := by
      rw [he] at hbound
      exact_mod_cast (show l*y*(y+j*c) ≤ c*(y+j*c+y) by nlinarith [hbound])
    have heq : (c:ℝ)*(1/(y:ℝ)+1/(y+j*c)) =
        ((c:ℝ)*((y:ℝ)+j*c+y))/((y:ℝ)*(y+j*c)) := by
      field_simp
      <;> ring
    rw [heq]
    apply (le_div_iff₀ (show (0:ℝ) < (y:ℝ)*(y+j*c) by exact_mod_cast mul_pos hy hy')).mpr
    nlinarith [hb]

#print axioms transition_certificate

end D5.S3.Observer.CubicGain.InteriorNormalForm
