/- GID: D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: Infinite congruence-family spectral obstruction for paired tensors. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Tactic

/-! The infinite congruence-family argument is from the completed general
endpoint mathematical note supplied 2026-11-02. It replaces the public source's
fixed mod-17 exceptional certificate. No finite exponent sample is a premise. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix Polynomial
open scoped Classical Kronecker
namespace D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionCongruence
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
open D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants

/- In characteristic three the parameters may have arbitrary nilpotent
thickenings. No fixed finite field, nilpotency order, or matrix-entry certificate
is retained as a provider. -/
private lemma shifted_tensor_nilpotent {R : Type*} [CommRing R] [CharP R 3]
    (b c : R) (hb : IsNilpotent (b+1)) (hc : IsNilpotent (c+1)) :
    IsNilpotent (tensorK 2 b c+1) := by
  have h3 : (3 : R)=0 := CharP.cast_eq_zero R 3
  have hf (k : R) : (F k+1)^2=(k+1) • (1 : Matrix (Fin 2) (Fin 2) R) := by
    have he : (F k+1)^2=(3 : R) • F k+(k+1) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pow_two,F,mul_apply,Fin.sum_univ_two,Matrix.one_apply] <;> ring
    simpa [h3] using he
  let U := (F b+1) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) R)
  let W := (1 : Matrix (Fin 2) (Fin 2) R) ⊗ₖ (F c+1)
  have hXsq : U^2=(b+1) • 1 := by
    dsimp [U]
    rw [pow_two,← mul_kronecker_mul,one_mul,← pow_two,hf]
    simp [smul_kronecker,one_kronecker_one]
  have hYsq : W^2=(c+1) • 1 := by
    dsimp [W]
    rw [pow_two,← mul_kronecker_mul,one_mul,← pow_two,hf]
    simp [kronecker_smul,one_kronecker_one]
  have hX : IsNilpotent U := by
    apply IsNilpotent.of_pow (m := 2)
    rw [hXsq]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hb.map (algebraMap R (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R))
  have hY : IsNilpotent W := by
    apply IsNilpotent.of_pow (m := 2)
    rw [hYsq]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hc.map (algebraMap R (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R))
  have hcomm : Commute U W := by
    show U*W=W*U
    dsimp [U,W]
    rw [← mul_kronecker_mul,← mul_kronecker_mul]
    simp
  have he : tensorK 2 b c+1=U+W-U*W := by
    have h2 : (2 : R) = -1 := by linear_combination h3
    ext ⟨i,j⟩ ⟨l,m⟩
    fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
      simp [U,W,tensorK,E,F,h2,mul_apply,Fintype.sum_prod_type,
        Fin.sum_univ_succ,kroneckerMap_apply,Matrix.one_apply] <;> ring
  rw [he]
  have hsum : Commute (U+W) (U*W) :=
    ((Commute.refl U).mul_right hcomm).add_left
      (hcomm.symm.mul_right (Commute.refl W))
  exact hsum.isNilpotent_sub
      (hcomm.isNilpotent_add hX hY) (hcomm.isNilpotent_mul_right hX)

/-- Over every commutative ring of characteristic three, nilpotent deviations
of both tail parameters from minus one give characteristic polynomial `X^4`
modulo the nilradical, with no bound on the nilpotency orders. -/
theorem shifted_tensor_charpoly_mod_three {R : Type*} [CommRing R] [CharP R 3]
    (b c : R) (hb : IsNilpotent (b+1)) (hc : IsNilpotent (c+1)) :
    IsNilpotent ((tensorK 2 b c+1).charpoly-X^4) := by
  simpa using Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
    (shifted_tensor_nilpotent b c hb hc)

/-- The determinant of the entire mod-nine family is not divisible by 27. -/
theorem shifted_tensor_det_not_dvd (s t : ℤ) :
    ¬(27 : ℤ) ∣ (tensorK 2 (9*s+5) (9*t+8)+1).det := by
  let Z := (3*s+2)*(t+1)
  let R := s+t+1
  let W := 270*Z^2+171*Z*R+158*Z-15*R^2-19*R-6
  have he : (tensorK 2 (9*s+5) (9*t+8)+1).det = 27*(4*W+2)+18 := by
    rw [det_two_add_one]
    dsimp [W,Z,R]
    ring
  intro hd
  have hh : (27 : ℤ) ∣ (tensorK 2 (9*s+5) (9*t+8)+1).det-27*(4*W+2) :=
    dvd_sub hd (dvd_mul_right 27 (4*W+2))
  rw [he] at hh
  norm_num at hh


private lemma shifted_tensor_map {R : Type*} [CommRing R] (b c : ℤ) :
    (tensorK (2 : ℤ) b c+1).map (Int.castRingHom R)=tensorK 2 (b : R) (c : R)+1 := by
  ext ⟨i,j⟩ ⟨l,m⟩
  change (((2+1)*(E b i l*E c j m)+2*(F b i l*F c j m)+
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ) (i,j) (l,m) : ℤ) : R) =
    (2+1)*(E (b : R) i l*E (c : R) j m)+2*(F (b : R) i l*F (c : R) j m)+
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) (i,j) (l,m)
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
    simp [E,F,Matrix.one_apply] <;> ring

/-- Every positive member of the full `b=5 mod 9, c=8 mod 9` family has a
noninteger real tensor eigenvalue. The source exceptional pair is a specialization. -/
theorem two_mod_nine_noninteger (s t : ℤ) (hb : 0 < 9*s+5) (hc : 0 < 9*t+8) :
    ∃ e : ℝ, (¬∃ z : ℤ, e=z) ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h ≠ 0 ∧ tensorK 2 ((9*s+5 : ℤ) : ℝ) ((9*t+8 : ℤ) : ℝ)*ᵥ h=e • h := by
  let b : ℤ := 9*s+5
  let c : ℤ := 9*t+8
  let D : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ := tensorK 2 b c+1
  let M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := symmetricK 2 b c+1
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hM : M.IsHermitian := (symmetric_hermitian 2 b c).add (by simp)
  have hcharR : D.charpoly.map (Int.castRingHom ℝ)=M.charpoly := by
    rw [← Matrix.charpoly_map,show D.map (Int.castRingHom ℝ)=tensorK 2 (b : ℝ) (c : ℝ)+1
      from shifted_tensor_map (R := ℝ) b c]
    simpa [M] using (tensor_symmetric_charpoly 2 (b : ℝ) (c : ℝ) (-1) hbR hcR).symm
  have hchar3 : D.charpoly.map (Int.castRingHom (ZMod 3))=X^4 := by
    rw [← Matrix.charpoly_map,show D.map (Int.castRingHom (ZMod 3))=
      tensorK 2 (b : ZMod 3) (c : ZMod 3)+1 from
        shifted_tensor_map (R := ZMod 3) b c]
    have h9 : (9 : ZMod 3)=0 := by decide
    have hb3 : (b : ZMod 3)+1=0 := by
      simp only [b,Int.cast_add,Int.cast_mul,Int.cast_ofNat,h9,zero_mul,zero_add]
      decide
    have hc3 : (c : ZMod 3)+1=0 := by
      simp only [c,Int.cast_add,Int.cast_mul,Int.cast_ofNat,h9,zero_mul,zero_add]
      decide
    exact sub_eq_zero.mp (shifted_tensor_charpoly_mod_three
      (b : ZMod 3) (c : ZMod 3) (by simp [hb3]) (by simp [hc3])).eq_zero
  have hex : ∃ i, ¬∃ z : ℤ, hM.eigenvalues i=z := by
    by_contra! hall
    choose z hz using hall
    have hroot (i : Fin 2 × Fin 2) : D.charpoly.eval (z i)=0 := by
      apply Int.cast_injective (α := ℝ)
      have he : M.charpoly.eval (z i : ℝ)=0 := by
        rw [hM.charpoly_eq]
        simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
        apply Finset.prod_eq_zero (mem_univ i)
        simpa using sub_eq_zero.mpr (hz i).symm
      have hh := congrArg (fun p : ℝ[X] => p.eval (z i : ℝ)) hcharR
      have hp : (D.charpoly.map (Int.castRingHom ℝ)).eval
          ((Int.castRingHom ℝ) (z i)) = (Int.castRingHom ℝ) (D.charpoly.eval (z i)) :=
        Polynomial.eval_map_apply (Int.castRingHom ℝ) (z i)
      have hzero : (Int.castRingHom ℝ) (D.charpoly.eval (z i))=0 :=
        hp.symm.trans (hh.trans he)
      simpa using hzero
    have hdiv (i : Fin 2 × Fin 2) : (3 : ℤ) ∣ z i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (z i) 3).mp
      have he : (D.charpoly.map (Int.castRingHom (ZMod 3))).eval (z i : ZMod 3)=0 := by
        change (D.charpoly.map (Int.castRingHom (ZMod 3))).eval
          ((Int.castRingHom (ZMod 3)) (z i))=0
        rw [Polynomial.eval_map_apply,hroot,map_zero]
      rw [hchar3] at he
      apply eq_zero_of_pow_eq_zero (n := 4)
      simpa only [Polynomial.eval_pow,Polynomial.eval_X] using he
    have hdet : D.det=∏ i,z i := by
      apply Int.cast_injective (α := ℝ)
      have he := hM.det_eq_prod_eigenvalues
      have hd : M.det=(D.det : ℝ) := by
        rw [show M=symmetricK 2 (b : ℝ) (c : ℝ)-(-1 : ℝ) • 1 by simp [M],
          tensor_symmetric_det_shift 2 (b : ℝ) (c : ℝ) (-1) hbR hcR]
        simp only [neg_smul,one_smul,sub_neg_eq_add]
        rw [← shifted_tensor_map (R := ℝ) b c]
        exact (RingHom.map_det (Int.castRingHom ℝ) D).symm
      rw [hd] at he
      simpa [hz,Int.cast_prod] using he
    have h81 : (81 : ℤ) ∣ D.det := by
      rw [hdet]
      have he : (∏ _i : Fin 2 × Fin 2, (3 : ℤ)) ∣ ∏ i, z i :=
        Finset.prod_dvd_prod_of_dvd (fun _ => (3 : ℤ)) z (fun i _ => hdiv i)
      simpa using he
    exact shifted_tensor_det_not_dvd s t (dvd_trans (by norm_num : (27 : ℤ) ∣ 81) h81)
  obtain ⟨i,hi⟩ := hex
  let v : Fin 2 × Fin 2 → ℝ := hM.eigenvectorBasis i
  have hv : v ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hM.eigenvectorBasis.orthonormal.ne_zero i)
  have heM := hM.mulVec_eigenvectorBasis i
  have heS : symmetricK 2 (b : ℝ) (c : ℝ)*ᵥ v=(hM.eigenvalues i-1) • v := by
    change (symmetricK 2 (b : ℝ) (c : ℝ)+1)*ᵥ v=hM.eigenvalues i • v at heM
    rw [add_mulVec,one_mulVec] at heM
    ext q
    have hh := congrFun heM q
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hh ⊢
    linarith
  obtain ⟨h,hh,hhe⟩ := tensor_eigenpair_of_symmetric 2 (b : ℝ) (c : ℝ)
    hbR hcR (hM.eigenvalues i-1) v hv heS
  refine ⟨hM.eigenvalues i-1,?_,h,hh,?_⟩
  · rintro ⟨z,hz⟩
    apply hi
    refine ⟨z+1,?_⟩
    push_cast
    linarith
  · exact hhe

end D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionCongruence
