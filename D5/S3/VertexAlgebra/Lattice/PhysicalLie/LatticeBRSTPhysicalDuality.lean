/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalDuality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalDuality
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
   utility: none
   digest: Explicit inverse-Wick duality on the original opposite-charge physical fibers. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber
import D5.S3.VertexAlgebra.Lattice.LatticeSugawaraNullFrame
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Batteries.Tactic.OpenPrivate

/-!
SOURCE ONLY UNCOMPILED. Only a fixed oscillator level is finite here.
The covariance is MINUS (k+1) times the transverse Gram. Its inverse is
MINUS (k+1)^{-1} times L H L^transpose. All sums below retain a signed
level; a negative level has no occupations.

Attribution: the original source-Wick factorial/substitution construction,
the actual finite HPL suppliers, and the classical inverse-Gram Wick
calculation in the supplied completed algebraic advisory. This source is
not kernel evidence and does not complete the original string-theory goal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators TensorProduct

open private symmetric creation wick_constant_left from
  D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick
open private polynomialEquiv_symm_X completeBasis_transverse completeBasis_plus
  completeBasis_minus from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private source_a oppositeEnergyEquiv transverseFiberEquiv oppositePairing_transverse from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalDuality

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction LatticeSugawaraNullFrame
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber
open SourceBPZ.OriginalSourcePairing OriginalCurrentMetric SignedOscillatorWick
open LatticeRelativeBRSTCohomology.Ground (energyTarget)
open MvPolynomial

private abbrev Poly (t : ℕ) := MvPolynomial (Fin t × ℕ) ℂ
private abbrev Occ (t : ℕ) := (Fin t × ℕ) →₀ ℕ
private def wt {t : ℕ} (e : Occ t) : ℕ :=
  Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e
private def signedWeight {t : ℕ} (e : Occ t) : ℤ :=
  Finsupp.weight (fun x : Fin t × ℕ => (x.2 : ℤ)+1) e

private theorem signedWeight_cast {t : ℕ} (e : Occ t) :
    signedWeight e = (wt e : ℤ) := by
  simp [signedWeight,wt,Finsupp.weight_apply,Finsupp.sum,
    Nat.cast_sum,Nat.cast_mul,Nat.cast_add]

private def levelSpace (t : ℕ) (ell : ℤ) : Submodule ℂ (Poly t) :=
  weightedHomogeneousSubmodule ℂ (fun x : Fin t × ℕ => (x.2 : ℤ)+1) ell
private abbrev LevelIndex (t : ℕ) (ell : ℤ) := {e : Occ t // signedWeight e = ell}

private theorem bounded_occupations_finite (t N : ℕ) :
    Finite {e : Occ t // wt e ≤ N} := by
  classical
  let A := {e : Occ t // wt e ≤ N}
  have hindex (e : A) (i : Fin t) (k : ℕ) (hk : N ≤ k) : e.1 (i,k) = 0 := by
    by_contra hne
    have h := Finsupp.le_weight_of_ne_zero' (fun x : Fin t × ℕ => x.2+1) hne
    change k+1 ≤ wt e.1 at h
    have he := e.2
    omega
  have hexponent (e : A) (x : Fin t × ℕ) : e.1 x ≤ N := by
    have h := Finsupp.le_weight (fun y : Fin t × ℕ => y.2+1) (s := x)
      (by omega) e.1
    exact h.trans e.2
  let encode (e : A) (x : Fin t × Fin N) : Fin (N+1) :=
    ⟨e.1 (x.1,x.2),Nat.lt_succ_of_le (hexponent e _)⟩
  have hinj : Function.Injective encode := by
    intro e f h
    apply Subtype.ext
    apply Finsupp.ext
    rintro ⟨i,k⟩
    by_cases hk : k < N
    · exact congrArg Fin.val (congrFun h (i,⟨k,hk⟩))
    · rw [hindex e i k (Nat.le_of_not_lt hk),hindex f i k (Nat.le_of_not_lt hk)]
  exact Finite.of_injective encode hinj

private instance levelIndexFinite (t : ℕ) (ell : ℤ) : Finite (LevelIndex t ell) := by
  letI := bounded_occupations_finite t ell.toNat
  let enc (a : LevelIndex t ell) : {e : Occ t // wt e ≤ ell.toNat} :=
    ⟨a.val,by have h := a.property;rw [signedWeight_cast] at h;omega⟩
  exact Finite.of_injective enc (by intro a b h;exact Subtype.ext (congrArg Subtype.val h))

private instance levelIndexFintype (t : ℕ) (ell : ℤ) : Fintype (LevelIndex t ell) :=
  Fintype.ofFinite _

private def monomialAt (t : ℕ) (ell : ℤ) (a : LevelIndex t ell) : levelSpace t ell :=
  ⟨monomial a.val 1,by
    apply isWeightedHomogeneous_monomial
    exact a.property⟩

private theorem level_expansion (t : ℕ) (ell : ℤ) (f : levelSpace t ell) :
    (∑ a : LevelIndex t ell, f.val.coeff a.val • monomialAt t ell a) = f := by
  classical
  apply Subtype.ext
  ext e
  simp only [Submodule.coe_sum,Submodule.coe_smul,coeff_sum,coeff_smul]
  by_cases he : signedWeight e = ell
  · let a : LevelIndex t ell := ⟨e,he⟩
    rw [Finset.sum_eq_single a]
    · simp [a,monomialAt]
    · intro b hb hba
      have hbe : b.val ≠ e := fun h => hba (Subtype.ext h)
      simp [monomialAt,coeff_monomial,hbe]
    · simp
  · rw [f.property.coeff_eq_zero e he]
    apply Finset.sum_eq_zero
    intro a ha
    have hae : a.val ≠ e := fun h => he (h ▸ a.property)
    simp [monomialAt,coeff_monomial,hae]

private def energyLevelEquiv (D : LatticeData) (t : ℕ) (p : Charge D) :
    energyTarget D t p ≃ₗ[ℂ] levelSpace t (1-chargeEnergy D p) where
  toFun f := ⟨f.val,by
    intro e he
    change signedWeight e = 1-chargeEnergy D p
    rw [signedWeight_cast]
    have h : (LatticeRelativeBRSTCohomology.Ground.weight e : ℤ)+chargeEnergy D p=1 := by
      by_contra hn
      exact he (f.property e hn)
    change (wt e : ℤ)+chargeEnergy D p=1 at h
    omega⟩
  invFun f := ⟨f.val,by
    intro e he
    apply f.property.coeff_eq_zero e
    change signedWeight e ≠ 1-chargeEnergy D p
    rw [signedWeight_cast]
    change (wt e : ℤ)+chargeEnergy D p ≠ 1 at he
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem substitution_preserves (t : ℕ) (ell : ℤ)
    (A : ℕ → Matrix (Fin t) (Fin t) ℂ) (P : Poly t)
    (hP : P ∈ levelSpace t ell) : substitution A P ∈ levelSpace t ell := by
  classical
  have hgen (x : Fin t × ℕ) :
      IsWeightedHomogeneous (fun y : Fin t × ℕ => (y.2 : ℤ)+1)
        (variableImage A x) ((x.2 : ℤ)+1) := by
    apply IsWeightedHomogeneous.sum
    intro j hj
    exact (weightedHomogeneousSubmodule ℂ _ _).smul_mem _
      (isWeightedHomogeneous_X ℂ _ (j,x.2))
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero ℂ
      (fun y : Fin t × ℕ => (y.2 : ℤ)+1) ell
  | add P Q hP hQ ihP ihQ => simpa only [map_add] using ihP.add ihQ
  | monomial e c he =>
      rw [substitution,MvPolynomial.aeval_monomial]
      have h := IsWeightedHomogeneous.prod e.support
        (fun x => variableImage A x ^ e x)
        (fun x => e x • ((x.2 : ℤ)+1)) (fun x hx => (hgen x).pow (e x))
      have hw : (∑ x ∈ e.support, e x • ((x.2 : ℤ)+1)) = ell := by
        simpa only [Finsupp.weight_apply,Finsupp.sum] using he
      rw [hw] at h
      exact h.C_mul c

private def levelSubstitution (t : ℕ) (ell : ℤ)
    (A : ℕ → Matrix (Fin t) (Fin t) ℂ) :
    levelSpace t ell →ₗ[ℂ] levelSpace t ell where
  toFun f := ⟨substitution A f.val,substitution_preserves t ell A f.val f.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/- Explicit E and L in standard coordinates. No inverse of an integer matrix
or signature assumption occurs. -/
section TransverseMatrices
variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
  (B : Module.Basis (Fin t) ℂ F.K)

private def columns : Matrix (Fin D.rank) (Label t) ℂ :=
  fun i c => F.completeBasis B c i
private def rows : Matrix (Label t) (Fin D.rank) ℂ :=
  fun c i => (F.completeBasis B).repr (standardBasis D i) c
private def transverseGram : Matrix (Fin t) (Fin t) ℂ :=
  fun a b => g D (B a : E D) (B b : E D)
private def transverseInverse (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Matrix (Fin t) (Fin t) ℂ :=
  fun a b => frameCoeff F B H (transverse t a) (transverse t b)

private theorem columns_rows : columns F B * rows F B = 1 := by
  classical
  ext i j
  have h := congrFun ((F.completeBasis B).sum_repr (standardBasis D j)) i
  simpa only [columns,rows,Matrix.mul_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,mul_comm,standardBasis,Pi.basisFun_apply,Matrix.one_apply,eq_comm] using h

private theorem rows_columns : rows F B * columns F B = 1 := by
  classical
  ext c d
  have h := congrArg ((F.completeBasis B).coord c)
    ((standardBasis D).sum_repr (F.completeBasis B d))
  simpa only [rows,columns,Matrix.mul_apply,map_sum,map_smul,smul_eq_mul,
    Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,
    Matrix.one_apply,eq_comm,mul_comm] using h

private theorem full_gram_entry (c d : Label t) :
    ((columns F B).transpose * gramComplex D * columns F B) c d =
      g D (F.completeBasis B c) (F.completeBasis B d) := by
  classical
  simp only [Matrix.mul_apply,Matrix.transpose_apply,columns,g,gramComplex,
    Matrix.map_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem full_inverse_entry (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (c d : Label t) :
    (rows F B * H * (rows F B).transpose) c d = frameCoeff F B H c d := by
  classical
  simp only [Matrix.mul_apply,Matrix.transpose_apply,rows,frameCoeff,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem transverse_right_inverse (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hGH : gramComplex D * H = 1) :
    transverseGram F B * transverseInverse F B H = 1 := by
  classical
  have hfull : ((columns F B).transpose * gramComplex D * columns F B) *
      (rows F B * H * (rows F B).transpose) = 1 := by
    calc
      _ = (columns F B).transpose * gramComplex D *
          (columns F B * rows F B) * H * (rows F B).transpose := by
        simp only [Matrix.mul_assoc]
      _ = (columns F B).transpose * (gramComplex D * H) * (rows F B).transpose := by
        rw [columns_rows,Matrix.mul_one];simp only [Matrix.mul_assoc]
      _ = (rows F B * columns F B).transpose := by
        rw [hGH,Matrix.mul_one,Matrix.transpose_mul]
      _ = 1 := by rw [rows_columns,Matrix.transpose_one]
  ext a b
  have h := congrArg (fun M => M (transverse t a) (transverse t b)) hfull
  rw [Matrix.mul_apply] at h
  simp only [full_gram_entry,full_inverse_entry,
    Fintype.sum_sum_type,Fintype.sum_unique,completeBasis_transverse,
    completeBasis_plus,completeBasis_minus,K_plus,K_minus,zero_mul,zero_add,
    Matrix.one_apply,transverse,Sum.inr.injEq,ite_true] at h
  simpa only [Matrix.mul_apply,transverseGram,transverseInverse,
    Matrix.one_apply] using h

private theorem transverse_left_inverse (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) :
    transverseInverse F B H * transverseGram F B = 1 := by
  classical
  have hfull : (rows F B * H * (rows F B).transpose) *
      ((columns F B).transpose * gramComplex D * columns F B) = 1 := by
    calc
      _ = rows F B * H * (columns F B * rows F B).transpose *
          gramComplex D * columns F B := by
        rw [Matrix.transpose_mul];simp only [Matrix.mul_assoc]
      _ = rows F B * (H * gramComplex D) * columns F B := by
        rw [columns_rows,Matrix.transpose_one,Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHG,Matrix.mul_one,rows_columns]
  ext a b
  have h := congrArg (fun M => M (transverse t a) (transverse t b)) hfull
  rw [Matrix.mul_apply] at h
  simp only [full_gram_entry,full_inverse_entry,
    Fintype.sum_sum_type,Fintype.sum_unique,completeBasis_transverse,
    completeBasis_plus,completeBasis_minus,plus_K,minus_K,zero_mul,mul_zero,zero_add,
    add_zero,Matrix.one_apply,transverse,Sum.inr.injEq,ite_true] at h
  simpa only [Matrix.mul_apply,transverseGram,transverseInverse,
    Matrix.one_apply] using h

private def covariance (k : ℕ) : Matrix (Fin t) (Fin t) ℂ :=
  (-((k : ℂ)+1)) • transverseGram F B
private def inverseCovariance (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (k : ℕ) :
    Matrix (Fin t) (Fin t) ℂ :=
  (-((k : ℂ)+1))⁻¹ • transverseInverse F B H

private theorem frequency_ne_zero (k : ℕ) : -((k : ℂ)+1) ≠ 0 := by
  apply neg_ne_zero.mpr
  exact_mod_cast (show k+1 ≠ 0 by omega)

private theorem covariance_mul_inverse (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hGH : gramComplex D * H = 1) (k : ℕ) :
    covariance F B k * inverseCovariance F B H k = 1 := by
  rw [covariance,inverseCovariance,smul_mul_assoc,mul_smul_comm,smul_smul,
    mul_inv_cancel₀ (frequency_ne_zero k),one_smul,transverse_right_inverse F B H hGH]

private theorem inverse_mul_covariance (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (k : ℕ) :
    inverseCovariance F B H k * covariance F B k = 1 := by
  rw [covariance,inverseCovariance,smul_mul_assoc,mul_smul_comm,smul_smul,
    inv_mul_cancel₀ (frequency_ne_zero k),one_smul,transverse_left_inverse F B H hHG]

end TransverseMatrices

section ActualTransverseWick
variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
  (B : Module.Basis (Fin t) ℂ F.K)

private theorem transverse_X (j : Fin t) (r : ℕ) :
    transverseOriginal F B (X (j,r)) = lin r (B j : E D) := by
  simp only [transverseOriginal,AlgHom.comp_apply,rename_X,
    AlgEquiv.toAlgHom_eq_coe,AlgEquiv.coe_algHom,transverseVariable]
  exact (polynomialEquiv_symm_X (F.completeBasis B) (transverse t j) r).trans
    (congrArg (lin r) (completeBasis_transverse F B j))

private theorem transverse_constant (Q : Poly t) :
    (transverseOriginal F B Q).coeff 0 = Q.coeff 0 := by
  change constantCoeff (transverseOriginal F B Q) = constantCoeff Q
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X Q x hQ =>
      rcases x with ⟨j,r⟩
      rw [map_mul,transverse_X]
      simp [lin]

private def transverseDerivative (a : Fin t) (r : ℕ) : Derivation ℂ (Poly t) (Poly t) :=
  ∑ b : Fin t, transverseGram F B a b • pderiv (b,r)

private theorem transverseDerivative_X (a b : Fin t) (r s : ℕ) :
    transverseDerivative F B a r (X (b,s)) =
      if r=s then transverseGram F B a b • (1 : Poly t) else 0 := by
  classical
  by_cases hrs : r=s
  · subst s
    simp [transverseDerivative,pderiv_X,Prod.mk.injEq]
  · simp [transverseDerivative,pderiv_X,Prod.mk.injEq,hrs]

private theorem transverseDerivative_transport (a : Fin t) (r : ℕ) (Q : Poly t) :
    oldDerivative (B a : E D) r (transverseOriginal F B Q) =
      transverseOriginal F B (transverseDerivative F B a r Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X Q x hQ =>
      rcases x with ⟨b,s⟩
      have hx : oldDerivative (B a : E D) r (transverseOriginal F B (X (b,s))) =
          transverseOriginal F B (transverseDerivative F B a r (X (b,s))) := by
        rw [transverse_X,oldDerivative_lin,transverseDerivative_X]
        split_ifs <;> simp [transverseGram]
      simp only [map_mul,Derivation.leibniz,smul_eq_mul,map_add,hQ,hx]

private theorem integerWick_lin (u : E D) (r : ℕ) (P Q : Oscillator D) :
    integerWick D (lin r u * P) Q =
      integerWick D P (-((r : ℂ)+1) • oldDerivative u r Q) := by
  have h := source_a (D := D) u (-(r : ℤ)-1)
    (Finsupp.single (0 : Charge D) P) (Finsupp.single (0 : Charge D) Q)
  rw [a_single,polynomialCurrent_negative,a_single,
    show -(-(r : ℤ)-1)=(r : ℤ)+1 by ring,polynomialCurrent_positive] at h
  simpa only [sourcePairing_single_single,neg_zero,if_pos rfl,map_smul,
    LinearMap.smul_apply,smul_eq_mul,neg_mul] using h

private theorem factorial_variable (A : ℕ → Matrix (Fin t) (Fin t) ℂ)
    (a : Fin t) (r : ℕ) (P Q : Poly t) :
    FactorialBilinear.form (Fin t × ℕ) (variableImage A (a,r) * P) Q =
      FactorialBilinear.form (Fin t × ℕ) P (lowering A a r Q) := by
  classical
  simp only [variableImage,Finset.sum_mul,smul_mul_assoc,map_sum,
    LinearMap.sum_apply,map_smul,LinearMap.smul_apply,creation,
    lowering_apply,map_sum,map_smul,smul_eq_mul]

private theorem covariance_lowering (a : Fin t) (r : ℕ) (Q : Poly t) :
    lowering (covariance F B) a r Q =
      -((r : ℂ)+1) • transverseDerivative F B a r Q := by
  classical
  have hs (b : Fin t) : transverseGram F B b a = transverseGram F B a b :=
    g_symm D (B b : E D) (B a : E D)
  simp [lowering_apply,covariance,transverseDerivative,hs,
    Finset.smul_sum,smul_smul]

/-- Restriction is proved from the actual creation recurrence. -/
private theorem transverse_wick (P Q : Poly t) :
    integerWick D (transverseOriginal F B P) (transverseOriginal F B Q) =
      FactorialBilinear.form (Fin t × ℕ) (substitution (covariance F B) P) Q := by
  classical
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
      have hc : integerWick D (C c) (transverseOriginal F B Q) = c * Q.coeff 0 := by
        change wick D (retune D (C c)) (transverseOriginal F B Q) = _
        have hC : retune D (C c) = C c := by simp
        rw [hC,wick_constant_left,transverse_constant]
      have hphi : transverseOriginal F B (C c) = C c := by simp
      have hsub : substitution (covariance F B) (C c) = C c := by simp
      rw [hphi,hsub,hc]
      simpa [FactorialFockMetric.weight] using
        (FactorialBilinear.monomial_left (0 : Occ t) c Q).symm
  | add P R hP hR =>
      simp only [map_add,LinearMap.add_apply,hP,hR]
  | mul_X P x hP =>
      rcases x with ⟨a,r⟩
      simp only [mul_comm P (X (a,r))]
      rw [map_mul,transverse_X,integerWick_lin,
        transverseDerivative_transport,← map_smul,hP,map_mul]
      rw [show substitution (covariance F B) (X (a,r)) =
        variableImage (covariance F B) (a,r) from MvPolynomial.aeval_X _ _]
      rw [factorial_variable,covariance_lowering]

end ActualTransverseWick

/- The two finite contractions. The second proof expands S_A f and then
applies S_T; it does not infer surjectivity from dimension or nondegeneracy. -/
section FiniteInverse
variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
  (B : Module.Basis (Fin t) ℂ F.K)
  (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
  (ell : ℤ)

private def levelWick : levelSpace t ell →ₗ[ℂ] Module.Dual ℂ (levelSpace t ell) where
  toFun f := (FactorialBilinear.form (Fin t × ℕ)
    (substitution (covariance F B) f.val)).comp (levelSpace t ell).subtype
  map_add' f g := by ext h;simp only [map_add,LinearMap.add_apply]
  map_smul' c f := by ext h;simp only [map_smul,LinearMap.smul_apply]

private def inverseWickMonomial (a : LevelIndex t ell) : levelSpace t ell :=
  (FactorialFockMetric.weight a.val : ℂ)⁻¹ •
    levelSubstitution t ell (inverseCovariance F B H) (monomialAt t ell a)

private theorem factorial_ne_zero (a : Occ t) :
    (FactorialFockMetric.weight a : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (FactorialFockMetric.weight_pos a))

private theorem inverseWickMonomial_left {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hGH : gramComplex D * H = 1) (ell : ℤ)
    (a : LevelIndex t ell) (f : levelSpace t ell) :
    levelWick F B ell (inverseWickMonomial F B H ell a) f = f.val.coeff a.val := by
  have hinv (P : Poly t) : substitution (covariance F B)
      (substitution (inverseCovariance F B H) P) = P :=
    AlgHom.congr_fun (substitution_inverse _ _ (covariance_mul_inverse F B H hGH)) P
  change FactorialBilinear.form (Fin t × ℕ)
    (substitution (covariance F B)
      ((FactorialFockMetric.weight a.val : ℂ)⁻¹ •
        substitution (inverseCovariance F B H) (monomial a.val 1))) f.val = _
  rw [map_smul,hinv,map_smul,LinearMap.smul_apply,
    FactorialBilinear.monomial_left,mul_one,smul_eq_mul,
    ← mul_assoc,inv_mul_cancel₀ (factorial_ne_zero a.val),one_mul]

private def levelInverse : Module.Dual ℂ (levelSpace t ell) →ₗ[ℂ] levelSpace t ell where
  toFun lam := ∑ a : LevelIndex t ell,
    lam (monomialAt t ell a) • inverseWickMonomial F B H ell a
  map_add' lam mu := by
    simp only [LinearMap.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c lam := by
    simp only [LinearMap.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

private theorem level_forward_inverse {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hGH : gramComplex D * H = 1) (ell : ℤ)
    (lam : Module.Dual ℂ (levelSpace t ell)) :
    levelWick F B ell (levelInverse F B H ell lam) = lam := by
  ext f
  change levelWick F B ell
    (∑ a : LevelIndex t ell,
      lam (monomialAt t ell a) • inverseWickMonomial F B H ell a) f = lam f
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
    inverseWickMonomial_left F B H hGH ell,smul_eq_mul]
  have h := congrArg lam (level_expansion t ell f)
  rw [map_sum] at h
  simp only [map_smul,smul_eq_mul] at h
  simpa only [mul_comm] using h

private theorem level_inverse_forward {D : LatticeData} (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (ell : ℤ) (f : levelSpace t ell) :
    levelInverse F B H ell (levelWick F B ell f) = f := by
  let Af : levelSpace t ell := levelSubstitution t ell (covariance F B) f
  have hcoeff (a : LevelIndex t ell) :
      levelWick F B ell f (monomialAt t ell a) =
        (FactorialFockMetric.weight a.val : ℂ) * Af.val.coeff a.val := by
    change FactorialBilinear.form _ Af.val (monomial a.val 1) = _
    rw [symmetric,FactorialBilinear.monomial_left,mul_one]
  have h : levelInverse F B H ell (levelWick F B ell f) =
      levelSubstitution t ell (inverseCovariance F B H)
        (∑ a : LevelIndex t ell, Af.val.coeff a.val • monomialAt t ell a) := by
    change (∑ a : LevelIndex t ell,
      levelWick F B ell f (monomialAt t ell a) •
        ((FactorialFockMetric.weight a.val : ℂ)⁻¹ •
          levelSubstitution t ell (inverseCovariance F B H) (monomialAt t ell a))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [map_smul,hcoeff,smul_smul]
    congr 1
    calc
      ((FactorialFockMetric.weight a.val : ℂ) * Af.val.coeff a.val) *
          (FactorialFockMetric.weight a.val : ℂ)⁻¹ =
          ((FactorialFockMetric.weight a.val : ℂ) *
            (FactorialFockMetric.weight a.val : ℂ)⁻¹) * Af.val.coeff a.val := by ring
      _ = _ := by rw [mul_inv_cancel₀ (factorial_ne_zero a.val),one_mul]
  rw [h,level_expansion]
  apply Subtype.ext
  exact AlgHom.congr_fun
    (substitution_inverse _ _ (inverse_mul_covariance F B H hHG)) f.val

end FiniteInverse

section OriginalPhysicalFibers

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1) (p : Charge D) (hp : p ≠ 0)

private def chosenFrame (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (p : Charge D) (hp : p ≠ 0) :
    NullFrame D := Classical.choose
  (LatticeNullFrameExistence.exists_nullFrame_pPlus_ne_zero D H hHG (by omega) p hp)

private theorem chosenFrame_plus : (chosenFrame D H h26 hHG p hp).pPlus p ≠ 0 :=
  Classical.choose_spec
    (LatticeNullFrameExistence.exists_nullFrame_pPlus_ne_zero D H hHG (by omega) p hp)

private theorem chosenFrame_minus : (chosenFrame D H h26 hHG p hp).pPlus (-p) ≠ 0 := by
  have he : (chosenFrame D H h26 hHG p hp).pPlus (-p) =
      -(chosenFrame D H h26 hHG p hp).pPlus p := by
    simp [pPlus,chargeVector,g,mul_neg,Finset.sum_neg_distrib]
  rw [he]
  exact neg_ne_zero.mpr (chosenFrame_plus D H h26 hHG p hp)

private def leftCoordinates :
    levelSpace (D.rank-2) (1-chargeEnergy D p) ≃ₗ[ℂ]
      physicalChargeFiber D H h26 hHG hGH p :=
  (energyLevelEquiv D (D.rank-2) p).symm.trans
    (transverseFiberEquiv D H h26 hHG hGH (chosenFrame D H h26 hHG p hp)
      (chosenFrame D H h26 hHG p hp).transverseBasis p
      (chosenFrame_plus D H h26 hHG p hp))

private def rightCoordinates :
    levelSpace (D.rank-2) (1-chargeEnergy D p) ≃ₗ[ℂ]
      physicalChargeFiber D H h26 hHG hGH (-p) :=
  (energyLevelEquiv D (D.rank-2) p).symm.trans
    ((oppositeEnergyEquiv D p).trans
      (transverseFiberEquiv D H h26 hHG hGH (chosenFrame D H h26 hHG p hp)
        (chosenFrame D H h26 hHG p hp).transverseBasis (-p)
        (chosenFrame_minus D H h26 hHG p hp)))

private theorem forward_coordinates
    (f g : levelSpace (D.rank-2) (1-chargeEnergy D p)) :
    oppositePairing D H h26 hHG hGH p
      (leftCoordinates D H h26 hHG hGH p hp f)
      (rightCoordinates D H h26 hHG hGH p hp g) =
    levelWick (chosenFrame D H h26 hHG p hp)
      (chosenFrame D H h26 hHG p hp).transverseBasis (1-chargeEnergy D p) f g := by
  change oppositePairing D H h26 hHG hGH p
    (transverseFiberEquiv D H h26 hHG hGH (chosenFrame D H h26 hHG p hp)
      (chosenFrame D H h26 hHG p hp).transverseBasis p
      (chosenFrame_plus D H h26 hHG p hp) ((energyLevelEquiv D (D.rank-2) p).symm f))
    (transverseFiberEquiv D H h26 hHG hGH (chosenFrame D H h26 hHG p hp)
      (chosenFrame D H h26 hHG p hp).transverseBasis (-p)
      (chosenFrame_minus D H h26 hHG p hp)
      (oppositeEnergyEquiv D p ((energyLevelEquiv D (D.rank-2) p).symm g))) = _
  rw [oppositePairing_transverse]
  exact transverse_wick (chosenFrame D H h26 hHG p hp)
    (chosenFrame D H h26 hHG p hp).transverseBasis f.val g.val

/-- An explicit COMPLEX-LINEAR inverse. Expanded, it is E_p of the finite
sum over exactly wt(alpha)=1-chargeEnergy p of
lambda(E_(-p) X^alpha) times
( product alpha! )^{-1} S_{-(k+1)^{-1} L H L^transpose}(X^alpha).
There is no choice of a dual preimage or dimension-based surjectivity step. -/
def nonzeroChargeDualInverse :
    Module.Dual ℂ (physicalChargeFiber D H h26 hHG hGH (-p)) →ₗ[ℂ]
      physicalChargeFiber D H h26 hHG hGH p :=
  (leftCoordinates D H h26 hHG hGH p hp).toLinearMap.comp
    ((levelInverse (chosenFrame D H h26 hHG p hp)
      (chosenFrame D H h26 hHG p hp).transverseBasis H (1-chargeEnergy D p)).comp
      { toFun := fun lam => lam.comp (rightCoordinates D H h26 hHG hGH p hp).toLinearMap
        map_add' := by intros;ext f;rfl
        map_smul' := by intros;ext f;rfl })

private theorem physical_forward_inverse
    (lam : Module.Dual ℂ (physicalChargeFiber D H h26 hHG hGH (-p))) :
    oppositePairing D H h26 hHG hGH p
      (nonzeroChargeDualInverse D H h26 hHG hGH p hp lam) = lam := by
  let Ep := leftCoordinates D H h26 hHG hGH p hp
  let Em := rightCoordinates D H h26 hHG hGH p hp
  let mu := lam.comp Em.toLinearMap
  ext y
  obtain ⟨g,rfl⟩ := Em.surjective y
  change oppositePairing D H h26 hHG hGH p
    (Ep (levelInverse (chosenFrame D H h26 hHG p hp)
      (chosenFrame D H h26 hHG p hp).transverseBasis H (1-chargeEnergy D p) mu))
    (Em g) = lam (Em g)
  rw [forward_coordinates]
  exact LinearMap.congr_fun
    (level_forward_inverse (chosenFrame D H h26 hHG p hp)
      (chosenFrame D H h26 hHG p hp).transverseBasis H hGH (1-chargeEnergy D p) mu) g

private theorem physical_inverse_forward (x : physicalChargeFiber D H h26 hHG hGH p) :
    nonzeroChargeDualInverse D H h26 hHG hGH p hp
      (oppositePairing D H h26 hHG hGH p x) = x := by
  let Ep := leftCoordinates D H h26 hHG hGH p hp
  let Em := rightCoordinates D H h26 hHG hGH p hp
  obtain ⟨f,rfl⟩ := Ep.surjective x
  have hmu : (oppositePairing D H h26 hHG hGH p (Ep f)).comp Em.toLinearMap =
      levelWick (chosenFrame D H h26 hHG p hp)
        (chosenFrame D H h26 hHG p hp).transverseBasis (1-chargeEnergy D p) f := by
    ext g
    exact forward_coordinates D H h26 hHG hGH p hp f g
  change Ep (levelInverse (chosenFrame D H h26 hHG p hp)
    (chosenFrame D H h26 hHG p hp).transverseBasis H (1-chargeEnergy D p)
    ((oppositePairing D H h26 hHG hGH p (Ep f)).comp Em.toLinearMap)) = Ep f
  rw [hmu,level_inverse_forward (chosenFrame D H h26 hHG p hp)
    (chosenFrame D H h26 hHG p hp).transverseBasis H hHG]

/-- Algebraic perfectness of the ACTUAL opposite-charge physical pairing,
with its explicit inverse, for EVERY nonzero original charge. The forward
map is definitionally the restriction of the actual globalB to the literal
physical image inside original Cohomology. The quotient and bracket have
not been replaced. No finite-dimensional, real-frame, signature, positivity,
integer-unimodularity, or perfectness assumption is an input. -/
def nonzeroChargeDuality :
    physicalChargeFiber D H h26 hHG hGH p ≃ₗ[ℂ]
      Module.Dual ℂ (physicalChargeFiber D H h26 hHG hGH (-p)) where
  toLinearMap := oppositePairing D H h26 hHG hGH p
  invFun := nonzeroChargeDualInverse D H h26 hHG hGH p hp
  left_inv := physical_inverse_forward D H h26 hHG hGH p hp
  right_inv := physical_forward_inverse D H h26 hHG hGH p hp

end OriginalPhysicalFibers
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalDuality
