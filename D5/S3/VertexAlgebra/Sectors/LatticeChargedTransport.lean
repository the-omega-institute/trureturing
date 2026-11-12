/-
Source candidate only: no compiler, elaborator, or native acceptance run.
The exact imported transport has independent final native acceptance; its
inherited source-only comment does not supersede the pinned final receipt.
The generic full-intertwiner import is an uncompiled source dependency.
All carriers, cocycles, Gram matrices and rational offsets below are literal.
Classical conventions: Bakalov--Kac math/0402315v1, section 4.1;
imported Hahn/residue and conformal work retain Carnahan/Kytölä attribution.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleFullIntertwiner
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeChargedTransport
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeDiscriminantTheta LatticeActualGeneratorLocality
open LatticeDualCosetTransport
open scoped BigOperators VertexOperator Matrix
noncomputable section


open private rat_unit pairRaw_add_left
  pairRaw_add_right pairRaw_gram_left pairRaw_gram_right integral_dot_gram
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private shift_pair from D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws
open private compressedField_modes from
  D5.S3.VertexAlgebra.Sectors.LatticeCosetInnerExpansion
open private injection_single projection_single
  from D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

/-- The literal cross-block character, with integral rather than reduced dot. -/
def chi (D : LatticeData) (a n : Charge D) : ℂ := paritySign (a ⬝ᵥ n)

private theorem sign_nonzero (k : ℤ) : paritySign k ≠ 0 := by
  unfold paritySign
  split_ifs <;> norm_num

theorem chi_nonzero (D : LatticeData) (a n : Charge D) : chi D a n ≠ 0 :=
  sign_nonzero _

theorem epsilon_nonzero (D : LatticeData) (a n : Charge D) : epsilon D a n ≠ 0 :=
  sign_nonzero _

/-- Order is epsilon(p,r) for T_r after T_p; beta is absent from the raw map. -/
theorem transport_comp (D : LatticeData) (a b p r : Charge D) :
    (transport D b r).comp (transport D a p) =
      epsilon D p r • transport D (a+b) (p+r) := by
  apply Finsupp.lhom_ext
  intro l v
  simp only [LinearMap.comp_apply, transport_single, map_smul,
    LinearMap.smul_apply, smul_smul]
  rw [show epsilon D l p * epsilon D (l+p) r =
      epsilon D p r * epsilon D l (p+r) by
    simpa only [mul_comm] using (epsilon_ordered D l p r).symm]
  simp only [add_assoc]

/-- Transport is an actual full module morphism, on every original mode. -/
def transportHom (D : LatticeData) (a n : Charge D) :
    Modules.FullJacobiIntertwiner.ModuleHom
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (shiftedCharge D a n)) (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D a) where
  linearMap := transport D a n
  intertwines h j v := transport_all_modes D a n h v j

private theorem shifted_add (D : LatticeData) (a b n m : Charge D) :
    shiftedCharge D a n + shiftedCharge D b m =
      shiftedCharge D (a+b) (n+m) := by
  simp only [shiftedCharge, Matrix.mulVec_add]
  abel

private def inverseSumHom (D : LatticeData) (a b n m : Charge D) :
    Modules.FullJacobiIntertwiner.ModuleHom (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (a+b))
      (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (shiftedCharge D a n + shiftedCharge D b m)) where
  linearMap := transportInverse D (a+b) (n+m)
  intertwines h j v := by
    rw [shifted_add]
    exact transportInverse_all_modes D (a+b) (n+m) h v j

/-- Lawful first, then scalar rigidity: this is the actual pulled-back field. -/
def transportedOperator (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b n m : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    LatticeDualCosetIntertwiner.operatorSpace D (shiftedCharge D a n) (shiftedCharge D b m) H :=
  Sectors.ActualWeakTargetFullIntertwiner.scalarReadback D _ _ H
    (Modules.ActualWeakModuleFullIntertwiner.sectorReadback _ _ H (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D
      (shiftedCharge D a n + shiftedCharge D b m))
      (Modules.ActualWeakModuleFullIntertwiner.map H (transportHom D a n) (transportHom D b m)
        (inverseSumHom D a b n m)
        ((Modules.ActualWeakModuleFullIntertwiner.sectorReadback a b H (Sectors.ActualWeakTargetFullIntertwiner.scalarModule D (a+b))).symm
          ((Sectors.ActualWeakTargetFullIntertwiner.scalarReadback D a b H).symm
            (LatticeDualCosetFusion.canonicalOperator D hD a b H hHG hGH)))))

/-- Every raw rational coefficient of that lawful field, on both full inputs. -/
theorem transportedOperator_coeff (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b n m : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u v : Carrier D) (q : ℚ) :
    (((transportedOperator D hD a b n m H hHG hGH).val u).coeff q v) =
      transportInverse D (a+b) (n+m)
        ((LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b (transport D a n u)).coeff q
          (transport D b m v)) := by
  change ((Modules.ActualWeakModuleFullIntertwiner.rawMap (transport D a n) (transport D b m)
    (transportInverse D (a+b) (n+m))
    (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b) u).coeff q v) = _
  exact Modules.ActualWeakModuleFullIntertwiner.rawMap_coeff _ _ _ _ u v q

/-- Both inverse-Gram equations are retained by the downstream scalar supplier. -/
private theorem dual_solves (D : LatticeData) (hD : (gramReal D).PosDef)
    (a : Charge D) :
    ∀ i, ∑ j, (D.G i j : ℚ) * dualVector D a j = (a i : ℚ) := by
  have h : gramRat D *ᵥ dualVector D a = fun i => (a i : ℚ) := by
    rw [dualVector, inverseRat, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (rat_unit D hD), Matrix.one_mulVec]
  exact congrFun h

/-- The original full rational offset, including its signed integral change. -/
theorem shift_gram (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b n m : Charge D) :
    LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (shiftedCharge D a n) (shiftedCharge D b m) =
      LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) a b +
        ((bilinear D n m + n ⬝ᵥ b + a ⬝ᵥ m : ℤ) : ℚ) := by
  simp only [shift_pair, Matrix.one_mulVec]
  change pairRaw D (b + gramMap D m) (a + gramMap D n) = _
  rw [pairRaw_add_left, pairRaw_add_right, pairRaw_add_right,
    pairRaw_gram_left D hD, pairRaw_gram_left D hD,
    pairRaw_gram_right D hD, integral_dot_gram]
  rw [dotProduct_comm m a, bilinear_symmetric D m n]
  push_cast
  ring

private theorem ambient_pair (D : LatticeData) (a b n m : Charge D) :
    bilinear (LatticeCosetCompression.ambient D D.rank (1 : Matrix _ _ ℤ) 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven)
      (LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven a n)
      (LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven b m) =
      bilinear D n m + n ⬝ᵥ b + a ⬝ᵥ m := by
  simp [bilinear, Fin.sum_univ_add, LatticeCosetCompression.ambient, LatticeCosetCompression.liftCharge,
    Matrix.one_apply, dotProduct, Finset.sum_add_distrib, Fin.addCases] <;> abel

/-- Old coordinates precede external coordinates in the ORIGINAL cocycle. -/
private theorem ambient_sign (D : LatticeData) (a b n m : Charge D) :
    epsilon (LatticeCosetCompression.ambient D D.rank (1 : Matrix _ _ ℤ) 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven)
      (LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven a n)
      (LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven b m) =
      epsilon D n m * chi D a m := by
  let E := LatticeCosetCompression.ambient D D.rank (1 : Matrix _ _ ℤ) 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven
  have hnat (i : Fin D.rank) : i.addNat D.rank = i.natAdd D.rank := by
    apply Fin.ext
    change i.val + D.rank = D.rank + i.val
    omega
  have hoo (i j : Fin D.rank) : LatticeTwistedGroundRealization.SignQuotient.lowerMatrix E (i.castAdd D.rank)
      (j.castAdd D.rank) = LatticeTwistedGroundRealization.SignQuotient.lowerMatrix D i j := by
    have hlt : j.castAdd D.rank < i.castAdd D.rank ↔ j < i := by rfl
    have heq : j.castAdd D.rank = i.castAdd D.rank ↔ j = i := by
      constructor
      · intro h; apply Fin.ext; exact congrArg (fun x : Fin (D.rank+D.rank) => x.val) h
      · rintro rfl; rfl
    simp only [LatticeTwistedGroundRealization.SignQuotient.lowerMatrix, E,
      LatticeCosetCompression.ambient, Fin.addCases_left, halfDiagonal, hlt, heq]
  have hoe (i j : Fin D.rank) : LatticeTwistedGroundRealization.SignQuotient.lowerMatrix E (i.castAdd D.rank)
      (j.natAdd D.rank) = 0 := by
    have hlt : ¬ j.natAdd D.rank < i.castAdd D.rank := by simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]; omega
    have hne : j.natAdd D.rank ≠ i.castAdd D.rank := by intro h; have := congrArg Fin.val h; simp only [Fin.val_natAdd, Fin.val_castAdd] at this; omega
    simp only [LatticeTwistedGroundRealization.SignQuotient.lowerMatrix, hlt, hne,
      if_false, zero_add]
  have heo (i j : Fin D.rank) : LatticeTwistedGroundRealization.SignQuotient.lowerMatrix E (i.natAdd D.rank)
      (j.castAdd D.rank) = (1 : Matrix (Fin D.rank) (Fin D.rank) ℤ) j i := by
    have hlt : j.castAdd D.rank < i.natAdd D.rank := by simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]; omega
    have hne : j.castAdd D.rank ≠ i.natAdd D.rank := by intro h; have := congrArg Fin.val h; simp only [Fin.val_natAdd, Fin.val_castAdd] at this; omega
    simp only [LatticeTwistedGroundRealization.SignQuotient.lowerMatrix, hlt, hne,
      if_false, if_true, add_zero, E, LatticeCosetCompression.ambient,
      Fin.addCases_right, Fin.addCases_left]
  have hee (i j : Fin D.rank) : LatticeTwistedGroundRealization.SignQuotient.lowerMatrix E (i.natAdd D.rank)
      (j.natAdd D.rank) = 0 := by
    simp only [LatticeTwistedGroundRealization.SignQuotient.lowerMatrix, E,
      LatticeCosetCompression.ambient, Fin.addCases_right, halfDiagonal,
      Matrix.zero_apply, Pi.zero_apply, zero_div, ite_self, zero_add]
    norm_num
  have h : lowerCocycleExponent E (LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven a n)
      (LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven b m) =
        lowerCocycleExponent D n m + a ⬝ᵥ m := by
    rw [LatticeTwistedGroundRealization.SignQuotient.lower_matrix_formula, LatticeTwistedGroundRealization.SignQuotient.lower_matrix_formula]
    change (∑ i : Fin (D.rank + D.rank), ∑ j : Fin (D.rank + D.rank), _) = _
    simp only [Fin.sum_univ_add, LatticeCosetCompression.liftCharge, hnat, Fin.addCases_left,
      Fin.addCases_right, hoo, hoe, heo, hee, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add, Finset.sum_add_distrib]
    simp [Matrix.one_apply, dotProduct]
  change paritySign (lowerCocycleExponent E _ _) = _
  rw [h, paritySign_add]
  rfl

/-- The same native leading calculation without an unnecessary sign-of-mode premise.
The supplier actual_negative_single has a nonnegativity argument unused in its proof. -/
private theorem raw_ground_leading (D : LatticeData) (a b : Charge D) :
    ((actualField D a)[[-bilinear D a b - 1]]) (Finsupp.single b 1) =
      epsilon D a b • Finsupp.single (a+b) 1 := by
  classical
  rw [actual_modes, (actual_creation_coefficient_transport D a a).2.2.1]
  have hs : (1 : Polynomial (Oscillator D)).support = {0} := by
    simpa using Polynomial.support_C (show (1 : Oscillator D) ≠ 0 from one_ne_zero)
  simp [rawSingle, translatedPolynomial, hs, creationCoeff,
    LatticeSugawaraConformal.exponential_constant,
    show -(-bilinear D a b - 1) - 1 - bilinear D a b = 0 by omega]

/-- The actual ground coefficient fixes the scalar AFTER full lawfulness. -/
theorem canonical_shifted_ground (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b n m : Charge D) :
    (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b (LatticeDualCosetIntertwiner.ground D n)).coeff
      (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (shiftedCharge D a n) (shiftedCharge D b m))
      (LatticeDualCosetIntertwiner.ground D m) =
        (chi D a m * epsilon D n m) • LatticeDualCosetIntertwiner.ground D (n+m) := by
  rw [shift_gram D hD]
  change (LatticeCosetCanonicalIntertwiner.field D 1 a b (LatticeDualCosetIntertwiner.ground D n)).coeff _ _ = _
  rw [LatticeCosetCanonicalIntertwiner.field_coeff, VertexOperator.coeff_eq_ncoeff, compressedField_modes]
  change LatticeCosetCompression.compressed D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven a b (LatticeDualCosetIntertwiner.ground D n)
    (-(bilinear D n m + n ⬝ᵥ b + a ⬝ᵥ m)-1) (LatticeDualCosetIntertwiner.ground D m) = _
  unfold LatticeCosetCompression.compressed LatticeDualCosetIntertwiner.ground
  simp only [LinearMap.comp_apply, injection_single, map_one]
  rw [stateField_ground, ← ambient_pair, raw_ground_leading, map_smul,
    projection_single, ambient_sign]
  have he : LatticeCosetCompression.externalCharge D 1 0
      LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven
      (LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven a n +
       LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven b m) = a+b := by
    funext i
    simp only [LatticeCosetCompression.externalCharge, LatticeCosetCompression.liftCharge,
      Pi.add_apply, Fin.addCases_right]
  have ho : LatticeCosetCompression.oldCharge D 1 0
      LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven
      (LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven a n +
       LatticeCosetCompression.liftCharge D 1 0 LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven b m) = n+m := by
    funext i
    simp only [LatticeCosetCompression.oldCharge, LatticeCosetCompression.liftCharge,
      Pi.add_apply, Fin.addCases_left]
  rw [he, if_pos rfl, ho]
  simp only [map_one, mul_comm]

private theorem inverse_ground (D : LatticeData) (a n : Charge D) :
    transportInverse D a n (LatticeDualCosetIntertwiner.ground D n) = LatticeDualCosetIntertwiner.ground D 0 := by
  have h := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => f (LatticeDualCosetIntertwiner.ground D 0))
    (transportInverse_left D a n)
  simpa only [LinearMap.comp_apply, transport_vacuum, LinearMap.id_apply] using h

private theorem transported_groundEvaluation (D : LatticeData)
    (hD : (gramReal D).PosDef) (a b n m : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    LatticeDualCosetIntertwiner.groundEvaluation D
      (shiftedCharge D a n) (shiftedCharge D b m) H
      (dualVector D (shiftedCharge D a n)) (dualVector D (shiftedCharge D b m))
      (transportedOperator D hD a b n m H hHG hGH) =
        chi D a m * epsilon D n m := by
  change LatticeDualCosetIntertwiner.groundScalar D (transportedOperator D hD a b n m H hHG hGH).val
    (dualVector D (shiftedCharge D a n)) (dualVector D (shiftedCharge D b m)) 0 0 = _
  unfold LatticeDualCosetIntertwiner.groundScalar
  rw [← LatticeDualCosetFusion.shift_eq_groundPower D hD _ _ _ _
      (dual_solves D hD _) (dual_solves D hD _), transportedOperator_coeff]
  rw [transport_vacuum, transport_vacuum, canonical_shifted_ground D hD,
    map_smul, inverse_ground]
  simp [LatticeDualCosetIntertwiner.ground, MvPolynomial.constantCoeff]

/-- Original two-leg identity, ALL states and ALL raw rational coefficients.
No ground-only uniqueness principle is used: scalarEquiv consumes a lawful member. -/
theorem two_leg_coeff (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b n m : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u v : Carrier D) (q : ℚ) :
    (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b (transport D a n u)).coeff q
      (transport D b m v) =
      (chi D a m * epsilon D n m) • transport D (a+b) (n+m)
        ((LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ)
          (shiftedCharge D a n) (shiftedCharge D b m) u).coeff q v) := by
  let J := transportedOperator D hD a b n m H hHG hGH
  let E := LatticeDualCosetFusion.scalarEquiv D hD (shiftedCharge D a n) (shiftedCharge D b m)
    H hHG hGH (dualVector D (shiftedCharge D a n))
    (dualVector D (shiftedCharge D b m)) (dual_solves D hD _) (dual_solves D hD _)
  have he := E.symm_apply_apply J
  change E J • LatticeDualCosetFusion.canonicalOperator D hD _ _ H hHG hGH = J at he
  have hs : E J = chi D a m * epsilon D n m :=
    transported_groundEvaluation D hD a b n m H hHG hGH
  rw [hs] at he
  have hc : (chi D a m * epsilon D n m) •
      ((LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ)
        (shiftedCharge D a n) (shiftedCharge D b m) u).coeff q v) =
          (J.val u).coeff q v := by
    simpa [LatticeDualCosetFusion.canonicalOperator] using
      congrArg (fun Q : LatticeDualCosetIntertwiner.operatorSpace D _ _ H =>
        (Q.val u).coeff q v) he
  rw [transportedOperator_coeff] at hc
  have ht := congrArg (transport D (a+b) (n+m)) hc
  rw [map_smul] at ht
  have hi := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D =>
    f ((LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b (transport D a n u)).coeff q
      (transport D b m v))) (transportInverse_right D (a+b) (n+m))
  rw [show transport D (a+b) (n+m)
      (transportInverse D (a+b) (n+m)
        ((LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b (transport D a n u)).coeff q
          (transport D b m v))) = _ from hi] at ht
  exact ht.symm

/-- The requested rational MODE version, without changing its original index. -/
theorem two_leg_mode (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b n m : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u v : Carrier D) (τ : ℚ) :
    LatticeCosetCanonicalIntertwiner.mode D (1 : Matrix _ _ ℤ) a b (transport D a n u) τ (transport D b m v) =
      (chi D a m * epsilon D n m) • transport D (a+b) (n+m)
        (LatticeCosetCanonicalIntertwiner.mode D (1 : Matrix _ _ ℤ) (shiftedCharge D a n)
          (shiftedCharge D b m) u τ v) :=
  two_leg_coeff D hD a b n m H hHG hGH u v (-τ-1)

/-- The same identity in ORIGINAL signed integer compressed modes. The full
integer displacement is retained, including its bilinear and both dot terms. -/
theorem two_leg_integer (D : LatticeData) (hD : (gramReal D).PosDef)
    (a b n m : Charge D) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u v : Carrier D) (j : ℤ) :
    LatticeCosetCompression.compressed D (1 : Matrix _ _ ℤ) 0
      LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven
      a b (transport D a n u) j (transport D b m v) =
      (chi D a m * epsilon D n m) • transport D (a+b) (n+m)
        (LatticeCosetCompression.compressed D (1 : Matrix _ _ ℤ) 0
          LatticeCosetCanonicalIntertwiner.zeroSymm LatticeCosetCanonicalIntertwiner.zeroEven
          (shiftedCharge D a n) (shiftedCharge D b m) u
          (j + (bilinear D n m + n ⬝ᵥ b + a ⬝ᵥ m)) v) := by
  have ht := two_leg_mode D hD a b n m H hHG hGH u v
    ((j : ℚ)-LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) a b)
  rw [LatticeCosetCanonicalIntertwiner.mode_integer] at ht
  have hj : (j : ℚ)-LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) a b =
      ((j + (bilinear D n m + n ⬝ᵥ b + a ⬝ᵥ m) : ℤ) : ℚ) -
        LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
          (shiftedCharge D a n) (shiftedCharge D b m) := by
    rw [shift_gram D hD]
    push_cast
    ring
  rw [hj, LatticeCosetCanonicalIntertwiner.mode_integer] at ht
  exact ht

end
end D5.S3.VertexAlgebra.LatticeChargedTransport
