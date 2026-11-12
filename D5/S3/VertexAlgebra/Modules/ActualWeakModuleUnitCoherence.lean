/-
SOURCE ONLY / UNCOMPILED / UNACCEPTED.
Coherence of the ORIGINAL arbitrary-weak-module product and its returned units.
The literal Quotient.out section, both inverse transport factors, original full
states, integer modes, rational Hahn exponents and independent universes remain.
No general opposite-braiding/inverse identification or multi-field coordinate
comparison is asserted. The original VOA/CFT/anomaly/fusion/string/AdS goal
remains ACTIVE / INCOMPLETE.

Conventions and attribution are inherited from the sealed suppliers:
Bakalov--Kac, math/0402315v1, section 4.1; the original residue/Sugawara work
retains its Scott Carnahan / Kalle Kytölä attribution. This is a coherence
consumer of those exact maps, without a new product, unit or associator.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnits
import D5.S3.VertexAlgebra.Modules.ActualWeakModulePentagon
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraidingField

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator Matrix

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open LatticeChargedTransport LatticeActualGeneratorLocality
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleHom (recordEquiv restrict)
open ActualWeakModuleUniversalField (P PairSector targetModule U elementary translation tag)
open ActualWeakModuleProductMultiplicity
open ActualWeakModuleAssociator
open ActualWeakModuleProductNaturality
open ActualWeakModulePentagon (normalizedPair normalizedPair_transport
  normalizedPair_smul normalizedPair_input alpha_normalized)
open ActualWeakModuleUnits
open ActualWeakModuleBraiding (braid unbraid braidIso braid_tag phase)
open LatticeChargedQuotientScalar (carry zeroCarry representative_zero unitCharacter
  unitCharacter_nonzero unitCharacter_zero carry_zero_left carry_zero_right)

open private familyMap classification_naturality from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private left_ext right_ext leftContraction rightContraction from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnits
open private shift_pair from D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws
open private pairRaw_gram_left from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

universe u v w t
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Scalars
variable (hD : (gramReal D).PosDef)

/-- This supplier proves beta_0=G*n_0, then writes the dot exponent as
    twice the original lower cocycle exponent, using the EVEN Gram diagonal.
    It does not assert that beta_0 is zero. -/
theorem gamma_zero : unitCharacter D hD 0 = 1 :=
  unitCharacter_zero D hD

theorem F_unit_left (c d : Discriminant D) : F hD 0 c d = 1 :=
  LatticeChargedQuotientScalar.associator_zero_left D hD c d

theorem F_unit_middle (c d : Discriminant D) :
    F hD c 0 d = unitCharacter D hD c :=
  LatticeChargedQuotientScalar.associator_zero_middle D hD c d

theorem F_unit_right (c d : Discriminant D) :
    F hD c d 0 = unitCharacter D hD d / unitCharacter D hD (c+d) :=
  LatticeChargedQuotientScalar.associator_zero_right D hD c d

/-- Elementary exponential evaluation, including negative integer exponents. -/
private theorem exp_pi_parity (n : ℤ) :
    Complex.exp (Real.pi * Complex.I * (n : ℂ)) = paritySign n := by
  have htwo : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
    rw [show (2 : ℂ) * Real.pi * Complex.I =
      Real.pi * Complex.I + Real.pi * Complex.I by ring]
    simp only [Complex.exp_add, Complex.exp_pi_mul_I]
    norm_num
  by_cases hn : Even n
  · obtain ⟨k,hk⟩ := hn
    rw [paritySign, if_pos (show Even n from ⟨k,hk⟩)]
    have he : Real.pi * Complex.I * (n : ℂ) =
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hk]
      push_cast
      ring
    rw [he, Complex.exp_int_mul, htwo, one_zpow]
  · obtain ⟨k,hk⟩ := (Int.even_or_odd n).resolve_left hn
    rw [paritySign, if_neg hn]
    have he : Real.pi * Complex.I * (n : ℂ) =
        (k : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I := by
      rw [hk]
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_int_mul, htwo,
      one_zpow, one_mul, Complex.exp_pi_mul_I]

/-- Q(beta_c,G*n_0)=beta_c dot n_0 in the ORIGINAL inverse-Gram pairing. -/
theorem unit_shift (c : Discriminant D) :
    LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
      (representative D c) (representative D 0) =
        ((representative D c ⬝ᵥ zeroCarry D hD : ℤ) : ℚ) := by
  rw [shift_pair, Matrix.one_mulVec, Matrix.one_mulVec, representative_zero D hD,
    pairRaw_gram_left D hD, dotProduct_comm]

/-- The actual forward Omega at the unit is gamma, including a nonzero beta_0. -/
theorem phase_unit (c : Discriminant D) :
    phase (D := D) c 0 = unitCharacter D hD c := by
  change Complex.exp (Real.pi * Complex.I *
    (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ)
      (representative D c) (representative D 0) : ℂ)) =
        paritySign (representative D c ⬝ᵥ zeroCarry D hD)
  rw [unit_shift hD]
  simpa using exp_pi_parity (representative D c ⬝ᵥ zeroCarry D hD)

end Scalars

section Morphisms
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

private theorem restrict_identity (c : Discriminant D) (x : Multiplicity A c) :
    restrict (ModuleHom.id A) c x = x := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The full original classification is natural for an independently given f. -/
theorem classified_natural (f : ModuleHom A B) (c : Discriminant D)
    (v : Carrier D) (x : Multiplicity A c) :
    f.linearMap (classified hD A c x v) =
      classified hD B c (restrict f c x) v := by
  change f.linearMap (classificationEquiv A hD (elementary A c v x)) =
    classificationEquiv B hD (elementary B c v (restrict f c x))
  rw [classification_naturality f hD]
  congr 1
  simp only [elementary, familyMap, DirectSum.lmap_lof,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- Genuine ModuleHom equality. productHom takes SOURCE-to-TARGET f,g;
    its apparent A',A order comes from the representability inputMap. -/
theorem leftUnit_natural (f : ModuleHom A B) :
    (leftUnitIso hD B).hom.comp (productHom hD (ModuleHom.id (I D)) f) =
      f.comp (leftUnitIso hD A).hom := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply left_ext hD A
  intro c v x
  change leftUnit hD B ((productHom hD (ModuleHom.id (I D)) f).linearMap
    (DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
      (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x)))) =
    f.linearMap (leftUnit hD A (DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
      (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x))))
  rw [productHom_pair, TensorProduct.map_tmul, restrict_identity,
    leftUnit_elementary, leftUnit_elementary, classified_natural]

theorem rightUnit_natural (f : ModuleHom A B) :
    (rightUnitIso hD B).hom.comp (productHom hD f (ModuleHom.id (I D))) =
      f.comp (rightUnitIso hD A).hom := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply right_ext hD A
  intro c v x
  change rightUnit hD B ((productHom hD f (ModuleHom.id (I D))).linearMap
    (DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
      (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] eta0 hD)))) =
    f.linearMap (rightUnit hD A (DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
      (v ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] eta0 hD))))
  rw [productHom_pair, TensorProduct.map_tmul, restrict_identity,
    rightUnit_elementary, rightUnit_elementary, map_smul, classified_natural]

/-- All original states, not just the unit vacuum; used in the finite raw diagram. -/
theorem hom_translation_pow (f : ModuleHom A B) (r : ℕ) (x : X) :
    f.linearMap ((translation A hD ^ r) x) =
      (translation B hD ^ r) (f.linearMap x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      change f.linearMap (mode A (LatticeActualConformalState.omega D (inverseGram hD)) 0
        ((translation A hD ^ r) x)) =
        mode B (LatticeActualConformalState.omega D (inverseGram hD)) 0
          ((translation B hD ^ r) (f.linearMap x))
      rw [f.intertwines, ih]

end Morphisms

section UnitEquality
variable (hD : (gramReal D).PosDef)

/-- Equality on the WHOLE original P(I,I). The actual unit multiplicities kill
    wrong sectors and reduce the remaining factor by its actual coefficient. -/
theorem leftUnit_eq_rightUnit_I :
    (leftUnitIso hD (I D)).hom = (rightUnitIso hD (I D)).hom := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply left_ext hD (I D)
  intro c v x
  change leftUnit hD (I D) (DirectSum.lof ℂ _ (PairSector (I D) (I D)) (0,c)
    (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x))) =
    rightUnit hD (I D) (DirectSum.lof ℂ _ (PairSector (I D) (I D)) (0,c)
      (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] x)))
  by_cases hc : c = 0
  · subst c
    have he : leftUnit hD (I D)
        (DirectSum.lof ℂ _ (PairSector (I D) (I D)) (0,0)
          (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] eta0 hD))) =
        rightUnit hD (I D)
          (DirectSum.lof ℂ _ (PairSector (I D) (I D)) (0,0)
            (v ⊗ₜ[ℂ] (eta0 hD ⊗ₜ[ℂ] eta0 hD))) := by
      rw [leftUnit_elementary, rightUnit_elementary]
      change classified hD (I D) 0 (eta0 hD) _ =
        unitCharacter D hD 0 • classified hD (I D) 0 (eta0 hD) _
      rw [gamma_zero hD, one_smul]
    rw [← etaCoefficient_inverse hD x]
    simpa only [TensorProduct.tmul_smul, map_smul] using
      congrArg (fun z : Carrier D => etaCoefficient hD x • z) he
  · rw [unit_multiplicity_wrong hD c hc x]
    simp

end UnitEquality

section GroundUnits
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- The equality proof stays INSIDE the supplied jAt fiber. mu_jAt performs
    the actual normalized reconstruction; its epsilon(-n_0,n_0)^-1 is retained. -/
theorem restrict_leftUnit_jAt (c : Discriminant D) (x : Multiplicity A c) :
    restrict (leftUnitIso hD A).hom c
      (jAt (I D) A hD c ⟨(0,c),zero_add c⟩ (eta0 hD ⊗ₜ[ℂ] x)) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change leftUnit hD A
    (jAt (I D) A hD c ⟨(0,c),zero_add c⟩ (eta0 hD ⊗ₜ[ℂ] x)).val.val = x.val.val
  rw [leftUnit_ground_mu, mu_jAt]
  simp [leftContraction, DirectSum.lof_eq_of]

/-- The right ground restriction is gamma_c*x, not x. -/
theorem restrict_rightUnit_jAt (c : Discriminant D) (x : Multiplicity A c) :
    restrict (rightUnitIso hD A).hom c
      (jAt A (I D) hD c ⟨(c,0),add_zero c⟩ (x ⊗ₜ[ℂ] eta0 hD)) =
        unitCharacter D hD c • x := by
  apply Subtype.ext
  apply Subtype.ext
  change rightUnit hD A
    (jAt A (I D) hD c ⟨(c,0),add_zero c⟩ (x ⊗ₜ[ℂ] eta0 hD)).val.val =
      unitCharacter D hD c • x.val.val
  rw [rightUnit_ground_mu, mu_jAt]
  simp [rightContraction, DirectSum.lof_eq_of]

/-- Full-state unit readbacks reuse the original classification_j formulas. -/
theorem leftUnit_normalized (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    leftUnit hD A (normalizedPair (I D) A hD 0 c (eta0 hD ⊗ₜ[ℂ] x) v) =
      classified hD A c x v := by
  change leftUnit hD A (DirectSum.lof ℂ _ (PairSector (I D) A) (0,c)
    (transportInverse D (representative D (0+c)) (carry D hD 0 c) v ⊗ₜ[ℂ]
      (eta0 hD ⊗ₜ[ℂ] x))) = _
  rw [← classification_j]
  exact leftUnit_classification_j hD A c v x

theorem rightUnit_normalized (c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) :
    rightUnit hD A (normalizedPair A (I D) hD c 0 (x ⊗ₜ[ℂ] eta0 hD) v) =
      unitCharacter D hD c • classified hD A c x v := by
  change rightUnit hD A (DirectSum.lof ℂ _ (PairSector A (I D)) (c,0)
    (transportInverse D (representative D (c+0)) (carry D hD c 0) v ⊗ₜ[ℂ]
      (x ⊗ₜ[ℂ] eta0 hD))) = _
  rw [← classification_j]
  exact rightUnit_classification_j hD A c v x

end GroundUnits

section NormalizedTriples
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (C : FullJacobiLatticeModule D Z) (hD : (gramReal D).PosDef)

/-- Same original normalized generator, with its sum equality retained in jAt. -/
theorem normalizedPair_left_fiber (a b e c : Discriminant D) (he : a+b=e)
    (w : PairMultiplicity A B (a,b)) (z : Multiplicity C c) (v : Carrier D) :
    normalizedPair (targetModule A B) C hD e c
      (jAt A B hD e ⟨(a,b),he⟩ w ⊗ₜ[ℂ] z) v =
    normalizedPair (targetModule A B) C hD (a+b) c
      (j A B hD a b w ⊗ₜ[ℂ] z) v := by
  subst e
  rfl

/-- A literal specialization of alpha_normalized; no inverse normalization
    or dependent equality is omitted at either inner or outer vertex. -/
theorem alpha_normalized_fibers (a b c ab bc : Discriminant D)
    (hab : a+b=ab) (hbc : b+c=bc) (v : Carrier D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    alpha A B C hD
      (normalizedPair (targetModule A B) C hD ab c
        (jAt A B hD ab ⟨(a,b),hab⟩ (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) v) =
    F hD a b c • normalizedPair A (targetModule B C) hD a bc
      (x ⊗ₜ[ℂ] jAt B C hD bc ⟨(b,c),hbc⟩ (y ⊗ₜ[ℂ] z)) v := by
  subst ab
  subst bc
  exact alpha_normalized A B C hD a b c v x y z

/-- ALL full vectors follow from the existing E_L finite generation and the
    genuine two-sided outer transport, with every tensor-zero branch inherited. -/
theorem normalizedTriple_induction (Q : LeftP A B C → Prop) (h0 : Q 0)
    (ha : ∀ s t, Q s → Q t → Q (s+t))
    (he : ∀ a b c v x y z,
      Q (normalizedPair (targetModule A B) C hD (a+b) c
        (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) v))
    (s : LeftP A B C) : Q s := by
  apply E_L_induction A B C hD Q h0 ha ?_ s
  intro a b c v x y z
  have hh := he a b c
    (transport D (representative D ((a+b)+c)) (carry D hD (a+b) c) v) x y z
  simpa only [normalizedPair_transport, E_L, leftElementary,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply] using hh

end NormalizedTriples

section TwoModules
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

theorem alpha_unit_left (c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) :
    alpha (I D) A B hD
      (normalizedPair (targetModule (I D) A) B hD c d
        (jAt (I D) A hD c ⟨(0,c),zero_add c⟩ (eta0 hD ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] y) v) =
    normalizedPair (I D) (targetModule A B) hD 0 (c+d)
      (eta0 hD ⊗ₜ[ℂ] j A B hD c d (x ⊗ₜ[ℂ] y)) v := by
  simpa only [F_unit_left, one_smul, jAt] using
    alpha_normalized_fibers (I D) A B hD 0 c d c (c+d)
      (zero_add c) rfl v (eta0 hD) x y

theorem alpha_unit_middle (c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) :
    alpha A (I D) B hD
      (normalizedPair (targetModule A (I D)) B hD c d
        (jAt A (I D) hD c ⟨(c,0),add_zero c⟩ (x ⊗ₜ[ℂ] eta0 hD) ⊗ₜ[ℂ] y) v) =
    unitCharacter D hD c • normalizedPair A (targetModule (I D) B) hD c d
      (x ⊗ₜ[ℂ] jAt (I D) B hD d ⟨(0,d),zero_add d⟩ (eta0 hD ⊗ₜ[ℂ] y)) v := by
  simpa only [F_unit_middle] using
    alpha_normalized_fibers A (I D) B hD c 0 d c d
      (add_zero c) (zero_add d) v x (eta0 hD) y

theorem alpha_unit_right (c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) :
    alpha A B (I D) hD
      (normalizedPair (targetModule A B) (I D) hD (c+d) 0
        (j A B hD c d (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] eta0 hD) v) =
    (unitCharacter D hD d / unitCharacter D hD (c+d)) •
      normalizedPair A (targetModule B (I D)) hD c d
        (x ⊗ₜ[ℂ] jAt B (I D) hD d ⟨(d,0),add_zero d⟩ (y ⊗ₜ[ℂ] eta0 hD)) v := by
  simpa only [F_unit_right, jAt] using
    alpha_normalized_fibers A B (I D) hD c d 0 (c+d) d
      rfl (add_zero d) v x y (eta0 hD)

/-- First full triangle path: alpha contributes F(c,0,d)=gamma_c and
    the left unit on the right inner jAt contributes one. -/
theorem triangle_left_normalized (c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) :
    (productHom hD (ModuleHom.id A) (leftUnitIso hD B).hom).linearMap
      (alpha A (I D) B hD
        (normalizedPair (targetModule A (I D)) B hD c d
          (jAt A (I D) hD c ⟨(c,0),add_zero c⟩ (x ⊗ₜ[ℂ] eta0 hD) ⊗ₜ[ℂ] y) v)) =
      unitCharacter D hD c • normalizedPair A B hD c d (x ⊗ₜ[ℂ] y) v := by
  rw [alpha_unit_middle, map_smul, normalizedPair_input,
    TensorProduct.map_tmul, restrict_identity, restrict_leftUnit_jAt]

/-- Second full triangle path: rho contributes the SAME gamma_c.
    Its omission would already fail at these exact full-state generators. -/
theorem triangle_right_normalized (c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A c) (y : Multiplicity B d) :
    (productHom hD (rightUnitIso hD A).hom (ModuleHom.id B)).linearMap
      (normalizedPair (targetModule A (I D)) B hD c d
        (jAt A (I D) hD c ⟨(c,0),add_zero c⟩ (x ⊗ₜ[ℂ] eta0 hD) ⊗ₜ[ℂ] y) v) =
      unitCharacter D hD c • normalizedPair A B hD c d (x ⊗ₜ[ℂ] y) v := by
  rw [normalizedPair_input, TensorProduct.map_tmul,
    restrict_rightUnit_jAt, restrict_identity, ← TensorProduct.smul_tmul',
    normalizedPair_smul]

/-- Original triangle as equality of ALL-STATE/ALL-INTEGER-MODE ModuleHoms,
    on the whole P(P(A,I),B), with no finite-dimensional or nonzero premise. -/
theorem triangle :
    (productHom hD (ModuleHom.id A) (leftUnitIso hD B).hom).comp
      (associatorIso A (I D) B hD).hom =
    productHom hD (rightUnitIso hD A).hom (ModuleHom.id B) := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro s
  change (productHom hD (ModuleHom.id A) (leftUnitIso hD B).hom).linearMap
    (alpha A (I D) B hD s) =
    (productHom hD (rightUnitIso hD A).hom (ModuleHom.id B)).linearMap s
  apply normalizedTriple_induction A (I D) B hD
    (fun s => (productHom hD (ModuleHom.id A) (leftUnitIso hD B).hom).linearMap
      (alpha A (I D) B hD s) =
      (productHom hD (rightUnitIso hD A).hom (ModuleHom.id B)).linearMap s)
    (by simp) (fun s t hs ht => by simp only [map_add, hs, ht]) ?_ s
  intro c e d v x n y
  by_cases he : e = 0
  · subst e
    have hh := (triangle_left_normalized A B hD c d v x y).trans
      (triangle_right_normalized A B hD c d v x y).symm
    simp only [normalizedPair_left_fiber A (I D) B hD c 0 c d (add_zero c)] at hh
    rw [← etaCoefficient_inverse hD n]
    simpa only [TensorProduct.tmul_smul, map_smul, ← TensorProduct.smul_tmul',
      normalizedPair_smul (targetModule A (I D)) B hD (c+0) d, map_smul] using
        congrArg (fun z : P A B => etaCoefficient hD n • z) hh
  · rw [unit_multiplicity_wrong hD e he n]
    simp [normalizedPair]

end TwoModules

section BraidingUnit
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X) (hD : (gramReal D).PosDef)

/-- The actual binary braiding and actual units as original ModuleHom records. -/
theorem braiding_unit :
    (leftUnitIso hD A).hom.comp (braidIso A (I D)).hom =
      (rightUnitIso hD A).hom := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply right_ext hD A
  intro c v x
  change leftUnit hD A (braid A (I D)
    (tag A (I D) c 0 x (eta0 hD) v)) =
    rightUnit hD A (tag A (I D) c 0 x (eta0 hD) v)
  rw [braid_tag, map_smul]
  simp only [ActualWeakModuleUniversalField.tag_apply, leftUnit_elementary hD A,
    rightUnit_elementary hD A]
  rw [phase_unit hD]
  rfl

/-- Only the genuine inverse of THIS unit braiding is identified. This
    follows after phase_unit/braiding_unit, without a statement about b(B,A). -/
theorem inverse_braiding_unit :
    (braidIso A (I D)).inv =
      (rightUnitIso hD A).inv.comp (leftUnitIso hD A).hom := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro s
  change unbraid A (I D) s = (rightUnit hD A).symm (leftUnit hD A s)
  apply (rightUnit hD A).injective
  rw [LinearEquiv.apply_symm_apply]
  have hh := congrArg (fun f : ModuleHom (targetModule A (I D)) A =>
    f.linearMap (unbraid A (I D) s)) (braiding_unit A hD)
  change leftUnit hD A (braid A (I D) (unbraid A (I D) s)) =
    rightUnit hD A (unbraid A (I D) s) at hh
  rw [ActualWeakModuleBraiding.braid_unbraid] at hh
  exact hh.symm

end BraidingUnit

section RawCoefficients
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable (hD : (gramReal D).PosDef)

/-- Every rational RAW-U coefficient, on arbitrary original full inputs. -/
theorem leftUnit_natural_U (f : ModuleHom A B) (u : Carrier D) (x : X) (q : ℚ) :
    leftUnit hD B ((U (I D) B hD u).coeff q (f.linearMap x)) =
      f.linearMap (leftUnit hD A ((U (I D) A hD u).coeff q x)) := by
  have hh := congrArg (fun g : ModuleHom (targetModule (I D) A) B =>
    g.linearMap ((U (I D) A hD u).coeff q x)) (leftUnit_natural hD f)
  change leftUnit hD B ((productHom hD (ModuleHom.id (I D)) f).linearMap
    ((U (I D) A hD u).coeff q x)) = _ at hh
  simpa only [productHom_U_coeff, ModuleHom.id, LinearMap.id_apply,
    ModuleHom.comp, LinearMap.comp_apply, ModuleIso.hom, leftUnitIso, rightUnitIso,
    LinearEquiv.coe_coe] using hh

theorem rightUnit_natural_U (f : ModuleHom A B) (x : X) (u : Carrier D) (q : ℚ) :
    rightUnit hD B ((U B (I D) hD (f.linearMap x)).coeff q u) =
      f.linearMap (rightUnit hD A ((U A (I D) hD x).coeff q u)) := by
  have hh := congrArg (fun g : ModuleHom (targetModule A (I D)) B =>
    g.linearMap ((U A (I D) hD x).coeff q u)) (rightUnit_natural hD f)
  change rightUnit hD B ((productHom hD f (ModuleHom.id (I D))).linearMap
    ((U A (I D) hD x).coeff q u)) = _ at hh
  simpa only [productHom_U_coeff, ModuleHom.id, LinearMap.id_apply,
    ModuleHom.comp, LinearMap.comp_apply, ModuleIso.hom, leftUnitIso, rightUnitIso,
    LinearEquiv.coe_coe] using hh

theorem unit_equality_U (u v : Carrier D) (q : ℚ) :
    leftUnit hD (I D) ((U (I D) (I D) hD u).coeff q v) =
      rightUnit hD (I D) ((U (I D) (I D) hD u).coeff q v) := by
  exact congrArg (fun g : ModuleHom (targetModule (I D) (I D)) (I D) =>
    g.linearMap ((U (I D) (I D) hD u).coeff q v)) (leftUnit_eq_rightUnit_I hD)

/-- Application of the proved triangle to the ACTUAL outer U. This compares
    maps of a coefficient; it asserts no product/iterate coordinate equation. -/
theorem triangle_U (s : P A (I D)) (y : Y) (q : ℚ) :
    (productHom hD (ModuleHom.id A) (leftUnitIso hD B).hom).linearMap
      (alpha A (I D) B hD ((U (targetModule A (I D)) B hD s).coeff q y)) =
    (U A B hD (rightUnit hD A s)).coeff q y := by
  have hh := congrArg (fun g : ModuleHom
    (targetModule (targetModule A (I D)) B) (targetModule A B) =>
      g.linearMap ((U (targetModule A (I D)) B hD s).coeff q y)) (triangle A B hD)
  change (productHom hD (ModuleHom.id A) (leftUnitIso hD B).hom).linearMap
    (alpha A (I D) B hD ((U (targetModule A (I D)) B hD s).coeff q y)) = _ at hh
  simpa only [productHom_U_coeff, ModuleIso.hom, ModuleHom.id,
    LinearMap.id_apply, rightUnitIso, LinearEquiv.coe_coe] using hh

/-- A nested raw coefficient consequence with the literal finite right-unit
    diagram. k and q remain separate; no new coordinate coherence is claimed. -/
theorem triangle_U_unit_integer (x : X) (u : Carrier D) (y : Y)
    (k : ℤ) (q : ℚ) (N : ℕ)
    (hN : ∀ m : ℤ, (N : ℤ) ≤ m → mode A u m x = 0) :
    (productHom hD (ModuleHom.id A) (leftUnitIso hD B).hom).linearMap
      (alpha A (I D) B hD
        ((U (targetModule A (I D)) B hD ((U A (I D) hD x).coeff (k : ℚ) u)).coeff q y)) =
    (U A B hD
      (∑ i ∈ Finset.range (((N : ℤ)+k+1).toNat),
        (((-1 : ℂ)^(k-(i : ℤ))) / (i.factorial : ℂ)) •
          ((translation A hD)^i) (mode A u ((i : ℤ)-k-1) x))).coeff q y := by
  rw [triangle_U, rightUnit_U_general_integer hD A x u k N hN]

/-- The original module's truncation supplies N for EVERY pair; the finite
    consequence above therefore adds no condition on an arbitrary module. -/
theorem triangle_U_unit_finite (x : X) (u : Carrier D) (y : Y) :
    ∃ N : ℕ,
      (∀ m : ℤ, (N : ℤ) ≤ m → mode A u m x = 0) ∧
      ∀ (k : ℤ) (q : ℚ),
        (productHom hD (ModuleHom.id A) (leftUnitIso hD B).hom).linearMap
          (alpha A (I D) B hD
            ((U (targetModule A (I D)) B hD
              ((U A (I D) hD x).coeff (k : ℚ) u)).coeff q y)) =
        (U A B hD
          (∑ i ∈ Finset.range (((N : ℤ)+k+1).toNat),
            (((-1 : ℂ)^(k-(i : ℤ))) / (i.factorial : ℂ)) •
              ((translation A hD)^i) (mode A u ((i : ℤ)-k-1) x))).coeff q y := by
  have hcut : ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → mode A u m x = 0 :=
    @ActualWeakModuleUnits.module_pair_cutoff D X _ _ A u x
  obtain ⟨N,hN⟩ := hcut
  exact ⟨N,hN,fun k q => triangle_U_unit_integer hD x u y k q N hN⟩

theorem braiding_unit_U (x : X) (u : Carrier D) (q : ℚ) :
    leftUnit hD A (braid A (I D) ((U A (I D) hD x).coeff q u)) =
      rightUnit hD A ((U A (I D) hD x).coeff q u) := by
  exact congrArg (fun g : ModuleHom (targetModule A (I D)) A =>
    g.linearMap ((U A (I D) hD x).coeff q u)) (braiding_unit A hD)

/-- The actual binary field supplier gives a finite reversed/translated sum.
    Every original rational exponent is retained, and the j-th reversed
    coefficient is q-j. This is not an equality at two unchanged indices. -/
theorem braiding_unit_U_finite (x : X) (u : Carrier D) (q : ℚ) :
    rightUnit hD A ((U A (I D) hD x).coeff q u) =
    ∑ᶠ j : ℕ,
      (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
        (translation A hD ^ j)
          (leftUnit hD A ((U (I D) A hD u).coeff (q-(j : ℚ)) x)) := by
  rw [← braiding_unit_U hD x u q, ActualWeakModuleBraidingField.U_braiding]
  change (leftUnit hD A).toLinearMap _ = _
  rw [map_finsum (leftUnit hD A).toLinearMap
    (ActualWeakModuleBraidingField.U_braiding_finite A (I D) hD x u q)]
  apply finsum_congr
  intro j
  rw [map_smul]
  change _ • (leftUnitIso hD A).hom.linearMap
    ((translation (targetModule (I D) A) hD ^ j)
      ((U (I D) A hD u).coeff (q-(j : ℚ)) x)) = _
  rw [hom_translation_pow hD (leftUnitIso hD A).hom]
  simp only [ModuleIso.hom, leftUnitIso, LinearEquiv.coe_coe]

/-- Finiteness remains true after the actual left unit is applied termwise. -/
theorem braiding_unit_U_terms_finite (x : X) (u : Carrier D) (q : ℚ) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
        (translation A hD ^ j)
          (leftUnit hD A ((U (I D) A hD u).coeff (q-(j : ℚ)) x))) := by
  apply (ActualWeakModuleBraidingField.U_braiding_finite A (I D) hD x u q).subset
  intro j hj hz
  apply hj
  have he := congrArg (leftUnit hD A) hz
  change (leftUnitIso hD A).hom.linearMap
    ((Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
      (translation (targetModule (I D) A) hD ^ j)
        ((U (I D) A hD u).coeff (q-(j : ℚ)) x)) =
    (leftUnitIso hD A).hom.linearMap 0 at he
  rw [map_smul, hom_translation_pow hD (leftUnitIso hD A).hom, map_zero] at he
  simpa only [ModuleIso.hom, leftUnitIso, LinearEquiv.coe_coe] using he

end RawCoefficients
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleUnitCoherence
