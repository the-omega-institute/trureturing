/-
SOURCE-ONLY REPAIR. No native elaboration or acceptance is claimed.
The two literal full ModuleHom hexagons and braid naturality retain their
original endpoints and independent universes. Products, restrictions, carries,
sections, inverse transports and associators are the pinned original APIs.
Nine retired companion/duplicate rows are preserved outside this canonical
module in application-exposition.txt and transient exact checks.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraidingField
import D5.S3.VertexAlgebra.Modules.ActualWeakModulePentagon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator Matrix

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraidedCoherence

attribute [local instance] Classical.propDecidable
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open FullJacobiCurrentTransport FullJacobiIntertwiner FullJacobiTensorModule
open FullJacobiDirectSum
open LatticeActualGeneratorLocality
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleHom (recordEquiv restrict)
open ActualWeakModuleUniversalField (P PairSector targetModule U translation tag tag_apply)
open ActualWeakModuleIntertwinerRepresentability
open ActualWeakModuleProductMultiplicity
open ActualWeakModuleAssociator
open ActualWeakModuleProductNaturality
open ActualWeakModulePentagon
open ActualWeakModuleBraiding
open ActualWeakModuleBraidingField
open LatticeCosetRationalSkew
open LatticeChargedTransport
open LatticeChargedQuotientScalar
open private associatorExponent sign_neg sign_inv sign_sub associator_eq_sign
  from D5.S3.VertexAlgebra.Sectors.LatticeChargedQuotientScalar
open private exp_pi_int from D5.S3.VertexAlgebra.Sectors.LatticeCosetRationalSkew
open private pairRaw_add_left pairRaw_add_right pairRaw_gram_left pairRaw_gram_right
  from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open private shift_pair from D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws

universe u v w u' v' w'
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Binary
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

/-- Carry symmetry is proved from the original constructive carry equation. -/
theorem carry_comm (c d : Discriminant D) :
    carry D hD c d = carry D hD d c := by
  apply carry_unique D hD d c
  simpa [add_comm] using carry_equation D hD c d

/-- The returned binary map on an arbitrary algebraic tensor in one direct-sum
    summand.  This is the full carrier formula used below; it is not a basis
    restriction. -/
theorem braid_lof (c d : Discriminant D) (v : Carrier D)
    (w : PairMultiplicity A B (c,d)) :
    braid A B (DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (v ⊗ₜ[ℂ] w)) =
      phase (D := D) c d •
        DirectSum.lof ℂ _ (PairSector B A) (d,c)
          (v ⊗ₜ[ℂ] (TensorProduct.comm ℂ (Multiplicity A c)
            (Multiplicity B d) w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' =>
      simpa only [TensorProduct.tmul_add, map_add, hw, hw', smul_add]
  | tmul x y =>
      simpa only [tag_apply, TensorProduct.comm_tmul] using
        (braid_tag A B c d x y v)

/-- Restriction of the returned braid on the normalized original generator.
    The target fibre is the literal swapped fibre, with its original equality
    proof. -/
theorem braid_normalizedPair (c d : Discriminant D)
    (w : PairMultiplicity A B (c,d)) (v : Carrier D) :
    (braidIso A B).hom.linearMap
        (normalizedPair A B hD c d w v) =
      phase (D := D) c d •
        normalizedPair B A hD d c
          (TensorProduct.comm ℂ (Multiplicity A c) (Multiplicity B d) w) v := by
  change braid A B (normalizedPair A B hD c d w v) = _
  simpa only [normalizedPair, LinearMap.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, carry_comm hD c d, add_comm c d] using
    (braid_lof A B c d
      (transportInverse D (representative D (c+d)) (carry D hD c d) v) w)

/-- The exact restriction image of the original dependent `jAt` subtype. -/
theorem braid_restrict_jAt (e : Discriminant D)
    (i : Fiber (D := D) e) (w : PairMultiplicity A B i.val) :
    restrict (braidIso A B).hom e (jAt A B hD e i w) =
      phase (D := D) i.val.1 i.val.2 •
        jAt B A hD e
          ⟨(i.val.2,i.val.1), by simpa [add_comm] using i.property⟩
          (TensorProduct.comm ℂ (Multiplicity A i.val.1)
            (Multiplicity B i.val.2) w) := by
  rcases i with ⟨⟨c,d⟩,h⟩
  subst e
  apply Subtype.ext
  apply Subtype.ext
  change braid A B (j A B hD c d w).val.val =
    phase (D := D) c d •
      (jAt B A hD (c+d) ⟨(d,c), by simp only [add_comm]⟩
        (TensorProduct.comm ℂ (Multiplicity A c) (Multiplicity B d) w)).val.val
  rw [j_val, jAt_val, braid_lof]
  simp only [ground, carry_comm hD c d, add_comm c d]

/-- Naturality for the existing representability-defined `productHom`. -/
theorem braid_natural
    {X' : Type u'} {Y' : Type v'}
    [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y'] [Module ℂ Y']
    {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'}
    (f : ModuleHom A' A) (g : ModuleHom B' B) :
    (productHom hD g f).comp (braidIso A' B').hom =
      (braidIso A B).hom.comp (productHom hD f g) := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  change (productHom hD g f).linearMap (braid A' B' z) =
    braid A B ((productHom hD f g).linearMap z)
  apply pair_induction A' B'
    (fun z => (productHom hD g f).linearMap (braid A' B' z) =
      braid A B ((productHom hD f g).linearMap z))
    (by simp) (fun x y hx hy => by simp only [map_add, hx, hy]) ?_ z
  intro c d x y v
  simp only [braid_lof A' B', map_smul, tag_apply, productHom_pair hD,
    TensorProduct.map_tmul, braid_lof A B, TensorProduct.comm_tmul]

end Binary

section Scalars

private theorem scalar_exponent_h1 (hD : (gramReal D).PosDef)
    (a b c : Discriminant D) :
    associatorExponent D hD a b c + associatorExponent D hD b c a -
        associatorExponent D hD b a c =
      representative D a ⬝ᵥ carry D hD b c := by
  simp only [associatorExponent, carry_comm hD c a, carry_comm hD b a,
    carry_comm hD (b+c) a, add_comm c a, add_comm b a]
  ring

private theorem scalar_exponent_h2 (hD : (gramReal D).PosDef)
    (a b c : Discriminant D) :
    associatorExponent D hD a c b - associatorExponent D hD a b c -
        associatorExponent D hD c a b =
      -(representative D c ⬝ᵥ carry D hD a b) := by
  simp only [associatorExponent, carry_comm hD c b, carry_comm hD c a,
    carry_comm hD (a+b) c, add_comm c b, add_comm c a]
  ring

/-- The phase ratio is derived from the inverse-Gram pairing and the actual
    carry equation.  It is a sign only for this particular ratio. -/
theorem phase_ratio_left (hD : (gramReal D).PosDef)
    (a b c : Discriminant D) :
    phase (D := D) a (b+c) /
        (phase (D := D) a b * phase (D := D) a c) =
      chi D (representative D a) (carry D hD b c) := by
  let r : ℚ := LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D a) (representative D (b+c))
  let s : ℚ := LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D a) (representative D b)
  let t : ℚ := LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D a) (representative D c)
  let n : ℤ := representative D a ⬝ᵥ carry D hD b c
  have he : r - s - t = -(n : ℚ) := by
    have hc := congrArg (fun t : Charge D => pairRaw D t (representative D a))
      (carry_equation D hD b c)
    simp only [pairRaw_add_left, pairRaw_gram_left D hD] at hc
    rw [dotProduct_comm (carry D hD b c) (representative D a)] at hc
    dsimp only [r, s, t, n]
    rw [shift_pair, shift_pair, shift_pair]
    simp only [Matrix.one_mulVec]
    linear_combination -hc
  change Complex.exp (Real.pi * Complex.I * (r : ℂ)) /
      (Complex.exp (Real.pi * Complex.I * (s : ℂ)) *
       Complex.exp (Real.pi * Complex.I * (t : ℂ))) = paritySign n
  calc
    _ = Complex.exp (Real.pi * Complex.I *
        ((r : ℂ) - (s : ℂ) - (t : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_sub]
      congr 1
      ring
    _ = Complex.exp (Real.pi * Complex.I * (-(n : ℂ))) := by
      have hec : (r : ℂ) - (s : ℂ) - (t : ℂ) = -(n : ℂ) := by
        exact_mod_cast he
      rw [hec]
    _ = paritySign n := by
      simpa only [Int.cast_neg, neg_one_zpow_eq_ite, paritySign, even_neg] using
        (exp_pi_int (-n))

/-- The second phase ratio, with the same sign-only qualification. -/
theorem phase_ratio_right (hD : (gramReal D).PosDef)
    (a b c : Discriminant D) :
    phase (D := D) (a+b) c /
        (phase (D := D) a c * phase (D := D) b c) =
      chi D (representative D c) (carry D hD a b) := by
  let r : ℚ := LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D (a+b)) (representative D c)
  let s : ℚ := LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D a) (representative D c)
  let t : ℚ := LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D b) (representative D c)
  let n : ℤ := representative D c ⬝ᵥ carry D hD a b
  have he : r - s - t = -(n : ℚ) := by
    have hc := congrArg (fun t : Charge D => pairRaw D (representative D c) t)
      (carry_equation D hD a b)
    simp only [pairRaw_add_right, pairRaw_gram_right D hD] at hc
    rw [dotProduct_comm (carry D hD a b) (representative D c)] at hc
    dsimp only [r, s, t, n]
    rw [shift_pair, shift_pair, shift_pair]
    simp only [Matrix.one_mulVec]
    linear_combination -hc
  change Complex.exp (Real.pi * Complex.I * (r : ℂ)) /
      (Complex.exp (Real.pi * Complex.I * (s : ℂ)) *
       Complex.exp (Real.pi * Complex.I * (t : ℂ))) = paritySign n
  calc
    _ = Complex.exp (Real.pi * Complex.I *
        ((r : ℂ) - (s : ℂ) - (t : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_sub]
      congr 1
      ring
    _ = Complex.exp (Real.pi * Complex.I * (-(n : ℂ))) := by
      have hec : (r : ℂ) - (s : ℂ) - (t : ℂ) = -(n : ℂ) := by
        exact_mod_cast he
      rw [hec]
    _ = paritySign n := by
      simpa only [Int.cast_neg, neg_one_zpow_eq_ite, paritySign, even_neg] using
        (exp_pi_int (-n))

/-- Exact scalar identity consumed by the first module hexagon. -/
theorem scalar_h1 (hD : (gramReal D).PosDef)
    (a b c : Discriminant D) :
    F hD a b c * F hD b c a / F hD b a c =
      phase (D := D) a b * phase (D := D) a c /
        phase (D := D) a (b+c) := by
  calc
    _ = paritySign (associatorExponent D hD a b c +
        associatorExponent D hD b c a - associatorExponent D hD b a c) := by
      simp only [F, associator_eq_sign, sign_sub, paritySign_add,
        div_eq_mul_inv, sign_inv]
    _ = paritySign (representative D a ⬝ᵥ carry D hD b c) := by
      rw [scalar_exponent_h1]
    _ = _ := by
      have hr := congrArg (fun z : ℂ => z⁻¹) (phase_ratio_left hD a b c)
      simpa only [chi, sign_inv, div_eq_mul_inv, mul_inv_rev, inv_inv] using hr.symm

/-- Exact scalar identity consumed by the second module hexagon. -/
theorem scalar_h2 (hD : (gramReal D).PosDef)
    (a b c : Discriminant D) :
    F hD a c b / (F hD a b c * F hD c a b) =
      phase (D := D) a c * phase (D := D) b c /
        phase (D := D) (a+b) c := by
  calc
    _ = paritySign (associatorExponent D hD a c b -
        associatorExponent D hD a b c - associatorExponent D hD c a b) := by
      simp only [F, associator_eq_sign, sign_sub, div_eq_mul_inv,
        mul_inv_rev, sign_inv] <;> ring
    _ = paritySign (representative D c ⬝ᵥ carry D hD a b) := by
      rw [scalar_exponent_h2, sign_neg]
    _ = _ := by
      have hr := congrArg (fun z : ℂ => z⁻¹) (phase_ratio_right hD a b c)
      simpa only [chi, sign_inv, div_eq_mul_inv, mul_inv_rev, inv_inv] using hr.symm

end Scalars

section Hexagons
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable [AddCommGroup Z] [Module ℂ Z]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (C : FullJacobiLatticeModule D Z) (hD : (gramReal D).PosDef)

/-- The normalized original generators used in both hexagons. -/
def leftGenerator (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    Carrier D →ₗ[ℂ] P (targetModule A B) C :=
  normalizedPair (targetModule A B) C hD (a+b) c
    (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)

def rightGenerator (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    Carrier D →ₗ[ℂ] P A (targetModule B C) :=
  normalizedPair A (targetModule B C) hD a (b+c)
    (x ⊗ₜ[ℂ] j B C hD b c (y ⊗ₜ[ℂ] z))

def hexagonLeftPath :
    ModuleHom (targetModule (targetModule A B) C)
      (targetModule B (targetModule C A)) :=
  (associatorIso B C A hD).hom.comp
    ((braidIso A (targetModule B C)).hom.comp
      (associatorIso A B C hD).hom)

def hexagonLeftPathRight :
    ModuleHom (targetModule (targetModule A B) C)
      (targetModule B (targetModule C A)) :=
  (productHom hD (ModuleHom.id B) (braidIso A C).hom).comp
    ((associatorIso B A C hD).hom.comp
      (productHom hD (braidIso A B).hom (ModuleHom.id C)))

def hexagonRightPath :
    ModuleHom (targetModule A (targetModule B C))
      (targetModule (targetModule C A) B) :=
  (associatorIso C A B hD).inv.comp
    ((braidIso (targetModule A B) C).hom.comp
      (associatorIso A B C hD).inv)

def hexagonRightPathRight :
    ModuleHom (targetModule A (targetModule B C))
      (targetModule (targetModule C A) B) :=
  (productHom hD (braidIso A C).hom (ModuleHom.id B)).comp
    ((associatorIso A C B hD).inv.comp
      (productHom hD (ModuleHom.id A) (braidIso B C).hom))

private theorem left_inner_braid (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (braidIso A (targetModule B C)).hom.linearMap
      (rightGenerator A B C hD a b c x y z v) =
      phase (D := D) a (b+c) •
        leftGenerator B C A hD b c a y z x v := by
  simpa [rightGenerator, leftGenerator] using
    (braid_normalizedPair A (targetModule B C) hD a (b+c)
      (x ⊗ₜ[ℂ] j B C hD b c (y ⊗ₜ[ℂ] z)) v)

private theorem right_inner_braid (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (braidIso (targetModule A B) C).hom.linearMap
      (leftGenerator A B C hD a b c x y z v) =
      phase (D := D) (a+b) c •
        rightGenerator C A B hD c a b z x y v := by
  simpa [leftGenerator, rightGenerator] using
    (braid_normalizedPair (targetModule A B) C hD (a+b) c
      (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) v)

private theorem product_inner_braid_left (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (productHom hD (braidIso A B).hom (ModuleHom.id C)).linearMap
      (leftGenerator A B C hD a b c x y z v) =
      phase (D := D) a b •
        leftGenerator B A C hD b a c y x z v := by
  simp only [leftGenerator, normalizedPair_input, TensorProduct.map_tmul]
  have hj := braid_restrict_jAt A B hD (a+b)
    ⟨(a,b), rfl⟩ (x ⊗ₜ[ℂ] y)
  change normalizedPair (targetModule B A) C hD (a+b) c
    (restrict (braidIso A B).hom (a+b)
      (jAt A B hD (a+b) ⟨(a,b), rfl⟩ (x ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ] z) v = _
  rw [hj]
  simp only [TensorProduct.comm_tmul, jAt]
  have hc (e e' : Discriminant D) (he : e' = e)
      (f : PairMultiplicity B A (b,a) →ₗ[ℂ] Multiplicity (targetModule B A) e') :
      normalizedPair (targetModule B A) C hD e c
        (((he ▸ f) (y ⊗ₜ[ℂ] x)) ⊗ₜ[ℂ] z) v =
        normalizedPair (targetModule B A) C hD e' c
          (f (y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] z) v := by
    subst e
    rfl
  rw [← TensorProduct.smul_tmul', normalizedPair_smul]
  exact congrArg (fun t => phase (D := D) a b • t)
    (hc (a+b) (b+a) (add_comm b a) (j B A hD b a))

private theorem product_inner_braid_right (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (productHom hD (ModuleHom.id B) (braidIso A C).hom).linearMap
      (rightGenerator B A C hD b a c y x z v) =
      phase (D := D) a c •
        rightGenerator B C A hD b c a y z x v := by
  simp only [rightGenerator, normalizedPair_input, TensorProduct.map_tmul]
  have hj := braid_restrict_jAt A C hD (a+c)
    ⟨(a,c), rfl⟩ (x ⊗ₜ[ℂ] z)
  change normalizedPair B (targetModule C A) hD b (a+c)
    (y ⊗ₜ[ℂ] restrict (braidIso A C).hom (a+c)
      (jAt A C hD (a+c) ⟨(a,c), rfl⟩ (x ⊗ₜ[ℂ] z))) v = _
  rw [hj]
  simp only [TensorProduct.comm_tmul, jAt]
  have hc (e e' : Discriminant D) (he : e' = e)
      (f : PairMultiplicity C A (c,a) →ₗ[ℂ] Multiplicity (targetModule C A) e') :
      normalizedPair B (targetModule C A) hD b e
        (y ⊗ₜ[ℂ] ((he ▸ f) (z ⊗ₜ[ℂ] x))) v =
        normalizedPair B (targetModule C A) hD b e'
          (y ⊗ₜ[ℂ] f (z ⊗ₜ[ℂ] x)) v := by
    subst e
    rfl
  rw [TensorProduct.tmul_smul, normalizedPair_smul]
  exact congrArg (fun t => phase (D := D) a c • t)
    (hc (a+c) (c+a) (add_comm c a) (j C A hD c a))

private theorem alpha_forward_generator (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (associatorIso A B C hD).hom.linearMap
      (leftGenerator A B C hD a b c x y z v) =
      F hD a b c • rightGenerator A B C hD a b c x y z v := by
  exact alpha_normalized A B C hD a b c v x y z

private theorem alpha_inverse_generator (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (associatorIso A B C hD).inv.linearMap
      (rightGenerator A B C hD a b c x y z v) =
      (F hD a b c)⁻¹ • leftGenerator A B C hD a b c x y z v := by
  change (associatorEquiv A B C hD).symm
    (rightGenerator A B C hD a b c x y z v) = _
  apply (associatorEquiv A B C hD).injective
  rw [LinearEquiv.apply_symm_apply, map_smul]
  change rightGenerator A B C hD a b c x y z v =
    (F hD a b c)⁻¹ • (associatorIso A B C hD).hom.linearMap
      (leftGenerator A B C hD a b c x y z v)
  rw [alpha_forward_generator, smul_smul,
    inv_mul_cancel₀ (associator_nonzero D hD a b c), one_smul]

private theorem hexagon_left_generator (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (hexagonLeftPath A B C hD).linearMap
      (leftGenerator A B C hD a b c x y z v) =
      (F hD a b c * phase (D := D) a (b+c) * F hD b c a) •
        rightGenerator B C A hD b c a y z x v := by
  rw [show (hexagonLeftPath A B C hD).linearMap =
      (associatorIso B C A hD).hom.linearMap.comp
        ((braidIso A (targetModule B C)).hom.linearMap.comp
          (associatorIso A B C hD).hom.linearMap) by rfl]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, alpha_forward_generator,
    map_smul, left_inner_braid]
  simp only [map_smul]
  rw [alpha_forward_generator]
  simp only [smul_smul, mul_assoc]

private theorem hexagon_left_generator_right (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (hexagonLeftPathRight A B C hD).linearMap
      (leftGenerator A B C hD a b c x y z v) =
      (phase (D := D) a b * F hD b a c * phase (D := D) a c) •
        rightGenerator B C A hD b c a y z x v := by
  rw [show (hexagonLeftPathRight A B C hD).linearMap =
      (productHom hD (ModuleHom.id B) (braidIso A C).hom).linearMap.comp
        ((associatorIso B A C hD).hom.linearMap.comp
          (productHom hD (braidIso A B).hom (ModuleHom.id C)).linearMap) by rfl]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    product_inner_braid_left, map_smul, alpha_forward_generator]
  simp only [map_smul]
  rw [product_inner_braid_right]
  simp only [smul_smul, mul_assoc]

private theorem hexagon_right_generator (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (hexagonRightPath A B C hD).linearMap
      (rightGenerator A B C hD a b c x y z v) =
      ((F hD a b c)⁻¹ * phase (D := D) (a+b) c *
        (F hD c a b)⁻¹) •
        leftGenerator C A B hD c a b z x y v := by
  rw [show (hexagonRightPath A B C hD).linearMap =
      (associatorIso C A B hD).inv.linearMap.comp
        ((braidIso (targetModule A B) C).hom.linearMap.comp
          (associatorIso A B C hD).inv.linearMap) by rfl]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    alpha_inverse_generator, map_smul, right_inner_braid]
  simp only [map_smul]
  rw [alpha_inverse_generator]
  simp only [smul_smul, mul_assoc]

private theorem hexagon_right_generator_right (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (v : Carrier D) :
    (hexagonRightPathRight A B C hD).linearMap
      (rightGenerator A B C hD a b c x y z v) =
      ((phase (D := D) b c * (F hD a c b)⁻¹ *
        phase (D := D) a c)) •
        leftGenerator C A B hD c a b z x y v := by
  rw [show (hexagonRightPathRight A B C hD).linearMap =
      (productHom hD (braidIso A C).hom (ModuleHom.id B)).linearMap.comp
        ((associatorIso A C B hD).inv.linearMap.comp
          (productHom hD (ModuleHom.id A) (braidIso B C).hom).linearMap) by rfl]
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    product_inner_braid_right, map_smul, alpha_inverse_generator]
  simp only [map_smul]
  rw [product_inner_braid_left]
  simp only [smul_smul, mul_assoc]

/-- First literal ModuleHom hexagon, with the exact requested endpoints. -/
theorem moduleMap_hexagon_left :
    (associatorIso B C A hD).hom.comp
      ((braidIso A (targetModule B C)).hom.comp
        (associatorIso A B C hD).hom) =
    (productHom hD (ModuleHom.id B)
      (braidIso A C).hom).comp
      ((associatorIso B A C hD).hom.comp
        (productHom hD
          (braidIso A B).hom (ModuleHom.id C))) := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro s
  change (hexagonLeftPath A B C hD).linearMap s =
    (hexagonLeftPathRight A B C hD).linearMap s
  apply E_L_induction A B C hD
    (fun s => (hexagonLeftPath A B C hD).linearMap s =
      (hexagonLeftPathRight A B C hD).linearMap s)
    (by simp) (fun x y hx hy => by simp only [map_add, hx, hy]) ?_ s
  intro a b c v x y z
  have hs := (div_eq_div_iff (associator_nonzero D hD b a c)
    (Omega_ne_zero D (1 : Matrix _ _ ℤ) (representative D a)
      (representative D (b+c)))).mp (scalar_h1 hD a b c)
  have hscalar : F hD a b c * phase (D := D) a (b+c) * F hD b c a =
      phase (D := D) a b * F hD b a c * phase (D := D) a c := by
    calc
      _ = (F hD a b c * F hD b c a) * phase (D := D) a (b+c) := by ring
      _ = (phase (D := D) a b * phase (D := D) a c) * F hD b a c := hs
      _ = _ := by ring
  let v' := transport D (representative D ((a+b)+c))
    (carry D hD (a+b) c) v
  have h : (hexagonLeftPath A B C hD).linearMap
        (leftGenerator A B C hD a b c x y z v') =
      (hexagonLeftPathRight A B C hD).linearMap
        (leftGenerator A B C hD a b c x y z v') := by
    rw [hexagon_left_generator, hexagon_left_generator_right, hscalar]
  simpa only [leftGenerator, v', normalizedPair_transport, E_L, ActualWeakModuleAssociator.leftElementary, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply] using h

/-- Second literal ModuleHom hexagon, with inverse associators in the exact
    directions prescribed by the original statement. -/
theorem moduleMap_hexagon_right :
    (associatorIso C A B hD).inv.comp
      ((braidIso (targetModule A B) C).hom.comp
        (associatorIso A B C hD).inv) =
    (productHom hD
      (braidIso A C).hom (ModuleHom.id B)).comp
      ((associatorIso A C B hD).inv.comp
        (productHom hD (ModuleHom.id A)
          (braidIso B C).hom)) := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro s
  change (hexagonRightPath A B C hD).linearMap s =
    (hexagonRightPathRight A B C hD).linearMap s
  apply E_R_induction A B C hD
    (fun s => (hexagonRightPath A B C hD).linearMap s =
      (hexagonRightPathRight A B C hD).linearMap s)
    (by simp) (fun x y hx hy => by simp only [map_add, hx, hy]) ?_ s
  intro a b c v x y z
  have hf1 := associator_nonzero D hD a b c
  have hf2 := associator_nonzero D hD c a b
  have hf3 := associator_nonzero D hD a c b
  have hs := (div_eq_div_iff (mul_ne_zero hf1 hf2)
    (Omega_ne_zero D (1 : Matrix _ _ ℤ) (representative D (a+b))
      (representative D c))).mp (scalar_h2 hD a b c)
  have hscalar : (F hD a b c)⁻¹ * phase (D := D) (a+b) c *
      (F hD c a b)⁻¹ =
      phase (D := D) b c * (F hD a c b)⁻¹ * phase (D := D) a c := by
    field_simp [hf1, hf2, hf3]
    linear_combination hs
  let v' := transport D (representative D (a+(b+c)))
    (carry D hD a (b+c)) v
  have h : (hexagonRightPath A B C hD).linearMap
        (rightGenerator A B C hD a b c x y z v') =
      (hexagonRightPathRight A B C hD).linearMap
        (rightGenerator A B C hD a b c x y z v') := by
    rw [hexagon_right_generator, hexagon_right_generator_right, hscalar]
  simpa only [rightGenerator, v', normalizedPair_transport, E_R, ActualWeakModuleAssociator.rightElementary, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply] using h

end Hexagons

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraidedCoherence
