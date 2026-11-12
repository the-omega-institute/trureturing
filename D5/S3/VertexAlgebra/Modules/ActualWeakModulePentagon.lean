/- SOURCE CANDIDATE: UNCOMPILED / UNACCEPTED.
   A module-map pentagon on the literal arbitrary-weak P. This does not assert
   the separate five-Hahn-field/sharedSeries pentagon (pending1667), any unit,
   triangle, braiding, native acceptance, or completion of the string/AdS goal. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductNaturality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModulePentagon

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates
open ActualWeakModuleHom (recordEquiv restrict)
open ActualWeakModuleScalarProbes (Coordinate coordinate tensorCoordinates tensorCoordinates_tmul)
open ActualWeakModuleUniversalField (P PairSector targetModule)
open ActualWeakModuleProductMultiplicity
open ActualWeakModuleAssociator
open ActualWeakModuleProductNaturality
open LatticeChargedQuotientScalar (carry)

universe u v w t s k
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section PairVectors
variable {X : Type u} {Y : Type v}
variable [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

/-- An elementary vector map INTO THE ORIGINAL P. This is just its literal lof
    with the prescribed inverse transport on the carrier, not a product map. -/
def normalizedPair (c d : Discriminant D) (w : PairMultiplicity A B (c,d)) :
    Carrier D →ₗ[ℂ] P A B :=
  (DirectSum.lof ℂ _ (PairSector A B) (c,d)).comp
    (((TensorProduct.mk ℂ (Carrier D) _).flip w).comp
      (transportInverse D (representative D (c+d)) (carry D hD c d)))

include D X Y A B hD instGX instMX instGY instMY in
private def normalizedPair_transport_proof (c d : Discriminant D)
    (w : PairMultiplicity A B (c,d)) (v : Carrier D) :
    normalizedPair A B hD c d w
      (transport D (representative D (c+d)) (carry D hD c d) v) =
      DirectSum.lof ℂ _ (PairSector A B) (c,d) (v ⊗ₜ[ℂ] w) := by
  change DirectSum.lof ℂ _ (PairSector A B) (c,d)
    (((transportLinearEquiv D (representative D (c+d)) (carry D hD c d)).symm
      ((transportLinearEquiv D (representative D (c+d)) (carry D hD c d)) v)) ⊗ₜ[ℂ] w) = _
  rw [LinearEquiv.symm_apply_apply]



/-- The unnormalized and normalized generators have identical range; all states
    are covered by the actual two-sided inverse, not a surjectivity premise. -/
theorem normalizedPair_transport {D : LatticeData} {X : Type u} {Y : Type v} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (hD : (gramReal D).PosDef) (c d : Discriminant D)
    (w : PairMultiplicity A B (c,d)) (v : Carrier D) :
    normalizedPair A B hD c d w
      (transport D (representative D (c+d)) (carry D hD c d) v) =
      DirectSum.lof ℂ _ (PairSector A B) (c,d) (v ⊗ₜ[ℂ] w) := by
  exact normalizedPair_transport_proof A B hD c d w v


include D X Y A B hD instGX instMX instGY instMY in
private def normalizedPair_smul_proof (c d : Discriminant D) (a : ℂ)
    (w : PairMultiplicity A B (c,d)) (v : Carrier D) :
    normalizedPair A B hD c d (a • w) v = a • normalizedPair A B hD c d w v := by
  change DirectSum.lof ℂ _ (PairSector A B) (c,d)
    (((transportInverse D (representative D (c+d)) (carry D hD c d)) v) ⊗ₜ[ℂ] (a • w)) =
    a • DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (((transportInverse D (representative D (c+d)) (carry D hD c d)) v) ⊗ₜ[ℂ] w)
  rw [TensorProduct.tmul_smul, map_smul]



theorem normalizedPair_smul {D : LatticeData} {X : Type u} {Y : Type v} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (hD : (gramReal D).PosDef) (c d : Discriminant D) (a : ℂ)
    (w : PairMultiplicity A B (c,d)) (v : Carrier D) :
    normalizedPair A B hD c d (a • w) v = a • normalizedPair A B hD c d w v := by
  exact normalizedPair_smul_proof A B hD c d a w v


include D X Y A B hD instGX instMX instGY instMY in
private def normalizedPair_single_proof (c d : Discriminant D)
    (w : PairMultiplicity A B (c,d)) (l : Charge D) (p : Oscillator D) :
    normalizedPair A B hD c d w (Finsupp.single l p) =
      ((epsilon D (-carry D hD c d) (carry D hD c d))⁻¹ *
        epsilon D l (-carry D hD c d)) •
      DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (Finsupp.single (l-carry D hD c d) p ⊗ₜ[ℂ] w) := by
  simp only [normalizedPair, LinearMap.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, transportInverse_single, ← TensorProduct.smul_tmul', map_smul]



/-- Visible root normalization, including its half-diagonal inverse sign. -/
theorem normalizedPair_single {D : LatticeData} {X : Type u} {Y : Type v} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (hD : (gramReal D).PosDef) (c d : Discriminant D)
    (w : PairMultiplicity A B (c,d)) (l : Charge D) (p : Oscillator D) :
    normalizedPair A B hD c d w (Finsupp.single l p) =
      ((epsilon D (-carry D hD c d) (carry D hD c d))⁻¹ *
        epsilon D l (-carry D hD c d)) •
      DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (Finsupp.single (l-carry D hD c d) p ⊗ₜ[ℂ] w) := by
  exact normalizedPair_single_proof A B hD c d w l p


include D X Y A B hD instGX instMX instGY instMY in
private def j_coordinate_proof (c d : Discriminant D) (w : PairMultiplicity A B (c,d))
    (r : Coordinate D) :
    tensorCoordinates ((j A B hD c d w).val.val (c,d)) r =
      ((epsilon D (-carry D hD c d) (carry D hD c d))⁻¹ *
        coordinate D r (Finsupp.single (-carry D hD c d) (1 : Oscillator D))) • w := by
  rw [j_val]
  change tensorCoordinates ((DirectSum.component ℂ _ (PairSector A B) (c,d))
    (DirectSum.lof ℂ _ _ (c,d) _)) r = _
  rw [DirectSum.component.lof_self, ground_single, ← TensorProduct.smul_tmul', map_smul]
  simp only [Finsupp.smul_apply, tensorCoordinates_tmul, smul_smul]



/-- The same original inverse normalization at an INNER nested multiplicity.
    Apply this at (c,d) and (b,c+d) in fourRight; neither factor is suppressed. -/
theorem j_coordinate {D : LatticeData} {X : Type u} {Y : Type v} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (hD : (gramReal D).PosDef) (c d : Discriminant D) (w : PairMultiplicity A B (c,d))
    (r : Coordinate D) :
    tensorCoordinates ((j A B hD c d w).val.val (c,d)) r =
      ((epsilon D (-carry D hD c d) (carry D hD c d))⁻¹ *
        coordinate D r (Finsupp.single (-carry D hD c d) (1 : Oscillator D))) • w := by
  exact j_coordinate_proof A B hD c d w r


end PairVectors

section PairInput
variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type t}
variable [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y]
variable [instGX' : AddCommGroup X'] [instMX' : Module ℂ X'] [instGY' : AddCommGroup Y'] [instMY' : Module ℂ Y']
variable {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y}
variable {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'}
variable (hD : (gramReal D).PosDef)

include D X Y X' Y' A B A' B' hD instGX instMX instGY instMY instGX' instMX' instGY' instMY' in
private def normalizedPair_input_proof (f : ModuleHom A' A) (g : ModuleHom B' B)
    (c d : Discriminant D) (w : PairMultiplicity A' B' (c,d)) (v : Carrier D) :
    (productHom hD f g).linearMap (normalizedPair A' B' hD c d w v) =
      normalizedPair A B hD c d (TensorProduct.map (restrict f c) (restrict g d) w) v := by
  exact productHom_pair hD f g c d
    (transportInverse D (representative D (c+d)) (carry D hD c d) v) w



theorem normalizedPair_input {D : LatticeData} {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type t} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGX' : AddCommGroup X'] [instMX' : Module ℂ X'] [instGY' : AddCommGroup Y'] [instMY' : Module ℂ Y'] {A : FullJacobiLatticeModule D X} {B : FullJacobiLatticeModule D Y} {A' : FullJacobiLatticeModule D X'} {B' : FullJacobiLatticeModule D Y'} (hD : (gramReal D).PosDef) (f : ModuleHom A' A) (g : ModuleHom B' B)
    (c d : Discriminant D) (w : PairMultiplicity A' B' (c,d)) (v : Carrier D) :
    (productHom hD f g).linearMap (normalizedPair A' B' hD c d w v) =
      normalizedPair A B hD c d (TensorProduct.map (restrict f c) (restrict g d) w) v := by
  exact normalizedPair_input_proof hD f g c d w v


end PairInput

section ThreeVectors
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y]
variable [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (C : FullJacobiLatticeModule D Z) (hD : (gramReal D).PosDef)

include D X Y Z A B C hD instGX instMX instGY instMY instGZ instMZ in
private def alpha_normalized_proof (a b c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    alpha A B C hD (normalizedPair (targetModule A B) C hD (a+b) c
      (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) v) =
      F hD a b c • normalizedPair A (targetModule B C) hD a (b+c)
        (x ⊗ₜ[ℂ] j B C hD b c (y ⊗ₜ[ℂ] z)) v := by
  change alpha A B C hD (E_L A B C hD a b c
    ((transportLinearEquiv D (representative D ((a+b)+c)) (carry D hD (a+b) c)).symm v)
    x y z) = _
  have hv : transport D (representative D ((a+b)+c)) (carry D hD (a+b) c)
      ((transportLinearEquiv D (representative D ((a+b)+c)) (carry D hD (a+b) c)).symm v) = v :=
    (transportLinearEquiv D (representative D ((a+b)+c)) (carry D hD (a+b) c)).apply_symm_apply v
  rw [alpha_E_L, hv]
  rfl



/-- Source alpha_E_L with the ACTUAL inverse outer transport. The cancellation
    is T*T^-1, so the inverse epsilon is retained, not set to one. -/
theorem alpha_normalized {D : LatticeData} {X : Type u} {Y : Type v} {Z : Type w} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (C : FullJacobiLatticeModule D Z) (hD : (gramReal D).PosDef) (a b c : Discriminant D) (v : Carrier D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    alpha A B C hD (normalizedPair (targetModule A B) C hD (a+b) c
      (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) v) =
      F hD a b c • normalizedPair A (targetModule B C) hD a (b+c)
        (x ⊗ₜ[ℂ] j B C hD b c (y ⊗ₜ[ℂ] z)) v := by
  exact alpha_normalized_proof A B C hD a b c v x y z


/-- Right-nested ORIGINAL multiplicity at the SAME left-associated weight as
    the source. Only equality transport in the supplied Fiber is used. -/
def rightNestedJ (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    Multiplicity (targetModule A (targetModule B C)) ((a+b)+c) :=
  jAt A (targetModule B C) hD ((a+b)+c)
    ⟨(a,b+c), (add_assoc a b c).symm⟩ (x ⊗ₜ[ℂ] j B C hD b c (y ⊗ₜ[ℂ] z))

set_option maxHeartbeats 2000000 in
include D X Y Z A B C hD instGX instMX instGY instMY instGZ instMZ in
private def restrict_alpha_nested_proof (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    restrict (associatorIso A B C hD).hom ((a+b)+c)
      (j (targetModule A B) C hD (a+b) c (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)) =
      F hD a b c • rightNestedJ A B C hD a b c x y z := by
  have hL := j_val (targetModule A B) C hD (a+b) c
    (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)
  have hR := jAt_val A (targetModule B C) hD ((a+b)+c)
    ⟨(a,b+c), (add_assoc a b c).symm⟩ (x ⊗ₜ[ℂ] j B C hD b c (y ⊗ₜ[ℂ] z))
  have h := (congrArg (alpha A B C hD) hL).trans
    ((alpha_normalized A B C hD a b c (Finsupp.single 0 (1 : Oscillator D)) x y z).trans
      (congrArg (fun q : P A (targetModule B C) => F hD a b c • q) hR.symm))
  exact Subtype.ext (Subtype.ext h)



set_option maxHeartbeats 2000000 in
/-- Actual restriction of alpha on a nested ground multiplicity. This is
    obtained by its full carrier formula at [0]1, with both j normalizations. -/
theorem restrict_alpha_nested {D : LatticeData} {X : Type u} {Y : Type v} {Z : Type w} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (C : FullJacobiLatticeModule D Z) (hD : (gramReal D).PosDef) (a b c : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c) :
    restrict (associatorIso A B C hD).hom ((a+b)+c)
      (j (targetModule A B) C hD (a+b) c (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)) =
      F hD a b c • rightNestedJ A B C hD a b c x y z := by
  exact restrict_alpha_nested_proof A B C hD a b c x y z


end ThreeVectors

private theorem map_smul_congr {V : Type s} {W : Type k}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) {v w : V} {a : ℂ} (h : v = a • w) :
    f v = a • f w :=
  (congrArg f h).trans (f.map_smul a w)

private theorem finite_sum_closed {V : Type s} [AddCommGroup V]
    (Q : V → Prop) (h0 : Q 0) (ha : ∀ a b, Q a → Q b → Q (a+b))
    {ι : Type k} (is : Finset ι) (f : ι → V) (hf : ∀ i ∈ is, Q (f i)) :
    Q (∑ i ∈ is, f i) := by
  classical
  induction is using Finset.induction_on with
  | empty => simpa using h0
  | @insert i is hi ih =>
      rw [Finset.sum_insert hi]
      exact ha _ _ (hf i (Finset.mem_insert_self i is))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

section FourInputs
variable {X : Type u} {Y : Type v} {Z : Type w} {T : Type t}
variable [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y]
variable [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] [instGT : AddCommGroup T] [instMT : Module ℂ T]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (C : FullJacobiLatticeModule D Z) (E : FullJacobiLatticeModule D T)
variable (hD : (gramReal D).PosDef)

/-- Four ORIGINAL multiplicity vectors with all three nested inverse transports. -/
def fourLeft (a b c d : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) : Carrier D →ₗ[ℂ] P (targetModule (targetModule A B) C) E :=
  normalizedPair (targetModule (targetModule A B) C) E hD ((a+b)+c) d
    (j (targetModule A B) C hD (a+b) c (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t)

def fourRight (a b c d : Discriminant D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) : Carrier D →ₗ[ℂ] P A (targetModule B (targetModule C E)) :=
  normalizedPair A (targetModule B (targetModule C E)) hD a (b+(c+d))
    (x ⊗ₜ[ℂ] j B (targetModule C E) hD b (c+d) (y ⊗ₜ[ℂ] j C E hD c d (z ⊗ₜ[ℂ] t)))

include D X Y Z T A B C E hD instGX instMX instGY instMY instGZ instMZ instGT instMT in
private def fourLeft_induction_proof
    (Q : P (targetModule (targetModule A B) C) E → Prop) (h0 : Q 0)
    (ha : ∀ a b, Q a → Q b → Q (a+b))
    (he : ∀ a b c d v x y z t, Q (fourLeft A B C E hD a b c d x y z t v))
    (s : P (targetModule (targetModule A B) C) E) : Q s := by
  let L (ab c d : Discriminant D) (v : Carrier D)
      (z : Multiplicity C c) (t : Multiplicity E d) :
      Multiplicity (targetModule A B) ab →ₗ[ℂ] P (targetModule (targetModule A B) C) E :=
    (DirectSum.lof ℂ _ (PairSector (targetModule (targetModule A B) C) E) (ab+c,d)).comp
      ((TensorProduct.mk ℂ (Carrier D) _ v).comp
        (((TensorProduct.mk ℂ _ _).flip t).comp
          ((j (targetModule A B) C hD ab c).comp ((TensorProduct.mk ℂ _ _).flip z))))
  have hp (a b c d : Discriminant D) (v : Carrier D)
      (w : PairMultiplicity A B (a,b)) (z : Multiplicity C c) (t : Multiplicity E d) :
      Q (E_L (targetModule A B) C E hD (a+b) c d v (j A B hD a b w) z t) := by
    let m := (L (a+b) c d v z t).comp (j A B hD a b)
    change Q (m w)
    induction w using TensorProduct.induction_on with
    | zero => exact (congrArg Q m.map_zero).mpr h0
    | add w w' hw hw' =>
        exact (congrArg Q (m.map_add w w')).mpr (ha _ _ hw hw')
    | tmul x y =>
        have hv := he a b c d
          (transport D (representative D (((a+b)+c)+d)) (carry D hD ((a+b)+c) d) v)
          x y z t
        exact (congrArg Q (normalizedPair_transport
          (targetModule (targetModule A B) C) E hD ((a+b)+c) d
          (j (targetModule A B) C hD (a+b) c
            (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t) v)).mp hv
  apply E_L_induction (targetModule A B) C E hD Q h0 ha ?_ s
  intro ab c d v q z t
  change Q (L ab c d v z t q)
  have hq := congrArg (fun q' => Q (L ab c d v z t q')) (nu_mu A B hD ab q)
  refine hq.mp ?_
  have hn := congrArg (L ab c d v z t) (nu_expansion A B hD ab (mu A B hD ab q))
  have hs := map_sum (L ab c d v z t)
    (fun i => jAt A B hD ab i (mu A B hD ab q i)) (mu A B hD ab q).support
  refine (congrArg Q (hn.trans hs)).mpr ?_
  apply finite_sum_closed Q h0 ha
  intro i hi
  rcases i with ⟨⟨a,b⟩,hab⟩
  subst ab
  exact hp a b c d v _ z t



/-- Finite generation of EVERY vector in the literal four-input source. Outer
    E_L generation is supplied; its remaining product multiplicity is expanded
    by actual nu_mu/nu_expansion over that vector's own finite support, followed
    by algebraic tensor induction. No new presentation or finiteness premise. -/
theorem fourLeft_induction {D : LatticeData} {X : Type u} {Y : Type v} {Z : Type w} {T : Type t} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] [instGT : AddCommGroup T] [instMT : Module ℂ T] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (C : FullJacobiLatticeModule D Z) (E : FullJacobiLatticeModule D T) (hD : (gramReal D).PosDef)
    (Q : P (targetModule (targetModule A B) C) E → Prop) (h0 : Q 0)
    (ha : ∀ a b, Q a → Q b → Q (a+b))
    (he : ∀ a b c d v x y z t, Q (fourLeft A B C E hD a b c d x y z t v))
    (s : P (targetModule (targetModule A B) C) E) : Q s := by
  exact fourLeft_induction_proof A B C E hD Q h0 ha he s


/-- Short pentagon path with the EXACT original full source and target. -/
def pentagonShort :
    ModuleHom (targetModule (targetModule (targetModule A B) C) E)
      (targetModule A (targetModule B (targetModule C E))) :=
  (associatorIso A B (targetModule C E) hD).hom.comp
    (associatorIso (targetModule A B) C E hD).hom

/-- Long pentagon path. Both P(-,-) arrows are the corrected inputMap transported
    through the original recordEquiv, with actual full identity/alpha records. -/
def pentagonLong :
    ModuleHom (targetModule (targetModule (targetModule A B) C) E)
      (targetModule A (targetModule B (targetModule C E))) :=
  (productHom hD (ModuleHom.id A) (associatorIso B C E hD).hom).comp
    ((associatorIso A (targetModule B C) E hD).hom.comp
      (productHom hD (associatorIso A B C hD).hom (ModuleHom.id E)))

include D X Y Z T A B C E hD instGX instMX instGY instMY instGZ instMZ instGT instMT in
private def pentagonShort_elementary_proof (a b c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) :
    (pentagonShort A B C E hD).linearMap (fourLeft A B C E hD a b c d x y z t v) =
      (F hD (a+b) c d * F hD a b (c+d)) • fourRight A B C E hD a b c d x y z t v := by
  change alpha A B (targetModule C E) hD
    (alpha (targetModule A B) C E hD (fourLeft A B C E hD a b c d x y z t v)) = _
  have hfirst := alpha_normalized (targetModule A B) C E hD (a+b) c d v
    (j A B hD a b (x ⊗ₜ[ℂ] y)) z t
  have hsecond := alpha_normalized A B (targetModule C E) hD a b (c+d) v
    x y (j C E hD c d (z ⊗ₜ[ℂ] t))
  exact (congrArg (alpha A B (targetModule C E) hD) hfirst).trans
    (((alpha A B (targetModule C E) hD).map_smul (F hD (a+b) c d) _).trans
      ((congrArg (fun q : P A (targetModule B (targetModule C E)) =>
        F hD (a+b) c d • q) hsecond).trans (smul_smul _ _ _)))



/-- The ACTUAL short path is identified on all four-input elementary vectors,
    for arbitrary full carrier states, before any use of scalar_pentagon. -/
theorem pentagonShort_elementary {D : LatticeData} {X : Type u} {Y : Type v} {Z : Type w} {T : Type t} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] [instGT : AddCommGroup T] [instMT : Module ℂ T] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (C : FullJacobiLatticeModule D Z) (E : FullJacobiLatticeModule D T) (hD : (gramReal D).PosDef) (a b c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) :
    (pentagonShort A B C E hD).linearMap (fourLeft A B C E hD a b c d x y z t v) =
      (F hD (a+b) c d * F hD a b (c+d)) • fourRight A B C E hD a b c d x y z t v := by
  exact pentagonShort_elementary_proof A B C E hD a b c d v x y z t


set_option maxHeartbeats 2000000 in
include D X Y Z T A B C E hD instGX instMX instGY instMY instGZ instMZ instGT instMT in
private def pentagonLong_elementary_proof (a b c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) :
    (pentagonLong A B C E hD).linearMap (fourLeft A B C E hD a b c d x y z t v) =
      (F hD a b c * F hD a (b+c) d * F hD b c d) •
        fourRight A B C E hD a b c d x y z t v := by
  let f := (productHom hD (ModuleHom.id A) (associatorIso B C E hD).hom).linearMap
  let g := alpha A (targetModule B C) E hD
  let n1 := normalizedPair (targetModule A (targetModule B C)) E hD ((a+b)+c) d
    (rightNestedJ A B C hD a b c x y z ⊗ₜ[ℂ] t) v
  let n2 := normalizedPair A (targetModule (targetModule B C) E) hD a ((b+c)+d)
    (x ⊗ₜ[ℂ] j (targetModule B C) E hD (b+c) d
      (j B C hD b c (y ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t)) v
  have h1 :
      (productHom hD (associatorIso A B C hD).hom (ModuleHom.id E)).linearMap
        (fourLeft A B C E hD a b c d x y z t v) = F hD a b c • n1 := by
    have hbase := normalizedPair_input hD (associatorIso A B C hD).hom (ModuleHom.id E)
      ((a+b)+c) d
      (j (targetModule A B) C hD (a+b) c
        (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t) v
    have hcoef := (TensorProduct.map_tmul
      (restrict (associatorIso A B C hD).hom ((a+b)+c)) (restrict (ModuleHom.id E) d)
      (j (targetModule A B) C hD (a+b) c
        (j A B hD a b (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)) t).trans
      (congrArg (fun q => q ⊗ₜ[ℂ] t) (restrict_alpha_nested A B C hD a b c x y z))
    have hs := ((TensorProduct.mk ℂ _ _).flip t).map_smul
      (F hD a b c) (rightNestedJ A B C hD a b c x y z)
    exact hbase.trans
      ((congrArg (fun q => normalizedPair (targetModule A (targetModule B C)) E hD
        ((a+b)+c) d q v) (hcoef.trans hs)).trans
          (normalizedPair_smul (targetModule A (targetModule B C)) E hD
            ((a+b)+c) d (F hD a b c)
            (rightNestedJ A B C hD a b c x y z ⊗ₜ[ℂ] t) v))
  have h2 : g n1 = F hD a (b+c) d • n2 := by
    have hn (e : Discriminant D) (heq : a+(b+c)=e) :
        alpha A (targetModule B C) E hD
          (normalizedPair (targetModule A (targetModule B C)) E hD e d
            (jAt A (targetModule B C) hD e ⟨(a,b+c),heq⟩
              (x ⊗ₜ[ℂ] j B C hD b c (y ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ] t) v) =
        F hD a (b+c) d • n2 := by
      subst e
      exact alpha_normalized A (targetModule B C) E hD a (b+c) d v
        x (j B C hD b c (y ⊗ₜ[ℂ] z)) t
    exact hn ((a+b)+c) (add_assoc a b c).symm
  have h3 : f n2 = F hD b c d • fourRight A B C E hD a b c d x y z t v := by
    have hbase := normalizedPair_input hD (ModuleHom.id A) (associatorIso B C E hD).hom
      a ((b+c)+d)
      (x ⊗ₜ[ℂ] j (targetModule B C) E hD (b+c) d
        (j B C hD b c (y ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t)) v
    have hcoef := (TensorProduct.map_tmul (restrict (ModuleHom.id A) a)
      (restrict (associatorIso B C E hD).hom ((b+c)+d))
      x (j (targetModule B C) E hD (b+c) d
        (j B C hD b c (y ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] t))).trans
      (congrArg (fun q => x ⊗ₜ[ℂ] q) (restrict_alpha_nested B C E hD b c d y z t))
    have hs := (TensorProduct.mk ℂ _ _ x).map_smul
      (F hD b c d) (rightNestedJ B C E hD b c d y z t)
    have hn (e : Discriminant D) (heq : b+(c+d)=e) :
        normalizedPair A (targetModule B (targetModule C E)) hD a e
          (x ⊗ₜ[ℂ] jAt B (targetModule C E) hD e ⟨(b,c+d),heq⟩
            (y ⊗ₜ[ℂ] j C E hD c d (z ⊗ₜ[ℂ] t))) v =
        fourRight A B C E hD a b c d x y z t v := by
      subst e
      rfl
    exact hbase.trans
      ((congrArg (fun q => normalizedPair A (targetModule B (targetModule C E)) hD
        a ((b+c)+d) q v) (hcoef.trans hs)).trans
          ((normalizedPair_smul A (targetModule B (targetModule C E)) hD a ((b+c)+d)
            (F hD b c d) (x ⊗ₜ[ℂ] rightNestedJ B C E hD b c d y z t) v).trans
              (congrArg (fun q => F hD b c d • q) (hn ((b+c)+d) (add_assoc b c d).symm))))
  change f (g ((productHom hD (associatorIso A B C hD).hom (ModuleHom.id E)).linearMap
    (fourLeft A B C E hD a b c d x y z t v))) = _
  have k1 := map_smul_congr f (map_smul_congr g h1)
  have k2 := map_smul_congr f h2
  exact k1.trans
    ((congrArg (fun q => F hD a b c • q) k2).trans
      ((congrArg (fun q => F hD a b c • (F hD a (b+c) d • q)) h3).trans
        ((smul_smul (F hD a b c) (F hD a (b+c) d)
          (F hD b c d • fourRight A B C E hD a b c d x y z t v)).trans
          (smul_smul (F hD a b c * F hD a (b+c) d) (F hD b c d)
            (fourRight A B C E hD a b c d x y z t v)))))



set_option maxHeartbeats 2000000 in
/-- The ACTUAL long path is separately identified. The two P-arrow calculations
    use restriction on the ORIGINAL nested subtypes, including normalized j. -/
theorem pentagonLong_elementary {D : LatticeData} {X : Type u} {Y : Type v} {Z : Type w} {T : Type t} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] [instGT : AddCommGroup T] [instMT : Module ℂ T] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (C : FullJacobiLatticeModule D Z) (E : FullJacobiLatticeModule D T) (hD : (gramReal D).PosDef) (a b c d : Discriminant D) (v : Carrier D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) :
    (pentagonLong A B C E hD).linearMap (fourLeft A B C E hD a b c d x y z t v) =
      (F hD a b c * F hD a (b+c) d * F hD b c d) •
        fourRight A B C E hD a b c d x y z t v := by
  exact pentagonLong_elementary_proof A B C E hD a b c d v x y z t


include D X Y Z T A B C E hD instGX instMX instGY instMY instGZ instMZ instGT instMT in
private def fourRight_coordinate_proof (a b c d : Discriminant D) (l : Charge D)
    (p : Oscillator D) (r : Coordinate D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) :
    tensorCoordinates ((fourRight A B C E hD a b c d x y z t (Finsupp.single l p)) (a,b+(c+d))) r =
      ((epsilon D (-carry D hD a (b+(c+d))) (carry D hD a (b+(c+d))))⁻¹ *
        epsilon D l (-carry D hD a (b+(c+d))) *
        coordinate D r (Finsupp.single (l-carry D hD a (b+(c+d))) p)) •
      (x ⊗ₜ[ℂ] j B (targetModule C E) hD b (c+d) (y ⊗ₜ[ℂ] j C E hD c d (z ⊗ₜ[ℂ] t))) := by
  change tensorCoordinates
    ((DirectSum.component ℂ _ (PairSector A (targetModule B (targetModule C E))) (a,b+(c+d)))
      (normalizedPair A (targetModule B (targetModule C E)) hD a (b+(c+d))
        (x ⊗ₜ[ℂ] j B (targetModule C E) hD b (c+d)
          (y ⊗ₜ[ℂ] j C E hD c d (z ⊗ₜ[ℂ] t))) (Finsupp.single l p))) r = _
  simp only [normalizedPair_single, map_smul, DirectSum.component.lof_self,
    Finsupp.smul_apply, tensorCoordinates_tmul, smul_smul]



/-- Coefficient of the ORIGINAL target tensor at any carrier charge/monomial.
    The two inner j factors are the original subtypes, whose raw values are
    exactly j_val/ground_single, with their two further epsilon(-n,n)^-1 signs. -/
theorem fourRight_coordinate {D : LatticeData} {X : Type u} {Y : Type v} {Z : Type w} {T : Type t} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] [instGT : AddCommGroup T] [instMT : Module ℂ T] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (C : FullJacobiLatticeModule D Z) (E : FullJacobiLatticeModule D T) (hD : (gramReal D).PosDef) (a b c d : Discriminant D) (l : Charge D)
    (p : Oscillator D) (r : Coordinate D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) :
    tensorCoordinates ((fourRight A B C E hD a b c d x y z t (Finsupp.single l p)) (a,b+(c+d))) r =
      ((epsilon D (-carry D hD a (b+(c+d))) (carry D hD a (b+(c+d))))⁻¹ *
        epsilon D l (-carry D hD a (b+(c+d))) *
        coordinate D r (Finsupp.single (l-carry D hD a (b+(c+d))) p)) •
      (x ⊗ₜ[ℂ] j B (targetModule C E) hD b (c+d) (y ⊗ₜ[ℂ] j C E hD c d (z ⊗ₜ[ℂ] t))) := by
  exact fourRight_coordinate_proof A B C E hD a b c d l p r x y z t


set_option maxHeartbeats 2000000 in
include D X Y Z T A B C E hD instGX instMX instGY instMY instGZ instMZ instGT instMT in
private def pentagon_path_coordinates_proof (a b c d : Discriminant D) (l : Charge D)
    (p : Oscillator D) (cd : Discriminant D × Discriminant D) (r : Coordinate D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) :
    let e := fourLeft A B C E hD a b c d x y z t (Finsupp.single l p)
    let terminal := tensorCoordinates
      ((fourRight A B C E hD a b c d x y z t (Finsupp.single l p)) cd) r
    tensorCoordinates (((pentagonShort A B C E hD).linearMap e) cd) r =
        (F hD (a+b) c d * F hD a b (c+d)) • terminal ∧
      tensorCoordinates (((pentagonLong A B C E hD).linearMap e) cd) r =
        (F hD a b c * F hD a (b+c) d * F hD b c d) • terminal := by
  constructor
  · have hp := congrArg
      (fun q : P A (targetModule B (targetModule C E)) => tensorCoordinates (q cd) r)
      (pentagonShort_elementary A B C E hD a b c d (Finsupp.single l p) x y z t)
    have hs := congrArg
      (fun q : Coordinate D →₀ PairMultiplicity A (targetModule B (targetModule C E)) cd => q r)
      ((tensorCoordinates (D := D)).map_smul (F hD (a+b) c d * F hD a b (c+d))
        ((fourRight A B C E hD a b c d x y z t (Finsupp.single l p)) cd))
    exact hp.trans hs

  · have hp := congrArg
      (fun q : P A (targetModule B (targetModule C E)) => tensorCoordinates (q cd) r)
      (pentagonLong_elementary A B C E hD a b c d (Finsupp.single l p) x y z t)
    have hs := congrArg
      (fun q : Coordinate D →₀ PairMultiplicity A (targetModule B (targetModule C E)) cd => q r)
      ((tensorCoordinates (D := D)).map_smul (F hD a b c * F hD a (b+c) d * F hD b c d)
        ((fourRight A B C E hD a b c d x y z t (Finsupp.single l p)) cd))
    exact hp.trans hs



set_option maxHeartbeats 2000000 in
/-- Both actual paths have the same ORIGINAL terminal tensor coefficient apart
    from the displayed scalar products. This precedes scalar_pentagon. -/
theorem pentagon_path_coordinates {D : LatticeData} {X : Type u} {Y : Type v} {Z : Type w} {T : Type t} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] [instGT : AddCommGroup T] [instMT : Module ℂ T] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (C : FullJacobiLatticeModule D Z) (E : FullJacobiLatticeModule D T) (hD : (gramReal D).PosDef) (a b c d : Discriminant D) (l : Charge D)
    (p : Oscillator D) (cd : Discriminant D × Discriminant D) (r : Coordinate D)
    (x : Multiplicity A a) (y : Multiplicity B b) (z : Multiplicity C c)
    (t : Multiplicity E d) :
    let e := fourLeft A B C E hD a b c d x y z t (Finsupp.single l p)
    let terminal := tensorCoordinates
      ((fourRight A B C E hD a b c d x y z t (Finsupp.single l p)) cd) r
    tensorCoordinates (((pentagonShort A B C E hD).linearMap e) cd) r =
        (F hD (a+b) c d * F hD a b (c+d)) • terminal ∧
      tensorCoordinates (((pentagonLong A B C E hD).linearMap e) cd) r =
        (F hD a b c * F hD a (b+c) d * F hD b c d) • terminal := by
  exact pentagon_path_coordinates_proof A B C E hD a b c d l p cd r x y z t


include D X Y Z T A B C E hD instGX instMX instGY instMY instGZ instMZ instGT instMT in
private def moduleMap_pentagon_proof : pentagonShort A B C E hD = pentagonLong A B C E hD := by
  apply (recordEquiv _ _).injective
  apply Subtype.ext
  apply LinearMap.ext
  intro s
  change (pentagonShort A B C E hD).linearMap s = (pentagonLong A B C E hD).linearMap s
  apply fourLeft_induction A B C E hD
    (fun s => (pentagonShort A B C E hD).linearMap s = (pentagonLong A B C E hD).linearMap s)
    (((pentagonShort A B C E hD).linearMap.map_zero).trans
      ((pentagonLong A B C E hD).linearMap.map_zero).symm)
    (fun a b ha hb =>
      ((pentagonShort A B C E hD).linearMap.map_add a b).trans
        ((congrArg₂ (fun q q' : P A (targetModule B (targetModule C E)) => q + q') ha hb).trans
          ((pentagonLong A B C E hD).linearMap.map_add a b).symm)) ?_ s
  intro a b c d v x y z t
  have hscalar := LatticeChargedQuotientScalar.scalar_pentagon D hD a b c d
  change F hD a b c * F hD a (b+c) d * F hD b c d =
    F hD (a+b) c d * F hD a b (c+d) at hscalar
  exact (pentagonShort_elementary A B C E hD a b c d v x y z t).trans
    ((congrArg (fun k : ℂ => k • fourRight A B C E hD a b c d x y z t v)
      hscalar.symm).trans (pentagonLong_elementary A B C E hD a b c d v x y z t).symm)



/-- Full MODULE-MAP Mac Lane pentagon. Scalar pentagon is consumed only here,
    after BOTH actual paths have been calculated. Finite four-input generation
    extends their equality to ALL original vectors, including every zero branch.
    This is separate from the pending five-Hahn-field/sharedSeries problem. -/
theorem moduleMap_pentagon {D : LatticeData} {X : Type u} {Y : Type v} {Z : Type w} {T : Type t} [instGX : AddCommGroup X] [instMX : Module ℂ X] [instGY : AddCommGroup Y] [instMY : Module ℂ Y] [instGZ : AddCommGroup Z] [instMZ : Module ℂ Z] [instGT : AddCommGroup T] [instMT : Module ℂ T] (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y) (C : FullJacobiLatticeModule D Z) (E : FullJacobiLatticeModule D T) (hD : (gramReal D).PosDef) : pentagonShort A B C E hD = pentagonLong A B C E hD := by
  exact moduleMap_pentagon_proof A B C E hD


end FourInputs
end D5.S3.VertexAlgebra.Modules.ActualWeakModulePentagon
