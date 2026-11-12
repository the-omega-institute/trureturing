/-
SOURCE CANDIDATE: no compiler or kernel acceptance is asserted.
The product is literally the pinned UniversalField.P / targetModule (U72).
Accepted99 supplies classification, finite tensor coordinates and algebraic
separation; the independently accepted transport supplies vacuum cyclicity.
The scalar carry supplier is the exact source 13 of the sealed Pro question.
No representing equivalence, input bifunctor, or primitive field is assumed.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleUniversalField
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
import D5.S3.VertexAlgebra.Modules.FullJacobiModuleMaps
import D5.S3.VertexAlgebra.Sectors.LatticeSectorGroundRigidity
import D5.S3.VertexAlgebra.Sectors.LatticeChargedQuotientScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductMultiplicity

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeDualCosetModule LatticeDualCosetTransport
open LatticeSugawaraCurrents LatticeSectorIntertwiner
open FullJacobiCurrentTransport FullJacobiIntertwiner
open FullJacobiTensorModule FullJacobiDirectSum
open ActualCurrentTaylor ActualGroundJointWeights ActualGroundChargedSelection
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleScalarProbes
open ActualWeakModuleUniversalField (P PairSector targetModule)
open LatticeChargedQuotientScalar (carry carry_equation)

open private currentState_single inverseGram_left from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification
open private jointWeightMap from D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
open private gramMap_injective class_representative class_add class_gram from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

universe u v w
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Coordinates
variable {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- Current readback at one ORIGINAL charge, for an arbitrary carrier vector. -/
theorem current_charge (a : Charge D) (i : Fin D.rank) (m : ℤ)
    (x : Carrier D) (l : Charge D) :
    current (sectorModule D a) i m x l =
      shiftedCurrentPolynomial D a 1 i l m (x l) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | single k f =>
    rw [current, currentState_single, sectorModule_mode, action_current_coefficients]
    by_cases h : k = l
    · subst k; simp
    · simp [Finsupp.single_apply, h, Ne.symm h]

/-- The accepted scalar ground theorem is used once on each original charge.
Its inverse-Gram hypothesis comes from the ORIGINAL positive Gram matrix. -/
theorem ground_charge (hD : (gramReal D).PosDef) (a : Charge D)
    (x : Omega (sectorModule D a)) (l : Charge D) :
    x.val l = (x.val l).constantCoeff • (1 : Oscillator D) := by
  apply scalar_of_positive_currents D (inverseGram hD) (inverseGram_left hD) l
  intro i r
  have h := congrArg (fun z : Carrier D => z l)
    ((mem_Omega (sectorModule D a) x.val).mp x.property i r)
  rw [current_charge] at h
  simpa [shiftedCurrentPolynomial, neutralPolynomialMode,
    show ¬ ((r : ℤ) + 1 < 0) by omega,
    show (r : ℤ) + 1 ≠ 0 by omega, weightedPartial] using h

/-- Every nonconstant oscillator ActualWeakModuleScalarProbes.coordinate vanishes. This is a statement
about the original finite monomial coordinates, with arbitrary W. -/
theorem ground_nonconstant_coordinate (hD : (gramReal D).PosDef) (a : Charge D)
    (x : Omega (tensorModule (sectorModule D a) W))
    (l : Charge D) (d : Index D →₀ ℕ) (hd : d ≠ 0) :
    tensorCoordinates x.val (l,d) = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro ell
  let f := contractHom (sectorModule D a) ell
  have hc : contract ell x.val ∈ Omega (sectorModule D a) := by
    apply (mem_Omega _ _).mpr
    intro i r
    change mode (sectorModule D a) (currentState D i) ((r : ℤ)+1)
      (f.linearMap x.val) = 0
    rw [← f.intertwines (currentState D i) ((r : ℤ)+1) x.val]
    change f.linearMap (current (tensorModule (sectorModule D a) W) i ((r : ℤ)+1) x.val) = 0
    rw [(mem_Omega _ _).mp x.property i r, map_zero]
  rw [dual_tensorCoordinates, coordinate_apply]
  have hs := ground_charge hD a ⟨contract ell x.val,hc⟩ l
  rw [hs]
  simp [MvPolynomial.coeff_one, hd, Ne.symm hd]

/-- Finite ground expansion of ONE tensor, in the original coordinates. -/
theorem ground_expansion (hD : (gramReal D).PosDef) (a : Charge D)
    (x : Omega (tensorModule (sectorModule D a) W)) :
    x.val = ∑ r ∈ (tensorCoordinates x.val).support,
      Finsupp.single r.1 (1 : Oscillator D) ⊗ₜ[ℂ]
        tensorCoordinates x.val (r.1,0) := by
  conv_lhs => rw [← tensorCoordinates_expansion x.val]
  apply Finset.sum_congr rfl
  rintro ⟨l,d⟩ hr
  by_cases hd : d = 0
  · subst d; simp
  · have hz := ground_nonconstant_coordinate hD a x l d hd
    have hn : tensorCoordinates x.val (l,d) ≠ 0 := Finsupp.mem_support_iff.mp hr
    exact (hn hz).elim

/-- The zero-current equation is imposed AFTER positive-current exhaustion. -/
theorem joint_coordinate_weight (a b : Charge D)
    (x : jointWeight (tensorModule (sectorModule D a) W) b)
    (l : Charge D) (i : Fin D.rank) :
    (((a + gramMap D l) i : ℤ) : ℂ) • tensorCoordinates x.val.val (l,0) =
      (b i : ℂ) • tensorCoordinates x.val.val (l,0) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro ell
  let f := contractHom (sectorModule D a) ell
  have hx := (mem_jointWeight_iff _ b x.val).mp x.property i
  have he : current (sectorModule D a) i 0 (contract ell x.val.val) =
      (b i : ℂ) • contract ell x.val.val := by
    calc
      _ = contract ell (current (tensorModule (sectorModule D a) W) i 0 x.val.val) :=
        (f.intertwines (currentState D i) 0 x.val.val).symm
      _ = _ := by rw [hx,map_smul]
  have hc := congrArg (fun y : Carrier D => (y l).coeff 0) he
  rw [current_charge] at hc
  simp only [map_sub,map_smul,dual_tensorCoordinates]
  apply sub_eq_zero.mpr
  have hg : (gramMap D l) i = bilinear D (unitCharge D i) l := gram_mulVec_unit l i
  simpa [shiftedCurrentPolynomial,ActualWeakModuleScalarProbes.coordinate,hg,add_comm] using hc

/-- An incompatible original charge has zero coefficient, even for zero W. -/
theorem joint_wrong_charge (a b : Charge D)
    (x : jointWeight (tensorModule (sectorModule D a) W) b)
    (l : Charge D) (hl : a + gramMap D l ≠ b) :
    tensorCoordinates x.val.val (l,0) = 0 := by
  obtain ⟨i,hi⟩ : ∃ i, (a + gramMap D l) i ≠ b i := by
    by_contra! hn
    exact hl (funext hn)
  have h := joint_coordinate_weight a b x l i
  have hz : (((a + gramMap D l) i : ℂ) - (b i : ℂ)) •
      tensorCoordinates x.val.val (l,0) = 0 := by rw [sub_smul,h,sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hi))

/-- All joint-weight coordinates are exhausted by the ORIGINAL equation
`a + G l = b`, with no chosen basis of W. -/
theorem joint_coordinate_exhaustion (hD : (gramReal D).PosDef) (a b : Charge D)
    (x : jointWeight (tensorModule (sectorModule D a) W) b)
    (r : Coordinate D) (hr : r.2 ≠ 0 ∨ a + gramMap D r.1 ≠ b) :
    tensorCoordinates x.val.val r = 0 := by
  rcases hr with hd | hl
  · exact ground_nonconstant_coordinate hD a x.val r.1 r.2 hd
  · by_cases hd : r.2 = 0
    · obtain ⟨l,d⟩ := r; dsimp at hd; subst d
      exact joint_wrong_charge a b x l hl
    · exact ground_nonconstant_coordinate hD a x.val r.1 r.2 hd

/-- The class equation has no solution on a wrong product summand. -/
theorem pair_weight_implies_sum (c d e : Discriminant D) (l : Charge D)
    (hl : representative D c + representative D d + gramMap D l = representative D e) :
    c+d = e := by
  have h := congrArg (classOf D) hl
  simpa only [class_add,class_gram,class_representative,add_zero] using h

/-- Original G injectivity gives the UNIQUE surviving charge. -/
theorem pair_weight_iff (hD : (gramReal D).PosDef) (c d e : Discriminant D)
    (l : Charge D) :
    representative D c + representative D d + gramMap D l = representative D e ↔
      c+d=e ∧ l = -carry D hD c d := by
  constructor
  · intro hl
    have he := pair_weight_implies_sum c d e l hl
    refine ⟨he,?_⟩
    apply gramMap_injective D hD
    have hn := carry_equation D hD c d
    rw [← he,hn] at hl
    rw [map_neg]
    linear_combination (norm := module) hl
  · rintro ⟨rfl,rfl⟩
    rw [carry_equation D hD c d,map_neg]
    abel

/-- A single surviving ActualWeakModuleScalarProbes.coordinate reconstructs the entire tensor. -/
theorem joint_single_charge (hD : (gramReal D).PosDef) (a b l : Charge D)
    (hl : ∀ k, a + gramMap D k = b ↔ k=l)
    (x : jointWeight (tensorModule (sectorModule D a) W) b) :
    x.val.val = Finsupp.single l (1 : Oscillator D) ⊗ₜ[ℂ]
      tensorCoordinates x.val.val (l,0) := by
  apply (tensorCoordinates (D := D) (W := W)).injective
  apply Finsupp.ext
  rintro ⟨k,d⟩
  by_cases hk : k=l
  · subst k
    by_cases hd : d=0
    · subst d; simp [ActualWeakModuleScalarProbes.coordinate]
    · rw [ground_nonconstant_coordinate hD a x.val l d hd]
      simp [ActualWeakModuleScalarProbes.coordinate,MvPolynomial.coeff_one,hd,Ne.symm hd]
  · rw [joint_coordinate_exhaustion hD a b x (k,d)
        (Or.inr (fun h => hk ((hl k).mp h)))]
    simp [ActualWeakModuleScalarProbes.coordinate,Finsupp.single_apply,Ne.symm hk]

/-- No support whatsoever in a wrong discriminant class, for arbitrary W. -/
theorem pair_joint_zero (hD : (gramReal D).PosDef) (c d e : Discriminant D)
    (hne : c+d≠e)
    (x : jointWeight
      (tensorModule (sectorModule D (representative D c+representative D d)) W)
      (representative D e)) : x.val.val = 0 := by
  apply (tensorCoordinates (D := D) (W := W)).injective
  apply Finsupp.ext
  rintro ⟨l,f⟩
  rw [map_zero,Finsupp.zero_apply]
  exact joint_coordinate_exhaustion hD _ _ x (l,f)
    (Or.inr (fun h => hne (pair_weight_implies_sum c d e l h)))

/-- In the equal class the UNIQUE surviving original charge is -n(c,d). -/
theorem pair_joint_single (hD : (gramReal D).PosDef) (c d : Discriminant D)
    (x : jointWeight
      (tensorModule (sectorModule D (representative D c+representative D d)) W)
      (representative D (c+d))) :
    x.val.val = Finsupp.single (-carry D hD c d) (1 : Oscillator D) ⊗ₜ[ℂ]
      tensorCoordinates x.val.val (-carry D hD c d,0) := by
  apply joint_single_charge hD _ _ _ ?_ x
  intro l
  rw [pair_weight_iff hD]
  simp only [true_and]

end Coordinates

section Product
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

abbrev PairMultiplicity (cd : Discriminant D × Discriminant D) :=
  Multiplicity A cd.1 ⊗[ℂ] Multiplicity B cd.2
abbrev Fiber (e : Discriminant D) :=
  {cd : Discriminant D × Discriminant D // cd.1+cd.2=e}
abbrev FiberSum (e : Discriminant D) :=
  ⨁ i : Fiber (D := D) e, PairMultiplicity A B i.val

/-- The parameter is exactly the one in the actual carry equation. -/
theorem pair_shift (c d : Discriminant D) :
    shiftedCharge D (representative D (c+d)) (carry D hD c d) =
      representative D c + representative D d := by
  exact (carry_equation D hD c d).symm

/-- The normalized inverse vacuum; its half-diagonal sign is retained. -/
def ground (c d : Discriminant D) : Carrier D :=
  transportInverse D (representative D (c+d)) (carry D hD c d)
    (Finsupp.single 0 (1 : Oscillator D))

@[simp] theorem ground_single (c d : Discriminant D) :
    ground hD c d = (epsilon D (-carry D hD c d) (carry D hD c d))⁻¹ •
      Finsupp.single (-carry D hD c d) (1 : Oscillator D) := by
  simp [ground,transportInverse_single]

/-- A component is an actual full module map, independently of its weight. -/
def pairProjection (cd : Discriminant D × Discriminant D) :
    ModuleHom (targetModule A B)
      (tensorModule (sectorModule D (representative D cd.1 + representative D cd.2))
        (PairMultiplicity A B cd)) := projectionHom _ cd

/-- The concrete nested-subtype projection; original weights are preserved. -/
def weightComponent (e : Discriminant D) (cd : Discriminant D × Discriminant D) :
    Multiplicity (targetModule A B) e →ₗ[ℂ]
      jointWeight
        (tensorModule (sectorModule D (representative D cd.1+representative D cd.2))
          (PairMultiplicity A B cd)) (representative D e) :=
  jointWeightMap (pairProjection A B cd) (representative D e)

@[simp] theorem weightComponent_val (e : Discriminant D)
    (cd : Discriminant D × Discriminant D) (x : Multiplicity (targetModule A B) e) :
    (weightComponent A B e cd x).val.val = x.val.val cd := rfl

/-- Membership uses the original positive and zero modes, on the literal
inverse-vacuum tensor and its literal direct-sum inclusion. -/
theorem j_mem (c d : Discriminant D) (w : PairMultiplicity A B (c,d)) :
    let v := DirectSum.lof ℂ _ (PairSector A B) (c,d) (ground hD c d ⊗ₜ[ℂ] w)
    v ∈ Omega (targetModule A B) ∧ ∀ i : Fin D.rank,
      current (targetModule A B) i 0 v = (representative D (c+d) i : ℂ) • v := by
  let v := DirectSum.lof ℂ _ (PairSector A B) (c,d) (ground hD c d ⊗ₜ[ℂ] w)
  have hcur (i : Fin D.rank) (m : ℤ) :
      current (targetModule A B) i m v =
        DirectSum.lof ℂ _ (PairSector A B) (c,d)
          ((transportInverse D (representative D (c+d)) (carry D hD c d)
            (current (sectorModule D (representative D (c+d))) i m
              (Finsupp.single 0 (1 : Oscillator D)))) ⊗ₜ[ℂ] w) := by
    change mode (targetModule A B) (currentState D i) m
      (DirectSum.lof ℂ _ (PairSector A B) (c,d) (ground hD c d ⊗ₜ[ℂ] w)) = _
    unfold targetModule
    rw [directSumModule_mode,DirectSum.lmap_lof,tensorModule_mode,
      TensorProduct.map_tmul,LinearMap.id_apply]
    congr 2
    simpa only [ground,current,sectorModule_mode,pair_shift hD c d] using
      (transportInverse_all_modes D (representative D (c+d)) (carry D hD c d)
        (currentState D i) (Finsupp.single 0 (1 : Oscillator D)) m).symm
  have hbase (i : Fin D.rank) (m : ℤ) :
      current (sectorModule D (representative D (c+d))) i m
        (Finsupp.single 0 (1 : Oscillator D)) =
      Finsupp.single 0 (shiftedCurrentPolynomial D (representative D (c+d)) 1 i 0 m 1) := by
    rw [current,currentState_single,sectorModule_mode,action_current_coefficients]
  have hv : v ∈ Omega (targetModule A B) := by
    apply (mem_Omega _ _).mpr
    intro i r
    rw [hcur,hbase]
    simp [shiftedCurrentPolynomial,show ¬ ((r : ℤ)+1<0) by omega,
      show (r : ℤ)+1≠0 by omega]
  refine ⟨hv,?_⟩
  intro i
  have hz : current (sectorModule D (representative D (c+d))) i 0
      (Finsupp.single 0 (1 : Oscillator D)) =
      (representative D (c+d) i : ℂ) • Finsupp.single 0 (1 : Oscillator D) := by
    rw [hbase]
    simp [shiftedCurrentPolynomial, bilinear]
  rw [hcur,hz]
  simp only [map_smul,← TensorProduct.smul_tmul']
  rfl

/-- The ACTUAL nested subtype map j_cd, with no replacement multiplicity. -/
def j (c d : Discriminant D) :
    PairMultiplicity A B (c,d) →ₗ[ℂ] Multiplicity (targetModule A B) (c+d) where
  toFun w := ⟨⟨DirectSum.lof ℂ _ (PairSector A B) (c,d) (ground hD c d ⊗ₜ[ℂ] w),
    (j_mem A B hD c d w).1⟩,
    (mem_jointWeight_iff _ _ _).mpr (j_mem A B hD c d w).2⟩
  map_add' x y := by
    apply Subtype.ext; apply Subtype.ext
    simp only [TensorProduct.tmul_add,map_add,Submodule.coe_add]
  map_smul' a x := by
    apply Subtype.ext; apply Subtype.ext
    simp only [TensorProduct.tmul_smul,map_smul,Submodule.coe_smul,RingHom.id_apply]

@[simp] theorem j_val (c d : Discriminant D) (w : PairMultiplicity A B (c,d)) :
    (j A B hD c d w).val.val = DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (ground hD c d ⊗ₜ[ℂ] w) := rfl

/-- Equality transport is on the ORIGINAL nested subtype. -/
def jAt (e : Discriminant D) (i : Fiber (D := D) e) :
    PairMultiplicity A B i.val →ₗ[ℂ] Multiplicity (targetModule A B) e := by
  rcases i with ⟨⟨c,d⟩,hi⟩
  subst e
  exact j A B hD c d

@[simp] theorem jAt_val (e : Discriminant D) (i : Fiber (D := D) e)
    (w : PairMultiplicity A B i.val) :
    (jAt A B hD e i w).val.val = DirectSum.lof ℂ _ (PairSector A B) i.val
      (ground hD i.val.1 i.val.2 ⊗ₜ[ℂ] w) := by
  rcases i with ⟨⟨c,d⟩,hi⟩; subst e; rfl

/-- The coefficient carries epsilon(-n,n), the inverse of ground's factor. -/
def coefficient (cd : Discriminant D × Discriminant D) :
    PairSector A B cd →ₗ[ℂ] PairMultiplicity A B cd :=
  epsilon D (-carry D hD cd.1 cd.2) (carry D hD cd.1 cd.2) •
    ((Finsupp.lapply (-carry D hD cd.1 cd.2,0)).comp
      (tensorCoordinates (D := D)).toLinearMap)

@[simp] theorem coefficient_ground (cd : Discriminant D × Discriminant D)
    (w : PairMultiplicity A B cd) :
    coefficient A B hD cd (ground hD cd.1 cd.2 ⊗ₜ[ℂ] w) = w := by
  simp [coefficient,ground_single,tensorCoordinates_tmul,ActualWeakModuleScalarProbes.coordinate,
    smul_smul,LatticeChargedTransport.epsilon_nonzero]

include hD in
/-- Wrong summands vanish; no finiteness of the discriminant is used. -/
theorem component_wrong (e : Discriminant D) (x : Multiplicity (targetModule A B) e)
    (cd : Discriminant D × Discriminant D) (he : cd.1+cd.2≠e) : x.val.val cd = 0 := by
  apply (tensorCoordinates (D := D)).injective
  apply Finsupp.ext
  rintro ⟨l,d⟩
  rw [map_zero,Finsupp.zero_apply]
  exact joint_coordinate_exhaustion hD _ _ (weightComponent A B e cd x) (l,d)
    (Or.inr (fun h => he (pair_weight_implies_sum cd.1 cd.2 e l h)))

theorem component_reconstruct (e : Discriminant D)
    (x : Multiplicity (targetModule A B) e) (cd : Discriminant D × Discriminant D)
    (he : cd.1+cd.2=e) :
    x.val.val cd = ground hD cd.1 cd.2 ⊗ₜ[ℂ] coefficient A B hD cd (x.val.val cd) := by
  have hs := joint_single_charge hD (representative D cd.1+representative D cd.2)
    (representative D e) (-carry D hD cd.1 cd.2)
    (fun l => by rw [pair_weight_iff hD]; simp only [he,true_and])
    (weightComponent A B e cd x)
  rw [weightComponent_val] at hs
  rw [ground_single,coefficient,LinearMap.smul_apply,LinearMap.comp_apply,
    ← TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul,
    inv_mul_cancel₀ (LatticeChargedTransport.epsilon_nonzero D _ _),one_smul]
  exact hs

private def extract (e : Discriminant D) (cd : Discriminant D × Discriminant D) :
    PairSector A B cd →ₗ[ℂ] FiberSum A B e :=
  if h : cd.1+cd.2=e then
    (DirectSum.lof ℂ _ (fun i : Fiber (D := D) e => PairMultiplicity A B i.val) ⟨cd,h⟩).comp
      (coefficient A B hD cd)
  else 0

def mu (e : Discriminant D) :
    Multiplicity (targetModule A B) e →ₗ[ℂ] FiberSum A B e :=
  (DirectSum.toModule ℂ _ _ (extract A B hD e)).comp
    ((Omega (targetModule A B)).subtype.comp (jointWeight (targetModule A B) (representative D e)).subtype)

def nu (e : Discriminant D) :
    FiberSum A B e →ₗ[ℂ] Multiplicity (targetModule A B) e :=
  DirectSum.toModule ℂ _ _ (jAt A B hD e)

@[simp] theorem mu_component (e : Discriminant D)
    (x : Multiplicity (targetModule A B) e) (i : Fiber (D := D) e) :
    mu A B hD e x i = coefficient A B hD i.val (x.val.val i.val) := by
  classical
  have he : (DirectSum.component ℂ _ _ i).comp
      (DirectSum.toModule ℂ _ _ (extract A B hD e)) =
      (coefficient A B hD i.val).comp (DirectSum.component ℂ _ (PairSector A B) i.val) := by
    apply DirectSum.linearMap_ext
    intro cd
    apply LinearMap.ext
    intro z
    by_cases hcd : cd = i.val
    · subst cd
      simp [extract,i.property,DirectSum.component.of]
    · by_cases hc : cd.1+cd.2=e
      · have hi : (⟨cd,hc⟩ : Fiber (D := D) e) ≠ i :=
          fun h => hcd (congrArg Subtype.val h)
        simp [extract,hc,DirectSum.component.of,hi,hcd,Ne.symm hcd]
      · simp [extract,hc,DirectSum.component.of,hcd,Ne.symm hcd]
  exact LinearMap.congr_fun he x.val.val

/-- Literal normalized coefficient, before unfolding any support machinery. -/
theorem mu_coordinate (e : Discriminant D)
    (x : Multiplicity (targetModule A B) e) (i : Fiber (D := D) e) :
    mu A B hD e x i =
      epsilon D (-carry D hD i.val.1 i.val.2) (carry D hD i.val.1 i.val.2) •
        tensorCoordinates (x.val.val i.val) (-carry D hD i.val.1 i.val.2,0) := by
  exact mu_component A B hD e x i

/-- Support containment is in the support of THIS original vector. -/
theorem mu_support (e : Discriminant D) (x : Multiplicity (targetModule A B) e)
    (i : Fiber (D := D) e) (hi : i ∈ (mu A B hD e x).support) :
    i.val ∈ x.val.val.support := by
  by_contra hn
  have hz := DFinsupp.notMem_support_iff.mp hn
  have hm := DFinsupp.mem_support_iff.mp hi
  exact hm (by rw [mu_component,hz,map_zero])

@[simp] theorem mu_jAt (e : Discriminant D) (i : Fiber (D := D) e)
    (w : PairMultiplicity A B i.val) :
    mu A B hD e (jAt A B hD e i w) = DirectSum.lof ℂ _ _ i w := by
  change DirectSum.toModule ℂ _ _ (extract A B hD e)
    (jAt A B hD e i w).val.val = _
  rw [jAt_val,DirectSum.toModule_lof]
  simp only [extract,dif_pos i.property,LinearMap.comp_apply,coefficient_ground]

@[simp] theorem nu_lof (e : Discriminant D) (i : Fiber (D := D) e)
    (w : PairMultiplicity A B i.val) :
    nu A B hD e (DirectSum.lof ℂ _ _ i w) = jAt A B hD e i w := by
  simp only [nu,DirectSum.toModule_lof]

/-- Finite inverse expansion, with each dependent equality kept in its index. -/
theorem nu_expansion (e : Discriminant D) (z : FiberSum A B e) :
    nu A B hD e z = ∑ i ∈ z.support, jAt A B hD e i (z i) := by
  conv_lhs => rw [← DirectSum.sum_support_of z]
  simp only [map_sum,← DirectSum.lof_eq_of ℂ,nu_lof]

theorem mu_nu (e : Discriminant D) (z : FiberSum A B e) :
    mu A B hD e (nu A B hD e z) = z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i w => simpa only [← DirectSum.lof_eq_of ℂ,nu_lof,mu_jAt]
  | add x y hx hy => simp only [map_add,hx,hy]

theorem nu_mu (e : Discriminant D) (x : Multiplicity (targetModule A B) e) :
    nu A B hD e (mu A B hD e x) = x := by
  apply Subtype.ext; apply Subtype.ext
  rw [nu_expansion]
  simp only [Submodule.coe_sum,jAt_val]
  apply DFinsupp.ext
  intro cd
  change (DirectSum.component ℂ _ (PairSector A B) cd)
    (∑ i ∈ (mu A B hD e x).support,
      DirectSum.lof ℂ _ (PairSector A B) i.val
        (ground hD i.val.1 i.val.2 ⊗ₜ[ℂ] mu A B hD e x i)) = x.val.val cd
  rw [map_sum]
  by_cases he : cd.1+cd.2=e
  · let i : Fiber (D := D) e := ⟨cd,he⟩
    have hv := component_reconstruct A B hD e x cd he
    by_cases hi : i ∈ (mu A B hD e x).support
    · rw [Finset.sum_eq_single i]
      · change (DirectSum.component ℂ _ (PairSector A B) cd)
          (DirectSum.lof ℂ _ (PairSector A B) cd
            (ground hD cd.1 cd.2 ⊗ₜ[ℂ] mu A B hD e x i)) = x.val.val cd
        rw [DirectSum.component.lof_self,mu_component]
        exact hv.symm
      · intro k hk hki
        have hkc : k.val ≠ cd := fun h => hki (Subtype.ext h)
        simp only [DirectSum.component.of, dif_neg hkc]
      · exact fun hn => (hn hi).elim
    · have hz : mu A B hD e x i = 0 := DFinsupp.notMem_support_iff.mp hi
      have hx : x.val.val cd = 0 := by rw [hv,← mu_component A B hD e x i,hz,TensorProduct.tmul_zero]
      rw [hx]
      apply Finset.sum_eq_zero
      intro k hk
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      have hkc : k.val ≠ cd := fun h => hki (Subtype.ext h)
      simp only [DirectSum.component.of, dif_neg hkc]
  · rw [component_wrong A B hD e x cd he]
    apply Finset.sum_eq_zero
    intro k hk
    have hkc : k.val ≠ cd := fun h => he (h ▸ k.property)
    simp only [DirectSum.component.of, dif_neg hkc]

def multiplicityEquiv (e : Discriminant D) :
    Multiplicity (targetModule A B) e ≃ₗ[ℂ] FiberSum A B e where
  toLinearMap := mu A B hD e
  invFun := nu A B hD e
  left_inv := nu_mu A B hD e
  right_inv := mu_nu A B hD e

/-- The classified inclusion is a full map from the original sector. -/
def classified (J : FullJacobiLatticeModule D X) (c : Discriminant D)
    (w : Multiplicity J c) : Carrier D →ₗ[ℂ] X :=
  (classificationEquiv J hD).toLinearMap.comp
    ((DirectSum.lof ℂ _ (Sector J) c).comp
      ((TensorProduct.mk ℂ (Carrier D) _).flip w))

theorem classified_modes (J : FullJacobiLatticeModule D X) (c : Discriminant D)
    (w : Multiplicity J c) (a v : Carrier D) (m : ℤ) :
    classified hD J c w (mode (sectorModule D (representative D c)) a m v) =
      mode J a m (classified hD J c w v) := by
  simpa only [classified, LinearMap.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap,
    sectorModule, canonicalModule, directSumModule_mode,
    DirectSum.lmap_lof, tensorModule_mode,TensorProduct.map_tmul,
    LinearMap.id_apply] using
      (classification J hD a m (DirectSum.lof ℂ _ (Sector J) c (v ⊗ₜ[ℂ] w)))

/-- All-state readback: vacuum normalization is upgraded by the ACTUAL
accepted cyclicity theorem, rather than by an unproved ground projection. -/
theorem classification_j (c d : Discriminant D) (w : PairMultiplicity A B (c,d))
    (v : Carrier D) :
    classificationEquiv (targetModule A B) hD
      (DirectSum.lof ℂ _ _ (c+d) (v ⊗ₜ[ℂ] j A B hD c d w)) =
      DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (transportInverse D (representative D (c+d)) (carry D hD c d) v ⊗ₜ[ℂ] w) := by
  let f := classified hD (targetModule A B) (c+d) (j A B hD c d w)
  let g : Carrier D →ₗ[ℂ] P A B :=
    (DirectSum.lof ℂ _ (PairSector A B) (c,d)).comp
      (((TensorProduct.mk ℂ (Carrier D) _).flip w).comp
        (transportInverse D (representative D (c+d)) (carry D hD c d)))
  have he : f = g := by
    apply modeHom_ext_of_vacuum D (representative D (c+d))
      (fun a m => mode (targetModule A B) a m)
    · intro a m v
      exact classified_modes hD (targetModule A B) (c+d) (j A B hD c d w) a v m
    · intro a m u
      change DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (transportInverse D (representative D (c+d)) (carry D hD c d)
          (mode (sectorModule D (representative D (c+d))) a m u) ⊗ₜ[ℂ] w) = _
      change DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (transportInverse D (representative D (c+d)) (carry D hD c d)
          (mode (sectorModule D (representative D (c+d))) a m u) ⊗ₜ[ℂ] w) =
        mode (targetModule A B) a m
          (DirectSum.lof ℂ _ (PairSector A B) (c,d)
            (transportInverse D (representative D (c+d)) (carry D hD c d) u ⊗ₜ[ℂ] w))
      rw [targetModule,directSumModule_mode,DirectSum.lmap_lof,
        tensorModule_mode,TensorProduct.map_tmul,LinearMap.id_apply]
      congr 2
      simpa only [sectorModule_mode,pair_shift hD c d] using
        (transportInverse_all_modes D (representative D (c+d)) (carry D hD c d) a u m)
    · exact classification_normalization (targetModule A B) hD (c+d) (j A B hD c d w)
  exact LinearMap.congr_fun he v

theorem classification_inverse_pair (c d : Discriminant D)
    (v : Carrier D) (w : PairMultiplicity A B (c,d)) :
    (classificationEquiv (targetModule A B) hD).symm
      (DirectSum.lof ℂ _ (PairSector A B) (c,d) (v ⊗ₜ[ℂ] w)) =
    DirectSum.lof ℂ _ _ (c+d)
      (transport D (representative D (c+d)) (carry D hD c d) v ⊗ₜ[ℂ] j A B hD c d w) := by
  apply (classificationEquiv (targetModule A B) hD).injective
  rw [LinearEquiv.apply_symm_apply,classification_j]
  congr 2
  exact ((transportLinearEquiv D _ _).symm_apply_apply v).symm

end Product
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleProductMultiplicity
