/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Result
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 UpperBasis Result on original physical labels. -/
/- UNCOMPILED source preparation. Selected-span quotient and exact basis.
   No Lean/kernel, registration, official acceptance or publication claim. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Reconstruction
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Isomorphisms
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Weights
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Result

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base seed place)
open MersenneExceptional19PermutationStabilizer (aa bb parameter_exact eighth_facts)
open MersenneExceptional19ZeroLattice
  (integerWeightedSum coordinateGenerator primitive phaseWeight source_eq_scale_primitive)
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent (row)
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.PositiveChargeGeometry
  (quotientLabel quotient_zero_iff)
open private primitive_place
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Weights
open private weighted_sum_row
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19ZeroLattice.Result

/-- The ACTUAL selected upper indicators span the ORIGINAL integer kernel.
The quotient annihilates exactly those selected rows; the all-zero-family
reconstruction theorem is never used to discharge that hypothesis. -/
theorem actual_selected_upper_span_eq_kernel (r : ℕ) :
    Submodule.span ℤ (Set.range (selectedRow r))=
      LinearMap.ker (integerWeightedSum r) := by
  classical
  let L := Submodule.span ℤ (Set.range (selectedRow r))
  change L=LinearMap.ker (integerWeightedSum r)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    exact (selectedKernelRow r k).property
  · intro z hz
    change integerWeightedSum r z=0 at hz
    let X : Fin (3*degree r) → (Fin (3*degree r) → ℤ) ⧸ L := quotientLabel L
    have hX : SelectedAnnihilates r X := by
      intro k
      apply (quotient_zero_iff (M := L) (selectedMask r k)).mpr
      exact Submodule.subset_span ⟨k,rfl⟩
    let c : (Fin (3*degree r) → ℤ) ⧸ L := L.mkQ (coordinateGenerator r)
    have hcoord (i : Fin (3*degree r)) : X i=primitive r i • c := by
      have hi := actual_selected_upper_reconstruction r X hX i
      simpa only [c,coordinateGenerator,map_add,map_smul,X,quotientLabel] using hi
    have qz : L.mkQ z=(∑ i, z i*primitive r i) • c := by
      calc
        L.mkQ z=L.mkQ (∑ i, z i • Pi.single i (1 : ℤ)) := by
          rw [← pi_eq_sum_univ' z]
        _=∑ i, z i • X i := by
          simp only [map_sum,map_smul,X,quotientLabel]
        _=∑ i, (z i*primitive r i) • c := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoord,smul_smul]
        _=(∑ i, z i*primitive r i) • c := by rw [Finset.sum_smul]
    have factor_ne : 19*((base r : ℤ)-1)≠0 := by
      obtain ⟨hB,hE,hmod⟩ := eighth_facts r
      omega
    have scale : integerWeightedSum r z=
        (19*((base r : ℤ)-1))*(∑ i, z i*primitive r i) := by
      change (∑ i, z i*SourceWidth.actualSource (3*degree r) (seed r) i)=_
      simp_rw [source_eq_scale_primitive]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hzprim : (∑ i, z i*primitive r i)=0 := by
      rw [scale] at hz
      exact (mul_eq_zero.mp hz).resolve_left factor_ne
    have qzero : L.mkQ z=0 := by rw [qz,hzprim,zero_smul]
    exact (Submodule.Quotient.mk_eq_zero L).mp qzero

/-- Exactly 3d-1 selected actual UPPER indicators form an integer basis,
for every natural r including 0, with their ORIGINAL coordinate functions. -/
theorem actual_selected_upper_integer_basis (r : ℕ) :
    ∃ b : Basis (UpperIndex r) ℤ
      (LinearMap.ker (MersenneExceptional19ZeroLattice.integerWeightedSum r)),
      ∀ k, (b k).val =
        D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.row (selectedMask r k) := by
  classical
  let V := Fin (3*degree r) → ℤ
  let K := LinearMap.ker (integerWeightedSum r)
  have spans : Submodule.span ℤ (Set.range (selectedKernelRow r))=⊤ := by
    apply Submodule.map_injective_of_injective K.injective_subtype
    rw [Submodule.map_span,Submodule.map_subtype_top,Set.image_range]
    change Submodule.span ℤ (Set.range (selectedRow r))=K
    exact actual_selected_upper_span_eq_kernel r
  let P : V →ₗ[ℤ] ℤ :=
    { toFun := fun z => ∑ i, z i*primitive r i
      map_add' := by intro z w; simp [Pi.add_apply,add_mul,Finset.sum_add_distrib]
      map_smul' := by
        intro a z
        simp [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc] }
  have scale (z : V) : integerWeightedSum r z=(19*((base r : ℤ)-1))*P z := by
    change (∑ i, z i*SourceWidth.actualSource (3*degree r) (seed r) i)=_
    simp_rw [source_eq_scale_primitive]
    change (∑ i, z i*((19*((base r : ℤ)-1))*primitive r i))=
      (19*((base r : ℤ)-1))*(∑ i, z i*primitive r i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have factor_ne : 19*((base r : ℤ)-1)≠0 := by
    obtain ⟨hB,hE,hmod⟩ := eighth_facts r
    omega
  have hker : LinearMap.ker P=K := by
    ext z
    change P z=0 ↔ integerWeightedSum r z=0
    rw [scale,mul_eq_zero]
    simp only [factor_ne,false_or]
  have pe (i : Fin (3*degree r)) : P (Pi.single i (1 : ℤ))=primitive r i := by
    simp [P,Pi.single_apply]
  have hd : 12≤degree r := by dsimp [degree]; omega
  let j0 : Fin (degree r) := ⟨0,by omega⟩
  have p0 : primitive r (place 0 j0)=aa r := by
    simp [primitive_place,phaseWeight,j0,show (0 : ℕ)≠degree r-1 by omega]
  have p2 : primitive r (place 2 j0)=bb r := by
    simp [primitive_place,phaseWeight,j0,show (0 : ℕ)≠degree r-2 by omega,
      show (0 : ℕ)≠degree r-1 by omega]
  have pc : P (coordinateGenerator r)=1 := by
    change P ((-3 : ℤ) • Pi.single (place 0 j0) 1+
      (2 : ℤ) • Pi.single (place 2 j0) 1)=1
    rw [map_add,map_smul,map_smul,pe,pe,p0,p2]
    obtain ⟨ha,hb,hs⟩ := parameter_exact r
    simp only [smul_eq_mul]
    omega
  have surj : Function.Surjective P := by
    intro m
    refine ⟨m • coordinateGenerator r,?_⟩
    rw [map_smul,pc]
    simp
  have qr : Module.finrank ℤ (V ⧸ LinearMap.ker P)=1 := by
    rw [(P.quotKerEquivOfSurjective surj).finrank_eq,Module.finrank_self]
  have rankK : Module.finrank ℤ K=3*degree r-1 := by
    have rn := (LinearMap.ker P).finrank_quotient_add_finrank
    rw [qr,hker] at rn
    have rv : Module.finrank ℤ V=3*degree r := by
      simp only [V,Module.finrank_pi,Fintype.card_fin]
    rw [rv] at rn
    omega
  let b : Basis (UpperIndex r) ℤ K :=
    basisOfTopLeSpanOfCardEqFinrank (selectedKernelRow r)
      (by rw [spans]) (by rw [card_upperIndex,rankK])
  refine ⟨b,?_⟩
  intro k
  have hb : b k=selectedKernelRow r k := by
    exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank (selectedKernelRow r)
      (by rw [spans]) (by rw [card_upperIndex,rankK])) k
  rw [hb]
  rfl

end D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
