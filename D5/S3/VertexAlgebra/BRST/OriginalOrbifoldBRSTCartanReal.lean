/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTCartanReal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTCartanReal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The canonical Hermitian form at zero momentum has the original hyperbolic Gram matrix. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTCartanPairing
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalReal

/-! The canonical Hermitian form on the native zero-momentum BRST sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTCartanReal

open OriginalOrbifoldCriticalMatter (Matter State hyperbolicData hyperbolic_gram
  orbifoldVertexAlgebra)
open OriginalBRSTWeightPositive (orbifoldConjugation)
open OriginalOrbifoldBRSTChainReal (stateConjugation cohomologyConjugation
  cohomologyConjugation_mk degreeOneConjugation)
open OriginalOrbifoldBRSTQuartetReal (stateConjugation_tmul)
open OriginalOrbifoldBRSTDescent (relativeBoundaries)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open OriginalOrbifoldBRSTMomentum (physicalMomentum)
open OriginalOrbifoldBRSTPhysicalReal (canonicalPhysicalHermitian)
open OriginalOrbifoldBRSTContravariant (contravariantBPZ contravariantBPZ_apply)
open OriginalOrbifoldBRSTCartan (cartanCycle h h_mem_physicalMomentum_zero
  span_h_eq_physicalMomentum_zero)
open OriginalOrbifoldBRSTCartanPairing (physicalBPZ_h)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ)
open OriginalOrbifoldBRSTChevalley (chevalley chevalley_h)
open OriginalOrbifoldRelativeQuartet (UCharge)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open OriginalOrbifoldBRSTGhostBilinear (kappa_ket)
open SourceBPZ.OriginalMatterHermitian (kappaCarrier kappaCarrier_single kappaOsc)
open TwistedGround.Orbifold.ActualTwistedDescendantPositive (negativeConjugation)

open private ghostConjugation from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTChainReal
open private cartanCycle_tensor from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTCartanPairing

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem orbifoldConjugation_vacuum :
    orbifoldConjugation orbifoldVertexAlgebra.vacuum = orbifoldVertexAlgebra.vacuum := by
  apply Prod.ext
  · apply Subtype.ext
    change kappaCarrier (Finsupp.single 0 1) = Finsupp.single 0 1
    rw [kappaCarrier_single]
    exact congrArg (Finsupp.single 0) (map_one (MvPolynomial.map (starRingEnd ℂ)))
  · change negativeConjugation 0 = 0
    exact negativeConjugation.map_zero

/-- The actual Cartan cycle is fixed before passage to cohomology. -/
theorem stateConjugation_cartanCycle (i : Fin hyperbolicData.rank) :
    stateConjugation ((cartanCycle i).1 : State) = ((cartanCycle i).1 : State) := by
  rw [cartanCycle_tensor, stateConjugation_tmul, orbifoldConjugation_vacuum, kappaCarrier_single]
  have hg : ghostConjugation (ket {1}) = ket {1} := kappa_ket _
  rw [hg, kappaOsc, MvPolynomial.map_X]

/-- The canonical degree-one conjugation fixes both native Cartan classes. -/
theorem degreeOneConjugation_h (i : Fin hyperbolicData.rank) :
    degreeOneConjugation (h i) = h i := by
  apply Subtype.ext
  change cohomologyConjugation (relativeBoundaries.mkQ (cartanCycle i)) =
    relativeBoundaries.mkQ (cartanCycle i)
  rw [cohomologyConjugation_mk]
  exact congrArg relativeBoundaries.mkQ
    (Subtype.ext (Subtype.ext (stateConjugation_cartanCycle i)))

/-- The original Cartan classes, viewed in the zero-momentum subspace. -/
def zeroMomentumCartan (i : Fin hyperbolicData.rank) : physicalMomentum (0 : UCharge) :=
  ⟨h i, h_mem_physicalMomentum_zero i⟩

/-- The canonical Hermitian Gram entries are the integral entries of the original `U` pairing. -/
theorem canonicalPhysicalHermitian_h (i j : Fin hyperbolicData.rank) :
    canonicalPhysicalHermitian 0 (zeroMomentumCartan i) (zeroMomentumCartan j) =
      (hyperbolicData.G i j : ℂ) := by
  calc
    _ = contravariantBPZ (degreeOneConjugation (h i)) (h j) := rfl
    _ = contravariantBPZ (h i) (h j) :=
      congrArg (fun x : DegreeOne => contravariantBPZ x (h j)) (degreeOneConjugation_h i)
    _ = -physicalBPZ (h i) (chevalley (h j)) := contravariantBPZ_apply (h i) (h j)
    _ = -physicalBPZ (h i) (-h j) :=
      congrArg (fun y : DegreeOne => -physicalBPZ (h i) y) (chevalley_h j)
    _ = physicalBPZ (h i) (h j) :=
      (congrArg Neg.neg ((physicalBPZ (h i)).map_neg (h j))).trans (neg_neg _)
    _ = _ := physicalBPZ_h i j

private theorem span_pair_subtype {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (u v : W)
    (hw : Submodule.span ℂ ({u.val, v.val} : Set V) = W) (x : W) :
    ∃ a b : ℂ, a • u + b • v = x := by
  have hx : x.val ∈ Submodule.span ℂ ({u.val, v.val} : Set V) := hw.symm ▸ x.property
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
  exact ⟨a, b, Subtype.ext hab⟩

private theorem range_of_fin_two {V : Type*} (f : Fin 2 → V) :
    Set.range f = {f 0, f 1} := by
  have hf : f = ![f 0, f 1] := funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
  exact (congrArg Set.range hf).trans (Matrix.range_cons_cons_empty _ _ ![])

section HyperbolicPair

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (u v : V)

private theorem hyperbolic_coordinates
    (huu : B u u = 0) (huv : B u v = 1) (hvu : B v u = 1) (hvv : B v v = 0)
    (a b c d : ℂ) :
    B (a • u + b • v) (c • u + d • v) = star a * d + star b * c := by
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, starRingEnd_apply, huu, huv, hvu, hvv,
    mul_zero, mul_one, zero_add, add_zero]
  ring

private theorem hyperbolic_conj_symm
    (hspan : ∀ x : V, ∃ a b : ℂ, a • u + b • v = x)
    (hcoord : ∀ a b c d : ℂ,
      B (a • u + b • v) (c • u + d • v) = star a * d + star b * c) (x y : V) :
    star (B x y) = B y x := by
  obtain ⟨a, b, rfl⟩ := hspan x
  obtain ⟨c, d, rfl⟩ := hspan y
  simp only [hcoord, star_add, star_mul, star_star]
  ring

private theorem hyperbolic_nondegenerate
    (hspan : ∀ x : V, ∃ a b : ℂ, a • u + b • v = x)
    (huu : B u u = 0) (huv : B u v = 1) (hvu : B v u = 1) (hvv : B v v = 0)
    (hsymm : ∀ x y : V, star (B x y) = B y x) : B.Nondegenerate := by
  have hright : B.SeparatingRight := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := hspan x
    have ha := hx v
    have hb := hx u
    simp only [map_add, map_smul, smul_eq_mul, huu, huv, hvu, hvv,
      mul_zero, mul_one, zero_add, add_zero] at ha hb
    simp only [ha, hb, zero_smul, add_zero]
  refine ⟨?_, hright⟩
  intro x hx
  apply hright x
  intro y
  rw [← hsymm x y, hx y, star_zero]

private theorem hyperbolic_split_entries
    (huu : B u u = 0) (huv : B u v = 1) (hvu : B v u = 1) (hvv : B v v = 0) :
    B (u + v) (u + v) = 2 ∧ B (u + v) (u - v) = 0 ∧
      B (u - v) (u + v) = 0 ∧ B (u - v) (u - v) = -2 := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, huu, huv, hvu, hvv]
  norm_num

private theorem hyperbolic_split_independent
    (hpp : B (u + v) (u + v) = 2) (hpm : B (u + v) (u - v) = 0)
    (hmm : B (u - v) (u - v) = -2) : LinearIndependent ℂ ![u + v, u - v] := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    have hz' := congrArg (B (u - v)) hz
    change B (u - v) (u - v) = B (u - v) 0 at hz'
    rw [hmm, map_zero] at hz'
    norm_num at hz'
  · intro a ha
    have ha' := congrArg (B (u + v)) ha
    change B (u + v) (a • (u - v)) = B (u + v) (u + v) at ha'
    rw [map_smul, hpm, smul_zero, hpp] at ha'
    norm_num at ha'

private theorem hyperbolic_split_spans
    (hspan : ∀ x : V, ∃ a b : ℂ, a • u + b • v = x) :
    ⊤ ≤ Submodule.span ℂ (Set.range (![u + v, u - v] : Fin 2 → V)) := by
  intro x _
  rw [Matrix.range_cons_cons_empty]
  obtain ⟨a, b, hab⟩ := hspan x
  refine Submodule.mem_span_pair.mpr ⟨(a + b) / 2, (a - b) / 2, ?_⟩
  have ha : (a + b) / 2 + (a - b) / 2 = a := by ring
  have hb : (a + b) / 2 - (a - b) / 2 = b := by ring
  rw [smul_add, smul_sub, ← add_sub_assoc, add_right_comm, add_sub_assoc,
    ← add_smul, ← sub_smul, ha, hb]
  exact hab

end HyperbolicPair

section ZeroMomentum

open OrderedHyperbolicExtension (U_zero_zero U_zero_one U_one_zero U_one_one)

local notation "H₀" => canonicalPhysicalHermitian 0
local notation "h₀" => zeroMomentumCartan 0
local notation "h₁" => zeroMomentumCartan 1

private theorem zeroMomentumCartan_span (x : physicalMomentum (0 : UCharge)) :
    ∃ a b : ℂ, a • h₀ + b • h₁ = x :=
  span_pair_subtype (physicalMomentum 0) h₀ h₁
    ((congrArg (Submodule.span ℂ) (range_of_fin_two h)).symm.trans
      span_h_eq_physicalMomentum_zero) x

private theorem zero_entry_00 : H₀ h₀ h₀ = 0 := by
  rw [canonicalPhysicalHermitian_h, hyperbolic_gram, U_zero_zero, Int.cast_zero]

private theorem zero_entry_01 : H₀ h₀ h₁ = 1 := by
  rw [canonicalPhysicalHermitian_h, hyperbolic_gram, U_zero_one, Int.cast_one]

private theorem zero_entry_10 : H₀ h₁ h₀ = 1 := by
  rw [canonicalPhysicalHermitian_h, hyperbolic_gram, U_one_zero, Int.cast_one]

private theorem zero_entry_11 : H₀ h₁ h₁ = 0 := by
  rw [canonicalPhysicalHermitian_h, hyperbolic_gram, U_one_one, Int.cast_zero]

/-- The canonical form in the original two Cartan coordinates. -/
theorem canonicalPhysicalHermitian_zero_coordinates (a b c d : ℂ) :
    H₀ (a • h₀ + b • h₁) (c • h₀ + d • h₁) = star a * d + star b * c :=
  hyperbolic_coordinates H₀ h₀ h₁ zero_entry_00 zero_entry_01 zero_entry_10 zero_entry_11 a b c d

/-- The canonical form is Hermitian on the entire native momentum-zero space. -/
theorem canonicalPhysicalHermitian_zero_conj_symm (x y : physicalMomentum (0 : UCharge)) :
    star (H₀ x y) = H₀ y x :=
  hyperbolic_conj_symm H₀ h₀ h₁ zeroMomentumCartan_span
    canonicalPhysicalHermitian_zero_coordinates x y

private theorem zero_split_entries :
    H₀ (h₀ + h₁) (h₀ + h₁) = 2 ∧ H₀ (h₀ + h₁) (h₀ - h₁) = 0 ∧
      H₀ (h₀ - h₁) (h₀ + h₁) = 0 ∧ H₀ (h₀ - h₁) (h₀ - h₁) = -2 :=
  hyperbolic_split_entries H₀ h₀ h₁ zero_entry_00 zero_entry_01 zero_entry_10 zero_entry_11

private theorem zero_split_independent :
    LinearIndependent ℂ ![h₀ + h₁, h₀ - h₁] :=
  hyperbolic_split_independent H₀ h₀ h₁ zero_split_entries.1 zero_split_entries.2.1
    zero_split_entries.2.2.2

/-- The sum and difference of the original Cartan classes form a basis at zero momentum. -/
def zeroMomentumCartanSplitBasis : Module.Basis (Fin 2) ℂ (physicalMomentum (0 : UCharge)) :=
  Module.Basis.mk zero_split_independent (hyperbolic_split_spans h₀ h₁ zeroMomentumCartan_span)

/-- The ordered basis `(h 0 + h 1, h 0 - h 1)` has Gram diagonal `(2, -2)`.
This is signature `(1, 1)` on the original zero-momentum BRST sector. -/
theorem canonicalPhysicalHermitian_zero_signature :
    let e := zeroMomentumCartanSplitBasis
    e 0 = h₀ + h₁ ∧ e 1 = h₀ - h₁ ∧ H₀ (e 0) (e 0) = 2 ∧
      H₀ (e 0) (e 1) = 0 ∧ H₀ (e 1) (e 0) = 0 ∧ H₀ (e 1) (e 1) = -2 := by
  dsimp only
  have hp : zeroMomentumCartanSplitBasis 0 = h₀ + h₁ :=
    Module.Basis.mk_apply zero_split_independent _ 0
  have hm : zeroMomentumCartanSplitBasis 1 = h₀ - h₁ :=
    Module.Basis.mk_apply zero_split_independent _ 1
  exact ⟨hp, hm, by simpa only [hp, hm] using zero_split_entries⟩

/-- The canonical form has trivial radicals on the original zero-momentum sector. -/
theorem canonicalPhysicalHermitian_zero_nondegenerate : (H₀).Nondegenerate :=
  hyperbolic_nondegenerate H₀ h₀ h₁ zeroMomentumCartan_span
    zero_entry_00 zero_entry_01 zero_entry_10 zero_entry_11
    canonicalPhysicalHermitian_zero_conj_symm

end ZeroMomentum

#print axioms stateConjugation_cartanCycle
#print axioms degreeOneConjugation_h
#print axioms canonicalPhysicalHermitian_h
#print axioms canonicalPhysicalHermitian_zero_coordinates
#print axioms canonicalPhysicalHermitian_zero_conj_symm
#print axioms canonicalPhysicalHermitian_zero_signature
#print axioms canonicalPhysicalHermitian_zero_nondegenerate

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTCartanReal
