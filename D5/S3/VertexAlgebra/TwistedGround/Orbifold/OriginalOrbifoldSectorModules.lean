/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldSectorModules
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldSectorModules
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both original twisted slices and the untwisted odd sector are fixed-algebra modules. -/

import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure
import D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds
import Batteries.Tactic.OpenPrivate

/-! The actual fixed lattice algebra acts on both twisted sign eigenspaces
and on the odd eigenspace of the untwisted lattice carrier. -/

set_option autoImplicit false

noncomputable section
open scoped VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldSectorModules

open LatticeGeneratingFieldLocality (Carrier LatticeData)
open LatticeAllStateField (Y identity_modes stateField_vacuum vacuum)
open LatticeInvolution (FixedCarrier fixedMode fixedVacuum mem_eigenspace mem_fixedSpace
  minusSpace stateField_theta theta)
open LatticeHalfFockCorrectedField (correctedField)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private vacuum_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

private theorem finite_of_coe {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Submodule ℂ V} (f : ℕ → S)
    (hf : Function.HasFiniteSupport (fun i => (f i).val)) :
    Function.HasFiniteSupport f :=
  hf.subset fun _ hi hz => hi (Subtype.ext hz)

private theorem finsum_val {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Submodule ℂ V} (f : ℕ → S) :
    (∑ᶠ i, f i).val = ∑ᶠ i, (f i).val :=
  S.subtype.toAddMonoidHom.map_finsum_of_injective Subtype.val_injective f

/-! ## Twisted parity slices -/

private theorem fixedParitySlice_mode_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a : FixedCarrier D) (n : ℤ) (v : paritySpace D hu s) :
    (((fixedParitySlice D hu s a)[[n]]) v).val =
      (correctedField D hu a.val).coeff (-2*n-2) v.val := by
  change (correctedField D hu a.val).coeff (2*(-n-1)) v.val = _
  rw [show 2*(-n-1) = -2*n-2 by omega]

/-- The fixed algebra acts linearly in its source on the actual twisted slice. -/
def fixedParityY (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ) :
    FixedCarrier D →ₗ[ℂ] VertexOperator ℂ (paritySpace D hu s) where
  toFun := fixedParitySlice D hu s
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext n
    apply LinearMap.ext
    intro v
    simp only [VertexOperator.coeff_eq_ncoeff, map_add, Pi.add_apply, LinearMap.add_apply]
    apply Subtype.ext
    simp only [fixedParitySlice_mode_val, Submodule.coe_add, map_add, Pi.add_apply,
      LinearMap.add_apply]
  map_smul' z a := by
    apply HVertexOperator.coeff_inj
    funext n
    apply LinearMap.ext
    intro v
    simp only [VertexOperator.coeff_eq_ncoeff, map_smul, Pi.smul_apply,
      LinearMap.smul_apply, RingHom.id_apply]
    apply Subtype.ext
    simp only [fixedParitySlice_mode_val, Submodule.coe_smul, map_smul, Pi.smul_apply,
      LinearMap.smul_apply]

/-- Full signed fixed-source Borcherds on each actual twisted parity slice. -/
theorem fixedParitySlice_borcherds (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (a b : FixedCarrier D) (u : paritySpace D hu s) (p q r : ℤ) :
    let ρ := fun (c : FixedCarrier D) (n : ℤ) => (fixedParityY D hu s c)[[n]]
    let left := fun i : ℕ => integerBinomial p i • ρ (fixedMode D a (r+i) b) (p+q-i) u
    let first := fun i : ℕ =>
      (((-1 : ℂ)^i)*integerBinomial r i) • ρ a (p+r-i) (ρ b (q+i) u)
    let second := fun i : ℕ =>
      (((-1 : ℂ)^i)*integerBinomial r i) • (epsilon r • ρ b (q+r-i) (ρ a (p+i) u))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ,
          (((-1 : ℂ)^i)*integerBinomial r i) •
            (ρ a (p+r-i) (ρ b (q+i) u) - epsilon r • ρ b (q+r-i) (ρ a (p+i) u)) := by
  have eigen : theta D a.val = (-1 : ℂ) ^ (0 : ℤ) • a.val := by
    simpa only [zpow_zero, one_smul] using (mem_fixedSpace D a.val).mp a.property
  have native := LatticeHalfFockGroundRightCurrentTransport.first_eigen_arbitrary_second
    D hu a.val 0 eigen b.val 0
  unfold LatticeHalfFockGroundRightCurrentTransport.OriginalCompatible
    LatticeHalfFockGroundRightCurrentTransport.Calculus.fullLaw at native
  have binom (n : ℤ) (i : ℕ) : integerBinomial n i = Ring.choose (n : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) n i
  have h := native p q r u.val
  unfold LatticeHalfFockGroundRightCurrentTransport.Calculus.leftTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.firstTerm
    LatticeHalfFockGroundRightCurrentTransport.Calculus.secondTerm
    LatticeHalfFockGroundRightCurrentTransport.residueWeight at h
  simp only [LatticeHalfFockPhysicalRescaling.physicalSlice_mode,
    Int.cast_zero, zero_div, add_zero, sub_zero, ← binom] at h
  have fixed_val (n : ℤ) :
      (fixedMode D a n b).val = LatticeAllStateReconstruction.mu D a.val n b.val := rfl
  dsimp only [fixedParityY, LinearMap.coe_mk, AddHom.coe_mk]
  refine ⟨finite_of_coe _ ?_, finite_of_coe _ ?_, finite_of_coe _ ?_, ?_⟩
  · simpa only [Submodule.coe_smul, fixedParitySlice_mode_val, fixed_val] using h.1
  · simpa only [Submodule.coe_smul, fixedParitySlice_mode_val] using h.2.1
  · simpa only [Submodule.coe_smul, fixedParitySlice_mode_val, epsilon] using h.2.2.1
  · apply Subtype.ext
    simp_rw [smul_sub]
    simp only [finsum_val, Submodule.coe_sub, Submodule.coe_smul,
      fixedParitySlice_mode_val, fixed_val, epsilon]
    rw [finsum_sub_distrib h.2.1 h.2.2.1]
    exact h.2.2.2

/-- The fixed vacuum acts by the identity field on each actual twisted parity slice. -/
theorem fixedParitySlice_vacuum_ncoeff (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (n : ℤ) (u : paritySpace D hu s) :
    ((fixedParityY D hu s (fixedVacuum D))[[n]]) u = if n = -1 then u else 0 := by
  apply Subtype.ext
  change (((fixedParitySlice D hu s (fixedVacuum D))[[n]]) u).val = _
  rw [fixedParitySlice_mode_val]
  change (correctedField D hu (vacuum D)).coeff (-2*n-2) u.val = _
  rw [vacuum_coeff]
  by_cases hn : n = -1
  · subst n
    rfl
  · simp only [if_neg (show -2*n-2 ≠ 0 by omega), if_neg hn, Submodule.coe_zero]

/-! ## Untwisted odd sector -/

private theorem odd_mode_closed (D : LatticeData) (a : FixedCarrier D)
    (n : ℤ) (v : Carrier D) (hv : v ∈ minusSpace D) :
    ((Y D a.val)[[n]]) v ∈ minusSpace D := by
  rw [minusSpace, mem_eigenspace] at hv ⊢
  rw [stateField_theta, (mem_fixedSpace D a.val).mp a.property, hv, map_smul]

private def oddMode (D : LatticeData) (a : FixedCarrier D) (n : ℤ) :
    Module.End ℂ (minusSpace D) :=
  ((Y D a.val)[[n]]).restrict (fun v hv => odd_mode_closed D a n v hv)

private def oddField (D : LatticeData) (a : FixedCarrier D) :
    VertexOperator ℂ (minusSpace D) :=
  VertexOperator.of_coeff (fun k => oddMode D a (-k-1)) (by
    intro v
    refine ⟨((HahnModule.of ℂ).symm ((Y D a.val) v.val)).order, ?_⟩
    intro k hk
    by_contra h
    apply hk
    apply Subtype.ext
    change ((Y D a.val)[[-k-1]]) v.val = 0
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega)

private theorem oddField_ncoeff_val (D : LatticeData) (a : FixedCarrier D)
    (n : ℤ) (v : minusSpace D) :
    (((oddField D a)[[n]]) v).val = ((Y D a.val)[[n]]) v.val := by
  change (oddMode D a (-(-n-1)-1) v).val = _
  rw [show -(-n-1)-1 = n by omega]
  rfl

/-- The field obtained by restricting the actual lattice modes to the odd eigenspace. -/
def oddY (D : LatticeData) : FixedCarrier D →ₗ[ℂ] VertexOperator ℂ (minusSpace D) where
  toFun := oddField D
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext n
    apply LinearMap.ext
    intro v
    simp only [VertexOperator.coeff_eq_ncoeff, map_add, Pi.add_apply, LinearMap.add_apply]
    apply Subtype.ext
    simp only [oddField_ncoeff_val, Submodule.coe_add, map_add, Pi.add_apply,
      LinearMap.add_apply]
  map_smul' z a := by
    apply HVertexOperator.coeff_inj
    funext n
    apply LinearMap.ext
    intro v
    simp only [VertexOperator.coeff_eq_ncoeff, map_smul, Pi.smul_apply,
      LinearMap.smul_apply, RingHom.id_apply]
    apply Subtype.ext
    simp only [oddField_ncoeff_val, Submodule.coe_smul, map_smul, Pi.smul_apply,
      LinearMap.smul_apply]

@[simp] theorem oddY_ncoeff_val (D : LatticeData) (a : FixedCarrier D)
    (n : ℤ) (v : minusSpace D) :
    (((oddY D a)[[n]]) v).val = ((Y D a.val)[[n]]) v.val :=
  oddField_ncoeff_val D a n v

/-- Full signed fixed-source Borcherds with three finite supports on the untwisted odd sector. -/
theorem oddY_borcherds (D : LatticeData)
    (a b : FixedCarrier D) (u : minusSpace D) (p q r : ℤ) :
    let ρ := fun (c : FixedCarrier D) (n : ℤ) => (oddY D c)[[n]]
    let left := fun i : ℕ => integerBinomial p i • ρ (fixedMode D a (r+i) b) (p+q-i) u
    let first := fun i : ℕ =>
      (((-1 : ℂ)^i)*integerBinomial r i) • ρ a (p+r-i) (ρ b (q+i) u)
    let second := fun i : ℕ =>
      (((-1 : ℂ)^i)*integerBinomial r i) • (epsilon r • ρ b (q+r-i) (ρ a (p+i) u))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ,
          (((-1 : ℂ)^i)*integerBinomial r i) •
            (ρ a (p+r-i) (ρ b (q+i) u) - epsilon r • ρ b (q+r-i) (ρ a (p+i) u)) := by
  have h := (LatticeActualVertexAlgebra.actualVertexAlgebra D).borcherds
    a.val b.val u.val p q r
  dsimp only [LatticeActualVertexAlgebra.actualVertexAlgebra] at h
  have fixed_val (n : ℤ) :
      (fixedMode D a n b).val = ((Y D a.val)[[n]]) b.val := rfl
  dsimp only
  refine ⟨finite_of_coe _ ?_, finite_of_coe _ ?_, finite_of_coe _ ?_, ?_⟩
  · simpa only [Submodule.coe_smul, oddY_ncoeff_val, fixed_val] using h.1
  · simpa only [Submodule.coe_smul, oddY_ncoeff_val] using h.2.1
  · simpa only [Submodule.coe_smul, oddY_ncoeff_val] using h.2.2.1
  · apply Subtype.ext
    simpa only [finsum_val, Submodule.coe_smul, Submodule.coe_sub, oddY_ncoeff_val,
      fixed_val] using h.2.2.2

/-- The fixed vacuum acts by the identity field on the untwisted odd sector. -/
theorem oddY_vacuum_ncoeff (D : LatticeData) (n : ℤ) (u : minusSpace D) :
    ((oddY D (fixedVacuum D))[[n]]) u = if n = -1 then u else 0 := by
  apply Subtype.ext
  rw [oddY_ncoeff_val]
  change ((Y D (vacuum D))[[n]]) u.val = _
  rw [stateField_vacuum, identity_modes]
  split_ifs <;> rfl

#print axioms fixedParityY
#print axioms fixedParitySlice_borcherds
#print axioms fixedParitySlice_vacuum_ncoeff
#print axioms oddY
#print axioms oddY_ncoeff_val
#print axioms oddY_borcherds
#print axioms oddY_vacuum_ncoeff

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldSectorModules
