/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeMassShell
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeMassShell
   mirror-E: none(waiver:algebraic-original-orbifold-relative-mass-shell)
   anchors: []
   utility: none
   digest: Fixed hyperbolic momentum relative mass shells of the actual critical Leech orbifold. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell

/-! The full algebraic tensor basis detects the native relative constraints and
bounds the orbifold, hyperbolic oscillator, and ghost degrees at each U charge. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldRelativeMassShell

open OriginalOrbifoldCriticalMatter
open OriginalOrbifoldBRSTZeroEnergy
open LatticeGeneratingFieldLocality (Charge Oscillator)
open LatticePositiveEnergy (chargeEnergy oscillatorEnergy oscillatorLeFinite)
open LatticeRelativeMassShell (massShellCutoff massShellCutoff_cast)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open BcGhostRelativeEnergy (level level_cast relative_level_coeff_iff relative_level_support)

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData
private abbrev LatticeState := LatticeMatterGhostCoupling.State hyperbolicData
private abbrev LatticeLabel := LatticeRelativeMassShell.TensorLabel hyperbolicData

private theorem latticeBasis_eq : LatticeBRSTZeroEnergyReduction.fullBasis hyperbolicData =
    LatticeRelativeMassShell.tensorBasis hyperbolicData := rfl

private theorem fullBasis_apply (i : FullLabel) :
    fullBasis i =
      (orbifoldBasis i.1 ⊗ₜ[ℂ] Finsupp.single i.2.1.1 (MvPolynomial.monomial i.2.1.2 1))
        ⊗ₜ[ℂ] ket i.2.2 := by
  simp only [fullBasis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply',
    latticeBasis_eq, LatticeRelativeMassShell.tensorBasis_apply, TensorProduct.assoc_symm_tmul]

private def orbifoldSlices : State ≃ₗ[ℂ] (OrbifoldLabel →₀ LatticeState) :=
  (TensorProduct.assoc ℂ Orbifold Hyperbolic Fock).trans
    (TensorProduct.equivFinsuppOfBasisLeft orbifoldBasis)

private def orbifoldSlice (j : OrbifoldLabel) : State →ₗ[ℂ] LatticeState :=
  (Finsupp.lapply j).comp orbifoldSlices.toLinearMap

private theorem orbifoldSlice_tmul (j : OrbifoldLabel)
    (u : Orbifold) (v : Hyperbolic) (w : Fock) :
    orbifoldSlice j ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) =
      orbifoldBasis.repr u j • (v ⊗ₜ[ℂ] w) := by
  change TensorProduct.equivFinsuppOfBasisLeft orbifoldBasis
    (TensorProduct.assoc ℂ Orbifold Hyperbolic Fock ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w)) j = _
  rw [TensorProduct.assoc_tmul, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]

set_option maxHeartbeats 800000 in
-- Identifying the tensor coefficients reduces the actual nested carrier instances.
private theorem orbifoldSlice_coeff (x : State) (j : OrbifoldLabel) (i : LatticeLabel) :
    LatticeRelativeMassShell.coeff hyperbolicData (orbifoldSlice j x) i =
      fullBasis.repr x (j, i) := by
  classical
  let c : LatticeState →ₗ[ℂ] ℂ := (LatticeRelativeMassShell.tensorBasis hyperbolicData).coord i
  have h : c.comp (orbifoldSlice j) = fullBasis.coord (j, i) := by
    apply fullBasis.ext
    rintro ⟨k, l⟩
    change c (orbifoldSlice j (fullBasis (k, l))) = fullBasis.repr (fullBasis (k, l)) (j, i)
    rw [fullBasis.repr_self, fullBasis_apply, orbifoldSlice_tmul, map_smul, smul_eq_mul]
    change orbifoldBasis.repr (orbifoldBasis k) j *
      c (Finsupp.single l.1.1 (MvPolynomial.monomial l.1.2 1) ⊗ₜ[ℂ] ket l.2) = _
    rw [← LatticeRelativeMassShell.tensorBasis_apply, orbifoldBasis.repr_self]
    change Finsupp.single k (1 : ℂ) j *
      (LatticeRelativeMassShell.tensorBasis hyperbolicData).repr
        (LatticeRelativeMassShell.tensorBasis hyperbolicData l) i = _
    rw [Module.Basis.repr_self]
    by_cases hk : k = j <;> by_cases hl : l = i <;>
      simp [Prod.mk.injEq, hk, hl]
  exact LinearMap.congr_fun h x

set_option maxHeartbeats 800000 in
-- Tensor basis extensionality reduces both native realizations of the ghost action.
private theorem orbifoldSlice_b (j : OrbifoldLabel) (x : State) :
    orbifoldSlice j (b 0 x) =
      LatticeMatterGhostCoupling.ghostB hyperbolicData 0 (orbifoldSlice j x) := by
  have h : (orbifoldSlice j).comp (b 0) =
      (LatticeMatterGhostCoupling.ghostB hyperbolicData 0).comp (orbifoldSlice j) := by
    apply fullBasis.ext
    intro i
    change orbifoldSlice j (b 0 (fullBasis i)) =
      LatticeMatterGhostCoupling.ghostB hyperbolicData 0 (orbifoldSlice j (fullBasis i))
    simp only [fullBasis_apply, b, VirasoroBRST.ghostB, BcGhostChargeTensor.B,
      BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
      orbifoldSlice_tmul, map_smul, LatticeMatterGhostCoupling.ghostB]
  exact LinearMap.congr_fun h x

set_option maxHeartbeats 800000 in
-- Injectivity of the slice equivalence reduces the equality on the nested state space.
private theorem b_zero_iff (x : State) :
    b 0 x = 0 ↔ ∀ i : FullLabel, 3 ∈ i.2.2 → fullBasis.repr x i = 0 := by
  constructor
  · intro hx i hi
    have hs : LatticeMatterGhostCoupling.ghostB hyperbolicData 0
        (orbifoldSlice i.1 x) = 0 := by
      rw [← orbifoldSlice_b, hx, (orbifoldSlice i.1).map_zero]
    change fullBasis.repr x (i.1, i.2) = 0
    rw [← orbifoldSlice_coeff]
    exact (LatticeRelativeMassShell.ghostB_zero_iff hyperbolicData _).mp hs i.2 hi
  · intro hx
    apply orbifoldSlices.injective
    rw [orbifoldSlices.map_zero]
    apply Finsupp.ext
    intro j
    change orbifoldSlice j (b 0 x) = 0
    rw [orbifoldSlice_b, LatticeRelativeMassShell.ghostB_zero_iff]
    intro i hi
    rw [orbifoldSlice_coeff]
    exact hx (j, i) hi

set_option maxHeartbeats 800000 in
-- Coefficient extensionality uses the module instances of the full native state space.
private theorem totalL0_zero_iff (x : State) :
    totalL0 x = 0 ↔ ∀ i : FullLabel, fullBasis.repr x i ≠ 0 → totalEnergy i = 0 := by
  constructor
  · intro hx i hi
    have h := congrArg (fun y : State => fullBasis.repr y i) hx
    change fullBasis.repr (totalL0 x) i = fullBasis.repr 0 i at h
    rw [totalL0_coeff, fullBasis.repr.map_zero, Finsupp.zero_apply] at h
    exact Int.cast_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hi)
  · intro hx
    apply fullBasis.repr.injective
    rw [fullBasis.repr.map_zero]
    apply Finsupp.ext
    intro i
    rw [totalL0_coeff, Finsupp.zero_apply]
    by_cases hi : fullBasis.repr x i = 0
    · rw [hi, mul_zero]
    · rw [hx i hi, Int.cast_zero, zero_mul]

/-- The native momentum subspace uses the U charge of the original lattice monomial. -/
def fixedMomentum (a : UCharge) : Submodule ℂ State :=
  (Finsupp.supported ℂ ℂ {i : FullLabel | i.2.1.1 = a}).comap fullBasis.repr.toLinearMap

theorem mem_fixedMomentum_iff (a : UCharge) (x : State) :
    x ∈ fixedMomentum a ↔ ∀ i : FullLabel, i.2.1.1 ≠ a → fullBasis.repr x i = 0 := by
  change fullBasis.repr x ∈ Finsupp.supported ℂ ℂ _ ↔ _
  rw [Finsupp.mem_supported']
  rfl

/-- The relative mass shell is the simultaneous native b₀ and total-L₀ kernel at momentum a. -/
def relativeMassShell (a : UCharge) : Submodule ℂ State :=
  (fixedMomentum a ⊓ LinearMap.ker (b 0)) ⊓ LinearMap.ker totalL0

/-- The ordered U coordinates give the actual half-norm. -/
theorem hyperbolic_chargeEnergy (a : UCharge) :
    chargeEnergy hyperbolicData a = a 0 * a 1 := by
  have h := LatticePositiveEnergy.two_chargeEnergy hyperbolicData a
  change 2 * chargeEnergy hyperbolicData a =
    ∑ i : Fin 2, ∑ j : Fin 2, a i * hyperbolicData.G i j * a j at h
  rw [hyperbolic_gram] at h
  simp only [Fin.sum_univ_two,
    OrderedHyperbolicExtension.U_zero_zero, OrderedHyperbolicExtension.U_zero_one,
    OrderedHyperbolicExtension.U_one_zero, OrderedHyperbolicExtension.U_one_one,
    mul_zero, zero_mul, mul_one, zero_add, add_zero] at h
  linarith

/-- This half-norm agrees with that of the pure U charge in the actual Leech product. -/
theorem chargeEnergy_pureU (a : UCharge) :
    chargeEnergy ActualLeechHyperbolic.rank26Data
      (OrderedHyperbolicExtension.splice ActualLeechHyperbolic.leechData
        0 (a 0) (a 1)) = chargeEnergy hyperbolicData a := by
  rw [OrderedHyperbolicExtension.chargeEnergy_splice, LatticePositiveEnergy.chargeEnergy_zero,
    zero_add, hyperbolic_chargeEnergy]

/-- The integer energy equation with the relative ghost vacuum shift incorporated. -/
private theorem totalEnergy_eq_zero_iff (a : UCharge) (i : FullLabel)
    (hcharge : i.2.1.1 = a) :
    totalEnergy i = 0 ↔
      ((i.1.1 + oscillatorEnergy i.2.1.2 + level i.2.2 : ℕ) : ℤ) =
        1 - chargeEnergy hyperbolicData a := by
  simp only [totalEnergy, LatticeBRSTZeroEnergyReduction.totalEnergy,
    LatticePositiveEnergy.energy, Nat.cast_add, level_cast, BcGhostRelativeEnergy.relativeEnergy,
    hcharge]
  omega

def allowedLabels (a : UCharge) : Set FullLabel :=
  {i | i.2.1.1 = a ∧ 3 ∉ i.2.2 ∧
    ((i.1.1 + oscillatorEnergy i.2.1.2 + level i.2.2 : ℕ) : ℤ) =
      1 - chargeEnergy hyperbolicData a}

/-- The exact coefficient criterion for the native intersection, in both directions. -/
theorem mem_relativeMassShell_iff (a : UCharge) (x : State) :
    x ∈ relativeMassShell a ↔
      ∀ i : FullLabel, fullBasis.repr x i ≠ 0 → i ∈ allowedLabels a := by
  change (x ∈ fixedMomentum a ∧ b 0 x = 0) ∧ totalL0 x = 0 ↔ _
  rw [mem_fixedMomentum_iff, b_zero_iff, totalL0_zero_iff]
  constructor
  · rintro ⟨⟨hm, hb⟩, hL⟩ i hi
    have hcharge : i.2.1.1 = a := not_ne_iff.mp (fun h => hi (hm i h))
    exact ⟨hcharge, fun h => hi (hb i h), (totalEnergy_eq_zero_iff a i hcharge).mp (hL i hi)⟩
  · intro hx
    refine ⟨⟨fun i hm => not_not.mp (fun hi => hm (hx i hi).1),
      fun i hb => not_not.mp (fun hi => (hx i hi).2.1 hb)⟩, ?_⟩
    intro i hi
    exact (totalEnergy_eq_zero_iff a i (hx i hi).1).mpr (hx i hi).2.2

/-- The allowed vectors of the existing full basis span the actual kernel intersection. -/
theorem relativeMassShell_eq_span (a : UCharge) :
    relativeMassShell a = Submodule.span ℂ (fullBasis '' allowedLabels a) := by
  ext x
  rw [mem_relativeMassShell_iff, fullBasis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff]

private theorem ket_relativeLevel (S : Finset ℕ) (hS : 3 ∉ S) :
    BcGhostRelativeEnergy.RelativeLevel (level S) (ket S) := by
  rw [relative_level_coeff_iff]
  constructor
  · intro T hT
    have hne : S ≠ T := fun h => hS (h ▸ hT)
    simp [ket, hne]
  · intro T hT
    by_cases h : T = S
    · subst T
      exact (level_cast S).symm
    · simp [ket, Ne.symm h] at hT

private theorem allowed_charge_le_one (a : UCharge) {i : FullLabel}
    (hi : i ∈ allowedLabels a) : chargeEnergy hyperbolicData a ≤ 1 := by
  have h := hi.2.2
  omega

private theorem allowed_bounds (a : UCharge) {i : FullLabel} (hi : i ∈ allowedLabels a) :
    i.1.1 + oscillatorEnergy i.2.1.2 + level i.2.2 = massShellCutoff hyperbolicData a ∧
      i.2.2 ⊆ Finset.range (2 * massShellCutoff hyperbolicData a + 4) := by
  have hcut := massShellCutoff_cast hyperbolicData a (allowed_charge_le_one a hi)
  have he : i.1.1 + oscillatorEnergy i.2.1.2 + level i.2.2 =
      massShellCutoff hyperbolicData a := Int.ofNat_inj.mp (hi.2.2.trans hcut.symm)
  have hsites := relative_level_support (level i.2.2) (ket i.2.2)
    (ket_relativeLevel i.2.2 hi.2.1) i.2.2 (by simp [ket])
  refine ⟨he, fun j hj => Finset.mem_range.mpr ?_⟩
  have h := Finset.mem_range.mp (hsites hj)
  omega

/-- Every occupied coefficient obeys the total excitation cutoff and the ghost site bound. -/
theorem coefficient_support_bound (a : UCharge) {x : State} (hx : x ∈ relativeMassShell a)
    {i : FullLabel} (hi : fullBasis.repr x i ≠ 0) :
    i.1.1 + oscillatorEnergy i.2.1.2 + level i.2.2 = massShellCutoff hyperbolicData a ∧
      i.2.2 ⊆ Finset.range (2 * massShellCutoff hyperbolicData a + 4) :=
  allowed_bounds a ((mem_relativeMassShell_iff a x).mp hx i hi)

theorem relativeMassShell_eq_bot_of_one_lt (a : UCharge)
    (ha : 1 < chargeEnergy hyperbolicData a) : relativeMassShell a = ⊥ := by
  rw [relativeMassShell_eq_span]
  have hempty : allowedLabels a = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr (fun _ hi => (not_le_of_gt ha) (allowed_charge_le_one a hi))
  rw [hempty, Set.image_empty, Submodule.span_empty]

private theorem allowedLabels_finite (a : UCharge) : (allowedLabels a).Finite := by
  classical
  let N := massShellCutoff hyperbolicData a
  let _ := oscillatorLeFinite hyperbolicData N
  let encode (i : allowedLabels a) :
      (Σ n : Fin (N + 1), Fin (Module.finrank ℂ ((orbifoldMode 0).eigenspace (n.val : ℂ)))) ×
      {d : LatticePositiveEnergy.Exponent hyperbolicData // oscillatorEnergy d ≤ N} ×
      {S : Finset ℕ // S ∈ (Finset.range (2 * N + 4)).powerset} := by
    have h := allowed_bounds a i.property
    exact ⟨⟨⟨i.val.1.1, by omega⟩, i.val.1.2⟩,
      ⟨i.val.2.1.2, by omega⟩, ⟨i.val.2.2, Finset.mem_powerset.mpr h.2⟩⟩
  let forget (j : Σ n : Fin (N + 1),
      Fin (Module.finrank ℂ ((orbifoldMode 0).eigenspace (n.val : ℂ)))) : OrbifoldLabel :=
    ⟨j.1.val, j.2⟩
  have hinj : Function.Injective encode := by
    intro i j h
    apply Subtype.ext
    refine Prod.ext (congrArg (fun z => forget z.1) h) (Prod.ext ?_ ?_)
    · exact Prod.ext (i.property.1.trans j.property.1.symm) (congrArg (fun z => z.2.1.val) h)
    · exact congrArg (fun z => z.2.2.val) h
  let _ : Finite (allowedLabels a) := Finite.of_injective encode hinj
  exact Set.toFinite _

/-- The finite orbifold weight bases and the oscillator and ghost cutoffs give finite dimension. -/
theorem relativeMassShell_finiteDimensional (a : UCharge) :
    FiniteDimensional ℂ (relativeMassShell a) := by
  rw [relativeMassShell_eq_span]
  exact FiniteDimensional.span_of_finite ℂ ((allowedLabels_finite a).image fullBasis)

private theorem fixedMomentum_eq_span (a : UCharge) :
    fixedMomentum a = Submodule.span ℂ (fullBasis '' {i : FullLabel | i.2.1.1 = a}) := by
  ext x
  change (fullBasis.repr x ∈ Finsupp.supported ℂ ℂ _ ↔ _)
  rw [Finsupp.mem_supported]
  exact fullBasis.mem_span_image.symm

private theorem single_tmul_mem_fixedMomentum (a : UCharge) (u : Orbifold)
    (p : Oscillator hyperbolicData) (w : Fock) :
    (u ⊗ₜ[ℂ] Finsupp.single a p) ⊗ₜ[ℂ] w ∈ fixedMomentum a := by
  rw [mem_fixedMomentum_iff]
  rintro ⟨j, ⟨q, d⟩, S⟩ hq
  rw [← orbifoldSlice_coeff, orbifoldSlice_tmul]
  let c := (LatticeRelativeMassShell.tensorBasis hyperbolicData).coord ((q, d), S)
  change c (orbifoldBasis.repr u j • (Finsupp.single a p ⊗ₜ[ℂ] w)) = 0
  rw [map_smul, smul_eq_mul]
  change orbifoldBasis.repr u j *
    LatticeRelativeMassShell.coeff hyperbolicData (Finsupp.single a p ⊗ₜ[ℂ] w) ((q, d), S) = 0
  rw [LatticeRelativeMassShell.coeff_tmul_original]
  simp [hq]

private theorem summand_mem_fixedMomentum (a : UCharge) (m : ℤ) (u : Orbifold)
    (p : Oscillator hyperbolicData) (w : Fock) :
    VirasoroBRST.summand matterDatum m ((u ⊗ₜ[ℂ] Finsupp.single a p) ⊗ₜ[ℂ] w) ∈
      fixedMomentum a := by
  change TensorProduct.map (mode m) (BcGhostFock.c (-m))
    ((u ⊗ₜ[ℂ] Finsupp.single a p) ⊗ₜ[ℂ] w) ∈ _
  simp only [TensorProduct.map_tmul, mode, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, TensorProduct.add_tmul, hyperbolicMode]
  rw [LatticeSugawaraVirasoro.sugawaraMode_single_sector]
  exact (fixedMomentum a).add_mem (single_tmul_mem_fixedMomentum a _ _ _)
    (single_tmul_mem_fixedMomentum a _ _ _)

/-- Each matter-ghost summand and the pure ghost charge preserve actual hyperbolic momentum. -/
theorem Q_mem_fixedMomentum (a : UCharge) {x : State} (hx : x ∈ fixedMomentum a) :
    Q x ∈ fixedMomentum a := by
  rw [fixedMomentum_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨⟨j, ⟨q, d⟩, S⟩, hq, rfl⟩
      have hqa : q = a := hq
      subst q
      rw [fullBasis_apply]
      apply (fixedMomentum a).add_mem
      · change (∑ᶠ m : ℤ, VirasoroBRST.summand matterDatum m
          ((orbifoldBasis j ⊗ₜ[ℂ] Finsupp.single a (MvPolynomial.monomial d 1)) ⊗ₜ[ℂ] ket S)) ∈ _
        exact finsum_induction _ (fixedMomentum a).zero_mem
          (fun _ _ => (fixedMomentum a).add_mem)
          (fun m => summand_mem_fixedMomentum a m _ _ _)
      · change TensorProduct.map LinearMap.id BcGhostBRST.Qg
          ((orbifoldBasis j ⊗ₜ[ℂ] Finsupp.single a (MvPolynomial.monomial d 1)) ⊗ₜ[ℂ] ket S) ∈ _
        rw [TensorProduct.map_tmul, LinearMap.id_apply]
        exact single_tmul_mem_fixedMomentum a _ _ _
  | zero => rw [map_zero]; exact (fixedMomentum a).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (fixedMomentum a).add_mem hx hy
  | smul z x _ hx => rw [map_smul]; exact (fixedMomentum a).smul_mem z hx

/-- The native Ward identity and total-energy commutation close the relative constraints. -/
theorem Q_mem_relativeMassShell (a : UCharge) {x : State} (hx : x ∈ relativeMassShell a) :
    Q x ∈ relativeMassShell a := by
  change (x ∈ fixedMomentum a ∧ b 0 x = 0) ∧ totalL0 x = 0 at hx
  obtain ⟨⟨hm, hb⟩, hL⟩ := hx
  change (Q x ∈ fixedMomentum a ∧ b 0 (Q x) = 0) ∧ totalL0 (Q x) = 0
  refine ⟨⟨Q_mem_fixedMomentum a hm, ?_⟩, ?_⟩
  · have h := LinearMap.congr_fun (Q_ward_b 0) x
    change Q (b 0 x) + b 0 (Q x) = totalL0 x at h
    simpa only [hb, hL, map_zero, zero_add] using h
  · have h := LinearMap.congr_fun Q_totalL0 x
    change Q (totalL0 x) = totalL0 (Q x) at h
    simpa only [hL, map_zero] using h.symm

/-- The restriction of the native BRST differential to the fixed momentum shell. -/
def differential (a : UCharge) : Module.End ℂ (relativeMassShell a) :=
  Q.restrict (fun _ hx => Q_mem_relativeMassShell a hx)

theorem differential_squared (a : UCharge) : differential a ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Q (Q (x : State)) = 0
  have h := LinearMap.congr_fun Q_squared (x : State)
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply] using h

#print axioms fixedMomentum
#print axioms mem_fixedMomentum_iff
#print axioms relativeMassShell
#print axioms hyperbolic_chargeEnergy
#print axioms chargeEnergy_pureU
#print axioms allowedLabels
#print axioms mem_relativeMassShell_iff
#print axioms relativeMassShell_eq_span
#print axioms coefficient_support_bound
#print axioms relativeMassShell_eq_bot_of_one_lt
#print axioms relativeMassShell_finiteDimensional
#print axioms Q_mem_fixedMomentum
#print axioms Q_mem_relativeMassShell
#print axioms differential
#print axioms differential_squared

end D5.S3.VertexAlgebra.OriginalOrbifoldRelativeMassShell
