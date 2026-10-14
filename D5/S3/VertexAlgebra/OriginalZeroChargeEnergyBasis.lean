/- GID: D5/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalZeroChargeEnergyBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native coefficient support identifies the entire exceptional zero-energy sector. -/

import D5.S3.VertexAlgebra.OriginalZeroChargeEnergySector
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalZeroChargeEnergyBasis

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
  LatticeBcGhostBrstCharge BcGhostFockSupport LatticePositiveEnergy
  OriginalZeroChargeEnergySector
open scoped BigOperators TensorProduct

noncomputable section

abbrev FullIndex (D : LatticeData) := (Σ _ : Charge D, Exponent D) × Finset ℕ

def fullBasis (D : LatticeData) : Module.Basis (FullIndex D) ℂ (State D) :=
  (Finsupp.basis (fun _ : Charge D =>
    MvPolynomial.basisMonomials (Index D) ℂ)).tensorProduct
      (Finsupp.basisSingleOne : Module.Basis (Finset ℕ) ℂ (Fock ℂ))

theorem fullBasis_apply (D : LatticeData) (index : FullIndex D) :
    fullBasis D index =
      Finsupp.single index.1.1 (MvPolynomial.monomial index.1.2 1) ⊗ₜ[ℂ]
        Finsupp.single index.2 1 := by
  simp [fullBasis, Module.Basis.tensorProduct_apply', Finsupp.coe_basis,
    MvPolynomial.coe_basisMonomials]

def fullEnergy (D : LatticeData) (index : FullIndex D) : ℤ :=
  energy D (index.1.1, index.1.2) + BcGhostLZeroSpectrum.energy index.2

theorem totalZero_fullBasis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (index : FullIndex D) :
    (M D H 0 + G D 0) (fullBasis D index) =
      (fullEnergy D index : ℂ) • fullBasis D index := by
  have homogeneous := MvPolynomial.isWeightedHomogeneous_monomial
    (fun site : Index D => site.2 + 1) index.1.2 (1 : ℂ) rfl
  have matter := sugawaraMode_weighted_homogeneous D H leftInverse rightInverse
    index.1.1 (MvPolynomial.monomial index.1.2 1) (oscillatorEnergy index.1.2) homogeneous
  have halfNorm : (bilinear D index.1.1 index.1.1 : ℂ) / 2 =
      (chargeEnergy D index.1.1 : ℂ) := by
    have integral := two_chargeEnergy D index.1.1
    have cast := congrArg (fun value : ℤ => (value : ℂ)) integral
    push_cast at cast
    rw [div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)]
    simpa only [mul_comm] using cast.symm
  rw [fullBasis_apply]
  simp only [LinearMap.add_apply, M, G, TensorProduct.map_tmul, LinearMap.id_apply,
    matter, BcGhostLZeroSpectrum.L_zero_single, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, ← add_smul, halfNorm]
  congr 1
  simp [fullEnergy, energy, add_comm]

theorem totalZero_coefficient (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (state : State D) (index : FullIndex D) :
    (fullBasis D).repr ((M D H 0 + G D 0) state) index =
      (fullEnergy D index : ℂ) * (fullBasis D).repr state index := by
  have identity :
      (Finsupp.lapply index).comp ((fullBasis D).repr.toLinearMap.comp (M D H 0 + G D 0)) =
      (fullEnergy D index : ℂ) •
        ((Finsupp.lapply index).comp (fullBasis D).repr.toLinearMap) := by
    apply (fullBasis D).ext
    intro other
    by_cases same : other = index <;>
      simp [totalZero_fullBasis D H leftInverse rightInverse, same]
  exact congrArg (fun operator : State D →ₗ[ℂ] ℂ => operator state) identity

def labels (D : LatticeData) : Set (FullIndex D) :=
  {index | index.1.1 = 0 ∧
    (oscillatorEnergy index.1.2 : ℤ) + BcGhostLZeroSpectrum.energy index.2 = 0}

abbrev sector (D : LatticeData) : Submodule ℂ (State D) :=
  (Finsupp.supported ℂ ℂ (labels D)).comap (fullBasis D).repr.toLinearMap

theorem mem_sector_iff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftInverse : H * gramComplex D = 1) (rightInverse : gramComplex D * H = 1)
    (state : State D) :
    state ∈ sector D ↔
      (∀ index : FullIndex D, index.1.1 ≠ 0 → (fullBasis D).repr state index = 0) ∧
        (M D H 0 + G D 0) state = 0 := by
  change (fullBasis D).repr state ∈ Finsupp.supported ℂ ℂ (labels D) ↔ _
  rw [Finsupp.mem_supported']
  constructor
  · intro supported
    refine ⟨fun index nonzero => supported index (fun member => nonzero member.1), ?_⟩
    apply (fullBasis D).repr.injective
    ext index
    rw [totalZero_coefficient D H leftInverse rightInverse]
    by_cases member : index ∈ labels D
    · have zeroEnergy : fullEnergy D index = 0 := by
        simp only [fullEnergy, energy, member.1, chargeEnergy_zero, zero_add]
        exact member.2
      simp [zeroEnergy]
    · simp [supported index member]
  · rintro ⟨chargeSupport, annihilated⟩ index outside
    by_cases nonzeroCharge : index.1.1 ≠ 0
    · exact chargeSupport index nonzeroCharge
    have zeroCharge : index.1.1 = 0 := not_ne_iff.mp nonzeroCharge
    have nonzeroEnergy : fullEnergy D index ≠ 0 := by
      intro zeroEnergy
      apply outside
      refine ⟨zeroCharge, ?_⟩
      simpa only [fullEnergy, energy, zeroCharge, chargeEnergy_zero, zero_add] using zeroEnergy
    have equation := totalZero_coefficient D H leftInverse rightInverse state index
    simp only [annihilated, map_zero, Finsupp.zero_apply] at equation
    exact (mul_eq_zero.mp equation.symm).resolve_left (by exact_mod_cast nonzeroEnergy)

def sectorCoordinates (D : LatticeData) : sector D ≃ₗ[ℂ] (labels D →₀ ℂ) :=
  (LinearEquiv.ofSubmodule' (fullBasis D).repr
    (Finsupp.supported ℂ ℂ (labels D))).trans (Finsupp.supportedEquivFinsupp _)

def fiberBasis (D : LatticeData) : Module.Basis (labels D) ℂ (sector D) :=
  Module.Basis.ofRepr (sectorCoordinates D)

inductive GhostIndex
  | empty
  | zeroMode
  | pair
  | triple
  deriving DecidableEq

instance : Fintype GhostIndex where
  elems := {.empty, .zeroMode, .pair, .triple}
  complete index := by cases index <;> simp

def ghostSites : GhostIndex → Finset ℕ
  | .empty => ∅
  | .zeroMode => {3}
  | .pair => {1, 5}
  | .triple => {1, 3, 5}

abbrev BasisIndex (D : LatticeData) := GhostIndex ⊕ (Fin D.rank × Bool)

def basisLabel (D : LatticeData) : BasisIndex D → FullIndex D
  | .inl ghost => (⟨0, 0⟩, ghostSites ghost)
  | .inr (axis, includeZero) =>
      (⟨0, Finsupp.single (axis, 0) 1⟩, if includeZero then {1, 3} else {1})

private theorem basisLabel_mem (D : LatticeData) (index : BasisIndex D) :
    basisLabel D index ∈ labels D := by
  rcases index with ghost | ⟨axis, includeZero⟩
  · cases ghost <;>
      simp [basisLabel, labels, ghostSites, oscillatorEnergy,
        BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight]
  · cases includeZero <;>
      norm_num [basisLabel, labels, oscillatorEnergy, Finsupp.weight_single,
        BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight]

private theorem ghostSites_injective : Function.Injective ghostSites := by
  intro first second same
  have one := congrArg (fun subset : Finset ℕ => 1 ∈ subset) same
  have three := congrArg (fun subset : Finset ℕ => 3 ∈ subset) same
  have five := congrArg (fun subset : Finset ℕ => 5 ∈ subset) same
  cases first <;> cases second <;> simp [ghostSites] at one three five ⊢

theorem basisLabel_injective (D : LatticeData) : Function.Injective (basisLabel D) := by
  intro first second same
  rcases first with ghostFirst | ⟨axisFirst, zeroFirst⟩ <;>
    rcases second with ghostSecond | ⟨axisSecond, zeroSecond⟩
  · exact congrArg Sum.inl (ghostSites_injective (congrArg Prod.snd same))
  · have powers := congrArg (fun index : FullIndex D => index.1.2) same
    change 0 = Finsupp.single (axisSecond, 0) 1 at powers
    exact False.elim ((Finsupp.single_ne_zero.mpr (by decide : (1 : ℕ) ≠ 0)) powers.symm)
  · have powers := congrArg (fun index : FullIndex D => index.1.2) same
    change Finsupp.single (axisFirst, 0) 1 = 0 at powers
    exact False.elim ((Finsupp.single_ne_zero.mpr (by decide : (1 : ℕ) ≠ 0)) powers)
  · have powers := congrArg (fun index : FullIndex D => index.1.2) same
    have sites := congrArg Prod.snd same
    have axis : axisFirst = axisSecond := by
      have count := congrArg (fun exponent : Exponent D => exponent (axisFirst, 0)) powers
      simp only [basisLabel, Finsupp.single_eq_same] at count
      by_contra different
      simp [different] at count
    have zero : zeroFirst = zeroSecond := by
      have membership := congrArg (fun subset : Finset ℕ => 3 ∈ subset) sites
      cases zeroFirst <;> cases zeroSecond <;> simp [basisLabel] at membership ⊢
    simp [axis, zero]

theorem basisLabel_surjective (D : LatticeData) :
    Function.Surjective (fun index : BasisIndex D =>
      (⟨basisLabel D index, basisLabel_mem D index⟩ : labels D)) := by
  rintro ⟨⟨⟨charge, powers⟩, subset⟩, zeroCharge, zeroEnergy⟩
  dsimp at zeroCharge zeroEnergy
  subst charge
  have alternatives := (zero_energy_labels D powers subset).mp zeroEnergy
  rcases alternatives with ⟨rfl, ground⟩ | ⟨⟨axis, rfl⟩, excited⟩
  · rcases ground with rfl | rfl | rfl | rfl
    · exact ⟨.inl .empty, rfl⟩
    · exact ⟨.inl .zeroMode, rfl⟩
    · exact ⟨.inl .pair, rfl⟩
    · exact ⟨.inl .triple, rfl⟩
  · rcases excited with rfl | rfl
    · exact ⟨.inr (axis, false), rfl⟩
    · exact ⟨.inr (axis, true), rfl⟩

def labelEquiv (D : LatticeData) : BasisIndex D ≃ labels D :=
  Equiv.ofBijective (fun index => ⟨basisLabel D index, basisLabel_mem D index⟩)
    ⟨fun _ _ same => basisLabel_injective D (congrArg Subtype.val same),
      basisLabel_surjective D⟩

def sectorBasis (D : LatticeData) : Module.Basis (BasisIndex D) ℂ (sector D) :=
  (fiberBasis D).reindex (labelEquiv D).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem sectorBasis_coe (D : LatticeData) (index : BasisIndex D) :
    (sectorBasis D index : State D) = fullBasis D (basisLabel D index) := by
  apply (fullBasis D).repr.injective
  simp only [sectorBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    fiberBasis, Module.Basis.coe_ofRepr, Module.Basis.repr_self]
  rw [sectorCoordinates, LinearEquiv.symm_trans_apply,
    LinearEquiv.ofSubmodule'_symm_apply, LinearEquiv.apply_symm_apply,
    Finsupp.supportedEquivFinsupp_symm_single]
  rfl

def indexDegree (D : LatticeData) : BasisIndex D → ℤ
  | .inl .empty => 0
  | .inl .zeroMode => 1
  | .inl .pair => 2
  | .inl .triple => 3
  | .inr (_, includeZero) => if includeZero then 2 else 1

theorem basisLabel_degree (D : LatticeData) (index : BasisIndex D) :
    BcGhostNumber.degree (basisLabel D index).2 = indexDegree D index := by
  rcases index with ghost | ⟨axis, includeZero⟩
  · cases ghost <;> norm_num [basisLabel, ghostSites, indexDegree,
      BcGhostNumber.degree, Finset.filter_insert, Finset.filter_singleton]
  · cases includeZero <;> norm_num [basisLabel, indexDegree,
      BcGhostNumber.degree, Finset.filter_insert, Finset.filter_singleton]

theorem J_sectorBasis (D : LatticeData) (index : BasisIndex D) :
    LatticeBcGhostBrstGhostNumber.J D (sectorBasis D index : State D) =
      (indexDegree D index : ℂ) • (sectorBasis D index : State D) := by
  rw [sectorBasis_coe, fullBasis_apply]
  simp [LatticeBcGhostBrstGhostNumber.J, BcGhostNumber.J,
    basisLabel_degree, ← TensorProduct.tmul_smul]

instance sectorFiniteDimensional (D : LatticeData) : FiniteDimensional ℂ (sector D) :=
  Module.Finite.of_basis (sectorBasis D)

theorem sector_finrank (D : LatticeData) : Module.finrank ℂ (sector D) = 4 + 2 * D.rank := by
  rw [Module.finrank_eq_card_basis (sectorBasis D)]
  simp [BasisIndex, show Fintype.card GhostIndex = 4 from by decide, Nat.mul_comm]

#print axioms mem_sector_iff
#print axioms basisLabel_surjective
#print axioms sector_finrank

end
end D5.S3.VertexAlgebra.OriginalZeroChargeEnergyBasis
