import D5.S3.VertexAlgebra.TemporaryNeutralNativeSupport
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence
import D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 8

namespace D5.S3.VertexAlgebra.LatticeBcGhostNeutralCohomology

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge LatticeBcGhostBrstNeutralMatrix
  LatticeBcGhostBrstVacuumClass BcGhostFockSupport
open scoped BigOperators TensorProduct Classical

noncomputable section

inductive NativeIndex (D : LatticeData) where
  | v
  | u
  | j (axis : Fin D.rank)
  | k (axis : Fin D.rank)
  | z
  | w
  deriving DecidableEq, Fintype

def nativeLabel (D : LatticeData) : NativeIndex D → Support.TensorLabel D
  | .v => ((0, 0), ∅)
  | .u => ((0, 0), {3})
  | .j axis => ((0, Finsupp.single (axis, 0) 1), {1})
  | .k axis => ((0, Finsupp.single (axis, 0) 1), {1, 3})
  | .z => ((0, 0), {1, 5})
  | .w => ((0, 0), {1, 3, 5})

def orientation (D : LatticeData) : NativeIndex D → ℂ
  | .v => 1
  | .u => 1
  | .j _ => 1
  | .k _ => -1
  | .z => -1
  | .w => -1

def native (D : LatticeData) : NativeIndex D → State D
  | .v => vacuumState D
  | .u => uState D
  | .j axis => jState D axis
  | .k axis => kState D axis
  | .z => zState D
  | .w => wState D

def E0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Submodule ℂ (State D) := Support.neutral D ⊓ LinearMap.ker (M D H 0 + G D 0)

def neutralChargeProjection (D : LatticeData) : Module.End ℂ (State D) :=
  (Support.stateBasis D).repr.symm.toLinearMap.comp
    ((Finsupp.supported ℂ ℂ {label : Support.TensorLabel D | label.1.1 = 0}).subtype.comp
      ((Finsupp.restrictDom ℂ ℂ {label : Support.TensorLabel D | label.1.1 = 0}).comp
        (Support.stateBasis D).repr.toLinearMap))

theorem neutralChargeProjection_coeff (D : LatticeData) (state : State D)
    (label : Support.TensorLabel D) :
    (Support.stateBasis D).repr (neutralChargeProjection D state) label =
      if label.1.1 = 0 then (Support.stateBasis D).repr state label else 0 := by
  simp [neutralChargeProjection, Finsupp.filter_apply]

theorem neutral_fixed_iff (D : LatticeData) (state : State D) :
    neutralChargeProjection D state = state ↔ state ∈ Support.neutral D := by
  change _ ↔ (Support.stateBasis D).repr state ∈
    Finsupp.supported ℂ ℂ {label : Support.TensorLabel D | label.1.1 = 0}
  rw [Finsupp.mem_supported']
  constructor
  · intro fixed label outside
    change label.1.1 ≠ 0 at outside
    have equality := congrArg (fun input => (Support.stateBasis D).repr input label) fixed
    rw [neutralChargeProjection_coeff, if_neg outside] at equality
    exact equality.symm
  · intro supported
    apply (Support.stateBasis D).repr.injective
    ext label
    rw [neutralChargeProjection_coeff]
    split_ifs with chosen
    · rfl
    · exact (supported label chosen).symm

theorem mem_E0_iff (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (state : State D) : state ∈ E0 D H ↔
      neutralChargeProjection D state = state ∧ (M D H 0 + G D 0) state = 0 := by
  simp only [E0, Submodule.mem_inf, LinearMap.mem_ker, neutral_fixed_iff]

theorem nativeLabel_injective (D : LatticeData) : Function.Injective (nativeLabel D) := by
  intro first second equality
  have tags := congrArg (fun label : Support.TensorLabel D => label.2.sum id) equality
  cases first <;> cases second <;> try { norm_num [nativeLabel] at tags } <;> try rfl
  all_goals
    rename_i axis other
    congr 1
    by_contra different
    have coefficient := congrArg
      (fun label : Support.TensorLabel D => label.1.2 (axis, 0)) equality
    simp [nativeLabel, Finsupp.single_apply, different, Ne.symm different] at coefficient

theorem nativeLabel_range (D : LatticeData) :
    Set.range (nativeLabel D) = Support.zeroLabels D := by
  ext label
  constructor
  · rintro ⟨index, rfl⟩
    cases index <;> simp [nativeLabel, Support.zeroLabels]
    all_goals exact ⟨_, rfl⟩
  · rintro ⟨chargeZero, ground | oscillator⟩
    · rcases ground with ⟨exponentZero, subset | subset | subset | subset⟩
      · exact ⟨.v, by ext <;> simp [nativeLabel, chargeZero, exponentZero, subset]⟩
      · exact ⟨.u, by ext <;> simp [nativeLabel, chargeZero, exponentZero, subset]⟩
      · exact ⟨.z, by ext <;> simp [nativeLabel, chargeZero, exponentZero, subset]⟩
      · exact ⟨.w, by ext <;> simp [nativeLabel, chargeZero, exponentZero, subset]⟩
    · rcases oscillator with ⟨axis, exponent, subset | subset⟩
      · exact ⟨.j axis, by ext <;> simp [nativeLabel, chargeZero, exponent, subset]⟩
      · exact ⟨.k axis, by ext <;> simp [nativeLabel, chargeZero, exponent, subset]⟩

theorem orientation_square (D : LatticeData) (index : NativeIndex D) :
    orientation D index * orientation D index = 1 := by
  cases index <;> norm_num [orientation]

theorem native_signed_basis (D : LatticeData) (index : NativeIndex D) :
    native D index = orientation D index • Support.stateBasis D (nativeLabel D index) := by
  cases index <;>
    simp [native, nativeLabel, orientation, Support.stateBasis_apply,
      LatticePositiveEnergy.carrierBasis_apply, vacuumState, vacuumVector,
      uState, jState, kState, zState, wState, neutralMatter, C,
      TensorProduct.map_tmul, TensorProduct.tmul_neg, neg_one_smul,
      c, create, vacuum, Finsupp.linearCombination_single, createBasis, sign,
      MvPolynomial.X]
  all_goals norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.insert_comm, Finsupp.single_neg, TensorProduct.tmul_neg]
  all_goals congr 2 <;> decide

def coordinates (D : LatticeData) : State D →ₗ[ℂ] (NativeIndex D → ℂ) where
  toFun state index := orientation D index * (Support.stateBasis D).repr state (nativeLabel D index)
  map_add' first second := by ext index; simp [mul_add]
  map_smul' scalar state := by ext index; simp [smul_eq_mul, mul_left_comm]

def realize (D : LatticeData) : (NativeIndex D → ℂ) →ₗ[ℂ] State D where
  toFun coefficient := ∑ index, coefficient index • native D index
  map_add' first second := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' scalar coefficient := by simp [smul_smul, Finset.smul_sum]

theorem coordinates_native (D : LatticeData) (input output : NativeIndex D) :
    coordinates D (native D input) output = if input = output then 1 else 0 := by
  rw [native_signed_basis]
  change orientation D output *
    ((Support.stateBasis D).repr (orientation D input •
      Support.stateBasis D (nativeLabel D input)) (nativeLabel D output)) = _
  rw [map_smul]
  change orientation D output *
    (orientation D input * (Support.stateBasis D).repr
      (Support.stateBasis D (nativeLabel D input)) (nativeLabel D output)) = _
  rw [(Support.stateBasis D).repr_self]
  by_cases equality : input = output
  · subst input
    simp [Finsupp.single_apply, orientation_square]
  · have different : nativeLabel D input ≠ nativeLabel D output :=
      fun same => equality (nativeLabel_injective D same)
    simp [Finsupp.single_apply, equality, different]

theorem coordinates_realize (D : LatticeData) (coefficient : NativeIndex D → ℂ) :
    coordinates D (realize D coefficient) = coefficient := by
  ext output
  simp [realize, map_sum, map_smul, coordinates_native, Pi.smul_apply,
    Finset.sum_ite_eq', smul_eq_mul]

theorem realize_single (D : LatticeData) (index : NativeIndex D) (scalar : ℂ) :
    realize D (Pi.single index scalar) = scalar • native D index := by
  simp [realize, Pi.single_apply, Finset.sum_ite_eq']

theorem native_mem_E0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (index : NativeIndex D) : native D index ∈ E0 D H := by
  rw [E0, Support.neutral_T0_kernel_eq_span D H hHG hGH, native_signed_basis]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨nativeLabel D index, nativeLabel_range D ▸ Set.mem_range_self index, rfl⟩

theorem realize_mem_E0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (coefficient : NativeIndex D → ℂ) : realize D coefficient ∈ E0 D H := by
  change (∑ index, coefficient index • native D index) ∈ E0 D H
  apply Submodule.sum_mem
  intro index _
  exact Submodule.smul_mem _ _ (native_mem_E0 D H hHG hGH index)

theorem E0_eq_range_realize (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    E0 D H = LinearMap.range (realize D) := by
  apply le_antisymm
  · rw [E0, Support.neutral_T0_kernel_eq_span D H hHG hGH]
    apply Submodule.span_le.mpr
    rintro state ⟨label, allowed, rfl⟩
    obtain ⟨index, rfl⟩ := (nativeLabel_range D).symm ▸ allowed
    refine ⟨Pi.single index (orientation D index), ?_⟩
    rw [realize_single, native_signed_basis, smul_smul, orientation_square, one_smul]
  · rintro state ⟨coefficient, rfl⟩
    exact realize_mem_E0 D H hHG hGH coefficient

theorem realize_coordinates (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) :
    realize D (coordinates D state) = state := by
  rw [E0_eq_range_realize D H hHG hGH] at membership
  obtain ⟨coefficient, rfl⟩ := membership
  rw [coordinates_realize]

def coordinateEquiv (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    E0 D H ≃ₗ[ℂ] (NativeIndex D → ℂ) where
  toLinearMap := (coordinates D).comp (E0 D H).subtype
  invFun coefficient := ⟨realize D coefficient, realize_mem_E0 D H hHG hGH coefficient⟩
  left_inv state := Subtype.ext (realize_coordinates D H hHG hGH state state.property)
  right_inv := coordinates_realize D

def nativeBasis (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.Basis (NativeIndex D) ℂ (E0 D H) :=
  (Pi.basisFun ℂ (NativeIndex D)).map (coordinateEquiv D H hHG hGH).symm

theorem nativeBasis_apply (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (index : NativeIndex D) :
    (nativeBasis D H hHG hGH index : State D) = native D index := by
  simp [nativeBasis, coordinateEquiv, Pi.basisFun_apply, realize_single]

theorem neutralCoefficient_kronecker (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (first second : Fin D.rank) :
    neutralCoefficient D H first second = kronecker D first second := by
  have left := congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ =>
    matrix first second) hHG
  have right := congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ =>
    matrix second first) hGH
  simp only [Matrix.mul_apply, Matrix.one_apply] at left right
  have transposeSum : ∑ axis, H axis first * gramComplex D axis second =
      ∑ axis, gramComplex D second axis * H axis first := by
    apply Finset.sum_congr rfl
    intro axis _
    change H axis first * (D.G axis second : ℂ) = (D.G second axis : ℂ) * H axis first
    rw [D.symmetric axis second]
    ring
  simp only [neutralCoefficient, add_mul, Finset.sum_add_distrib]
  rw [transposeSum, left, right]
  by_cases equality : first = second
  · norm_num [kronecker, equality]
  · simp [kronecker, equality, Ne.symm equality]

def coordinateQ (D : LatticeData) : Module.End ℂ (NativeIndex D → ℂ) where
  toFun coefficient index := if index = .z then (-2 : ℂ) * coefficient .u else 0
  map_add' first second := by ext index; split_ifs <;> simp_all [mul_add]
  map_smul' scalar coefficient := by ext index; split_ifs <;> simp_all [smul_eq_mul, mul_left_comm]

theorem Q_native (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (index : NativeIndex D) : Q D H (native D index) =
      if index = .u then (-2 : ℂ) • native D .z else 0 := by
  cases index
  · simpa [native] using Q_vacuum D H
  · simpa [native] using Q_c0_vacuum D H
  · simpa [native, neutralCoefficient_kronecker D H hHG hGH] using
      Q_one_oscillator D H _
  · simpa [native] using Q_c0_one_oscillator D H _
  · simpa [native] using Q_z D H
  · simpa [native] using Q_w D H

theorem Q_realize (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (coefficient : NativeIndex D → ℂ) :
    Q D H (realize D coefficient) = realize D (coordinateQ D coefficient) := by
  simp [realize, map_sum, map_smul, Q_native D H hHG hGH,
    coordinateQ, Finset.sum_ite_eq', smul_smul, mul_comm]

theorem Q_coordinates (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) :
    coordinates D (Q D H state) = coordinateQ D (coordinates D state) := by
  conv_lhs => rw [← realize_coordinates D H hHG hGH state membership]
  rw [Q_realize D H hHG hGH, coordinates_realize]

theorem Q_mem_E0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : E0 D H) : Q D H state ∈ E0 D H := by
  rw [← realize_coordinates D H hHG hGH state state.property, Q_realize D H hHG hGH]
  exact realize_mem_E0 D H hHG hGH _

def differential (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (E0 D H) :=
  ((Q D H).comp (E0 D H).subtype).codRestrict (E0 D H) (Q_mem_E0 D H hHG hGH)

theorem differential_square_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) :
    (differential D H hHG hGH).comp (differential D H hHG hGH) = 0 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  have square := LinearMap.congr_fun
    (LatticeBcGhostBrstNilpotence.nilpotent D H hHG hGH hcritical) (state : State D)
  simpa [differential, Module.End.mul_apply] using square

theorem coordinate_chain_equivalence (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    (coordinateEquiv D H hHG hGH).toLinearMap.comp (differential D H hHG hGH) =
      (coordinateQ D).comp (coordinateEquiv D H hHG hGH).toLinearMap := by
  ext state index
  exact congrFun (Q_coordinates D H hHG hGH state state.property) index

theorem Q_on_E0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) :
    Q D H state = ((-2 : ℂ) * coordinates D state .u) • native D .z := by
  conv_lhs => rw [← realize_coordinates D H hHG hGH state membership]
  rw [Q_realize D H hHG hGH]
  have single : coordinateQ D (coordinates D state) =
      Pi.single .z ((-2 : ℂ) * coordinates D state .u) := by
    ext index
    simp [coordinateQ, Pi.single_apply, eq_comm]
  rw [single, realize_single]

theorem cycle_iff_u_zero (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) :
    Q D H state = 0 ↔ coordinates D state .u = 0 := by
  constructor
  · intro cycle
    have coefficient := congrArg (fun input => coordinates D input .z) cycle
    rw [Q_coordinates D H hHG hGH state membership] at coefficient
    have product : (-2 : ℂ) * coordinates D state .u = 0 := by
      simpa [coordinateQ] using coefficient
    exact (mul_eq_zero.mp product).resolve_left (by norm_num)
  · intro vanished
    rw [Q_on_E0 D H hHG hGH state membership, vanished, mul_zero, zero_smul]

theorem E0_full_image_iff_z (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) :
    state ∈ LinearMap.range (Q D H) ↔ ∃ scalar : ℂ, state = scalar • native D .z := by
  have reduction := Image.full_image_iff_restricted D H hHG hGH state membership
  constructor
  · intro boundary
    obtain ⟨preimage, preimageMembership, equality⟩ := reduction.mp boundary
    exact ⟨(-2 : ℂ) * coordinates D preimage .u,
      equality.symm.trans (Q_on_E0 D H hHG hGH preimage preimageMembership)⟩
  · rintro ⟨scalar, rfl⟩
    refine ⟨(-scalar / 2) • native D .u, ?_⟩
    have acted : Q D H (native D .u) = (-2 : ℂ) • native D .z := by
      simpa using Q_native D H hHG hGH .u
    rw [map_smul, acted, smul_smul]
    have cancellation : (-scalar / 2 : ℂ) * (-2) = scalar := by ring
    rw [cancellation]

def Cycles (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Submodule ℂ (State D) := E0 D H ⊓ LinearMap.ker (Q D H)

def Boundaries (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Submodule ℂ (Cycles D H) := (LinearMap.range (Q D H)).comap (Cycles D H).subtype

def AbsoluteCohomology (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :=
  (Cycles D H) ⧸ Boundaries D H

attribute [reducible] AbsoluteCohomology

def boundaryWitness (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : E0 D H →ₗ[ℂ] Cycles D H :=
  ((Q D H).comp (E0 D H).subtype).codRestrict (Cycles D H) (fun state => by
    refine ⟨Q_mem_E0 D H hHG hGH state, ?_⟩
    have square := LinearMap.congr_fun
      (LatticeBcGhostBrstNilpotence.nilpotent D H hHG hGH hcritical) (state : State D)
    simpa [Module.End.mul_apply] using square)

theorem Boundaries_eq_range_boundaryWitness (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) :
    Boundaries D H = LinearMap.range (boundaryWitness D H hHG hGH hcritical) := by
  ext state
  change (state : State D) ∈ LinearMap.range (Q D H) ↔ _
  rw [Image.full_image_iff_restricted D H hHG hGH state state.property.1]
  constructor
  · rintro ⟨preimage, membership, equality⟩
    exact ⟨⟨preimage, membership⟩, Subtype.ext equality⟩
  · rintro ⟨preimage, equality⟩
    exact ⟨preimage, preimage.property, congrArg Subtype.val equality⟩

abbrev AbsoluteCoordinates (D : LatticeData) :=
  ℂ × (Fin D.rank → ℂ) × (Fin D.rank → ℂ) × ℂ

def absoluteEmbed (D : LatticeData) : AbsoluteCoordinates D →ₗ[ℂ] (NativeIndex D → ℂ) where
  toFun coefficient index := match index with
    | .v => coefficient.1
    | .u => 0
    | .j axis => coefficient.2.1 axis
    | .k axis => coefficient.2.2.1 axis
    | .z => 0
    | .w => coefficient.2.2.2
  map_add' first second := by ext index; cases index <;> simp
  map_smul' scalar coefficient := by ext index; cases index <;> simp

def absoluteRepresentative (D : LatticeData) : AbsoluteCoordinates D →ₗ[ℂ] State D :=
  (realize D).comp (absoluteEmbed D)

def absoluteRepresentCycle (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    AbsoluteCoordinates D →ₗ[ℂ] Cycles D H :=
  (absoluteRepresentative D).codRestrict (Cycles D H) (fun coefficient => by
    have membership := realize_mem_E0 D H hHG hGH (absoluteEmbed D coefficient)
    refine ⟨membership, (cycle_iff_u_zero D H hHG hGH _ membership).mpr ?_⟩
    simp [absoluteRepresentative, coordinates_realize, absoluteEmbed])

def absoluteRead (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Cycles D H →ₗ[ℂ] AbsoluteCoordinates D where
  toFun state := (coordinates D state .v, fun axis => coordinates D state (.j axis),
    fun axis => coordinates D state (.k axis), coordinates D state .w)
  map_add' first second := by ext <;> simp
  map_smul' scalar state := by ext <;> simp

theorem absoluteRead_represent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (coefficient : AbsoluteCoordinates D) :
    absoluteRead D H (absoluteRepresentCycle D H hHG hGH coefficient) = coefficient := by
  simp [absoluteRead, absoluteRepresentCycle, absoluteRepresentative,
    coordinates_realize, absoluteEmbed]

theorem absolute_cycle_split (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : Cycles D H) : (state : State D) =
      absoluteRepresentative D (absoluteRead D H state) +
        coordinates D state .z • native D .z := by
  have uZero := (cycle_iff_u_zero D H hHG hGH state state.property.1).mp state.property.2
  have coefficientSplit : coordinates D state =
      absoluteEmbed D (absoluteRead D H state) + Pi.single .z (coordinates D state .z) := by
    ext index
    cases index <;> simp [absoluteEmbed, absoluteRead, Pi.single_apply, uZero]
  calc
    (state : State D) = realize D (coordinates D state) :=
      (realize_coordinates D H hHG hGH state state.property.1).symm
    _ = _ := by
      conv_lhs => rw [coefficientSplit, map_add, realize_single]
      rfl

theorem absoluteRead_kernel (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : LinearMap.ker (absoluteRead D H) = Boundaries D H := by
  ext state
  constructor
  · intro vanished
    have split := absolute_cycle_split D H hHG hGH state
    rw [LinearMap.mem_ker] at vanished
    rw [vanished, map_zero, zero_add] at split
    exact (E0_full_image_iff_z D H hHG hGH state state.property.1).mpr
      ⟨coordinates D state .z, split⟩
  · intro boundary
    rw [Boundaries_eq_range_boundaryWitness D H hHG hGH hcritical] at boundary
    obtain ⟨preimage, rfl⟩ := boundary
    change absoluteRead D H (boundaryWitness D H hHG hGH hcritical preimage) = 0
    have matrix := Q_coordinates D H hHG hGH preimage preimage.property
    ext <;> simp [absoluteRead, boundaryWitness, matrix, coordinateQ]

def absoluteQuotientRead (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : AbsoluteCohomology D H →ₗ[ℂ] AbsoluteCoordinates D :=
  (Boundaries D H).liftQ (absoluteRead D H)
    (absoluteRead_kernel D H hHG hGH hcritical).symm.le

def absoluteQuotientRepresentative (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    AbsoluteCoordinates D →ₗ[ℂ] AbsoluteCohomology D H :=
  (Boundaries D H).mkQ.comp (absoluteRepresentCycle D H hHG hGH)

def absoluteEquiv (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : AbsoluteCohomology D H ≃ₗ[ℂ] AbsoluteCoordinates D where
  toLinearMap := absoluteQuotientRead D H hHG hGH hcritical
  invFun := absoluteQuotientRepresentative D H hHG hGH
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro state
    change (Boundaries D H).mkQ
      (absoluteRepresentCycle D H hHG hGH (absoluteRead D H state)) =
        (Boundaries D H).mkQ state
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ,
      ← absoluteRead_kernel D H hHG hGH hcritical, LinearMap.mem_ker, map_sub,
      absoluteRead_represent, sub_self]
  right_inv coefficient := absoluteRead_represent D H hHG hGH coefficient

theorem absoluteEquiv_mkQ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (state : Cycles D H) :
    absoluteEquiv D H hHG hGH hcritical ((Boundaries D H).mkQ state) =
      absoluteRead D H state := rfl

theorem absoluteEquiv_inverse (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (coefficient : AbsoluteCoordinates D) :
    (absoluteEquiv D H hHG hGH hcritical).symm coefficient =
      (Boundaries D H).mkQ (absoluteRepresentCycle D H hHG hGH coefficient) := rfl

theorem cycle_difference_full_image_iff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (first second : Cycles D H) :
    ((first : State D) - second) ∈ LinearMap.range (Q D H) ↔
      absoluteRead D H first = absoluteRead D H second := by
  change first - second ∈ Boundaries D H ↔ _
  rw [← absoluteRead_kernel D H hHG hGH hcritical, LinearMap.mem_ker, map_sub, sub_eq_zero]

theorem representatives_full_image_injective (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (first second : AbsoluteCoordinates D) :
    absoluteRepresentative D first - absoluteRepresentative D second ∈
      LinearMap.range (Q D H) ↔ first = second := by
  have result :=
    cycle_difference_full_image_iff D H hHG hGH hcritical
      (absoluteRepresentCycle D H hHG hGH first) (absoluteRepresentCycle D H hHG hGH second)
  change absoluteRepresentative D first - absoluteRepresentative D second ∈
    LinearMap.range (Q D H) ↔
    absoluteRead D H (absoluteRepresentCycle D H hHG hGH first) =
      absoluteRead D H (absoluteRepresentCycle D H hHG hGH second) at result
  simpa only [absoluteRead_represent] using result

theorem representatives_full_image_surjective (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (state : Cycles D H) :
    ∃ coefficient : AbsoluteCoordinates D,
      (state : State D) - absoluteRepresentative D coefficient ∈ LinearMap.range (Q D H) := by
  refine ⟨absoluteRead D H state, ?_⟩
  exact (cycle_difference_full_image_iff D H hHG hGH hcritical state
    (absoluteRepresentCycle D H hHG hGH (absoluteRead D H state))).mpr
      (absoluteRead_represent D H hHG hGH _).symm

def ghostDegree (D : LatticeData) : NativeIndex D → ℤ
  | .v => 0
  | .u => 1
  | .j _ => 1
  | .k _ => 2
  | .z => 2
  | .w => 3

def coordinateJ (D : LatticeData) : Module.End ℂ (NativeIndex D → ℂ) where
  toFun coefficient index := (ghostDegree D index : ℂ) * coefficient index
  map_add' first second := by ext index; simp [mul_add]
  map_smul' scalar coefficient := by ext index; simp [smul_eq_mul, mul_left_comm]

theorem J_native (D : LatticeData) (index : NativeIndex D) :
    LatticeBcGhostBrstGhostNumber.J D (native D index) =
      (ghostDegree D index : ℂ) • native D index := by
  rw [native_signed_basis]
  cases index <;>
    simp [nativeLabel, orientation, ghostDegree, Support.stateBasis_apply,
      LatticeBcGhostBrstGhostNumber.J, BcGhostNumber.J, BcGhostNumber.degree,
      Finsupp.linearCombination_single, TensorProduct.map_tmul,
      TensorProduct.tmul_smul, smul_smul, mul_comm]
  all_goals norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finsupp.smul_single, ← TensorProduct.tmul_smul]

theorem J_realize (D : LatticeData) (coefficient : NativeIndex D → ℂ) :
    LatticeBcGhostBrstGhostNumber.J D (realize D coefficient) =
      realize D (coordinateJ D coefficient) := by
  simp [realize, map_sum, map_smul, J_native, coordinateJ, smul_smul, mul_comm]

theorem J_coordinates (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) :
    coordinates D (LatticeBcGhostBrstGhostNumber.J D state) =
      coordinateJ D (coordinates D state) := by
  conv_lhs => rw [← realize_coordinates D H hHG hGH state membership]
  rw [J_realize, coordinates_realize]

theorem B_native (D : LatticeData) (index : NativeIndex D) :
    B D 0 (native D index) = match index with
      | .u => native D .v
      | .k axis => native D (.j axis)
      | .w => -native D .z
      | _ => 0 := by
  cases index <;>
    simp [native_signed_basis, nativeLabel, orientation, Support.stateBasis_apply,
      B, b, annihilate, Finsupp.linearCombination_single, annihilateBasis, sign,
      TensorProduct.map_tmul, TensorProduct.tmul_neg, neg_one_smul]
  all_goals norm_num [Finset.filter_insert, Finset.filter_singleton,
    Finset.erase_insert_of_ne, Finset.erase_singleton, Finsupp.single_neg,
    TensorProduct.tmul_neg]

def coordinateB (D : LatticeData) : Module.End ℂ (NativeIndex D → ℂ) where
  toFun coefficient index := match index with
    | .v => coefficient .u
    | .j axis => coefficient (.k axis)
    | .z => -coefficient .w
    | _ => 0
  map_add' first second := by ext index; cases index <;> simp [add_comm]
  map_smul' scalar coefficient := by ext index; cases index <;> simp

theorem coordinateB_single (D : LatticeData) (index : NativeIndex D) :
    coordinateB D (Pi.single index 1) = match index with
      | .u => Pi.single .v 1
      | .k axis => Pi.single (.j axis) 1
      | .w => Pi.single .z (-1)
      | _ => 0 := by
  ext output
  cases index <;> cases output <;> simp [coordinateB, Pi.single_apply, eq_comm]

theorem B_realize (D : LatticeData) (coefficient : NativeIndex D → ℂ) :
    B D 0 (realize D coefficient) = realize D (coordinateB D coefficient) := by
  have equality : (B D 0).comp (realize D) = (realize D).comp (coordinateB D) := by
    apply (Pi.basisFun ℂ (NativeIndex D)).ext
    intro index
    rw [Pi.basisFun_apply]
    change B D 0 (realize D (Pi.single index 1)) =
      realize D (coordinateB D (Pi.single index 1))
    rw [realize_single, one_smul, B_native, coordinateB_single]
    cases index <;> simp [realize_single]
  exact LinearMap.congr_fun equality coefficient

theorem B_coordinates (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) :
    coordinates D (B D 0 state) = coordinateB D (coordinates D state) := by
  conv_lhs => rw [← realize_coordinates D H hHG hGH state membership]
  rw [B_realize, coordinates_realize]

theorem B_kernel_iff (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) : B D 0 state = 0 ↔
      coordinates D state .u = 0 ∧
      (∀ axis, coordinates D state (.k axis) = 0) ∧ coordinates D state .w = 0 := by
  constructor
  · intro killed
    have matrix := B_coordinates D H hHG hGH state membership
    rw [killed, map_zero] at matrix
    refine ⟨?_, ?_, ?_⟩
    · simpa [coordinateB] using (congrFun matrix .v).symm
    · intro axis
      simpa [coordinateB] using (congrFun matrix (.j axis)).symm
    · have negated : -coordinates D state .w = 0 := by
        simpa [coordinateB] using (congrFun matrix .z).symm
      exact neg_eq_zero.mp negated
  · rintro ⟨uZero, kZero, wZero⟩
    conv_lhs => rw [← realize_coordinates D H hHG hGH state membership]
    rw [B_realize]
    have vanished : coordinateB D (coordinates D state) = 0 := by
      ext index
      cases index <;> simp [coordinateB, uZero, kZero, wZero]
    rw [vanished, map_zero]

def RelativeSpace (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Submodule ℂ (State D) := E0 D H ⊓ LinearMap.ker (B D 0)

attribute [reducible] RelativeSpace

theorem relative_Q_zero (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : RelativeSpace D H) : Q D H state = 0 := by
  apply (cycle_iff_u_zero D H hHG hGH state state.property.1).mpr
  exact ((B_kernel_iff D H hHG hGH state state.property.1).mp state.property.2).1

def relativeDifferential (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (RelativeSpace D H) :=
  ((Q D H).comp (RelativeSpace D H).subtype).codRestrict (RelativeSpace D H)
    (fun state => by
      change Q D H (state : State D) ∈ RelativeSpace D H
      rw [relative_Q_zero D H hHG hGH state]
      exact Submodule.zero_mem _)

theorem relativeDifferential_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    relativeDifferential D H hHG hGH = 0 := by
  apply LinearMap.ext
  intro state
  apply Subtype.ext
  exact relative_Q_zero D H hHG hGH state

def RelativeCycles (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Submodule ℂ (RelativeSpace D H) := LinearMap.ker (relativeDifferential D H hHG hGH)

attribute [reducible] RelativeCycles

def RelativeBoundaries (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Submodule ℂ (RelativeCycles D H hHG hGH) :=
  (LinearMap.range (relativeDifferential D H hHG hGH)).comap
    (RelativeCycles D H hHG hGH).subtype

def RelativeCohomology (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :=
  (RelativeCycles D H hHG hGH) ⧸ RelativeBoundaries D H hHG hGH

attribute [reducible] RelativeCohomology

theorem relative_cycles_top (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    RelativeCycles D H hHG hGH = ⊤ := by
  simp [RelativeCycles, relativeDifferential_zero]

theorem relative_boundaries_bot (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    RelativeBoundaries D H hHG hGH = ⊥ := by
  ext state
  change (state : RelativeSpace D H) ∈
    LinearMap.range (relativeDifferential D H hHG hGH) ↔ state = 0
  rw [relativeDifferential_zero, LinearMap.range_zero, Submodule.mem_bot]
  constructor
  · intro vanished
    exact Subtype.ext vanished
  · intro vanished
    exact congrArg Subtype.val vanished

abbrev RelativeCoordinates (D : LatticeData) := ℂ × (Fin D.rank → ℂ) × ℂ

def relativeEmbed (D : LatticeData) : RelativeCoordinates D →ₗ[ℂ] (NativeIndex D → ℂ) where
  toFun coefficient index := match index with
    | .v => coefficient.1
    | .j axis => coefficient.2.1 axis
    | .z => coefficient.2.2
    | _ => 0
  map_add' first second := by ext index; cases index <;> simp
  map_smul' scalar coefficient := by ext index; cases index <;> simp

def relativeRepresentative (D : LatticeData) : RelativeCoordinates D →ₗ[ℂ] State D :=
  (realize D).comp (relativeEmbed D)

def relativeRepresentSpace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    RelativeCoordinates D →ₗ[ℂ] RelativeSpace D H :=
  (relativeRepresentative D).codRestrict (RelativeSpace D H) (fun coefficient => by
    have membership := realize_mem_E0 D H hHG hGH (relativeEmbed D coefficient)
    refine ⟨membership, (B_kernel_iff D H hHG hGH _ membership).mpr ?_⟩
    simp [relativeRepresentative, coordinates_realize, relativeEmbed])

def relativeRepresentCycle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    RelativeCoordinates D →ₗ[ℂ] RelativeCycles D H hHG hGH :=
  (relativeRepresentSpace D H hHG hGH).codRestrict (RelativeCycles D H hHG hGH)
    (fun coefficient => by rw [relative_cycles_top]; exact Submodule.mem_top)

def relativeRead (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    RelativeCycles D H hHG hGH →ₗ[ℂ] RelativeCoordinates D where
  toFun state := (coordinates D (state : RelativeSpace D H) .v,
    fun axis => coordinates D (state : RelativeSpace D H) (.j axis),
    coordinates D (state : RelativeSpace D H) .z)
  map_add' first second := by ext <;> simp
  map_smul' scalar state := by ext <;> simp

theorem relativeRead_represent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (coefficient : RelativeCoordinates D) :
    relativeRead D H hHG hGH (relativeRepresentCycle D H hHG hGH coefficient) = coefficient := by
  simp [relativeRead, relativeRepresentCycle, relativeRepresentSpace,
    relativeRepresentative, coordinates_realize, relativeEmbed]

theorem relative_reconstruction (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : RelativeCycles D H hHG hGH) :
    relativeRepresentCycle D H hHG hGH (relativeRead D H hHG hGH state) = state := by
  apply Subtype.ext
  apply Subtype.ext
  have relativeMembership := (state : RelativeSpace D H).property
  have zeros := (B_kernel_iff D H hHG hGH _ relativeMembership.1).mp relativeMembership.2
  change realize D (relativeEmbed D (relativeRead D H hHG hGH state)) =
    (state : RelativeSpace D H)
  rw [← realize_coordinates D H hHG hGH _ relativeMembership.1]
  congr 1
  ext index
  cases index <;> simp [relativeEmbed, relativeRead, zeros.1, zeros.2.1, zeros.2.2]

theorem relativeRead_kernel (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    LinearMap.ker (relativeRead D H hHG hGH) = RelativeBoundaries D H hHG hGH := by
  rw [relative_boundaries_bot]
  ext state
  rw [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro vanished
    rw [← relative_reconstruction D H hHG hGH state, vanished, map_zero]
  · intro vanished
    rw [vanished, map_zero]

def relativeQuotientRead (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    RelativeCohomology D H hHG hGH →ₗ[ℂ] RelativeCoordinates D :=
  (RelativeBoundaries D H hHG hGH).liftQ (relativeRead D H hHG hGH)
    (relativeRead_kernel D H hHG hGH).symm.le

def relativeQuotientRepresentative (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    RelativeCoordinates D →ₗ[ℂ] RelativeCohomology D H hHG hGH :=
  (RelativeBoundaries D H hHG hGH).mkQ.comp (relativeRepresentCycle D H hHG hGH)

def relativeEquiv (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    RelativeCohomology D H hHG hGH ≃ₗ[ℂ] RelativeCoordinates D where
  toLinearMap := relativeQuotientRead D H hHG hGH
  invFun := relativeQuotientRepresentative D H hHG hGH
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro state
    change (RelativeBoundaries D H hHG hGH).mkQ
      (relativeRepresentCycle D H hHG hGH (relativeRead D H hHG hGH state)) =
        (RelativeBoundaries D H hHG hGH).mkQ state
    rw [relative_reconstruction]
  right_inv := relativeRead_represent D H hHG hGH

theorem z_absolute_exact (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    zState D ∈ LinearMap.range (Q D H) := by
  refine ⟨(-1 / 2 : ℂ) • uState D, ?_⟩
  rw [map_smul, Q_c0_vacuum, smul_smul]
  norm_num

theorem z_relative_nonexact (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    ¬ ∃ preimage : RelativeSpace D H, Q D H preimage = zState D := by
  rintro ⟨preimage, equality⟩
  rw [relative_Q_zero D H hHG hGH preimage] at equality
  have coefficient := congrArg (fun input => coordinates D input .z) equality
  have occupied := coordinates_native D .z .z
  simpa [native] using coefficient.trans occupied

theorem neutral_P0_mem (D : LatticeData) (state : State D)
    (membership : state ∈ Support.neutral D) : Energy.P0 D state ∈ Support.neutral D := by
  change (Support.stateBasis D).repr (Energy.P0 D state) ∈
    Finsupp.supported ℂ ℂ {label : Support.TensorLabel D | label.1.1 = 0}
  rw [Finsupp.mem_supported']
  have vanishing := (Finsupp.mem_supported' ℂ ((Support.stateBasis D).repr state)).mp membership
  intro label outside
  change (Energy.fullBasis D).repr (Energy.energyWeight D
    (fun energy => if energy = 0 then 1 else 0) state) label = 0
  rw [Energy.energyWeight_coeff]
  change _ * (Support.stateBasis D).repr state label = 0
  rw [vanishing label outside, mul_zero]

theorem P0_fixed_on_E0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) : Energy.P0 D state = state := by
  apply (Support.stateBasis D).repr.injective
  ext label
  change (Energy.fullBasis D).repr (Energy.energyWeight D
    (fun energy => if energy = 0 then 1 else 0) state) label = _
  rw [Energy.energyWeight_coeff]
  change (if Energy.totalEnergy D label = 0 then (1 : ℂ) else 0) *
    (Energy.fullBasis D).repr state label = (Energy.fullBasis D).repr state label
  by_cases energyZero : Energy.totalEnergy D label = 0
  · simp [energyZero]
  · have killed : (M D H 0 + G D 0) state = 0 := membership.2
    have coefficient := Energy.totalZero_coeff D H hHG hGH state label
    rw [killed, map_zero, Finsupp.zero_apply] at coefficient
    have vanished := (mul_eq_zero.mp coefficient.symm).resolve_left
      (Int.cast_ne_zero.mpr energyZero)
    simp [energyZero, vanished]

def NeutralCycles (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Submodule ℂ (State D) := Support.neutral D ⊓ LinearMap.ker (Q D H)

def NeutralBoundaries (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Submodule ℂ (NeutralCycles D H) :=
  (LinearMap.range (Q D H)).comap (NeutralCycles D H).subtype

def FullNeutralCohomology (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :=
  (NeutralCycles D H) ⧸ NeutralBoundaries D H

attribute [reducible] FullNeutralCohomology

def neutralCycleProjection (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    NeutralCycles D H →ₗ[ℂ] Cycles D H :=
  ((Energy.P0 D).comp (NeutralCycles D H).subtype).codRestrict (Cycles D H) (fun state => by
    refine ⟨⟨neutral_P0_mem D state state.property.1, ?_⟩, ?_⟩
    · have killed := LinearMap.congr_fun (Energy.totalZero_P0 D H hHG hGH) (state : State D)
      simpa [Module.End.mul_apply] using killed
    · have commutes := LinearMap.congr_fun
        (Energy.energyWeight_commutes D H hHG hGH
          (fun energy => if energy = 0 then 1 else 0)) (state : State D)
      change Energy.P0 D (Q D H state) = Q D H (Energy.P0 D state) at commutes
      rw [state.property.2, map_zero] at commutes
      exact commutes.symm)

def zeroCycleInclusion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Cycles D H →ₗ[ℂ] NeutralCycles D H :=
  (Cycles D H).subtype.codRestrict (NeutralCycles D H)
    (fun state => ⟨state.property.1.1, state.property.2⟩)

def fullNeutralRead (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    NeutralCycles D H →ₗ[ℂ] AbsoluteCoordinates D :=
  (absoluteRead D H).comp (neutralCycleProjection D H hHG hGH)

def fullNeutralRepresentCycle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    AbsoluteCoordinates D →ₗ[ℂ] NeutralCycles D H :=
  (zeroCycleInclusion D H).comp (absoluteRepresentCycle D H hHG hGH)

theorem neutralCycleProjection_inclusion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : Cycles D H) :
    neutralCycleProjection D H hHG hGH (zeroCycleInclusion D H state) = state := by
  apply Subtype.ext
  exact P0_fixed_on_E0 D H hHG hGH state state.property.1

theorem fullNeutralRead_represent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (coefficient : AbsoluteCoordinates D) :
    fullNeutralRead D H hHG hGH (fullNeutralRepresentCycle D H hHG hGH coefficient) =
      coefficient := by
  change absoluteRead D H (neutralCycleProjection D H hHG hGH
    (zeroCycleInclusion D H (absoluteRepresentCycle D H hHG hGH coefficient))) = _
  rw [neutralCycleProjection_inclusion, absoluteRead_represent]

theorem fullNeutralRead_kernel (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) :
    LinearMap.ker (fullNeutralRead D H hHG hGH) = NeutralBoundaries D H := by
  ext state
  constructor
  · intro vanished
    have projectedBoundary : neutralCycleProjection D H hHG hGH state ∈ Boundaries D H := by
      rw [← absoluteRead_kernel D H hHG hGH hcritical, LinearMap.mem_ker]
      exact vanished
    obtain ⟨preimage, equality⟩ := projectedBoundary
    have homotopy := LinearMap.congr_fun (Energy.homotopy_identity D H hHG hGH)
      (state : State D)
    have difference : (state : State D) - Energy.P0 D state = Q D H (Energy.h D state) := by
      have closed : Q D H (state : State D) = 0 := state.property.2
      simpa [Module.End.mul_apply, closed] using homotopy.symm
    refine ⟨Energy.h D state + preimage, ?_⟩
    rw [map_add, ← difference]
    change (state : State D) - Energy.P0 D state + Q D H preimage = state
    change Q D H preimage = Energy.P0 D state at equality
    rw [equality, sub_add_cancel]
  · rintro ⟨preimage, equality⟩
    change absoluteRead D H (neutralCycleProjection D H hHG hGH state) = 0
    rw [← LinearMap.mem_ker, absoluteRead_kernel D H hHG hGH hcritical]
    refine ⟨Energy.P0 D preimage, ?_⟩
    have commutes := LinearMap.congr_fun
      (Energy.energyWeight_commutes D H hHG hGH
        (fun energy => if energy = 0 then 1 else 0)) preimage
    change Energy.P0 D (Q D H preimage) = Q D H (Energy.P0 D preimage) at commutes
    rw [equality] at commutes
    exact commutes.symm

def fullNeutralQuotientRead (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : FullNeutralCohomology D H →ₗ[ℂ] AbsoluteCoordinates D :=
  (NeutralBoundaries D H).liftQ (fullNeutralRead D H hHG hGH)
    (fullNeutralRead_kernel D H hHG hGH hcritical).symm.le

def fullNeutralEquiv (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : FullNeutralCohomology D H ≃ₗ[ℂ] AbsoluteCoordinates D where
  toLinearMap := fullNeutralQuotientRead D H hHG hGH hcritical
  invFun coefficient := (NeutralBoundaries D H).mkQ
    (fullNeutralRepresentCycle D H hHG hGH coefficient)
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro state
    change (NeutralBoundaries D H).mkQ
      (fullNeutralRepresentCycle D H hHG hGH (fullNeutralRead D H hHG hGH state)) =
        (NeutralBoundaries D H).mkQ state
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, Submodule.ker_mkQ,
      ← fullNeutralRead_kernel D H hHG hGH hcritical, LinearMap.mem_ker, map_sub,
      fullNeutralRead_represent, sub_self]
  right_inv := fullNeutralRead_represent D H hHG hGH

def absoluteWeight (D : LatticeData) : Module.End ℂ (AbsoluteCoordinates D) where
  toFun coefficient := (0, coefficient.2.1, (2 : ℂ) • coefficient.2.2.1,
    (3 : ℂ) * coefficient.2.2.2)
  map_add' first second := by ext <;> simp [smul_add, mul_add]
  map_smul' scalar coefficient := by ext <;> simp [smul_smul, smul_eq_mul, mul_left_comm, mul_assoc]

def relativeWeight (D : LatticeData) : Module.End ℂ (RelativeCoordinates D) where
  toFun coefficient := (0, coefficient.2.1, (2 : ℂ) * coefficient.2.2)
  map_add' first second := by ext <;> simp [mul_add]
  map_smul' scalar coefficient := by ext <;> simp [smul_eq_mul, mul_left_comm]

theorem J_mem_E0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : State D) (membership : state ∈ E0 D H) :
    LatticeBcGhostBrstGhostNumber.J D state ∈ E0 D H := by
  rw [← realize_coordinates D H hHG hGH state membership, J_realize]
  exact realize_mem_E0 D H hHG hGH _

def absoluteCycleJ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (Cycles D H) :=
  ((LatticeBcGhostBrstGhostNumber.J D).comp (Cycles D H).subtype).codRestrict
    (Cycles D H) (fun state => by
      have membership := J_mem_E0 D H hHG hGH state state.property.1
      refine ⟨membership, (cycle_iff_u_zero D H hHG hGH _ membership).mpr ?_⟩
      rw [J_coordinates D H hHG hGH state state.property.1]
      have uZero := (cycle_iff_u_zero D H hHG hGH state state.property.1).mp state.property.2
      simp [coordinateJ, ghostDegree, uZero])

theorem absoluteRead_J (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : Cycles D H) : absoluteRead D H (absoluteCycleJ D H hHG hGH state) =
      absoluteWeight D (absoluteRead D H state) := by
  have matrix := J_coordinates D H hHG hGH state state.property.1
  ext <;> simp [absoluteRead, absoluteCycleJ, matrix, coordinateJ, ghostDegree,
    absoluteWeight, smul_eq_mul]

def absoluteJ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : Module.End ℂ (AbsoluteCohomology D H) :=
  (Boundaries D H).liftQ ((Boundaries D H).mkQ.comp (absoluteCycleJ D H hHG hGH)) (by
    intro state boundary
    change (Boundaries D H).mkQ (absoluteCycleJ D H hHG hGH state) = 0
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ,
      ← absoluteRead_kernel D H hHG hGH hcritical, LinearMap.mem_ker, absoluteRead_J]
    have vanished : absoluteRead D H state = 0 := by
      rw [← LinearMap.mem_ker, absoluteRead_kernel D H hHG hGH hcritical]
      exact boundary
    rw [vanished, map_zero])

theorem absoluteEquiv_J (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (quotient : AbsoluteCohomology D H) :
    absoluteEquiv D H hHG hGH hcritical (absoluteJ D H hHG hGH hcritical quotient) =
      absoluteWeight D (absoluteEquiv D H hHG hGH hcritical quotient) := by
  refine Quotient.inductionOn quotient ?_
  intro state
  exact absoluteRead_J D H hHG hGH state

def relativeSpaceJ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (RelativeSpace D H) :=
  ((LatticeBcGhostBrstGhostNumber.J D).comp (RelativeSpace D H).subtype).codRestrict
    (RelativeSpace D H) (fun state => by
      have membership := J_mem_E0 D H hHG hGH state state.property.1
      refine ⟨membership, (B_kernel_iff D H hHG hGH _ membership).mpr ?_⟩
      have zeros := (B_kernel_iff D H hHG hGH state state.property.1).mp state.property.2
      rw [J_coordinates D H hHG hGH state state.property.1]
      simp [coordinateJ, ghostDegree, zeros.1, zeros.2.1, zeros.2.2])

def relativeCycleJ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (RelativeCycles D H hHG hGH) :=
  ((relativeSpaceJ D H hHG hGH).comp (RelativeCycles D H hHG hGH).subtype).codRestrict
    (RelativeCycles D H hHG hGH) (fun state => by
      have universal : ∀ value : RelativeSpace D H, value ∈ RelativeCycles D H hHG hGH := by
        intro value
        rw [relative_cycles_top]
        exact Submodule.mem_top
      exact universal _)

theorem relativeRead_J (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : RelativeCycles D H hHG hGH) :
    relativeRead D H hHG hGH (relativeCycleJ D H hHG hGH state) =
      relativeWeight D (relativeRead D H hHG hGH state) := by
  have matrix := J_coordinates D H hHG hGH (state : RelativeSpace D H)
    (state : RelativeSpace D H).property.1
  simp [relativeRead, relativeCycleJ, relativeSpaceJ, matrix, coordinateJ, ghostDegree,
    relativeWeight]

def relativeJ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.End ℂ (RelativeCohomology D H hHG hGH) :=
  (RelativeBoundaries D H hHG hGH).liftQ
    ((RelativeBoundaries D H hHG hGH).mkQ.comp (relativeCycleJ D H hHG hGH)) (by
      intro state boundary
      rw [relative_boundaries_bot, Submodule.mem_bot] at boundary
      change (RelativeBoundaries D H hHG hGH).mkQ (relativeCycleJ D H hHG hGH state) = 0
      simp [boundary])

theorem relativeEquiv_J (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (quotient : RelativeCohomology D H hHG hGH) :
    relativeEquiv D H hHG hGH (relativeJ D H hHG hGH quotient) =
      relativeWeight D (relativeEquiv D H hHG hGH quotient) := by
  refine Quotient.inductionOn quotient ?_
  intro state
  exact relativeRead_J D H hHG hGH state

def AbsoluteGrade (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (degree : ℤ) : Submodule ℂ (AbsoluteCohomology D H) :=
  LinearMap.ker (absoluteJ D H hHG hGH hcritical -
    (degree : ℂ) • LinearMap.id)

def RelativeGrade (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (degree : ℤ) : Submodule ℂ (RelativeCohomology D H hHG hGH) :=
  LinearMap.ker (relativeJ D H hHG hGH - (degree : ℂ) • LinearMap.id)

def AbsoluteCoordinateGrade (D : LatticeData) (degree : ℤ) :
    Submodule ℂ (AbsoluteCoordinates D) :=
  LinearMap.ker (absoluteWeight D - (degree : ℂ) • LinearMap.id)

def RelativeCoordinateGrade (D : LatticeData) (degree : ℤ) :
    Submodule ℂ (RelativeCoordinates D) :=
  LinearMap.ker (relativeWeight D - (degree : ℂ) • LinearMap.id)

theorem absoluteGrade_comap (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (degree : ℤ) :
    AbsoluteGrade D H hHG hGH hcritical degree =
      (AbsoluteCoordinateGrade D degree).comap
        (absoluteEquiv D H hHG hGH hcritical).toLinearMap := by
  ext quotient
  change absoluteJ D H hHG hGH hcritical quotient - (degree : ℂ) • quotient = 0 ↔
    absoluteWeight D (absoluteEquiv D H hHG hGH hcritical quotient) -
      (degree : ℂ) • absoluteEquiv D H hHG hGH hcritical quotient = 0
  constructor
  · intro vanished
    have mapped := congrArg (absoluteEquiv D H hHG hGH hcritical) vanished
    simpa [map_sub, map_smul, absoluteEquiv_J] using mapped
  · intro vanished
    apply (absoluteEquiv D H hHG hGH hcritical).injective
    simpa [map_sub, map_smul, absoluteEquiv_J] using vanished

theorem relativeGrade_comap (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (degree : ℤ) : RelativeGrade D H hHG hGH degree =
      (RelativeCoordinateGrade D degree).comap (relativeEquiv D H hHG hGH).toLinearMap := by
  ext quotient
  change relativeJ D H hHG hGH quotient - (degree : ℂ) • quotient = 0 ↔
    relativeWeight D (relativeEquiv D H hHG hGH quotient) -
      (degree : ℂ) • relativeEquiv D H hHG hGH quotient = 0
  constructor
  · intro vanished
    have mapped := congrArg (relativeEquiv D H hHG hGH) vanished
    simpa [map_sub, map_smul, relativeEquiv_J] using mapped
  · intro vanished
    apply (relativeEquiv D H hHG hGH).injective
    simpa [map_sub, map_smul, relativeEquiv_J] using vanished

def absoluteGradeEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (degree : ℤ) :
    AbsoluteGrade D H hHG hGH hcritical degree ≃ₗ[ℂ] AbsoluteCoordinateGrade D degree :=
  (LinearEquiv.ofEq _ _ (absoluteGrade_comap D H hHG hGH hcritical degree)).trans
    (LinearEquiv.ofSubmodule' (absoluteEquiv D H hHG hGH hcritical)
      (AbsoluteCoordinateGrade D degree))

def relativeGradeEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (degree : ℤ) :
    RelativeGrade D H hHG hGH degree ≃ₗ[ℂ] RelativeCoordinateGrade D degree :=
  (LinearEquiv.ofEq _ _ (relativeGrade_comap D H hHG hGH degree)).trans
    (LinearEquiv.ofSubmodule' (relativeEquiv D H hHG hGH) (RelativeCoordinateGrade D degree))

theorem absolute_eigen_iff (D : LatticeData) (degree : ℤ) (coefficient : AbsoluteCoordinates D) :
    coefficient ∈ AbsoluteCoordinateGrade D degree ↔
      (0 - (degree : ℂ)) * coefficient.1 = 0 ∧
      (∀ axis, (1 - (degree : ℂ)) * coefficient.2.1 axis = 0) ∧
      (∀ axis, (2 - (degree : ℂ)) * coefficient.2.2.1 axis = 0) ∧
      (3 - (degree : ℂ)) * coefficient.2.2.2 = 0 := by
  change absoluteWeight D coefficient - (degree : ℂ) • coefficient = 0 ↔ _
  constructor
  · intro equality
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [absoluteWeight, smul_eq_mul, sub_mul] using congrArg Prod.fst equality
    · intro axis
      simpa [absoluteWeight, smul_eq_mul, sub_mul] using
        congrArg (fun value : AbsoluteCoordinates D => value.2.1 axis) equality
    · intro axis
      simpa [absoluteWeight, smul_eq_mul, sub_mul] using
        congrArg (fun value : AbsoluteCoordinates D => value.2.2.1 axis) equality
    · simpa [absoluteWeight, smul_eq_mul, sub_mul] using
        congrArg (fun value : AbsoluteCoordinates D => value.2.2.2) equality
  · rintro ⟨first, second, third, fourth⟩
    apply Prod.ext
    · simpa [absoluteWeight, smul_eq_mul, sub_mul] using first
    · apply Prod.ext
      · ext axis
        simpa [absoluteWeight, smul_eq_mul, sub_mul] using second axis
      · apply Prod.ext
        · ext axis
          simpa [absoluteWeight, smul_eq_mul, sub_mul] using third axis
        · simpa [absoluteWeight, smul_eq_mul, sub_mul] using fourth

theorem relative_eigen_iff (D : LatticeData) (degree : ℤ) (coefficient : RelativeCoordinates D) :
    coefficient ∈ RelativeCoordinateGrade D degree ↔
      (0 - (degree : ℂ)) * coefficient.1 = 0 ∧
      (∀ axis, (1 - (degree : ℂ)) * coefficient.2.1 axis = 0) ∧
      (2 - (degree : ℂ)) * coefficient.2.2 = 0 := by
  change relativeWeight D coefficient - (degree : ℂ) • coefficient = 0 ↔ _
  constructor
  · intro equality
    refine ⟨?_, ?_, ?_⟩
    · simpa [relativeWeight, smul_eq_mul, sub_mul] using congrArg Prod.fst equality
    · intro axis
      simpa [relativeWeight, smul_eq_mul, sub_mul] using
        congrArg (fun value : RelativeCoordinates D => value.2.1 axis) equality
    · simpa [relativeWeight, smul_eq_mul, sub_mul] using
        congrArg (fun value : RelativeCoordinates D => value.2.2) equality
  · rintro ⟨first, second, third⟩
    apply Prod.ext
    · simpa [relativeWeight, smul_eq_mul, sub_mul] using first
    · apply Prod.ext
      · ext axis
        simpa [relativeWeight, smul_eq_mul, sub_mul] using second axis
      · simpa [relativeWeight, smul_eq_mul, sub_mul] using third


def absoluteCoordinateGradeZero (D : LatticeData) : AbsoluteCoordinateGrade D 0 ≃ₗ[ℂ] ℂ where
  toFun state := (state : AbsoluteCoordinates D).1
  invFun coefficient := ⟨(coefficient, 0, 0, 0), by rw [absolute_eigen_iff]; norm_num⟩
  left_inv state := by
    have equations := (absolute_eigen_iff D 0 (state : AbsoluteCoordinates D)).mp state.property
    apply Subtype.ext
    change ((state : AbsoluteCoordinates D).1, 0, 0, 0) = (state : AbsoluteCoordinates D)
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · ext axis
        have vanished : (state : AbsoluteCoordinates D).2.1 axis = 0 :=
          (mul_eq_zero.mp (equations.2.1 axis)).resolve_left (by norm_num)
        exact vanished.symm
      · apply Prod.ext
        · ext axis
          have vanished : (state : AbsoluteCoordinates D).2.2.1 axis = 0 :=
            (mul_eq_zero.mp (equations.2.2.1 axis)).resolve_left (by norm_num)
          exact vanished.symm
        · have vanished : (state : AbsoluteCoordinates D).2.2.2 = 0 :=
            (mul_eq_zero.mp equations.2.2.2).resolve_left (by norm_num)
          exact vanished.symm
  right_inv coefficient := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

def absoluteCoordinateGradeOne (D : LatticeData) : AbsoluteCoordinateGrade D 1 ≃ₗ[ℂ] (Fin D.rank → ℂ) where
  toFun state := (state : AbsoluteCoordinates D).2.1
  invFun coefficient := ⟨(0, coefficient, 0, 0), by rw [absolute_eigen_iff]; norm_num⟩
  left_inv state := by
    have equations := (absolute_eigen_iff D 1 (state : AbsoluteCoordinates D)).mp state.property
    apply Subtype.ext
    change (0, (state : AbsoluteCoordinates D).2.1, 0, 0) = (state : AbsoluteCoordinates D)
    apply Prod.ext
    · have vanished : (state : AbsoluteCoordinates D).1 = 0 :=
        (mul_eq_zero.mp equations.1).resolve_left (by norm_num)
      exact vanished.symm
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · ext axis
          have vanished : (state : AbsoluteCoordinates D).2.2.1 axis = 0 :=
            (mul_eq_zero.mp (equations.2.2.1 axis)).resolve_left (by norm_num)
          exact vanished.symm
        · have vanished : (state : AbsoluteCoordinates D).2.2.2 = 0 :=
            (mul_eq_zero.mp equations.2.2.2).resolve_left (by norm_num)
          exact vanished.symm
  right_inv coefficient := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

def absoluteCoordinateGradeTwo (D : LatticeData) : AbsoluteCoordinateGrade D 2 ≃ₗ[ℂ] (Fin D.rank → ℂ) where
  toFun state := (state : AbsoluteCoordinates D).2.2.1
  invFun coefficient := ⟨(0, 0, coefficient, 0), by rw [absolute_eigen_iff]; norm_num⟩
  left_inv state := by
    have equations := (absolute_eigen_iff D 2 (state : AbsoluteCoordinates D)).mp state.property
    apply Subtype.ext
    change (0, 0, (state : AbsoluteCoordinates D).2.2.1, 0) = (state : AbsoluteCoordinates D)
    apply Prod.ext
    · have vanished : (state : AbsoluteCoordinates D).1 = 0 :=
        (mul_eq_zero.mp equations.1).resolve_left (by norm_num)
      exact vanished.symm
    · apply Prod.ext
      · ext axis
        have vanished : (state : AbsoluteCoordinates D).2.1 axis = 0 :=
          (mul_eq_zero.mp (equations.2.1 axis)).resolve_left (by norm_num)
        exact vanished.symm
      · apply Prod.ext
        · rfl
        · have vanished : (state : AbsoluteCoordinates D).2.2.2 = 0 :=
            (mul_eq_zero.mp equations.2.2.2).resolve_left (by norm_num)
          exact vanished.symm
  right_inv coefficient := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

def absoluteCoordinateGradeThree (D : LatticeData) : AbsoluteCoordinateGrade D 3 ≃ₗ[ℂ] ℂ where
  toFun state := (state : AbsoluteCoordinates D).2.2.2
  invFun coefficient := ⟨(0, 0, 0, coefficient), by rw [absolute_eigen_iff]; norm_num⟩
  left_inv state := by
    have equations := (absolute_eigen_iff D 3 (state : AbsoluteCoordinates D)).mp state.property
    apply Subtype.ext
    change (0, 0, 0, (state : AbsoluteCoordinates D).2.2.2) = (state : AbsoluteCoordinates D)
    apply Prod.ext
    · have vanished : (state : AbsoluteCoordinates D).1 = 0 :=
        (mul_eq_zero.mp equations.1).resolve_left (by norm_num)
      exact vanished.symm
    · apply Prod.ext
      · ext axis
        have vanished : (state : AbsoluteCoordinates D).2.1 axis = 0 :=
          (mul_eq_zero.mp (equations.2.1 axis)).resolve_left (by norm_num)
        exact vanished.symm
      · apply Prod.ext
        · ext axis
          have vanished : (state : AbsoluteCoordinates D).2.2.1 axis = 0 :=
            (mul_eq_zero.mp (equations.2.2.1 axis)).resolve_left (by norm_num)
          exact vanished.symm
        · rfl
  right_inv coefficient := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

def relativeCoordinateGradeZero (D : LatticeData) : RelativeCoordinateGrade D 0 ≃ₗ[ℂ] ℂ where
  toFun state := (state : RelativeCoordinates D).1
  invFun coefficient := ⟨(coefficient, 0, 0), by rw [relative_eigen_iff]; norm_num⟩
  left_inv state := by
    have equations := (relative_eigen_iff D 0 (state : RelativeCoordinates D)).mp state.property
    apply Subtype.ext
    change ((state : RelativeCoordinates D).1, 0, 0) = (state : RelativeCoordinates D)
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · ext axis
        have vanished : (state : RelativeCoordinates D).2.1 axis = 0 :=
          (mul_eq_zero.mp (equations.2.1 axis)).resolve_left (by norm_num)
        exact vanished.symm
      · have vanished : (state : RelativeCoordinates D).2.2 = 0 :=
          (mul_eq_zero.mp equations.2.2).resolve_left (by norm_num)
        exact vanished.symm
  right_inv coefficient := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

def relativeCoordinateGradeOne (D : LatticeData) : RelativeCoordinateGrade D 1 ≃ₗ[ℂ] (Fin D.rank → ℂ) where
  toFun state := (state : RelativeCoordinates D).2.1
  invFun coefficient := ⟨(0, coefficient, 0), by rw [relative_eigen_iff]; norm_num⟩
  left_inv state := by
    have equations := (relative_eigen_iff D 1 (state : RelativeCoordinates D)).mp state.property
    apply Subtype.ext
    change (0, (state : RelativeCoordinates D).2.1, 0) = (state : RelativeCoordinates D)
    apply Prod.ext
    · have vanished : (state : RelativeCoordinates D).1 = 0 :=
        (mul_eq_zero.mp equations.1).resolve_left (by norm_num)
      exact vanished.symm
    · apply Prod.ext
      · rfl
      · have vanished : (state : RelativeCoordinates D).2.2 = 0 :=
          (mul_eq_zero.mp equations.2.2).resolve_left (by norm_num)
        exact vanished.symm
  right_inv coefficient := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

def relativeCoordinateGradeTwo (D : LatticeData) : RelativeCoordinateGrade D 2 ≃ₗ[ℂ] ℂ where
  toFun state := (state : RelativeCoordinates D).2.2
  invFun coefficient := ⟨(0, 0, coefficient), by rw [relative_eigen_iff]; norm_num⟩
  left_inv state := by
    have equations := (relative_eigen_iff D 2 (state : RelativeCoordinates D)).mp state.property
    apply Subtype.ext
    change (0, 0, (state : RelativeCoordinates D).2.2) = (state : RelativeCoordinates D)
    apply Prod.ext
    · have vanished : (state : RelativeCoordinates D).1 = 0 :=
        (mul_eq_zero.mp equations.1).resolve_left (by norm_num)
      exact vanished.symm
    · apply Prod.ext
      · ext axis
        have vanished : (state : RelativeCoordinates D).2.1 axis = 0 :=
          (mul_eq_zero.mp (equations.2.1 axis)).resolve_left (by norm_num)
        exact vanished.symm
      · rfl
  right_inv coefficient := rfl
  map_add' first second := rfl
  map_smul' scalar state := rfl

def absoluteGhostZeroEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26)
    : AbsoluteGrade D H hHG hGH hcritical 0 ≃ₗ[ℂ] ℂ :=
  (absoluteGradeEquiv D H hHG hGH hcritical 0).trans (absoluteCoordinateGradeZero D)

theorem absolute_ghost_0_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26)
    : Module.finrank ℂ (AbsoluteGrade D H hHG hGH hcritical 0) = 1 := by
  rw [(absoluteGhostZeroEquiv D H hHG hGH hcritical).finrank_eq]
  simp [Module.finrank_pi_fintype]

def absoluteGhostOneEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26)
    : AbsoluteGrade D H hHG hGH hcritical 1 ≃ₗ[ℂ] (Fin D.rank → ℂ) :=
  (absoluteGradeEquiv D H hHG hGH hcritical 1).trans (absoluteCoordinateGradeOne D)

theorem absolute_ghost_1_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26)
    : Module.finrank ℂ (AbsoluteGrade D H hHG hGH hcritical 1) = D.rank := by
  rw [(absoluteGhostOneEquiv D H hHG hGH hcritical).finrank_eq]
  simp [Module.finrank_pi_fintype]

def absoluteGhostTwoEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26)
    : AbsoluteGrade D H hHG hGH hcritical 2 ≃ₗ[ℂ] (Fin D.rank → ℂ) :=
  (absoluteGradeEquiv D H hHG hGH hcritical 2).trans (absoluteCoordinateGradeTwo D)

theorem absolute_ghost_2_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26)
    : Module.finrank ℂ (AbsoluteGrade D H hHG hGH hcritical 2) = D.rank := by
  rw [(absoluteGhostTwoEquiv D H hHG hGH hcritical).finrank_eq]
  simp [Module.finrank_pi_fintype]

def absoluteGhostThreeEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26)
    : AbsoluteGrade D H hHG hGH hcritical 3 ≃ₗ[ℂ] ℂ :=
  (absoluteGradeEquiv D H hHG hGH hcritical 3).trans (absoluteCoordinateGradeThree D)

theorem absolute_ghost_3_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26)
    : Module.finrank ℂ (AbsoluteGrade D H hHG hGH hcritical 3) = 1 := by
  rw [(absoluteGhostThreeEquiv D H hHG hGH hcritical).finrank_eq]
  simp [Module.finrank_pi_fintype]

def relativeGhostZeroEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    : RelativeGrade D H hHG hGH 0 ≃ₗ[ℂ] ℂ :=
  (relativeGradeEquiv D H hHG hGH 0).trans (relativeCoordinateGradeZero D)

theorem relative_ghost_0_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    : Module.finrank ℂ (RelativeGrade D H hHG hGH 0) = 1 := by
  rw [(relativeGhostZeroEquiv D H hHG hGH).finrank_eq]
  simp [Module.finrank_pi_fintype]

def relativeGhostOneEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    : RelativeGrade D H hHG hGH 1 ≃ₗ[ℂ] (Fin D.rank → ℂ) :=
  (relativeGradeEquiv D H hHG hGH 1).trans (relativeCoordinateGradeOne D)

theorem relative_ghost_1_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    : Module.finrank ℂ (RelativeGrade D H hHG hGH 1) = D.rank := by
  rw [(relativeGhostOneEquiv D H hHG hGH).finrank_eq]
  simp [Module.finrank_pi_fintype]

def relativeGhostTwoEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    : RelativeGrade D H hHG hGH 2 ≃ₗ[ℂ] ℂ :=
  (relativeGradeEquiv D H hHG hGH 2).trans (relativeCoordinateGradeTwo D)

theorem relative_ghost_2_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    : Module.finrank ℂ (RelativeGrade D H hHG hGH 2) = 1 := by
  rw [(relativeGhostTwoEquiv D H hHG hGH).finrank_eq]
  simp [Module.finrank_pi_fintype]

inductive AbsoluteIndex (D : LatticeData) where
  | v
  | j (axis : Fin D.rank)
  | k (axis : Fin D.rank)
  | w
  deriving DecidableEq, Fintype

inductive RelativeIndex (D : LatticeData) where
  | v
  | j (axis : Fin D.rank)
  | z
  deriving DecidableEq, Fintype

def absoluteNativeIndex (D : LatticeData) : AbsoluteIndex D → NativeIndex D
  | .v => .v
  | .j axis => .j axis
  | .k axis => .k axis
  | .w => .w

def relativeNativeIndex (D : LatticeData) : RelativeIndex D → NativeIndex D
  | .v => .v
  | .j axis => .j axis
  | .z => .z

def absoluteFunctionEquiv (D : LatticeData) :
    AbsoluteCoordinates D ≃ₗ[ℂ] (AbsoluteIndex D → ℂ) where
  toFun coefficient index := match index with
    | .v => coefficient.1
    | .j axis => coefficient.2.1 axis
    | .k axis => coefficient.2.2.1 axis
    | .w => coefficient.2.2.2
  invFun coefficient := (coefficient .v, fun axis => coefficient (.j axis),
    fun axis => coefficient (.k axis), coefficient .w)
  left_inv coefficient := rfl
  right_inv coefficient := by ext index; cases index <;> rfl
  map_add' first second := by ext index; cases index <;> rfl
  map_smul' scalar coefficient := by ext index; cases index <;> rfl

def relativeFunctionEquiv (D : LatticeData) :
    RelativeCoordinates D ≃ₗ[ℂ] (RelativeIndex D → ℂ) where
  toFun coefficient index := match index with
    | .v => coefficient.1
    | .j axis => coefficient.2.1 axis
    | .z => coefficient.2.2
  invFun coefficient := (coefficient .v, fun axis => coefficient (.j axis), coefficient .z)
  left_inv coefficient := rfl
  right_inv coefficient := by ext index; cases index <;> rfl
  map_add' first second := by ext index; cases index <;> rfl
  map_smul' scalar coefficient := by ext index; cases index <;> rfl

def absoluteBasis (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) :
    Module.Basis (AbsoluteIndex D) ℂ (AbsoluteCohomology D H) :=
  (Pi.basisFun ℂ (AbsoluteIndex D)).map
    ((absoluteEquiv D H hHG hGH hcritical).trans (absoluteFunctionEquiv D)).symm

def relativeBasis (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.Basis (RelativeIndex D) ℂ (RelativeCohomology D H hHG hGH) :=
  (Pi.basisFun ℂ (RelativeIndex D)).map
    ((relativeEquiv D H hHG hGH).trans (relativeFunctionEquiv D)).symm

theorem absolute_basis_representative (D : LatticeData) (index : AbsoluteIndex D) :
    absoluteRepresentative D ((absoluteFunctionEquiv D).symm (Pi.single index 1)) =
      native D (absoluteNativeIndex D index) := by
  have coefficient : absoluteEmbed D ((absoluteFunctionEquiv D).symm (Pi.single index 1)) =
      Pi.single (absoluteNativeIndex D index) 1 := by
    ext output
    cases index <;> cases output <;>
      simp [absoluteEmbed, absoluteFunctionEquiv, absoluteNativeIndex, Pi.single_apply, eq_comm]
  change realize D (absoluteEmbed D ((absoluteFunctionEquiv D).symm (Pi.single index 1))) = _
  rw [coefficient, realize_single, one_smul]

theorem relative_basis_representative (D : LatticeData) (index : RelativeIndex D) :
    relativeRepresentative D ((relativeFunctionEquiv D).symm (Pi.single index 1)) =
      native D (relativeNativeIndex D index) := by
  have coefficient : relativeEmbed D ((relativeFunctionEquiv D).symm (Pi.single index 1)) =
      Pi.single (relativeNativeIndex D index) 1 := by
    ext output
    cases index <;> cases output <;>
      simp [relativeEmbed, relativeFunctionEquiv, relativeNativeIndex, Pi.single_apply, eq_comm]
  change realize D (relativeEmbed D ((relativeFunctionEquiv D).symm (Pi.single index 1))) = _
  rw [coefficient, realize_single, one_smul]

theorem absoluteBasis_apply (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (index : AbsoluteIndex D) :
    absoluteBasis D H hHG hGH hcritical index = (Boundaries D H).mkQ
      (absoluteRepresentCycle D H hHG hGH
        ((absoluteFunctionEquiv D).symm (Pi.single index 1))) := by
  simp [absoluteBasis, Pi.basisFun_apply, absoluteEquiv_inverse]

theorem relativeBasis_apply (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (index : RelativeIndex D) :
    relativeBasis D H hHG hGH index = (RelativeBoundaries D H hHG hGH).mkQ
      (relativeRepresentCycle D H hHG hGH
        ((relativeFunctionEquiv D).symm (Pi.single index 1))) := by
  simp [relativeBasis, Pi.basisFun_apply, relativeEquiv, relativeQuotientRepresentative]

theorem absolute_finiteDimensional (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : FiniteDimensional ℂ (AbsoluteCohomology D H) :=
  Module.Finite.of_basis (absoluteBasis D H hHG hGH hcritical)

theorem relative_finiteDimensional (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    FiniteDimensional ℂ (RelativeCohomology D H hHG hGH) :=
  Module.Finite.of_basis (relativeBasis D H hHG hGH)

theorem absolute_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : Module.finrank ℂ (AbsoluteCohomology D H) = 2 * D.rank + 2 := by
  rw [(absoluteEquiv D H hHG hGH hcritical).finrank_eq]
  simp [AbsoluteCoordinates, Module.finrank_prod, Module.finrank_pi_fintype] <;> omega

theorem relative_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    Module.finrank ℂ (RelativeCohomology D H hHG hGH) = D.rank + 2 := by
  rw [(relativeEquiv D H hHG hGH).finrank_eq]
  simp [RelativeCoordinates, Module.finrank_prod, Module.finrank_pi_fintype] <;> omega

theorem full_neutral_finrank (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : Module.finrank ℂ (FullNeutralCohomology D H) = 2 * D.rank + 2 := by
  rw [(fullNeutralEquiv D H hHG hGH hcritical).finrank_eq]
  simp [AbsoluteCoordinates, Module.finrank_prod, Module.finrank_pi_fintype] <;> omega

theorem neutralChargeProjection_basis (D : LatticeData) (input : Support.TensorLabel D) :
    neutralChargeProjection D (Support.stateBasis D input) =
      if input.1.1 = 0 then Support.stateBasis D input else 0 := by
  apply (Support.stateBasis D).repr.injective
  ext output
  rw [neutralChargeProjection_coeff, (Support.stateBasis D).repr_self]
  by_cases equality : input = output
  · subst output
    split_ifs <;> simp [(Support.stateBasis D).repr_self]
  · have different : output ≠ input := Ne.symm equality
    split_ifs <;> simp [(Support.stateBasis D).repr_self,
      Finsupp.single_apply, equality, different]

theorem neutralChargeProjection_commutes_Q (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    (neutralChargeProjection D).comp (Q D H) =
      (Q D H).comp (neutralChargeProjection D) := by
  apply (Support.stateBasis D).ext
  intro input
  change neutralChargeProjection D (Q D H (Support.stateBasis D input)) =
    Q D H (neutralChargeProjection D (Support.stateBasis D input))
  rw [neutralChargeProjection_basis]
  by_cases chosen : input.1.1 = 0
  · rw [if_pos chosen]
    apply (Support.stateBasis D).repr.injective
    ext output
    rw [neutralChargeProjection_coeff]
    by_cases outputChosen : output.1.1 = 0
    · rw [if_pos outputChosen]
    · rw [if_neg outputChosen]
      exact (Image.Q_charge_coeff_zero D H input output
        (by simpa [chosen] using outputChosen)).symm
  · rw [if_neg chosen, map_zero]
    apply (Support.stateBasis D).repr.injective
    ext output
    rw [neutralChargeProjection_coeff, map_zero, Finsupp.zero_apply]
    by_cases outputChosen : output.1.1 = 0
    · rw [if_pos outputChosen]
      exact Image.Q_charge_coeff_zero D H input output
        (by intro equality; exact chosen (equality.symm.trans outputChosen))
    · rw [if_neg outputChosen]

set_option maxRecDepth 4096 in
theorem charge_energy_projection_assembly (D : LatticeData) :
    (neutralChargeProjection D).comp (Energy.P0 D) = Image.jointProjection D := by
  apply (Support.stateBasis D).ext
  intro input
  change neutralChargeProjection D (Energy.energyWeight D
    (fun energy => if energy = 0 then 1 else 0) (Energy.fullBasis D input)) =
    Image.jointProjection D (Support.stateBasis D input)
  rw [Energy.energyWeight_basis, map_smul]
  change (if Energy.totalEnergy D input = 0 then (1 : ℂ) else 0) •
    neutralChargeProjection D (Support.stateBasis D input) =
    Image.jointProjection D (Image.fullBasis D input)
  rw [neutralChargeProjection_basis, Image.jointProjection_basis]
  by_cases chargeZero : input.1.1 = 0 <;>
    by_cases energyZero : Image.totalEnergy D input = 0 <;>
      simp [Image.jointLabels, show Energy.totalEnergy D input = Image.totalEnergy D input from rfl,
        chargeZero, energyZero]
  all_goals rfl

def OriginalCycles (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :=
  LinearMap.ker (Q D H)

def OriginalBoundaries (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Submodule ℂ (OriginalCycles D H) :=
  (LinearMap.range (Q D H)).comap (OriginalCycles D H).subtype

def OriginalCohomology (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :=
  OriginalCycles D H ⧸ OriginalBoundaries D H

attribute [reducible] OriginalCohomology

def originalCycleInclusion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Cycles D H →ₗ[ℂ] OriginalCycles D H :=
  (Cycles D H).subtype.codRestrict (OriginalCycles D H) (fun state => state.property.2)

def absoluteToOriginal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    AbsoluteCohomology D H →ₗ[ℂ] OriginalCohomology D H :=
  (Boundaries D H).liftQ
    ((OriginalBoundaries D H).mkQ.comp (originalCycleInclusion D H)) (by
      intro state boundary
      change (OriginalBoundaries D H).mkQ (originalCycleInclusion D H state) = 0
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact boundary)

theorem absoluteToOriginal_eq_zero_iff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (quotient : AbsoluteCohomology D H) :
    absoluteToOriginal D H quotient = 0 ↔ quotient = 0 := by
  refine Quotient.inductionOn quotient ?_
  intro state
  change (OriginalBoundaries D H).mkQ (originalCycleInclusion D H state) = 0 ↔
    (Boundaries D H).mkQ state = 0
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ,
    ← LinearMap.mem_ker, Submodule.ker_mkQ]
  rfl

theorem absoluteToOriginal_injective (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Function.Injective (absoluteToOriginal D H) := by
  intro first second equality
  apply sub_eq_zero.mp
  apply (absoluteToOriginal_eq_zero_iff D H (first - second)).mp
  rw [map_sub, equality, sub_self]

theorem original_image_in_cycles (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) : LinearMap.range (Q D H) ≤ OriginalCycles D H := by
  rintro state ⟨preimage, rfl⟩
  have square := LinearMap.congr_fun
    (LatticeBcGhostBrstNilpotence.nilpotent D H hHG hGH hcritical) preimage
  simpa [OriginalCycles, Module.End.mul_apply, LinearMap.mem_ker] using square

theorem absolute_coordinate_grade_outside (D : LatticeData) (degree : ℤ)
    (notZero : degree ≠ 0) (notOne : degree ≠ 1)
    (notTwo : degree ≠ 2) (notThree : degree ≠ 3) :
    AbsoluteCoordinateGrade D degree = ⊥ := by
  have differenceNonzero (integer : ℤ) (different : degree ≠ integer) :
      (integer : ℂ) - (degree : ℂ) ≠ 0 := by
    rw [← Int.cast_sub]
    exact Int.cast_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm different))
  ext coefficient
  rw [Submodule.mem_bot]
  constructor
  · intro membership
    obtain ⟨first, second, third, fourth⟩ := (absolute_eigen_iff D degree coefficient).mp membership
    apply Prod.ext
    · exact (mul_eq_zero.mp first).resolve_left (by simpa using differenceNonzero 0 notZero)
    · apply Prod.ext
      · ext axis
        exact (mul_eq_zero.mp (second axis)).resolve_left (by simpa using differenceNonzero 1 notOne)
      · apply Prod.ext
        · ext axis
          exact (mul_eq_zero.mp (third axis)).resolve_left (differenceNonzero 2 notTwo)
        · exact (mul_eq_zero.mp fourth).resolve_left (differenceNonzero 3 notThree)
  · intro vanished
    rw [vanished]
    exact Submodule.zero_mem _

theorem relative_coordinate_grade_outside (D : LatticeData) (degree : ℤ)
    (notZero : degree ≠ 0) (notOne : degree ≠ 1) (notTwo : degree ≠ 2) :
    RelativeCoordinateGrade D degree = ⊥ := by
  have differenceNonzero (integer : ℤ) (different : degree ≠ integer) :
      (integer : ℂ) - (degree : ℂ) ≠ 0 := by
    rw [← Int.cast_sub]
    exact Int.cast_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm different))
  ext coefficient
  rw [Submodule.mem_bot]
  constructor
  · intro membership
    obtain ⟨first, second, third⟩ := (relative_eigen_iff D degree coefficient).mp membership
    apply Prod.ext
    · exact (mul_eq_zero.mp first).resolve_left (by simpa using differenceNonzero 0 notZero)
    · apply Prod.ext
      · ext axis
        exact (mul_eq_zero.mp (second axis)).resolve_left (by simpa using differenceNonzero 1 notOne)
      · exact (mul_eq_zero.mp third).resolve_left (differenceNonzero 2 notTwo)
  · intro vanished
    rw [vanished]
    exact Submodule.zero_mem _

theorem absolute_grade_outside (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hcritical : D.rank = 26) (degree : ℤ)
    (notZero : degree ≠ 0) (notOne : degree ≠ 1)
    (notTwo : degree ≠ 2) (notThree : degree ≠ 3) :
    AbsoluteGrade D H hHG hGH hcritical degree = ⊥ := by
  rw [absoluteGrade_comap,
    absolute_coordinate_grade_outside D degree notZero notOne notTwo notThree]
  ext quotient
  change absoluteEquiv D H hHG hGH hcritical quotient = 0 ↔ quotient = 0
  constructor
  · intro vanished
    apply (absoluteEquiv D H hHG hGH hcritical).injective
    simpa using vanished
  · intro vanished
    rw [vanished, map_zero]

theorem relative_grade_outside (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (degree : ℤ) (notZero : degree ≠ 0) (notOne : degree ≠ 1) (notTwo : degree ≠ 2) :
    RelativeGrade D H hHG hGH degree = ⊥ := by
  rw [relativeGrade_comap, relative_coordinate_grade_outside D degree notZero notOne notTwo]
  ext quotient
  change relativeEquiv D H hHG hGH quotient = 0 ↔ quotient = 0
  constructor
  · intro vanished
    apply (relativeEquiv D H hHG hGH).injective
    simpa using vanished
  · intro vanished
    rw [vanished, map_zero]

end

end D5.S3.VertexAlgebra.LatticeBcGhostNeutralCohomology
