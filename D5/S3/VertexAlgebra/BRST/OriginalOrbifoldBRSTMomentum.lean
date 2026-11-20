/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTMomentum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTMomentum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native hyperbolic momentum grading of the original orbifold BRST descent. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeMassShell
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie

/-! Zero modes of the native hyperbolic currents detect momentum. Their derivation
law grades the original descent, and momentum projections pass through the
relative differential to the physical Lie algebra. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTMomentum

open D5.S3.Quantum.Fermionic
open OriginalOrbifoldCriticalMatter (Matter State Orbifold Hyperbolic b hyperbolicData
  hyperbolic_gram orbifoldVertexAlgebra)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis)
open OriginalOrbifoldRelativeMassShell (fixedMomentum mem_fixedMomentum_iff)
open OriginalOrbifoldBRSTStateField (Y)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTSuperJacobi (homogeneous_borcherds)
open StateFieldResidueReconstruction (epsilon)
open LatticeGeneratingFieldLocality (Charge bilinear unitCharge)
open LatticeFiniteNegativeGeneration (neutralField neutralMode neutralPolynomialMode)

open private fullBasis_apply from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeMassShell
open private left_vacuum_ncoeff from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTensorField
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private mode_add_left of_parity_eigenspaces zero_binomial_sum
  signed_zero_binomial_sum from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTModeDerivation
open private bilinear_unit from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := Charge hyperbolicData
private abbrev mode (a : State) (n : ℤ) (x : State) : State := ((Y a)[[n]]) x

private def opposite (i : Fin hyperbolicData.rank) : Fin hyperbolicData.rank :=
  if i = 0 then 1 else 0

private theorem pairing_opposite (i : Fin hyperbolicData.rank) (p : UCharge) :
    bilinear hyperbolicData (unitCharge hyperbolicData (opposite i)) p = p i := by
  rw [bilinear_unit]
  change (∑ j : Fin 2, hyperbolicData.G (opposite i) j * p j) = p i
  rw [hyperbolic_gram, Fin.sum_univ_two]
  fin_cases i
  · simp [opposite, OrderedHyperbolicExtension.U_one_zero]
  · simp [opposite, OrderedHyperbolicExtension.U_zero_one]

/-- The Heisenberg vacuum state in the null direction dual to momentum coordinate `i`. -/
def momentumCurrent (i : Fin hyperbolicData.rank) : State :=
  (orbifoldVertexAlgebra.vacuum ⊗ₜ[ℂ]
    ((neutralField hyperbolicData (opposite i))[[-1]]) (LatticeAllStateField.vacuum hyperbolicData))
      ⊗ₜ[ℂ] CountableOccupationFock.vacuum

/-- The coordinate operator is the zero mode of the actual lifted Heisenberg state. -/
def momentumZeroMode (i : Fin hyperbolicData.rank) : Module.End ℂ State :=
  (Y (momentumCurrent i))[[0]]

private theorem momentumZeroMode_tensor (i : Fin hyperbolicData.rank) :
    momentumZeroMode i = TensorProduct.map
      ((neutralMode hyperbolicData (opposite i) 0).lTensor Orbifold) LinearMap.id := by
  rw [momentumZeroMode, momentumCurrent, OriginalOrbifoldBRSTStateField.right_vacuum_ncoeff]
  rw [left_vacuum_ncoeff]
  change TensorProduct.map
    (((LatticeAllStateField.Y hyperbolicData
      (((neutralField hyperbolicData (opposite i))[[-1]])
        (LatticeAllStateField.vacuum hyperbolicData)))[[0]]).lTensor Orbifold)
    LinearMap.id = _
  rw [LatticeAllStateField.stateField_current, LatticeSugawaraCurrents.neutralField_ncoeff]

private theorem momentumCurrent_even (i : Fin hyperbolicData.rank) :
    parity (momentumCurrent i) = (-1 : ℂ) ^ 0 • momentumCurrent i := by
  simp only [momentumCurrent, parity, TensorProduct.map_tmul, LinearMap.id_apply,
    CountableOccupationFock.vacuum, parity_ket, Finset.card_empty, pow_zero, one_smul]

private theorem momentumZeroMode_basis (i : Fin hyperbolicData.rank) (j : FullLabel) :
    momentumZeroMode i (fullBasis j) = (j.2.1.1 i : ℂ) • fullBasis j := by
  rw [momentumZeroMode_tensor, fullBasis_apply]
  simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply,
    LatticeSugawaraCurrents.neutralMode_single, neutralPolynomialMode, lt_irrefl,
    ite_false, ite_true, LinearMap.smul_apply, pairing_opposite, ← Finsupp.smul_single,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul]

/-- In the full tensor basis each current reads the indicated native momentum coordinate. -/
theorem momentumZeroMode_coeff (i : Fin hyperbolicData.rank) (x : State) (j : FullLabel) :
    fullBasis.repr (momentumZeroMode i x) j = (j.2.1.1 i : ℂ) * fullBasis.repr x j := by
  classical
  let coeff : State →ₗ[ℂ] ℂ := fullBasis.coord j
  have diagonal : coeff.comp (momentumZeroMode i) = (j.2.1.1 i : ℂ) • coeff := by
    apply fullBasis.ext
    intro k
    rw [LinearMap.comp_apply, momentumZeroMode_basis, map_smul, LinearMap.smul_apply]
    by_cases hk : k = j
    · subst k
      rfl
    · have hz : coeff (fullBasis k) = 0 := by
        simp [coeff, Module.Basis.repr_self, hk]
      simp [hz]
  exact LinearMap.congr_fun diagonal x

/-- Native fixed momentum is precisely the simultaneous eigenspace of its two zero modes. -/
theorem mem_fixedMomentum_iff_zero_modes (p : UCharge) (x : State) :
    x ∈ fixedMomentum p ↔ ∀ i : Fin hyperbolicData.rank, momentumZeroMode i x = (p i : ℂ) • x := by
  rw [mem_fixedMomentum_iff]
  constructor
  · intro hx i
    apply fullBasis.repr.injective
    ext j
    rw [momentumZeroMode_coeff, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hj : j.2.1.1 = p
    · rw [hj]
    · rw [hx j hj, mul_zero, mul_zero]
  · intro hx j hj
    by_contra hc
    apply hj
    funext i
    have h := congrArg (fun y : State => fullBasis.repr y j) (hx i)
    rw [momentumZeroMode_coeff, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    exact Int.cast_injective (mul_right_cancel₀ hc h)

/-- The native even current acts as a derivation of every integer mode. -/
theorem momentumZeroMode_mode (i : Fin hyperbolicData.rank) (a x : State) (n : ℤ) :
    momentumZeroMode i (mode a n x) =
      mode (momentumZeroMode i a) n x + mode a n (momentumZeroMode i x) := by
  apply of_parity_eigenspaces (fun v =>
    momentumZeroMode i (mode v n x) =
      mode (momentumZeroMode i v) n x + mode v n (momentumZeroMode i x)) _ _ a
  · intro v w hv hw
    simp only [mode_add_left, map_add, hv, hw]
    abel
  · intro v k hv
    have law := (homogeneous_borcherds (momentumCurrent i) v x 0 k
      (momentumCurrent_even i) hv 0 n 0).2.2.2
    dsimp only at law
    simp only [zero_binomial_sum, signed_zero_binomial_sum, Nat.cast_zero,
      zero_add, add_zero, sub_zero, epsilon, zpow_zero, zero_mul, pow_zero, one_mul,
      one_smul] at law
    exact (eq_sub_iff_add_eq.mp law).symm

/-- The integer modes of the original field add the actual hyperbolic momenta. -/
theorem mode_mem_fixedMomentum {p q : UCharge} {a x : State}
    (ha : a ∈ fixedMomentum p) (hx : x ∈ fixedMomentum q) (n : ℤ) :
    ((Y a)[[n]]) x ∈ fixedMomentum (p + q) := by
  apply (mem_fixedMomentum_iff_zero_modes _ _).mpr
  intro i
  rw [momentumZeroMode_mode, (mem_fixedMomentum_iff_zero_modes p a).mp ha i,
    (mem_fixedMomentum_iff_zero_modes q x).mp hx i]
  simp only [mode, map_smul, Pi.smul_apply, LinearMap.smul_apply,
    Pi.add_apply, Int.cast_add, add_smul]

private theorem momentumZeroMode_b (i : Fin hyperbolicData.rank) (r : ℤ) (x : State) :
    momentumZeroMode i (b r x) = b r (momentumZeroMode i x) := by
  have h : (momentumZeroMode i).comp (b r) = (b r).comp (momentumZeroMode i) := by
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.comp_apply, momentumZeroMode_tensor, b, VirasoroBRST.ghostB,
      BcGhostChargeTensor.B, BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul,
      LinearMap.id_apply]
  exact LinearMap.congr_fun h x

/-- The native ghost operators, including the descent antighost, preserve momentum. -/
theorem b_mem_fixedMomentum (r : ℤ) {p : UCharge} {x : State} (hx : x ∈ fixedMomentum p) :
    b r x ∈ fixedMomentum p := by
  apply (mem_fixedMomentum_iff_zero_modes _ _).mpr
  intro i
  rw [momentumZeroMode_b, (mem_fixedMomentum_iff_zero_modes p x).mp hx i, map_smul]

open OriginalOrbifoldBRSTDescent (descent)

/-- Native descent adds momenta on the original state space. -/
theorem descent_mem_fixedMomentum {p q : UCharge} {x y : State}
    (hx : x ∈ fixedMomentum p) (hy : y ∈ fixedMomentum q) :
    descent x y ∈ fixedMomentum (p + q) :=
  mode_mem_fixedMomentum (b_mem_fixedMomentum (-1) hx) hy 0

section Quotient

open OriginalOrbifoldCriticalMatter (Q)
open OriginalOrbifoldBRSTZeroEnergy (totalL0 totalL0_basis)
open OriginalOrbifoldRelativeMassShell (Q_mem_fixedMomentum)
open OriginalOrbifoldBRSTDescent (relativeStates relativeDifferential relativeDifferential_square
  relativeCycles relativeBoundaries RelativeCohomology cycleDescent cohomologyDescent
  cohomologyDescent_mk)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne N grade cohomologyNumber cohomologyNumber_mk
  degreeOne_bracket)
open private number_basis from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie
open private cycleMap cohomologyMap from D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

private def momentumPart (p : UCharge) : Module.End ℂ State :=
  fullBasis.constr ℂ (fun j => if j.2.1.1 = p then fullBasis j else 0)

private theorem momentumPart_basis (p : UCharge) (j : FullLabel) :
    momentumPart p (fullBasis j) = if j.2.1.1 = p then fullBasis j else 0 :=
  fullBasis.constr_basis ℂ _ j

private theorem momentumPart_coeff (p : UCharge) (x : State) (i : FullLabel) :
    fullBasis.repr (momentumPart p x) i =
      if i.2.1.1 = p then fullBasis.repr x i else 0 := by
  classical
  let coeff : State →ₗ[ℂ] ℂ := fullBasis.coord i
  have h : coeff.comp (momentumPart p) = if i.2.1.1 = p then coeff else 0 := by
    apply fullBasis.ext
    intro j
    rw [LinearMap.comp_apply, momentumPart_basis]
    by_cases hji : j = i
    · subst j
      by_cases hi : i.2.1.1 = p <;> simp [hi]
    · have hz : coeff (fullBasis j) = 0 := by simp [coeff, Module.Basis.repr_self, hji]
      by_cases hi : i.2.1.1 = p <;> by_cases hj : j.2.1.1 = p <;> simp [hi, hj, hz]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i.2.1.1 = p <;> simpa only [hi, ite_true, ite_false,
    LinearMap.comp_apply, LinearMap.zero_apply, coeff, Module.Basis.coord_apply] using hx

private theorem momentumPart_mem (p : UCharge) (x : State) :
    momentumPart p x ∈ fixedMomentum p := by
  rw [mem_fixedMomentum_iff]
  intro i hi
  rw [momentumPart_coeff, ite_eq_right hi]

private theorem momentumPart_of_mem {p : UCharge} {x : State} (hx : x ∈ fixedMomentum p) :
    momentumPart p x = x := by
  apply fullBasis.repr.injective
  ext i
  rw [momentumPart_coeff]
  by_cases hi : i.2.1.1 = p
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, (mem_fixedMomentum_iff p x).mp hx i hi]

private theorem momentumPart_of_mem_ne {p q : UCharge} {x : State}
    (hx : x ∈ fixedMomentum q) (hpq : p ≠ q) : momentumPart p x = 0 := by
  apply fullBasis.repr.injective
  ext i
  change fullBasis.coord i (momentumPart p x) = fullBasis.coord i 0
  rw [(fullBasis.coord i).map_zero, Module.Basis.coord_apply, momentumPart_coeff]
  split_ifs with hi
  · exact (mem_fixedMomentum_iff q x).mp hx i (hi.trans_ne hpq)
  · rfl

private theorem momentumPart_commutes (p : UCharge) (T : Module.End ℂ State)
    (hT : ∀ q x, x ∈ fixedMomentum q → T x ∈ fixedMomentum q) :
    (momentumPart p).comp T = T.comp (momentumPart p) := by
  classical
  apply fullBasis.ext
  intro j
  have hj : fullBasis j ∈ fixedMomentum j.2.1.1 := by
    apply (mem_fixedMomentum_iff _ _).mpr
    intro i hi
    have hji : j ≠ i := fun h => hi (h ▸ rfl)
    simp [Module.Basis.repr_self, hji]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, momentumPart_basis]
  by_cases hp : j.2.1.1 = p
  · rw [ite_eq_left hp, momentumPart_of_mem (hp ▸ hT _ _ hj)]
  · rw [ite_eq_right hp, map_zero, momentumPart_of_mem_ne (hT _ _ hj) (Ne.symm hp)]

private theorem momentumPart_commutes_diagonal (p : UCharge) (T : Module.End ℂ State)
    (weight : FullLabel → ℂ) (hT : ∀ j, T (fullBasis j) = weight j • fullBasis j) :
    (momentumPart p).comp T = T.comp (momentumPart p) := by
  apply fullBasis.ext
  intro j
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hT j, map_smul, momentumPart_basis]
  split_ifs <;> simp [hT]

private def relativePart (p : UCharge) : Module.End ℂ relativeStates :=
  (momentumPart p).restrict (by
    intro x hx
    change b 0 x = 0 ∧ totalL0 x = 0 at hx
    change b 0 (momentumPart p x) = 0 ∧ totalL0 (momentumPart p x) = 0
    have hb := LinearMap.congr_fun
      (momentumPart_commutes p (b 0) (fun _ _ h => b_mem_fixedMomentum 0 h)) x
    have hL := LinearMap.congr_fun (momentumPart_commutes_diagonal p totalL0 _
      totalL0_basis) x
    simp only [LinearMap.comp_apply, hx.1, hx.2, map_zero] at hb hL
    exact ⟨hb.symm, hL.symm⟩)

private theorem relativePart_chain (p : UCharge) :
    (relativePart p).comp relativeDifferential = relativeDifferential.comp (relativePart p) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun
    (momentumPart_commutes p Q (fun q _ h => Q_mem_fixedMomentum q h)) (x : State)

private def cyclePart (p : UCharge) : Module.End ℂ relativeCycles :=
  cycleMap relativeDifferential relativeDifferential (relativePart p) (relativePart_chain p)

private def cohomologyPart (p : UCharge) : Module.End ℂ RelativeCohomology :=
  cohomologyMap relativeDifferential relativeDifferential
    relativeDifferential_square relativeDifferential_square (relativePart p) (relativePart_chain p)

private theorem cohomologyPart_mk (p : UCharge) (z : relativeCycles) :
    cohomologyPart p (relativeBoundaries.mkQ z) = relativeBoundaries.mkQ (cyclePart p z) := rfl

/-- The momentum component of the actual relative quotient is the image of the native cycles
at that momentum. -/
def relativeMomentum (p : UCharge) : Submodule ℂ RelativeCohomology :=
  ((fixedMomentum p).comap (relativeStates.subtype.comp relativeCycles.subtype)).map
    relativeBoundaries.mkQ

set_option maxHeartbeats 800000 in
-- Unfolding the submodule image compares the nested cycle and quotient carriers.
/-- A relative class lies in a momentum component exactly when it has a cycle there. -/
theorem mem_relativeMomentum_iff (p : UCharge) (x : RelativeCohomology) :
    x ∈ relativeMomentum p ↔
      ∃ z : relativeCycles, relativeBoundaries.mkQ z = x ∧ (z.1 : State) ∈ fixedMomentum p := by
  rw [relativeMomentum, Submodule.mem_map]
  exact exists_congr (fun _ => and_comm)

private theorem mk_cyclePart_mem (p : UCharge) (z : relativeCycles) :
    relativeBoundaries.mkQ (cyclePart p z) ∈ relativeMomentum p :=
  (mem_relativeMomentum_iff _ _).mpr ⟨_, rfl, momentumPart_mem p (z.1 : State)⟩

private theorem cohomologyPart_of_mem {p : UCharge} {x : RelativeCohomology}
    (hx : x ∈ relativeMomentum p) : cohomologyPart p x = x := by
  obtain ⟨z, rfl, hz⟩ := (mem_relativeMomentum_iff _ _).mp hx
  rw [cohomologyPart_mk]
  exact congrArg relativeBoundaries.mkQ (Subtype.ext (Subtype.ext (momentumPart_of_mem hz)))

private theorem cohomologyPart_of_mem_ne {p q : UCharge} {x : RelativeCohomology}
    (hx : x ∈ relativeMomentum q) (hpq : p ≠ q) : cohomologyPart p x = 0 := by
  obtain ⟨z, rfl, hz⟩ := (mem_relativeMomentum_iff _ _).mp hx
  rw [cohomologyPart_mk]
  have h : cyclePart p z = 0 := Subtype.ext (Subtype.ext (momentumPart_of_mem_ne hz hpq))
  rw [h, map_zero]

set_option maxHeartbeats 800000 in
-- Transporting the representative equations elaborates through the quotient operation.
/-- Relative descent on the native quotient adds the momenta of its two classes. -/
theorem cohomologyDescent_mem_relativeMomentum {p q : UCharge} {x y : RelativeCohomology}
    (hx : x ∈ relativeMomentum p) (hy : y ∈ relativeMomentum q) :
    cohomologyDescent x y ∈ relativeMomentum (p + q) := by
  obtain ⟨u, hu, hup⟩ := (mem_relativeMomentum_iff p x).mp hx
  obtain ⟨v, hv, hvq⟩ := (mem_relativeMomentum_iff q y).mp hy
  rw [← hu, ← hv, cohomologyDescent_mk]
  refine (mem_relativeMomentum_iff _ _).mpr ⟨cycleDescent u v, rfl, ?_⟩
  exact descent_mem_fixedMomentum hup hvq

/-- The physical momentum component lies in the actual ghost-number-one Lie algebra. -/
def physicalMomentum (p : UCharge) : Submodule ℂ DegreeOne :=
  (relativeMomentum p).comap (grade 1).subtype

/-- The physical Lie bracket adds native hyperbolic momenta. -/
theorem degreeOne_bracket_mem_physicalMomentum {p q : UCharge} {x y : DegreeOne}
    (hx : x ∈ physicalMomentum p) (hy : y ∈ physicalMomentum q) :
    ⁅x, y⁆ ∈ physicalMomentum (p + q) := by
  change (↑⁅x, y⁆ : RelativeCohomology) ∈ relativeMomentum (p + q)
  rw [degreeOne_bracket]
  exact cohomologyDescent_mem_relativeMomentum hx hy

private theorem relativeMomentum_independent : iSupIndep relativeMomentum := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
  intro s v hv hsum p hp
  have h := congrArg (cohomologyPart p) hsum
  rw [map_sum, map_zero, Finset.sum_eq_single_of_mem p hp] at h
  · exact (cohomologyPart_of_mem (hv p hp)).symm.trans h
  · intro q hq hpq
    exact cohomologyPart_of_mem_ne (hv q hq) hpq.symm

set_option maxHeartbeats 800000 in
-- The subtype inclusion compares the two finite sums on the relative quotient.
private theorem physicalMomentum_independent : iSupIndep physicalMomentum := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
  intro s v hv hsum p hp
  have h := congrArg (grade 1).subtype hsum
  rw [map_sum, map_zero] at h
  exact (grade 1).subtype_injective
    ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
      relativeMomentum_independent s _ hv h p hp)

private def momentumSupport (x : State) : Finset UCharge :=
  (fullBasis.repr x).support.image (fun j => j.2.1.1)

private theorem sum_momentumPart (x : State) :
    ∑ p ∈ momentumSupport x, momentumPart p x = x := by
  classical
  apply fullBasis.repr.injective
  ext j
  change fullBasis.coord j (∑ p ∈ momentumSupport x, momentumPart p x) = _
  rw [map_sum]
  simp only [Module.Basis.coord_apply, momentumPart_coeff]
  by_cases hj : j ∈ (fullBasis.repr x).support
  · have hp : j.2.1.1 ∈ momentumSupport x := Finset.mem_image.mpr ⟨j, hj, rfl⟩
    rw [Finset.sum_eq_single_of_mem j.2.1.1 hp]
    · rw [ite_eq_left rfl]
    · intro q _ hq
      rw [ite_eq_right hq.symm]
  · simp [Finsupp.notMem_support_iff.mp hj]

private theorem sum_cyclePart (z : relativeCycles) :
    ∑ p ∈ momentumSupport (z.1 : State), cyclePart p z = z := by
  let incl : relativeCycles →ₗ[ℂ] State := relativeStates.subtype.comp relativeCycles.subtype
  apply (relativeStates.subtype_injective.comp relativeCycles.subtype_injective)
  change incl (∑ p ∈ momentumSupport (z.1 : State), cyclePart p z) = (z.1 : State)
  rw [map_sum]
  exact sum_momentumPart (z.1 : State)

/-- The actual relative quotient is the algebraic direct sum of its momentum components. -/
theorem relativeMomentum_grading : DirectSum.IsInternal relativeMomentum := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top relativeMomentum_independent
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := relativeBoundaries.mkQ_surjective x
  rw [← sum_cyclePart z, map_sum]
  apply Submodule.sum_mem
  intro p _
  exact le_iSup relativeMomentum p (mk_cyclePart_mem p z)

private theorem cyclePart_number_one (p : UCharge) (z : relativeCycles)
    (hz : N (z.1 : State) = (z.1 : State)) :
    N ((cyclePart p z).1 : State) = ((cyclePart p z).1 : State) := by
  have h := LinearMap.congr_fun (momentumPart_commutes_diagonal p N _ number_basis)
    (z.1 : State)
  change N (momentumPart p (z.1 : State)) = momentumPart p (z.1 : State)
  simpa only [LinearMap.comp_apply, hz] using h.symm

set_option maxHeartbeats 800000 in
-- Ghost number on a cycle reduces through the two relative subtypes.
private theorem class_mem_grade_one (z : relativeCycles)
    (hz : N (z.1 : State) = (z.1 : State)) : relativeBoundaries.mkQ z ∈ grade 1 := by
  apply Module.End.mem_eigenspace_iff.mpr
  have h : OriginalOrbifoldBRSTPhysicalLie.cycleNumber z = z := Subtype.ext (Subtype.ext hz)
  let cl : relativeCycles →ₗ[ℂ] RelativeCohomology := relativeBoundaries.mkQ
  change cohomologyNumber (cl z) = ((1 : ℤ) : ℂ) • cl z
  calc
    cohomologyNumber (cl z) = cl (OriginalOrbifoldBRSTPhysicalLie.cycleNumber z) :=
      cohomologyNumber_mk z
    _ = cl z := congrArg cl h
    _ = ((1 : ℤ) : ℂ) • cl z := by simp only [Int.cast_one, one_smul]

/-- A physical momentum class admits a relative cycle with the specified momentum and
ghost number one. -/
theorem mem_physicalMomentum_iff (p : UCharge) (x : DegreeOne) :
    x ∈ physicalMomentum p ↔ ∃ z : relativeCycles,
      relativeBoundaries.mkQ z = (x : RelativeCohomology) ∧
        (z.1 : State) ∈ fixedMomentum p ∧ N (z.1 : State) = (z.1 : State) := by
  constructor
  · intro hx
    obtain ⟨z, hz, hn⟩ := OriginalOrbifoldBRSTPhysicalLie.homogeneous_cycle_lift
      1 (x : RelativeCohomology) x.property
    refine ⟨cyclePart p z, ?_, momentumPart_mem p _, cyclePart_number_one p z ?_⟩
    · rw [← cohomologyPart_mk, hz]
      exact cohomologyPart_of_mem hx
    · simpa only [Int.cast_one, one_smul] using hn
  · rintro ⟨z, hz, hp, _⟩
    exact (mem_relativeMomentum_iff _ _).mpr ⟨z, hz, hp⟩

private def physicalClassPart (p : UCharge) (z : relativeCycles)
    (hz : N (z.1 : State) = (z.1 : State)) : DegreeOne :=
  ⟨relativeBoundaries.mkQ (cyclePart p z), class_mem_grade_one _ (cyclePart_number_one p z hz)⟩

set_option maxHeartbeats 800000 in
-- The finite decomposition passes through the cycle quotient and the degree-one subtype.
/-- The momentum components form an algebraic direct-sum grading of the physical Lie algebra. -/
theorem physicalMomentum_grading : DirectSum.IsInternal physicalMomentum := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top physicalMomentum_independent
  apply top_unique
  intro x _
  obtain ⟨z, hz, hn⟩ := OriginalOrbifoldBRSTPhysicalLie.homogeneous_cycle_lift
    1 (x : RelativeCohomology) x.property
  have hn' : N (z.1 : State) = (z.1 : State) := by
    simpa only [Int.cast_one, one_smul] using hn
  let S := momentumSupport (z.1 : State)
  let part : UCharge → DegreeOne := fun p => physicalClassPart p z hn'
  let incl : DegreeOne →ₗ[ℂ] RelativeCohomology := (grade 1).subtype
  let cl : relativeCycles →ₗ[ℂ] RelativeCohomology := relativeBoundaries.mkQ
  have hsum : ∑ p ∈ S, part p = x := by
    apply (grade 1).subtype_injective
    calc
      incl (∑ p ∈ S, part p) = ∑ p ∈ S, incl (part p) := map_sum incl part S
      _ = cl (∑ p ∈ S, cyclePart p z) := (map_sum cl (fun p => cyclePart p z) S).symm
      _ = cl z := congrArg cl (sum_cyclePart z)
      _ = incl x := hz
  have hmem : (∑ p ∈ S, part p) ∈ ⨆ p, physicalMomentum p := by
    apply Submodule.sum_mem
    intro p _
    exact le_iSup physicalMomentum p (mk_cyclePart_mem p z)
  exact hsum ▸ hmem

end Quotient

#print axioms momentumZeroMode_coeff
#print axioms mem_fixedMomentum_iff_zero_modes
#print axioms momentumZeroMode_mode
#print axioms mode_mem_fixedMomentum
#print axioms b_mem_fixedMomentum
#print axioms descent_mem_fixedMomentum
#print axioms mem_relativeMomentum_iff
#print axioms cohomologyDescent_mem_relativeMomentum
#print axioms relativeMomentum_grading
#print axioms mem_physicalMomentum_iff
#print axioms degreeOne_bracket_mem_physicalMomentum
#print axioms physicalMomentum_grading

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTMomentum
