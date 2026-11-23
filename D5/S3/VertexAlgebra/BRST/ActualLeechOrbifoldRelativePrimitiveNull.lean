/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativePrimitiveNull
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativePrimitiveNull
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual relative shell at primitive null momentum in the Leech orbifold string. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLowWeights
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo

/-! The relative shell on the original orbifold, plane and ghost tensor factors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativePrimitiveNull

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (Orbifold leechUnit)
open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane hyperbolicMatter)
open ActualLeechOrbifoldBRST (ComplexState Q E b0)
open ActualLeechOrbifoldRelativeNormTwo (N)
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open LatticeSugawaraVirasoro
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open BcGhostRelativeEnergy (relativeEnergy relativeEnergy_nonneg)
open TwistedGround.Orbifold

open private coordinates coordinates_tmul coordinates_separate fixedProjection twistedProjection
  matter_mode_tmul plane_energy_coordinate
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeNormTwo
open private mode_vacuum from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLowWeights
open private plane_inverse from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private Q_commutes_energy from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
open private annihilate_coefficient from D5.S3.Quantum.Fermionic.CountableOccupationFock

/-- The first primitive null vector in the ordered hyperbolic basis. -/
def momentum : Charge hyperbolicPlane := unitCharge hyperbolicPlane (0 : Fin 2)

private abbrev Plane := Carrier hyperbolicPlane

private def chargeProjection (p : Charge hyperbolicPlane) : Module.End ℂ Plane :=
  (Finsupp.lsingle p).comp (Finsupp.lapply p)

private def matterProjection (p : Charge hyperbolicPlane) : Module.End ℂ Matter :=
  TensorProduct.map LinearMap.id (chargeProjection p)

/-- Projection onto a chosen plane charge on the actual three-factor carrier. -/
def projectionAt (p : Charge hyperbolicPlane) : Module.End ℂ ComplexState :=
  TensorProduct.map (matterProjection p) LinearMap.id

private def momentumDifference : Module.End ℂ ComplexState where
  toFun x := projectionAt momentum x - x
  map_add' x y := by
    rw [map_add]
    exact add_sub_add_comm (projectionAt momentum x) (projectionAt momentum y) x y
  map_smul' a x := by
    rw [map_smul]
    exact (smul_sub a (projectionAt momentum x) x).symm

/-- Fixed charge, zero total energy, and zero action of the native b₀. -/
def C : Submodule ℂ ComplexState :=
  LinearMap.ker momentumDifference ⊓ LinearMap.ker E ⊓ LinearMap.ker b0

private theorem mem_C (x : ComplexState) :
    x ∈ C ↔ projectionAt momentum x = x ∧ E x = 0 ∧ b0 x = 0 := by
  simp only [C, momentumDifference, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.coe_mk, AddHom.coe_mk, sub_eq_zero, and_assoc]

private theorem plane_mode_commutes_projection (p : Charge hyperbolicPlane) (n : ℤ) :
    (chargeProjection p).comp (hyperbolicMatter.mode n) =
      (hyperbolicMatter.mode n).comp (chargeProjection p) := by
  classical
  apply Finsupp.lhom_ext
  intro a u
  change chargeProjection p (hyperbolicMatter.mode n (Finsupp.single a u)) =
    hyperbolicMatter.mode n (chargeProjection p (Finsupp.single a u))
  have action (z : Oscillator hyperbolicPlane) :
      hyperbolicMatter.mode n (Finsupp.single a z) =
        Finsupp.single a (sectorSugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) a n z) :=
    sugawaraMode_single_sector hyperbolicPlane _ a n z
  rw [action]
  by_cases h : a = p
  · subst a
    simp [chargeProjection, action]
  · simp [chargeProjection, Ne.symm h]

private theorem matter_mode_commutes_projection (p : Charge hyperbolicPlane) (n : ℤ) :
    (matterProjection p).comp (matter.mode n) = (matter.mode n).comp (matterProjection p) := by
  apply TensorProduct.ext'
  intro v u
  have h := LinearMap.congr_fun (plane_mode_commutes_projection p n) u
  simp only [LinearMap.comp_apply] at h
  simp only [LinearMap.comp_apply, matter_mode_tmul, matterProjection, map_add,
    TensorProduct.map_tmul, LinearMap.id_apply, h]

/-- The original BRST charge preserves every plane momentum. -/
theorem projectionAt_Q (p : Charge hyperbolicPlane) (x : ComplexState) :
    projectionAt p (Q x) = Q (projectionAt p x) := by
  have hs (n : ℤ) :
      (projectionAt p).comp (VirasoroBRST.summand matter n) =
        (VirasoroBRST.summand matter n).comp (projectionAt p) := by
    apply TensorProduct.ext'
    intro m g
    have h := LinearMap.congr_fun (matter_mode_commutes_projection p n) m
    simp only [LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, projectionAt, VirasoroBRST.summand,
      TensorProduct.map_tmul, LinearMap.id_apply, h]
  have hg : (projectionAt p).comp (VirasoroBRST.ghostCharge matter) =
      (VirasoroBRST.ghostCharge matter).comp (projectionAt p) := by
    apply TensorProduct.ext'
    intro m g
    rfl
  change projectionAt p
      ((∑ᶠ n : ℤ, VirasoroBRST.summand matter n x) + VirasoroBRST.ghostCharge matter x) =
    (∑ᶠ n : ℤ, VirasoroBRST.summand matter n (projectionAt p x)) +
      VirasoroBRST.ghostCharge matter (projectionAt p x)
  have hgx := LinearMap.congr_fun hg x
  simp only [LinearMap.comp_apply] at hgx
  rw [map_add, hgx]
  congr 1
  calc
    _ = ∑ᶠ n : ℤ, projectionAt p (VirasoroBRST.summand matter n x) :=
      (projectionAt p).toAddMonoidHom.map_finsum (VirasoroBRST.summand_finite matter x)
    _ = _ := finsum_congr (fun n => by
      simpa only [LinearMap.comp_apply] using LinearMap.congr_fun (hs n) x)

private theorem Q_mem_C {x : ComplexState} (hx : x ∈ C) : Q x ∈ C := by
  obtain ⟨hp, he, hb⟩ := (mem_C x).mp hx
  refine (mem_C _).mpr ⟨by rw [projectionAt_Q, hp], ?_, ?_⟩
  · have h : Q (E x) = E (Q x) := LinearMap.congr_fun Q_commutes_energy x
    rw [he, map_zero] at h
    exact h.symm
  · have h : Q (b0 x) + b0 (Q x) = E x :=
      LinearMap.congr_fun (VirasoroBRST.Q_ward_b matter 0) x
    simpa only [he, hb, map_zero, zero_add] using h

private def planeCoord (l : Label hyperbolicPlane) : Plane →ₗ[ℂ] ℂ :=
  (carrierBasis hyperbolicPlane).coord l

/-- The orbifold-valued coefficient at a plane monomial and a ghost occupation. -/
private def slice (l : Label hyperbolicPlane) (S : Finset ℕ) : ComplexState →ₗ[ℂ] Orbifold :=
  ((TensorProduct.rid ℂ Orbifold).toLinearMap.comp
      (TensorProduct.map LinearMap.id (Finsupp.lapply S))).comp
    (TensorProduct.map
      ((TensorProduct.rid ℂ Orbifold).toLinearMap.comp
        (TensorProduct.map LinearMap.id (planeCoord l)))
      LinearMap.id)

private theorem slice_tmul (l : Label hyperbolicPlane) (S : Finset ℕ)
    (v : Orbifold) (u : Plane) (g : Fock) :
    slice l S ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] g) =
      (carrierCoeffEquiv hyperbolicPlane u l * g S) • v := by
  simp only [slice, planeCoord, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul,
    Module.Basis.coord_apply, Finsupp.lapply_apply, smul_smul]
  rw [mul_comm]
  rfl

private theorem coordinate_slice {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (f : Orbifold →ₗ[ℂ] V)
    (i : ι) (l : Label hyperbolicPlane) (S : Finset ℕ) (x : ComplexState) :
    coordinates b f i l S x = b.repr (f (slice l S x)) i := by
  induction x using TensorProduct.inductionOn with
  | tmul y g =>
    induction y using TensorProduct.inductionOn with
    | tmul v u =>
      rw [coordinates_tmul, slice_tmul, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
      ring
    | add y z hy hz => simp only [TensorProduct.add_tmul, map_add, Finsupp.add_apply, hy, hz]
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]

private theorem slice_ext {x y : ComplexState}
    (h : ∀ l S, slice l S x = slice l S y) : x = y := by
  apply sub_eq_zero.mp
  apply coordinates_separate <;>
    intro i l S <;>
    rw [coordinate_slice, map_sub, h, sub_self, map_zero, map_zero, Finsupp.zero_apply]

private theorem slice_energy (l : Label hyperbolicPlane) (S : Finset ℕ) (x : ComplexState) :
    slice l S (E x) = ActualLeechOrbifoldMatter.mode 0 (slice l S x) +
      ((energy hyperbolicPlane l + BcGhostRelativeEnergy.energy S : ℤ) : ℂ) • slice l S x := by
  induction x using TensorProduct.inductionOn with
  | tmul y g =>
    induction y using TensorProduct.inductionOn with
    | tmul v u =>
      change slice l S ((matter.mode 0 (v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] g) +
        ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] BcGhostVirasoro.L 0 g)) = _
      rw [matter_mode_tmul, TensorProduct.add_tmul]
      simp only [map_add, slice_tmul, plane_energy_coordinate,
        BcGhostRelativeEnergy.L_zero_coefficient, map_smul, Int.cast_add, smul_smul]
      module
    | add y z hy hz =>
      simp only [TensorProduct.add_tmul, map_add, hy, hz, smul_add]
      apply add_add_add_comm
  | add y z hy hz =>
    simp only [map_add, hy, hz, smul_add]
    apply add_add_add_comm

private theorem slice_projection (p : Charge hyperbolicPlane) (l : Label hyperbolicPlane)
    (S : Finset ℕ) (x : ComplexState) :
    slice l S (projectionAt p x) =
      (if l.1 = p then (1 : ℂ) else 0) • slice l S x := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul y g =>
    induction y using TensorProduct.inductionOn with
    | tmul v u =>
      change slice l S ((v ⊗ₜ[ℂ] chargeProjection p u) ⊗ₜ[ℂ] g) = _
      simp only [slice_tmul]
      change (((Finsupp.single p (u p) : Plane) l.1).coeff l.2 * g S) • v =
        (if l.1 = p then (1 : ℂ) else 0) • (((u l.1).coeff l.2 * g S) • v)
      by_cases h : l.1 = p <;> simp [h]
    | add y z hy hz => simp only [TensorProduct.add_tmul, map_add, hy, hz, smul_add]
  | add y z hy hz => simp only [map_add, hy, hz, smul_add]

private theorem slice_b0 (l : Label hyperbolicPlane) (S : Finset ℕ) (hS : 3 ∈ S)
    (x : ComplexState) :
    slice l (S.erase 3) (b0 x) = CountableOccupationFock.phase 3 S • slice l S x := by
  induction x using TensorProduct.inductionOn with
  | tmul y g =>
    induction y using TensorProduct.inductionOn with
    | tmul v u =>
      change slice l (S.erase 3)
          ((v ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] CountableOccupationFock.annihilate 3 g) = _
      rw [slice_tmul, slice_tmul, annihilate_coefficient _ _ _ hS, smul_smul]
      ring_nf
    | add y z hy hz => simp only [TensorProduct.add_tmul, map_add, hy, hz, smul_add]
  | add y z hy hz => simp only [map_add, hy, hz, smul_add]

private theorem chargeEnergy_momentum : chargeEnergy hyperbolicPlane momentum = 0 := by
  change (∑ i : Fin 2, ∑ j : Fin 2,
    (if i = 0 then 1 else 0) * OrderedHyperbolicExtension.U i j *
      (if j = 0 then 1 else 0)) / 2 = 0
  norm_num [OrderedHyperbolicExtension.U, Fin.sum_univ_two]

private theorem slice_eq_vacuum_or_zero {x : ComplexState} (hx : x ∈ C)
    (l : Label hyperbolicPlane) (S : Finset ℕ) (h : slice l S x ≠ 0) :
    l.1 = momentum ∧ 3 ∉ S ∧
      (oscillatorEnergy l.2 : ℤ) + relativeEnergy S = 1 ∧
      ActualLeechOrbifoldMatter.mode 0 (slice l S x) = 0 := by
  obtain ⟨hp, he, hb⟩ := (mem_C x).mp hx
  have hl : l.1 = momentum := by
    by_contra hn
    have hzero := slice_projection momentum l S x
    rw [hp, ite_eq_right hn, zero_smul] at hzero
    exact h hzero
  have hS : 3 ∉ S := by
    intro hm
    have hzero := slice_b0 l S hm x
    rw [hb, map_zero] at hzero
    exact h ((smul_eq_zero.mp hzero.symm).resolve_left
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
  have hwt : energy hyperbolicPlane l + BcGhostRelativeEnergy.energy S =
      (oscillatorEnergy l.2 : ℤ) + relativeEnergy S - 1 := by
    simp only [energy, hl, chargeEnergy_momentum, zero_add, relativeEnergy]
    omega
  let t : ℤ := (oscillatorEnergy l.2 : ℤ) + relativeEnergy S - 1
  have ht : -1 ≤ t := by
    have := relativeEnergy_nonneg S
    dsimp [t]
    omega
  have hm := slice_energy l S x
  rw [he, map_zero, hwt] at hm
  have hm' : ActualLeechOrbifoldMatter.mode 0 (slice l S x) =
      (-(t : ℂ)) • slice l S x := by
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact hm.symm
  have hz : t = 0 := by
    by_contra hn
    by_cases hneg : t = -1
    · apply h
      apply ActualLeechOrbifoldMatter.eq_zero_of_weight_one
      simpa [hneg] using hm'
    · have ht' : 0 < t := by omega
      exact h (ActualLeechOrbifoldMatter.eq_zero_of_weight_neg _ _
        (by simp only [Complex.neg_re, Complex.intCast_re]; exact_mod_cast (show -t < 0 by omega))
        hm')
  refine ⟨hl, hS, ?_, ?_⟩
  · dsimp [t] at hz
    omega
  · simpa [hz] using hm'

private theorem ghost_low_support (S : Finset ℕ) (h3 : 3 ∉ S) (hS : relativeEnergy S ≤ 1) :
    S = ∅ ∨ S = {1} ∨ S = {1, 5} := by
  classical
  have site_bound (j : ℕ) (hj : j ∈ S) (h1 : j ≠ 1) : j = 5 := by
    have hmem : j ∈ (S.erase 1).erase 3 := by
      simp [Finset.mem_erase, hj, h1, show j ≠ 3 from fun e => h3 (e ▸ hj)]
    have hsum : BcGhostRelativeEnergy.siteEnergy j ≤
        ∑ k ∈ (S.erase 1).erase 3, BcGhostRelativeEnergy.siteEnergy k :=
      Finset.single_le_sum (fun k hk =>
        (BcGhostRelativeEnergy.siteEnergy_pos_of_ne_one_three
          (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1).le) hmem
    rw [BcGhostRelativeEnergy.relativeEnergy_split] at hS
    have hjle : BcGhostRelativeEnergy.siteEnergy j ≤ 1 := by
      split_ifs at hS <;> omega
    by_cases hev : j % 2 = 0
    · have hje : j = 2 * (j / 2) := by omega
      rw [hje, BcGhostRelativeEnergy.siteEnergy_even] at hjle
      omega
    · have hjo : j = 2 * (j / 2) + 1 := by omega
      rw [hjo, BcGhostRelativeEnergy.siteEnergy_odd] at hjle
      have hn3 : j ≠ 3 := fun e => h3 (e ▸ hj)
      omega
  by_cases h5 : 5 ∈ S
  · have h1 : 1 ∈ S := by
      by_contra hn
      have hmem : 5 ∈ (S.erase 1).erase 3 := by simp [h5]
      have hsum : BcGhostRelativeEnergy.siteEnergy 5 ≤
          ∑ k ∈ (S.erase 1).erase 3, BcGhostRelativeEnergy.siteEnergy k :=
        Finset.single_le_sum (fun k hk =>
          (BcGhostRelativeEnergy.siteEnergy_pos_of_ne_one_three
            (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1).le) hmem
      have hval : BcGhostRelativeEnergy.siteEnergy 5 = 1 := by decide
      rw [BcGhostRelativeEnergy.relativeEnergy_split, ite_eq_left hn] at hS
      omega
    right; right
    ext j
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun hj => or_iff_not_imp_left.mpr (site_bound j hj),
      fun hj => hj.elim (fun e => e ▸ h1) (fun e => e ▸ h5)⟩
  · by_cases h1 : 1 ∈ S
    · right; left
      ext j
      simp only [Finset.mem_singleton]
      exact ⟨fun hj => by by_contra hn; exact h5 (site_bound j hj hn ▸ hj),
        fun e => e ▸ h1⟩
    · left
      exact Finset.eq_empty_iff_forall_notMem.mpr
        (fun j hj => h5 (site_bound j hj (fun e => h1 (e ▸ hj)) ▸ hj))

private abbrev excitation (i : Fin 2) : Exponent hyperbolicPlane :=
  Finsupp.single (i, 0) 1

private abbrev orbifoldVacuum : Orbifold := OriginalOrbifoldField.vacuumState leechData leechUnit

private def shellState (d : Exponent hyperbolicPlane) (S : Finset ℕ) : ComplexState :=
  (orbifoldVacuum ⊗ₜ[ℂ] carrierBasis hyperbolicPlane (momentum, d)) ⊗ₜ[ℂ] ket S

/-- The literal matter ground with empty ghost occupation. -/
def v : ComplexState := shellState 0 ∅

/-- The literal plane oscillator with ghost occupation at site one. -/
def u (i : Fin 2) : ComplexState := shellState (excitation i) {1}

/-- The literal matter ground with ghost occupation at sites one and five. -/
def w : ComplexState := shellState 0 {1, 5}

private theorem shellState_mem_C (d : Exponent hyperbolicPlane) (S : Finset ℕ)
    (h3 : 3 ∉ S) (hE : (oscillatorEnergy d : ℤ) + BcGhostRelativeEnergy.energy S = 0) :
    shellState d S ∈ C := by
  classical
  apply (mem_C _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change ((orbifoldVacuum ⊗ₜ[ℂ] chargeProjection momentum
      (carrierBasis hyperbolicPlane (momentum, d))) ⊗ₜ[ℂ] ket S) = _
    simp only [carrierBasis_apply, chargeProjection, LinearMap.comp_apply,
      Finsupp.lapply_apply, Finsupp.single_eq_same, Finsupp.lsingle_apply, shellState]
  · have hp : hyperbolicMatter.mode 0 (carrierBasis hyperbolicPlane (momentum, d)) =
        (oscillatorEnergy d : ℂ) • carrierBasis hyperbolicPlane (momentum, d) := by
      change sugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) 0 _ = _
      simpa only [energy, chargeEnergy_momentum, zero_add, Int.cast_natCast] using
        actualL0_basis hyperbolicPlane _ plane_inverse plane_inverse (momentum, d)
    change (matter.mode 0 (orbifoldVacuum ⊗ₜ[ℂ] carrierBasis hyperbolicPlane (momentum, d))
      ⊗ₜ[ℂ] ket S) + (_ ⊗ₜ[ℂ] BcGhostVirasoro.L 0 (ket S)) = _
    rw [matter_mode_tmul, mode_vacuum 0 (by omega), TensorProduct.zero_tmul, zero_add,
      hp, BcGhostRelativeEnergy.L_zero_ket]
    simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', LinearMap.id_apply]
    rw [← add_smul, ← Int.cast_natCast, ← Int.cast_add, hE, Int.cast_zero, zero_smul]
  · change _ ⊗ₜ[ℂ] CountableOccupationFock.annihilate 3 (ket S) = _
    rw [CountableOccupationFock.annihilate_ket, ite_eq_right h3, TensorProduct.tmul_zero]

private theorem v_mem_C : v ∈ C :=
  shellState_mem_C _ _ (by decide) (by simp [oscillatorEnergy, BcGhostRelativeEnergy.energy])

private theorem u_mem_C (i : Fin 2) : u i ∈ C :=
  shellState_mem_C _ _ (by decide) (by
    have he := (Lattice.RootlessLowGrades.oscillator_one_iff hyperbolicPlane (excitation i)).mpr
      ⟨i, rfl⟩
    rw [he]
    exact (by decide : (1 : ℤ) + BcGhostRelativeEnergy.energy {1} = 0))

private theorem w_mem_C : w ∈ C :=
  shellState_mem_C _ _ (by decide) (by
    rw [(oscillatorEnergy_eq_zero_iff hyperbolicPlane 0).mpr rfl]
    decide)

private theorem slice_shellState (l : Label hyperbolicPlane) (S : Finset ℕ)
    (d : Exponent hyperbolicPlane) (T : Finset ℕ) :
    slice l S (shellState d T) =
      if l = (momentum, d) ∧ S = T then orbifoldVacuum else 0 := by
  classical
  rw [shellState, slice_tmul, carrierCoeffEquiv_basis]
  by_cases hl : l = (momentum, d)
  · subst l
    by_cases hS : S = T
    · subst S
      simp [ket]
    · simp [ket, hS]
  · simp [ket, hl]

private def coefficient (l : Label hyperbolicPlane) (S : Finset ℕ) : ComplexState →ₗ[ℂ] ℂ :=
  ((carrierBasis leechData).coord (0, 0)).comp (fixedProjection.comp (slice l S))

private theorem coefficient_vacuum {l : Label hyperbolicPlane} {S : Finset ℕ}
    {x : ComplexState} (h : ActualLeechOrbifoldMatter.mode 0 (slice l S x) = 0) :
    slice l S x = coefficient l S x • orbifoldVacuum :=
  ActualLeechOrbifoldMatter.weight_zero_vacuum _ h

private theorem excitation_ne : excitation 0 ≠ excitation 1 := by
  intro h
  have he := DFunLike.congr_fun h ((0 : Fin 2), 0)
  change Finsupp.single ((0 : Fin 2), (0 : ℕ)) (1 : ℕ) ((0 : Fin 2), 0) =
    Finsupp.single ((1 : Fin 2), (0 : ℕ)) (1 : ℕ) ((0 : Fin 2), 0) at he
  simp at he

private theorem slice_support {x : ComplexState} (hx : x ∈ C)
    (l : Label hyperbolicPlane) (S : Finset ℕ) (h : slice l S x ≠ 0) :
    (l = (momentum, 0) ∧ S = ∅) ∨
      (l = (momentum, excitation 0) ∧ S = {1}) ∨
      (l = (momentum, excitation 1) ∧ S = {1}) ∨
      (l = (momentum, 0) ∧ S = {1, 5}) := by
  obtain ⟨hl, h3, hwt, _⟩ := slice_eq_vacuum_or_zero hx l S h
  have hS : relativeEnergy S ≤ 1 := by omega
  rcases ghost_low_support S h3 hS with rfl | rfl | rfl
  · have hghost : relativeEnergy ∅ = 1 := by decide
    left
    exact ⟨Prod.ext hl ((oscillatorEnergy_eq_zero_iff _ _).mp (by omega)), rfl⟩
  · have hghost : relativeEnergy {1} = 0 := by decide
    obtain ⟨i, hi⟩ := (Lattice.RootlessLowGrades.oscillator_one_iff hyperbolicPlane l.2).mp
      (by omega)
    fin_cases i
    · exact Or.inr (Or.inl ⟨Prod.ext hl hi, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨Prod.ext hl hi, rfl⟩))
  · have hghost : relativeEnergy {1, 5} = 1 := by decide
    exact Or.inr (Or.inr (Or.inr
      ⟨Prod.ext hl ((oscillatorEnergy_eq_zero_iff _ _).mp (by omega)), rfl⟩))

private abbrev cv := coefficient (momentum, 0) ∅
private abbrev cu (i : Fin 2) := coefficient (momentum, excitation i) {1}
private abbrev cw := coefficient (momentum, 0) {1, 5}

/-- The four original tensor states span every relative zero-energy state at this charge. -/
theorem expansion {x : ComplexState} (hx : x ∈ C) :
    x = cv x • v + cu 0 x • u 0 + cu 1 x • u 1 + cw x • w := by
  classical
  apply slice_ext
  intro l S
  simp only [map_add, map_smul, v, u, w, slice_shellState]
  by_cases hs : (l = (momentum, 0) ∧ S = ∅) ∨
      (l = (momentum, excitation 0) ∧ S = {1}) ∨
      (l = (momentum, excitation 1) ∧ S = {1}) ∨
      (l = (momentum, 0) ∧ S = {1, 5})
  · have hm : ActualLeechOrbifoldMatter.mode 0 (slice l S x) = 0 := by
      by_cases h : slice l S x = 0
      · rw [h, map_zero]
      · exact (slice_eq_vacuum_or_zero hx l S h).2.2.2
    have hvac := coefficient_vacuum hm
    have h01 : (momentum, excitation 0) ≠ (momentum, excitation 1) :=
      fun e => excitation_ne (congrArg Prod.snd e)
    have e01 : (∅ : Finset ℕ) ≠ {1} := by decide
    have e02 : (∅ : Finset ℕ) ≠ {1, 5} := by decide
    have e12 : ({1} : Finset ℕ) ≠ {1, 5} := by decide
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simpa [h01, Ne.symm h01, e01, Ne.symm e01, e02, Ne.symm e02, e12, Ne.symm e12]
        using hvac
  · simp only [not_or] at hs
    rw [ite_eq_right hs.1, ite_eq_right hs.2.1, ite_eq_right hs.2.2.1,
      ite_eq_right hs.2.2.2]
    simp only [smul_zero, add_zero]
    by_contra h
    rcases slice_support hx l S h with h0 | h1 | h2 | h3
    · exact hs.1 h0
    · exact hs.2.1 h1
    · exact hs.2.2.1 h2
    · exact hs.2.2.2 h3

#print axioms projectionAt_Q
#print axioms expansion

end D5.S3.VertexAlgebra.ActualLeechOrbifoldRelativePrimitiveNull
