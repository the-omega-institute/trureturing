/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeZeroMomentum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeZeroMomentum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Leech orbifold relative BRST cohomology at zero momentum. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
import D5.S3.VertexAlgebra.Lattice.LatticeZeroMomentumBRST

/-! At zero plane momentum the slice energy bound and the actual orbifold low
weights reduce the shell to the orbifold vacuum tensored with the original
plane and ghost shell. The Ward readouts follow the primitive-null computation
(lexa-ms, a0e58e3cdf940bf6f5725484ddc6e54ac4dc2581). -/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeZeroMomentum

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (Orbifold mode leechUnit weight_zero_vacuum eq_zero_of_weight_one)
open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane hyperbolicMatter)
open LatticeGeneratingFieldLocality (Carrier Charge)
open LatticePositiveEnergy (carrierBasis carrierCoeffEquiv carrierCoeffEquiv_basis)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open LatticeQuartetContraction (State StateIndex ghostB0 chargeProject)
open LatticeRelativeMassShell (relativeMassShell fixedMomentum totalL0)
open LatticeMatterGhostDegree (tensorNumber)
open LatticeRelativeShellDegreeBounds (frameEnergy)
open RelativeCohomology (GhostSpace assocN relativeQ_degree GradedCycles GradedBoundaries
  GradedCohomology)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket vacuum annihilate annihilate_ket lowerCount phase)
open BcGhostRelativeEnergy (relativeEnergy relativeEnergy_nonneg)

open private plane_inverse from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter
open private mode_vacuum from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLowWeights
open private matter_mode_tmul rightLift_tmul rightSlice_tmul assocB0_eq assocE_decomposition
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private eq_zero_of_all_rightSlices
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightConeDegreeBounds
open private assocN_eq mem_ghostSpace assocQ_reassoc gradedBoundaryMap
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private mem_fixedMomentum_iff_chargeProject originalEnergy
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
open private sugawara_current neutral_ground_nonneg
  from D5.S3.VertexAlgebra.Lattice.LatticeZeroMomentumBRST
open private L_vacuum L_vacuum_nonneg from D5.S3.Quantum.Fermionic.BcGhostVirasoro

private abbrev orbVac : Orbifold := TwistedGround.Orbifold.OriginalOrbifoldField.vacuumState
  leechData leechUnit

private abbrev H := gramComplex hyperbolicPlane
private abbrev PlaneState := State hyperbolicPlane
private abbrev PlaneShell := relativeMassShell hyperbolicPlane H 0
private abbrev Shell := relativeShell (0 : Charge hyperbolicPlane)
private abbrev slice := rightSlice planeFrame planeBasis

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup
local instance : AddCommGroup Shell := Submodule.addCommGroup _
local instance : AddCommGroup PlaneShell := Submodule.addCommGroup _

private def vacCoeff : Orbifold →ₗ[ℂ] ℂ :=
  ((carrierBasis leechData).coord (0, 0)).comp
    ((Submodule.subtype (LatticeInvolution.fixedSpace leechData)).comp (LinearMap.fst ℂ _ _))

private theorem vacCoeff_vac : vacCoeff orbVac = 1 := by
  change carrierCoeffEquiv leechData (Finsupp.single 0 1) (0, 0) = 1
  have h : carrierBasis leechData (0, 0) = Finsupp.single 0 1 := by simp
  rw [← h, carrierCoeffEquiv_basis, Finsupp.single_eq_same]

private def vacTensor : PlaneState →ₗ[ℂ] AssocState :=
  TensorProduct.mk ℂ Orbifold PlaneState orbVac

private def dropVac : AssocState →ₗ[ℂ] PlaneState :=
  (TensorProduct.lid ℂ PlaneState).toLinearMap.comp (vacCoeff.rTensor PlaneState)

private theorem dropVac_tmul (v : Orbifold) (y : PlaneState) :
    dropVac (v ⊗ₜ[ℂ] y) = vacCoeff v • y := by
  simp only [dropVac, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul]

private theorem dropVac_vacTensor (y : PlaneState) : dropVac (vacTensor y) = y := by
  change dropVac (orbVac ⊗ₜ[ℂ] y) = y
  rw [dropVac_tmul, vacCoeff_vac, one_smul]

private theorem vacTensor_injective : Function.Injective vacTensor :=
  Function.LeftInverse.injective dropVac_vacTensor

private theorem vacTensor_slice (x : AssocState) (i : StateIndex hyperbolicPlane 0) :
    slice i (vacTensor (dropVac x)) = vacCoeff (slice i x) • orbVac := by
  induction x using TensorProduct.inductionOn with
  | tmul v y =>
    rw [dropVac_tmul, map_smul, map_smul]
    change vacCoeff v • slice i (orbVac ⊗ₜ[ℂ] y) =
      vacCoeff (slice i (v ⊗ₜ[ℂ] y)) • orbVac
    simp only [rightSlice_tmul, map_smul, smul_smul, smul_eq_mul]
    rw [mul_comm (vacCoeff v)]
  | add x y hx hy => simp only [map_add, hx, hy, add_smul]

private theorem shell_slice_vac (x : Shell) (i : StateIndex hyperbolicPlane 0) :
    slice i x.val = vacCoeff (slice i x.val) • orbVac := by
  by_cases hi : slice i x.val = 0
  · rw [hi, map_zero, zero_smul]
  obtain ⟨hp, _, _, hlevel⟩ :=
    relativeShell_rightSlice_bounds planeFrame planeBasis 0 x.val x.property i hi
  have hcharge : LatticePositiveEnergy.chargeEnergy hyperbolicPlane (0 : Charge hyperbolicPlane)
      = 0 := by simp
  have he := rightSlice_eigen_of_assocE_eq_zero planeFrame planeBasis x.val
    ((mem_relativeShell_iff 0 x.val).mp x.property).2.2 i
  rw [hp, hcharge, sub_zero] at he
  rw [hcharge, sub_zero] at hlevel
  have hf : 0 ≤ (frameEnergy i.1.2 : ℤ) := Int.natCast_nonneg _
  have hg := relativeEnergy_nonneg i.2
  have hzero : 1 - (frameEnergy i.1.2 : ℤ) - relativeEnergy i.2 = 0 := by
    by_contra hn
    have hone : 1 - (frameEnergy i.1.2 : ℤ) - relativeEnergy i.2 = 1 := by omega
    rw [hone, Int.cast_one, one_smul] at he
    exact hi (eq_zero_of_weight_one _ he)
  rw [hzero, Int.cast_zero, zero_smul] at he
  exact weight_zero_vacuum _ he

private theorem vacTensor_dropVac_shell (x : Shell) : vacTensor (dropVac x.val) = x.val := by
  apply sub_eq_zero.mp
  apply eq_zero_of_all_rightSlices planeFrame planeBasis
  intro i
  rw [map_sub, vacTensor_slice, ← shell_slice_vac x i, sub_self]

private theorem lift_vacTensor (A : Module.End ℂ PlaneState) (y : PlaneState) :
    rightLift A (vacTensor y) = vacTensor (A y) := rightLift_tmul A orbVac y

private theorem vacTensor_mem_shell (y : PlaneState) :
    vacTensor y ∈ Shell ↔ y ∈ PlaneShell := by
  have he : assocE (vacTensor y) = vacTensor (totalL0 hyperbolicPlane H y) := by
    rw [assocE_decomposition, LinearMap.add_apply, lift_vacTensor]
    change mode 0 orbVac ⊗ₜ[ℂ] y + vacTensor (originalEnergy hyperbolicPlane H y) = _
    rw [mode_vacuum 0 (by decide), TensorProduct.zero_tmul, zero_add]
    rfl
  rw [mem_relativeShell_iff, assocB0_eq, lift_vacTensor, lift_vacTensor, he]
  change (_ ∧ _ ∧ _) ↔
    (y ∈ fixedMomentum hyperbolicPlane 0 ∧ ghostB0 y = 0) ∧ totalL0 hyperbolicPlane H y = 0
  rw [← vacTensor.map_zero]
  constructor
  · rintro ⟨hp, hb, hE⟩
    exact ⟨⟨(mem_fixedMomentum_iff_chargeProject 0 y).mpr (vacTensor_injective hp),
      vacTensor_injective hb⟩, vacTensor_injective hE⟩
  · rintro ⟨⟨hp, hb⟩, hE⟩
    exact ⟨congrArg vacTensor ((mem_fixedMomentum_iff_chargeProject 0 y).mp hp),
      congrArg vacTensor hb, congrArg vacTensor hE⟩

private def planeInclusion : PlaneShell ≃ₗ[ℂ] Shell where
  toFun y := ⟨vacTensor y.val, (vacTensor_mem_shell y.val).mpr y.property⟩
  invFun x := ⟨dropVac x.val, (vacTensor_mem_shell _).mp (by
    rw [vacTensor_dropVac_shell]
    exact x.property)⟩
  left_inv y := Subtype.ext (dropVac_vacTensor y.val)
  right_inv x := Subtype.ext (vacTensor_dropVac_shell x)
  map_add' x y := Subtype.ext (vacTensor.map_add x.val y.val)
  map_smul' a x := Subtype.ext (vacTensor.map_smul a x.val)

abbrev Coordinates := LatticeZeroMomentumBRST.Coordinates hyperbolicPlane

private abbrev planeEquiv :=
  LatticeZeroMomentumBRST.shellEquiv hyperbolicPlane H plane_inverse plane_inverse

/-- The coefficients of the literal zero-momentum relative shell. -/
def shellEquiv : Shell ≃ₗ[ℂ] Coordinates := planeInclusion.symm.trans planeEquiv

private abbrev cochain (z : Coordinates) : Shell := shellEquiv.symm z

private theorem cochain_val (z : Coordinates) :
    (cochain z).val = vacTensor (LatticeZeroMomentumBRST.Psi
      hyperbolicPlane H plane_inverse plane_inverse z) := by
  change (planeInclusion (planeEquiv.symm z)).val = _
  rfl

/-- The native three-factor representative of a shell coefficient vector. -/
def representative : Coordinates →ₗ[ℂ] ComplexState :=
  reassoc.symm.toLinearMap.comp (Shell.subtype.comp shellEquiv.symm.toLinearMap)

private theorem representative_eq (x : Shell) :
    representative (shellEquiv x) = reassoc.symm x.val := by
  change reassoc.symm (shellEquiv.symm (shellEquiv x)).val = _
  rw [LinearEquiv.symm_apply_apply]

private abbrev planeVac := LatticeZeroMomentumBRST.ground hyperbolicPlane
private abbrev planeCurrent := LatticeZeroMomentumBRST.current hyperbolicPlane

/-- The vacuum in degree zero. -/
def v : ComplexState := (orbVac ⊗ₜ[ℂ] planeVac) ⊗ₜ[ℂ] ket ∅

/-- A level-one plane current with the literal c(1) vacuum occupation. -/
def u (i : Fin 2) : ComplexState := (orbVac ⊗ₜ[ℂ] planeCurrent i) ⊗ₜ[ℂ] ket {1}

/-- The matter vacuum with the literal two-ghost occupation. -/
def w : ComplexState := (orbVac ⊗ₜ[ℂ] planeVac) ⊗ₜ[ℂ] ket {1, 5}

/-- All actual shell representatives in the original tensor association. -/
theorem representative_formula (z : Coordinates) :
    representative z = z.1 • v +
      ((orbVac ⊗ₜ[ℂ] (∑ i, z.2.1 i • planeCurrent i)) ⊗ₜ[ℂ] ket {1}) +
      z.2.2 • w := by
  change reassoc.symm (cochain z).val = _
  rw [cochain_val, LatticeZeroMomentumBRST.Psi_formula]
  simp only [map_add, map_smul, vacTensor, TensorProduct.mk_apply, reassoc,
    TensorProduct.assoc_symm_tmul, v, w]

private theorem representative_zero (c : ℂ) : representative (c, (0, 0)) = c • v := by
  simp [representative_formula]

private theorem representative_one (f : Fin 2 → ℂ) :
    representative (0, (f, 0)) = (orbVac ⊗ₜ[ℂ] (∑ i, f i • planeCurrent i)) ⊗ₜ[ℂ] ket {1} := by
  rw [representative_formula]
  simp only [zero_smul, zero_add, add_zero]
  rfl

private theorem representative_two (c : ℂ) : representative (0, (0, c)) = c • w := by
  simp [representative_formula]

private theorem representative_current (i : Fin 2) :
    representative (0, (Pi.single i 1, 0)) = u i := by
  classical
  have hs :
      (∑ j : Fin 2, Pi.single (M := fun _ : Fin 2 => ℂ) i 1 j • planeCurrent j) =
        planeCurrent i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  rw [representative_one, hs, u]

private def ghostCoordinates (z : Coordinates) : Coordinates := (0, (z.2.1, 2 * z.2.2))

private theorem ghost_action (z : Coordinates) :
    assocN (cochain z).val = (cochain (ghostCoordinates z)).val := by
  simp only [cochain_val, assocN_eq, lift_vacTensor]
  change vacTensor (tensorNumber hyperbolicPlane
    (LatticeZeroMomentumBRST.Psi hyperbolicPlane H plane_inverse plane_inverse z)) =
    vacTensor (LatticeZeroMomentumBRST.Psi hyperbolicPlane H plane_inverse plane_inverse
      (0, (z.2.1, 2 * z.2.2)))
  rw [LatticeZeroMomentumBRST.totalGhostNumber_Psi]

private theorem ghost_iff (g : ℤ) (z : Coordinates) :
    cochain z ∈ GhostSpace 0 g ↔ ghostCoordinates z = (g : ℂ) • z := by
  have hs : (cochain ((g : ℂ) • z)).val = (g : ℂ) • (cochain z).val :=
    congrArg Subtype.val (shellEquiv.symm.map_smul (g : ℂ) z)
  rw [mem_ghostSpace, ghost_action, ← hs]
  constructor
  · intro h
    exact shellEquiv.symm.injective (Subtype.ext h)
  · intro h
    rw [h]

private theorem ghost_support (g : ℤ) (x : Shell) (hx : x ∈ GhostSpace 0 g) :
    let z := shellEquiv x
    (g ≠ 0 → z.1 = 0) ∧ (g ≠ 1 → z.2.1 = 0) ∧ (g ≠ 2 → z.2.2 = 0) := by
  let z := shellEquiv x
  have hz : cochain z ∈ GhostSpace 0 g := by
    simpa only [z, LinearEquiv.symm_apply_apply] using hx
  have h := (ghost_iff g z).mp hz
  refine ⟨?_, ?_, ?_⟩
  · intro hg
    have hc : (g : ℂ) ≠ 0 := by exact_mod_cast hg
    have h0 : 0 = (g : ℂ) * z.1 := congrArg Prod.fst h
    exact (mul_eq_zero.mp h0.symm).resolve_left hc
  · intro hg
    have hc : (g : ℂ) ≠ 1 := by exact_mod_cast hg
    funext i
    have h1 : z.2.1 i = (g : ℂ) * z.2.1 i :=
      congrArg (fun z : Coordinates => z.2.1 i) h
    change z.2.1 i = 0
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hc)
    rw [sub_mul, one_mul, ← h1, sub_self]
  · intro hg
    have hc : (g : ℂ) ≠ 2 := by exact_mod_cast hg
    have h2 : 2 * z.2.2 = (g : ℂ) * z.2.2 := congrArg (fun z : Coordinates => z.2.2) h
    apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hc)
    rw [sub_mul, ← h2, sub_self]

private theorem zero_mem_degree (c : ℂ) : cochain (c, (0, 0)) ∈ GhostSpace 0 0 := by
  rw [ghost_iff]
  simp [ghostCoordinates]

private theorem one_mem_degree (f : Fin 2 → ℂ) : cochain (0, (f, 0)) ∈ GhostSpace 0 1 := by
  rw [ghost_iff]
  simp [ghostCoordinates]

private theorem two_mem_degree (c : ℂ) : cochain (0, (0, c)) ∈ GhostSpace 0 2 := by
  rw [ghost_iff]
  change ((0, (0, 2 * c)) : Coordinates) = (2 : ℂ) • ((0, (0, c)) : Coordinates)
  apply Prod.ext
  · change (0 : ℂ) = 2 * 0
    simp
  · apply Prod.ext
    · change (0 : Fin 2 → ℂ) = (2 : ℂ) • (0 : Fin 2 → ℂ)
      rw [smul_zero]
    · rfl

/-- No other integral ghost degree contains a nonzero actual cochain. -/
theorem ghostSpace_eq_bot (g : ℤ) (h0 : g ≠ 0) (h1 : g ≠ 1) (h2 : g ≠ 2) :
    GhostSpace 0 g = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hz, hu, hw⟩ := ghost_support g x hx
  have h : shellEquiv x = 0 := Prod.ext (hz h0) (Prod.ext (hu h1) (hw h2))
  exact (Submodule.mem_bot ℂ).mpr (shellEquiv.map_eq_zero_iff.mp h)

private abbrev B (n : ℤ) := VirasoroBRST.ghostB matter n
private abbrev C (n : ℤ) := VirasoroBRST.ghostC matter n
private abbrev L (n : ℤ) := VirasoroBRST.Ltotal matter n

private theorem ghost_B_neg_down : BcGhostFock.b (-1) (ket {1}) = vacuum := by
  change annihilate 1 (ket {1}) = _
  rw [annihilate_ket]
  have hc : lowerCount 1 {1} = 0 := by decide
  have he : ({1} : Finset ℕ).erase 1 = ∅ := by decide
  simp [phase, hc, he, vacuum]

private theorem ghost_B_pos_top : BcGhostFock.b 1 (ket {1, 5}) = -ket {1} := by
  change annihilate 5 (ket {1, 5}) = _
  rw [annihilate_ket]
  have hc : lowerCount 5 {1, 5} = 1 := by decide
  have he : ({1, 5} : Finset ℕ).erase 5 = {1} := by decide
  simp [phase, hc, he]

private theorem ghost_L_neg_vacuum : BcGhostVirasoro.L (-1) vacuum = 0 := by
  rw [L_vacuum, show Finset.Icc ((-1 : ℤ) + 2) 1 = {1} by decide]
  simp

private theorem ghost_L_pos_down : BcGhostVirasoro.L 1 (ket {1}) = 0 := by
  rw [← BcGhostFock.ghost_vacuum.2.2.1]
  have h := LinearMap.congr_fun (BcGhostVirasoro.ward_c 1 1) vacuum
  change BcGhostVirasoro.L 1 (BcGhostFock.c 1 vacuum) -
    BcGhostFock.c 1 (BcGhostVirasoro.L 1 vacuum) =
    ((-2 * 1 - 1 : ℤ) : ℂ) • BcGhostFock.c 2 vacuum at h
  rw [L_vacuum_nonneg 1 (by decide), map_zero, sub_zero,
    BcGhostFock.ghost_vacuum.2.1 2 (by decide), smul_zero] at h
  exact h

private theorem L_neg_v : L (-1) v = 0 := by
  have hp : hyperbolicMatter.mode (-1) planeVac = 0 :=
    LatticeZeroMomentumBRST.sugawara_ground hyperbolicPlane H (-1) (by decide)
  change (matter.mode (-1) (orbVac ⊗ₜ[ℂ] planeVac) ⊗ₜ[ℂ] vacuum) +
    ((orbVac ⊗ₜ[ℂ] planeVac) ⊗ₜ[ℂ] BcGhostVirasoro.L (-1) vacuum) = 0
  simp only [matter_mode_tmul, mode_vacuum (-1) (by decide), hp, ghost_L_neg_vacuum,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add]

private theorem L_pos_u (i : Fin 2) : L 1 (u i) = 0 := by
  have hp : hyperbolicMatter.mode 1 (planeCurrent i) = 0 := by
    change sugawaraMode hyperbolicPlane H 1 (planeCurrent i) = 0
    rw [sugawara_current hyperbolicPlane H plane_inverse plane_inverse i 1 (by decide)]
    exact neutral_ground_nonneg hyperbolicPlane i 0 (by decide)
  change (matter.mode 1 (orbVac ⊗ₜ[ℂ] planeCurrent i) ⊗ₜ[ℂ] ket {1}) +
    ((orbVac ⊗ₜ[ℂ] planeCurrent i) ⊗ₜ[ℂ] BcGhostVirasoro.L 1 (ket {1})) = 0
  simp only [matter_mode_tmul, mode_vacuum 1 (by decide), hp, ghost_L_pos_down,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add]

private theorem ward_readout (n : ℤ) (x : ComplexState)
    (hb : B n x = 0) (hl : L n x = 0) : B n (Q x) = 0 := by
  have h : Q (B n x) + B n (Q x) = L n x :=
    LinearMap.congr_fun (VirasoroBRST.Q_ward_b matter n) x
  simpa only [hb, hl, map_zero, zero_add] using h

private theorem degree_one_readout (x : Shell) (hx : x ∈ GhostSpace 0 1)
    (hb : B (-1) (reassoc.symm x.val) = 0) : reassoc.symm x.val = 0 := by
  let z := shellEquiv x
  obtain ⟨h0, _, h2⟩ := ghost_support 1 x hx
  have hz : z = (0, (z.2.1, 0)) :=
    Prod.ext (h0 (by decide)) (Prod.ext rfl (h2 (by decide)))
  have hr : reassoc.symm x.val =
      (orbVac ⊗ₜ[ℂ] (∑ i, z.2.1 i • planeCurrent i)) ⊗ₜ[ℂ] ket {1} := by
    calc
      reassoc.symm x.val = representative z := (representative_eq x).symm
      _ = representative (0, (z.2.1, 0)) := congrArg representative hz
      _ = _ := representative_one _
  have h : C 1 (B (-1) (reassoc.symm x.val)) = reassoc.symm x.val := by
    rw [hr]
    change _ ⊗ₜ[ℂ] BcGhostFock.c 1 (BcGhostFock.b (-1) (ket {1})) = _
    rw [ghost_B_neg_down, BcGhostFock.ghost_vacuum.2.2.1]
    rfl
  rw [hb, map_zero] at h
  exact h.symm

private theorem degree_two_readout (x : Shell) (hx : x ∈ GhostSpace 0 2)
    (hb : B 1 (reassoc.symm x.val) = 0) : reassoc.symm x.val = 0 := by
  let z := shellEquiv x
  obtain ⟨h0, h1, _⟩ := ghost_support 2 x hx
  have hz : z = (0, (0, z.2.2)) :=
    Prod.ext (h0 (by decide)) (Prod.ext (h1 (by decide)) rfl)
  have hr : reassoc.symm x.val = z.2.2 • w := by
    calc
      reassoc.symm x.val = representative z := (representative_eq x).symm
      _ = representative (0, (0, z.2.2)) := congrArg representative hz
      _ = _ := representative_two _
  have hw : C (-1) (B 1 w) = w := by
    change _ ⊗ₜ[ℂ] BcGhostFock.c (-1) (BcGhostFock.b 1 (ket {1, 5})) = _
    rw [ghost_B_pos_top, map_neg, LatticeZeroMomentumBRST.c_minus_one_down, neg_neg]
    rfl
  have h := congrArg (C (-1)) hb
  rw [map_zero, hr, map_smul, map_smul, hw] at h
  exact hr.trans h

private theorem relativeQ_native (z : Coordinates) :
    reassoc.symm (relativeQ planeFrame planeBasis 0 (cochain z)).val =
      Q (representative z) := by
  have h := assocQ_reassoc (reassoc.symm (cochain z).val)
  rw [LinearEquiv.apply_symm_apply] at h
  change reassoc.symm (assocQ (cochain z).val) = Q (reassoc.symm (cochain z).val)
  rw [h, LinearEquiv.symm_apply_apply]

private theorem Q_v : Q v = 0 := by
  let x := relativeQ planeFrame planeBasis 0 (cochain (1, (0, 0)))
  have hx : x ∈ GhostSpace 0 1 :=
    relativeQ_degree planeFrame planeBasis 0 0 _ (zero_mem_degree 1)
  have h : reassoc.symm x.val = Q v := by
    simpa only [representative_zero, one_smul] using relativeQ_native (1, (0, 0))
  rw [← h]
  apply degree_one_readout x hx
  rw [h]
  apply ward_readout (-1) v _ L_neg_v
  change _ ⊗ₜ[ℂ] BcGhostFock.b (-1) vacuum = 0
  rw [BcGhostFock.ghost_vacuum.1 (-1) (by decide), TensorProduct.tmul_zero]

private theorem Q_u (i : Fin 2) : Q (u i) = 0 := by
  let x := relativeQ planeFrame planeBasis 0 (cochain (0, (Pi.single i 1, 0)))
  have hx : x ∈ GhostSpace 0 2 :=
    relativeQ_degree planeFrame planeBasis 0 1 _ (one_mem_degree _)
  have h : reassoc.symm x.val = Q (u i) := by
    simpa only [representative_current] using relativeQ_native (0, (Pi.single i 1, 0))
  rw [← h]
  apply degree_two_readout x hx
  rw [h]
  apply ward_readout 1 (u i) _ (L_pos_u i)
  change _ ⊗ₜ[ℂ] annihilate 5 (ket {1}) = 0
  rw [annihilate_ket, ite_eq_right (by decide), TensorProduct.tmul_zero]

private theorem Q_w : Q w = 0 := by
  let x := relativeQ planeFrame planeBasis 0 (cochain (0, (0, 1)))
  have hx : x ∈ GhostSpace 0 3 :=
    relativeQ_degree planeFrame planeBasis 0 2 _ (two_mem_degree 1)
  rw [ghostSpace_eq_bot 3 (by decide) (by decide) (by decide)] at hx
  have hx0 := (Submodule.mem_bot ℂ).mp hx
  have h : reassoc.symm x.val = Q w := by
    simpa only [representative_two, one_smul] using relativeQ_native (0, (0, 1))
  rw [← h, hx0]
  exact map_zero reassoc.symm

/-- The original BRST charge kills all four native basis vectors. -/
theorem differential_on_basis : Q v = 0 ∧ (∀ i, Q (u i) = 0) ∧ Q w = 0 :=
  ⟨Q_v, Q_u, Q_w⟩

/-- The actual differential on the literal zero-momentum relative shell is zero. -/
theorem relativeQ_eq_zero : relativeQ planeFrame planeBasis (0 : Charge hyperbolicPlane) = 0 := by
  apply LinearMap.ext
  intro x
  let z := shellEquiv x
  have hx : cochain z = x := shellEquiv.symm_apply_apply x
  have hr : representative z = z.1 • v + (∑ i, z.2.1 i • u i) + z.2.2 • w := by
    simp only [representative_formula, u, TensorProduct.tmul_sum, TensorProduct.sum_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have hq : Q (representative z) = 0 := by
    rw [hr]
    obtain ⟨hv, hu, hw⟩ := differential_on_basis
    simp only [map_add, map_sum, map_smul, hv, hu, hw, smul_zero, Finset.sum_const_zero, add_zero]
  have h := relativeQ_native z
  rw [hx, hq] at h
  apply Subtype.ext
  change (relativeQ planeFrame planeBasis 0 x).val = 0
  exact reassoc.symm.map_eq_zero_iff.mp h

abbrev Cohomology (g : ℤ) := GradedCohomology planeFrame planeBasis 0 g

local instance (g : ℤ) : AddCommGroup (GradedCycles planeFrame planeBasis 0 g) :=
  Submodule.addCommGroup _

private def cyclesEquiv (g : ℤ) : GhostSpace 0 g ≃ₗ[ℂ] GradedCycles planeFrame planeBasis 0 g where
  toFun x := ⟨x.val, x.property, by
    change relativeQ planeFrame planeBasis 0 x.val = 0
    rw [relativeQ_eq_zero, LinearMap.zero_apply]⟩
  invFun x := ⟨x.val, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem boundaries_eq_bot (g : ℤ) : GradedBoundaries planeFrame planeBasis 0 g = ⊥ := by
  change LinearMap.range (gradedBoundaryMap planeFrame planeBasis 0 g) = ⊥
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change relativeQ planeFrame planeBasis 0 x.val = 0
  rw [relativeQ_eq_zero, LinearMap.zero_apply]

/-- The actual kernel/image quotient is identified with its ghost eigenspace. -/
def cohomologyGhostEquiv (g : ℤ) : Cohomology g ≃ₗ[ℂ] GhostSpace 0 g :=
  ((GradedBoundaries planeFrame planeBasis 0 g).quotEquivOfEqBot (boundaries_eq_bot g)).trans
    (cyclesEquiv g).symm

/-- The literal class of a zero-momentum cochain in its own degree. -/
def classOf (g : ℤ) (x : GhostSpace 0 g) : Cohomology g :=
  Submodule.Quotient.mk (cyclesEquiv g x)

private theorem cohomologyGhostEquiv_symm_class (g : ℤ) (x : GhostSpace 0 g) :
    (cohomologyGhostEquiv g).symm x = classOf g x :=
  Submodule.quotEquivOfEqBot_symm_apply _ (boundaries_eq_bot g) (cyclesEquiv g x)

/-- The degree-zero cochain line, with its native vacuum coefficient. -/
def degreeZeroEquiv : GhostSpace 0 0 ≃ₗ[ℂ] ℂ where
  toFun x := (shellEquiv x.val).1
  invFun c := ⟨cochain (c, (0, 0)), zero_mem_degree c⟩
  left_inv x := by
    apply Subtype.ext
    apply shellEquiv.injective
    change shellEquiv (cochain ((shellEquiv x.val).1, (0, 0))) = shellEquiv x.val
    rw [LinearEquiv.apply_symm_apply]
    obtain ⟨_, h1, h2⟩ := ghost_support 0 x.val x.property
    exact Prod.ext rfl (Prod.ext (h1 (by decide)).symm (h2 (by decide)).symm)
  right_inv c := by
    change (shellEquiv (cochain (c, (0, 0)))).1 = c
    rw [LinearEquiv.apply_symm_apply]
  map_add' x y := congrArg Prod.fst (shellEquiv.map_add x.val y.val)
  map_smul' a x := congrArg Prod.fst (shellEquiv.map_smul a x.val)

/-- The two degree-one current coefficients in the literal shell. -/
def degreeOneEquiv : GhostSpace 0 1 ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun x := (shellEquiv x.val).2.1
  invFun f := ⟨cochain (0, (f, 0)), one_mem_degree f⟩
  left_inv x := by
    apply Subtype.ext
    apply shellEquiv.injective
    change shellEquiv (cochain (0, ((shellEquiv x.val).2.1, 0))) = shellEquiv x.val
    rw [LinearEquiv.apply_symm_apply]
    obtain ⟨h0, _, h2⟩ := ghost_support 1 x.val x.property
    exact Prod.ext (h0 (by decide)).symm (Prod.ext rfl (h2 (by decide)).symm)
  right_inv f := by
    change (shellEquiv (cochain (0, (f, 0)))).2.1 = f
    rw [LinearEquiv.apply_symm_apply]
  map_add' x y := congrArg (fun z : Coordinates => z.2.1) (shellEquiv.map_add x.val y.val)
  map_smul' a x := congrArg (fun z : Coordinates => z.2.1) (shellEquiv.map_smul a x.val)

/-- The degree-two cochain line supported at ghost sites 1 and 5. -/
def degreeTwoEquiv : GhostSpace 0 2 ≃ₗ[ℂ] ℂ where
  toFun x := (shellEquiv x.val).2.2
  invFun c := ⟨cochain (0, (0, c)), two_mem_degree c⟩
  left_inv x := by
    apply Subtype.ext
    apply shellEquiv.injective
    change shellEquiv (cochain (0, (0, (shellEquiv x.val).2.2))) = shellEquiv x.val
    rw [LinearEquiv.apply_symm_apply]
    obtain ⟨h0, h1, _⟩ := ghost_support 2 x.val x.property
    exact Prod.ext (h0 (by decide)).symm (Prod.ext (h1 (by decide)).symm rfl)
  right_inv c := by
    change (shellEquiv (cochain (0, (0, c)))).2.2 = c
    rw [LinearEquiv.apply_symm_apply]
  map_add' x y := congrArg (fun z : Coordinates => z.2.2) (shellEquiv.map_add x.val y.val)
  map_smul' a x := congrArg (fun z : Coordinates => z.2.2) (shellEquiv.map_smul a x.val)

/-- Actual zero-momentum relative cohomology in ghost degree zero. -/
def ghostZeroCohomologyEquiv : Cohomology 0 ≃ₗ[ℂ] ℂ :=
  (cohomologyGhostEquiv 0).trans degreeZeroEquiv

/-- Actual zero-momentum relative cohomology in ghost degree one. -/
def ghostOneCohomologyEquiv : Cohomology 1 ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (cohomologyGhostEquiv 1).trans degreeOneEquiv

/-- Actual zero-momentum relative cohomology in ghost degree two. -/
def ghostTwoCohomologyEquiv : Cohomology 2 ≃ₗ[ℂ] ℂ :=
  (cohomologyGhostEquiv 2).trans degreeTwoEquiv

/-- All other ghost degrees have zero actual relative cohomology. -/
theorem cohomology_vanishes (g : ℤ) (h0 : g ≠ 0) (h1 : g ≠ 1) (h2 : g ≠ 2) :
    Subsingleton (Cohomology g) := by
  have hz (x : GhostSpace 0 g) : x.val = 0 := by
    have hx : x.val ∈ (⊥ : Submodule ℂ Shell) := ghostSpace_eq_bot g h0 h1 h2 ▸ x.property
    exact (Submodule.mem_bot ℂ).mp hx
  exact ⟨fun x y => (cohomologyGhostEquiv g).injective
    (Subtype.ext ((hz _).trans (hz _).symm))⟩

/-- The inverse in degree zero is the class of the indicated vacuum multiple. -/
theorem ghostZeroCohomologyEquiv_symm (c : ℂ) :
    ghostZeroCohomologyEquiv.symm c =
      classOf 0 ⟨shellEquiv.symm (c, (0, 0)), zero_mem_degree c⟩ :=
  cohomologyGhostEquiv_symm_class 0 _

/-- The inverse in degree one is the class of the indicated plane current. -/
theorem ghostOneCohomologyEquiv_symm (f : Fin 2 → ℂ) :
    ghostOneCohomologyEquiv.symm f =
      classOf 1 ⟨shellEquiv.symm (0, (f, 0)), one_mem_degree f⟩ :=
  cohomologyGhostEquiv_symm_class 1 _

/-- The inverse in degree two uses the actual occupation at sites 1 and 5. -/
theorem ghostTwoCohomologyEquiv_symm (c : ℂ) :
    ghostTwoCohomologyEquiv.symm c =
      classOf 2 ⟨shellEquiv.symm (0, (0, c)), two_mem_degree c⟩ :=
  cohomologyGhostEquiv_symm_class 2 _

/-- The inverse quotient isomorphisms send the standard coordinates to the classes of the
displayed native basis states. -/
theorem basis_representatives :
    (∃ x : GhostSpace 0 0,
      ghostZeroCohomologyEquiv.symm 1 = classOf 0 x ∧ reassoc.symm x.val.val = v) ∧
    (∀ i : Fin 2, ∃ x : GhostSpace 0 1,
      ghostOneCohomologyEquiv.symm (Pi.single i 1) = classOf 1 x ∧
        reassoc.symm x.val.val = u i) ∧
    (∃ x : GhostSpace 0 2,
      ghostTwoCohomologyEquiv.symm 1 = classOf 2 x ∧ reassoc.symm x.val.val = w) := by
  refine ⟨⟨_, ghostZeroCohomologyEquiv_symm 1, ?_⟩,
    fun i => ⟨_, ghostOneCohomologyEquiv_symm (Pi.single i 1), representative_current i⟩,
    ⟨_, ghostTwoCohomologyEquiv_symm 1, ?_⟩⟩
  · exact (representative_zero 1).trans (one_smul ℂ v)
  · exact (representative_two 1).trans (one_smul ℂ w)

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeZeroMomentum
