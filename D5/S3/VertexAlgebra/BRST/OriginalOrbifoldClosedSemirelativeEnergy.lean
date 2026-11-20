/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedSemirelativeEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedSemirelativeEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native level-matched BRST energy contraction and transport of shell exactness. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelativeComparison

/-!
# Energy reduction of the native closed semirelative BRST complex

The left finite-support energy projection restricts to a chain retraction
onto the joint zero-energy shell. The sum antighost Ward identity and the
inverse left energy give a homotopy on level-matched states. The resulting
cohomology inverse is induced by the same projection on cycles.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldClosedSemirelativeEnergy

open D5.S3.HomologicalAlgebra.FinitePerturbation (Boundaries)
open OriginalOrbifoldCriticalMatter (Matter State Q b)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTZeroEnergy (fullBasis totalEnergy energyWeight energyWeight_coeff
  totalL0 totalL0_basis totalL0_coeff P0 EInv)
open OriginalOrbifoldClosedSemirelative
open OriginalOrbifoldClosedSemirelativeComparison
open private chiralL0_parity from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelative
open private chiralL0_b left_right left_twisted bPlus_semirelative_mem class_eq_zero_iff from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelativeComparison
open private energyWeight_basis from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
open private cycleMap cohomologyMap cohomologyMap_mk from
  D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev b0 : Module.End ℂ State := b 0

local notation "ℓ(" T ")" => LinearMap.rTensor State T
local notation "ρ(" T ")" => TensorProduct.map parity T

/-- A coefficient multiplier commutes with every map preserving the actual
chiral zero-mode eigenspaces. This uses the algebraic basis of the native state. -/
private lemma energyWeight_commute (weight : ℤ → ℂ) (T : Module.End ℂ State)
    (hT : totalL0 * T = T * totalL0) :
    energyWeight weight * T = T * energyWeight weight := by
  classical
  apply fullBasis.ext
  intro i
  change energyWeight weight (T (fullBasis i)) = T (energyWeight weight (fullBasis i))
  rw [energyWeight_basis, map_smul]
  apply fullBasis.repr.injective
  ext j
  rw [energyWeight_coeff, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases h : totalEnergy j = totalEnergy i
  · rw [h]
  · have he : totalL0 (T (fullBasis i)) = (totalEnergy i : ℂ) • T (fullBasis i) := by
      simpa only [Module.End.mul_apply, totalL0_basis, map_smul] using
        LinearMap.congr_fun hT (fullBasis i)
    have hcoeff := congrArg (fun x : State => fullBasis.repr x j) he
    change fullBasis.repr (totalL0 (T (fullBasis i))) j =
      fullBasis.repr ((totalEnergy i : ℂ) • T (fullBasis i)) j at hcoeff
    rw [totalL0_coeff, map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoeff
    have hz : fullBasis.repr (T (fullBasis i)) j = 0 := by
      by_contra hn
      exact h (Int.cast_injective (mul_right_cancel₀ hn hcoeff))
    rw [hz, mul_zero, mul_zero]

private abbrev J : Module.End ℂ ClosedState := ℓ(EInv)
/-- The original chiral zero-energy projection acting on the left factor. -/
abbrev energyProjection : Module.End ℂ ClosedState := ℓ(P0)

private lemma leftWeight_Q (w : ℤ → ℂ) :
    ℓ(energyWeight w) * closedQ = closedQ * ℓ(energyWeight w) := by
  have hP : totalL0 * parity = parity * totalL0 := LinearMap.ext chiralL0_parity
  have hQ := energyWeight_commute w Q OriginalOrbifoldBRSTZeroEnergy.Q_totalL0.symm
  change ℓ(energyWeight w) * (ℓ(Q) + ρ(Q)) =
    (ℓ(Q) + ρ(Q)) * ℓ(energyWeight w)
  rw [mul_add, add_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, hQ,
    left_twisted _ _ (energyWeight_commute w parity hP)]

private lemma leftWeight_semirelative (w : ℤ → ℂ) (z : ClosedState)
    (hz : z ∈ semirelativeStates) : ℓ(energyWeight w) z ∈ semirelativeStates := by
  have hP : totalL0 * parity = parity * totalL0 := LinearMap.ext chiralL0_parity
  have hb : ℓ(energyWeight w) * bMinus = bMinus * ℓ(energyWeight w) := by
    change ℓ(energyWeight w) * (ℓ(b0) - ρ(b0)) =
      (ℓ(b0) - ρ(b0)) * ℓ(energyWeight w)
    rw [mul_sub, sub_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul,
      energyWeight_commute w b0 chiralL0_b, left_twisted _ _ (energyWeight_commute w parity hP)]
  have hL : ℓ(energyWeight w) * LMinus = LMinus * ℓ(energyWeight w) := by
    change ℓ(energyWeight w) * (leftEnergy - rightEnergy) =
      (leftEnergy - rightEnergy) * ℓ(energyWeight w)
    rw [mul_sub, sub_mul, ← left_right (energyWeight w) totalL0,
      ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, energyWeight_commute w totalL0 rfl]
  obtain ⟨hzB, hzL⟩ := (mem_semirelativeStates _).mp hz
  exact (mem_semirelativeStates _).mpr
    ⟨by simpa only [Module.End.mul_apply, hzB, map_zero] using
        (LinearMap.congr_fun hb z).symm,
      by simpa only [Module.End.mul_apply, hzL, map_zero] using
        (LinearMap.congr_fun hL z).symm⟩

private lemma P_shell (z : semirelativeStates) : energyProjection z ∈ jointZeroShell := by
  refine ⟨leftWeight_semirelative _ _ z.property, ?_⟩
  have eq : leftEnergy * energyProjection = 0 := by
    rw [← LinearMap.rTensor_mul]
    have h : totalL0 * P0 = 0 := LinearMap.ext OriginalOrbifoldBRSTZeroEnergy.totalL0_P0
    rw [h, LinearMap.rTensor_zero]
  exact LinearMap.congr_fun eq (z : ClosedState)

private lemma P_fixed (z : jointZeroShell) : energyProjection (z : ClosedState) = z := by
  have hz : leftEnergy (z : ClosedState) = 0 := z.property.2
  have h : J * leftEnergy = 1 - energyProjection := by
    rw [← LinearMap.rTensor_mul, OriginalOrbifoldBRSTZeroEnergy.EInv_totalL0,
      LinearMap.rTensor_sub, show ℓ((1 : Module.End ℂ State)) = 1 from
        LinearMap.rTensor_id State State]
  have equality := LinearMap.congr_fun h (z : ClosedState)
  change J (leftEnergy z) = (z : ClosedState) - energyProjection z at equality
  rw [hz, map_zero] at equality
  exact (sub_eq_zero.mp equality.symm).symm

/-- The inverse common-energy multiplier is lifted from the left native
`EInv`. On matched states the two energies agree, so half this multiplier
is the inverse of their sum, extended by zero on their joint kernel. -/
def matchedHomotopy : Module.End ℂ ClosedState := (1 / 2 : ℂ) • (bPlus * J)

theorem matchedHomotopy_mem (z : semirelativeStates) :
    matchedHomotopy z ∈ semirelativeStates :=
  semirelativeStates.smul_mem _ (bPlus_semirelative_mem _ (leftWeight_semirelative _ _ z.property))

theorem matchedHomotopy_identity (z : semirelativeStates) :
    closedQ (matchedHomotopy z) + matchedHomotopy (closedQ (z : ClosedState)) =
      (z : ClosedState) - energyProjection z := by
  have hJ : J * closedQ = closedQ * J := leftWeight_Q _
  have h : closedQ * matchedHomotopy + matchedHomotopy * closedQ =
      (1 / 2 : ℂ) • (sumEnergy * J) := by
    unfold matchedHomotopy
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, ← sum_ward, add_mul]
    simp only [mul_assoc, hJ]
  have hl : leftEnergy * J = 1 - energyProjection := by
    rw [← LinearMap.rTensor_mul, OriginalOrbifoldBRSTZeroEnergy.totalL0_EInv,
      LinearMap.rTensor_sub, show ℓ((1 : Module.End ℂ State)) = 1 from
        LinearMap.rTensor_id State State]
  have hm : leftEnergy (J z) = rightEnergy (J z) :=
    sub_eq_zero.mp ((mem_semirelativeStates _).mp
      (leftWeight_semirelative _ _ z.property)).2
  have hs := LinearMap.congr_fun h (z : ClosedState)
  change closedQ (matchedHomotopy z) + matchedHomotopy (closedQ (z : ClosedState)) =
    (1 / 2 : ℂ) • (leftEnergy (J z) + rightEnergy (J z)) at hs
  rw [← hm, ← two_smul ℂ, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num,
    one_smul] at hs
  exact hs.trans (LinearMap.congr_fun hl (z : ClosedState))

/-- Native finite-support cycle reduction. The primitive stays semirelative. -/
theorem semirelative_cycle_reduction (z : semirelativeStates)
    (hz : closedQ (z : ClosedState) = 0) :
    energyProjection (z : ClosedState) ∈ jointZeroShell ∧ closedQ (energyProjection z) = 0 ∧
      matchedHomotopy (z : ClosedState) ∈ semirelativeStates ∧
      (z : ClosedState) - energyProjection z = closedQ (matchedHomotopy z) := by
  refine ⟨P_shell z, ?_, matchedHomotopy_mem z, ?_⟩
  · have h : energyProjection * closedQ = closedQ * energyProjection := leftWeight_Q _
    simpa only [Module.End.mul_apply, hz, map_zero] using
      (LinearMap.congr_fun h (z : ClosedState)).symm
  · simpa only [hz, map_zero, add_zero] using (matchedHomotopy_identity z).symm

/-- Applying the same projection to a semirelative primitive yields a genuine
joint-zero primitive for every joint-zero boundary. -/
theorem semirelative_boundary_reduction (x : jointZeroShell) (z : semirelativeStates)
    (h : closedQ (z : ClosedState) = x) :
    energyProjection (z : ClosedState) ∈ jointZeroShell ∧ closedQ (energyProjection z) = x := by
  refine ⟨P_shell z, ?_⟩
  have hP : energyProjection * closedQ = closedQ * energyProjection := leftWeight_Q _
  have eq := LinearMap.congr_fun hP (z : ClosedState)
  change energyProjection (closedQ (z : ClosedState)) = closedQ (energyProjection z) at eq
  rw [h, P_fixed x] at eq
  exact eq.symm

/-- The zero-energy projector with its actual joint-shell codomain. -/
def shellProjection : semirelativeStates →ₗ[ℂ] jointZeroShell :=
  (energyProjection.comp semirelativeStates.subtype).codRestrict jointZeroShell P_shell

/-- The inclusion of the joint-zero shell in the level-matched complex. -/
def shellToSemi : jointZeroShell →ₗ[ℂ] semirelativeStates :=
  Submodule.inclusion inf_le_left

theorem shellProjection_shellToSemi (x : jointZeroShell) :
    shellProjection (shellToSemi x) = x :=
  Subtype.ext (P_fixed x)

theorem shellProjection_chain :
    shellProjection.comp semirelativeDifferential = shellDifferential.comp shellProjection := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (leftWeight_Q _) (z : ClosedState)

theorem shellToSemi_chain :
    shellToSemi.comp shellDifferential = semirelativeDifferential.comp shellToSemi := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

local notation "Bₛ" => Boundaries shellDifferential shellDifferential_square
local notation "Bₘ" => Boundaries semirelativeDifferential semirelativeDifferential_square
local notation "includeCycle" =>
  cycleMap shellDifferential semirelativeDifferential shellToSemi shellToSemi_chain
local notation "projectCycle" =>
  cycleMap semirelativeDifferential shellDifferential shellProjection shellProjection_chain

private def shellToSemiClass : ShellCohomology →ₗ[ℂ] SemirelativeCohomology :=
  cohomologyMap shellDifferential semirelativeDifferential
    shellDifferential_square semirelativeDifferential_square shellToSemi shellToSemi_chain

private def semiToShellClass : SemirelativeCohomology →ₗ[ℂ] ShellCohomology :=
  cohomologyMap semirelativeDifferential shellDifferential
    semirelativeDifferential_square shellDifferential_square shellProjection shellProjection_chain

set_option maxHeartbeats 1800000 in
-- Elaborate the quotient representative with both native subtype maps.
private theorem project_include_class (x : ShellCohomology) :
    semiToShellClass (shellToSemiClass x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective Bₛ x
  change (Bₛ).mkQ (projectCycle (includeCycle z)) = (Bₛ).mkQ z
  exact congrArg (Bₛ).mkQ (Subtype.ext (shellProjection_shellToSemi z.1))

set_option maxHeartbeats 1800000 in
-- Elaborate the projected cycle and its native semirelative primitive.
private theorem include_project_class (x : SemirelativeCohomology) :
    shellToSemiClass (semiToShellClass x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective Bₘ x
  let y := includeCycle (projectCycle z)
  change (Bₘ).mkQ y = (Bₘ).mkQ z
  have hz : closedQ (z.1 : ClosedState) = 0 :=
    congrArg (fun v : semirelativeStates => (v : ClosedState)) z.property
  obtain ⟨_, _, hh, he⟩ := semirelative_cycle_reduction z.1 hz
  have hb : (Bₘ).mkQ (z - y) = 0 :=
    (class_eq_zero_iff _ _ _).mpr ⟨⟨matchedHomotopy z.1, hh⟩, Subtype.ext he.symm⟩
  rw [map_sub, sub_eq_zero] at hb
  exact hb.symm

/-- The inclusion and the actual energy projection induce inverse maps on
the native cohomology quotients. -/
def shellCohomologyEquiv : ShellCohomology ≃ₗ[ℂ] SemirelativeCohomology :=
  LinearEquiv.ofLinearMap shellToSemiClass semiToShellClass
    (LinearMap.ext include_project_class) (LinearMap.ext project_include_class)

theorem shellCohomologyEquiv_class (z : LinearMap.ker shellDifferential) :
    shellCohomologyEquiv ((Bₛ).mkQ z) = (Bₘ).mkQ (includeCycle z) := rfl

theorem shellCohomologyEquiv_symm_class (z : LinearMap.ker semirelativeDifferential) :
    shellCohomologyEquiv.symm ((Bₘ).mkQ z) = (Bₛ).mkQ (projectCycle z) := rfl

end

end D5.S3.VertexAlgebra.OriginalOrbifoldClosedSemirelativeEnergy
