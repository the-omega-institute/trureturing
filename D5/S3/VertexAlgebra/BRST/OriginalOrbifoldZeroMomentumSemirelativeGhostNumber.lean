import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldZeroMomentumSemirelativeSpectrum

/-! The occupation ghost number on the native zero-momentum semirelative shell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldZeroMomentumSemirelativeGhostNumber

noncomputable section

open D5.S3.Quantum.Fermionic
open OriginalOrbifoldCriticalMatter (Orbifold Hyperbolic Matter State)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldClosedSemirelative (ClosedState)
open OriginalOrbifoldChiralZeroModeConnection (zeroBasis)
open OriginalOrbifoldRelativeNull (ShellIndex bottom top ghostNumber ghostNumber_shellVector)
open OriginalOrbifoldRelativeQuartet (shellNumber)
open OriginalOrbifoldGhostDilaton
open OriginalOrbifoldZeroMomentumSemirelativeSpectrum
  (zeroShellCoordinates zeroShellCoordinates_apply zeroShellCoordinates_differential)

open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private c0 from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedSemirelative
open private cPlus_apply relativeInclusion include_tmul zeroBasis_val from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldGhostDilaton
open private raise raise_basis from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldChiralZeroModeConnection

local instance : AddCommGroup Matter := TensorProduct.addCommGroup (M := Orbifold) (N := Hyperbolic)
local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)
local instance : AddCommGroup ClosedState := TensorProduct.addCommGroup (M := State)
local instance : AddCommGroup ZeroRelativeTensor :=
  TensorProduct.addCommGroup (M := ↥ZeroChiralShell)

private abbrev chiralNumber : Module.End ℂ State := VirasoroBRST.number (V := Matter)
private abbrev chiralShellNumber : Module.End ℂ ZeroChiralShell := shellNumber 0

private theorem chiralNumber_c0 (x : State) :
    chiralNumber (c0 x) = c0 (chiralNumber x) + c0 x := by
  have h : chiralNumber * c0 - c0 * chiralNumber = c0 := by
    apply TensorProduct.ext'
    intro v w
    have hw := LinearMap.congr_fun (BcGhostCharge.ghost_number_relations.2.2 0) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hw
    simp only [chiralNumber, c0, VirasoroBRST.number, VirasoroBRST.ghostC,
      BcGhostChargeTensor.number, BcGhostChargeTensor.C, BcGhostChargeTensor.liftGhost,
      LinearMap.sub_apply, Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [← TensorProduct.tmul_sub, hw]
  exact (sub_eq_iff_eq_add.mp (LinearMap.congr_fun h x)).trans (add_comm _ _)

private theorem chiralNumber_parity (x : State) :
    chiralNumber (parity x) = parity (chiralNumber x) := by
  have hF : BcGhostCharge.ghostNumber.comp CountableOccupationFock.parity =
      CountableOccupationFock.parity.comp BcGhostCharge.ghostNumber := by
    apply CountableOccupationFock.end_ext
    intro s
    simp only [LinearMap.comp_apply, number_ket, parity_ket, map_smul, smul_smul]
    rw [mul_comm]
  have h : chiralNumber.comp parity = parity.comp chiralNumber := by
    apply TensorProduct.ext'
    intro v w
    simp only [LinearMap.comp_apply, chiralNumber, VirasoroBRST.number,
      BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost, parity,
      TensorProduct.map_tmul, LinearMap.id_apply]
    exact congrArg (fun z => v ⊗ₜ[ℂ] z) (LinearMap.congr_fun hF w)
  exact LinearMap.congr_fun h x

/-- Total ghost number on the closed tensor state space. -/
def closedGhostNumber : Module.End ℂ ClosedState :=
  TensorProduct.map chiralNumber LinearMap.id + TensorProduct.map LinearMap.id chiralNumber

private theorem closedGhostNumber_tmul (x y : State) :
    closedGhostNumber (x ⊗ₜ[ℂ] y) =
      chiralNumber x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] chiralNumber y := by
  simp only [closedGhostNumber, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]

/-- The native normalized sum ghost raises total ghost number by one. -/
theorem closedGhostNumber_cPlus :
    closedGhostNumber * cPlus - cPlus * closedGhostNumber = cPlus := by
  apply sub_eq_iff_eq_add.mpr
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, LinearMap.add_apply, cPlus_apply, closedGhostNumber_tmul,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul, map_smul, map_add, chiralNumber_c0,
    chiralNumber_parity, TensorProduct.add_tmul, TensorProduct.tmul_add, ← smul_add]
  congr 1
  abel

/-- Sum of the two native restricted chiral occupation operators. -/
def zeroRelativeGhostNumber : Module.End ℂ ZeroRelativeTensor :=
  TensorProduct.map chiralShellNumber LinearMap.id +
    TensorProduct.map LinearMap.id chiralShellNumber

private theorem closedGhostNumber_include (u : ZeroRelativeTensor) :
    closedGhostNumber (relativeInclusion u) = relativeInclusion (zeroRelativeGhostNumber u) := by
  have h : closedGhostNumber.comp relativeInclusion =
      relativeInclusion.comp zeroRelativeGhostNumber := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, include_tmul, closedGhostNumber_tmul,
      zeroRelativeGhostNumber, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      map_add]
    rfl
  exact LinearMap.congr_fun h u

private theorem closedGhostNumber_coordinates (u v : ZeroRelativeTensor) :
    closedGhostNumber (zeroShellCoordinates (u, v) : ClosedState) =
      (zeroShellCoordinates (zeroRelativeGhostNumber u, zeroRelativeGhostNumber v + v) :
        ClosedState) := by
  have h (z : ClosedState) :
      closedGhostNumber (cPlus z) = cPlus (closedGhostNumber z) + cPlus z :=
    (sub_eq_iff_eq_add.mp (LinearMap.congr_fun closedGhostNumber_cPlus z)).trans (add_comm _ _)
  simp only [zeroShellCoordinates_apply, map_add, h, closedGhostNumber_include]

theorem closedGhostNumber_mem_zeroMomentumShell (z : ClosedState) (hz : z ∈ zeroMomentumShell) :
    closedGhostNumber z ∈ zeroMomentumShell := by
  obtain ⟨⟨u, v⟩, huv⟩ := zeroShellCoordinates.surjective (⟨z, hz⟩ : zeroMomentumShell)
  have h : (zeroShellCoordinates (u, v) : ClosedState) = z :=
    congrArg (fun w : zeroMomentumShell => (w : ClosedState)) huv
  rw [← h, closedGhostNumber_coordinates]
  exact (zeroShellCoordinates _).property

/-- The closed occupation ghost number restricted to the actual semirelative shell. -/
def zeroShellGhostNumber : Module.End ℂ zeroMomentumShell :=
  closedGhostNumber.restrict closedGhostNumber_mem_zeroMomentumShell

theorem zeroShellGhostNumber_coordinates (u v : ZeroRelativeTensor) :
    zeroShellGhostNumber (zeroShellCoordinates (u, v)) =
      zeroShellCoordinates (zeroRelativeGhostNumber u, zeroRelativeGhostNumber v + v) := by
  apply Subtype.ext
  exact closedGhostNumber_coordinates u v

private theorem chiralShellNumber_basis (i : ShellIndex) :
    chiralShellNumber (zeroBasis i) = (ghostNumber i : ℂ) • zeroBasis i := by
  apply Subtype.ext
  change chiralNumber (zeroBasis i : State) = (ghostNumber i : ℂ) • (zeroBasis i : State)
  rw [zeroBasis_val]
  exact ghostNumber_shellVector 0 i

private theorem chiralShellNumber_raise (x : ZeroChiralShell) :
    chiralShellNumber (raise x) = raise (chiralShellNumber x) + (2 : ℂ) • raise x := by
  have h : chiralShellNumber * raise = raise * chiralShellNumber + (2 : ℂ) • raise := by
    apply zeroBasis.ext
    intro i
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      chiralShellNumber_basis, map_smul, raise_basis]
    by_cases hi : i = bottom
    · subst i
      have hb : (ghostNumber bottom : ℂ) = 0 := by norm_num [ghostNumber, bottom]
      have ht : (ghostNumber top : ℂ) = 2 := by norm_num [ghostNumber, top]
      simp only [ite_true, chiralShellNumber_basis, hb, ht, zero_smul, zero_add]
    · simp only [ite_eq_right hi, map_zero, smul_zero, add_zero]
  exact LinearMap.congr_fun h x

/-- The native connection sends relative ghost number `n` to `n + 2`. -/
theorem zeroRelativeGhostNumber_connection :
    zeroRelativeGhostNumber * zeroShellConnection =
      zeroShellConnection * zeroRelativeGhostNumber + (2 : ℂ) • zeroShellConnection := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    zeroRelativeGhostNumber, zeroShellConnection, TensorProduct.map_tmul, LinearMap.id_apply,
    map_add, chiralShellNumber_raise, TensorProduct.add_tmul, TensorProduct.tmul_add,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
  abel

/-- The actual zero-momentum semirelative BRST differential has ghost number one. -/
theorem zeroShellGhostNumber_differential :
    zeroShellGhostNumber * zeroShellDifferential =
      zeroShellDifferential * zeroShellGhostNumber + zeroShellDifferential := by
  apply LinearMap.ext
  intro z
  obtain ⟨⟨u, v⟩, rfl⟩ := zeroShellCoordinates.surjective z
  simp only [Module.End.mul_apply, LinearMap.add_apply, zeroShellCoordinates_differential,
    zeroShellGhostNumber_coordinates, map_zero, add_zero]
  rw [← zeroShellCoordinates.map_add]
  refine congrArg zeroShellCoordinates (Prod.ext ?_ ?_)
  · change zeroRelativeGhostNumber (zeroShellConnection v) =
      zeroShellConnection (zeroRelativeGhostNumber v + v) + zeroShellConnection v
    have h := LinearMap.congr_fun zeroRelativeGhostNumber_connection v
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
    rw [h, map_add, two_smul, add_assoc]
  · exact (add_zero (0 : ZeroRelativeTensor)).symm

#print axioms closedGhostNumber_cPlus
#print axioms zeroShellGhostNumber_coordinates
#print axioms zeroRelativeGhostNumber_connection
#print axioms zeroShellGhostNumber_differential

end

end D5.S3.VertexAlgebra.OriginalOrbifoldZeroMomentumSemirelativeGhostNumber
