/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTQuartetReal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTQuartetReal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original real-frame quartet homotopy commutes with chain conjugation. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTChainReal
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRealNullFrame

/-! Conjugation of the native quartet operators and the original relative shell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTQuartetReal

open OriginalOrbifoldCriticalMatter (Matter State Orbifold Hyperbolic hyperbolicData)
open OriginalBRSTWeightPositive (orbifoldConjugation)
open OriginalOrbifoldBRSTChainReal (stateConjugation stateConjugation_Q
  stateConjugation_mem_relativeStates)
open OriginalOrbifoldRealNullFrame (IsRealFrame pPlus_real)
open OriginalOrbifoldBRSTMomentum (momentumZeroMode mem_fixedMomentum_iff_zero_modes)
open OriginalOrbifoldRelativeMassShell (fixedMomentum relativeMassShell differential)
open OriginalOrbifoldRelativeQuartet (Frame UCharge UState transverseBasis shellD0 shellH lift)
open LatticeGeneratingFieldLocality (LatticeData Carrier Oscillator)
open LatticeFiniteNegativeGeneration (neutralMode)
open LatticeLightConeCoordinates (E lin)
open LatticeLightConeCoordinates.NullFrame (Label plus minus pPlus)
open LatticeRealNullFrame (conjugateVector)
open LatticeQuartetContraction (tp tp_tmul sector actualBasis actualBasis_apply
  StateIndex Exponents totalCount d0 invM h dTerm rTerm dm rr dFamily rFamily
  unscaledD unscaledR)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
  (Family diagonal_basis)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock ket)
open OriginalOrbifoldBRSTGhostBilinear (kappa_b kappa_c kappa_ket)
open SourceBPZ.OriginalMatterHermitian (kappaCarrier kappaCarrier_single
  kappaCarrier_neutralMode kappaOsc kappaOsc_smul kappaOsc_X kappaOsc_coeff)
open MvPolynomial (X monomial monomial_eq C_1)

open private polynomialEquiv_symm_X completeBasis_plus completeBasis_minus from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private carrierConjugation from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldVirasoroReal
open private ghostConjugation from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTChainReal
open private assoc lift_assoc_tmul from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeShellQuartet
open private delta from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeQuartet
open private momentumZeroMode_tensor from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum
open private mem_shell from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalSpectrum

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem completeBasis_real (F : Frame) (hF : IsRealFrame F) (j : Label 0) :
    conjugateVector (F.completeBasis (transverseBasis F) j) =
      F.completeBasis (transverseBasis F) j := by
  rcases j with ⟨⟩ | j
  · change conjugateVector (F.completeBasis (transverseBasis F) (plus 0)) =
      F.completeBasis (transverseBasis F) (plus 0)
    simpa only [completeBasis_plus] using hF.1
  · rcases j with ⟨⟩ | j
    · change conjugateVector (F.completeBasis (transverseBasis F) (minus 0)) =
        F.completeBasis (transverseBasis F) (minus 0)
      simpa only [completeBasis_minus] using hF.2
    · exact Fin.elim0 j

private theorem kappaOsc_lin (r : ℕ) (z : E hyperbolicData)
    (hz : conjugateVector z = z) : kappaOsc (lin r z) = lin r z := by
  classical
  change MvPolynomial.map (starRingEnd ℂ) (∑ i, z i • (X (i, r) : Oscillator hyperbolicData)) =
    ∑ i, z i • (X (i, r) : Oscillator hyperbolicData)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change kappaOsc (z i • (X (i, r) : Oscillator hyperbolicData)) = z i • X (i, r)
  have hi : starRingEnd ℂ (z i) = z i := congrFun hz i
  rw [kappaOsc_smul, kappaOsc_X, hi]

private theorem kappaOsc_frameMonomial (F : Frame) (hF : IsRealFrame F) (d : Exponents 0) :
    kappaOsc ((F.coordinateEquiv (transverseBasis F)).symm (monomial d 1)) =
      (F.coordinateEquiv (transverseBasis F)).symm (monomial d 1) := by
  classical
  let A := (F.coordinateEquiv (transverseBasis F)).symm
  have hx (k : Label 0 × ℕ) :
      MvPolynomial.map (starRingEnd ℂ) (A (X k)) = A (X k) := by
    rcases k with ⟨j, r⟩
    change kappaOsc ((LatticeLightConeCoordinates.polynomialEquiv
      (F.completeBasis (transverseBasis F))).symm (X (j, r))) = _
    rw [polynomialEquiv_symm_X]
    exact kappaOsc_lin r _ (completeBasis_real F hF j)
  change MvPolynomial.map (starRingEnd ℂ) (A (monomial d 1)) = A (monomial d 1)
  simp only [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, map_pow, hx]

def uConjugation : UState →ₗ⋆[ℂ] UState :=
  TensorProduct.map (carrierConjugation hyperbolicData) ghostConjugation

private theorem uConjugation_tmul (v : Hyperbolic) (w : Fock) :
    uConjugation (v ⊗ₜ[ℂ] w) =
      kappaCarrier v ⊗ₜ[ℂ] ghostConjugation w :=
  TensorProduct.map_tmul _ _ _ _

private theorem uConjugation_actualBasis (F : Frame) (hF : IsRealFrame F)
    (i : StateIndex hyperbolicData 0) :
    uConjugation (actualBasis F (transverseBasis F) i) =
      actualBasis F (transverseBasis F) i := by
  rcases i with ⟨⟨a, d⟩, S⟩
  rw [actualBasis_apply, sector, uConjugation_tmul, kappaCarrier_single,
    kappaOsc_frameMonomial F hF d, show ghostConjugation (ket S) = ket S from kappa_ket S]

private theorem uConjugation_tp (A : Module.End ℂ Hyperbolic) (G : Module.End ℂ Fock)
    (hA : Function.Commute kappaCarrier A) (hG : Function.Commute ghostConjugation G) :
    Function.Commute uConjugation (tp A G) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul v w => simp only [tp_tmul, uConjugation_tmul, hA v, hG w]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem kappaCarrier_current {D : LatticeData} (z : E D) (hz : conjugateVector z = z)
    (m : ℤ) : Function.Commute kappaCarrier (LatticeLightConeCoordinates.a z m) := by
  classical
  intro x
  change carrierConjugation D ((LatticeLightConeCoordinates.a z m) x) =
    (LatticeLightConeCoordinates.a z m) (carrierConjugation D x)
  simp only [LatticeLightConeCoordinates.a, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [map_sum (carrierConjugation D)]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.map_smulₛₗ]
  have hi : starRingEnd ℂ (z i) = z i := congrFun hz i
  rw [hi]
  exact congrArg (fun y : Carrier D => z i • y) (kappaCarrier_neutralMode i m x)

private theorem uConjugation_dTerm (F : Frame) (hF : IsRealFrame F) (r : ℕ) :
    Function.Commute uConjugation (dTerm F r) := by
  have ht (n : ℤ) : Function.Commute uConjugation (dm F n) :=
    uConjugation_tp _ _ (kappaCarrier_current F.eMinus hF.2 n) (kappa_c (-n))
  intro x
  simp only [dTerm, LinearMap.add_apply, map_add,
    ht ((r : ℤ) + 1) x, ht (-((r : ℤ) + 1)) x]

private theorem uConjugation_rTerm (F : Frame) (hF : IsRealFrame F) (r : ℕ) :
    Function.Commute uConjugation (rTerm F r) := by
  have ht (n : ℤ) : Function.Commute uConjugation (rr F n) :=
    uConjugation_tp _ _ (kappaCarrier_current F.ePlus hF.1 (-n)) (kappa_b n)
  have hs : starRingEnd ℂ ((r + 1 : ℂ)⁻¹) = (r + 1 : ℂ)⁻¹ := by
    simp only [map_inv₀, map_add, map_natCast, map_one]
  intro x
  simp only [rTerm, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.map_smulₛₗ,
    hs, map_add, ht ((r : ℤ) + 1) x, ht (-((r : ℤ) + 1)) x]

private theorem uConjugation_total (A : Family UState)
    (hA : ∀ r, Function.Commute uConjugation (A.term r)) :
    Function.Commute uConjugation A.total := by
  intro x
  let n := max (A.bound x) (A.bound (uConjugation x))
  rw [A.total_eq_sum x n (le_max_left _ _),
    A.total_eq_sum (uConjugation x) n (le_max_right _ _), map_sum]
  exact Finset.sum_congr rfl (fun r _ => hA r x)

/-- The two signed b-current terms per frequency and the light-cone denominator
are preserved by coefficient conjugation on the native tensor. -/
private theorem uConjugation_R (F : Frame) (hF : IsRealFrame F) (a : UCharge) :
    Function.Commute uConjugation (LatticeQuartetContraction.R F a) := by
  have ht : Function.Commute uConjugation (unscaledR F) :=
    uConjugation_total (rFamily F) (uConjugation_rTerm F hF)
  intro x
  simp only [LatticeQuartetContraction.R, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    ht x, map_inv₀, pPlus_real F hF a]

private theorem uConjugation_d0 (F : Frame) (hF : IsRealFrame F) (a : UCharge) :
    Function.Commute uConjugation (d0 F a) := by
  have ht : Function.Commute uConjugation (unscaledD F) :=
    uConjugation_total (dFamily F) (uConjugation_dTerm F hF)
  intro x
  simp only [d0, LinearMap.smul_apply, LinearMap.map_smulₛₗ, ht x, pPlus_real F hF a]

/-- The eigenvalue of the original inverse-count operator is either zero or the
real reciprocal of the original natural quartet count. -/
private theorem uConjugation_invM (F : Frame) (hF : IsRealFrame F) :
    Function.Commute uConjugation (invM F (transverseBasis F)) := by
  let A := invM F (transverseBasis F)
  let B := actualBasis F (transverseBasis F)
  have he : uConjugation.comp A = A.comp uConjugation := by
    apply B.ext
    intro i
    change uConjugation (A (B i)) = A (uConjugation (B i))
    have hB : uConjugation (B i) = B i := uConjugation_actualBasis F hF i
    have hA : A (B i) = (if totalCount i = 0 then 0 else (totalCount i : ℂ)⁻¹) • B i :=
      diagonal_basis B _ i
    rw [hB, hA, LinearMap.map_smulₛₗ, hB]
    by_cases hi : totalCount i = 0 <;> simp [hi, map_inv₀]
  exact fun x => LinearMap.congr_fun he x

theorem uConjugation_h (F : Frame) (hF : IsRealFrame F) (a : UCharge) :
    Function.Commute uConjugation (h F (transverseBasis F) a) := by
  intro x
  change uConjugation (LatticeQuartetContraction.R F a (invM F (transverseBasis F) x)) =
    LatticeQuartetContraction.R F a (invM F (transverseBasis F) (uConjugation x))
  rw [uConjugation_R F hF a (invM F (transverseBasis F) x), uConjugation_invM F hF x]

theorem stateConjugation_tmul (u : Orbifold) (v : Hyperbolic) (w : Fock) :
    stateConjugation ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) =
      (orbifoldConjugation u ⊗ₜ[ℂ] kappaCarrier v) ⊗ₜ[ℂ] ghostConjugation w := by
  simp only [stateConjugation, OriginalOrbifoldVirasoroReal.matterConjugation,
    TensorProduct.map_tmul]
  rfl

private theorem stateConjugation_assoc_tmul (u : Orbifold) (v : UState) :
    stateConjugation (assoc.symm (u ⊗ₜ[ℂ] v)) =
      assoc.symm (orbifoldConjugation u ⊗ₜ[ℂ] uConjugation v) := by
  induction v using TensorProduct.inductionOn with
  | tmul x y =>
      simp only [uConjugation_tmul, TensorProduct.assoc_symm_tmul, stateConjugation_tmul]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

private theorem stateConjugation_lift (A : Module.End ℂ UState)
    (hA : Function.Commute uConjugation A) :
    Function.Commute stateConjugation (lift A) := by
  have he : (stateConjugation.comp (lift A)).comp assoc.symm.toLinearMap =
      ((lift A).comp stateConjugation).comp assoc.symm.toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change stateConjugation (lift A (assoc.symm (u ⊗ₜ[ℂ] v))) =
      lift A (stateConjugation (assoc.symm (u ⊗ₜ[ℂ] v)))
    rw [lift_assoc_tmul, stateConjugation_assoc_tmul, stateConjugation_assoc_tmul,
      lift_assoc_tmul, hA v]
  intro x
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun he (assoc x)

private theorem stateConjugation_momentumZeroMode (i : Fin hyperbolicData.rank) :
    Function.Commute stateConjugation (momentumZeroMode i) := by
  intro x
  rw [momentumZeroMode_tensor]
  induction x using TensorProduct.inductionOn with
  | tmul y w =>
    induction y using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.id_apply,
        stateConjugation_tmul, kappaCarrier_neutralMode]
    | add y z hy hz =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hy hz
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Native coefficient conjugation preserves the joint real momentum eigenvalues. -/
theorem stateConjugation_mem_fixedMomentum (a : UCharge) (x : State)
    (hx : x ∈ fixedMomentum a) : stateConjugation x ∈ fixedMomentum a := by
  apply (mem_fixedMomentum_iff_zero_modes a _).mpr
  intro i
  rw [← stateConjugation_momentumZeroMode i x, (mem_fixedMomentum_iff_zero_modes a x).mp hx i,
    LinearMap.map_smulₛₗ, map_intCast]

/-- The native BRST conjugation restricts to the same relative shell at charge a. -/
def shellConjugation (a : UCharge) : relativeMassShell a →ₗ⋆[ℂ] relativeMassShell a :=
  stateConjugation.restrict (by
    intro x hx
    have h := (mem_shell a x).mp hx
    exact (mem_shell a _).mpr
      ⟨stateConjugation_mem_fixedMomentum a x h.1,
        stateConjugation_mem_relativeStates x h.2⟩)

theorem shellConjugation_shellH (F : Frame) (hF : IsRealFrame F) (a : UCharge) :
    Function.Commute (shellConjugation a) (shellH F a) := by
  intro x
  apply Subtype.ext
  exact stateConjugation_lift _ (uConjugation_h F hF a) (x : State)

private theorem shellConjugation_shellD0 (F : Frame) (hF : IsRealFrame F) (a : UCharge) :
    Function.Commute (shellConjugation a) (shellD0 F a) := by
  intro x
  apply Subtype.ext
  exact stateConjugation_lift _ (uConjugation_d0 F hF a) (x : State)

private theorem shellConjugation_differential (a : UCharge) :
    Function.Commute (shellConjugation a) (differential a) := by
  intro x
  exact Subtype.ext (stateConjugation_Q (x : State))

theorem shellConjugation_delta (F : Frame) (hF : IsRealFrame F) (a : UCharge) :
    Function.Commute (shellConjugation a) (delta F a) := by
  intro x
  change shellConjugation a (differential a x - shellD0 F a x) =
    differential a (shellConjugation a x) - shellD0 F a (shellConjugation a x)
  rw [map_sub, shellConjugation_differential a x, shellConjugation_shellD0 F hF a x]

#print axioms uConjugation_h
#print axioms shellConjugation_shellH
#print axioms shellConjugation_delta

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTQuartetReal
