import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldVirasoroReal
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostBilinear
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTContravariant

/-!
Conjugation of the native orbifold, hyperbolic, and bc state and its descent to
the native relative quotient. The orbifold and hyperbolic mode commutation
lemmas come from the verified OriginalOrbifoldVirasoroReal module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTChainReal

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)
open OriginalBRSTWeightPositive (orbifoldConjugation_involutive)
open OriginalOrbifoldVirasoroReal (matterConjugation matterConjugation_commutes_mode)
open OriginalOrbifoldCriticalMatter (Hyperbolic Matter State mode matterDatum Q b)
open OriginalOrbifoldBRSTGhostBilinear (kappa kappa_smul kappa_kappa kappa_ket
  kappa_b kappa_c kappa_Qg)
open OriginalOrbifoldBRSTDescent
  (relativeStates relativeDifferential relativeDifferential_square relativeCycles
    relativeBoundaries RelativeCohomology)
open OriginalOrbifoldBRSTPhysicalLie (N cycleNumber cohomologyNumber cohomologyNumber_mk
  grade DegreeOne)
open OriginalOrbifoldBRSTContravariant (contravariantBPZ)
open OriginalOrbifoldBRSTZeroEnergy (totalL0)
open SourceBPZ.OriginalMatterHermitian
  (kappaCarrier_involutive)
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private def ghostConjugation : Fock →ₗ⋆[ℂ] Fock where
  toFun := kappa
  map_add' := kappa.map_add
  map_smul' := kappa_smul

/-- Conjugate the actual matter tensor and the signed occupation Fock space. -/
def stateConjugation : State →ₗ⋆[ℂ] State :=
  TensorProduct.map matterConjugation ghostConjugation

private theorem matterConjugation_involutive : Function.Involutive matterConjugation := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      simp only [matterConjugation, TensorProduct.map_tmul, orbifoldConjugation_involutive v]
      exact congrArg (fun z : Hyperbolic => v ⊗ₜ[ℂ] z) (kappaCarrier_involutive w)
  | add u v hu hv => simp only [map_add, hu, hv]

theorem stateConjugation_involutive : Function.Involutive stateConjugation := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      simp only [stateConjugation, TensorProduct.map_tmul, matterConjugation_involutive v]
      exact congrArg (fun z : Fock => v ⊗ₜ[ℂ] z) (kappa_kappa w)
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem conjugate_intCast (n : ℤ) :
    starRingEnd ℂ (n : ℂ) = (n : ℂ) :=
  star_intCast n

private theorem ghostConjugation_number (x : Fock) :
    ghostConjugation (BcGhostCharge.ghostNumber x) =
      BcGhostCharge.ghostNumber (ghostConjugation x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | single S a =>
      have hs : Finsupp.single S a = a • ket S := by simp [ket]
      have hk : ghostConjugation (ket S) = ket S := kappa_ket S
      rw [hs]
      simp only [map_smul, LinearMap.map_smulₛₗ, number_ket, hk,
        conjugate_intCast]

private theorem stateConjugation_tensorMap (M : Module.End ℂ Matter)
    (G : Module.End ℂ Fock) (hM : Function.Commute matterConjugation M)
    (hG : Function.Commute ghostConjugation G) :
    Function.Commute stateConjugation (TensorProduct.map M G) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      simp only [stateConjugation, TensorProduct.map_tmul, hM v, hG w]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem stateConjugation_b (r : ℤ) :
    Function.Commute stateConjugation (b r) :=
  stateConjugation_tensorMap LinearMap.id (BcGhostFock.b r) (fun _ => rfl) (kappa_b r)

theorem stateConjugation_N : Function.Commute stateConjugation N :=
  stateConjugation_tensorMap LinearMap.id BcGhostCharge.ghostNumber (fun _ => rfl)
    ghostConjugation_number

private theorem stateConjugation_ghostCharge :
    Function.Commute stateConjugation (VirasoroBRST.ghostCharge matterDatum) :=
  stateConjugation_tensorMap LinearMap.id BcGhostBRST.Qg (fun _ => rfl) kappa_Qg

private theorem stateConjugation_summand (m : ℤ) :
    Function.Commute stateConjugation (VirasoroBRST.summand matterDatum m) :=
  stateConjugation_tensorMap (mode m) (BcGhostFock.c (-m))
    (matterConjugation_commutes_mode m) (kappa_c (-m))

private theorem stateConjugation_T (x : State) :
    stateConjugation (VirasoroBRST.T matterDatum x) =
      VirasoroBRST.T matterDatum (stateConjugation x) := by
  classical
  obtain ⟨s, hs⟩ := VirasoroBRST.common_capture matterDatum {x, stateConjugation x}
  have hx := hs x (by simp)
  have hconj := hs (stateConjugation x) (by simp)
  rw [VirasoroBRST.finite_capture matterDatum x s hx,
    VirasoroBRST.finite_capture matterDatum (stateConjugation x) s hconj, map_sum]
  exact Finset.sum_congr rfl (fun m _ => stateConjugation_summand m x)

/-- Commutation with the literal charge T plus the lifted cubic ghost charge. -/
theorem stateConjugation_Q :
    Function.Commute stateConjugation Q := by
  intro x
  simp only [OriginalOrbifoldCriticalMatter.Q, VirasoroBRST.Q, LinearMap.add_apply,
    map_add, stateConjugation_T x, stateConjugation_ghostCharge x]

/-- The antighost Ward identity gives commutation on the full carrier. -/
theorem stateConjugation_L0 :
    Function.Commute stateConjugation totalL0 := by
  intro x
  have ward (y : State) : Q (b 0 y) + b 0 (Q y) = totalL0 y :=
    LinearMap.congr_fun (VirasoroBRST.Q_ward_b matterDatum 0) y
  rw [← ward x, ← ward (stateConjugation x), map_add,
    stateConjugation_Q (b 0 x), stateConjugation_b 0 x,
    stateConjugation_b 0 (Q x), stateConjugation_Q x]

theorem stateConjugation_mem_relativeStates
    (x : State) (hx : x ∈ relativeStates) :
    stateConjugation x ∈ relativeStates := by
  change b 0 x = 0 ∧ totalL0 x = 0 at hx
  change b 0 (stateConjugation x) = 0 ∧ totalL0 (stateConjugation x) = 0
  exact ⟨by rw [← stateConjugation_b 0 x, hx.1, map_zero],
    by rw [← stateConjugation_L0 x, hx.2, map_zero]⟩

/-- Restriction to the native two-kernel submodule. -/
def relativeConjugation : relativeStates →ₗ⋆[ℂ] relativeStates :=
  stateConjugation.restrict stateConjugation_mem_relativeStates

theorem relativeConjugation_involutive :
    Function.Involutive relativeConjugation :=
  fun x => Subtype.ext (stateConjugation_involutive (x : State))

theorem relativeConjugation_differential :
    Function.Commute relativeConjugation relativeDifferential := by
  intro x
  exact Subtype.ext (stateConjugation_Q (x : State))

/-- Restriction to the kernel of the actual relative differential. -/
def cycleConjugation : relativeCycles →ₗ⋆[ℂ] relativeCycles :=
  relativeConjugation.restrict (by
    intro x hx
    have hclosed := LinearMap.mem_ker.mp hx
    apply LinearMap.mem_ker.mpr
    rw [← relativeConjugation_differential x, hclosed, map_zero])

theorem cycleConjugation_involutive :
    Function.Involutive cycleConjugation :=
  fun x => Subtype.ext (relativeConjugation_involutive x.1)

/-- A boundary goes to the boundary of the conjugated relative primitive. -/
theorem cycleConjugation_mem_relativeBoundaries
    (x : relativeCycles) (hx : x ∈ relativeBoundaries) :
    cycleConjugation x ∈ relativeBoundaries := by
  change ∃ z, boundaryMap relativeDifferential relativeDifferential_square z = x at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨relativeConjugation z, Subtype.ext ?_⟩
  exact (relativeConjugation_differential z).symm

/-- Semilinear descent through the native boundary submodule. -/
def cohomologyConjugation : RelativeCohomology →ₗ⋆[ℂ] RelativeCohomology :=
  relativeBoundaries.mapQ relativeBoundaries cycleConjugation (by
    intro x hx
    exact cycleConjugation_mem_relativeBoundaries x hx)

theorem cohomologyConjugation_mk (x : relativeCycles) :
    cohomologyConjugation (relativeBoundaries.mkQ x) =
      relativeBoundaries.mkQ (cycleConjugation x) := rfl

theorem cohomologyConjugation_involutive :
    Function.Involutive cohomologyConjugation := by
  intro a
  obtain ⟨x, rfl⟩ := relativeBoundaries.mkQ_surjective a
  calc
    cohomologyConjugation (cohomologyConjugation (relativeBoundaries.mkQ x)) =
        cohomologyConjugation (relativeBoundaries.mkQ (cycleConjugation x)) :=
      congrArg (fun z : RelativeCohomology => cohomologyConjugation z)
        (cohomologyConjugation_mk x)
    _ = relativeBoundaries.mkQ (cycleConjugation (cycleConjugation x)) :=
      cohomologyConjugation_mk (cycleConjugation x)
    _ = relativeBoundaries.mkQ x :=
      congrArg (fun z : relativeCycles => relativeBoundaries.mkQ z)
        (cycleConjugation_involutive x)

private theorem cycleConjugation_number (x : relativeCycles) :
    cycleConjugation (cycleNumber x) = cycleNumber (cycleConjugation x) :=
  Subtype.ext (Subtype.ext (stateConjugation_N (x.1 : State)))

theorem cohomologyConjugation_number :
    Function.Commute cohomologyConjugation cohomologyNumber := by
  intro a
  obtain ⟨x, rfl⟩ := relativeBoundaries.mkQ_surjective a
  simp only [cohomologyNumber_mk, cohomologyConjugation_mk, cycleConjugation_number]

set_option backward.isDefEq.respectTransparency true in
theorem cohomologyConjugation_mem_grade (p : ℤ)
    (x : RelativeCohomology) (hx : x ∈ grade p) :
    cohomologyConjugation x ∈ grade p := by
  have hxN : cohomologyNumber x = (p : ℂ) • x :=
    (Module.End.mem_eigenspace_iff (f := cohomologyNumber)).mp hx
  apply (Module.End.mem_eigenspace_iff (f := cohomologyNumber)).mpr
  calc
    cohomologyNumber (cohomologyConjugation x) =
        cohomologyConjugation (cohomologyNumber x) := (cohomologyConjugation_number x).symm
    _ = cohomologyConjugation ((p : ℂ) • x) :=
      congrArg (fun z : RelativeCohomology => cohomologyConjugation z) hxN
    _ = (p : ℂ) • cohomologyConjugation x := by
      rw [LinearMap.map_smulₛₗ, conjugate_intCast]

/-- The induced conjugation on the actual ghost-number-one relative cohomology. -/
def degreeOneConjugation : DegreeOne →ₗ⋆[ℂ] DegreeOne :=
  cohomologyConjugation.restrict (cohomologyConjugation_mem_grade 1)

theorem degreeOneConjugation_involutive :
    Function.Involutive degreeOneConjugation :=
  fun x => Subtype.ext (cohomologyConjugation_involutive (x : RelativeCohomology))

/-- The native contravariant BPZ form with conjugation in the first slot. -/
def degreeOneSesquilinear : DegreeOne →ₗ⋆[ℂ] DegreeOne →ₗ[ℂ] ℂ :=
  LinearMap.comp contravariantBPZ degreeOneConjugation

#print axioms stateConjugation_involutive
#print axioms stateConjugation_Q
#print axioms stateConjugation_b
#print axioms stateConjugation_L0
#print axioms stateConjugation_N
#print axioms relativeConjugation_differential
#print axioms cohomologyConjugation_mk
#print axioms cohomologyConjugation_involutive
#print axioms cohomologyConjugation_number
#print axioms degreeOneConjugation
#print axioms degreeOneConjugation_involutive
#print axioms degreeOneSesquilinear

end

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTChainReal
