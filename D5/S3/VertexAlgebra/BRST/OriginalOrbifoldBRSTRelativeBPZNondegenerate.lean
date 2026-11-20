/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTRelativeBPZNondegenerate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTRelativeBPZNondegenerate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Basic]
   utility: none
   digest: Nondegeneracy of the native BPZ pairing on total energy zero and on relative cochains. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZEnergy
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZNondegenerate
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeMassShell
import Batteries.Tactic.OpenPrivate

/-! Energy orthogonality reduces absolute BPZ tests to the kernel of total L₀.
The zero-mode CAR then detects both radicals of the original relative form. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTRelativeBPZNondegenerate

noncomputable section

open D5.S3.Quantum.Fermionic
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum mode)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis totalEnergy totalL0 totalL0_basis P0
  totalL0_P0)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTDescent (relativeStates)
open OriginalOrbifoldBRSTBPZWard (betaTotal betaRelTotal)
open OriginalOrbifoldBRSTBPZEnergy (betaTotal_eq_zero_of_ne_weight)
open OriginalOrbifoldBRSTBPZNondegenerate (betaTotal_nondegenerate)

open private b_square from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
open private c0 liftGhost b_zero_c_zero_car betaTotal_isotropic ghost_c_adjoint tensor_adjoint from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem P0_basis (i : FullLabel) :
    P0 (fullBasis i) = if totalEnergy i = 0 then fullBasis i else 0 := by
  change fullBasis.constr ℂ
    (fun j => (if totalEnergy j = 0 then (1 : ℂ) else 0) • fullBasis j) (fullBasis i) = _
  rw [Module.Basis.constr_basis]
  by_cases hi : totalEnergy i = 0 <;> simp [hi]

private theorem map_P0_eq_of_basis (f : State →ₗ[ℂ] ℂ)
    (hf : ∀ i : FullLabel, totalEnergy i ≠ 0 → f (fullBasis i) = 0) (z : State) :
    f (P0 z) = f z := by
  classical
  let coeff := fullBasis.repr z
  have expand : (∑ i ∈ coeff.support, coeff i • fullBasis i) = z := by
    simpa only [coeff, Finsupp.linearCombination_apply, Finsupp.sum] using
      fullBasis.linearCombination_repr z
  calc
    f (P0 z) = (f.comp P0) (∑ i ∈ coeff.support, coeff i • fullBasis i) :=
      congrArg (f.comp P0) expand.symm
    _ = f (∑ i ∈ coeff.support, coeff i • fullBasis i) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [LinearMap.comp_apply, map_smul, P0_basis]
      by_cases hi : totalEnergy i = 0
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi, map_zero, hf i hi]
    _ = f z := congrArg f expand

private theorem mem_weight_zero {x : State} (hx : totalL0 x = 0) :
    x ∈ totalL0.eigenspace (0 : ℂ) :=
  Module.End.mem_eigenspace_iff.mpr (by simpa only [zero_smul] using hx)

private theorem betaTotal_P0_right {x : State} (hx : totalL0 x = 0) (z : State) :
    betaTotal x (P0 z) = betaTotal x z := by
  refine map_P0_eq_of_basis (betaTotal x) (fun i hi => ?_) z
  have hne : (totalEnergy i : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hi
  exact betaTotal_eq_zero_of_ne_weight hne.symm (mem_weight_zero hx)
    (Module.End.mem_eigenspace_iff.mpr (totalL0_basis i))

private theorem betaTotal_P0_left {x : State} (hx : totalL0 x = 0) (z : State) :
    betaTotal (P0 z) x = betaTotal z x := by
  let f : State →ₗ[ℂ] ℂ := betaTotal.flip x
  have hf (i : FullLabel) (hi : totalEnergy i ≠ 0) : f (fullBasis i) = 0 := by
    change betaTotal (fullBasis i) x = 0
    have hne : (totalEnergy i : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hi
    exact betaTotal_eq_zero_of_ne_weight hne
      (Module.End.mem_eigenspace_iff.mpr (totalL0_basis i)) (mem_weight_zero hx)
  change f (P0 z) = f z
  exact map_P0_eq_of_basis f hf z

/-- The restriction of the full BPZ form to the native total-energy kernel
has trivial left and right radicals. -/
theorem betaTotal_ker_totalL0_nondegenerate :
    (betaTotal.restrict (LinearMap.ker totalL0)).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    change (x : State) = 0
    refine betaTotal_nondegenerate.1 (x : State) (fun z => ?_)
    have hx0 : totalL0 (x : State) = 0 := x.property
    rw [← betaTotal_P0_right hx0 z]
    exact hx ⟨P0 z, totalL0_P0 z⟩
  · intro x hx
    apply Subtype.ext
    change (x : State) = 0
    refine betaTotal_nondegenerate.2 (x : State) (fun z => ?_)
    have hx0 : totalL0 (x : State) = 0 := x.property
    rw [← betaTotal_P0_left hx0 z]
    exact hx ⟨P0 z, totalL0_P0 z⟩

private theorem totalL0_b_zero (x : State) : totalL0 (b 0 x) = b 0 (totalL0 x) := by
  have ward (z : State) : Q (b 0 z) + b 0 (Q z) = totalL0 z :=
    LinearMap.congr_fun (VirasoroBRST.Q_ward_b matterDatum 0) z
  rw [← ward (b 0 x), ← ward x, (b 0).map_add]
  simp only [b_square, map_zero, zero_add, add_zero]

private theorem totalL0_c_zero (x : State) : totalL0 (c0 x) = c0 (totalL0 x) := by
  have ghost : BcGhostVirasoro.L 0 * BcGhostFock.c 0 =
      BcGhostFock.c 0 * BcGhostVirasoro.L 0 := by
    apply sub_eq_zero.mp
    simpa only [mul_zero, sub_zero, Int.cast_zero, zero_smul] using BcGhostVirasoro.ward_c 0 0
  have h : totalL0 * c0 = c0 * totalL0 := by
    apply TensorProduct.ext'
    intro v w
    have hw : BcGhostVirasoro.L 0 (BcGhostFock.c 0 w) =
        BcGhostFock.c 0 (BcGhostVirasoro.L 0 w) := LinearMap.congr_fun ghost w
    let M0 : Module.End ℂ State := TensorProduct.map (mode 0) LinearMap.id
    let G0 : Module.End ℂ State := TensorProduct.map LinearMap.id (BcGhostVirasoro.L 0)
    let C0 : Module.End ℂ State := TensorProduct.map LinearMap.id (BcGhostFock.c 0)
    change (M0 + G0) (C0 (v ⊗ₜ[ℂ] w)) = C0 ((M0 + G0) (v ⊗ₜ[ℂ] w))
    simp only [M0, G0, C0, LinearMap.add_apply, map_add, TensorProduct.map_tmul,
      LinearMap.id_apply, hw]
  exact LinearMap.congr_fun h x

private theorem c_zero_square (x : State) : c0 (c0 x) = 0 := by
  have twice : (2 : ℂ) • (BcGhostFock.c 0 * BcGhostFock.c 0) = 0 := by
    simpa only [two_smul] using BcGhostFock.ghost_c_car 0 0
  have ghost : BcGhostFock.c 0 * BcGhostFock.c 0 = 0 :=
    (smul_eq_zero.mp twice).resolve_left (by norm_num)
  have h : c0 * c0 = 0 := by
    change liftGhost (BcGhostFock.c 0) * liftGhost (BcGhostFock.c 0) = 0
    simpa only [map_mul, map_zero] using congrArg liftGhost ghost
  exact LinearMap.congr_fun h x

private theorem zero_mode_split (z : State) : b 0 (c0 z) + c0 (b 0 z) = z :=
  LinearMap.congr_fun b_zero_c_zero_car z

private theorem b_zero_mem_relative {z : State} (hz : totalL0 z = 0) :
    b 0 z ∈ relativeStates := by
  change b 0 (b 0 z) = 0 ∧ totalL0 (b 0 z) = 0
  refine ⟨b_square 0 z, ?_⟩
  rw [totalL0_b_zero, hz, map_zero]

private theorem betaTotal_c_zero (x y : State) :
    betaTotal (c0 x) y = -betaTotal (parity x) (c0 y) := by
  change betaTotal (TensorProduct.map LinearMap.id (BcGhostFock.c 0) x) y =
    -betaTotal (parity x) (TensorProduct.map LinearMap.id (BcGhostFock.c 0) y)
  simpa only [neg_one_mul] using
    tensor_adjoint LinearMap.id LinearMap.id (BcGhostFock.c 0) (BcGhostFock.c 0)
      (-1 : ℂ) (fun _ _ => rfl)
      (fun a d => by simpa only [neg_zero] using ghost_c_adjoint 0 a d) x y

/-- The original relative BPZ cochain form has trivial radicals before imposing momentum
or taking BRST cohomology. -/
theorem betaRelTotal_nondegenerate : betaRelTotal.Nondegenerate := by
  constructor
  · intro x hx
    have hxRel : b 0 (x : State) = 0 ∧ totalL0 (x : State) = 0 := x.property
    let x0 : LinearMap.ker totalL0 := ⟨(x : State), hxRel.2⟩
    have hx0 : x0 = 0 := by
      refine betaTotal_ker_totalL0_nondegenerate.1 x0 (fun z => ?_)
      change betaTotal (x : State) (z : State) = 0
      have hz : totalL0 (z : State) = 0 := z.property
      have htest : betaTotal (x : State) (c0 (b 0 (z : State))) = 0 :=
        hx ⟨b 0 (z : State), b_zero_mem_relative hz⟩
      calc
        _ = betaTotal (x : State) (b 0 (c0 (z : State)) + c0 (b 0 (z : State))) :=
          congrArg (betaTotal (x : State)) (zero_mode_split (z : State)).symm
        _ = 0 := by
          rw [map_add, betaTotal_isotropic hxRel.1 (b_square 0 (c0 (z : State))),
            htest, add_zero]
    apply Subtype.ext
    change (x : State) = 0
    exact congrArg Subtype.val hx0
  · intro y hy
    have hyRel : b 0 (y : State) = 0 ∧ totalL0 (y : State) = 0 := y.property
    have hcyL : totalL0 (c0 (y : State)) = 0 := by
      rw [totalL0_c_zero, hyRel.2, map_zero]
    let cy : LinearMap.ker totalL0 := ⟨c0 (y : State), hcyL⟩
    have hcy : cy = 0 := by
      refine betaTotal_ker_totalL0_nondegenerate.2 cy (fun z => ?_)
      change betaTotal (z : State) (c0 (y : State)) = 0
      have hz : totalL0 (z : State) = 0 := z.property
      have hcz : totalL0 (c0 (z : State)) = 0 := by
        rw [totalL0_c_zero, hz, map_zero]
      have htest : betaTotal (b 0 (c0 (z : State))) (c0 (y : State)) = 0 :=
        hy ⟨b 0 (c0 (z : State)), b_zero_mem_relative hcz⟩
      calc
        _ = betaTotal (b 0 (c0 (z : State)) + c0 (b 0 (z : State))) (c0 (y : State)) :=
          congrArg (betaTotal.flip (c0 (y : State))) (zero_mode_split (z : State)).symm
        _ = 0 := by
          rw [betaTotal.map_add, LinearMap.add_apply, htest, betaTotal_c_zero, c_zero_square,
            map_zero, neg_zero, add_zero]
    have hyc : c0 (y : State) = 0 := congrArg Subtype.val hcy
    apply Subtype.ext
    change (y : State) = 0
    simpa only [hyc, hyRel.1, map_zero, add_zero] using (zero_mode_split (y : State)).symm

#print axioms betaTotal_ker_totalL0_nondegenerate
#print axioms betaRelTotal_nondegenerate

end

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTRelativeBPZNondegenerate
