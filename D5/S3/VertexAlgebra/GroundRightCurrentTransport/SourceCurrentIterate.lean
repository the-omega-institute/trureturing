/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/SourceCurrentIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/SourceCurrentIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source current iterate with independently truncated source and current supports. -/
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.SectorPropagation
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient

/-! The original state-field iterate is transported through the linear
physical-slice coefficient map. Its source tail and positive-current tail give
two different finite supports; no target compatibility is assumed.
Local-field calculus: Matsuo--Nagatomo and Bakalov--Kac (math/0402315).
Actual source fields: Scott Carnahan, vertexAlg
4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeHalfFockCurrentBorcherds
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents LatticeHalfFockLeftCurrentTransport
open scoped BigOperators TensorProduct VertexOperator
noncomputable section
local notation "μ" => LatticeAllStateReconstruction.mu
local notation "σ" => BinomialKernelDelta.chooseSign
local notation "ε" => StateFieldResidueReconstruction.epsilon
local macro "upper" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.upper))
local macro "high" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.high))
local macro "source_current" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds.source_current))

theorem source_current_iterate_slice
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ)
    (hK : upper (Y D a) b ≤ K)
    (gamma delta d r : ℤ) :
    let N : ℕ := ((K : ℤ) - r).toNat
    let M : ℕ := vectorFrequencyBound D b + 1
    let left : ℕ → VertexOperator ℂ (ActualTensor D hu) := fun j =>
      σ d j • targetSlice D hu
        (neutralMode D i (d - (j : ℤ)) (μ D a (r + (j : ℤ)) b))
        (gamma + delta + 1)
    let right : ℕ → VertexOperator ℂ (ActualTensor D hu) := fun j =>
      σ d j • targetSlice D hu
        (μ D a (d + r - (j : ℤ)) (neutralMode D i (j : ℤ) b))
        (gamma + delta + 1)
    Function.HasFiniteSupport left ∧
      Function.HasFiniteSupport right ∧
      targetSlice D hu (μ D (neutralMode D i d a) r b)
          (gamma + delta + 1) =
        (∑ j ∈ Finset.range N, left j) -
          ε d • ∑ j ∈ Finset.range M, right j := by
  classical
  dsimp
  let N : ℕ := ((K : ℤ) - r).toNat
  let M : ℕ := vectorFrequencyBound D b + 1
  let h := neutralMode D i (-1) (vacuum D)
  have current_mode (t : ℤ) (v : Carrier D) :
      ((Y D h)[[t]]) v = neutralMode D i t v :=
    source_current D i t v
  have source_iter :
      μ D (neutralMode D i d a) r b =
        (∑ᶠ j : ℕ,
          σ d j • neutralMode D i (d - (j : ℤ))
            (μ D a (r + (j : ℤ)) b)) -
        ε d • (∑ᶠ j : ℕ,
          σ d j • μ D a (d + r - (j : ℤ))
            (neutralMode D i (j : ℤ) b)) := by
    rcases stateField_iterate D h a b d r with ⟨_, _, hiterate⟩
    simpa only [LatticeAllStateReconstruction.mu, h, current_mode, BinomialKernelDelta.chooseSign, StateFieldResidueReconstruction.epsilon] using hiterate
  have slice_zero (s : ℤ) : targetSlice D hu 0 s = 0 := by
    apply HVertexOperator.coeff_inj
    funext e
    rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
    apply LinearMap.ext
    intro x
    simp [targetSlice, physicalSlice_mode]
  have left_carrier_support :
      Function.support
        (fun j : ℕ =>
          σ d j • neutralMode D i (d - (j : ℤ))
            (μ D a (r + (j : ℤ)) b)) ⊆ (Finset.range N : Set ℕ) := by
    intro j hj
    by_contra hmem
    have hnot : N ≤ j := Nat.le_of_not_gt (Finset.mem_range.not.mp hmem)
    have htail : (K : ℤ) ≤ r + (j : ℤ) := by
      dsimp [N] at hnot
      omega
    have hhigh := high (Y D a) b (r + (j : ℤ)) (by omega)
    have hzero : μ D a (r + (j : ℤ)) b = 0 := by
      exact hhigh
    exact hj (by dsimp only; rw [hzero, map_zero, smul_zero])
  have right_carrier_support :
      Function.support
        (fun j : ℕ =>
          σ d j • μ D a (d + r - (j : ℤ))
            (neutralMode D i (j : ℤ) b)) ⊆ (Finset.range M : Set ℕ) := by
    intro j hj
    by_contra hmem
    have hpositive : (vectorFrequencyBound D b : ℤ) < (j : ℤ) := by
      have bound : M ≤ j := Nat.le_of_not_gt (Finset.mem_range.not.mp hmem)
      dsimp [M] at bound
      omega
    have hzero := neutralMode_vanish D i b (j :ℤ) hpositive
    exact hj (by simp [hzero, LatticeAllStateReconstruction.mu])
  have left_support :
      Function.HasFiniteSupport
        (fun j : ℕ =>
          σ d j • targetSlice D hu
            (neutralMode D i (d - (j : ℤ))
              (μ D a (r + (j : ℤ)) b))
            (gamma + delta + 1)) := by
    refine (Finset.range N).finite_toSet.subset ?_
    intro j hj
    by_contra hmem
    have hnot : N ≤ j := Nat.le_of_not_gt (Finset.mem_range.not.mp hmem)
    have htail : (K : ℤ) ≤ r + (j : ℤ) := by
      dsimp [N] at hnot
      omega
    have hhigh := high (Y D a) b (r + (j : ℤ)) (by omega)
    have hzero : μ D a (r + (j : ℤ)) b = 0 := by
      exact hhigh
    exact hj (by dsimp only; rw [hzero, map_zero, slice_zero, smul_zero])
  have right_support :
      Function.HasFiniteSupport
        (fun j : ℕ =>
          σ d j • targetSlice D hu
            (μ D a (d + r - (j : ℤ))
              (neutralMode D i (j : ℤ) b))
            (gamma + delta + 1)) := by
    refine (Finset.range M).finite_toSet.subset ?_
    intro j hj
    by_contra hmem
    have hpositive : (vectorFrequencyBound D b : ℤ) < (j : ℤ) := by
      have bound : M ≤ j := Nat.le_of_not_gt (Finset.mem_range.not.mp hmem)
      dsimp [M] at bound
      omega
    have hzero := neutralMode_vanish D i b (j : ℤ) hpositive
    have hz : μ D a (d + r - (j : ℤ)) (neutralMode D i (j : ℤ) b) = 0 := by
      simp [LatticeAllStateReconstruction.mu, hzero]
    exact hj (by dsimp only; rw [hz, slice_zero, smul_zero])
  rw [finsum_eq_sum_of_support_subset _ left_carrier_support,
    finsum_eq_sum_of_support_subset _ right_carrier_support] at source_iter
  refine ⟨left_support, right_support, ?_⟩
  apply HVertexOperator.coeff_inj
  funext e
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  apply LinearMap.ext
  intro x
  let S : Carrier D →ₗ[ℂ] ActualTensor D hu :=
    { toFun := fun v => (slice D hu v (gamma + delta + 1) (-e-1)) x
      map_add' := by
        intro u v
        simp only [slice, map_add, Pi.add_apply, LinearMap.add_apply]
      map_smul' := by
        intro c v
        simp only [slice, map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply] }
  have hmap := congrArg S source_iter
  simp only [map_sub, map_smul, map_sum] at hmap
  simpa only [S, LinearMap.coe_mk, AddHom.coe_mk, N, M, slice, targetSlice, physicalSlice_mode, map_sub, map_sum, map_smul,
    Pi.sub_apply, Pi.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Finset.sum_apply] using hmap

end
end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
