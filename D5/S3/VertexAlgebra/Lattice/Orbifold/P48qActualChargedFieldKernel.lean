import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFieldCarrierTransport

/-! The vacuum pole of opposite lattice charges detects vectors in any cubic twisted target. -/

set_option autoImplicit false

open scoped BigOperators VertexOperator

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualChargedFieldKernel

open LatticeGeneratingFieldLocality (Charge bilinear creationCoeff epsilon)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open P48qTwistedChargeAction (lattice)
open P48qAllJetWickField (NativeStates)
open P48qCurrentChargedIterate (chargedGround)
open P48qFieldCarrierTransport (stripResidueOn TwistedBorcherdsOn)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)

/-- The source product of the negative charge with the positive charge has
vacuum coefficient at mode `(a, a) - 1` and vanishes at every larger mode. -/
theorem oppositeCharge_vacuum_pole (a : Charge lattice) :
    mu lattice (chargedGround (-a)) (bilinear lattice a a - 1) (chargedGround a) =
        epsilon lattice (-a) a • vacuum lattice ∧
      (∀ n : ℤ, bilinear lattice a a ≤ n →
        mu lattice (chargedGround (-a)) n (chargedGround a) = 0) ∧
      epsilon lattice (-a) a ≠ 0 := by
  have product (n : ℤ) : mu lattice (chargedGround (-a)) n (chargedGround a) =
      epsilon lattice (-a) a • Finsupp.single 0
        (creationCoeff lattice (-a) (bilinear lattice a a - n - 1)) := by
    change HVertexOperator.coeff
      ((LatticeActualVertexAlgebra.actualVertexAlgebra lattice).stateField (chargedGround (-a)))
      (-n - 1) (chargedGround a) = _
    have hindex : -n - 1 = bilinear lattice (-a) a + (bilinear lattice a a - n - 1) := by
      rw [LatticeFiniteNegativeGeneration.bilinear_neg_left]
      omega
    rw [hindex, P48qThirdTwistedField.untwistedChargedGround_coeff, neg_add_cancel]
  refine ⟨?_, ?_, ?_⟩
  · rw [product, show bilinear lattice a a - (bilinear lattice a a - 1) - 1 = 0 by omega]
    simp [creationCoeff, LatticeSugawaraConformal.exponential_constant, vacuum]
  · intro n hn
    rw [product]
    simp [creationCoeff, show bilinear lattice a a - n - 1 < 0 by omega]
  · unfold epsilon LatticeGeneratingFieldLocality.paritySign
    split_ifs <;> simp

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem jointKernel_eq_zero_of_vacuum_pole
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (a b : NativeStates) (n : ℤ) (N : ℕ)
    (hn : n < (N : ℤ)) (hB : TwistedBorcherdsOn Y a b 0 0 N)
    (hVac : HVertexOperator.coeff (Y (vacuum lattice)) 0 = (1 : Module.End ℂ W))
    (c : ℂ) (hc : c ≠ 0) (hpole : mu lattice a n b = c • vacuum lattice)
    (htail : ∀ m : ℤ, n < m → mu lattice a m b = 0)
    (w : W) (hw : ∀ k : ℤ, HVertexOperator.coeff (Y b) k w = 0) : w = 0 := by
  let order : ℤ := ((HahnModule.of ℂ).symm (Y a w)).order
  let p : ℤ := max 0 (-order)
  let q : ℤ := -p - 1
  have ha (j : ℕ) : ((stripResidueOn (0 - 3 * p) (Y a))[[j]]) w = 0 := by
    change HVertexOperator.coeff (Y a) (3 * (-(j : ℤ) - 1) + (0 - 3 * p)) w = 0
    apply VertexOperator.coeff_eq_zero_of_lt_order
    change 3 * (-(j : ℤ) - 1) + (0 - 3 * p) < order
    have hp₀ : 0 ≤ p := le_max_left _ _
    have hp : -order ≤ p := le_max_right _ _
    omega
  have hb (k : ℤ) : ((stripResidueOn 0 (Y b))[[k]]) w = 0 :=
    hw (3 * (-k - 1) + 0)
  have hres : (((residueField 1 n (stripResidueOn (0 - 3 * p) (Y a))
      (stripResidueOn 0 (Y b))).operator)[[q]]) w = 0 := by
    rw [(residueField 1 n _ _).coefficient]
    simp only [residueCoefficient, residueLeft, residueRight, ha, hb, map_zero, smul_zero,
      finsum_zero, sub_zero]
  have hsum := congrArg (fun T : Module.End ℂ W => T w) (hB p q n)
  change (((residueField 1 n (stripResidueOn (0 - 3 * p) (Y a))
    (stripResidueOn 0 (Y b))).operator)[[q]]) w = _ at hsum
  rw [hres] at hsum
  let term (j : ℕ) : Module.End ℂ W :=
    Ring.choose ((p : ℂ) - ((0 : ℤ) : ℂ) / 3) j •
      HVertexOperator.coeff (Y (mu lattice a (n + (j : ℤ)) b))
        (0 + 0 - 3 * (p + q - (j : ℤ) + 1))
  change 0 = (∑ j ∈ Finset.range ((N : ℤ) - n).toNat, term j) w at hsum
  have hsingle : (∑ j ∈ Finset.range ((N : ℤ) - n).toNat, term j) = term 0 := by
    apply Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))
    intro j _ hj
    dsimp only [term]
    rw [htail _ (by omega)]
    simp only [map_zero, Pi.zero_apply, smul_zero]
  have hdeg : 0 + 0 - 3 * (p + q - ((0 : ℕ) : ℤ) + 1) = 0 := by
    dsimp [q]
    omega
  rw [hsingle] at hsum
  have hterm : term 0 w = c • w := by
    dsimp only [term]
    rw [hdeg]
    simp only [Nat.cast_zero, add_zero, hpole, map_smul, Pi.smul_apply, hVac,
      Ring.choose_zero_right, one_smul, LinearMap.smul_apply, Module.End.one_apply]
  exact (smul_eq_zero.mp (hterm.symm.trans hsum.symm)).resolve_left hc

/-- For a fixed charge, the cubic twisted Borcherds law for the negative and
positive ground states has residues zero. At any cutoff covering the source
pole, it forces the positive charge field to have trivial joint kernel. -/
theorem chargedGround_jointKernel_eq_zero
    (Y : NativeStates →ₗ[ℂ] VertexOperator ℂ W) (a : Charge lattice) (N : ℕ)
    (hN : bilinear lattice a a ≤ (N : ℤ))
    (hB : TwistedBorcherdsOn Y (chargedGround (-a)) (chargedGround a) 0 0 N)
    (hVac : HVertexOperator.coeff (Y (vacuum lattice)) 0 = (1 : Module.End ℂ W))
    (w : W) (hw : ∀ k : ℤ, HVertexOperator.coeff (Y (chargedGround a)) k w = 0) : w = 0 := by
  obtain ⟨hpole, htail, hc⟩ := oppositeCharge_vacuum_pole a
  exact jointKernel_eq_zero_of_vacuum_pole Y _ _ _ N (by omega) hB hVac
    (epsilon lattice (-a) a) hc hpole (fun m hm => htail m (by omega)) w hw

#print axioms oppositeCharge_vacuum_pole
#print axioms chargedGround_jointKernel_eq_zero

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qActualChargedFieldKernel
