/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTL1Nilpotent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTL1Nilpotent
   mirror-E: none(waiver:algebraic-original-brst-local-nilpotence)
   anchors: []
   utility: none
   digest: Fixed-momentum energy floors and local nilpotence of the native total L(1). -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTMomentum

/-! The native total mode `L(1)` preserves hyperbolic momentum and lowers the
integer energy by one. Each momentum has its own lower energy bound. A state
has finite tensor basis support, so the finitely many energy cutoffs suffice. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTL1Nilpotent

open OriginalOrbifoldCriticalMatter (Matter State matterDatum mode Q b hyperbolicData)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel fullBasis totalEnergy totalL0
  totalL0_basis totalL0_coeff)
open OriginalOrbifoldRelativeMassShell (fixedMomentum mem_fixedMomentum_iff Q_mem_fixedMomentum)
open OriginalOrbifoldBRSTMomentum (b_mem_fixedMomentum)
open LatticeGeneratingFieldLocality (Charge)
open LatticePositiveEnergy (chargeEnergy)
open D5.S3.Quantum.Fermionic

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

local notation "totalL1" => VirasoroBRST.Ltotal matterDatum 1

/-- The native total mode preserves every hyperbolic momentum sector. -/
theorem totalL1_mem_fixedMomentum {p : Charge hyperbolicData} {x : State}
    (hx : x ∈ fixedMomentum p) : totalL1 x ∈ fixedMomentum p := by
  have ward : Q (b 1 x) + b 1 (Q x) = totalL1 x :=
    LinearMap.congr_fun (VirasoroBRST.Q_ward_b matterDatum 1) x
  rw [← ward]
  exact (fixedMomentum p).add_mem (Q_mem_fixedMomentum p (b_mem_fixedMomentum 1 hx))
    (b_mem_fixedMomentum 1 (Q_mem_fixedMomentum p hx))

/-- A nonzero integral eigenstate has energy at least its momentum half-norm minus one. -/
theorem fixedMomentum_energy_lower_bound {p : Charge hyperbolicData} {x : State}
    {e : ℤ} (hx : x ∈ fixedMomentum p) (hx0 : x ≠ 0)
    (he : totalL0 x = (e : ℂ) • x) : chargeEnergy hyperbolicData p - 1 ≤ e := by
  classical
  have hRepr : fullBasis.repr x ≠ 0 :=
    fun h => hx0 (fullBasis.repr.injective (h.trans fullBasis.repr.map_zero.symm))
  obtain ⟨i, hiMem⟩ := Finsupp.support_nonempty_iff.mpr hRepr
  have hi := Finsupp.mem_support_iff.mp hiMem
  have hp : i.2.1.1 = p := by
    by_contra hn
    exact hi ((mem_fixedMomentum_iff p x).mp hx i hn)
  have h := congrArg (fun y : State => fullBasis.repr y i) he
  change fullBasis.repr (totalL0 x) i = fullBasis.repr ((e : ℂ) • x) i at h
  rw [totalL0_coeff, fullBasis.repr.map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hEnergy : totalEnergy i = e := Int.cast_injective (mul_right_cancel₀ hi h)
  have hGhost := BcGhostRelativeEnergy.relativeEnergy_nonneg i.2.2
  change 0 ≤ BcGhostRelativeEnergy.energy i.2.2 + 1 at hGhost
  rw [← hEnergy]
  unfold totalEnergy LatticeBRSTZeroEnergyReduction.totalEnergy LatticePositiveEnergy.energy
  rw [hp]
  omega

private theorem totalL0_totalL1_commutator :
    totalL0 * totalL1 - totalL1 * totalL0 = -totalL1 := by
  apply TensorProduct.ext'
  intro u w
  have hMatter : mode 0 (mode 1 u) - mode 1 (mode 0 u) = -(mode 1 u) := by
    have h := LinearMap.congr_fun (OriginalOrbifoldCriticalMatter.mode_virasoro 0 1) u
    norm_num [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply] at h
    exact h
  have hGhost : BcGhostVirasoro.L 0 (BcGhostVirasoro.L 1 w) -
      BcGhostVirasoro.L 1 (BcGhostVirasoro.L 0 w) = -(BcGhostVirasoro.L 1 w) := by
    have h := LinearMap.congr_fun (BcGhostVirasoro.virasoro 0 1) w
    norm_num [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply] at h
    exact h
  change
    ((TensorProduct.map (mode 0) LinearMap.id +
        TensorProduct.map LinearMap.id (BcGhostVirasoro.L 0)) *
      (TensorProduct.map (mode 1) LinearMap.id +
        TensorProduct.map LinearMap.id (BcGhostVirasoro.L 1)) -
      (TensorProduct.map (mode 1) LinearMap.id +
        TensorProduct.map LinearMap.id (BcGhostVirasoro.L 1)) *
      (TensorProduct.map (mode 0) LinearMap.id +
        TensorProduct.map LinearMap.id (BcGhostVirasoro.L 0)) :
      Module.End ℂ State) (u ⊗ₜ[ℂ] w) =
    (-(TensorProduct.map (mode 1) LinearMap.id +
      TensorProduct.map LinearMap.id (BcGhostVirasoro.L 1)) :
      Module.End ℂ State) (u ⊗ₜ[ℂ] w)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    Module.End.mul_apply, map_add, TensorProduct.map_tmul, LinearMap.id_apply]
  calc
    _ = (mode 0 (mode 1 u) - mode 1 (mode 0 u)) ⊗ₜ[ℂ] w +
        u ⊗ₜ[ℂ] (BcGhostVirasoro.L 0 (BcGhostVirasoro.L 1 w) -
          BcGhostVirasoro.L 1 (BcGhostVirasoro.L 0 w)) := by
      simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
    _ = _ := by
      rw [hMatter, hGhost, TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_add]

/-- Each application of the native total mode lowers the integer energy by one. -/
theorem totalL1_lowers_energy {e : ℤ} {x : State} (hx : totalL0 x = (e : ℂ) • x) :
    totalL0 (totalL1 x) = ((e - 1 : ℤ) : ℂ) • totalL1 x := by
  have h := LinearMap.congr_fun totalL0_totalL1_commutator x
  change totalL0 (totalL1 x) - totalL1 (totalL0 x) = -totalL1 x at h
  rw [hx, map_smul] at h
  rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul, sub_eq_add_neg]
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Lowering past the momentum floor annihilates the state. -/
theorem totalL1_pow_eq_zero_of_energy_lt {p : Charge hyperbolicData} {x : State}
    {e : ℤ} (hx : x ∈ fixedMomentum p) (he : totalL0 x = (e : ℂ) • x)
    (n : ℕ) (hn : e - (n : ℤ) < chargeEnergy hyperbolicData p - 1) :
    (totalL1 ^ n) x = 0 := by
  have hIter (k : ℕ) : (totalL1 ^ k) x ∈ fixedMomentum p ∧
      totalL0 ((totalL1 ^ k) x) = ((e - (k : ℤ) : ℤ) : ℂ) • (totalL1 ^ k) x := by
    induction k with
    | zero => simpa only [pow_zero, Module.End.one_apply, Int.natCast_zero, sub_zero]
        using And.intro hx he
    | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        refine ⟨totalL1_mem_fixedMomentum ih.1, ?_⟩
        have hk : e - ((k + 1 : ℕ) : ℤ) = e - (k : ℤ) - 1 := by omega
        rw [hk]
        exact totalL1_lowers_energy ih.2
  by_contra h
  exact (not_le_of_gt hn) (fixedMomentum_energy_lower_bound (hIter n).1 h (hIter n).2)

/-- Any exponent above all the energy gaps represented in the finite support suffices. -/
theorem totalL1_pow_eq_zero_of_support_bound (x : State) (n : ℕ)
    (hn : (fullBasis.repr x).support.sup
      (fun i => (totalEnergy i - chargeEnergy hyperbolicData i.2.1.1 + 1).toNat) < n) :
    (totalL1 ^ n) x = 0 := by
  classical
  rw [← fullBasis.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hp : fullBasis i ∈ fixedMomentum i.2.1.1 := by
    apply (mem_fixedMomentum_iff _ _).mpr
    intro j hj
    rw [fullBasis.repr_self]
    exact Finsupp.single_eq_of_ne (fun h => hj (congrArg (fun k : FullLabel => k.2.1.1) h))
  have hGap : (totalEnergy i - chargeEnergy hyperbolicData i.2.1.1 + 1).toNat < n :=
    (Finset.le_sup hi).trans_lt hn
  rw [map_smul, totalL1_pow_eq_zero_of_energy_lt hp (totalL0_basis i) n (by omega), smul_zero]

/-- The actual positive total Virasoro mode is locally nilpotent on the original carrier. -/
theorem totalL1_locally_nilpotent (x : State) : ∃ n : ℕ, (totalL1 ^ n) x = 0 := by
  let bound := (fullBasis.repr x).support.sup
    (fun i => (totalEnergy i - chargeEnergy hyperbolicData i.2.1.1 + 1).toNat)
  exact ⟨bound + 1, totalL1_pow_eq_zero_of_support_bound x _ (Nat.lt_succ_self bound)⟩

#print axioms totalL1_mem_fixedMomentum
#print axioms fixedMomentum_energy_lower_bound
#print axioms totalL1_lowers_energy
#print axioms totalL1_pow_eq_zero_of_energy_lt
#print axioms totalL1_pow_eq_zero_of_support_bound
#print axioms totalL1_locally_nilpotent

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTL1Nilpotent
