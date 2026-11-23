/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPureC1Primary
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPureC1Primary
   mirror-E: none(waiver:algebraic-original-brst)
   anchors: []
   utility: none
   digest: Absolute BRST on the original one-ghost tensors and the Virasoro primary equations. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldBRST
import D5.S3.VertexAlgebra.Lattice.LatticeZeroMomentumBRST
import D5.S3.Quantum.Fermionic.BcGhostQuartetCount

/-!
The absolute charge on the pure c(1) tensors is detected by independent
original occupation coefficients, including the coefficient at the c(0) site.

proof_shape: Q_tmul_c1vac, Q_tmul_c1vac_eq_zero_iff: content
admission_basis: escape-witness
escape_witness: The original matter sum is captured in a finite interval on
each tensor, and the cubic contributes the intercept. Each positive-mode
constraint and the weight constraint are recovered at distinct ghost sites.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldCriticalMatter (Matter matter)
open D5.S3.Quantum.Fermionic
open BcGhostFock (c)
open BcGhostQuartetCount (c1vac c1vac_eq)
open CountableOccupationFock (Fock ket create annihilate create_ket annihilate_ket
  phase lowerCount)

private theorem c_neg_c1vac_of_neg (n : ℤ) (hn : n < 0) : c (-n) c1vac = 0 := by
  rw [c1vac_eq]
  by_cases h : n = -1
  · subst n
    change create 1 (ket {1}) = 0
    simp
  · have hcut : ¬ -n ≤ (1 : ℤ) := by omega
    have hsite : 2 * (-n - 2).toNat ∉ ({1} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      omega
    rw [BcGhostFock.c, ite_eq_right hcut, annihilate_ket, ite_eq_right hsite]

/-- The absolute charge on a pure c(1) tensor, with a cutoff supplied by
statewise truncation of the original matter modes. -/
theorem Q_tmul_c1vac (φ : Matter) :
    ∃ N : ℤ, (∀ n : ℤ, N < n → matter.mode n φ = 0) ∧
      Q (φ ⊗ₜ[ℂ] c1vac) =
        ((matter.mode 0 φ - φ) ⊗ₜ[ℂ] c 0 c1vac) +
          ∑ n ∈ Finset.Icc 1 N, matter.mode n φ ⊗ₜ[ℂ] c (-n) c1vac := by
  obtain ⟨N, hN⟩ := matter.positive_mode_truncation φ
  refine ⟨N, hN, ?_⟩
  let s := Finset.Icc (1 : ℤ) N
  have h0 : (0 : ℤ) ∉ s := by
    intro h
    have h' : (1 : ℤ) ≤ 0 := (Finset.mem_Icc.mp h).1
    omega
  have hs : Function.support
      (fun n => VirasoroBRST.summand matter n (φ ⊗ₜ[ℂ] c1vac)) ⊆
        (↑(insert 0 s) : Set ℤ) := by
    intro n hn
    by_contra hout
    have hnot : n ≠ 0 ∧ ¬ (1 ≤ n ∧ n ≤ N) := by
      simpa only [Finset.mem_coe, Finset.mem_insert, s, Finset.mem_Icc, not_or] using hout
    apply hn
    simp only [VirasoroBRST.summand, TensorProduct.map_tmul]
    by_cases hneg : n < 0
    · rw [c_neg_c1vac_of_neg n hneg, TensorProduct.tmul_zero]
    · rw [hN n (by omega), TensorProduct.zero_tmul]
  have hg : BcGhostBRST.Qg c1vac = -(c 0 c1vac) := by
    rw [c1vac_eq]
    exact LatticeZeroMomentumBRST.Qg_down
  change VirasoroBRST.T matter (φ ⊗ₜ[ℂ] c1vac) + (φ ⊗ₜ[ℂ] BcGhostBRST.Qg c1vac) = _
  rw [VirasoroBRST.finite_capture matter _ _ hs, Finset.sum_insert h0]
  rw [TensorProduct.sub_tmul]
  simp only [VirasoroBRST.summand, TensorProduct.map_tmul, neg_zero, hg,
    TensorProduct.tmul_neg]
  abel

-- Occupation 1 is c(1). Occupation cSite n is c(-n).
private def cSite (n : ℤ) : ℕ := 2 * (1 + n).toNat + 1

private def cOccupation (n : ℤ) : Finset ℕ := insert (cSite n) {1}

private theorem one_lt_cSite (n : ℤ) (hn : 0 ≤ n) : 1 < cSite n := by
  unfold cSite
  omega

private theorem c_neg_c1vac_of_nonneg (n : ℤ) (hn : 0 ≤ n) :
    c (-n) c1vac = -ket (cOccupation n) := by
  have hsite := one_lt_cSite n hn
  have hf : cSite n ∉ ({1} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using ne_of_gt hsite
  have hl : lowerCount (cSite n) {1} = 1 := by
    simp [lowerCount, Finset.filter_singleton, hsite]
  rw [c1vac_eq, BcGhostFock.c, ite_eq_left (show -n ≤ 1 by omega), sub_neg_eq_add]
  change create (cSite n) (ket {1}) = _
  simp only [create_ket, ite_eq_right hf, phase, hl, pow_one, neg_one_smul, cOccupation]

private theorem cOccupation_inj {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (h : cOccupation m = cOccupation n) : m = n := by
  have hmem : cSite m ∈ cOccupation n := by
    rw [← h]
    exact Finset.mem_insert_self _ _
  have hs : cSite m = cSite n := by
    simpa only [cOccupation, Finset.mem_insert, Finset.mem_singleton,
      ne_of_gt (one_lt_cSite m hm), or_false] using hmem
  unfold cSite at hs
  omega

private def ghostCoefficient (S : Finset ℕ) : ComplexState →ₗ[ℂ] Matter :=
  (TensorProduct.rid ℂ Matter).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : Matter →ₗ[ℂ] Matter)
      (Finsupp.lapply S : Fock →ₗ[ℂ] ℂ))

private theorem ghostCoefficient_tmul (S : Finset ℕ) (φ : Matter) (v : Fock) :
    ghostCoefficient S (φ ⊗ₜ[ℂ] v) = v S • φ := by
  simp only [ghostCoefficient, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    Finsupp.lapply_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

private theorem coefficient_c_tmul (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) (φ : Matter) :
    ghostCoefficient (cOccupation n) (φ ⊗ₜ[ℂ] c (-m) c1vac) =
      if m = n then -φ else 0 := by
  rw [c_neg_c1vac_of_nonneg m hm, ghostCoefficient_tmul, Finsupp.neg_apply]
  by_cases h : m = n
  · subst m
    simp only [ket, Finsupp.single_eq_same, ite_true]
    exact neg_one_smul ℂ φ
  · have hS : cOccupation m ≠ cOccupation n := fun he => h (cOccupation_inj hm hn he)
    simp only [ket, Finsupp.single_apply, ite_eq_right hS, ite_eq_right h, neg_zero, zero_smul]

private theorem coefficient_positive_sum (φ : Matter) (N n : ℤ) (hn : 0 ≤ n) :
    ghostCoefficient (cOccupation n)
        (∑ m ∈ Finset.Icc 1 N, matter.mode m φ ⊗ₜ[ℂ] c (-m) c1vac) =
      if n ∈ Finset.Icc 1 N then -(matter.mode n φ) else 0 := by
  rw [map_sum]
  by_cases hmem : n ∈ Finset.Icc 1 N
  · rw [ite_eq_left hmem, Finset.sum_eq_single_of_mem n hmem]
    · rw [coefficient_c_tmul n n hn hn, ite_eq_left rfl]
    · intro m hm hne
      have hm0 : 0 ≤ m := (show (0 : ℤ) ≤ 1 by decide).trans (Finset.mem_Icc.mp hm).1
      rw [coefficient_c_tmul m n hm0 hn, ite_eq_right hne]
  · rw [ite_eq_right hmem]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm0 : 0 ≤ m := (show (0 : ℤ) ≤ 1 by decide).trans (Finset.mem_Icc.mp hm).1
    have hne : m ≠ n := fun h => hmem (h ▸ hm)
    rw [coefficient_c_tmul m n hm0 hn, ite_eq_right hne]

/-- Pure c(1) states are closed precisely at weight one with all positive
original Virasoro modes zero. -/
theorem Q_tmul_c1vac_eq_zero_iff (φ : Matter) :
    Q (φ ⊗ₜ[ℂ] c1vac) = 0 ↔
      matter.mode 0 φ = φ ∧ ∀ n : ℤ, 0 < n → matter.mode n φ = 0 := by
  obtain ⟨N, hN, hformula⟩ := Q_tmul_c1vac φ
  have hzero (n : ℤ) (hn : 0 ≤ n) :
      ghostCoefficient (cOccupation n) ((matter.mode 0 φ - φ) ⊗ₜ[ℂ] c 0 c1vac) =
        if 0 = n then -(matter.mode 0 φ - φ) else 0 := by
    simpa only [neg_zero] using coefficient_c_tmul 0 n (le_refl 0) hn (matter.mode 0 φ - φ)
  constructor
  · intro hQ
    have h0 := congrArg (ghostCoefficient (cOccupation 0)) hQ
    have hmem0 : (0 : ℤ) ∉ Finset.Icc 1 N := by
      intro h
      have h' : (1 : ℤ) ≤ 0 := (Finset.mem_Icc.mp h).1
      omega
    rw [map_zero, hformula, map_add, hzero 0 (le_refl 0), ite_eq_left rfl,
      coefficient_positive_sum φ N 0 (le_refl 0), ite_eq_right hmem0, add_zero] at h0
    refine ⟨sub_eq_zero.mp (neg_eq_zero.mp h0), ?_⟩
    intro n hn
    by_cases hbound : n ≤ N
    · have hmem : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hbound⟩
      have h := congrArg (ghostCoefficient (cOccupation n)) hQ
      rw [map_zero, hformula, map_add, hzero n hn.le, ite_eq_right (ne_of_lt hn),
        coefficient_positive_sum φ N n hn.le, ite_eq_left hmem, zero_add] at h
      exact neg_eq_zero.mp h
    · exact hN n (lt_of_not_ge hbound)
  · rintro ⟨h0, hp⟩
    have hs : (∑ n ∈ Finset.Icc 1 N, matter.mode n φ ⊗ₜ[ℂ] c (-n) c1vac) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have hn' : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [hp n (by omega), TensorProduct.zero_tmul]
    rw [hformula, h0, sub_self, TensorProduct.zero_tmul, zero_add, hs]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
