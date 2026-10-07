/- GID: D5/S3/VertexAlgebra/PolynomialFockChargedIrreducibility
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/PolynomialFockChargedIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Charged polynomial Heisenberg modes admit only zero and full invariant subspaces. -/

/-
proof_shape: charged_modes_irreducible: content
escape_witness: In an arbitrary nonzero invariant subspace, minimal total degree
  forces all partial derivatives of a nonzero member to vanish. Characteristic
  zero makes that member a nonzero constant, and actual creation modes then
  generate every polynomial in the same subspace.
admission_basis: escape-witness
utility: none; this is a universal algebraic invariant-subspace theorem, not a
  finite enumeration, checker, numerical reduction or certified instance.
Direct frozen dependencies:
  D5/S3/VertexAlgebra/PolynomialFockSugawaraSupport.mode:
  sha256:a9b55fcf79663edfd4809fb83752ca19fb89e0b91f6d372cbf8836e8633ccead;
  .annihilate: sha256:348bce17f371f8e3c4b8671683d5b983fec45ee84d7b10fa0c284decd5962447;
  .create: sha256:4046c1e82bbacb54e1f7840bedcb77bb47ff5bb66e60beb117ad1e2e63539991;
  .Fock: sha256:fe7a8b8d44612011dd52c600c9c92515af748b2726aa1031a8b6141302d583c7.
  D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity original helpers
  exists_minimum_degree, totalDegree_pderiv_lt, eq_constant_of_partials_zero;
  baseline statement_ids respectively
  sha256:9d90b03aa4dd1c82069d2c93d8baec08153beb284fb7aedccee85fcf40edcbde,
  sha256:12cf57f4c677c080d13e535ca5b9ab12575b53ff78318f1ea4a30a7c5a050b7b,
  sha256:91602ae6fec6a28a16c583f0ec423208eece266af8bf2720d7b2c087e8644c5c.
-/

import D5.S3.VertexAlgebra.PolynomialFockSugawaraSupport
import D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.PolynomialFockChargedIrreducibility

open MvPolynomial PolynomialFockSugawaraSupport
open D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.API

/-- The actual Heisenberg action of complex charge lambda. -/
noncomputable def chargedMode (lambda : ℂ) (n : ℤ) : Module.End ℂ Fock :=
  if n = 0 then lambda • LinearMap.id else mode n

/-- Every complex subspace invariant under all actual charged modes is zero or full. -/
theorem charged_modes_irreducible (lambda : ℂ) (S : Submodule ℂ Fock)
    (hmode : ∀ n : ℤ, ∀ p : Fock, p ∈ S → chargedMode lambda n p ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hpartial (q : Fock) (hq : q ∈ S) (j : ℕ) : pderiv j q ∈ S := by
    have hm := hmode (Int.ofNat (j + 1)) q hq
    have hn : (Int.ofNat (j + 1)) ≠ 0 :=
      Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero j)
    have hc : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    rw [chargedMode, if_neg hn] at hm
    change ((j + 1 : ℂ) • pderiv j q) ∈ S at hm
    have hs := S.smul_mem ((j + 1 : ℂ)⁻¹) hm
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hs
  obtain ⟨q, hq, hqne⟩ := S.ne_bot_iff.mp hS
  obtain ⟨p, ⟨hp, hpne⟩, hmin⟩ := exists_minimum_degree
    (fun p : Fock => p ∈ S ∧ p ≠ 0) ⟨q, hq, hqne⟩
  have hzero : ∀ j : ℕ, pderiv j p = 0 := by
    intro j
    by_contra hj
    exact (not_le_of_gt (totalDegree_pderiv_lt p j hj))
      (hmin _ ⟨hpartial p hp j, hj⟩)
  have hconstant := eq_constant_of_partials_zero p hzero
  have hc : constantCoeff p ≠ 0 := by
    intro hz
    exact hpne (by rw [hconstant, hz, C_0])
  have hone : (1 : Fock) ∈ S := by
    have hs := S.smul_mem (constantCoeff p)⁻¹ hp
    rw [hconstant] at hs
    simpa [smul_eq_C_mul, ← map_mul, hc] using hs
  apply top_unique
  intro v hv
  clear hv
  induction v using MvPolynomial.induction_on with
  | C a => simpa [smul_eq_C_mul] using S.smul_mem a hone
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p j hp =>
    have hm := hmode (Int.negSucc j) p hp
    simpa [chargedMode, mode, create, LinearMap.mulLeft_apply, mul_comm] using hm

end D5.S3.VertexAlgebra.PolynomialFockChargedIrreducibility
