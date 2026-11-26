import GRH.Lib.Adelic.CuspForms.DeltaForms
import GRH.Lib.GLn.Branching.Branching
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Dual of a Weyl module by Jacobi's complementary minors; Cartan component (known result;
see Lib.GLn.Branching.Branching).

This file: Integral isometric Cartan component of a Weyl module tensor a dual Weyl module. -/


open Finset Matrix Kronecker Fintype PolyRep MatMul
variable {Φ} (n) [Fintype Φ] [Fintype n] (kp km l : Φ → ℕ → ℕ)

/-- The column multiplicity function sending (τ,i) to kp_τ(i) + km_τ(|n|−i), with truncated
subtraction of natural numbers. -/
abbrev mixedWeight τ i := kp τ i + km τ (card n - i)

/-- An integral isometry Δ_l → Δ_kp ⊗ Δ_km of Weyl lattices with integral left inverse, sending
ev₁ to ev₁ ⊗ ev_{w₀} (w₀ the reversal) and intertwining ∏_τ det(g_τ)^{−∑_{0<i<|n|}
km_τ(i)}·S_l(g) with S_kp(g) ⊗ S_km(g⁻ᵀ) in characteristic 0. -/
structure PolyRep.MixedCartanEmbedding where
  matrix : Matrix (WeylIndex n kp × WeylIndex n km) (WeylIndex n l) ℤ
  hasLeftInv : HasLeftInv matrix
  gram_eq : matrixᵀ * weylGram n kp ⊗ₖ weylGram n km * matrix = weylGram _ _
  top R [Field R] [CharZero R] : let v {κ} p := weylEval (R := R) _ κ (permArray fun _ a ↦
      p (equivFin n a))
    matrix.map (↑) *ᵥ v Fin.val = (vecMulVec (v (·.rev)) (v Fin.val)).vec
  intertwines {R} [Field R] [CharZero R] (g : Φ → GL n R) v :
    matrix.map (↑) *ᵥ weylRep l (-∑ i ∈ Ico 1 (card n),
    km · i) g *ᵥ v = schur kp (g ·) ⊗ₖ schur _ (fun τ ↦ (g τ)⁻¹.1ᵀ) *ᵥ matrix.map (↑) *ᵥ v

/-- Duality for Weyl lattices: for all column counts kp and km, a map `PolyRep.MixedCartanEmbedding`
exists from the lattice with column counts kp_τ(i) + km_τ(|n| − i) to Δ_kp ⊗ Δ_km, that is, an
equivariant integral isometry with integral left inverse sending ev₁ to ev₁ ⊗ ev_{w₀}. -/
lemma nonempty_mixedCartanEmbedding :
  Nonempty (MixedCartanEmbedding n kp km (mixedWeight n kp km)) := by
  obtain ⟨J, J', _⟩ := exists_dual_isometry (κ := km) (rowPos n) _ rfl (by tauto)
  let K R [CommRing R] := mulLinearMap R (kronecker (diagonal 1) (J.map (↑))) (comulMatrix R _ kp _)
  have _ R [CommRing R] : (K ℤ).map (↑) = K R := by aesop (add simp mul_apply)
  refine ⟨.mk (l := _ + _) (K ℤ) (hasLeftInv_comulMatrix.imp' (mulLinearMap ℤ · (1 ⊗ₖ J')) ?_)
    (.trans ?_ (comulMatrix_isometry_and_equivariant 1).1) ?_ ?_⟩ <;> simp_all [K, weylRep,
    ← (_ ⊗ₖ _).mul_assoc, ← mul_kronecker_mul, ← comulMatrix_isometry_and_equivariant,
  ← kroneckerMap_transpose, kronecker_smul, funext @Int.cast_id, cm_mulVec_weylEval,
    ← mulVec_mulVec (weylEval _ _ _)]

/-- A chosen element of `PolyRep.MixedCartanEmbedding` for l = `mixedWeight` n kp km: an integral
map Δ_l → Δ_kp ⊗ Δ_km together with its laws. -/
noncomputable def mixedCartan := (nonempty_mixedCartanEmbedding n kp km).some
