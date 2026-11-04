/- GID: D5/S3/QuadraticForms/JenzerPermutedRotorLoop
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/JenzerPermutedRotorLoop
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Permuted rotor loops obey the subset formula without the star condition. -/

/-
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22564
admission_basis: open-problem-resolution (#22266; Proved).
escape_witness: none; admission is through the settling result.
Per-declaration proof_shape; names are relative to this module namespace:
full_trace_zero_of_not_odd: proof_shape: content. Consumers: result.
result: proof_shape: content. escape_witness: none.
returnSign: proof_shape: definition. Consumers: result, scalar_pair_split.
scalar_pair_split: proof_shape: content. Consumers: result.
scalar_subset_square: proof_shape: bind-only. Consumers: result.
The source uses the native grade-zero coefficient and homogeneous bivectors.
The exterior equivalence reads grades and never transports multiplication.
-/

import D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra
import D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords

open D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra
open D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoop
noncomputable section
variable {V : Type} [AddCommGroup V] [Module ℝ V]

private def returnSign {k : ℕ} (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) : ℝ :=
  (-1 : ℝ)^S.card * (-1 : ℝ)^inversionCount τ S

private lemma scalar_pair_split {q : QuadraticForm ℝ V} {k : ℕ}
    (hk : 1 ≤ k) (B : Fin k → CliffordAlgebra q)
    (hB : AnticommutingUnitFamily q k B) (θ : Fin k → ℝ)
    (τ : Equiv.Perm (Fin k)) (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (S T : Finset (Fin k)) :
    a θ S * (returnSign τ T * a θ T) *
        scalarProjection q (subsetProduct B S * subsetProduct B T) =
      (if S = T then returnSign τ S * a θ S ^ 2 *
        scalarProjection q (subsetProduct B S * subsetProduct B S) else 0) +
      ((∏ i, s θ i * c θ i) * scalarProjection q (subsetProduct B Finset.univ)) *
        (returnSign τ T * b.ExteriorAlgebra.repr
          (b.ExteriorAlgebra S * b.ExteriorAlgebra T) Finset.univ) := by
  let t : CliffordAlgebra q →ₗ[ℝ] ℝ :=
    (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℝ V →ₐ[ℝ] ℝ).toLinearMap.comp
      (CliffordAlgebra.equivExterior q).toLinearMap
  by_cases he : S = T
  · subst T
    have hext := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ComplementBridge.canonical_exterior_top b S S
      (D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ComplementBridge.complement_ne_self hk S)
    rw [hext, mul_zero, mul_zero, add_zero, if_pos rfl]
    ring
  · rw [if_neg he]
    by_cases hc : T = Finset.univ \ S
    · subst T
      have ht := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ComplementBridge.canonical_complementary_trace B hB.2.2 t b S
      change scalarProjection q (subsetProduct B S * subsetProduct B (Finset.univ \ S)) =
        b.ExteriorAlgebra.repr (b.ExteriorAlgebra S * b.ExteriorAlgebra (Finset.univ \ S))
          Finset.univ * scalarProjection q (subsetProduct B Finset.univ) at ht
      rw [ht]
      calc
        _ = (a θ S * a θ (Finset.univ \ S)) *
          (scalarProjection q (subsetProduct B Finset.univ) *
            (returnSign τ (Finset.univ \ S) *
              b.ExteriorAlgebra.repr
                (b.ExteriorAlgebra S * b.ExteriorAlgebra (Finset.univ \ S)) Finset.univ)) := by ring
        _ = _ := by rw [coefficient_complement]; ring
    · have hs : ∀ i, B i * B i = -1 := fun i => by simpa only [pow_two] using hB.2.1 i
      have hz := D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport.tracial_off_diagonal_zero t
        (fun x y => D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeBridge.scalar_cyclic q x y) B hs hB.2.2 S T he
        (fun hh => hc hh.2)
      change scalarProjection q (subsetProduct B S * subsetProduct B T) = 0 at hz
      have hext := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ComplementBridge.canonical_exterior_top b S T hc
      rw [hz, hext]
      ring

private lemma full_trace_zero_of_not_odd {q : QuadraticForm ℝ V} {k : ℕ}
    (hk : 1 ≤ k) (B : Fin k → CliffordAlgebra q)
    (hB : AnticommutingUnitFamily q k B) (ho : ¬Odd k) :
    scalarProjection q (subsetProduct B Finset.univ) = 0 := by
  let t : CliffordAlgebra q →ₗ[ℝ] ℝ :=
    (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℝ V →ₐ[ℝ] ℝ).toLinearMap.comp
      (CliffordAlgebra.equivExterior q).toLinearMap
  have hs : ∀ i, B i * B i = -1 := fun i => by simpa only [pow_two] using hB.2.1 i
  have hn : (Finset.univ : Finset (Fin k)).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hz := D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport.tracial_subset_vanishing t
    (fun x y => D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeBridge.scalar_cyclic q x y) B hs hB.2.2
    Finset.univ hn (fun hh => ho hh.2)
  exact hz

private lemma scalar_subset_square {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (hB : AnticommutingUnitFamily q k B)
    (S : Finset (Fin k)) :
    scalarProjection q (subsetProduct B S * subsetProduct B S) =
      (-1 : ℝ)^(S.card*(S.card+1)/2) := by
  rw [subsetProduct_square B hB]
  simp [scalarProjection, CliffordAlgebra.equivExterior]

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoop

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoop
noncomputable section

theorem result : claim := by
  classical
  intro V _ _ _ q hq k hk B hB θ τ
  let b : Module.Basis (Fin k) ℝ (Fin k → ℝ) := Pi.basisFun ℝ (Fin k)
  let H : Finset (Finset (Fin k)) := Finset.univ.powerset
  let K : ℝ := (∏ i, s θ i * c θ i) * scalarProjection q (subsetProduct B Finset.univ)
  let D : Finset (Fin k) → ℝ := fun S =>
    returnSign τ S * a θ S ^ 2 * scalarProjection q (subsetProduct B S * subsetProduct B S)
  let Y : Finset (Fin k) → Finset (Fin k) → ℝ := fun S T =>
    returnSign τ T * b.ExteriorAlgebra.repr
      (b.ExteriorAlgebra S * b.ExteriorAlgebra T) Finset.univ
  have hexpand : scalarProjection q (loop B θ τ) =
      ∑ S ∈ H, ∑ T ∈ H, a θ S * (returnSign τ T * a θ T) *
        scalarProjection q (subsetProduct B S * subsetProduct B T) := by
    unfold loop
    rw [chain_expansion B θ, return_expansion B hB θ τ]
    simp only [H, scalarProjection, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
      mul_smul_comm, map_sum, map_smul, smul_eq_mul, returnSign, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    ring
  have hsplit : (∑ S ∈ H, ∑ T ∈ H,
      a θ S * (returnSign τ T * a θ T) *
        scalarProjection q (subsetProduct B S * subsetProduct B T)) =
      ∑ S ∈ H, ∑ T ∈ H, ((if S = T then D S else 0) + K * Y S T) := by
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    exact scalar_pair_split hk B hB θ τ b S T
  have hsums : (∑ S ∈ H, ∑ T ∈ H, ((if S = T then D S else 0) + K * Y S T)) =
      (∑ S ∈ H, D S) + K * (∑ S ∈ H, ∑ T ∈ H, Y S T) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    simp [hS]
  have hcorr : K * (∑ S ∈ H, ∑ T ∈ H, Y S T) = 0 := by
    by_cases ho : Odd k
    · have hz := D5.S3.QuadraticForms.JenzerPermutedRotorLoopWords.ExteriorSum.signed_top_sum_zero b τ ho
      change (∑ S ∈ H, ∑ T ∈ H, Y S T) = 0 at hz
      rw [hz, mul_zero]
    · have hz := full_trace_zero_of_not_odd hk B hB ho
      simp only [K, hz, mul_zero, zero_mul]
  calc
    scalarProjection q (loop B θ τ) = (∑ S ∈ H, D S) + K *
        (∑ S ∈ H, ∑ T ∈ H, Y S T) := hexpand.trans (hsplit.trans hsums)
    _ = ∑ S ∈ H, D S := by rw [hcorr, add_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      dsimp only [D]
      rw [scalar_subset_square B hB, coefficient_square θ S]
      unfold returnSign eta
      ring

end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoop
