/- GID: D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: All-map triple tensor trace obstruction along finite additive embeddings. -/

import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedOriginalClassification
import D5.S3.FiniteGroups.GroupAlgebra.BoundedTensorPolarization
import D5.S3.FiniteGroups.GroupAlgebra.EquivariantPartialTrace

/-!
# Triple tensor trace obstruction

The iterated multiplication dual has zero trace pairing when either binomial factor
vanishes. Finite-sample coefficient recovery and the highest tensor coefficient reduce
every equivariant map to this canonical map for trace purposes. The argument uses the
original polynomial dual actions and no division by a dimension.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTripleTensorObstruction

open ElmerKadrTensorCounterexample PolynomialKernelPolarization
open ElmerKadrPositiveCriterion RectangularTensorObstruction
open EmbeddedOriginalClassification
open Finset Polynomial
open scoped TensorProduct

universe uK uE

variable {K : Type uK} [Field K]

/-- The parenthesized triple tensor of the original polynomial contragredients. -/
abbrev TripleSpace (n m k : ℕ) := TensorSpace K n m ⊗[K] DualPower K (k + 1)

/-- The actual diagonal translation action, before restriction to the finite subgroup. -/
def tripleAction (n m k : ℕ) : Representation K (Multiplicative K) (TripleSpace (K := K) n m k) :=
  (tensorAction K n m).tprod (dualAction K (k + 1))

private def tripleDegree (n m k : ℕ)
    (i : Fin (n + m + 1) × Fin (k + 1)) : Fin (n + m + k + 1) :=
  ⟨i.1.val + i.2.val, by have := i.1.isLt; have := i.2.isLt; omega⟩

/-- Group the binary tensor coefficients and the third factor by their total degree. -/
def tripleCoefficient (n m k : ℕ) (r : Fin (n + m + k + 1)) :
    Module.End K (TripleSpace (K := K) n m k) :=
  ∑ i : Fin (n + m + 1) × Fin (k + 1), if tripleDegree n m k i = r then
    TensorProduct.map (tensorCoefficient K n m i.1) (coefficient K (k + 1) i.2.val)
    else 0

theorem triple_action_expansion (n m k : ℕ) (a : K) :
    tripleAction (K := K) n m k (Multiplicative.ofAdd (-a)) =
      ∑ r : Fin (n + m + k + 1), a ^ r.val • tripleCoefficient n m k r := by
  classical
  have hb : tensorAction K n m (Multiplicative.ofAdd (-a)) =
      ∑ r : Fin (n + m + 1), a ^ r.val • tensorCoefficient K n m r := by
    rw [tensor_action_expansion]
    symm
    simp only [tensorCoefficient, Finset.smul_sum, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ij _
    simp
  have ht : tripleAction (K := K) n m k (Multiplicative.ofAdd (-a)) =
      ∑ i : Fin (n + m + 1) × Fin (k + 1), a ^ (tripleDegree n m k i).val •
        TensorProduct.map (tensorCoefficient K n m i.1)
          (coefficient K (k + 1) i.2.val) := by
    apply TensorProduct.ext'
    intro x y
    simp only [tripleAction, Representation.tprod_apply, TensorProduct.map_tmul, hb,
      action_expansion K (k + 1) (k + 1) (le_refl (k + 1)),
      LinearMap.sum_apply, LinearMap.smul_apply, TensorProduct.sum_tmul,
      TensorProduct.tmul_sum, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      Finset.smul_sum, smul_smul, ← pow_add, Fintype.sum_prod_type, tripleDegree]
    rw [Finset.sum_comm]
    simp only [Nat.add_comm]
  rw [ht]
  symm
  simp only [tripleCoefficient, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ij _
  simp

private theorem triple_coefficient_top (n m k : ℕ) :
    tripleCoefficient (K := K) n m k (Fin.last (n + m + k)) =
      TensorProduct.map (tensorCoefficient K n m (Fin.last (n + m)))
        (coefficient K (k + 1) k) := by
  classical
  rw [tripleCoefficient, Finset.sum_eq_single (Fin.last (n + m), Fin.last k)]
  · simp [tripleDegree, Fin.ext_iff]
  · rintro ⟨u, v⟩ _ hne
    have hd : tripleDegree n m k (u, v) ≠ Fin.last (n + m + k) := by
      intro he
      have hs : u.val + v.val = n + m + k := congrArg Fin.val he
      have hu := u.isLt
      have hv := v.isLt
      apply hne
      apply Prod.ext
      · apply Fin.ext
        change u.val = n + m
        omega
      · apply Fin.ext
        change v.val = k
        omega
    simp [hd]
  · simp

theorem triple_coefficient_top_range (n m k : ℕ) (z : TripleSpace (K := K) n m k) :
    ∃ c : K, tripleCoefficient n m k (Fin.last (n + m + k)) z =
      c • ((dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K]
        dualBasis K (m + 1) (Fin.last m)) ⊗ₜ[K]
          dualBasis K (k + 1) (Fin.last k)) := by
  rw [triple_coefficient_top]
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      obtain ⟨c, hc⟩ := tensor_coefficient_top_range K n m x
      refine ⟨c * y (Polynomial.degreeLT.basis K (k + 1) 0), ?_⟩
      rw [TensorProduct.map_tmul, hc, coefficient_top]
      simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul, mul_comm]
  | add x y hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, by rw [map_add, hc, hd, add_smul]⟩

/-- The canonical map dual to actual polynomial multiplication. -/
def delta (n m : ℕ) :
    (dualAction K (n + m + 1)).IntertwiningMap (tensorAction K n m) :=
  (dualTensorEquiv (primalAction K (n + 1)) (primalAction K (m + 1))).symm.toIntertwiningMap.comp
    (dualIntertwiner (multiplicationIntertwiner n m))

theorem delta_top (n m : ℕ) :
    delta (K := K) n m (dualBasis K (n + m + 1) (Fin.last (n + m))) =
      dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K] dualBasis K (m + 1) (Fin.last m) := by
  classical
  apply (TensorProduct.dualDistribEquiv K (Primal K (n + 1)) (Primal K (m + 1))).injective
  change TensorProduct.dualDistribEquiv K (Primal K (n + 1)) (Primal K (m + 1))
    ((TensorProduct.dualDistribEquiv K (Primal K (n + 1)) (Primal K (m + 1))).symm
      ((multiplication n m).dualMap (dualBasis K (n + m + 1) (Fin.last (n + m))))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply ((Polynomial.degreeLT.basis K (n + 1)).tensorProduct
    (Polynomial.degreeLT.basis K (m + 1))).ext
  rintro ⟨i, j⟩
  simp only [Module.Basis.tensorProduct_apply, LinearMap.dualMap_apply,
    multiplication_basis, TensorProduct.dualDistribEquiv_tmul_tmul,
    dualBasis, Module.Basis.dualBasis_apply_self, Fin.ext_iff, Fin.val_last]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi' : i.val = n <;> by_cases hj' : j.val = m <;> simp_all
  omega

section Embedded

variable {E : Type uE} [AddGroup E]
variable (α : E →+ K)

/-- Restrict the multiplication dual along the actual additive embedding. -/
def embeddedDelta (n m : ℕ) :
    Representation.IntertwiningMap ((dualAction K (n + m + 1)).comp α.toMultiplicative)
      ((tensorAction K n m).comp α.toMultiplicative) :=
  restrictIntertwiner α.toMultiplicative (delta n m)

/-- The iterated multiplication dual, with the specified left parenthesization. -/
def embeddedTripleDelta (n m k : ℕ) :
    Representation.IntertwiningMap ((dualAction K (n + m + k + 1)).comp α.toMultiplicative)
      ((tripleAction n m k).comp α.toMultiplicative) :=
  ((embeddedDelta α n m).rTensor ((dualAction K (k + 1)).comp α.toMultiplicative)).comp
    (embeddedDelta α (n + m) k)

theorem embedded_triple_delta_top (n m k : ℕ) :
    embeddedTripleDelta α n m k (dualBasis K (n + m + k + 1) (Fin.last (n + m + k))) =
      (dualBasis K (n + 1) (Fin.last n) ⊗ₜ[K] dualBasis K (m + 1) (Fin.last m)) ⊗ₜ[K]
        dualBasis K (k + 1) (Fin.last k) := by
  change TensorProduct.map (delta (K := K) n m).toLinearMap LinearMap.id
    (delta (K := K) (n + m) k
      (dualBasis K (n + m + k + 1) (Fin.last (n + m + k)))) = _
  rw [delta_top, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [show (delta (K := K) n m).toLinearMap
    (dualBasis K (n + m + 1) (Fin.last (n + m))) = _ from delta_top n m]

variable [Fintype E] (hα : Function.Injective α)

include hα

theorem restricted_triple_intertwines_coefficients {n m k : ℕ}
    (hbound : n + m + k + 1 ≤ Fintype.card E)
    (f : Representation.IntertwiningMap
      ((dualAction K (n + m + k + 1)).comp α.toMultiplicative)
      ((tripleAction n m k).comp α.toMultiplicative))
    (r : Fin (n + m + k + 1)) :
    f.toLinearMap.comp (coefficient K (n + m + k + 1) r.val) =
      (tripleCoefficient n m k r).comp f.toLinearMap := by
  refine intertwines_coefficients_of_samples (α : E → K) hα hbound
    (fun j => coefficient K (n + m + k + 1) j.val)
    (fun j => tripleCoefficient n m k j) f.toLinearMap ?_ r
  intro e
  have he := f.isIntertwining' (Multiplicative.ofAdd (-e))
  change f.toLinearMap.comp
    (dualAction K (n + m + k + 1) (Multiplicative.ofAdd (α (-e)))) =
      (tripleAction n m k (Multiplicative.ofAdd (α (-e)))).comp f.toLinearMap at he
  simp only [map_neg] at he
  rw [action_expansion K (n + m + k + 1) (n + m + k + 1) (le_refl _) (α e),
    triple_action_expansion n m k (α e)] at he
  exact he

set_option maxHeartbeats 1000000 in
theorem embedded_canonical_trace_zero (n m k : ℕ)
    (hsize : n + m + k + 2 ≤ Fintype.card E)
    (hchoose : ((n + m).choose n : K) * ((n + m + k).choose (n + m) : K) = 0)
    (g : Representation.IntertwiningMap ((tripleAction n m k).comp α.toMultiplicative)
      ((dualAction K (n + m + k + 1)).comp α.toMultiplicative)) :
    LinearMap.trace K (DualPower K (n + m + k + 1))
      (g.toLinearMap.comp (embeddedTripleDelta α n m k).toLinearMap) = 0 := by
  let d := embeddedDelta α n m
  let e := embeddedDelta α (n + m) k
  let τ := (dualAction K (k + 1)).comp α.toMultiplicative
  rcases mul_eq_zero.mp hchoose with hd | he
  · have hdt : ∀ q : Representation.IntertwiningMap
        ((tensorAction K n m).comp α.toMultiplicative)
        ((dualAction K (n + m + 1)).comp α.toMultiplicative),
        LinearMap.trace K (DualPower K (n + m + 1))
        (q.toLinearMap.comp d.toLinearMap) = 0 := by
      intro q
      exact embedded_composition_trace_zero α hα n m (by omega) hd d q
    have ht := Representation.IntertwiningMap.trace_pairing_zero_rTensor
      (τ := τ) d hdt (e.comp g)
    change LinearMap.trace K (DualPower K (n + m + k + 1))
      (g.toLinearMap.comp ((d.rTensor τ).toLinearMap.comp e.toLinearMap)) = 0
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
    change LinearMap.trace K (DualPower K (n + m + 1) ⊗[K] DualPower K (k + 1))
      ((e.toLinearMap.comp g.toLinearMap).comp (d.rTensor τ).toLinearMap) = 0 at ht
    simpa only [LinearMap.comp_assoc] using ht
  · exact embedded_composition_trace_zero α hα (n + m) k hsize he e
      (g.comp (d.rTensor τ))

/-- Every equivariant trace pairing with the triple tensor vanishes when the product of
the two binomial coefficients vanishes. The field and embedding universes are independent. -/
theorem embedded_composition_trace_zero (n m k : ℕ)
    (hsize : n + m + k + 2 ≤ Fintype.card E)
    (hchoose : ((n + m).choose n : K) * ((n + m + k).choose (n + m) : K) = 0)
    (f : Representation.IntertwiningMap
      ((dualAction K (n + m + k + 1)).comp α.toMultiplicative)
      ((tripleAction n m k).comp α.toMultiplicative))
    (g : Representation.IntertwiningMap ((tripleAction n m k).comp α.toMultiplicative)
      ((dualAction K (n + m + k + 1)).comp α.toMultiplicative)) :
    LinearMap.trace K (DualPower K (n + m + k + 1))
      (g.toLinearMap.comp f.toLinearMap) = 0 := by
  have hf : f (dualBasis K (n + m + k + 1) (Fin.last (n + m + k))) =
      tripleCoefficient n m k (Fin.last (n + m + k))
        (f (dualBasis K (n + m + k + 1) 0)) := by
    have he := LinearMap.congr_fun
      (restricted_triple_intertwines_coefficients α hα (by omega) f
        (Fin.last (n + m + k))) (dualBasis K (n + m + k + 1) 0)
    have hcyc : coefficient K (n + m + k + 1) (n + m + k)
        (dualBasis K (n + m + k + 1) 0) =
        dualBasis K (n + m + k + 1) (Fin.last (n + m + k)) := by
      simpa only [Fin.val_last] using
        coefficient_cyclic K (n + m + k) (Fin.last (n + m + k))
    simpa only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply,
      Fin.val_last, hcyc] using he
  obtain ⟨c, hc⟩ := triple_coefficient_top_range n m k
    (f (dualBasis K (n + m + k + 1) 0))
  have hf' : f (dualBasis K (n + m + k + 1) (Fin.last (n + m + k))) =
      c • embeddedTripleDelta α n m k
        (dualBasis K (n + m + k + 1) (Fin.last (n + m + k))) := by
    rw [hf, hc, embedded_triple_delta_top]
  have ht := embedded_endomorphism_trace α hα (n + m + k) hsize (g.comp f)
  have hΔ := embedded_endomorphism_trace α hα (n + m + k) hsize
    (g.comp (embeddedTripleDelta α n m k))
  have hz := embedded_canonical_trace_zero α hα n m k hsize hchoose g
  change LinearMap.trace K (DualPower K (n + m + k + 1))
      (g.toLinearMap.comp f.toLinearMap) =
    ((n + m + k + 1 : ℕ) : K) *
      g (f (dualBasis K (n + m + k + 1) (Fin.last (n + m + k))))
        (Polynomial.degreeLT.basis K (n + m + k + 1) (Fin.last (n + m + k))) at ht
  rw [ht, hf', map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hΔ' : ((n + m + k + 1 : ℕ) : K) *
      g (embeddedTripleDelta α n m k
        (dualBasis K (n + m + k + 1) (Fin.last (n + m + k))))
        (Polynomial.degreeLT.basis K (n + m + k + 1) (Fin.last (n + m + k))) = 0 :=
    hΔ.symm.trans hz
  calc
    _ = c * (((n + m + k + 1 : ℕ) : K) *
      g (embeddedTripleDelta α n m k
        (dualBasis K (n + m + k + 1) (Fin.last (n + m + k))))
        (Polynomial.degreeLT.basis K (n + m + k + 1) (Fin.last (n + m + k)))) := by ring
    _ = 0 := by rw [hΔ', mul_zero]

end Embedded

end D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTripleTensorObstruction
