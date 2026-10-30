/- GID: D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Quotient.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.Dual]
   utility: none
   digest: Actual rational cohomology quotients transport by coefficient evacuation, inverse transpose to nonloop cycle contraction. -/

import D5.S3.Combinatorics.Graph.Incidence.MultigraphContraction
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
The cohomology carrier is the quotient of all rational edge functions by the
range of the actual head-minus-tail coboundary. Only the edge type is finite.
Evacuation subtracts the deleted coefficient times the original target row;
its inverse on the quotient is zero extension. Evaluation on signed-incidence
cycles descends to this quotient and intertwines evacuation with the inverse
of the existing cycle equivalence. No cyclic-order or Jacobi relation is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity
open D5.S3.Combinatorics.Graph.Incidence.MultigraphContraction
open scoped BigOperators

universe u v
variable {V : Type u} {E : Type v}

/-- The actual endpoint coboundary on arbitrary vertex functions. -/
def coboundary (G : DirectedMultigraph V E) : (V → ℚ) →ₗ[ℚ] (E → ℚ) where
  toFun h f := h (G.target f) - h (G.source f)
  map_add' h k := by ext f; simp only [Pi.add_apply]; ring
  map_smul' c h := by ext f; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Native first graph cohomology: edge functions modulo actual coboundaries. -/
abbrev Cohomology (G : DirectedMultigraph V E) := (E → ℚ) ⧸ (coboundary G).range

section Contraction
variable [DecidableEq V] [DecidableEq E]

/-- Remove the selected coefficient using the incidence row at its target. -/
def evacuate (G : DirectedMultigraph V E) (e : E) :
    (E → ℚ) →ₗ[ℚ] (Surviving e → ℚ) where
  toFun a f := a f.val - a e * incidence G (G.target e) f.val
  map_add' a b := by ext f; simp only [Pi.add_apply]; ring
  map_smul' c a := by ext f; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Zero extension at exactly the deleted edge ID. -/
def extend (e : E) : (Surviving e → ℚ) →ₗ[ℚ] (E → ℚ) where
  toFun b f := if hf : f = e then 0 else b ⟨f, hf⟩
  map_add' a b := by ext f; by_cases hf : f = e <;> simp [hf]
  map_smul' c a := by ext f; by_cases hf : f = e <;> simp [hf]

private theorem restrict_vertexMap (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (k : V → ℚ) (w : V) :
    k (vertexMap G e h w).val =
      k w - (k (G.target e) - k (G.source e)) * (if w = G.target e then 1 else 0) := by
  by_cases hw : w = G.target e <;> simp [vertexMap, hw] <;> ring

/-- Evacuation sends an actual coboundary to the restricted vertex potential. -/
theorem evacuate_coboundary (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (k : V → ℚ) :
    evacuate G e (coboundary G k) =
      coboundary (contract G e h) (fun w => k w.val) := by
  ext f
  change k (G.target f.val) - k (G.source f.val) -
    (k (G.target e) - k (G.source e)) * incidence G (G.target e) f.val =
      k (vertexMap G e h (G.target f.val)).val -
        k (vertexMap G e h (G.source f.val)).val
  rw [restrict_vertexMap G e h k (G.target f.val),
    restrict_vertexMap G e h k (G.source f.val)]
  by_cases ht : G.target f.val = G.target e <;>
    by_cases hs : G.source f.val = G.target e <;>
      simp_all [incidence, signedIncidence, eq_comm] <;> ring

/-- Zero extension of a contracted coboundary is pullback along vertexMap. -/
theorem extend_coboundary (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (k : ContractedVertex G e → ℚ) :
    extend e (coboundary (contract G e h) k) =
      coboundary G (k ∘ vertexMap G e h) := by
  ext f
  by_cases hf : f = e
  · subst f
    simp [extend, coboundary, vertexMap, h]
  · simp [extend, hf, coboundary, contract, Function.comp_def]

/-- Evacuation after zero extension preserves every surviving coordinate. -/
theorem evacuate_extend (G : DirectedMultigraph V E) (e : E) (b : Surviving e → ℚ) :
    evacuate G e (extend e b) = b := by
  ext f
  simp [evacuate, extend, f.property]

/-- The other composite differs from the identity by this exact coboundary. -/
theorem extend_evacuate_sub (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (a : E → ℚ) :
    extend e (evacuate G e a) - a =
      coboundary G (fun w => -a e * (if w = G.target e then 1 else 0)) := by
  ext f
  by_cases hf : f = e
  · subst f
    simp [extend, coboundary, h]
  · by_cases ht : G.target f = G.target e <;>
      by_cases hs : G.source f = G.target e <;>
        simp_all [extend, evacuate, coboundary, incidence, signedIncidence, eq_comm] <;> ring

private def quotientEvacuate (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) :
    Cohomology G →ₗ[ℚ] Cohomology (contract G e h) :=
  (coboundary G).range.mapQ (coboundary (contract G e h)).range (evacuate G e) (by
    rintro a ⟨k, rfl⟩
    exact ⟨fun w => k w.val, (evacuate_coboundary G e h k).symm⟩)

private def quotientExtend (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) :
    Cohomology (contract G e h) →ₗ[ℚ] Cohomology G :=
  (coboundary (contract G e h)).range.mapQ (coboundary G).range (extend e) (by
    rintro a ⟨k, rfl⟩
    exact ⟨k ∘ vertexMap G e h, (extend_coboundary G e h k).symm⟩)

/-- Explicit mutually inverse maps on the native cohomology quotients. -/
def cohomologyEquiv (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) :
    Cohomology G ≃ₗ[ℚ] Cohomology (contract G e h) where
  toLinearMap := quotientEvacuate G e h
  invFun := quotientExtend G e h
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with | H a =>
      change Submodule.Quotient.mk (extend e (evacuate G e a)) =
        (Submodule.Quotient.mk a : Cohomology G)
      apply (Submodule.Quotient.eq (coboundary G).range).mpr
      exact ⟨_, (extend_evacuate_sub G e h a).symm⟩
  right_inv x := by
    induction x using Submodule.Quotient.induction_on with | H b =>
      change Submodule.Quotient.mk (evacuate G e (extend e b)) =
        (Submodule.Quotient.mk b : Cohomology (contract G e h))
      rw [evacuate_extend]

/-- Both quotient maps compute on every representative, with no chosen splitting. -/
theorem cohomologyEquiv_representatives (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) :
    (∀ a : E → ℚ, cohomologyEquiv G e h ((coboundary G).range.mkQ a) =
      (coboundary (contract G e h)).range.mkQ (evacuate G e a)) ∧
    (∀ b : Surviving e → ℚ,
      (cohomologyEquiv G e h).symm ((coboundary (contract G e h)).range.mkQ b) =
        (coboundary G).range.mkQ (extend e b)) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

end Contraction

section Pairing
variable [DecidableEq V] [Fintype E]

/-- Finite support needed for summing vertex potentials; isolates need no enumeration. -/
def endpoints (G : DirectedMultigraph V E) : Finset V :=
  Finset.univ.image G.source ∪ Finset.univ.image G.target

private theorem endpoint_duality (G : DirectedMultigraph V E) (k : V → ℚ) (z : E → ℚ) :
    (∑ f : E, coboundary G k f * z f) =
      ∑ w ∈ endpoints G, k w * boundary G z w := by
  symm
  calc
    _ = ∑ w ∈ endpoints G, ∑ f : E, k w * (incidence G w f * z f) := by
      simp only [boundary, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ = ∑ f : E, ∑ w ∈ endpoints G, k w * (incidence G w f * z f) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      have ht : G.target f ∈ endpoints G :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩)
      have hs : G.source f ∈ endpoints G :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩)
      simp only [incidence, signedIncidence, Int.cast_sub, Int.cast_ite,
        Int.cast_one, Int.cast_zero, sub_mul, mul_sub, Finset.sum_sub_distrib]
      simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq', ht, hs, ite_true, one_mul]
      change k (G.target f) * z f - k (G.source f) * z f = _
      change _ = (k (G.target f) - k (G.source f)) * z f
      ring

/-- Every actual coboundary annihilates every actual signed-incidence cycle. -/
theorem coboundary_annihilates_cycles (G : DirectedMultigraph V E)
    (k : V → ℚ) (z : CycleSpace G) :
    (∑ f : E, coboundary G k f * z.val f) = 0 := by
  rw [endpoint_duality]
  have hz (w : V) : boundary G z.val w = 0 := congrFun z.property w
  simp only [hz, mul_zero, Finset.sum_const_zero]

/-- Restrict the standard edge-coordinate functional to the existing cycle subspace. -/
def cycleEvaluation [DecidableEq E] (G : DirectedMultigraph V E) :
    (E → ℚ) →ₗ[ℚ] Module.Dual ℚ (CycleSpace G) :=
  (CycleSpace G).subtype.dualMap.comp (dotProductEquiv ℚ E).toLinearMap

/-- Evaluation descends through actual coboundaries, not through an assumed relation. -/
def cohomologyPairing [DecidableEq E] (G : DirectedMultigraph V E) :
    Cohomology G →ₗ[ℚ] Module.Dual ℚ (CycleSpace G) :=
  (coboundary G).range.liftQ (cycleEvaluation G) (by
    rintro a ⟨k, rfl⟩
    apply LinearMap.ext
    intro z
    change (∑ f : E, coboundary G k f * z.val f) = 0
    exact coboundary_annihilates_cycles G k z)

end Pairing

section Naturality
variable [DecidableEq V] [DecidableEq E] [Fintype E]

private theorem inverse_cycle_coefficients (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (z : CycleSpace (contract G e h)) :
    ((cycleEquiv G e h).symm z).val e = -residual G e z.val (G.target e) ∧
    ∀ f : Surviving e, ((cycleEquiv G e h).symm z).val f.val = z.val f := by
  constructor
  · simp [cycleEquiv, lift]
  · intro f
    simp [cycleEquiv, lift, f.property]

private theorem evacuation_inverse_transpose (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (a : E → ℚ)
    (z : CycleSpace (contract G e h)) :
    (∑ f : Surviving e, evacuate G e a f * z.val f) =
      ∑ f : E, a f * ((cycleEquiv G e h).symm z).val f := by
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun f : E => a f * ((cycleEquiv G e h).symm z).val f) e]
  rw [(inverse_cycle_coefficients G e h z).1]
  simp_rw [(inverse_cycle_coefficients G e h z).2]
  change (∑ f : Surviving e,
    (a f.val - a e * incidence G (G.target e) f.val) * z.val f) = _
  simp only [sub_mul, Finset.sum_sub_distrib, residual, mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- Representative evaluation and both directions of inverse-transpose naturality. -/
theorem cohomology_pairing_naturality (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) :
    (∀ (a : E → ℚ) (z : CycleSpace G),
      cohomologyPairing G ((coboundary G).range.mkQ a) z = ∑ f : E, a f * z.val f) ∧
    (∀ (a : Cohomology G) (z : CycleSpace (contract G e h)),
      cohomologyPairing (contract G e h) (cohomologyEquiv G e h a) z =
        cohomologyPairing G a ((cycleEquiv G e h).symm z)) ∧
    (∀ (b : Cohomology (contract G e h)) (z : CycleSpace G),
      cohomologyPairing G ((cohomologyEquiv G e h).symm b) z =
        cohomologyPairing (contract G e h) b (cycleEquiv G e h z)) := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro a z
    induction a using Submodule.Quotient.induction_on with | H a =>
      change cohomologyPairing (contract G e h)
        (cohomologyEquiv G e h ((coboundary G).range.mkQ a)) z = _
      rw [(cohomologyEquiv_representatives G e h).1]
      exact evacuation_inverse_transpose G e h a z
  · intro b z
    induction b using Submodule.Quotient.induction_on with | H b =>
      change cohomologyPairing G
        ((cohomologyEquiv G e h).symm ((coboundary (contract G e h)).range.mkQ b)) z = _
      rw [(cohomologyEquiv_representatives G e h).2]
      have hb := evacuation_inverse_transpose G e h (extend e b) (cycleEquiv G e h z)
      rw [evacuate_extend, LinearEquiv.symm_apply_apply] at hb
      exact hb.symm

#print axioms cohomologyEquiv
#print axioms coboundary_annihilates_cycles
#print axioms cohomology_pairing_naturality

end Naturality
end D5.S3.Combinatorics.Graph.Incidence.MultigraphCohomologyContraction
