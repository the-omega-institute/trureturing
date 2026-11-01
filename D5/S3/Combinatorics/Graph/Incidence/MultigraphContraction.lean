/- GID: D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/MultigraphContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonloop contraction preserves rational signed-incidence cycles by literal restriction of surviving edge coordinates. -/

import D5.S3.ConceptDynamics.Coding.EssentialWordRealization
import D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
The endpoint carrier is EssentialWordRealization.DirectedMultigraph, with no
simplicity, connectedness, essentiality, or cyclic-order condition. The boundary
is the rational cast of SignedIncidenceTotalUnimodularity.signedIncidence:
head minus tail. Only the edge type is required to be finite.

Contraction removes the target vertex of a selected nonloop edge, maps that
vertex to its source, and deletes exactly the selected edge ID. The remaining
IDs and their orientations are retained, including loops and parallel edges.
The inverse on cycles reconstructs the deleted coefficient as the negative
remaining boundary at its original target. This is the cycle-space step of the
common-contraction argument in the supplied marked-four-loop proof, not a
statement about cyclic orders, AS/IHX/CL, cohomology, or a Jacobi quotient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.MultigraphContraction

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity
open scoped BigOperators

universe u v

variable {V : Type u} {E : Type v}

/-- Exact rational cast of the existing head-minus-tail integer matrix. -/
def incidence [DecidableEq V] (G : DirectedMultigraph V E) : Matrix V E ℚ :=
  fun v f => (signedIncidence G.source G.target v f : ℚ)

private theorem incidence_apply [DecidableEq V] (G : DirectedMultigraph V E)
    (v : V) (f : E) : incidence G v f =
      (if v = G.target f then 1 else 0) - (if v = G.source f then 1 else 0) := by
  by_cases hh : v = G.target f <;> by_cases ht : v = G.source f <;>
    simp [incidence, signedIncidence, hh, ht]

/-- Actual signed boundary on edge coordinates. -/
def boundary [DecidableEq V] [Fintype E] (G : DirectedMultigraph V E) :
    (E → ℚ) →ₗ[ℚ] (V → ℚ) :=
  (incidence G).mulVecLin

/-- Rational cycles, defined as the kernel of the actual signed boundary. -/
abbrev CycleSpace [DecidableEq V] [Fintype E] (G : DirectedMultigraph V E) :=
  LinearMap.ker (boundary G)

/-- All original edge IDs except the selected ID. -/
abbrev Surviving (e : E) := {f : E // f ≠ e}

/-- All original vertices except the target of the selected edge. -/
abbrev ContractedVertex (G : DirectedMultigraph V E) (e : E) :=
  {v : V // v ≠ G.target e}

/-- Identify the target with the source, fixing every other vertex. -/
def vertexMap [DecidableEq V] (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (w : V) : ContractedVertex G e :=
  if hw : w = G.target e then ⟨G.source e, h⟩ else ⟨w, hw⟩

/-- Endpoint contraction on the existing multigraph structure. -/
def contract [DecidableEq V] (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) :
    DirectedMultigraph (ContractedVertex G e) (Surviving e) where
  source f := vertexMap G e h (G.source f.val)
  target f := vertexMap G e h (G.target f.val)

private theorem vertexMap_fiber [DecidableEq V] (G : DirectedMultigraph V E)
    (e : E) (h : G.source e ≠ G.target e) (w : V) (v : ContractedVertex G e) :
    vertexMap G e h w = v ↔
      w = v.val ∨ (w = G.target e ∧ v.val = G.source e) := by
  rw [Subtype.ext_iff]
  by_cases hw : w = G.target e
  · subst w
    simp [vertexMap, v.property, Ne.symm v.property, eq_comm]
  · simp [vertexMap, hw]

section FiniteEdges

variable [DecidableEq V] [DecidableEq E] [Fintype E]

/-- Literal surviving-edge coordinate restriction. -/
def restrict (e : E) : (E → ℚ) →ₗ[ℚ] (Surviving e → ℚ) where
  toFun x f := x f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Original boundary contribution of all surviving edge IDs. -/
def residual (G : DirectedMultigraph V E) (e : E) (x : Surviving e → ℚ)
    (v : V) : ℚ := ∑ f : Surviving e, incidence G v f.val * x f

private theorem boundary_apply (G : DirectedMultigraph V E) (x : E → ℚ) (v : V) :
    boundary G x v = ∑ f : E, incidence G v f * x f := rfl

private theorem boundary_split (G : DirectedMultigraph V E) (e : E)
    (x : E → ℚ) (v : V) : boundary G x v =
      incidence G v e * x e + residual G e (restrict e x) v := by
  rw [boundary_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun f : E => incidence G v f * x f) e]
  rfl

private theorem contracted_incidence (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (v : ContractedVertex G e) (f : Surviving e) :
    incidence (contract G e h) v f = incidence G v.val f.val +
      if v.val = G.source e then incidence G (G.target e) f.val else 0 := by
  have hvb := v.property
  have hfiber (w : V) : v = vertexMap G e h w ↔
      w = v.val ∨ (w = G.target e ∧ v.val = G.source e) := by
    constructor
    · intro hv
      exact (vertexMap_fiber G e h w v).mp hv.symm
    · intro hv
      exact ((vertexMap_fiber G e h w v).mpr hv).symm
  simp only [incidence_apply, contract, hfiber]
  by_cases hva : v.val = G.source e <;>
    by_cases hvh : G.target f.val = v.val <;>
    by_cases hvta : G.source f.val = v.val <;>
    by_cases hbh : G.target f.val = G.target e <;>
    by_cases hbt : G.source f.val = G.target e <;>
    simp_all [eq_comm] <;>
      first
      | ring
      | exact fun hs => h (hs.trans hbh.symm)

private theorem contracted_boundary (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (x : Surviving e → ℚ)
    (v : ContractedVertex G e) :
    boundary (contract G e h) x v = residual G e x v.val +
      if v.val = G.source e then residual G e x (G.target e) else 0 := by
  change (∑ f : Surviving e, incidence (contract G e h) v f * x f) = _
  simp_rw [contracted_incidence]
  by_cases hv : v.val = G.source e <;>
    simp [hv, residual, add_mul, Finset.sum_add_distrib]

private theorem restrict_cycle (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (z : CycleSpace G) :
    restrict e z.val ∈ CycleSpace (contract G e h) := by
  apply LinearMap.mem_ker.mpr
  funext v
  have hz (w : V) : boundary G z.val w = 0 := congrFun z.property w
  have hv := boundary_split G e z.val v.val
  have hb := boundary_split G e z.val (G.target e)
  rw [contracted_boundary]
  by_cases ha : v.val = G.source e
  · have hvb := v.property
    simp only [incidence_apply, ha, if_pos rfl, if_neg h, if_neg (Ne.symm h)] at hv hb
    simp only [hz] at hv hb
    simp only [Pi.zero_apply] at hv hb ⊢
    simp only [ha, if_pos rfl]
    simp only [if_true, if_false, zero_sub, one_mul, zero_mul, sub_zero,
      add_zero, zero_add] at hv hb ⊢
    linarith
  · have hvb := v.property
    simp [incidence_apply, ha, hvb, hz] at hv
    simp only [Pi.zero_apply] at hv ⊢
    simp only [ha, if_false]
    linarith

/-- Reconstruct the removed coefficient using the original target balance. -/
def lift (G : DirectedMultigraph V E) (e : E) (x : Surviving e → ℚ) : E → ℚ :=
  fun f => if hf : f = e then -residual G e x (G.target e) else x ⟨f, hf⟩

private theorem restrict_lift (G : DirectedMultigraph V E) (e : E)
    (x : Surviving e → ℚ) : restrict e (lift G e x) = x := by
  funext f
  simp [restrict, lift, f.property]

private theorem lift_cycle (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (z : CycleSpace (contract G e h)) :
    lift G e z.val ∈ CycleSpace G := by
  apply LinearMap.mem_ker.mpr
  funext v
  rw [boundary_split G e, restrict_lift]
  by_cases hvb : v = G.target e
  · subst v
    simp [lift, incidence_apply, Ne.symm h]
  · have hz := congrFun z.property (⟨v, hvb⟩ : ContractedVertex G e)
    rw [contracted_boundary] at hz
    by_cases hva : v = G.source e
    · simp only [hva, if_pos rfl] at hz
      simp only [Pi.zero_apply] at hz ⊢
      simp [lift, incidence_apply, hva, h] at hz ⊢
      linarith
    · simpa [incidence_apply, hvb, hva, Pi.zero_apply] using hz

private theorem lift_restrict_cycle (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) (z : CycleSpace G) :
    lift G e (restrict e z.val) = z.val := by
  funext f
  by_cases hf : f = e
  · subst f
    have hz := congrFun z.property (G.target e)
    rw [boundary_split G e] at hz
    simp only [incidence_apply, if_pos rfl, if_neg (Ne.symm h), sub_zero,
      one_mul] at hz
    simp only [Pi.zero_apply] at hz ⊢
    simp [lift] at hz ⊢
    linarith
  · simp [lift, hf, restrict]

/-- Explicit equivalence: restriction forward, target-balance reconstruction backward. -/
def cycleEquiv (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) :
    CycleSpace G ≃ₗ[ℚ] CycleSpace (contract G e h) where
  toFun z := ⟨restrict e z.val, restrict_cycle G e h z⟩
  invFun z := ⟨lift G e z.val, lift_cycle G e h z⟩
  left_inv z := Subtype.ext (lift_restrict_cycle G e h z)
  right_inv z := Subtype.ext (restrict_lift G e z.val)
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Actual endpoint contraction and the cycle equivalence with both coordinate rules. -/
theorem nonloop_contraction_cycle_equiv (G : DirectedMultigraph V E) (e : E)
    (h : G.source e ≠ G.target e) :
    (∀ (w : V) (v : ContractedVertex G e), vertexMap G e h w = v ↔
      w = v.val ∨ (w = G.target e ∧ v.val = G.source e)) ∧
    ∃ Φ : CycleSpace G ≃ₗ[ℚ] CycleSpace (contract G e h),
      (∀ (z : CycleSpace G) (f : Surviving e), (Φ z).val f = z.val f.val) ∧
      (∀ z : CycleSpace (contract G e h),
        (Φ.symm z).val e = -residual G e z.val (G.target e)) ∧
      (∀ (z : CycleSpace (contract G e h)) (f : Surviving e),
        (Φ.symm z).val f.val = z.val f) := by
  refine ⟨vertexMap_fiber G e h, cycleEquiv G e h, ?_, ?_, ?_⟩
  · intro z f
    rfl
  · intro z
    simp [cycleEquiv, lift]
  · intro z f
    simp [cycleEquiv, lift, f.property]

#print axioms nonloop_contraction_cycle_equiv

end FiniteEdges
end D5.S3.Combinatorics.Graph.Incidence.MultigraphContraction
