/- GID: D5/S3/Quantum/Foundation/CircuitBalancedConfirmation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/CircuitBalancedConfirmation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Circuit balance constructs reciprocal least confirmation on the original cone. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.NNReal.Defs

/-!
The normalized base, its full extreme-point set, and the full proper interval
are defined on the same real carrier. The conic-generation hypothesis below
is explicit: its derivation from a closed pointed generating cone and a strictly
positive unit is not supplied by this module. No reciprocity, relation descent,
least confirmation or finite-mixture law is assumed.

The signed support-contained circuit decomposition is reused directly from
NonnegativeKernelCircuit.OrderedField.signConformalGlobalKernelCircuitDecomposition.
The new construction descends balanced readings and uses the full proper interval
twice, at interchanged references, to force reciprocity and least confirmation.
The auxiliary binding lemmas are consumed by this construction.
Literature priority is not asserted.
-/

noncomputable section
open scoped BigOperators Matrix NNReal

namespace D5.S3.Quantum.Foundation.CircuitBalancedConfirmation

open D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.OrderedField

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- The entire normalized base of the specified original cone and unit. -/
def base (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) : Set A :=
  {x | x ∈ C ∧ u x = 1}

/-- All extreme points of the entire normalized base. -/
def pure (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) : Set A :=
  (base C u).extremePoints ℝ

/-- All proper effects on the original cone, with no restricted-effect supplier. -/
def proper (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (f : A →ₗ[ℝ] ℝ) : Prop :=
  ∀ x ∈ C, 0 ≤ f x ∧ f x ≤ u x

/-- The entire confirming subset of the proper interval. -/
def confirms (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p : A)
    (f : A →ₗ[ℝ] ℝ) : Prop := proper C u f ∧ f p = 1

/-- The lower envelope of all original proper confirming effects. -/
def comparison (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) (p x : A) : ℝ :=
  sInf {r | ∃ f : A →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = r}

/-- A nonzero relation minimal among all signed relations on the same labels.
The finite ambient set may contain unused labels; minimality concerns actual support. -/
def circuit {P : Set A} (s : Finset P) (c : s → ℝ) : Prop :=
  c ≠ 0 ∧ (∑ i, c i • (i.1 : A)) = 0 ∧
    ∀ w : s → ℝ, (∑ i, w i • (i.1 : A)) = 0 → w ≠ 0 →
      Function.support w ⊆ Function.support c →
      Function.support w = Function.support c

/-- Balance on every actual minimal-support pure relation. Subtype labels are distinct. -/
def balanced (P : Set A) (v : P → ℝ) : Prop :=
  ∀ (s : Finset P) (c : s → ℝ), circuit s c → ∑ i, c i * v i.1 = 0

private theorem coordinates_relation {P : Set A} (s : Finset P) (c : s → ℝ) :
    (fun r i => (Module.finBasis ℝ A).equivFun (i.1 : A) r) *ᵥ c = 0 ↔
      (∑ i, c i • (i.1 : A)) = 0 := by
  constructor
  · intro h
    apply (Module.finBasis ℝ A).equivFun.injective
    ext r
    simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun h r
  · intro h
    ext r
    have hh := congrArg (fun x => (Module.finBasis ℝ A).equivFun x r) h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hh

private theorem preserves_finite_relations {P : Set A} {v : P → ℝ}
    (hv : balanced P v) (s : Finset P) (x : s → ℝ)
    (hx : (∑ i, x i • (i.1 : A)) = 0) : ∑ i, x i * v i.1 = 0 := by
  classical
  let B : Matrix (Fin (Module.finrank ℝ A)) s ℝ :=
    fun r i => (Module.finBasis ℝ A).equivFun (i.1 : A) r
  obtain ⟨n, c, hc, _, _, _, hcir⟩ :=
    signConformalGlobalKernelCircuitDecomposition B x ((coordinates_relation s x).mpr hx)
  have hz (j : Fin n) : ∑ i, c j i * v i.1 = 0 := by
    obtain ⟨hne, hker, _, hmin⟩ := hcir j
    apply hv s (c j)
    refine ⟨hne, (coordinates_relation s (c j)).mp hker, ?_⟩
    intro w hw hne' hs
    exact hmin w ((coordinates_relation s w).mpr hw) hne' hs
  calc
    ∑ i, x i * v i.1 = ∑ j, ∑ i, c j i * v i.1 := by
      rw [← hc]
      simp only [Finset.sum_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = 0 := Finset.sum_eq_zero (fun j _ => hz j)

private theorem descends {P : Set A} {v : P → ℝ} (hv : balanced P v)
    (hspan : Submodule.span ℝ P = ⊤) :
    ∃ e : A →ₗ[ℝ] ℝ, ∀ p : P, e p = v p := by
  classical
  let Q : (P →₀ ℝ) →ₗ[ℝ] A := Finsupp.linearCombination ℝ (fun p : P => (p : A))
  let V : (P →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ v
  have hsur : Function.Surjective Q := by
    apply LinearMap.range_eq_top.mp
    simpa only [Q, Finsupp.range_linearCombination, Subtype.range_coe_subtype,
      Set.ofPred_mem_eq] using hspan
  have hker : LinearMap.ker Q ≤ LinearMap.ker V := by
    intro c hc
    have hx : (∑ i : c.support, c i.1 • (i.1 : A)) = 0 := by
      exact (Finset.sum_coe_sort c.support (fun i : P => c i • (i : A))).trans hc
    have hh := preserves_finite_relations hv c.support (fun i => c i.1) hx
    change (∑ i ∈ c.support, c i * v i) = 0
    exact (Finset.sum_coe_sort c.support (fun i : P => c i * v i)).symm.trans hh
  let e := (Q.liftOfSurjective hsur) ⟨V, hker⟩
  refine ⟨e, fun p => ?_⟩
  have he := Q.equivOfSurjective_apply hsur hker (m := Finsupp.single p 1)
  simpa [Q, V, e] using he

omit [FiniteDimensional ℝ A] in
private theorem pure_mem {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (p : pure C u) : (p : A) ∈ C ∧ u p = 1 :=
  p.property.1

private theorem base_convex (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) :
    Convex ℝ (base C u) := by
  intro x hx y hy a b ha hb hab
  refine ⟨C.add_mem (C.smul_mem ha hx.1) (C.smul_mem hb hy.1), ?_⟩
  simpa only [map_add, map_smul, smul_eq_mul, hx.2, hy.2, mul_one] using hab

private theorem normalized_mem {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x) {x : A} (hx : x ∈ C) (hne : x ≠ 0) :
    (u x)⁻¹ • x ∈ base C u := by
  refine ⟨C.smul_mem (inv_nonneg.mpr (hu x hx hne).le) hx, ?_⟩
  simp [map_smul, (hu x hx hne).ne']

private theorem base_compact {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set A))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x) : IsCompact (base C u) := by
  have hK : IsClosed (base C u) :=
    hclosed.inter (isClosed_eq u.continuous_of_finiteDimensional continuous_const)
  rcases (base C u).eq_empty_or_nonempty with hempty | ⟨x, hx⟩
  · rw [hempty]
    exact isCompact_empty
  have hne (z : A) (hz : z ∈ base C u) : z ≠ 0 := by
    intro he
    simpa [he] using hz.2
  have hsphere (z : A) (hz : z ∈ C) (hz0 : z ≠ 0) :
      ‖z‖⁻¹ • z ∈ ({y | y ∈ C ∧ ‖y‖ = 1} : Set A) := by
    refine ⟨C.smul_mem (inv_nonneg.mpr (norm_nonneg z)) hz, ?_⟩
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
      norm_ne_zero_iff.mpr hz0]
  have hS : IsCompact ({y | y ∈ C ∧ ‖y‖ = 1} : Set A) := by
    simpa [Metric.sphere, dist_zero_right] using (isCompact_sphere (0 : A) 1).inter_left hclosed
  obtain ⟨y, hy, hmin⟩ := hS.exists_isMinOn
    ⟨‖x‖⁻¹ • x, hsphere x hx.1 (hne x hx)⟩ u.continuous_of_finiteDimensional.continuousOn
  have hy0 : y ≠ 0 := by
    intro he
    simpa [he] using hy.2
  have hm : 0 < u y := hu y hy.1 hy0
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨hK, isBounded_iff_forall_norm_le.mpr ⟨(u y)⁻¹, ?_⟩⟩
  intro z hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (hne z hz)
  have hh := hmin (hsphere z hz.1 (hne z hz))
  have hmz : u y ≤ 1 / ‖z‖ := by
    simpa [map_smul, hz.2, one_div] using hh
  have hh' := (le_div_iff₀ hz0).mp hmz
  exact (le_div_iff₀ hm).mpr (by simpa [mul_comm] using hh')

private theorem nonneg_on_cone {C : PointedCone ℝ A} {u f : A →ₗ[ℝ] ℝ}
    (hK : IsCompact (base C u))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hf : ∀ p : pure C u, 0 ≤ f p) : ∀ x ∈ C, 0 ≤ f x := by
  have hbase : ∀ x ∈ base C u, 0 ≤ f x := by
    have hsub : convexHull ℝ (pure C u) ⊆ {x | 0 ≤ f x} :=
      convexHull_min (fun x hx => hf ⟨x, hx⟩)
        ((convex_Ici (0 : ℝ)).linear_preimage f)
    have hcl : IsClosed {x : A | 0 ≤ f x} :=
      isClosed_le continuous_const f.continuous_of_finiteDimensional
    have hh := closure_minimal hsub hcl
    rw [show closure (convexHull ℝ (pure C u)) = base C u from
      closure_convexHull_extremePoints hK (base_convex C u)] at hh
    exact hh
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hh := hbase _ (normalized_mem hu hx hx0)
  have hux := hu x hx hx0
  simpa only [map_smul, smul_eq_mul, mul_nonneg_iff_of_pos_left (inv_pos.mpr hux)] using hh

private theorem cone_bound {C : PointedCone ℝ A} {u f : A →ₗ[ℝ] ℝ}
    (hK : IsCompact (base C u))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hf : ∀ p : pure C u, 0 ≤ f p ∧ f p ≤ 1) : proper C u f := by
  intro x hx
  refine ⟨nonneg_on_cone hK hu (fun p => (hf p).1) x hx, ?_⟩
  have hh := nonneg_on_cone (f := u - f) hK hu (fun p => ?_) x hx
  · simpa only [LinearMap.sub_apply, sub_nonneg] using hh
  · simpa only [LinearMap.sub_apply, (pure_mem p).2, sub_nonneg] using (hf p).2

private theorem pure_span {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hK : IsCompact (base C u))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    Submodule.span ℝ (pure C u) = ⊤ := by
  have hsub : base C u ⊆ Submodule.span ℝ (pure C u) := by
    have hh := closure_minimal
      (convexHull_min (Submodule.subset_span : pure C u ⊆ Submodule.span ℝ (pure C u))
        (Submodule.convex _))
      (Submodule.closed_of_finiteDimensional (Submodule.span ℝ (pure C u)))
    rwa [closure_convexHull_extremePoints hK (base_convex C u)] at hh
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro x hx
  by_cases hx0 : x = 0
  · exact hx0 ▸ Submodule.zero_mem _
  have hh := (Submodule.span ℝ (pure C u)).smul_mem (u x) (hsub (normalized_mem hu hx hx0))
  simpa only [smul_smul, mul_inv_cancel₀ (hu x hx hx0).ne', one_smul] using hh

private theorem comparison_bounds {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (hu : ∀ x ∈ C, 0 ≤ u x) (p q : pure C u) :
    0 ≤ comparison C u p q ∧ comparison C u p q ≤ 1 ∧ comparison C u p p = 1 := by
  have hunit : confirms C u p u := ⟨fun x hx => ⟨hu x hx, le_rfl⟩, (pure_mem p).2⟩
  have hne (x : A) : ({r | ∃ f : A →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = r} : Set ℝ).Nonempty :=
    ⟨u x, u, hunit, rfl⟩
  have hb (x : A) (hx : x ∈ C) :
      BddBelow {r | ∃ f : A →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = r} :=
    ⟨0, fun _ ⟨f, hf, he⟩ => he ▸ (hf.1 x hx).1⟩
  refine ⟨le_csInf (hne q) (fun _ ⟨f, hf, he⟩ => he ▸ (hf.1 q (pure_mem q).1).1), ?_, ?_⟩
  · exact (csInf_le (hb q (pure_mem q).1) ⟨u, hunit, rfl⟩).trans_eq (pure_mem q).2
  · apply le_antisymm
    · exact (csInf_le (hb p (pure_mem p).1) ⟨u, hunit, rfl⟩).trans_eq (pure_mem p).2
    · apply le_csInf (hne p)
      rintro r ⟨f, hf, he⟩
      exact le_of_eq (hf.2.symm.trans he)

/-- All-reference circuit balance constructs reciprocal least confirming effects on
the original carrier. Pure conic generation is an explicit application hypothesis. -/
theorem circuit_balance_least_confirmation
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤)
    (hb : ∀ p : pure C u, balanced (pure C u) (fun q => comparison C u q p)) :
    ∃ e : pure C u → (A →ₗ[ℝ] ℝ),
      (∀ p : pure C u, confirms C u p (e p)) ∧
      (∀ p q : pure C u, e p q = comparison C u q p) ∧
      (∀ p q : pure C u, comparison C u p q = comparison C u q p) ∧
      (∀ (p : pure C u) f, confirms C u p f → ∀ x ∈ C, e p x ≤ f x) ∧
      (∀ (p : pure C u) x, x ∈ C → comparison C u p x = e p x) ∧
      (∀ (p : pure C u) (n : ℕ) (q : Fin n → pure C u) (w : Fin n → ℝ),
        (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
        comparison C u p (∑ i, w i • (q i : A)) =
          ∑ i, w i * comparison C u (q i) p) := by
  classical
  have hu : ∀ x ∈ C, 0 ≤ u x := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · exact (hstrict x hx hx0).le
  have hK := base_compact hclosed hstrict
  have hext (p : pure C u) := descends (hb p) (pure_span hK hstrict hspan)
  choose e he using hext
  have hconf (p : pure C u) : confirms C u p (e p) := by
    refine ⟨cone_bound hK hstrict (fun q => ?_), ?_⟩
    · rw [he p q]
      exact ⟨(comparison_bounds hu q p).1, (comparison_bounds hu q p).2.1⟩
    · rw [he p p]
      exact (comparison_bounds hu p p).2.2
  have hle (p q : pure C u) : comparison C u p q ≤ comparison C u q p := by
    rw [← he p q]
    apply csInf_le
    · exact ⟨0, fun _ ⟨f, hf, hr⟩ => hr ▸ (hf.1 q (pure_mem q).1).1⟩
    · exact ⟨e p, hconf p, rfl⟩
  have hsym (p q : pure C u) : comparison C u p q = comparison C u q p :=
    le_antisymm (hle p q) (hle q p)
  have hleast (p : pure C u) (f : A →ₗ[ℝ] ℝ) (hf : confirms C u p f) :
      ∀ x ∈ C, e p x ≤ f x := by
    have hnon : ∀ q : pure C u, 0 ≤ (f - e p) q := by
      intro q
      have ht : comparison C u p q ≤ f q := by
        apply csInf_le
        · exact ⟨0, fun _ ⟨g, hg, hr⟩ => hr ▸ (hg.1 q (pure_mem q).1).1⟩
        · exact ⟨f, hf, rfl⟩
      simpa only [LinearMap.sub_apply, he p q, hsym p q, sub_nonneg] using ht
    intro x hx
    exact sub_nonneg.mp (nonneg_on_cone hK hstrict hnon x hx)
  have hexact (p : pure C u) (x : A) (hx : x ∈ C) :
      comparison C u p x = e p x := by
    change sInf {r | ∃ f : A →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = r} = e p x
    apply le_antisymm
    · exact csInf_le ⟨0, fun _ ⟨f, hf, hr⟩ => hr ▸ (hf.1 x hx).1⟩ ⟨e p, hconf p, rfl⟩
    · refine le_csInf (s := {r | ∃ f : A →ₗ[ℝ] ℝ, confirms C u p f ∧ f x = r}) ?_ ?_
      · exact ⟨e p x, e p, hconf p, rfl⟩
      · rintro r ⟨f, hf, hr⟩
        exact hr ▸ hleast p f hf x hx
  refine ⟨e, hconf, he, hsym, hleast, hexact, ?_⟩
  intro p n q w hw _
  rw [hexact p _ (C.sum_mem (fun i _ => C.smul_mem (hw i) (pure_mem (q i)).1))]
  simp only [map_sum, map_smul, smul_eq_mul, he]

#print axioms circuit_balance_least_confirmation

end D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
