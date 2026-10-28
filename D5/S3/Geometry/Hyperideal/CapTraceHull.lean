/- GID: D5/S3/Geometry/Hyperideal/CapTraceHull
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CapTraceHull
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Hull]
   utility: none
   digest: A coordinate support zero trace is the convex hull of the endpoints on that cap. -/

import D5.S3.Geometry.Hyperideal.LengthGramPolytope
import D5.S3.Geometry.Hyperideal.ZeroTraceHull
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.CapTraceHull

abbrev V := Fin 4 → ℝ
abbrev Support := Fin 4 ⊕ Fin 4

def support (l : Fin 6 → ℝ) : Support → V →ₗ[ℝ] ℝ
  | Sum.inl i => -(LinearMap.proj i)
  | Sum.inr i => ∑ j, lengthGram l i j • LinearMap.proj j

def incident : Support → Fin 4 → Fin 4 → Prop
  | Sum.inl k, i, j => k ≠ i ∧ k ≠ j
  | Sum.inr k, i, _ => k = i

instance (f : Support) (i j : Fin 4) : Decidable (incident f i j) := by
  cases f <;> dsimp [incident] <;> infer_instance

lemma support_body (l : Fin 6 → ℝ) (x : V) (hx : x ∈ cutBody l)
    (f : Support) : support l f x ≤ 0 := by
  cases f with
  | inl i => exact neg_nonpos.mpr (hx.1.1 i)
  | inr i => simpa [support] using hx.2 i

lemma endpoint_support (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) (i j : Fin 4) (hij : i ≠ j) :
    (incident f i j → support l f (endpoint l i j) = 0) ∧
    (¬ incident f i j → support l f (endpoint l i j) < 0) := by
  obtain ⟨_, hi, hj, hz, hr, ho⟩ := (cut_body_polytope l hl).2.2.2 i j hij
  cases f with
  | inl k =>
    constructor
    · rintro ⟨hki, hkj⟩
      simpa [support] using congrArg Neg.neg (hz k hki hkj)
    · intro h
      by_cases hki : k = i
      · subst k
        simpa [support] using neg_neg_of_pos hi
      · have hkj : k = j := by
          by_contra hkj
          exact h ⟨hki, hkj⟩
        subst k
        simpa [support] using neg_neg_of_pos hj
  | inr k =>
    constructor
    · intro h
      change k = i at h
      subst k
      simpa [support] using hr
    · intro h
      simpa [support] using ho k h

private lemma endpoint_support_zero_iff (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) (i j : Fin 4) (hij : i ≠ j) :
    support l f (endpoint l i j) = 0 ↔ incident f i j := by
  constructor
  · intro he
    by_contra hn
    exact ((endpoint_support l hl f i j hij).2 hn).ne he
  · exact (endpoint_support l hl f i j hij).1

def capEndpoint (l : Fin 6 → ℝ) (i : Fin 4) : {j : Fin 4 // j ≠ i} → V :=
  fun j => endpoint l i j

/-- The zero trace of a coordinate support is exactly the hull of its cap endpoints. -/
theorem cap_trace_hull (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (i : Fin 4) :
    {x ∈ cutBody l | support l (Sum.inr i) x = 0} =
      convexHull ℝ (range (capEndpoint l i)) := by
  let P : Set V := range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)
  have hP : convexHull ℝ P = cutBody l := (cut_body_polytope l hl).2.1
  have hz := D5.S3.Geometry.Hyperideal.ZeroTraceHull.zero_trace_hull P
    (fun _ : Unit => support l (Sum.inr i))
    (by
      rintro p ⟨⟨⟨a, b⟩, hab⟩, rfl⟩ _
      exact support_body l _ ((cut_body_polytope l hl).2.2.2 a b hab).1 _)
  have hverts : {p ∈ P | support l (Sum.inr i) p = 0} =
      range (capEndpoint l i) := by
    ext x
    constructor
    · rintro ⟨⟨⟨⟨a, b⟩, hab⟩, rfl⟩, hzero⟩
      have hi := (endpoint_support_zero_iff l hl (Sum.inr i) a b hab).mp hzero
      change i = a at hi
      subst a
      exact ⟨⟨b, hab.symm⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      let p : EndpointLabel := ⟨(i, j.1), Ne.symm j.2⟩
      refine ⟨⟨p, ?_⟩, ?_⟩
      · rfl
      · exact (endpoint_support l hl (Sum.inr i) i j.1 (Ne.symm j.2)).1 (by rfl)
  have hz' : {x ∈ convexHull ℝ P | support l (Sum.inr i) x = 0} =
      convexHull ℝ {p ∈ P | support l (Sum.inr i) p = 0} := by
    simpa only [forall_const] using hz.symm
  calc
    {x ∈ cutBody l | support l (Sum.inr i) x = 0} =
        {x ∈ convexHull ℝ P | support l (Sum.inr i) x = 0} := by
      rw [← hP]
    _ = convexHull ℝ {p ∈ P | support l (Sum.inr i) p = 0} := hz'
    _ = convexHull ℝ (range (capEndpoint l i)) := by
      rw [hverts]

#print axioms cap_trace_hull

end D5.S3.Geometry.Hyperideal.CapTraceHull
