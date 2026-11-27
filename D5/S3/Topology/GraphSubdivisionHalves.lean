/- GID: D5/S3/Topology/GraphSubdivisionHalves
   generality: G
   mirror-B: D5/B/S3/Topology/GraphSubdivisionHalves
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Compatible half-edge coordinates on subdivisions give a global interval-valued map. -/

import D5.S3.Topology.GraphSubdivisionIntervals
import OmegaBuild.Commands

/-! Compatible half-edge coordinates on subdivisions give a global interval-valued map. -/

compile_only_with_mathlib


namespace D5.S3.Topology.GraphSubdivisionHalves

open BarycentricBaseRigidity (retainedVertex)
open BarycentricGraphDistance (Face Vertex oneSkeleton)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open GraphSubdivisionIntervals (originalSupport originalSupport_retained)
open PathContiguity (intervalComplex IsIntervalMap)

set_option autoImplicit false
noncomputable section
local instance (X : Type*) : DecidableEq X := Classical.decEq X

variable {X : Type}

theorem split_charts (A : PreAbstractSimplicialComplex X) (m : ℕ)
    (left right : {e : Face A // e.val.val.card = 2} → Vertex A)
    (chart : {e : Face A // e.val.val.card = 2} → Vertex (intervalComplex (2 * 2 ^ m)) →
      Vertex (iteratedAmbient A (m + 1)).2)
    (hinj : ∀ e, Function.Injective (chart e))
    (hend : ∀ e i, (i.val = 0 → chart e i = retainedVertex (m + 1) (left e)) ∧
      (i.val = 2 * 2 ^ m → chart e i = retainedVertex (m + 1) (right e)))
    (hdisjoint : ∀ e d i j, i.val ≠ 0 → i.val ≠ 2 * 2 ^ m →
      chart e i = chart d j → e = d)
    (hcover : ∀ s, s ∈ (iteratedAmbient A (m + 1)).2 →
      (∃ v : Vertex A, s = {(retainedVertex (m + 1) v).val}) ∨
      ∃ e t, t ∈ intervalComplex (2 * 2 ^ m) ∧
        ∀ x : Vertex (iteratedAmbient A (m + 1)).2, x.val ∈ s →
          ∃ i, i.val ∈ t ∧ chart e i = x) :
    let M := 2 ^ m
    let P := (iteratedAmbient A (m + 1)).2
    ∃ (owner : Vertex P → Option (Vertex A)) (distance : Vertex P → ℕ),
      (∀ e i, owner (chart e i) = if i.val < M then some (left e)
        else if M < i.val then some (right e) else none) ∧
      (∀ e i, distance (chart e i) = max (M - i.val) (i.val - M)) ∧
      (∀ s, s ∈ P → ∃ w, ∀ x : Vertex P, x.val ∈ s → owner x = none ∨ owner x = w) ∧
      IsIntervalMap (oneSkeleton P) M distance ∧
      (∀ x, owner x = none → distance x = 0) ∧
      (∀ x, (¬ ∃ e i, chart e i = x) →
        ∃ v : Vertex A, x = retainedVertex (m + 1) v ∧ owner x = some v ∧ distance x = M) := by
  classical
  let M : ℕ := 2 ^ m
  let P := (iteratedAmbient A (m + 1)).2
  let E := {e : Face A // e.val.val.card = 2}
  let I := Vertex (intervalComplex (2 * M))
  have hM : 0 < M := by positivity
  let data (e : E) (i : I) : Option (Vertex A) × ℕ :=
    (if i.val < M then some (left e) else if M < i.val then some (right e) else none,
      max (M - i.val) (i.val - M))
  have at_end (e : E) (i : I) (hi : i.val = 0 ∨ i.val = 2 * M) :
      ∃ v : Vertex A, chart e i = retainedVertex (m + 1) v ∧ data e i = (some v, M) := by
    rcases hi with hi | hi
    · exact ⟨left e, (hend e i).1 hi, by simp [data, hi, hM]⟩
    · have hh : M < 2 * M := by omega
      exact ⟨right e, (hend e i).2 hi, by simp [data, hi, hh, hh.not_gt]; omega⟩
  have agree {e d : E} {i j : I} (he : chart e i = chart d j) : data e i = data d j := by
    by_cases hi : i.val = 0 ∨ i.val = 2 * M
    · by_cases hj : j.val = 0 ∨ j.val = 2 * M
      · obtain ⟨v, hv, hvdata⟩ := at_end e i hi
        obtain ⟨u, hu, hudata⟩ := at_end d j hj
        rw [hv, hu] at he
        have hraw := congrArg
          (fun x : Vertex P => originalSupport A (m + 1) {x.val}) he
        simp only [originalSupport_retained, Finset.singleton_inj] at hraw
        rw [hvdata, hudata, show v = u from Subtype.ext hraw]
      · have hd := hdisjoint d e j i (fun h => hj (Or.inl h)) (fun h => hj (Or.inr h)) he.symm
        subst d
        rw [hinj e he]
    · have hd := hdisjoint e d i j (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h)) he
      subst d
      rw [hinj e he]
  let onChart (x : Vertex P) : Prop := ∃ ei : E × I, chart ei.1 ei.2 = x
  have isolated {x : Vertex P} (hx : ¬ onChart x) :
      ∃ v : Vertex A, x = retainedVertex (m + 1) v := by
    rcases hcover {x.val} x.property with ⟨v, hv⟩ | ⟨e, t, _, honto⟩
    · exact ⟨v, Subtype.ext (Finset.singleton_injective hv)⟩
    · obtain ⟨i, _, hi⟩ := honto x (Finset.mem_singleton_self _)
      exact (hx ⟨(e, i), hi⟩).elim
  let global (x : Vertex P) : Option (Vertex A) × ℕ :=
    if hx : onChart x then data hx.choose.1 hx.choose.2
    else (some (isolated hx).choose, M)
  have trace (e : E) (i : I) : global (chart e i) = data e i := by
    have hx : onChart (chart e i) := ⟨(e, i), rfl⟩
    simp only [global, dite_eq_left hx]
    exact agree hx.choose_spec
  have outside {x : Vertex P} (hx : ¬ onChart x) :
      ∃ v : Vertex A, x = retainedVertex (m + 1) v ∧ global x = (some v, M) := by
    exact ⟨(isolated hx).choose, (isolated hx).choose_spec, by simp only [global, dite_eq_right hx]⟩
  refine ⟨fun x => (global x).1, fun x => (global x).2,
    fun e i => congrArg Prod.fst (trace e i), fun e i => congrArg Prod.snd (trace e i),
    ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro s hs
    rcases hcover s hs with ⟨v, hv⟩ | ⟨e, t, ht, honto⟩
    · refine ⟨(global (retainedVertex (m + 1) v)).1, fun x hx => Or.inr ?_⟩
      rw [hv, Finset.mem_singleton] at hx
      rw [show x = retainedVertex (m + 1) v from Subtype.ext hx]
    · by_cases hl : ∃ j ∈ t, j < M
      · obtain ⟨j, hj, hjM⟩ := hl
        refine ⟨some (left e), fun x hx => ?_⟩
        obtain ⟨i, hi, rfl⟩ := honto x hx
        have hnear := ht.2.2 _ hi _ hj
        have hn : ¬ M < i.val := by omega
        dsimp only
        rw [trace]
        by_cases hiM : i.val < M <;> simp [data, hiM, hn]
      · refine ⟨some (right e), fun x hx => ?_⟩
        obtain ⟨i, hi, rfl⟩ := honto x hx
        have hn : ¬ i.val < M := fun h => hl ⟨i.val, hi, h⟩
        dsimp only
        rw [trace]
        by_cases hiM : M < i.val <;> simp [data, hiM, hn]
  · intro x
    by_cases hx : onChart x
    · obtain ⟨⟨e, i⟩, rfl⟩ := hx
      have hi := i.property.2.1 _ (Finset.mem_singleton_self i.val)
      change (global (chart e i)).2 ≤ M
      rw [trace]
      change max (M - i.val) (i.val - M) ≤ M
      omega
    · obtain ⟨v, _, hv⟩ := outside hx
      change (global x).2 ≤ M
      rw [hv]
  · intro x y hxy
    rcases hcover {x.val, y.val} hxy.2 with ⟨v, hv⟩ | ⟨e, t, ht, honto⟩
    · have hx : x.val = (retainedVertex (m + 1) v).val :=
        Finset.mem_singleton.mp (hv ▸ Finset.mem_insert_self _ _)
      have hy : y.val = (retainedVertex (m + 1) v).val :=
        Finset.mem_singleton.mp (hv ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      exact (hxy.1 (Subtype.ext (hx.trans hy.symm))).elim
    · obtain ⟨i, hi, rfl⟩ := honto x (Finset.mem_insert_self _ _)
      obtain ⟨j, hj, rfl⟩ := honto y (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have h₁ := ht.2.2 _ hi _ hj
      have h₂ := ht.2.2 _ hj _ hi
      simp only [trace, data]
      omega
  · intro x hx
    by_cases he : onChart x
    · obtain ⟨⟨e, i⟩, rfl⟩ := he
      change (global (chart e i)).1 = none at hx
      change (global (chart e i)).2 = 0
      rw [trace] at hx ⊢
      change (if i.val < M then some (left e) else if M < i.val then some (right e) else none) =
        none at hx
      have hi : i.val = M := by
        split at hx
        · contradiction
        · split at hx
          · contradiction
          · omega
      simp [data, hi]
    · obtain ⟨v, _, hv⟩ := outside he
      change (global x).1 = none at hx
      rw [hv] at hx
      contradiction
  · intro x hx
    obtain ⟨v, hv, hdata⟩ := outside (fun ⟨⟨e, i⟩, hi⟩ => hx ⟨e, i, hi⟩)
    exact ⟨v, hv, congrArg Prod.fst hdata, congrArg Prod.snd hdata⟩

end
end D5.S3.Topology.GraphSubdivisionHalves
