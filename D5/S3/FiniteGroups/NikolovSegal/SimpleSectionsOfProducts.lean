/- GID: D5/S3/FiniteGroups/NikolovSegal/SimpleSectionsOfProducts
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/SimpleSectionsOfProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A simple section of a finite product occurs in one factor. -/

import D5.S3.FiniteGroups.NikolovSegal.Sections
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
namespace NikolovSegal
universe u v w
variable {A : Type w} [Group A] [IsSimpleGroup A]

/-- A simple section of a finite direct product occurs in an individual factor.
The section subgroup is arbitrary; it need not itself be a product subgroup. -/
theorem simple_involves_pi_factor (ι : Type u) [Finite ι]
    (H : ι → Type v) [∀ i, Group (H i)] (h : Involves A (∀ i, H i)) :
    ∃ i, Involves A (H i) := by
  let P : Type u → Prop := fun I =>
    ∀ (K : I → Type v) [∀ i, Group (K i)],
      Involves A (∀ i, K i) → ∃ i, Involves A (K i)
  have hp : P ι := by
    apply Finite.induction_empty_option (P := P) _ _ _ ι
    · intro I J e ih K _ hh
      let q : (∀ j, K j) →* (∀ i, K (e i)) :=
        { toFun := fun t i => t (e i), map_one' := rfl, map_mul' := fun _ _ => rfl }
      have hq : Function.Injective q := by
        intro x y hxy
        funext j
        obtain ⟨i, rfl⟩ := e.surjective j
        exact congrFun hxy i
      obtain ⟨i, hi⟩ := ih (fun i => K (e i)) (involves_of_injective q hq hh)
      exact ⟨e i, hi⟩
    · intro K _ hh
      obtain ⟨L, f, hf⟩ := hh
      have ht : Subsingleton A := by
        constructor
        intro a b
        obtain ⟨x, rfl⟩ := hf a
        obtain ⟨y, rfl⟩ := hf b
        exact congrArg f (Subsingleton.elim x y)
      exact False.elim (not_subsingleton A ht)
    · intro I _ ih K _ hh
      let q : (∀ j, K j) →* (∀ i : I, K (some i)) :=
        { toFun := fun t i => t (some i), map_one' := rfl, map_mul' := fun _ _ => rfl }
      rcases simple_involves_map_or_kernel q hh with hq | hk
      · obtain ⟨i, hi⟩ := ih (fun i => K (some i)) hq
        exact ⟨some i, hi⟩
      · let j : q.ker →* K none :=
          (Pi.evalMonoidHom K none).comp q.ker.subtype
        have hj : Function.Injective j := by
          intro x y hxy
          apply Subtype.ext
          funext t
          cases t with
          | none => exact hxy
          | some i =>
            have hx := congrFun (MonoidHom.mem_ker.mp x.property) i
            have hy := congrFun (MonoidHom.mem_ker.mp y.property) i
            exact hx.trans hy.symm
        exact ⟨none, involves_of_injective j hj hk⟩
  exact hp H h

end NikolovSegal
