/- GID: D5/S3/FiniteGroups/NikolovSegal/BoundedTupleLift
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/BoundedTupleLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lemma 2 lifts a fixed quotient tuple inside the bounded-section class. -/

import D5.S3.FiniteGroups.NikolovSegal.SectionClosure
import D5.S3.FiniteGroups.GaschutzFixed

set_option autoImplicit false

namespace NikolovSegal

universe u v
variable {G : Type u} {Q : Type v} [Group G] [Group Q] [Finite G] [Finite Q]

/-- Lemma 2 replaces a quotient tuple by lifts whose generated subgroup stays
in the bounded-section class. No rank bound on the full preimage is needed. -/
theorem exists_bounded_tuple_lift (q : G →* Q) (hq : Function.Surjective q)
    {d k : ℕ} (hk : 4 ≤ k) (y : Fin d → Q)
    (hy : alpha (Subgroup.closure (Set.range y)) ≤ k) :
    ∃ z : Fin d → G, (∀ i, q (z i) = y i) ∧
      alpha (Subgroup.closure (Set.range z)) ≤ k := by
  classical
  let H := Subgroup.closure (Set.range y)
  let T := H.comap q
  let r : T →* H := (q.comp T.subtype).codRestrict H (fun x => x.property)
  choose s hs using fun i => hq (y i)
  let t : Fin d → T := fun i => ⟨s i, by
    change q (s i) ∈ H
    rw [hs i]
    exact Subgroup.subset_closure ⟨i, rfl⟩⟩
  obtain ⟨L, hL, hαL⟩ := exists_supplement_alpha_le r.ker
  have hLbound : alpha L ≤ k :=
    hαL.trans (max_le ((alpha_quotient_kernel_le r).trans hy) hk)
  choose a ha using fun i => D5.S3.FiniteGroups.GaschutzFixed.correction_exists r.ker L hL (t i)
  let z : Fin d → G := fun i => ((a i : T) * t i : T)
  let M := L.map T.subtype
  have hzM : ∀ i, z i ∈ M := fun i => Subgroup.mem_map.mpr ⟨_, ha i, rfl⟩
  have hMbound : alpha M ≤ k := by
    let e := L.equivMapOfInjective T.subtype T.subtype_injective
    exact (alpha_le_of_injective e.symm.toMonoidHom e.symm.injective).trans hLbound
  refine ⟨z, ?_, (alpha_le_of_subgroup_le ?_).trans hMbound⟩
  · intro i
    have ha₁ : q ((a i : T) : G) = 1 :=
      congrArg (fun x : H => (x : Q)) (MonoidHom.mem_ker.mp (a i).property)
    change q (((a i : T) : G) * (s i)) = y i
    rw [map_mul, ha₁, one_mul, hs i]
  · apply (Subgroup.closure_le M).2
    rintro _ ⟨i, rfl⟩
    exact hzM i

end NikolovSegal
