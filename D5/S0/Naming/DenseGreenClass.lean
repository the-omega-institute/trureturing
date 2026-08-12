/- GID: D5/S0/Naming/DenseGreenClass
   generality: G
   mirror-B: D5/B/S0/Naming/DenseGreenClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every nonempty open set meets a dense set. -/

import Mathlib.Topology.Closure

namespace D5.S0.Naming.DenseGreenClass

/-- A nonempty open class meets every dense property. This is the direct set-theoretic
form of `Dense.inter_open_nonempty`. -/
theorem dense_inter_green_class_nonempty
    {X : Type*} [TopologicalSpace X] (P G : Set X)
    (hP : Dense P) (hG : IsOpen G) (hne : G.Nonempty) :
    (G ∩ P).Nonempty :=
  hP.inter_open_nonempty G hG hne

/-- The hypotheses are simultaneously realized by the universal subsets of any inhabited space. -/
example {X : Type*} [TopologicalSpace X] [Nonempty X] :
    ∃ (P G : Set X),
      Dense P ∧ IsOpen G ∧ G.Nonempty ∧ (G ∩ P).Nonempty := by
  refine ⟨Set.univ, Set.univ, dense_univ, isOpen_univ, ?_, ?_⟩
  · exact Set.univ_nonempty
  · exact dense_inter_green_class_nonempty Set.univ Set.univ dense_univ isOpen_univ
      Set.univ_nonempty

end D5.S0.Naming.DenseGreenClass
