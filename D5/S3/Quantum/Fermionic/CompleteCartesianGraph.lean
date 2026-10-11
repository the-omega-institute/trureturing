/- GID: D5/S3/Quantum/Fermionic/CompleteCartesianGraph
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/CompleteCartesianGraph
   mirror-E: none(waiver:general-finite-product-graph)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: Changing one coordinate gives a regular Cartesian product of complete graphs. -/

/-
regular_and_edge_count:
  proof_shape: content
  escape_witness: regular_and_edge_count (form 2): the bijection between neighbours of x
    and a coordinate together with a replacement value different from x at that coordinate.
admission_basis: escape-witness
Same-delivery inlined content: local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  none; remaining prerequisites are pinned Mathlib declarations.
computational_content.kind: none; the theorem counts neighbours for arbitrary finite
  alphabets and unbounded numbers of coordinates, rather than enumerating a fixed instance.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15194.
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace D5.S3.Quantum.Fermionic.CompleteCartesianGraph

/-- Two tuples are adjacent exactly when they differ in one coordinate. -/
def coordinateGraph (q : ℕ) (α : Type*) : SimpleGraph (Fin q → α) where
  Adj x y := ∃ a, x a ≠ y a ∧ ∀ b, b ≠ a → x b = y b
  symm := ⟨fun _x _y ⟨a, ha, h⟩ => ⟨a, ha.symm, fun b hb => (h b hb).symm⟩⟩
  loopless := ⟨fun _x ⟨_a, ha, _⟩ => ha rfl⟩

open Classical in
/-- The degree is q times the alphabet size minus one, with the corresponding edge count. -/
theorem regular_and_edge_count (q : ℕ) (α : Type*) [Fintype α] :
    (coordinateGraph q α).IsRegularOfDegree (q * (Fintype.card α - 1)) ∧
    2 * (coordinateGraph q α).edgeFinset.card =
      (Fintype.card α) ^ q * (q * (Fintype.card α - 1)) := by
  classical
  have hregular : (coordinateGraph q α).IsRegularOfDegree (q * (Fintype.card α - 1)) := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    let Replacements := (a : Fin q) × {b : α // b ≠ x a}
    let f : Replacements → (coordinateGraph q α).neighborSet x := fun p =>
      ⟨Function.update x p.1 p.2.val, p.1, by simpa using p.2.property.symm,
        fun b hb => by rw [Function.update_of_ne hb]⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨a, k⟩ ⟨b, l⟩ h
        have hab : a = b := by
          by_contra hab
          have he := congrArg (fun y : (coordinateGraph q α).neighborSet x => y.val a) h
          change Function.update x a k.val a = Function.update x b l.val a at he
          rw [Function.update_self, Function.update_of_ne hab] at he
          exact k.property he
        subst b
        have hkl : k = l := by
          apply Subtype.ext
          have he := congrArg (fun y : (coordinateGraph q α).neighborSet x => y.val a) h
          simpa [f] using he
        subst l
        rfl
      · intro y
        obtain ⟨a, ha, hrest⟩ := y.property
        refine ⟨⟨a, ⟨y.val a, ha.symm⟩⟩, Subtype.ext ?_⟩
        change Function.update x a (y.val a) = y.val
        funext b
        by_cases hba : b = a
        · subst b
          exact Function.update_self a (y.val a) x
        · rw [Function.update_of_ne hba]
          exact hrest b hba
    have hcard (a : Fin q) : Fintype.card {b : α // b ≠ x a} = Fintype.card α - 1 := by
      have h := Fintype.card_compl_set ({x a} : Set α)
      simp at h ⊢
    calc
      Fintype.card ((coordinateGraph q α).neighborSet x) = Fintype.card Replacements :=
        (Fintype.card_congr (Equiv.ofBijective f hf)).symm
      _ = q * (Fintype.card α - 1) := by
        simp [Replacements, Fintype.card_sigma, hcard]
  refine ⟨hregular, ?_⟩
  have hsum := (coordinateGraph q α).sum_degrees_eq_twice_card_edges
  simp only [hregular.degree_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum.symm

end D5.S3.Quantum.Fermionic.CompleteCartesianGraph
