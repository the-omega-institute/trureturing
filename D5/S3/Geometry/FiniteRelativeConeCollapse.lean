/- GID: D5/S3/Geometry/FiniteRelativeConeCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteRelativeConeCollapse
   mirror-E: none(waiver:finite-relative-cone-collapse)
   anchors: [mathlib/module/Mathlib.Order.Preorder.Finite, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: A finite labeled cone collapses onto any subcone containing its actual apex by relative elementary collapses. -/
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Card

/-!
A finite cone collapses onto a subcone with the same apex. At each step a
maximal apex-free face outside the subcone is paired with its cone face.
The retained complex is again a cone containing the entire subcone, and
its number of faces strictly decreases. All faces retain their original labels.
-/

noncomputable section

open Set Finset

namespace D5.S3.Geometry.FiniteRelativeConeCollapse

open FiniteElementaryCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cone collapses onto every subcone containing the same apex. -/
theorem exists_sequence {K L : PreAbstractSimplicialComplex V} {v : V}
    (hLK : L ≤ K) (hv : ({v} : Finset V) ∈ L)
    (hK : ∀ s ∈ K, insert v s ∈ K)
    (hL : ∀ s ∈ L, insert v s ∈ L) :
    Nonempty (FiniteRelativeSimplicialCollapse.Sequence K L) := by
  classical
  suffices h : ∀ n : ℕ, ∀ M : PreAbstractSimplicialComplex V,
      M.faces.ncard = n → L ≤ M →
      (∀ s ∈ M, insert v s ∈ M) →
      Nonempty (FiniteRelativeSimplicialCollapse.Sequence M L) from
    h _ K rfl hLK hK
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M hn hLM hM
    by_cases hML : M ≤ L
    · have he : M = L := le_antisymm hML hLM
      subst M
      exact ⟨.refl L⟩
    · have hex : ∃ s : Finset V, s ∈ M ∧ s ∉ L := by
        by_contra h
        apply hML
        intro s hs
        by_contra hsL
        exact h ⟨s, hs, hsL⟩
      obtain ⟨s, hsM, hsL⟩ := hex
      have hsne : s.Nonempty := (M.isRelLowerSet_faces hsM).1
      have hene : (s.erase v).Nonempty := by
        by_contra he
        apply hsL
        apply (L.isRelLowerSet_faces hv).2 ?_ hsne
        intro a ha
        have hav : a = v := by
          by_contra hav
          exact he ⟨a, Finset.mem_erase.mpr ⟨hav, ha⟩⟩
        exact Finset.mem_singleton.mpr hav
      have heM : s.erase v ∈ M :=
        (M.isRelLowerSet_faces hsM).2 (Finset.erase_subset _ _) hene
      have heL : s.erase v ∉ L := by
        intro he
        exact hsL ((L.isRelLowerSet_faces (hL _ he)).2
          (Finset.insert_erase_subset _ _) hsne)
      let A : Set (Finset V) := {t | t ∈ M ∧ v ∉ t}
      have heA : s.erase v ∈ A := ⟨heM, Finset.notMem_erase _ _⟩
      obtain ⟨p, hep, hpmax⟩ := (Set.toFinite A).exists_le_maximal heA
      have hpM : p ∈ M := hpmax.1.1
      have hvp : v ∉ p := hpmax.1.2
      have hpne : p.Nonempty := by
        obtain ⟨a, ha⟩ := hene
        exact ⟨a, hep ha⟩
      have hpL : p ∉ L := by
        intro hp
        exact heL ((L.isRelLowerSet_faces hp).2 hep hene)
      have hfree : ∀ t ∈ M, p ⊂ t → t = insert v p := by
        intro t ht hpt
        have hpt' : p ⊆ t := (Finset.ssubset_iff_subset_ne.mp hpt).1
        by_cases hvt : v ∈ t
        · have hpe : p ⊆ t.erase v :=
            Finset.subset_erase.mpr ⟨hpt', hvp⟩
          have htene : (t.erase v).Nonempty := by
            obtain ⟨a, ha⟩ := hpne
            exact ⟨a, hpe ha⟩
          have hteM : t.erase v ∈ M :=
            (M.isRelLowerSet_faces ht).2 (Finset.erase_subset _ _) htene
          have htep : t.erase v ⊆ p :=
            hpmax.2 ⟨hteM, Finset.notMem_erase _ _⟩ hpe
          have heq : t.erase v = p := Finset.Subset.antisymm htep hpe
          calc
            t = insert v (t.erase v) := (Finset.insert_erase hvt).symm
            _ = insert v p := congrArg (insert v) heq
        · have htp : t ⊆ p := hpmax.2 ⟨ht, hvt⟩ hpt'
          exact False.elim ((Finset.ssubset_iff_subset_ne.mp hpt).2
            (Finset.Subset.antisymm hpt' htp))
      let P : CollapsePair V :=
        { ambient := M
          lower := p
          apex := v
          lower_nonempty := hpne
          apex_notMem := hvp
          upper_mem := hM p hpM
          free := hfree }
      have hLP : L ≤ P.retained := by
        intro t ht
        change t ∈ M ∧ ¬ p ⊆ t
        refine ⟨hLM ht, ?_⟩
        intro hpt
        exact hpL ((L.isRelLowerSet_faces ht).2 hpt hpne)
      have hPcone : ∀ t ∈ P.retained, insert v t ∈ P.retained := by
        intro t ht
        change t ∈ M ∧ ¬ p ⊆ t at ht
        change insert v t ∈ M ∧ ¬ p ⊆ insert v t
        refine ⟨hM t ht.1, ?_⟩
        intro hpi
        apply ht.2
        intro a ha
        rcases Finset.mem_insert.mp (hpi ha) with hav | hat
        · exact False.elim (hvp (hav ▸ ha))
        · exact hat
      have hproper : P.retained.faces ⊂ M.faces := by
        refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro t ht
          exact ht.1
        · intro heq
          have hpRet : p ∈ P.retained.faces := heq.symm ▸ hpM
          exact hpRet.2 (Finset.Subset.refl p)
      have hcount : P.retained.faces.ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard hproper (Set.toFinite M.faces)
      obtain ⟨tail⟩ := ih P.retained.faces.ncard hcount P.retained rfl hLP hPcone
      exact ⟨FiniteRelativeSimplicialCollapse.Sequence.step P tail⟩

end D5.S3.Geometry.FiniteRelativeConeCollapse
