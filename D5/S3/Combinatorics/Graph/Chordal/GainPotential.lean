/- GID: D5/S3/Combinatorics/Graph/Chordal/GainPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/GainPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle-compatible group gains on finite chordal graphs admit vertex potentials. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac

/-! # Potentials from triangle-compatible gains

An oriented edge carries an element of an arbitrary group. Reversing an edge inverts
its gain, and traversing two sides of a triangle agrees with its third side.
Simplicial elimination extends these local constraints to a vertex potential.
-/

universe u v

namespace SimpleGraph

variable {V : Type u} {H : Type v} [Group H]

/-- On a finite chordal graph, triangle-compatible group gains are differences of
vertex potentials. The group need not be commutative and the graph need not be connected.
Labels on the diagonal and on nonedges are unrestricted. -/
theorem IsChordal.exists_gain_potential [Finite V] {G : SimpleGraph V}
    (hG : G.IsChordal) (g : V → V → H)
    (hrev : ∀ i j, G.Adj i j → g j i = (g i j)⁻¹)
    (htri : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      g i j * g j k = g i k) :
    ∃ φ : V → H, ∀ i j, G.Adj i j → g i j = (φ i)⁻¹ * φ j := by
  classical
  let := Fintype.ofFinite V
  have construct : ∀ s : Finset V, ∃ φ : V → H,
      ∀ i ∈ s, ∀ j ∈ s, G.Adj i j → g i j = (φ i)⁻¹ * φ j := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨a, ha⟩ := hs
        let : Nonempty (s : Set V) := ⟨⟨a, ha⟩⟩
        obtain ⟨z, hz⟩ := (hG.induce (s : Set V)).exists_isSimplicial
        let x : V := z
        have hx : x ∈ s := z.property
        obtain ⟨ψ, hψ⟩ := ih (s.erase x) (Finset.erase_ssubset hx)
        by_cases hn : ∃ w ∈ s.erase x, G.Adj x w
        · obtain ⟨w, hw, hxw⟩ := hn
          let φ : V → H := Function.update ψ x (ψ w * (g x w)⁻¹)
          have extend : ∀ j ∈ s.erase x, G.Adj x j →
              g x j = (φ x)⁻¹ * φ j := by
            intro j hj hxj
            have hjx : j ≠ x := (Finset.mem_erase.mp hj).1
            have hwx : w ≠ x := (Finset.mem_erase.mp hw).1
            by_cases hjw : j = w
            · subst j
              simp [φ, hwx, mul_assoc]
            · have hw' : (⟨w, (Finset.mem_erase.mp hw).2⟩ : (s : Set V)) ∈
                  (G.induce (s : Set V)).neighborSet z := hxw
              have hj' : (⟨j, (Finset.mem_erase.mp hj).2⟩ : (s : Set V)) ∈
                  (G.induce (s : Set V)).neighborSet z := hxj
              have hwj : G.Adj w j := hz hw' hj' (by
                intro heq
                exact hjw (congrArg Subtype.val heq).symm)
              calc
                g x j = g x w * g w j := (htri x w j hxw hwj hxj).symm
                _ = g x w * ((ψ w)⁻¹ * ψ j) := by rw [hψ w hw j hj hwj]
                _ = (φ x)⁻¹ * φ j := by simp [φ, hjx, mul_assoc]
          refine ⟨φ, ?_⟩
          intro i hi j hj hij
          by_cases hix : i = x
          · subst i
            exact extend j (Finset.mem_erase.mpr ⟨hij.ne.symm, hj⟩) hij
          · by_cases hjx : j = x
            · subst j
              calc
                g i x = (g x i)⁻¹ := hrev x i hij.symm
                _ = ((φ x)⁻¹ * φ i)⁻¹ := by
                  rw [extend i (Finset.mem_erase.mpr ⟨hix, hi⟩) hij.symm]
                _ = (φ i)⁻¹ * φ x := by simp
            · simpa [φ, hix, hjx] using
                hψ i (Finset.mem_erase.mpr ⟨hix, hi⟩)
                  j (Finset.mem_erase.mpr ⟨hjx, hj⟩) hij
        · refine ⟨ψ, ?_⟩
          intro i hi j hj hij
          have hix : i ≠ x := by
            intro heq
            subst i
            exact hn ⟨j, Finset.mem_erase.mpr ⟨hij.ne.symm, hj⟩, hij⟩
          have hjx : j ≠ x := by
            intro heq
            subst j
            exact hn ⟨i, Finset.mem_erase.mpr ⟨hij.ne, hi⟩, hij.symm⟩
          exact hψ i (Finset.mem_erase.mpr ⟨hix, hi⟩)
            j (Finset.mem_erase.mpr ⟨hjx, hj⟩) hij
      · refine ⟨fun _ => 1, ?_⟩
        intro i hi
        exact (hs ⟨i, hi⟩).elim
  obtain ⟨φ, hφ⟩ := construct Finset.univ
  exact ⟨φ, fun i j hij => hφ i (Finset.mem_univ i) j (Finset.mem_univ j) hij⟩

end SimpleGraph
