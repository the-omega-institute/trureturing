/- GID: D5/S3/Combinatorics/Graph/Chordal/GainPotentialStability
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/GainPotentialStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle defects bound simultaneous chordal group gain potential errors. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import Mathlib.Topology.MetricSpace.IsometricSMul

/-! # Stability of group gain potentials

Simplicial elimination accumulates at most one triangle defect at each extension.
Both translations are isometries; no commutation of group elements is required.
-/

universe u v

namespace SimpleGraph

variable {V : Type u} {H : Type v} [Group H] [PseudoMetricSpace H]
  [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

/-- Reversal-compatible gains on a finite chordal graph with triangle defect at most
`ε` admit a simultaneous vertex potential with edge error at most `(|V| - 2) * ε`.
The subtraction is in the natural numbers. Nonedges and diagonal labels are unrestricted. -/
theorem IsChordal.exists_approximate_gain_potential [Finite V] {G : SimpleGraph V}
    (hG : G.IsChordal) (g : V → V → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, G.Adj i j → g j i = (g i j)⁻¹)
    (htri : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
      Dist.dist (g i j * g j k) (g i k) ≤ ε) :
    ∃ φ : V → H, ∀ i j, G.Adj i j →
      Dist.dist (g i j) ((φ i)⁻¹ * φ j) ≤ ((Nat.card V - 2 : ℕ) : ℝ) * ε := by
  classical
  let := Fintype.ofFinite V
  have construct : ∀ s : Finset V, ∃ φ : V → H,
      ∀ i ∈ s, ∀ j ∈ s, G.Adj i j →
        Dist.dist (g i j) ((φ i)⁻¹ * φ j) ≤ ((s.card - 2 : ℕ) : ℝ) * ε := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      have nonneg : 0 ≤ ((s.card - 2 : ℕ) : ℝ) * ε :=
        mul_nonneg (Nat.cast_nonneg _) hε
      by_cases hs : s.Nonempty
      · obtain ⟨a, ha⟩ := hs
        let : Nonempty (s : Set V) := ⟨⟨a, ha⟩⟩
        obtain ⟨z, hz⟩ := (hG.induce (s : Set V)).exists_isSimplicial
        let x : V := z
        have hx : x ∈ s := z.property
        have hcard : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
        have mono : (((s.erase x).card - 2 : ℕ) : ℝ) * ε ≤
            ((s.card - 2 : ℕ) : ℝ) * ε := by
          apply mul_le_mul_of_nonneg_right _ hε
          exact_mod_cast (show (s.erase x).card - 2 ≤ s.card - 2 by omega)
        obtain ⟨ψ, hψ⟩ := ih (s.erase x) (Finset.erase_ssubset hx)
        by_cases hn : ∃ w ∈ s.erase x, G.Adj x w
        · obtain ⟨w, hw, hxw⟩ := hn
          let φ : V → H := Function.update ψ x (ψ w * (g x w)⁻¹)
          have extend : ∀ j ∈ s.erase x, G.Adj x j →
              Dist.dist (g x j) ((φ x)⁻¹ * φ j) ≤ ((s.card - 2 : ℕ) : ℝ) * ε := by
            intro j hj hxj
            have hjx : j ≠ x := (Finset.mem_erase.mp hj).1
            have hwx : w ≠ x := (Finset.mem_erase.mp hw).1
            by_cases hjw : j = w
            · subst j
              simpa [φ, hwx, mul_assoc] using nonneg
            · have hw' : (⟨w, (Finset.mem_erase.mp hw).2⟩ : (s : Set V)) ∈
                  (G.induce (s : Set V)).neighborSet z := hxw
              have hj' : (⟨j, (Finset.mem_erase.mp hj).2⟩ : (s : Set V)) ∈
                  (G.induce (s : Set V)).neighborSet z := hxj
              have hwj : G.Adj w j := hz hw' hj' (by
                intro heq
                exact hjw (congrArg Subtype.val heq).symm)
              have htwo : 2 ≤ (s.erase x).card := by
                exact Finset.one_lt_card.mpr ⟨w, hw, j, hj, Ne.symm hjw⟩
              have hsum : (1 : ℝ) + (((s.erase x).card - 2 : ℕ) : ℝ) =
                  ((s.card - 2 : ℕ) : ℝ) := by
                exact_mod_cast (show 1 + ((s.erase x).card - 2) = s.card - 2 by omega)
              calc
                Dist.dist (g x j) ((φ x)⁻¹ * φ j) ≤
                    Dist.dist (g x j) (g x w * g w j) +
                      Dist.dist (g x w * g w j) ((φ x)⁻¹ * φ j) := _root_.dist_triangle _ _ _
                _ = Dist.dist (g x w * g w j) (g x j) +
                      Dist.dist (g w j) ((ψ w)⁻¹ * ψ j) := by
                    rw [_root_.dist_comm (g x j)]
                    simp [φ, hjx, mul_assoc, dist_mul_left]
                _ ≤ ε + (((s.erase x).card - 2 : ℕ) : ℝ) * ε :=
                    add_le_add (htri x w j hxw hwj hxj) (hψ w hw j hj hwj)
                _ = ((s.card - 2 : ℕ) : ℝ) * ε := by rw [← hsum]; ring
          refine ⟨φ, ?_⟩
          intro i hi j hj hij
          by_cases hix : i = x
          · subst i
            exact extend j (Finset.mem_erase.mpr ⟨hij.ne.symm, hj⟩) hij
          · by_cases hjx : j = x
            · subst j
              calc
                Dist.dist (g i x) ((φ i)⁻¹ * φ x) =
                    Dist.dist (g x i) ((φ x)⁻¹ * φ i) := by
                  rw [hrev x i hij.symm, ← dist_inv_inv (g x i) ((φ x)⁻¹ * φ i)]
                  simp
                _ ≤ _ := extend i (Finset.mem_erase.mpr ⟨hix, hi⟩) hij.symm
            · have hold := hψ i (Finset.mem_erase.mpr ⟨hix, hi⟩)
                  j (Finset.mem_erase.mpr ⟨hjx, hj⟩) hij
              simpa [φ, hix, hjx] using hold.trans mono
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
          exact (hψ i (Finset.mem_erase.mpr ⟨hix, hi⟩)
            j (Finset.mem_erase.mpr ⟨hjx, hj⟩) hij).trans mono
      · refine ⟨fun _ => 1, ?_⟩
        intro i hi
        exact (hs ⟨i, hi⟩).elim
  obtain ⟨φ, hφ⟩ := construct Finset.univ
  refine ⟨φ, ?_⟩
  intro i j hij
  simpa [Nat.card_eq_fintype_card] using
    hφ i (Finset.mem_univ i) j (Finset.mem_univ j) hij

end SimpleGraph
