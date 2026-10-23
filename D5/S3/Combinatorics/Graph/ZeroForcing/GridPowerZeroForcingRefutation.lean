/- GID: D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hasse, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.claim; result=D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.result; claim=D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.claim
   digest: The unrestricted grid-power zero-forcing conjecture fails on the three-by-two grid at power one. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation

open SimpleGraph
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree

/-- Distance power: distinct vertices are adjacent exactly when their base-graph distance is at
most `k`. Extended distance retains the unreachable-vertex convention without an extra hypothesis. -/
noncomputable def graphPower {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.edist u v ≤ (k : ℕ∞)
  symm.symm u v h := by
    exact ⟨h.1.symm, by simpa only [G.edist_comm] using h.2⟩
  loopless.irrefl u h := h.1 rfl

/-- Conjecture 12 of Abiad, Flagg, Ghasemi Nezhad and Zeijlemaker, literally over its printed domain. -/
def claim : Prop := ∀ b k ell : ℕ, 1 ≤ b → 1 ≤ k → k + 1 ≤ ell →
  zeroForcingNumber (graphPower (pathGraph b □ pathGraph ell) k) = b * k

/-- Two initial vertices force the three-by-two grid, contradicting the printed value three. -/
theorem result : ¬ claim := by
  intro h
  let G := pathGraph 3 □ pathGraph 2
  have hp : graphPower G 1 = G := by
    ext u v
    change (u ≠ v ∧ G.edist u v ≤ (1 : ℕ∞)) ↔ G.Adj u v
    rw [G.edist_le_one_iff_adj_or_eq]
    exact ⟨fun h => h.2.resolve_right h.1, fun h => ⟨h.ne, Or.inl h⟩⟩
  let A : Fin 3 × Fin 2 := (0, 0)
  let B : Fin 3 × Fin 2 := (0, 1)
  let C : Fin 3 × Fin 2 := (1, 0)
  let D : Fin 3 × Fin 2 := (1, 1)
  let E : Fin 3 × Fin 2 := (2, 0)
  let F : Fin 3 × Fin 2 := (2, 1)
  let S : Finset (Fin 3 × Fin 2) := {A, B}
  have hA : Black G (S : Set _) A := .init (by simp [S])
  have hB : Black G (S : Set _) B := .init (by simp [S])
  have hC : Black G (S : Set _) C := by
    apply Black.force hA (by simp only [G, boxProd_adj, pathGraph_adj]; decide)
    intro x hax hxC
    have hx : x = B := (by simp only [G, boxProd_adj, pathGraph_adj]; decide : ∀ x, G.Adj A x → x ≠ C → x = B) x hax hxC
    simpa only [hx] using hB
  have hD : Black G (S : Set _) D := by
    apply Black.force hB (by simp only [G, boxProd_adj, pathGraph_adj]; decide)
    intro x hbx hxD
    have hx : x = A := (by simp only [G, boxProd_adj, pathGraph_adj]; decide : ∀ x, G.Adj B x → x ≠ D → x = A) x hbx hxD
    simpa only [hx] using hA
  have hE : Black G (S : Set _) E := by
    apply Black.force hC (by simp only [G, boxProd_adj, pathGraph_adj]; decide)
    intro x hcx hxE
    have hx : x = A ∨ x = D :=
      (by simp only [G, boxProd_adj, pathGraph_adj]; decide : ∀ x, G.Adj C x → x ≠ E → x = A ∨ x = D) x hcx hxE
    rcases hx with rfl | rfl
    · exact hA
    · exact hD
  have hF : Black G (S : Set _) F := by
    apply Black.force hD (by simp only [G, boxProd_adj, pathGraph_adj]; decide)
    intro x hdx hxF
    have hx : x = B ∨ x = C :=
      (by simp only [G, boxProd_adj, pathGraph_adj]; decide : ∀ x, G.Adj D x → x ≠ F → x = B ∨ x = C) x hdx hxF
    rcases hx with rfl | rfl
    · exact hB
    · exact hC
  have hz : IsZeroForcing G (S : Set _) := by
    intro v
    have hv : v = A ∨ v = B ∨ v = C ∨ v = D ∨ v = E ∨ v = F :=
      (by decide : ∀ v, v = A ∨ v = B ∨ v = C ∨ v = D ∨ v = E ∨ v = F) v
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hle : zeroForcingNumber G ≤ 2 :=
    Nat.sInf_le ⟨S, by decide, hz⟩
  have heq := h 3 1 2 (by decide) (by decide) (by decide)
  change zeroForcingNumber (graphPower G 1) = 3 * 1 at heq
  rw [hp] at heq
  change zeroForcingNumber G = 3 at heq
  omega

#print axioms result

end D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation
