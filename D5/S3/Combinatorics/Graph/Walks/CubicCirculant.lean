/- GID: D5/S3/Combinatorics/Graph/Walks/CubicCirculant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CubicCirculant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Circulant, mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic]
   utility: none
   digest: Native cubic circulants, their component coordinates and all positive well-covered powers. -/
import D5.S3.Combinatorics.Graph.Walks.BinaryRungSpectrum
import D5.S3.Combinatorics.Graph.Walks.FiniteDistancePower
import D5.S3.Combinatorics.Graph.Walks.CirculantComponents
import D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CubicCirculant

open SimpleGraph Finset
open WellCoveredPowerCliqueProduct (IsMaximalIndep WellCovered power WCP)
open MatchingCliqueCycle (spectrum)
open BinaryRungSpectrum (Vertex graph closing forward)

noncomputable section

/-- The native cubic circulant, using exactly the two published cyclic jumps. -/
abbrev cubic (n a : ℕ) : SimpleGraph (ZMod n) :=
  circulantGraph ({(a : ZMod n),((n/2 : ℕ) : ZMod n)} : Set (ZMod n))

/-- Every component in the entire cubic range has explicit native ladder coordinates.
The component count is `gcd(a,n/2)`, including all disconnected parameters. -/
theorem component_decomposition (n a : ℕ) (hn : 4 ≤ n) (hnEven : Even n)
    (ha : 1 ≤ a) (haHalf : a < n/2) :
    let h := Nat.gcd n a
    let ell := n/h
    let g := Nat.gcd a (n/2)
    Nat.card (cubic n a).ConnectedComponent = g ∧
      (Even ell → h=g ∧ ∃ m : ℕ, ell=2*(m+2) ∧
        ∀ C : (cubic n a).ConnectedComponent, Nonempty (mobius m ≃g C.toSimpleGraph)) ∧
      (Odd ell → Even h ∧ g=h/2 ∧ ∃ r : ℕ, ell=r+3 ∧
        ∀ C : (cubic n a).ConnectedComponent,
          Nonempty (((cycleGraph (r+3)) □ (⊤ : SimpleGraph (ZMod 2))) ≃g C.toSimpleGraph)) := by
  obtain ⟨k,hk⟩ := hnEven
  have hk2 : 2 ≤ k := by omega
  let p := k-2
  have hnrep : n=2*(p+2) := by dsimp [p]; omega
  rw [hnrep] at haHalf ⊢
  have hhalf : 2*(p+2)/2=p+2 := by omega
  dsimp only
  have hG : cubic (2*(p+2)) a =
      circulantGraph ({(a : ZMod (2*(p+2))),((p+2 : ℕ) : ZMod (2*(p+2)))} : Set _) := by
    simp only [cubic,hhalf]
  generalize hX : cubic (2*(p+2)) a = G at ⊢
  have hGX : G = circulantGraph
      ({(a : ZMod (2*(p+2))),((p+2 : ℕ) : ZMod (2*(p+2)))} : Set _) := hX.symm.trans hG
  clear hX hG
  subst G
  simp only [hhalf]
  have hord : addOrderOf (a : ZMod (2*(p+2))) = 2*(p+2)/Nat.gcd (2*(p+2)) a :=
    ZMod.addOrderOf_coe a (by omega)
  have hlt : a < p+2 := by rwa [hhalf] at haHalf
  have hlo := step_order_lower_bound p a ha hlt
  refine ⟨?_,?_,?_⟩
  · simpa only [cubic,hhalf] using
      component_count (n := 2*(p+2)) a (p+2) (show p+2 ∣ 2*(p+2) from ⟨2,by omega⟩)
  · intro heven
    have heven' : Even (addOrderOf (a : ZMod (2*(p+2)))) := hord.symm ▸ heven
    refine ⟨?_,?_⟩
    · simpa only [hhalf] using (even_component_number p a heven').symm
    obtain ⟨j,hj⟩ := heven'
    let m := j-2
    have heq : addOrderOf (a : ZMod (2*(p+2))) = 2*(m+2) := by dsimp [m]; omega
    refine ⟨m,hord.symm.trans heq,?_⟩
    intro C
    have e := evenComponentIso p (a : ZMod (2*(p+2)))
      (show Even (addOrderOf (a : ZMod (2*(p+2)))) from ⟨j,hj⟩) C
    rw [heq] at e
    have hmh : 2*(m+2)/2=m+2 := by omega
    exact ⟨by simpa only [mobius,hmh] using e⟩
  · intro hodd
    have hodd' : Odd (addOrderOf (a : ZMod (2*(p+2)))) := hord.symm ▸ hodd
    have hc := odd_component_number p a hodd'
    refine ⟨⟨Nat.gcd a (p+2),by omega⟩,?_,?_⟩
    · omega
    let r := addOrderOf (a : ZMod (2*(p+2)))-3
    have heq : addOrderOf (a : ZMod (2*(p+2)))=r+3 := by dsimp [r]; omega
    refine ⟨r,hord.symm.trans heq,?_⟩
    intro C
    exact ⟨oddComponentIso p r (a : ZMod (2*(p+2))) heq (heq ▸ hodd') C⟩


end
end CubicCirculant
