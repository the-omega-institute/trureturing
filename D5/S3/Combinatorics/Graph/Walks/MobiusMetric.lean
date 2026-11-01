/- GID: D5/S3/Combinatorics/Graph/Walks/MobiusMetric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/MobiusMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Circulant, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Diam]
   utility: none
   digest: Antipodal finite-walk reduction gives the exact diameter of every native Mobius ladder. -/
import D5.S3.Combinatorics.Graph.Walks.CirculantComponents
import D5.S3.Combinatorics.Graph.Walks.MobiusLadderSpectrum
import D5.S3.Combinatorics.Graph.Walks.InvolutiveMatchingDistance
import D5.S3.Combinatorics.Graph.Walks.PowerSpectrumStructure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CubicCirculant
open SimpleGraph
open WellCoveredPowerCliqueProduct (cycleMetric)
noncomputable section

/-- Unit-jump cyclic coordinates preserve the native cycle adjacency. -/
def cycleZModIso (m : ℕ) :
    cycleGraph (2*(m+2)) ≃g circulantGraph ({1} : Set (ZMod (2*(m+2)))) where
  toEquiv := (ZMod.finEquiv (2*(m+2))).toEquiv
  map_rel_iff' := by
    intro u v
    let f := ZMod.finEquiv (2*(m+2))
    have hc : cycleGraph (2*(m+2)) =
        circulantGraph ({1} : Set (Fin (2*(m+2)))) := by
      have H : ∀ n : ℕ, [NeZero n] → cycleGraph n =
          circulantGraph ({1} : Set (Fin n)) := by
        intro n hn
        cases n with
        | zero => exact False.elim (hn.out rfl)
        | succ n => exact cycleGraph_eq_circulantGraph n
      exact H _
    rw [hc]
    change (circulantGraph ({1} : Set (ZMod (2*(m+2))))).Adj (f u) (f v) ↔ _
    simp only [circulantGraph_adj,Set.mem_singleton_iff]
    have hd (u v : Fin (2*(m+2))) : f u-f v=1 ↔ u-v=1 := by
      rw [← map_sub,← map_one f]
      exact f.injective.eq_iff
    simp only [f.injective.eq_iff]
    rw [hd,hd]

private theorem cycleZMod_distance (m : ℕ) (u v : ZMod (2*(m+2))) :
    (circulantGraph ({1} : Set (ZMod (2*(m+2))))).dist u v =
      min (Nat.dist u.val v.val) (2*(m+2)-Nat.dist u.val v.val) := by
  have he := FiniteDistancePower.dist_iso (cycleZModIso m)
    ((cycleZModIso m).symm u) ((cycleZModIso m).symm v)
  simp only [RelIso.apply_symm_apply] at he
  rw [he]
  have hc : ∀ i j : Fin (2*(m+2)), (cycleGraph (2*(m+2))).dist i j = cycleMetric (2*(m+2)) i j := by
    have H : ∀ n : ℕ, 3 ≤ n → ∀ i j : Fin n,
        (cycleGraph n).dist i j = cycleMetric n i j := by
      intro n hn
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
      have hnk : n=k+3 := by omega
      clear hk hn
      subst n
      exact MatchingCliqueCycle.cycle_distance k
    exact H _ (by omega)
  rw [hc]
  rfl

/-- The added antipodal matching is exactly the existing native two-jump circulant. -/
theorem mobius_extension (m : ℕ) :
    InvolutiveMatchingDistance.extension
      (translateIso ({1} : Set (ZMod (2*(m+2)))) ((m+2 : ℕ) : ZMod (2*(m+2)))) = mobius m := by
  ext u v
  change ((u≠v ∧ (u-v=1 ∨ v-u=1)) ∨
      (u≠v ∧ (u+((m+2 : ℕ) : ZMod (2*(m+2)))=v ∨
        v+((m+2 : ℕ) : ZMod (2*(m+2)))=u))) ↔ _
  simp only [mobius,circulantGraph_adj,Set.mem_insert_iff,Set.mem_singleton_iff,
    sub_eq_iff_eq_add']
  tauto

/-- The distance depends on the actual cyclic difference and at most one antipodal step. -/
theorem mobius_distance (m : ℕ) (u v : ZMod (2*(m+2))) :
    (mobius m).dist u v =
      min (min (v-u).val (2*(m+2)-(v-u).val))
        (1+min (Nat.dist (m+2) (v-u).val) (2*(m+2)-Nat.dist (m+2) (v-u).val)) := by
  let B := circulantGraph ({1} : Set (ZMod (2*(m+2))))
  let e := translateIso ({1} : Set (ZMod (2*(m+2)))) ((m+2 : ℕ) : ZMod (2*(m+2)))
  have hc : B.Connected := (cycleZModIso m).connected_iff.mp connected_cycleGraph_add_one
  have he (x : ZMod (2*(m+2))) : e (e x)=x := by
    change (x+((m+2 : ℕ) : ZMod (2*(m+2))))+((m+2 : ℕ) : ZMod (2*(m+2)))=x
    rw [add_assoc,antipode_add,add_zero]
  have hd := InvolutiveMatchingDistance.distance hc e he 0 (v-u)
  rw [mobius_extension] at hd
  have ht := FiniteDistancePower.dist_iso
    (translateIso ({(1 : ZMod (2*(m+2))),((m+2 : ℕ) : ZMod (2*(m+2)))} : Set _) (-u)) u v
  have ht' : (mobius m).dist u v = (mobius m).dist 0 (v-u) := by
    change (mobius m).dist (u+ -u) (v+ -u) = (mobius m).dist u v at ht
    simpa only [add_neg_cancel,← sub_eq_add_neg] using ht.symm
  have he0 : e 0 = ((m+2 : ℕ) : ZMod (2*(m+2))) := by
    change 0+((m+2 : ℕ) : ZMod (2*(m+2))) = _
    exact zero_add _
  rw [ht',hd,he0]
  change min (B.dist 0 (v-u)) (1+B.dist ((m+2 : ℕ) : ZMod (2*(m+2))) (v-u)) = _
  rw [cycleZMod_distance,cycleZMod_distance]
  rw [ZMod.val_zero,ZMod.val_natCast_of_lt (by omega)]
  simp only [Nat.dist_zero_left]

/-- Every native Möbius ladder is connected, witnessed by its spanning unit-jump cycle. -/
theorem mobius_connected (m : ℕ) : (mobius m).Connected := by
  have hc0 : (circulantGraph ({1} : Set (ZMod (2*(m+2))))).Connected :=
    (cycleZModIso m).connected_iff.mp connected_cycleGraph_add_one
  have hle : circulantGraph ({1} : Set (ZMod (2*(m+2)))) ≤ mobius m := by
    intro u v huv
    rcases huv with ⟨hne,huv⟩
    refine ⟨hne,?_⟩
    rcases huv with h | h
    · exact Or.inl (by simp_all)
    · exact Or.inr (by simp_all)
  exact hc0.mono hle

/-- Exact native diameters hold at every size, including the four-vertex boundary. -/
theorem mobius_diameter (m : ℕ) : (mobius m).diam = (m+3)/2 := by
  have hc := mobius_connected m
  have hf := connected_iff_ediam_ne_top.mp hc
  apply le_antisymm
  · obtain ⟨u,v,huv⟩ := (mobius m).exists_dist_eq_diam
    rw [← huv,mobius_distance]
    have hz := ZMod.val_lt (v-u)
    simp only [Nat.dist]
    omega
  · let z : ZMod (2*(m+2)) := ((m+3)/2 : ℕ)
    have hz : z.val=(m+3)/2 := ZMod.val_natCast_of_lt (by omega)
    have hb := (mobius m).dist_le_diam hf (u := 0) (v := z)
    rw [mobius_distance,sub_zero,hz] at hb
    simp only [Nat.dist] at hb
    omega

end
end CubicCirculant
