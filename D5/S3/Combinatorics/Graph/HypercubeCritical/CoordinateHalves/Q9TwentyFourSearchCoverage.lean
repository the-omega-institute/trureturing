import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCubeMetric
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelDistances

/-! Follow the verified embedding search along a given ordered placement. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourSearchCoverage

open private Model hamming respectsDistances Admissible embeddings mem_embeddings from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck
open private distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelDistances

private theorem respects_prefix (model : Model) (position : List Nat)
    (k : Nat) (hk : k < model.length) (hpos : k + 1 < position.length)
    (hdist : ∀ j (hj : j < k + 1),
      let d := distance model (k + 1) j
      let h := hamming position[k+1] (position[j]'(by omega))
      0 < h ∧ h ≤ d ∧ (h = 1 ↔ d = 1) ∧ h % 2 = d % 2) :
    respectsDistances model[k].2 position[k+1] (position.take (k + 1)) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  let placed := position.take (k + 1)
  have hlen : placed.length = k + 1 := by
    simp [placed, Nat.min_eq_left (by omega : k + 1 ≤ position.length)]
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
  have hj' : j < k + 1 := by
    change j < placed.zipIdx.length at hj
    simpa only [List.length_zipIdx, hlen] using hj
  have hzip : (position.take (k + 1)).zipIdx[j] = (position[j]'(by omega), j) := by
    rw [List.getElem_zipIdx, Nat.zero_add, List.getElem_take]
  rw [hzip]
  have hrow : distance model (k + 1) j = (model[k].2 >>> (4 * j)) &&& 15 := by
    have hn : k + 1 ≠ j := by omega
    have hlt : ¬k + 1 < j := by omega
    simp only [distance, hn, hlt, ite_false, Nat.add_sub_cancel, getElem!_pos model k hk]
  obtain ⟨hp, hle, hone, hpar⟩ := hdist j hj'
  rw [hrow] at hle hone hpar
  have heq : (hamming position[k+1] (position[j]'(by omega)) == 1) ==
      (((model[k].2 >>> (4 * j)) &&& 15) == 1) := by
    apply beq_iff_eq.mpr
    exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using hone)
  simp only [decide_eq_true hp, decide_eq_true hle, Bool.true_and, heq,
    beq_iff_eq.mpr hpar]

private theorem embedding_of_order (model : Model) (position : List Nat) (axes used : Nat → Nat)
    (hsize : position.length = model.length + 1) (hz : position[0]! = 0) (hu0 : used 0 = 0)
    (hstep : ∀ k (hk : k < model.length),
      model[k].1 < k + 1 ∧ axes k < min (used k + 1) 8 ∧
        used (k + 1) = max (used k) (axes k + 1) ∧
        position[k+1]'(by omega) = (position[model[k].1]! ^^^ (1 <<< axes k)) ∧
        respectsDistances model[k].2 (position[k+1]'(by omega))
          (position.take (k + 1)) = true) :
    position ∈ embeddings model [0] 0 := by
  have follow (fuel k : Nat) (hk : fuel + k = model.length) :
      Admissible (model.drop k) (position.take (k + 1)) (used k) position := by
    induction fuel generalizing k with
    | zero =>
      have he : k = model.length := by omega
      subst k
      rw [List.drop_length, ← hsize, List.take_length]
      rfl
    | succ fuel ih =>
      have hlt : k < model.length := by omega
      have hk' : k + 1 < position.length := by omega
      obtain ⟨hparent, haxis, hused, hp, hd⟩ := hstep k hlt
      have hnext := ih (k + 1) (by omega)
      have hparent' : model[k].1 < (position.take (k + 1)).length := by
        rw [List.length_take, Nat.min_eq_left (by omega : k + 1 ≤ position.length)]
        exact hparent
      have hpoint : (position.take (k + 1))[model[k].1]! = position[model[k].1]! := by
        rw [getElem!_pos (position.take (k + 1)) model[k].1 hparent',
          getElem!_pos position model[k].1 (by omega)]
        exact List.getElem_take
      rw [List.drop_eq_getElem_cons hlt]
      refine ⟨axes k, haxis, ?_⟩
      change respectsDistances model[k].2
          ((position.take (k + 1))[model[k].1]! ^^^ (1 <<< axes k))
          (position.take (k + 1)) = true ∧
        Admissible (model.drop (k + 1))
          (position.take (k + 1) ++ [(position.take (k + 1))[model[k].1]! ^^^ (1 <<< axes k)])
          (max (used k) (axes k + 1)) position
      rw [hpoint, ← hp]
      exact ⟨hd, by rwa [← hused, ← List.take_succ_eq_append_getElem hk']⟩
  have hfirst : position.take 1 = [0] := by
    cases position with
    | nil => simp at hsize
    | cons a rest => simpa using hz
  have hm := follow model.length 0 (by omega)
  rw [List.drop_zero, hfirst, hu0] at hm
  exact (mem_embeddings model [0] 0 position).mpr hm

#print axioms respects_prefix
#print axioms embedding_of_order

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourSearchCoverage
