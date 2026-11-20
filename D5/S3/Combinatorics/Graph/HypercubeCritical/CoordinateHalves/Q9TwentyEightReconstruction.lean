import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixReconstruction

/-! Each of the proposed 28-point half models forces a 20-point cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyEightReconstruction

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open private reconstructedSupport mem_reconstructedSupport from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixReconstruction

private def listedHalves : List (List (BitVec 9)) :=
  ([[0, 1, 3, 5, 8, 11, 13, 16, 19, 21, 40, 41, 43, 45, 48, 49, 51, 53, 96, 97, 99, 101, 104,
      107, 109, 112, 115, 117],
    [0, 1, 3, 5, 8, 11, 13, 16, 19, 21, 40, 41, 43, 45, 56, 59, 61, 80, 81, 83, 85, 88, 91,
      93, 120, 121, 123, 125],
    [0, 1, 3, 5, 8, 11, 13, 16, 19, 21, 40, 41, 43, 45, 80, 81, 83, 85, 104, 107, 109, 112,
      115, 117, 120, 121, 123, 125]] : List (List Nat)).map (List.map fun x => BitVec.ofNat 9 (2 * x))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem listedCuts : listedHalves.all (fun half =>
    decide half.Nodup &&
      ((reconstructedSupport half).filter fun x => x.getLsbD 2 = true).card == 20) = true := by
  decide +kernel

open Classical in
private theorem twenty_cut_of_listed_half {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {half : List (BitVec 9)} (hlisted : half ∈ listedHalves)
    (hm : ∀ x : BitVec 9, x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice C false) :
    (C.filter fun x => x 2 = true).card = 20 := by
  classical
  obtain ⟨hn, hsize⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp listedCuts half hlisted)
  let S := reconstructedSupport half
  let f := cubeBitVec 9
  have hS : S.image f = C := by
    ext x
    obtain ⟨b, rfl⟩ := f.surjective x
    have hm' := mem_reconstructedSupport hr hb half (of_decide_eq_true hn) hm b
    constructor
    · intro hx
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hx
      exact hm'.mp (f.injective he ▸ ha)
    · intro hx
      exact Finset.mem_image_of_mem f (hm'.mpr hx)
  rw [← hS, Finset.filter_image, Finset.card_image_of_injective _ f.injective]
  exact beq_iff_eq.mp hsize

#print axioms twenty_cut_of_listed_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyEightReconstruction
