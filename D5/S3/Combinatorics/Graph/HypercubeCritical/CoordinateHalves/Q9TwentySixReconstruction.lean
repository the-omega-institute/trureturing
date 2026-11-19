import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction

/-! Recover the full support from one half, including its other coordinate cuts. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixReconstruction

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9TwentyTwoReconstruction (bit_iff_opposite_mem)
open private neighborMask from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

private def vertices : Finset (BitVec 9) :=
  Finset.univ.map ⟨BitVec.ofFin, fun _ _ h => congrArg BitVec.toFin h⟩

private def reconstructedSupport (half : List (BitVec 9)) : Finset (BitVec 9) :=
  let mask := half.foldl (fun acc x => acc ^^^ neighborMask x) 0
  vertices.filter fun x =>
    if x.getLsbD 0 then mask.testBit (x.toNat / 2) = true else x ∈ half

attribute [local instance] Classical.propDecidable

private theorem mem_reconstructedSupport {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (half : List (BitVec 9)) (hn : half.Nodup)
    (hm : ∀ x : BitVec 9, x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice C false)
    (x : BitVec 9) : x ∈ reconstructedSupport half ↔ cubeBitVec 9 x ∈ C := by
  have hv : x ∈ vertices := Finset.mem_map.mpr ⟨x.toFin, Finset.mem_univ _, rfl⟩
  simp only [reconstructedSupport, Finset.mem_filter, hv, true_and]
  cases hx : x.getLsbD 0
  · simpa [hx, coordinateSlice, show cubeBitVec 9 x 0 = false from hx] using hm x
  · let y := x ^^^ (1 : BitVec 9)
    have hflip : cubeBitVec 9 y = BalancedCriticalSpectrum.flip (cubeBitVec 9 x) 0 :=
      cubeBitVec_xor_single x 0
    have hplane : y.getLsbD 0 = false := by
      change cubeBitVec 9 y 0 = false
      rw [hflip]
      simp [BalancedCriticalSpectrum.flip, show cubeBitVec 9 x 0 = true from hx]
    have hkey : y.toNat / 2 = x.toNat / 2 := by
      change (x.toNat ^^^ 1) / 2 = x.toNat / 2
      rw [← Nat.shiftRight_one, ← Nat.shiftRight_one, Nat.shiftRight_xor_distrib]
      simp
    have h := bit_iff_opposite_mem hr hb half hn hm hplane
    rw [hkey, hflip, BalancedCriticalSpectrum.flip_flip] at h
    simpa [hx] using h

private def listedHalves : List (List (BitVec 9)) :=
  ([[0, 1, 3, 6, 7, 10, 11, 20, 21, 23, 30, 31, 32, 34, 38, 42, 52, 54, 62, 64, 66, 70, 74,
      84, 86, 94],
    [0, 1, 3, 6, 7, 10, 11, 20, 21, 23, 32, 34, 38, 42, 52, 54, 64, 66, 70, 74, 84, 86, 150,
      151, 182, 214],
    [0, 1, 3, 6, 7, 10, 11, 23, 30, 31, 32, 34, 38, 42, 54, 62, 64, 66, 70, 74, 86, 94, 150,
      151, 182, 214]] : List (List Nat)).map (List.map fun x => BitVec.ofNat 9 (2 * x))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 40000000 in
private theorem listedCuts :
    listedHalves.all (fun half =>
      (Finset.filter (fun x => x.getLsbD 1 = true) (reconstructedSupport half)).card == 20) =
        true := by
  decide +kernel

/-- Each of the three half sets in the embedding calculation forces a 20-point
half in a second coordinate. -/
private theorem twenty_cut_of_listed_half {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {half : List (BitVec 9)} (hn : half.Nodup)
    (hm : ∀ x : BitVec 9, x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice C false)
    (hlisted : half ∈ listedHalves) : (C.filter fun x => x 1 = true).card = 20 := by
  classical
  have he :
      ((reconstructedSupport half).filter fun x => x.getLsbD 1 = true).image (cubeBitVec 9) =
        C.filter fun x => x 1 = true := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr
        ⟨(mem_reconstructedSupport hr hb half hn hm x).mp (Finset.mem_filter.mp hx).1,
          (Finset.mem_filter.mp hx).2⟩
    · intro hz
      let x := (cubeBitVec 9).symm z
      have hx : cubeBitVec 9 x = z := (cubeBitVec 9).apply_symm_apply z
      obtain ⟨hC, hbit⟩ := Finset.mem_filter.mp hz
      refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨?_, ?_⟩, hx⟩
      · exact (mem_reconstructedSupport hr hb half hn hm x).mpr (hx ▸ hC)
      · change cubeBitVec 9 x 1 = true
        rw [hx]
        exact hbit
  rw [← he, Finset.card_image_of_injective _ (cubeBitVec 9).injective]
  exact beq_iff_eq.mp (List.all_eq_true.mp listedCuts half hlisted)

#print axioms twenty_cut_of_listed_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixReconstruction
