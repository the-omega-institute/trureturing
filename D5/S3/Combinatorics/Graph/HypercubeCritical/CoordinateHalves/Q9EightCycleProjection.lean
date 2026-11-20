/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9EightCycleProjection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9EightCycleProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Fiber occupation and the weighted suffix quotient of a normalized eight-cycle. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4SmallProjectionOrbits
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5EightCycleQuotient

/-! Each parity class of the projected cycle is copied as a block in a suffix fiber.
The signed rows determine the degrees across the two resulting suffix supports. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9EightCycleProjection

open Finset
open scoped BigOperators
open Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9SignedProjection (join fiber signedRow)
open Q9FourFiberSpectrum (leftProjection signedRowOn fiber_and_signedRow_supported
  balanced_projection_two_step_mem_iff two_step_signed_value)
open Q4SmallProjectionOrbits (representative neighborDirections)
open Q9FourProjection (flipBit)
open Q9ThetaProjection (leftCode)
open private mem_leftProjection signedRow_eq_on abs_prefixSign abs_fiber from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
open private decode_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourProjection
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private carrier mem_carrier card_carrier carrier_false_endpoints twelve_direction_edges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection
open private pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection

local notation "flip" => BalancedCriticalSpectrum.flip

private instance : Fintype (BitVec 4) :=
  Fintype.ofEquiv (Fin (2 ^ 4)) (BitVec.equivFin (m := 4)).toEquiv.symm

/-- The first four coordinates in the specified order realize the eight-cycle representative. -/
def Normalized (C : Finset (Q 9)) : Prop :=
  leftProjection C = (representative false).image (cubeBitVec 4)

/-- The representative of a pattern's parity class in the normalized eight-cycle. -/
def parityRepresentative (k : BitVec 4) : BitVec 4 :=
  if k ∈ ({1, 2, 13, 14} : Finset (BitVec 4)) then 1 else 0

private theorem normalized_mem {C : Finset (Q 9)} (hn : Normalized C) (k : BitVec 4) :
    pattern k ∈ leftProjection C ↔ k ∈ representative false := by
  rw [Normalized] at hn
  rw [hn]
  constructor
  · rintro hk
    obtain ⟨l, hl, he⟩ := mem_image.mp hk
    exact (cubeBitVec 4).injective he ▸ hl
  · exact fun hk => mem_image_of_mem _ hk

private theorem normalized_directions {C : Finset (Q 9)} (hn : Normalized C) (k : BitVec 4) :
    directions (leftProjection C) (pattern k) = neighborDirections (representative false) k := by
  ext i
  rw [mem_directions, ← decode_flip, normalized_mem hn]
  simp [neighborDirections]

private theorem degree_table :
    ∀ k ∈ representative false, (neighborDirections (representative false) k).card = 2 := by
  decide +kernel

private theorem normalized_degree {C : Finset (Q 9)} (hn : Normalized C) :
    ∀ p ∈ leftProjection C, (directions (leftProjection C) p).card = 2 := by
  intro p hp
  obtain ⟨k, rfl⟩ := (cubeBitVec 4).surjective p
  rw [normalized_directions hn]
  exact degree_table k ((normalized_mem hn k).mp hp)

private theorem path_table : ∀ k ∈ representative false,
    let p := parityRepresentative k
    p ∈ representative false ∧ ∃ a b c d : Fin 4,
      let q := flipBit p a
      let r := flipBit q b
      let s := flipBit r c
      q ∈ representative false ∧ r ∈ representative false ∧ s ∈ representative false ∧
        flipBit s d = k := by
  decide +kernel

open Classical in
/-- Each pattern in the normalized cycle occurs in exactly the same suffix fibers
as its parity representative, with even class represented by 0 and odd class by 1. -/
theorem fiber_occupation {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) {k : BitVec 4} (hk : k ∈ representative false)
    (y : Q 5) :
    join (pattern k) y ∈ C ↔ join (pattern (parityRepresentative k)) y ∈ C := by
  have step {p : BitVec 4} {i j : Fin 4} (hp : p ∈ representative false)
      (hi : flipBit p i ∈ representative false)
      (hj : flipBit (flipBit p i) j ∈ representative false) :
      join (pattern p) y ∈ C ↔ join (pattern (flipBit (flipBit p i) j)) y ∈ C := by
    simp only [decode_flip] at ⊢
    apply balanced_projection_two_step_mem_iff hr hb (normalized_degree hn) y
      ((normalized_mem hn _).mpr hp)
    · rw [mem_directions, ← decode_flip, normalized_mem hn]
      exact hi
    · rw [mem_directions, ← decode_flip, ← decode_flip, normalized_mem hn]
      exact hj
  obtain ⟨hp, a, b, c, d, hq, hs, ht, hk'⟩ := path_table k hk
  have hpath := (step (i := a) (j := b) hp hq hs).trans
    (step (i := c) (j := d) hs ht (hk'.symm ▸ hk))
  rw [hk'] at hpath
  exact hpath.symm

open Classical in
private theorem carrier_eq {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) {k : BitVec 4} (hk : k ∈ representative false) :
    carrier C k = carrier C (parityRepresentative k) := by
  ext y
  simp only [mem_carrier, fiber_occupation hr hb hn hk y]

/-- The suffix support of the even class, including full fibers. -/
noncomputable def evenSupport (C : Finset (Q 9)) : Finset (Q 5) := carrier C 0

/-- The suffix support of the odd class, including full fibers. -/
noncomputable def oddSupport (C : Finset (Q 9)) : Finset (Q 5) := carrier C 1

private theorem leftCode_mem {C : Finset (Q 9)} (hn : Normalized C) {u : Q 9} (hu : u ∈ C) :
    leftCode u ∈ representative false := by
  apply (normalized_mem hn _).mp
  unfold leftCode pattern
  rw [Equiv.apply_symm_apply]
  exact mem_image_of_mem _ hu

private theorem card_sum_carriers {C T : Finset (Q 9)} (hn : Normalized C) (hsub : T ⊆ C) :
    T.card = ∑ k ∈ representative false, (carrier T k).card := by
  classical
  simpa only [card_carrier] using
    (card_eq_sum_card_fiberwise (f := leftCode) (s := T) (t := representative false)
      (fun _ hu => leftCode_mem hn (hsub hu)))

private theorem sum_representative {M : Type*} [AddCommMonoid M] (f : BitVec 4 → M) :
    (∑ k ∈ representative false, f k) =
      f 0 + (f 1 + (f 2 + (f 5 + (f 10 + (f 13 + (f 14 + f 15)))))) := by
  let codes : List (BitVec 4) := [0, 1, 2, 5, 10, 13, 14, 15]
  have hcodes : representative false = codes.toFinset := by decide +kernel
  have hnodup : codes.Nodup := by decide +kernel
  rw [hcodes, List.sum_toFinset f hnodup]
  simp only [codes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

open Classical in
private theorem sum_parity_carriers {M : Type*} [AddCommMonoid M] {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) (f : Finset (Q 5) → M) :
    (∑ k ∈ representative false, f (carrier C k)) =
      4 • f (evenSupport C) + 4 • f (oddSupport C) := by
  rw [sum_representative]
  have hc2 : carrier C 2 = carrier C 1 := carrier_eq hr hb hn (k := 2) (by decide +kernel)
  have hc5 : carrier C 5 = carrier C 0 := carrier_eq hr hb hn (k := 5) (by decide +kernel)
  have hc10 : carrier C 10 = carrier C 0 := carrier_eq hr hb hn (k := 10) (by decide +kernel)
  have hc13 : carrier C 13 = carrier C 1 := carrier_eq hr hb hn (k := 13) (by decide +kernel)
  have hc14 : carrier C 14 = carrier C 1 := carrier_eq hr hb hn (k := 14) (by decide +kernel)
  have hc15 : carrier C 15 = carrier C 0 := carrier_eq hr hb hn (k := 15) (by decide +kernel)
  rw [hc2, hc5, hc10, hc13, hc14, hc15]
  simp only [evenSupport, oddSupport, show (4 : ℕ) = 3 + 1 by decide, add_nsmul, one_nsmul,
    show (3 : ℕ) = 2 + 1 by decide, two_nsmul]
  abel

open Classical in
/-- Each occupied parity class contributes four vertices in a suffix fiber. -/
theorem normalized_card {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) :
    C.card = 4 * (evenSupport C).card + 4 * (oddSupport C).card := by
  rw [card_sum_carriers hn (Subset.rfl : C ⊆ C)]
  simpa [nsmul_eq_mul] using sum_parity_carriers hr hb hn (fun T => T.card)

private theorem neighbor_table : ∀ k ∈ representative false, ∃ i : Fin 4,
    flipBit k i ∈ representative false ∧
      parityRepresentative (flipBit k i) = (if parityRepresentative k = 0 then 1 else 0) := by
  decide +kernel

open Classical in
/-- At any pattern whose opposite class is occupied, the absolute prefix row is two. -/
theorem abs_signedRow_of_opposite_occupied {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C)
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u) (y : Q 5)
    {k : BitVec 4} (hk : k ∈ representative false)
    (hy : join (pattern (if parityRepresentative k = 0 then 1 else 0)) y ∈ C) :
    |signedRow (fiber z y) (pattern k)| = 2 := by
  obtain ⟨i, hi, hclass⟩ := neighbor_table k hk
  let p := pattern (flipBit k i)
  have hpk : flip p i = pattern k := by
    exact (congrArg (fun q => flip q i) (decode_flip k i)).trans
      (BalancedCriticalSpectrum.flip_flip _ _)
  have hp := (normalized_mem hn _).mpr hi
  have hx : join p y ∈ C := (fiber_occupation hr hb hn hi y).mpr (hclass.symm ▸ hy)
  have hi' : i ∈ directions (leftProjection C) p :=
    (mem_directions _ _ i).mpr (hpk ▸ (normalized_mem hn _).mpr hk)
  have hs (q : Q 4) (hq : q ∉ leftProjection C) :=
    fiber_and_signedRow_supported hzero hrow y hq
  have hbound (q : Q 4) : |fiber z y q| ≤ 1 := by
    rw [abs_fiber hunit hzero]
    split <;> decide
  have hentry : |fiber z y p| = 1 := by rw [abs_fiber hunit hzero, ite_eq_left hx]
  have hdeg := normalized_degree hn
  have hsum : truePrefixSign p i * signedRowOn (leftProjection C) (fiber z y) (flip p i) =
      2 * fiber z y p := by
    rw [signedRowOn, mul_sum]
    calc
      _ = ∑ _j ∈ directions (leftProjection C) (flip p i), fiber z y p := by
        apply sum_congr rfl
        intro j hj
        exact two_step_signed_value (fun q hq => (hs q hq).1) (fun q hq => (hs q hq).2)
          hbound hentry (hdeg _ hp) (fun a ha => hdeg _ ((mem_directions _ _ a).mp ha))
          hi' hj
      _ = _ := by simp [hdeg _ ((mem_directions _ _ i).mp hi')]
  have habs := congrArg abs hsum
  have habsTwo : |(2 : ℤ)| = 2 := by decide
  simpa only [abs_mul, abs_prefixSign, one_mul, hentry, mul_one, habsTwo, hpk,
    ← signedRow_eq_on (leftProjection C) (fun q hq => (hs q hq).1)] using habs

/-- Suffixes with the even class alone. -/
noncomputable def evenOnly (C : Finset (Q 9)) : Finset (Q 5) := evenSupport C \ oddSupport C

/-- Suffixes with the odd class alone. -/
noncomputable def oddOnly (C : Finset (Q 9)) : Finset (Q 5) := oddSupport C \ evenSupport C

/-- Suffixes with both classes. -/
noncomputable def fullSupport (C : Finset (Q 9)) : Finset (Q 5) := evenSupport C ∩ oddSupport C

private theorem even_union_full (C : Finset (Q 9)) :
    evenOnly C ∪ fullSupport C = evenSupport C := by
  ext y
  simp only [evenOnly, fullSupport, mem_union, mem_sdiff, mem_inter]
  tauto

private theorem odd_union_full (C : Finset (Q 9)) :
    oddOnly C ∪ fullSupport C = oddSupport C := by
  ext y
  simp only [oddOnly, fullSupport, mem_union, mem_sdiff, mem_inter]
  tauto

private theorem supports_disjoint (C : Finset (Q 9)) :
    Disjoint (evenOnly C) (oddOnly C) ∧ Disjoint (evenOnly C) (fullSupport C) ∧
      Disjoint (oddOnly C) (fullSupport C) := by
  simp only [disjoint_left, evenOnly, oddOnly, fullSupport, mem_sdiff, mem_inter]
  tauto

private theorem carrier_outside {C : Finset (Q 9)} (hn : Normalized C) {k : BitVec 4}
    (hk : k ∉ representative false) : carrier C k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hk ((normalized_mem hn k).mp (mem_leftProjection.mpr ⟨y, (mem_carrier _ _ _).mp hy⟩))

open Classical in
private theorem normalized_direction_zero_edges {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) :
    directionEdges C ((0 : Fin 4).castAdd 5) = 2 * (fullSupport C).card := by
  rw [directionEdges, card_sum_carriers hn (filter_subset _ _)]
  simp only [carrier_false_endpoints, sum_representative]
  change (carrier C 0 ∩ carrier C 1).card + (0 + ((carrier C 2 ∩ carrier C 3).card +
    (0 + ((carrier C 10 ∩ carrier C 11).card +
    (0 + ((carrier C 14 ∩ carrier C 15).card + 0)))))) = _
  have h3 := carrier_outside hn (k := 3) (by decide +kernel)
  have h11 := carrier_outside hn (k := 11) (by decide +kernel)
  have h14 : carrier C 14 = carrier C 1 := carrier_eq hr hb hn (k := 14) (by decide +kernel)
  have h15 : carrier C 15 = carrier C 0 := carrier_eq hr hb hn (k := 15) (by decide +kernel)
  rw [h3, h11, h14, h15, inter_comm (carrier C 1) (carrier C 0)]
  simp [fullSupport, evenSupport, oddSupport, two_mul]

open Classical in
/-- The normalized order-72 support has six full fibers and six exclusive fibers. -/
theorem normalized_fiber_counts {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) (hsize : C.card = 72) :
    (fullSupport C).card = 6 ∧ (evenOnly C).card + (oddOnly C).card = 6 := by
  obtain ⟨_, hRF, hBF⟩ := supports_disjoint C
  have hfull : (fullSupport C).card = 6 := by
    have he := twelve_direction_edges hr hb hsize ((0 : Fin 4).castAdd 5)
    rw [normalized_direction_zero_edges hr hb hn] at he
    omega
  have htotal := normalized_card hr hb hn
  rw [← even_union_full C, ← odd_union_full C, card_union_of_disjoint hRF,
    card_union_of_disjoint hBF] at htotal
  exact ⟨hfull, by omega⟩

private theorem carrier_suffix_cut (C : Finset (Q 9)) (k : BitVec 4) (i : Fin 5) (b : Bool) :
    carrier (C.filter fun u => u (i.natAdd 4) = b) k =
      (carrier C k).filter fun y => y i = b := by
  ext y
  simp only [mem_carrier, mem_filter, join, Fin.append_right]

open Classical in
/-- The size of an ambient suffix half is four times the weight of its quotient half. -/
theorem normalized_suffix_half_card {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) (i : Fin 5) (b : Bool) :
    (C.filter fun u => u (i.natAdd 4) = b).card =
      4 * Q5EightCycleQuotient.halfWeight (evenOnly C) (oddOnly C) (fullSupport C) i b := by
  rw [card_sum_carriers hn (filter_subset _ _)]
  simp only [carrier_suffix_cut]
  rw [sum_parity_carriers hr hb hn (fun T => (T.filter fun y => y i = b).card)]
  obtain ⟨_, hRF, hBF⟩ := supports_disjoint C
  have cut_card {S T : Finset (Q 5)} (h : Disjoint S T) :
      ((S ∪ T).filter fun y => y i = b).card =
        (S.filter fun y => y i = b).card + (T.filter fun y => y i = b).card := by
    rw [filter_union, card_union_of_disjoint (h.mono (filter_subset _ _) (filter_subset _ _))]
  simp only [← even_union_full C, ← odd_union_full C, cut_card hRF, cut_card hBF,
    Q5EightCycleQuotient.halfWeight]
  change 4 * _ + 4 * _ = _
  omega

private theorem neighbor_parity_table :
    ∀ k ∈ representative false, ∀ i : Fin 4, flipBit k i ∈ representative false →
      parityRepresentative (flipBit k i) = (if parityRepresentative k = 0 then 1 else 0) := by
  decide +kernel

private noncomputable def prefixSupport (C : Finset (Q 9)) (y : Q 5) : Finset (Q 4) := by
  classical
  exact univ.filter fun p => join p y ∈ C

@[simp] private theorem mem_prefixSupport (C : Finset (Q 9)) (y : Q 5) (p : Q 4) :
    p ∈ prefixSupport C y ↔ join p y ∈ C := by
  simp [prefixSupport]

open Q5EightCycleQuotient (neighbors SquareFree)
open private flip_join_left flip_join_right from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open private directions_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private signedRow_eq_sum_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum

private theorem neighbors_card_eq_directions (T : Finset (Q 5)) (y : Q 5) :
    (neighbors T y).card = (directions T y).card :=
  (directions_card T y).symm

open Classical in
private theorem degree_split (C : Finset (Q 9)) (k : BitVec 4) (y : Q 5) :
    (directions C (join (pattern k) y)).card =
      (directions (prefixSupport C y) (pattern k)).card + (neighbors (carrier C k) y).card := by
  rw [neighbors_card_eq_directions]
  simp only [directions, card_filter]
  rw [Fin.sum_univ_add (a := 4) (b := 5)]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply sum_congr rfl
    intro j _
    exact if_congr (by rw [flip_join_left, mem_prefixSupport]) rfl rfl
  · apply sum_congr rfl
    intro j _
    exact if_congr (by rw [flip_join_right, mem_carrier]) rfl rfl

open Classical in
private theorem normalized_prefix_degree {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) {k : BitVec 4} (hk : k ∈ representative false)
    (y : Q 5) :
    (directions (prefixSupport C y) (pattern k)).card =
      if y ∈ carrier C (if parityRepresentative k = 0 then 1 else 0) then 2 else 0 := by
  let p : BitVec 4 := if parityRepresentative k = 0 then 1 else 0
  change _ = if y ∈ carrier C p then 2 else 0
  have hdirs : directions (prefixSupport C y) (pattern k) =
      if y ∈ carrier C p then directions (leftProjection C) (pattern k) else ∅ := by
    ext j
    rw [mem_directions, mem_prefixSupport, ← decode_flip]
    by_cases hj : flipBit k j ∈ representative false
    · have hd : j ∈ directions (leftProjection C) (pattern k) := by
        rw [mem_directions, ← decode_flip, normalized_mem hn]
        exact hj
      rw [fiber_occupation hr hb hn hj, neighbor_parity_table k hk j hj, ← mem_carrier]
      change y ∈ carrier C p ↔ _
      by_cases hy : y ∈ carrier C p
      · rw [ite_eq_left hy]
        exact iff_of_true hy hd
      · rw [ite_eq_right hy]
        exact iff_of_false hy (notMem_empty _)
    · have hd : j ∉ directions (leftProjection C) (pattern k) := by
        rw [mem_directions, ← decode_flip, normalized_mem hn]
        exact hj
      have hs : join (pattern (flipBit k j)) y ∉ C := fun h =>
        hj ((normalized_mem hn _).mp (mem_leftProjection.mpr ⟨y, h⟩))
      by_cases hy : y ∈ carrier C p
      · rw [ite_eq_left hy]
        exact iff_of_false hs hd
      · rw [ite_eq_right hy]
        exact iff_of_false hs (notMem_empty _)
  rw [hdirs]
  by_cases hy : y ∈ carrier C p
  · simpa only [ite_eq_left hy] using normalized_degree hn _ ((normalized_mem hn k).mpr hk)
  · simp only [ite_eq_right hy, card_empty]

open Classical in
private theorem same_class_degree {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) {k : BitVec 4} (hk : k ∈ representative false)
    {y : Q 5} (hy : y ∈ carrier C k) :
    (neighbors (carrier C k) y).card =
      if y ∈ carrier C (if parityRepresentative k = 0 then 1 else 0) then 1 else 3 := by
  have hreg := regular_directions C hr ((mem_carrier C k y).mp hy)
  rw [degree_split, normalized_prefix_degree hr hb hn hk] at hreg
  by_cases h : y ∈ carrier C (if parityRepresentative k = 0 then 1 else 0)
  · simp only [ite_eq_left h] at hreg ⊢
    omega
  · simp only [ite_eq_right h] at hreg ⊢
    omega

open Classical in
private theorem degree_of_abs_suffix_row_two {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (k : BitVec 4) (y : Q 5)
    (habs : |signedRow (fun v => fiber z v (pattern k)) y| = 2) :
    (neighbors (carrier C k) y).card = 2 ∨ (neighbors (carrier C k) y).card = 4 := by
  let D := directions (carrier C k) y
  let term (j : Fin 5) := truePrefixSign y j * fiber z (flip y j) (pattern k)
  have hz (v : Q 5) (hv : v ∉ carrier C k) : fiber z v (pattern k) = 0 :=
    hzero _ (fun h => hv ((mem_carrier _ _ _).mpr h))
  rw [signedRow_eq_sum_directions (carrier C k) hz] at habs
  change |∑ j ∈ D, term j| = 2 at habs
  have hu (j : Fin 5) (hj : j ∈ D) : |term j| = 1 := by
    have hocc := (mem_carrier C k _).mp ((mem_directions _ _ j).mp hj)
    simp only [term, abs_mul, abs_prefixSign, one_mul, abs_fiber hunit hzero, ite_eq_left hocc]
  have hlower : (2 : ℤ) ≤ D.card := by
    calc
      2 = |∑ j ∈ D, term j| := habs.symm
      _ ≤ ∑ j ∈ D, |term j| := abs_sum_le_sum_abs _ _
      _ = ∑ _j ∈ D, (1 : ℤ) := sum_congr rfl hu
      _ = D.card := by simp
  have hupper : D.card ≤ 5 := by
    simpa using card_le_univ D
  -- A sum of signed units has the same parity as the number of summands.
  have hsum : (∑ j ∈ D, term j) = 2 * (∑ j ∈ D, (if term j = 1 then 1 else 0 : ℤ)) -
      D.card := by
    calc
      _ = ∑ j ∈ D, (2 * (if term j = 1 then 1 else 0 : ℤ) - 1) := by
        apply sum_congr rfl
        intro j hj
        rcases (abs_eq (by decide)).mp (hu j hj) with h | h <;> simp [h]
      _ = _ := by
        rw [sum_sub_distrib, mul_sum]
        simp
  rw [neighbors_card_eq_directions]
  change D.card = 2 ∨ D.card = 4
  rcases (abs_eq (by decide)).mp habs with h | h <;> omega

open Classical in
private theorem opposite_class_degree {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C)
    (hunit : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    {k : BitVec 4} (hk : k ∈ representative false)
    {y : Q 5} (hy : y ∉ carrier C k)
    (hopp : y ∈ carrier C (if parityRepresentative k = 0 then 1 else 0)) :
    (neighbors (carrier C k) y).card = 2 ∨ (neighbors (carrier C k) y).card = 4 := by
  apply degree_of_abs_suffix_row_two hunit hzero
  have hprefix := abs_signedRow_of_opposite_occupied hr hb hn hunit hzero hrow y hk
    ((mem_carrier _ _ _).mp hopp)
  have hentry : fiber z y (pattern k) = 0 := hzero _ (fun h => hy ((mem_carrier _ _ _).mpr h))
  have hsplit := Q9SignedProjection.q9_signed_row_split hrow (pattern k) y
  rw [hentry, mul_zero] at hsplit
  have hcancel : signedRow (fiber z y) (pattern k) =
      -(Q9SignedProjection.leftParitySign (pattern k) *
        signedRow (fun v => fiber z v (pattern k)) y) := eq_neg_of_add_eq_zero_left hsplit.symm
  have hparity : |Q9SignedProjection.leftParitySign (pattern k)| = 1 := by
    simp [Q9SignedProjection.leftParitySign, abs_pow]
  rw [hcancel, abs_neg, abs_mul, hparity, one_mul] at hprefix
  exact hprefix

open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private common_neighbor from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5EightCycleQuotient

private theorem carrier_squareFree {C : Finset (Q 9)} (hb : IsBalanced C) (k : BitVec 4) :
    SquareFree (carrier C k) := by
  intro x hx z hz hxz y hy w hw hyw hxy hxw hzy hzw
  obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
  obtain ⟨j, rfl⟩ := adjacent_exists_flip hxw
  have hij : i ≠ j := fun h => hyw (congrArg (flip x) h)
  have hz' := (common_neighbor hij hzy.symm hzw.symm).resolve_left hxz.symm
  have hlift : i.natAdd 4 ≠ j.natAdd 4 := fun h =>
    hij (Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))
  apply BalancedCubeGirth.no_selected_square hb hlift ((mem_carrier _ _ _).mp hx)
  · rw [flip_join_right]
    exact (mem_carrier _ _ _).mp hy
  · rw [flip_join_right]
    exact (mem_carrier _ _ _).mp hw
  · rw [flip_join_right, flip_join_right, ← hz']
    exact (mem_carrier _ _ _).mp hz

open Classical in
/-- The two suffix classes of a normalized order-72 projection satisfy the
eight-cycle quotient theorem and force a suffix half of quotient weight five. -/
theorem normalized_halfWeight_eq_five {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) (hsize : C.card = 72) :
    ∃ i b, Q5EightCycleQuotient.halfWeight (evenOnly C) (oddOnly C) (fullSupport C) i b = 5 := by
  obtain ⟨hRB, hRF, hBF⟩ := supports_disjoint C
  obtain ⟨hF, hRBsize⟩ := normalized_fiber_counts hr hb hn hsize
  obtain ⟨z, hunit, hzero, hrow, _⟩ := Q9SignedProjection.q9_balanced_signed_projection hr hb
  have h0 : (0 : BitVec 4) ∈ representative false := by decide +kernel
  have h1 : (1 : BitVec 4) ∈ representative false := by decide +kernel
  have hd0 {y : Q 5} (hy : y ∈ evenSupport C) :
      (neighbors (evenSupport C) y).card = if y ∈ oddSupport C then 1 else 3 :=
    same_class_degree hr hb hn h0 hy
  have hd1 {y : Q 5} (hy : y ∈ oddSupport C) :
      (neighbors (oddSupport C) y).card = if y ∈ evenSupport C then 1 else 3 :=
    same_class_degree hr hb hn h1 hy
  apply Q5EightCycleQuotient.halfWeight_eq_five hRB hRF hBF hRBsize hF
  all_goals first | rw [even_union_full] | rw [odd_union_full]
  · intro y hy
    obtain ⟨he, ho⟩ := mem_sdiff.mp hy
    simpa only [ite_eq_right ho] using hd0 he
  · intro y hy
    obtain ⟨ho, he⟩ := mem_sdiff.mp hy
    simpa only [ite_eq_right he] using hd1 ho
  · intro y hy
    obtain ⟨he, ho⟩ := mem_inter.mp hy
    simpa only [ite_eq_left ho] using hd0 he
  · intro y hy
    obtain ⟨he, ho⟩ := mem_inter.mp hy
    simpa only [ite_eq_left he] using hd1 ho
  · intro y hy
    obtain ⟨he, ho⟩ := mem_sdiff.mp hy
    exact opposite_class_degree hr hb hn hunit hzero hrow h1 ho he
  · intro y hy
    obtain ⟨ho, he⟩ := mem_sdiff.mp hy
    exact opposite_class_degree hr hb hn hunit hzero hrow h0 he ho
  · exact carrier_squareFree hb 0
  · exact carrier_squareFree hb 1

open Classical in
/-- A normalized eight-cycle projection of a balanced induced cubic support of order
72 forces a coordinate half of size 20 in the remaining five coordinates. -/
theorem normalized_exists_half_card_twenty {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) (hsize : C.card = 72) :
    ∃ (i : Fin 5) (b : Bool), (C.filter fun u => u (i.natAdd 4) = b).card = 20 := by
  obtain ⟨i, b, hi⟩ := normalized_halfWeight_eq_five hr hb hn hsize
  exact ⟨i, b, by rw [normalized_suffix_half_card hr hb hn, hi]⟩

#print axioms fiber_occupation
#print axioms normalized_card
#print axioms abs_signedRow_of_opposite_occupied
#print axioms normalized_fiber_counts
#print axioms normalized_suffix_half_card
#print axioms normalized_halfWeight_eq_five
#print axioms normalized_exists_half_card_twenty

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9EightCycleProjection
