import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
import Batteries.Tactic.OpenPrivate

/-! The nine-point theta projection of a balanced cubic support collapses to its
eight-cycle. Exterior signed rows tie the occupied fibers of the two branch
vertices together. Cubicity then makes the middle vertex of the short path
have no selected neighbors along the four projection coordinates. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip directionEdges direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9SignedProjection (join fiber signedRow q9_balanced_signed_projection)
open private flip_join_left flip_join_right from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private balanced_subset from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

/-- The four projection coordinates in little-endian order, starting at coordinate zero. -/
def leftCode (u : Q 9) : BitVec 4 :=
  (cubeBitVec 4).symm (fun i : Fin 4 => u (i.castAdd 5))

/-- The allowed four-bit patterns of the three paths between points 1 and 2. -/
def thetaEnvelope : Finset (BitVec 4) := {1, 2, 3, 4, 5, 6, 8, 9, 10}

private abbrev pattern (k : BitVec 4) : Q 4 := cubeBitVec 4 k

private def rightBlock (u : Q 9) : Q 5 := fun i => u (i.natAdd 4)

private theorem leftCode_join (k : BitVec 4) (y : Q 5) :
    leftCode (join (pattern k) y) = k := by
  simpa only [leftCode, join, Fin.append_left] using (cubeBitVec 4).symm_apply_apply k

private theorem join_blocks (u : Q 9) : join (pattern (leftCode u)) (rightBlock u) = u := by
  change join ((cubeBitVec 4) ((cubeBitVec 4).symm (fun i : Fin 4 => u (i.castAdd 5))))
    (rightBlock u) = u
  rw [Equiv.apply_symm_apply]
  exact Fin.append_castAdd_natAdd (m := 4) (n := 5) (f := u)

private def flipCode (k : BitVec 4) (i : Fin 4) : BitVec 4 :=
  k ^^^ BitVec.ofNat 4 (2 ^ i.val)

private theorem flip_pattern (k : BitVec 4) (i : Fin 4) :
    flip (pattern k) i = pattern (flipCode k i) :=
  (cubeBitVec_xor_single k i).symm

-- Use a computable filter for the closed sign checks.
private def prefixSign (k : BitVec 4) (i : Fin 4) : ℤ :=
  (-1) ^ ((univ : Finset (Fin 4)).filter fun j => j < i ∧ pattern k j = true).card

private theorem prefixSign_eq (k : BitVec 4) (i : Fin 4) :
    truePrefixSign (pattern k) i = prefixSign k i := by
  unfold truePrefixSign prefixSign
  exact congrArg (fun s : Finset (Fin 4) => (-1 : ℤ) ^ s.card)
    (Finset.filter_congr_decidable _ _ _)

private theorem sum_four {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + f 3)) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]

private abbrev FlipTable (k a b c d : BitVec 4) : Prop :=
  flipCode k 0 = a ∧ flipCode k 1 = b ∧ flipCode k 2 = c ∧ flipCode k 3 = d

private theorem signed_row_four (g : Q 4 → ℤ) (k a b c d : BitVec 4) (s₀ s₁ s₂ s₃ : ℤ)
    (hf : FlipTable k a b c d)
    (hs : prefixSign k 0 = s₀ ∧ prefixSign k 1 = s₁ ∧
      prefixSign k 2 = s₂ ∧ prefixSign k 3 = s₃) :
    signedRow g (pattern k) =
      s₀ * g (pattern a) + (s₁ * g (pattern b) + (s₂ * g (pattern c) + s₃ * g (pattern d))) := by
  obtain ⟨ha, hb, hc, hd⟩ := hf
  obtain ⟨hs₀, hs₁, hs₂, hs₃⟩ := hs
  simp only [signedRow, sum_four, flip_pattern, ha, hb, hc, hd, prefixSign_eq, hs₀, hs₁, hs₂, hs₃]

private theorem boundary_rows (g : Q 4 → ℤ) :
    signedRow g (pattern 0) = g (pattern 1) + (g (pattern 2) + (g (pattern 4) + g (pattern 8))) ∧
    signedRow g (pattern 7) = g (pattern 6) + (-g (pattern 5) + (g (pattern 3) + -g (pattern 15))) ∧
    signedRow g (pattern 12) = g (pattern 13) + (g (pattern 14) + (g (pattern 8) + -g (pattern 4))) ∧
    signedRow g (pattern 13) = g (pattern 12) + (-g (pattern 15) + (-g (pattern 9) + g (pattern 5))) ∧
    signedRow g (pattern 14) = g (pattern 15) + (g (pattern 12) + (-g (pattern 10) + g (pattern 6))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul] using
      signed_row_four g 0 1 2 4 8 1 1 1 1 (by decide +kernel) (by decide +kernel)
  · simpa only [one_mul, neg_one_mul] using
      signed_row_four g 7 6 5 3 15 1 (-1) 1 (-1) (by decide +kernel) (by decide +kernel)
  · simpa only [one_mul, neg_one_mul] using
      signed_row_four g 12 13 14 8 4 1 1 1 (-1) (by decide +kernel) (by decide +kernel)
  · simpa only [one_mul, neg_one_mul] using
      signed_row_four g 13 12 15 9 5 1 (-1) (-1) 1 (by decide +kernel) (by decide +kernel)
  · simpa only [one_mul, neg_one_mul] using
      signed_row_four g 14 15 12 10 6 1 1 (-1) 1 (by decide +kernel) (by decide +kernel)

private theorem outside_patterns :
    (0 : BitVec 4) ∉ thetaEnvelope ∧ (7 : BitVec 4) ∉ thetaEnvelope ∧
    (11 : BitVec 4) ∉ thetaEnvelope ∧ (12 : BitVec 4) ∉ thetaEnvelope ∧
    (13 : BitVec 4) ∉ thetaEnvelope ∧ (14 : BitVec 4) ∉ thetaEnvelope ∧
    (15 : BitVec 4) ∉ thetaEnvelope := by
  decide +kernel

private theorem flips_one : FlipTable 1 0 3 5 9 := by decide +kernel
private theorem flips_two : FlipTable 2 3 0 6 10 := by decide +kernel
private theorem flips_three : FlipTable 3 2 1 7 11 := by decide +kernel

attribute [local instance] Classical.propDecidable

private theorem boundary_relations (g : Q 4 → ℤ)
    (hz : ∀ k ∉ thetaEnvelope, g (pattern k) = 0)
    (hr : ∀ k ∉ thetaEnvelope, signedRow g (pattern k) = 0) :
    g (pattern 8) = g (pattern 4) ∧ g (pattern 9) = g (pattern 5) ∧
    g (pattern 10) = g (pattern 6) ∧ g (pattern 1) + g (pattern 2) = -2 * g (pattern 4) ∧
    g (pattern 3) = g (pattern 5) - g (pattern 6) := by
  obtain ⟨n0, n7, _, n12, n13, n14, n15⟩ := outside_patterns
  obtain ⟨e0, e7, e12, e13, e14⟩ := boundary_rows g
  simp only [hr 0 n0, hr 7 n7, hr 12 n12, hr 13 n13, hr 14 n14,
    hz 12 n12, hz 13 n13, hz 14 n14, hz 15 n15, neg_zero, add_zero, zero_add]
    at e0 e7 e12 e13 e14
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

private noncomputable def occupation (C : Finset (Q 9)) (k : BitVec 4) (y : Q 5) : ℕ :=
  if join (pattern k) y ∈ C then 1 else 0

private theorem degree_split (C : Finset (Q 9)) (k : BitVec 4) (y : Q 5) :
    (directions C (join (pattern k) y)).card =
      (∑ i : Fin 4, occupation C (flipCode k i) y) +
        ∑ j : Fin 5, occupation C k (flip y j) := by
  unfold directions
  rw [Finset.card_filter, Fin.sum_univ_add (a := 4) (b := 5)]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply sum_congr rfl
    intro i _
    unfold occupation
    exact if_congr (by rw [flip_join_left, flip_pattern]) rfl rfl
  · apply sum_congr rfl
    intro j _
    unfold occupation
    exact if_congr (by rw [flip_join_right]) rfl rfl

private theorem row_degree {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {k a b c d : BitVec 4} {y : Q 5} (hf : FlipTable k a b c d)
    (hy : join (pattern k) y ∈ C) :
    occupation C a y + (occupation C b y + (occupation C c y + occupation C d y)) +
      (∑ j : Fin 5, occupation C k (flip y j)) = 3 := by
  obtain ⟨ha, hb, hc, hd⟩ := hf
  have h := regular_directions C hr hy
  rw [degree_split, sum_four] at h
  simpa only [ha, hb, hc, hd] using h

/-- A balanced induced cubic support in the nine-cube whose first four bits lie in
the theta envelope cannot contain a vertex with projected point 3. -/
theorem theta_projection_excludes_three {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (htheta : ∀ u ∈ C, leftCode u ∈ thetaEnvelope) :
    ∀ u ∈ C, leftCode u ≠ 3 := by
  obtain ⟨z, hunit, hzero, _, hrow⟩ := q9_balanced_signed_projection hr hb
  let h (k : BitVec 4) (y : Q 5) : ℤ := fiber z y (pattern k)
  have selected (k : BitVec 4) (y : Q 5) : join (pattern k) y ∈ C ↔ h k y ≠ 0 := by
    constructor
    · intro hy hz
      change z (join (pattern k) y) = 0 at hz
      rcases hunit _ hy with hp | hm <;> omega
    · intro hn
      by_contra hy
      exact hn (hzero _ hy)
  have flat (k : BitVec 4) (y : Q 5) : h k y = 0 ∨ h k y = 1 ∨ h k y = -1 := by
    by_cases hy : join (pattern k) y ∈ C
    · exact Or.inr (hunit _ hy)
    · exact Or.inl (hzero _ hy)
  have avoid (k : BitVec 4) (hk : k ∉ thetaEnvelope) (y : Q 5) : join (pattern k) y ∉ C := by
    intro hy
    exact hk (by simpa only [leftCode_join] using htheta _ hy)
  have boundary (y : Q 5) :
      h 8 y = h 4 y ∧ h 9 y = h 5 y ∧ h 10 y = h 6 y ∧
      h 1 y + h 2 y = -2 * h 4 y ∧ h 3 y = h 5 y - h 6 y :=
    boundary_relations (fiber z y) (fun k hk => hzero _ (avoid k hk y))
      (fun k hk => hrow (pattern k) (avoid k hk) y)
  -- Flatness and the even sum identify the supports of the two branch rows.
  have sameEnds (y : Q 5) : join (pattern 1) y ∈ C ↔ join (pattern 2) y ∈ C := by
    rw [selected 1 y, selected 2 y]
    apply not_congr
    obtain ⟨_, _, _, he, _⟩ := boundary y
    constructor
    · intro h1
      rcases flat 2 y with h2 | h2 | h2 <;> omega
    · intro h2
      rcases flat 1 y with h1 | h1 | h1 <;> omega
  have occupation_eq (y : Q 5) {k l : BitVec 4} (he : h k y = h l y) :
      occupation C k y = occupation C l y := by
    unfold occupation
    refine if_congr ?_ rfl rfl
    rw [selected k y, selected l y, he]
  have zeroThree (y : Q 5) (hy : join (pattern 1) y ∈ C) : h 3 y = 0 := by
    obtain ⟨_, h95, h106, _, h356⟩ := boundary y
    have complementary :
        (∑ j : Fin 5, occupation C 1 (flip y j)) =
        ∑ j : Fin 5, occupation C 2 (flip y j) := by
      apply sum_congr rfl
      intro j _
      unfold occupation
      exact if_congr (sameEnds (flip y j)) rfl rfl
    have h0 : occupation C 0 y = 0 := ite_eq_right (avoid 0 outside_patterns.1 y)
    have d1 := row_degree hr flips_one hy
    have d2 := row_degree hr flips_two ((sameEnds y).mp hy)
    rw [h0, occupation_eq y h95] at d1
    rw [h0, occupation_eq y h106, ← complementary] at d2
    have ho : occupation C 5 y = occupation C 6 y := by omega
    have hs : h 5 y ≠ 0 ↔ h 6 y ≠ 0 := by
      have one (k : BitVec 4) : occupation C k y = 1 ↔ join (pattern k) y ∈ C := by
        unfold occupation
        by_cases hk : join (pattern k) y ∈ C <;> simp [hk]
      rw [← selected 5 y, ← selected 6 y, ← one 5, ← one 6, ho]
    by_cases h5 : h 5 y = 0
    · have h6 : h 6 y = 0 := by
        by_contra hn
        exact hs.mpr hn h5
      omega
    · rcases (flat 5 y).resolve_left h5 with hp5 | hm5 <;>
        rcases (flat 6 y).resolve_left (hs.mp h5) with hp6 | hm6 <;>
        rcases flat 3 y with h3 | h3 | h3 <;> omega
  have noLeft (y : Q 5) (hy : join (pattern 3) y ∈ C) (i : Fin 4) :
      flip (join (pattern 3) y) (i.castAdd 5) ∉ C := by
    have noOne : join (pattern 1) y ∉ C := fun h1 => (selected 3 y).mp hy (zeroThree y h1)
    have noTwo : join (pattern 2) y ∉ C := fun h2 => noOne ((sameEnds y).mpr h2)
    obtain ⟨f0, f1, f2, f3⟩ := flips_three
    rw [flip_join_left, flip_pattern]
    fin_cases i
    · change join (pattern (flipCode 3 0)) y ∉ C
      rw [f0]
      exact noTwo
    · change join (pattern (flipCode 3 1)) y ∉ C
      rw [f1]
      exact noOne
    · change join (pattern (flipCode 3 2)) y ∉ C
      rw [f2]
      exact avoid 7 outside_patterns.2.1 y
    · change join (pattern (flipCode 3 3)) y ∉ C
      rw [f3]
      exact avoid 11 outside_patterns.2.2.1 y
  -- The row at point 3 is closed in the induced graph, so it is still cubic.
  let E := C.filter (fun u => leftCode u = 3)
  have hsub : E ⊆ C := filter_subset _ _
  have represent {u : Q 9} (hu : u ∈ E) : join (pattern 3) (rightBlock u) = u := by
    have hcode : leftCode u = 3 := (mem_filter.mp hu).2
    rw [← hcode, join_blocks]
  have closed {u v : Q 9} (hu : u ∈ E) (hv : v ∈ C) (huv : (hypercube 9).Adj u v) :
      v ∈ E := by
    obtain ⟨i, rfl⟩ := adjacent_exists_flip huv
    refine mem_filter.mpr ⟨hv, ?_⟩
    have hu' : join (pattern 3) (rightBlock u) ∈ C := by
      rw [represent hu]
      exact hsub hu
    rw [← represent hu] at hv ⊢
    revert hv
    refine Fin.addCases (m := 4) (n := 5) ?_ ?_ i
    · intro j hj
      exact (noLeft _ hu' j hj).elim
    · intro j _
      rw [flip_join_right, leftCode_join]
  have hreg : ((hypercube 9).induce (E : Set (Q 9))).IsRegularOfDegree 3 := by
    intro u
    have neighbors : (hypercube 9).neighborFinset u.val ∩ E =
        (hypercube 9).neighborFinset u.val ∩ C := by
      ext v
      simp only [mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun ⟨huv, hv⟩ => ⟨huv, hsub hv⟩,
        fun ⟨huv, hv⟩ => ⟨huv, closed u.property hv huv⟩⟩
    calc
      _ = ((hypercube 9).neighborFinset u.val ∩ E).card :=
        (selected_neighbor_card (U := E) u.property).symm
      _ = ((hypercube 9).neighborFinset u.val ∩ C).card := congrArg Finset.card neighbors
      _ = _ := (selected_neighbor_card (U := C) (hsub u.property)).trans
        (hr ⟨u.val, hsub u.property⟩)
  let axis := (0 : Fin 4).castAdd 5
  have noEdges : directionEdges E axis = 0 := by
    unfold directionEdges
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨huE, _, hflip⟩ := mem_filter.mp hu
    have hu' : join (pattern 3) (rightBlock u) ∈ C := by
      rw [represent huE]
      exact hsub huE
    apply noLeft _ hu' 0
    rw [represent huE]
    exact hsub hflip
  have hcount := direction_edge_count (d := 3) E hreg (balanced_subset hb hsub) axis
  rw [noEdges, Nat.mul_zero] at hcount
  intro u hu hcode
  have hpos : 0 < E.card := card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, hcode⟩⟩
  omega

#print axioms theta_projection_excludes_three

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
