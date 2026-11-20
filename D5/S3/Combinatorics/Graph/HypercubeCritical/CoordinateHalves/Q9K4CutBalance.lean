/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4CutBalance
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9K4CutBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The integer cut equations and occupancy counts for the ten-point K4 projection. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SmallParitySupport

/-! The centered cut potential for the normalized ten-pattern projection of Q9. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance

open scoped Matrix BigOperators
open Finset
open BalancedCriticalSpectrum (directionEdges direction_edge_count)
open BalancedCriticalSpectrum (Q IsBalanced)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9FourFiberSpectrum (leftProjection fiber_and_signedRow_supported)
open private signedRow_pairing_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint
open Q9ThetaProjection (leftCode)
open private mem_leftProjection from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFiberSpectrum
open private leftCode_join join_blocks rightBlock flipCode flip_pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private direction_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SmallParitySupport
open private tenCodes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence
open BalancedCriticalSpectrum (directionEndpoints)
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open Q9SignedProjection (join fiber signedRow leftParitySign q9_signed_row_split)
open Q9TenPatternIncidence (tenProjection vertexCode midpointCode endpoints incidence potential
  balanced_fibers_incidence_cut midpoint_cut)
open private pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private transpose_mulVec endpoints_cover from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenPatternIncidence

open private flip_join_left flip_join_right sign_join_left from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open BalancedCubeComponentBoundary (directions regular_directions)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

local notation "flip" => BalancedCriticalSpectrum.flip

/-- The four even label functions, with the suffix as their argument. -/
def evenLabel (z : Q 9 → ℤ) (i : Fin 4) (y : Q 5) : ℤ :=
  fiber z y (pattern (vertexCode i))

/-- Four times the centered potential of the midpoint cut. -/
def cScaled (z : Q 9 → ℤ) (i : Fin 4) (y : Q 5) : ℤ :=
  4 * potential (fiber z y) i - ∑ j, potential (fiber z y) j

private theorem incidence_laplacian (v : Fin 4 → ℤ) (i : Fin 4) :
    (incidence *ᵥ (incidence.transpose *ᵥ v)) i = 4 * v i - ∑ j, v j := by
  fin_cases i <;>
    simp [Matrix.mulVec_apply_eq_sum, incidence, endpoints, Fin.sum_univ_succ] <;> ring

private theorem pattern_parities :
    (∀ i, leftParitySign (pattern (vertexCode i)) = 1) ∧
    (∀ e, leftParitySign (pattern (midpointCode e)) = -1) := by
  decide +kernel

private theorem midpoint_scaled {z : Q 9 → ℤ} {y : Q 5} (e : Fin 6)
    (hm : (fun e => fiber z y (pattern (midpointCode e))) =
      incidence.transpose *ᵥ potential (fiber z y)) :
    4 * fiber z y (pattern (midpointCode e)) =
      cScaled z (endpoints e).1 y - cScaled z (endpoints e).2 y := by
  have he := congrFun hm e
  rw [transpose_mulVec] at he
  simp only [cScaled]
  linarith

private theorem signedRow_sub {n : ℕ} (f g : Q n → ℤ) (y : Q n) :
    signedRow (fun x => f x - g x) y = signedRow f y - signedRow g y := by
  simp [signedRow, mul_sub, Finset.sum_sub_distrib]

private theorem signedRow_four_mul {n : ℕ} (f : Q n → ℤ) (y : Q n) :
    signedRow (fun x => 4 * f x) y = 4 * signedRow f y := by
  simp [signedRow, Finset.mul_sum, mul_left_comm]

private theorem signedRow_sum (f : Fin 4 → Q 5 → ℤ) (y : Q 5) :
    signedRow (fun x => ∑ j, f j x) y = ∑ j, signedRow (f j) y := by
  simp only [signedRow, Finset.mul_sum]
  rw [Finset.sum_comm]

open Classical in
/-- The same switching labels give both coupled integer equations on Q5. -/
theorem balanced_coupled_rows {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ u, signedRow z u = 3 * z u) ∧
      (∀ y : Q 5,
        let f := fiber z y
        (∑ i, evenLabel z i y) = 0 ∧
        (fun i => signedRow f (pattern (vertexCode i))) =
          incidence *ᵥ (fun e => f (pattern (midpointCode e))) ∧
        (fun e => signedRow f (pattern (midpointCode e))) =
          incidence.transpose *ᵥ (fun i => evenLabel z i y) ∧
        (fun e => f (pattern (midpointCode e))) = incidence.transpose *ᵥ potential f ∧
        ∃ (level : ℤ) (side : Fin 4 → Bool),
          (∀ i, potential f i = level + if side i then 1 else 0) ∧
          (∀ e, join (pattern (midpointCode e)) y ∈ C ↔
            side (endpoints e).1 ≠ side (endpoints e).2)) ∧
      ∀ i y,
        signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
        signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y := by
  obtain ⟨z, hunit, hzero, hrow, hcut⟩ := balanced_fibers_incidence_cut hreg hb hP
  have hsum (y : Q 5) : ∑ i, evenLabel z i y = 0 := by
    simpa [evenLabel, Fin.sum_univ_succ, add_assoc] using (hcut y).1
  have hcenter (y : Q 5) : ∑ i, cScaled z i y = 0 := by
    simp [cScaled, Fin.sum_univ_succ]
    ring
  refine ⟨z, hunit, hzero, hrow, fun y => ?_, fun i y => ?_⟩
  · obtain ⟨_, he, ho, hm, _, hside⟩ := hcut y
    exact ⟨hsum y, he, ho, hm, hside⟩
  · constructor
    · have h := q9_signed_row_split hrow (pattern (vertexCode i)) y
      have he := congrFun (hcut y).2.1 i
      change _ = (incidence *ᵥ (fun e => fiber z y (pattern (midpointCode e)))) i at he
      rw [(hcut y).2.2.2.1, incidence_laplacian] at he
      simp only [pattern_parities.1, one_mul, he] at h
      change 3 * evenLabel z i y = cScaled z i y + signedRow (evenLabel z i) y at h
      omega
    · let residual (j : Fin 4) := signedRow (cScaled z j) y -
          (4 * evenLabel z j y - 3 * cScaled z j y)
      have hdiff (e : Fin 6) : residual (endpoints e).1 = residual (endpoints e).2 := by
        let mid (x : Q 5) := fiber z x (pattern (midpointCode e))
        have hmid (x : Q 5) : 4 * mid x =
            cScaled z (endpoints e).1 x - cScaled z (endpoints e).2 x :=
          midpoint_scaled e (hcut x).2.2.2.1
        have ho := congrFun (hcut y).2.2.1 e
        change signedRow (fiber z y) (pattern (midpointCode e)) =
          (incidence.transpose *ᵥ (fun i => evenLabel z i y)) e at ho
        rw [transpose_mulVec] at ho
        have hv : 3 * mid y = _ := q9_signed_row_split hrow (pattern (midpointCode e)) y
        simp only [pattern_parities.2, neg_one_mul, ho] at hv
        change 3 * mid y = _ - signedRow mid y at hv
        have hr := congrArg (fun f : Q 5 → ℤ => signedRow f y) (funext hmid)
        rw [signedRow_four_mul, signedRow_sub] at hr
        dsimp [residual]
        linarith [hmid y]
      have hconstant (j : Fin 4) : residual j = residual 0 := by
        by_cases hj : j = 0
        · rw [hj]
        · obtain ⟨e, he | he⟩ := endpoints_cover j 0 hj
          · simpa [he] using hdiff e
          · simpa [he] using (hdiff e).symm
      have hrzero : ∑ j, residual j = 0 := by
        simp only [residual, Finset.sum_sub_distrib, ← signedRow_sum, ← Finset.mul_sum,
          hsum, hcenter, mul_zero, sub_zero]
        simp [signedRow]
      rw [Finset.sum_congr rfl (fun j _ => hconstant j)] at hrzero
      have hz0 : residual 0 = 0 := by
        simp at hrzero
        omega
      have hi := (hconstant i).trans hz0
      dsimp [residual] at hi
      omega

#print axioms balanced_coupled_rows

/-- Integer indicator of an occupied signed label. -/
def occupied (v : ℤ) : ℤ := if v = 0 then 0 else 1

/-- Number of selected even patterns in a suffix fiber. -/
def evenCount (a : Fin 4 → ℤ) : ℤ := ∑ i, occupied (a i)

/-- Number of selected odd patterns in a suffix fiber. -/
def oddCount (z : Q 9 → ℤ) (y : Q 5) : ℤ :=
  ∑ e, occupied (fiber z y (pattern (midpointCode e)))

private def cutPotential (side : Fin 4 → Bool) (i : Fin 4) : ℤ :=
  4 * (if side i then 1 else 0) - ∑ j, (if side j then 1 else 0)

private def crosses (side : Fin 4 → Bool) (e : Fin 6) : ℤ :=
  if side (endpoints e).1 = side (endpoints e).2 then 0 else 1

/-- The zero, singleton and balanced cut types, with all allowed even labels. -/
def LocalType (a c : Fin 4 → ℤ) (odd : ℤ) : Prop :=
  ((∀ i, c i = 0) ∧ odd = 0 ∧ (evenCount a = 0 ∨ evenCount a = 2 ∨ evenCount a = 4)) ∨
  (∃ (i : Fin 4) (sign : Bool), let s : ℤ := if sign then 1 else -1
    odd = 3 ∧
    (∀ j, c j = s * (if j = i then 3 else -1)) ∧
    ((∀ j, a j = 0) ∨ ∃ k : Fin 4, k ≠ i ∧
      ∀ j, a j = s * ((if j = i then 1 else 0) - (if j = k then 1 else 0)))) ∨
  (odd = 4 ∧ (∀ i, c i = 2 ∨ c i = -2) ∧
    (∀ i, a i = 0 ∨ 2 * a i = c i) ∧
    (evenCount a = 0 ∨ evenCount a = 2 ∨ evenCount a = 4))

private def ternary (t : Fin 3) : ℤ := (t.val : ℤ) - 1

private theorem exists_ternary {v : ℤ} (h : v = 0 ∨ v = 1 ∨ v = -1) :
    ∃ t, ternary t = v := by
  rcases h with rfl | rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩

-- The finite table varies the four side bits and the four ternary even labels.
private theorem local_table :
    ∀ (b₀ b₁ b₂ b₃ : Bool) (t₀ t₁ t₂ t₃ : Fin 3),
      let side : Fin 4 → Bool := ![b₀, b₁, b₂, b₃]
      let a : Fin 4 → ℤ := ![ternary t₀, ternary t₁, ternary t₂, ternary t₃]
      let c := cutPotential side
      (∑ i, a i) = 0 →
      (∀ i, a i = 0 ∨ c i = 0 ∨ 0 < a i * c i) →
      LocalType a c (∑ e, crosses side e) := by
  unfold LocalType
  decide +kernel

private theorem local_classification {a : Fin 4 → ℤ} (side : Fin 4 → Bool)
    (hu : ∀ i, a i = 0 ∨ a i = 1 ∨ a i = -1) (hs : ∑ i, a i = 0)
    (hp : ∀ i, a i = 0 ∨ cutPotential side i = 0 ∨ 0 < a i * cutPotential side i) :
    LocalType a (cutPotential side) (∑ e, crosses side e) := by
  obtain ⟨t₀, h₀⟩ := exists_ternary (hu 0)
  obtain ⟨t₁, h₁⟩ := exists_ternary (hu 1)
  obtain ⟨t₂, h₂⟩ := exists_ternary (hu 2)
  obtain ⟨t₃, h₃⟩ := exists_ternary (hu 3)
  have ha : (![ternary t₀, ternary t₁, ternary t₂, ternary t₃] : Fin 4 → ℤ) = a := by
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
  have hb : (![side 0, side 1, side 2, side 3] : Fin 4 → Bool) = side := by
    funext i
    fin_cases i <;> rfl
  have ht := local_table (side 0) (side 1) (side 2) (side 3) t₀ t₁ t₂ t₃
  dsimp only at ht
  rw [ha, hb] at ht
  exact ht hs hp

private theorem label_values {z : Q 9 → ℤ} {C : Finset (Q 9)}
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0) (u : Q 9) :
    z u = 0 ∨ z u = 1 ∨ z u = -1 := by
  by_cases h : u ∈ C
  · exact Or.inr (hu u h)
  · exact Or.inl (hz u h)

private theorem nonzero_iff_mem {z : Q 9 → ℤ} {C : Finset (Q 9)}
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0) (u : Q 9) :
    z u ≠ 0 ↔ u ∈ C := by
  constructor
  · contrapose!
    exact hz u
  · intro h
    rcases hu u h with h' | h' <;> simp [h']

-- Every selected edge saturates its contribution to the signed row.
open Classical in
private theorem selected_term {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u) {u : Q 9} (hm : u ∈ C) (i : Fin 9) :
    z u * (truePrefixSign u i * z (flip u i)) = occupied (z (flip u i)) := by
  classical
  let weight (j : Fin 9) := occupied (z (flip u j))
  let term (j : Fin 9) := z u * (truePrefixSign u j * z (flip u j))
  have hle (j : Fin 9) : term j ≤ weight j := by
    by_cases h : flip u j ∈ C
    · have hsign : truePrefixSign u j = 1 ∨ truePrefixSign u j = -1 := by
        unfold truePrefixSign
        exact neg_one_pow_eq_or _ _
      rcases hu u hm with ha | ha <;> rcases hu _ h with hb | hb <;>
        rcases hsign with hc | hc <;> simp [term, weight, occupied, ha, hb, hc]
    · simp [term, weight, occupied, hz _ h]
  have hw : ∑ j, weight j = 3 := by
    have he (j : Fin 9) : weight j = if j ∈ directions C u then 1 else 0 := by
      by_cases hmj : flip u j ∈ C
      · simp [weight, occupied, mem_directions, hmj, (nonzero_iff_mem hu hz _).mpr hmj]
      · simp [weight, occupied, mem_directions, hmj, hz _ hmj]
    simp only [he, sum_boole]
    rw [show (univ.filter fun j => j ∈ directions C u) = directions C u by ext; simp,
      regular_directions C hreg hm]
    rfl
  have ht : ∑ j, term j = 3 := by
    change (∑ j, z u * (truePrefixSign u j * z (flip u j))) = 3
    rw [← mul_sum]
    change z u * signedRow z u = 3
    rw [hrow]
    rcases hu u hm with ha | ha <;> norm_num [ha]
  apply le_antisymm (hle i)
  by_contra! h
  have hlt := sum_lt_sum (fun j _ => hle j) ⟨i, mem_univ i, h⟩
  rw [ht, hw] at hlt
  exact (lt_irrefl _ hlt).elim

private theorem cutPotential_eq {z : Q 9 → ℤ} {y : Q 5} {level : ℤ}
    {side : Fin 4 → Bool}
    (hl : ∀ i, potential (fiber z y) i = level + if side i then 1 else 0) (i : Fin 4) :
    cScaled z i y = cutPotential side i := by
  simp only [cScaled, hl, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, cutPotential]
  ring

private theorem oddCount_eq {C : Finset (Q 9)} {z : Q 9 → ℤ} {y : Q 5}
    {side : Fin 4 → Bool}
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hc : ∀ e, join (pattern (midpointCode e)) y ∈ C ↔
      side (endpoints e).1 ≠ side (endpoints e).2) :
    oddCount z y = ∑ e, crosses side e := by
  refine sum_congr rfl (fun e _ => ?_)
  by_cases h : side (endpoints e).1 = side (endpoints e).2
  · simp [crosses, h, occupied, fiber, hz _ (fun hmem => (hc e).mp hmem h)]
  · have hn := (nonzero_iff_mem hu hz _).mpr ((hc e).mpr h)
    simp [crosses, h, occupied, fiber, hn]

open Classical in
private theorem even_mul_center {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    {i : Fin 4} {y : Q 5} (ha : evenLabel z i y ≠ 0)
    (he : signedRow (fiber z y) (pattern (vertexCode i)) = cScaled z i y) :
    evenLabel z i y * cScaled z i y =
      ∑ j : Fin 4, occupied (fiber z y (flip (pattern (vertexCode i)) j)) := by
  let x := pattern (vertexCode i)
  have hm : join x y ∈ C := (nonzero_iff_mem hu hz _).mp ha
  rw [← he, signedRow, Finset.mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  have ht := selected_term hreg hu hz hrow hm (j.castAdd 5)
  rw [sign_join_left, flip_join_left] at ht
  exact ht

open Classical in
/-- A single choice of switching realizes the coupled rows and the exact local cut table. -/
theorem balanced_cut_types {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ u, signedRow z u = 3 * z u) ∧
      (∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
        signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y) ∧
      ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y) := by
  obtain ⟨z, hu, hz, hrow, hcut, hcoupled⟩ := balanced_coupled_rows hreg hb hP
  refine ⟨z, hu, hz, hrow, hcoupled, fun y => ?_⟩
  obtain ⟨hs, he, _, hm, level, side, hl, hc⟩ := hcut y
  have hcenter (i : Fin 4) := cutPotential_eq hl i
  rw [oddCount_eq hu hz hc, show (fun i => cScaled z i y) = cutPotential side from funext hcenter]
  refine local_classification side (fun i => label_values hu hz _) hs (fun i => ?_)
  rw [← hcenter]
  by_cases ha : evenLabel z i y = 0
  · exact Or.inl ha
  by_cases hcz : cScaled z i y = 0
  · exact Or.inr (Or.inl hcz)
  have hhor := congrFun he i
  change _ = (incidence *ᵥ (fun e => fiber z y (pattern (midpointCode e)))) i at hhor
  rw [hm, incidence_laplacian] at hhor
  have hn := even_mul_center hreg hu hz hrow ha hhor
  refine Or.inr (Or.inr (lt_of_le_of_ne ?_ (Ne.symm (mul_ne_zero ha hcz))))
  rw [hn]
  exact sum_nonneg (fun j _ => by unfold occupied; split <;> omega)

#print axioms balanced_cut_types

private def projectionCode : Fin 4 ⊕ Fin 6 → BitVec 4 :=
  Sum.elim vertexCode midpointCode

private theorem projectionCode_injective : Function.Injective projectionCode := by
  decide +kernel

private theorem mem_codes (k : BitVec 4) : k ∈ tenCodes ↔ ∃ j, projectionCode j = k := by
  revert k
  decide +kernel

private theorem code_of_mem {C : Finset (Q 9)} (hP : leftProjection C = tenProjection)
    {u : Q 9} (hu : u ∈ C) : leftCode u ∈ tenCodes := by
  have hmem : pattern (leftCode u) ∈ leftProjection C :=
    mem_leftProjection.mpr ⟨rightBlock u, by rw [join_blocks]; exact hu⟩
  rw [hP] at hmem
  exact (Finset.mem_map' (cubeBitVec 4).toEmbedding).mp hmem

private def point (y : Q 5) (j : Fin 4 ⊕ Fin 6) : Q 9 :=
  join (pattern (projectionCode j)) y

private theorem leftCode_point (y : Q 5) (j : Fin 4 ⊕ Fin 6) :
    leftCode (point y j) = projectionCode j :=
  leftCode_join _ _

open Classical in
private theorem sum_support {C : Finset (Q 9)} (hP : leftProjection C = tenProjection)
    (g : Q 9 → ℤ) :
    (∑ y : Q 5, ∑ j : Fin 4 ⊕ Fin 6, if point y j ∈ C then g (point y j) else 0) =
      ∑ u ∈ C, g u := by
  rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
  refine Finset.sum_bij (fun p _ => point p.1 p.2) ?_ ?_ ?_ ?_
  · intro p hp
    exact (mem_filter.mp hp).2
  · rintro ⟨y, j⟩ _ ⟨y', j'⟩ _ he
    apply Prod.ext
    · exact funext fun t => by simpa [point, join] using congrFun he (t.natAdd 4)
    · apply projectionCode_injective
      simpa only [leftCode_point] using congrArg leftCode he
  · intro u hu
    obtain ⟨j, hj⟩ := (mem_codes _).mp (code_of_mem hP hu)
    have h : point (rightBlock u) j = u := by
      simpa [point, hj] using join_blocks u
    exact ⟨(rightBlock u, j), mem_filter.mpr ⟨mem_univ _, by simpa only [h] using hu⟩, h⟩
  · intros
    rfl

private def isEvenCode (k : BitVec 4) : Prop := k ∈ univ.image vertexCode

private instance (k : BitVec 4) : Decidable (isEvenCode k) := by
  unfold isEvenCode
  infer_instance

private theorem even_odd_codes :
    (∀ i, isEvenCode (vertexCode i)) ∧ (∀ e, ¬isEvenCode (midpointCode e)) := by
  decide +kernel

private theorem isEven_flip_code :
    ∀ (k : BitVec 4) (j : Fin 4), k ∈ tenCodes → flipCode k j ∈ tenCodes →
      (isEvenCode (flipCode k j) ↔ ¬isEvenCode k) := by
  decide +kernel

private theorem leftCode_flip (u : Q 9) (j : Fin 4) :
    leftCode (flip u (j.castAdd 5)) = flipCode (leftCode u) j := by
  conv_lhs => rw [← join_blocks u, flip_join_left, flip_pattern, leftCode_join]

open Classical in
private theorem even_endpoints_card {C : Finset (Q 9)} (hP : leftProjection C = tenProjection)
    (j : Fin 4) :
    ((directionEndpoints C (j.castAdd 5)).filter (fun u => isEvenCode (leftCode u))).card =
      directionEdges C (j.castAdd 5) := by
  let axis := j.castAdd 5
  let E := directionEndpoints C axis
  let even (u : Q 9) := isEvenCode (leftCode u)
  have flipE (u : Q 9) (hu : u ∈ E) : flip u axis ∈ E := by
    simp only [E, directionEndpoints, mem_filter] at hu ⊢
    exact ⟨hu.2, by simpa using hu.1⟩
  have flipEven (u : Q 9) (hu : u ∈ E) : even (flip u axis) ↔ ¬even u := by
    have ha := mem_filter.mp hu
    simpa only [even, axis, leftCode_flip] using
      isEven_flip_code (leftCode u) j (code_of_mem hP ha.1)
        (by rw [← leftCode_flip]; exact code_of_mem hP ha.2)
  have hcard : (E.filter even).card = (E.filter fun u => ¬even u).card := by
    apply card_bij (fun u _ => flip u axis)
    · intro u hu
      exact mem_filter.mpr ⟨flipE u (mem_filter.mp hu).1,
        fun hf => (flipEven u (mem_filter.mp hu).1).mp hf (mem_filter.mp hu).2⟩
    · intro u _ v _ huv
      simpa using congrArg (fun x => flip x axis) huv
    · intro v hv
      exact ⟨flip v axis, mem_filter.mpr ⟨flipE v (mem_filter.mp hv).1,
        (flipEven v (mem_filter.mp hv).1).mpr (mem_filter.mp hv).2⟩,
        BalancedCriticalSpectrum.flip_flip v axis⟩
  have hadd := Finset.card_filter_add_card_filter_not (s := E) even
  rw [show E.card = 2 * directionEdges C axis from endpoint_card_twice C axis] at hadd
  change (E.filter even).card = directionEdges C axis
  omega

/-- The star of an even label contains that vertex and its three incident midpoints. -/
def starCount (z : Q 9 → ℤ) (i : Fin 4) (y : Q 5) : ℤ :=
  occupied (evenLabel z i y) +
    ∑ e, if i = (endpoints e).1 ∨ i = (endpoints e).2 then
      occupied (fiber z y (pattern (midpointCode e))) else 0

/-- The horizontal coordinate whose half is the given K4 star. -/
def starAxis : Fin 4 → Fin 4 := ![3, 0, 1, 2]

private theorem star_half_table :
    (∀ (i k : Fin 4), (pattern (vertexCode k) (starAxis i) = decide (i ≠ 0)) ↔ i = k) ∧
    (∀ (i : Fin 4) (e : Fin 6),
      (pattern (midpointCode e) (starAxis i) = decide (i ≠ 0)) ↔
        i = (endpoints e).1 ∨ i = (endpoints e).2) := by
  decide +kernel

open Classical in
private theorem occupied_eq_indicator {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0) (u : Q 9) :
    occupied (z u) = if u ∈ C then 1 else 0 := by
  by_cases h : u ∈ C
  · simp [occupied, h, (nonzero_iff_mem hu hz _).mpr h]
  · simp [occupied, h, hz u h]

open Classical in
private theorem star_count_eq_half {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0) (i : Fin 4) :
    (∑ y, starCount z i y) = (C.filter (fun u => u ((starAxis i).castAdd 5) =
      decide (i ≠ 0))).card := by
  let mark (u : Q 9) : ℤ := if u ((starAxis i).castAdd 5) = decide (i ≠ 0) then 1 else 0
  rw [← sum_boole (R := ℤ)]
  change _ = ∑ u ∈ C, mark u
  rw [← sum_support hP mark]
  refine sum_congr rfl (fun y _ => ?_)
  rw [Fintype.sum_sum_type]
  simp only [point, projectionCode, Sum.elim_inl, Sum.elim_inr, mark, join, Fin.append_left,
    star_half_table.1, star_half_table.2]
  unfold starCount
  simp only [evenLabel, fiber, occupied_eq_indicator hu hz, join]
  congr 1
  · symm
    calc
      _ = (if Fin.append (pattern (vertexCode i)) y ∈ C then
        (if i = i then (1 : ℤ) else 0) else 0) := by
          apply Finset.sum_eq_single i
          · intro k _ hki
            simp [Ne.symm hki]
          · simp
      _ = _ := by simp
  · refine sum_congr rfl (fun e _ => ?_)
    split <;> split <;> simp_all

open Classical in
private theorem total_occupation {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0) :
    (∑ y, evenCount (fun i => evenLabel z i y)) + (∑ y, oddCount z y) =
      (C.card : ℤ) := by
  rw [← sum_add_distrib]
  calc
    _ = ∑ u ∈ C, (1 : ℤ) := by
      rw [← sum_support hP (fun _ => 1)]
      refine sum_congr rfl (fun y _ => ?_)
      simp only [Fintype.sum_sum_type, point, projectionCode, Sum.elim_inl, Sum.elim_inr,
        evenCount, oddCount, evenLabel, fiber, occupied_eq_indicator hu hz]
      congr 1
    _ = _ := by simp

private theorem sum_stars (z : Q 9 → ℤ) (y : Q 5) :
    (∑ i, starCount z i y) = evenCount (fun i => evenLabel z i y) + 2 * oddCount z y := by
  simp only [starCount, Finset.sum_add_distrib, evenCount, oddCount, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun e _ => ?_)
  generalize fiber z y (pattern (midpointCode e)) = k
  fin_cases e <;> simp [endpoints, Fin.sum_univ_succ] <;> ring

open Classical in
private theorem horizontal_endpoint_sum {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0) (j : Fin 4) :
    (∑ y, ∑ i,
      occupied (evenLabel z i y) *
        occupied (fiber z y (flip (pattern (vertexCode i)) j))) =
      (directionEdges C (j.castAdd 5) : ℤ) := by
  let axis := j.castAdd 5
  let g (u : Q 9) : ℤ :=
    if isEvenCode (leftCode u) ∧ flip u axis ∈ C then 1 else 0
  calc
    _ = ∑ u ∈ C, g u := by
      rw [← sum_support hP g]
      refine sum_congr rfl (fun y _ => ?_)
      rw [Fintype.sum_sum_type]
      simp only [g, leftCode_point, projectionCode, Sum.elim_inl, Sum.elim_inr,
        even_odd_codes.1, even_odd_codes.2, true_and, false_and, ite_false, ite_self,
        sum_const_zero, add_zero]
      refine sum_congr rfl (fun i _ => ?_)
      simp only [point, projectionCode, Sum.elim_inl, evenLabel, fiber,
        occupied_eq_indicator hu hz, axis, ← flip_join_left]
      split <;> split <;> simp_all
    _ = _ := by
      rw [sum_boole, ← even_endpoints_card hP j]
      apply congrArg (fun S : Finset (Q 9) => (S.card : ℤ))
      ext u
      simp [directionEndpoints, axis, and_left_comm, and_comm]

open Classical in
private theorem horizontal_total {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (ha : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y) :
    (∑ y, ∑ i, evenLabel z i y * cScaled z i y) =
      ∑ j : Fin 4, (directionEdges C (j.castAdd 5) : ℤ) := by
  calc
    _ = ∑ y, ∑ i, ∑ j : Fin 4,
      occupied (evenLabel z i y) *
        occupied (fiber z y (flip (pattern (vertexCode i)) j)) := by
      refine sum_congr rfl (fun y _ => sum_congr rfl (fun i _ => ?_))
      by_cases ha0 : evenLabel z i y = 0
      · simp [ha0, occupied]
      · have hr := q9_signed_row_split hrow (pattern (vertexCode i)) y
        simp only [pattern_parities.1, one_mul] at hr
        change 3 * evenLabel z i y =
          signedRow (fiber z y) (pattern (vertexCode i)) + signedRow (evenLabel z i) y at hr
        rw [ha] at hr
        have hh : signedRow (fiber z y) (pattern (vertexCode i)) = cScaled z i y := by omega
        simpa only [occupied, ite_eq_right ha0, one_mul] using
          even_mul_center hreg hu hz hrow ha0 hh
    _ = ∑ y, ∑ j : Fin 4, ∑ i,
        occupied (evenLabel z i y) *
          occupied (fiber z y (flip (pattern (vertexCode i)) j)) := by
      exact sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := by
      rw [Finset.sum_comm]
      exact sum_congr rfl (fun j _ => horizontal_endpoint_sum hP hu hz j)

private theorem local_pairing {a c : Fin 4 → ℤ} {odd : ℤ}
    (ht : LocalType a c odd) :
    (∑ i, a i * c i) = if odd = 0 then 0 else 2 * evenCount a := by
  rcases ht with ⟨hc, rfl, _⟩ | ⟨i, sign, rfl, hc, ha⟩ | ⟨rfl, hc, ha, _⟩
  · simp [hc]
  · rcases ha with ha | ⟨k, hk, ha⟩
    · simp [ha, occupied, evenCount]
    · cases sign <;> fin_cases i <;> fin_cases k <;>
        simp only [evenCount, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero] <;>
        simp_all [occupied]
  · norm_num
    rw [evenCount, Finset.mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rcases ha i with h | h
    · simp [h, occupied]
    · rcases hc i with hc | hc
      all_goals
        have ha0 : a i ≠ 0 := by omega
        simp [occupied, ha0, hc]
        omega

open Classical in
/-- At order 72 the four star halves are tight, and the 24 even points and
48 odd points lie entirely in nonzero cut fibers. -/
theorem balanced_occupation_split {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hhalves : ∀ i, 30 ≤ (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ u, signedRow z u = 3 * z u) ∧
      (∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
        signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y) ∧
      (∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y)) ∧
      (∑ y, evenCount (fun i => evenLabel z i y)) = 24 ∧
      (∑ y, oddCount z y) = 48 ∧
      (∀ i, (∑ y, starCount z i y) = 30) ∧
      ∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0 := by
  obtain ⟨z, hu, hz, hrow, hcoupled, hlocal⟩ := balanced_cut_types hreg hb hP
  let A (y : Q 5) := evenCount (fun i => evenLabel z i y)
  let O := oddCount z
  let A₀ (y : Q 5) := if O y = 0 then A y else 0
  let H (i : Fin 4) := ∑ y, starCount z i y
  have hnonneg (y : Q 5) : 0 ≤ A₀ y := by
    have hA : 0 ≤ A y := sum_nonneg (fun i _ => by unfold occupied; split <;> omega)
    by_cases h : O y = 0 <;> simp [A₀, h, hA]
  have hhalf (i : Fin 4) : 30 ≤ H i := by
    rw [show H i = _ from star_count_eq_half hP hu hz i]
    exact_mod_cast hhalves i
  have htot := total_occupation hP hu hz
  rw [hsize] at htot
  change (∑ y, A y) + (∑ y, O y) = 72 at htot
  have hstars : (∑ i, H i) = (∑ y, A y) + 2 * (∑ y, O y) := by
    rw [show (∑ i, H i) = ∑ y, ∑ i, starCount z i y from Finset.sum_comm]
    simp [sum_stars, A, O, sum_add_distrib, mul_sum]
  have hedges := horizontal_total hreg hP hu hz hrow (fun i y => (hcoupled i y).1)
  have h12 (j : Fin 4) : directionEdges C (j.castAdd 5) = 12 := by
    have h := direction_edge_count (d := 3) C hreg hb (j.castAdd 5)
    omega
  simp only [h12, Nat.cast_ofNat, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hedges
  simp only [local_pairing (hlocal _)] at hedges
  have he (y : Q 5) : (if O y = 0 then 0 else 2 * A y) = 2 * A y - 2 * A₀ y := by
    by_cases h : O y = 0 <;> simp [A₀, h]
  change (∑ y, if O y = 0 then 0 else 2 * A y) = _ at hedges
  simp_rw [he, sum_sub_distrib, ← mul_sum] at hedges
  have h120 : 120 ≤ ∑ i, H i := by
    have h := sum_le_sum (s := (univ : Finset (Fin 4))) (fun i _ => hhalf i)
    norm_num at h
    exact h
  have hn : 0 ≤ ∑ y, A₀ y := sum_nonneg (fun y _ => hnonneg y)
  have hzero : ∑ y, A₀ y = 0 := by omega
  have h24 : (∑ y, A y) = 24 := by omega
  have h48 : (∑ y, O y) = 48 := by omega
  refine ⟨z, hu, hz, hrow, hcoupled, hlocal, h24, h48, fun i => ?_, fun y hy i => ?_⟩
  · have hsum : ∑ i, (H i - 30) = 0 := by
      simp [Finset.sum_sub_distrib]
      omega
    have hle := single_le_sum (f := fun i => H i - 30)
      (fun j _ => by have := hhalf j; omega) (mem_univ i)
    change H i - 30 ≤ ∑ j, (H j - 30) at hle
    rw [hsum] at hle
    change H i = 30
    exact le_antisymm (by omega) (hhalf i)
  · have hy0 := single_le_sum (f := A₀) (fun y _ => hnonneg y) (mem_univ y)
    rw [hzero] at hy0
    change O y = 0 at hy
    simp only [A₀, hy, ite_true] at hy0
    have hi := single_le_sum (f := fun i => occupied (evenLabel z i y))
      (fun i _ => by unfold occupied; split <;> omega) (mem_univ i)
    change occupied (evenLabel z i y) ≤ A y at hi
    by_contra h
    simp [occupied, h] at hi
    omega

#print axioms balanced_occupation_split

/-- The binary indicator of a singleton cut. -/
def singletonIndicator (z : Q 9 → ℤ) (y : Q 5) : ZMod 2 :=
  if oddCount z y = 3 then 1 else 0

private theorem center_mod_two {z : Q 9 → ℤ} {y : Q 5}
    (ht : LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (i : Fin 4) : (cScaled z i y : ZMod 2) = singletonIndicator z y := by
  rcases ht with ⟨hc, ho, _⟩ | ⟨j, sign, ho, hc, _⟩ | ⟨ho, hc, _⟩
  · simp [singletonIndicator, hc, ho]
  · have he : cScaled z i y = _ := hc i
    rw [he, singletonIndicator, ho]
    cases sign <;> by_cases hij : i = j <;>
      simp only [hij, Bool.false_eq_true, ite_false, ite_true] <;> decide
  · rcases hc i with h | h <;> simp only [singletonIndicator, ho, h] <;> decide

private theorem cast_signedRow (f : Q 5 → ℤ) (y : Q 5) :
    (signedRow f y : ZMod 2) = ∑ j : Fin 5, (f (flip y j) : ZMod 2) := by
  simp only [signedRow, Int.cast_sum, Int.cast_mul]
  refine sum_congr rfl (fun j _ => ?_)
  have h : (truePrefixSign y j : ZMod 2) = 1 := by
    unfold truePrefixSign
    push_cast
    rw [show (-1 : ZMod 2) = 1 by decide, one_pow]
  rw [h, one_mul]

/-- Modulo two, the two coupled equations give the singleton row and its
adjacency fixed-point equation. -/
theorem singleton_parity_rows {z : Q 9 → ℤ}
    (hunit : ∀ i y, evenLabel z i y = 0 ∨ evenLabel z i y = 1 ∨ evenLabel z i y = -1)
    (hrow : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
      signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y)) :
    (∀ i y, (∑ j : Fin 5, (occupied (evenLabel z i (flip y j)) : ZMod 2)) +
      (occupied (evenLabel z i y) : ZMod 2) = singletonIndicator z y) ∧
    ∀ y, (∑ j : Fin 5, singletonIndicator z (flip y j)) = singletonIndicator z y := by
  have hcast (i : Fin 4) (y : Q 5) :
      (evenLabel z i y : ZMod 2) = (occupied (evenLabel z i y) : ZMod 2) := by
    rcases hunit i y with h | h | h <;> simp only [h, occupied] <;> decide
  have three : (3 : ZMod 2) = 1 := by decide
  have four : (4 : ZMod 2) = 0 := by decide
  have neg (v : ZMod 2) : -v = v := ZModModule.neg_eq_self v
  constructor
  · intro i y
    have h := congrArg (fun v : ℤ => (v : ZMod 2)) (hrow i y).1
    change (signedRow (evenLabel z i) y : ZMod 2) =
      ((3 * evenLabel z i y - cScaled z i y : ℤ) : ZMod 2) at h
    simp only [cast_signedRow, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, three, one_mul,
      center_mod_two (hlocal _), hcast] at h
    rw [sub_eq_add_neg, neg] at h
    rw [h, add_right_comm]
    let a := (occupied (evenLabel z i y) : ZMod 2)
    have twice : a + a = 0 := (congrArg (fun v => v + a) (neg a).symm).trans (neg_add_cancel a)
    rw [show (a + a) + singletonIndicator z y = _ from by rw [twice, zero_add]]
  · intro y
    have h := congrArg (fun v : ℤ => (v : ZMod 2)) (hrow 0 y).2
    simpa only [cast_signedRow, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, three, four, one_mul,
      zero_mul, center_mod_two (hlocal _), zero_sub, neg] using h

#print axioms singleton_parity_rows

private def countIf (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- Number of suffix fibers with singleton cuts. -/
def singletons (z : Q 9 → ℤ) : ℤ := ∑ y, countIf (oddCount z y = 3)

/-- Number of suffix fibers with balanced cuts. -/
def balancedCuts (z : Q 9 → ℤ) : ℤ := ∑ y, countIf (oddCount z y = 4)

/-- Number of singleton cuts centered at the given even label. -/
def singletonCenters (z : Q 9 → ℤ) (i : Fin 4) : ℤ := ∑ y, countIf (|cScaled z i y| = 3)

/-- Number of selected occurrences of the given even label. -/
def labelCount (z : Q 9 → ℤ) (i : Fin 4) : ℤ := ∑ y, occupied (evenLabel z i y)

/-- Number of selected occurrences of the even label as a singleton center. -/
def activeCenters (z : Q 9 → ℤ) (i : Fin 4) : ℤ :=
  ∑ y, occupied (evenLabel z i y) * countIf (|cScaled z i y| = 3)

/-- Number of selected occurrences of the even label as a singleton partner. -/
def activePartners (z : Q 9 → ℤ) (i : Fin 4) : ℤ :=
  ∑ y, occupied (evenLabel z i y) * countIf (oddCount z y = 3 ∧ |cScaled z i y| ≠ 3)

/-- Number of selected occurrences of the even label in balanced cuts. -/
def activeBalanced (z : Q 9 → ℤ) (i : Fin 4) : ℤ :=
  ∑ y, occupied (evenLabel z i y) * countIf (oddCount z y = 4)

private def incidentCount (side : Fin 4 → Bool) (i : Fin 4) : ℤ :=
  ∑ e, if i = (endpoints e).1 ∨ i = (endpoints e).2 then crosses side e else 0

private theorem cut_moment_table :
    ∀ (b₀ b₁ b₂ b₃ : Bool) (i : Fin 4),
      let side : Fin 4 → Bool := ![b₀, b₁, b₂, b₃]
      let c := cutPotential side i
      let o := ∑ e, crosses side e
      let r := incidentCount side i
      2 * r = o - countIf (o = 3) + 4 * countIf (|c| = 3) ∧
      4 * r - c ^ 2 = o := by
  decide +kernel

open Classical in
private theorem star_moments {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u) (i : Fin 4) (y : Q 5) :
    let r := starCount z i y - occupied (evenLabel z i y)
    let c := cScaled z i y
    let o := oddCount z y
    2 * r = o - countIf (o = 3) + 4 * countIf (|c| = 3) ∧
    4 * r - c ^ 2 = o := by
  dsimp only
  have hs (x : Q 4) (hx : x ∉ tenProjection) :=
    fiber_and_signedRow_supported hz hrow y (hP.symm ▸ hx)
  obtain ⟨_, _, lev, side, hl, hc⟩ := midpoint_cut
    (fun x hx => (hs x hx).1) (fun x hx => (hs x hx).2)
    (fun e => by
      rcases label_values hu hz (join (pattern (midpointCode e)) y) with h | h | h <;>
        change |z _| ≤ 1 <;> simp [h])
  have hm (e : Fin 6) : occupied (fiber z y (pattern (midpointCode e))) = crosses side e := by
    by_cases he : side (endpoints e).1 = side (endpoints e).2
    · have hzero : fiber z y (pattern (midpointCode e)) = 0 :=
        not_not.mp (fun hm => (hc e).mp hm he)
      simp [occupied, crosses, he, hzero]
    · simp [occupied, crosses, he, (hc e).mpr he]
  have hr : starCount z i y - occupied (evenLabel z i y) = incidentCount side i := by
    simp [starCount, incidentCount, hm]
  simp only [hr, cutPotential_eq hl, oddCount, hm]
  have hv : (![side 0, side 1, side 2, side 3] : Fin 4 → Bool) = side := by
    funext j
    fin_cases j <;> rfl
  have h := cut_moment_table (side 0) (side 1) (side 2) (side 3) i
  dsimp only at h
  rwa [hv] at h

private theorem pairing_identity (a c : Q 5 → ℤ)
    (ha : ∀ y, signedRow a y = 3 * a y - c y)
    (hc : ∀ y, signedRow c y = 4 * a y - 3 * c y) :
    6 * (∑ y, a y * c y) = 4 * (∑ y, a y ^ 2) + ∑ y, c y ^ 2 := by
  have left (y : Q 5) : (3 * a y - c y) * c y = 3 * (a y * c y) - c y ^ 2 := by ring
  have right (y : Q 5) : a y * (4 * a y - 3 * c y) = 4 * a y ^ 2 - 3 * (a y * c y) := by ring
  have h := signedRow_pairing_symmetric a c
  simp only [ha, hc, left, right, sum_sub_distrib, ← mul_sum] at h
  omega

private theorem label_contributions {z : Q 9 → ℤ} {i : Fin 4} {y : Q 5}
    (ht : LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hempty : oddCount z y = 0 → evenLabel z i y = 0) :
    let a := evenLabel z i y
    let c := cScaled z i y
    let o := oddCount z y
    let m := occupied a * countIf (|c| = 3)
    let l := occupied a * countIf (o = 3 ∧ |c| ≠ 3)
    let p := occupied a * countIf (o = 4)
    3 * countIf (o = 3) + 4 * countIf (o = 4) = o ∧
    occupied a = m + l + p ∧ a * c = 3 * m + l + 2 * p := by
  dsimp only
  rcases ht with ⟨hc, ho, _⟩ | ⟨j, sign, ho, hc, ha⟩ | ⟨ho, hc, ha, _⟩
  · simp [ho, show cScaled z i y = 0 from hc i, hempty ho, countIf, occupied]
  · have hci : cScaled z i y = _ := hc i
    rw [ho, hci]
    rcases ha with ha | ⟨k, hk, ha⟩
    · have hai : evenLabel z i y = 0 := ha i
      rw [hai]
      cases sign <;> by_cases hij : i = j <;> norm_num [hij, countIf, occupied]
    · have hai : evenLabel z i y = _ := ha i
      cases sign <;> by_cases hij : i = j <;> by_cases hik : i = k <;>
        simp_all [countIf, occupied]
  · have hci : cScaled z i y = 2 ∨ cScaled z i y = -2 := hc i
    have hai : evenLabel z i y = 0 ∨ 2 * evenLabel z i y = cScaled z i y := ha i
    rcases hci with hci | hci <;> rcases hai with hai | hai
    · norm_num [ho, hci, hai, countIf, occupied]
    · have ha' : evenLabel z i y = 1 := by omega
      norm_num [ho, hci, ha', countIf, occupied]
    · norm_num [ho, hci, hai, countIf, occupied]
    · have ha' : evenLabel z i y = -1 := by omega
      norm_num [ho, hci, ha', countIf, occupied]


/-- Suffix degree of a particular even pattern, evaluated as a sum of indicators. -/
def evenVerticalDegree (z : Q 9 → ℤ) (i : Fin 4) (y : Q 5) : ℤ :=
  ∑ j : Fin 5, occupied (evenLabel z i (flip y j))

open Classical in
private theorem even_degree {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (ha : ∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y)
    (i : Fin 4) (y : Q 5) (hsel : evenLabel z i y ≠ 0) :
    evenVerticalDegree z i y = 3 - evenLabel z i y * cScaled z i y := by
  let u := join (pattern (vertexCode i)) y
  have hm : u ∈ C := (nonzero_iff_mem hu hz _).mp hsel
  have hg : (∑ j : Fin 9, occupied (z (flip u j))) = 3 := by
    simp only [occupied_eq_indicator hu hz, sum_boole]
    change (↑(directions C u).card : ℤ) = 3
    rw [regular_directions C hreg hm]
    rfl
  rw [Fin.sum_univ_add (a := 4) (b := 5)] at hg
  simp only [u, flip_join_left, flip_join_right] at hg
  have hr := q9_signed_row_split hrow (pattern (vertexCode i)) y
  simp only [pattern_parities.1, one_mul] at hr
  change 3 * evenLabel z i y =
    signedRow (fiber z y) (pattern (vertexCode i)) + signedRow (evenLabel z i) y at hr
  rw [ha] at hr
  have hh : signedRow (fiber z y) (pattern (vertexCode i)) = cScaled z i y := by omega
  have hp := even_mul_center hreg hu hz hrow hsel hh
  change (∑ j : Fin 4, occupied (fiber z y (flip (pattern (vertexCode i)) j))) +
    evenVerticalDegree z i y = 3 at hg
  omega

private def starEdges (i : Fin 4) : Finset (Fin 6) :=
  univ.filter (fun e => i = (endpoints e).1 ∨ i = (endpoints e).2)

private theorem starEdges_card : ∀ i, (starEdges i).card = 3 := by
  decide +kernel

private theorem incident_direction :
    ∀ (i : Fin 4) (e : Fin 6), e ∈ starEdges i →
      ∃ d : Fin 4, flip (pattern (vertexCode i)) d = pattern (midpointCode e) := by
  decide +kernel

open Classical in
private theorem balanced_neighbors_disjoint {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (i : Fin 4) (y : Q 5) (d : Fin 5) (hy : oddCount z y = 4)
    (hy' : oddCount z (flip y d) = 4) (hai : evenLabel z i y ≠ 0) :
    evenLabel z i (flip y d) = 0 := by
  by_contra ha
  let P (v : Q 5) := (starEdges i).filter fun e => join (pattern (midpointCode e)) v ∈ C
  have hcard (v : Q 5) (hv : oddCount z v = 4) : (P v).card = 2 := by
    have hc : cScaled z i v = 2 ∨ cScaled z i v = -2 := by
      rcases hlocal v with ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, hc, _⟩
      · omega
      · omega
      · exact hc i
    have hr := (star_moments hP hu hz hrow i v).2
    have hcount : starCount z i v - occupied (evenLabel z i v) = ((P v).card : ℤ) := by
      rw [starCount, add_sub_cancel_left, ← sum_boole (R := ℤ), ← sum_filter]
      exact sum_congr rfl (fun e _ => occupied_eq_indicator hu hz _)
    rw [hcount, hv] at hr
    rcases hc with hc | hc <;> rw [hc] at hr <;> norm_num at hr <;> omega
  have hU : P y ∪ P (flip y d) ⊆ starEdges i :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have hbound := card_le_card hU
  have hint := card_union_add_card_inter (P y) (P (flip y d))
  rw [hcard y hy, hcard (flip y d) hy'] at hint
  rw [starEdges_card] at hbound
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < (P y ∩ P (flip y d)).card by omega)
  obtain ⟨he₁, he₂⟩ := mem_inter.mp he
  have hspoke := (mem_filter.mp he₁).1
  obtain ⟨j, hj⟩ := incident_direction i e hspoke
  have hne : j.castAdd 5 ≠ d.natAdd 4 := by
    intro heq
    have hval := congrArg Fin.val heq
    have hbnd := j.isLt
    change j.val = 4 + d.val at hval
    omega
  have hm := (nonzero_iff_mem hu hz _).mp hai
  refine BalancedCubeGirth.no_selected_square hb hne hm ?_ ?_ ?_
  · rw [flip_join_left, hj]
    exact (mem_filter.mp he₁).2
  · rw [flip_join_right]
    exact (nonzero_iff_mem hu hz _).mp ha
  · rw [flip_join_left, hj, flip_join_right]
    exact (mem_filter.mp he₂).2

private theorem evenCount_eq_four_imp {a : Fin 4 → ℤ} (h : evenCount a = 4)
    (i : Fin 4) : a i ≠ 0 := by
  have hsum : ∑ k, (1 - occupied (a k)) = (0 : ℤ) := by
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat, mul_one]
    change 4 - evenCount a = 0
    rw [h, sub_self]
  have hi := single_le_sum (f := fun k => 1 - occupied (a k))
    (fun k _ => by unfold occupied; split <;> omega) (mem_univ i)
  change 1 - occupied (a i) ≤ ∑ k, (1 - occupied (a k)) at hi
  rw [hsum] at hi
  intro hzero
  simp [occupied, hzero] at hi

private theorem active_singleton_count {a : Fin 4 → ℤ} {i k : Fin 4} (sign : Bool)
    (hk : k ≠ i)
    (ha : ∀ j, a j = (if sign then (1 : ℤ) else -1) *
      ((if j = i then 1 else 0) - (if j = k then 1 else 0))) :
    evenCount a = 2 := by
  cases sign <;> fin_cases i <;> fin_cases k <;>
    simp only [evenCount, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero] <;>
    simp_all [occupied]

open Classical in
/-- All fibers with selected even patterns contain exactly two of them.
Selected even suffix edges cannot join two balanced cuts. -/
theorem balanced_active_fibers {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hhalves : ∀ i, 30 ≤ (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ i y, evenLabel z i y ≠ 0 →
        evenVerticalDegree z i y = 3 - evenLabel z i y * cScaled z i y) ∧
      (∀ i y d, oddCount z y = 4 → oddCount z (flip y d) = 4 →
        evenLabel z i y ≠ 0 → evenLabel z i (flip y d) = 0) ∧
      (∀ y, evenCount (fun i => evenLabel z i y) = 0 ∨
        evenCount (fun i => evenLabel z i y) = 2) ∧
      (∑ y, countIf (evenCount (fun i => evenLabel z i y) ≠ 0)) = 12 := by
  obtain ⟨z, hu, hz, hrow, hcoupled, hlocal, h24, _, _, hzero⟩ :=
    balanced_occupation_split hsize hreg hb hP hhalves
  have hdeg := even_degree hreg hu hz hrow (fun i y => (hcoupled i y).1)
  have hdisj := balanced_neighbors_disjoint hb hP hu hz hrow hlocal
  have htwo (y : Q 5) : evenCount (fun i => evenLabel z i y) = 0 ∨
      evenCount (fun i => evenLabel z i y) = 2 := by
    rcases hlocal y with ⟨_, ho, _⟩ | ⟨i, sign, _, _, ha | ⟨k, hk, ha⟩⟩ |
      ⟨ho, _, hs, hcard | hcard | hcard⟩
    · exact Or.inl (by simp [evenCount, occupied, hzero y ho])
    · exact Or.inl (by simp [evenCount, occupied, show ∀ j, evenLabel z j y = 0 from ha])
    · exact Or.inr (active_singleton_count sign hk ha)
    · exact Or.inl hcard
    · exact Or.inr hcard
    · have hsel (i : Fin 4) : evenLabel z i y ≠ 0 := evenCount_eq_four_imp hcard i
      have hp : evenLabel z 0 y * cScaled z 0 y = 2 := by
        have h := (label_contributions (i := 0) (hlocal y) (fun h => hzero y h 0)).2.2
        have hc : cScaled z 0 y = 2 ∨ cScaled z 0 y = -2 := by
          rcases hlocal y with ⟨_, hz, _⟩ | ⟨_, _, hz, _⟩ | ⟨_, hc, _⟩
          · omega
          · omega
          · exact hc 0
        rcases hc with hc | hc <;> norm_num [ho, hc, countIf, occupied, hsel 0] at h ⊢ <;>
          exact h
      have hd := hdeg 0 y (hsel 0)
      rw [hp] at hd
      obtain ⟨d, hdne⟩ : ∃ d, evenLabel z 0 (flip y d) ≠ 0 := by
        by_contra! he
        simp [evenVerticalDegree, occupied, he] at hd
      let v := flip y d
      rcases hlocal v with ⟨_, hv, _⟩ | ⟨j, sign, _, hc, ha | ⟨k, hk, ha⟩⟩ | ⟨hv, _⟩
      · exact (hdne (hzero v hv 0)).elim
      · exact (hdne (ha 0)).elim
      · have hac : evenLabel z j v = (if sign then 1 else -1) := by
          have h := ha j
          simpa [Ne.symm hk] using h
        have hcp : cScaled z j v = (if sign then (1 : ℤ) else -1) * 3 := by
          simpa using hc j
        have hj : evenLabel z j v ≠ 0 := by cases sign <;> norm_num [hac]
        have hvdeg := hdeg j v hj
        have hterm : occupied (evenLabel z j (flip v d)) ≤ evenVerticalDegree z j v :=
          single_le_sum (f := fun t => occupied (evenLabel z j (flip v t)))
            (fun _ _ => by unfold occupied; split <;> omega) (mem_univ d)
        have hback : flip v d = y := BalancedCriticalSpectrum.flip_flip y d
        rw [hback] at hterm
        cases sign <;> norm_num [hac, hcp] at hvdeg <;>
          simp [occupied, hsel j, hvdeg] at hterm
      · exact (hdne (hdisj 0 y d ho hv (hsel 0))).elim
  refine ⟨z, hu, hz, hdeg, hdisj, htwo, ?_⟩
  have hcount (y : Q 5) :
      evenCount (fun i => evenLabel z i y) =
        2 * countIf (evenCount (fun i => evenLabel z i y) ≠ 0) := by
    rcases htwo y with h | h <;> norm_num [h, countIf]
  have htotal := sum_congr (s₁ := (univ : Finset (Q 5))) rfl (fun y _ => hcount y)
  rw [h24, ← mul_sum] at htotal
  omega

#print axioms balanced_active_fibers

/-- The part of the Q9 support lying over even K4 labels. -/
def evenSupport (C : Finset (Q 9)) : Finset (Q 9) :=
  C.filter (fun u => isEvenCode (leftCode u))

private theorem leftCode_suffix_flip (u : Q 9) (d : Fin 5) :
    leftCode (flip u (d.natAdd 4)) = leftCode u := by
  conv_lhs => rw [← join_blocks u, flip_join_right, leftCode_join]

open Classical in
private theorem suffix_endpoint_sum {C : Finset (Q 9)} {z : Q 9 → ℤ}
    (hP : leftProjection C = tenProjection)
    (hu : ∀ u ∈ C, z u = 1 ∨ z u = -1) (hz : ∀ u ∉ C, z u = 0) (d : Fin 5) :
    (∑ y, ∑ i, occupied (evenLabel z i y) * occupied (evenLabel z i (flip y d))) =
      ((directionEndpoints (evenSupport C) (d.natAdd 4)).card : ℤ) := by
  let g (u : Q 9) : ℤ :=
    if isEvenCode (leftCode u) ∧ flip u (d.natAdd 4) ∈ C then 1 else 0
  calc
    _ = ∑ u ∈ C, g u := by
      rw [← sum_support hP g]
      refine sum_congr rfl (fun y _ => ?_)
      rw [Fintype.sum_sum_type]
      simp only [g, leftCode_point, projectionCode, Sum.elim_inl, Sum.elim_inr, even_odd_codes.1,
        even_odd_codes.2, true_and, false_and, ite_false, ite_self, sum_const_zero, add_zero]
      refine sum_congr rfl (fun i _ => ?_)
      simp only [point, projectionCode, Sum.elim_inl, evenLabel, fiber,
        occupied_eq_indicator hu hz, ← flip_join_right]
      split <;> split <;> simp_all
    _ = _ := by
      rw [sum_boole]
      apply congrArg (fun S : Finset (Q 9) => (S.card : ℤ))
      ext u
      simp [evenSupport, directionEndpoints, leftCode_suffix_flip]
      tauto

open Classical in
/-- Over the even K4 labels, the five suffix directions carry twelve edges in total. -/
theorem balanced_even_suffix_edges {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hhalves : ∀ i, 30 ≤ (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card) :
    (∑ d : Fin 5, directionEdges (evenSupport C) (d.natAdd 4)) = 12 := by
  obtain ⟨z, hu, hz, hrow, hcoupled, _, h24, _, _, _⟩ :=
    balanced_occupation_split hsize hreg hb hP hhalves
  have ha (i : Fin 4) (y : Q 5) := (hcoupled i y).1
  have hhorizontal := horizontal_total hreg hP hu hz hrow ha
  have he (j : Fin 4) : directionEdges C (j.castAdd 5) = 12 := by
    have h := direction_edge_count (d := 3) C hreg hb (j.castAdd 5)
    omega
  simp only [he, Nat.cast_ofNat, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hhorizontal
  have hpoint (i : Fin 4) (y : Q 5) : occupied (evenLabel z i y) * evenVerticalDegree z i y =
      3 * occupied (evenLabel z i y) - evenLabel z i y * cScaled z i y := by
    by_cases h : evenLabel z i y = 0
    · simp [h, occupied]
    · simp [occupied, h, even_degree hreg hu hz hrow ha i y h]
  have hcount : (∑ y, ∑ i, occupied (evenLabel z i y) * evenVerticalDegree z i y) =
      3 * (∑ y, evenCount (fun i => evenLabel z i y)) -
        (∑ y, ∑ i, evenLabel z i y * cScaled z i y) := by
    simp only [hpoint, sum_sub_distrib, ← mul_sum, evenCount]
  rw [h24, hhorizontal] at hcount
  have hs : (∑ y, ∑ i, occupied (evenLabel z i y) * evenVerticalDegree z i y) =
      2 * ∑ d : Fin 5, (directionEdges (evenSupport C) (d.natAdd 4) : ℤ) := by
    calc
      _ = ∑ y, ∑ d : Fin 5, ∑ i,
        occupied (evenLabel z i y) * occupied (evenLabel z i (flip y d)) := by
        simp only [evenVerticalDegree, mul_sum]
        exact sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl (fun d _ => ?_)
        rw [suffix_endpoint_sum hP hu hz d, endpoint_card_twice]
        push_cast
        rfl
  rw [hs] at hcount
  have h : (∑ d : Fin 5, (directionEdges (evenSupport C) (d.natAdd 4) : ℤ)) = 12 := by
    omega
  exact_mod_cast h

#print axioms balanced_even_suffix_edges

private theorem partner_bound {z : Q 9 → ℤ} (i : Fin 4)
    (hlocal : ∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y))
    (hzero : ∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0)
    (hdeg : ∀ i y, evenLabel z i y ≠ 0 →
      evenVerticalDegree z i y = 3 - evenLabel z i y * cScaled z i y)
    (hdisj : ∀ i y d, oddCount z y = 4 → oddCount z (flip y d) = 4 →
      evenLabel z i y ≠ 0 → evenLabel z i (flip y d) = 0) :
    activeBalanced z i ≤ 2 * activePartners z i := by
  let a := evenLabel z i
  let c := cScaled z i
  let B (y : Q 5) := occupied (a y) * countIf (oddCount z y = 4)
  let P (y : Q 5) := occupied (a y) * countIf (oddCount z y = 3 ∧ |c y| ≠ 3)
  have hterm (y : Q 5) (d : Fin 5) :
      occupied (a (flip y d)) ≤ evenVerticalDegree z i y :=
    single_le_sum (f := fun d => occupied (a (flip y d)))
      (fun _ _ => by unfold occupied; split <;> omega) (mem_univ d)
  have hleft (y : Q 5) : B y * (∑ d : Fin 5, P (flip y d)) = B y := by
    by_cases ha : a y = 0
    · simp [B, ha, occupied]
    by_cases ho : oddCount z y = 4
    · have hbal : a y * c y = 2 := by
        have h := (label_contributions (i := i) (hlocal y) (fun h => hzero y h i)).2.2
        have hc : c y = 2 ∨ c y = -2 := by
          rcases hlocal y with ⟨_, ht, _⟩ | ⟨_, _, ht, _⟩ | ⟨_, hc, _⟩
          · omega
          · omega
          · exact hc i
        change evenLabel z i y ≠ 0 at ha
        change a y * c y = _ at h
        rcases hc with hc | hc <;>
          simpa [a, c, countIf, occupied, ha, ho, show cScaled z i y = _ from hc] using h
      have hdegY := hdeg i y ha
      change _ = 3 - a y * c y at hdegY
      rw [hbal] at hdegY
      have hP (d : Fin 5) : P (flip y d) = occupied (a (flip y d)) := by
        let v := flip y d
        by_cases hv : a v = 0
        · simp [P, show flip y d = v from rfl, hv, occupied]
        change P v = _
        rcases hlocal v with ⟨_, ht, _⟩ | ⟨j, sign, ht, hc, _⟩ | ⟨ht, _⟩
        · exact (hv (hzero v ht i)).elim
        · have hnc : |c v| ≠ 3 := by
            by_contra hcenter
            have h := (label_contributions (i := i) (hlocal v) (fun h => hzero v h i)).2.2
            change a v * c v = _ at h
            have ha' : evenLabel z i v ≠ 0 := hv
            have hc' : |cScaled z i v| = 3 := hcenter
            have hp : a v * c v = 3 := by
              simpa [a, c, occupied, countIf, hc', ha', ht] using h
            have hdegV := hdeg i v hv
            change _ = 3 - a v * c v at hdegV
            rw [hp, sub_self] at hdegV
            have hback : flip v d = y := BalancedCriticalSpectrum.flip_flip y d
            have hb := hterm v d
            rw [hback, hdegV] at hb
            simp [occupied, ha] at hb
          simp [P, ht, hnc, countIf, show flip y d = v from rfl]
        · exact (hv (hdisj i y d ho ht ha)).elim
      rw [show (∑ d : Fin 5, P (flip y d)) = evenVerticalDegree z i y from
        sum_congr rfl (fun d _ => hP d), hdegY]
      ring
    · simp [B, ho, countIf]
  have hright (y : Q 5) : P y * (∑ d : Fin 5, B (flip y d)) ≤ 2 * P y := by
    by_cases ha : a y = 0
    · simp [P, ha, occupied]
    by_cases hp : oddCount z y = 3 ∧ |c y| ≠ 3
    · have hprod : a y * c y = 1 := by
        have h := (label_contributions (i := i) (hlocal y) (fun h => hzero y h i)).2.2
        have ha' : evenLabel z i y ≠ 0 := ha
        have hc : |cScaled z i y| ≠ 3 := hp.2
        simpa [a, c, occupied, countIf, ha', hc, hp.1] using h
      have hd := hdeg i y ha
      change _ = 3 - a y * c y at hd
      rw [hprod] at hd
      have hs : (∑ d : Fin 5, B (flip y d)) ≤ evenVerticalDegree z i y := by
        exact sum_le_sum (fun d _ => by
          unfold B countIf
          split <;> simp [occupied] <;> split <;> omega)
      simp [P, ha, hp, occupied, countIf]
      omega
    · simp [P, hp, countIf]
  have hswap (d : Fin 5) : (∑ y, B y * P (flip y d)) = ∑ y, P y * B (flip y d) := by
    let e : Q 5 ≃ Q 5 :=
      ⟨fun y => flip y d, fun y => flip y d, fun y => BalancedCriticalSpectrum.flip_flip y d,
        fun y => BalancedCriticalSpectrum.flip_flip y d⟩
    refine Fintype.sum_equiv e _ _ (fun y => ?_)
    change B y * P (flip y d) = P (flip y d) * B (flip (flip y d) d)
    rw [BalancedCriticalSpectrum.flip_flip, mul_comm]
  change (∑ y, B y) ≤ 2 * ∑ y, P y
  calc
    _ = ∑ y, B y * (∑ d : Fin 5, P (flip y d)) := sum_congr rfl (fun y _ => (hleft y).symm)
    _ = ∑ d : Fin 5, ∑ y, B y * P (flip y d) := by
      simp only [mul_sum]
      exact sum_comm
    _ = ∑ d : Fin 5, ∑ y, P y * B (flip y d) := sum_congr rfl (fun d _ => hswap d)
    _ = ∑ y, P y * (∑ d : Fin 5, B (flip y d)) := by
      simp only [mul_sum]
      exact sum_comm
    _ ≤ _ := by
      rw [mul_sum]
      exact sum_le_sum (fun y _ => hright y)


private def binary (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem xor_table :
    ∀ u v w x y t : Bool, binary u + binary v + binary w + binary x + binary y =
      binary t → t = (u ^^ v ^^ w ^^ x ^^ y) := by
  decide +kernel

local instance : Fintype (BitVec 5) :=
  Fintype.ofEquiv (Fin 32) {
    toFun := BitVec.ofFin (w := 5)
    invFun := BitVec.toFin
    left_inv := by intro x; rfl
    right_inv := by intro x; cases x; rfl }

/-- Singleton cut locations as little-endian words in the five-cube. -/
def singletonSupport (z : Q 9 → ℤ) : Finset (BitVec 5) :=
  univ.filter (fun x => oddCount z (cubeBitVec 5 x) = 3)

private theorem singletonSupport_card (z : Q 9 → ℤ) :
    ((singletonSupport z).card : ℤ) = singletons z := by
  have h := Fintype.sum_equiv (cubeBitVec 5)
    (fun x => countIf (oddCount z (cubeBitVec 5 x) = 3))
    (fun y => countIf (oddCount z y = 3)) (fun _ => rfl)
  simpa only [singletons, singletonSupport, countIf, sum_boole] using h

/-- The singleton support satisfies the bit-vector odd-neighbor condition on Q5. -/
theorem singleton_support_neighborParity {z : Q 9 → ℤ}
    (hfix : ∀ y, (∑ d : Fin 5, singletonIndicator z (flip y d)) = singletonIndicator z y)
    (x : BitVec 5) :
    decide (x ∈ singletonSupport z) =
      Q5SmallParitySupport.neighborParity (singletonSupport z) x := by
  have hind (w : BitVec 5) :
      singletonIndicator z (cubeBitVec 5 w) = binary (decide (w ∈ singletonSupport z)) := by
    by_cases h : oddCount z (cubeBitVec 5 w) = 3 <;>
      simp [singletonIndicator, binary, singletonSupport, h]
  have h := hfix (cubeBitVec 5 x)
  have hf (d : Fin 5) :
      flip (cubeBitVec 5 x) d = cubeBitVec 5 (x ^^^ BitVec.ofNat 5 (2 ^ d.val)) :=
    (cubeBitVec_xor_single x d).symm
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero, hf, hind] at h
  unfold Q5SmallParitySupport.neighborParity
  apply xor_table
  have h0 : (BitVec.ofNat 5 (2 ^ (0 : Fin 5).val)) = 1 := rfl
  have h1 : (BitVec.ofNat 5 (2 ^ (1 : Fin 5).val)) = 2 := rfl
  have h2 : (BitVec.ofNat 5 (2 ^ (2 : Fin 5).val)) = 4 := rfl
  have h3 : (BitVec.ofNat 5 (2 ^ (3 : Fin 5).val)) = 8 := rfl
  have h4 : (BitVec.ofNat 5 (2 ^ (4 : Fin 5).val)) = 16 := rfl
  simpa only [h0, h1, h2, h3, h4, add_assoc] using h

/-- A singleton cut count divisible by four and bounded by sixteen has four possible weights. -/
theorem singleton_count_cases {z : Q 9 → ℤ}
    (hfix : ∀ y, (∑ d : Fin 5, singletonIndicator z (flip y d)) = singletonIndicator z y)
    (hmod : singletons z % 4 = 0) (hmax : singletons z ≤ 16) :
    singletons z = 0 ∨ singletons z = 8 ∨ singletons z = 12 ∨ singletons z = 16 := by
  have hcard := singletonSupport_card z
  have hn : 0 ≤ singletons z := by omega
  suffices hne : singletons z ≠ 4 by omega
  intro hs
  let S := singletonSupport z
  have hS : S.card = 4 := by
    change (singletonSupport z).card = 4
    omega
  have hdeg (x : BitVec 5) (hx : x ∈ S) :
      ((univ : Finset (Fin 5)).filter fun i => (x ^^^ BitVec.twoPow 5 i.val) ∈ S).card ≤ 3 := by
    let F := (univ : Finset (Fin 5)).filter fun i => (x ^^^ BitVec.twoPow 5 i.val) ∈ S
    have hm : Set.MapsTo (fun i : Fin 5 => x ^^^ BitVec.twoPow 5 i.val)
        (F : Set (Fin 5)) (S.erase x : Set (BitVec 5)) := by
      intro i hi
      apply Finset.mem_erase.mpr
      refine ⟨?_, (mem_filter.mp hi).2⟩
      intro he
      have hpow : ∀ d : Fin 5, BitVec.twoPow 5 d.val = BitVec.ofNat 5 (2 ^ d.val) := by
        decide +kernel
      change x ^^^ BitVec.twoPow 5 i.val = x at he
      rw [hpow] at he
      have hflip := congrArg (cubeBitVec 5) he
      rw [cubeBitVec_xor_single] at hflip
      have h := congrFun hflip i
      change flip (cubeBitVec 5 x) i i = cubeBitVec 5 x i at h
      rw [BalancedCriticalSpectrum.flip_apply_same] at h
      cases (cubeBitVec 5 x) i <;> simp_all
    have hi : Function.Injective (fun i : Fin 5 => x ^^^ BitVec.twoPow 5 i.val) := by
      intro a b hab
      apply direction_injective
      apply (BitVec.xor_left_inj x).mp
      change x ^^^ BitVec.twoPow 5 a.val = x ^^^ BitVec.twoPow 5 b.val at hab
      simpa only [BitVec.xor_comm x] using hab
    have hle := card_le_card_of_injOn _ hm hi.injOn
    rw [card_erase_of_mem hx, hS] at hle
    exact hle
  have h8 := Q5SmallParitySupport.eight_le_card_of_neighborParity
    (card_pos.mp (show 0 < S.card by omega))
    (singleton_support_neighborParity hfix) hdeg
  omega

#print axioms singleton_support_neighborParity
#print axioms singleton_count_cases

open Classical in
/-- The tight stars and self-adjointness determine the label and cut counts. -/
theorem balanced_label_identities {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hhalves : ∀ i, 30 ≤ (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card) :
    ∃ z : Q 9 → ℤ,
      (∀ u ∈ C, z u = 1 ∨ z u = -1) ∧ (∀ u ∉ C, z u = 0) ∧
      (∀ u, signedRow z u = 3 * z u) ∧
      (∀ i y, signedRow (evenLabel z i) y = 3 * evenLabel z i y - cScaled z i y ∧
        signedRow (cScaled z i) y = 4 * evenLabel z i y - 3 * cScaled z i y) ∧
      (∀ y, LocalType (fun i => evenLabel z i y) (fun i => cScaled z i y) (oddCount z y)) ∧
      (∑ y, evenCount (fun i => evenLabel z i y)) = 24 ∧
      (∑ y, oddCount z y) = 48 ∧
      (∀ i, (∑ y, starCount z i y) = 30) ∧
      (∀ y, oddCount z y = 0 → ∀ i, evenLabel z i y = 0) ∧
      (∀ x : BitVec 5, decide (x ∈ singletonSupport z) =
        Q5SmallParitySupport.neighborParity (singletonSupport z) x) ∧
      3 * singletons z + 4 * balancedCuts z = 48 ∧
      (singletons z = 0 ∨ singletons z = 8 ∨ singletons z = 12 ∨ singletons z = 16) ∧
      ∀ i, let s := singletons z
        let si := singletonCenters z i
        let n := labelCount z i
        let m := activeCenters z i
        let l := activePartners z i
        let p := activeBalanced z i
        n = m + l + p ∧ n = 6 + s / 2 - 2 * si ∧
        (∑ y, evenLabel z i y * cScaled z i y) = 12 ∧ 3 * m + l + 2 * p = 12 ∧
        m - l = 4 * si - s ∧ p = 6 - s / 2 + 2 * (si - m) ∧ 3 * si ≤ s ∧ p ≤ 2 * l := by
  obtain ⟨z, hu, hz, hrow, hcoupled, hlocal, h24, h48, h30, hempty⟩ :=
    balanced_occupation_split hsize hreg hb hP hhalves
  have hcon (i : Fin 4) (y : Q 5) := label_contributions (i := i) (hlocal y) (hempty y · i)
  have hsb : 3 * singletons z + 4 * balancedCuts z = 48 := by
    have h := sum_congr (s₁ := (univ : Finset (Q 5))) rfl (fun y _ => (hcon 0 y).1)
    simpa only [sum_add_distrib, ← mul_sum, singletons, balancedCuts, h48] using h
  have hbn : 0 ≤ balancedCuts z := sum_nonneg (fun _ _ => by unfold countIf; split <;> omega)
  have hsmod : singletons z % 4 = 0 := by omega
  have hfix := (singleton_parity_rows (fun i y => label_values hu hz
    (join (pattern (vertexCode i)) y)) hcoupled hlocal).2
  have hdeg := even_degree hreg hu hz hrow (fun i y => (hcoupled i y).1)
  have hdisj := balanced_neighbors_disjoint hb hP hu hz hrow hlocal
  refine ⟨z, hu, hz, hrow, hcoupled, hlocal, h24, h48, h30, hempty,
    singleton_support_neighborParity hfix, hsb, singleton_count_cases hfix hsmod (by omega),
    fun i => ?_⟩
  dsimp only
  have hn : labelCount z i = activeCenters z i + activePartners z i + activeBalanced z i := by
    unfold labelCount activeCenters activePartners activeBalanced
    simp only [← sum_add_distrib]
    exact sum_congr rfl (fun y _ => (hcon i y).2.1)
  have hpair : (∑ y, evenLabel z i y * cScaled z i y) =
      3 * activeCenters z i + activePartners z i + 2 * activeBalanced z i := by
    unfold activeCenters activePartners activeBalanced
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun y _ => (hcon i y).2.2)
  have hstar₁ := sum_congr (s₁ := (univ : Finset (Q 5))) rfl
    (fun y _ => (star_moments hP hu hz hrow i y).1)
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, h30, h48] at hstar₁
  change 2 * (30 - labelCount z i) = 48 - singletons z + 4 * singletonCenters z i at hstar₁
  have hstar₂ := sum_congr (s₁ := (univ : Finset (Q 5))) rfl
    (fun y _ => (star_moments hP hu hz hrow i y).2)
  simp only [sum_sub_distrib, ← mul_sum, h30, h48] at hstar₂
  change 4 * (30 - labelCount z i) - (∑ y, cScaled z i y ^ 2) = 48 at hstar₂
  have hp := pairing_identity (evenLabel z i) (cScaled z i)
    (fun y => (hcoupled i y).1) (fun y => (hcoupled i y).2)
  have hsq (y : Q 5) : evenLabel z i y ^ 2 = occupied (evenLabel z i y) := by
    rcases label_values hu hz (join (pattern (vertexCode i)) y) with h | h | h <;>
      change evenLabel z i y = _ at h <;> norm_num [h, occupied]
  simp only [hsq] at hp
  change 6 * (∑ y, evenLabel z i y * cScaled z i y) =
    4 * labelCount z i + ∑ y, cScaled z i y ^ 2 at hp
  have hpair12 : (∑ y, evenLabel z i y * cScaled z i y) = 12 := by omega
  have hms : activeCenters z i ≤ singletonCenters z i := by
    exact sum_le_sum (fun y _ => by unfold occupied countIf; split <;> split <;> omega)
  have hl : 0 ≤ activePartners z i := by
    exact sum_nonneg (fun y _ => by unfold occupied countIf; split <;> split <;> omega)
  exact ⟨hn, by omega, hpair12, by omega, by omega, by omega, by omega,
    partner_bound i hlocal hempty hdeg hdisj⟩

#print axioms balanced_label_identities

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
