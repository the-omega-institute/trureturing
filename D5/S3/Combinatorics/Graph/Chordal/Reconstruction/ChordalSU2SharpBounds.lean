/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spherical caps control unit-quaternion gain reconstruction on finite chordal graphs. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import OmegaMath.Geometry.SphericalJung
import OmegaMath.Geometry.UnitQuaternionMetric
import OmegaMath.Geometry.SU2ThreeParentHolonomy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open scoped Quaternion InnerProductSpace

namespace SimpleGraph

open Omega.Geometry.UnitQuaternion
open Real

local notation "U" => unitary ℍ[ℝ]

variable {V : Type*} {G : SimpleGraph V}

/-- Reversing an edge inverts its gain. -/
def SU2Skew (G : SimpleGraph V) (g : V → V → U) : Prop :=
  ∀ u v, G.Adj u v → g v u = (g u v)⁻¹

/-- Triangle gains differ from the corresponding two-edge products by at most `δ`. -/
def SU2TriangleBound (G : SimpleGraph V) (g : V → V → U) (δ : ℝ) : Prop :=
  ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w →
    roundDist (g u v * g v w) (g u w) ≤ δ

/-- The oriented edge residuals of a potential are all at most `r`. -/
def SU2Fits (G : SimpleGraph V) (g : V → V → U) (p : V → U) (r : ℝ) : Prop :=
  ∀ u v, G.Adj u v → roundDist (g u v) ((p u)⁻¹ * p v) ≤ r

private theorem fits_of_simplicial_center [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g) {r : ℝ}
    (center : ∀ (a : V) (N : Finset V) (p : V → U),
      a ∉ N → G.IsClique (↑N : Set V) → (∀ x ∈ N, G.Adj x a) →
      (∀ x ∈ N, ∀ y ∈ N, G.Adj x y → roundDist (p x * g x y) (p y) ≤ r) →
      ∃ c : U, ∀ x ∈ N, roundDist (p x * g x a) c ≤ r) :
    ∃ p : V → U, G.SU2Fits g p r := by
  classical
  let := Fintype.ofFinite V
  have hmain (S : Finset V) :
      ∃ p : V → U, ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → roundDist (p x * g x y) (p y) ≤ r := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hs : S.Nonempty
      · let : Nonempty (↑S : Set V) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
        obtain ⟨z, hz⟩ := (hG.induce (S : Set V)).exists_isSimplicial
        let a : V := z.val
        have ha : a ∈ S := z.property
        obtain ⟨p, hp⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        let N := S.filter fun x => G.Adj x a
        have memN {x : V} : x ∈ N ↔ x ∈ S ∧ G.Adj x a := Finset.mem_filter
        have haN : a ∉ N := fun h => (memN.mp h).2.ne rfl
        have hcl : G.IsClique (↑N : Set V) := by
          intro x hx y hy hne
          exact hz (show (⟨x, (memN.mp hx).1⟩ : (S : Set V)) ∈ _ from (memN.mp hx).2.symm)
            (show (⟨y, (memN.mp hy).1⟩ : (S : Set V)) ∈ _ from (memN.mp hy).2.symm)
            (by simpa [Subtype.ext_iff] using hne)
        have hN (x) (hx : x ∈ N) : G.Adj x a := (memN.mp hx).2
        have herase (x) (hx : x ∈ N) : x ∈ S.erase a :=
          Finset.mem_erase.mpr ⟨(hN x hx).ne, (memN.mp hx).1⟩
        obtain ⟨c, hc⟩ := center a N p haN hcl hN
          (fun x hx y hy hxy => hp x (herase x hx) y (herase y hy) hxy)
        let p' (x : V) := if x = a then c else p x
        have hnew (x) (hx : x ∈ N) : roundDist (p' x * g x a) (p' a) ≤ r := by
          simpa [p', (hN x hx).ne] using hc x hx
        refine ⟨p', fun x hx y hy hxy => ?_⟩
        by_cases hxa : x = a
        · subst x
          rw [hskew y a hxy.symm, ← round_mul_right (g y a)]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
          rw [round_comm]
          exact hnew y (memN.mpr ⟨hy, hxy.symm⟩)
        · by_cases hya : y = a
          · subst y
            exact hnew x (memN.mpr ⟨hx, hxy⟩)
          · simpa [p', hxa, hya] using
              hp x (Finset.mem_erase.mpr ⟨hxa, hx⟩) y (Finset.mem_erase.mpr ⟨hya, hy⟩) hxy
      · exact ⟨fun _ => 1, fun x hx => (hs ⟨x, hx⟩).elim⟩
  obtain ⟨p, hp⟩ := hmain Finset.univ
  exact ⟨p, fun x y hxy => (round_edge _ _ _).trans_le
    (hp x (Finset.mem_univ _) y (Finset.mem_univ _) hxy)⟩

private theorem card_neighbors_lt {a : V} {N : Finset V}
    (ha : a ∉ N) (hcl : G.IsClique (↑N : Set V)) (hN : ∀ x ∈ N, G.Adj x a)
    {k : ℕ} (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ k) :
    N.card < k := by
  classical
  have h := hclique (insert a N) (by
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hx
    · exact (hN y (hy.resolve_left hxy.symm)).symm
    · rcases hy with rfl | hy
      · exact hN x hx
      · exact hcl hx hy hxy)
  rwa [Finset.card_insert_of_notMem ha, ← Nat.lt_iff_add_one_le] at h

private theorem candidate_diameter {g : V → V → U} {δ r : ℝ} (htri : G.SU2TriangleBound g δ)
    {a : V} {N : Finset V} {p : V → U} (hcl : G.IsClique (↑N : Set V))
    (hN : ∀ x ∈ N, G.Adj x a) (hp : ∀ x ∈ N, ∀ y ∈ N, G.Adj x y →
      roundDist (p x * g x y) (p y) ≤ r) {x y : V} (hx : x ∈ N) (hy : y ∈ N) (hne : x ≠ y) :
    roundDist (p x * g x a) (p y * g y a) ≤ r + δ := by
  have hxy := hcl hx hy hne
  have h₁ : roundDist (p x * g x a) ((p x * g x y) * g y a) ≤ δ := by
    rw [mul_assoc, round_mul_left, round_comm]
    exact htri x y a hxy (hN y hy) (hN x hx)
  have h₂ : roundDist ((p x * g x y) * g y a) (p y * g y a) ≤ r := by
    rw [round_mul_right]
    exact hp x hx y hy hxy
  exact (round_triangle _ _ _).trans (by linarith)

private theorem exists_simplicial_su2_fit_of_cos [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g) {δ r : ℝ} (htri : G.SU2TriangleBound g δ)
    (hr : r ∈ Set.Icc 0 π) (hd : r + δ ∈ Set.Icc 0 (π / 2))
    (ht : cos r ≤ √(cos (r + δ) + (1 - cos (r + δ)) / 4)) :
    ∃ p : V → U, G.SU2Fits g p r := by
  classical
  apply fits_of_simplicial_center hG hskew
  intro a N p _ hcl hN hp
  by_cases hne : N.Nonempty
  · let : Nonempty (↑N : Set V) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    let q (i : (↑N : Set V)) : ℍ[ℝ] := ((p i * g i a : U) : ℍ[ℝ])
    have hnorm (i) : ‖q i‖ = 1 := norm_coe _
    have hpair (i j : (↑N : Set V)) : cos (r + δ) ≤ ⟪q i, q j⟫_ℝ := by
      by_cases hij : i = j
      · subst j
        simpa [real_inner_self_eq_norm_sq, hnorm] using cos_le_one (r + δ)
      · apply (round_le_iff (p i * g i a) (p j * g j a) hd.1 (by linarith [hd.2, pi_pos])).mp
        exact candidate_diameter htri hcl hN hp i.property j.property (Subtype.coe_ne_coe.mpr hij)
    have hcos : 0 ≤ cos (r + δ) := cos_nonneg_of_mem_Icc ⟨by linarith [hd.1, pi_pos], hd.2⟩
    obtain ⟨c, hc, hcp⟩ := Omega.Geometry.SphericalJung.exists_cap q 4 (by decide)
      (.inr (by rw [Quaternion.finrank_eq_four])) hnorm (cos_le_one _)
      (fun i j _ => hpair i j)
      (Omega.Geometry.SphericalJung.zero_not_mem_convexHull_of_pairwise_nonneg q hnorm
        (fun i j => hcos.trans (hpair i j)))
    refine ⟨ofUnit c hc, fun x hx => (round_le_iff _ _ hr.1 hr.2).mpr ?_⟩
    rw [coe_ofUnit, real_inner_comm]
    exact ht.trans (hcp ⟨x, hx⟩)
  · exact ⟨1, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- Small triangle defect at most `π / 6` yields a fit at twice the defect. -/
theorem IsChordal.exists_su2_gain_potential_small_defect_two [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ π / 6)
    (htri : G.SU2TriangleBound g δ) : ∃ p : V → U, G.SU2Fits g p (2 * δ) := by
  apply exists_simplicial_su2_fit_of_cos hG hskew htri
    ⟨by linarith, by linarith [pi_pos]⟩ ⟨by linarith, by linarith⟩
  rw [show 2 * δ + δ = 3 * δ by ring]
  have hc := cos_le_cos_of_nonneg_of_le_pi hδ (by linarith [pi_pos] : π / 6 ≤ π) hδπ
  rw [cos_pi_div_six] at hc
  have hc₀ : 0 ≤ cos δ := (div_nonneg (sqrt_nonneg _) (by norm_num)).trans hc
  have hcs : 3 ≤ 4 * cos δ ^ 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by positivity : 0 ≤ cos δ + √3 / 2)]
  have hprod := mul_nonneg (mul_nonneg (sub_nonneg.mpr (cos_le_one δ))
    (by positivity : 0 ≤ 4 * cos δ + 1)) (sub_nonneg.mpr hcs)
  have hsq : cos (2 * δ) ^ 2 ≤ cos (3 * δ) + (1 - cos (3 * δ)) / 4 := by
    rw [cos_two_mul, cos_three_mul]
    linarith only [hprod]
  exact le_sqrt_of_sq_le hsq

/-- All finite chordal graphs admit the coefficient `8 / 5` for defects at most `1 / 10`. -/
theorem IsChordal.exists_su2_gain_potential_small_defect_eight_fifths [Finite V]
    (hG : G.IsChordal) {g : V → V → U} (hskew : G.SU2Skew g)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 10) (htri : G.SU2TriangleBound g δ) :
    ∃ p : V → U, G.SU2Fits g p ((8 / 5) * δ) := by
  have hr : (8 / 5) * δ ∈ Set.Icc 0 π := ⟨by linarith, by linarith [pi_gt_three]⟩
  have hd : (8 / 5) * δ + δ ∈ Set.Icc 0 (π / 2) :=
    ⟨by linarith, by linarith [pi_gt_three]⟩
  apply exists_simplicial_su2_fit_of_cos hG hskew htri hr hd
  have hpoly : (14936 / 9375) * δ ≤ sin ((8 / 5) * δ) := by
    have ht := sin_ge_sub_cube hr.1
    have hδsq : δ ^ 2 ≤ 1 / 100 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (by positivity : 0 ≤ (1 / 10) + δ)]
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδsq)]
  have hs : 0 ≤ sin ((13 / 10) * δ) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three])
  have hsin : sin ((13 / 10) * δ) ≤ (13 / 10) * δ := sin_le (by linarith)
  have hb : 0 ≤ √(3 / 2 : ℝ) := sqrt_nonneg _
  have hbsq : (√(3 / 2 : ℝ)) ^ 2 = 3 / 2 := sq_sqrt (by norm_num)
  have hcoef : √(3 / 2 : ℝ) * (13 / 10) ≤ 637 / 400 := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity : (0 : ℝ) ≤ 637 / 400)
    rw [mul_pow, hbsq]
    norm_num
  have hsin' : √(3 / 2 : ℝ) * sin ((13 / 10) * δ) ≤ sin ((8 / 5) * δ) :=
    (mul_le_mul_of_nonneg_left hsin hb).trans
      (by
        calc
          _ = (√(3 / 2 : ℝ) * (13 / 10)) * δ := by ring
          _ ≤ (637 / 400) * δ := mul_le_mul_of_nonneg_right hcoef hδ
          _ ≤ (14936 / 9375) * δ := mul_le_mul_of_nonneg_right (by norm_num) hδ
          _ ≤ _ := hpoly)
  have hsquare : (3 / 2) * sin ((13 / 10) * δ) ^ 2 ≤ sin ((8 / 5) * δ) ^ 2 := by
    have hsq := pow_le_pow_left₀ (mul_nonneg hb hs) hsin' 2
    rwa [mul_pow, hbsq] at hsq
  apply le_sqrt_of_sq_le
  rw [show (8 / 5) * δ + δ = 2 * ((13 / 10) * δ) by ring, cos_two_mul_eq_one_sub]
  nlinarith only [hsquare, sin_sq_add_cos_sq ((8 / 5) * δ)]

private theorem hemisphere_center {ι : Type*} [Fintype ι] (q : ι → U)
    (hcard : Fintype.card ι ≤ 4) : ∃ c : U, ∀ i, roundDist (q i) c ≤ π / 2 := by
  obtain ⟨v, hv, h⟩ := Omega.Geometry.SphericalJung.exists_closed_hemisphere
    (fun i => (q i : ℍ[ℝ])) (by rw [Quaternion.finrank_eq_four]; decide)
    (by rw [Quaternion.finrank_eq_four]; exact hcard)
  refine ⟨ofUnit v hv, fun i => (round_le_iff _ _ (by positivity) (by linarith [pi_pos])).mpr ?_⟩
  simpa only [coe_ofUnit, cos_pi_div_two, real_inner_comm (q i : ℍ[ℝ]) v] using h i

/-- A chordal graph whose cliques have at most five vertices admits a closed-hemisphere fit. -/
theorem IsChordal.exists_cliqueFive_su2_gain_potential_half_pi [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g)
    (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 5) :
    ∃ p : V → U, G.SU2Fits g p (π / 2) := by
  classical
  apply fits_of_simplicial_center hG hskew
  intro a N p ha hcl hN _
  have hn := card_neighbors_lt ha hcl hN hclique
  obtain ⟨c, hc⟩ := hemisphere_center (fun i : N => p i * g i a) (by
    rw [Fintype.card_coe]
    exact Nat.le_of_lt_succ hn)
  exact ⟨c, fun x hx => hc ⟨x, hx⟩⟩


/-- With cliques of size at most three, half the candidate diameter bounds
the insertion error, up to the closed-hemisphere radius. -/
theorem IsChordal.exists_cliqueThree_su2_gain_potential_min [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hδ : 0 ≤ δ)
    (htri : G.SU2TriangleBound g δ)
    (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 3) :
    ∃ p : V → U, G.SU2Fits g p (min δ (π / 2)) := by
  by_cases hhalf : δ < π / 2
  · rw [min_eq_left hhalf.le]
    classical
    apply fits_of_simplicial_center hG hskew
    intro a N p ha hcl hN hp
    have hn := card_neighbors_lt ha hcl hN hclique
    obtain ⟨c, hc⟩ := exists_two_parent_center (fun i : N => p i * g i a)
      (by rw [Fintype.card_coe]; omega) hδ hhalf (fun i j hij => by
        rw [two_mul]
        exact candidate_diameter htri hcl hN hp i.property j.property (Subtype.coe_ne_coe.mpr hij))
    exact ⟨c, fun x hx => hc ⟨x, hx⟩⟩
  · rw [min_eq_right (le_of_not_gt hhalf)]
    exact hG.exists_cliqueFive_su2_gain_potential_half_pi hskew
      (fun S hS => (hclique S hS).trans (by decide))

private theorem cliqueFour_su2_fit_jung [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ π / 5) (htri : G.SU2TriangleBound g δ)
    (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 4) :
    ∃ p : V → U, G.SU2Fits g p (2 * δ) := by
  classical
  apply fits_of_simplicial_center hG hskew
  intro a N p ha hcl hN hp
  have hn := card_neighbors_lt ha hcl hN hclique
  obtain ⟨c, hc⟩ := exists_three_parent_jung_center (fun i : N => p i * g i a)
    (by rw [Fintype.card_coe]; omega) hδ hsmall (fun i j hij => by
      have h := candidate_diameter htri hcl hN hp i.property j.property (Subtype.coe_ne_coe.mpr hij)
      linarith)
  exact ⟨c, fun x hx => hc ⟨x, hx⟩⟩

end SimpleGraph
