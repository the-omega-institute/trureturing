/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalSU2SharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spherical caps control unit-quaternion gain reconstruction on finite chordal graphs. -/

import D5.S3.Combinatorics.Graph.Chordal.UniformGainPotential
import D5.S3.Geometry.UnitQuaternions.Holonomy.SU2SharpLayer
import D5.S3.Geometry.UnitQuaternions.Holonomy.SU2ThreeParentHolonomy

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


open Omega.Geometry.HolonomySpectrum

private theorem round_to_one_re (x : U) {s : ℝ} (hs : 0 ≤ s) (hπ : s ≤ π) :
    roundDist x 1 ≤ s ↔ cos s ≤ (x : ℍ[ℝ]).re := by
  rw [round_le_iff x 1 hs hπ]
  change cos s ≤ ((x : ℍ[ℝ]) * star (1 : ℍ[ℝ])).re ↔ _
  simp

private theorem exists_surjection_of_finset_card {α : Type*} (N : Finset α) (hne : N.Nonempty)
    {n : ℕ} (hn : N.card ≤ n) : ∃ f : Fin n → N, Function.Surjective f := by
  classical
  let e := N.equivFin
  let x₀ : N := ⟨hne.choose, hne.choose_spec⟩
  let f (i : Fin n) : N := if h : i.val < N.card then e.symm ⟨i.val, h⟩ else x₀
  refine ⟨f, fun x => ⟨Fin.castLE hn (e x), ?_⟩⟩
  dsimp [f]
  split_ifs with h
  · exact e.symm_apply_apply x
  · exact (h (e x).isLt).elim

private theorem cliqueFour_su2_fit_holonomy [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hlo : π / 5 ≤ δ) (hhi : δ < π / 4)
    (htri : G.SU2TriangleBound g δ)
    (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 4) :
    ∃ p : V → U, G.SU2Fits g p (2 * δ) := by
  classical
  have hδ : 0 ≤ δ := by linarith [pi_pos]
  apply fits_of_simplicial_center hG hskew
  intro a N p ha hcl hN hp
  by_cases hne : N.Nonempty
  · have hn := card_neighbors_lt ha hcl hN hclique
    obtain ⟨f, hf⟩ := exists_surjection_of_finset_card N hne (show N.card ≤ 3 by omega)
    let v (i : Fin 3) : V := (f i : V)
    let q (i : Fin 3) := p (v i) * g (v i) a
    let e (i j : Fin 3) := if v i = v j then 1 else p (v i) * g (v i) (v j) * (p (v j))⁻¹
    have hv (i : Fin 3) : v i ∈ N := (f i).property
    have he (i j : Fin 3) : v i ≠ v j → G.Adj (v i) (v j) := hcl (hv i) (hv j)
    have hflip (i j : Fin 3) : e j i = (e i j)⁻¹ := by
      by_cases hij : v i = v j
      · simp [e, hij]
      · simp [e, hij, Ne.symm hij, hskew _ _ (he i j hij), mul_assoc]
    let M : HolonomyGains (Fin 3) := ⟨e, fun i => by simp [e], hflip⟩
    have hmove (i j : Fin 3) (_ : i ≠ j) : cos (2 * δ) ≤ (M.gain i j : ℍ[ℝ]).re := by
      apply (round_to_one_re _ (by linarith) (by linarith [pi_pos])).mp
      change roundDist (e i j) 1 ≤ _
      by_cases hij : v i = v j
      · simpa [e, hij] using (show 0 ≤ 2 * δ by linarith)
      · simp only [e, ite_eq_right hij]
        rw [← round_mul_right (p (v j))]
        simp only [mul_assoc, inv_mul_cancel, mul_one, one_mul]
        exact hp _ (hv i) _ (hv j) (he i j hij)
    have hnear (i j : Fin 3) (_ : i ≠ j) :
        cos δ ≤ (↑((q i)⁻¹ * M.gain i j * q j) : ℍ[ℝ]).re := by
      apply (round_to_one_re _ hδ (by linarith [pi_pos])).mp
      change roundDist ((q i)⁻¹ * e i j * q j) 1 ≤ δ
      by_cases hij : v i = v j
      · simpa [e, q, hij] using hδ
      · simp only [e, ite_eq_right hij]
        have heq : (q i)⁻¹ * (p (v i) * g (v i) (v j) * (p (v j))⁻¹) * q j =
            (g (v i) a)⁻¹ * (g (v i) (v j) * g (v j) a) := by
          dsimp [q]
          group
        rw [heq, ← round_mul_left (g (v i) a)]
        simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_one]
        exact htri _ _ _ (he i j hij) (hN _ (hv j)) (hN _ (hv i))
    have hcyc (i j k : Fin 3) (_ : i ≠ j) (_ : j ≠ k) (_ : i ≠ k) :
        cos δ ≤ (↑(M.gain i j * M.gain j k * M.gain k i) : ℍ[ℝ]).re := by
      apply (round_to_one_re _ hδ (by linarith [pi_pos])).mp
      change roundDist (e i j * e j k * e k i) 1 ≤ δ
      by_cases hij : v i = v j
      · simpa [e, hij, hflip j k] using hδ
      by_cases hjk : v j = v k
      · simpa [e, hjk, hflip i k] using hδ
      by_cases hik : v i = v k
      · simpa [e, hik, hflip k j, hflip i j] using hδ
      have hEq : e i j * e j k * e k i =
          p (v i) * ((g (v i) (v j) * g (v j) (v k)) * (g (v i) (v k))⁻¹) * (p (v i))⁻¹ := by
        simp only [e, ite_eq_right hij, ite_eq_right hjk, ite_eq_right (Ne.symm hik), hskew _ _ (he i k hik)]
        group
      rw [hEq, ← round_mul_right (p (v i))]
      simp only [mul_assoc, inv_mul_cancel, mul_one, one_mul]
      rw [← round_mul_left (p (v i))⁻¹]
      simp only [← mul_assoc, inv_mul_cancel, one_mul]
      rw [← round_mul_right (g (v i) (v k))]
      simp only [mul_assoc, inv_mul_cancel, mul_one, one_mul]
      exact htri _ _ _ (he i j hij) (he j k hjk) (he i k hik)
    obtain ⟨c, hc⟩ := exists_three_parent_holonomy_center q M hlo hhi hmove hnear hcyc
    refine ⟨c, fun x hx => ?_⟩
    obtain ⟨i, hi⟩ := hf ⟨x, hx⟩
    simpa [q, v, hi] using hc i
  · exact ⟨1, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- A finite chordal graph whose cliques have at most four vertices admits
a unit-quaternion potential with every edge residual at most twice the triangle defect. -/
theorem IsChordal.exists_cliqueFour_su2_gain_potential_two [Finite V] (hG : G.IsChordal)
    {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hδ : 0 ≤ δ)
    (htri : G.SU2TriangleBound g δ)
    (hclique : ∀ S : Finset V, G.IsClique (↑S : Set V) → S.card ≤ 4) :
    ∃ p : V → U, G.SU2Fits g p (2 * δ) := by
  by_cases hsmall : δ ≤ π / 5
  · exact cliqueFour_su2_fit_jung hG hskew hδ hsmall htri hclique
  by_cases hmid : δ < π / 4
  · exact cliqueFour_su2_fit_holonomy hG hskew (le_of_not_ge hsmall) hmid htri hclique
  obtain ⟨p, hp⟩ := hG.exists_cliqueFive_su2_gain_potential_half_pi hskew
    (fun S hS => (hclique S hS).trans (by decide))
  exact ⟨p, fun x y hxy => (hp x y hxy).trans (by linarith [le_of_not_gt hmid])⟩


private theorem round_to_one_conj (a x : U) :
    roundDist (a * x * a⁻¹) 1 = roundDist x 1 := by
  rw [← round_mul_right a, mul_assoc, inv_mul_cancel, mul_one, one_mul]
  simpa only [mul_one] using round_mul_left a x 1

set_option maxHeartbeats 2000000 in
private theorem fits_of_bfs_caps [Finite V] (hG : G.IsChordal) (hconn : G.Connected)
    (o : V) {g : V → V → U} (hskew : G.SU2Skew g) {δ r R : ℝ} (hδ : 0 ≤ δ)
    (hδπ : δ ≤ π) (htri : G.SU2TriangleBound g δ) (hR : 0 ≤ R) (hr : 2 * R ≤ r)
    (center : ∀ (I : Finset V) (_ : I.Nonempty) (P : SU2Patch I δ), Nonempty (SU2Cap P.point R))
    (same : ∀ (I J : Finset V) (P : SU2Patch I δ) (Q : SU2Patch J δ)
      (e : I → J) (u : U) (C : SU2Cap P.point R) (D : SU2Cap Q.point R),
      (∀ i, roundDist (P.point i * u) (Q.point (e i)) ≤ δ) →
      (∀ i j, P.holonomy.gain i j = Q.holonomy.gain (e i) (e j)) →
      roundDist (C.center * u) D.center ≤ r) :
    ∃ p : V → U, G.SU2Fits g p r := by
  classical
  let := Fintype.ofFinite V
  let γ := gain g
  have hg {x y : V} (h : G.Adj x y) : γ x y = g x y := gain_adj g h
  have hg₀ (x : V) : γ x x = 1 := by simp [γ, gain]
  have hrev {x y : V} (h : x = y ∨ G.Adj x y) : γ y x = (γ x y)⁻¹ := by
    rcases h with rfl | h
    · simp [hg₀]
    · rw [hg h, hg h.symm]
      exact hskew _ _ h
  have tri {x y z : V} (hxy : x = y ∨ G.Adj x y) (hyz : y = z ∨ G.Adj y z)
      (hxz : x = z ∨ G.Adj x z) : roundDist (γ x y * γ y z) (γ x z) ≤ δ := by
    rcases hxy with rfl | hxy
    · simp [hg₀, hδ]
    rcases hyz with rfl | hyz
    · simp [hg₀, hδ]
    rcases hxz with rfl | hxz
    · simp [hg₀, hrev (Or.inr hxy), hδ]
    · simpa only [hg hxy, hg hyz, hg hxz] using htri _ _ _ hxy hyz hxz
  have near {k : ℕ} {C : Component G o (k + 1)} {x y : V}
      (hx : x ∈ Shadow G o C) (hy : y ∈ Shadow G o C) : x = y ∨ G.Adj x y :=
    (eq_or_ne x y).imp_right (shadow_clique hG hconn C hx hy)
  choose anchor anchor_parent anchor_adj using
    (fun (k : ℕ) (C : Component G o (k + 2)) => exists_shadow_anchor hG hconn C)
  let a : (k : ℕ) → Component G o (k + 1) → V
    | 0, _ => o
    | k + 1, C => anchor k C
  have a_adj {k : ℕ} {C : Component G o (k + 1)} {x : V} (hx : x ∈ Shadow G o C) :
      a k C = x ∨ G.Adj (a k C) x := by
    cases k with
    | zero => exact Or.inl (hconn.dist_eq_zero_iff.mp hx.1)
    | succ k => exact Or.inr (anchor_adj k C x hx)
  let parents (k : ℕ) (x : V) := Finset.univ.filter (fun y => G.dist o y = k ∧ G.Adj y x)
  have memP {k : ℕ} {x y : V} : y ∈ parents k x ↔ G.dist o y = k ∧ G.Adj y x := by
    simp [parents]
  have Pnon {k : ℕ} {x : V} (hx : G.dist o x = k + 1) : (parents k x).Nonempty := by
    obtain ⟨y, hy, hk⟩ := exists_predecessor hx
    exact ⟨y, memP.mpr ⟨hk, hy⟩⟩
  have Pshadow {k : ℕ} {x : V} (hx : G.dist o x = k + 1) (i : parents k x) :
      (i : V) ∈ Shadow G o (componentOf G o (k + 1) x hx.ge) :=
    mem_shadow_of_adj (memP.mp i.property).1 hx.ge (memP.mp i.property).2
  let P (k : ℕ) (x : V) (hx : G.dist o x = k + 1) : SU2Patch (parents k x) δ := by
    let A := a k (componentOf G o (k + 1) x hx.ge)
    let u (i : parents k x) := γ A i
    let v (i : parents k x) := γ i x
    let f (i j : parents k x) := u i * γ i j * (u j)⁻¹
    let b := fun i : parents k x => u i * v i
    have hf₀ (i : parents k x) : f i i = 1 := by simp [f, hg₀]
    have hfR (i j : parents k x) : f j i = (f i j)⁻¹ := by
      dsimp only [f]
      rw [hrev (near (Pshadow hx i) (Pshadow hx j))]
      group
    let M : HolonomyGains (parents k x) := ⟨f, hf₀, hfR⟩
    refine ⟨b, M, ?_, ?_, ?_⟩
    · intro i j _
      apply (round_to_one_re _ hδ hδπ).mp
      change roundDist (f i j) 1 ≤ δ
      rw [← round_mul_right (u j)]
      simp only [f, mul_assoc, inv_mul_cancel, mul_one, one_mul]
      exact tri (a_adj (Pshadow hx i)) (near (Pshadow hx i) (Pshadow hx j)) (a_adj (Pshadow hx j))
    · intro i j _
      apply (round_to_one_re _ hδ hδπ).mp
      change roundDist ((b i)⁻¹ * f i j * b j) 1 ≤ δ
      have he : (b i)⁻¹ * f i j * b j = (v i)⁻¹ * (γ i j * v j) := by
        dsimp [f, b]
        group
      rw [he, ← round_mul_left (v i)]
      simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_one]
      exact tri (near (Pshadow hx i) (Pshadow hx j))
        (Or.inr (memP.mp j.property).2) (Or.inr (memP.mp i.property).2)
    · intro i j l _ _ _
      apply (round_to_one_re _ hδ hδπ).mp
      change roundDist (f i j * f j l * f l i) 1 ≤ δ
      have hij := near (Pshadow hx i) (Pshadow hx j)
      have hjl := near (Pshadow hx j) (Pshadow hx l)
      have hil := near (Pshadow hx i) (Pshadow hx l)
      have he : f i j * f j l * f l i =
          u i * ((γ i j * γ j l) * (γ i l)⁻¹) * (u i)⁻¹ := by
        dsimp [f]
        rw [hrev hil]
        group
      rw [he, round_to_one_conj, ← round_mul_right (γ i l)]
      simp only [mul_assoc, inv_mul_cancel, mul_one, one_mul]
      exact tri hij hjl hil
  let D (k : ℕ) (x : V) (hx : G.dist o x = k + 1) : SU2Cap (P k x hx).point R :=
    (center (parents k x) (Pnon hx) (P k x hx)).some
  let Q := anchorGain γ a
  let atLevel (x : V) : (k : ℕ) → G.dist o x = k → U
    | 0, _ => 1
    | k + 1, hx => Q k (componentOf G o (k + 1) x hx.ge) * (D k x hx).center
  let p (x : V) := atLevel x (G.dist o x) rfl
  have pat (x : V) (k : ℕ) (hx : G.dist o x = k) : p x = atLevel x k hx := by
    subst k
    rfl
  have peval {k : ℕ} {x : V} (hx : G.dist o x = k + 1) :
      p x = Q k (componentOf G o (k + 1) x hx.ge) * (D k x hx).center := pat x _ hx
  have across {x y : V} {k : ℕ} (hx : G.dist o x = k) (hy : G.dist o y = k + 1)
      (hxy : G.Adj x y) : roundDist (p x * γ x y) (p y) ≤ r := by
    cases k with
    | zero =>
      have hroot : o = x := hconn.dist_eq_zero_iff.mp hx
      subst x
      have hp0 : p o = 1 := pat o 0 (by simp)
      rw [hp0, peval hy]
      simpa only [one_mul, Q, anchorGain, P, a, hg₀] using
        ((D 0 y hy).radius ⟨o, memP.mpr ⟨hx, hxy⟩⟩).trans (by linarith)
    | succ k =>
      let C := componentOf G o (k + 2) y hy.ge
      let i : parents (k + 1) y := ⟨x, memP.mpr ⟨hx, hxy⟩⟩
      have hs := Pshadow hy i
      have hc := shadow_parent hs
      have ha := anchor_parent k C
      have hadj := anchor_adj k C x hs
      let j : parents k x := ⟨anchor k C, memP.mpr ⟨ha.1, hadj⟩⟩
      have hm := (D k x hx).radius j
      have hn := (D (k + 1) y hy).radius i
      have hm' : roundDist (Q (k + 1) C * γ (a (k + 1) C) x) (p x) ≤ R := by
        rw [peval hx, ← hc]
        change roundDist
          ((Q k (parent G o C) * γ (a k (parent G o C)) (anchor k C)) * γ (anchor k C) x)
          (Q k (parent G o C) * (D k x hx).center) ≤ R
        rw [mul_assoc, round_mul_left, hc]
        exact hm
      have hn' : roundDist ((Q (k + 1) C * γ (a (k + 1) C) x) * γ x y) (p y) ≤ R := by
        rw [peval hy, mul_assoc, round_mul_left]
        exact hn
      have hm'' : roundDist (p x * γ x y) ((Q (k + 1) C * γ (a (k + 1) C) x) * γ x y) ≤ R := by
        rw [round_mul_right, round_comm]
        exact hm'
      exact (round_triangle _ _ _).trans ((add_le_add hm'' hn').trans (by linarith only [hr]))
  have within {x y : V} {k : ℕ} (hx : G.dist o x = k + 1) (hy : G.dist o y = k + 1)
      (hxy : G.Adj x y) : roundDist (p x * γ x y) (p y) ≤ r := by
    have hc := componentOf_adj hx.ge hy.ge hxy
    have hnest : parents k x ⊆ parents k y ∨ parents k y ⊆ parents k x := by
      by_contra h
      obtain ⟨i, hi, hiy⟩ := Finset.not_subset.mp (fun hn => h (Or.inl hn))
      obtain ⟨j, hj, hjx⟩ := Finset.not_subset.mp (fun hn => h (Or.inr hn))
      have hij : i ≠ j := fun he => hiy (he.symm ▸ hj)
      have hi' := Pshadow hx (⟨i, hi⟩ : parents k x)
      have hj' := Pshadow hy (⟨j, hj⟩ : parents k y)
      rw [← hc] at hj'
      have hij' := shadow_clique hG hconn _ hi' hj' hij
      have hxi := (memP.mp hi).2
      have hyj := (memP.mp hj).2
      rcases four_cycle_diagonal hG hxi hxy hyj.symm hij'.symm
        (by intro he; have := (memP.mp hi).1; rw [he] at this; omega)
        (by intro he; have := (memP.mp hj).1; rw [← he] at this; omega) with h | h
      · exact hiy (memP.mpr ⟨(memP.mp hi).1, h⟩)
      · exact hjx (memP.mpr ⟨(memP.mp hj).1, h.symm⟩)
    have hforward {x y : V} (hx : G.dist o x = k + 1) (hy : G.dist o y = k + 1)
        (hxy : G.Adj x y) (hs : parents k x ⊆ parents k y) :
        roundDist (p x * γ x y) (p y) ≤ r := by
      let e (i : parents k x) : parents k y := ⟨i, hs i.property⟩
      have hc := componentOf_adj hx.ge hy.ge hxy
      have hpairs (i : parents k x) :
          roundDist ((P k x hx).point i * γ x y) ((P k y hy).point (e i)) ≤ δ := by
        change roundDist ((γ (a k _) i * γ i x) * γ x y) (γ (a k _) i * γ i y) ≤ δ
        rw [← hc, mul_assoc, round_mul_left]
        exact tri (Or.inr (memP.mp i.property).2) (Or.inr hxy) (Or.inr (memP.mp (e i).property).2)
      have hhol (i j : parents k x) :
          (P k x hx).holonomy.gain i j = (P k y hy).holonomy.gain (e i) (e j) := by
        dsimp [P, e]
        rw [hc]
      rw [peval hx, peval hy, hc, mul_assoc, round_mul_left]
      exact same _ _ _ _ e _ _ _ hpairs hhol
    rcases hnest with hs | hs
    · exact hforward hx hy hxy hs
    · have h := hforward hy hx hxy.symm hs
      rw [hrev (Or.inr hxy), ← round_mul_right (γ x y), mul_assoc, inv_mul_cancel, mul_one] at h
      simpa only [round_comm] using h
  have hfit {x y : V} (hxy : G.Adj x y) (hord : G.dist o x ≤ G.dist o y) :
      roundDist (p x * γ x y) (p y) ≤ r := by
    by_cases heq : G.dist o x = G.dist o y
    · by_cases hz : G.dist o x = 0
      · have hx : o = x := hconn.dist_eq_zero_iff.mp hz
        have hy : o = y := hconn.dist_eq_zero_iff.mp (heq.symm.trans hz)
        exact (hxy.ne (hx.symm.trans hy)).elim
      · exact within (k := G.dist o x - 1) (by omega) (by omega) hxy
    · exact across rfl (by have := hxy.diff_dist_adj (u := o); omega) hxy
  refine ⟨p, fun x y hxy => ?_⟩
  rw [round_edge, ← hg hxy]
  rcases le_total (G.dist o x) (G.dist o y) with h | h
  · exact hfit hxy h
  · have hs := hfit hxy.symm h
    rw [hrev (Or.inr hxy), ← round_mul_right (γ x y), mul_assoc, inv_mul_cancel, mul_one] at hs
    simpa only [round_comm] using hs


open Omega.Geometry.SU2ChordalIntervals

private theorem su2_first_range [Finite V] (hG : G.IsChordal) (hconn : G.Connected)
    (o : V) {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 4 / 5) (htri : G.SU2TriangleBound g δ) :
    ∃ p : V → U, G.SU2Fits g p (3 * δ) := by
  classical
  let s := √(capSquare (cos δ))
  let R := arccos s
  have hδ₂ : δ ≤ π / 2 := by linarith [pi_gt_three]
  have hδπ : δ ≤ π := by linarith [pi_gt_three]
  have hR₀ : 0 ≤ R := arccos_nonneg _
  have hRπ : R ≤ π := arccos_le_pi _
  have hR := jung_radius_first_range hδ hδmax
  change R ≤ 27 / 20 * δ at hR
  have hs₁ : s ≤ 1 := by
    change √(capSquare (cos δ)) ≤ 1
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := sin_sq_add_cos_sq δ
    unfold capSquare
    nlinarith only [h, sq_nonneg (sin δ)]
  have hcos : cos R = s := cos_arccos (by linarith [sqrt_nonneg (capSquare (cos δ))]) hs₁
  have hc : 9 / 16 < cos δ := by
    have hs := pow_le_pow_left₀ hδ hδmax 2
    nlinarith only [one_sub_sq_div_two_le_cos (x := δ), hs]
  apply fits_of_bfs_caps hG hconn o hskew hδ hδπ htri hR₀ (show 2 * R ≤ 3 * δ by linarith)
  · intro I hI P
    let : Nonempty I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
    apply P.exists_jung_cap hδ hδ₂ hc hR₀ hRπ
    rw [hcos, show s = √(cos (2 * δ) + (1 - cos (2 * δ)) / 4) by
      unfold s capSquare
      rw [cos_two_mul]
      congr 1
      ring]
  · intro I J P Q e u C D hp _
    let θ := roundDist (C.center * u) D.center
    have hθ₀ : 0 ≤ θ := round_nonneg _ _
    have hθπ : θ ≤ π := round_le_pi _ _
    have hRδ : R + δ ≤ π := by linarith [pi_gt_three]
    have hproj := cap_projection C D e u hδ hR₀ hRδ hp
    change cos (R + δ) ≤ ‖C.nearest‖ * cos θ at hproj
    have hcap : s ≤ ‖C.nearest‖ := hcos ▸ C.cos_radius_le_nearest_norm hR₀ hRπ
    have hnorm := C.nearest_norm_le_one
    by_cases hsmall : δ ≤ 1 / 2
    · have hnon : 0 ≤ cos (R + δ) :=
        cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩
      have hθ : 0 ≤ cos θ := nonneg_of_mul_nonneg_right (hnon.trans hproj) C.pos
      have hproj' := hproj.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm hθ)
      have hh : θ ≤ R + δ := (strictAntiOn_cos.le_iff_ge
        ⟨by positivity, hRδ⟩ ⟨hθ₀, hθπ⟩).mp hproj'
      show θ ≤ 3 * δ
      linarith
    · change θ ≤ 3 * δ
      by_contra! hbad
      have ht := cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ 3 * δ) hθπ hbad.le
      have hlt := cap_center_cosine_lt (le_of_not_ge hsmall) hδmax hcap hnorm
      have he : cos (R + δ) = s * cos δ - √(1 - capSquare (cos δ)) * sin δ := by
        rw [cos_add, hcos]
        dsimp only [R]
        rw [sin_arccos]
        have hs : 0 ≤ capSquare (cos δ) := by
          unfold capSquare
          have hc' : 17 / 25 ≤ cos δ := by
            nlinarith only [one_sub_sq_div_two_le_cos (x := δ), pow_le_pow_left₀ hδ hδmax 2]
          nlinarith only [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 17 / 25) hc' 2]
        simp only [s, sq_sqrt hs]
      rw [← he] at hlt
      exact (not_lt_of_ge hproj) ((mul_le_mul_of_nonneg_left ht C.pos.le).trans_lt hlt)


/-- Every skew unit-quaternion gain on a finite connected chordal graph
admits a potential with edge residuals at most `434δ/125` when all
triangle defects are at most `δ`. -/
theorem IsChordal.exists_su2_gain_potential_global_sharp [Finite V] (hG : G.IsChordal)
    (hconn : G.Connected) {g : V → V → U} (hskew : G.SU2Skew g) {δ : ℝ} (hδ : 0 ≤ δ)
    (htri : G.SU2TriangleBound g δ) : ∃ p : V → U, G.SU2Fits g p ((434 / 125) * δ) := by
  obtain ⟨o⟩ := hconn.nonempty
  by_cases hsmall : δ ≤ 4 / 5
  · obtain ⟨p, hp⟩ := su2_first_range hG hconn o hskew hδ hsmall htri
    exact ⟨p, fun x y hxy => (hp x y hxy).trans (by linarith only [hδ])⟩
  by_cases hπ : (434 / 125) * δ ≤ π
  · have hδπ : δ ≤ π := by linarith only [hδ, hπ]
    obtain ⟨t, s, k, L, ht, ht', hT, hc₀, hc, hs, hs', hspec, hR, hangle, hk, hk₀,
      hgap, _, hL, hcert⟩ := exists_range_two_bounds (le_of_not_ge hsmall) hπ
    have hs₀ : 0 < s := by linarith only [hs]
    have hspec' : s ≤ holonomyCosine t := hspec
    apply fits_of_bfs_caps hG hconn o hskew hδ hδπ htri (arccos_nonneg s) hR
    · intro I hI P
      let : Nonempty I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
      exact P.exists_holonomy_cap ht ht' hT hc hc₀ hs₀ hs'.le hspec'
    · intro I J P Q e u C D hp hhol
      exact same_layer_second_range P Q e u C D hp hhol hδ hδπ hπ ht ht' hT hc hs₀ hs' hspec'
        hangle hk hk₀ hgap hL hcert
  · exact ⟨fun _ => 1, fun x y hxy => (round_le_pi _ _).trans (le_of_not_ge hπ)⟩

end SimpleGraph
