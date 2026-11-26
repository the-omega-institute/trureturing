/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCenter
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoCenter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Tight distance-two contact forces eight neighbors at each exterior star center. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar

/-! Base cells and external center directions for the tight distance-two family. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions mem_directions exterior_even regular_directions flip_injective)
open BalancedCubeGirth (adjacent_exists_flip flip_comm)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (minimumDisplacements minimum_displacements_card_and_equality wordParity)
open Q9TightContactStar (tight_contact_cell_full_star)
open Q9SignedFragmentBoundary (signedFragment card_add_abs_le)
open Q9WeightedSaturation (defect signedBiadjacency)
open TwoBalancedComponents (componentFinset componentFinset_subset)
open Translation.Q9ActualAperiodicity (exists_two_aperiodic_components signed_defect_det_eq_component)
open private differingAxes parity_flip parity_foldl_flip mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_symm differingAxes_right_inj differingAxes_flip_cell flip_cell_involution from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private antipode Cell antipode_cell flip_cell diff_subset diff_single diff_pair diff_flip_left
  dist_flip_pair isolated_row center_terms_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private edge edge_sq edge_curvature from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private fullRow_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedFragmentBoundary
open private exists_both_parity_supported_of_signed_defect_singular from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ActualMinimumDisplacements
open private component_connected from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
open private componentFinset_disjoint componentFinset_neighbor_closed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

/-- Both orders of a distance-two contact use the same starting parity. -/
private theorem parity_eq_of_distance_two {u v : Q 9} (h : hammingDist u v = 2) :
    parity u = parity v := by
  obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp
    (show (differingAxes u v).card = 2 from h)
  have hv : v = flip (flip u i) j := differingAxes_right_inj (hT.trans (diff_pair u hij).symm)
  rw [hv, parity_flip, parity_flip, Bool.not_not]

private theorem minimumDisplacements_swap_two (C D : Finset (Q 9)) (b : Bool) :
    minimumDisplacements C D b 2 = minimumDisplacements D C b 2 := by
  have hswap {S T : Finset (Q 9)} {M : Finset (Fin 9)}
      (h : M ∈ minimumDisplacements S T b 2) : M ∈ minimumDisplacements T S b 2 := by
    obtain ⟨u, hu, v, hv, hp, hd, he⟩ := mem_minimumDisplacements.mp h
    exact mem_minimumDisplacements.mpr ⟨v, hv, u, hu,
      (parity_eq_of_distance_two hd).symm.trans hp, (hammingDist_comm v u).trans hd,
      (differingAxes_symm v u).trans he⟩
  ext M
  exact ⟨hswap, hswap⟩

private theorem flip_antipode (A : Finset (Fin 9)) (z : Q 9) (i : Fin 9) :
    flip (antipode A z) i = antipode A (flip z i) := by
  change flip (A.toList.foldl flip z) i = A.toList.foldl flip (flip z i)
  generalize A.toList = w
  induction w generalizing z with
  | nil => rfl
  | cons j w ih =>
    simp only [List.foldl_cons]
    rw [ih, flip_comm z j i]

private theorem parity_antipode_four {A : Finset (Fin 9)} (hA : A.card = 4) (z : Q 9) :
    parity (antipode A z) = parity z := by
  have hlen : A.toList.length = 4 := by simpa only [Finset.length_toList] using hA
  obtain ⟨i, j, k, l, he⟩ := List.length_eq_four.mp hlen
  change parity (A.toList.foldl flip z) = parity z
  rw [parity_foldl_flip, he]
  simp [wordParity]

/-- Every point from level two through level four of a four-axis cell lies
on, or is adjacent to, a leaf of the opposite star. -/
private theorem near_opposite_leaf {A : Finset (Fin 9)} {z u : Q 9}
    (hA : A.card = 4) (hu : Cell A z u) (hfar : 2 ≤ (differingAxes u z).card) :
    ∃ i ∈ A, hammingDist u (flip (antipode A z) i) ≤ 1 := by
  classical
  let w := antipode A z
  let T := differingAxes u w
  have hsub : differingAxes u z ⊆ A := diff_subset hu (fun _ _ => rfl)
  have hT : T = A \ differingAxes u z := differingAxes_flip_cell A u z hsub
  have hcard : T.card ≤ 2 := by
    rw [hT, Finset.card_sdiff_of_subset hsub, hA]
    omega
  by_cases hne : T.Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hia : i ∈ A := by
      rw [hT] at hi
      exact (Finset.mem_sdiff.mp hi).1
    have his : i ∈ differingAxes w u := by
      rw [differingAxes_symm w u]
      exact hi
    have he : differingAxes u (flip w i) = T.erase i := by
      rw [differingAxes_symm u (flip w i), diff_flip_left, ite_eq_left his, differingAxes_symm w u]
    refine ⟨i, hia, ?_⟩
    change (differingAxes u (flip w i)).card ≤ 1
    rw [he]
    have hc := Finset.card_erase_add_one hi
    omega
  · have hzero : T.card = 0 := by
      by_contra hn
      exact hne (Finset.card_pos.mp (Nat.pos_of_ne_zero hn))
    have he : u = w := hammingDist_eq_zero.mp (show hammingDist u w = 0 from hzero)
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
    exact ⟨i, hi, by rw [he]; exact le_of_eq (flip_adj w i)⟩

/-- Separate the two leaves of an exterior row by their two-coordinate mask. -/
private theorem row_contact {C D : Finset (Q 9)} {b : Bool} {q : Q 9} {i j : Fin 9}
    (hC : flip q i ∈ C) (hD : flip q j ∈ D) (hij : i ≠ j)
    (hp : parity (flip q i) = b) :
    ({i, j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
  have he : differingAxes (flip q i) (flip q j) = {i, j} := by
    simpa only [BalancedCriticalSpectrum.flip_flip] using diff_pair (flip q i) hij
  have hd : hammingDist (flip q i) (flip q j) = 2 := by
    change (differingAxes (flip q i) (flip q j)).card = 2
    rw [he, Finset.card_pair hij]
  exact mem_minimumDisplacements.mpr ⟨_, hC, _, hD, hp, hd, he⟩

/-- The constraints on one side of a tight distance-two cell in its actual cube coordinates. -/
structure TightStarSide (C : Finset (Q 9)) (A : Finset (Fin 9)) (z : Q 9) : Prop where
  base : ∀ u, (∀ i ∉ A, u i = z i) → (u ∈ C ↔ ∃ i ∈ A, flip z i = u)
  adjacent : ∀ t ∉ A, ∀ u, (∀ i ∉ A, u i = z i) → flip u t ∈ C →
    u = z ∨ ∃ i ∈ A, flip z i = u
  pairRow : ∀ i ∈ A, ∀ j ∈ A, i ≠ j →
    flip (flip z i) j ∉ C ∧ directions C (flip (flip z i) j) = {i, j}
  leafDegree : ∀ i ∈ A, (directions C (flip z i)).card = 3 ∧
    ∀ j ∈ directions C (flip z i), j ∉ A
  centerDegree : (directions C z).card = 8
  externalDegree : (directions C z \ A).card = 4
  missing : ∃ t ∉ A, directions C z = Finset.univ.erase t ∧
    ∀ u ∈ directions C z \ A,
      directions C (flip z u) \ A ⊆ {t} ∧
      2 ≤ (directions C (flip z u) ∩ A).card ∧ (directions C (flip z u) ∩ A).card ≤ 3

set_option maxHeartbeats 1000000 in
open Classical in
private theorem tight_star_side {C D : Finset (Q 9)} {A : Finset (Fin 9)} {b : Bool} {z : Q 9}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hA : A.card = 4)
    (hfamily : minimumDisplacements C D b 2 = A.powersetCard 2) (hzpar : parity z = !b)
    (hleaf : ∀ i ∈ A, flip z i ∈ C)
    (hopp : ∀ i ∈ A, flip (antipode A z) i ∈ D) : TightStarSide C A z := by
  classical
  have hzcell : Cell A z z := fun _ _ => rfl
  have hsub : A ⊆ directions C z := fun i hi => (mem_directions C z i).mpr (hleaf i hi)
  have hz : z ∉ C := by
    intro hz
    have hc := Finset.card_le_card hsub
    rw [hA, regular_directions C hr hz] at hc
    omega
  have hpos (u : Q 9) (hu : Cell A z u) :
      (differingAxes u z).card < 2 → u = z ∨ ∃ i ∈ A, flip z i = u := by
    intro hc
    by_cases hzero : (differingAxes u z).card = 0
    · exact Or.inl (hammingDist_eq_zero.mp (show hammingDist u z = 0 from hzero))
    · have hd : hammingDist z u = 1 := by
        rw [hammingDist_comm z u]
        change (differingAxes u z).card = 1
        omega
      obtain ⟨i, hi⟩ := adjacent_exists_flip (show (hypercube 9).Adj z u from hd)
      have hia := diff_subset hzcell hu
      have him : i ∈ differingAxes z u := by rw [hi, diff_single]; simp
      exact Or.inr ⟨i, hia him, hi.symm⟩
  have hbase (u : Q 9) (hu : Cell A z u) : u ∈ C ↔ ∃ i ∈ A, flip z i = u := by
    constructor
    · intro huC
      have hc : (differingAxes u z).card < 2 := by
        by_contra! hfar
        obtain ⟨i, hi, hnear⟩ := near_opposite_leaf hA hu hfar
        exact (not_le_of_gt (show hammingDist u (flip (antipode A z) i) < 2 by omega))
          (hsep u huC _ (hopp i hi))
      rcases hpos u hu hc with rfl | h
      · exact (hz huC).elim
      · exact h
    · rintro ⟨i, hi, rfl⟩
      exact hleaf i hi
  have hadjacent (t : Fin 9) (ht : t ∉ A) (u : Q 9) (hu : Cell A z u)
      (huC : flip u t ∈ C) : u = z ∨ ∃ i ∈ A, flip z i = u := by
    apply hpos u hu
    by_contra! hfar
    obtain ⟨i, hi, hnear⟩ := near_opposite_leaf hA hu hfar
    let v := flip (antipode A z) i
    have hvD : v ∈ D := hopp i hi
    have hzero : hammingDist u v ≠ 0 := by
      intro he
      have huv := hammingDist_eq_zero.mp he
      have hs := hsep _ huC v hvD
      rw [← huv] at hs
      have hone : hammingDist (flip u t) u = 1 := (flip_adj u t).symm
      omega
    have hd : hammingDist u v = 1 := by
      change hammingDist u v ≤ 1 at hnear
      omega
    obtain ⟨j, hj⟩ := adjacent_exists_flip (show (hypercube 9).Adj u v from hd)
    have hvc : Cell A z v := flip_cell (antipode_cell hzcell) hi
    have hja : j ∈ A := diff_subset hu hvc (by rw [hj, diff_single]; simp)
    have htj : t ≠ j := fun h => ht (h.symm ▸ hja)
    have hpv : parity v = b := by
      change parity (flip (antipode A z) i) = b
      rw [parity_flip, parity_antipode_four hA, hzpar, Bool.not_not]
    have hp : parity (flip u t) = b := by
      rw [parity_flip, ← parity_flip u j, ← hj, hpv]
    have hm := row_contact huC (hj ▸ hvD) htj hp
    rw [hfamily] at hm
    exact ht ((Finset.mem_powersetCard.mp hm).1 (by simp))
  have hrow (i : Fin 9) (hi : i ∈ A) (j : Fin 9) (hj : j ∈ A) (hij : i ≠ j) :
      flip (flip z i) j ∉ C ∧ directions C (flip (flip z i) j) = {i, j} := by
    have hp : ({i, j} : Finset (Fin 9)) ⊆ A := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hi
      · exact hj
    have hnonempty : (A \ ({i, j} : Finset (Fin 9))).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff_of_subset hp, hA, Finset.card_pair hij]
      decide
    obtain ⟨k, hk⟩ := hnonempty
    obtain ⟨hka, hkp⟩ := Finset.mem_sdiff.mp hk
    have hki : k ≠ i := fun he => hkp (by simp [he])
    have hkj : k ≠ j := fun he => hkp (by simp [he])
    let q := flip (flip z i) j
    have hqc : Cell A z q := flip_cell (flip_cell hzcell hi) hj
    have hqb : parity q = !b := by simp only [q, parity_flip, Bool.not_not, hzpar]
    have hd : hammingDist q (flip z k) = 3 :=
      (hammingDist_comm q (flip z k)).trans (dist_flip_pair z hij hki hkj)
    obtain ⟨hq, haxes⟩ :=
      isolated_row hsep (show A.card = 2 + 2 from hA) hfamily hqc (flip_cell hzcell hka)
        hqb (by rw [← flip_antipode]; exact hopp k hka) hd
    have hqi : flip q i = flip z j := by
      dsimp only [q]
      rw [flip_comm z i j, BalancedCriticalSpectrum.flip_flip]
    have hqj : flip q j = flip z i := BalancedCriticalSpectrum.flip_flip _ _
    refine ⟨hq, ?_⟩
    ext r
    constructor
    · intro hrq
      obtain ⟨l, _, he⟩ := (hbase (flip q r) (flip_cell hqc (haxes hrq))).mp
        ((mem_directions C q r).mp hrq)
      by_cases hli : l = i
      · subst l
        have hrj := flip_injective q (he.symm.trans hqj.symm)
        simp [hrj]
      · by_cases hlj : l = j
        · subst l
          have hri := flip_injective q (he.symm.trans hqi.symm)
          simp [hri]
        · have hd3 : hammingDist (flip z l) q = 3 := dist_flip_pair z hij hli hlj
          have hd1 : hammingDist (flip z l) q = 1 := by rw [he]; exact (flip_adj q r).symm
          omega
    · intro hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with he | he
      · rw [he]
        exact (mem_directions C q i).mpr (hqi.symm ▸ hleaf j hj)
      · rw [he]
        exact (mem_directions C q j).mpr (hqj.symm ▸ hleaf i hi)
  have hleafDegree (i : Fin 9) (hi : i ∈ A) :
      (directions C (flip z i)).card = 3 ∧ ∀ j ∈ directions C (flip z i), j ∉ A := by
    refine ⟨regular_directions C hr (hleaf i hi), ?_⟩
    intro j hj hja
    have hmem := (mem_directions C (flip z i) j).mp hj
    by_cases hij : i = j
    · subst j
      rw [BalancedCriticalSpectrum.flip_flip] at hmem
      exact hz hmem
    · exact (hrow i hi j hja hij).1 hmem
  obtain ⟨σ, hs⟩ := hb
  have halign (i : Fin 9) (hi : i ∈ A) (j : Fin 9) (hj : j ∈ A) :
      edge z i * σ (flip z i) = edge z j * σ (flip z j) := by
    by_cases hij : i = j
    · subst j
      rfl
    · exact center_terms_eq hr hs z hij (hrow i hi j hj hij).1 (hrow i hi j hj hij).2
  let K := A.image (flip z)
  have hKC : K ⊆ C := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact hleaf i hi
  have hdirs : directions K z = A := by
    ext i
    rw [mem_directions]
    constructor
    · intro hi
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
      exact (flip_injective z he) ▸ hj
    · intro hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  let a := fun j : Fin 9 => edge z j * σ (flip z j)
  let s := a i
  have haunit (j : Fin 9) (hj : j ∈ directions C z) : |a j| = 1 := by
    have hm := SupportedEigenSaturation.matrix_abs_of_adj (flip_adj z j)
    rcases hs.1 _ ((mem_directions C z j).mp hj) with h | h <;> simp [a, edge, h, hm]
  have hsunit : |s| = 1 := by
    exact haunit i (hsub hi)
  have hsumA : (∑ j ∈ A, a j) = (A.card : ℝ) * s := by
    calc
      _ = ∑ _j ∈ A, s := Finset.sum_congr rfl (fun j hj => halign j hj i hi)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hfrag : |signedFragment K σ z| = (A.card : ℝ) := by
    have hsum : signedFragment K σ z = (A.card : ℝ) * s := by
      change (∑ j ∈ directions K z, a j) = _
      rw [hdirs]
      exact hsumA
    rw [hsum, abs_mul, hsunit, mul_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ A.card)]
  have hbound := card_add_abs_le hKC hr hs z hz
  rw [hdirs, hfrag] at hbound
  have hlo : A.card + A.card ≤ (directions C z).card := by exact_mod_cast hbound
  have hhi : (directions C z).card ≤ 9 := by simpa using Finset.card_le_univ (directions C z)
  obtain ⟨n, hn⟩ := exterior_even C hr ⟨σ, hs⟩ z hz
  have h8 : (directions C z).card = 8 := by omega
  have h4 : (directions C z \ A).card = 4 := by
    rw [Finset.card_sdiff_of_subset hsub, h8, hA]
  have h1 : ((Finset.univ : Finset (Fin 9)) \ directions C z).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), h8] <;> simp
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h1
  have htC : t ∉ directions C z :=
    (Finset.mem_sdiff.mp (ht.symm ▸ Finset.mem_singleton_self t)).2
  have hmissing : directions C z = Finset.univ.erase t := by
    ext j
    have he : j = t ↔ j ∉ directions C z := by
      have h := Finset.ext_iff.mp ht j
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] using h.symm
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact not_not.symm.trans (not_congr he).symm
  let E := directions C z \ A
  have hsumE : (∑ j ∈ E, a j) = -(4 : ℝ) * s := by
    have hzero : (∑ j ∈ directions C z, a j) = 0 := fullRow_zero hr hs z hz
    have hsplit : (∑ j ∈ E, a j) + ∑ j ∈ A, a j = 0 :=
      (Finset.sum_sdiff hsub).trans hzero
    rw [hsumA, hA] at hsplit
    push_cast at hsplit
    linarith only [hsplit]
  have hsq : s ^ 2 = 1 := by
    change (edge z i * σ (flip z i)) ^ 2 = 1
    rw [mul_pow, edge_sq, BalancedCriticalSpectrum.switching_sq hs (hleaf i hi), mul_one]
  have htotal : (∑ j ∈ E, (1 + s * a j)) = 0 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumE, Finset.sum_const, nsmul_eq_mul,
      show E.card = 4 from h4]
    push_cast
    nlinarith only [hsq]
  have hnonneg (j : Fin 9) (hj : j ∈ E) : 0 ≤ 1 + s * a j := by
    have habs : |s * a j| = 1 := by
      rw [abs_mul, hsunit, haunit j (Finset.mem_sdiff.mp hj).1, mul_one]
    linarith only [(abs_le.mp habs.le).1]
  have hneg (j : Fin 9) (hj : j ∈ E) : a j = -s := by
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp htotal j hj
    have heq : s * a j = -1 := by linarith only [hzero]
    calc
      a j = s * (s * a j) := by rw [← mul_assoc, ← pow_two, hsq, one_mul]
      _ = -s := by rw [heq]; ring
  have hnoDouble (u v : Fin 9) (hu : u ∈ E) (hv : v ∈ E) (huv : u ≠ v) :
      flip (flip z u) v ∉ C := by
    let q := flip (flip z u) v
    intro hq
    have huC := (mem_directions C z u).mp (Finset.mem_sdiff.mp hu).1
    have hvC := (mem_directions C z v).mp (Finset.mem_sdiff.mp hv).1
    have htpath : edge (flip z u) v = σ (flip z u) * σ q :=
      hs.2 _ huC _ hq (flip_adj (flip z u) v)
    have hq' : flip (flip z v) u ∈ C := (flip_comm z u v) ▸ hq
    have hupath' : edge (flip z v) u =
        σ (flip z v) *
          σ (flip (flip z v) u) :=
      hs.2 _ hvC _ hq' (flip_adj (flip z v) u)
    have hupath : edge (flip z v) u =
        σ (flip z v) * σ q := by
      rw [hupath', flip_comm z v u]
    have hcurv : a u * σ q = -(a v * σ q) := by
      simpa only [a, htpath, hupath, mul_assoc] using edge_curvature z huv
    rw [hneg u hu, hneg v hv] at hcurv
    have hsne : s ≠ 0 := by
      intro h
      simp [h] at hsunit
    have hqne : σ q ≠ 0 := by
      rcases hs.1 q hq with h | h <;> norm_num [h]
    exact (mul_ne_zero (neg_ne_zero.mpr hsne) hqne) (by linarith only [hcurv])
  refine ⟨hbase, hadjacent, hrow, hleafDegree, h8, h4, t, fun h => htC (hsub h), hmissing, ?_⟩
  intro u hu
  have hExt : directions C (flip z u) \ A ⊆ {t} := by
    intro v hv
    obtain ⟨hvC, hvA⟩ := Finset.mem_sdiff.mp hv
    have hmem := (mem_directions C (flip z u) v).mp hvC
    by_contra hn
    have hvt : v ≠ t := fun he => hn (Finset.mem_singleton.mpr he)
    have hvz : v ∈ directions C z := by
      rw [hmissing]
      exact Finset.mem_erase.mpr ⟨hvt, Finset.mem_univ _⟩
    by_cases huv : u = v
    · subst v
      exact hz (by simpa only [BalancedCriticalSpectrum.flip_flip] using hmem)
    · exact hnoDouble u v hu (Finset.mem_sdiff.mpr ⟨hvz, hvA⟩) huv hmem
  have huC := (mem_directions C z u).mp (Finset.mem_sdiff.mp hu).1
  have hreg := regular_directions C hr huC
  have hle := Finset.card_le_card hExt
  rw [Finset.card_singleton] at hle
  have hsplt := Finset.card_inter_add_card_sdiff (directions C (flip z u)) A
  exact ⟨hExt, by omega, by omega⟩

open Classical in
/-- The frozen full-star theorem supplies the opposite leaves. Each exterior center
has four internal and four external occupied directions. -/
theorem tight_distance_two_cell
    {C D : Finset (Q 9)} {A : Finset (Fin 9)} {b : Bool} {x y : Q 9}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hC : ∀ i, ∃ f : Q 9 → ℝ,
      (∀ u, f u ≠ 0 ↔ u ∈ C ∧ parity u = b) ∧
      (∀ u ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f u = 0))
    (hD : ∀ c, ∃ g : Q 9 → ℝ,
      (∀ v, g v ≠ 0 ↔ v ∈ D ∧ parity v = c) ∧
      (∀ v ∉ D, weightedLinear (fun _ => 1) g v = 0))
    (hA : A.card = 4) (hfamily : minimumDisplacements C D b 2 = A.powersetCard 2)
    (hx : x ∈ C) (hy : y ∈ D) (hxb : parity x = b) (hxy : hammingDist x y = 2) :
    ∃ z : Q 9, (∀ i ∉ A, z i = x i) ∧ parity z = !b ∧
      TightStarSide C A z ∧ TightStarSide D A (A.toList.foldl flip z) := by
  obtain ⟨_, z, hzc, hzb, _, hstarC, hstarD⟩ :=
    tight_contact_cell_full_star (le_refl 2) hsep hrC hbC hC hD hA hfamily hx hy hxb hxy
  have hleafC (i : Fin 9) (hi : i ∈ A) : flip z i ∈ C := by
    have hp : parity (flip z i) = b := by rw [parity_flip, hzb, Bool.not_not]
    exact (hstarC _ hp (flip_cell hzc hi)).mpr ⟨i, hi, rfl⟩
  have hleafD (i : Fin 9) (hi : i ∈ A) : flip (antipode A z) i ∈ D := by
    rw [flip_antipode]
    have hp : parity (antipode A (antipode A (flip z i))) = b := by
      change parity (A.toList.foldl flip (A.toList.foldl flip (flip z i))) = b
      rw [flip_cell_involution, parity_flip, hzb, Bool.not_not]
    exact (hstarD _ hp (antipode_cell (flip_cell hzc hi))).mpr ⟨i, hi, rfl⟩
  have hback : antipode A (antipode A z) = z := flip_cell_involution A z
  have hsep' (u : Q 9) (hu : u ∈ D) (v : Q 9) (hv : v ∈ C) : 2 ≤ hammingDist u v :=
    (hammingDist_comm u v).symm ▸ hsep v hv u hu
  have hfamily' := (minimumDisplacements_swap_two C D b).symm.trans hfamily
  refine ⟨z, hzc, hzb, tight_star_side hsep hrC hbC hA hfamily hzb hleafC hleafD, ?_⟩
  exact tight_star_side hsep' hrD hbD hA hfamily' ((parity_antipode_four hA z).trans hzb)
    hleafD (by rw [hback]; exact hleafC)

open Classical in
/-- Universal signed-defect singularity supplies the weighted hypotheses of the
full-star theorem. A six-mask parity slice supplies the four tight axes. -/
theorem tight_distance_two_cell_of_signed_defect
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (htight : (minimumDisplacements C D b 2).card = 6) :
    ∃ (A : Finset (Fin 9)) (z : Q 9), A.card = 4 ∧
      minimumDisplacements C D b 2 = A.powersetCard 2 ∧ parity z = !b ∧
      TightStarSide C A z ∧ TightStarSide D A (A.toList.foldl flip z) := by
  have hC (i : Fin 9) : ∃ f : Q 9 → ℝ,
      (∀ u, f u ≠ 0 ↔ u ∈ C ∧ parity u = b) ∧
      (∀ u ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f u = 0) := by
    let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
    have hw (k : Fin 9) : 0 < w k := by
      dsimp only [w]
      split <;> norm_num
    exact exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b
  have hD (c : Bool) : ∃ g : Q 9 → ℝ,
      (∀ v, g v ≠ 0 ↔ v ∈ D ∧ parity v = c) ∧
      (∀ v ∉ D, weightedLinear (fun _ => 1) g v = 0) := by
    let w : Fin 9 → ℝ := fun _ => 1
    exact exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD w
      (fun _ => by norm_num [w]) (hdetD w) c
  have hne : (minimumDisplacements C D b 2).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨A, hA, hfamily⟩ :=
    (minimum_displacements_card_and_equality C D b 2 (by decide) hsep hne hC hD).2
      (show (minimumDisplacements C D b 2).card = (2 + 2).choose 2 from htight)
  obtain ⟨T, hT⟩ := hne
  obtain ⟨x, hx, y, hy, hxb, hxy, _⟩ := mem_minimumDisplacements.mp hT
  obtain ⟨z, _, hzb, hleft, hright⟩ :=
    tight_distance_two_cell hsep hrC hrD hbC hbD hC hD hA hfamily hx hy hxb hxy
  exact ⟨A, z, hA, hfamily, hzb, hleft, hright⟩

open Classical in
/-- On the two actual components with universally singular signed defects,
each six-mask distance-two parity slice gives a tight opposing-star cell. -/
theorem exists_actual_components_with_tight_cell_of_six_masks
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      K ≠ L ∧ ∀ b,
        let C := componentFinset U K
        let D := componentFinset U L
        (minimumDisplacements C D b 2).card = 6 →
          ∃ (A : Finset (Fin 9)) (z : Q 9), A.card = 4 ∧
            minimumDisplacements C D b 2 = A.powersetCard 2 ∧ parity z = !b ∧
            TightStarSide C A z ∧ TightStarSide D A (A.toList.foldl flip z) := by
  obtain ⟨K, L, hKL, hcomponents⟩ := exists_two_aperiodic_components U hU hdeg
  let C := componentFinset U K
  let D := componentFinset U L
  have hdisj : Disjoint C D := componentFinset_disjoint U K L hKL
  have hsep (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) : 2 ≤ hammingDist u v := by
    have h0 : hammingDist u v ≠ 0 := fun he =>
      Finset.disjoint_left.mp hdisj ((hammingDist_eq_zero.mp he) ▸ hu) hv
    have h1 : hammingDist u v ≠ 1 := fun he =>
      Finset.disjoint_left.mp hdisj
        (componentFinset_neighbor_closed U K u hu v (componentFinset_subset U L hv) he) hv
    omega
  obtain ⟨hrC, hbC, hdetC, _⟩ := hcomponents K (Or.inl rfl)
  obtain ⟨hrD, hbD, hdetD, _⟩ := hcomponents L (Or.inr rfl)
  refine ⟨K, L, hKL, fun b htight => ?_⟩
  exact tight_distance_two_cell_of_signed_defect hsep hrC hrD
    (component_connected U K) (component_connected U L) hbC hbD
    (fun w => (signed_defect_det_eq_component w U false K).trans (hdetC w))
    (fun w => (signed_defect_det_eq_component w U false L).trans (hdetD w)) htight

/-- A compensating direction in a shared exterior row makes an actual
opposite-parity contact with each occupied internal neighbor on the other side. -/
theorem boundary_row_external_mask {C D : Finset (Q 9)} {A : Finset (Fin 9)}
    {b : Bool} {q : Q 9} {r j : Fin 9} (hp : parity q = b)
    (hr : r ∈ directions C q \ A) (hj : j ∈ directions D q ∩ A) :
    ({r, j} : Finset (Fin 9)) ∈ minimumDisplacements C D (!b) 2 := by
  obtain ⟨hrC, hrA⟩ := Finset.mem_sdiff.mp hr
  obtain ⟨hjD, hjA⟩ := Finset.mem_inter.mp hj
  exact row_contact ((mem_directions C q r).mp hrC) ((mem_directions D q j).mp hjD)
    (fun h => hrA (h.symm ▸ hjA)) (by rw [parity_flip, hp])

/-- The translation direction of a pair row returns to its empty base vertex. -/
theorem pair_row_translation_direction_absent {C : Finset (Q 9)} {A : Finset (Fin 9)}
    {z : Q 9} (h : TightStarSide C A z) {i j t : Fin 9}
    (hi : i ∈ A) (hj : j ∈ A) (hij : i ≠ j) :
    t ∉ directions C (flip (flip (flip z i) j) t) := by
  rw [mem_directions, BalancedCriticalSpectrum.flip_flip]
  exact (h.pairRow i hi j hj hij).1

open Classical in
/-- If each side has one occupied internal neighbor and at most two directions
are available for compensation, each side uses a distinct compensator. -/
theorem singleton_boundary_row_compensators {C D : Finset (Q 9)}
    {A W : Finset (Fin 9)} {q : Q 9}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hC : (directions C q ∩ A).card = 1) (hD : (directions D q ∩ A).card = 1)
    (hWC : directions C q \ A ⊆ W) (hWD : directions D q \ A ⊆ W) (hW : W.card ≤ 2) :
    ∃ r ∈ W, ∃ s ∈ W, r ≠ s ∧
      directions C q \ A = {r} ∧ directions D q \ A = {s} := by
  have hexterior (S : Finset (Q 9)) (hS : (directions S q ∩ A).card = 1) :
      ∃ i, flip q i ∈ S := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (directions S q ∩ A).card by omega)
    exact ⟨i, (mem_directions S q i).mp (Finset.mem_inter.mp hi).1⟩
  obtain ⟨i, hi⟩ := hexterior C hC
  obtain ⟨j, hj⟩ := hexterior D hD
  have hqC : q ∉ C := by
    intro hq
    have hlow := hsep q hq _ hj
    have hd : hammingDist q (flip q j) = 1 := flip_adj q j
    omega
  have hqD : q ∉ D := by
    intro hq
    have hlow := hsep _ hi q hq
    have hd : hammingDist (flip q i) q = 1 := (flip_adj q i).symm
    omega
  have hone (S : Finset (Q 9))
      (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
      (hb : IsBalanced S) (hq : q ∉ S) (hS : (directions S q ∩ A).card = 1)
      (hsub : directions S q \ A ⊆ W) : (directions S q \ A).card = 1 := by
    have hsplit := Finset.card_inter_add_card_sdiff (directions S q) A
    have hle := (Finset.card_le_card hsub).trans hW
    obtain ⟨n, hn⟩ := exterior_even S hr hb q hq
    omega
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (hone C hrC hbC hqC hC hWC)
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp (hone D hrD hbD hqD hD hWD)
  have hrC' : r ∈ directions C q \ A := hr.symm ▸ Finset.mem_singleton_self r
  have hsD' : s ∈ directions D q \ A := hs.symm ▸ Finset.mem_singleton_self s
  refine ⟨r, hWC hrC', s, hWD hsD', ?_, hr, hs⟩
  intro he
  subst s
  have hlow := hsep _ ((mem_directions C q r).mp (Finset.mem_sdiff.mp hrC').1)
    _ ((mem_directions D q r).mp (Finset.mem_sdiff.mp hsD').1)
  rw [hammingDist_self] at hlow
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
