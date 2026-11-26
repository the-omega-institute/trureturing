/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactStar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The signed boundary at a tight contact cell excludes equality at distance three or more. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ActualMinimumDisplacements
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedFragmentBoundary

/-! Exterior parity and Huang square curvature in a tight minimum-contact cell. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj flip_apply_same flip_flip IsBalanced IsSwitching)
open BalancedCubeComponentBoundary (directions mem_directions exterior_even regular_directions flip_injective)
open BalancedCubeGirth (adjacent_exists_flip flip_comm)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (minimumDisplacements minimum_displacements_card_and_equality)
open Q9TightContactComplement (minimum_contact_flip_complement minimum_contact_cell_antipodes)
open Q9SignedFragmentBoundary (signedFragment card_add_abs_le)
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open Q9WeightedSaturation (defect signedBiadjacency)
open private exists_both_parity_supported_of_signed_defect_singular from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ActualMinimumDisplacements
open private edge edge_sq edge_reciprocal edge_curvature from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private fullRow_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedFragmentBoundary
open private differingAxes differingAxes_foldl_flip foldl_flip_apply parity_flip
  mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_flip_cell differingAxes_right_inj flip_cell_involution from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement

private abbrev antipode (A : Finset (Fin 9)) (u : Q 9) : Q 9 :=
  A.toList.foldl flip u

private abbrev Cell (A : Finset (Fin 9)) (x u : Q 9) : Prop :=
  ∀ i ∉ A, u i = x i

private theorem mem_diff (u v : Q 9) (i : Fin 9) :
    i ∈ differingAxes u v ↔ u i ≠ v i := by
  simp [differingAxes]

private theorem diff_subset {A : Finset (Fin 9)} {x u v : Q 9}
    (hu : Cell A x u) (hv : Cell A x v) : differingAxes u v ⊆ A := by
  intro i hi
  by_contra hn
  exact (mem_diff u v i).mp hi ((hu i hn).trans (hv i hn).symm)

private theorem flip_cell {A : Finset (Fin 9)} {x u : Q 9} {i : Fin 9}
    (hu : Cell A x u) (hi : i ∈ A) : Cell A x (flip u i) := by
  intro k hk
  have hki : k ≠ i := fun h => hk (h.symm ▸ hi)
  simpa [BalancedCriticalSpectrum.flip, hki] using hu k hk

private theorem antipode_cell {A : Finset (Fin 9)} {x u : Q 9}
    (hu : Cell A x u) : Cell A x (antipode A u) := by
  intro i hi
  change A.toList.foldl flip u i = x i
  rw [foldl_flip_apply _ (Finset.nodup_toList _), ite_eq_right (fun h => hi (Finset.mem_toList.mp h))]
  exact hu i hi

private theorem diff_flip_left (u v : Q 9) (i : Fin 9) :
    differingAxes (flip u i) v =
      if i ∈ differingAxes u v then (differingAxes u v).erase i
      else insert i (differingAxes u v) := by
  classical
  ext k
  by_cases hki : k = i
  · subst k
    have hf : (flip u i i ≠ v i) ↔ ¬ (u i ≠ v i) := by
      rw [flip_apply_same]
      cases u i <;> cases v i <;> decide
    rw [mem_diff (flip u i) v i, hf, ← mem_diff u v i]
    by_cases hi : i ∈ differingAxes u v <;> simp [hi]
  · have he : flip u i k = u k := by simp [BalancedCriticalSpectrum.flip, hki]
    by_cases hi : i ∈ differingAxes u v
    · rw [ite_eq_left hi, Finset.mem_erase, mem_diff (flip u i) v k, mem_diff u v k, he]
      simp [hki]
    · rw [ite_eq_right hi, Finset.mem_insert, mem_diff (flip u i) v k, mem_diff u v k, he]
      simp [hki]

private theorem diff_single (u : Q 9) (i : Fin 9) :
    differingAxes u (flip u i) = {i} := by
  simpa using differingAxes_foldl_flip [i] (by simp) u

private theorem diff_pair (u : Q 9) {i j : Fin 9} (hij : i ≠ j) :
    differingAxes u (flip (flip u i) j) = {i, j} := by
  simpa using differingAxes_foldl_flip [i, j] (by simp [hij]) u

private theorem dist_flip_pair (u : Q 9) {i j k : Fin 9}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    hammingDist (flip u k) (flip (flip u i) j) = 3 := by
  change (differingAxes (flip u k) (flip (flip u i) j)).card = 3
  rw [diff_flip_left, diff_pair u hij, ite_eq_right (by simp [hki, hkj]),
    Finset.card_insert_of_notMem (by simp [hki, hkj]), Finset.card_pair hij]

private theorem distance_to_antipode {A : Finset (Fin 9)} {u v : Q 9}
    (h : differingAxes u v ⊆ A) :
    hammingDist u (antipode A v) + hammingDist u v = A.card := by
  change (differingAxes u (antipode A v)).card + (differingAxes u v).card = A.card
  rw [differingAxes_flip_cell A u v h, Finset.card_sdiff_add_card_eq_card h]

/-- A row three flips from a vertex of the matched slice sees no exterior-axis
contributions. The parity condition is on the row itself. -/
private theorem isolated_row
    {C D : Finset (Q 9)} {b : Bool} {d : ℕ} {A : Finset (Fin 9)} {x u w : Q 9}
    (hsep : ∀ p ∈ C, ∀ q ∈ D, d ≤ hammingDist p q)
    (hA : A.card = d + 2) (hfamily : minimumDisplacements C D b d = A.powersetCard d)
    (hu : Cell A x u) (hw : Cell A x w) (hub : parity u = !b)
    (hwD : antipode A w ∈ D) (hdist : hammingDist u w = 3) :
    u ∉ C ∧ directions C u ⊆ A := by
  have hc := distance_to_antipode (diff_subset hu hw)
  have hshort : hammingDist u (antipode A w) + 1 = d := by omega
  have hvc := antipode_cell hw
  refine ⟨?_, ?_⟩
  · intro huC
    have := hsep u huC _ hwD
    omega
  · intro i hi
    by_contra hia
    have hni : i ∉ differingAxes u (antipode A w) :=
      fun h => hia (diff_subset hu hvc h)
    have hflip : differingAxes (flip u i) (antipode A w) =
        insert i (differingAxes u (antipode A w)) := by
      rw [diff_flip_left, ite_eq_right hni]
    have hd : hammingDist (flip u i) (antipode A w) = d := by
      change (differingAxes (flip u i) (antipode A w)).card = d
      rw [hflip, Finset.card_insert_of_notMem hni]
      exact hshort
    have hp : parity (flip u i) = b := by rw [parity_flip, hub, Bool.not_not]
    have hm := mem_minimumDisplacements.mpr
      ⟨flip u i, (mem_directions C u i).mp hi, antipode A w, hwD, hp, hd, hflip⟩
    rw [hfamily] at hm
    exact hia ((Finset.mem_powersetCard.mp hm).1 (Finset.mem_insert_self _ _))

open Classical in
/-- The local signed equation at the double-flip corner identifies the two
contributions at the center of the same coordinate square. -/
private theorem center_terms_eq {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (z : Q 9) {i j : Fin 9} (hij : i ≠ j)
    (hQ : flip (flip z i) j ∉ C)
    (hN : directions C (flip (flip z i) j) = {i, j}) :
    edge z i * σ (flip z i) = edge z j * σ (flip z j) := by
  let q := flip (flip z i) j
  have hqi : flip q i = flip z j := by
    dsimp only [q]
    rw [flip_comm z i j, BalancedCriticalSpectrum.flip_flip]
  have hqj : flip q j = flip z i := flip_flip _ _
  have hsum := fullRow_zero hr hs q hQ
  have hrow : edge q j * σ (flip z i) = -(edge q i * σ (flip z j)) := by
    change (∑ k ∈ directions C q, edge q k * σ (flip q k)) = 0 at hsum
    rw [show directions C q = {i, j} from hN, Finset.sum_pair hij, hqi, hqj] at hsum
    linarith only [hsum]
  have hrecj : edge q j = edge (flip z i) j := edge_reciprocal (flip z i) j
  have hreci : edge q i = edge (flip z j) i := by
    dsimp only [q]
    rw [flip_comm z i j, edge_reciprocal]
  have hcurv : edge z i * edge q j = -(edge z j * edge q i) := by
    rw [hrecj, hreci]
    exact edge_curvature z hij
  calc
    edge z i * σ (flip z i) = edge z i * edge q j ^ 2 * σ (flip z i) := by
      rw [edge_sq, mul_one]
    _ = (edge z i * edge q j) * (edge q j * σ (flip z i)) := by ring
    _ = (-(edge z j * edge q i)) * (-(edge q i * σ (flip z j))) := by rw [hcurv, hrow]
    _ = edge z j * edge q i ^ 2 * σ (flip z j) := by ring
    _ = edge z j * σ (flip z j) := by rw [edge_sq, mul_one]

open Classical in
/-- Aligned, unit signed contributions on the prescribed axes use at least
as many further directions at an exterior row. -/
private theorem center_axis_bound {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C σ) (A : Finset (Fin 9)) (z : Q 9) (hz : z ∉ C)
    (hA : A.Nonempty) (hleaf : ∀ i ∈ A, flip z i ∈ C)
    (halign : ∀ i ∈ A, ∀ j ∈ A, edge z i * σ (flip z i) = edge z j * σ (flip z j)) :
    A.card + A.card ≤ 9 := by
  classical
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
  obtain ⟨i, hi⟩ := hA
  let s := edge z i * σ (flip z i)
  have hsunit : |s| = 1 := by
    have hm := SupportedEigenSaturation.matrix_abs_of_adj (flip_adj z i)
    rcases hs.1 _ (hleaf i hi) with h | h <;> simp [s, edge, h, hm]
  have hfrag : |signedFragment K σ z| = (A.card : ℝ) := by
    have hsum : signedFragment K σ z = (A.card : ℝ) * s := by
      change (∑ j ∈ directions K z, edge z j * σ (flip z j)) = _
      rw [hdirs]
      calc
        _ = ∑ _j ∈ A, s := Finset.sum_congr rfl (fun j hj => halign j hj i hi)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum, abs_mul, hsunit, mul_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ A.card)]
  have hbound := card_add_abs_le hKC hr hs z hz
  rw [hdirs, hfrag] at hbound
  have hn : A.card + A.card ≤ (directions C z).card := by exact_mod_cast hbound
  exact hn.trans (by simpa using Finset.card_le_univ (directions C z))

private theorem axis_of_flip_in_cell {A : Finset (Fin 9)} {x u : Q 9} {i : Fin 9}
    (hu : Cell A x u) (hv : Cell A x (flip u i)) : i ∈ A :=
  diff_subset hu hv (by rw [diff_single]; exact Finset.mem_singleton_self i)

set_option maxHeartbeats 1000000 in
open Classical in
/-- A tight contact cell consists, on the contacting parity, of the full star on
the tight axes. The opposite component's matching slice is its cell antipode.
The signed boundary at the center requires twice as many axes as the star uses. -/
theorem tight_contact_cell_full_star
    {C D : Finset (Q 9)} {b : Bool} {d : ℕ} {A : Finset (Fin 9)} {x y : Q 9}
    (hd : 2 ≤ d) (hsep : ∀ u ∈ C, ∀ v ∈ D, d ≤ hammingDist u v)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hC : ∀ i, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0))
    (hD : ∀ c, ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = c) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0))
    (hA : A.card = d + 2) (hfamily : minimumDisplacements C D b d = A.powersetCard d)
    (hx : x ∈ C) (hy : y ∈ D) (hxb : parity x = b) (hxy : hammingDist x y = d) :
    A.card + A.card ≤ 9 ∧ ∃ z : Q 9,
      (∀ i ∉ A, z i = x i) ∧ parity z = !b ∧ z ∉ C ∧
      (∀ u, parity u = b → (∀ i ∉ A, u i = x i) →
        (u ∈ C ↔ ∃ i ∈ A, flip z i = u)) ∧
      (∀ v, parity (A.toList.foldl flip v) = b → (∀ i ∉ A, v i = x i) →
        (v ∈ D ↔ ∃ i ∈ A, A.toList.foldl flip (flip z i) = v)) := by
  classical
  let T := differingAxes x y
  have hT : T ⊆ A := by
    have hm : T ∈ minimumDisplacements C D b d :=
      mem_minimumDisplacements.mpr ⟨x, hx, y, hy, hxb, hxy, rfl⟩
    rw [hfamily] at hm
    exact (Finset.mem_powersetCard.mp hm).1
  have hxc : Cell A x x := fun _ _ => rfl
  have hyc : Cell A x y := by
    intro i hi
    by_contra hne
    exact hi (hT ((mem_diff x y i).mpr (Ne.symm hne)))
  have hpos : 0 < d := by omega
  obtain ⟨_, hcomp⟩ :=
    minimum_contact_flip_complement hpos hsep hC hD hA hfamily hx hy hxb hxy (T := T) rfl
  dsimp only at hcomp
  have hcomp_eq : (A \ T).toList.foldl flip x = antipode A y :=
    differingAxes_right_inj (hcomp.2.2.2.2.2.1.trans (differingAxes_flip_cell A x y hT).symm)
  have hyab : parity (antipode A y) = b := hcomp_eq ▸ hcomp.2.2.1
  let E := fun u : Q 9 => u ∈ C ∧ parity u = b ∧ Cell A x u
  have hmatch (u : Q 9) (hub : parity u = b) (huc : Cell A x u) :
      u ∈ C ↔ antipode A u ∈ D := by
    constructor
    · intro hu
      exact (minimum_contact_cell_antipodes hpos hsep hC hD hA hfamily hu hy hub hyab
        (fun i hi => (huc i hi).trans (hyc i hi).symm)).2
    · intro hu
      have hui : parity (antipode A (antipode A u)) = b := by
        change parity (A.toList.foldl flip (A.toList.foldl flip u)) = b
        rw [flip_cell_involution, hub]
      have huc' := antipode_cell huc
      have he := (minimum_contact_cell_antipodes hpos hsep hC hD hA hfamily hx hu hxb hui
        (fun i hi => (huc' i hi).symm)).1
      rwa [flip_cell_involution] at he
  have hpair (u v : Q 9) (hu : E u) (hv : E v) (hne : u ≠ v) :
      hammingDist u v = 2 := by
    have hc := distance_to_antipode (diff_subset hu.2.2 hv.2.2)
    have hs := hsep u hu.1 _ ((hmatch v hv.2.1 hv.2.2).mp hv.1)
    have h0 : hammingDist u v ≠ 0 := fun he => hne (hammingDist_eq_zero.mp he)
    have h1 : hammingDist u v ≠ 1 := fun he =>
      cubeParity_ne_of_adj (show (hypercube 9).Adj u v from he) (hu.2.1.trans hv.2.1.symm)
    omega
  have hlocal (u w : Q 9) (huc : Cell A x u) (hub : parity u = !b) (hw : E w)
      (huw : hammingDist u w = 3) : u ∉ C ∧ directions C u ⊆ A :=
    isolated_row hsep hA hfamily huc hw.2.2 hub ((hmatch w hw.2.1 hw.2.2).mp hw.1) huw
  let N := fun u : Q 9 => directions C u ∩ A
  have hN {u : Q 9} (huc : Cell A x u) (hub : parity u = !b) {i : Fin 9} :
      i ∈ N u ↔ E (flip u i) ∧ i ∈ A := by
    change i ∈ directions C u ∩ A ↔ _
    rw [Finset.mem_inter, mem_directions]
    have hp : parity (flip u i) = b := by rw [parity_flip, hub, Bool.not_not]
    exact ⟨fun ⟨hi, hia⟩ => ⟨⟨hi, hp, flip_cell huc hia⟩, hia⟩,
      fun ⟨hi, hia⟩ => ⟨hi.1, hia⟩⟩
  have hmiss {u w : Q 9} (huc : Cell A x u) (hub : parity u = !b)
      (hw : E w) (hfar : hammingDist u w ≠ 1) :
      ∀ i ∈ N u, (differingAxes u w).card = 3 ∧ i ∈ differingAxes u w := by
    intro i hi
    have hne : flip u i ≠ w := fun he =>
      hfar (show hammingDist u w = 1 from he ▸ flip_adj u i)
    have he := hpair (flip u i) w ((hN huc hub).mp hi).1 hw hne
    change (differingAxes (flip u i) w).card = 2 at he
    rw [diff_flip_left] at he
    by_cases hm : i ∈ differingAxes u w
    · rw [ite_eq_left hm] at he
      have hc := Finset.card_erase_add_one hm
      exact ⟨by omega, hm⟩
    · rw [ite_eq_right hm, Finset.card_insert_of_notMem hm] at he
      exact (hfar (show (differingAxes u w).card = 1 by omega)).elim

  -- A row with three slice neighbors cannot miss any point of the slice.
  have hcover_of_three {u : Q 9} (huc : Cell A x u) (hub : parity u = !b)
      (h3 : 3 ≤ (N u).card) : ∀ w, E w → hammingDist u w = 1 := by
    intro w hw
    by_contra hfar
    have hm := hmiss huc hub hw hfar
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (N u).card by omega)
    have hc := (hm i hi).1
    have hle := Finset.card_le_card (show N u ⊆ differingAxes u w from fun j hj => (hm j hj).2)
    obtain ⟨huC, haxes⟩ := hlocal u w huc hub hw hc
    obtain ⟨n, hn⟩ := exterior_even C hr hb u huC
    have heq : N u = directions C u := Finset.inter_eq_left.mpr haxes
    rw [← heq] at hn
    omega
  have hxE : E x := ⟨hx, hxb, hxc⟩
  let x' := antipode A y
  have hx'E : E x' := ⟨by change antipode A y ∈ C; rw [← hcomp_eq]; exact hcomp.1, hyab, antipode_cell hyc⟩
  have hx'x : hammingDist x x' = 2 := by
    have hc := distance_to_antipode hT
    change hammingDist x x' + hammingDist x y = A.card at hc
    omega
  obtain ⟨z, hzc, hzb, hcover⟩ :
      ∃ z, Cell A x z ∧ parity z = !b ∧ (∀ w, E w → hammingDist z w = 1) := by
    obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp
      (show (differingAxes x x').card = 2 from hx'x)
    have ha := diff_subset hxc hx'E.2.2
    have hi : i ∈ A := ha (by rw [he]; simp)
    have hj : j ∈ A := ha (by rw [he]; simp)
    let z := flip x i
    have hzc : Cell A x z := flip_cell hxc hi
    have hzb : parity z = !b := by simp only [z, parity_flip, hxb]
    have hzi : flip z i = x := flip_flip x i
    have hzj : flip z j = x' := differingAxes_right_inj ((diff_pair x hij).trans he.symm)
    have hni : i ∈ N z := (hN hzc hzb).mpr ⟨hzi.symm ▸ hxE, hi⟩
    have hnj : j ∈ N z := (hN hzc hzb).mpr ⟨hzj.symm ▸ hx'E, hj⟩
    by_cases hall : ∀ w, E w → hammingDist z w = 1
    · exact ⟨z, hzc, hzb, hall⟩
    · push Not at hall
      obtain ⟨w, hw, hfar⟩ := hall
      have hmi := hmiss hzc hzb hw hfar i hni
      have hmj := hmiss hzc hzb hw hfar j hnj
      let z' := flip (flip z i) j
      have hz'c : Cell A x z' := flip_cell (flip_cell hzc hi) hj
      have hz'b : parity z' = !b := by simp only [z', parity_flip, Bool.not_not, hzb]
      have hdi : differingAxes (flip z i) w = (differingAxes z w).erase i := by
        rw [diff_flip_left, ite_eq_left hmi.2]
      have hdj : j ∈ differingAxes (flip z i) w := by
        rw [hdi]
        exact Finset.mem_erase.mpr ⟨hij.symm, hmj.2⟩
      have hwz' : hammingDist z' w = 1 := by
        change (differingAxes (flip (flip z i) j) w).card = 1
        rw [diff_flip_left, ite_eq_left hdj]
        have hcj := Finset.card_erase_add_one hdj
        rw [hdi] at hcj ⊢
        have hci := Finset.card_erase_add_one hmi.2
        have hc := hmi.1
        omega
      obtain ⟨k, hkw⟩ := adjacent_exists_flip (show (hypercube 9).Adj z' w from hwz')
      have hk : flip z' k = w := hkw.symm
      have hki' : flip z' i = flip z j := by
        dsimp only [z']
        rw [flip_comm z i j, BalancedCriticalSpectrum.flip_flip]
      have hkj' : flip z' j = flip z i := flip_flip _ _
      have hki : k ≠ i := by
        intro heq
        have hwj : w = flip z j := hk.symm.trans ((congrArg (flip z') heq).trans hki')
        exact hfar (by rw [hwj]; exact flip_adj z j)
      have hkj : k ≠ j := by
        intro heq
        have hwi : w = flip z i := hk.symm.trans ((congrArg (flip z') heq).trans hkj')
        exact hfar (by rw [hwi]; exact flip_adj z i)
      have hka : k ∈ A := axis_of_flip_in_cell hz'c (hk.symm ▸ hw.2.2)
      have hni' : i ∈ N z' := (hN hz'c hz'b).mpr ⟨(hki'.trans hzj).symm ▸ hx'E, hi⟩
      have hnj' : j ∈ N z' := (hN hz'c hz'b).mpr ⟨(hkj'.trans hzi).symm ▸ hxE, hj⟩
      have hnk' : k ∈ N z' := (hN hz'c hz'b).mpr ⟨hk.symm ▸ hw, hka⟩
      have hc : ({i, j, k} : Finset (Fin 9)).card = 3 :=
        Finset.card_triple_eq_three_iff.mpr ⟨hij, hki.symm, hkj.symm⟩
      have hsub : ({i, j, k} : Finset (Fin 9)) ⊆ N z' := by
        intro r h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl
        · exact hni'
        · exact hnj'
        · exact hnk'
      exact ⟨z', hz'c, hz'b, hcover_of_three hz'c hz'b (hc ▸ Finset.card_le_card hsub)⟩
  have hstar (w : Q 9) : E w ↔ ∃ i ∈ N z, flip z i = w := by
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := adjacent_exists_flip (show (hypercube 9).Adj z w from hcover w hw)
      exact ⟨i, (hN hzc hzb).mpr ⟨hw, axis_of_flip_in_cell hzc hw.2.2⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ((hN hzc hzb).mp hi).1
  have hrow {i j k : Fin 9} (hi : i ∈ A) (hj : j ∈ A) (hk : k ∈ N z)
      (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
      let q := flip (flip z i) j
      q ∉ C ∧ ∀ r, r ∈ directions C q ↔ (r = j ∧ i ∈ N z) ∨ (r = i ∧ j ∈ N z) := by
    let q := flip (flip z i) j
    have hqc : Cell A x q := flip_cell (flip_cell hzc hi) hj
    have hqb : parity q = !b := by simp only [q, parity_flip, Bool.not_not, hzb]
    have heq : hammingDist q (flip z k) = 3 :=
      (hammingDist_comm q (flip z k)).trans (dist_flip_pair z hij hki hkj)
    obtain ⟨hqC, haxes⟩ := hlocal q (flip z k) hqc hqb ((hN hzc hzb).mp hk).1 heq
    have hqi : flip q i = flip z j := by
      dsimp only [q]
      rw [flip_comm z i j, BalancedCriticalSpectrum.flip_flip]
    have hqj : flip q j = flip z i := flip_flip _ _
    refine ⟨hqC, fun r => ⟨?_, ?_⟩⟩
    · intro hrq
      have hrN : r ∈ N q := Finset.mem_inter.mpr ⟨hrq, haxes hrq⟩
      obtain ⟨l, hl, he⟩ := (hstar (flip q r)).mp ((hN hqc hqb).mp hrN).1
      by_cases hli : l = i
      · subst l
        exact Or.inl ⟨flip_injective q (he.symm.trans hqj.symm), hl⟩
      · by_cases hlj : l = j
        · subst l
          exact Or.inr ⟨flip_injective q (he.symm.trans hqi.symm), hl⟩
        · have hd3 := dist_flip_pair z hij hli hlj
          change hammingDist (flip z l) q = 3 at hd3
          have hd1 : hammingDist (flip z l) q = 1 := by rw [he]; exact (flip_adj q r).symm
          omega
    · rintro (⟨he, hrn⟩ | ⟨he, hrn⟩)
      · rw [he, mem_directions, hqj]
        exact ((hN hzc hzb).mp hrn).1.1
      · rw [he, mem_directions, hqi]
        exact ((hN hzc hzb).mp hrn).1.1
  have hfull : A ⊆ N z := by
    obtain ⟨i, hi, hxi⟩ := (hstar x).mp hxE
    obtain ⟨k, hk, hxk⟩ := (hstar x').mp hx'E
    have hki : k ≠ i := by
      intro he
      have hxe : x = x' := hxi.symm.trans ((congrArg (flip z) he).symm.trans hxk)
      rw [← hxe, hammingDist_self] at hx'x
      omega
    intro j hj
    by_contra hnj
    have hij : i ≠ j := fun he => hnj (he ▸ hi)
    have hkj : k ≠ j := fun he => hnj (he ▸ hk)
    have hia := ((hN hzc hzb).mp hi).2
    obtain ⟨hqC, hq⟩ := hrow hia hj hk hij hki hkj
    have heq : directions C (flip (flip z i) j) = {j} := by
      ext r
      rw [hq]
      simp [hi, hnj]
    have heven := exterior_even C hr hb _ hqC
    rw [heq, Finset.card_singleton] at heven
    obtain ⟨m, hm⟩ := heven
    omega
  have hleaf (i : Fin 9) (hi : i ∈ A) : flip z i ∈ C :=
    ((hN hzc hzb).mp (hfull hi)).1.1
  have hzC : z ∉ C := by
    intro hz
    have hsub : A ⊆ directions C z := fun i hi => (mem_directions C z i).mpr (hleaf i hi)
    have hc := Finset.card_le_card hsub
    rw [regular_directions C hr hz] at hc
    omega
  obtain ⟨σ, hs⟩ := hb
  have halign (i : Fin 9) (hi : i ∈ A) (j : Fin 9) (hj : j ∈ A) :
      edge z i * σ (flip z i) = edge z j * σ (flip z j) := by
    by_cases hij : i = j
    · subst j
      rfl
    · have hne : (A \ ({i, j} : Finset (Fin 9))).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff_of_subset (show ({i, j} : Finset (Fin 9)) ⊆ A by
          intro l hl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl
          · exact hi
          · exact hj), Finset.card_pair hij]
        omega
      obtain ⟨k, hk⟩ := hne
      obtain ⟨hka, hkp⟩ := Finset.mem_sdiff.mp hk
      have hki : k ≠ i := fun he => hkp (by simp [he])
      have hkj : k ≠ j := fun he => hkp (by simp [he])
      obtain ⟨hqC, hq⟩ := hrow hi hj (hfull hka) hij hki hkj
      apply center_terms_eq hr hs z hij hqC
      ext r
      rw [hq]
      simp [hfull hi, hfull hj, or_comm]
  have hbound := center_axis_bound hr hs A z hzC
    (Finset.card_pos.mp (show 0 < A.card by omega)) hleaf halign
  have hstarA (u : Q 9) (hub : parity u = b) (huc : Cell A x u) :
      u ∈ C ↔ ∃ i ∈ A, flip z i = u := by
    constructor
    · intro hu
      obtain ⟨i, hi, he⟩ := (hstar u).mp ⟨hu, hub, huc⟩
      exact ⟨i, ((hN hzc hzb).mp hi).2, he⟩
    · rintro ⟨i, hi, rfl⟩
      exact hleaf i hi
  refine ⟨hbound, z, hzc, hzb, hzC, hstarA, ?_⟩
  intro v hvb hvc
  have hu := antipode_cell hvc
  constructor
  · intro hv
    have hv' : antipode A (antipode A v) ∈ D := by
      change A.toList.foldl flip (A.toList.foldl flip v) ∈ D
      rwa [flip_cell_involution]
    obtain ⟨i, hi, he⟩ := (hstarA _ hvb hu).mp ((hmatch _ hvb hu).mpr hv')
    refine ⟨i, hi, ?_⟩
    change antipode A (flip z i) = v
    rw [he]
    exact flip_cell_involution A v
  · rintro ⟨i, hi, rfl⟩
    have huc : Cell A x (flip z i) := flip_cell hzc hi
    have hub : parity (flip z i) = b := by rw [parity_flip, hzb, Bool.not_not]
    exact (hmatch _ hub huc).mp (hleaf i hi)

open Classical in
/-- At every starting parity that realizes the minimum distance d ≥ 3, the
displacement count strictly exceeds the tight binomial count. -/
theorem minimum_displacements_card_strict
    {C D : Finset (Q 9)} {b : Bool} {d : ℕ}
    (hd : 3 ≤ d) (hsep : ∀ u ∈ C, ∀ v ∈ D, d ≤ hammingDist u v)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hne : (minimumDisplacements C D b d).Nonempty)
    (hC : ∀ i, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0))
    (hD : ∀ c, ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = c) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)) :
    (d + 2).choose 2 < (minimumDisplacements C D b d).card := by
  obtain ⟨hlo, htight⟩ :=
    minimum_displacements_card_and_equality C D b d (by omega) hsep hne hC hD
  by_contra hn
  have he : (minimumDisplacements C D b d).card = (d + 2).choose 2 := by omega
  obtain ⟨A, hA, hfamily⟩ := htight he
  obtain ⟨T, hT⟩ := hne
  obtain ⟨x, hx, y, hy, hxb, hxy, _⟩ := mem_minimumDisplacements.mp hT
  have hbound := (tight_contact_cell_full_star (by omega) hsep hr hb hC hD hA hfamily
    hx hy hxb hxy).1
  omega

open Classical in
/-- The strict count applies to a fixed component pair whose weighted signed
defects are singular on the initial parity used by the component construction. -/
theorem minimum_displacements_card_strict_of_signed_defect
    {C D : Finset (Q 9)} {b : Bool} {d : ℕ}
    (hd : 3 ≤ d) (hsep : ∀ u ∈ C, ∀ v ∈ D, d ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hne : (minimumDisplacements C D b d).Nonempty) :
    (d + 2).choose 2 < (minimumDisplacements C D b d).card := by
  apply minimum_displacements_card_strict hd hsep hrC hbC hne
  · intro i
    let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
    have hw (k : Fin 9) : 0 < w k := by
      dsimp only [w]
      split <;> norm_num
    exact exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b
  · intro c
    let w : Fin 9 → ℝ := fun _ => 1
    exact exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD w
      (fun _ => by norm_num [w]) (hdetD w) c

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
