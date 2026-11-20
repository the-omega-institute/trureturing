/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CubeEvenMinimumSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CubeEvenMinimumSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Small singleton-free parity supports in even cubes are full neighborhoods. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
import Batteries.Tactic.OpenPrivate

/-! Minimum singleton-free parity supports in even-dimensional Boolean cubes. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CubeEvenMinimumSupport

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip_adj)
open private diff diff_flip directions_covered from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_symm diff_triangle_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private cubeParity huangMatrix huang_energy from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_support from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private even_diff_of_parity_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangUnitSupportGap
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

private def twoPartners {n : ℕ} (S : Finset (Q n)) (x : Q n) : Finset (Q n) :=
  S.filter (fun z => (diff x z).card = 2)

private theorem self_not_partner {n : ℕ} (S : Finset (Q n)) (x : Q n) :
    x ∉ twoPartners S x := by
  simp [twoPartners, diff]

open Classical in
private theorem partner_cover {n : ℕ} (S : Finset (Q n))
    (hno : ∀ y : Q n, (S.filter (fun z => (hypercube n).Adj y z)).card ≠ 1)
    {x : Q n} (hx : x ∈ S) :
    Finset.univ ⊆ (twoPartners S x).biUnion (diff x) := by
  intro i hi
  obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp (directions_covered S hno hx hi)
  obtain ⟨hzx, hdist⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_biUnion.mpr
    ⟨z, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hzx).2, hdist⟩, hiz⟩

private theorem card_biUnion_le_twice {α β : Type*} [DecidableEq β]
    (B : Finset α) (E : α → Finset β) (hE : ∀ v ∈ B, (E v).card ≤ 2) :
    (B.biUnion E).card ≤ 2 * B.card := by
  calc
    _ ≤ ∑ v ∈ B, (E v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ B, 2 := Finset.sum_le_sum hE
    _ = _ := by simp [Nat.mul_comm]

-- If the union attains the counting bound, each member has size two
-- and shares no element with the union of the other members.
private theorem tight_pair_union {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : Finset α) (E : α → Finset β)
    (hE : ∀ v ∈ B, (E v).card ≤ 2) (htight : 2 * B.card ≤ (B.biUnion E).card)
    {w : α} (hw : w ∈ B) :
    (E w).card = 2 ∧ Disjoint (E w) ((B.erase w).biUnion E) := by
  have herase := Finset.card_erase_add_one hw
  have hrest := card_biUnion_le_twice (B.erase w) E
    (fun v hv => hE v (Finset.mem_of_mem_erase hv))
  have hunion := Finset.card_union_add_card_inter (E w) ((B.erase w).biUnion E)
  have hsplit : (B.biUnion E) = E w ∪ (B.erase w).biUnion E := by
    rw [← Finset.biUnion_insert, Finset.insert_erase hw]
  rw [hsplit] at htight
  have hwsize := hE w hw
  refine ⟨by omega, Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp ?_)⟩
  omega

open Classical in
private theorem pair_distance_two {n : ℕ} (hn : 6 ≤ n) (heven : Even n)
    (S : Finset (Q n)) (hcard : S.card ≤ n)
    (hpar : ∀ x ∈ S, ∀ z ∈ S, cubeParity x = cubeParity z)
    (hno : ∀ y : Q n, (S.filter (fun z => (hypercube n).Adj y z)).card ≠ 1)
    {x z : Q n} (hx : x ∈ S) (hz : z ∈ S) (hxz : x ≠ z) :
    (diff x z).card = 2 := by
  classical
  obtain ⟨half, hn_eq⟩ := heven
  let T := twoPartners S
  have hcount (y : Q n) (hy : y ∈ S) : n ≤ 2 * (T y).card := by
    have h := Finset.card_le_card (partner_cover S hno hy)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact h.trans (card_biUnion_le_twice (T y) (diff y)
      (fun v hv => (Finset.mem_filter.mp hv).2.le))
  by_contra hbad
  let A := diff x z
  have hAeven : Even A.card := even_diff_of_parity_eq x z (hpar x hx z hz)
  have hApos : 0 < A.card := hammingDist_pos.mpr hxz
  obtain ⟨a, ha⟩ := hAeven
  have hAmin : 4 ≤ A.card := by
    change A.card ≠ 2 at hbad
    omega
  have hzX : z ∉ T x := fun h => hbad (Finset.mem_filter.mp h).2
  have hxZ : x ∉ T z := by
    intro h
    apply hbad
    simpa only [diff_symm x z] using (Finset.mem_filter.mp h).2
  let B := T x \ T z
  have hspread : T x ∪ T z ⊆ (S.erase x).erase z := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_erase.mpr
        ⟨fun h => hzX (h ▸ hv), Finset.mem_erase.mpr
          ⟨fun h => self_not_partner S x (h ▸ hv), (Finset.mem_filter.mp hv).1⟩⟩
    · exact Finset.mem_erase.mpr
        ⟨fun h => self_not_partner S z (h ▸ hv), Finset.mem_erase.mpr
          ⟨fun h => hxZ (h ▸ hv), (Finset.mem_filter.mp hv).1⟩⟩
  have hbudget : 2 * B.card + 4 ≤ n := by
    have h := Finset.card_le_card hspread
    rw [← Finset.card_sdiff_add_card] at h
    have hxcard := Finset.card_erase_add_one hx
    have hzcard := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hxz.symm, hz⟩)
    have hzmin := hcount z hz
    change B.card + (T z).card ≤ ((S.erase x).erase z).card at h
    omega
  have hcommon (v : Q n) (hvx : v ∈ T x) (hvz : v ∈ T z) :
      A.card = 4 ∧ diff x v ⊆ A := by
    have hxv := (Finset.mem_filter.mp hvx).2
    have hzv := (Finset.mem_filter.mp hvz).2
    have htri := diff_triangle_card z v x
    rw [diff_symm z x, diff_symm v x] at htri
    change (diff z v).card + 2 * (A ∩ diff x v).card = A.card + (diff x v).card at htri
    have hinter := Finset.card_le_card
      (Finset.inter_subset_right (s₁ := A) (s₂ := diff x v))
    have heq : A ∩ diff x v = diff x v := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      omega
    refine ⟨by omega, ?_⟩
    intro i hi
    have hit : i ∈ A ∩ diff x v := heq.symm ▸ hi
    exact (Finset.mem_inter.mp hit).1
  have hAcard : A.card = 4 := by
    by_contra hnot
    have hsub : (T x) ⊆ B := by
      intro v hv
      refine Finset.mem_sdiff.mpr ⟨hv, ?_⟩
      intro hvz
      exact hnot (hcommon v hv hvz).1
    have := Finset.card_le_card hsub
    have := hcount x hx
    omega
  let E (v : Q n) := diff x v \ A
  have houtside : Finset.univ \ A ⊆ B.biUnion E := by
    intro i hi
    have hiA := (Finset.mem_sdiff.mp hi).2
    obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp
      (partner_cover S hno hx (Finset.mem_univ i))
    exact Finset.mem_biUnion.mpr
      ⟨v, Finset.mem_sdiff.mpr ⟨hv, fun hvz => hiA ((hcommon v hv hvz).2 hiv)⟩,
        Finset.mem_sdiff.mpr ⟨hiv, hiA⟩⟩
  have houtside_count : n - 4 ≤ (B.biUnion E).card := by
    simpa [Finset.card_sdiff_of_subset (Finset.subset_univ A), hAcard] using
      Finset.card_le_card houtside
  have hE (v : Q n) (hv : v ∈ B) : (E v).card ≤ 2 :=
    (Finset.card_le_card Finset.sdiff_subset).trans_eq
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  have htight : 2 * B.card ≤ (B.biUnion E).card := by omega
  have hBpos : 0 < B.card := by
    have := card_biUnion_le_twice B E hE
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hBpos
  obtain ⟨hwsize, hwdisj⟩ := tight_pair_union B E hE htight hw
  obtain ⟨hwX, hwZ⟩ := Finset.mem_sdiff.mp hw
  have hwfull : E w = diff x w :=
    Finset.eq_of_subset_of_card_le Finset.sdiff_subset
      ((Finset.mem_filter.mp hwX).2.trans hwsize.symm).le
  have hdisj : Disjoint (T w) (T x) := by
    apply Finset.disjoint_left.mpr
    intro v hvw hvx
    have hvw_ne : v ≠ w := fun h => self_not_partner S w (h ▸ hvw)
    have hempty : Disjoint (diff x w) (diff x v) := by
      apply Finset.disjoint_left.mpr
      intro i hiw hiv
      have hiE : i ∈ E w := hwfull.symm ▸ hiw
      have hiA := (Finset.mem_sdiff.mp hiE).2
      have hvB : v ∈ B := Finset.mem_sdiff.mpr
        ⟨hvx, fun hvz => hiA ((hcommon v hvx hvz).2 hiv)⟩
      exact Finset.disjoint_left.mp hwdisj hiE
        (Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_erase.mpr ⟨hvw_ne, hvB⟩, Finset.mem_sdiff.mpr ⟨hiv, hiA⟩⟩)
    have htri := diff_triangle_card w v x
    rw [diff_symm w x, diff_symm v x, Finset.disjoint_iff_inter_eq_empty.mp hempty,
      Finset.card_empty] at htri
    have hwd := (Finset.mem_filter.mp hwX).2
    have hvd := (Finset.mem_filter.mp hvx).2
    have hvwd := (Finset.mem_filter.mp hvw).2
    omega
  have hzW : z ∉ T w := by
    intro h
    exact hwZ (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hwX).1, by simpa only [diff_symm z w] using
        (Finset.mem_filter.mp h).2⟩)
  have hsub : T w ∪ T x ⊆ S.erase z := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_erase.mpr ⟨fun h => hzW (h ▸ hv), (Finset.mem_filter.mp hv).1⟩
    · exact Finset.mem_erase.mpr ⟨fun h => hzX (h ▸ hv), (Finset.mem_filter.mp hv).1⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h
  have hwcount := hcount w (Finset.mem_filter.mp hwX).1
  have hxcount := hcount x hx
  have hzcard := Finset.card_erase_add_one hz
  omega

-- Three intersecting pairs without a common coordinate form a triangle.
private theorem common_direction {α β : Type*} [DecidableEq β]
    (T : Finset α) (f : α → Finset β)
    (hsize : ∀ v ∈ T, (f v).card = 2)
    (hmeet : ∀ v ∈ T, ∀ w ∈ T, (f v ∩ f w).Nonempty)
    (hwide : 3 < (T.biUnion f).card) :
    ∃ i, ∀ v ∈ T, i ∈ f v := by
  classical
  have hT : T.Nonempty := by
    by_contra! h
    rw [h, Finset.biUnion_empty, Finset.card_empty] at hwide
    omega
  obtain ⟨u, hu⟩ := hT
  obtain ⟨a, b, hab, hU⟩ := Finset.card_eq_two.mp (hsize u hu)
  by_cases ha : ∀ v ∈ T, a ∈ f v
  · exact ⟨a, ha⟩
  by_cases hb : ∀ v ∈ T, b ∈ f v
  · exact ⟨b, hb⟩
  push Not at ha hb
  obtain ⟨v, hv, hva⟩ := ha
  obtain ⟨w, hw, hwb⟩ := hb
  obtain ⟨b', hb'⟩ := hmeet u hu v hv
  obtain ⟨a', ha'⟩ := hmeet u hu w hw
  obtain ⟨c, hc⟩ := hmeet v hv w hw
  simp only [Finset.mem_inter, hU, Finset.mem_insert, Finset.mem_singleton] at hb' ha' hc
  have hbv : b ∈ f v := by grind
  have haw : a ∈ f w := by grind
  have hbc : b ≠ c := fun h => hwb (h.symm ▸ hc.2)
  have hac : a ≠ c := fun h => hva (h.symm ▸ hc.1)
  have hV : f v = {b, c} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | h
      · exact hbv
      · simpa only [Finset.mem_singleton.mp h] using hc.1
    · simp [hsize v hv, hbc]
  have hW : f w = {a, c} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | h
      · exact haw
      · simpa only [Finset.mem_singleton.mp h] using hc.2
    · simp [hsize w hw, hac]
  have hsub : T.biUnion f ⊆ {a, b, c} := by
    intro i hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨p, q, hpq, hZ⟩ := Finset.card_eq_two.mp (hsize z hz)
    obtain ⟨iU, hiU⟩ := hmeet z hz u hu
    obtain ⟨iV, hiV⟩ := hmeet z hz v hv
    obtain ⟨iW, hiW⟩ := hmeet z hz w hw
    simp only [Finset.mem_inter, hZ, hU, hV, hW, Finset.mem_insert,
      Finset.mem_singleton] at hiU hiV hiW
    simp only [hZ, Finset.mem_insert, Finset.mem_singleton] at hiz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    clear hsize hmeet
    grind
  have hbound := (Finset.card_le_card hsub).trans Finset.card_le_three
  omega

open Classical in
/-- A nonempty, singleton-free support of at most `n` points in one parity
of an even cube of dimension `n ≥ 6` is a full neighborhood. -/
theorem eq_neighbors_of_no_singleton {n : ℕ} (hn : 6 ≤ n) (heven : Even n)
    (S : Finset (Q n)) (hS : S.Nonempty) (hcard : S.card ≤ n)
    (hpar : ∃ b : Bool, ∀ x ∈ S, cubeParity x = b)
    (hno : ∀ y : Q n, (S.filter (fun z => (hypercube n).Adj y z)).card ≠ 1) :
    ∃ y : Q n, S = Finset.univ.filter (fun z => (hypercube n).Adj y z) := by
  classical
  obtain ⟨b, hb⟩ := hpar
  have hall {x z : Q n} (hx : x ∈ S) (hz : z ∈ S) (hne : x ≠ z) :
      (diff x z).card = 2 :=
    pair_distance_two hn heven S hcard
      (fun v hv w hw => (hb v hv).trans (hb w hw).symm) hno hx hz hne
  obtain ⟨x, hx⟩ := hS
  let T := S.erase x
  have hsize (z : Q n) (hz : z ∈ T) : (diff x z).card = 2 := by
    obtain ⟨hzx, hzS⟩ := Finset.mem_erase.mp hz
    exact hall hx hzS hzx.symm
  have hcover : Finset.univ ⊆ T.biUnion (diff x) := by
    intro i hi
    obtain ⟨z, hz, hiz⟩ := Finset.mem_biUnion.mp (directions_covered S hno hx hi)
    exact Finset.mem_biUnion.mpr ⟨z, (Finset.mem_filter.mp hz).1, hiz⟩
  have hmeet (z : Q n) (hz : z ∈ T) (w : Q n) (hw : w ∈ T) :
      (diff x z ∩ diff x w).Nonempty := by
    have hdist : (diff z w).card ≤ 2 := by
      by_cases he : z = w
      · subst w
        simp [diff]
      · exact (hall (Finset.mem_of_mem_erase hz) (Finset.mem_of_mem_erase hw) he).le
    have htri := diff_triangle_card z w x
    rw [diff_symm z x, diff_symm w x, hsize z hz, hsize w hw] at htri
    exact Finset.card_pos.mp (by omega)
  have hwide : 3 < (T.biUnion (diff x)).card := by
    have hc := Finset.card_le_card hcover
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨i, hi⟩ := common_direction T (diff x) hsize hmeet hwide
  let y := BalancedCriticalSpectrum.flip x i
  have hsub : S ⊆ Finset.univ.filter (fun z => (hypercube n).Adj y z) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_cases hzx : z = x
    · subst z
      exact (flip_adj x i).symm
    · have hzT : z ∈ T := Finset.mem_erase.mpr ⟨hzx, hz⟩
      change (diff (BalancedCriticalSpectrum.flip x i) z).card = 1
      rw [diff_flip, ite_eq_left (hi z hzT), Finset.card_erase_of_mem (hi z hzT), hsize z hzT]
  have hcoverErase :
      Finset.univ ⊆ insert i (T.biUnion (fun z => (diff x z).erase i)) := by
    intro j hj
    by_cases hji : j = i
    · exact Finset.mem_insert.mpr (Or.inl hji)
    · obtain ⟨z, hz, hjz⟩ := Finset.mem_biUnion.mp (hcover hj)
      exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_erase.mpr ⟨hji, hjz⟩⟩))
  have hbi : (T.biUnion (fun z => (diff x z).erase i)).card ≤ T.card := by
    calc
      _ ≤ ∑ z ∈ T, ((diff x z).erase i).card := Finset.card_biUnion_le
      _ = T.card * 1 := Finset.sum_const_nat fun z hz => by
        rw [Finset.card_erase_of_mem (hi z hz), hsize z hz]
      _ = T.card := Nat.mul_one _
  have hlow := (Finset.card_le_card hcoverErase).trans (Finset.card_insert_le _ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hlow
  refine ⟨y, Finset.eq_of_subset_of_card_le hsub ?_⟩
  rw [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree,
    (hypercube_regular n).degree_eq]
  have herase : T.card + 1 = S.card := Finset.card_erase_add_one hx
  omega

#print axioms eq_neighbors_of_no_singleton

private theorem insertNth_flip (i : Fin 9) (b : Bool) (x : Q 8) (j : Fin 8) :
    i.insertNth (α := fun _ => Bool) b (BalancedCriticalSpectrum.flip x j) =
      BalancedCriticalSpectrum.flip (i.insertNth (α := fun _ => Bool) b x) (i.succAbove j) := by
  simp only [BalancedCriticalSpectrum.flip, Fin.insertNth_update, Fin.insertNth_apply_succAbove]

private theorem cubeParity_insertNth (i : Fin 9) (b : Bool) (x : Q 8) :
    cubeParity (i.insertNth (α := fun _ => Bool) b x) = b + cubeParity x := by
  unfold cubeParity
  rw [Fin.sum_univ_succAbove _ i]
  simp

/-- The nonzero support of a binary word on the face where coordinate `i` has value `b`. -/
def binaryFaceSupport (i : Fin 9) (b : Bool) (f : Q 9 → ZMod 2) : Finset (Q 8) :=
  Finset.univ.filter (fun x => f (i.insertNth (α := fun _ => Bool) b x) ≠ 0)

#print axioms binaryFaceSupport

open Classical in
/-- A nonzero one-parity binary kernel word supported on the complement
has more than eight support points on each face it meets, provided every
vertex has at least two selected neighbors in the full cube. -/
private theorem eight_lt_binaryFaceSupport_card (i : Fin 9) (b : Bool)
    (K : Finset (Q 9)) (f : Q 9 → ZMod 2)
    (hK : ∀ x ∈ K, f x = 0)
    (hdegree : ∀ y : Q 9, 2 ≤ (K.filter (fun x => (hypercube 9).Adj y x)).card)
    (hpar : ∃ p : Bool, ∀ x, f x ≠ 0 → cubeParity x = p)
    (hker : ∀ y : Q 9, ∑ j : Fin 8, f (BalancedCriticalSpectrum.flip y (i.succAbove j)) = 0)
    (hne : (binaryFaceSupport i b f).Nonempty) :
    8 < (binaryFaceSupport i b f).card := by
  classical
  let S := binaryFaceSupport i b f
  have hpar' : ∃ p : Bool, ∀ x ∈ S, cubeParity x = p := by
    obtain ⟨p, hp⟩ := hpar
    refine ⟨b + p, ?_⟩
    intro x hx
    have hh := hp _ (Finset.mem_filter.mp hx).2
    rw [cubeParity_insertNth] at hh
    rw [← hh, ← add_assoc, BooleanRing.add_self, zero_add]
  have hno (y : Q 8) : (S.filter (fun x => (hypercube 8).Adj y x)).card ≠ 1 := by
    intro hs
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hs
    have hxmem : x ∈ S.filter (fun x => (hypercube 8).Adj y x) := by
      simp [hx]
    obtain ⟨hxS, hadj⟩ := Finset.mem_filter.mp hxmem
    obtain ⟨j, rfl⟩ := adjacent_exists_flip hadj
    have hrow :
        (∑ k : Fin 8, f (i.insertNth (α := fun _ => Bool) b
          (BalancedCriticalSpectrum.flip y k))) = 0 := by
      simpa only [insertNth_flip] using hker (i.insertNth (α := fun _ => Bool) b y)
    rw [Finset.sum_eq_single j] at hrow
    · exact (Finset.mem_filter.mp hxS).2 hrow
    · intro k _ hkj
      by_contra hne'
      have hkS : BalancedCriticalSpectrum.flip y k ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne'⟩
      have hk : BalancedCriticalSpectrum.flip y k ∈ S.filter (fun x => (hypercube 8).Adj y x) :=
        Finset.mem_filter.mpr ⟨hkS, flip_adj y k⟩
      rw [hx] at hk
      exact hkj (flip_injective y (Finset.mem_singleton.mp hk))
    · simp
  by_contra! hcard
  obtain ⟨y, hy⟩ := eq_neighbors_of_no_singleton (by decide) (by decide) S hne hcard hpar' hno
  let Y := i.insertNth (α := fun _ => Bool) b y
  have htwo : 1 < (K.filter (fun x => (hypercube 9).Adj Y x)).card := hdegree Y
  obtain ⟨z, hz, hzi⟩ := Finset.exists_mem_ne htwo (BalancedCriticalSpectrum.flip Y i)
  obtain ⟨hzK, hzadj⟩ := Finset.mem_filter.mp hz
  obtain ⟨k, hk⟩ := adjacent_exists_flip hzadj
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
  · exact hzi hk
  · have hj : BalancedCriticalSpectrum.flip y j ∈ S := by
      rw [hy]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, flip_adj y j⟩
    have he := (Finset.mem_filter.mp hj).2
    rw [insertNth_flip, ← hk] at he
    exact he (hK z hzK)

#print axioms eight_lt_binaryFaceSupport_card

-- The half-flip in direction zero is a right inverse on the binary kernel.
private theorem binary_preimage (f : Q 8 → ZMod 2)
    (hker : ∀ x, ∑ j : Fin 8, f (BalancedCriticalSpectrum.flip x j) = 0) :
    ∃ g : Q 8 → ZMod 2, ∀ x, ∑ j : Fin 8, g (BalancedCriticalSpectrum.flip x j) = f x := by
  classical
  let g (x : Q 8) := if x 0 then f (BalancedCriticalSpectrum.flip x 0) else 0
  refine ⟨g, fun x => ?_⟩
  have hmem : (0 : Fin 8) ∈ Finset.univ := Finset.mem_univ _
  cases hx : x 0
  · calc
      _ = g (BalancedCriticalSpectrum.flip x 0) := by
        apply Finset.sum_eq_single_of_mem 0 hmem
        intro j _ hj
        simp [g, BalancedCriticalSpectrum.flip, Function.update_of_ne (Ne.symm hj), hx]
      _ = f x := by simp [g, hx]
  · have hw := hker (BalancedCriticalSpectrum.flip x 0)
    rw [← Finset.sum_erase_add _ _ hmem, BalancedCriticalSpectrum.flip_flip] at hw
    rw [← Finset.sum_erase_add _ _ hmem]
    have hreindex :
        (∑ j ∈ Finset.univ.erase (0 : Fin 8), g (BalancedCriticalSpectrum.flip x j)) =
          ∑ j ∈ Finset.univ.erase (0 : Fin 8),
            f (BalancedCriticalSpectrum.flip (BalancedCriticalSpectrum.flip x 0) j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hn := (Finset.mem_erase.mp hj).1
      have hb : BalancedCriticalSpectrum.flip x j 0 = true := by
        simpa [BalancedCriticalSpectrum.flip, Function.update_of_ne (Ne.symm hn)] using hx
      simp only [g, hb, ite_true, flip_comm x j 0]
    rw [hreindex, show g (BalancedCriticalSpectrum.flip x 0) = 0 by simp [g, hx], add_zero]
    exact (show ∀ a b : ZMod 2, a + b = 0 → a = b by decide) _ _ hw

-- Lift through signed Huang adjacency. An integer square modulo four
-- records whether its base is nonzero modulo two, while Huang's energy
-- identity makes the sum of the squares divisible by eight.
private theorem four_dvd_binary_support (f : Q 8 → ZMod 2)
    (hker : ∀ x, ∑ j : Fin 8, f (BalancedCriticalSpectrum.flip x j) = 0) :
    4 ∣ (Finset.univ.filter (fun x => f x ≠ 0)).card := by
  classical
  obtain ⟨g, hg⟩ := binary_preimage f hker
  let H (x y : Q 8) : ℤ := ⌊huangMatrix 8 x y⌋
  let G (y : Q 8) : ℤ := (g y).val
  let t (x : Q 8) : ℤ := ∑ y, H x y * G y
  have hreal (x y : Q 8) : (H x y : ℝ) = huangMatrix 8 x y := by
    have hs := matrix_support x y
    by_cases ha : (hypercube 8).Adj x y
    · rw [ite_eq_left ha] at hs
      rcases eq_or_eq_neg_of_abs_eq hs with h | h <;> norm_num [H, h]
    · rw [ite_eq_right ha] at hs
      norm_num [H, abs_eq_zero.mp hs]
  have hbinary (x y : Q 8) :
      (H x y : ZMod 2) = if (hypercube 8).Adj x y then 1 else 0 := by
    have hs := matrix_support x y
    by_cases ha : (hypercube 8).Adj x y
    · rw [ite_eq_left ha] at hs ⊢
      rcases eq_or_eq_neg_of_abs_eq hs with h | h
      · norm_num [H, h]
      · change (⌊huangMatrix 8 x y⌋ : ZMod 2) = 1
        rw [h, show ⌊(-1 : ℝ)⌋ = (-1 : ℤ) by norm_num]
        decide
    · rw [ite_eq_right ha] at hs ⊢
      norm_num [H, abs_eq_zero.mp hs]
  have hred (x : Q 8) : (t x : ZMod 2) = f x := by
    have hadj : (Finset.univ : Finset (Fin 8)).image (BalancedCriticalSpectrum.flip x) =
        Finset.univ.filter (fun y => (hypercube 8).Adj x y) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · rintro ⟨j, rfl⟩
        exact flip_adj x j
      · intro hy
        obtain ⟨j, hj⟩ := adjacent_exists_flip hy
        exact ⟨j, hj.symm⟩
    calc
      _ = ∑ y, (if (hypercube 8).Adj x y then (1 : ZMod 2) else 0) * g y := by
        simp [t, G, hbinary]
      _ = ∑ y ∈ Finset.univ.filter (fun y => (hypercube 8).Adj x y), g y := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y _
        split <;> simp_all
      _ = ∑ j : Fin 8, g (BalancedCriticalSpectrum.flip x j) := by
        rw [← hadj, Finset.sum_image (fun _ _ _ _ he => flip_injective x he)]
      _ = f x := hg x
  have henergy : (∑ x, t x ^ 2) = 8 * ∑ x, G x ^ 2 := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    convert huang_energy 8 (fun x => (G x : ℝ)) using 1
    simp only [t, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hreal]
  have hsq (x : Q 8) : (t x : ZMod 4) ^ 2 = if f x ≠ 0 then 1 else 0 := by
    by_cases hx : f x = 0
    · obtain ⟨a, ha⟩ := ZMod.intCast_eq_zero_iff_even.mp ((hred x).trans hx)
      simp only [hx, ne_eq, not_true_eq_false, ite_false, ha, Int.cast_add]
      exact (show ∀ a : ZMod 4, (a + a) ^ 2 = 0 by decide) _
    · have hx1 : f x = 1 := (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) _ hx
      obtain ⟨a, ha⟩ := ZMod.intCast_eq_one_iff_odd.mp ((hred x).trans hx1)
      rw [ite_eq_left hx, ha]
      push_cast
      exact (show ∀ a : ZMod 4, (2 * a + 1) ^ 2 = 1 by decide) _
  apply (ZMod.natCast_eq_zero_iff _ 4).mp
  calc
    _ = ∑ x, (if f x ≠ 0 then (1 : ZMod 4) else 0) := by
      rw [← Finset.sum_filter]
      simp
    _ = ((∑ x, t x ^ 2 : ℤ) : ZMod 4) := by simp only [Int.cast_sum, Int.cast_pow, hsq]
    _ = 0 := by
      rw [henergy, Int.cast_mul, show ((8 : ℤ) : ZMod 4) = 0 by decide, zero_mul]

open Classical in
/-- In the Q9 binary complement setting, every nonzero active face has
at least twelve support points for a word supported in one parity. -/
theorem twelve_le_binaryFaceSupport_card (i : Fin 9) (b : Bool)
    (K : Finset (Q 9)) (f : Q 9 → ZMod 2)
    (hK : ∀ x ∈ K, f x = 0)
    (hdegree : ∀ y : Q 9, 2 ≤ (K.filter (fun x => (hypercube 9).Adj y x)).card)
    (hpar : ∃ p : Bool, ∀ x, f x ≠ 0 → cubeParity x = p)
    (hker : ∀ y : Q 9, ∑ j : Fin 8, f (BalancedCriticalSpectrum.flip y (i.succAbove j)) = 0)
    (hne : (binaryFaceSupport i b f).Nonempty) :
    12 ≤ (binaryFaceSupport i b f).card := by
  have hmin := eight_lt_binaryFaceSupport_card i b K f hK hdegree hpar hker hne
  have hdvd : 4 ∣ (binaryFaceSupport i b f).card := by
    apply four_dvd_binary_support
    intro x
    simpa only [insertNth_flip] using hker (i.insertNth (α := fun _ => Bool) b x)
  omega

#print axioms twelve_le_binaryFaceSupport_card

open Classical in
/-- For any omitted direction, a nonzero binary complement word occupies at
least twelve vertices on some face. The exterior hypotheses are the positive
and even selected-neighbor counts used for a saturated pair. -/
theorem exists_twelve_le_binaryFaceSupport_card (i : Fin 9)
    (K : Finset (Q 9)) (f : Q 9 → ZMod 2) (hf : f ≠ 0)
    (hK : ∀ x ∈ K, f x = 0)
    (hinside : ∀ y ∈ K, (K.filter (fun x => (hypercube 9).Adj y x)).card = 3)
    (houtside : ∀ y ∉ K, (K.filter (fun x => (hypercube 9).Adj y x)).Nonempty ∧
      Even (K.filter (fun x => (hypercube 9).Adj y x)).card)
    (hpar : ∃ p : Bool, ∀ x, f x ≠ 0 → cubeParity x = p)
    (hker : ∀ y : Q 9, ∑ j : Fin 8, f (BalancedCriticalSpectrum.flip y (i.succAbove j)) = 0) :
    ∃ b : Bool, 12 ≤ (binaryFaceSupport i b f).card := by
  classical
  have hdegree (y : Q 9) : 2 ≤ (K.filter (fun x => (hypercube 9).Adj y x)).card := by
    by_cases hy : y ∈ K
    · rw [hinside y hy]
      decide
    · obtain ⟨hne, k, hk⟩ := houtside y hy
      have hp := Finset.card_pos.mpr hne
      omega
  have hpoint : ∃ x : Q 9, f x ≠ 0 := by
    by_contra! h
    exact hf (funext h)
  obtain ⟨x, hx⟩ := hpoint
  refine ⟨x i, twelve_le_binaryFaceSupport_card i (x i) K f hK hdegree hpar hker ?_⟩
  refine ⟨i.removeNth (α := fun _ => Bool) x,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simpa only [Fin.insertNth_self_removeNth] using hx

#print axioms exists_twelve_le_binaryFaceSupport_card

end D5.S3.Combinatorics.Graph.HypercubeCritical.CubeEvenMinimumSupport
