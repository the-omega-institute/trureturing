import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! The two-color quotient of an eight-cycle in a four-coordinate projection. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5EightCycleQuotient

open Finset
open scoped BigOperators
open Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_apply_same)
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

local notation "A" => SimpleGraph.Adj (hypercube 5)

/-- Neighbors of `v` belonging to a specified set of vertices. -/
noncomputable def neighbors (S : Finset (Q 5)) (v : Q 5) : Finset (Q 5) := by
  classical
  exact S.filter (A v)

@[simp] private theorem mem_neighbors {S : Finset (Q 5)} {v w : Q 5} :
    w ∈ neighbors S v ↔ w ∈ S ∧ A v w := by
  classical
  simp [neighbors]

/-- Weight in one coordinate half, with shared fibers counted twice. -/
def halfWeight (R B F : Finset (Q 5)) (i : Fin 5) (value : Bool) : Nat :=
  (R.filter fun x => x i = value).card + (B.filter fun x => x i = value).card +
    2 * (F.filter fun x => x i = value).card

private theorem flip_apply_of_ne {n : Nat} (x : Q n) {i j : Fin n} (h : j ≠ i) :
    flip x i j = x j := Function.update_of_ne h _ _

private theorem common_neighbor {n : Nat} {c f : Q n} {i j : Fin n} (hij : i ≠ j)
    (hi : (hypercube n).Adj (flip c i) f) (hj : (hypercube n).Adj (flip c j) f) :
    f = c ∨ f = flip (flip c i) j := by
  obtain ⟨a, ha⟩ := adjacent_exists_flip hi
  obtain ⟨b, hb⟩ := adjacent_exists_flip hj
  by_cases hai : a = i
  · left
    simpa [hai] using ha
  · have hbi : b = i := by
      by_contra hbi
      have h := congrFun (ha.symm.trans hb) i
      simp only [flip_apply_of_ne c hij, flip_apply_of_ne _ (Ne.symm hai),
        flip_apply_of_ne _ (Ne.symm hbi), flip_apply_same] at h
      cases hc : c i <;> simp [hc] at h
    right
    rw [hb, hbi, flip_comm]

/-- In the star configuration, the half through a blue leaf has weight five.
Each full vertex joins a red neighbor of the center to a blue leaf. -/
theorem halfWeight_eq_five_of_star {R B F : Finset (Q 5)} {c leaf : Q 5}
    (hrb : Disjoint R B) (hcf : c ∉ F) (hleaf : leaf ∈ B) (hcl : A c leaf)
    (hR : ∀ r ∈ R, A c r) (hB : ∀ b ∈ B, b = c ∨ A c b)
    (hF : ∀ f ∈ F, ∃ r ∈ R, ∃ b ∈ B, A c b ∧ A r f ∧ A b f)
    (hdeg : (neighbors F leaf).card = 2) :
    ∃ i value, halfWeight R B F i value = 5 := by
  classical
  obtain ⟨k, hk⟩ := adjacent_exists_flip hcl
  have half_neighbor (x : Q 5) (hx : A c x) :
      x k = !c k ↔ x = leaf := by
    obtain ⟨i, hi⟩ := adjacent_exists_flip hx
    by_cases hik : i = k
    · simp [hi, hk, hik]
    · have hne : flip c i ≠ leaf := fun h => hik (flip_injective c (h.trans hk))
      rw [hi, flip_apply_of_ne c (Ne.symm hik)]
      cases c k <;> simp [hne]
  have hRed : (R.filter fun x => x k = !c k) = ∅ := by
    ext x
    simp only [mem_filter, notMem_empty, iff_false]
    rintro ⟨hx, hbit⟩
    exact (disjoint_left.mp hrb hx) (by rwa [(half_neighbor x (hR x hx)).mp hbit])
  have hBlue : (B.filter fun x => x k = !c k) = {leaf} := by
    ext x
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hx, hbit⟩
      rcases hB x hx with he | ha
      · rw [he] at hbit
        cases hc : c k <;> simp [hc] at hbit
      · exact (half_neighbor x ha).mp hbit
    · intro he
      subst x
      exact ⟨hleaf, (half_neighbor leaf hcl).mpr rfl⟩
  have hFull : (F.filter fun x => x k = !c k) = neighbors F leaf := by
    ext f
    simp only [mem_filter, mem_neighbors]
    refine and_congr_right fun hf => ?_
    obtain ⟨r, hr, b, hb, hcb, hrf, hbf⟩ := hF f hf
    obtain ⟨i, hi⟩ := adjacent_exists_flip (hR r hr)
    obtain ⟨j, hj⟩ := adjacent_exists_flip hcb
    have hij : i ≠ j := by
      intro he
      exact (disjoint_left.mp hrb hr) (by rwa [show r = b by rw [hi, hj, he]])
    have hik : i ≠ k := by
      intro he
      exact (disjoint_left.mp hrb hr) (by rwa [show r = leaf by rw [hi, hk, he]])
    have he : f = flip (flip c i) j :=
      (common_neighbor hij (hi.symm ▸ hrf) (hj.symm ▸ hbf)).resolve_left
        (fun h => hcf (by rwa [← h]))
    by_cases hjk : j = k
    · subst j
      have hbl : b = leaf := hj.trans hk.symm
      constructor
      · intro _
        simpa only [← hbl] using hbf
      · intro _
        rw [he, flip_apply_same, flip_apply_of_ne _ (Ne.symm hik)]
    · rw [he, flip_apply_of_ne _ (Ne.symm hjk), flip_apply_of_ne _ (Ne.symm hik)]
      constructor
      · intro h
        cases hc : c k <;> simp [hc] at h
      · intro ha
        obtain ⟨l, hl⟩ := adjacent_exists_flip ha
        rw [hk] at hl
        by_cases hlk : l = k
        · subst l
          rw [BalancedCriticalSpectrum.flip_flip] at hl
          exact (hcf (by rwa [← he.trans hl])).elim
        · have hbit := congrFun hl k
          rw [flip_apply_of_ne _ (Ne.symm hlk), flip_apply_of_ne _ (Ne.symm hjk),
            flip_apply_of_ne _ (Ne.symm hik), flip_apply_same] at hbit
          cases hc : c k <;> simp [hc] at hbit
  exact ⟨k, !c k, by simp [halfWeight, hRed, hBlue, hFull, hdeg]⟩


private theorem parity_eq_of_common {x y z : Q 5} (hx : A x z) (hy : A y z) :
    cubeParity x = cubeParity y := by
  have h₁ := cubeParity_ne_of_adj hx
  have h₂ := cubeParity_ne_of_adj hy
  cases he₁ : cubeParity x <;> cases he₂ : cubeParity y <;>
    cases he₃ : cubeParity z <;> simp_all

private theorem full_neighbors_le_two {B F : Finset (Q 5)} {r b : Q 5}
    (hr : r ∉ B) (hb : b ∉ F) (hrb : A b r)
    (hcover : ∀ f ∈ F, (neighbors B f).Nonempty)
    (hopp : ∀ z ∈ B, cubeParity z ≠ cubeParity b → A b z)
    (hdeg : (neighbors B b).card = 2) : (neighbors F r).card ≤ 2 := by
  classical
  obtain ⟨p, q, _, hpq⟩ := card_eq_two.mp hdeg
  have bound (z : Q 5) (hz : z ∈ neighbors B b) : ∃ f₀, ∀ f ∈ neighbors F r, A z f → f = f₀ := by
    obtain ⟨i, hi⟩ := adjacent_exists_flip hrb
    obtain ⟨j, hj⟩ := adjacent_exists_flip (mem_neighbors.mp hz).2
    have hij : i ≠ j := by
      intro h
      exact hr (by rw [hi, h, ← hj]; exact (mem_neighbors.mp hz).1)
    refine ⟨flip (flip b i) j, ?_⟩
    intro f hf hzf
    obtain ⟨hfF, hrf⟩ := mem_neighbors.mp hf
    rcases common_neighbor hij (hi ▸ hrf) (hj ▸ hzf) with rfl | he
    · exact (hb hfF).elim
    · exact he
  have hp : p ∈ neighbors B b := by simp [hpq]
  have hq : q ∈ neighbors B b := by simp [hpq]
  obtain ⟨fp, hp'⟩ := bound p hp
  obtain ⟨fq, hq'⟩ := bound q hq
  have hsub : neighbors F r ⊆ {fp, fq} := by
    intro f hf
    obtain ⟨hfF, hrf⟩ := mem_neighbors.mp hf
    obtain ⟨z, hz⟩ := hcover f hfF
    obtain ⟨hzB, hfz⟩ := mem_neighbors.mp hz
    have hpar : cubeParity z ≠ cubeParity b := by
      rw [parity_eq_of_common hfz.symm hrf]
      exact (cubeParity_ne_of_adj hrb).symm
    have hm : z ∈ neighbors B b := mem_neighbors.mpr ⟨hzB, hopp z hzB hpar⟩
    rw [hpq, mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact mem_insert.mpr (Or.inl (hp' f hf hfz.symm))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (hq' f hf hfz.symm)))
  exact (card_le_card hsub).trans card_le_two

/-- The induced cube graph on the given vertices contains no square. -/
def SquareFree (S : Finset (Q 5)) : Prop :=
  ∀ x ∈ S, ∀ z ∈ S, x ≠ z → ∀ y ∈ S, ∀ w ∈ S, y ≠ w →
    A x y → A x w → A z y → A z w → False

private theorem neighbors_subset (S : Finset (Q 5)) (v : Q 5) : neighbors S v ⊆ S :=
  fun _ h => (mem_neighbors.mp h).1

private theorem neighbors_union_card {S T : Finset (Q 5)} (h : Disjoint S T) (v : Q 5) :
    (neighbors (S ∪ T) v).card = (neighbors S v).card + (neighbors T v).card := by
  classical
  have he : neighbors (S ∪ T) v = neighbors S v ∪ neighbors T v := by
    ext w
    simp [or_and_right]
  rw [he, card_union_of_disjoint (h.mono (neighbors_subset S v) (neighbors_subset T v))]

private theorem sum_neighbors_comm (S T : Finset (Q 5)) :
    ∑ s ∈ S, (neighbors T s).card = ∑ t ∈ T, (neighbors S t).card := by
  classical
  simp_rw [neighbors, card_eq_sum_ones, sum_filter]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun t _ => sum_congr rfl fun s _ => by rw [SimpleGraph.adj_comm]

private theorem eq_of_sum_card_mul {S : Finset (Q 5)} {f : Q 5 → Nat} {k : Nat}
    (hle : ∀ x ∈ S, f x ≤ k) (hsum : ∑ x ∈ S, f x = S.card * k) (x : Q 5) (hx : x ∈ S) :
    f x = k := by
  have he := add_sum_erase S f hx
  have hbound : ∑ y ∈ S.erase x, f y ≤ (S.erase x).card * k := by
    calc
      _ ≤ ∑ _y ∈ S.erase x, k := sum_le_sum fun y hy => hle y (mem_erase.mp hy).2
      _ = _ := sum_const_nat fun _ _ => rfl
  have hmul : S.card * k = (S.erase x).card * k + k := by
    rw [← card_erase_add_one hx, Nat.add_mul, Nat.one_mul]
  rw [hsum, hmul] at he
  have := hle x hx
  omega

private theorem sum_neighbors_le (S T : Finset (Q 5)) :
    ∑ s ∈ S, (neighbors T s).card ≤ S.card * T.card := by
  calc
    _ ≤ ∑ _s ∈ S, T.card := sum_le_sum fun s _ => card_le_card (neighbors_subset T s)
    _ = _ := sum_const_nat fun _ _ => rfl

private theorem complete_of_sum {S T : Finset (Q 5)}
    (hsum : ∑ s ∈ S, (neighbors T s).card = S.card * T.card)
    {x y : Q 5} (hx : x ∈ S) (hy : y ∈ T) : A x y := by
  have hcard := eq_of_sum_card_mul (fun s _ => card_le_card (neighbors_subset T s)) hsum x hx
  have he := eq_of_subset_of_card_le (neighbors_subset T x) hcard.ge
  exact (mem_neighbors.mp (he.symm ▸ hy)).2

private theorem not_complete_of_squareFree {S L M : Finset (Q 5)} (hs : SquareFree S)
    (hl : L ⊆ S) (hm : M ⊆ S) (hL : 1 < L.card) (hM : 1 < M.card)
    (hall : ∀ x ∈ L, ∀ y ∈ M, A x y) : False := by
  obtain ⟨x, hx, z, hz, hxz⟩ := one_lt_card.mp hL
  obtain ⟨y, hy, w, hw, hyw⟩ := one_lt_card.mp hM
  exact hs x (hl hx) z (hl hz) hxz y (hm hy) w (hm hw) hyw
    (hall x hx y hy) (hall x hx w hw) (hall z hz y hy) (hall z hz w hw)

private def parityHalf (S : Finset (Q 5)) (p : Bool) : Finset (Q 5) :=
  S.filter fun x => cubeParity x = p

private theorem neighbors_other_parity {S : Finset (Q 5)} {x : Q 5} {p : Bool}
    (hx : cubeParity x = p) : neighbors S x = neighbors (parityHalf S (!p)) x := by
  ext y
  simp only [mem_neighbors, parityHalf, mem_filter]
  constructor
  · rintro ⟨hy, ha⟩
    have hn := cubeParity_ne_of_adj ha
    rw [hx] at hn
    have he : cubeParity y = !p := (Bool.not_eq_iff.mpr hn).symm
    exact ⟨⟨hy, he⟩, ha⟩
  · rintro ⟨⟨hy, _⟩, ha⟩
    exact ⟨hy, ha⟩

private theorem parity_partition (S : Finset (Q 5)) (p : Bool) :
    parityHalf S p ∪ parityHalf S (!p) = S ∧
      Disjoint (parityHalf S p) (parityHalf S (!p)) := by
  classical
  constructor
  · ext x
    cases p <;> cases h : cubeParity x <;> simp [parityHalf, h]
  · apply disjoint_left.mpr
    intro x hx hy
    simp only [parityHalf, mem_filter] at hx hy
    have h := hx.2.symm.trans hy.2
    cases p <;> contradiction

private theorem sum_degree_twice (S : Finset (Q 5)) (p : Bool) :
    ∑ s ∈ S, (neighbors S s).card =
      2 * ∑ x ∈ parityHalf S p, (neighbors (parityHalf S (!p)) x).card := by
  classical
  obtain ⟨hu, hd⟩ := parity_partition S p
  have hleft : ∑ x ∈ parityHalf S p, (neighbors S x).card =
      ∑ x ∈ parityHalf S p, (neighbors (parityHalf S (!p)) x).card := by
    apply sum_congr rfl
    intro x hx
    rw [neighbors_other_parity ((mem_filter.mp hx).2)]
  have hright : ∑ x ∈ parityHalf S (!p), (neighbors S x).card =
      ∑ x ∈ parityHalf S (!p), (neighbors (parityHalf S p) x).card := by
    apply sum_congr rfl
    intro x hx
    rw [neighbors_other_parity ((mem_filter.mp hx).2), Bool.not_not]
  calc
    _ = (∑ x ∈ parityHalf S p, (neighbors S x).card) +
          ∑ x ∈ parityHalf S (!p), (neighbors S x).card := by
        rw [← sum_union hd, hu]
    _ = _ := by rw [hleft, hright, sum_neighbors_comm (parityHalf S (!p)), two_mul]


/-- The quotient has a coordinate half of weight five when the two exclusive
colors have sizes two and four. The blue parity split distinguishes the star
from the path. -/
theorem halfWeight_eq_five_of_card_two_four {R B F : Finset (Q 5)}
    (hRB : Disjoint R B) (hRF : Disjoint R F) (hBF : Disjoint B F)
    (hR : R.card = 2) (hB : B.card = 4) (hF : F.card = 6)
    (hred : ∀ r ∈ R, (neighbors (R ∪ F) r).card = 3)
    (hblue : ∀ b ∈ B, (neighbors (B ∪ F) b).card = 3)
    (hfullRed : ∀ f ∈ F, (neighbors (R ∪ F) f).card = 1)
    (hfullBlue : ∀ f ∈ F, (neighbors (B ∪ F) f).card = 1)
    (hopp : ∀ b ∈ B, (neighbors (R ∪ F) b).card = 2 ∨ (neighbors (R ∪ F) b).card = 4)
    (hfree : SquareFree B) : ∃ i value, halfWeight R B F i value = 5 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : Bool, (parityHalf B p).card ≤ (parityHalf B (!p)).card := by
    rcases le_total (parityHalf B false).card (parityHalf B true).card with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  let L := parityHalf B p
  let M := parityHalf B (!p)
  let e := ∑ b ∈ L, (neighbors M b).card
  have hL : L ⊆ B := filter_subset _ _
  have hM : M ⊆ B := filter_subset _ _
  have hcard : L.card + M.card = 4 := by
    obtain ⟨hu, hd⟩ := parity_partition B p
    rw [← card_union_of_disjoint hd, hu, hB]
  have hsize : L.card ≤ 2 := by change L.card ≤ M.card at hp; omega
  have heBound : e ≤ L.card * M.card := sum_neighbors_le L M
  have heUpper : e ≤ 3 := by
    by_contra h
    have hL₂ : L.card = 2 := by
      by_contra hn
      have hl : L.card = 0 ∨ L.card = 1 := by omega
      rcases hl with hzero | hone
      · simp [hzero] at heBound
        omega
      · simp [hone] at heBound
        omega
    have hM₂ : M.card = 2 := by omega
    rw [hL₂, hM₂] at heBound
    have he₄ : e = L.card * M.card := by rw [hL₂, hM₂]; omega
    exact not_complete_of_squareFree hfree hL hM (by omega) (by omega)
      (fun _ hx _ hy => complete_of_sum he₄ hx hy)
  have hsumB : ∑ b ∈ B, (neighbors (B ∪ F) b).card = 12 := by
    rw [sum_const_nat hblue, hB]
  simp_rw [neighbors_union_card hBF, sum_add_distrib, sum_degree_twice B p] at hsumB
  have heSum : 2 * e + ∑ f ∈ F, (neighbors B f).card = 12 := by
    simpa only [e, L, M, sum_neighbors_comm B F] using hsumB
  have hcapF : ∀ f ∈ F, (neighbors B f).card ≤ 1 := by
    intro f hf
    have h := hfullBlue f hf
    rw [neighbors_union_card hBF] at h
    omega
  have hsumF : ∑ f ∈ F, (neighbors B f).card ≤ 6 := by
    calc
      _ ≤ ∑ _f ∈ F, 1 := sum_le_sum hcapF
      _ = 6 := by simp [hF]
  have he₃ : e = 3 := by omega
  have hFB (f : Q 5) (hf : f ∈ F) : (neighbors B f).card = 1 :=
    eq_of_sum_card_mul hcapF (by rw [hF, Nat.mul_one]; omega) f hf
  have hFR (f : Q 5) (hf : f ∈ F) : (neighbors R f).card = 1 := by
    have hb := hfullBlue f hf
    have hr := hfullRed f hf
    rw [neighbors_union_card hBF, hFB f hf] at hb
    rw [neighbors_union_card hRF] at hr
    omega
  have hsumRed : ∑ r ∈ R, (neighbors (R ∪ F) r).card = 6 := by
    rw [sum_const_nat hred, hR]
  have hsumFR : ∑ f ∈ F, (neighbors R f).card = 6 := by
    rw [sum_const_nat hFR, hF, Nat.mul_one]
  simp_rw [neighbors_union_card hRF, sum_add_distrib, sum_neighbors_comm R F, hsumFR] at hsumRed
  have hrF (r : Q 5) (hr : r ∈ R) : (neighbors F r).card = 3 := by
    have hrd := hred r hr
    rw [neighbors_union_card hRF] at hrd
    have hsum := add_sum_erase R (fun r => (neighbors R r).card) hr
    omega
  have hcoverB (f : Q 5) (hf : f ∈ F) : (neighbors B f).Nonempty :=
    card_pos.mp (by rw [hFB f hf]; decide)
  have hcoverR (f : Q 5) (hf : f ∈ F) : (neighbors R f).Nonempty :=
    card_pos.mp (by rw [hFR f hf]; decide)
  have hLpos : L.card ≠ 0 := by
    intro h
    rw [h, Nat.zero_mul] at heBound
    omega
  by_cases hL₁ : L.card = 1
  · have hM₃ : M.card = 3 := by omega
    have hcomplete : ∀ x ∈ L, ∀ y ∈ M, A x y := by
      have hsum : e = L.card * M.card := by rw [hL₁, hM₃, Nat.one_mul, he₃]
      exact fun _ hx _ hy => complete_of_sum hsum hx hy
    obtain ⟨c, hc⟩ := card_eq_one.mp hL₁
    have hcL : c ∈ L := by simp [hc]
    have hcm (b : Q 5) (hb : b ∈ M) : A c b := hcomplete c hcL b hb
    have hcent : neighbors B c = M := by
      rw [neighbors_other_parity (mem_filter.mp hcL).2]
      exact subset_antisymm (neighbors_subset M c) (fun b hb => mem_neighbors.mpr ⟨hb, hcm b hb⟩)
    have hcentF : (neighbors F c).card = 0 := by
      have h := hblue c (hL hcL)
      rw [neighbors_union_card hBF, hcent, hM₃] at h
      omega
    have hallR (r : Q 5) (hr : r ∈ R) : A c r := by
      have h := hopp c (hL hcL)
      rw [neighbors_union_card hRF, hcentF, Nat.add_zero] at h
      have hle := card_le_card (neighbors_subset R c)
      rw [hR] at hle
      have heq := eq_of_subset_of_card_le (neighbors_subset R c)
        (by rw [hR]; omega)
      exact (mem_neighbors.mp (heq.symm ▸ hr)).2
    have hBstar (b : Q 5) (hb : b ∈ B) : b = c ∨ A c b := by
      rw [← (parity_partition B p).1, mem_union] at hb
      rcases hb with h | h
      · change b ∈ L at h
        exact Or.inl (by simpa [hc] using h)
      · exact Or.inr (hcm b h)
    have hFstar (f : Q 5) (hf : f ∈ F) :
        ∃ r ∈ R, ∃ b ∈ B, A c b ∧ A r f ∧ A b f := by
      obtain ⟨r, hr⟩ := hcoverR f hf
      obtain ⟨b, hb⟩ := hcoverB f hf
      obtain ⟨hrR, hfr⟩ := mem_neighbors.mp hr
      obtain ⟨hbB, hfb⟩ := mem_neighbors.mp hb
      refine ⟨r, hrR, b, hbB, ?_, hfr.symm, hfb.symm⟩
      rcases hBstar b hbB with he | h
      · rw [he] at hfb
        have hf' := mem_neighbors.mpr ⟨hf, hfb.symm⟩
        have hpos := card_pos.mpr (show (neighbors F c).Nonempty from ⟨f, hf'⟩)
        omega
      · exact h
    obtain ⟨leaf, hl⟩ := card_pos.mp (show 0 < M.card by omega)
    have hleaf : neighbors B leaf = {c} := by
      rw [neighbors_other_parity (mem_filter.mp hl).2, Bool.not_not,
        show parityHalf B p = {c} from hc]
      ext x
      simp only [mem_neighbors, mem_singleton]
      exact ⟨And.left, fun h => ⟨h, h.symm ▸ (hcm leaf hl).symm⟩⟩
    have hleafF : (neighbors F leaf).card = 2 := by
      have h := hblue leaf (hM hl)
      rw [neighbors_union_card hBF, hleaf, card_singleton] at h
      omega
    exact halfWeight_eq_five_of_star hRB (disjoint_left.mp hBF (hL hcL))
      (hM hl) (hcm leaf hl) hallR hBstar hFstar hleafF
  · have hL₂ : L.card = 2 := by omega
    have hM₂ : M.card = 2 := by omega
    obtain ⟨b, hbL, hbDeg⟩ : ∃ b ∈ L, (neighbors M b).card = 2 := by
      by_contra! hn
      have hbound : ∑ b ∈ L, (neighbors M b).card ≤ 2 := by
        calc
          _ ≤ ∑ _b ∈ L, 1 := by
            apply sum_le_sum
            intro b hb
            have h₁ := hn b hb
            have h₂ := card_le_card (neighbors_subset M b)
            omega
          _ = 2 := by simp [hL₂]
      exact (by omega : False)
    have hbParity : cubeParity b = p := (mem_filter.mp hbL).2
    have hbD : (neighbors B b).card = 2 := by
      rw [neighbors_other_parity hbParity]
      exact hbDeg
    have hbF : (neighbors F b).card = 1 := by
      have h := hblue b (hL hbL)
      rw [neighbors_union_card hBF, hbD] at h
      omega
    have hbOpp := hopp b (hL hbL)
    rw [neighbors_union_card hRF, hbF] at hbOpp
    obtain ⟨r, hr⟩ := card_pos.mp (show 0 < (neighbors R b).card by omega)
    obtain ⟨hrR, hbr⟩ := mem_neighbors.mp hr
    have hbAll (z : Q 5) (hz : z ∈ B) (hpar : cubeParity z ≠ cubeParity b) : A b z := by
      have hzM : z ∈ M := by
        change z ∈ parityHalf B (!p)
        rw [hbParity] at hpar
        exact mem_filter.mpr ⟨hz, (Bool.not_eq_iff.mpr hpar.symm).symm⟩
      have heq := eq_of_subset_of_card_le (neighbors_subset M b) (by rw [hM₂, hbDeg])
      exact (mem_neighbors.mp (heq.symm ▸ hzM)).2
    have hbad := full_neighbors_le_two (disjoint_left.mp hRB hrR)
      (disjoint_left.mp hBF (hL hbL)) hbr hcoverB hbAll hbD
    have hgood := hrF r hrR
    omega


private theorem squareFree_mono {S T : Finset (Q 5)} (h : S ⊆ T) (ht : SquareFree T) :
    SquareFree S :=
  fun x hx z hz hxz y hy w hw hyw => ht x (h hx) z (h hz) hxz y (h hy) w (h hw) hyw

private theorem no_cubic_six {S : Finset (Q 5)} (hS : S.card = 6)
    (hfree : SquareFree S) (hdeg : ∀ x ∈ S, (neighbors S x).card = 3) : False := by
  classical
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < S.card by omega)
  let p := cubeParity x
  let L := parityHalf S p
  let M := parityHalf S (!p)
  have hxm : (neighbors M x).card = 3 := by
    rw [← neighbors_other_parity (show cubeParity x = p from rfl)]
    exact hdeg x hx
  obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (neighbors M x).card by omega)
  have hyM := (mem_neighbors.mp hy).1
  have hyl : (neighbors L y).card = 3 := by
    have he := neighbors_other_parity (S := S) (mem_filter.mp hyM).2
    rw [Bool.not_not] at he
    rw [← he]
    exact hdeg y (mem_filter.mp hyM).1
  obtain ⟨hun, hd⟩ := parity_partition S p
  have htotal : L.card + M.card = 6 := by rw [← card_union_of_disjoint hd, hun, hS]
  have hl := card_le_card (neighbors_subset L y)
  have hm := card_le_card (neighbors_subset M x)
  have hM : M.card = 3 := by omega
  have hL : 1 < L.card := by omega
  apply not_complete_of_squareFree (L := L) (M := M) hfree (filter_subset _ _ : L ⊆ S)
    (filter_subset _ _ : M ⊆ S) hL (by omega)
  intro a ha b hb
  have h := hdeg a (mem_filter.mp ha).1
  rw [neighbors_other_parity (mem_filter.mp ha).2] at h
  have he := eq_of_subset_of_card_le (neighbors_subset M a) (by rw [hM]; exact h.ge)
  exact (mem_neighbors.mp (he.symm ▸ hb)).2

private theorem exclusive_nonempty {R B F : Finset (Q 5)}
    (hBF : Disjoint B F) (hRB : R.card + B.card = 6)
    (hblue : ∀ b ∈ B, (neighbors (B ∪ F) b).card = 3)
    (hfullRed : ∀ f ∈ F, (neighbors (R ∪ F) f).card = 1)
    (hfullBlue : ∀ f ∈ F, (neighbors (B ∪ F) f).card = 1)
    (hfree : SquareFree B) : R.card ≠ 0 := by
  classical
  intro hzero
  have hempty := card_eq_zero.mp hzero
  have hF (f : Q 5) (hf : f ∈ F) : (neighbors B f).card = 0 := by
    have hr := hfullRed f hf
    rw [hempty, empty_union] at hr
    have hb := hfullBlue f hf
    rw [neighbors_union_card hBF, hr] at hb
    omega
  apply no_cubic_six (show B.card = 6 by omega) hfree
  intro b hb
  have hno : neighbors F b = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨hfF, hbf⟩ := mem_neighbors.mp hf
    have hb' := mem_neighbors.mpr ⟨hb, hbf.symm⟩
    rw [card_eq_zero.mp (hF f hfF)] at hb'
    exact notMem_empty _ hb'
  simpa [neighbors_union_card hBF, hno] using hblue b hb

private theorem exclusive_even {R F : Finset (Q 5)}
    (hRF : Disjoint R F) (hF : F.card = 6)
    (hexclusive : ∀ x ∈ R, (neighbors (R ∪ F) x).card = 3)
    (hfull : ∀ x ∈ F, (neighbors (R ∪ F) x).card = 1) : R.card % 2 = 0 := by
  have h := sum_degree_twice (R ∪ F) false
  rw [sum_union hRF, sum_const_nat hexclusive, sum_const_nat hfull, hF] at h
  omega

/-- The two-color eight-cycle quotient forces a coordinate half with one unit
per exclusive fiber and two per full fiber, totaling five. -/
theorem halfWeight_eq_five {R B F : Finset (Q 5)}
    (hRB : Disjoint R B) (hRF : Disjoint R F) (hBF : Disjoint B F)
    (hRBsize : R.card + B.card = 6) (hF : F.card = 6)
    (hred : ∀ r ∈ R, (neighbors (R ∪ F) r).card = 3)
    (hblue : ∀ b ∈ B, (neighbors (B ∪ F) b).card = 3)
    (hfullRed : ∀ f ∈ F, (neighbors (R ∪ F) f).card = 1)
    (hfullBlue : ∀ f ∈ F, (neighbors (B ∪ F) f).card = 1)
    (hoppR : ∀ r ∈ R, (neighbors (B ∪ F) r).card = 2 ∨ (neighbors (B ∪ F) r).card = 4)
    (hoppB : ∀ b ∈ B, (neighbors (R ∪ F) b).card = 2 ∨ (neighbors (R ∪ F) b).card = 4)
    (hfreeR : SquareFree (R ∪ F)) (hfreeB : SquareFree (B ∪ F)) :
    ∃ i value, halfWeight R B F i value = 5 := by
  have hrFree := squareFree_mono (show R ⊆ R ∪ F from subset_union_left) hfreeR
  have hbFree := squareFree_mono (show B ⊆ B ∪ F from subset_union_left) hfreeB
  have hrPos := exclusive_nonempty hBF hRBsize hblue hfullRed hfullBlue hbFree
  have hbPos := exclusive_nonempty hRF (Nat.add_comm R.card B.card ▸ hRBsize)
    hred hfullBlue hfullRed hrFree
  have hrEven := exclusive_even hRF hF hred hfullRed
  have hbEven := exclusive_even hBF hF hblue hfullBlue
  by_cases hr : R.card = 2
  · exact halfWeight_eq_five_of_card_two_four hRB hRF hBF hr (by omega) hF
      hred hblue hfullRed hfullBlue hoppB hbFree
  · obtain ⟨i, value, he⟩ := halfWeight_eq_five_of_card_two_four hRB.symm hBF hRF
      (by omega) (by omega) hF hblue hred hfullBlue hfullRed hoppR hrFree
    refine ⟨i, value, ?_⟩
    unfold halfWeight at he ⊢
    omega

#print axioms halfWeight_eq_five_of_star
#print axioms halfWeight_eq_five_of_card_two_four
#print axioms halfWeight_eq_five

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5EightCycleQuotient
