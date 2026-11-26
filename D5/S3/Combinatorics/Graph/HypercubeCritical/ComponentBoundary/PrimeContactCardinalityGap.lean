/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The signed two-contact cube has at least nine columns and cannot have exactly ten. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeOrders
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Cardinality gap for two-contact Huang cube columns

Hong–Wu–Xia, arXiv:2610.09483v1, §7, Problem 2.
The geometric part uses the actual cube and the row sign equations.
The exponent lift is used in the final application of the order cover.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj flip_flip)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeGirth (adjacent_exists_flip flip_comm)
open BalancedCubeComponentBoundary (flip_injective)
open PrimeContactCubeLift (RowSigns EmptyGain occupied_ne_at_common_rows
  common_rows_of_hammingDist_two)
open PrimeContactCubeOrders
open PrimeContactTransport (Exponent)
open private double_flip_apply from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeLift

section GraphCounting

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Count the same finite incidence relation from its two sides. -/
private theorem sum_card_filter_swap (A : Finset α) (B : Finset β)
    (R : α → β → Prop) [∀ a b, Decidable (R a b)] :
    (∑ a ∈ A, (B.filter (R a)).card) =
      ∑ b ∈ B, (A.filter (fun a => R a b)).card := by
  exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := R) (s := A) (t := B)

variable (G : SimpleGraph α) [DecidableRel G.Adj]

/-- Neighbors in the graph induced on a finite set of vertices. -/
def neighborsIn (S : Finset α) (x : α) : Finset α :=
  S.filter (G.Adj x)

/-- Common neighbors in the same induced graph. -/
def commonIn (S : Finset α) (x y : α) : Finset α :=
  neighborsIn G S x ∩ neighborsIn G S y

@[simp] theorem mem_neighborsIn {S : Finset α} {x y : α} :
    y ∈ neighborsIn G S x ↔ y ∈ S ∧ G.Adj x y := Finset.mem_filter

@[simp] theorem mem_commonIn {S : Finset α} {x y z : α} :
    z ∈ commonIn G S x y ↔ z ∈ S ∧ G.Adj x z ∧ G.Adj y z := by
  simp only [commonIn, Finset.mem_inter, mem_neighborsIn]
  tauto

/-- In a four-regular induced graph, if nonadjacent distinct vertices have at
most two common neighbors, the number of incident triangles at a vertex gives
a lower bound on the size of the entire vertex set. The local sum counts
ordered pairs of adjacent neighbors. -/
theorem eleven_le_card_add_of_two_step_count (S : Finset α) (x : α)
    (hx : x ∈ S) (t : ℕ)
    (hdegree : ∀ y ∈ S, (neighborsIn G S y).card = 4)
    (hcommon : ∀ y ∈ S, y ≠ x → ¬ G.Adj x y → (commonIn G S x y).card ≤ 2)
    (hlocal : (∑ y ∈ neighborsIn G S x, (commonIn G S x y).card) = 2 * t) :
    11 ≤ S.card + t := by
  let A := neighborsIn G S x
  have hA : A ⊆ S.erase x := by
    intro y hy
    obtain ⟨hyS, hxy⟩ := (mem_neighborsIn G).mp hy
    exact Finset.mem_erase.mpr ⟨Ne.symm (G.ne_of_adj hxy), hyS⟩
  have hAc : A.card = 4 := hdegree x hx
  have htotal : (∑ y ∈ S.erase x, (commonIn G S x y).card) = 12 := by
    calc
      _ = ∑ y ∈ S.erase x, (A.filter (fun z => G.Adj y z)).card := by
        apply Finset.sum_congr rfl
        intro y _
        congr 1
        ext z
        simp only [mem_commonIn, Finset.mem_filter, A, mem_neighborsIn, and_assoc]
      _ = ∑ z ∈ A, ((S.erase x).filter (fun y => G.Adj y z)).card :=
        sum_card_filter_swap (S.erase x) A (fun y z => G.Adj y z)
      _ = ∑ z ∈ A, ((neighborsIn G S z).erase x).card := by
        apply Finset.sum_congr rfl
        intro z _
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_erase, mem_neighborsIn]
        constructor
        · rintro ⟨⟨hne, hy⟩, hadj⟩
          exact ⟨hne, hy, G.adj_symm hadj⟩
        · rintro ⟨hne, hy, hadj⟩
          exact ⟨⟨hne, hy⟩, G.adj_symm hadj⟩
      _ = A.card * 3 := by
        apply Finset.sum_const_nat
        intro z hz
        obtain ⟨hzS, hxz⟩ := (mem_neighborsIn G).mp hz
        have hmem : x ∈ neighborsIn G S z := (mem_neighborsIn G).mpr ⟨hx, G.adj_symm hxz⟩
        rw [Finset.card_erase_of_mem hmem, hdegree z hzS]
      _ = 12 := by rw [hAc]
  have hrest : (∑ y ∈ S.erase x \ A, (commonIn G S x y).card) ≤
      (S.erase x \ A).card * 2 := by
    calc
      _ ≤ ∑ _y ∈ S.erase x \ A, (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro y hy
        obtain ⟨hy, hnot⟩ := Finset.mem_sdiff.mp hy
        obtain ⟨hne, hyS⟩ := Finset.mem_erase.mp hy
        exact hcommon y hyS hne (fun hadj => hnot ((mem_neighborsIn G).mpr ⟨hyS, hadj⟩))
      _ = _ := by simp
  have hsplit := Finset.sum_sdiff (f := fun y => (commonIn G S x y).card) hA
  have hcard := Finset.card_sdiff_add_card_eq_card hA
  rw [Finset.card_erase_of_mem hx, hAc] at hcard
  change (∑ y ∈ A, (commonIn G S x y).card) = 2 * t at hlocal
  rw [hlocal, htotal] at hsplit
  omega

end GraphCounting

section CubeGeometry

/-- The coordinate set on which two Boolean cube vertices differ. -/
private def diff {n : ℕ} (x y : Q n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ y i)

private theorem diff_card {n : ℕ} (x y : Q n) :
    (diff x y).card = hammingDist x y := rfl

private theorem diff_symm {n : ℕ} (x y : Q n) : diff x y = diff y x := by
  ext i
  simp [diff, ne_comm]

private theorem diff_triangle {n : ℕ} (x y z : Q n) :
    diff x y = (diff x z \ diff y z) ∪ (diff y z \ diff x z) := by
  ext i
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [diff, hx, hy, hz]

private theorem diff_triangle_card {n : ℕ} (x y z : Q n) :
    (diff x y).card + 2 * (diff x z ∩ diff y z).card =
      (diff x z).card + (diff y z).card := by
  have hd : Disjoint (diff x z \ diff y z) (diff y z \ diff x z) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have ha := Finset.card_sdiff_add_card_inter (diff x z) (diff y z)
  have hb := Finset.card_sdiff_add_card_inter (diff y z) (diff x z)
  rw [Finset.inter_comm (diff y z) (diff x z)] at hb
  rw [diff_triangle x y z, Finset.card_union_of_disjoint hd]
  omega

private theorem diff_injective {n : ℕ} (x : Q n) : Function.Injective (diff x) := by
  intro y z h
  funext i
  have hi := Finset.ext_iff.mp h i
  simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;> simp_all

private theorem diff_double_flip {n : ℕ} (x : Q n) {i j : Fin n} (hij : i ≠ j) :
    diff x (flip (flip x i) j) = {i, j} := by
  ext k
  simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, double_flip_apply x hij k]
  by_cases hk : k = i ∨ k = j
  · simp [hk, Bool.self_ne_not]
  · simp [hk]

/-- The distance-two graph on the Boolean cube. Restricting its vertex set
to the selected columns gives the graph used in the counting argument. -/
def distanceTwoGraph (n : ℕ) : SimpleGraph (Q n) where
  Adj x y := hammingDist x y = 2
  symm := ⟨fun x y h => (hammingDist_comm y x).trans h⟩
  loopless := ⟨fun x => by simp⟩

instance (n : ℕ) : DecidableRel (distanceTwoGraph n).Adj :=
  fun x y => inferInstanceAs (Decidable (hammingDist x y = 2))

abbrev columnNeighbors (K : Finset (Q 8)) (q : Q 8) :=
  neighborsIn (distanceTwoGraph 8) K q

abbrev commonColumns (K : Finset (Q 8)) (q p : Q 8) :=
  commonIn (distanceTwoGraph 8) K q p

@[simp] theorem mem_columnNeighbors {K : Finset (Q 8)} {q p : Q 8} :
    p ∈ columnNeighbors K q ↔ p ∈ K ∧ hammingDist q p = 2 :=
  mem_neighborsIn (distanceTwoGraph 8)

@[simp] theorem mem_commonColumns {K : Finset (Q 8)} {q p r : Q 8} :
    r ∈ commonColumns K q p ↔ r ∈ K ∧ hammingDist q r = 2 ∧ hammingDist p r = 2 :=
  mem_commonIn (distanceTwoGraph 8)

variable {K : Finset (Q 8)} {occupied : Q 8 → Bool} {τ σ : Q 8 → ℝ}
variable {q p : Q 8} {i j k : Fin 8}

/-- Column reached by crossing the unique other contact of an empty row. -/
def partnerColumn (K : Finset (Q 8)) (q : Q 8) (i : Fin 8) : Q 8 :=
  flip (flip q i) (partnerAxis K q i)

private theorem partner_ne (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hi : i ∈ emptyDirections occupied q) :
    i ≠ partnerAxis K q i := by
  have he := mem_emptyDirections.mp hi
  have ho := partnerAxis_occupied hs htwo hq he
  intro h
  rw [← h, he] at ho
  contradiction

private theorem diff_partnerColumn (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hi : i ∈ emptyDirections occupied q) :
    diff q (partnerColumn K q i) = {i, partnerAxis K q i} :=
  diff_double_flip q (partner_ne hs htwo hq hi)

private theorem partnerColumn_mem (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hi : i ∈ emptyDirections occupied q) :
    partnerColumn K q i ∈ columnNeighbors K q := by
  have hp := (partnerAxis_eq_iff htwo hq (mem_emptyDirections.mp hi)).mp rfl
  refine mem_columnNeighbors.mpr ⟨hp.1, ?_⟩
  rw [← diff_card, diff_partnerColumn hs htwo hq hi]
  exact Finset.card_pair (partner_ne hs htwo hq hi)

/-- Its four neighbors are indexed by its four empty axes. This is an
induced distance-two graph because the row sign curvature forces a mixed square. -/
theorem columnNeighbors_eq_image (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K) :
    columnNeighbors K q = (emptyDirections occupied q).image (partnerColumn K q) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpK, hd⟩ := mem_columnNeighbors.mp hp
    obtain ⟨r, s, _, he, hrows⟩ := common_rows_of_hammingDist_two hs hq hpK hd
    obtain ⟨hqs, hps⟩ := (hrows s).mpr (Or.inr rfl)
    obtain ⟨i, hi⟩ := adjacent_exists_flip hqs
    obtain ⟨j, hj⟩ := adjacent_exists_flip hps
    have hei : occupied (flip q i) = false := hi ▸ he
    have hpq : p ≠ q := by
      intro h
      subst p
      simp at hd
    have hpij : flip (flip q i) j = p := by rw [← hi, hj, BalancedCriticalSpectrum.flip_flip]
    have hpartner := (partnerAxis_eq_iff htwo hq hei).mpr
      ⟨hpij.symm ▸ hpK, hpij.symm ▸ hpq⟩
    exact Finset.mem_image.mpr ⟨i, mem_emptyDirections.mpr hei,
      by simpa only [partnerColumn, hpartner] using hpij⟩
  · intro hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact partnerColumn_mem hs htwo hq hi

theorem partnerColumn_injOn (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K) :
    Set.InjOn (partnerColumn K q) (emptyDirections occupied q : Set (Fin 8)) := by
  intro i hi j hj h
  have hi' : i ∈ emptyDirections occupied q := Finset.mem_coe.mp hi
  have hj' : j ∈ emptyDirections occupied q := Finset.mem_coe.mp hj
  have hlabels := congrArg (diff q) h
  rw [diff_partnerColumn hs htwo hq hi', diff_partnerColumn hs htwo hq hj'] at hlabels
  have hmem : i ∈ ({j, partnerAxis K q j} : Finset (Fin 8)) :=
    hlabels ▸ (Finset.mem_insert_self i {partnerAxis K q i})
  rcases Finset.mem_insert.mp hmem with hij | hij
  · exact hij
  · have he := mem_emptyDirections.mp hi'
    rw [Finset.mem_singleton.mp hij] at he
    rw [partnerAxis_occupied hs htwo hq (mem_emptyDirections.mp hj')] at he
    contradiction

theorem card_columnNeighbors (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hfour : (emptyDirections occupied q).card = 4) :
    (columnNeighbors K q).card = 4 := by
  rw [columnNeighbors_eq_image hs htwo hq,
    Finset.card_image_of_injOn (partnerColumn_injOn hs htwo hq), hfour]

/-- Two distinct empty axes give adjacent neighbors exactly when they
have the same occupied partner. -/
theorem partnerColumn_adj_iff (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hi : i ∈ emptyDirections occupied q) (hk : k ∈ emptyDirections occupied q)
    (hik : i ≠ k) :
    hammingDist (partnerColumn K q i) (partnerColumn K q k) = 2 ↔
      partnerAxis K q i = partnerAxis K q k := by
  classical
  let a := partnerAxis K q i
  let b := partnerAxis K q k
  have hia : i ≠ a := partner_ne hs htwo hq hi
  have hkb : k ≠ b := partner_ne hs htwo hq hk
  have hib : i ≠ b := by
    intro h
    have he := mem_emptyDirections.mp hi
    rw [h, show occupied (flip q b) = true from
      partnerAxis_occupied hs htwo hq (mem_emptyDirections.mp hk)] at he
    contradiction
  have hka : k ≠ a := by
    intro h
    have he := mem_emptyDirections.mp hk
    rw [h, show occupied (flip q a) = true from
      partnerAxis_occupied hs htwo hq (mem_emptyDirections.mp hi)] at he
    contradiction
  have hc := diff_triangle_card (partnerColumn K q i) (partnerColumn K q k) q
  rw [diff_symm (partnerColumn K q i) q, diff_symm (partnerColumn K q k) q,
    diff_partnerColumn hs htwo hq hi, diff_partnerColumn hs htwo hq hk, diff_card] at hc
  change hammingDist (partnerColumn K q i) (partnerColumn K q k) +
    2 * (({i, a} : Finset (Fin 8)) ∩ {k, b}).card =
      ({i, a} : Finset (Fin 8)).card + ({k, b} : Finset (Fin 8)).card at hc
  have ha : ({i, a} : Finset (Fin 8)).card = 2 := Finset.card_pair hia
  have hb : ({k, b} : Finset (Fin 8)).card = 2 := Finset.card_pair hkb
  rw [ha, hb] at hc
  change hammingDist (partnerColumn K q i) (partnerColumn K q k) = 2 ↔ a = b
  by_cases hab : a = b
  · have hinter : ({i, a} : Finset (Fin 8)) ∩ {k, b} = {a} := by
      ext l
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · exact False.elim (h.elim hik hib)
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, Or.inr hab⟩
    rw [hinter, Finset.card_singleton] at hc
    exact ⟨fun _ => hab, fun _ => by omega⟩
  · have hinter : ({i, a} : Finset (Fin 8)) ∩ {k, b} = ∅ := by
      ext l
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false]
      rintro ⟨rfl | rfl, h⟩
      · exact h.elim hik hib
      · exact h.elim (Ne.symm hka) hab
    rw [hinter, Finset.card_empty] at hc
    exact ⟨fun hd => by omega, fun h => (hab h).elim⟩


/-- Empty axes having the specified occupied partner. -/
def sourceFiber (K : Finset (Q 8)) (occupied : Q 8 → Bool)
    (q : Q 8) (j : Fin 8) : Finset (Fin 8) :=
  (emptyDirections occupied q).filter (fun k => partnerAxis K q k = j)

private theorem mem_sourceFiber :
    i ∈ sourceFiber K occupied q j ↔
      i ∈ emptyDirections occupied q ∧ partnerAxis K q i = j :=
  Finset.mem_filter

/-- The neighbors of a specified neighbor inside the neighborhood at q are
exactly the other sources with its occupied partner. -/
theorem commonColumns_eq_image_fiber_erase
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hi : i ∈ emptyDirections occupied q) :
    commonColumns K q (partnerColumn K q i) =
      ((sourceFiber K occupied q (partnerAxis K q i)).erase i).image (partnerColumn K q) := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨hrK, hqr, hir⟩ := mem_commonColumns.mp hr
    have hrN := mem_columnNeighbors.mpr ⟨hrK, hqr⟩
    rw [columnNeighbors_eq_image hs htwo hq] at hrN
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hrN
    have hik : i ≠ k := by
      intro h
      subst k
      simp at hir
    have he := (partnerColumn_adj_iff hs htwo hq hi hk hik).mp hir
    exact Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr
      ⟨hik.symm, mem_sourceFiber.mpr ⟨hk, he.symm⟩⟩, rfl⟩
  · intro hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hki, hk⟩ := Finset.mem_erase.mp hk
    obtain ⟨hk, he⟩ := mem_sourceFiber.mp hk
    obtain ⟨hrK, hqr⟩ := mem_columnNeighbors.mp (partnerColumn_mem hs htwo hq hk)
    exact mem_commonColumns.mpr ⟨hrK, hqr,
      (partnerColumn_adj_iff hs htwo hq hi hk hki.symm).mpr he.symm⟩

theorem card_commonColumns_of_partner
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hi : i ∈ emptyDirections occupied q) :
    (commonColumns K q (partnerColumn K q i)).card =
      (sourceFiber K occupied q (partnerAxis K q i)).card - 1 := by
  classical
  rw [commonColumns_eq_image_fiber_erase hs htwo hq hi,
    Finset.card_image_of_injOn (show Set.InjOn (partnerColumn K q)
      (↑((sourceFiber K occupied q (partnerAxis K q i)).erase i) : Set (Fin 8)) from by
        intro a ha b hb hab
        exact partnerColumn_injOn hs htwo hq
          (mem_sourceFiber.mp (Finset.mem_erase.mp (Finset.mem_coe.mp ha)).2).1
          (mem_sourceFiber.mp (Finset.mem_erase.mp (Finset.mem_coe.mp hb)).2).1 hab),
    Finset.card_erase_of_mem (mem_sourceFiber.mpr ⟨hi, rfl⟩)]

private theorem partner_fiber_card_cases
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) (hi : i ∈ emptyDirections occupied q) :
    (sourceFiber K occupied q (partnerAxis K q i)).card = 1 ∨
      (sourceFiber K occupied q (partnerAxis K q i)).card = 2 := by
  have ho := partnerAxis_occupied hs htwo hq (mem_emptyDirections.mp hi)
  have hcard := card_rowContacts_of_occupied hs htwo hq ho
  change (rowContacts K (flip q (partnerAxis K q i))).card =
    (sourceFiber K occupied q (partnerAxis K q i)).card + 1 at hcard
  have hle := hthree _ ho
  have hpos := Finset.card_pos.mpr (show (sourceFiber K occupied q (partnerAxis K q i)).Nonempty
    from ⟨i, mem_sourceFiber.mpr ⟨hi, rfl⟩⟩)
  omega

/-- The induced graph on each neighborhood has maximum degree one. -/
theorem card_commonColumns_of_adj_le_one
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) (hp : p ∈ columnNeighbors K q) :
    (commonColumns K q p).card ≤ 1 := by
  rw [columnNeighbors_eq_image hs htwo hq] at hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  rw [card_commonColumns_of_partner hs htwo hq hi]
  rcases partner_fiber_card_cases hs htwo hthree hq hi with h | h <;> omega

/-- The occupied partner axes at which a column has a three-contact row. -/
private def tripleTargets (K : Finset (Q 8)) (occupied : Q 8 → Bool) (q : Q 8) :
    Finset (Fin 8) :=
  Finset.univ.filter (fun j => occupied (flip q j) = true ∧
    (rowContacts K (flip q j)).card = 3)

private theorem card_tripleTargets :
    (tripleTargets K occupied q).card = (threeContactRowsAt K occupied q).card := by
  unfold threeContactRowsAt
  change (tripleTargets K occupied q).card =
    ((tripleTargets K occupied q).image (flip q)).card
  rw [Finset.card_image_of_injective _ (flip_injective q)]

private theorem card_fiber_of_tripleTarget
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hj : j ∈ tripleTargets K occupied q) :
    (sourceFiber K occupied q j).card = 2 := by
  obtain ⟨ho, hc⟩ := (Finset.mem_filter.mp hj).2
  have h := card_rowContacts_of_occupied hs htwo hq ho
  change (rowContacts K (flip q j)).card = (sourceFiber K occupied q j).card + 1 at h
  omega

private theorem card_commonColumns_eq_indicator
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) (hi : i ∈ emptyDirections occupied q) :
    (commonColumns K q (partnerColumn K q i)).card =
      if partnerAxis K q i ∈ tripleTargets K occupied q then 1 else 0 := by
  have ho := partnerAxis_occupied hs htwo hq (mem_emptyDirections.mp hi)
  have hcard := card_rowContacts_of_occupied hs htwo hq ho
  change (rowContacts K (flip q (partnerAxis K q i))).card =
    (sourceFiber K occupied q (partnerAxis K q i)).card + 1 at hcard
  rw [card_commonColumns_of_partner hs htwo hq hi]
  rcases partner_fiber_card_cases hs htwo hthree hq hi with h | h
  · have hnot : partnerAxis K q i ∉ tripleTargets K occupied q := by
      intro hm
      have hc := (Finset.mem_filter.mp hm).2.2
      omega
    simp [h, hnot]
  · have hm : partnerAxis K q i ∈ tripleTargets K occupied q :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho, by omega⟩
    simp [h, hm]

/-- Each three-contact occupied row contributes precisely two ordered incidences
between neighboring columns. Together with the degree-one bound this identifies
the neighborhood as t disjoint edges and 4 - 2*t isolated vertices. -/
theorem sum_commonColumns_at_neighbors
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) :
    (∑ p ∈ columnNeighbors K q, (commonColumns K q p).card) =
      2 * (threeContactRowsAt K occupied q).card := by
  classical
  rw [columnNeighbors_eq_image hs htwo hq,
    Finset.sum_image (partnerColumn_injOn hs htwo hq)]
  calc
    _ = ∑ i ∈ emptyDirections occupied q,
        if partnerAxis K q i ∈ tripleTargets K occupied q then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact card_commonColumns_eq_indicator hs htwo hthree hq hi
    _ = ((emptyDirections occupied q).filter
        (fun i => partnerAxis K q i ∈ tripleTargets K occupied q)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ j ∈ tripleTargets K occupied q, (sourceFiber K occupied q j).card :=
      (Finset.sum_card_fiberwise_eq_card_filter (emptyDirections occupied q)
        (tripleTargets K occupied q) (partnerAxis K q)).symm
    _ = (tripleTargets K occupied q).card * 2 :=
      Finset.sum_const_nat (fun j hj => card_fiber_of_tripleTarget hs htwo hq hj)
    _ = _ := by rw [card_tripleTargets, Nat.mul_comm]

/-- A column has at most two incident three-contact occupied rows. -/
theorem threeContactRowsAt_card_le_two
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) (hfour : (emptyDirections occupied q).card = 4) :
    (threeContactRowsAt K occupied q).card ≤ 2 := by
  have hsum := sum_commonColumns_at_neighbors hs htwo hthree hq
  have hdeg := card_columnNeighbors hs htwo hq hfour
  have hle : (∑ p ∈ columnNeighbors K q, (commonColumns K q p).card) ≤
      ∑ _p ∈ columnNeighbors K q, (1 : ℕ) :=
    Finset.sum_le_sum (fun p hp => card_commonColumns_of_adj_le_one hs htwo hthree hq hp)
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one, hdeg] at hle
  omega

/-- For two distinct nonadjacent columns with a common neighbor, the two
two-coordinate labels are disjoint. Each common neighbor is labelled by
two elements of the four coordinates on which the endpoints differ. -/
private theorem common_label_subset_four {n : ℕ} {x y z : Q n}
    (hne : x ≠ y) (hnadj : hammingDist x y ≠ 2)
    (hxz : hammingDist x z = 2) (hyz : hammingDist y z = 2) :
    (diff x y).card = 4 ∧ diff x z ⊆ diff x y := by
  have hc := diff_triangle_card x y z
  have hpos := hammingDist_pos.mpr hne
  rw [diff_card x y, diff_card x z, diff_card y z, hxz, hyz] at hc
  have hfour : hammingDist x y = 4 := by omega
  have hzero : (diff x z ∩ diff y z).card = 0 := by omega
  refine ⟨hfour, ?_⟩
  intro i hi
  rw [diff_triangle x y z]
  apply Finset.mem_union.mpr
  left
  refine Finset.mem_sdiff.mpr ⟨hi, fun hj => ?_⟩
  have hm := Finset.mem_inter.mpr ⟨hi, hj⟩
  rw [Finset.card_eq_zero.mp hzero] at hm
  simp at hm

/-- In the octahedron of two-element labels in a four-element set, a given
label has only one distinct nonadjacent label: its complement. -/
private theorem common_label_unique_nonadjacent {n : ℕ} {x y a b c : Q n}
    (hxy : (diff x y).card = 4)
    (ha : diff x a ⊆ diff x y) (hb : diff x b ⊆ diff x y)
    (hc : diff x c ⊆ diff x y)
    (hxa : hammingDist x a = 2) (hxb : hammingDist x b = 2)
    (hxc : hammingDist x c = 2)
    (hab : a ≠ b) (hac : a ≠ c)
    (hnab : hammingDist a b ≠ 2) (hnac : hammingDist a c ≠ 2) :
    b = c := by
  have hAB := diff_triangle_card a b x
  have hAC := diff_triangle_card a c x
  rw [diff_symm a x, diff_symm b x, diff_card a b, diff_card x a, diff_card x b,
    hxa, hxb] at hAB
  rw [diff_symm a x, diff_symm c x, diff_card a c, diff_card x a, diff_card x c,
    hxa, hxc] at hAC
  have hpAB := hammingDist_pos.mpr hab
  have hpAC := hammingDist_pos.mpr hac
  have hzeroAB : (diff x a ∩ diff x b).card = 0 := by omega
  have hzeroAC : (diff x a ∩ diff x c).card = 0 := by omega
  let D := diff x y \ diff x a
  have hD : D.card = 2 := by
    change (diff x y \ diff x a).card = 2
    rw [Finset.card_sdiff_of_subset ha, hxy, diff_card, hxa]
  have hB : diff x b ⊆ D := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨hb hi, fun hia => ?_⟩
    have hm := Finset.mem_inter.mpr ⟨hia, hi⟩
    rw [Finset.card_eq_zero.mp hzeroAB] at hm
    simp at hm
  have hC : diff x c ⊆ D := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨hc hi, fun hia => ?_⟩
    have hm := Finset.mem_inter.mpr ⟨hia, hi⟩
    rw [Finset.card_eq_zero.mp hzeroAC] at hm
    simp at hm
  have hBeq := Finset.eq_of_subset_of_card_le hB (by rw [hD, diff_card, hxb])
  have hCeq := Finset.eq_of_subset_of_card_le hC (by rw [hD, diff_card, hxc])
  exact diff_injective x (hBeq.trans hCeq.symm)

/-- Nonadjacent columns have at most two common neighbors. Three of the
octahedron labels necessarily induce a vertex with two neighbors, contrary
to the matching structure of the neighborhood. -/
theorem card_commonColumns_of_nonadj_le_two
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) (hqp : q ≠ p) (hnadj : hammingDist q p ≠ 2) :
    (commonColumns K q p).card ≤ 2 := by
  by_contra! hbig
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hbig
  obtain ⟨haK, hqa, hpa⟩ := mem_commonColumns.mp ha
  obtain ⟨hbK, hqb, hpb⟩ := mem_commonColumns.mp hb
  obtain ⟨hcK, hqc, hpc⟩ := mem_commonColumns.mp hc
  obtain ⟨hfour, hA⟩ := common_label_subset_four hqp hnadj hqa hpa
  have hB := (common_label_subset_four hqp hnadj hqb hpb).2
  have hC := (common_label_subset_four hqp hnadj hqc hpc).2
  have htwoedges {u v w : Q 8} (hu : u ∈ columnNeighbors K q)
      (hv : v ∈ columnNeighbors K q) (hw : w ∈ columnNeighbors K q)
      (hvw : v ≠ w) (huv : hammingDist u v = 2) (huw : hammingDist u w = 2) : False := by
    have hv' := mem_columnNeighbors.mp hv
    have hw' := mem_columnNeighbors.mp hw
    have hle := card_commonColumns_of_adj_le_one hs htwo hthree hq hu
    have hbetween := Finset.card_le_one.mp hle
    exact hvw (hbetween v (mem_commonColumns.mpr ⟨hv'.1, hv'.2, huv⟩)
      w (mem_commonColumns.mpr ⟨hw'.1, hw'.2, huw⟩))
  have hna : a ∈ columnNeighbors K q := mem_columnNeighbors.mpr ⟨haK, hqa⟩
  have hnb : b ∈ columnNeighbors K q := mem_columnNeighbors.mpr ⟨hbK, hqb⟩
  have hnc : c ∈ columnNeighbors K q := mem_columnNeighbors.mpr ⟨hcK, hqc⟩
  by_cases hab' : hammingDist a b = 2
  · have hac' : hammingDist a c ≠ 2 := fun h => htwoedges hna hnb hnc hbc hab' h
    have hbc' : hammingDist b c ≠ 2 := fun h =>
      htwoedges hnb hna hnc hac ((hammingDist_comm b a).trans hab') h
    exact hab (common_label_unique_nonadjacent hfour hC hA hB hqc hqa hqb
      hac.symm hbc.symm (by simpa only [hammingDist_comm c a] using hac')
      (by simpa only [hammingDist_comm c b] using hbc'))
  · by_cases hac' : hammingDist a c = 2
    · have hcb' : hammingDist c b ≠ 2 := fun h =>
        htwoedges hnc hna hnb hab ((hammingDist_comm c a).trans hac') h
      exact hac (common_label_unique_nonadjacent hfour hB hA hC hqb hqa hqc
        hab.symm hbc (by simpa only [hammingDist_comm b a] using hab')
        (by simpa only [hammingDist_comm b c] using hcb'))
    · exact hbc (common_label_unique_nonadjacent hfour hA hB hC hqa hqb hqc
        hab hac hab' hac')

/-- The pointwise order bound follows from the geometry alone. -/
theorem eleven_le_card_add_threeContactRowsAt
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ q ∈ K, (emptyDirections occupied q).card = 4)
    (hq : q ∈ K) :
    11 ≤ K.card + (threeContactRowsAt K occupied q).card := by
  apply eleven_le_card_add_of_two_step_count (distanceTwoGraph 8) K q hq
  · intro p hp
    exact card_columnNeighbors hs htwo hp (hfour p hp)
  · intro p _ hne hn
    exact card_commonColumns_of_nonadj_le_two hs htwo hthree hq hne.symm hn
  · exact sum_commonColumns_at_neighbors hs htwo hthree hq

end CubeGeometry

section CardinalityGap

variable {K : Finset (Q 8)} {occupied : Q 8 → Bool} {τ σ : Q 8 → ℝ}
variable {q : Q 8}

/-- The occupied rows supporting a triangle of columns. -/
def threeContactRows (K : Finset (Q 8)) (occupied : Q 8 → Bool) : Finset (Q 8) :=
  Finset.univ.filter (fun r => occupied r = true ∧ (rowContacts K r).card = 3)

/-- Every three-contact occupied row contributes exactly three incidences. -/
theorem sum_threeContactRowsAt (K : Finset (Q 8)) (occupied : Q 8 → Bool) :
    (∑ q ∈ K, (threeContactRowsAt K occupied q).card) =
      3 * (threeContactRows K occupied).card := by
  classical
  calc
    _ = ∑ q ∈ K, ((threeContactRows K occupied).filter
        (fun r => (hypercube 8).Adj q r)).card := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      ext r
      simp only [mem_threeContactRowsAt, threeContactRows, Finset.mem_filter,
        Finset.mem_univ, true_and]
      tauto
    _ = ∑ r ∈ threeContactRows K occupied,
        (K.filter (fun q => (hypercube 8).Adj q r)).card :=
      sum_card_filter_swap K (threeContactRows K occupied) (fun q r => (hypercube 8).Adj q r)
    _ = (threeContactRows K occupied).card * 3 := by
      apply Finset.sum_const_nat
      intro r hr
      exact (Finset.mem_filter.mp hr).2.2
    _ = _ := Nat.mul_comm _ _

/-- The counts of the three allowed column types partition the column set,
and their triangle incidence is the corresponding weighted sum. -/
theorem columnCount_partition_and_incidence
    (ht : ∀ q ∈ K, (threeContactRowsAt K occupied q).card ≤ 2) :
    columnCount K occupied 0 + columnCount K occupied 1 + columnCount K occupied 2 = K.card ∧
      columnCount K occupied 1 + 2 * columnCount K occupied 2 =
        3 * (threeContactRows K occupied).card := by
  classical
  let t (q : Q 8) := (threeContactRowsAt K occupied q).card
  have hcases (q : Q 8) (hq : q ∈ K) : t q = 0 ∨ t q = 1 ∨ t q = 2 := by
    have h := ht q hq
    change t q ≤ 2 at h
    omega
  have hpartition :
      (∑ q ∈ K, ((if t q = 0 then (1 : ℕ) else 0) +
        (if t q = 1 then 1 else 0) + (if t q = 2 then 1 else 0))) = K.card := by
    calc
      _ = ∑ _q ∈ K, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro q hq
        rcases hcases q hq with h | h | h <;> simp [h]
      _ = _ := by simp
  have hinc :
      (∑ q ∈ K, ((if t q = 1 then (1 : ℕ) else 0) +
        (if t q = 2 then 2 else 0))) = 3 * (threeContactRows K occupied).card := by
    calc
      _ = ∑ q ∈ K, t q := by
        apply Finset.sum_congr rfl
        intro q hq
        rcases hcases q hq with h | h | h <;> simp [h]
      _ = _ := sum_threeContactRowsAt K occupied
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, Nat.nsmul_eq_mul, mul_one] at hpartition hinc
  unfold columnCount
  constructor
  · exact hpartition
  · simpa only [Nat.mul_comm 2] using hinc

/-- Delete every edge that belongs to a triangle. -/
def triangleFreeNeighbors (K : Finset (Q 8)) (q : Q 8) : Finset (Q 8) :=
  (columnNeighbors K q).filter (fun p => (commonColumns K q p).card = 0)

@[simp] theorem mem_triangleFreeNeighbors {p : Q 8} :
    p ∈ triangleFreeNeighbors K q ↔
      p ∈ K ∧ hammingDist q p = 2 ∧ (commonColumns K q p).card = 0 := by
  simp only [triangleFreeNeighbors, Finset.mem_filter, mem_columnNeighbors, and_assoc]

theorem mem_triangleFreeNeighbors_symm {p : Q 8} (hq : q ∈ K)
    (hp : p ∈ triangleFreeNeighbors K q) :
    q ∈ triangleFreeNeighbors K p := by
  obtain ⟨_, hd, hc⟩ := mem_triangleFreeNeighbors.mp hp
  exact mem_triangleFreeNeighbors.mpr ⟨hq, (hammingDist_comm p q).trans hd,
    by
      change (columnNeighbors K p ∩ columnNeighbors K q).card = 0
      rw [Finset.inter_comm]
      exact hc⟩

/-- After removal of the triangle edges, the residual degree is 4 - 2*t. -/
theorem card_triangleFreeNeighbors_add_twice
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) (hfour : (emptyDirections occupied q).card = 4) :
    (triangleFreeNeighbors K q).card + 2 * (threeContactRowsAt K occupied q).card = 4 := by
  classical
  have hsum :
      (∑ p ∈ columnNeighbors K q,
        ((if (commonColumns K q p).card = 0 then (1 : ℕ) else 0) +
          (commonColumns K q p).card)) = 4 := by
    calc
      _ = ∑ _p ∈ columnNeighbors K q, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hle := card_commonColumns_of_adj_le_one hs htwo hthree hq hp
        have hcases : (commonColumns K q p).card = 0 ∨ (commonColumns K q p).card = 1 := by omega
        rcases hcases with h | h <;> simp [h]
      _ = _ := by simp [card_columnNeighbors hs htwo hq hfour]
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, Nat.nsmul_eq_mul, mul_one,
    sum_commonColumns_at_neighbors hs htwo hthree hq] at hsum
  exact hsum

/-- A nonempty two-contact column set has at least nine columns.
The stronger pointwise inequality was proved above and uses only geometry. -/
theorem nine_le_card_of_twoContact (hK : K.Nonempty)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ q ∈ K, (emptyDirections occupied q).card = 4) :
    9 ≤ K.card := by
  obtain ⟨q, hq⟩ := hK
  have hlower := eleven_le_card_add_threeContactRowsAt hs htwo hthree hfour hq
  have hupper := threeContactRowsAt_card_le_two hs htwo hthree hq (hfour q hq)
  omega

/-- Ten columns would force exactly two vertices of residual degree two.
Since every other vertex would have residual degree zero, these two vertices
cannot have two distinct neighbors in a simple graph. -/
theorem card_ne_ten_of_twoContact
    {v : Q 8 → Exponent 8}
    (hK : K.Nonempty)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (hv : EmptyGain (K : Set (Q 8)) occupied v)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ q ∈ K, (emptyDirections occupied q).card = 4) :
    K.card ≠ 10 := by
  classical
  intro hn
  have hupper (q : Q 8) (hq : q ∈ K) :
      (threeContactRowsAt K occupied q).card ≤ 2 :=
    threeContactRowsAt_card_le_two hs htwo hthree hq (hfour q hq)
  have hlower (q : Q 8) (hq : q ∈ K) :
      1 ≤ (threeContactRowsAt K occupied q).card := by
    have h := eleven_le_card_add_threeContactRowsAt hs htwo hthree hfour hq
    omega
  obtain ⟨hpartition, hinc⟩ := columnCount_partition_and_incidence hupper
  have hcover := weighted_order_coverage_of_cube K hK occupied τ σ v hs hv hfour htwo hthree
  have hzero : columnCount K occupied 0 = 0 := by
    unfold columnCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨hqK, ht⟩ := Finset.mem_filter.mp hq
    have h := hlower q hqK
    omega
  have hone : columnCount K occupied 1 = 2 := by omega
  have htwoCount : columnCount K occupied 2 = 8 := by omega
  let S := K.filter (fun q => (threeContactRowsAt K occupied q).card = 1)
  have hS : S.card = 2 := hone
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨hqK, hqt⟩ := Finset.mem_filter.mp (show q ∈ K.filter
    (fun q => (threeContactRowsAt K occupied q).card = 1) from hq)
  have hdeg := card_triangleFreeNeighbors_add_twice hs htwo hthree hqK (hfour q hqK)
  have hdeg2 : (triangleFreeNeighbors K q).card = 2 := by omega
  have hsub : triangleFreeNeighbors K q ⊆ S.erase q := by
    intro p hp
    obtain ⟨hpK, hd, _⟩ := mem_triangleFreeNeighbors.mp hp
    have hpq : p ≠ q := by
      intro h
      subst p
      simp at hd
    have hback := mem_triangleFreeNeighbors_symm hqK hp
    have hpos : 0 < (triangleFreeNeighbors K p).card := Finset.card_pos.mpr ⟨q, hback⟩
    have hpdeg := card_triangleFreeNeighbors_add_twice hs htwo hthree hpK (hfour p hpK)
    have hplower := hlower p hpK
    have hpt : (threeContactRowsAt K occupied p).card = 1 := by omega
    exact Finset.mem_erase.mpr ⟨hpq, Finset.mem_filter.mpr ⟨hpK, hpt⟩⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hq, hS, hdeg2] at hle
  omega

/-- Cardinality gap for the actual Q8 column set under the same hypotheses
as the compiled weighted coordinate-order coverage theorem. -/
theorem cardinality_gap_of_twoContact
    (K : Finset (Q 8)) (hK : K.Nonempty)
    (occupied : Q 8 → Bool) (τ σ : Q 8 → ℝ) (v : Q 8 → Exponent 8)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (hv : EmptyGain (K : Set (Q 8)) occupied v)
    (hfour : ∀ q ∈ K, (emptyDirections occupied q).card = 4)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3) :
    9 ≤ K.card ∧ K.card ≠ 10 := by
  exact ⟨nine_le_card_of_twoContact hK hs htwo hthree hfour,
    card_ne_ten_of_twoContact hK hs hv htwo hthree hfour⟩

end CardinalityGap

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap
