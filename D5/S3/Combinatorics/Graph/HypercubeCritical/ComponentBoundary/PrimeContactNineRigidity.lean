/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactNineRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactNineRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Nine signed two-contact columns have a two-triple Cartesian grid and constant occupied center. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap

/-!
# Nine-column rigidity for two-contact Huang cube columns

Equality in the two-step count determines the actual Boolean cube embedding,
and the sign equations determine its empty directions. This is the nine-column
case of the projection obstruction for Hong–Wu–Xia, arXiv:2610.09483v1, §7,
Problem 2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactNineRigidity

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj flip_flip)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (flip_injective)
open PrimeContactCubeLift (RowSigns occupied_ne_at_common_rows)
open PrimeContactCubeOrders PrimeContactCardinalityGap
open private diff diff_card diff_symm diff_triangle diff_triangle_card diff_double_flip
  diff_injective diff_partnerColumn partnerColumn_mem mem_sourceFiber tripleTargets
  card_tripleTargets card_fiber_of_tripleTarget common_label_subset_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap
open private double_flip_apply from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeLift

variable {K : Finset (Q 8)} {occupied : Q 8 → Bool} {τ σ : Q 8 → ℝ}
variable {q : Q 8}

/-- At equality every column meets two three-contact occupied rows. -/
theorem threeContactRowsAt_card_eq_two_of_nine (hK : K.card = 9)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ p ∈ K, (emptyDirections occupied p).card = 4)
    (hq : q ∈ K) : (threeContactRowsAt K occupied q).card = 2 := by
  have hl := eleven_le_card_add_threeContactRowsAt hs htwo hthree hfour hq
  have hu := threeContactRowsAt_card_le_two hs htwo hthree hq (hfour q hq)
  omega

/-- The four root neighbors form two pairs of adjacent vertices. -/
theorem card_commonColumns_of_adj_eq_one_of_nine (hK : K.card = 9)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ p ∈ K, (emptyDirections occupied p).card = 4)
    (hq : q ∈ K) {p : Q 8} (hp : p ∈ columnNeighbors K q) :
    (commonColumns K q p).card = 1 := by
  have ht := threeContactRowsAt_card_eq_two_of_nine hK hs htwo hthree hfour hq
  have hdeg := card_columnNeighbors hs htwo hq (hfour q hq)
  have hsum := sum_commonColumns_at_neighbors hs htwo hthree hq
  have hle (r) (hr : r ∈ columnNeighbors K q) :=
    card_commonColumns_of_adj_le_one hs htwo hthree hq hr
  by_contra hn
  have hlt := Finset.sum_lt_sum (s := columnNeighbors K q)
    (f := fun r => (commonColumns K q r).card) (g := fun _ => (1 : ℕ))
    hle ⟨p, hp, by have := hle p hp; omega⟩
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one, hdeg] at hlt
  omega

/-- Equality in the two-step count saturates the common-neighbor bound at
all four columns outside a root and its neighborhood. -/
theorem card_commonColumns_of_nonadj_eq_two_of_nine (hK : K.card = 9)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ p ∈ K, (emptyDirections occupied p).card = 4)
    (hq : q ∈ K) {p : Q 8} (hp : p ∈ K) (hpq : p ≠ q)
    (hnadj : hammingDist q p ≠ 2) : (commonColumns K q p).card = 2 := by
  classical
  let N := columnNeighbors K q
  let R := K.erase q \ N
  have hN : N ⊆ K.erase q := by
    intro x hx
    obtain ⟨hxK, hd⟩ := mem_columnNeighbors.mp hx
    refine Finset.mem_erase.mpr ⟨?_, hxK⟩
    intro he
    subst x
    simp at hd
  have hNcard : N.card = 4 := card_columnNeighbors hs htwo hq (hfour q hq)
  have hRcard : R.card = 4 := by
    have hh := Finset.card_sdiff_add_card_eq_card hN
    rw [Finset.card_erase_of_mem hq, hK, hNcard] at hh
    change R.card + 4 = 8 at hh
    omega
  have htotal : (∑ x ∈ K.erase q, (commonColumns K q x).card) = 12 := by
    calc
      _ = ∑ x ∈ K.erase q, (N.filter (fun y => hammingDist x y = 2)).card := by
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        ext y
        simp only [Finset.mem_filter, mem_commonColumns, N, mem_columnNeighbors, and_assoc]
      _ = ∑ y ∈ N, ((K.erase q).filter (fun x => hammingDist x y = 2)).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (r := fun x y => hammingDist x y = 2) (s := K.erase q) (t := N)
      _ = ∑ y ∈ N, ((columnNeighbors K y).erase q).card := by
        apply Finset.sum_congr rfl
        intro y _
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase, mem_columnNeighbors,
          hammingDist_comm x y, and_assoc]
      _ = N.card * 3 := by
        apply Finset.sum_const_nat
        intro y hy
        obtain ⟨hyK, hqy⟩ := mem_columnNeighbors.mp hy
        have hmem : q ∈ columnNeighbors K y :=
          mem_columnNeighbors.mpr ⟨hq, (hammingDist_comm y q).trans hqy⟩
        rw [Finset.card_erase_of_mem hmem, card_columnNeighbors hs htwo hyK (hfour y hyK)]
      _ = 12 := by rw [hNcard]
  have hlocal := sum_commonColumns_at_neighbors hs htwo hthree hq
  rw [threeContactRowsAt_card_eq_two_of_nine hK hs htwo hthree hfour hq] at hlocal
  change (∑ x ∈ N, (commonColumns K q x).card) = 2 * 2 at hlocal
  have hsplit := Finset.sum_sdiff (f := fun x => (commonColumns K q x).card) hN
  change (∑ x ∈ R, (commonColumns K q x).card) +
    (∑ x ∈ N, (commonColumns K q x).card) = _ at hsplit
  rw [hlocal, htotal] at hsplit
  have hsumR : (∑ x ∈ R, (commonColumns K q x).card) = 8 := by omega
  have hle (x) (hx : x ∈ R) : (commonColumns K q x).card ≤ 2 := by
    obtain ⟨hx', hn⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hne, hxK⟩ := Finset.mem_erase.mp hx'
    exact card_commonColumns_of_nonadj_le_two hs htwo hthree hq hne.symm
      (fun hd => hn (mem_columnNeighbors.mpr ⟨hxK, hd⟩))
  have hpR : p ∈ R := Finset.mem_sdiff.mpr
    ⟨Finset.mem_erase.mpr ⟨hpq, hp⟩, fun hn => hnadj (mem_columnNeighbors.mp hn).2⟩
  by_contra hn
  have hlt := Finset.sum_lt_sum (s := R) (f := fun x => (commonColumns K q x).card)
    (g := fun _ => (2 : ℕ)) hle ⟨p, hpR, by have := hle p hpR; omega⟩
  rw [hsumR] at hlt
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, hRcard] at hlt
  omega

/-- A signed translate of the column with one set coordinate in each triple. -/
def gridVertex (c : Q 8) (a b : Fin 8) : Q 8 := flip (flip c a) b

/-- All columns of a signed translate of the three-by-three grid. -/
def nineGrid (c : Q 8) (A B : Finset (Fin 8)) : Finset (Q 8) :=
  (A ×ˢ B).image (fun ab => gridVertex c ab.1 ab.2)

@[simp] theorem mem_nineGrid {c : Q 8} {A B : Finset (Fin 8)} {p : Q 8} :
    p ∈ nineGrid c A B ↔ ∃ a ∈ A, ∃ b ∈ B, gridVertex c a b = p := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, hp⟩ := Finset.mem_image.mp h
    exact ⟨a, (Finset.mem_product.mp hab).1, b, (Finset.mem_product.mp hab).2, hp⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

private theorem cross_ne {A B : Finset (Fin 8)} (hAB : Disjoint A B)
    {a b : Fin 8} (ha : a ∈ A) (hb : b ∈ B) : a ≠ b := by
  intro h
  exact Finset.disjoint_left.mp hAB (h ▸ ha) hb

private theorem gridVertex_diff {c : Q 8} {a b : Fin 8} (hab : a ≠ b) :
    diff c (gridVertex c a b) = {a, b} := diff_double_flip c hab

private def axisChange (a x : Fin 8) : Finset (Fin 8) :=
  if a = x then ∅ else {a, x}

private theorem axisChange_subset {A : Finset (Fin 8)} {a x : Fin 8}
    (ha : a ∈ A) (hx : x ∈ A) : axisChange a x ⊆ A := by
  intro i hi
  by_cases h : a = x
  · simp [axisChange, h] at hi
  · simp only [axisChange, if_neg h, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption

private theorem card_axisChange (a x : Fin 8) :
    (axisChange a x).card = if a = x then 0 else 2 := by
  by_cases h : a = x <;> simp [axisChange, h, Finset.card_pair]

/-- The cube labels between two grid points are the disjoint axis changes
within the two triples. -/
private theorem gridVertex_diff_gridVertex {c : Q 8} {A B : Finset (Fin 8)}
    (hAB : Disjoint A B) {a x b y : Fin 8}
    (ha : a ∈ A) (hx : x ∈ A) (hb : b ∈ B) (hy : y ∈ B) :
    diff (gridVertex c a b) (gridVertex c x y) = axisChange a x ∪ axisChange b y := by
  have hab := cross_ne hAB ha hb
  have hay := cross_ne hAB ha hy
  have hxb := cross_ne hAB hx hb
  have hxy := cross_ne hAB hx hy
  rw [diff_triangle (gridVertex c a b) (gridVertex c x y) c,
    diff_symm (gridVertex c a b) c, diff_symm (gridVertex c x y) c,
    gridVertex_diff hab, gridVertex_diff hxy]
  ext i
  by_cases hax : a = x <;> by_cases hby : b = y <;>
    simp only [axisChange, hax, hby, if_true, if_false, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> grind

/-- The induced distance-two graph of the embedding is the Cartesian product
of two triangles. The Hamming distance is twice the number of changed factors. -/
theorem hammingDist_gridVertex {c : Q 8} {A B : Finset (Fin 8)}
    (hAB : Disjoint A B) {a x b y : Fin 8}
    (ha : a ∈ A) (hx : x ∈ A) (hb : b ∈ B) (hy : y ∈ B) :
    hammingDist (gridVertex c a b) (gridVertex c x y) =
      (if a = x then 0 else 2) + (if b = y then 0 else 2) := by
  rw [← diff_card, gridVertex_diff_gridVertex hAB ha hx hb hy,
    Finset.card_union_of_disjoint (hAB.mono (axisChange_subset ha hx) (axisChange_subset hb hy)),
    card_axisChange, card_axisChange]

private theorem gridVertex_involutive (q : Q 8) (a b : Fin 8) :
    gridVertex (gridVertex q a b) a b = q := by
  unfold gridVertex
  rw [flip_comm (flip q a) b a, BalancedCriticalSpectrum.flip_flip, BalancedCriticalSpectrum.flip_flip]

/-- If a nonneighbor of the root is adjacent to two neighbors with disjoint
labels, its root label is exactly their union. This is the four-axis XOR
rectangle completion, proved in the actual cube rather than an abstract graph. -/
private theorem mixed_label {q p s r : Q 8}
    (hrq : r ≠ q) (hn : hammingDist q r ≠ 2)
    (hqp : hammingDist q p = 2) (hqs : hammingDist q s = 2)
    (hrp : hammingDist r p = 2) (hrs : hammingDist r s = 2)
    (hd : Disjoint (diff q p) (diff q s)) :
    diff q r = diff q p ∪ diff q s := by
  obtain ⟨hc, hp⟩ := common_label_subset_four hrq.symm hn hqp hrp
  have hs := (common_label_subset_four hrq.symm hn hqs hrs).2
  have hsub := Finset.union_subset hp hs
  have hcard : (diff q p ∪ diff q s).card = 4 := by
    rw [Finset.card_union_of_disjoint hd, diff_card, diff_card, hqp, hqs]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc, hcard])).symm

/-- There is no outside common neighbor of the two members of a root pair.
Their one permitted common neighbor is the root itself. -/
private theorem outside_not_same_partner
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) {r : Q 8} (hr : r ∈ K) (hrq : r ≠ q)
    {i j : Fin 8} (hi : i ∈ emptyDirections occupied q)
    (hj : j ∈ emptyDirections occupied q) (hij : i ≠ j)
    (hri : hammingDist r (partnerColumn K q i) = 2)
    (hrj : hammingDist r (partnerColumn K q j) = 2) :
    partnerAxis K q i ≠ partnerAxis K q j := by
  intro he
  obtain ⟨hip, hqi⟩ := mem_columnNeighbors.mp (partnerColumn_mem hs htwo hq hi)
  obtain ⟨hjp, hqj⟩ := mem_columnNeighbors.mp (partnerColumn_mem hs htwo hq hj)
  have hadj := (partnerColumn_adj_iff hs htwo hq hi hj hij).mpr he
  have hnb : partnerColumn K q j ∈ columnNeighbors K (partnerColumn K q i) :=
    mem_columnNeighbors.mpr ⟨hjp, hadj⟩
  have hle := card_commonColumns_of_adj_le_one hs htwo hthree hip hnb
  have hqmem : q ∈ commonColumns K (partnerColumn K q i) (partnerColumn K q j) :=
    mem_commonColumns.mpr ⟨hq, (hammingDist_comm _ q).trans hqi,
      (hammingDist_comm _ q).trans hqj⟩
  have hrmem : r ∈ commonColumns K (partnerColumn K q i) (partnerColumn K q j) :=
    mem_commonColumns.mpr ⟨hr, (hammingDist_comm _ r).trans hri,
      (hammingDist_comm _ r).trans hrj⟩
  exact hrq (Finset.card_le_one.mp hle r hrmem q hqmem)

/-- Equality forces a signed translate of the full three-by-three grid in Q8.
The six active axes come from the two occupied triple targets at a root and
their respective pairs of empty source axes. -/
theorem eq_nineGrid_of_twoContact (hK : K.card = 9)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ p ∈ K, (emptyDirections occupied p).card = 4) :
    ∃ c : Q 8, ∃ A B : Finset (Fin 8),
      A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧ K = nineGrid c A B := by
  classical
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < K.card by omega)
  have ht := threeContactRowsAt_card_eq_two_of_nine hK hs htwo hthree hfour hq
  have hT : (tripleTargets K occupied q).card = 2 := card_tripleTargets.trans ht
  obtain ⟨a, b, hab, hT⟩ := Finset.card_eq_two.mp hT
  have haT : a ∈ tripleTargets K occupied q := by rw [hT]; simp
  have hbT : b ∈ tripleTargets K occupied q := by rw [hT]; simp
  have hao := (Finset.mem_filter.mp haT).2.1
  have hbo := (Finset.mem_filter.mp hbT).2.1
  let E := emptyDirections occupied q
  let U := sourceFiber K occupied q a
  let V := sourceFiber K occupied q b
  have hU : U.card = 2 := card_fiber_of_tripleTarget hs htwo hq haT
  have hV : V.card = 2 := card_fiber_of_tripleTarget hs htwo hq hbT
  have hUE : U ⊆ E := fun _ hi => (mem_sourceFiber.mp hi).1
  have hVE : V ⊆ E := fun _ hi => (mem_sourceFiber.mp hi).1
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hab ((mem_sourceFiber.mp hi).2.symm.trans (mem_sourceFiber.mp hj).2)
  have haE : a ∉ E := by
    intro h
    have hh := mem_emptyDirections.mp h
    rw [hao] at hh
    contradiction
  have hbE : b ∉ E := by
    intro h
    have hh := mem_emptyDirections.mp h
    rw [hbo] at hh
    contradiction
  have hcover : U ∪ V = E := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hUE hVE)
    rw [Finset.card_union_of_disjoint hUV, hU, hV]
    exact le_of_eq (hfour q hq)
  let A := insert a U
  let B := insert b V
  have hA : A.card = 3 := by
    change (insert a U).card = 3
    rw [Finset.card_insert_of_notMem (fun h => haE (hUE h)), hU]
  have hB : B.card = 3 := by
    change (insert b V).card = 3
    rw [Finset.card_insert_of_notMem (fun h => hbE (hVE h)), hV]
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rcases Finset.mem_insert.mp hj with h | hj
      · exact hab h
      · exact haE (hVE hj)
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hbE (hUE hi)
      · exact Finset.disjoint_left.mp hUV hi hj
  have haA : a ∈ A := Finset.mem_insert_self _ _
  have hbB : b ∈ B := Finset.mem_insert_self _ _
  have hUA : U ⊆ A := fun _ hi => Finset.mem_insert_of_mem hi
  have hVB : V ⊆ B := fun _ hi => Finset.mem_insert_of_mem hi
  let c := gridVertex q a b
  have hroot : gridVertex c a b = q := gridVertex_involutive q a b
  have hlabelU (i : Fin 8) (hi : i ∈ U) : diff q (partnerColumn K q i) = {i, a} := by
    rw [diff_partnerColumn hs htwo hq (hUE hi), (mem_sourceFiber.mp hi).2]
  have hlabelV (j : Fin 8) (hj : j ∈ V) : diff q (partnerColumn K q j) = {j, b} := by
    rw [diff_partnerColumn hs htwo hq (hVE hj), (mem_sourceFiber.mp hj).2]
  have hchangeU (i : Fin 8) (hi : i ∈ U) : axisChange a i = {i, a} := by
    have hn : a ≠ i := fun h => haE (hUE (h.symm ▸ hi))
    rw [axisChange, if_neg hn, Finset.pair_comm]
  have hchangeV (j : Fin 8) (hj : j ∈ V) : axisChange b j = {j, b} := by
    have hn : b ≠ j := fun h => hbE (hVE (h.symm ▸ hj))
    rw [axisChange, if_neg hn, Finset.pair_comm]
  have hgridlabel (x y : Fin 8) (hx : x ∈ A) (hy : y ∈ B) :
      diff q (gridVertex c x y) = axisChange a x ∪ axisChange b y := by
    rw [← hroot]
    exact gridVertex_diff_gridVertex hAB haA hx hbB hy
  have hneighborU (i : Fin 8) (hi : i ∈ U) :
      gridVertex c i b = partnerColumn K q i := by
    apply diff_injective q
    rw [hgridlabel i b (hUA hi) hbB, hchangeU i hi, hlabelU i hi] <;>
      simp [axisChange]
  have hneighborV (j : Fin 8) (hj : j ∈ V) :
      gridVertex c a j = partnerColumn K q j := by
    apply diff_injective q
    rw [hgridlabel a j haA (hVB hj), hchangeV j hj, hlabelV j hj] <;>
      simp [axisChange]
  have hmixed (r : Q 8) (hrq : r ≠ q) (hn : hammingDist q r ≠ 2)
      (i j : Fin 8) (hi : i ∈ U) (hj : j ∈ V)
      (hri : hammingDist r (partnerColumn K q i) = 2)
      (hrj : hammingDist r (partnerColumn K q j) = 2) :
      gridVertex c i j = r := by
    have hdisj : Disjoint (diff q (partnerColumn K q i)) (diff q (partnerColumn K q j)) := by
      rw [hlabelU i hi, hlabelV j hj]
      apply hAB.mono
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hUA hi
        · rw [Finset.mem_singleton.mp hk]
          exact haA
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hVB hj
        · rw [Finset.mem_singleton.mp hk]
          exact hbB
    have he := mixed_label hrq hn
      (mem_columnNeighbors.mp (partnerColumn_mem hs htwo hq (hUE hi))).2
      (mem_columnNeighbors.mp (partnerColumn_mem hs htwo hq (hVE hj))).2 hri hrj hdisj
    apply diff_injective q
    rw [hgridlabel i j (hUA hi) (hVB hj), hchangeU i hi, hchangeV j hj,
      he, hlabelU i hi, hlabelV j hj]
  have hsub : K ⊆ nineGrid c A B := by
    intro r hr
    by_cases hrq : r = q
    · subst r
      exact mem_nineGrid.mpr ⟨a, haA, b, hbB, hroot⟩
    by_cases hd : hammingDist q r = 2
    · have h := mem_columnNeighbors.mpr ⟨hr, hd⟩
      rw [columnNeighbors_eq_image hs htwo hq] at h
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      change i ∈ E at hi
      rw [← hcover] at hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact mem_nineGrid.mpr ⟨i, hUA hi, b, hbB, hneighborU i hi⟩
      · exact mem_nineGrid.mpr ⟨a, haA, i, hVB hi, hneighborV i hi⟩
    · have hc := card_commonColumns_of_nonadj_eq_two_of_nine hK hs htwo hthree hfour hq hr hrq hd
      obtain ⟨p, s, hps, hc⟩ := Finset.card_eq_two.mp hc
      have hp : p ∈ commonColumns K q r := by rw [hc]; simp
      have hs' : s ∈ commonColumns K q r := by rw [hc]; simp
      obtain ⟨hpK, hqp, hrp⟩ := mem_commonColumns.mp hp
      obtain ⟨hsK, hqs, hrs⟩ := mem_commonColumns.mp hs'
      have hpN := mem_columnNeighbors.mpr ⟨hpK, hqp⟩
      have hsN := mem_columnNeighbors.mpr ⟨hsK, hqs⟩
      rw [columnNeighbors_eq_image hs htwo hq] at hpN hsN
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hpN
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hsN
      have hij : i ≠ j := fun h => hps (congrArg (partnerColumn K q) h)
      have hne := outside_not_same_partner hs htwo hthree hq hr hrq hi hj hij hrp hrs
      change i ∈ E at hi
      change j ∈ E at hj
      rw [← hcover] at hi hj
      rcases Finset.mem_union.mp hi with hi | hi <;> rcases Finset.mem_union.mp hj with hj | hj
      · exact (hne ((mem_sourceFiber.mp hi).2.trans (mem_sourceFiber.mp hj).2.symm)).elim
      · exact mem_nineGrid.mpr ⟨i, hUA hi, j, hVB hj, hmixed r hrq hd i j hi hj hrp hrs⟩
      · exact mem_nineGrid.mpr ⟨j, hUA hj, i, hVB hi, hmixed r hrq hd j i hj hi hrs hrp⟩
      · exact (hne ((mem_sourceFiber.mp hi).2.trans (mem_sourceFiber.mp hj).2.symm)).elim
  have hcard : (nineGrid c A B).card ≤ K.card := by
    unfold nineGrid
    calc
      _ ≤ (A ×ˢ B).card := Finset.card_image_le
      _ = K.card := by rw [Finset.card_product, hA, hB, hK]
  exact ⟨c, A, B, hA, hB, hAB, Finset.eq_of_subset_of_card_le hsub hcard⟩

/-- A direction is occupied if flipping it reaches an occupied row.
The occupied-center mask is the bitwise XOR of the column and these directions. -/
def occupiedCenter (occupied : Q 8 → Bool) (q : Q 8) : Q 8 :=
  fun i => if occupied (flip q i) = true then !q i else q i

private theorem occupied_of_row_with_three_contacts
    (htwo : TwoContactEmptyRows K occupied) {r : Q 8} {S : Finset (Fin 8)}
    (hS : S.card = 3) (hsub : S.image (flip r) ⊆ rowContacts K r) : occupied r = true := by
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (flip_injective r), hS] at hcard
  apply Bool.eq_true_of_not_eq_false
  intro he
  have hn : (rowContacts K r).Nonempty := Finset.card_pos.mp (by omega)
  have hh := htwo r he hn
  omega

/-- Each singleton row of the signed embedding has three contacts, hence is
occupied. The argument also applies after interchanging the two triples. -/
private theorem occupied_grid_singleton_left {c : Q 8} {A B : Finset (Fin 8)}
    (hK : K = nineGrid c A B) (htwo : TwoContactEmptyRows K occupied)
    (hA : A.card = 3) {b : Fin 8} (hb : b ∈ B) : occupied (flip c b) = true := by
  apply occupied_of_row_with_three_contacts htwo hA
  intro p hp
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  apply mem_rowContacts.mpr
  refine ⟨?_, (flip_adj (flip c b) a).symm⟩
  rw [hK]
  exact mem_nineGrid.mpr ⟨a, ha, b, hb, flip_comm c a b⟩

private theorem occupied_grid_singleton_right {c : Q 8} {A B : Finset (Fin 8)}
    (hK : K = nineGrid c A B) (htwo : TwoContactEmptyRows K occupied)
    (hB : B.card = 3) {a : Fin 8} (ha : a ∈ A) : occupied (flip c a) = true := by
  apply occupied_of_row_with_three_contacts htwo hB
  intro p hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
  apply mem_rowContacts.mpr
  refine ⟨?_, (flip_adj (flip c a) b).symm⟩
  rw [hK]
  exact mem_nineGrid.mpr ⟨a, ha, b, hb, rfl⟩

private theorem flip_grid_left (c : Q 8) (a b : Fin 8) :
    flip (gridVertex c a b) a = flip c b := by
  unfold gridVertex
  rw [flip_comm (flip c a) b a, BalancedCriticalSpectrum.flip_flip]

private theorem flip_grid_right (c : Q 8) (a b : Fin 8) :
    flip (gridVertex c a b) b = flip c a := flip_flip _ _

private theorem flip_grid_other_left (c : Q 8) (a b k : Fin 8) :
    flip (gridVertex c a b) k = flip (gridVertex c k b) a := by
  unfold gridVertex
  rw [flip_comm (flip c a) b k, flip_comm c a k, flip_comm (flip c k) a b]

private theorem flip_grid_other_right (c : Q 8) (a b k : Fin 8) :
    flip (gridVertex c a b) k = flip (gridVertex c a k) b := by
  unfold gridVertex
  exact flip_comm (flip c a) b k

/-- The actual empty directions are precisely the two other axes in each of
its triples. This uses the occupied/empty row sign equations of the cube. -/
theorem emptyDirections_of_nineGrid {c : Q 8} {A B : Finset (Fin 8)}
    (hK : K = nineGrid c A B) (hA : A.card = 3) (hB : B.card = 3)
    (hAB : Disjoint A B)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hfour : ∀ p ∈ K, (emptyDirections occupied p).card = 4)
    {a b : Fin 8} (ha : a ∈ A) (hb : b ∈ B) :
    emptyDirections occupied (gridVertex c a b) = A.erase a ∪ B.erase b := by
  classical
  have hmem (x y : Fin 8) (hx : x ∈ A) (hy : y ∈ B) : gridVertex c x y ∈ K := by
    rw [hK]
    exact mem_nineGrid.mpr ⟨x, hx, y, hy, rfl⟩
  have hp := hmem a b ha hb
  have hoa : occupied (flip (gridVertex c a b) a) = true := by
    rw [flip_grid_left]
    exact occupied_grid_singleton_left hK htwo hA hb
  have hob : occupied (flip (gridVertex c a b) b) = true := by
    rw [flip_grid_right]
    exact occupied_grid_singleton_right hK htwo hB ha
  have hsub : A.erase a ∪ B.erase b ⊆ emptyDirections occupied (gridVertex c a b) := by
    intro k hk
    apply mem_emptyDirections.mpr
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨hka, hkA⟩ := Finset.mem_erase.mp hk
      have hne : gridVertex c a b ≠ gridVertex c k b := by
        apply hammingDist_pos.mp
        rw [hammingDist_gridVertex hAB ha hkA hb hb]
        simp [hka.symm]
      have hn := occupied_ne_at_common_rows hs hp (hmem k b hkA hb) hne
        (flip_grid_other_left c a b k)
      exact Bool.eq_false_of_not_eq_true (fun he => hn (he.trans hoa.symm))
    · obtain ⟨hkb, hkB⟩ := Finset.mem_erase.mp hk
      have hne : gridVertex c a b ≠ gridVertex c a k := by
        apply hammingDist_pos.mp
        rw [hammingDist_gridVertex hAB ha ha hb hkB]
        simp [hkb.symm]
      have hn := occupied_ne_at_common_rows hs hp (hmem a k ha hkB) hne
        (flip_grid_other_right c a b k)
      exact Bool.eq_false_of_not_eq_true (fun he => hn (he.trans hob.symm))
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_union_of_disjoint (hAB.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)),
    Finset.card_erase_of_mem ha, Finset.card_erase_of_mem hb, hA, hB, hfour _ hp]

/-- The center mask is constant in the grid. It equals the signed translate
on the six active axes and its complement on the two unused axes. -/
theorem occupiedCenter_of_nineGrid {c : Q 8} {A B : Finset (Fin 8)}
    (hK : K = nineGrid c A B) (hA : A.card = 3) (hB : B.card = 3)
    (hAB : Disjoint A B)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hfour : ∀ p ∈ K, (emptyDirections occupied p).card = 4)
    {a b : Fin 8} (ha : a ∈ A) (hb : b ∈ B) :
    occupiedCenter occupied (gridVertex c a b) =
      fun i => if i ∈ A ∪ B then c i else !c i := by
  have he := emptyDirections_of_nineGrid hK hA hB hAB hs htwo hfour ha hb
  have hab := cross_ne hAB ha hb
  funext i
  have hocc : occupied (flip (gridVertex c a b) i) = false ↔
      (i ∈ A ∧ i ≠ a) ∨ (i ∈ B ∧ i ≠ b) := by
    rw [← mem_emptyDirections, he]
    simp only [Finset.mem_union, Finset.mem_erase, and_comm]
  have hbit : gridVertex c a b i = if i = a ∨ i = b then !c i else c i :=
    double_flip_apply c hab i
  change (if occupied (flip (gridVertex c a b) i) = true then
    !(gridVertex c a b i) else gridVertex c a b i) = _
  rw [hbit]
  by_cases hia : i = a
  · subst i
    have ho : occupied (flip (gridVertex c a b) a) = true := by
      rw [flip_grid_left]
      exact occupied_grid_singleton_left hK htwo hA hb
    simp [ho, ha]
  by_cases hib : i = b
  · subst i
    have ho : occupied (flip (gridVertex c a b) b) = true := by
      rw [flip_grid_right]
      exact occupied_grid_singleton_right hK htwo hB ha
    simp [ho, hb]
  by_cases hi : i ∈ A ∪ B
  · have ho : occupied (flip (gridVertex c a b) i) = false := by
      apply hocc.mpr
      rcases Finset.mem_union.mp hi with hiA | hiB
      · exact Or.inl ⟨hiA, hia⟩
      · exact Or.inr ⟨hiB, hib⟩
    simp [ho, hi, hia, hib]
  · have ho : occupied (flip (gridVertex c a b) i) = true := by
      apply Bool.eq_true_of_not_eq_false
      intro hf
      rcases hocc.mp hf with hh | hh
      · exact hi (Finset.mem_union.mpr (Or.inl hh.1))
      · exact hi (Finset.mem_union.mpr (Or.inr hh.1))
    simp [ho, hi, hia, hib]

/-- The nine-column equality classification, including the actual common
center and a signed Hamming embedding of K3 square K3. -/
theorem nine_column_equality (hK : K.card = 9)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ p ∈ K, (emptyDirections occupied p).card = 4) :
    ∃ c : Q 8, ∃ A B : Finset (Fin 8),
      A.card = 3 ∧ B.card = 3 ∧ Disjoint A B ∧ K = nineGrid c A B ∧
      (∀ a ∈ A, ∀ b ∈ B,
        emptyDirections occupied (gridVertex c a b) = A.erase a ∪ B.erase b) ∧
      (∀ p ∈ K, occupiedCenter occupied p = fun i => if i ∈ A ∪ B then c i else !c i) ∧
      (∀ a ∈ A, ∀ x ∈ A, ∀ b ∈ B, ∀ y ∈ B,
        hammingDist (gridVertex c a b) (gridVertex c x y) =
          (if a = x then 0 else 2) + (if b = y then 0 else 2)) := by
  obtain ⟨c, A, B, hA, hB, hAB, he⟩ := eq_nineGrid_of_twoContact hK hs htwo hthree hfour
  refine ⟨c, A, B, hA, hB, hAB, he, ?_, ?_, ?_⟩
  · intro a ha b hb
    exact emptyDirections_of_nineGrid he hA hB hAB hs htwo hfour ha hb
  · intro p hp
    rw [he] at hp
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_nineGrid.mp hp
    exact occupiedCenter_of_nineGrid he hA hB hAB hs htwo hfour ha hb
  · intro a ha x hx b hb y hy
    exact hammingDist_gridVertex hAB ha hx hb hy

/-- The occupied-center mask is independent of the column in the nine-column
equality case. -/
theorem occupiedCenter_constant_of_nine (hK : K.card = 9)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hfour : ∀ p ∈ K, (emptyDirections occupied p).card = 4) :
    ∃ z : Q 8, ∀ p ∈ K, occupiedCenter occupied p = z := by
  obtain ⟨c, A, B, _, _, _, _, _, hcenter, _⟩ := nine_column_equality hK hs htwo hthree hfour
  exact ⟨fun i => if i ∈ A ∪ B then c i else !c i, hcenter⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactNineRigidity
