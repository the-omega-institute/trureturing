/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCubeOrders
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity, mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Two-contact empty rows of the Huang cube give a weighted cover of coordinate orders. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeLift
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactOrderCoverage

/-!
# Coordinate-order coverage on the two-contact cube

Each empty direction at a column gives an exponent step toward an occupied
direction. The fibers of this map form disjoint stars with their occupied axes
as targets. A star has size three exactly when its target row has three contacts.

This is the two-contact order bound for Hong–Wu–Xia, arXiv:2610.09483v1, §7, Problem 2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeOrders

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj flip_flip)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeGirth (adjacent_exists_flip flip_comm)
open BalancedCubeComponentBoundary (flip_injective)
open PrimeContactCubeLift (RowSigns EmptyGain occupied_ne_at_common_rows)
open PrimeContactOrderCoverage (StarFamily HasExponentSteps weighted_order_coverage)
open PrimeContactTransport (Exponent axis)

/-- The selected columns adjacent to a given cube row. -/
def rowContacts (K : Finset (Q 8)) (r : Q 8) : Finset (Q 8) := by
  classical
  exact K.filter (fun p => (hypercube 8).Adj p r)

@[simp] theorem mem_rowContacts {K : Finset (Q 8)} {p r : Q 8} :
    p ∈ rowContacts K r ↔ p ∈ K ∧ (hypercube 8).Adj p r := by
  classical
  unfold rowContacts
  exact Finset.mem_filter

/-- The axes of the empty rows incident to a column. -/
def emptyDirections (occupied : Q 8 → Bool) (q : Q 8) : Finset (Fin 8) :=
  Finset.univ.filter (fun i => occupied (flip q i) = false)

@[simp] theorem mem_emptyDirections {occupied : Q 8 → Bool} {q : Q 8} {i : Fin 8} :
    i ∈ emptyDirections occupied q ↔ occupied (flip q i) = false := by
  simp only [emptyDirections, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every empty row incident to the selected columns has exactly two contacts. -/
def TwoContactEmptyRows (K : Finset (Q 8)) (occupied : Q 8 → Bool) : Prop :=
  ∀ r, occupied r = false → (rowContacts K r).Nonempty → (rowContacts K r).card = 2

/-- The occupied rows incident to a column that have exactly three contacts. -/
def threeContactRowsAt (K : Finset (Q 8)) (occupied : Q 8 → Bool) (q : Q 8) :
    Finset (Q 8) := by
  classical
  exact (Finset.univ.filter (fun j =>
    occupied (flip q j) = true ∧ (rowContacts K (flip q j)).card = 3)).image (flip q)

@[simp] theorem mem_threeContactRowsAt
    {K : Finset (Q 8)} {occupied : Q 8 → Bool} {q r : Q 8} :
    r ∈ threeContactRowsAt K occupied q ↔
      (hypercube 8).Adj q r ∧ occupied r = true ∧ (rowContacts K r).card = 3 := by
  classical
  unfold threeContactRowsAt
  constructor
  · intro hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨flip_adj q j, (Finset.mem_filter.mp hj).2⟩
  · rintro ⟨hadj, hr⟩
    obtain ⟨j, rfl⟩ := adjacent_exists_flip hadj
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hr⟩, rfl⟩

/-- The number of columns incident to exactly `t` three-contact occupied rows. -/
def columnCount (K : Finset (Q 8)) (occupied : Q 8 → Bool) (t : ℕ) : ℕ :=
  (K.filter (fun q => (threeContactRowsAt K occupied q).card = t)).card

variable {K : Finset (Q 8)} {occupied : Q 8 → Bool} {τ σ : Q 8 → ℝ}
variable {v : Q 8 → Exponent 8} {q : Q 8} {i j k : Fin 8}

private def OtherContact (K : Finset (Q 8)) (q : Q 8) (i j : Fin 8) : Prop :=
  flip (flip q i) j ∈ K ∧ flip (flip q i) j ≠ q

private theorem existsUnique_otherContact (htwo : TwoContactEmptyRows K occupied)
    (hq : q ∈ K) (hi : occupied (flip q i) = false) :
    ∃! j : Fin 8, OtherContact K q i j := by
  classical
  have hqrow : q ∈ rowContacts K (flip q i) := mem_rowContacts.mpr ⟨hq, flip_adj q i⟩
  have hcard := htwo (flip q i) hi ⟨q, hqrow⟩
  have herase : ((rowContacts K (flip q i)).erase q).card = 1 := by
    rw [Finset.card_erase_of_mem hqrow, hcard]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp herase
  have hpmem : p ∈ (rowContacts K (flip q i)).erase q :=
    hp.symm ▸ Finset.mem_singleton_self p
  obtain ⟨hpq, hprow⟩ := Finset.mem_erase.mp hpmem
  obtain ⟨hpK, hpadj⟩ := mem_rowContacts.mp hprow
  obtain ⟨j, hj⟩ := adjacent_exists_flip hpadj.symm
  refine ⟨j, ⟨hj ▸ hpK, hj ▸ hpq⟩, ?_⟩
  intro k hk
  have hkmem : flip (flip q i) k ∈ (rowContacts K (flip q i)).erase q :=
    Finset.mem_erase.mpr ⟨hk.2, mem_rowContacts.mpr ⟨hk.1, (flip_adj (flip q i) k).symm⟩⟩
  rw [hp, Finset.mem_singleton] at hkmem
  exact flip_injective (flip q i) (hkmem.trans hj)

/-- An axis to another contact at `flip q i`, with `i` as the default. -/
def partnerAxis (K : Finset (Q 8)) (q : Q 8) (i : Fin 8) : Fin 8 := by
  classical
  exact if h : ∃ j, OtherContact K q i j then Classical.choose h else i

/-- At a selected column and an empty direction, the partner axis labels the
unique other contact with the empty row. -/
theorem partnerAxis_eq_iff (htwo : TwoContactEmptyRows K occupied)
    (hq : q ∈ K) (hi : occupied (flip q i) = false) :
    partnerAxis K q i = j ↔ flip (flip q i) j ∈ K ∧ flip (flip q i) j ≠ q := by
  classical
  have h := existsUnique_otherContact htwo hq hi
  have hex : ∃ j, OtherContact K q i j := h.exists
  have hpartner : OtherContact K q i (partnerAxis K q i) := by
    unfold partnerAxis
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact ⟨fun he => he ▸ hpartner, fun hj => (h.unique hj hpartner).symm⟩

private theorem shared_row (q : Q 8) (i j : Fin 8) :
    flip q i = flip (flip (flip q i) j) j :=
  (flip_flip (flip q i) j).symm

/-- An empty direction at a selected column has an occupied partner axis. -/
theorem partnerAxis_occupied (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hi : occupied (flip q i) = false) :
    occupied (flip q (partnerAxis K q i)) = true := by
  obtain ⟨hp, hpq⟩ := (partnerAxis_eq_iff htwo hq hi).mp rfl
  have hne := occupied_ne_at_common_rows hs hq hp hpq.symm (shared_row q i (partnerAxis K q i))
  exact Bool.eq_true_of_not_eq_false (fun hj => hne (hi.trans hj.symm))

/-- The matched empty contact realizes the exponent step along its two axes. -/
theorem partnerAxis_gain (htwo : TwoContactEmptyRows K occupied)
    (hv : EmptyGain (K : Set (Q 8)) occupied v) (hq : q ∈ K)
    (hi : occupied (flip q i) = false) (hf : partnerAxis K q i = j) :
    v (flip (flip q i) j) = v q + axis i - axis j := by
  obtain ⟨hp, hpq⟩ := (partnerAxis_eq_iff htwo hq hi).mp hf
  exact eq_sub_of_add_eq (hv hq hp hpq.symm (shared_row q i j) hi).symm

private def sources (K : Finset (Q 8)) (occupied : Q 8 → Bool) (q : Q 8) (j : Fin 8) :
    Finset (Fin 8) :=
  (emptyDirections occupied q).filter (fun i => partnerAxis K q i = j)

private theorem mem_sources : i ∈ sources K occupied q j ↔
    occupied (flip q i) = false ∧ partnerAxis K q i = j := by
  simp only [sources, Finset.mem_filter, mem_emptyDirections]

private def targets (K : Finset (Q 8)) (occupied : Q 8 → Bool) (q : Q 8) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => occupied (flip q j) = true ∧ (sources K occupied q j).Nonempty)

private theorem mem_targets : j ∈ targets K occupied q ↔
    occupied (flip q j) = true ∧ (sources K occupied q j).Nonempty := by
  simp only [targets, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem contacts_eq_insert_image (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hj : occupied (flip q j) = true) :
    rowContacts K (flip q j) = insert q ((sources K occupied q j).image (flip (flip q j))) := by
  classical
  ext p
  constructor
  · intro hp
    by_cases hpq : p = q
    · exact Finset.mem_insert.mpr (Or.inl hpq)
    · obtain ⟨hpK, hpadj⟩ := mem_rowContacts.mp hp
      obtain ⟨i, hi⟩ := adjacent_exists_flip hpadj.symm
      have hpi : flip (flip q i) j = p := (flip_comm q i j).trans hi.symm
      have hr : flip q i = flip p j := (shared_row q i j).trans (congrArg (fun x => flip x j) hpi)
      have hne := occupied_ne_at_common_rows hs hq hpK (Ne.symm hpq) hr
      have he : occupied (flip q i) = false :=
        Bool.eq_false_of_not_eq_true (fun he => hne (he.trans hj.symm))
      have hf : partnerAxis K q i = j :=
        (partnerAxis_eq_iff htwo hq he).mpr ⟨hpi.symm ▸ hpK, hpi.symm ▸ hpq⟩
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
        ⟨i, mem_sources.mpr ⟨he, hf⟩, hi.symm⟩))
  · intro hp
    rcases Finset.mem_insert.mp hp with hpq | hp
    · subst p
      exact mem_rowContacts.mpr ⟨hq, flip_adj q j⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨he, hf⟩ := mem_sources.mp hi
      have hpK := ((partnerAxis_eq_iff htwo hq he).mp hf).1
      rw [flip_comm q i j] at hpK
      exact mem_rowContacts.mpr ⟨hpK, (flip_adj (flip q j) i).symm⟩

/-- At an occupied direction, the other contacts are indexed bijectively by the
empty directions whose partner is that occupied axis. -/
theorem card_rowContacts_of_occupied (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K)
    (hj : occupied (flip q j) = true) :
    (rowContacts K (flip q j)).card =
      ((emptyDirections occupied q).filter (fun i => partnerAxis K q i = j)).card + 1 := by
  classical
  have hnot : q ∉ (sources K occupied q j).image (flip (flip q j)) := by
    intro h
    obtain ⟨i, hi, hflip⟩ := Finset.mem_image.mp h
    obtain ⟨he, hf⟩ := mem_sources.mp hi
    exact ((partnerAxis_eq_iff htwo hq he).mp hf).2 ((flip_comm q i j).trans hflip)
  change (rowContacts K (flip q j)).card = (sources K occupied q j).card + 1
  rw [contacts_eq_insert_image hs htwo hq hj, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ (flip_injective (flip q j))]

private def starBlock (K : Finset (Q 8)) (occupied : Q 8 → Bool) (q : Q 8) (j : Fin 8) :
    Finset (Fin 8) :=
  insert j (sources K occupied q j)

private theorem occupied_not_mem_sources (hi : occupied (flip q i) = true) :
    i ∉ sources K occupied q j :=
  fun hm => Bool.false_ne_true ((mem_sources.mp hm).1.symm.trans hi)

private theorem starBlock_disjoint (hj : occupied (flip q j) = true)
    (hk : occupied (flip q k) = true) (hjk : j ≠ k) :
    Disjoint (starBlock K occupied q j) (starBlock K occupied q k) := by
  rw [Finset.disjoint_left]
  intro i hij hik
  rcases Finset.mem_insert.mp hij with rfl | hs
  · exact (Finset.mem_insert.mp hik).elim hjk (occupied_not_mem_sources hj)
  · rcases Finset.mem_insert.mp hik with rfl | ht
    · exact occupied_not_mem_sources hk hs
    · exact hjk ((mem_sources.mp hs).2.symm.trans (mem_sources.mp ht).2)

private theorem starBlock_injOn :
    Set.InjOn (starBlock K occupied q) (targets K occupied q : Set (Fin 8)) := by
  intro j hj k _ he
  have hmem : j ∈ starBlock K occupied q k :=
    he ▸ (Finset.mem_insert_self j (sources K occupied q j))
  exact (Finset.mem_insert.mp hmem).resolve_right
    (occupied_not_mem_sources (mem_targets.mp (Finset.mem_coe.mp hj)).1)

private def starBlocks (K : Finset (Q 8)) (occupied : Q 8 → Bool) (q : Q 8) :
    Finset (Finset (Fin 8)) :=
  (targets K occupied q).image (starBlock K occupied q)

private theorem exists_blockTarget (b : ↥(starBlocks K occupied q)) :
    ∃ j ∈ targets K occupied q, starBlock K occupied q j = b.val :=
  Finset.mem_image.mp b.property

/-- The disjoint blocks of empty directions with the same occupied partner,
with the occupied partner included as each block's target. -/
def cubeStarFamily (K : Finset (Q 8)) (occupied : Q 8 → Bool) (q : Q 8) : StarFamily 8 where
  blocks := starBlocks K occupied q
  target b := by
    let j := Classical.choose (exists_blockTarget b)
    have he : starBlock K occupied q j = b.val := (Classical.choose_spec (exists_blockTarget b)).2
    exact ⟨j, he ▸ Finset.mem_insert_self j (sources K occupied q j)⟩
  disjoint := by
    intro b d hne
    obtain ⟨j, hj, hb⟩ := exists_blockTarget b
    obtain ⟨k, hk, hd⟩ := exists_blockTarget d
    have hjk : j ≠ k := by
      intro he
      subst k
      exact hne (Subtype.ext (hb.symm.trans hd))
    rw [← hb, ← hd]
    exact starBlock_disjoint (mem_targets.mp hj).1 (mem_targets.mp hk).1 hjk

/-- Each block consists of its occupied target and exactly the empty directions
whose partner is that target. -/
theorem cubeStarFamily_block_eq (b : ↥(cubeStarFamily K occupied q).blocks) :
    let j := ((cubeStarFamily K occupied q).target b).val
    occupied (flip q j) = true ∧
      b.val = insert j ((emptyDirections occupied q).filter (fun i => partnerAxis K q i = j)) := by
  have h := Classical.choose_spec (exists_blockTarget b)
  exact ⟨(mem_targets.mp h.1).1, h.2.symm⟩

private theorem card_starBlock (hj : occupied (flip q j) = true) :
    (starBlock K occupied q j).card = (sources K occupied q j).card + 1 :=
  Finset.card_insert_of_notMem (occupied_not_mem_sources hj)

private theorem cubeStarFamily_block_size (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    (hq : q ∈ K) (b : ↥(cubeStarFamily K occupied q).blocks) :
    b.val.card = 2 ∨ b.val.card = 3 := by
  obtain ⟨j, hj, hb⟩ := exists_blockTarget b
  obtain ⟨ho, hnonempty⟩ := mem_targets.mp hj
  have hpos : 0 < (sources K occupied q j).card := Finset.card_pos.mpr hnonempty
  have hle := hthree (flip q j) ho
  rw [card_rowContacts_of_occupied hs htwo hq ho] at hle
  change (sources K occupied q j).card + 1 ≤ 3 at hle
  rw [← hb, card_starBlock ho]
  omega

private theorem cubeStarFamily_source_count (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K) :
    (∑ b : ↥(cubeStarFamily K occupied q).blocks, (b.val.card - 1)) =
      (emptyDirections occupied q).card := by
  have hmaps : Set.MapsTo (partnerAxis K q) (emptyDirections occupied q : Set (Fin 8))
      (targets K occupied q : Set (Fin 8)) := by
    intro i hi
    have he := mem_emptyDirections.mp (Finset.mem_coe.mp hi)
    exact Finset.mem_coe.mpr (mem_targets.mpr ⟨partnerAxis_occupied hs htwo hq he,
      ⟨i, mem_sources.mpr ⟨he, rfl⟩⟩⟩)
  change (∑ b : ↥(starBlocks K occupied q), (b.val.card - 1)) = _
  calc
    _ = ∑ b ∈ starBlocks K occupied q, (b.card - 1) := Finset.sum_attach _ _
    _ = ∑ j ∈ targets K occupied q, ((starBlock K occupied q j).card - 1) :=
      Finset.sum_image (f := fun b : Finset (Fin 8) => b.card - 1) starBlock_injOn
    _ = ∑ j ∈ targets K occupied q, (sources K occupied q j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [card_starBlock (mem_targets.mp hj).1, Nat.add_sub_cancel]
    _ = _ := (Finset.card_eq_sum_card_fiberwise hmaps).symm

private theorem cubeStarFamily_steps (htwo : TwoContactEmptyRows K occupied)
    (hv : EmptyGain (K : Set (Q 8)) occupied v) :
    HasExponentSteps K (cubeStarFamily K occupied) v := by
  intro q hq b i hi
  have hb := (cubeStarFamily_block_eq b).2
  have hmem : i.val ∈ starBlock K occupied q ((cubeStarFamily K occupied q).target b).val :=
    by
      have hb' : b.val = starBlock K occupied q ((cubeStarFamily K occupied q).target b).val := hb
      rw [← hb']
      exact i.property
  have hne : i.val ≠ ((cubeStarFamily K occupied q).target b).val := fun h => hi (Subtype.ext h)
  obtain ⟨he, hf⟩ := mem_sources.mp ((Finset.mem_insert.mp hmem).resolve_left hne)
  exact ⟨_, ((partnerAxis_eq_iff htwo hq he).mp hf).1, partnerAxis_gain htwo hv hq he hf⟩

/-- A three-axis block is equivalent to a three-contact occupied row at the column. -/
theorem tripleCount_eq_card_threeContactRowsAt (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (htwo : TwoContactEmptyRows K occupied) (hq : q ∈ K) :
    (cubeStarFamily K occupied q).tripleCount = (threeContactRowsAt K occupied q).card := by
  classical
  have hfilter :
      (targets K occupied q).filter (fun j => (starBlock K occupied q j).card = 3) =
        Finset.univ.filter (fun j => occupied (flip q j) = true ∧
          (rowContacts K (flip q j)).card = 3) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_targets]
    constructor
    · rintro ⟨⟨ho, _⟩, hb⟩
      exact ⟨ho, (card_rowContacts_of_occupied hs htwo hq ho).trans ((card_starBlock ho).symm.trans hb)⟩
    · rintro ⟨ho, hc⟩
      have hsources : (sources K occupied q j).card + 1 = 3 :=
        (card_rowContacts_of_occupied hs htwo hq ho).symm.trans hc
      have hpos : 0 < (sources K occupied q j).card := by omega
      exact ⟨⟨ho, Finset.card_pos.mp hpos⟩, (card_starBlock ho).trans hsources⟩
  have hinj : Set.InjOn (starBlock K occupied q)
      (↑((targets K occupied q).filter (fun j => (starBlock K occupied q j).card = 3)) :
        Set (Fin 8)) := by
    intro j hj k hk h
    exact starBlock_injOn
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).1) h
  unfold StarFamily.tripleCount
  rw [Finset.univ_eq_attach, Finset.filter_attach (fun b : Finset (Fin 8) => b.card = 3),
    Finset.card_map, Finset.card_attach]
  change (((targets K occupied q).image (starBlock K occupied q)).filter
    (fun b => b.card = 3)).card = _
  rw [Finset.filter_image, Finset.card_image_of_injOn hinj, hfilter, threeContactRowsAt,
    Finset.card_image_of_injective _ (flip_injective q)]

/-- The actual cube stars supply the exponent steps, block sizes and source
count used by the order cover. -/
theorem cubeStarFamily_spec (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (hv : EmptyGain (K : Set (Q 8)) occupied v)
    (hfour : ∀ q ∈ K, (emptyDirections occupied q).card = 4)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3) :
    HasExponentSteps K (cubeStarFamily K occupied) v ∧
      (∀ q ∈ K, ∀ b : ↥(cubeStarFamily K occupied q).blocks, b.val.card = 2 ∨ b.val.card = 3) ∧
      (∀ q ∈ K, (∑ b : ↥(cubeStarFamily K occupied q).blocks, (b.val.card - 1)) = 4) :=
  ⟨cubeStarFamily_steps htwo hv, fun _ hq b => cubeStarFamily_block_size hs htwo hthree hq b,
    fun q hq => (cubeStarFamily_source_count hs htwo hq).trans (hfour q hq)⟩

/-- Weighted coordinate-order coverage for an actual nonempty subset of the
Huang eight-cube in the two-contact empty-row case. -/
theorem weighted_order_coverage_of_cube (K : Finset (Q 8)) (hK : K.Nonempty)
    (occupied : Q 8 → Bool) (τ σ : Q 8 → ℝ) (v : Q 8 → Exponent 8)
    (hs : RowSigns (K : Set (Q 8)) occupied τ σ)
    (hv : EmptyGain (K : Set (Q 8)) occupied v)
    (hfour : ∀ q ∈ K, (emptyDirections occupied q).card = 4)
    (htwo : TwoContactEmptyRows K occupied)
    (hthree : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3) :
    144 ≤ 9 * columnCount K occupied 0
      + 12 * columnCount K occupied 1
      + 16 * columnCount K occupied 2 := by
  obtain ⟨hstep, hsize, hsource⟩ := cubeStarFamily_spec hs hv hfour htwo hthree
  have hcover := weighted_order_coverage K hK (cubeStarFamily K occupied) v hstep hsize hsource
  have hcount (t : ℕ) :
      (K.filter (fun q => (cubeStarFamily K occupied q).tripleCount = t)).card =
        columnCount K occupied t := by
    unfold columnCount
    apply congrArg Finset.card
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hq, ht⟩
      exact ⟨hq, (tripleCount_eq_card_threeContactRowsAt hs htwo hq).symm.trans ht⟩
    · rintro ⟨hq, ht⟩
      exact ⟨hq, (tripleCount_eq_card_threeContactRowsAt hs htwo hq).trans ht⟩
  simpa only [hcount] using hcover

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeOrders
