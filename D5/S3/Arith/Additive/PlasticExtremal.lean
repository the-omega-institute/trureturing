/- GID: D5/S3/Arith/Additive/PlasticExtremal
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticExtremal
   mirror-E: none(waiver:finite-memory-extremal-count)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Additive/PlasticExtremal.whole_theorem_three_one; premises=D5/S3/Arith/Additive/PlasticExtremal.table_step
   digest: Lossless finite-memory counting for arbitrary integer plastic-power exponent sets. -/

import D5.S3.Arith.Additive.PlasticPowerCollisions
import Mathlib.Data.Finset.Preimage

/-! Theorem 3.1 of SUM_PRODUCT_PLASTIC_POWER_FAMILIES: the actual four
translation counts, arbitrary signed exponents and unbounded gaps. The state
retains distances 0 through 8; weights are evaluated BEFORE truncating the
shifted state, so distance 9 is retained in the weight calculation. -/


/-
Statement echo: source SUM_PRODUCT_PLASTIC_POWER_FAMILIES Theorem 3.1,
atom 68e2f9eaaaec6d3f1f34ba86083794e6afc44216357f0fde5e5b0a433a6dc403.
For every real r > 1 with r^3 = r+1 and every natural n >= 10, the
four source template counts on every n-point integer set are <= 4*n-26;
all translated n-point intervals attain equality; the actual real sumset
minimum over every n-element subset of the full power group is
n*(n+1)/2-4*n+26; ten is the least INTEGER uniform threshold.
No diameter, nonnegative-exponent, product-set or precomputed-count premise.
Theorem 3.2 (all equality cases) and Theorem 3.3 (stability) remain open.

Admission basis: escape-witness. The live content is the actual-prefix
finite-memory counting invariant prefix_certificate and its arbitrary-size
extension count_bound. The original endpoint sets, not an assumed recurrence,
supply count_insert; source translation is checked by endpoints_translate.
All allowed one-step inequalities between finite table entries are kernel checked,
but they alone do not establish
any statement about arbitrary integer sets. Unreachable is encoded by 15,
and the actual prefix invariant retains potential < 15 at every step.
No exact-maximality or predecessor-attainability claim is made for the table.

Computational content: numeric-reduction. The fulfilled premises table_step_0
through table_step_8 are consumed by table_step, then prefix_certificate,
count_bound and whole_theorem_three_one. The finite nine-point computation
is consumed by the actual least-threshold assertion, not retained as a
standalone certified instance. The unbounded consumer is in the same module.
Helpers are internal and actually consumed; their bind-only translations,
arithmetic, projections and normalizations are not claimed as new content.

Direct frozen dependency:
D5/S3/Arith/Additive/PlasticPowerCollisions.sumset_card_add_template_counts
module statement_id: sha256:7a545e972683020381a90bb8b691757202ea828bd62b04904604c6d812c348ce
Search: repository additive/combinatorics and pinned Mathlib additive and
computability modules did not supply this finite-memory extremal theorem.
The frozen collision classification is reused, not reproved.
-/

set_option autoImplicit false

namespace D5.S3.Arith.Additive.PlasticExtremal

/-- The literal distance window of an actual integer prefix. -/
def memory (E : Finset ℤ) (x : ℤ) : Finset ℤ :=
  (Finset.Icc 0 8).filter fun a => x - a ∈ E

/-- Full shift: no truncation before counting completed templates. -/
def shifted (S : Finset ℤ) (g : ℤ) : Finset ℤ := S.image (fun a => a + g)

/-- The next finite state. -/
def advance (S : Finset ℤ) (g : ℤ) : Finset ℤ :=
  insert 0 ((shifted S g).filter fun a => a ≤ 8)

/-- Literal right-endpoint incidence for the four source templates. -/
def weight (D : Finset ℤ) : ℕ :=
  (if 1 ∈ D ∧ 2 ∈ D ∧ 4 ∈ D then 1 else 0) +
  (if 1 ∈ D ∧ 3 ∈ D ∧ 6 ∈ D then 1 else 0) +
  (if 2 ∈ D ∧ 7 ∈ D then 1 else 0) +
  (if 1 ∈ D ∧ 4 ∈ D ∧ 9 ∈ D then 1 else 0)

/-- Every needed distance sees exactly the actual previous prefix. -/
private theorem shifted_memory_iff (E : Finset ℤ) (x y a : ℤ)
    (hmax : ∀ z ∈ E, z ≤ x) (hxy : x < y) (ha : 1 ≤ a) (ha9 : a ≤ 9) :
    a ∈ shifted (memory E x) (y - x) ↔ y - a ∈ E := by
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h
    have hbE := (Finset.mem_filter.mp hb).2
    have : x - b = y - a := by omega
    simpa [this] using hbE
  · intro h
    have hh := hmax (y - a) h
    apply Finset.mem_image.mpr
    refine ⟨a - (y - x), ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    have he : x - (a - (y - x)) = y - a := by omega
    simpa only [he] using h

/-- Inserting the next actual maximum implements the finite-state transition. -/
theorem memory_insert (E : Finset ℤ) (x y : ℤ)
    (hmax : ∀ z ∈ E, z ≤ x) (hxy : x < y) :
    memory (insert y E) y = advance (memory E x) (y - x) := by
  ext a
  simp only [memory, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, advance]
  constructor
  · rintro ⟨⟨ha, ha8⟩, h⟩
    rcases h with h | h
    · left; omega
    · right
      exact ⟨(shifted_memory_iff E x y a hmax hxy (by
        have := hmax (y-a) h; omega) (by omega)).mpr h, ha8⟩
  · intro h
    rcases h with h | ⟨h, ha8⟩
    · subst a; simp
    · obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h
      obtain ⟨hb, hbE⟩ := Finset.mem_filter.mp hb
      obtain ⟨hb0, hb8⟩ := Finset.mem_Icc.mp hb
      refine ⟨⟨by omega, ha8⟩, Or.inr ?_⟩
      have : y - a = x - b := by omega
      simpa [this] using hbE

/-- A large positive gap resets the state and cannot complete any template. -/
private theorem large_gap (S : Finset ℤ) (hS : ∀ a ∈ S, 0 ≤ a) (g : ℤ) (hg : 9 ≤ g) :
    advance S g = {0} ∧ weight (shifted S g) = 0 := by
  have hlo : ∀ a ∈ shifted S g, 9 ≤ a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have := hS b hb
    omega
  have hf : (shifted S g).filter (fun a => a ≤ 8) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha, hh⟩ := Finset.mem_filter.mp ha
    have := hlo a ha
    omega
  have h1 : (1 : ℤ) ∉ shifted S g := by intro h; have := hlo 1 h; omega
  have h2 : (2 : ℤ) ∉ shifted S g := by intro h; have := hlo 2 h; omega
  simp [advance, hf, weight, h1, h2]

/-- Capping a gap at nine preserves both the next state and its reward. -/
theorem cap_gap (S : Finset ℤ) (hS : ∀ a ∈ S, 0 ≤ a) (g : ℤ) :
    advance S (min g 9) = advance S g ∧
      weight (shifted S (min g 9)) = weight (shifted S g) := by
  by_cases hg : g ≤ 9
  · simp [min_eq_left hg]
  · have hg9 : 9 ≤ g := by omega
    obtain ⟨ha, hw⟩ := large_gap S hS g hg9
    obtain ⟨ha9, hw9⟩ := large_gap S hS 9 (by omega)
    simp [min_eq_right hg9, ha, hw, ha9, hw9]

/-- Right endpoints of a translated finite offset pattern. -/
private def endpoints (E L : Finset ℤ) : Finset ℤ :=
  E.filter fun t => ∀ a ∈ L, t - a ∈ E

/-- Insertion creates exactly the patterns with the new, unique largest point.
This is an equality of actual endpoint sets, not a supplied recurrence. -/
private theorem endpoints_insert (E L : Finset ℤ) (y : ℤ)
    (hmax : ∀ z ∈ E, z < y) (hpos : ∀ a ∈ L, 0 < a) :
    endpoints (insert y E) L =
      if (∀ a ∈ L, y - a ∈ E) then insert y (endpoints E L) else endpoints E L := by
  have hold : ∀ t ∈ E, ∀ a ∈ L, (t - a ∈ insert y E ↔ t - a ∈ E) := by
    intro t ht a ha
    have := hmax t ht
    have := hpos a ha
    simp only [Finset.mem_insert]
    constructor
    · rintro (h | h)
      · omega
      · exact h
    · exact Or.inr
  have hnew : (∀ a ∈ L, y - a ∈ insert y E) ↔ ∀ a ∈ L, y - a ∈ E := by
    constructor
    · intro h a ha
      have := hpos a ha
      rcases Finset.mem_insert.mp (h a ha) with h | h
      · omega
      · exact h
    · intro h a ha
      exact Finset.mem_insert_of_mem (h a ha)
  ext t
  by_cases ht : t = y
  · subst t
    simp only [endpoints, Finset.mem_filter, Finset.mem_insert, true_or, true_and]
    simp only [Finset.mem_insert] at hnew
    rw [hnew]
    split_ifs with h
    · simp only [Finset.mem_insert, true_or, iff_true]; exact h
    · simp [show y ∉ E from fun hy => lt_irrefl y (hmax y hy), h]
  · have hte : (t ∈ insert y E) ↔ t ∈ E := by simp [ht]
    simp only [endpoints, Finset.mem_filter, hte]
    by_cases he : t ∈ E
    · simp only [he, true_and]
      have hp : (∀ a ∈ L, t - a ∈ insert y E) ↔ ∀ a ∈ L, t - a ∈ E := by
        exact forall_congr' fun a => forall_congr' fun ha => hold t he a ha
      rw [hp]
      split_ifs <;> simp [Finset.mem_insert, ht, he]
    · simp only [he, false_and]
      split_ifs <;> simp [Finset.mem_insert, ht, he]

/-- The four original patterns represented by their unique right endpoints. -/
def count (E : Finset ℤ) : ℕ :=
  (endpoints E {1,2,4}).card + (endpoints E {1,3,6}).card +
  (endpoints E {2,7}).card + (endpoints E {1,4,9}).card

private theorem endpoints_card_insert (E L : Finset ℤ) (y : ℤ)
    (hmax : ∀ z ∈ E, z < y) (hpos : ∀ a ∈ L, 0 < a) :
    (endpoints (insert y E) L).card = (endpoints E L).card +
      if (∀ a ∈ L, y-a ∈ E) then 1 else 0 := by
  rw [endpoints_insert E L y hmax hpos]
  have hy : y ∉ endpoints E L := by
    intro h
    exact lt_irrefl y (hmax y (Finset.mem_filter.mp h).1)
  split_ifs <;> simp [hy]

/-- The full untruncated shifted window gives the actual increment. -/
theorem count_insert (E : Finset ℤ) (x y : ℤ)
    (hmax : ∀ z ∈ E, z ≤ x) (hxy : x < y) :
    count (insert y E) = count E + weight (shifted (memory E x) (y-x)) := by
  have hm : ∀ z ∈ E, z < y := fun z hz => lt_of_le_of_lt (hmax z hz) hxy
  have hc := endpoints_card_insert E
  rw [count, hc {1,2,4} y hm (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega),
    hc {1,3,6} y hm (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega),
    hc {2,7} y hm (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> omega),
    hc {1,4,9} y hm (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> omega)]
  have h1 := shifted_memory_iff E x y 1 hmax hxy (by omega) (by omega)
  have h2 := shifted_memory_iff E x y 2 hmax hxy (by omega) (by omega)
  have h3 := shifted_memory_iff E x y 3 hmax hxy (by omega) (by omega)
  have h4 := shifted_memory_iff E x y 4 hmax hxy (by omega) (by omega)
  have h6 := shifted_memory_iff E x y 6 hmax hxy (by omega) (by omega)
  have h7 := shifted_memory_iff E x y 7 hmax hxy (by omega) (by omega)
  have h9 := shifted_memory_iff E x y 9 hmax hxy (by omega) (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    weight, h1, h2, h3, h4, h6, h7, h9]
  dsimp [count]
  omega

/-- Translation of each literal start to its unique right endpoint. -/
private theorem endpoints_translate (E T : Finset ℤ) (d : ℤ) (h0 : 0 ∈ T) (hd : d ∈ T) :
    endpoints E (T.image fun a => d-a) =
      (E.filter fun t => ∀ a ∈ T, t+a ∈ E).image (fun t => t+d) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hy, hall⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_image.mpr ⟨y-d, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    constructor
    · have hh := hall d (Finset.mem_image.mpr ⟨0, h0, by omega⟩)
      exact hh
    · intro a ha
      have hh := hall (d-a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      have he : y - (d-a) = y-d+a := by omega
      simpa only [he] using hh
  · intro hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨ht, hall⟩ := Finset.mem_filter.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨hall d hd, ?_⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have he : t+d-(d-b) = t+b := by omega
    simpa only [he] using hall b hb

/-- Exact equality with the four filters in the frozen collision theorem. -/
private theorem count_eq_source (E : Finset ℤ) :
    count E =
      (E.filter fun t => t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E).card +
      (E.filter fun t => t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E).card +
      (E.filter fun t => t+5 ∈ E ∧ t+7 ∈ E).card +
      (E.filter fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E).card := by
  have hc (T : Finset ℤ) (d : ℤ) (h0 : 0 ∈ T) (hd : d ∈ T) :
      (endpoints E (T.image fun a => d-a)).card =
        (E.filter fun t => ∀ a ∈ T, t+a ∈ E).card := by
    rw [endpoints_translate E T d h0 hd, Finset.card_image_of_injective]
    exact add_left_injective d
  have h4 := hc {0,2,3,4} 4 (by simp) (by simp)
  have h6 := hc {0,3,5,6} 6 (by simp) (by simp)
  have h7 := hc {0,5,7} 7 (by simp) (by simp)
  have h9 := hc {0,5,8,9} 9 (by simp) (by simp)
  have h4' : (endpoints E {1,2,4}).card =
      (E.filter fun t => t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E).card := by
    convert h4 using 2 <;> ext t <;>
      norm_num [endpoints, and_assoc, and_comm, and_left_comm]
  have h6' : (endpoints E {1,3,6}).card =
      (E.filter fun t => t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E).card := by
    convert h6 using 2 <;> ext t <;>
      norm_num [endpoints, and_assoc, and_comm, and_left_comm]
  have h7' : (endpoints E {2,7}).card =
      (E.filter fun t => t+5 ∈ E ∧ t+7 ∈ E).card := by
    convert h7 using 2 <;> ext t <;>
      norm_num [endpoints, and_assoc, and_comm, and_left_comm]
  have h9' : (endpoints E {1,4,9}).card =
      (E.filter fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E).card := by
    convert h9 using 2 <;> ext t <;>
      norm_num [endpoints, and_assoc, and_comm, and_left_comm]
  unfold count
  rw [h4', h6', h7', h9']

/-- The source's ten columns, transposed to layer-major order. Fifteen means
unreachable, not zero. Values 0 through 14 are actual finite upper bounds. -/
private def table : Array (Array ℕ) := #[
  #[
    0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],
  #[
    0,0,0,15,0,15,15,15,0,15,15,15,15,15,15,15,0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],
  #[
    0,0,0,0,0,0,0,15,0,0,0,15,0,15,15,15,0,0,0,15,0,15,15,15,0,15,15,15,15,15,15,15,
    0,0,0,15,0,15,15,15,0,15,15,15,15,15,15,15,0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,0,1,15,0,15,15,15,0,15,15,15,15,15,15,15,0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,0,0,15,0,15,15,15,0,15,15,15,15,15,15,15,0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],
  #[
    1,0,0,0,0,0,0,0,0,1,1,1,0,0,0,15,0,0,0,0,1,0,0,15,0,0,0,15,0,15,15,15,
    0,0,0,0,0,1,0,15,1,0,0,15,0,15,15,15,0,0,0,15,0,15,15,15,0,15,15,15,15,15,15,15,
    1,0,1,1,0,0,1,15,0,0,1,15,0,15,15,15,1,0,1,15,0,15,15,15,0,15,15,15,15,15,15,15,
    0,0,1,15,0,15,15,15,0,15,15,15,15,15,15,15,0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    1,0,0,0,0,1,0,15,0,0,0,15,0,15,15,15,0,0,0,15,0,15,15,15,0,15,15,15,15,15,15,15,
    1,0,0,15,0,15,15,15,0,15,15,15,15,15,15,15,0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,0,1,15,0,15,15,15,0,15,15,15,15,15,15,15,0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,
    0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],
  #[
    1,1,1,0,1,0,0,0,1,1,1,3,0,1,1,1,1,0,0,1,1,1,1,1,0,1,1,1,1,0,0,15,
    1,0,0,0,0,1,1,1,1,1,1,1,1,1,1,15,1,0,0,0,1,1,0,15,1,0,0,15,0,15,15,15,
    1,1,2,1,1,0,1,1,1,1,2,3,1,0,1,15,1,1,2,1,1,0,1,15,1,0,1,15,1,15,15,15,
    1,0,1,1,0,1,1,15,1,0,1,15,0,15,15,15,1,0,1,15,0,15,15,15,0,15,15,15,15,15,15,15,
    1,1,1,0,1,1,0,1,1,1,1,1,0,1,0,15,1,0,0,0,1,1,1,15,1,0,0,15,0,15,15,15,
    1,1,1,0,1,2,0,15,1,0,0,15,0,15,15,15,1,0,0,15,0,15,15,15,1,15,15,15,15,15,15,15,
    1,0,1,1,0,1,1,15,0,0,1,15,0,15,15,15,1,0,1,15,0,15,15,15,0,15,15,15,15,15,15,15,
    1,0,1,15,0,15,15,15,0,15,15,15,15,15,15,15,0,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],
  #[
    3,1,1,1,1,1,1,0,1,2,2,3,1,1,1,3,1,1,1,1,2,1,1,3,1,1,1,3,1,1,1,2,
    1,1,1,0,1,1,1,2,2,2,2,3,2,3,3,3,1,1,1,1,1,2,1,2,1,1,1,1,1,1,1,15,
    2,1,2,2,1,1,2,1,1,2,3,5,1,1,2,3,2,1,2,2,2,1,2,2,2,1,2,3,3,1,2,15,
    2,1,2,1,1,1,2,2,1,1,2,3,1,1,2,15,3,1,2,1,1,1,1,15,1,0,1,15,1,15,15,15,
    3,1,1,1,1,2,1,1,1,1,1,3,1,2,1,2,1,1,1,1,2,2,2,3,1,1,1,1,1,1,1,15,
    2,1,1,1,1,3,1,2,2,1,1,1,1,2,1,15,2,1,1,0,1,2,1,15,3,1,1,15,1,15,15,15,
    3,1,2,1,1,1,1,2,1,1,2,3,1,1,1,15,1,1,2,1,1,1,2,15,1,0,1,15,1,15,15,15,
    3,1,2,1,1,2,1,15,1,0,1,15,0,15,15,15,1,0,1,15,0,15,15,15,1,15,15,15,15,15,15,15],
  #[
    5,3,3,1,3,1,1,1,3,2,2,4,1,2,2,3,3,1,1,2,2,2,2,3,1,2,2,4,2,2,2,4,
    3,1,1,1,1,2,2,2,2,3,3,4,3,4,5,6,2,1,1,1,2,2,2,4,2,2,2,3,2,3,3,4,
    3,2,3,2,2,1,2,2,2,2,3,6,2,2,3,5,3,2,3,3,3,2,3,4,3,2,3,5,5,3,4,5,
    3,2,3,2,2,2,2,3,2,2,3,5,3,3,4,5,5,3,4,2,3,2,2,3,3,2,3,3,3,2,3,15,
    5,3,3,1,3,2,1,2,3,2,2,3,1,2,1,4,3,1,1,2,2,3,3,5,2,2,2,3,2,2,2,4,
    3,2,2,1,2,3,2,3,3,2,2,3,2,4,3,4,3,2,2,1,2,3,3,4,5,3,3,2,3,3,3,15,
    5,3,4,2,3,2,2,2,3,2,3,5,1,2,2,4,3,1,2,2,2,2,3,4,3,1,2,3,3,2,3,15,
    5,3,4,2,3,3,2,3,3,1,2,3,1,2,2,15,3,1,2,1,2,2,2,15,3,1,2,15,2,15,15,15],
  #[
    6,5,5,3,5,3,3,1,5,4,4,4,3,2,2,4,5,3,3,2,4,2,2,4,3,2,2,4,2,2,2,6,
    5,3,3,1,3,2,2,3,4,3,3,5,3,5,6,8,3,2,2,2,2,3,2,5,3,3,3,4,3,4,5,7,
    5,3,4,3,3,2,3,2,3,3,4,6,3,3,4,6,4,3,4,4,3,3,4,5,3,3,4,7,6,5,6,8,
    4,3,4,3,3,3,3,3,3,3,4,6,4,5,6,8,6,5,6,4,5,4,4,5,5,4,5,6,6,5,6,7,
    6,5,5,3,5,4,3,2,5,4,4,4,3,3,2,4,5,3,3,2,4,3,3,6,3,2,2,4,3,3,3,6,
    5,3,3,2,3,4,3,4,3,3,3,4,3,5,5,7,4,3,3,2,3,4,4,6,6,5,5,4,5,5,6,7,
    6,5,6,4,5,4,4,3,5,4,5,6,3,3,3,6,5,3,4,3,3,3,4,6,4,3,4,5,5,4,5,7,
    6,5,6,4,5,5,4,4,5,3,4,5,3,4,4,6,6,3,4,3,4,4,4,5,6,3,4,4,5,4,5,15],
  #[
    8,6,6,5,6,5,5,3,6,6,6,6,5,4,4,4,6,5,5,4,6,4,4,4,5,4,4,5,4,3,3,6,
    6,5,5,3,5,4,4,3,6,5,5,5,5,5,6,9,5,3,3,2,4,3,3,5,4,4,4,5,4,5,6,9,
    6,5,6,4,5,3,4,3,5,4,5,7,4,4,5,7,6,4,5,4,5,3,4,6,5,4,5,8,6,6,7,10,
    5,4,5,4,4,4,4,4,4,4,5,7,5,6,8,10,7,6,7,6,6,6,6,6,6,6,7,8,8,8,9,11,
    8,6,6,5,6,6,5,4,6,6,6,6,5,5,4,5,6,5,5,4,6,5,5,6,5,4,4,5,4,4,4,8,
    6,5,5,3,5,5,3,5,5,4,4,5,4,6,6,9,5,4,4,3,4,5,5,8,7,6,6,6,6,7,8,10,
    8,6,7,6,6,6,6,5,6,6,7,8,5,5,5,7,6,5,6,4,5,4,5,7,5,4,5,7,7,6,7,10,
    8,6,7,6,6,7,6,6,6,5,6,7,5,6,7,9,8,6,7,5,6,6,6,8,8,6,7,7,8,7,8,10],
  #[
    11,8,8,6,8,6,6,5,8,7,7,8,6,6,6,6,8,6,6,6,7,6,6,6,6,6,6,7,6,5,5,7,
    8,6,6,5,6,6,6,5,7,7,7,7,7,7,8,9,6,5,5,4,6,5,5,6,6,5,5,6,6,6,7,11,
    9,6,7,6,6,5,6,4,6,6,7,8,6,4,5,8,7,6,7,6,7,5,6,6,7,5,6,9,8,7,8,12,
    8,5,6,5,5,5,5,5,6,5,6,8,6,7,9,12,8,7,8,7,8,7,7,8,8,7,8,10,10,10,11,14,
    11,8,8,6,8,7,6,6,8,7,7,8,6,7,6,7,8,6,6,6,7,7,7,8,6,6,6,7,6,6,6,9,
    9,6,6,5,6,7,5,5,7,6,6,6,6,7,7,10,8,5,5,4,6,6,6,9,8,8,8,8,8,9,10,13,
    11,8,9,7,8,7,7,7,8,7,8,10,6,7,7,9,9,6,7,6,7,6,7,8,8,6,7,9,8,8,9,12,
    11,8,9,7,8,8,7,8,9,7,8,9,8,8,9,12,11,8,9,7,9,8,9,10,11,9,10,10,11,10,12,14]
 ]

/-- Odd binary mask divided by two is the source table's column address. -/
private def address (S : Finset ℤ) : ℕ := (∑ a ∈ S, 2 ^ a.toNat) / 2

def potential (k : ℕ) (S : Finset ℤ) : ℕ :=
  (table[k]?.getD #[])[address S]?.getD 15

/-- The explicit 256-state carrier, excluding windows without a current point. -/
def states : Finset (Finset ℤ) :=
  (Finset.Icc (0 : ℤ) 8).powerset.filter fun S => 0 ∈ S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_0 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 0 S < 15 →
        potential 1 (advance S g) < 15 ∧
        potential 0 S + weight (shifted S g) ≤ potential 1 (advance S g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_1 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 1 S < 15 →
        potential 2 (advance S g) < 15 ∧
        potential 1 S + weight (shifted S g) ≤ potential 2 (advance S g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_2 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 2 S < 15 →
        potential 3 (advance S g) < 15 ∧
        potential 2 S + weight (shifted S g) ≤ potential 3 (advance S g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_3 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 3 S < 15 →
        potential 4 (advance S g) < 15 ∧
        potential 3 S + weight (shifted S g) ≤ potential 4 (advance S g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_4 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 4 S < 15 →
        potential 5 (advance S g) < 15 ∧
        potential 4 S + weight (shifted S g) ≤ potential 5 (advance S g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_5 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 5 S < 15 →
        potential 6 (advance S g) < 15 ∧
        potential 5 S + weight (shifted S g) ≤ potential 6 (advance S g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_6 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 6 S < 15 →
        potential 7 (advance S g) < 15 ∧
        potential 6 S + weight (shifted S g) ≤ potential 7 (advance S g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_7 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 7 S < 15 →
        potential 8 (advance S g) < 15 ∧
        potential 7 S + weight (shifted S g) ≤ potential 8 (advance S g) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_step_8 :
    ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential 8 S < 15 →
        potential 9 (advance S g) < 15 ∧
        potential 8 S + weight (shifted S g) ≤ potential 9 (advance S g) := by
  decide +kernel

/-- All finite table entries satisfy every allowed one-step inequality.
The unreachable marker is excluded, rather than treated as reward zero. -/
theorem table_step :
    ∀ k ∈ Finset.range 9, ∀ S ∈ states, ∀ g ∈ Finset.Icc (1 : ℤ) 9,
      potential k S < 15 →
        potential (k+1) (advance S g) < 15 ∧
        potential k S + weight (shifted S g) ≤ potential (k+1) (advance S g) := by
  intro k hk
  have : k < 9 := Finset.mem_range.mp hk
  interval_cases k
  · exact table_step_0
  · exact table_step_1
  · exact table_step_2
  · exact table_step_3
  · exact table_step_4
  · exact table_step_5
  · exact table_step_6
  · exact table_step_7
  · exact table_step_8


/-- Actual nonempty prefix windows belong to the certificate's finite carrier. -/
theorem memory_mem_states (E : Finset ℤ) (x : ℤ) (hx : x ∈ E) :
    memory E x ∈ states := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_powerset.mpr
    exact Finset.filter_subset _ _
  · simp [memory, hx]

set_option maxRecDepth 100000 in
/-- The finite certificate bounds every actual prefix of at most ten points. -/
theorem prefix_certificate (E : Finset ℤ) :
    ∀ x ∈ E, (∀ z ∈ E, z ≤ x) → E.card ≤ 10 →
      count E ≤ potential (E.card-1) (memory E x) ∧
        potential (E.card-1) (memory E x) < 15 := by
  induction E using Finset.induction_on_max with
  | empty => simp
  | @insert y E hy ih =>
    intro x hx hmax hcard
    have hx_eq : x = y := by
      have hxy : y ≤ x := hmax y (by simp)
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rfl
      · have := hy x hx; omega
    subst x
    have hynot : y ∉ E := fun h => lt_irrefl y (hy y h)
    rw [Finset.card_insert_of_notMem hynot] at hcard ⊢
    rcases E.eq_empty_or_nonempty with rfl | hE
    · have hm : memory {y} y = {0} := by
        ext a
        simp only [memory, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
        omega
      have hc : count {y} = 0 := by simp [count, endpoints]
      have hp : potential 0 {0} = 0 := by decide
      simpa only [Finset.insert_empty, Finset.card_empty, zero_add,
        Nat.sub_self, hm, hc, hp] using (show 0 ≤ (0:ℕ) ∧ 0 < (15:ℕ) by omega)
    · let z := E.max' hE
      have hz : z ∈ E := Finset.max'_mem E hE
      have hmaxz : ∀ a ∈ E, a ≤ z := fun a ha => Finset.le_max' E a ha
      have hzy : z < y := hy z hz
      obtain ⟨hc, hp⟩ := ih z hz hmaxz (by omega)
      have hS := memory_mem_states E z hz
      have hn : ∀ a ∈ memory E z, 0 ≤ a := by
        intro a ha
        exact (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      obtain ⟨ha, hw⟩ := cap_gap (memory E z) hn (y-z)
      have hg : min (y-z) 9 ∈ Finset.Icc (1 : ℤ) 9 := by
        simp only [Finset.mem_Icc]
        omega
      have hk : E.card - 1 ∈ Finset.range 9 := by
        simp only [Finset.mem_range]
        have := Finset.card_pos.mpr hE
        omega
      obtain ⟨hp', hc'⟩ := table_step (E.card-1) hk (memory E z) hS
        (min (y-z) 9) hg hp
      have hi : E.card - 1 + 1 = E.card := by
        have := Finset.card_pos.mpr hE
        omega
      rw [ha, hi, ← memory_insert E z y hmaxz hzy] at hp' hc'
      rw [hw] at hc'
      have hcount := count_insert E z y hmaxz hzy
      simp only [Nat.add_sub_cancel]
      exact ⟨by omega, hp'⟩

/-- Every later maximum contributes at most the four literal patterns. -/
private theorem weight_le_four (S : Finset ℤ) : weight S ≤ 4 := by
  unfold weight
  split_ifs <;> omega

/-- The uniform combinatorial bound on arbitrary signed exponent sets. -/
private theorem count_bound (E : Finset ℤ) (hn : 10 ≤ E.card) :
    count E + 26 ≤ 4 * E.card := by
  induction E using Finset.induction_on_max with
  | empty => simp at hn
  | @insert y E hy ih =>
    have hynot : y ∉ E := fun h => lt_irrefl y (hy y h)
    have hcard := Finset.card_insert_of_notMem hynot
    by_cases hsmall : E.card < 10
    · have hn10 : (insert y E).card = 10 := by omega
      have hm : ∀ z ∈ insert y E, z ≤ y := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · rfl
        · exact le_of_lt (hy z hz)
      have hh := prefix_certificate (insert y E) y (by simp) hm (by omega)
      omega
    · have hE : E.Nonempty := Finset.card_pos.mp (by omega)
      let z := E.max' hE
      have hz : z ∈ E := Finset.max'_mem E hE
      have hm : ∀ a ∈ E, a ≤ z := fun a ha => Finset.le_max' E a ha
      have hcount := count_insert E z y hm (hy z hz)
      have hb := ih (by omega)
      have hw := weight_le_four (shifted (memory E z) (y-z))
      omega
/-- Exact template count of every translated interval, with no origin assumption. -/
private theorem count_interval (a : ℤ) (n : ℕ) (hn : 10 ≤ n) :
    count (Finset.Icc a (a+(n:ℤ)-1)) + 26 = 4*n := by
  let E := Finset.Icc a (a+(n:ℤ)-1)
  have h4 : E.filter (fun t => t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E) =
      Finset.Icc a (a+(n:ℤ)-1-4) := by
    ext t; simp only [E, Finset.mem_filter, Finset.mem_Icc]; omega
  have h6 : E.filter (fun t => t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E) =
      Finset.Icc a (a+(n:ℤ)-1-6) := by
    ext t; simp only [E, Finset.mem_filter, Finset.mem_Icc]; omega
  have h7 : E.filter (fun t => t+5 ∈ E ∧ t+7 ∈ E) =
      Finset.Icc a (a+(n:ℤ)-1-7) := by
    ext t; simp only [E, Finset.mem_filter, Finset.mem_Icc]; omega
  have h9 : E.filter (fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E) =
      Finset.Icc a (a+(n:ℤ)-1-9) := by
    ext t; simp only [E, Finset.mem_filter, Finset.mem_Icc]; omega
  change count E + 26 = 4*n
  rw [count_eq_source, h4, h6, h7, h9]
  simp only [Int.card_Icc]
  omega

open scoped Pointwise

/-- Import the frozen algebraic classification without re-proving it. -/
theorem sum_card_identity (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (E : Finset ℤ) :
    ((E.image fun z => r^z) + (E.image fun z => r^z)).card + count E =
      E.card*(E.card+1)/2 := by
  have h := PlasticPowerCollisions.sumset_card_add_template_counts r hr hroot E
  rw [count_eq_source]
  rw [Nat.choose_two_right] at h
  simp only [Nat.add_sub_cancel] at h
  rw [Nat.mul_comm (E.card+1) E.card] at h
  omega

/-- The sharp real-sumset lower bound on every finite exponent set. -/
private theorem sum_card_lower (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (E : Finset ℤ) (hn : 10 ≤ E.card) :
    E.card*(E.card+1)/2 - 4*E.card + 26 ≤
      ((E.image fun z => r^z) + (E.image fun z => r^z)).card := by
  have hc := count_bound E hn
  have hs := sum_card_identity r hr hroot E
  have hM : 4*E.card ≤ E.card*(E.card+1)/2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0<2)).mpr (by
      calc 4*E.card*2 = E.card*8 := by ring
           _ ≤ E.card*(E.card+1) := Nat.mul_le_mul_left _ (by omega))
  omega

/-- Actual real sums attain the bound for every translated consecutive interval. -/
private theorem sum_card_interval (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (a : ℤ) (n : ℕ) (hn : 10 ≤ n) :
    let E := Finset.Icc a (a+(n:ℤ)-1)
    ((E.image fun z => r^z) + (E.image fun z => r^z)).card = n*(n+1)/2-4*n+26 := by
  dsimp only
  let E := Finset.Icc a (a+(n:ℤ)-1)
  have hcard : E.card=n := by simp only [E, Int.card_Icc]; omega
  have hc := count_interval a n hn
  have hs := sum_card_identity r hr hroot E
  rw [hcard] at hs
  have hM : 4*n ≤ n*(n+1)/2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0<2)).mpr (by
      calc 4*n*2 = n*8 := by ring
           _ ≤ n*(n+1) := Nat.mul_le_mul_left _ (by omega))
  change ((E.image fun z => r^z) + (E.image fun z => r^z)).card = _
  change count E + 26 = 4*n at hc
  omega
/-- Sharp extremal theorem and least uniform threshold, on the actual power group. -/
theorem whole_theorem_three_one (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (n : ℕ) (hn : 10 ≤ n) :
    (∀ E : Finset ℤ, E.card=n → count E ≤ 4*n-26 ∧
      n*(n+1)/2-4*n+26 ≤ ((E.image fun z => r^z)+(E.image fun z => r^z)).card) ∧
    (∀ a : ℤ, let E := Finset.Icc a (a+(n:ℤ)-1)
      E.card=n ∧ count E=4*n-26 ∧
      ((E.image fun z => r^z)+(E.image fun z => r^z)).card=n*(n+1)/2-4*n+26) ∧
    IsLeast {m : ℕ | ∃ A : Finset ℝ,
      (↑A : Set ℝ) ⊆ Set.range (fun z : ℤ => r^z) ∧ A.card=n ∧ (A+A).card=m}
      (n*(n+1)/2-4*n+26) ∧
    IsLeast {N : ℤ | ∀ E : Finset ℤ, N ≤ (E.card : ℤ) →
      (count E : ℤ) ≤ 4*(E.card : ℤ)-26} 10 := by
  classical
  have hf : Function.Injective (fun z : ℤ => r^z) := (zpow_right_strictMono₀ hr).injective
  have hbound : ∀ E : Finset ℤ, E.card=n → count E ≤ 4*n-26 ∧
      n*(n+1)/2-4*n+26 ≤ ((E.image fun z => r^z)+(E.image fun z => r^z)).card := by
    intro E he
    have hc := count_bound E (by omega)
    have hs := sum_card_lower r hr hroot E (by omega)
    rw [he] at hs
    exact ⟨by omega, hs⟩
  have hint : ∀ a : ℤ, let E := Finset.Icc a (a+(n:ℤ)-1)
      E.card=n ∧ count E=4*n-26 ∧
      ((E.image fun z => r^z)+(E.image fun z => r^z)).card=n*(n+1)/2-4*n+26 := by
    intro a
    dsimp only
    have hc := count_interval a n hn
    refine ⟨?_, by omega, sum_card_interval r hr hroot a n hn⟩
    simp only [Int.card_Icc]
    omega
  refine ⟨hbound, hint, ?_, ?_⟩
  · constructor
    · let E := Finset.Icc (0 : ℤ) ((n : ℤ)-1)
      refine ⟨E.image (fun z => r^z), ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
        exact ⟨z, rfl⟩
      · rw [Finset.card_image_of_injective _ hf]
        simpa only [zero_add] using (hint 0).1
      · simpa only [zero_add] using (hint 0).2.2
    · intro m hm
      obtain ⟨A, hA, hcard, hsum⟩ := hm
      let E := A.preimage (fun z : ℤ => r^z) hf.injOn
      have himage : E.image (fun z => r^z) = A := by
        exact (Finset.image_preimage _ A hf.injOn).trans
          (Finset.filter_eq_self.mpr fun x hx => hA hx)
      have he : E.card=n := by
        rw [← Finset.card_image_of_injective E hf, himage, hcard]
      have hb := (hbound E he).2
      simpa only [himage, hsum] using hb
  · constructor
    · intro E hnE
      have hb := count_bound E (by omega)
      omega
    intro N hN
    have hcard : (({0} : Finset ℤ) ∪ Finset.Icc 2 9).card = 9 := by decide
    have hcount : count (({0} : Finset ℤ) ∪ Finset.Icc 2 9) = 11 := by decide
    by_contra h
    have hh := hN (({0} : Finset ℤ) ∪ Finset.Icc 2 9) (by rw [hcard]; omega)
    rw [hcount, hcard] at hh
    norm_num at hh

#print axioms whole_theorem_three_one

end D5.S3.Arith.Additive.PlasticExtremal
