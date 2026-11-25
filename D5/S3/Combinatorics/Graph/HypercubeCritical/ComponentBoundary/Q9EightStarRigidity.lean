/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Huang curvature makes the occupied graph diamond-free and identifies its complete bipartite equality. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap

/-!
# Eight-column rigidity for the occupied graph

For Q9 Problem 2, an occupied graph isomorphic to K₄,₄ forces the eight
projected columns to be the full neighborhood of a unique empty row. The
occupied squares between those columns recover the two parts of the graph.

The sign argument also shows that every occupied triangle is supported by
one occupied row. With a three-contact cap, an edge lies in at most one
triangle.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarRigidity

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj)
open BalancedCubeGirth (adjacent_exists_flip flip_comm)
open BalancedCubeComponentBoundary (flip_injective)
open PrimeContactCubeOrders (rowContacts mem_rowContacts)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private edge edge_sq edge_reciprocal edge_curvature from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private square_of_shared_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCubeLift
open private diff diff_card diff_symm diff_triangle_card diff_double_flip
  diff_injective common_label_subset_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.PrimeContactCardinalityGap

variable {n : ℕ}

/-- The contribution of a column after switching its Huang sign. -/
def switchedEntry (τ : Q n → ℝ) (r q : Q n) : ℝ := huangMatrix n r q * τ q

/-- Unit switching signs make all selected contacts at each occupied row agree. -/
structure SwitchingCoherent (K : Finset (Q n)) (occupied : Q n → Bool) (τ : Q n → ℝ) :
    Prop where
  unit : ∀ q ∈ K, τ q ^ 2 = 1
  agree : ∀ ⦃q p r : Q n⦄, q ∈ K → p ∈ K →
    (hypercube n).Adj q r → (hypercube n).Adj p r → occupied r = true →
    switchedEntry τ r q = switchedEntry τ r p

/-- Distinct selected columns are adjacent when they share an occupied row. -/
def occupiedGraph (K : Finset (Q n)) (occupied : Q n → Bool) : SimpleGraph (Q n) where
  Adj q p := q ∈ K ∧ p ∈ K ∧ q ≠ p ∧
    ∃ r, occupied r = true ∧ (hypercube n).Adj q r ∧ (hypercube n).Adj p r
  symm := ⟨by
    rintro q p ⟨hq, hp, hqp, r, ho, hqr, hpr⟩
    exact ⟨hp, hq, hqp.symm, r, ho, hpr, hqr⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

variable {K : Finset (Q n)} {occupied : Q n → Bool} {τ : Q n → ℝ}

theorem occupiedGraph_adj {q p : Q n} :
    (occupiedGraph K occupied).Adj q p ↔ q ∈ K ∧ p ∈ K ∧ q ≠ p ∧
      ∃ r, occupied r = true ∧ (hypercube n).Adj q r ∧ (hypercube n).Adj p r :=
  Iff.rfl

/-- A shared row identifies the two coordinates on which the columns differ. -/
private theorem shared_row_label {q p r : Q n} (hqp : q ≠ p)
    (hqr : (hypercube n).Adj q r) (hpr : (hypercube n).Adj p r) :
    ∃ i j : Fin n, i ≠ j ∧ r = flip q i ∧ flip (flip q i) j = p ∧
      diff q p = {i, j} := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip hqr
  obtain ⟨j, hj⟩ := adjacent_exists_flip hpr
  obtain ⟨hij, hp, _⟩ := square_of_shared_row hqp (hi.symm.trans hj)
  exact ⟨i, j, hij, hi, hp, hp ▸ diff_double_flip q hij⟩

/-- An occupied graph edge is a distance-two pair of cube columns. -/
theorem hammingDist_of_occupiedAdj {q p : Q n} (h : (occupiedGraph K occupied).Adj q p) :
    hammingDist q p = 2 := by
  obtain ⟨_, _, hqp, r, _, hqr, hpr⟩ := occupiedGraph_adj.mp h
  obtain ⟨i, j, hij, _, _, hdiff⟩ := shared_row_label hqp hqr hpr
  rw [← diff_card, hdiff, Finset.card_pair hij]

private theorem adj_flip_iff_mem_diff {q p : Q n} (hd : hammingDist q p = 2) (i : Fin n) :
    (hypercube n).Adj p (flip q i) ↔ i ∈ diff q p := by
  constructor
  · intro h
    have hqp : q ≠ p := by
      rintro rfl
      simp at hd
    obtain ⟨a, b, _, he, _, hlabel⟩ := shared_row_label hqp (flip_adj q i) h
    have hia : i = a := flip_injective q he
    rw [hia, hlabel]
    simp
  · intro hi
    have hc : (diff q p).card = 2 := (diff_card q p).trans hd
    obtain ⟨a, b, hab, hlabel⟩ := Finset.card_eq_two.mp hc
    have hp : flip (flip q a) b = p :=
      diff_injective q ((diff_double_flip q hab).trans hlabel.symm)
    rw [hlabel, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hia | hib
    · rw [hia, ← hp]
      exact (flip_adj (flip q a) b).symm
    · rw [hib, ← hp, flip_comm q a b]
      exact (flip_adj (flip q b) a).symm

private theorem switchedEntry_sq (hs : SwitchingCoherent K occupied τ)
    {q r : Q n} (hq : q ∈ K) (hqr : (hypercube n).Adj q r) :
    switchedEntry τ r q ^ 2 = 1 := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip hqr
  have hentry : huangMatrix n r q ^ 2 = 1 := by
    rw [hi]
    simpa only [edge, BalancedCriticalSpectrum.flip_flip] using edge_sq (flip q i) i
  rw [switchedEntry, mul_pow, hentry, hs.unit q hq, mul_one]

private theorem switched_product_at_occupied (hs : SwitchingCoherent K occupied τ)
    {q p r : Q n} (hq : q ∈ K) (hp : p ∈ K) (ho : occupied r = true)
    (hqr : (hypercube n).Adj q r) (hpr : (hypercube n).Adj p r) :
    switchedEntry τ r q * switchedEntry τ r p = 1 := by
  rw [← hs.agree hq hp hqr hpr ho, ← pow_two]
  exact switchedEntry_sq hs hq hqr

private theorem switched_square {q p r s : Q n} (hqp : q ≠ p) (hrs : r ≠ s)
    (hqr : (hypercube n).Adj q r) (hpr : (hypercube n).Adj p r)
    (hqs : (hypercube n).Adj q s) (hps : (hypercube n).Adj p s) :
    switchedEntry τ r q * switchedEntry τ r p =
      -(switchedEntry τ s q * switchedEntry τ s p) := by
  obtain ⟨i, j, hij, hr, hp, hlabel⟩ := shared_row_label hqp hqr hpr
  obtain ⟨k, hk⟩ := adjacent_exists_flip hqs
  have hd : hammingDist q p = 2 := by rw [← diff_card, hlabel, Finset.card_pair hij]
  have hmem := (adj_flip_iff_mem_diff hd k).mp (hk ▸ hps)
  rw [hlabel, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hs : s = flip q j := by
    rcases hmem with hki | hkj
    · exact (hrs (hr.trans (hki ▸ hk.symm))).elim
    · exact hk.trans (congrArg (flip q) hkj)
  have hp' : flip (flip q j) i = p := (flip_comm q j i).trans hp
  have hiq : huangMatrix n (flip q i) q = edge q i := by
    simpa only [edge, BalancedCriticalSpectrum.flip_flip] using edge_reciprocal q i
  have hjq : huangMatrix n (flip q j) q = edge q j := by
    simpa only [edge, BalancedCriticalSpectrum.flip_flip] using edge_reciprocal q j
  have hip : edge (flip q i) j = huangMatrix n (flip q i) p := by simp only [edge, hp]
  have hjp : edge (flip q j) i = huangMatrix n (flip q j) p := by simp only [edge, hp']
  unfold switchedEntry
  rw [hr, hs, hiq, hjq, ← hip, ← hjp]
  calc
    _ = (edge q i * edge (flip q i) j) * (τ q * τ p) := by ring
    _ = -(edge q j * edge (flip q j) i) * (τ q * τ p) := by rw [edge_curvature q hij]
    _ = _ := by ring

/-- Switching coherence forbids a pair from sharing two different occupied rows. -/
theorem occupied_common_row_unique (hs : SwitchingCoherent K occupied τ)
    {q p r s : Q n} (hq : q ∈ K) (hp : p ∈ K) (hqp : q ≠ p)
    (hr : occupied r = true) (hs' : occupied s = true)
    (hqr : (hypercube n).Adj q r) (hpr : (hypercube n).Adj p r)
    (hqs : (hypercube n).Adj q s) (hps : (hypercube n).Adj p s) : r = s := by
  by_contra hne
  have h := switched_square (τ := τ) hqp hne hqr hpr hqs hps
  rw [switched_product_at_occupied hs hq hp hr hqr hpr,
    switched_product_at_occupied hs hq hp hs' hqs hps] at h
  norm_num at h

private theorem common_triangle_row {q p a : Q n}
    (hqp : hammingDist q p = 2) (hqa : hammingDist q a = 2)
    (hpa : hammingDist p a = 2) :
    ∃! r, (hypercube n).Adj q r ∧ (hypercube n).Adj p r ∧ (hypercube n).Adj a r := by
  have hc := diff_triangle_card p a q
  rw [diff_symm p q, diff_symm a q, diff_card p a, diff_card q p, diff_card q a,
    hqp, hqa, hpa] at hc
  obtain ⟨i, hi, hiunique⟩ := Finset.card_eq_one_iff_existsUnique.mp
    (show (diff q p ∩ diff q a).card = 1 by omega)
  have hmem := Finset.mem_inter.mp hi
  refine ⟨flip q i, ⟨flip_adj q i, (adj_flip_iff_mem_diff hqp i).mpr hmem.1,
    (adj_flip_iff_mem_diff hqa i).mpr hmem.2⟩, ?_⟩
  rintro r ⟨hqr, hpr, har⟩
  obtain ⟨j, rfl⟩ := adjacent_exists_flip hqr
  have hj := hiunique j (Finset.mem_inter.mpr
    ⟨(adj_flip_iff_mem_diff hqp j).mp hpr, (adj_flip_iff_mem_diff hqa j).mp har⟩)
  exact congrArg (flip q) hj

private theorem switched_product_at_other_row (hs : SwitchingCoherent K occupied τ)
    {q p r : Q n} (h : (occupiedGraph K occupied).Adj q p) (hr : occupied r ≠ true)
    (hqr : (hypercube n).Adj q r) (hpr : (hypercube n).Adj p r) :
    switchedEntry τ r q * switchedEntry τ r p = -1 := by
  obtain ⟨hq, hp, hqp, s, hso, hqs, hps⟩ := occupiedGraph_adj.mp h
  have hrs : r ≠ s := fun he => hr (he.symm ▸ hso)
  rw [switched_square hqp hrs hqr hpr hqs hps,
    switched_product_at_occupied hs hq hp hso hqs hps]

/-- Three edges of the occupied graph have a single common occupied row. -/
theorem occupied_triangle_row (hs : SwitchingCoherent K occupied τ) {q p a : Q n}
    (hqp : (occupiedGraph K occupied).Adj q p) (hqa : (occupiedGraph K occupied).Adj q a)
    (hpa : (occupiedGraph K occupied).Adj p a) :
    ∃! r, occupied r = true ∧
      (hypercube n).Adj q r ∧ (hypercube n).Adj p r ∧ (hypercube n).Adj a r := by
  obtain ⟨r, ⟨hqr, hpr, har⟩, hunique⟩ := common_triangle_row
    (hammingDist_of_occupiedAdj hqp) (hammingDist_of_occupiedAdj hqa)
    (hammingDist_of_occupiedAdj hpa)
  refine ⟨r, ⟨?_, hqr, hpr, har⟩, fun s hs' => hunique s hs'.2⟩
  by_contra hr
  have h₁ := switched_product_at_other_row hs hqp hr hqr hpr
  have h₂ := switched_product_at_other_row hs hpa hr hpr har
  have h₃ := switched_product_at_other_row hs hqa hr hqr har
  have hpK := (occupiedGraph_adj.mp hqp).2.1
  have hc : (switchedEntry τ r q * switchedEntry τ r p) *
      (switchedEntry τ r p * switchedEntry τ r a) = -1 := by
    calc
      _ = (switchedEntry τ r q * switchedEntry τ r a) * switchedEntry τ r p ^ 2 := by ring
      _ = -1 := by rw [switchedEntry_sq hs hpK hpr, mul_one, h₃]
  rw [h₁, h₂] at hc
  norm_num at hc

/-- The three-contact cap makes the two common neighbors of any occupied edge
coincide whenever both exist. -/
theorem occupied_edge_triangle_unique {K : Finset (Q 8)}
    {occupied : Q 8 → Bool} {τ : Q 8 → ℝ}
    (hs : SwitchingCoherent K occupied τ)
    (hcap : ∀ r, occupied r = true → (rowContacts K r).card ≤ 3)
    {q p a b : Q 8} (hqp : (occupiedGraph K occupied).Adj q p)
    (hqa : (occupiedGraph K occupied).Adj q a) (hpa : (occupiedGraph K occupied).Adj p a)
    (hqb : (occupiedGraph K occupied).Adj q b) (hpb : (occupiedGraph K occupied).Adj p b) :
    a = b := by
  classical
  obtain ⟨r, ⟨hro, hqr, hpr, har⟩, _⟩ := occupied_triangle_row hs hqp hqa hpa
  obtain ⟨s, ⟨hso, hqs, hps, hbs⟩, _⟩ := occupied_triangle_row hs hqp hqb hpb
  obtain ⟨hqK, hpK, hqpne, _⟩ := occupiedGraph_adj.mp hqp
  obtain ⟨_, haK, hqane, _⟩ := occupiedGraph_adj.mp hqa
  obtain ⟨_, hbK, hqbne, _⟩ := occupiedGraph_adj.mp hqb
  have hpane := (occupiedGraph_adj.mp hpa).2.2.1
  have hpbne := (occupiedGraph_adj.mp hpb).2.2.1
  have hrs := occupied_common_row_unique hs hqK hpK hqpne hro hso hqr hpr hqs hps
  have hbr : (hypercube 8).Adj b r := hrs.symm ▸ hbs
  by_contra hab
  have hsub : ({q, p, a, b} : Finset (Q 8)) ⊆ rowContacts K r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_rowContacts.mpr ⟨hqK, hqr⟩
    · exact mem_rowContacts.mpr ⟨hpK, hpr⟩
    · exact mem_rowContacts.mpr ⟨haK, har⟩
    · exact mem_rowContacts.mpr ⟨hbK, hbr⟩
  have hqnot : q ∉ ({p, a, b} : Finset (Q 8)) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      And.intro hqpne (And.intro hqane hqbne)
  have hpnot : p ∉ ({a, b} : Finset (Q 8)) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using And.intro hpane hpbne
  have hf : ({q, p, a, b} : Finset (Q 8)).card = 4 := by
    rw [Finset.card_insert_of_notMem hqnot, Finset.card_insert_of_notMem hpnot, Finset.card_pair hab]
  have hle := Finset.card_le_card hsub
  rw [hf] at hle
  have := hcap r hro
  omega

/-- The axes leading from a particular column to occupied rows. -/
def occupiedAxes (occupied : Q n → Bool) (q : Q n) : Finset (Fin n) :=
  Finset.univ.filter fun i => occupied (flip q i) = true

@[simp] theorem mem_occupiedAxes {q : Q n} {i : Fin n} :
    i ∈ occupiedAxes occupied q ↔ occupied (flip q i) = true := by
  simp [occupiedAxes]

/-- An edge through axis i has its other common row on a different, empty axis. -/
theorem occupied_edge_square (hs : SwitchingCoherent K occupied τ)
    {q p r : Q n} (hq : q ∈ K) (hp : p ∈ K) (hqp : q ≠ p)
    (ho : occupied r = true) (hqr : (hypercube n).Adj q r) (hpr : (hypercube n).Adj p r) :
    ∃ i j : Fin n, i ≠ j ∧ r = flip q i ∧ flip (flip q i) j = p ∧
      occupied (flip q j) = false := by
  obtain ⟨i, j, hij, hr, hp', _⟩ := shared_row_label hqp hqr hpr
  refine ⟨i, j, hij, hr, hp', Bool.eq_false_of_not_eq_true ?_⟩
  intro hj
  have hp'' : flip (flip q j) i = p := (flip_comm q j i).trans hp'
  have hpr' : (hypercube n).Adj p (flip q j) := hp'' ▸ (flip_adj (flip q j) i).symm
  have he := occupied_common_row_unique hs hq hp hqp ho hj hqr hpr (flip_adj q j) hpr'
  exact hij (flip_injective q (hr.symm.trans he))

private theorem diff_star_pair (r : Q n) {i j : Fin n} (hij : i ≠ j) :
    diff (flip r i) (flip r j) = {i, j} := by
  simpa only [BalancedCriticalSpectrum.flip_flip] using diff_double_flip (flip r i) hij

private theorem hammingDist_star_pair (r : Q n) {i j : Fin n} (hij : i ≠ j) :
    hammingDist (flip r i) (flip r j) = 2 := by
  rw [← diff_card, diff_star_pair r hij, Finset.card_pair hij]

/-- The occupied graph on neighbors of an empty row records whether
the opposite row of each coordinate square is occupied. -/
theorem occupied_square_iff_adj {r : Q n} (hr : occupied r = false)
    {i j : Fin n} (hij : i ≠ j) (hi : flip r i ∈ K) (hj : flip r j ∈ K) :
    occupied (flip (flip r i) j) = true ↔
      (occupiedGraph K occupied).Adj (flip r i) (flip r j) := by
  have hne : flip r i ≠ flip r j := fun h => hij (flip_injective r h)
  have hs : flip (flip r i) j = flip (flip r j) i := flip_comm r i j
  constructor
  · intro ho
    exact ⟨hi, hj, hne, _, ho, flip_adj (flip r i) j, hs.symm ▸ flip_adj (flip r j) i⟩
  · intro hadj
    obtain ⟨_, _, _, s, hso, his, hjs⟩ := occupiedGraph_adj.mp hadj
    obtain ⟨k, hk⟩ := adjacent_exists_flip his
    have hmem := (adj_flip_iff_mem_diff (hammingDist_star_pair r hij) k).mp (hk ▸ hjs)
    rw [diff_star_pair r hij, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · rw [hk, BalancedCriticalSpectrum.flip_flip, hr] at hso
      cases hso
    · exact hk ▸ hso

/-- If the occupied graph is K₄,₄ with parts A and B, their union is the
full neighborhood of a unique empty row. A square through the center has
an occupied opposite row exactly when its two axes give opposite parts. -/
theorem occupiedK44_star {A B : Finset (Q 8)} {occupied : Q 8 → Bool} {τ : Q 8 → ℝ}
    (hs : SwitchingCoherent (A ∪ B) occupied τ)
    (hA : A.card = 4) (hB : B.card = 4) (hsep : Disjoint A B)
    (hpart : ∀ q p, (occupiedGraph (A ∪ B) occupied).Adj q p ↔
      (q ∈ A ∧ p ∈ B) ∨ (q ∈ B ∧ p ∈ A))
    (hfour : ∀ q ∈ A ∪ B, (occupiedAxes occupied q).card = 4) :
    ∃! r : Q 8, occupied r = false ∧
      (∀ x, x ∈ A ∪ B ↔ (hypercube 8).Adj r x) ∧
      (∀ i j : Fin 8, i ≠ j →
        (occupied (flip (flip r i) j) = true ↔
          (flip r i ∈ A ∧ flip r j ∈ B) ∨ (flip r i ∈ B ∧ flip r j ∈ A))) := by
  classical
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hqK : q ∈ A ∪ B := Finset.mem_union_left _ hq
  let O := occupiedAxes occupied q
  have hO : O.card = 4 := hfour q hqK
  have hsep' {x : Q 8} (ha : x ∈ A) (hb : x ∈ B) : False := Finset.disjoint_left.mp hsep ha hb
  have hparams (b : B) : ∃ j k : Fin 8,
      j ∈ O ∧ occupied (flip q k) = false ∧ flip (flip q j) k = (b : Q 8) := by
    obtain ⟨hqK, hbK, hqb, s, hso, hqs, hbs⟩ :=
      occupiedGraph_adj.mp ((hpart q b).mpr (Or.inl ⟨hq, b.property⟩))
    obtain ⟨j, k, _, hj, hp, hk⟩ := occupied_edge_square hs hqK hbK hqb hso hqs hbs
    exact ⟨j, k, mem_occupiedAxes.mpr (hj ▸ hso), hk, hp⟩
  choose j k hj hk hp using hparams
  have hjk (b c : B) : j b ≠ k c := by
    intro he
    have ho := mem_occupiedAxes.mp (show j b ∈ occupiedAxes occupied q from hj b)
    rw [he, hk c] at ho
    cases ho
  have hjinj : Function.Injective j := by
    intro b c hbc
    apply Subtype.ext
    by_contra hne
    have hb : (hypercube 8).Adj (b : Q 8) (flip q (j b)) :=
      (hp b) ▸ (flip_adj (flip q (j b)) (k b)).symm
    have hc : (hypercube 8).Adj (c : Q 8) (flip q (j c)) :=
      (hp c) ▸ (flip_adj (flip q (j c)) (k c)).symm
    have hcross := (hpart b c).mp
      ⟨Finset.mem_union_right _ b.property, Finset.mem_union_right _ c.property, hne,
        flip q (j b), mem_occupiedAxes.mp (hj b), hb, hbc.symm ▸ hc⟩
    rcases hcross with h | h
    · exact hsep' h.1 b.property
    · exact hsep' h.2 c.property
  have hJsub : (Finset.univ.image j) ⊆ O := by
    intro l hl
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hl
    exact hj b
  have hJcard : (Finset.univ.image j).card = 4 := by
    rw [Finset.card_image_of_injective _ hjinj, Finset.card_univ, Fintype.card_coe, hB]
  have hJ : Finset.univ.image j = O :=
    Finset.eq_of_subset_of_card_le hJsub (by rw [hJcard, hO])
  have hsur (l : Fin 8) (hl : l ∈ O) : ∃ b : B, j b = l := by
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp (hJ.symm ▸ hl)
    exact ⟨b, he⟩
  have hlabel (b : B) : diff q (b : Q 8) = {j b, k b} := by
    simpa only [hp b] using diff_double_flip q (hjk b b)
  have hqdist (b : B) : hammingDist q (b : Q 8) = 2 :=
    hammingDist_of_occupiedAdj ((hpart q b).mpr (Or.inl ⟨hq, b.property⟩))
  have hadist {a : Q 8} (ha : a ∈ A) (b : B) : hammingDist a (b : Q 8) = 2 :=
    hammingDist_of_occupiedAdj ((hpart a b).mpr (Or.inl ⟨ha, b.property⟩))
  obtain ⟨b₀, hb₀⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  let bRef : B := ⟨b₀, hb₀⟩
  have hkRef : k bRef ∉ O := by
    intro he
    have ho := mem_occupiedAxes.mp (show k bRef ∈ occupiedAxes occupied q from he)
    rw [hk bRef] at ho
    cases ho
  -- A label of size four would contain all four occupied axes and an empty one.
  have haweight {a : Q 8} (ha : a ∈ A.erase q) : hammingDist q a = 2 := by
    obtain ⟨hane, haA⟩ := Finset.mem_erase.mp ha
    by_contra hn
    have hsub (b : B) : ({j b, k b} : Finset (Fin 8)) ⊆ diff q a := by
      rw [← hlabel b]
      exact (common_label_subset_four hane.symm hn (hqdist b) (hadist haA b)).2
    have hinsert : insert (k bRef) O ⊆ diff q a := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hsub bRef (by simp)
      · obtain ⟨b, rfl⟩ := hsur l hl
        exact hsub b (by simp)
    have hle := Finset.card_le_card hinsert
    have hc := (common_label_subset_four hane.symm hn (hqdist bRef) (hadist haA bRef)).1
    rw [Finset.card_insert_of_notMem hkRef, hO, hc] at hle
    omega
  -- An occupied axis in the label would give an edge within A.
  have ha_avoids_occupied {a : Q 8} (ha : a ∈ A.erase q) {l : Fin 8}
      (hl : l ∈ O) (hd : l ∈ diff q a) : False := by
    obtain ⟨hane, haA⟩ := Finset.mem_erase.mp ha
    have hqa := (adj_flip_iff_mem_diff (haweight ha) l).mpr hd
    have hcross := (hpart q a).mp
      ⟨hqK, Finset.mem_union_left _ haA, hane.symm, flip q l,
        mem_occupiedAxes.mp hl, flip_adj q l, hqa⟩
    rcases hcross with h | h
    · exact hsep' haA h.2
    · exact hsep' hq h.1
  have ha_contains_empty_axis {a : Q 8} (ha : a ∈ A.erase q) (b : B) :
      k b ∈ diff q a := by
    have hc := diff_triangle_card a (b : Q 8) q
    have haA := (Finset.mem_erase.mp ha).2
    rw [diff_symm a q, diff_symm (b : Q 8) q, diff_card a (b : Q 8),
      diff_card q a, diff_card q (b : Q 8), haweight ha, hqdist b, hadist haA b] at hc
    have hpos : 0 < (diff q a ∩ diff q (b : Q 8)).card := by omega
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
    obtain ⟨hla, hlb⟩ := Finset.mem_inter.mp hl
    rw [hlabel b, Finset.mem_insert, Finset.mem_singleton] at hlb
    rcases hlb with he | he
    · exact (ha_avoids_occupied ha (show l ∈ O from he.symm ▸ hj b) hla).elim
    · exact he ▸ hla
  -- Two distinct empty axes would determine the entire label of every nonroot A column.
  have hkconstant (b : B) : k b = k bRef := by
    by_contra hne
    have heq {a : Q 8} (ha : a ∈ A.erase q) : ({k b, k bRef} : Finset (Fin 8)) = diff q a := by
      apply Finset.eq_of_subset_of_card_le
      · intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · exact ha_contains_empty_axis ha b
        · exact ha_contains_empty_axis ha bRef
      · rw [Finset.card_pair hne, diff_card, haweight ha]
    have hle : (A.erase q).card ≤ 1 := Finset.card_le_one.mpr (by
      intro a ha c hc
      exact diff_injective q ((heq ha).symm.trans (heq hc)))
    rw [Finset.card_erase_of_mem hq, hA] at hle
    omega
  let r := flip q (k bRef)
  have hro : occupied r = false := hk bRef
  have hstar (x : Q 8) (hx : x ∈ A ∪ B) : (hypercube 8).Adj r x := by
    rcases Finset.mem_union.mp hx with hxA | hxB
    · by_cases hxq : x = q
      · subst x
        exact (flip_adj q (k bRef)).symm
      · have ha : x ∈ A.erase q := Finset.mem_erase.mpr ⟨hxq, hxA⟩
        exact ((adj_flip_iff_mem_diff (haweight ha) (k bRef)).mpr
          (ha_contains_empty_axis ha bRef)).symm
    · let b : B := ⟨x, hxB⟩
      have he : flip r (j b) = x := by
        calc
          flip r (j b) = flip (flip q (j b)) (k bRef) := flip_comm q (k bRef) (j b)
          _ = flip (flip q (j b)) (k b) := by rw [hkconstant b]
          _ = x := hp b
      exact he ▸ flip_adj r (j b)
  let S : Finset (Q 8) := Finset.univ.image (BalancedCriticalSpectrum.flip r)
  have hS (x : Q 8) : x ∈ S ↔ (hypercube 8).Adj r x := by
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact flip_adj r i
    · intro hx
      obtain ⟨i, hi⟩ := adjacent_exists_flip hx
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
  have hSK : A ∪ B = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact (hS x).mpr (hstar x hx)
    · rw [Finset.card_union_of_disjoint hsep, hA, hB]
      change (Finset.univ.image (BalancedCriticalSpectrum.flip r)).card ≤ 4 + 4
      rw [Finset.card_image_of_injective _ (flip_injective r), Finset.card_univ, Fintype.card_fin]
  have hfull (x : Q 8) : x ∈ A ∪ B ↔ (hypercube 8).Adj r x := by rw [hSK, hS]
  refine ⟨r, ⟨hro, hfull, ?_⟩, ?_⟩
  · intro i j hij
    have hi := (hfull (flip r i)).mpr (flip_adj r i)
    have hj' := (hfull (flip r j)).mpr (flip_adj r j)
    exact (occupied_square_iff_adj hro hij hi hj').trans (hpart (flip r i) (flip r j))
  · rintro s ⟨_, hsfull, _⟩
    let i : Fin 8 := 0
    let j' : Fin 8 := 1
    let k' : Fin 8 := 2
    obtain ⟨u, _, hu⟩ := common_triangle_row
      (hammingDist_star_pair r (show (0 : Fin 8) ≠ 1 by decide))
      (hammingDist_star_pair r (show (0 : Fin 8) ≠ 2 by decide))
      (hammingDist_star_pair r (show (1 : Fin 8) ≠ 2 by decide))
    have hru := hu r ⟨(flip_adj r i).symm, (flip_adj r j').symm, (flip_adj r k').symm⟩
    have hsu := hu s ⟨((hsfull _).mp ((hfull _).mpr (flip_adj r i))).symm,
      ((hsfull _).mp ((hfull _).mpr (flip_adj r j'))).symm,
      ((hsfull _).mp ((hfull _).mpr (flip_adj r k'))).symm⟩
    exact hsu.trans hru.symm

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarRigidity
