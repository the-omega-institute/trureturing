/- GID: D5/S3/Combinatorics/Geometry/CentralSizeEdgeMinima
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/CentralSizeEdgeMinima
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Feasible center sizes of n-point metric spaces and their sharp central-edge minima. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#323; delivered and
  first frozen together with CompleteCentralParity and MinimumCentralOrder)
escape_witness: odd_cov and odd_hit (the borrowed-edge packing: on Z/(2m+1) every class
  r < 2m - 1 together with one reserved edge covers every point, and these 2m - 1 covers use
  only m + 1 edges each), with chord_hit and even_hit for the edge count of every class.
proof_shape:
  ctr, wrap, labO, chord, edgeO, edgeE, Feasible: definitions; consumers: the lemmas below.
  chord_hit, odd_cov, odd_hit, even_hit: content; consumer: attain.
  ctr_spec, cls_eq: bind-only helpers; consumers: chord_hit, even_hit.
  feasible_of: content (the two-point space is bicentral); consumer: all_center_sizes.
  attain: content via the band; consumer: all_center_sizes.
  all_center_sizes: content.
Direct frozen dependencies: D5/S3/Combinatorics/Geometry/CentralEdgeCover (edge_cover_bound),
  D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges (center, centralGraph).
Same-delivery dependencies: CompleteCentralParity (Band, plab, cls, band lemmas, space_cov,
  third_point), MinimumCentralOrder (center_card_bound).
Search record (§3.1): no frozen module packs near-one-factors of an odd complete graph into
  spanning edge covers; the paper credits Andersen's cover-index criterion as the antecedent and
  gives the direct construction formalized here.
-/

import D5.S3.Combinatorics.Geometry.MinimumCentralOrder

/-! # All feasible center sizes and sharp edge minima

For `n ≥ 3`, an `n`-point metric space can have exactly `k` central values (zero included)
precisely for `1 ≤ k ≤ n` when `n` is even and for `1 ≤ k ≤ n - 1` when `n` is odd; at `n = 1`
only `k = 1` and at `n = 2` only `k = 2` occur. For every feasible pair the least number of
central edges is `(k - 1) ⌈n / 2⌉`.

Even orders use `k - 1` round-robin classes. For odd `n = 2m + 1` the classes `i + j ≡ r`
on `Z/(2m+1)` miss one point each; the classes `2m - 1` and `2m` are reserved, and each other
class `r` borrows one reserved edge at its missing point, oriented along the path that the two
reserved classes form. Every other pair gets its own non-central distance.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.CentralSizeEdgeMinima

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open D5.S3.Combinatorics.Geometry.CentralEdgeCover
open D5.S3.Combinatorics.Geometry.CompleteCentralParity
open D5.S3.Combinatorics.Geometry.MinimumCentralOrder

noncomputable section

variable (m : ℕ)

/-- The point missed by class `r` among `Z/(2m+1)`: the solution of `2u ≡ r`. -/
private def ctr (r : ℕ) : ℕ := if r % 2 = 0 then r / 2 else (r + 2 * m + 1) / 2

private lemma ctr_spec (r : ℕ) (hr : r < 2 * m + 1) :
    (2 * ctr m r = r ∨ 2 * ctr m r = r + (2 * m + 1)) ∧ ctr m r < 2 * m + 1 := by
  unfold ctr; split_ifs <;> omega

/-- Reduction of `v < 2 (2m+1)` modulo `2m+1`. -/
private def wrap (v : ℕ) : ℕ := if v < 2 * m + 1 then v else v - (2 * m + 1)

/-- The odd-order label of a pair `i < j` of points of `Fin (2m+1)`: its class `i + j` modulo
`2m+1` below `2m - 1`, the class borrowing it for the reserved classes, and `2m - 1` for the
one reserved pair `{0, 2m}` that no class borrows. -/
def labO (i j : ℕ) : ℕ :=
  if i + j < 2 * m - 1 then i + j
  else if i + j = 2 * m - 1 then 2 * i
  else if i + j = 2 * m then (if j < 2 * m then 2 * j - 2 * m - 1 else 2 * m - 1)
  else i + j - (2 * m + 1)

/-- The pair `ctr r ± t` modulo `2m+1`. -/
private def chord (r t : ℕ) : Sym2 ℕ := s(wrap m (ctr m r + t), wrap m (ctr m r + (2 * m + 1) - t))

/-- Every pair `i < j < 2m+1` is a chord `ctr r ± t` with `0 < t ≤ m` of its class
`r ≡ i + j`. -/
private lemma chord_hit (i j r : ℕ) (hij : i < j) (hj : j < 2 * m + 1) (hr : r < 2 * m + 1)
    (hrij : r = i + j ∨ r + (2 * m + 1) = i + j) :
    ∃ t, 0 < t ∧ t < m + 1 ∧ chord m r t = s(i, j) := by
  have hu := ctr_spec m r hr
  unfold chord
  generalize ctr m r = u at hu ⊢
  by_cases hp : (j - i) % 2 = 0
  · refine ⟨(j - i) / 2, by omega, by omega, ?_⟩
    generalize ht : (j - i) / 2 = t
    unfold wrap
    split_ifs <;> simp only [Sym2.eq_iff] <;> omega
  · refine ⟨(2 * m + 1 - (j - i)) / 2, by omega, by omega, ?_⟩
    generalize ht : (2 * m + 1 - (j - i)) / 2 = t
    unfold wrap
    split_ifs <;> simp only [Sym2.eq_iff] <;> omega

/-- The `t`-th edge of class `r`: the borrowed edge for `t = 0` and the chord `ctr r ± t`
otherwise. -/
private def edgeO (r t : ℕ) : Sym2 ℕ :=
  if t = 0 then
    (if r % 2 = 0 then s(ctr m r, 2 * m - 1 - ctr m r) else s(ctr m r, 2 * m - ctr m r))
  else chord m r t

/-- The `t`-th edge of round-robin class `r` on `Fin (2m+2)`: the pair with the point `2m+1`
for `t = 0` and the chord `ctr r ± t` otherwise. -/
private def edgeE (r t : ℕ) : Sym2 ℕ :=
  if t = 0 then s(ctr m r, 2 * m + 1) else chord m r t

/-- Every class `r < 2m - 1` meets every point of `Fin (2m+1)`. -/
private lemma odd_cov (hm : 1 ≤ m) (x : Fin (2 * m + 1)) (r : ℕ) (hr : r < 2 * m - 1) :
    ∃ y : Fin (2 * m + 1), y ≠ x ∧ plab (2 * m + 1) (labO m) x y = r := by
  obtain ⟨x, hx⟩ := x
  by_cases hc : x = ctr m r
  · by_cases hr2 : r % 2 = 0
    · simp only [ctr, hr2, ↓reduceIte] at hc
      refine ⟨⟨2 * m - 1 - x, by omega⟩, ?_, ?_⟩
      · intro e; have := congrArg Fin.val e; simp only at this; omega
      · unfold plab labO; simp only; split_ifs <;> omega
    · simp only [ctr, hr2, ↓reduceIte] at hc
      refine ⟨⟨2 * m - x, by omega⟩, ?_, ?_⟩
      · intro e; have := congrArg Fin.val e; simp only at this; omega
      · unfold plab labO; simp only; split_ifs <;> omega
  · have hc' : ¬ (r % 2 = 0 ∧ x = r / 2) ∧ ¬ (r % 2 = 1 ∧ x = (r + 2 * m + 1) / 2) := by
      unfold ctr at hc; split_ifs at hc <;> omega
    by_cases hxr : x ≤ r
    · refine ⟨⟨r - x, by omega⟩, ?_, ?_⟩
      · intro e; have := congrArg Fin.val e; simp only at this; omega
      · unfold plab labO; simp only; split_ifs <;> omega
    · refine ⟨⟨r + 2 * m + 1 - x, by omega⟩, ?_, ?_⟩
      · intro e; have := congrArg Fin.val e; simp only at this; omega
      · unfold plab labO; simp only; split_ifs <;> omega

/-- Every pair with label below `2m - 1` is an edge `edgeO r t` of its class. -/
private lemma odd_hit (hm : 1 ≤ m) (c : ℕ) (hc : c ≤ 2 * m - 1) (x y : Fin (2 * m + 1))
    (hxy : x ≠ y) (hl : plab (2 * m + 1) (labO m) x y < c) :
    ∃ r < c, ∃ t < m + 1, edgeO m r t = s(x.1, y.1) := by
  have hne : x.1 ≠ y.1 := fun e => hxy (Fin.ext e)
  wlog hlt : x.1 < y.1 generalizing x y
  · obtain ⟨r, hr, t, ht, h⟩ :=
      this y x (Ne.symm hxy) ((plab_comm _ _ y x).trans_lt hl) (Ne.symm hne) (by omega)
    exact ⟨r, hr, t, ht, by rw [h, Sym2.eq_swap]⟩
  unfold plab at hl
  rw [min_eq_left hlt.le, max_eq_right hlt.le] at hl
  obtain ⟨i, hi⟩ := x
  obtain ⟨j, hj⟩ := y
  simp only at hl hlt hne ⊢
  refine ⟨labO m i j, hl, ?_⟩
  by_cases h1 : i + j < 2 * m - 1
  · have hr : labO m i j = i + j := by unfold labO; split_ifs; omega
    rw [hr]
    obtain ⟨t, ht0, htm, he⟩ := chord_hit m i j (i + j) hlt hj (by omega) (by omega)
    exact ⟨t, htm, by unfold edgeO; simp only [ht0.ne', ↓reduceIte]; exact he⟩
  by_cases h2 : i + j = 2 * m - 1
  · have hr : labO m i j = 2 * i := by unfold labO; split_ifs; omega
    rw [hr]
    refine ⟨0, by omega, ?_⟩
    unfold edgeO; simp only [↓reduceIte]
    unfold ctr; split_ifs <;> simp only [Sym2.eq_iff] <;> omega
  by_cases h3 : i + j = 2 * m
  · by_cases h4 : j < 2 * m
    · have hr : labO m i j = 2 * j - 2 * m - 1 := by unfold labO; split_ifs; omega
      rw [hr]
      refine ⟨0, by omega, ?_⟩
      unfold edgeO; simp only [↓reduceIte]
      unfold ctr; split_ifs <;> simp only [Sym2.eq_iff] <;> omega
    · have hr : labO m i j = 2 * m - 1 := by unfold labO; split_ifs; omega
      omega
  · have hr : labO m i j = i + j - (2 * m + 1) := by unfold labO; split_ifs; omega
    rw [hr]
    obtain ⟨t, ht0, htm, he⟩ :=
      chord_hit m i j (i + j - (2 * m + 1)) hlt hj (by omega) (by omega)
    exact ⟨t, htm, by unfold edgeO; simp only [ht0.ne', ↓reduceIte]; exact he⟩

/-- The round-robin class of a pair `i < j` of points of `Fin (2m+2)` without remainders. -/
private lemma cls_eq (i j : ℕ) (hij : i < j) (hj : j < 2 * m + 2) :
    cls m i j = if j = 2 * m + 1 then (if 2 * i < 2 * m + 1 then 2 * i else 2 * i - (2 * m + 1))
      else (if i + j < 2 * m + 1 then i + j else i + j - (2 * m + 1)) := by
  have hi : i ≠ 2 * m + 1 := by omega
  have red : ∀ v, v < 2 * (2 * m + 1) →
      v % (2 * m + 1) = if v < 2 * m + 1 then v else v - (2 * m + 1) := by
    intro v hv
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold cls
  simp only [hi, ↓reduceIte]
  split_ifs <;> rw [red _ (by omega)] <;> split_ifs <;> omega

/-- Every central pair of the round-robin band is an edge `edgeE r t` of its class. -/
private lemma even_hit (c : ℕ) (hc : c ≤ 2 * m + 1) (x y : Fin (2 * m + 2)) (hxy : x ≠ y)
    (hl : plab (2 * m + 2) (cls m) x y < c) :
    ∃ r < c, ∃ t < m + 1, edgeE m r t = s(x.1, y.1) := by
  have hne : x.1 ≠ y.1 := fun e => hxy (Fin.ext e)
  wlog hlt : x.1 < y.1 generalizing x y
  · obtain ⟨r, hr, t, ht, h⟩ :=
      this y x (Ne.symm hxy) ((plab_comm _ _ y x).trans_lt hl) (Ne.symm hne) (by omega)
    exact ⟨r, hr, t, ht, by rw [h, Sym2.eq_swap]⟩
  unfold plab at hl
  rw [min_eq_left hlt.le, max_eq_right hlt.le] at hl
  obtain ⟨i, hi⟩ := x
  obtain ⟨j, hj⟩ := y
  simp only at hl hlt hne ⊢
  refine ⟨cls m i j, hl, ?_⟩
  rw [cls_eq m i j hlt hj] at hl ⊢
  by_cases hb : j = 2 * m + 1
  · refine ⟨0, by omega, ?_⟩
    unfold edgeE; simp only [↓reduceIte]
    unfold ctr; split_ifs <;> simp only [Sym2.eq_iff] <;> omega
  · simp only [hb, ↓reduceIte] at hl ⊢
    generalize hR : (if i + j < 2 * m + 1 then i + j else i + j - (2 * m + 1)) = R at hl ⊢
    have hR' : R < 2 * m + 1 ∧ (R = i + j ∨ R + (2 * m + 1) = i + j) := by
      split_ifs at hR <;> omega
    obtain ⟨t, ht0, htm, he⟩ := chord_hit m i j R hlt (by omega) hR'.1 hR'.2
    exact ⟨t, htm, by unfold edgeE; simp only [ht0.ne', ↓reduceIte]; exact he⟩

/-- The feasible pairs of an order `n ≥ 1` and a center size `k`. -/
def Feasible (n k : ℕ) : Prop :=
  if n = 1 then k = 1 else if n = 2 then k = 2 else 1 ≤ k ∧ k ≤ n ∧ (Even n ∨ k < n)

/-- Every nonempty finite metric space has a feasible order and center size. -/
private lemma feasible_of (X : Type) [Fintype X] [MetricSpace X] (hX : 1 ≤ Fintype.card X) :
    Feasible (Fintype.card X) (Nat.card (center X)) := by
  obtain ⟨p⟩ : Nonempty X := Fintype.card_pos_iff.mp hX
  have hfin : (center X).Finite :=
    (Set.finite_range fun y => dist y p).subset (fun t ht => ht.2 p)
  have h0 : (0 : ℝ) ∈ center X := ⟨le_rfl, fun x => ⟨x, dist_self x⟩⟩
  have hpos : 1 ≤ Nat.card (center X) := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_pos hfin).mpr ⟨0, h0⟩
  obtain ⟨hle, hodd⟩ := center_card_bound X hX
  unfold Feasible
  split_ifs with h1 h2
  · omega
  · obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.mp (Nat.card_eq_fintype_card.trans h2)
    have hmem : ∀ q : X, q = a ∨ q = b := fun q => by
      have : q ∈ ({a, b} : Set X) := huniv ▸ Set.mem_univ q
      simpa using this
    have ht : dist a b ∈ center X := ⟨dist_nonneg, fun q => by
      rcases hmem q with rfl | rfl
      · exact ⟨b, dist_comm b q⟩
      · exact ⟨a, rfl⟩⟩
    have hab' : (0 : ℝ) ≠ dist a b := (dist_pos.mpr hab).ne
    have h2le : 2 ≤ Nat.card (center X) := by
      rw [Nat.card_coe_set_eq, ← Set.ncard_pair hab']
      exact Set.ncard_le_ncard (Set.insert_subset h0 (Set.singleton_subset_iff.mpr ht)) hfin
    omega
  · refine ⟨hpos, hle, ?_⟩
    rcases Nat.even_or_odd (Fintype.card X) with h | h
    · exact Or.inl h
    · exact Or.inr (hodd h (by omega))

open Classical in
/-- Every feasible pair is realized with at most `(k - 1) ⌈n / 2⌉` central edges. -/
private lemma attain (n k : ℕ) (hn : 1 ≤ n) (hf : Feasible n k) :
    ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X), Fintype.card X = n ∧
      Nat.card (center X) = k ∧ (centralGraph X).edgeFinset.card ≤ (k - 1) * ((n + 1) / 2) := by
  unfold Feasible at hf
  rcases Nat.even_or_odd' n with ⟨m', rfl | rfl⟩
  · -- even order `2m + 2`
    obtain ⟨m, rfl⟩ : ∃ m, m' = m + 1 := ⟨m' - 1, by omega⟩
    have hk : 1 ≤ k ∧ k ≤ 2 * m + 2 ∧ (m = 0 → k = 2) := by
      split_ifs at hf with h1 h2 <;> omega
    have hcov : ∀ x : Fin (2 * m + 2), ∀ r < k - 1, ∃ y : Fin (2 * m + 2), y ≠ x ∧
        plab (2 * m + 2) (cls m) x y = r := fun x r hr => space_cov m x r (by omega)
    have h3 : ∀ x y : Fin (2 * m + 2), x ≠ y → k - 1 ≤ plab (2 * m + 2) (cls m) x y →
        ∃ z : Fin (2 * m + 2), z ≠ x ∧ z ≠ y := fun x y _ hc => by
      have := cls_lt m (min x.1 y.1) (max x.1 y.1)
      exact third_point _ (by unfold plab at hc; omega) x y
    refine ⟨Band (2 * m + 2) (k - 1) (cls m), inferInstance, inferInstance,
      (band_card _ _ _).trans (by ring), ?_, ?_⟩
    · rw [band_center_card _ _ _ (by omega) hcov h3]; omega
    · have := band_edges _ _ _ (by omega) hcov h3 (m + 1) (edgeE m)
        (fun x y hxy hl => even_hit m (k - 1) (by omega) x y hxy hl)
      rwa [show (2 * (m + 1) + 1) / 2 = m + 1 by omega]
  · -- odd order `2m + 1`
    by_cases h0 : m' = 0
    · subst h0
      have hk : k = 1 := by simpa using hf
      subst hk
      have h3 : ∀ x y : Fin 1, x ≠ y → 0 ≤ plab 1 (labO 0) x y →
          ∃ z : Fin 1, z ≠ x ∧ z ≠ y := fun x y hxy _ => absurd (Subsingleton.elim x y) hxy
      refine ⟨Band 1 0 (labO 0), inferInstance, inferInstance, band_card _ _ _,
        band_center_card _ _ _ (by omega) (fun _ r hr => absurd hr (by omega)) h3, ?_⟩
      have := band_edges 1 0 (labO 0) (by omega) (fun _ r hr => absurd hr (by omega)) h3 1
        (edgeO 0) (fun _ _ _ hl => absurd hl (by omega))
      simpa using this
    · have hm : 1 ≤ m' := by omega
      have hk : 1 ≤ k ∧ k ≤ 2 * m' := by
        split_ifs at hf with h1 h2
        · omega
        · omega
        · obtain ⟨hk1, hkn, hev | hlt⟩ := hf
          · exact absurd hev (by rw [Nat.not_even_iff_odd]; exact ⟨m', rfl⟩)
          · omega
      have hcov : ∀ x : Fin (2 * m' + 1), ∀ r < k - 1, ∃ y : Fin (2 * m' + 1), y ≠ x ∧
          plab (2 * m' + 1) (labO m') x y = r := fun x r hr => odd_cov m' hm x r (by omega)
      have h3 : ∀ x y : Fin (2 * m' + 1), x ≠ y → k - 1 ≤ plab (2 * m' + 1) (labO m') x y →
          ∃ z : Fin (2 * m' + 1), z ≠ x ∧ z ≠ y := fun x y _ _ => third_point _ (by omega) x y
      refine ⟨Band (2 * m' + 1) (k - 1) (labO m'), inferInstance, inferInstance,
        band_card _ _ _, ?_, ?_⟩
      · rw [band_center_card _ _ _ (by omega) hcov h3]; omega
      · have := band_edges _ _ _ (by omega) hcov h3 (m' + 1) (edgeO m')
          (fun x y hxy hl => odd_hit m' hm (k - 1) (by omega) x y hxy hl)
        rwa [show (2 * m' + 1 + 1) / 2 = m' + 1 by omega]

open Classical in
/-- For `n ≥ 1`, an `n`-point metric space with exactly `k` central values exists if and only
if `(n, k)` is feasible: `k = 1` for `n = 1`, `k = 2` for `n = 2`, and for `n ≥ 3` the range
`1 ≤ k ≤ n` when `n` is even and `1 ≤ k ≤ n - 1` when `n` is odd. For every feasible pair the
least number of central edges is `(k - 1) ⌈n / 2⌉`. -/
theorem all_center_sizes (n k : ℕ) (hn : 1 ≤ n) :
    ((∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X),
        Fintype.card X = n ∧ Nat.card (center X) = k) ↔ Feasible n k) ∧
    (Feasible n k → IsLeast {e : ℕ | ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X),
        Fintype.card X = n ∧ Nat.card (center X) = k ∧ (centralGraph X).edgeFinset.card = e}
      ((k - 1) * ((n + 1) / 2))) := by
  refine ⟨⟨?_, fun hf => ?_⟩, fun hf => ⟨?_, ?_⟩⟩
  · rintro ⟨X, _, _, rfl, rfl⟩
    exact feasible_of X hn
  · obtain ⟨X, hF, hM, hX, hk, -⟩ := attain n k hn hf
    exact ⟨X, hF, hM, hX, hk⟩
  · obtain ⟨X, hF, hM, hX, hk, he⟩ := attain n k hn hf
    refine ⟨X, hF, hM, hX, hk, le_antisymm he ?_⟩
    have := edge_cover_bound X
    rwa [hk, hX] at this
  · rintro e ⟨X, _, _, rfl, rfl, rfl⟩
    exact edge_cover_bound X

end

end D5.S3.Combinatorics.Geometry.CentralSizeEdgeMinima
