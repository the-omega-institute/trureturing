/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisInputClauses
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisInputClauses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The input clauses express the local cubic, signed, and contact laws in the signed occupancy valuation. The replay matches each reconstructed proposition to its actual clause. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisRepresentative
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFourLeafSigns
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisThreeLeafInputs

/-! Translate the rooted signed geometry into the corresponding SAT rows. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisInputClauses

open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open Q9IsotropicHuang (parity)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9FiveAxisOrbitCover (otherAxes satisfies_of_falsified)
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private upperRow lowerRow parityRow from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF
open private signValue from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisValuation
open Q9SharedContactCNF (Word Axis Variable pos neg)
open Q9TightDistanceTwoCNF (support)
open Q9FiveAxisValuation (valuation occupancy_value sign_value polarity_value signIndex polarityIndex)
open Q9FiveAxisSignedRows (Signing polarity_iff edge_sign_iff opposite_neighbor)
open Q9FiveAxisOrbitGeometry (family MidpointCounts ContactTranslations)
open Q9FiveAxisLayerAction (LayerMatches)
open Q9FiveAxisMissingContact (Geometry)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9FiveAxisSignedNormalization (rupFlipSign)
open Q9FiveAxisContactWitnesses (witnessIndex)
open Q9FiveAxisFourLeafSigns (coherent_exterior_four_leaves)
open Q9FiveAxisThreeLeafInputs (coherent_exterior_triples)
open private switching_of_rup_signing from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFourLeafSigns
open private minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
open private axis axis_injective active_iff mask_subset shared_directions cube_root_zero cube_root_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitGeometry
open private axesOf xor_mask literalIndex from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private masks witness_value from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisContactWitnesses
open private evenWord from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskClauses
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private step step_cube from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedRows

private abbrev occ := Variable.occupied

private def lit (p : Bool) (n : ℕ) : Sat.Literal := if p then .pos n else .neg n

private def coefficient (w : Word) (i : Fin 9) : Bool := decide (rupFlipSign i (cubeBitVec 9 w) = 1)

open Classical in
structure Inputs (C D : Finset (Q 9)) (f : Bool → Q 9 → ℤ)
    (r : Q9FiveAxisOrbitCover.Pattern) : Prop where
  geom : Geometry C D
  masks : minimumDisplacements C D false 2 = family
  layer : LayerMatches C D r
  counts : MidpointCounts C D
  translates : ContactTranslations C D
  regular : ∀ s, ((hypercube 9).induce (support C D s : Set (Q 9))).IsRegularOfDegree 3
  signing : ∀ s, Signing (support C D s) (f s)

private theorem literal_index_small {C D : Finset (Q 9)} {f : Bool → Q 9 → ℤ}
    {c : Sat.Clause} (h : (Q9TightDistanceTwoCNF.valuation (support C D)).satisfies c)
    (hn : List.all c (fun l => decide (literalIndex l < 9216)) = true) :
    (valuation C D f).satisfies c := by
  change List Sat.Literal at c
  induction c with
  | nil => exact h
  | cons x xs ih =>
    rw [List.all_cons, Bool.and_eq_true] at hn
    intro hx
    refine ih (h ?_) hn.2
    have hs := of_decide_eq_true hn.1
    cases x with
    | pos n =>
      change n < 9216 at hs
      simpa only [Sat.Valuation.neg, valuation, ite_eq_left hs] using hx
    | neg n =>
      change n < 9216 at hs
      simpa only [Sat.Valuation.neg, valuation, ite_eq_left hs] using hx

theorem root_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r) (s : Bool) :
    (valuation C D f).satisfies [pos (occ s (if s then 3 else 0))] := by
  intro hn
  apply hn
  rw [occupancy_value]
  cases s
  · change cubeBitVec 9 (0 : Word) ∈ C
    rw [cube_root_zero]
    exact h.geom.left_root
  · change cubeBitVec 9 (3 : Word) ∈ D
    rw [cube_root_three]
    exact h.geom.right_root

theorem close_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r) (x y : Word)
    (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) ≤ 1) :
    (valuation C D f).satisfies [neg (occ false x), neg (occ true y)] := by
  intro hx hy
  have hs := h.geom.separated _ ((occupancy_value C D f false x).mp hx)
    _ ((occupancy_value C D f true y).mp hy)
  omega

theorem forbidden_mask_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r) (x y : Word)
    (hp : parity (cubeBitVec 9 x) = false)
    (hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 2)
    (hm : axesOf (x ^^^ y) ∉ family) :
    (valuation C D f).satisfies [neg (occ false x), neg (occ true y)] := by
  intro hx hy
  apply hm
  rw [← xor_mask, ← h.masks]
  exact mem_minimumDisplacements.mpr
    ⟨_, (occupancy_value C D f false x).mp hx, _, (occupancy_value C D f true y).mp hy, hp, hd, rfl⟩

private theorem witness_at (C D : Finset (Q 9)) (f : Bool → Q 9 → ℤ)
    (m : Fin 8) (i : Fin 256) :
    valuation C D f (witnessIndex m i) ↔
      cubeBitVec 9 (evenWord i) ∈ C ∧ cubeBitVec 9 (evenWord i ^^^ masks m) ∈ D := by
  have hm := m.isLt
  have hi := i.isLt
  have hlo : 10240 ≤ witnessIndex m i := by unfold witnessIndex; omega
  have hhi : witnessIndex m i < 12288 := by unfold witnessIndex; omega
  rw [valuation, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hhi]
  exact witness_value C D _ m i

theorem witness_clause {C D : Finset (Q 9)} {f : Bool → Q 9 → ℤ}
    (m : Fin 8) (i : Fin 256) (s : Bool) :
    (valuation C D f).satisfies [.neg (witnessIndex m i),
      pos (occ s (if s then evenWord i ^^^ masks m else evenWord i))] := by
  intro hv hn
  have hw := (witness_at C D f m i).mp hv
  apply hn
  rw [occupancy_value]
  cases s
  · exact hw.1
  · exact hw.2

theorem realized_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r) (m : Fin 8) :
    (valuation C D f).satisfies ((List.finRange 256).map fun i => Sat.Literal.pos (witnessIndex m i)) := by
  have hh := Q9FiveAxisContactWitnesses.realized_clause (other := fun _ => False) h.masks m
  have he : ∀ i : Fin 256, valuation C D f (witnessIndex m i) ↔
      Q9FiveAxisContactWitnesses.installWitnesses C D (fun _ => False) (witnessIndex m i) :=
    fun i => (witness_at C D f m i).trans (witness_value C D _ m i).symm
  generalize List.finRange 256 = ids at hh ⊢
  induction ids with
  | nil => exact hh
  | cons i ids ih =>
    intro hno
    exact ih (hh (fun hyes => hno ((he i).mpr hyes)))

theorem orbit_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (hw : w ∈ Q9FiveAxisOrbitCover.evenWords) (p : Bool)
    (hp : (w ∈ r.on s) ↔ p = true) :
    (valuation C D f).satisfies [lit p (occ s w).index] := by
  have hv := (occupancy_value C D f s w).trans ((h.layer s w hw).trans hp)
  cases p
  · intro htrue
    exact Bool.false_ne_true (hv.mp htrue)
  · intro hfalse
    exact hfalse (hv.mpr rfl)

theorem translated_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (w : Word) (i j p q : Q9FiveAxisOrbitCover.Axis) (s : Bool)
    (hp : parity (cubeBitVec 9 w) = false) (hi : i = 1 ∨ i = 2)
    (htriple : ({j, p, q} : Finset Q9FiveAxisOrbitCover.Axis) = {0, 3, 4}) :
    let x := step (step w (axis i)) (axis j)
    (valuation C D f).satisfies [neg (occ false w), neg (occ true x),
      pos (occ s (step (step (if s then x else w) (axis p)) (axis q)))] := by
  dsimp only
  intro hx hy hn
  have hu := (occupancy_value C D f false w).mp hx
  have hv := (occupancy_value C D f true _).mp hy
  simp only [step_cube] at hv
  obtain ⟨hC, hD⟩ := h.translates _ i j p q hp hi htriple hu hv
  apply hn
  rw [occupancy_value]
  cases s
  · simpa only [step_cube, support, Bool.false_eq_true, ite_false] using hC
  · simpa only [step_cube, support, ite_true] using hD

private theorem local_rules {C D : Finset (Q 9)} (h : Geometry C D) (s : Bool) :
    Q9SharedContactNormalized.LocalRules (support C D s) := by
  cases s
  · exact h.left_rules
  · exact h.right_rules

theorem degree_upper_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (L : List Axis) (hd : L.toFinset.card = 4)
    (hn : List.all (upperRow s w L) (fun l => decide (literalIndex l < 9216)) = true) :
    (valuation C D f).satisfies (upperRow s w L) :=
  literal_index_small (Q9TightDistanceTwoCNF.upperClause s (local_rules h.geom s) w L hd) hn

theorem degree_lower_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (L : List Axis) (hd : L.toFinset.card = 7)
    (hn : List.all (lowerRow s w L) (fun l => decide (literalIndex l < 9216)) = true) :
    (valuation C D f).satisfies (lowerRow s w L) :=
  literal_index_small (Q9TightDistanceTwoCNF.lowerClause s (local_rules h.geom s) w L hd) hn

theorem degree_parity_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (i : Fin 8) (sg : Fin 4)
    (hn : List.all (parityRow s w i sg) (fun l => decide (literalIndex l < 9216)) = true) :
    (valuation C D f).satisfies (parityRow s w i sg) :=
  literal_index_small (Q9TightDistanceTwoCNF.parityClause s (local_rules h.geom s) w i sg) hn

theorem edge_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (i : Axis) (v : Bool) :
    let y := step w i
    (valuation C D f).satisfies [neg (occ s w), neg (occ s y),
      lit (!v) (signIndex s w), lit (v == coefficient w i) (signIndex s y)] := by
  dsimp only
  intro hx hy hfirst hsecond
  have hsign := edge_sign_iff s w i (h.signing s) hx hy
  change False
  cases v <;> cases hc : coefficient w i <;>
    simp [lit, hc, Sat.Valuation.neg] at hfirst hsecond <;>
    simp [coefficient] at hc <;> tauto

theorem polarity_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (p : Bool) (v : Fin 3) :
    (valuation C D f).satisfies
      (if v = 0 then [.neg (polarityIndex s w p), pos (occ s w)]
       else if v = 1 then [.neg (polarityIndex s w p), lit p (signIndex s w)]
       else [neg (occ s w), lit (!p) (signIndex s w), .pos (polarityIndex s w p)]) := by
  have hv := polarity_iff s w p (h.signing s)
  fin_cases v <;> cases p <;> simp [lit, Sat.Valuation.satisfies, Sat.Valuation.neg] at * <;> tauto

private theorem polarity_contribution {C D : Finset (Q 9)} {f : Bool → Q 9 → ℤ}
    (s : Bool) (w : Word) (i : Axis) (p : Bool) :
    valuation C D f (polarityIndex s (step w i) (p == coefficient w i)) ↔
      rupFlipSign i (cubeBitVec 9 w) * f s (cubeBitVec 9 (step w i)) = (if p then 1 else -1) := by
  have hs : rupFlipSign i (cubeBitVec 9 w) = 1 ∨ rupFlipSign i (cubeBitVec 9 w) = -1 :=
    neg_one_pow_eq_or ℤ _
  rw [polarity_value]
  rcases hs with hs | hs <;> cases p <;> simp [coefficient, hs, signValue] <;> omega

theorem opposite_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (i : Axis) (p : Bool) :
    (valuation C D f).satisfies
      (pos (occ s w) :: .neg (polarityIndex s (step w i) (p == coefficient w i)) ::
        (List.finRange 9).map fun j =>
          .pos (polarityIndex s (step w j) ((!p) == coefficient w j))) := by
  intro hout hterm
  have hsign := (polarity_contribution s w i p).mp hterm
  obtain ⟨j, hj⟩ := opposite_neighbor s w i _ (h.signing s)
    (by cases p <;> simp) hout hsign
  apply satisfies_of_falsified
  intro hneg
  have hAt : ¬ valuation C D f (polarityIndex s (step w j) ((!p) == coefficient w j)) :=
    hneg (.pos _) (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  exact hAt ((polarity_contribution s w j (!p)).mpr (by cases p <;> simpa using hj))

private theorem shared_at {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (j i : Q9FiveAxisOrbitCover.Axis)
    (hp : parity (cubeBitVec 9 w) = true)
    (hj : valuation C D f (occ (!s) (step w (axis j))).index)
    (hi : valuation C D f (occ s (step w (axis i))).index) :
    (directions (support C D s) (cubeBitVec 9 w)).card = 2 ∧
    directions (support C D s) (cubeBitVec 9 w) ⊆ Q9FiveAxisMissingContact.firstFiveAxes := by
  have hi' := (occupancy_value C D f s _).mp hi
  have hj' := (occupancy_value C D f (!s) _).mp hj
  simp only [step_cube] at hi' hj'
  have par (k : Q9FiveAxisOrbitCover.Axis) : parity (flip (cubeBitVec 9 w) (axis k)) = false := by
    rw [parity_flip, hp]
    rfl
  cases s
  · exact (shared_directions h.geom h.masks h.counts hi' hj' (par i)).1
  · exact (shared_directions h.geom h.masks h.counts hj' hi' (par j)).2

theorem midpoint_lower_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (j i : Q9FiveAxisOrbitCover.Axis)
    (hp : parity (cubeBitVec 9 w) = true) :
    (valuation C D f).satisfies (neg (occ (!s) (step w (axis j))) ::
        neg (occ s (step w (axis i))) ::
        (otherAxes i).map (fun k => pos (occ s (step w (axis k))))) := by
  intro hj hi
  obtain ⟨hc, hs⟩ := shared_at h s w j i hp hj hi
  obtain ⟨k, hk, hki⟩ := exists_mem_ne (by rw [hc]; decide) (axis i)
  let l : Q9FiveAxisOrbitCover.Axis := ⟨k.val, (active_iff k).mp (hs hk)⟩
  have hl : axis l = k := Fin.ext rfl
  have hli : l ≠ i := fun he => hki (hl.symm.trans (congrArg axis he))
  have hlmem : l ∈ otherAxes i := by
    have hall : ∀ t : Q9FiveAxisOrbitCover.Axis, t ∈ ([0, 1, 2, 3, 4] : List Q9FiveAxisOrbitCover.Axis) := by decide
    simp [otherAxes, hall, hli]
  apply satisfies_of_falsified
  intro hneg
  have hAt := hneg _ (List.mem_map.mpr ⟨l, hlmem, rfl⟩)
  apply hAt
  apply (occupancy_value C D f s _).mpr
  rw [step_cube, hl]
  exact (mem_directions _ _ _).mp hk

theorem midpoint_upper_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (j a b c : Q9FiveAxisOrbitCover.Axis)
    (hp : parity (cubeBitVec 9 w) = true)
    (hab : a < b) (hbc : b < c) :
    (valuation C D f).satisfies [neg (occ (!s) (step w (axis j))),
      neg (occ s (step w (axis a))), neg (occ s (step w (axis b))),
      neg (occ s (step w (axis c)))] := by
  intro hj ha hb hc
  have hcard := (shared_at h s w j a hp hj ha).1
  have here (k : Q9FiveAxisOrbitCover.Axis)
      (hk : valuation C D f (occ s (step w (axis k))).index) :
      axis k ∈ directions (support C D s) (cubeBitVec 9 w) := by
    rw [mem_directions, ← step_cube]
    exact (occupancy_value C D f s _).mp hk
  have hsub : ({axis a, axis b, axis c} : Finset (Fin 9)) ⊆
      directions (support C D s) (cubeBitVec 9 w) := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨here a ha, here b hb, here c hc⟩
  have hab' : axis a ≠ axis b := fun he => hab.ne (axis_injective he)
  have hac' : axis a ≠ axis c := fun he => (hab.trans hbc).ne (axis_injective he)
  have hbc' : axis b ≠ axis c := fun he => hbc.ne (axis_injective he)
  have hthree : ({axis a, axis b, axis c} : Finset (Fin 9)).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab', hac']), card_pair hbc']
  have hle := card_le_card hsub
  change False
  omega

private theorem balanced_at {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r) (s : Bool) :
    IsBalanced (support C D s) :=
  ⟨_, switching_of_rup_signing (h.signing s).units (h.signing s).edge⟩

private theorem separated_at {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r) (s : Bool) :
    ∀ x ∈ support C D s, ∀ y ∈ support C D (!s), 2 ≤ hammingDist x y := by
  cases s
  · exact h.geom.separated
  · intro x hx y hy
    rw [hammingDist_comm]
    exact h.geom.separated y hy x hx

private theorem masks_at {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r) (s : Bool) :
    ∀ T ∈ minimumDisplacements (support C D s) (support C D (!s)) false 2,
      T ⊆ Q9FiveAxisMissingContact.firstFiveAxes := by
  have he : minimumDisplacements (support C D s) (support C D (!s)) false 2 = family := by
    cases s
    · exact h.masks
    · exact (minimumDisplacements_swap_two C D false).symm.trans h.masks
  rw [he]
  exact fun _ => mask_subset

private def threeAxes : List Axis := [0, 3, 4]

private def fourAxes (low : Axis) : List Axis := [0, low, 3, 4]

private def starMask (low : Axis) : Word := step (25 : Word) low

private def signedStar (s : Bool) (w : Word) (L : List Axis) (shift : Word) : List Sat.Literal :=
  L.map (fun i => neg (occ s (step w i))) ++
    L.map (fun i => neg (occ (!s) (step w i ^^^ shift)))

theorem three_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (low : Axis) (L : List Axis)
    (hlow : low = 1 ∨ low = 2)
    (hp : parity (cubeBitVec 9 w) = true) (hL : L.toFinset.card = 4) :
    (valuation C D f).satisfies
      (threeAxes.map (fun i => neg (occ s (step w i))) ++ [pos (occ s w)] ++
        threeAxes.map (fun i => neg (occ (!s) (step w i ^^^ starMask low))) ++
        L.map (fun i => pos (occ s (step w i)))) := by
  apply satisfies_of_falsified
  intro hn
  have here (a : Axis) (ha : a ∈ threeAxes) : cubeBitVec 9 (step w a) ∈ support C D s :=
    (occupancy_value C D f s _).mp (hn (neg (occ s (step w a)))
      (by exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)))))
  have there (a : Axis) (ha : a ∈ threeAxes) :
      cubeBitVec 9 (step w a ^^^ starMask low) ∈ support C D (!s) :=
    (occupancy_value C D f (!s) _).mp (hn (neg (occ (!s) (step w a ^^^ starMask low)))
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩))))
  have h₁ : ∀ i ∈ Q9FiveAxisThreeLeafInputs.partners, cubeBitVec 9 (step w i) ∈ support C D s := by
    intro i hi
    exact here i (by simpa [Q9FiveAxisThreeLeafInputs.partners, threeAxes] using hi)
  have h₂ : ∀ i ∈ Q9FiveAxisThreeLeafInputs.partners,
      cubeBitVec 9 (step w i ^^^ starMask low) ∈ support C D (!s) := by
    intro i hi
    exact there i (by simpa [Q9FiveAxisThreeLeafInputs.partners, threeAxes] using hi)
  obtain hmem | hdeg := coherent_exterior_triples hlow (by decide) (masks_at h s)
    (separated_at h s) (h.regular s) (h.regular (!s)) (balanced_at h s) (balanced_at h (!s)) hp h₁ h₂
  · exact hn (pos (occ s w)) (by simp) ((occupancy_value C D f s w).mpr hmem)
  · obtain ⟨a, ha, hw⟩ := hdeg L.toFinset hL
    exact hn (pos (occ s (step w a))) (List.mem_append_right _ (List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha, rfl⟩))
      ((occupancy_value C D f s _).mpr hw)

private theorem four_data {C D : Finset (Q 9)} {f} {r} {s : Bool} {w : Word} {low : Axis}
    (h : Inputs C D f r) (hlow : low = 1 ∨ low = 2) (hp : parity (cubeBitVec 9 w) = true)
    (hn : ∀ l ∈ signedStar s w (fourAxes low) (starMask low), (valuation C D f).neg l) :
    (∀ a b : Axis, a ≠ b →
        cubeBitVec 9 (step w a) ∈ support C D s ∨ cubeBitVec 9 (step w b) ∈ support C D s) ∧
      (∀ a : Axis, a ∉ Q9FiveAxisFourLeafSigns.star low →
        cubeBitVec 9 (step w a) ∈ support C D s →
        rupFlipSign a (cubeBitVec 9 w) * f s (cubeBitVec 9 (step w a)) = -f s (cubeBitVec 9 (step w 0))) := by
  have mask : starMask low = Q9FiveAxisFourLeafSigns.starMask low := by
    rcases hlow with h | h <;> rw [h] <;> decide
  have here (a : Axis) (ha : a ∈ Q9FiveAxisFourLeafSigns.star low) :
      cubeBitVec 9 (step w a) ∈ support C D s := by
    have ha' : a ∈ fourAxes low := by simpa [Q9FiveAxisFourLeafSigns.star, fourAxes] using ha
    exact (occupancy_value C D f s _).mp (hn (neg (occ s (step w a)))
      (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha', rfl⟩)))
  have there (a : Axis) (ha : a ∈ Q9FiveAxisFourLeafSigns.star low) :
      cubeBitVec 9 (step w a ^^^ Q9FiveAxisFourLeafSigns.starMask low) ∈ support C D (!s) := by
    have ha' : a ∈ fourAxes low := by simpa [Q9FiveAxisFourLeafSigns.star, fourAxes] using ha
    rw [← mask]
    exact (occupancy_value C D f (!s) _).mp (hn (neg (occ (!s) (step w a ^^^ starMask low)))
      (List.mem_append_right _ (List.mem_map.mpr ⟨a, ha', rfl⟩)))
  exact (coherent_exterior_four_leaves hlow (by decide) (masks_at h s) (separated_at h s)
    (h.regular s) (h.regular (!s)) (balanced_at h (!s)) (h.signing s).units
    (h.signing s).edge hp here there).2.2

theorem four_occupancy_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (low a b : Axis)
    (hlow : low = 1 ∨ low = 2) (hp : parity (cubeBitVec 9 w) = true) (hab : a ≠ b) :
    (valuation C D f).satisfies
      (signedStar s w (fourAxes low) (starMask low) ++
        [pos (occ s (step w a)), pos (occ s (step w b))]) := by
  apply satisfies_of_falsified
  intro hn
  obtain ha | hb := (four_data h hlow hp (fun l hl => hn l (List.mem_append_left _ hl))).1 a b hab
  · exact hn (pos (occ s (step w a))) (by simp) ((occupancy_value C D f s _).mpr ha)
  · exact hn (pos (occ s (step w b))) (by simp) ((occupancy_value C D f s _).mpr hb)

theorem four_sign_clause {C D : Finset (Q 9)} {f} {r} (h : Inputs C D f r)
    (s : Bool) (w : Word) (low a : Axis) (p : Bool)
    (hlow : low = 1 ∨ low = 2) (hp : parity (cubeBitVec 9 w) = true)
    (ha : a ∉ Q9FiveAxisFourLeafSigns.star low) :
    (valuation C D f).satisfies
      (signedStar s w (fourAxes low) (starMask low) ++
        [neg (occ s (step w a)), lit p (signIndex s (step w 0)),
         lit (p == coefficient w a) (signIndex s (step w a))]) := by
  apply satisfies_of_falsified
  intro hn
  have hout : cubeBitVec 9 (step w a) ∈ support C D s :=
    (occupancy_value C D f s _).mp (hn (neg (occ s (step w a))) (by simp))
  have hbridge := (four_data h hlow hp (fun l hl => hn l (List.mem_append_left _ hl))).2 a ha hout
  have hpivot : cubeBitVec 9 (step w 0) ∈ support C D s :=
    (occupancy_value C D f s _).mp (hn (neg (occ s (step w 0))) (by simp [signedStar, fourAxes]))
  have h₀ := (h.signing s).units _ hpivot
  have hₐ := (h.signing s).units _ hout
  have hn₀ := hn (lit p (signIndex s (step w 0))) (by simp)
  have hnₐ := hn (lit (p == coefficient w a) (signIndex s (step w a))) (by simp)
  have hc : rupFlipSign a (cubeBitVec 9 w) = 1 ∨ rupFlipSign a (cubeBitVec 9 w) = -1 :=
    neg_one_pow_eq_or ℤ _
  rcases hc with hc | hc <;> cases p <;>
    rcases h₀ with h0 | h0 <;> rcases hₐ with h1 | h1 <;>
    simp [lit, coefficient, Sat.Valuation.neg, sign_value, hc, h0, h1] at hn₀ hnₐ hbridge

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisInputClauses
