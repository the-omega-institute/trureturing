/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SquareMaskGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Forced squares constrain the number and shape of distance-two contact masks. -/

import D5.S3.Combinatorics.CubicSquareCompletion
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeThreeContactOrbit

/-! The four-cycle restriction on the actual distance-two Q9 mask graph. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open Q9IsotropicHuang (parity weightedLinear)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9MinimumDistanceOperator (minimumDisplacements RidgeContact)
open Q9DegreeThreeContactOrbit (three_partner_contact_completes_square)
open private axes extensions mem_axes mem_extensions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
open private extensions_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9EightMaskGraph
open private mem_minimumDisplacements minimum_displacements_three_extensions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_right_inj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)

/-- The vertices are exactly the coordinates occurring in the mask family. -/
abbrev activeAxes (F : Finset (Finset (Fin 9))) : Finset (Fin 9) := axes F

/-- An edge joins two distinct active coordinates whose pair is a mask. -/
def maskGraph (F : Finset (Finset (Fin 9))) : SimpleGraph (activeAxes F) where
  Adj a b := a ≠ b ∧ ({a.val, b.val} : Finset (Fin 9)) ∈ F
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, by simpa only [Finset.pair_comm a.val b.val] using h.2⟩⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩

instance (F : Finset (Finset (Fin 9))) : DecidableRel (maskGraph F).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ ({a.val, b.val} : Finset (Fin 9)) ∈ F))

private theorem pair_ne {F : Finset (Finset (Fin 9))}
    (hsize : ∀ T ∈ F, T.card = 2) {i j : Fin 9}
    (hm : ({i, j} : Finset (Fin 9)) ∈ F) : i ≠ j := by
  intro he
  subst j
  simpa using hsize _ hm

private theorem mem_partners {F : Finset (Finset (Fin 9))}
    (hsize : ∀ T ∈ F, T.card = 2) {i j : Fin 9} :
    j ∈ extensions F {i} ↔ ({i, j} : Finset (Fin 9)) ∈ F := by
  rw [mem_extensions, Finset.pair_comm j i, mem_singleton]
  exact ⟨And.right, fun hm => ⟨(pair_ne hsize hm).symm, hm⟩⟩

/-- The existing singleton-ridge extension count is the graph degree. -/
theorem degree_eq_extensions (F : Finset (Finset (Fin 9)))
    (hsize : ∀ T ∈ F, T.card = 2) (a : activeAxes F) :
    (maskGraph F).degree a = (extensions F {a.val}).card := by
  let e : activeAxes F ↪ Fin 9 := ⟨Subtype.val, Subtype.val_injective⟩
  have he : ((maskGraph F).neighborFinset a).map e = extensions F {a.val} := by
    ext k
    rw [mem_map, mem_partners hsize]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ((maskGraph F).mem_neighborFinset _ _ |>.mp hv).2
    · intro hm
      let v : activeAxes F := ⟨k, mem_axes.mpr ⟨_, hm, by simp⟩⟩
      have hne : a ≠ v := fun h => pair_ne hsize hm (congrArg Subtype.val h)
      exact ⟨v, (maskGraph F).mem_neighborFinset _ _ |>.mpr ⟨hne, hm⟩, rfl⟩
  rw [← he, card_map, SimpleGraph.card_neighborFinset_eq_degree]

/-- Every used mask corresponds to exactly one unordered graph edge. -/
theorem card_edges (F : Finset (Finset (Fin 9)))
    (hsize : ∀ T ∈ F, T.card = 2) : (maskGraph F).edgeFinset.card = F.card := by
  let toMask : Sym2 (activeAxes F) → Finset (Fin 9) :=
    fun e => (Sym2.map Subtype.val e).toFinset
  have hinj : Function.Injective toMask := by
    intro e f h
    apply Sym2.map.injective Subtype.val_injective
    apply Sym2.ext
    intro k
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset]
    exact Iff.of_eq (congrArg (fun T : Finset (Fin 9) => k ∈ T) h)
  have he : (maskGraph F).edgeFinset.image toMask = F := by
    ext T
    rw [mem_image]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨a, b⟩ := e
      have hab : (maskGraph F).Adj a b := SimpleGraph.mem_edgeFinset.mp he
      simpa only [toMask, Sym2.map_mk, Sym2.toFinset_mk_eq] using hab.2
    · intro hT
      obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp (hsize T hT)
      let a : activeAxes F := ⟨i, mem_axes.mpr ⟨_, hT, by simp⟩⟩
      let b : activeAxes F := ⟨j, mem_axes.mpr ⟨_, hT, by simp⟩⟩
      have hab : (maskGraph F).Adj a b := ⟨fun h => hij (congrArg Subtype.val h), hT⟩
      refine ⟨Sym2.mk a b, SimpleGraph.mem_edgeFinset.mpr hab, ?_⟩
      simp [toMask, Sym2.toFinset_mk_eq, a, b]
  calc
    _ = ((maskGraph F).edgeFinset.image toMask).card := (card_image_of_injective _ hinj).symm
    _ = F.card := congrArg Finset.card he

open Classical in
/-- Separation and universal singularity force minimum degree three and the
four-cycle completion law at each edge joining two degree-three vertices. -/
theorem distance_two_mask_graph_constraints
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    let F := minimumDisplacements C D b 2
    let G := maskGraph F
    (∀ a, 3 ≤ G.degree a) ∧
      (∀ {a v c}, G.Adj a v → G.Adj a c → v ≠ c →
        G.degree a = 3 → G.degree v = 3 →
        ∃ d, d ≠ a ∧ G.Adj v d ∧ G.Adj c d) := by
  let F := minimumDisplacements C D b 2
  let G := maskGraph F
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨x, _, y, _, _, hd, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hd
  have hC (i : Fin 9) : ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0) := by
    let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
    have hw (k : Fin 9) : 0 < w k := by
      dsimp only [w]
      split <;> norm_num
    exact exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b
  have hD (c : Bool) : ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = c) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0) :=
    exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD
      (fun _ => 1) (fun _ => by norm_num) (hdetD fun _ => 1) c
  have hext := extensions_bound (minimum_displacements_three_extensions C D b 2 hsep hC hD)
  refine ⟨?_, ?_⟩
  · intro a
    obtain ⟨T, hT, haT⟩ := mem_axes.mp a.prop
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp (hsize T hT)
    rw [degree_eq_extensions F hsize]
    rcases mem_insert.mp haT with hai | haj
    · rw [hai]
      have h := hext _ hT j (by simp)
      have herase : ({i, j} : Finset (Fin 9)).erase j = {i} := by
        rw [Finset.pair_comm i j, Finset.erase_insert (by simpa using hij.symm)]
      rw [herase] at h
      exact h
    · have haj' := mem_singleton.mp haj
      rw [haj']
      have h := hext _ hT i (by simp)
      have herase : ({i, j} : Finset (Fin 9)).erase i = {j} :=
        Finset.erase_insert (by simpa using hij)
      rw [herase] at h
      exact h
  · intro a v c hav hac hvc ha hv
    let A := extensions F {a.val}
    let B := extensions F {v.val}
    have hAc : A.card = 3 := (degree_eq_extensions F hsize a).symm.trans ha
    have hBc : B.card = 3 := (degree_eq_extensions F hsize v).symm.trans hv
    have hvA : v.val ∈ A := (mem_partners hsize).mpr hav.2
    have hcA : c.val ∈ A := (mem_partners hsize).mpr hac.2
    have hvc' : v.val ≠ c.val := fun h => hvc (Subtype.ext h)
    have htwo : 1 < (A.erase v.val).card := by rw [card_erase_of_mem hvA, hAc]; decide
    obtain ⟨q, hq, hqc⟩ := exists_mem_ne htwo c.val
    have hqv := (mem_erase.mp hq).1
    have hqA := (mem_erase.mp hq).2
    have hAeq : A = {v.val, c.val, q} := by
      symm
      apply eq_of_subset_of_card_le (insert_subset hvA (insert_subset hcA (singleton_subset_iff.mpr hqA)))
      simp [hAc, hvc', hqv.symm, hqc.symm]
    have haPart (k : Fin 9) (hk : ({a.val, k} : Finset (Fin 9)) ∈ F) :
        k = v.val ∨ k = c.val ∨ k = q := by
      have hm : k ∈ A := (mem_partners hsize).mpr hk
      simpa [hAeq] using hm
    have hvPart (k : Fin 9) (hk : ({v.val, k} : Finset (Fin 9)) ∈ F) : k ∈ B :=
      (mem_partners hsize).mpr hk
    obtain ⟨x, hx, y, hy, hxb, _, hdiff⟩ := mem_minimumDisplacements.mp hav.2
    have hav' : a.val ≠ v.val := pair_ne hsize hav.2
    have hyflip : y = flip (flip x a.val) v.val :=
      differingAxes_right_inj (hdiff.trans (diff_pair x hav').symm)
    have hcontact : RidgeContact C D b [a.val] v.val x :=
      ⟨by simpa using hav'.symm, hx, hxb, hyflip ▸ hy⟩
    obtain ⟨f, hf, hAf⟩ := hC v.val
    obtain ⟨g, hg, hAg⟩ := hD b
    obtain ⟨r, _, hra, hrv, hrc, hvr, hcr⟩ :=
      three_partner_contact_completes_square (pair_ne hsize hac.2) hvc'
        hqc.symm (by rw [hBc]) haPart hvPart hsep hrC hrD hbC hbD f g hf hg hAf hAg hcontact
    let d : activeAxes F := ⟨r, mem_axes.mpr ⟨_, hvr, by simp⟩⟩
    exact ⟨d, fun h => hra (congrArg Subtype.val h),
      ⟨fun h => hrv (congrArg Subtype.val h).symm, hvr⟩,
      ⟨fun h => hrc (congrArg Subtype.val h).symm, hcr⟩⟩

open Classical in
/-- Eleven distance-two masks on seven active axes are impossible for
separated, connected, balanced cubic supports with universally singular signed defects. -/
theorem no_eleven_masks_on_seven_axes
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 7)
    (hmask : (minimumDisplacements C D b 2).card = 11) : False := by
  let F := minimumDisplacements C D b 2
  let G := maskGraph F
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨x, _, y, _, _, hd, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hd
  have hn : Fintype.card (activeAxes F) = 7 := (Fintype.card_coe _).trans haxes
  have he : G.edgeFinset.card = 11 := (card_edges F hsize).trans hmask
  obtain ⟨hmin, hsquare⟩ := distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  change (∀ a, 3 ≤ G.degree a) at hmin
  have hsum : (∑ a, G.degree a) = 22 := by
    rw [G.sum_degrees_eq_twice_card_edges, he]
  let excess (a : activeAxes F) := G.degree a - 3
  have hsplit (a : activeAxes F) : G.degree a = 3 + excess a := by
    have h := hmin a
    dsimp only [excess]
    omega
  have hxsum : (∑ a, excess a) = 1 := by
    have hh : (∑ a, G.degree a) = (∑ a : activeAxes F, 3) + ∑ a, excess a := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun a _ => hsplit a
    rw [hsum, sum_const, card_univ, hn] at hh
    change 22 = 21 + (∑ a, excess a) at hh
    omega
  obtain ⟨h, _, hhpos⟩ : ∃ h ∈ (univ : Finset (activeAxes F)), 0 < excess h := by
    by_contra! hnpos
    have hz : (∑ a, excess a) = 0 := sum_eq_zero fun a ha => by
      have h := hnpos a ha
      omega
    omega
  have hhbound : excess h ≤ 1 := by
    have hh := single_le_sum (f := excess) (fun a _ => Nat.zero_le (excess a)) (mem_univ h)
    rwa [hxsum] at hh
  have hh : G.degree h = 4 := by
    have heq := hsplit h
    omega
  have hcubic (a : activeAxes F) (ha : a ≠ h) : G.degree a = 3 := by
    have hle := sum_le_sum_of_subset_of_nonneg (f := excess)
      (show ({a, h} : Finset (activeAxes F)) ⊆ univ from subset_univ _)
      (fun _ _ _ => Nat.zero_le _)
    rw [hxsum, sum_pair ha] at hle
    have heq := hsplit a
    omega
  have hshape := Omega.CubicSquareCompletion.complete_bipartite G h
    (by rw [hh]; decide) (by rw [hh]) (by rw [hn, hh]) hcubic hsquare
  omega

open Classical in
/-- A nine-mask family on six coordinates is a complete bipartite graph with
three coordinates in each part. -/
theorem nine_masks_on_six_axes_bipartite
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 6)
    (hmask : (minimumDisplacements C D b 2).card = 9) :
    let F := minimumDisplacements C D b 2
    let G := maskGraph F
    ∃ R : Finset (activeAxes F), R.card = 3 ∧
      ∀ a b, G.Adj a b ↔ (a ∈ R ∧ b ∉ R) ∨ (a ∉ R ∧ b ∈ R) := by
  let F := minimumDisplacements C D b 2
  let G := maskGraph F
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨x, _, y, _, _, hd, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hd
  have hn : Fintype.card (activeAxes F) = 6 := (Fintype.card_coe _).trans haxes
  have he : G.edgeFinset.card = 9 := (card_edges F hsize).trans hmask
  obtain ⟨hmin, hsquare⟩ := distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  change (∀ a, 3 ≤ G.degree a) at hmin
  have hsum : (∑ a, G.degree a) = 18 := by
    rw [G.sum_degrees_eq_twice_card_edges, he]
  let excess (a : activeAxes F) := G.degree a - 3
  have hsplit (a : activeAxes F) : G.degree a = 3 + excess a := by
    have h := hmin a
    dsimp only [excess]
    omega
  have hxsum : (∑ a, excess a) = 0 := by
    have hh : (∑ a, G.degree a) = (∑ a : activeAxes F, 3) + ∑ a, excess a := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun a _ => hsplit a
    rw [hsum, sum_const, card_univ, hn] at hh
    change 18 = 18 + (∑ a, excess a) at hh
    omega
  have hcubic (a : activeAxes F) : G.degree a = 3 := by
    have hle := single_le_sum (f := excess) (fun a _ => Nat.zero_le (excess a)) (mem_univ a)
    rw [hxsum] at hle
    have heq := hsplit a
    omega
  have hnonempty : Nonempty (activeAxes F) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨h⟩ := hnonempty
  obtain ⟨_, hG⟩ := Omega.CubicSquareCompletion.complete_bipartite G h
    (by rw [hcubic]) (by rw [hcubic]; decide) (by rw [hn, hcubic])
    (fun a _ => hcubic a) hsquare
  refine ⟨G.neighborFinset h, by rw [SimpleGraph.card_neighborFinset_eq_degree, hcubic], ?_⟩
  intro a b
  simpa only [SimpleGraph.mem_neighborFinset] using hG a b

#print axioms nine_masks_on_six_axes_bipartite

#print axioms no_eleven_masks_on_seven_axes

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph
