/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: An eight-point lower bound on four-coordinate projections of balanced cubic supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjection
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TripleProjection
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe

/-! Antipodal complementary edges force eight occupied patterns in the four-cube.
For Hong–Wu–Xia, §7 Problem 2, the missing pair and triple restrictions give
this antipodality on every four-coordinate projection. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourProjection

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum
  (Q IsBalanced flip flip_apply_same directionEdges direction_edge_count)
open Q9PairProjection (pair_projection_surjective)
open Q9TripleProjection (half_card_le_of_missing_triple_patterns)

private instance : Fintype (BitVec 4) :=
  Fintype.ofEquiv (Fin (2 ^ 4)) (BitVec.equivFin (m := 4)).toEquiv.symm

/-- Flip the bit in direction `i` in the little-endian four-cube. -/
def flipBit (x : BitVec 4) (i : Fin 4) : BitVec 4 :=
  x ^^^ BitVec.ofNat 4 (2 ^ i.val)

private theorem decode_flip (x : BitVec 4) (i : Fin 4) :
    cubeBitVec 4 (flipBit x i) = flip (cubeBitVec 4 x) i :=
  cubeBitVec_xor_single x i

private theorem bit_flip_same (x : BitVec 4) (i : Fin 4) :
    (flipBit x i).getLsbD i.val = !x.getLsbD i.val :=
  (congrFun (decode_flip x i) i).trans (flip_apply_same _ _)

private theorem bit_flip_other (x : BitVec 4) {i j : Fin 4} (h : j ≠ i) :
    (flipBit x i).getLsbD j.val = x.getLsbD j.val :=
  (congrFun (decode_flip x i) j).trans (Function.update_of_ne h _ _)

private theorem xor_involutive (m : BitVec 4) :
    Function.Involutive (fun x : BitVec 4 => x ^^^ m) := by
  intro x
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem flipBit_flip (x : BitVec 4) (i : Fin 4) : flipBit (flipBit x i) i = x :=
  xor_involutive _ x

private theorem flip_antipode (x : BitVec 4) (i : Fin 4) :
    flipBit (x ^^^ 15) i = flipBit x i ^^^ 15 := by
  simp only [flipBit, BitVec.xor_assoc, BitVec.xor_comm (15 : BitVec 4)]

private theorem bit_antipode (x : BitVec 4) (i : Fin 4) :
    (x ^^^ 15).getLsbD i.val = !x.getLsbD i.val := by
  have h : ∀ j : Fin 4, (15 : BitVec 4).getLsbD j.val = true := by decide +kernel
  rw [BitVec.getLsbD_xor, h i, Bool.xor_true]

private def half (S : Finset (BitVec 4)) (i : Fin 4) (b : Bool) : Finset (BitVec 4) :=
  S.filter (fun x => x.getLsbD i.val = b)

private theorem mem_half {S : Finset (BitVec 4)} {i : Fin 4} {b : Bool} {x : BitVec 4} :
    x ∈ half S i b ↔ x ∈ S ∧ x.getLsbD i.val = b := mem_filter

private theorem half_card_sum (S : Finset (BitVec 4)) (i : Fin 4) :
    (half S i false).card + (half S i true).card = S.card := by
  have h : S.filter (fun x => ¬ x.getLsbD i.val = false) = half S i true := by
    ext x
    cases hx : x.getLsbD i.val <;> simp [half, hx]
  rw [← h]
  exact card_filter_add_card_filter_not (s := S) (fun x => x.getLsbD i.val = false)

private def edgeStarts (S : Finset (BitVec 4)) (i : Fin 4) : Finset (BitVec 4) :=
  S.filter (fun x => x.getLsbD i.val = false ∧ flipBit x i ∈ S)

private theorem mem_edgeStarts {S : Finset (BitVec 4)} {i : Fin 4} {x : BitVec 4} :
    x ∈ edgeStarts S i ↔ x ∈ S ∧ x.getLsbD i.val = false ∧ flipBit x i ∈ S :=
  mem_filter

-- The union counts all edges meeting P, and the intersection counts the edges inside P.
private theorem matching_count (P : Finset (BitVec 4)) (i : Fin 4) :
    (edgeStarts Pᶜ i).card + P.card = 8 + (edgeStarts P i).card := by
  let U := half univ i false
  let A := half P i false
  let B := U.filter (fun x => flipBit x i ∈ P)
  have hU : U.card = 8 :=
    (show ∀ j : Fin 4, (half univ j false).card = 8 by decide +kernel) i
  have hB : B.card = (half P i true).card := by
    apply card_bijective (fun x => flipBit x i)
      (xor_involutive (BitVec.ofNat 4 (2 ^ i.val))).bijective
    intro x
    simp only [B, U, mem_filter, mem_half, mem_univ, true_and, bit_flip_same]
    cases x.getLsbD i.val <;> simp [and_comm]
  have hi : A ∩ B = edgeStarts P i := by
    ext x
    simp only [A, B, U, mem_inter, mem_edgeStarts, mem_half, mem_filter, mem_univ, true_and]
    tauto
  have ht : U \ (A ∪ B) = edgeStarts Pᶜ i := by
    ext x
    simp only [A, B, U, mem_sdiff, mem_union, mem_edgeStarts, mem_half, mem_filter, mem_univ,
      true_and, mem_compl]
    tauto
  have hsub : A ∪ B ⊆ U :=
    union_subset (fun x hx => mem_half.mpr ⟨mem_univ x, (mem_half.mp hx).2⟩) (filter_subset _ _)
  have hcover := card_sdiff_add_card_eq_card hsub
  rw [ht, hU] at hcover
  have hcount := card_union_add_card_inter A B
  rw [hi, hB] at hcount
  have hpart : A.card + (half P i true).card = P.card := half_card_sum P i
  omega

private theorem exists_unpaired {P : Finset (BitVec 4)} (hP : P.card = 7) :
    ∃ z : BitVec 4, z ∉ P ∧ z ^^^ 15 ∈ P := by
  by_contra h
  have closed (x : BitVec 4) (hx : x ∉ P) : x ^^^ 15 ∉ P := fun ha => h ⟨x, hx, ha⟩
  have hc (x : BitVec 4) : x ∈ Pᶜ ↔ x ^^^ 15 ∈ Pᶜ := by
    refine ⟨fun hx => mem_compl.mpr (closed x (mem_compl.mp hx)), ?_⟩
    intro hx
    have he : (x ^^^ 15) ^^^ 15 = x := xor_involutive 15 x
    exact mem_compl.mpr (he ▸ closed (x ^^^ 15) (mem_compl.mp hx))
  have heq : (half Pᶜ 0 false).card = (half Pᶜ 0 true).card := by
    apply card_bijective (fun x => x ^^^ 15) (xor_involutive 15).bijective
    intro x
    rw [mem_half, mem_half, bit_antipode, ← hc x]
    cases x.getLsbD (0 : Fin 4).val <;> simp
  have hT : (Pᶜ).card = 9 := by
    rw [card_compl, show Fintype.card (BitVec 4) = 16 by decide +kernel, hP]
  have hsplit := half_card_sum Pᶜ 0
  omega

private theorem eight_of_unpaired {P : Finset (BitVec 4)} (z : BitVec 4)
    (hz : z ∉ P) (hza : z ^^^ 15 ∈ P)
    (hclosed : ∀ x i, x ∉ P → flipBit x i ∉ P → x ^^^ 15 ∉ P) : 8 ≤ P.card := by
  by_contra hsmall
  -- XOR translation to z = 0 commutes with every coordinate flip and with the antipode.
  let A := P.image (fun x => z ^^^ x)
  have hinv : Function.Involutive (fun x => z ^^^ x) := by
    intro x
    simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  have hcard : A.card = P.card := card_image_of_injective _ hinv.injective
  have hmem (x : BitVec 4) : x ∈ A ↔ z ^^^ x ∈ P := by
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := mem_image.mp hx
      rw [← hyx]
      have he : z ^^^ (z ^^^ y) = y := hinv y
      rw [he]
      exact hy
    · intro hx
      exact mem_image.mpr ⟨z ^^^ x, hx, hinv x⟩
  have isolated (x : BitVec 4) (hx : x ∉ A) (ha : x ^^^ 15 ∈ A) (i : Fin 4) :
      flipBit x i ∈ A := by
    by_contra hn
    have hh : flipBit (z ^^^ x) i ∉ P := by
      simpa only [flipBit, BitVec.xor_assoc] using (hmem _).not.mp hn
    have hn' := hclosed (z ^^^ x) i ((hmem x).not.mp hx) hh
    exact hn' (by simpa only [BitVec.xor_assoc] using (hmem _).mp ha)
  have h0 : (0 : BitVec 4) ∉ A := by
    intro hx
    have he : z ^^^ (0 : BitVec 4) = z := BitVec.xor_zero
    exact hz (he ▸ (hmem 0).mp hx)
  have h15 : (15 : BitVec 4) ∈ A := (hmem 15).mpr hza
  let near : Finset (BitVec 4) := {1, 2, 4, 8, 15}
  let far : Finset (BitVec 4) := {7, 11, 13, 14}
  have hnear : near ⊆ A := by
    have he : near = insert 15 (univ.image (flipBit 0)) := by decide +kernel
    rw [he]
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact h15
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      have he : (0 : BitVec 4) ^^^ 15 = 15 := by decide +kernel
      exact isolated 0 h0 (he.symm ▸ h15) i
  have hall : (near ∪ far).card = 9 := by decide +kernel
  obtain ⟨w, hw, hwA⟩ := exists_mem_notMem_of_card_lt_card
    (show A.card < (near ∪ far).card by omega)
  have hwfar := (mem_union.mp hw).resolve_left (fun hn => hwA (hnear hn))
  have hfar_antipode : ∀ v : BitVec 4, v ∈ far → v ^^^ 15 ∈ near := by decide +kernel
  have hfar_count : ∀ v : BitVec 4, v ∈ far →
      8 ≤ (near ∪ (univ.image (flipBit v))).card := by decide +kernel
  have hneighbors : univ.image (flipBit w) ⊆ A := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact isolated w hwA (hnear (hfar_antipode w hwfar)) i
  have hbound := (hfar_count w hwfar).trans (card_le_card (union_subset hnear hneighbors))
  omega

/-- Suppose every direction has an edge in `P`, and any two distinct edges in the
complement in the same direction are antipodal. Then `P` has at least eight vertices.
An edge is represented by its FALSE endpoint, so its antipodal edge starts at
`flipBit (x ^^^ 15) i`. -/
theorem card_ge_eight_of_antipodal_complement_edges (P : Finset (BitVec 4))
    (hedge : ∀ i : Fin 4, ∃ x ∈ P, x.getLsbD i.val = false ∧ flipBit x i ∈ P)
    (hantipodal : ∀ (i : Fin 4) (x y : BitVec 4),
      x.getLsbD i.val = false → y.getLsbD i.val = false →
      x ∉ P → flipBit x i ∉ P → y ∉ P → flipBit y i ∉ P →
      x ≠ y → y = flipBit (x ^^^ 15) i) : 8 ≤ P.card := by
  have hop (i : Fin 4) {x y : BitVec 4}
      (hx : x ∈ edgeStarts Pᶜ i) (hy : y ∈ edgeStarts Pᶜ i) (hne : x ≠ y) :
      y = flipBit (x ^^^ 15) i := by
    obtain ⟨hxP, hxi, hfx⟩ := mem_edgeStarts.mp hx
    obtain ⟨hyP, hyi, hfy⟩ := mem_edgeStarts.mp hy
    exact hantipodal i x y hxi hyi (mem_compl.mp hxP) (mem_compl.mp hfx)
      (mem_compl.mp hyP) (mem_compl.mp hfy) hne
  have at_most_two (i : Fin 4) : (edgeStarts Pᶜ i).card ≤ 2 := by
    by_cases he : (edgeStarts Pᶜ i).Nonempty
    · obtain ⟨x, hx⟩ := he
      refine (card_le_card (t := {x, flipBit (x ^^^ 15) i}) ?_).trans card_le_two
      intro y hy
      by_cases h : x = y
      · simp [h]
      · simp [hop i hx hy h]
    · rw [not_nonempty_iff_eq_empty.mp he, card_empty]
      exact Nat.zero_le _
  have at_least_one (i : Fin 4) : 0 < (edgeStarts P i).card := by
    obtain ⟨x, hx, hi, hf⟩ := hedge i
    exact card_pos.mpr ⟨x, mem_edgeStarts.mpr ⟨hx, hi, hf⟩⟩
  by_contra hsmall
  have hseven : P.card = 7 := by
    have := matching_count P 0
    have := at_most_two 0
    have := at_least_one 0
    omega
  have htwo (i : Fin 4) : (edgeStarts Pᶜ i).card = 2 := by
    have := matching_count P i
    have := at_most_two i
    have := at_least_one i
    omega
  have partner (i : Fin 4) {x : BitVec 4} (hx : x ∈ edgeStarts Pᶜ i) :
      flipBit (x ^^^ 15) i ∈ edgeStarts Pᶜ i := by
    have h : 1 < (edgeStarts Pᶜ i).card := by
      simpa only [htwo] using (show 1 < 2 by decide)
    obtain ⟨y, hy, hne⟩ := exists_mem_ne h x
    exact hop i hx hy hne.symm ▸ hy
  have hclosed (x : BitVec 4) (i : Fin 4) (hx : x ∉ P) (hf : flipBit x i ∉ P) :
      x ^^^ 15 ∉ P := by
    by_cases hi : x.getLsbD i.val = false
    · have h := partner i (mem_edgeStarts.mpr ⟨mem_compl.mpr hx, hi, mem_compl.mpr hf⟩)
      simpa only [mem_compl, flipBit_flip] using (mem_edgeStarts.mp h).2.2
    · have hi' : (flipBit x i).getLsbD i.val = false := by
        rw [bit_flip_same]
        cases hb : x.getLsbD i.val <;> simp_all
      have h := partner i (mem_edgeStarts.mpr ⟨mem_compl.mpr hf, hi',
        mem_compl.mpr (by simpa only [flipBit_flip] using hx)⟩)
      simpa only [mem_compl, flip_antipode, flipBit_flip] using (mem_edgeStarts.mp h).1
  obtain ⟨z, hz, hza⟩ := exists_unpaired hseven
  exact hsmall (eight_of_unpaired z hz hza hclosed)

-- A nonzero difference mask other than the antipodal edge mask has a changed
-- and an unchanged bit outside the edge direction.
private theorem remaining_axes (i : Fin 4) (m : BitVec 4)
    (hi : m.getLsbD i.val = false) (hnz : m ≠ 0) (hanti : m ≠ flipBit 15 i) :
    ∃ j k l : Fin 4, j ≠ i ∧ k ≠ i ∧ l ≠ i ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      m.getLsbD k.val = true ∧ m.getLsbD l.val = false ∧
      ∀ r : Fin 4, r ≠ i → r = j ∨ r = k ∨ r = l := by
  decide +revert +kernel

open Classical in
/-- Distinct complement edges in the same direction of a four-coordinate projection
are antipodal when all bit pairs occur on the chosen axes and their halves exceed 24. -/
theorem four_projection_antipodal_complement_edges_of_pair_coverage
    {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced S)
    (axes : Fin 4 ↪ Fin 9)
    (hpair : ∀ ⦃j k : Fin 4⦄, j ≠ k → ∀ a b : Bool,
      ∃ v ∈ S, v (axes j) = a ∧ v (axes k) = b)
    (hhalf : ∀ (k : Fin 4) (b : Bool), 24 < (S.filter (fun x => x (axes k) = b)).card) :
    let project (v : Q 9) : BitVec 4 := (cubeBitVec 4).symm (fun i => v (axes i))
    let P := S.image project
    ∀ (i : Fin 4) (x y : BitVec 4),
      x.getLsbD i.val = false → y.getLsbD i.val = false →
      x ∉ P → flipBit x i ∉ P → y ∉ P → flipBit y i ∉ P →
      x ≠ y → y = flipBit (x ^^^ 15) i := by
  classical
  intro project P
  have project_bit (v : Q 9) (i : Fin 4) : (project v).getLsbD i.val = v (axes i) :=
    congrFun ((cubeBitVec 4).apply_symm_apply (fun j => v (axes j))) i
  intro i x y hxi hyi hx hfx hy hfy hxy
  by_contra hnot
  have hmask : (x ^^^ y).getLsbD i.val = false := by
    simp only [BitVec.getLsbD_xor, hxi, hyi, Bool.xor_false]
  have hmask_ne : x ^^^ y ≠ flipBit 15 i := by
    intro he
    apply hnot
    apply (BitVec.xor_right_inj x).mp
    calc
      x ^^^ y = flipBit 15 i := he
      _ = x ^^^ flipBit (x ^^^ 15) i := by
        simp only [flipBit, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  obtain ⟨j, k, l, hji, hki, hli, hjk, hjl, hkl, hk, hl, cover⟩ :=
    remaining_axes i (x ^^^ y) hmask (fun h => hxy (BitVec.xor_eq_zero_iff.mp h)) hmask_ne
  have bit_from_mask (r : Fin 4) :
      y.getLsbD r.val = (x.getLsbD r.val ^^ (x ^^^ y).getLsbD r.val) := by
    rw [BitVec.getLsbD_xor]
    cases x.getLsbD r.val <;> cases y.getLsbD r.val <;> rfl
  have hyk : y.getLsbD k.val = !x.getLsbD k.val := by
    simpa only [hk, Bool.xor_true] using bit_from_mask k
  have hyl : y.getLsbD l.val = x.getLsbD l.val := by
    simpa only [hl, Bool.xor_false] using bit_from_mask l
  -- If the three other bits are fixed, the only extensions are the two endpoints.
  have absent (u : BitVec 4) (hui : u.getLsbD i.val = false)
      (hu : u ∉ P) (hfu : flipBit u i ∉ P) (v : Q 9) (hv : v ∈ S)
      (hvj : v (axes j) = u.getLsbD j.val) (hvk : v (axes k) = u.getLsbD k.val)
      (hvl : v (axes l) = u.getLsbD l.val) : False := by
    have hproj : project v ∈ P := mem_image.mpr ⟨v, hv, rfl⟩
    have extend (w : BitVec 4) (hw : w.getLsbD i.val = v (axes i))
        (hother : ∀ r : Fin 4, r ≠ i → w.getLsbD r.val = u.getLsbD r.val) :
        project v = w := by
      apply (cubeBitVec 4).injective
      funext r
      change (project v).getLsbD r.val = w.getLsbD r.val
      rw [project_bit]
      by_cases hri : r = i
      · subst r
        exact hw.symm
      · rw [hother r hri]
        rcases cover r hri with h | h | h <;> subst r <;> assumption
    cases hvi : v (axes i)
    · exact hu (extend u (hui.trans hvi.symm) (fun _ _ => rfl) ▸ hproj)
    · have hwi : (flipBit u i).getLsbD i.val = v (axes i) := by
        simp only [bit_flip_same, hui, hvi, Bool.not_false]
      exact hfu (extend _ hwi (fun _ hr => bit_flip_other u hr) ▸ hproj)
  cases hj : (x ^^^ y).getLsbD j.val
  · have hyj : y.getLsbD j.val = x.getLsbD j.val := by
      simpa only [hj, Bool.xor_false] using bit_from_mask j
    obtain ⟨v, hv, hvj, hvl⟩ := hpair hjl (x.getLsbD j.val) (x.getLsbD l.val)
    by_cases hvk : v (axes k) = x.getLsbD k.val
    · exact absent x hxi hx hfx v hv hvj hvk hvl
    · have hvk' : v (axes k) = !(x.getLsbD k.val) := by
        cases ha : v (axes k) <;> cases hb : x.getLsbD k.val <;> simp_all
      exact absent y hyi hy hfy v hv (hvj.trans hyj.symm)
        (hvk'.trans hyk.symm) (hvl.trans hyl.symm)
  · have hyj : y.getLsbD j.val = !x.getLsbD j.val := by
      simpa only [hj, Bool.xor_true] using bit_from_mask j
    have hbound := half_card_le_of_missing_triple_patterns hsize hreg hb
      (axes j) (axes k) (axes l)
      (x.getLsbD j.val) (x.getLsbD k.val) (x.getLsbD l.val)
      (axes.injective.ne hjk) (axes.injective.ne hjl) (axes.injective.ne hkl) (by
        intro v hv hp
        rcases hp with hp | hp
        · simp only [Prod.mk.injEq] at hp
          exact absent x hxi hx hfx v hv hp.1 hp.2.1 hp.2.2
        · simp only [Prod.mk.injEq] at hp
          exact absent y hyi hy hfy v hv (hp.1.trans hyj.symm)
            (hp.2.1.trans hyk.symm) (hp.2.2.trans hyl.symm))
    exact (not_lt_of_ge hbound) (hhalf l (x.getLsbD l.val))

open Classical in
/-- Distinct complement edges in the same direction of a four-coordinate projection
of an order-72 balanced induced cubic nine-cube support are antipodal, provided
each coordinate half contains at least 30 selected vertices. -/
theorem four_projection_antipodal_complement_edges {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced S)
    (hhalf : ∀ (k : Fin 9) (b : Bool), 30 ≤ (S.filter (fun x => x k = b)).card)
    (axes : Fin 4 ↪ Fin 9) :
    let project (v : Q 9) : BitVec 4 := (cubeBitVec 4).symm (fun i => v (axes i))
    let P := S.image project
    ∀ (i : Fin 4) (x y : BitVec 4),
      x.getLsbD i.val = false → y.getLsbD i.val = false →
      x ∉ P → flipBit x i ∉ P → y ∉ P → flipBit y i ∉ P →
      x ≠ y → y = flipBit (x ^^^ 15) i := by
  apply four_projection_antipodal_complement_edges_of_pair_coverage hsize hreg hb axes
  · intro j k hjk a b
    exact pair_projection_surjective hsize hreg hb hhalf (axes.injective.ne hjk) a b
  · intro k b
    exact (by decide : 24 < 30).trans_le (hhalf (axes k) b)

open Classical in
/-- The order and balance provide an occupied edge in each direction, so antipodality
of parallel complement edges forces at least eight realized patterns. -/
theorem four_projection_card_ge_eight_of_antipodal_complement_edges
    {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced S)
    (axes : Fin 4 ↪ Fin 9)
    (hanti :
      let P := S.image (fun v => (cubeBitVec 4).symm (fun i => v (axes i)))
      ∀ (i : Fin 4) (x y : BitVec 4),
        x.getLsbD i.val = false → y.getLsbD i.val = false →
        x ∉ P → flipBit x i ∉ P → y ∉ P → flipBit y i ∉ P →
        x ≠ y → y = flipBit (x ^^^ 15) i) :
    8 ≤ (S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))).card := by
  classical
  let project (v : Q 9) : BitVec 4 := (cubeBitVec 4).symm (fun i => v (axes i))
  let P := S.image project
  have project_bit (v : Q 9) (i : Fin 4) : (project v).getLsbD i.val = v (axes i) :=
    congrFun ((cubeBitVec 4).apply_symm_apply (fun j => v (axes j))) i
  change 8 ≤ P.card
  apply card_ge_eight_of_antipodal_complement_edges P
  · intro i
    have hd := direction_edge_count (d := 3) S hreg hb (axes i)
    have hpos : 0 < directionEdges S (axes i) := by omega
    unfold directionEdges at hpos
    obtain ⟨v, hv⟩ := card_pos.mp hpos
    obtain ⟨hvS, hvi, hfS⟩ := mem_filter.mp hv
    have hf : flipBit (project v) i = project (flip v (axes i)) := by
      apply (cubeBitVec 4).injective
      funext j
      change (flipBit (project v) i).getLsbD j.val = (project (flip v (axes i))).getLsbD j.val
      rw [project_bit]
      by_cases h : j = i
      · subst j
        rw [bit_flip_same, project_bit, flip_apply_same]
      · rw [bit_flip_other _ h, project_bit]
        exact (Function.update_of_ne (axes.injective.ne h) _ _).symm
    refine ⟨project v, mem_image.mpr ⟨v, hvS, rfl⟩, (project_bit v i).trans hvi, ?_⟩
    rw [hf]
    exact mem_image.mpr ⟨flip v (axes i), hfS, rfl⟩
  · exact hanti

open Classical in
/-- Every ordered choice of four distinct coordinates of an order-72 balanced
induced cubic nine-cube support has at least eight realized patterns, provided
each coordinate half contains at least 30 selected vertices. -/
theorem four_projection_card_ge_eight {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced S)
    (hhalf : ∀ (k : Fin 9) (b : Bool), 30 ≤ (S.filter (fun x => x k = b)).card)
    (axes : Fin 4 ↪ Fin 9) :
    8 ≤ (S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))).card := by
  exact four_projection_card_ge_eight_of_antipodal_complement_edges hsize hreg hb axes
    (four_projection_antipodal_complement_edges hsize hreg hb hhalf axes)

#print axioms card_ge_eight_of_antipodal_complement_edges
#print axioms four_projection_antipodal_complement_edges_of_pair_coverage
#print axioms four_projection_antipodal_complement_edges
#print axioms four_projection_card_ge_eight_of_antipodal_complement_edges
#print axioms four_projection_card_ge_eight

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourProjection
