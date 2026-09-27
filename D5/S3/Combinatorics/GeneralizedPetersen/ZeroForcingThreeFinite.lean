/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite
   mirror-E: none(waiver:finite-certificate-support-for-an-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.fortOK
   digest: Transparent finite checkers certify forts and cyclic support words for the zero-forcing proof. -/

import D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFiniteCore
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFiniteRotation
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite

open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)

/-- The finite neighbourhood of a vertex, without requiring a `LocallyFinite` instance. -/
def finiteNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter (G.Adj v)

/-- A fort is a nonempty set met either zero or at least twice by every outside neighbourhood. -/
def IsFort {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset V) : Prop :=
  F.Nonempty ∧ ∀ v ∉ F, (finiteNeighbors G v ∩ F).card ≠ 1

/-- Every advertised neighbour in the 13-column checker is an actual graph neighbour, and vice versa. -/
theorem neighbors13_spec (v w : V13) :
    w ∈ neighbors13 v ↔ (gp 13 3).Adj v w := by
  decide +kernel +revert

/-- The bit-position encoding is injective on the 26 vertices. -/
private theorem code13_injective : Function.Injective code13 := by
  rintro ⟨ba, ia⟩ ⟨bb, ib⟩ h
  cases ba <;> cases bb
  · simp [code13] at h
    congr
    exact Fin.ext h
  · simp [code13] at h
    omega
  · simp [code13] at h
    omega
  · simp [code13] at h
    congr
    exact Fin.ext h

/-- The mask positions are exactly the vertices of `P(13,3)`. -/
private def finCode13 (v : V13) : Fin 26 :=
  ⟨code13 v, by cases v with | mk b i => cases b <;> simp [code13] <;> omega⟩

private theorem finCode13_bijective : Function.Bijective finCode13 := by
  apply (Fintype.bijective_iff_injective_and_card finCode13).2
  constructor
  · intro v w h
    exact code13_injective (Fin.ext_iff.mp h)
  · simp [V13]

/-- The vertex-to-bit-position equivalence used by every finite certificate. -/
private noncomputable def vertexCodeEquiv13 : V13 ≃ Fin 26 :=
  Equiv.ofBijective finCode13 finCode13_bijective

/-- A bounded mask is recovered from exactly the vertices that it decodes. -/
private theorem maskSet13_injective_bounded {m₁ m₂ : Nat} (hm₁ : m₁ < 2 ^ 26)
    (hm₂ : m₂ < 2 ^ 26) (hset : maskSet13 m₁ = maskSet13 m₂) : m₁ = m₂ := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 26
  · let j : Fin 26 := ⟨i, hi⟩
    obtain ⟨v, hv⟩ := vertexCodeEquiv13.surjective j
    have hs := Finset.ext_iff.mp hset v
    have hcode : code13 v = i := by
      have := congrArg Fin.val hv
      change code13 v = i at this
      exact this
    simpa [maskSet13, hcode] using hs
  · have hp : 2 ^ 26 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_eq_false_of_lt (hm₁.trans_le hp),
      Nat.testBit_eq_false_of_lt (hm₂.trans_le hp)]

/-- The explicit bit count is the cardinality of the decoded vertex set. -/
theorem bitCount26_eq_card_maskSet13 (m : Nat) :
    bitCount26 m = (maskSet13 m).card := by
  have huniv : Finset.univ.image code13 = Finset.range 26 := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      exact (finCode13 v).isLt
    · intro hi
      let j : Fin 26 := ⟨i, hi⟩
      obtain ⟨v, hv⟩ := vertexCodeEquiv13.surjective j
      refine ⟨v, ?_⟩
      have := congrArg Fin.val hv
      change code13 v = i at this
      exact this
  have himage : (maskSet13 m).image code13 =
      (Finset.range 26).filter fun i => m.testBit i := by
    rw [← huniv]
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, rfl⟩, by simpa [maskSet13] using hv⟩
    · rintro ⟨⟨v, rfl⟩, hv⟩
      exact ⟨v, by simpa [maskSet13] using hv, rfl⟩
  rw [bitCount26, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _),
    List.toFinset_filter]
  simp only [List.toFinset_range]
  rw [← himage, Finset.card_image_of_injective _ code13_injective]

/-- The numeric neighbour list is a duplicate-free encoding of the graph neighbourhood. -/
private theorem neighborCodes13_nodup (v : V13) :
    (neighborCodes13 (code13 v)).Nodup := by
  decide +kernel +revert

private theorem neighborCodes13_toFinset (v : V13) :
    (neighborCodes13 (code13 v)).toFinset = (neighbors13 v).image code13 := by
  decide +kernel +revert

/-- Numeric neighbour counting agrees with intersection in the decoded graph. -/
private theorem neighborCount13_spec (m : Nat) (v : V13) :
    (neighborCodes13 (code13 v)).countP m.testBit =
      (neighbors13 v ∩ maskSet13 m).card := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((neighborCodes13_nodup v).filter _),
    List.toFinset_filter, neighborCodes13_toFinset]
  have himage : (neighbors13 v ∩ maskSet13 m).image code13 =
      ((neighbors13 v).image code13).filter fun i => m.testBit i := by
    ext i
    simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨w, ⟨hw, hm⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, by simpa [maskSet13] using hm⟩
    · rintro ⟨⟨w, hw, rfl⟩, hm⟩
      exact ⟨w, ⟨hw, by simpa [maskSet13] using hm⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ code13_injective]

/-- A successful numeric fort check denotes a genuine fort in `P(13,3)`. -/
theorem fortOK_sound {m : Nat} (hm : fortOK m = true) :
    IsFort (gp 13 3) (maskSet13 m) := by
  rw [fortOK, Bool.and_eq_true] at hm
  have hbounds : 0 < m ∧ m < 2 ^ 26 := of_decide_eq_true hm.1
  constructor
  · rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hzero : m = 0 := by
      apply Nat.zero_of_testBit_eq_false
      intro i
      by_cases hi : i < 26
      · let j : Fin 26 := ⟨i, hi⟩
        obtain ⟨v, hv⟩ := vertexCodeEquiv13.surjective j
        have := Finset.notMem_empty v
        have hcode : code13 v = i := by
          have := congrArg Fin.val hv
          change code13 v = i at this
          exact this
        rw [← he] at this
        simp only [maskSet13, Finset.mem_filter, Finset.mem_univ,
          true_and, hcode] at this
        exact Bool.eq_false_iff.mpr this
      · exact Nat.testBit_eq_false_of_lt
          (hbounds.2.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)))
    omega
  · intro v hv
    have hneighbors : finiteNeighbors (gp 13 3) v = neighbors13 v := by
      ext w
      simp [finiteNeighbors, neighbors13_spec]
    rw [hneighbors, ← neighborCount13_spec]
    have hall := List.all_eq_true.mp hm.2 (code13 v)
    have hcode : code13 v < 26 := (finCode13 v).isLt
    have hmem : code13 v ∈ List.range 26 := List.mem_range.mpr hcode
    specialize hall hmem
    rw [Bool.or_eq_true] at hall
    rcases hall with hin | hcount
    · exact (hv (by simpa [maskSet13] using hin)).elim
    · exact of_decide_eq_true hcount

/-- Encode a finite vertex set into the certificate mask convention. -/
def setMask13 (S : Finset V13) : Nat := ∑ v ∈ S, 2 ^ code13 v

/-- A set's encoded mask has a bit exactly at its member vertices. -/
theorem testBit_setMask13 (S : Finset V13) (v : V13) :
    (setMask13 S).testBit (code13 v) ↔ v ∈ S := by
  have hsum : setMask13 S = ∑ i ∈ S.image code13, 2 ^ i := by
    rw [setMask13, Finset.sum_image]
    exact fun _ _ _ _ h => code13_injective h
  have hbits := Finset.toFinset_bitIndices_sum_two_pow (S.image code13)
  rw [← hsum] at hbits
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, hbits]
  simp [code13_injective.eq_iff]

/-- Every encoded vertex set stays inside the low 26 bits. -/
theorem setMask13_lt_two_pow (S : Finset V13) : setMask13 S < 2 ^ 26 := by
  have hsubset : S.image code13 ⊆ Finset.range 26 := by
    intro i hi
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (finCode13 v).isLt
  have hsum : setMask13 S = ∑ i ∈ S.image code13, 2 ^ i := by
    rw [setMask13, Finset.sum_image]
    exact fun _ _ _ _ h => code13_injective h
  rw [hsum]
  calc
    ∑ i ∈ S.image code13, 2 ^ i ≤ ∑ i ∈ Finset.range 26, 2 ^ i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
    _ < 2 ^ 26 := by rw [Nat.geomSum_eq (by omega : 2 ≤ 2)]; norm_num

/-- Rotate a finite vertex set columnwise. -/
def rotateFinset13 (r : Fin 13) (S : Finset V13) : Finset V13 := S.image (rotate13 r)


/-- The six anchors exhaust every oriented force after rotating its source to column zero. -/
theorem initialForce_anchor13 (u w : V13) (huw : (gp 13 3).Adj u w) :
    ∃ a : Anchor13,
      anchorTarget a = rotate13 u.2 w ∧
      anchorRequired a =
        insert (rotate13 u.2 u) ((neighbors13 u).erase w |>.image (rotate13 u.2)) := by
  revert huw
  decide +kernel +revert

/-- All seven-sets extending one fixed oriented first-force anchor. -/
private def anchorCandidates (a : Anchor13) : Finset (Finset V13) :=
  let eligible := Finset.univ \ insert (anchorTarget a) (anchorRequired a)
  (eligible.powersetCard 4).image fun extra => anchorRequired a ∪ extra

/-- Each anchor fixes three black vertices and excludes a fourth vertex. -/
private theorem anchorRequired_card (a : Anchor13) : (anchorRequired a).card = 3 := by
  cases a <;> decide

private theorem anchorTarget_not_mem_required (a : Anchor13) :
    anchorTarget a ∉ anchorRequired a := by
  cases a <;> decide

private theorem anchorEligible_card (a : Anchor13) :
    (Finset.univ \ insert (anchorTarget a) (anchorRequired a)).card = 22 := by
  cases a <;> decide

/-- The semantic family of seven-sets extending one anchor has exactly `choose 22 4` members. -/
private theorem anchorCandidates_card (a : Anchor13) : (anchorCandidates a).card = 7315 := by
  let eligible := Finset.univ \ insert (anchorTarget a) (anchorRequired a)
  have helig : eligible.card = 22 := anchorEligible_card a
  rw [anchorCandidates, Finset.card_image_iff.mpr]
  · rw [Finset.card_powersetCard, helig]
    decide
  · intro x hx y hy hxy
    have hxr : Disjoint x (anchorRequired a) := by
      rw [Finset.disjoint_left]
      intro v hvx hvr
      have hvEligible := (Finset.mem_powersetCard.mp hx).1 hvx
      exact (Finset.mem_sdiff.mp hvEligible).2 (Finset.mem_insert_of_mem hvr)
    have hyr : Disjoint y (anchorRequired a) := by
      rw [Finset.disjoint_left]
      intro v hvy hvr
      have hvEligible := (Finset.mem_powersetCard.mp hy).1 hvy
      exact (Finset.mem_sdiff.mp hvEligible).2 (Finset.mem_insert_of_mem hvr)
    ext v
    have hv := Finset.ext_iff.mp hxy v
    by_cases hvr : v ∈ anchorRequired a
    · exact iff_of_false
        (fun hvx => (Finset.disjoint_left.mp hxr) hvx hvr)
        (fun hvy => (Finset.disjoint_left.mp hyr) hvy hvr)
    · simpa [hvr] using hv

/-- A mask passing the anchor-shape check decodes to the advertised semantic family. -/
private theorem candidateShapeOK_sound {a : Anchor13} {m : Nat}
    (h : candidateShapeOK a m = true) : maskSet13 m ∈ anchorCandidates a := by
  have hs := of_decide_eq_true h
  let required := anchorRequired a
  let eligible := Finset.univ \ insert (anchorTarget a) required
  let extra := maskSet13 m \ required
  have hreq : required ⊆ maskSet13 m := by
    intro v hv
    simpa [maskSet13] using (hs.2.2.1 v hv)
  have htarget : anchorTarget a ∉ maskSet13 m := by
    simpa [maskSet13] using hs.2.2.2
  have hextra : extra ⊆ eligible := by
    intro v hv
    have hv' := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, by
      rw [Finset.mem_insert]
      exact not_or_intro (fun hvt => htarget (hvt ▸ hv'.1)) hv'.2⟩
  have hcardSet : (maskSet13 m).card = 7 := by
    rw [← bitCount26_eq_card_maskSet13]
    exact hs.2.1
  have hcardExtra : extra.card = 4 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hreq, hcardSet, anchorRequired_card]
  have hpowerset : extra ∈ eligible.powersetCard 4 :=
    Finset.mem_powersetCard.mpr ⟨hextra, hcardExtra⟩
  rw [anchorCandidates]
  refine Finset.mem_image.mpr ⟨extra, hpowerset, ?_⟩
  exact Finset.union_sdiff_of_subset hreq

/-- Ordered checked rows exhaust every mask of the corresponding anchor shape. -/
theorem orderedRows_complete {a : Anchor13} {rows : List (Nat × Nat)}
    (horder : familyOrderOK rows = true)
    (hshape : ∀ row ∈ rows, candidateShapeOK a row.1 = true)
    {m : Nat} (hm : candidateShapeOK a m = true) : ∃ f, (m, f) ∈ rows := by
  rw [familyOrderOK, Bool.and_eq_true] at horder
  have hlen : rows.length = 7315 := of_decide_eq_true horder.1
  have hchain : rows.IsChain (fun x y => x.1 < y.1) := by
    exact of_decide_eq_true (show StrictKeys rows = true from horder.2)
  have hkeys : (rows.map Prod.fst).Nodup := by
    have hp : (rows.map Prod.fst).Pairwise (fun x y => x < y) := by
      rw [List.pairwise_map]
      exact hchain.pairwise
    exact hp.nodup
  let rowSets : Finset (Finset V13) :=
    (rows.map Prod.fst).toFinset.image maskSet13
  have hrowSetsCard : rowSets.card = 7315 := by
    change ((rows.map Prod.fst).toFinset.image maskSet13).card = 7315
    rw [Finset.card_image_iff.mpr, List.toFinset_card_of_nodup hkeys, List.length_map,
      hlen]
    intro x hx y hy hxy
    apply maskSet13_injective_bounded
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact (of_decide_eq_true (hshape row hrow)).1
    · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
      exact (of_decide_eq_true (hshape row hrow)).1
    · exact hxy
  have hsubset : rowSets ⊆ anchorCandidates a := by
    intro S hS
    obtain ⟨key, hkey, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hkey)
    exact candidateShapeOK_sound (hshape row hrow)
  have heq : rowSets = anchorCandidates a := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hrowSetsCard, anchorCandidates_card]
  have hmSet : maskSet13 m ∈ rowSets := by
    rw [heq]
    exact candidateShapeOK_sound hm
  obtain ⟨key, hkey, hmask⟩ := Finset.mem_image.mp hmSet
  obtain ⟨row, hrow, hrowkey⟩ := List.mem_map.mp (List.mem_toFinset.mp hkey)
  refine ⟨row.2, ?_⟩
  have hboundM : m < 2 ^ 26 := (of_decide_eq_true hm).1
  have hboundKey : key < 2 ^ 26 := by
    rw [← hrowkey]
    exact (of_decide_eq_true (hshape row hrow)).1
  have hkeyeq : key = m := maskSet13_injective_bounded hboundKey hboundM hmask
  have hr1 : row.1 = m := hrowkey.trans hkeyeq
  simpa [← hr1] using hrow

/-- Candidate masks for one anchor in deterministic increasing order. -/
private def candidateMasksFor13 (a : Anchor13) : List Nat :=
  ((anchorCandidates a).image setMask13).sort (· ≤ ·)

/-- Candidate masks in a deterministic increasing order, retaining anchor multiplicity. -/
private def candidateMasks13 : List Nat := (anchors13.map candidateMasksFor13).flatten

/-- Validate rows without trusting a generator: candidates must be exactly the generated list. -/
private def certificateOK13 (rows : List (Nat × Nat)) : Bool :=
  decide (rows.map Prod.fst = candidateMasks13) && rows.all rowOK

#print axioms neighbors13_spec
#print axioms code13_injective

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
