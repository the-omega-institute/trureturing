/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleySparseWeightSix
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleySparseWeightSix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The weight-six Paley certificate excludes norm four in the P48p odd neighbor. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pPaleySparseCheck
import OmegaBuild.Commands

/-!
# The weight-six Paley certificate

A normalized input has three fixed anchor coordinates and three signed free
slopes. The checker sums the six character contributions in each output
coordinate and stops at the seventh nonzero coordinate. Each finite check
fixes the two anchor signs, the first free slope, and its sign.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleySparseWeightSix

open scoped Matrix
open P48pTernaryPaleyGraph (F3 paleyC)
open P48pPaleySparseCheck (Entry paleyRowWeight anchoredSupports mem_anchoredSupports_iff
  paley_small_support_certificate_of_weight_six)
open P48pOddNeighbor (RatRow oddNeighbor cataloguePairing)
open P48pPaleyNormFour (norm_ne_four_of_paley_small_support)

open private paleyCComputable paleyC_eq_computable from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pTernaryPaleyGraph
open private anchorWord exactSignedSubsets freeSlopes freeSlopes_nodup mem_freeSlopes_iff
  signPairs signPair_cases from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pPaleySparseCheck

/-- One character lookup, with the nonzero squares modulo 23 stored as set bits. -/
private def characterResidue (i j : Fin 24) : ℕ :=
  if i.val = j.val then 0
  else if i.val = 23 then 2
  else if j.val = 23 then 1
  else if (340830 : ℕ).testBit ((j.val + 23 - i.val) % 23) then 1 else 2

set_option maxHeartbeats 6000000 in
private theorem characterResidue_cast (i j : Fin 24) :
    (characterResidue i j : F3) = paleyC i j := by
  rw [paleyC_eq_computable]
  have row : List.ofFn (fun col : Fin 24 => (characterResidue i col : F3)) =
      List.ofFn (fun col : Fin 24 => paleyCComputable i col) := by
    fin_cases i <;> decide +kernel
  exact congrFun (List.ofFn_injective row) j

private def sparseRow : List Entry → Fin 24 → F3
  | [] => 0
  | e :: es => Pi.single e.1 e.2 + sparseRow es

private theorem sparseRow_apply (entries : List Entry) (j : Fin 24) :
    sparseRow entries j = ((entries.filter (fun e => e.1 = j)).map Prod.snd).sum := by
  induction entries with
  | nil => simp [sparseRow]
  | cons e es ih =>
      rcases e with ⟨d, c⟩
      by_cases h : d = j
      · subst j
        simp [sparseRow, Pi.add_apply, Pi.single_apply, ih]
      · simp [sparseRow, Pi.add_apply, Pi.single_apply, ih, h, Ne.symm h]

private theorem sparseRow_ne_zero_iff (entries : List Entry)
    (hdistinct : (entries.map Prod.fst).Nodup)
    (hnonzero : ∀ e ∈ entries, e.2 ≠ 0) (j : Fin 24) :
    sparseRow entries j ≠ 0 ↔ j ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [sparseRow]
  | cons e es ih =>
      rcases e with ⟨d, c⟩
      change (d :: es.map Prod.fst).Nodup at hdistinct
      obtain ⟨hd, hds⟩ := List.nodup_cons.mp hdistinct
      have hc : c ≠ 0 := hnonzero (d, c) List.mem_cons_self
      have ht := ih hds (fun e he => hnonzero e (List.mem_cons_of_mem _ he))
      by_cases h : d = j
      · subst j
        have hz : sparseRow es d = 0 := by
          by_contra hn
          exact hd (ht.mp hn)
        simp [sparseRow, Pi.add_apply, Pi.single_apply, hz, hc]
      · simpa [sparseRow, Pi.add_apply, Pi.single_apply, h, Ne.symm h] using ht

private theorem hammingNorm_sparseRow (entries : List Entry)
    (hdistinct : (entries.map Prod.fst).Nodup)
    (hnonzero : ∀ e ∈ entries, e.2 ≠ 0) :
    hammingNorm (sparseRow entries) = entries.length := by
  have hSupport : Finset.univ.filter (fun j => sparseRow entries j ≠ 0) =
      (entries.map Prod.fst).toFinset := by
    ext j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset] using
      sparseRow_ne_zero_iff entries hdistinct hnonzero j
  rw [hammingNorm, hSupport, List.toFinset_card_of_nodup hdistinct, List.length_map]

private def sparseSum (j : Fin 24) : List Entry → ℕ
  | [] => 0
  | e :: es => e.2.val * characterResidue e.1 j + sparseSum j es

private theorem sparseSum_cast (entries : List Entry) (j : Fin 24) :
    (sparseSum j entries : F3) = (sparseRow entries ᵥ* paleyC) j := by
  induction entries with
  | nil => simp [sparseSum, sparseRow]
  | cons e es ih =>
      rw [sparseSum, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val,
        characterResidue_cast, ih, sparseRow, Matrix.add_vecMul, Matrix.single_vecMul] <;> rfl

private def reachesNonzero (entries : List Entry) : ℕ → List (Fin 24) → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | k + 1, j :: js =>
      if sparseSum j entries % 3 = 0 then reachesNonzero entries (k + 1) js
      else reachesNonzero entries k js

private theorem reachesNonzero_sound (entries : List Entry) (k : ℕ) (cols : List (Fin 24))
    (h : reachesNonzero entries k cols = true) :
    k ≤ (cols.filter (fun j => (sparseRow entries ᵥ* paleyC) j ≠ 0)).length := by
  induction cols generalizing k with
  | nil => cases k <;> simp [reachesNonzero] at h ⊢
  | cons j js ih =>
      cases k with
      | zero => exact Nat.zero_le _
      | succ k =>
          have hz : (sparseRow entries ᵥ* paleyC) j = 0 ↔ sparseSum j entries % 3 = 0 := by
            rw [← sparseSum_cast, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
          by_cases hj : sparseSum j entries % 3 = 0
          · have ht := ih (k + 1) (by simpa only [reachesNonzero, if_pos hj] using h)
            simpa [hz.mpr hj] using ht
          · have ht := ih k (by simpa only [reachesNonzero, if_neg hj] using h)
            have hj' : (sparseRow entries ᵥ* paleyC) j ≠ 0 := fun he => hj (hz.mp he)
            simpa [hj'] using Nat.succ_le_succ ht

private theorem hammingNorm_eq_filter_length (a : Fin 24 → F3) :
    hammingNorm a = ((List.finRange 24).filter (fun j => a j ≠ 0)).length := by
  rw [← List.toFinset_card_of_nodup
    ((List.nodup_finRange 24).filter (fun j => decide (a j ≠ 0)))]
  unfold hammingNorm
  congr 1
  ext j
  simp

private theorem exactSignedSubsets_shape (slopes : List (Fin 24)) (k : ℕ)
    (extra : List Entry) (h : extra ∈ exactSignedSubsets slopes k) :
    extra.length = k ∧ (extra.map Prod.fst).Sublist slopes ∧ ∀ e ∈ extra, e.2 ≠ 0 := by
  induction slopes generalizing k extra with
  | nil =>
      cases k with
      | zero =>
          have he : extra = [] := by simpa [exactSignedSubsets] using h
          subst extra
          simp
      | succ k => simp [exactSignedSubsets] at h
  | cons d ds ih =>
      cases k with
      | zero =>
          have he : extra = [] := by simpa [exactSignedSubsets] using h
          subst extra
          simp
      | succ k =>
          have hcons (c : F3) (hc : c ≠ 0) (es : List Entry)
              (he : es ∈ exactSignedSubsets ds k) :
              ((d, c) :: es).length = k + 1 ∧
                (((d, c) :: es).map Prod.fst).Sublist (d :: ds) ∧
                ∀ e ∈ (d, c) :: es, e.2 ≠ 0 := by
            obtain ⟨hlen, hsub, hn⟩ := ih k es he
            refine ⟨congrArg Nat.succ hlen, List.Sublist.cons_cons d hsub, ?_⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact hc
            · exact hn e he
          simp only [exactSignedSubsets, List.mem_append, List.mem_map] at h
          rcases h with (⟨es, he, rfl⟩ | ⟨es, he, rfl⟩) | he
          · exact hcons 1 (by decide +kernel) es he
          · exact hcons 2 (by decide +kernel) es he
          · obtain ⟨hlen, hsub, hn⟩ := ih (k + 1) extra he
            exact ⟨hlen, List.Sublist.cons d hsub, hn⟩

private def anchorEntries (s : F3 × F3) (extra : List Entry) : List Entry :=
  (23, 1) :: (0, s.1) :: (1, s.2) :: extra

private theorem anchorEntries_row (s : F3 × F3) (extra : List Entry)
    (hsub : (extra.map Prod.fst).Sublist freeSlopes) :
    sparseRow (anchorEntries s extra) = anchorWord s extra := by
  have hzero (d : Fin 24) (hd : d ∉ freeSlopes) : sparseRow extra d = 0 := by
    rw [sparseRow_apply]
    have hempty : extra.filter (fun e => e.1 = d) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      simp only [decide_eq_true_eq]
      intro heq
      apply hd
      rw [← heq]
      exact hsub.subset (List.mem_map_of_mem he)
    simp [hempty]
  have h23 : (23 : Fin 24) ∉ freeSlopes := fun h => ((mem_freeSlopes_iff 23).mp h).1 rfl
  have h0 : (0 : Fin 24) ∉ freeSlopes := fun h => ((mem_freeSlopes_iff 0).mp h).2.1 rfl
  have h1 : (1 : Fin 24) ∉ freeSlopes := fun h => ((mem_freeSlopes_iff 1).mp h).2.2 rfl
  funext j
  by_cases hj23 : j = 23
  · subst j
    simp [anchorEntries, anchorWord, sparseRow, Pi.add_apply, Pi.single_apply, hzero 23 h23]
  by_cases hj0 : j = 0
  · subst j
    simp [anchorEntries, anchorWord, sparseRow, Pi.add_apply, Pi.single_apply, hzero 0 h0]
  by_cases hj1 : j = 1
  · subst j
    simp [anchorEntries, anchorWord, sparseRow, Pi.add_apply, Pi.single_apply, hzero 1 h1]
  simp [anchorEntries, anchorWord, sparseRow, Pi.add_apply, Pi.single_apply, hj23, hj0, hj1,
    Ne.symm hj23, Ne.symm hj0, Ne.symm hj1, sparseRow_apply]

private theorem anchorEntries_weight (s : F3 × F3) (hs : s ∈ signPairs) (extra : List Entry)
    (he : extra ∈ exactSignedSubsets freeSlopes 3) :
    hammingNorm (sparseRow (anchorEntries s extra)) = 6 := by
  obtain ⟨hlen, hsub, hn⟩ := exactSignedSubsets_shape freeSlopes 3 extra he
  have hm (d : Fin 24) (hd : d ∈ extra.map Prod.fst) :=
    (mem_freeSlopes_iff d).mp (hsub.subset hd)
  have h23 : (23 : Fin 24) ∉ extra.map Prod.fst := fun h => (hm 23 h).1 rfl
  have h0 : (0 : Fin 24) ∉ extra.map Prod.fst := fun h => (hm 0 h).2.1 rfl
  have h1 : (1 : Fin 24) ∉ extra.map Prod.fst := fun h => (hm 1 h).2.2 rfl
  have hdistinct : ((anchorEntries s extra).map Prod.fst).Nodup := by
    have ht := hsub.nodup freeSlopes_nodup
    simp [anchorEntries, List.nodup_cons, h23, h0, h1, ht]
  have hsigns : s.1 ≠ 0 ∧ s.2 ≠ 0 := by
    rcases signPair_cases s hs with rfl | rfl | rfl | rfl <;> decide +kernel
  have hnonzero : ∀ e ∈ anchorEntries s extra, e.2 ≠ 0 := by
    intro e he'
    simp only [anchorEntries, List.mem_cons] at he'
    rcases he' with rfl | rfl | rfl | he'
    · exact one_ne_zero
    · exact hsigns.1
    · exact hsigns.2
    · exact hn e he'
  rw [hammingNorm_sparseRow _ hdistinct hnonzero]
  simp [anchorEntries, hlen]

/-- Find the first chosen slope and the suffix used to generate the other two. -/
private theorem exactSignedSubsets_three_cover (slopes : List (Fin 24)) (extra : List Entry)
    (h : extra ∈ exactSignedSubsets slopes 3) :
    ∃ (i : ℕ), i < slopes.length ∧ ∃ (d : Fin 24) (tail : List (Fin 24)),
      slopes.drop i = d :: tail ∧ ∃ es ∈ exactSignedSubsets tail 2,
        extra = (d, 1) :: es ∨ extra = (d, 2) :: es := by
  induction slopes with
  | nil => simp [exactSignedSubsets] at h
  | cons d ds ih =>
      simp only [exactSignedSubsets, List.mem_append, List.mem_map] at h
      rcases h with (⟨es, he, rfl⟩ | ⟨es, he, rfl⟩) | he
      · exact ⟨0, Nat.zero_lt_succ _, d, ds, rfl, es, he, Or.inl rfl⟩
      · exact ⟨0, Nat.zero_lt_succ _, d, ds, rfl, es, he, Or.inr rfl⟩
      · obtain ⟨i, hi, e, tail, hdrop, es, hes, hshape⟩ := ih he
        exact ⟨i + 1, Nat.succ_lt_succ hi, e, tail, by simpa using hdrop, es, hes, hshape⟩

private def slopeCheck (s : F3 × F3) (i : Fin 21) (c : F3) : Bool :=
  match freeSlopes.drop i.val with
  | [] => true
  | d :: tail => (exactSignedSubsets tail 2).all (fun es =>
      reachesNonzero (anchorEntries s ((d, c) :: es)) 7 (List.finRange 24))

-- Each sign and slope branch is a separate closed kernel reduction.
set_option maxHeartbeats 6000000 in
private theorem slopeCheck_11 (i : Fin 21) :
    slopeCheck (1, 1) i 1 = true ∧ slopeCheck (1, 1) i 2 = true := by
  fin_cases i <;> constructor <;> decide +kernel

set_option maxHeartbeats 6000000 in
private theorem slopeCheck_12 (i : Fin 21) :
    slopeCheck (1, 2) i 1 = true ∧ slopeCheck (1, 2) i 2 = true := by
  fin_cases i <;> constructor <;> decide +kernel

set_option maxHeartbeats 6000000 in
private theorem slopeCheck_21 (i : Fin 21) :
    slopeCheck (2, 1) i 1 = true ∧ slopeCheck (2, 1) i 2 = true := by
  fin_cases i <;> constructor <;> decide +kernel

set_option maxHeartbeats 6000000 in
private theorem slopeCheck_22 (i : Fin 21) :
    slopeCheck (2, 2) i 1 = true ∧ slopeCheck (2, 2) i 2 = true := by
  fin_cases i <;> constructor <;> decide +kernel

private theorem slopeCheck_true (s : F3 × F3) (hs : s ∈ signPairs) (i : Fin 21) :
    slopeCheck s i 1 = true ∧ slopeCheck s i 2 = true := by
  rcases signPair_cases s hs with rfl | rfl | rfl | rfl
  · exact slopeCheck_11 i
  · exact slopeCheck_12 i
  · exact slopeCheck_21 i
  · exact slopeCheck_22 i

private theorem anchorEntries_check (s : F3 × F3) (hs : s ∈ signPairs) (extra : List Entry)
    (he : extra ∈ exactSignedSubsets freeSlopes 3) :
    reachesNonzero (anchorEntries s extra) 7 (List.finRange 24) = true := by
  obtain ⟨i, hi, d, tail, hdrop, es, hes, hshape⟩ :=
    exactSignedSubsets_three_cover freeSlopes extra he
  have hlen : freeSlopes.length = 21 := by decide +kernel
  let idx : Fin 21 := ⟨i, by simpa only [hlen] using hi⟩
  have hdrop' : freeSlopes.drop idx.val = d :: tail := hdrop
  obtain ⟨hpos, hneg⟩ := slopeCheck_true s hs idx
  simp only [slopeCheck, hdrop'] at hpos hneg
  rcases hshape with rfl | rfl
  · exact (List.all_eq_true.mp hpos) es hes
  · exact (List.all_eq_true.mp hneg) es hes

/-- Every normalized row in the weight-six branch has total weight above twelve. -/
theorem anchored_weight_six_sparse {a : Fin 24 → F3}
    (ha : a ∈ anchoredSupports 3) : 12 < paleyRowWeight a := by
  obtain ⟨s, hs, extra, he, rfl⟩ := (mem_anchoredSupports_iff 3 a).mp ha
  have hcheck := anchorEntries_check s hs extra he
  have hout := reachesNonzero_sound _ _ _ hcheck
  rw [← hammingNorm_eq_filter_length] at hout
  have hin := anchorEntries_weight s hs extra he
  have hsub := (exactSignedSubsets_shape freeSlopes 3 extra he).2.1
  rw [anchorEntries_row s extra hsub] at hin hout
  unfold paleyRowWeight
  omega

/-- The finite check completes the certificate for every nonzero input of weight at most six. -/
theorem paley_small_support_certificate_sparse :
    ∀ a : Fin 24 → F3, a ≠ 0 → hammingNorm a ≤ 6 →
      12 < paleyRowWeight a :=
  paley_small_support_certificate_of_weight_six (fun _ ha => anchored_weight_six_sparse ha)

/-- The actual P48p odd neighbor contains no vector of catalogue squared norm four. -/
theorem norm_ne_four (x : RatRow) (hx : x ∈ oddNeighbor) : cataloguePairing x x ≠ 4 :=
  norm_ne_four_of_paley_small_support paley_small_support_certificate_sparse x hx

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleySparseWeightSix
