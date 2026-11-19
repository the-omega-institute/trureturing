import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.List.OfFn

/-! The signed path test reconstructs the midpoint of each compressed edge. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion

open BalancedCriticalSpectrum (Q IsBalanced)
open Q9SeventyTwoSignedSearch (modelEdges signed_middle_unique)
open Q9EightCubicGraphCertificate (modelAdj)
open BalancedCubeLowerBound (coordinateSlice)
open private middle_of_signed_path from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)

local notation "flip" => BalancedCriticalSpectrum.flip

private def tests (x y : Q 9) (product : ℤ) (i j : Fin 9) : Bool :=
  decide (flip (flip x i) j = y) &&
    decide (truePrefixSign x i * truePrefixSign (flip x i) j = product)

private theorem tests_iff (x y : Q 9) (product : ℤ) (i j : Fin 9) :
    tests x y product i j = true ↔
      flip (flip x i) j = y ∧ truePrefixSign x i * truePrefixSign (flip x i) j = product := by
  simp [tests]

private def firstFlip (x y : Q 9) (product : ℤ) : Option (Fin 9) :=
  (List.finRange 9).find? fun i => (List.finRange 9).any (tests x y product i)

private theorem firstFlip_eq {x y : Q 9} (hxy : x ≠ y) {product : ℤ}
    {i j : Fin 9} (h : tests x y product i j = true) : firstFlip x y product = some i := by
  unfold firstFlip
  cases hfind : (List.finRange 9).find? (fun k => (List.finRange 9).any (tests x y product k)) with
  | none =>
    exact (List.find?_eq_none.mp hfind i (List.mem_finRange i)
      (List.any_eq_true.mpr ⟨j, List.mem_finRange j, h⟩)).elim
  | some k =>
    have hk : (List.finRange 9).any (tests x y product k) = true :=
      List.find?_some (p := fun a => (List.finRange 9).any (tests x y product a)) hfind
    obtain ⟨l, _, hl⟩ := List.any_eq_true.mp hk
    obtain ⟨hy, hs⟩ := (tests_iff x y product i j).mp h
    obtain ⟨hy', hs'⟩ := (tests_iff x y product k l).mp hl
    exact congrArg some (signed_middle_unique hxy hy hy' (hs.trans hs'.symm)).symm

/-- The midpoint and its signing value are computed from the two high
vertices and their signed values. -/
def signedMiddle (x y : Q 9) (a b : ℤ) : Option (Q 9 × ℤ) :=
  (firstFlip x y (a * b)).map fun i => (flip x i, a * truePrefixSign x i)

/-- Every realized two-step path with distinct endpoints and unit values
is recovered by the signed midpoint computation. -/
theorem signedMiddle_of_path {x y m : Q 9} {z : Q 9 → ℤ} (hxy : x ≠ y)
    (hxm : (hypercube 9).Adj x m) (hmy : (hypercube 9).Adj m y)
    (hx : z x = 1 ∨ z x = -1) (hm : z m = 1 ∨ z m = -1)
    (h : ∀ u (i : Fin 9), (u = x ∧ flip u i = m) ∨ (u = m ∧ flip u i = y) →
      truePrefixSign u i = z u * z (flip u i)) :
    signedMiddle x y (z x) (z y) = some (m, z m) := by
  obtain ⟨i, j, hi, hj, hs, hz⟩ := middle_of_signed_path hxm hmy hx hm h
  have htest : tests x y (z x * z y) i j = true := by
    apply (tests_iff ..).mpr
    rw [← hi]
    exact ⟨hj.symm, hs⟩
  simp only [signedMiddle, firstFlip_eq hxy htest, Option.map_some, ← hi, ← hz]

#print axioms signedMiddle_of_path

private def signedRecords (wagner : Bool) (p : Fin 8 → Q 9) (s : Fin 8 → ℤ) :
    List (Q 9 × ℤ) :=
  List.ofFn (fun i => (p i, s i)) ++
    (List.finRange 8).flatMap fun i => (List.finRange 8).filterMap fun j =>
      if i < j ∧ modelAdj wagner i j = true then signedMiddle (p i) (p j) (s i) (s j)
      else none

private def valueIn (entries : List (Q 9 × ℤ)) (x : Q 9) : ℤ :=
  ((entries.find? fun e => decide (e.1 = x)).map Prod.snd).getD 0

/-- Form the full signed vector by computing the high and middle records in
the first half and applying the eigenvector row to obtain the second half. -/
def complete (wagner : Bool) (p : Fin 8 → Q 9) (s : Fin 8 → ℤ) (x : Q 9) : ℤ :=
  let value := valueIn (signedRecords wagner p s)
  if x 0 = false then value x
  else
    let y := flip x 0
    3 * value y -
      ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * value (flip y i)

/-- Every normalized signed support with its realized model incidences is
recovered exactly by the finite computation on the high vertices. -/
theorem complete_eq_of_actual {U : Finset (Q 9)} {wagner : Bool}
    (p : Fin 8 ↪ Q 9)
    (m : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9)
    (z : Q 9 → ℤ)
    (hU : coordinateSlice U false = Finset.univ.map p ∪ Finset.univ.map m)
    (hm : ∀ e k, (hypercube 9).Adj (m e) (p k) ↔ k = e.val.1 ∨ k = e.val.2)
    (hunit : ∀ x ∈ U, z x = 1 ∨ z x = -1) (hzero : ∀ x ∉ U, z x = 0)
    (hsign : ∀ x ∈ U, ∀ i : Fin 9, flip x i ∈ U →
      truePrefixSign x i = z x * z (flip x i))
    (hrow : ∀ y, z (flip y 0) =
      3 * z y - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * z (flip y i)) :
    complete wagner p (fun k => z (p k)) = z := by
  let entries := signedRecords wagner p (fun k => z (p k))
  have highMem (k : Fin 8) : p k ∈ Finset.univ.map p :=
    Finset.mem_map.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have midMem (e : (modelEdges wagner : Set (Fin 8 × Fin 8))) :
      m e ∈ Finset.univ.map m := Finset.mem_map.mpr ⟨e, Finset.mem_univ e, rfl⟩
  have memU {x : Q 9} (hx : x ∈ Finset.univ.map p ∪ Finset.univ.map m) : x ∈ U :=
    (Finset.mem_filter.mp (hU.symm ▸ hx)).1
  have actualMid (e : (modelEdges wagner : Set (Fin 8 × Fin 8))) :
      signedMiddle (p e.val.1) (p e.val.2) (z (p e.val.1)) (z (p e.val.2)) =
        some (m e, z (m e)) := by
    have hx := memU (Finset.mem_union_left _ (highMem e.val.1))
    have hy := memU (Finset.mem_union_left _ (highMem e.val.2))
    have hv := memU (Finset.mem_union_right _ (midMem e))
    apply signedMiddle_of_path
      (fun he => (Finset.mem_filter.mp e.property).2.1.ne (p.injective he))
      ((hm e e.val.1).mpr (Or.inl rfl)).symm ((hm e e.val.2).mpr (Or.inr rfl))
      (hunit _ hx) (hunit _ hv)
    rintro u i (⟨rfl, hi⟩ | ⟨rfl, hi⟩)
    · exact hsign _ hx _ (hi.symm ▸ hv)
    · exact hsign _ hv _ (hi.symm ▸ hy)
  have midRecord (i j : Fin 8) (hij : i < j ∧ modelAdj wagner i j = true) :
      ∃ val : Q 9 × ℤ,
        signedMiddle (p i) (p j) (z (p i)) (z (p j)) = some val ∧ val.2 = z val.1 := by
    let e : (modelEdges wagner : Set (Fin 8 × Fin 8)) :=
      ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
    exact ⟨(m e, z (m e)), actualMid e, rfl⟩
  have recordCorrect (v : Q 9 × ℤ) (hv : v ∈ entries) : v.2 = z v.1 := by
    change v ∈ signedRecords wagner p (fun k => z (p k)) at hv
    rw [signedRecords, List.mem_append] at hv
    rcases hv with hv | hv
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      rfl
    · obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hv
      split at hj
      · rename_i he
        obtain ⟨v', hs, hval⟩ := midRecord i j he
        rw [hs, Option.some.injEq] at hj
        exact hj ▸ hval
      · simp at hj
  have recordsCover (x : Q 9) (hx : x ∈ coordinateSlice U false) : (x, z x) ∈ entries := by
    rw [hU] at hx
    change (x, z x) ∈ signedRecords wagner p (fun k => z (p k))
    rw [signedRecords, List.mem_append]
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hx
      apply Or.inr
      refine List.mem_flatMap.mpr ⟨e.val.1, List.mem_finRange _, ?_⟩
      refine List.mem_filterMap.mpr ⟨e.val.2, List.mem_finRange _, ?_⟩
      rw [ite_eq_left (Finset.mem_filter.mp e.property).2]
      exact actualMid e
  have valueEq (x : Q 9) (hx : x 0 = false) : valueIn entries x = z x := by
    unfold valueIn
    cases hfind : entries.find? (fun v => decide (v.1 = x)) with
    | none =>
      have hnot : x ∉ U := by
        intro hxU
        exact List.find?_eq_none.mp hfind (x, z x)
          (recordsCover x (Finset.mem_filter.mpr ⟨hxU, hx⟩)) (by simp)
      exact (hzero x hnot).symm
    | some v =>
      have hv : v.1 = x :=
        of_decide_eq_true (List.find?_some (p := fun a : Q 9 × ℤ => decide (a.1 = x)) hfind)
      exact (recordCorrect v (List.mem_of_find?_eq_some hfind)).trans (congrArg z hv)
  funext x
  change (if x 0 = false then valueIn entries x
    else let y := flip x 0
         3 * valueIn entries y -
           ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * valueIn entries (flip y i))
      = z x
  by_cases hx : x 0 = false
  · rw [ite_eq_left hx, valueEq x hx]
  · rw [ite_eq_right hx]
    let y := flip x 0
    have hy : y 0 = false := by
      cases hb : x 0
      · exact (hx hb).elim
      · simp [y, hb]
    have hs :
        (∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * valueIn entries (flip y i)) =
          ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * z (flip y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [valueEq]
      exact (Function.update_of_ne (Finset.mem_erase.mp hi).1.symm _ _).trans hy
    change 3 * valueIn entries y - _ = z x
    rw [valueEq y hy, hs, ← hrow, BalancedCriticalSpectrum.flip_flip]

#print axioms complete_eq_of_actual

private def unitSign (bit : Bool) : ℤ := if bit then -1 else 1

section

local instance : DecidableRel (hypercube 9).Adj := fun x y =>
  inferInstanceAs (Decidable (hammingDist x y = 1))

/-- Check that the signs give a geometrically allowed midpoint on every
compressed edge of the normalized half. -/
def survives (wagner : Bool) (p : Fin 8 → Q 9) (bits : Fin 8 → Bool) : Bool :=
  (List.finRange 8).all fun i =>
    (List.finRange 8).all fun j =>
      if i < j ∧ modelAdj wagner i j = true then
        match signedMiddle (p i) (p j) (unitSign (bits i)) (unitSign (bits j)) with
        | none => false
        | some (m, _) =>
          !m 0 && (List.finRange 8).all fun k =>
            decide ((hypercube 9).Adj m (p k) ↔ k = i ∨ k = j)
      else true

private def permits (p : Fin 8 → Q 9) (i j : Fin 8) (different : Bool) : Bool :=
  match firstFlip (p i) (p j) (unitSign different) with
  | none => false
  | some a =>
    let mid := flip (p i) a
    !mid 0 && (List.finRange 8).all fun k =>
      decide ((hypercube 9).Adj mid (p k) ↔ k = i ∨ k = j)

/-- A fixed placement supplies two tests per compressed edge, one for
equal endpoint signs and one for opposite signs. -/
def signConstraints (wagner : Bool) (p : Fin 8 → Q 9) :
    List (Fin 8 × Fin 8 × Bool × Bool) :=
  (List.finRange 8).flatMap fun i => (List.finRange 8).filterMap fun j =>
    if i < j ∧ modelAdj wagner i j = true then
      some (i, j, permits p i j false, permits p i j true)
    else none

/-- Screening a signing uses only the parity on each pair of endpoints.
The midpoint tests can be shared across all assignments to the highs. -/
theorem survives_eq_all_signConstraints (wagner : Bool) (p : Fin 8 → Q 9)
    (bits : Fin 8 → Bool) :
    survives wagner p bits =
      (signConstraints wagner p).all (fun row =>
        if bits row.1 != bits row.2.1 then row.2.2.2 else row.2.2.1) := by
  have parity_sign (a b : Bool) : unitSign (a != b) = unitSign a * unitSign b := by
    cases a <;> cases b <;> decide +kernel
  rw [Bool.eq_iff_iff]
  unfold survives signConstraints
  simp only [List.all_eq_true, List.mem_flatMap, List.mem_filterMap]
  constructor
  · intro h row hrow
    obtain ⟨i, hi, j, hj, hrow⟩ := hrow
    split at hrow
    · rename_i hij
      rw [Option.some.injEq] at hrow
      subst row
      have hpath := h i hi j hj
      rw [ite_eq_left hij] at hpath
      change (if bits i != bits j then permits p i j true else permits p i j false) = true
      have he :
          (if bits i != bits j then permits p i j true else permits p i j false) =
            permits p i j (bits i != bits j) := by
        cases hbits : (bits i != bits j) <;> rfl
      rw [he, permits, parity_sign]
      cases hf : firstFlip (p i) (p j) (unitSign (bits i) * unitSign (bits j)) <;>
        simpa [signedMiddle, hf] using hpath
    · simp at hrow
  · intro h i hi j hj
    split
    · rename_i hij
      have ha := h (i, j, permits p i j false, permits p i j true)
        ⟨i, hi, j, hj, by rw [ite_eq_left hij]⟩
      change (if bits i != bits j then permits p i j true else permits p i j false) = true at ha
      have he :
          (if bits i != bits j then permits p i j true else permits p i j false) =
            permits p i j (bits i != bits j) := by
        cases hbits : (bits i != bits j) <;> rfl
      rw [he, permits, parity_sign] at ha
      cases hf : firstFlip (p i) (p j) (unitSign (bits i) * unitSign (bits j)) <;>
        simpa [signedMiddle, hf] using ha
    · rfl

end

/-- A normalized high-vertex signing has seven free bits. -/
def signsFromMask (n : Fin 128) : Fin 8 → Bool :=
  Fin.cases false (cubeBitVec 7 (BitVec.ofFin n))

private theorem exists_mask (bits : Fin 8 → Bool) (hroot : bits 0 = false) :
    ∃ n : Fin 128, signsFromMask n = bits := by
  let tail := (cubeBitVec 7).symm (fun j : Fin 7 => bits j.succ)
  refine ⟨tail.toFin, ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hroot.symm
  · exact congrFun ((cubeBitVec 7).apply_symm_apply (fun j : Fin 7 => bits j.succ)) j

private def refineMasks : List (Fin 8 × Fin 8 × Bool × Bool) → List (Fin 128) →
    List (Fin 128)
  | [], masks => masks
  | (i, j, same, different) :: tail, masks =>
    if same then
      if different then refineMasks tail masks
      else refineMasks tail (masks.filter fun n => signsFromMask n i == signsFromMask n j)
    else
      if different then refineMasks tail (masks.filter fun n => signsFromMask n i != signsFromMask n j)
      else []

private theorem mem_refineMasks (rows : List (Fin 8 × Fin 8 × Bool × Bool))
    (masks : List (Fin 128)) (n : Fin 128) :
    n ∈ refineMasks rows masks ↔ n ∈ masks ∧ rows.all (fun row =>
      if signsFromMask n row.1 != signsFromMask n row.2.1 then row.2.2.2 else row.2.2.1) = true := by
  induction rows generalizing masks with
  | nil => simp [refineMasks]
  | cons row rows ih =>
    obtain ⟨i, j, same, different⟩ := row
    cases same <;> cases different <;>
      simp only [refineMasks, Bool.false_eq_true, ite_false, ite_true, ih, List.all_cons,
        Bool.and_eq_true, List.mem_filter, not_false_eq_true]
    all_goals cases h : (signsFromMask n i != signsFromMask n j) <;> simp_all <;> tauto

/-- Enumerate the normalized signings of a placement, computing each
pair's midpoint tests only once. -/
def signMasks (wagner : Bool) (p : Fin 8 → Q 9) : List (Fin 128) :=
  refineMasks (signConstraints wagner p) (List.finRange 128)

/-- The enumeration contains exactly the midpoint-allowed sign codes. -/
theorem mem_signMasks (wagner : Bool) (p : Fin 8 → Q 9) (n : Fin 128) :
    n ∈ signMasks wagner p ↔ survives wagner p (signsFromMask n) = true := by
  rw [signMasks, mem_refineMasks, survives_eq_all_signConstraints]
  simp [List.mem_finRange]

private def signingCount (wagner : Bool) (pattern : Fin 5) : ℕ :=
  ((Q9SeventyTwoEmbeddingSearch.candidates wagner pattern).map fun p =>
    (signMasks wagner (cubeBitVec 9 ∘ p)).length).sum

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Evaluate the finite placement and sign search once for each root pattern.
theorem signingCount_eq (wagner : Bool) (pattern : Fin 5) :
    signingCount wagner pattern =
      (if wagner then ![0, 6, 0, 6, 0] else ![24, 6, 6, 6, 128]) pattern := by
  cases wagner <;> fin_cases pattern <;> decide +kernel

/-- Nonzero vertices of the reconstructed signed vector. -/
def support (wagner : Bool) (p : Fin 8 → Q 9) (bits : Fin 8 → Bool) : Finset (Q 9) :=
  Finset.univ.filter fun x => complete wagner p (unitSign ∘ bits) x ≠ 0

attribute [local instance] Classical.propDecidable

/-- Every actual seventy-two-vertex component with a twenty-vertex half is
covered by the geometric search and the midpoint sign filter. The first
high vertex may always be assigned sign \(+1\). -/
theorem exists_surviving_signs {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Fin 9 ≃ Fin 9) (wagner : Bool) (pattern : Fin 5)
      (p : Fin 8 ↪ Q 9) (bits : Fin 8 → Bool),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (fun i => (cubeBitVec 9).symm (p i)) ∈ Q9SeventyTwoEmbeddingSearch.candidates wagner pattern ∧
      bits 0 = false ∧ survives wagner p bits = true ∧ C.image g = support wagner p bits := by
  obtain ⟨g, σ, wagner, pattern, p, m, z, hg, hcut, hmem, hslice, hm, hu, hz, he, hw⟩ :=
    Q9SeventyTwoSignedSearch.exists_signed_candidate hC hr hb b hs
  have hslice' : coordinateSlice (C.image g) false =
      Finset.univ.map p ∪ Finset.univ.map m := by
    rw [← hslice]
    ext x
    simp only [coordinateSlice, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hzero⟩
      exact ⟨y, ⟨hy, (hcut y).mp hzero⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hzero⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, (hcut y).mpr hzero⟩
  have inU {x : Q 9} (hx : x ∈ Finset.univ.map p ∪ Finset.univ.map m) : x ∈ C.image g :=
    (Finset.mem_filter.mp (hslice'.symm ▸ hx)).1
  have high (k : Fin 8) : p k ∈ C.image g :=
    inU (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  obtain ⟨v, hvunit, hvzero, hvedge, hvrow, hvroot⟩ :
      ∃ v : Q 9 → ℤ,
        (∀ x ∈ C.image g, v x = 1 ∨ v x = -1) ∧ (∀ x ∉ C.image g, v x = 0) ∧
        (∀ x ∈ C.image g, ∀ i : Fin 9, flip x i ∈ C.image g →
          truePrefixSign x i = v x * v (flip x i)) ∧
        (∀ y, v (flip y 0) =
          3 * v y - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * v (flip y i)) ∧
        v (p 0) = 1 := by
    rcases hu _ (high 0) with hroot | hroot
    · exact ⟨z, hu, hz, he, hw, hroot⟩
    · refine ⟨fun x => -z x, ?_, ?_, ?_, ?_, by simp [hroot]⟩
      · intro x hx
        rcases hu x hx with h | h <;> simp [h]
      · intro x hx
        simp [hz x hx]
      · intro x hx i hi
        simpa using he x hx i hi
      · intro y
        change -z (flip y 0) =
          3 * (-z y) - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * (-z (flip y i))
        rw [hw y]
        simp only [mul_neg, Finset.sum_neg_distrib]
        ring
  let bits (i : Fin 8) : Bool := decide (v (p i) = -1)
  have hbits (i : Fin 8) : unitSign (bits i) = v (p i) := by
    rcases hvunit _ (high i) with h | h <;> simp [bits, unitSign, h]
  refine ⟨g, σ, wagner, pattern, p, bits, hg, hmem, by simp [bits, hvroot], ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    split
    · rename_i hij
      let e : (modelEdges wagner : Set (Fin 8 × Fin 8)) :=
        ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
      have hmemb : m e ∈ coordinateSlice (C.image g) false := by
        rw [hslice']
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩)
      obtain ⟨hmid, hmidCut⟩ := Finset.mem_filter.mp hmemb
      have hleft := (hm e i).mpr (Or.inl rfl)
      have hright := (hm e j).mpr (Or.inr rfl)
      have hpath : signedMiddle (p i) (p j) (v (p i)) (v (p j)) =
          some (m e, v (m e)) := by
        apply signedMiddle_of_path (fun h => hij.1.ne (p.injective h)) hleft.symm hright
          (hvunit _ (high i)) (hvunit _ hmid)
        rintro x k (⟨rfl, hf⟩ | ⟨rfl, hf⟩)
        · exact hvedge _ (high i) _ (hf.symm ▸ hmid)
        · exact hvedge _ hmid _ (hf.symm ▸ high j)
      rw [hbits, hbits, hpath]
      simp only [hmidCut, Bool.not_false, Bool.true_and]
      apply List.all_eq_true.mpr
      intro k _
      simpa only [decide_eq_true_eq] using hm e k
    · rfl
  · have hcomplete := complete_eq_of_actual p m v hslice' hm hvunit hvzero hvedge hvrow
    have hfun : unitSign ∘ bits = fun i => v (p i) := funext hbits
    unfold support
    rw [hfun, hcomplete]
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rcases hvunit x hx with h | h <;> simp [h]
    · intro h
      by_contra hx
      exact h (hvzero x hx)

#print axioms exists_surviving_signs

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedCompletion
