/- GID: D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation
   mirror-E: none(waiver:exact-finite-certificate)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.claim; result=D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.result; claim=D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.claim
   digest: Minimal matrices of RSK shape (8,8,1,1) cannot be Hankel. -/

/-
proof_shape: result: content
escape_witness: weightedComps_complete; insertionTableau_size
admission_basis: open-problem-resolution (#14454; Refuted)
proof_shape: insertRow_size: content; consumer: rowInsert_size
proof_shape: rowInsert_size: content; consumer: foldl_rowInsert_size
proof_shape: foldl_rowInsert_size: content; consumer: insertionTableau_size
proof_shape: insertionTableau_size: content; consumer: shape_size
proof_shape: shape_size: content; consumer: hankel_total18
proof_shape: K3_shape: bind-only; consumer: base_minimizer_exists, base_minimizer_not_hankel
proof_shape: K3_inv: bind-only; consumer: base_minimizer_not_hankel
proof_shape: hankel_reading_length: bind-only; consumer: hankel_total18
proof_shape: weightedComps_complete: content; consumer: baseChunk_complete
proof_shape: minimizer_exists: bind-only; consumer: base_minimizer_exists
proof_shape: hankel_parametrization: bind-only; consumer: base_minimizer_not_hankel
proof_shape: parameters_to_matrix: bind-only; consumer: base_of_chunk_checks
proof_shape: baseChunk_complete: content; consumer: base_of_chunk_checks
proof_shape: hankel_total18: content; consumer: base_of_chunk_checks
proof_shape: base_of_chunk_checks: content; consumer: hankel_lower_base
proof_shape: hankel_lower_base: content; consumer: base_minimizer_not_hankel
proof_shape: base_minimizer_exists: bind-only; consumer: result
proof_shape: base_minimizer_not_hankel: content; consumer: result
proof_shape: base_chunk0: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk1: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk2: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk3: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk4: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk5: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk6: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk7: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk8: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk9: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk10: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk11: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk12: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk13: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk14: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk15: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk16: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk17: bind-only; consumer: hankel_lower_base
proof_shape: base_chunk18: bind-only; consumer: hankel_lower_base
Direct frozen dependencies:
D5/S3/Constants/Moments/CoefficientNewtonSums.fullHermiteFromMoments
  statement_id: sha256:a8f034d7238c11fc1d3f6143ede10c85fcec4bbf14cb652d9a1893c8f77d2266
D5/S3/Constants/Moments/CoefficientNewtonSums.FullHermiteMatrix
  statement_id: sha256:0e0ff9a643559e003944aa927a8996549ce5dd61bced2e3bd418827d247f4ebe
D5/S3/Constants/Moments/CoefficientNewtonSums.FullHermiteMatrix.entries
  statement_id: sha256:3fbff726c30a5a1d3a1d32443a4da819abb20a25b76bc6c9635338fc1b3aa03f
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Constants.Moments.CoefficientNewtonSums

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.RSKMinimalInversionHankelRefutation

def insertRow : Nat → List Nat → List Nat × Option Nat
  | x, [] => ([x], none)
  | x, y :: ys =>
      if x < y then (x :: ys, some y)
      else
        let z := insertRow x ys
        (y :: z.1, z.2)

def rowInsert : Nat → List (List Nat) → List (List Nat)
  | x, [] => [[x]]
  | x, r :: rs =>
      let z := insertRow x r
      match z.2 with
      | none => z.1 :: rs
      | some y => z.1 :: rowInsert y rs

def insertionTableau (w : List Nat) : List (List Nat) :=
  w.foldl (fun T x => rowInsert x T) []


def readingWord {n : Nat} (M : Fin n → Fin n → Nat) : List Nat :=
  (List.finRange n).flatMap (fun i =>
    (List.finRange n).flatMap (fun j =>
      List.replicate (M i j) j.val))

def shape {n : Nat} (M : Fin n → Fin n → Nat) : List Nat :=
  (insertionTableau (readingWord M)).map List.length

private def tabSize (T : List (List Nat)) : Nat := (T.map List.length).sum

private lemma insertRow_size (x : Nat) (r : List Nat) :
    match (insertRow x r).2 with
    | none => (insertRow x r).1.length = r.length + 1
    | some _ => (insertRow x r).1.length = r.length := by
  induction r with
  | nil => simp [insertRow]
  | cons y ys ih =>
      by_cases h : x < y
      · simp only [insertRow, if_pos h, List.length_cons]
      · simp only [insertRow, if_neg h, List.length_cons]
        cases hz : (insertRow x ys).2 with
        | none =>
            have hi := ih
            simp [hz] at hi ⊢
            omega
        | some z =>
            have hi := ih
            simp [hz] at hi ⊢
            exact hi

private lemma rowInsert_size (x : Nat) (T : List (List Nat)) : tabSize (rowInsert x T) = tabSize T + 1 := by
  induction T generalizing x with
  | nil => simp [rowInsert, tabSize]
  | cons r rs ih =>
      unfold rowInsert
      cases hz : insertRow x r with
      | mk r' b =>
          cases hb : b with
          | none =>
              simp only [tabSize, List.map_cons, List.sum_cons]
              have hlen : r'.length = r.length + 1 := by
                simpa [hz, hb] using (insertRow_size x r)
              simp [hlen]
              omega
          | some y =>
              simp only [tabSize, List.map_cons, List.sum_cons]
              have hlen : r'.length = r.length := by
                simpa [hz, hb] using (insertRow_size x r)
              have htail := ih y
              change r'.length + tabSize (rowInsert y rs) = r.length + tabSize rs + 1
              rw [hlen, htail]
              omega

private lemma foldl_rowInsert_size (w : List Nat) (T : List (List Nat)) :
    tabSize (w.foldl (fun T x => rowInsert x T) T) = tabSize T + w.length := by
  induction w generalizing T with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, rowInsert_size]
      omega

private lemma insertionTableau_size (w : List Nat) : tabSize (insertionTableau w) = w.length := by
  simpa [insertionTableau, tabSize] using (foldl_rowInsert_size w [])

private lemma shape_size {n : Nat} (M : Fin n → Fin n → Nat) : (shape M).sum = (readingWord M).length := by
  simpa [shape, tabSize] using insertionTableau_size (readingWord M)

def inv {n : Nat} (M : Fin n → Fin n → Nat) : Nat :=
  ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
    if i < k ∧ l < j then M i j * M k l else 0

def IsMinimal {n : Nat} (lam : List Nat) (M : Fin n → Fin n → Nat) : Prop :=
  shape M = lam ∧ ∀ M' : Fin n → Fin n → Nat, shape M' = lam → inv M ≤ inv M'

def IsPartitionN (n : Nat) (lam : List Nat) : Prop :=
  lam.length = n ∧ (∀ x ∈ lam, 0 < x) ∧ lam.Pairwise (· ≥ ·)

def claim : Prop := ∀ (n : Nat) (lam : List Nat) (M : Fin n → Fin n → Nat),
  IsPartitionN n lam → IsMinimal lam M →
    (∀ i j, M i j = M j i) ∧
      ∃ s : Nat → Int, ∀ i j, (M i j : Int) = s (i.val + j.val)

private def K3 : Fin 4 → Fin 4 → Nat := fun i j =>
  match i.val, j.val with
  | 0, 0 => 0 | 0, 1 => 3 | 0, 2 => 0 | 0, 3 => 1
  | 1, 0 => 3 | 1, 1 => 0 | 1, 2 => 2 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 0 | 2, 3 => 3
  | 3, 0 => 1 | 3, 1 => 0 | 3, 2 => 3 | 3, 3 => 0
  | _, _ => 0



private theorem K3_shape : shape K3 = [8,8,1,1] := by decide
private theorem K3_inv : inv K3 = 43 := by decide

private def hankel4 (t : Fin 7 → Nat) : Fin 4 → Fin 4 → Nat := fun i j =>
  (D5.S3.Constants.Moments.CoefficientNewtonSums.fullHermiteFromMoments 4
    (fun k => if h : k < 7 then t ⟨k, h⟩ else 0)).entries i j

private def hankelWeight (t : Fin 7 → Nat) : Nat :=
  t 0 + 2 * t 1 + 3 * t 2 + 4 * t 3 + 3 * t 4 + 2 * t 5 + t 6

private lemma hankel_reading_length (t : Fin 7 → Nat) :
    (readingWord (hankel4 t)).length = hankelWeight t := by
  simp [readingWord, List.finRange, hankel4, hankelWeight,
    D5.S3.Constants.Moments.CoefficientNewtonSums.fullHermiteFromMoments,
    List.length_replicate]
  omega

private def dot (ws xs : List Nat) : Nat := (List.zipWith (· * ·) ws xs).sum

private def weightedComps : List Nat → Nat → List (List Nat)
  | [], s => if s = 0 then [[]] else []
  | w :: ws, s =>
      (List.range (s / w + 1)).flatMap (fun x =>
        (weightedComps ws (s - w * x)).map (fun ys => x :: ys))

private lemma weightedComps_complete (ws xs : List Nat) (s : Nat)
    (hlen : xs.length = ws.length)
    (hpos : ∀ w ∈ ws, 0 < w)
    (hdot : dot ws xs = s) : xs ∈ weightedComps ws s := by
  induction ws generalizing xs s with
  | nil =>
      cases xs with
      | nil =>
          have hs : s = 0 := by simpa [dot] using hdot.symm
          simp [weightedComps, hs]
      | cons x xs => simp at hlen
  | cons w ws ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have hw : 0 < w := hpos w (by simp)
          have hrestlen : xs.length = ws.length := by simpa using hlen
          have hdot' : w * x + dot ws xs = s := by simpa [dot] using hdot
          have hbound : x ≤ s / w := by
            apply (Nat.le_div_iff_mul_le hw).2
            have hmul : w * x ≤ s := by omega
            simpa [Nat.mul_comm] using hmul
          have hx : x ∈ List.range (s / w + 1) := by
            simp only [List.mem_range]
            omega
          have hsub : dot ws xs = s - w * x := by omega
          have hposTail : ∀ u ∈ ws, 0 < u := by
            intro u hu
            exact hpos u (by simp [hu])
          have htail := ih xs (s - w * x) hrestlen hposTail hsub
          simp only [weightedComps, List.mem_flatMap]
          refine ⟨x, hx, ?_⟩
          simp only [List.mem_map]
          exact ⟨xs, htail, rfl⟩

private def matrixFromList (xs : List Nat) : Fin 4 → Fin 4 → Nat :=
  hankel4 (fun k => xs.getD k.val 0)

private def baseGood (xs : List Nat) : Bool :=
  decide (shape (matrixFromList xs) = [8, 8, 1, 1] → 45 ≤ inv (matrixFromList xs))

private def baseChunk (x : Nat) : List (List Nat) :=
  (weightedComps [2, 3, 4, 3, 2, 1] (18 - x)).map (fun ys => x :: ys)

private lemma minimizer_exists {n : Nat} (lam : List Nat)
    (h : ∃ M : Fin n → Fin n → Nat, shape M = lam) :
    ∃ M : Fin n → Fin n → Nat, IsMinimal lam M := by
  classical
  have hc : ∃ c, ∃ M : Fin n → Fin n → Nat, shape M = lam ∧ inv M = c := by
    obtain ⟨M, hM⟩ := h
    exact ⟨inv M, M, hM, rfl⟩
  obtain ⟨M, hM, hcost⟩ := Nat.find_spec hc
  refine ⟨M, hM, ?_⟩
  intro M' hM'
  rw [hcost]
  exact Nat.find_min' hc ⟨M', hM', rfl⟩

private def matrixParameters (M : Fin 4 → Fin 4 → Nat) : Fin 7 → Nat := fun k =>
  match k.val with
  | 0 => M 0 0 | 1 => M 0 1 | 2 => M 0 2 | 3 => M 0 3
  | 4 => M 1 3 | 5 => M 2 3 | _ => M 3 3

private lemma hankel_parametrization (M : Fin 4 → Fin 4 → Nat)
    (h : ∃ s : Nat → Int, ∀ i j, (M i j : Int) = s (i.val + j.val)) :
    M = hankel4 (matrixParameters M) := by
  obtain ⟨s, hs⟩ := h
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [hankel4, matrixParameters,
      D5.S3.Constants.Moments.CoefficientNewtonSums.fullHermiteFromMoments] <;>
    apply Int.ofNat_inj.mp <;>
    rw [hs, hs] <;>
    congr 1

private lemma parameters_to_matrix (t : Fin 7 → Nat) : matrixFromList (List.ofFn t) = hankel4 t := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma baseChunk_complete (t : Fin 7 → Nat) (h : hankelWeight t = 18) :
    List.ofFn t ∈ baseChunk (t 0) := by
  have htail : dot [2,3,4,3,2,1] [t 1,t 2,t 3,t 4,t 5,t 6] = 18 - t 0 := by
    simp only [dot, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil, Nat.add_zero]
    unfold hankelWeight at h
    omega
  have hp : ∀ w ∈ ([2,3,4,3,2,1] : List Nat), 0 < w := by decide
  have hc := weightedComps_complete [2,3,4,3,2,1] [t 1,t 2,t 3,t 4,t 5,t 6]
    (18 - t 0) (by rfl) hp htail
  simp only [List.ofFn_succ, List.ofFn_zero, baseChunk, List.mem_map]
  exact ⟨_, hc, rfl⟩

private lemma hankel_total18 (t : Fin 7 → Nat) (h : shape (hankel4 t) = [8,8,1,1]) :
    hankelWeight t = 18 := by
  have he := shape_size (hankel4 t)
  rw [h, hankel_reading_length] at he
  simpa using he.symm

private lemma base_of_chunk_checks
    (hcheck : ∀ x, x ≤ 18 → (baseChunk x).all baseGood = true)
    (t : Fin 7 → Nat) (hshape : shape (hankel4 t) = [8,8,1,1]) :
    45 ≤ inv (hankel4 t) := by
  have htotal := hankel_total18 t hshape
  have h0 : t 0 ≤ 18 := by unfold hankelWeight at htotal; omega
  have hmem := baseChunk_complete t htotal
  have hgood := List.all_eq_true.mp (hcheck (t 0) h0) (List.ofFn t) hmem
  have hprop := of_decide_eq_true hgood
  rw [parameters_to_matrix] at hprop
  exact hprop hshape

set_option maxRecDepth 100000 in
private theorem base_chunk0 : (baseChunk 0).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk1 : (baseChunk 1).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk2 : (baseChunk 2).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk3 : (baseChunk 3).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk4 : (baseChunk 4).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk5 : (baseChunk 5).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk6 : (baseChunk 6).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk7 : (baseChunk 7).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk8 : (baseChunk 8).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk9 : (baseChunk 9).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk10 : (baseChunk 10).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk11 : (baseChunk 11).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk12 : (baseChunk 12).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk13 : (baseChunk 13).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk14 : (baseChunk 14).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk15 : (baseChunk 15).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk16 : (baseChunk 16).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk17 : (baseChunk 17).all baseGood = true := by decide
set_option maxRecDepth 100000 in
private theorem base_chunk18 : (baseChunk 18).all baseGood = true := by decide

private theorem hankel_lower_base (t : Fin 7 → Nat)
    (hshape : shape (hankel4 t) = [8,8,1,1]) :
    45 ≤ inv (hankel4 t) := by
  refine base_of_chunk_checks ?_ t hshape
  intro x hx
  interval_cases x
  · exact base_chunk0
  · exact base_chunk1
  · exact base_chunk2
  · exact base_chunk3
  · exact base_chunk4
  · exact base_chunk5
  · exact base_chunk6
  · exact base_chunk7
  · exact base_chunk8
  · exact base_chunk9
  · exact base_chunk10
  · exact base_chunk11
  · exact base_chunk12
  · exact base_chunk13
  · exact base_chunk14
  · exact base_chunk15
  · exact base_chunk16
  · exact base_chunk17
  · exact base_chunk18

private def baseLam : List Nat := [8,8,1,1]

private lemma base_minimizer_exists : ∃ M : Fin 4 → Fin 4 → Nat, IsMinimal baseLam M := by
  apply minimizer_exists
  exact ⟨K3, by simpa [baseLam] using K3_shape⟩

private lemma base_minimizer_not_hankel (M : Fin 4 → Fin 4 → Nat)
    (hM : IsMinimal baseLam M)
    (hH : ∃ s : Nat → Int, ∀ i j, (M i j : Int) = s (i.val + j.val)) : False := by
  have hcost : inv M ≤ 43 := by
    have h := hM.2 K3 (by simpa [baseLam] using K3_shape)
    simpa [K3_inv] using h
  have hparam := hankel_parametrization M hH
  have hlow : 45 ≤ inv M := by
    have hs := hankel_lower_base (matrixParameters M) (by
      rw [← hparam]
      exact hM.1)
    rw [← hparam] at hs
    exact hs
  omega

theorem result : ¬ claim := by
  intro hc
  obtain ⟨M, hM⟩ := base_minimizer_exists
  have hpart : IsPartitionN 4 baseLam := by
    simp [IsPartitionN, baseLam, List.pairwise_cons]
  have hh := hc 4 baseLam M hpart hM
  exact base_minimizer_not_hankel M hM hh.2


end D5.S3.Combinatorics.Permutation.RSKMinimalInversionHankelRefutation
