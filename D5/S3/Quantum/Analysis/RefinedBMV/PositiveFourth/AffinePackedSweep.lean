/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffinePackedSweep
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Evaluate the packed affine factors by signed shifts. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedRow

/-! An affine factor at a power of two is an integer multiplication by each
coordinate difference followed by one signed shift and one addition. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open private uFactors factor Certificate.packedColumns radix magnitude step sweep masked
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks
open private columnDot mergedRow
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffinePackedRow
open DimThree.PackedCheck (packSigned polynomialMask)

private def shiftFactor (s : ℕ) (a r : AffineRate) (w : ℤ) : ℤ :=
  ((a.1 : ℤ) - (r.1 : ℤ)) * w + ((((a.2 : ℤ) - (r.2 : ℤ)) * w) <<< s)

private theorem shiftFactor_eq (s : ℕ) (a r : AffineRate) (w : ℤ) :
    shiftFactor s a r w = w * (magnitude ((2 : ℤ) ^ s) a - magnitude ((2 : ℤ) ^ s) r) := by
  simp only [shiftFactor, Int.shiftLeft_eq, magnitude]
  ring

private def shiftPack (s : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: as => a + (shiftPack s as <<< s)

private theorem shiftPack_eq (s : ℕ) (cs : List ℤ) :
    shiftPack s cs = packSigned ((2 : ℤ) ^ s) cs := by
  induction cs with
  | nil => rfl
  | cons a cs ih => simp only [shiftPack, packSigned, Int.shiftLeft_eq, ih, mul_comm]

private def shiftProduct (s : ℕ) (a : AffineRate) (roots : List AffineRate) : ℤ :=
  roots.foldr (fun root value => shiftFactor s root a value) 1

private theorem shiftProduct_eq (s : ℕ) (a : AffineRate) (roots : List AffineRate) :
    shiftProduct s a roots = factor (magnitude ((2 : ℤ) ^ s) a)
      (roots.map (magnitude ((2 : ℤ) ^ s))) := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
    simp only [shiftProduct, List.foldr_cons, shiftFactor_eq, factor, List.map_cons,
      List.prod_cons] at ih ⊢
    rw [ih, mul_comm]

private def shiftUFactors (s : ℕ) (roots : List AffineRate) (k : ℕ) : Array ℤ :=
  let earlierRoots := roots.take k
  (roots.mapIdx fun i a => if i < k then 0 else shiftProduct s a earlierRoots).toArray

private theorem shiftUFactors_eq (s : ℕ) (roots : List AffineRate) (k : ℕ) :
    shiftUFactors s roots k = uFactors (roots.map (magnitude ((2 : ℤ) ^ s))) k := by
  unfold shiftUFactors uFactors
  apply congrArg List.toArray
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_mapIdx, List.getElem?_map]
  cases roots[i]? <;> simp [shiftProduct_eq, List.map_take]

private def updated (s : ℕ) (a : AffineRate) :
    List (AffineRate × ℤ) → ℤ × List (AffineRate × ℤ)
  | [] => (0, [])
  | (r, w) :: ws =>
    let tail := updated s a ws
    let weight := shiftFactor s a r w
    (weight + tail.1, (r, weight) :: tail.2)

private def evaluation (s : ℕ) (ws : List (AffineRate × ℤ)) : List (ℤ × ℤ) :=
  ws.map fun (r, w) => (magnitude ((2 : ℤ) ^ s) r, w)

private theorem updated_eq (s : ℕ) (a : AffineRate) (ws : List (AffineRate × ℤ)) :
    let row := updated s a ws
    row.1 = (row.2.map Prod.snd).sum ∧
      evaluation s row.2 = step (magnitude ((2 : ℤ) ^ s) a) (evaluation s ws) := by
  induction ws with
  | nil => simp [updated, evaluation, step]
  | cons w ws ih =>
    obtain ⟨r, weight⟩ := w
    obtain ⟨hs, ht⟩ := ih
    simp [updated, hs, evaluation, step, shiftFactor_eq] at ht ⊢
    exact ht

private def shiftSweep (s : ℕ) (test : ℤ → Bool) :
    ℕ → ℤ → List (AffineRate × ℤ) → Bool
  | 0, _, _ => true
  | _ + 1, _, [] => true
  | n + 1, total, (a, _) :: ws =>
    test total && (let row := updated s a ws; shiftSweep s test n row.1 row.2)

private theorem shiftSweep_eq (s : ℕ) (test : ℤ → Bool) (n : ℕ)
    (ws : List (AffineRate × ℤ)) :
    shiftSweep s test n (ws.map Prod.snd).sum ws =
      sweep test n (evaluation s ws) := by
  induction n generalizing ws with
  | zero => simp [shiftSweep, sweep]
  | succ n ih =>
    cases ws with
    | nil => rfl
    | cons w ws =>
      obtain ⟨a, h⟩ := w
      obtain ⟨hs, ht⟩ := updated_eq s a ws
      simp only [shiftSweep, evaluation, List.map_cons, List.sum_cons, sweep]
      rw [hs, ih, ht]
      simp only [evaluation, List.map_map, Function.comp_def]

private def affineColumns (c : Certificate) (s : ℕ) :
    List (AffineRate × List (ℕ × ℤ)) :=
  c.columns.map fun col => (col.1, col.2.map fun g => (g.uIndex, shiftPack s g.coefficients))

private def columnWeights (factors : Array ℤ)
    (columns : List (AffineRate × List (ℕ × ℤ))) (k : ℕ) : List (AffineRate × ℤ) :=
  columns.map fun col => (col.1, columnDot factors k col.2)

private def shiftRowWithColumns (roots : List AffineRate)
    (columns : List (AffineRate × List (ℕ × ℤ))) (s k : ℕ) : List (AffineRate × ℤ) :=
  columnWeights (shiftUFactors s roots k) columns k

private def shiftRow (c : Certificate) (s k : ℕ) : List (AffineRate × ℤ) :=
  shiftRowWithColumns c.rootsU (affineColumns c s) s k

private theorem shiftRow_eq (c : Certificate) (s k : ℕ) :
    evaluation s (shiftRow c s k) =
      mergedRow (c.rootsU.map (magnitude ((2 : ℤ) ^ s)))
        (Certificate.packedColumns c ((2 : ℤ) ^ s)) k := by
  unfold evaluation shiftRow shiftRowWithColumns affineColumns mergedRow Certificate.packedColumns
    columnWeights
  simp only [List.map_map, Function.comp_def, shiftPack_eq, shiftUFactors_eq]

def Certificate.checkShiftRow (c : Certificate) (width digits k : ℕ) : Bool :=
  let s := width + 1
  let ws := shiftRow c s k
  shiftSweep s (masked (polynomialMask width digits)) c.rootsV.length
    (ws.map Prod.snd).sum ws

theorem Certificate.checkShiftRow_eq (c : Certificate) (width digits k : ℕ) :
    c.checkShiftRow width digits k = c.checkRow width digits k := by
  rw [← c.checkMergedRow_eq]
  simp only [Certificate.checkShiftRow, shiftSweep_eq, shiftRow_eq,
    Certificate.checkMergedRow, radix]

/-- Check a block using shared packed columns and a shared coefficient mask. -/
def Certificate.checkShiftRows (c : Certificate) (width digits : ℕ) (indices : List ℕ) : Bool :=
  let s := width + 1
  let columns := affineColumns c s
  let test := masked (polynomialMask width digits)
  let limit := c.rootsV.length
  indices.all fun k =>
    let ws := shiftRowWithColumns c.rootsU columns s k
    shiftSweep s test limit (ws.map Prod.snd).sum ws

theorem Certificate.checkShiftRows_eq (c : Certificate) (width digits : ℕ) (indices : List ℕ) :
    c.checkShiftRows width digits indices = indices.all (c.checkShiftRow width digits) := rfl

private def initialSuffix (s : ℕ) (roots : List AffineRate) (k : ℕ) :
    List (AffineRate × ℤ) :=
  (roots.drop k).map fun a => (a, shiftProduct s a (roots.take k))

private def advanceSuffix (s : ℕ) : List (AffineRate × ℤ) → List (AffineRate × ℤ)
  | [] => []
  | (a, _) :: tail => tail.map fun (r, w) => (r, shiftFactor s a r w)

private theorem shiftProduct_append (s : ℕ) (a b : AffineRate) (roots : List AffineRate) :
    shiftProduct s a (roots ++ [b]) = shiftFactor s b a (shiftProduct s a roots) := by
  simp only [shiftProduct_eq, shiftFactor_eq, List.map_append, factor, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]

private theorem advanceSuffix_eq (s : ℕ) (roots : List AffineRate) (k : ℕ)
    (hk : k < roots.length) :
    advanceSuffix s (initialSuffix s roots k) = initialSuffix s roots (k + 1) := by
  unfold initialSuffix
  conv_lhs => rw [List.drop_eq_getElem_cons hk]
  simp only [advanceSuffix, List.map_cons, List.map_map, Function.comp_def,
    List.take_succ_eq_append_getElem hk, shiftProduct_append]

private theorem initialSuffix_factors (s : ℕ) (roots : List AffineRate) (k : ℕ)
    (hk : k ≤ roots.length) :
    (List.replicate k (0 : ℤ) ++ (initialSuffix s roots k).map Prod.snd).toArray =
      shiftUFactors s roots k := by
  unfold shiftUFactors
  apply congrArg List.toArray
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_mapIdx]
  by_cases hi : i < k
  · rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hi),
      List.getElem?_replicate_of_lt hi, List.getElem?_eq_getElem (hi.trans_le hk)]
    simp [hi]
  · rw [List.getElem?_append_right (by simpa only [List.length_replicate] using Nat.le_of_not_gt hi)]
    simp only [List.length_replicate, initialSuffix, List.getElem?_map, List.getElem?_drop,
      Nat.add_sub_of_le (Nat.le_of_not_gt hi)]
    cases roots[i]? <;> simp [hi]

private def checkSuffix (columns : List (AffineRate × List (ℕ × ℤ)))
    (s : ℕ) (test : ℤ → Bool) (limit : ℕ) :
    ℕ → ℕ → List (AffineRate × ℤ) → Bool
  | 0, _, _ => true
  | count + 1, k, suffix =>
    let factors := (List.replicate k 0 ++ suffix.map Prod.snd).toArray
    let ws := columnWeights factors columns k
    shiftSweep s test limit (ws.map Prod.snd).sum ws &&
      checkSuffix columns s test limit count (k + 1) (advanceSuffix s suffix)

def Certificate.checkShiftBlock (c : Certificate) (width digits k count : ℕ) : Bool :=
  let s := width + 1
  checkSuffix (affineColumns c s) s (masked (polynomialMask width digits))
    c.rootsV.length count k (initialSuffix s c.rootsU k)

theorem Certificate.checkShiftBlock_eq (c : Certificate) (width digits k count : ℕ)
    (h : k + count ≤ c.rootsU.length) :
    c.checkShiftBlock width digits k count =
      (List.range' k count).all (c.checkShiftRow width digits) := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
    have hk : k < c.rootsU.length := by omega
    unfold Certificate.checkShiftBlock
    simp only [checkSuffix, List.range'_succ, List.all_cons,
      initialSuffix_factors _ _ _ hk.le, advanceSuffix_eq _ _ _ hk]
    change (c.checkShiftRow width digits k && c.checkShiftBlock width digits (k + 1) count) = _
    rw [ih (k + 1) (by omega)]

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
