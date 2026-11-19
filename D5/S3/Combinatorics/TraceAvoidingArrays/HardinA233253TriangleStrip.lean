/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.finite_certificate
   digest: Barker's generating function for the literal normalized six-colour five-column strip. -/
/-
admission_basis: open-problem-resolution (#28234; Proved)
escape_witness: none
Direct frozen dependencies (declaration statement_ids):
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.allowed
statement_id: sha256:4ee019eb42606605da41b2b090212be244d3bf48d64a2c10dc2d9c6c6f7e6468
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.advance
statement_id: sha256:63e23e390cbc7ee42155ce307351f149d901cd9013daee3d6d2eac775e24af71
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish_fst
statement_id: sha256:5859cc0f84f4e6a91313521f32ea6d187c4822bb52d4e438939da5e000940bd5
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish_snd
statement_id: sha256:1ada14ea452d6f35f959dbbd5a034265c8c6921cd041422cad27ec166a94d24c
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good_iff
statement_id: sha256:59d0ffb034f7f2361718e6d2566eb24417785b9a178f6fcb44f336c1199d3d62
D5.S3.Observer.Separation.BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthNormal
statement_id: sha256:544f7677e789967b28078e2cb7f71e075b79492f79f4741e37f835329362022b
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthStep
statement_id: sha256:8c9c3150fd3c1de8690f85618bf432c3a53bb7dd26b0d6ce7d37853305810660
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthV
statement_id: sha256:4f3953ec5d8902b74486197a6f4d782f3fb58c6627a5740a5242632a7560f9ed
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthTotal
statement_id: sha256:1599dea1e937fc19cabeaa107a371a30c86b0526bfd9a251a1fcb71ebcab5ee3
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.width_counting_bridge
statement_id: sha256:b0ee269255efb9d46abe0df07b64609eafbc4ff070b1edfd59fae14859fc955d
D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
Row: proof_shape=bind-only; consumers=rowLegal
Boundary: proof_shape=bind-only; consumers=pairs, compatible, Valid
rowLegal: proof_shape=bind-only; consumers=Legal, classCount
bonds: proof_shape=bind-only; consumers=Legal, bonds_iff
Legal: proof_shape=bind-only; consumers=a, counting_bridge
instDecidableNormal: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableRowLegal: proof_shape=bind-only; consumers=instDecidableLegal, classCount
instDecidableBonds: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=counting_bridge, zero_count, result
pairs: proof_shape=bind-only; consumers=bonds_iff, classCount
compatible: proof_shape=bind-only; consumers=bonds_iff, classCount
instDecidableCompatible: proof_shape=bind-only; consumers=classCount
instDecidableGood: proof_shape=bind-only; consumers=classCount, firstCount
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=v_eq_w
total: proof_shape=bind-only; consumers=a_eq_w
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
Valid: proof_shape=bind-only; consumers=row_counts, initial_valid
instDecidableValid: proof_shape=bind-only; consumers=row_counts, initial_valid
rank: proof_shape=bind-only; consumers=rankCount, eval
valid_next: proof_shape=bind-only; consumers=v_eq_w
classCount: proof_shape=bind-only; consumers=finite_certificate
rankCount: proof_shape=bind-only; consumers=finite_certificate
firstCount: proof_shape=bind-only; consumers=finite_certificate
firstRank: proof_shape=bind-only; consumers=finite_certificate
sum_rows: proof_shape=bind-only; consumers=row_count_unseen_0101, initial_counts
rowPartial: proof_shape=bind-only; consumers=PrefixCounts
rankPartial: proof_shape=bind-only; consumers=PrefixCounts
firstPartial: proof_shape=bind-only; consumers=initial_partials
firstRankPartial: proof_shape=bind-only; consumers=initial_partials
PrefixCounts: proof_shape=bind-only; consumers=partial_unseen_0101
partial_unseen_0101: proof_shape=bind-only; consumers=row_count_unseen_0101
row_count_unseen_0101: proof_shape=bind-only; consumers=row_counts
partial_unseen_1010: proof_shape=bind-only; consumers=row_count_unseen_1010
row_count_unseen_1010: proof_shape=bind-only; consumers=row_counts
partial_seen_0101: proof_shape=bind-only; consumers=row_count_seen_0101
row_count_seen_0101: proof_shape=bind-only; consumers=row_counts
partial_seen_0102: proof_shape=bind-only; consumers=row_count_seen_0102
row_count_seen_0102: proof_shape=bind-only; consumers=row_counts
partial_seen_0120: proof_shape=bind-only; consumers=row_count_seen_0120
row_count_seen_0120: proof_shape=bind-only; consumers=row_counts
partial_seen_0121: proof_shape=bind-only; consumers=row_count_seen_0121
row_count_seen_0121: proof_shape=bind-only; consumers=row_counts
partial_seen_0201: proof_shape=bind-only; consumers=row_count_seen_0201
row_count_seen_0201: proof_shape=bind-only; consumers=row_counts
partial_seen_0202: proof_shape=bind-only; consumers=row_count_seen_0202
row_count_seen_0202: proof_shape=bind-only; consumers=row_counts
partial_seen_0210: proof_shape=bind-only; consumers=row_count_seen_0210
row_count_seen_0210: proof_shape=bind-only; consumers=row_counts
partial_seen_0212: proof_shape=bind-only; consumers=row_count_seen_0212
row_count_seen_0212: proof_shape=bind-only; consumers=row_counts
partial_seen_1010: proof_shape=bind-only; consumers=row_count_seen_1010
row_count_seen_1010: proof_shape=bind-only; consumers=row_counts
partial_seen_1012: proof_shape=bind-only; consumers=row_count_seen_1012
row_count_seen_1012: proof_shape=bind-only; consumers=row_counts
partial_seen_1020: proof_shape=bind-only; consumers=row_count_seen_1020
row_count_seen_1020: proof_shape=bind-only; consumers=row_counts
partial_seen_1021: proof_shape=bind-only; consumers=row_count_seen_1021
row_count_seen_1021: proof_shape=bind-only; consumers=row_counts
partial_seen_1201: proof_shape=bind-only; consumers=row_count_seen_1201
row_count_seen_1201: proof_shape=bind-only; consumers=row_counts
partial_seen_1202: proof_shape=bind-only; consumers=row_count_seen_1202
row_count_seen_1202: proof_shape=bind-only; consumers=row_counts
partial_seen_1210: proof_shape=bind-only; consumers=row_count_seen_1210
row_count_seen_1210: proof_shape=bind-only; consumers=row_counts
partial_seen_1212: proof_shape=bind-only; consumers=row_count_seen_1212
row_count_seen_1212: proof_shape=bind-only; consumers=row_counts
partial_seen_2010: proof_shape=bind-only; consumers=row_count_seen_2010
row_count_seen_2010: proof_shape=bind-only; consumers=row_counts
partial_seen_2012: proof_shape=bind-only; consumers=row_count_seen_2012
row_count_seen_2012: proof_shape=bind-only; consumers=row_counts
partial_seen_2020: proof_shape=bind-only; consumers=row_count_seen_2020
row_count_seen_2020: proof_shape=bind-only; consumers=row_counts
partial_seen_2021: proof_shape=bind-only; consumers=row_count_seen_2021
row_count_seen_2021: proof_shape=bind-only; consumers=row_counts
partial_seen_2101: proof_shape=bind-only; consumers=row_count_seen_2101
row_count_seen_2101: proof_shape=bind-only; consumers=row_counts
partial_seen_2102: proof_shape=bind-only; consumers=row_count_seen_2102
row_count_seen_2102: proof_shape=bind-only; consumers=row_counts
partial_seen_2120: proof_shape=bind-only; consumers=row_count_seen_2120
row_count_seen_2120: proof_shape=bind-only; consumers=row_counts
partial_seen_2121: proof_shape=bind-only; consumers=row_count_seen_2121
row_count_seen_2121: proof_shape=bind-only; consumers=row_counts
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_valid: proof_shape=bind-only; consumers=a_eq_w
initial_partials: proof_shape=bind-only; consumers=initial_counts
initial_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=v_eq_w, a_eq_w
w: proof_shape=bind-only; consumers=v_eq_w, recurrence
eval: proof_shape=bind-only; consumers=v_eq_w
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=recurrence, result
recurrence: proof_shape=bind-only; consumers=result
zero_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerSeries.Basic
/-! Literal five-column arrays and a three-dimensional symbolic continuation transfer. -/
set_option maxRecDepth 100000
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
open HardinA233175PairStrip (Seen allowed advance good finish finish_fst finish_snd good_iff)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open HardinA233251TriangleStrip
abbrev Row := Fin 5 → Fin 6
abbrev Boundary := Fin 4 → Fin 3
def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 4, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5
private def bonds (c d : Row) : Prop :=
  ∀ j : Fin 4, c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5
private def Legal {n : ℕ} (A : Fin n × Fin 5 → Fin 6) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
    (∀ i, rowLegal (fun j => A (i, j))) ∧
    (∀ (i : Fin n) (h : i.val + 1 < n), bonds (fun j => A (i, j))
      (fun j => A (⟨i.val + 1, h⟩, j))) ∧
    widthNormal (false, false) (fun i j => A (i, j))
private instance instDecidableNormal {n : ℕ} (s : Seen) (f : Fin n → Row) :
    Decidable (widthNormal s f) :=
  inferInstanceAs (Decidable (∀ _ _, (_ → _) ∧ (_ → _)))
instance instDecidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance instDecidableLegal {n : ℕ} (A : Fin n × Fin 5 → Fin 6) :
    Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
/-- The literal filtered count. The first-cell existential sets `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 5 → Fin 6 => Legal A)).card
def pairs (c : Row) : Boundary := fun j => beta (c j.succ)
def compatible (p : Boundary) (c : Row) : Prop :=
  ∀ j : Fin 4, p j ≠ beta (c j.castSucc)
private instance instDecidableCompatible (p : Boundary) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))
private instance instDecidableGood (s : Seen) (c : Row) : Decidable (good s c) := by
  unfold good
  infer_instance
private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, HardinA233251TriangleStrip.colour_bond_iff, compatible, pairs]
private abbrev v := widthV rowLegal pairs compatible
private abbrev total := widthTotal rowLegal pairs
private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  exact width_counting_bridge rowLegal pairs compatible bonds bonds_iff n
/-- Adjacent boundary labels differ; absent colour two excludes its whole pair. -/
def Valid (s : Seen) (p : Boundary) : Prop :=
  s.1 = true ∧ (∀ j : Fin 3, p j.castSucc ≠ p j.succ) ∧
    (s.2 = false → ∀ j, p j ≠ 2)
private instance instDecidableValid (s : Seen) (p : Boundary) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ (∀ _, _) ∧ (_ → ∀ _, _)))
/-- On the four boundary shapes ABAB, ABAC, ABCA, ABCB the ranks are 3,2,0,2. -/
def rank (p : Boundary) : ℤ :=
  if p 0 = p 2 then (if p 1 = p 3 then 3 else 2) else
    (if p 1 = p 3 then 2 else 0)
private theorem valid_next (s : Seen) (hs : s.1 = true) (c : Row)
    (hc : rowLegal c ∧ good s c) : Valid (finish s c) (pairs c) := by
  refine ⟨(finish_fst s c).mpr (Or.inl hs), ?_, ?_⟩
  · intro j
    have h := HardinA233251TriangleStrip.colour_bond_iff _ _ |>.mp (hc.1 j.succ)
    exact h
  · intro ht j
    have htwo : ∀ i, c i ≠ 2 := by
      intro i hi
      have hh := (finish_snd s c).mpr (Or.inr ⟨i, hi⟩)
      simp [ht] at hh
    have hstate : s.2 ≠ true := by
      intro hi
      have hh := (finish_snd s c).mpr (Or.inl hi)
      simp [ht] at hh
    have hthree : ∀ i, c i ≠ 3 := by
      intro i hi
      rcases ((good_iff s c).mp hc.2 i).2 hi with hh | ⟨r, _, hr⟩
      · exact hstate hh
      · exact htwo r hr
    have hb : ∀ x : Fin 6, beta x = 2 ↔ x = 2 ∨ x = 3 := by decide +kernel
    intro hp
    rcases (hb _).mp hp with hh | hh
    · exact htwo _ hh
    · exact hthree _ hh
/-- Count continuations by the second final flag. -/
def classCount (s : Seen) (p : Boundary) (b : Bool) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = b then 1 else 0
/-- Sum the boundary ranks of fully seen continuations. -/
def rankCount (s : Seen) (p : Boundary) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = true then rank (pairs c) else 0
/-- Count first rows by the second final flag. -/
def firstCount (b : Bool) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = b then 1 else 0
/-- Sum the ranks of fully seen first rows. -/
def firstRank : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = true then rank (pairs c) else 0
private theorem sum_rows (f : Row → ℤ) : (∑ c : Row, f c) =
    ∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6, ∑ d : Fin 6, ∑ e : Fin 6,
      f ![a, b, c, d, e] := by
  simp_rw [← (Fin.consEquiv (fun _ : Fin 5 => Fin 6)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 4 => Fin 6)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 3 => Fin 6)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 2 => Fin 6)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 1 => Fin 6)).sum_comp,
    Fintype.sum_prod_type]
  simp [Fin.consEquiv, Matrix.empty_eq]
private def rowPartial (s : Seen) (p : Boundary) (x y : Fin 6) (b : Bool) : ℤ :=
  ∑ z : Fin 6, ∑ t : Fin 6, ∑ u : Fin 6,
    let c : Row := ![x, y, z, t, u]
    if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = b then 1 else 0
private def rankPartial (s : Seen) (p : Boundary) (x y : Fin 6) : ℤ :=
  ∑ z : Fin 6, ∑ t : Fin 6, ∑ u : Fin 6,
    let c : Row := ![x, y, z, t, u]
    if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
      then rank (pairs c) else 0
private def firstPartial (x y : Fin 6) (b : Bool) : ℤ :=
  ∑ z : Fin 6, ∑ t : Fin 6, ∑ u : Fin 6,
    let c : Row := ![x, y, z, t, u]
    if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
      (finish (false, false) c).2 = b then 1 else 0
private def firstRankPartial (x y : Fin 6) : ℤ :=
  ∑ z : Fin 6, ∑ t : Fin 6, ∑ u : Fin 6,
    let c : Row := ![x, y, z, t, u]
    if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
      (finish (false, false) c).2 = true then rank (pairs c) else 0
private def PrefixCounts (s : Seen) (p : Boundary) (t f r : Fin 6 → Fin 6 → ℤ) : Prop :=
  ∀ x y : Fin 6, rowPartial s p x y true = t x y ∧
    rowPartial s p x y false = f x y ∧ rankPartial s p x y = r x y
private theorem partial_unseen_0101 : PrefixCounts (true, false) ![0, 1, 0, 1]
    ![![0, 0, 0, 0, 0, 0], ![20, 0, 32, 0, 0, 20], ![48, 0, 0, 0, 0, 48], ![0, 0, 0, 0, 0, 0],
      ![20, 0, 32, 0, 0, 20], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![8, 0, 0, 0, 0, 8], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![8, 0, 0, 0, 0, 8], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![36, 0, 56, 0, 0, 36], ![96, 0, 0, 0, 0, 96], ![0, 0, 0, 0, 0, 0],
      ![36, 0, 56, 0, 0, 36], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_unseen_0101 :
    classCount (true, false) ![0, 1, 0, 1] true = 240 ∧
    classCount (true, false) ![0, 1, 0, 1] false = 32 ∧
    rankCount (true, false) ![0, 1, 0, 1] = 448 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, false) ![0, 1, 0, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, false) ![0, 1, 0, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, false) ![0, 1, 0, 1] x y) = _
  simp_rw [(partial_unseen_0101 _ _).1, (partial_unseen_0101 _ _).2.1,
    (partial_unseen_0101 _ _).2.2]
  decide +kernel
private theorem partial_unseen_1010 : PrefixCounts (true, false) ![1, 0, 1, 0]
    ![![0, 20, 32, 0, 20, 0], ![0, 0, 0, 0, 0, 0], ![0, 48, 0, 0, 48, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 20, 32, 0, 20, 0]]
    ![![0, 8, 0, 0, 8, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 8, 0, 0, 8, 0]]
    ![![0, 36, 56, 0, 36, 0], ![0, 0, 0, 0, 0, 0], ![0, 96, 0, 0, 96, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 36, 56, 0, 36, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_unseen_1010 :
    classCount (true, false) ![1, 0, 1, 0] true = 240 ∧
    classCount (true, false) ![1, 0, 1, 0] false = 32 ∧
    rankCount (true, false) ![1, 0, 1, 0] = 448 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, false) ![1, 0, 1, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, false) ![1, 0, 1, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, false) ![1, 0, 1, 0] x y) = _
  simp_rw [(partial_unseen_1010 _ _).1, (partial_unseen_1010 _ _).2.1,
    (partial_unseen_1010 _ _).2.2]
  decide +kernel
private theorem partial_seen_0101 : PrefixCounts (true, true) ![0, 1, 0, 1]
    ![![0, 0, 0, 0, 0, 0], ![48, 0, 32, 32, 0, 48], ![48, 0, 0, 0, 0, 48], ![48, 0, 0, 0, 0, 48],
      ![48, 0, 32, 32, 0, 48], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![96, 0, 56, 56, 0, 96], ![96, 0, 0, 0, 0, 96], ![96, 0, 0, 0, 0, 96],
      ![96, 0, 56, 56, 0, 96], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_0101 :
    classCount (true, true) ![0, 1, 0, 1] true = 512 ∧
    classCount (true, true) ![0, 1, 0, 1] false = 0 ∧
    rankCount (true, true) ![0, 1, 0, 1] = 992 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 1, 0, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 1, 0, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![0, 1, 0, 1] x y) = _
  simp_rw [(partial_seen_0101 _ _).1, (partial_seen_0101 _ _).2.1,
    (partial_seen_0101 _ _).2.2]
  decide +kernel
private theorem partial_seen_0102 : PrefixCounts (true, true) ![0, 1, 0, 2]
    ![![0, 0, 0, 0, 0, 0], ![48, 0, 16, 16, 0, 48], ![48, 0, 0, 0, 0, 48], ![48, 0, 0, 0, 0, 48],
      ![48, 0, 16, 16, 0, 48], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![96, 0, 16, 16, 0, 96], ![96, 0, 0, 0, 0, 96], ![96, 0, 0, 0, 0, 96],
      ![96, 0, 16, 16, 0, 96], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_0102 :
    classCount (true, true) ![0, 1, 0, 2] true = 448 ∧
    classCount (true, true) ![0, 1, 0, 2] false = 0 ∧
    rankCount (true, true) ![0, 1, 0, 2] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 1, 0, 2] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 1, 0, 2] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![0, 1, 0, 2] x y) = _
  simp_rw [(partial_seen_0102 _ _).1, (partial_seen_0102 _ _).2.1,
    (partial_seen_0102 _ _).2.2]
  decide +kernel
private theorem partial_seen_0120 : PrefixCounts (true, true) ![0, 1, 2, 0]
    ![![0, 0, 0, 0, 0, 0], ![16, 0, 48, 48, 0, 16], ![16, 0, 0, 0, 0, 16], ![16, 0, 0, 0, 0, 16],
      ![16, 0, 48, 48, 0, 16], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![16, 0, 96, 96, 0, 16], ![16, 0, 0, 0, 0, 16], ![16, 0, 0, 0, 0, 16],
      ![16, 0, 96, 96, 0, 16], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_0120 :
    classCount (true, true) ![0, 1, 2, 0] true = 320 ∧
    classCount (true, true) ![0, 1, 2, 0] false = 0 ∧
    rankCount (true, true) ![0, 1, 2, 0] = 512 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 1, 2, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 1, 2, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![0, 1, 2, 0] x y) = _
  simp_rw [(partial_seen_0120 _ _).1, (partial_seen_0120 _ _).2.1,
    (partial_seen_0120 _ _).2.2]
  decide +kernel
private theorem partial_seen_0121 : PrefixCounts (true, true) ![0, 1, 2, 1]
    ![![0, 0, 0, 0, 0, 0], ![32, 0, 48, 48, 0, 32], ![32, 0, 0, 0, 0, 32], ![32, 0, 0, 0, 0, 32],
      ![32, 0, 48, 48, 0, 32], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![56, 0, 96, 96, 0, 56], ![56, 0, 0, 0, 0, 56], ![56, 0, 0, 0, 0, 56],
      ![56, 0, 96, 96, 0, 56], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_0121 :
    classCount (true, true) ![0, 1, 2, 1] true = 448 ∧
    classCount (true, true) ![0, 1, 2, 1] false = 0 ∧
    rankCount (true, true) ![0, 1, 2, 1] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 1, 2, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 1, 2, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![0, 1, 2, 1] x y) = _
  simp_rw [(partial_seen_0121 _ _).1, (partial_seen_0121 _ _).2.1,
    (partial_seen_0121 _ _).2.2]
  decide +kernel
private theorem partial_seen_0201 : PrefixCounts (true, true) ![0, 2, 0, 1]
    ![![0, 0, 0, 0, 0, 0], ![48, 0, 0, 0, 0, 48], ![48, 16, 0, 0, 16, 48],
      ![48, 16, 0, 0, 16, 48], ![48, 0, 0, 0, 0, 48], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![96, 0, 0, 0, 0, 96], ![96, 16, 0, 0, 16, 96],
      ![96, 16, 0, 0, 16, 96], ![96, 0, 0, 0, 0, 96], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_0201 :
    classCount (true, true) ![0, 2, 0, 1] true = 448 ∧
    classCount (true, true) ![0, 2, 0, 1] false = 0 ∧
    rankCount (true, true) ![0, 2, 0, 1] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 2, 0, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 2, 0, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![0, 2, 0, 1] x y) = _
  simp_rw [(partial_seen_0201 _ _).1, (partial_seen_0201 _ _).2.1,
    (partial_seen_0201 _ _).2.2]
  decide +kernel
private theorem partial_seen_0202 : PrefixCounts (true, true) ![0, 2, 0, 2]
    ![![0, 0, 0, 0, 0, 0], ![48, 0, 0, 0, 0, 48], ![48, 32, 0, 0, 32, 48],
      ![48, 32, 0, 0, 32, 48], ![48, 0, 0, 0, 0, 48], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![96, 0, 0, 0, 0, 96], ![96, 56, 0, 0, 56, 96],
      ![96, 56, 0, 0, 56, 96], ![96, 0, 0, 0, 0, 96], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_0202 :
    classCount (true, true) ![0, 2, 0, 2] true = 512 ∧
    classCount (true, true) ![0, 2, 0, 2] false = 0 ∧
    rankCount (true, true) ![0, 2, 0, 2] = 992 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 2, 0, 2] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 2, 0, 2] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![0, 2, 0, 2] x y) = _
  simp_rw [(partial_seen_0202 _ _).1, (partial_seen_0202 _ _).2.1,
    (partial_seen_0202 _ _).2.2]
  decide +kernel
private theorem partial_seen_0210 : PrefixCounts (true, true) ![0, 2, 1, 0]
    ![![0, 0, 0, 0, 0, 0], ![16, 0, 0, 0, 0, 16], ![16, 48, 0, 0, 48, 16],
      ![16, 48, 0, 0, 48, 16], ![16, 0, 0, 0, 0, 16], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![16, 0, 0, 0, 0, 16], ![16, 96, 0, 0, 96, 16],
      ![16, 96, 0, 0, 96, 16], ![16, 0, 0, 0, 0, 16], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_0210 :
    classCount (true, true) ![0, 2, 1, 0] true = 320 ∧
    classCount (true, true) ![0, 2, 1, 0] false = 0 ∧
    rankCount (true, true) ![0, 2, 1, 0] = 512 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 2, 1, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 2, 1, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![0, 2, 1, 0] x y) = _
  simp_rw [(partial_seen_0210 _ _).1, (partial_seen_0210 _ _).2.1,
    (partial_seen_0210 _ _).2.2]
  decide +kernel
private theorem partial_seen_0212 : PrefixCounts (true, true) ![0, 2, 1, 2]
    ![![0, 0, 0, 0, 0, 0], ![32, 0, 0, 0, 0, 32], ![32, 48, 0, 0, 48, 32],
      ![32, 48, 0, 0, 48, 32], ![32, 0, 0, 0, 0, 32], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![56, 0, 0, 0, 0, 56], ![56, 96, 0, 0, 96, 56],
      ![56, 96, 0, 0, 96, 56], ![56, 0, 0, 0, 0, 56], ![0, 0, 0, 0, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_0212 :
    classCount (true, true) ![0, 2, 1, 2] true = 448 ∧
    classCount (true, true) ![0, 2, 1, 2] false = 0 ∧
    rankCount (true, true) ![0, 2, 1, 2] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 2, 1, 2] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![0, 2, 1, 2] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![0, 2, 1, 2] x y) = _
  simp_rw [(partial_seen_0212 _ _).1, (partial_seen_0212 _ _).2.1,
    (partial_seen_0212 _ _).2.2]
  decide +kernel
private theorem partial_seen_1010 : PrefixCounts (true, true) ![1, 0, 1, 0]
    ![![0, 48, 32, 32, 48, 0], ![0, 0, 0, 0, 0, 0], ![0, 48, 0, 0, 48, 0], ![0, 48, 0, 0, 48, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 48, 32, 32, 48, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 96, 56, 56, 96, 0], ![0, 0, 0, 0, 0, 0], ![0, 96, 0, 0, 96, 0], ![0, 96, 0, 0, 96, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 96, 56, 56, 96, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_1010 :
    classCount (true, true) ![1, 0, 1, 0] true = 512 ∧
    classCount (true, true) ![1, 0, 1, 0] false = 0 ∧
    rankCount (true, true) ![1, 0, 1, 0] = 992 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 0, 1, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 0, 1, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![1, 0, 1, 0] x y) = _
  simp_rw [(partial_seen_1010 _ _).1, (partial_seen_1010 _ _).2.1,
    (partial_seen_1010 _ _).2.2]
  decide +kernel
private theorem partial_seen_1012 : PrefixCounts (true, true) ![1, 0, 1, 2]
    ![![0, 48, 16, 16, 48, 0], ![0, 0, 0, 0, 0, 0], ![0, 48, 0, 0, 48, 0], ![0, 48, 0, 0, 48, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 48, 16, 16, 48, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 96, 16, 16, 96, 0], ![0, 0, 0, 0, 0, 0], ![0, 96, 0, 0, 96, 0], ![0, 96, 0, 0, 96, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 96, 16, 16, 96, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_1012 :
    classCount (true, true) ![1, 0, 1, 2] true = 448 ∧
    classCount (true, true) ![1, 0, 1, 2] false = 0 ∧
    rankCount (true, true) ![1, 0, 1, 2] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 0, 1, 2] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 0, 1, 2] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![1, 0, 1, 2] x y) = _
  simp_rw [(partial_seen_1012 _ _).1, (partial_seen_1012 _ _).2.1,
    (partial_seen_1012 _ _).2.2]
  decide +kernel
private theorem partial_seen_1020 : PrefixCounts (true, true) ![1, 0, 2, 0]
    ![![0, 32, 48, 48, 32, 0], ![0, 0, 0, 0, 0, 0], ![0, 32, 0, 0, 32, 0], ![0, 32, 0, 0, 32, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 32, 48, 48, 32, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 56, 96, 96, 56, 0], ![0, 0, 0, 0, 0, 0], ![0, 56, 0, 0, 56, 0], ![0, 56, 0, 0, 56, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 56, 96, 96, 56, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_1020 :
    classCount (true, true) ![1, 0, 2, 0] true = 448 ∧
    classCount (true, true) ![1, 0, 2, 0] false = 0 ∧
    rankCount (true, true) ![1, 0, 2, 0] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 0, 2, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 0, 2, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![1, 0, 2, 0] x y) = _
  simp_rw [(partial_seen_1020 _ _).1, (partial_seen_1020 _ _).2.1,
    (partial_seen_1020 _ _).2.2]
  decide +kernel
private theorem partial_seen_1021 : PrefixCounts (true, true) ![1, 0, 2, 1]
    ![![0, 16, 48, 48, 16, 0], ![0, 0, 0, 0, 0, 0], ![0, 16, 0, 0, 16, 0], ![0, 16, 0, 0, 16, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 16, 48, 48, 16, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 16, 96, 96, 16, 0], ![0, 0, 0, 0, 0, 0], ![0, 16, 0, 0, 16, 0], ![0, 16, 0, 0, 16, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 16, 96, 96, 16, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_1021 :
    classCount (true, true) ![1, 0, 2, 1] true = 320 ∧
    classCount (true, true) ![1, 0, 2, 1] false = 0 ∧
    rankCount (true, true) ![1, 0, 2, 1] = 512 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 0, 2, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 0, 2, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![1, 0, 2, 1] x y) = _
  simp_rw [(partial_seen_1021 _ _).1, (partial_seen_1021 _ _).2.1,
    (partial_seen_1021 _ _).2.2]
  decide +kernel
private theorem partial_seen_1201 : PrefixCounts (true, true) ![1, 2, 0, 1]
    ![![0, 16, 0, 0, 16, 0], ![0, 0, 0, 0, 0, 0], ![48, 16, 0, 0, 16, 48],
      ![48, 16, 0, 0, 16, 48], ![0, 0, 0, 0, 0, 0], ![0, 16, 0, 0, 16, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 16, 0, 0, 16, 0], ![0, 0, 0, 0, 0, 0], ![96, 16, 0, 0, 16, 96],
      ![96, 16, 0, 0, 16, 96], ![0, 0, 0, 0, 0, 0], ![0, 16, 0, 0, 16, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_1201 :
    classCount (true, true) ![1, 2, 0, 1] true = 320 ∧
    classCount (true, true) ![1, 2, 0, 1] false = 0 ∧
    rankCount (true, true) ![1, 2, 0, 1] = 512 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 2, 0, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 2, 0, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![1, 2, 0, 1] x y) = _
  simp_rw [(partial_seen_1201 _ _).1, (partial_seen_1201 _ _).2.1,
    (partial_seen_1201 _ _).2.2]
  decide +kernel
private theorem partial_seen_1202 : PrefixCounts (true, true) ![1, 2, 0, 2]
    ![![0, 32, 0, 0, 32, 0], ![0, 0, 0, 0, 0, 0], ![48, 32, 0, 0, 32, 48],
      ![48, 32, 0, 0, 32, 48], ![0, 0, 0, 0, 0, 0], ![0, 32, 0, 0, 32, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 56, 0, 0, 56, 0], ![0, 0, 0, 0, 0, 0], ![96, 56, 0, 0, 56, 96],
      ![96, 56, 0, 0, 56, 96], ![0, 0, 0, 0, 0, 0], ![0, 56, 0, 0, 56, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_1202 :
    classCount (true, true) ![1, 2, 0, 2] true = 448 ∧
    classCount (true, true) ![1, 2, 0, 2] false = 0 ∧
    rankCount (true, true) ![1, 2, 0, 2] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 2, 0, 2] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 2, 0, 2] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![1, 2, 0, 2] x y) = _
  simp_rw [(partial_seen_1202 _ _).1, (partial_seen_1202 _ _).2.1,
    (partial_seen_1202 _ _).2.2]
  decide +kernel
private theorem partial_seen_1210 : PrefixCounts (true, true) ![1, 2, 1, 0]
    ![![0, 48, 0, 0, 48, 0], ![0, 0, 0, 0, 0, 0], ![16, 48, 0, 0, 48, 16],
      ![16, 48, 0, 0, 48, 16], ![0, 0, 0, 0, 0, 0], ![0, 48, 0, 0, 48, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 96, 0, 0, 96, 0], ![0, 0, 0, 0, 0, 0], ![16, 96, 0, 0, 96, 16],
      ![16, 96, 0, 0, 96, 16], ![0, 0, 0, 0, 0, 0], ![0, 96, 0, 0, 96, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_1210 :
    classCount (true, true) ![1, 2, 1, 0] true = 448 ∧
    classCount (true, true) ![1, 2, 1, 0] false = 0 ∧
    rankCount (true, true) ![1, 2, 1, 0] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 2, 1, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 2, 1, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![1, 2, 1, 0] x y) = _
  simp_rw [(partial_seen_1210 _ _).1, (partial_seen_1210 _ _).2.1,
    (partial_seen_1210 _ _).2.2]
  decide +kernel
private theorem partial_seen_1212 : PrefixCounts (true, true) ![1, 2, 1, 2]
    ![![0, 48, 0, 0, 48, 0], ![0, 0, 0, 0, 0, 0], ![32, 48, 0, 0, 48, 32],
      ![32, 48, 0, 0, 48, 32], ![0, 0, 0, 0, 0, 0], ![0, 48, 0, 0, 48, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 96, 0, 0, 96, 0], ![0, 0, 0, 0, 0, 0], ![56, 96, 0, 0, 96, 56],
      ![56, 96, 0, 0, 96, 56], ![0, 0, 0, 0, 0, 0], ![0, 96, 0, 0, 96, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_1212 :
    classCount (true, true) ![1, 2, 1, 2] true = 512 ∧
    classCount (true, true) ![1, 2, 1, 2] false = 0 ∧
    rankCount (true, true) ![1, 2, 1, 2] = 992 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 2, 1, 2] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![1, 2, 1, 2] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![1, 2, 1, 2] x y) = _
  simp_rw [(partial_seen_1212 _ _).1, (partial_seen_1212 _ _).2.1,
    (partial_seen_1212 _ _).2.2]
  decide +kernel
private theorem partial_seen_2010 : PrefixCounts (true, true) ![2, 0, 1, 0]
    ![![0, 48, 32, 32, 48, 0], ![0, 0, 32, 32, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 32, 32, 0, 0], ![0, 48, 32, 32, 48, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 96, 56, 56, 96, 0], ![0, 0, 56, 56, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 56, 56, 0, 0], ![0, 96, 56, 56, 96, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_2010 :
    classCount (true, true) ![2, 0, 1, 0] true = 448 ∧
    classCount (true, true) ![2, 0, 1, 0] false = 0 ∧
    rankCount (true, true) ![2, 0, 1, 0] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 0, 1, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 0, 1, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![2, 0, 1, 0] x y) = _
  simp_rw [(partial_seen_2010 _ _).1, (partial_seen_2010 _ _).2.1,
    (partial_seen_2010 _ _).2.2]
  decide +kernel
private theorem partial_seen_2012 : PrefixCounts (true, true) ![2, 0, 1, 2]
    ![![0, 48, 16, 16, 48, 0], ![0, 0, 16, 16, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 16, 16, 0, 0], ![0, 48, 16, 16, 48, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 96, 16, 16, 96, 0], ![0, 0, 16, 16, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 16, 16, 0, 0], ![0, 96, 16, 16, 96, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_2012 :
    classCount (true, true) ![2, 0, 1, 2] true = 320 ∧
    classCount (true, true) ![2, 0, 1, 2] false = 0 ∧
    rankCount (true, true) ![2, 0, 1, 2] = 512 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 0, 1, 2] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 0, 1, 2] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![2, 0, 1, 2] x y) = _
  simp_rw [(partial_seen_2012 _ _).1, (partial_seen_2012 _ _).2.1,
    (partial_seen_2012 _ _).2.2]
  decide +kernel
private theorem partial_seen_2020 : PrefixCounts (true, true) ![2, 0, 2, 0]
    ![![0, 32, 48, 48, 32, 0], ![0, 0, 48, 48, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 48, 48, 0, 0], ![0, 32, 48, 48, 32, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 56, 96, 96, 56, 0], ![0, 0, 96, 96, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 96, 96, 0, 0], ![0, 56, 96, 96, 56, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_2020 :
    classCount (true, true) ![2, 0, 2, 0] true = 512 ∧
    classCount (true, true) ![2, 0, 2, 0] false = 0 ∧
    rankCount (true, true) ![2, 0, 2, 0] = 992 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 0, 2, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 0, 2, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![2, 0, 2, 0] x y) = _
  simp_rw [(partial_seen_2020 _ _).1, (partial_seen_2020 _ _).2.1,
    (partial_seen_2020 _ _).2.2]
  decide +kernel
private theorem partial_seen_2021 : PrefixCounts (true, true) ![2, 0, 2, 1]
    ![![0, 16, 48, 48, 16, 0], ![0, 0, 48, 48, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 48, 48, 0, 0], ![0, 16, 48, 48, 16, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 16, 96, 96, 16, 0], ![0, 0, 96, 96, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 96, 96, 0, 0], ![0, 16, 96, 96, 16, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_2021 :
    classCount (true, true) ![2, 0, 2, 1] true = 448 ∧
    classCount (true, true) ![2, 0, 2, 1] false = 0 ∧
    rankCount (true, true) ![2, 0, 2, 1] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 0, 2, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 0, 2, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![2, 0, 2, 1] x y) = _
  simp_rw [(partial_seen_2021 _ _).1, (partial_seen_2021 _ _).2.1,
    (partial_seen_2021 _ _).2.2]
  decide +kernel
private theorem partial_seen_2101 : PrefixCounts (true, true) ![2, 1, 0, 1]
    ![![0, 0, 32, 32, 0, 0], ![48, 0, 32, 32, 0, 48], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![48, 0, 32, 32, 0, 48], ![0, 0, 32, 32, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 56, 56, 0, 0], ![96, 0, 56, 56, 0, 96], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![96, 0, 56, 56, 0, 96], ![0, 0, 56, 56, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_2101 :
    classCount (true, true) ![2, 1, 0, 1] true = 448 ∧
    classCount (true, true) ![2, 1, 0, 1] false = 0 ∧
    rankCount (true, true) ![2, 1, 0, 1] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 1, 0, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 1, 0, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![2, 1, 0, 1] x y) = _
  simp_rw [(partial_seen_2101 _ _).1, (partial_seen_2101 _ _).2.1,
    (partial_seen_2101 _ _).2.2]
  decide +kernel
private theorem partial_seen_2102 : PrefixCounts (true, true) ![2, 1, 0, 2]
    ![![0, 0, 16, 16, 0, 0], ![48, 0, 16, 16, 0, 48], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![48, 0, 16, 16, 0, 48], ![0, 0, 16, 16, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 16, 16, 0, 0], ![96, 0, 16, 16, 0, 96], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![96, 0, 16, 16, 0, 96], ![0, 0, 16, 16, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_2102 :
    classCount (true, true) ![2, 1, 0, 2] true = 320 ∧
    classCount (true, true) ![2, 1, 0, 2] false = 0 ∧
    rankCount (true, true) ![2, 1, 0, 2] = 512 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 1, 0, 2] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 1, 0, 2] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![2, 1, 0, 2] x y) = _
  simp_rw [(partial_seen_2102 _ _).1, (partial_seen_2102 _ _).2.1,
    (partial_seen_2102 _ _).2.2]
  decide +kernel
private theorem partial_seen_2120 : PrefixCounts (true, true) ![2, 1, 2, 0]
    ![![0, 0, 48, 48, 0, 0], ![16, 0, 48, 48, 0, 16], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![16, 0, 48, 48, 0, 16], ![0, 0, 48, 48, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 96, 96, 0, 0], ![16, 0, 96, 96, 0, 16], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![16, 0, 96, 96, 0, 16], ![0, 0, 96, 96, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_2120 :
    classCount (true, true) ![2, 1, 2, 0] true = 448 ∧
    classCount (true, true) ![2, 1, 2, 0] false = 0 ∧
    rankCount (true, true) ![2, 1, 2, 0] = 832 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 1, 2, 0] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 1, 2, 0] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![2, 1, 2, 0] x y) = _
  simp_rw [(partial_seen_2120 _ _).1, (partial_seen_2120 _ _).2.1,
    (partial_seen_2120 _ _).2.2]
  decide +kernel
private theorem partial_seen_2121 : PrefixCounts (true, true) ![2, 1, 2, 1]
    ![![0, 0, 48, 48, 0, 0], ![32, 0, 48, 48, 0, 32], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![32, 0, 48, 48, 0, 32], ![0, 0, 48, 48, 0, 0]]
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]]
    ![![0, 0, 96, 96, 0, 0], ![56, 0, 96, 96, 0, 56], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
      ![56, 0, 96, 96, 0, 56], ![0, 0, 96, 96, 0, 0]] := by
  intro x y; fin_cases x <;> fin_cases y <;> decide +kernel
private theorem row_count_seen_2121 :
    classCount (true, true) ![2, 1, 2, 1] true = 512 ∧
    classCount (true, true) ![2, 1, 2, 1] false = 0 ∧
    rankCount (true, true) ![2, 1, 2, 1] = 992 := by
  simp only [classCount, rankCount, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 1, 2, 1] x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rowPartial (true, true) ![2, 1, 2, 1] x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, rankPartial (true, true) ![2, 1, 2, 1] x y) = _
  simp_rw [(partial_seen_2121 _ _).1, (partial_seen_2121 _ _).2.1,
    (partial_seen_2121 _ _).2.2]
  decide +kernel
section
attribute [local irreducible] classCount rankCount
set_option maxHeartbeats 2000000 in
private theorem row_counts : ∀ s p, Valid s p →
    classCount s p true = (if s.2 then 320 + 64 * rank p else 240) ∧
    classCount s p false = (if s.2 then 0 else 32) ∧
    rankCount s p = (if s.2 then 512 + 160 * rank p else 448) := by
  intro s p h
  rcases s with ⟨x, y⟩
  have hx : x = true := h.1
  subst x
  have he : p = ![p 0, p 1, p 2, p 3] := by
    funext j
    fin_cases j <;> rfl
  rw [he] at h ⊢
  generalize p 0 = a at h ⊢
  generalize p 1 = b at h ⊢
  generalize p 2 = c at h ⊢
  generalize p 3 = d at h ⊢
  cases y <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> first
  | exact absurd h (by decide +kernel)
  | exact row_count_unseen_0101
  | exact row_count_unseen_1010
  | exact row_count_seen_0101
  | exact row_count_seen_0102
  | exact row_count_seen_0120
  | exact row_count_seen_0121
  | exact row_count_seen_0201
  | exact row_count_seen_0202
  | exact row_count_seen_0210
  | exact row_count_seen_0212
  | exact row_count_seen_1010
  | exact row_count_seen_1012
  | exact row_count_seen_1020
  | exact row_count_seen_1021
  | exact row_count_seen_1201
  | exact row_count_seen_1202
  | exact row_count_seen_1210
  | exact row_count_seen_1212
  | exact row_count_seen_2010
  | exact row_count_seen_2012
  | exact row_count_seen_2020
  | exact row_count_seen_2021
  | exact row_count_seen_2101
  | exact row_count_seen_2102
  | exact row_count_seen_2120
  | exact row_count_seen_2121
end
private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
      Valid (finish (false, false) c) (pairs c) := by
  have ht : ∀ x y z t u : Fin 6,
      let c : Row := ![x, y, z, t, u]
      c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
        Valid (finish (false, false) c) (pairs c) := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide +kernel
  intro c
  have he : (![c 0, c 1, c 2, c 3, c 4] : Row) = c := by
    funext j
    fin_cases j <;> rfl
  simpa only [he] using ht (c 0) (c 1) (c 2) (c 3) (c 4)
private theorem initial_partials (x y : Fin 6) :
    firstPartial x y true =
      ![![0, 28, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]] x y ∧
    firstPartial x y false =
      ![![0, 8, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]] x y ∧
    firstRankPartial x y =
      ![![0, 44, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
        ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]] x y := by
  fin_cases x <;> fin_cases y <;> decide +kernel
private theorem initial_counts : firstCount true = 28 ∧ firstCount false = 8 ∧
    firstRank = 44 := by
  simp only [firstCount, firstRank, sum_rows]
  change (∑ x : Fin 6, ∑ y : Fin 6, firstPartial x y true) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, firstPartial x y false) = _ ∧
    (∑ x : Fin 6, ∑ y : Fin 6, firstRankPartial x y) = _
  simp_rw [(initial_partials _ _).1, (initial_partials _ _).2.1,
    (initial_partials _ _).2.2]
  decide +kernel
/-- The weighted one-row transfer and initial-row counts. -/
theorem finite_certificate :
    (∀ s p, Valid s p →
      classCount s p true = (if s.2 then 320 + 64 * rank p else 240) ∧
      classCount s p false = (if s.2 then 0 else 32) ∧
      rankCount s p = (if s.2 then 512 + 160 * rank p else 448)) ∧
    firstCount true = 28 ∧ firstCount false = 8 ∧ firstRank = 44 :=
  ⟨row_counts, initial_counts⟩
private def w : ℕ → Fin 3 → ℤ
  | 0, i => if i = 2 then 0 else 1
  | n + 1, i => if i = 0 then 32 * w n 0 + 240 * w n 1 + 448 * w n 2 else
      if i = 1 then 320 * w n 1 + 512 * w n 2 else 64 * w n 1 + 160 * w n 2
private def eval (n : ℕ) (s : Seen) (p : Boundary) : ℤ :=
  if s.2 then w n 1 + rank p * w n 2 else w n 0
private theorem v_eq_w (n : ℕ) (s : Seen) (p : Boundary) (h : Valid s p) :
    v n s p = eval n s p := by
  induction n generalizing s p with
  | zero => simp [v, widthV, eval, w]
  | succ n ih =>
    rw [v, widthV, widthStep]
    change (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c then
      v n (finish s c) (pairs c) else 0) = _
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (pairs c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then (1 : ℤ) else 0) * w n 1 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then rank (pairs c) else 0) * w n 2 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = false
          then (1 : ℤ) else 0) * w n 0 := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s h.1 c ⟨hc.1, hc.2.2⟩)]
        cases hb : (finish s c).2 <;> simp [eval, hc, hb]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    change classCount s p true * w n 1 + rankCount s p * w n 2 +
      classCount s p false * w n 0 = eval (n + 1) s p
    rw [(finite_certificate.1 s p h).1, (finite_certificate.1 s p h).2.1,
      (finite_certificate.1 s p h).2.2]
    cases hb : s.2 <;> simp [hb, eval, w] <;> ring
private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = 8 * w n 0 + 28 * w n 1 + 44 * w n 2 := by
  rw [counting_bridge, total, widthTotal]
  change (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
    v n (finish (false, false) c) (pairs c) else 0) = _
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (pairs c) else 0) =
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then (1 : ℤ) else 0) * w n 1 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then rank (pairs c) else 0) * w n 2 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) * w n 0 := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w _ _ _ (initial_valid c hc)]
      cases hb : (finish (false, false) c).2 <;> simp [eval, hc, hb]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  change firstCount true * w n 1 + firstRank * w n 2 + firstCount false * w n 0 = _
  rw [finite_certificate.2.1, finite_certificate.2.2.1, finite_certificate.2.2.2]
  ring
private theorem recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = 512 * a (n + 3) - 33792 * a (n + 2) +
      589824 * a (n + 1) := by
  rw [show n + 4 = ((n + 1) + 1) + 1 + 1 by omega,
    a_eq_w, a_eq_w, a_eq_w, a_eq_w]
  simp only [w]
  norm_num
  ring
private theorem zero_count : a 0 = 0 := by
  simp [a, Legal]
attribute [local irreducible] a
open PowerSeries in
/-- Barker's identity for the literal count, with `a 0 = 0`. -/
theorem result :
    (1 - 32 * X) * (1 - 480 * X + 18432 * X ^ 2) *
      (PowerSeries.mk fun n => (a n : ℤ)) = 4 * X * (9 - 1120 * X + 30720 * X ^ 2) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 32 * X) * (1 - 480 * X + 18432 * X ^ 2) * F =
      F - 512 * (F * X ^ 1) + 33792 * (F * X ^ 2) -
        589824 * (F * X ^ 3) := by ring
  have hr : (4 * X * (9 - 1120 * X + 30720 * X ^ 2) : PowerSeries ℤ) =
      36 * X - 4480 * X ^ 2 + 122880 * X ^ 3 := by ring
  change (1 - 32 * X) * (1 - 480 * X + 18432 * X ^ 2) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_right (show n ≠ 1 by omega),
      ite_eq_right (show n ≠ 2 by omega), ite_eq_right (show n ≠ 3 by omega)]
    have hh := recurrence (n - 4)
    have h4 : n - 4 + 4 = n := by omega
    have h3 : n - 4 + 3 = n - 1 := by omega
    have h2 : n - 4 + 2 = n - 2 := by omega
    have h1 : n - 4 + 1 = n - 3 := by omega
    rw [h4, h3, h2, h1] at hh
    linarith
  · have h1 := a_eq_w 0
    have h2 := a_eq_w 1
    have h3 := a_eq_w 2
    norm_num [w] at h1 h2 h3
    interval_cases n <;> norm_num only [zero_count, h1, h2, h3,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, if_true, if_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero, zero_add] <;> ring
end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip
