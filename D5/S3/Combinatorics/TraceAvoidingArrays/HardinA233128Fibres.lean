/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Fibres
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Fibres
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate
   digest: Exact scanner fibres and finite row-sum coordinates. -/

/-
admission_basis: open-problem-resolution (#28672; Proved)
escape_witness: none; all-height class reduction is semiconjugacy iteration.
After normalizing finite one-step premises, v_eq_w is an instance of
Function.Semiconj.iterate_right. It and its downstream chain are bind-only.
Declaration namespace: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
Direct frozen dependencies (declaration GIDs and statement_ids):
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowFinish
statement_id: sha256:ded50bd8c5de69b5b2324e575fee135f275ae05b5bb30b328b0e5c0313d86b07
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowWeight
statement_id: sha256:076a03b0e19556ba67d0faed8d8d552fb3d55e6c40992d9c52c88faad85e373a
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.scanner_fibres
statement_id: sha256:63a356389be3d9bf756c53fb12271299a7668c1123562d84a2e34e78a341fc90
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow
statement_id: sha256:e97b1a06b78d944d101465bdc94301416cfe964a1e9cbf900093e9cd04d04132
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Row
statement_id: sha256:bfdef18389c25a4e0e0289ec0c41644aaf42d71c7a4d540ac5103952779dfd2c
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.decidableRowLegal
statement_id: sha256:566fa77bfdf47796ff0524d5a78f68b96413ca55006aa1429a767aad72408b70
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowLegal
statement_id: sha256:ad59d456a8f5b2710481be3ed4a9d79e276a0e4319f7b6918310d350fc440508
GID: D5/S3/Observer/Separation/BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
class_fibres: proof_shape=bind-only; consumers=class_fibres_normalized
labelTail: proof_shape=bind-only; consumers=tail_sum, class_fibres_normalized
tail_sum: proof_shape=bind-only; consumers=class_fibres_normalized
binary_sum: proof_shape=bind-only; consumers=class_fibres_normalized
class_fibres_normalized: proof_shape=bind-only; consumers=completed_0101010, unseen_0101010
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases

/-! Exact scanner fibres and finite row-sum coordinates. -/

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip (widthLegal colour_bond_iff)
open HardinA233255PairTransfer (Row rowLegal PairRow rowProper)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype
private theorem class_fibres (s : Seen) (p : PairRow) (k : Fin 21) :
    classCount s p k = ∑ q : PairRow,
      rowWeight s q * if (∀ j : Fin 6, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j) ∧ boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 7 s (fun t q =>
    if (∀ j : Fin 6, q j.castSucc ≠ q j.succ) ∧
      (∀ j, p j ≠ q j) ∧ boundaryClass t q = k then (1 : ℤ) else 0)]
  unfold classCount
  apply Finset.sum_congr rfl
  intro c _
  simp only [← colour_bond_iff]
  change (if rowLegal c ∧ compatible p c ∧ good s c ∧
      boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) =
    if good s c then (if rowLegal c ∧ compatible p c ∧
      boundaryClass (finish s c) (labels c) = k then 1 else 0) else 0
  by_cases hg : good s c <;> simp [hg]

private def labelTail : {k : ℕ} → Fin 3 → (Fin k → Fin 2) → (Fin k → Fin 3)
  | 0, _, _ => Fin.elim0
  | _ + 1, a, b => Fin.cons (a.succAbove (b 0))
      (labelTail (a.succAbove (b 0)) (Fin.tail b))

private theorem tail_sum (k : ℕ) (a : Fin 3) (H : (Fin k → Fin 3) → ℤ) :
    (∑ q : Fin k → Fin 3,
      if (∀ j : Fin k, (Fin.cons a q : Fin (k + 1) → Fin 3) j.castSucc ≠
          (Fin.cons a q : Fin (k + 1) → Fin 3) j.succ)
        then H q else 0) = ∑ b : Fin k → Fin 2, H (labelTail a b) := by
  induction k generalizing a with
  | zero =>
    simp [labelTail]
    congr 1
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 3)).sum_comp,
      Fintype.sum_prod_type]
    have hs (x : Fin 3) :
        (∑ q : Fin k → Fin 3,
          if (∀ j : Fin (k + 1),
              (Fin.cons a (Fin.cons x q) : Fin (k + 2) → Fin 3) j.castSucc ≠
                (Fin.cons a (Fin.cons x q) : Fin (k + 2) → Fin 3) j.succ)
            then H (Fin.cons x q) else 0) =
        if a ≠ x then ∑ b : Fin k → Fin 2, H (Fin.cons x (labelTail x b)) else 0 := by
      by_cases hx : a ≠ x
      · simpa [Fin.forall_fin_succ, Fin.castSucc_succ, hx] using
          ih x (fun q => H (Fin.cons x q))
      · simp [Fin.forall_fin_succ, Fin.castSucc_succ, hx]
    change (∑ x : Fin 3, ∑ q : Fin k → Fin 3,
      if (∀ j : Fin (k + 1),
          (Fin.cons a (Fin.cons x q) : Fin (k + 2) → Fin 3) j.castSucc ≠
            (Fin.cons a (Fin.cons x q) : Fin (k + 2) → Fin 3) j.succ)
        then H (Fin.cons x q) else 0) = _
    rw [Finset.sum_congr rfl (fun x _ => hs x)]
    rw [Fin.sum_univ_succAbove _ a]
    simp only [ne_self_iff_false, ↓reduceIte, zero_add]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 2)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    have hn : a ≠ a.succAbove b := (Fin.succAbove_ne a b).symm
    simp [Fin.consEquiv, labelTail, hn]

private theorem binary_sum (g : (Fin 6 → Fin 2) → ℤ) :
    (∑ b, g b) = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2,
      ∑ d : Fin 2, ∑ e : Fin 2, ∑ f : Fin 2, g ![a, b, c, d, e, f] := by
  let e : (Fin 6 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 :=
    { toFun := fun q => (q 0, q 1, q 2, q 3, q 4, q 5)
      invFun := fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2.1,
        t.2.2.2.2.1, t.2.2.2.2.2]
      left_inv := by intro q; ext j; fin_cases j <;> rfl
      right_inv := by rintro ⟨a, b, c, d, e, f⟩; rfl }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem class_fibres_normalized (s : Seen) (p : PairRow) (k : Fin 21) :
    classCount s p k = ∑ q0 : Fin 3, ∑ b1 : Fin 2, ∑ b2 : Fin 2,
      ∑ b3 : Fin 2, ∑ b4 : Fin 2, ∑ b5 : Fin 2, ∑ b6 : Fin 2,
      let q := Fin.cons q0 (labelTail q0 ![b1, b2, b3, b4, b5, b6])
      rowWeight s q * if (∀ j : Fin 7, p j ≠ q j) ∧
        boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [class_fibres, ← (Fin.consEquiv (fun _ : Fin 7 => Fin 3)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have h (q : Fin 6 → Fin 3) :
      rowWeight s (Fin.cons a q) *
        (if (∀ j : Fin 6, (Fin.cons a q : PairRow) j.castSucc ≠ (Fin.cons a q : PairRow) j.succ) ∧
            (∀ j : Fin 7, p j ≠ (Fin.cons a q : PairRow) j) ∧
            boundaryClass (rowFinish s (Fin.cons a q)) (Fin.cons a q) = k
          then 1 else 0) =
        if (∀ j : Fin 6, (Fin.cons a q : PairRow) j.castSucc ≠
            (Fin.cons a q : PairRow) j.succ) then
          rowWeight s (Fin.cons a q) *
            (if (∀ j : Fin 7, p j ≠ (Fin.cons a q : PairRow) j) ∧
                boundaryClass (rowFinish s (Fin.cons a q)) (Fin.cons a q) = k
              then 1 else 0) else 0 := by
    split_ifs <;> simp_all
  change (∑ q : Fin 6 → Fin 3, rowWeight s (Fin.cons a q) *
    (if (∀ j : Fin 6, (Fin.cons a q : PairRow) j.castSucc ≠
        (Fin.cons a q : PairRow) j.succ) ∧
      (∀ j : Fin 7, p j ≠ (Fin.cons a q : PairRow) j) ∧
      boundaryClass (rowFinish s (Fin.cons a q)) (Fin.cons a q) = k
      then 1 else 0)) = _
  rw [Finset.sum_congr rfl (fun q _ => h q)]
  rw [tail_sum, binary_sum]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
