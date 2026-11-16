/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoColumnOne
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingTwoColumnOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoColumnOne.result; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoColumnOne.certificate
   digest: The two-defect path recurrence from canonical colour-introduction states. -/

/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of result)
Prefix: proof_shape=bind-only; consumers=prefix_cons, prefix_zero
prefix_cons: proof_shape=content; consumers=accepted_iff
prefix_zero: proof_shape=bind-only; consumers=literal_bridge
cost: proof_shape=bind-only; consumers=Accepted, transfer_counts
acceptedDecidable: proof_shape=bind-only; consumers=count, count_step
Accepted: proof_shape=bind-only; consumers=accepted_iff, count_step, count_matrix
tailCost: proof_shape=bind-only; consumers=tailCost_step, adjacent_tail, accepted_iff
tailCost_step: proof_shape=bind-only; consumers=accepted_iff, adjacent_tail
adjacent_tail: proof_shape=content; consumers=grid_defects
grid_defects: proof_shape=bind-only; consumers=literal_bridge
accepted_iff: proof_shape=content; consumers=literal_bridge
count: proof_shape=bind-only; consumers=count_step, count_matrix, literal_bridge
count_step: proof_shape=bind-only; consumers=count_matrix
transfer: proof_shape=bind-only; consumers=certificate, count_matrix, result
terminal: proof_shape=bind-only; consumers=certificate, count_matrix, result
index: proof_shape=bind-only; consumers=transfer_counts, count_matrix
transfer_counts: proof_shape=bind-only; consumers=count_matrix
count_matrix: proof_shape=content; consumers=result
literal_bridge: proof_shape=content; consumers=result
backwardTable: proof_shape=bind-only; consumers=certificate, powers_table
powers_table: proof_shape=bind-only; consumers=result
certificate: proof_shape=bind-only; consumers=powers_table, result
result: proof_shape=bind-only; consumers=none (external open-problem-resolution #30655 C1)
-/

import D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingPath
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

/-! Canonical paths retain the number of introduced colours and the exact remaining budget. -/
open scoped BigOperators Matrix
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoColumnOne
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open KingGrid (Cell Edge mono)

private def Prefix {n : ℕ} (m : ℕ) (f : Fin n → Fin 4) : Prop :=
  ∀ i b, b < f i → b.val < m ∨ ∃ j, j < i ∧ f j = b

private theorem prefix_zero {n : ℕ} (f : Fin n → Fin 4) :
    Prefix 0 f ↔ Canonical f := by
  simp [Prefix, Canonical]

private theorem prefix_cons {n : ℕ} (m : ℕ) (c : Fin 4) (f : Fin n → Fin 4) :
    Prefix m (Fin.cons c f) ↔ c.val ≤ m ∧ Prefix (max m (c.val + 1)) f := by
  constructor
  · intro h
    have hc : c.val ≤ m := by
      by_contra hm
      have hm4 : m < 4 := by omega
      rcases h 0 ⟨m, hm4⟩ (show m < c.val from by omega) with hb | ⟨j, hj, _⟩
      · exact (Nat.lt_irrefl m) hb
      · exact (Fin.not_lt_zero j) hj
    refine ⟨hc, fun i b hb => ?_⟩
    rcases h i.succ b hb with hh | ⟨j, hj, he⟩
    · exact Or.inl (by omega)
    · cases j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero] at he
        exact Or.inl (by omega)
      | succ j => exact Or.inr ⟨j, Fin.succ_lt_succ_iff.mp hj, he⟩
  · rintro ⟨hc, h⟩ i
    cases i using Fin.cases with
    | zero =>
      intro b hb
      exact Or.inl (lt_of_lt_of_le (show b.val < c.val from hb) hc)
    | succ i =>
      intro b hb
      rcases h i b hb with hh | ⟨j, hj, he⟩
      · by_cases hm : b.val < m
        · exact Or.inl hm
        · right
          have he : c = b := Fin.ext (by omega)
          exact ⟨0, by simp, he⟩
      · exact Or.inr ⟨j.succ, Fin.succ_lt_succ_iff.mpr hj, he⟩

private def cost (p c : Fin 4) : ℕ := if p = c then 1 else 0

private def Accepted : {n : ℕ} → ℕ → Fin 4 → ℕ → (Fin n → Fin 4) → Prop
  | 0, _, _, d, _ => d = 0
  | _ + 1, m, p, d, f =>
    (f 0).val ≤ m ∧ cost p (f 0) ≤ d ∧
      Accepted (max m ((f 0).val + 1)) (f 0) (d - cost p (f 0)) (Fin.tail f)

private instance acceptedDecidable {n : ℕ} (m : ℕ) (p : Fin 4) (d : ℕ)
    (f : Fin n → Fin 4) : Decidable (Accepted m p d f) := by
  induction n generalizing m p d with
  | zero => exact inferInstanceAs (Decidable (d = 0))
  | succ n ih =>
    change Decidable ((f 0).val ≤ m ∧ cost p (f 0) ≤ d ∧ _)
    letI := ih (max m ((f 0).val + 1)) (f 0) (d - cost p (f 0)) (Fin.tail f)
    infer_instance

private def count (n m : ℕ) (p : Fin 4) (d : ℕ) : ℤ :=
  ∑ f : Fin n → Fin 4, if Accepted m p d f then 1 else 0

private def tailCost {n : ℕ} (p : Fin 4) (f : Fin n → Fin 4) : ℕ :=
  tailDefects (q := 4) (k := 1) ∅ {(0, 0)} (fun _ => p)
    (List.ofFn fun i _ => f i)

private theorem tailCost_step {n : ℕ} (p c : Fin 4) (f : Fin n → Fin 4) :
    tailCost p (Fin.cons c f) = cost p c + tailCost c f := by
  by_cases h : p = c <;>
    simp [tailCost, List.ofFn_succ, tailDefects, bondDefects, cost, h]

private theorem accepted_iff {n : ℕ} (m : ℕ) (p : Fin 4) (d : ℕ)
    (f : Fin n → Fin 4) : Accepted m p d f ↔ Prefix m f ∧ tailCost p f = d := by
  induction n generalizing m p d with
  | zero => simp [Accepted, Prefix, tailCost, tailDefects, eq_comm]
  | succ n ih =>
    rw [← Fin.cons_self_tail f]
    rw [prefix_cons, tailCost_step]
    change (_ ∧ _ ∧ Accepted _ _ _ _) ↔ _
    rw [ih]
    simp only [Fin.cons_zero, Fin.tail_cons]
    constructor
    · rintro ⟨hc, hd, hf, he⟩
      exact ⟨⟨hc, hf⟩, by omega⟩
    · rintro ⟨⟨hc, hf⟩, he⟩
      exact ⟨hc, by omega, hf, by omega⟩

private theorem adjacent_tail (n : ℕ) (f : Fin (n + 1) → Fin 4) :
    tailCost (f 0) (Fin.tail f) =
      ∑ i : Fin n, cost (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => simp [tailCost, tailDefects]
  | succ n ih =>
    rw [← Fin.cons_self_tail (Fin.tail f), tailCost_step, Fin.sum_univ_succ]
    exact congrArg (fun x => cost (f 0) (f (Fin.succ 0)) + x) (ih (Fin.tail f))

private theorem grid_defects (n : ℕ) (f : Cell (n + 1) 1 → Fin 4) :
    (Finset.univ.filter (fun e : Edge (n + 1) 1 => mono f e)).card =
      tailCost (f (0, 0)) (fun i : Fin n => f (i.succ, 0)) := by
  change _ = tailCost (f (0, 0)) (Fin.tail (fun i => f (i, 0)))
  rw [adjacent_tail n (fun i => f (i, 0))]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, KingGrid.sum_edges]
  simp only [Nat.reduceSub, Nat.sub_self, Fin.sum_univ_zero, Fin.sum_univ_one,
    Finset.sum_const_zero, zero_add, add_zero]
  have hsum : (∑ i : Fin (n + 1 - 1),
      if f (KingGrid.lo i, 0) = f (KingGrid.hi i, 0) then 1 else 0) =
      ∑ i : Fin n, cost (f (i.castSucc, 0)) (f (i.succ, 0)) := by
    let E : Fin (n + 1 - 1) ≃ Fin n := finCongr (by omega)
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  exact hsum

private theorem literal_bridge (n : ℕ) :
    (KingTwoGrid.T (n + 1) 1 : ℤ) = count n 1 0 2 := by
  classical
  let E : (Cell (n + 1) 1 → Fin 4) ≃ (Fin (n + 1) → Fin 4) := {
    toFun f i := f (i, 0)
    invFun f p := f p.1
    left_inv f := by
      funext p
      exact congrArg f (Prod.ext rfl (Subsingleton.elim (0 : Fin 1) p.2))
    right_inv f := rfl }
  have normal (f : Cell (n + 1) 1 → Fin 4) : KingGrid.normal f ↔ Canonical (E f) := by
    have h : (fun p : Cell (n + 1) 1 => E f p.1) = f := by
      funext p
      exact congrArg f (Prod.ext rfl (Subsingleton.elim (0 : Fin 1) p.2))
    rw [← h]
    exact KingPath.normal_path (E f)
  let F : {f : Cell (n + 1) 1 → Fin 4 // KingTwoGrid.TwoDefect f ∧ KingGrid.normal f} ≃
      {f : Fin (n + 1) → Fin 4 //
        Prefix 0 f ∧ tailCost (f 0) (Fin.tail f) = 2} := E.subtypeEquiv (by
    intro f
    rw [prefix_zero, ← normal]
    rw [KingTwoGrid.TwoDefect, grid_defects]
    exact and_comm)
  let G : {f : Fin (n + 1) → Fin 4 //
        Prefix 0 f ∧ tailCost (f 0) (Fin.tail f) = 2} ≃
      {f : Fin n → Fin 4 // Accepted 1 0 2 f} := {
    toFun f := ⟨Fin.tail f.val, by
      have h := (prefix_cons 0 (f.val 0) (Fin.tail f.val)).mp
        (by simpa using f.property.1)
      have hz : f.val 0 = 0 := Fin.ext (by omega)
      rw [accepted_iff]
      simpa [hz] using And.intro h.2 f.property.2⟩
    invFun f := ⟨Fin.cons 0 f.val, by
      have h := (accepted_iff 1 0 2 f.val).mp f.property
      exact ⟨(prefix_cons 0 0 f.val).mpr ⟨by decide, h.1⟩, h.2⟩⟩
    left_inv f := by
      apply Subtype.ext
      have h := (prefix_cons 0 (f.val 0) (Fin.tail f.val)).mp
        (by simpa using f.property.1)
      have hz : f.val 0 = 0 := Fin.ext (by omega)
      simpa [hz] using Fin.cons_self_tail f.val
    right_inv f := by apply Subtype.ext; funext i; rfl }
  have h := Nat.card_congr (F.trans G)
  rw [KingTwoGrid.T, h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.natCast_card_filter]
  rfl

private theorem count_step (n m : ℕ) (p : Fin 4) (d : ℕ) :
    count (n + 1) m p d = ∑ c : Fin 4,
      if c.val ≤ m ∧ cost p c ≤ d then
        count n (max m (c.val + 1)) c (d - cost p c) else 0 := by
  unfold count
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 4)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ f : Fin n → Fin 4,
    if c.val ≤ m ∧ cost p c ≤ d ∧
      Accepted (max m (c.val + 1)) c (d - cost p c) f then (1 : ℤ) else 0) = _
  by_cases hc : c.val ≤ m ∧ cost p c ≤ d
  · simp [hc.1, hc.2]
  · simp only [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro f _
    exact ite_eq_right (fun h => hc ⟨h.1, h.2.1⟩)

private def index (m d : ℕ) : Fin 12 := ⟨(3 * (m - 1) + d) % 12, Nat.mod_lt _ (by decide)⟩

private def transfer : Matrix (Fin 12) (Fin 12) ℤ :=
  fun i j =>
    (if j = i then (i.val / 3 : ℤ) else 0) +
    (if i.val % 3 > 0 ∧ j.val + 1 = i.val then 1 else 0) +
    (if i.val < 9 ∧ j.val = i.val + 3 then 1 else 0)

private def terminal : Fin 12 → ℤ := fun i => if i.val % 3 = 0 then 1 else 0

private theorem transfer_counts (m : Fin 5) (p : Fin 4) (d : Fin 3)
    (hm : 1 ≤ m.val) (hp : p.val < m.val) (w : Fin 12 → ℤ) :
    (∑ c : Fin 4, if c.val ≤ m.val ∧ cost p c ≤ d.val then
      w (index (max m.val (c.val + 1)) (d.val - cost p c)) else 0) =
      (transfer.mulVec w) (index m.val d.val) := by
  fin_cases m <;> fin_cases p <;> fin_cases d <;>
    simp_all [cost, index, transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem count_matrix (n m : ℕ) (p : Fin 4) (d : ℕ)
    (hm : 1 ≤ m ∧ m ≤ 4) (hp : p.val < m) (hd : d ≤ 2) :
    count n m p d = ((transfer ^ n).mulVec terminal) (index m d) := by
  induction n generalizing m p d with
  | zero =>
    simp only [count, Accepted, pow_zero, Matrix.one_mulVec]
    have he : (index m d).val % 3 = d := by
      have hlt : 3 * (m - 1) + d < 12 := by omega
      simp only [index, Fin.val_mk, Nat.mod_eq_of_lt hlt]
      omega
    simp only [terminal, he]
    exact Fintype.sum_unique _
  | succ n ih =>
    rw [count_step, pow_succ', ← Matrix.mulVec_mulVec]
    rw [← transfer_counts ⟨m, by omega⟩ p ⟨d, by omega⟩ hm.1 hp]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs with hc
    · exact ih _ _ _ (by constructor <;> omega) (by omega) (by omega)
    · rfl


private def backwardTable : Fin 10 → Fin 12 → ℤ :=
  ![![1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0],
    ![1, 1, 0, 2, 1, 0, 3, 1, 0, 3, 1, 0],
    ![2, 2, 1, 5, 4, 1, 9, 6, 1, 9, 6, 1],
    ![5, 6, 3, 14, 15, 6, 27, 27, 9, 27, 27, 9],
    ![14, 20, 12, 41, 56, 30, 81, 108, 54, 81, 108, 54],
    ![41, 70, 50, 122, 205, 140, 243, 405, 270, 243, 405, 270],
    ![122, 246, 210, 365, 732, 615, 729, 1458, 1215, 729, 1458, 1215],
    ![365, 854, 861, 1094, 2555, 2562, 2187, 5103, 5103, 2187, 5103, 5103],
    ![1094, 2920, 3416, 3281, 8752, 10220, 6561, 17496, 20412, 6561, 17496, 20412],
    ![3281, 9846, 13140, 9842, 29529, 39384, 19683, 59049, 78732, 19683, 59049, 78732]]

private theorem certificate :
    (backwardTable 0 = terminal ∧ ∀ i : Fin 9,
      backwardTable i.succ = Matrix.vecMul (backwardTable i.castSucc) transferᵀ) ∧
    backwardTable 9 = ∑ j : Fin 6,
      (![-27, 108, -171, 136, -57, 12] j : ℤ) • backwardTable ⟨3 + j.val, by omega⟩ := by
  decide +kernel

private theorem powers_table (i : Fin 10) :
    forward transferᵀ terminal i.val = backwardTable i := by
  induction i using Fin.induction with
  | zero => exact certificate.1.1.symm
  | succ i ih =>
    rw [forward, Fin.val_succ, Function.iterate_succ_apply']
    change Matrix.vecMul (forward transferᵀ terminal i.val) transferᵀ = backwardTable i.succ
    change forward transferᵀ terminal i.val = backwardTable i.castSucc at ih
    rw [ih]
    exact (certificate.1.2 i).symm

/-- The literal k=1 recurrence at every registered index n≥10. -/
theorem result (n : ℕ) (hn : 10 ≤ n) :
    (KingTwoGrid.T n 1 : ℤ) =
      12 * KingTwoGrid.T (n - 1) 1 - 57 * KingTwoGrid.T (n - 2) 1 +
      136 * KingTwoGrid.T (n - 3) 1 - 171 * KingTwoGrid.T (n - 4) 1 +
      108 * KingTwoGrid.T (n - 5) 1 - 27 * KingTwoGrid.T (n - 6) 1 := by
  have poly : forward transferᵀ terminal (3 + 6) =
      ∑ j : Fin 6, (![-27, 108, -171, 136, -57, 12] j : ℤ) •
        forward transferᵀ terminal (3 + j.val) := by
    rw [powers_table ⟨9, by omega⟩]
    simp_rw [show ∀ j : Fin 6,
        forward transferᵀ terminal (3 + j.val) = backwardTable ⟨3 + j.val, by omega⟩
      from fun j => powers_table ⟨3 + j.val, by omega⟩]
    exact certificate.2
  have bridge (m : ℕ) :
      dotProduct terminal (((transferᵀ) ^ m).mulVec (Pi.single 2 1)) =
        (KingTwoGrid.T (m + 1) 1 : ℤ) := by
    rw [← Matrix.transpose_pow, Matrix.dotProduct_transpose_mulVec]
    rw [single_dotProduct]
    simpa only [one_mul, show index 1 2 = 2 from rfl] using
      ((literal_bridge m).trans
        (count_matrix m 1 0 2 (by omega) (by decide) (by omega))).symm
  have h := forward_shift transferᵀ terminal (Pi.single 2 1) 6 3
    ![-27, 108, -171, 136, -57, 12] poly (n - 10)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ] at h
  simp_rw [bridge] at h
  have hi : n - 10 + 3 + 6 + 1 = n := by omega
  have h0 : n - 10 + 3 + 0 + 1 = n - 6 := by omega
  have h1 : n - 10 + 3 + (0 + 1) + 1 = n - 5 := by omega
  have h2 : n - 10 + 3 + (0 + 1 + 1) + 1 = n - 4 := by omega
  have h3 : n - 10 + 3 + (0 + 1 + 1 + 1) + 1 = n - 3 := by omega
  have h4 : n - 10 + 3 + (0 + 1 + 1 + 1 + 1) + 1 = n - 2 := by omega
  have h5 : n - 10 + 3 + (0 + 1 + 1 + 1 + 1 + 1) + 1 = n - 1 := by omega
  rw [hi, h5, h4, h3, h2, h1, h0] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoColumnOne
