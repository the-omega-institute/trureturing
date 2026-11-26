/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres.generating_function; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres.row_table,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres.initial_pairs,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres.powers_table,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres.power_relation,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres.four_initial,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres.three_next,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233198PairFibres.three_initial
   digest: Literal eight-colour arrays and their ordered complementary-pair fibres. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198LiteralModel

/-! Complementary-pair fibres with strict row-major colour prerequisites.
The numerical reduction serves the full generating_function, not finite agreement.
Its row_table and initial_pairs are consumed by ordinary_transfer; powers_table
and power_relation by four_recurrence; three_next and three_initial by
three_transfer. All premises are proved on the same contained-edge graph.
The fibre and graph-row equivalences supply the non-numerical counting bridges.
The imported literal counting module directly consumes the published Fin8 bond
criterion inside its fibre construction. -/

set_option Elab.async false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres

open scoped BigOperators

/-- The full generating-function assertion, as a proposition rather than an assumed theorem. -/
def GeneratingFunction : Prop := A = numerator * denominator⁻¹


private theorem row_horizontal {q : ℕ} (r : Row q) {j k : Fin 4}
    (h : k.val = j.val + 1) : r.1 j ≠ r.1 k := by
  have hj : j.val < 3 := by omega
  simpa only [show (⟨j.val, hj⟩ : Fin 3).castSucc = j from rfl,
    show (⟨j.val, hj⟩ : Fin 3).succ = k from Fin.ext h.symm] using r.2 ⟨j.val, hj⟩

private theorem proper_cons_iff {q n : ℕ} (r : Row q) (f : Fin n → Row q) :
    Proper (fun v : Cell (n + 1) => ((Fin.cons r f : Fin (n + 1) → Row q) v.1).1 v.2) ↔
      Proper (fun v : Cell n => (f v.1).1 v.2) ∧
        ∀ i : Fin n, i.val = 0 → compatible r (f i) := by
  constructor
  · intro h
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ he
      have hs : Edge (i.succ, j) (k.succ, l) := by
        dsimp only [Edge, Prod.fst, Prod.snd] at he ⊢
        rcases he with ⟨he, hc⟩ | ⟨he, hc⟩ | ⟨he, hc⟩
        · exact Or.inl ⟨congrArg Fin.succ he, hc⟩
        · exact Or.inr (Or.inl ⟨by simpa using congrArg Nat.succ he, hc⟩)
        · exact Or.inr (Or.inr ⟨by simpa using congrArg Nat.succ he, hc⟩)
      exact h (i.succ, j) (k.succ, l) hs
    · intro i hi
      constructor
      · intro j
        exact h (0, j) (i.succ, j) (Or.inr (Or.inl ⟨by simpa using hi, rfl⟩))
      · intro j
        exact h (0, j.succ) (i.succ, j.castSucc)
          (Or.inr (Or.inr ⟨by simpa using hi, rfl⟩))
  · rintro ⟨ht, hb⟩ ⟨i, j⟩ ⟨k, l⟩ he
    dsimp only [Edge, Prod.fst, Prod.snd] at he
    cases i using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero =>
        change r.1 j ≠ r.1 l
        have hh : l.val = j.val + 1 := by
          rcases he with h | h | h
          · exact h.2
          · have := h.1; simp at this
          · have := h.1; simp at this
        exact row_horizontal r hh
      | succ k =>
        change r.1 j ≠ (f k).1 l
        have hk : k.val = 0 := by
          rcases he with h | h | h
          · have := congrArg Fin.val h.1; simp at this
          · have := h.1; simp only [Fin.val_succ, Fin.val_zero] at this; omega
          · have := h.1; simp only [Fin.val_succ, Fin.val_zero] at this; omega
        have hc := hb k hk
        rcases he with h | h | h
        · have := congrArg Fin.val h.1; simp at this
        · simpa only [h.2] using hc.1 l
        · have hl : l.val < 3 := by have := h.2; omega
          simpa only [show (⟨l.val, hl⟩ : Fin 3).castSucc = l from rfl,
            show (⟨l.val, hl⟩ : Fin 3).succ = j from Fin.ext h.2.symm] using hc.2 ⟨l.val, hl⟩
    | succ i =>
      cases k using Fin.cases with
      | zero =>
        rcases he with h | h | h
        · have := congrArg Fin.val h.1; simp at this
        · have := h.1; simp only [Fin.val_succ, Fin.val_zero] at this; omega
        · have := h.1; simp only [Fin.val_succ, Fin.val_zero] at this; omega
      | succ k =>
        change (f i).1 j ≠ (f k).1 l
        apply ht (i, j) (k, l)
        dsimp only [Edge, Prod.fst, Prod.snd]
        rcases he with h | h | h
        · exact Or.inl ⟨Fin.succ_inj.mp h.1, h.2⟩
        · exact Or.inr (Or.inl ⟨by have := h.1; simp only [Fin.val_succ] at this; omega, h.2⟩)
        · exact Or.inr (Or.inr ⟨by have := h.1; simp only [Fin.val_succ] at this; omega, h.2⟩)

private theorem proper_rows_iff {q n : ℕ} (f : Fin n → Row q) :
    Proper (fun v : Cell n => (f v.1).1 v.2) ↔
      TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f) := by
  induction n with
  | zero => simp [Proper, TransferMatrix.good]
  | succ n ih =>
    rw [← Fin.cons_self_tail f, proper_cons_iff, ih]
    cases n with
    | zero => simp [TransferMatrix.good, List.ofFn_cons]
    | succ n =>
      rw [← Fin.cons_self_tail (Fin.tail f)]
      simp only [List.ofFn_cons, Fin.forall_fin_succ, Fin.val_zero,
        Fin.val_succ, Nat.succ_ne_zero, IsEmpty.forall_iff, false_implies,
        forall_const, true_implies, and_true]
      cases List.ofFn (Fin.tail (Fin.tail f)) <;>
        simp [TransferMatrix.good, TransferMatrix.tailGood, and_comm]

private noncomputable def properRowsEquiv (q n : ℕ) :
    {f : Cell n → Fin q // Proper f} ≃
      {f : Fin n → Row q //
        TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} where
  toFun f := ⟨fun i => ⟨fun j => f.1 (i, j), fun j =>
      f.2 (i, j.castSucc) (i, j.succ) (Or.inl ⟨rfl, rfl⟩)⟩,
    (proper_rows_iff _).mp f.2⟩
  invFun f := ⟨fun v => (f.1 v.1).1 v.2, (proper_rows_iff _).mpr f.2⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl

private def rowClass (r : Row 4) : Fin 5 :=
  if r.1 0 = r.1 2 then (if r.1 1 = r.1 3 then 0 else 1)
  else if r.1 0 = r.1 3 then 2 else if r.1 1 = r.1 3 then 3 else 4

private def Q : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, 2, 0, 0, 0;
     0, 2, 1, 1, 2;
     0, 2, 4, 1, 3;
     1, 1, 2, 2, 0;
     0, 0, 3, 2, 3]

private def initialPairs : Fin 5 → ℤ := ![48, 144, 240, 144, 192]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the entire finite compatibility and row-class table.
private theorem row_table : ∀ r : Row 4, ∀ s : Fin 5,
    (∑ t : Row 4, if compatible r t ∧ rowClass t = s then (1 : ℤ) else 0) =
      Q (rowClass r) s := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks all proper row pairs, including their final row class.
private theorem initial_pairs : ∀ s : Fin 5,
    (∑ r : Row 4, ∑ t : Row 4,
      if compatible r t ∧ rowClass t = s then (1 : ℤ) else 0) = initialPairs s := by
  decide +kernel

private theorem ordinary_transfer (n : ℕ) :
    (ordinaryCount 4 (n + 2) : ℤ) =
      dotProduct initialPairs ((Q ^ n).mulVec (1 : Fin 5 → ℤ)) := by
  unfold ordinaryCount
  rw [Nat.card_congr (properRowsEquiv 4 (n + 2))]
  apply TransferMatrix.cardMatrix compatible (fun _ _ _ => True)
    (fun _ r => rowClass r) Q initialPairs
  · intro a b _ s
    simpa only [true_and] using row_table b s
  · intro s
    convert initial_pairs s using 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : compatible r t ∧ rowClass t = s <;> simp [h]

private def W : Fin 5 → Fin 5 → ℤ :=
  ![![1, 1, 1, 1, 1],
    ![4, 6, 10, 6, 8],
    ![20, 44, 82, 42, 66],
    ![128, 344, 656, 312, 528],
    ![944, 2712, 5208, 2408, 4176]]

private theorem powers_table : ∀ k : Fin 5,
    (Q ^ k.val).mulVec (1 : Fin 5 → ℤ) = W k := by
  apply TransferMatrix.tabulatedPowers Q 4 W
  · exact List.ofFn_inj.mp rfl
  · intro k
    fin_cases k <;> exact List.ofFn_inj.mp rfl

private def recurrenceCoefficients : Fin 4 → ℤ := ![-64, 68, -40, 12]

private theorem power_relation : (Q ^ 4).mulVec (1 : Fin 5 → ℤ) =
    ∑ j : Fin 4, recurrenceCoefficients j • (Q ^ j.val).mulVec (1 : Fin 5 → ℤ) := by
  calc
    _ = W ⟨4, by decide⟩ := powers_table ⟨4, by decide⟩
    _ = ∑ j : Fin 4, recurrenceCoefficients j • W ⟨j.val, by omega⟩ :=
      List.ofFn_inj.mp rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [powers_table ⟨j.val, by omega⟩]

private theorem ordinary_one (q : ℕ) : ordinaryCount q 1 = Nat.card (Row q) := by
  unfold ordinaryCount
  rw [Nat.card_congr (properRowsEquiv q 1)]
  simp [TransferMatrix.good, List.ofFn_succ, Nat.card_eq_fintype_card]

private theorem four_initial : ordinaryCount 4 1 = 108 ∧ ordinaryCount 4 2 = 768 ∧
    ordinaryCount 4 3 = 5856 ∧ ordinaryCount 4 4 = 45696 ∧
    ordinaryCount 4 5 = 359424 := by
  constructor
  · rw [ordinary_one, Nat.card_eq_fintype_card]
    decide +kernel
  have h0 := ordinary_transfer 0
  have h1 := ordinary_transfer 1
  have h2 := ordinary_transfer 2
  have h3 := ordinary_transfer 3
  rw [powers_table ⟨0, by decide⟩] at h0
  rw [powers_table ⟨1, by decide⟩] at h1
  rw [powers_table ⟨2, by decide⟩] at h2
  rw [powers_table ⟨3, by decide⟩] at h3
  norm_num [initialPairs, W, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1,
    by exact_mod_cast h2, by exact_mod_cast h3⟩

private theorem four_recurrence (n : ℕ) (hn : 5 ≤ n) :
    (ordinaryCount 4 n : ℤ) = 12 * ordinaryCount 4 (n - 1) -
      40 * ordinaryCount 4 (n - 2) + 68 * ordinaryCount 4 (n - 3) -
      64 * ordinaryCount 4 (n - 4) := by
  by_cases hs : n = 5
  · subst n
    norm_num [four_initial.1, four_initial.2.1, four_initial.2.2.1,
      four_initial.2.2.2.1, four_initial.2.2.2.2]
  have h6 : 6 ≤ n := by omega
  have hr := TransferMatrix.scalarRelationShift Q initialPairs 4 0
    recurrenceCoefficients power_relation (n - 6)
  have ht (k : ℕ) :
      dotProduct initialPairs ((Q ^ k).mulVec (1 : Fin 5 → ℤ)) =
        (ordinaryCount 4 (k + 2) : ℤ) := (ordinary_transfer k).symm
  simp only [Nat.add_zero] at hr
  simp_rw [ht] at hr
  norm_num [recurrenceCoefficients, Fin.sum_univ_succ, Nat.add_assoc] at hr
  have hidx0 : n - 6 + 6 = n := by omega
  have hidx1 : n - 6 + 2 = n - 4 := by omega
  have hidx2 : n - 6 + 3 = n - 3 := by omega
  have hidx3 : n - 6 + 4 = n - 2 := by omega
  have hidx4 : n - 6 + 5 = n - 1 := by omega
  simp only [hidx0, hidx1, hidx2, hidx3, hidx4] at hr
  omega

/-- The triangle excludes two labels at every height greater than one. -/
theorem ordinary_two_count (n : ℕ) (hn : 0 < n) :
    ordinaryCount 2 n = if n = 1 then 2 else 0 := by
  by_cases h1 : n = 1
  · subst n
    rw [ite_eq_left rfl, ordinary_one, Nat.card_eq_fintype_card]
    decide +kernel
  rw [ite_eq_right h1]
  have h2 : 1 < n := by omega
  unfold ordinaryCount
  haveI : IsEmpty {f : Cell n → Fin 2 // Proper f} := ⟨by
    rintro ⟨f, hf⟩
    have hab := hf (⟨0, hn⟩, 0) (⟨0, hn⟩, 1) (Or.inl ⟨rfl, rfl⟩)
    have hac := hf (⟨0, hn⟩, 0) (⟨1, h2⟩, 0) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have hbc := hf (⟨0, hn⟩, 1) (⟨1, h2⟩, 0) (Or.inr (Or.inr ⟨rfl, rfl⟩))
    exact (by decide : ∀ a b c : Fin 2, a ≠ b → a ≠ c → b ≠ c → False)
      _ _ _ hab hac hbc⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the complete three-colour successor relation.
private theorem three_next : ∀ a b : Row 3, compatible a b →
    (∑ c : Row 3, if compatible b c then (1 : ℤ) else 0) = 1 := by
  decide +kernel

private theorem three_initial :
    (∑ a : Row 3, ∑ b : Row 3, if compatible a b then (1 : ℤ) else 0) = 6 := by
  decide +kernel

private theorem three_transfer (n : ℕ) : ordinaryCount 3 (n + 2) = 6 := by
  have h : (ordinaryCount 3 (n + 2) : ℤ) =
      dotProduct (fun _ : Fin 1 => (6 : ℤ))
        (((1 : Matrix (Fin 1) (Fin 1) ℤ) ^ n).mulVec (1 : Fin 1 → ℤ)) := by
    unfold ordinaryCount
    rw [Nat.card_congr (properRowsEquiv 3 (n + 2))]
    apply TransferMatrix.cardMatrix compatible (fun _ _ _ => True)
      (fun _ _ => (0 : Fin 1)) 1 (fun _ => 6)
    · intro a b hab s
      fin_cases s
      simpa [Matrix.one_apply] using three_next a b hab
    · intro s
      fin_cases s
      simpa using three_initial
  norm_num [dotProduct, Fin.sum_univ_succ] at h
  exact_mod_cast h

/-- Three distinct labels force a unique continuation after the first row pair. -/
theorem ordinary_three_count (n : ℕ) (hn : 0 < n) :
    ordinaryCount 3 n = if n = 1 then 24 else 6 := by
  by_cases h1 : n = 1
  · subst n
    rw [ite_eq_left rfl, ordinary_one, Nat.card_eq_fintype_card]
    decide +kernel
  rw [ite_eq_right h1]
  have he : n - 2 + 2 = n := by omega
  rw [← he]
  exact three_transfer _

/-- The ordinary four-colour series is proved on the identical contained-edge graph. -/
theorem ordinary_series_four : ordinarySeries 4 =
    (108 * PowerSeries.X ^ 1 - 528 * PowerSeries.X ^ 2 +
      960 * PowerSeries.X ^ 3 - 1200 * PowerSeries.X ^ 4) *
    (1 - 12 * PowerSeries.X ^ 1 + 40 * PowerSeries.X ^ 2 -
      68 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4)⁻¹ := by
  let X : PowerSeries ℚ := PowerSeries.X
  let F := ordinarySeries 4
  have hp : F * (1 - 12 * X ^ 1 + 40 * X ^ 2 - 68 * X ^ 3 + 64 * X ^ 4) =
      108 * X ^ 1 - 528 * X ^ 2 + 960 * X ^ 3 - 1200 * X ^ 4 := by
    have he : F * (1 - 12 * X ^ 1 + 40 * X ^ 2 - 68 * X ^ 3 + 64 * X ^ 4) =
        F - 12 * (F * X ^ 1) + 40 * (F * X ^ 2) -
          68 * (F * X ^ 3) + 64 * (F * X ^ 4) := by ring
    rw [he]
    apply PowerSeries.ext
    intro n
    simp only [X, map_sub, map_add, PowerSeries.coeff_ofNat_mul,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, F,
      ordinarySeries, PowerSeries.coeff_mk]
    by_cases hn : n < 5
    · interval_cases n <;> norm_num [four_initial.1, four_initial.2.1,
        four_initial.2.2.1, four_initial.2.2.2.1]
    · have h5 : 5 ≤ n := by omega
      have hq : (ordinaryCount 4 n : ℚ) = 12 * ordinaryCount 4 (n - 1) -
          40 * ordinaryCount 4 (n - 2) + 68 * ordinaryCount 4 (n - 3) -
          64 * ordinaryCount 4 (n - 4) := by exact_mod_cast four_recurrence n h5
      simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
        ite_eq_left (show 3 ≤ n by omega), ite_eq_left (show 4 ≤ n by omega),
        ite_eq_right (show n ≠ 0 by omega), ite_eq_right (show n ≠ 1 by omega),
        ite_eq_right (show n ≠ 2 by omega), ite_eq_right (show n ≠ 3 by omega),
        ite_eq_right (show n ≠ 4 by omega), ite_eq_right (show n - 1 ≠ 0 by omega),
        ite_eq_right (show n - 2 ≠ 0 by omega), ite_eq_right (show n - 3 ≠ 0 by omega),
        ite_eq_right (show n - 4 ≠ 0 by omega)]
      linarith
  change F = _
  calc
    F = (F * (1 - 12 * X ^ 1 + 40 * X ^ 2 - 68 * X ^ 3 + 64 * X ^ 4)) *
        (1 - 12 * X ^ 1 + 40 * X ^ 2 - 68 * X ^ 3 + 64 * X ^ 4)⁻¹ := by
      rw [mul_assoc, PowerSeries.mul_inv_cancel _ (by norm_num [X]), mul_one]
    _ = _ := by rw [hp]

private theorem scaled_literal_coeff (n : ℕ) :
    PowerSeries.coeff n (384 * A - PowerSeries.rescale (16 : ℚ) (ordinarySeries 4)) =
      if n = 0 then 0 else if n = 1 then 2496 else 384 * 16 ^ (n - 1) := by
  by_cases h0 : n = 0
  · subst n
    simp only [map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_rescale,
      A, ordinarySeries, PowerSeries.coeff_mk]
    norm_num
  have hn : 0 < n := Nat.pos_of_ne_zero h0
  have hc := literal_ordinary_count n hn
  rw [ordinary_two_count n hn, ordinary_three_count n hn] at hc
  simp only [map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_rescale,
    A, ordinarySeries, PowerSeries.coeff_mk, if_neg h0]
  by_cases h1 : n = 1
  · subst n
    norm_num at hc ⊢
    linarith
  · simp only [if_neg h1] at hc ⊢
    have hpow : (16 : ℚ) ^ n = 16 * 16 ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
      ring
    rw [hpow]
    nlinarith [hc]

/-- The unconditional rational formal-power-series identity for the literal event. -/
theorem generating_function : GeneratingFunction := by
  let X : PowerSeries ℚ := PowerSeries.X
  let R := PowerSeries.rescale (16 : ℚ) (ordinarySeries 4)
  let B : PowerSeries ℚ := 384 * A - R
  let d : PowerSeries ℚ := 1 - 192 * X + 10240 * X ^ 2 -
    278528 * X ^ 3 + 4194304 * X ^ 4
  have hcoeff (n : ℕ) : PowerSeries.coeff n B =
      if n = 0 then 0 else if n = 1 then 2496 else 384 * 16 ^ (n - 1) :=
    scaled_literal_coeff n
  have hB : B * (1 - 16 * X) = 2496 * X - 33792 * X ^ 2 := by
    have he : B * (1 - 16 * X) = B - 16 * (B * X ^ 1) := by ring
    rw [he]
    apply PowerSeries.ext
    intro n
    simp only [map_sub, PowerSeries.coeff_ofNat_mul,
      PowerSeries.coeff_mul_X_pow', X, PowerSeries.coeff_X,
      PowerSeries.coeff_X_pow, hcoeff]
    by_cases hn : n < 3
    · interval_cases n <;> norm_num
    · have h3 : 3 ≤ n := by omega
      simp only [if_pos (show 1 ≤ n by omega), if_neg (show n ≠ 0 by omega),
        if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
        if_neg (show n - 1 ≠ 0 by omega), if_neg (show n - 1 ≠ 1 by omega)]
      have hpow : (16 : ℚ) ^ (n - 1) = 16 * 16 ^ (n - 1 - 1) := by
        conv_lhs => rw [show n - 1 = (n - 1 - 1) + 1 by omega, pow_succ]
        ring
      rw [hpow]
      ring
  have hR : R * d = 1728 * X - 135168 * X ^ 2 +
      3932160 * X ^ 3 - 78643200 * X ^ 4 := by
    have h := ordinary_series_four
    have hprod : ordinarySeries 4 *
        (1 - 12 * PowerSeries.X ^ 1 + 40 * PowerSeries.X ^ 2 -
          68 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4) =
        108 * PowerSeries.X ^ 1 - 528 * PowerSeries.X ^ 2 +
          960 * PowerSeries.X ^ 3 - 1200 * PowerSeries.X ^ 4 := by
      rw [h, mul_assoc, PowerSeries.inv_mul_cancel _ (by norm_num), mul_one]
    have hs := congrArg (PowerSeries.rescale (16 : ℚ)) hprod
    simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, map_one,
      PowerSeries.rescale_X] at hs
    norm_num only [map_ofNat] at hs
    change R * _ = _ at hs
    convert hs using 1 <;> dsimp [d, X] <;> ring
  have hp384 : 384 * (A * denominator) = 384 * numerator := by
    calc
      384 * (A * denominator) = (B * (1 - 16 * X)) * d + (R * d) * (1 - 16 * X) := by
        dsimp [B, denominator, d, X]
        ring
      _ = 384 * numerator := by
        rw [hB, hR]
        dsimp [numerator, d, X]
        ring
  have hp : A * denominator = numerator := by
    apply PowerSeries.ext
    intro n
    have hc := congrArg (PowerSeries.coeff n) hp384
    simp only [PowerSeries.coeff_ofNat_mul] at hc
    linarith
  unfold GeneratingFunction
  calc
    A = (A * denominator) * denominator⁻¹ := by
      rw [mul_assoc, PowerSeries.mul_inv_cancel _ (by norm_num [denominator]), mul_one]
    _ = numerator * denominator⁻¹ := by rw [hp]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
