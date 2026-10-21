/- GID: D5/S3/Arith/Congruence/KumarPengTranModularComplexity
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/KumarPengTranModularComplexity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Congruence/KumarPengTranModularComplexity.claim; result=D5/S3/Arith/Congruence/KumarPengTranModularComplexity.result; claim=D5/S3/Arith/Congruence/KumarPengTranModularComplexity.claim
   digest: Three unit bases modulo seventeen have greater inefficiency than base two. -/

/-
admission_basis: open-problem-resolution (#19529; Refuted)
escape_witness: mem_V_iff
Direct frozen dependencies: none (the mathematical imports are pinned Mathlib).
result is the designated refutation result of the basis=refutes utility record.
cover_two is a bounded enumeration consumed only by separating_bounds and result.
gap_one is a bounded enumeration consumed only by separating_bounds and result.
gap_three is a bounded enumeration consumed only by separating_bounds and result.
gap_sixteen is a bounded enumeration consumed only by separating_bounds and result.
The public surface consists of the source expressions, their complexity and inefficiency,
the cardinal-ranking claim, and its closed refutation. The claim counts individual units.
At modulus 17, bases 3 and 16 tie; dense ranking by distinct values is not refuted.
The theorem uses E(17,2) ≤ 6 and E(17,1), E(17,3), E(17,16) > 6;
exact inefficiencies and least-counterexample status are not separate Lean claims.
Per-declaration proof_shape and consumers (direct frozen dependencies: none throughout):
Expr: proof_shape: bind-only; consumers: Expr.leaves, Expr.eval, complexity, mem_V_iff.
Expr.leaves: proof_shape: bind-only; consumers: complexity, leaves_pos, mem_V_iff.
Expr.eval: proof_shape: bind-only; consumers: complexity, mem_V_iff.
complexity: proof_shape: bind-only; consumers: inefficiency, complexity_le_iff.
inefficiency: proof_shape: bind-only; consumers: claim, inefficiency_le_of_cover,
  inefficiency_gt_of_gap, separating_bounds.
claim: proof_shape: bind-only; consumer: result.
V: proof_shape: content (recursive finite split construction); consumers: mem_V_iff,
  complexity_le_iff, inefficiency_le_of_cover, inefficiency_gt_of_gap,
  cover_two, gap_one, gap_three, gap_sixteen.
leaves_pos: proof_shape: bind-only; consumer: mem_V_iff.
mem_V_iff: proof_shape: content (strong induction on the leaf-budget invariant);
  escape_witness: mem_V_iff;
  consumers: complexity_le_iff, inefficiency_le_of_cover, inefficiency_gt_of_gap.
complexity_le_iff: proof_shape: content (after inlining mem_V_iff);
  escape_witness: mem_V_iff;
  consumers: inefficiency_le_of_cover,
  inefficiency_gt_of_gap.
inefficiency_le_of_cover: proof_shape: content (after inlining mem_V_iff);
  escape_witness: mem_V_iff;
  consumer: separating_bounds.
inefficiency_gt_of_gap: proof_shape: content (after inlining mem_V_iff);
  escape_witness: mem_V_iff;
  consumer: separating_bounds.
cover_two: proof_shape: bind-only; consumer: separating_bounds.
gap_one: proof_shape: bind-only; consumer: separating_bounds.
gap_three: proof_shape: bind-only; consumer: separating_bounds.
gap_sixteen: proof_shape: bind-only; consumer: separating_bounds.
separating_bounds: proof_shape: content (after inlining the recurrence correctness proof);
  escape_witness: mem_V_iff;
  consumer: result.
u1: proof_shape: bind-only; consumer: result.
u3: proof_shape: bind-only; consumer: result.
u16: proof_shape: bind-only; consumer: result.
result: proof_shape: content (after inlining the recurrence correctness proof);
  escape_witness: mem_V_iff; consumer: settling result.
-/

import Mathlib.Data.ZMod.Basic

/-! Binding conventions for A. Kumar, S. Peng and V. Tran, "Integer Complexity Generalizations in Various Rings",
arXiv:2211.04379v1, Section 4: expressions in one variable `x` built from `+`, `·` and parentheses, the complexity `‖r‖`
of `r ∈ ℤ/mℤ` with base `x = s` (the least number of `x`'s in an expression evaluating to `r`), the inefficiency
`E(m, s) = max(‖0‖, ‖1‖, …, ‖m − 1‖)`, and Conjecture 4.4, "E(m, 2) is the third most inefficient for odd m". -/

namespace D5.S3.Arith.Congruence.KumarPengTranModularComplexity

/-- An expression: a sequence of `x`'s joined by `+`, `·` and parentheses (a binary expression tree with leaves `x`). -/
inductive Expr
  | x : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

namespace Expr

/-- The number of `x`'s in an expression. -/
def leaves : Expr → ℕ
  | x => 1
  | add e f => e.leaves + f.leaves
  | mul e f => e.leaves + f.leaves

/-- The value of an expression in `ℤ/mℤ` at `x = s`. -/
def eval {m : ℕ} (s : ZMod m) : Expr → ZMod m
  | x => s
  | add e f => e.eval s + f.eval s
  | mul e f => e.eval s * f.eval s

end Expr

/-- `‖r‖` with base `x = s`: the least number of `x`'s in an expression evaluating to `r` in `ℤ/mℤ`. -/
noncomputable def complexity {m : ℕ} (s r : ZMod m) : ℕ :=
  sInf {n | ∃ e : Expr, e.leaves = n ∧ e.eval s = r}

/-- `E(m, s) = max(‖0‖, ‖1‖, …, ‖m − 1‖)`. -/
noncomputable def inefficiency (m : ℕ) [NeZero m] (s : ZMod m) : ℕ :=
  Finset.univ.sup fun r : ZMod m => complexity s r

/-- Conjecture 4.4, read as: for odd `m ≥ 3`, base `2` is among the three most inefficient bases, i.e. at most two unit
bases `s` have `E(m, s) > E(m, 2)`. The ranking counts individual unit bases, not distinct inefficiency values. -/
def claim : Prop :=
  ∀ (m : ℕ) [NeZero m], 3 ≤ m → Odd m →
    ((Finset.univ.filter fun s : (ZMod m)ˣ => inefficiency m (2 : ZMod m) < inefficiency m (s : ZMod m)).card ≤ 2)

end D5.S3.Arith.Congruence.KumarPengTranModularComplexity

namespace D5.S3.Arith.Congruence.KumarPengTranModularComplexity

private def V {m : ℕ} (s : ZMod m) : (n : ℕ) → Finset (ZMod m)
  | 0 => ∅
  | n + 1 => {s} ∪ (Finset.range n).attach.biUnion fun i =>
      (V s (i.val + 1)).biUnion fun a =>
        (V s (n - i.val)).biUnion fun b => {a + b, a * b}
termination_by n => n
decreasing_by
  all_goals
    have hi := i.property
    simp only [Finset.mem_range] at hi
    omega

private theorem leaves_pos (e : Expr) : 0 < e.leaves := by
  induction e with
  | x => exact Nat.zero_lt_one
  | add e f he _ => exact Nat.add_pos_left he _
  | mul e f he _ => exact Nat.add_pos_left he _

private theorem mem_V_iff {m : ℕ} (s r : ZMod m) (n : ℕ) :
    r ∈ V s n ↔ ∃ e : Expr, e.leaves ≤ n ∧ e.eval s = r := by
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    cases n with
    | zero =>
      simp only [V, Finset.notMem_empty, false_iff, not_exists, not_and]
      intro e he
      exact ((Nat.not_le_of_gt (leaves_pos e)) he).elim
    | succ n =>
      rw [V]
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion,
        Finset.mem_attach, true_and, Finset.mem_insert]
      constructor
      · rintro (hr | ⟨i, a, ha, b, hb, hr⟩)
        · exact ⟨.x, by simp [Expr.leaves], by simpa [Expr.eval] using hr.symm⟩
        · have hi : i.val < n := Finset.mem_range.mp i.property
          obtain ⟨e, he, rfl⟩ := (ih (i.val + 1) (by omega) a).1 ha
          obtain ⟨f, hf, rfl⟩ := (ih (n - i.val) (by omega) b).1 hb
          rcases hr with hr | hr
          · exact ⟨.add e f, by simp only [Expr.leaves]; omega, hr.symm⟩
          · exact ⟨.mul e f, by simp only [Expr.leaves]; omega, hr.symm⟩
      · rintro ⟨e, he, rfl⟩
        cases e with
        | x => exact Or.inl rfl
        | add e f =>
          have hp := leaves_pos e
          have hq := leaves_pos f
          simp only [Expr.leaves] at he
          right
          let i : ↥(Finset.range n) := ⟨e.leaves - 1, Finset.mem_range.mpr (by omega)⟩
          refine ⟨i, e.eval s, ?_, f.eval s, ?_, Or.inl rfl⟩
          · apply (ih (i.val + 1) (by dsimp [i]; omega) _).2
            exact ⟨e, by dsimp [i]; omega, rfl⟩
          · apply (ih (n - i.val) (by dsimp [i]; omega) _).2
            exact ⟨f, by dsimp [i]; omega, rfl⟩
        | mul e f =>
          have hp := leaves_pos e
          have hq := leaves_pos f
          simp only [Expr.leaves] at he
          right
          let i : ↥(Finset.range n) := ⟨e.leaves - 1, Finset.mem_range.mpr (by omega)⟩
          refine ⟨i, e.eval s, ?_, f.eval s, ?_, Or.inr rfl⟩
          · apply (ih (i.val + 1) (by dsimp [i]; omega) _).2
            exact ⟨e, by dsimp [i]; omega, rfl⟩
          · apply (ih (n - i.val) (by dsimp [i]; omega) _).2
            exact ⟨f, by dsimp [i]; omega, rfl⟩

end D5.S3.Arith.Congruence.KumarPengTranModularComplexity

namespace D5.S3.Arith.Congruence.KumarPengTranModularComplexity

private theorem complexity_le_iff {m : ℕ} (s r : ZMod m) (n : ℕ)
    (hr : ∃ e : Expr, e.eval s = r) :
    complexity s r ≤ n ↔ r ∈ V s n := by
  rw [mem_V_iff]
  constructor
  · intro hn
    obtain ⟨e, he⟩ := hr
    obtain ⟨f, hf, hfr⟩ := Nat.sInf_mem
      (s := {k | ∃ e : Expr, e.leaves = k ∧ e.eval s = r}) ⟨e.leaves, e, rfl, he⟩
    exact ⟨f, hf.trans_le hn, hfr⟩
  · rintro ⟨e, he, hval⟩
    exact (Nat.sInf_le (show e.leaves ∈ {k | ∃ e : Expr, e.leaves = k ∧ e.eval s = r}
      from ⟨e, rfl, hval⟩)).trans he

private theorem inefficiency_le_of_cover {m : ℕ} [NeZero m] (s : ZMod m) (n : ℕ)
    (hc : V s n = Finset.univ) : inefficiency m s ≤ n := by
  apply Finset.sup_le
  intro r _
  have hm : r ∈ V s n := hc.symm ▸ Finset.mem_univ r
  obtain ⟨e, _, he⟩ := (mem_V_iff s r n).1 hm
  exact (complexity_le_iff s r n ⟨e, he⟩).2 hm

private theorem inefficiency_gt_of_gap {m : ℕ} [NeZero m] (s r : ZMod m) (n k : ℕ)
    (hn : r ∉ V s n) (hk : r ∈ V s k) : n < inefficiency m s := by
  obtain ⟨e, _, he⟩ := (mem_V_iff s r k).1 hk
  have hlt : n < complexity s r := Nat.lt_of_not_ge fun h =>
    hn ((complexity_le_iff s r n ⟨e, he⟩).1 h)
  exact hlt.trans_le (Finset.le_sup (Finset.mem_univ r))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem cover_two : V (2 : ZMod 17) 6 = Finset.univ := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem gap_one : (10 : ZMod 17) ∉ V 1 6 ∧ (10 : ZMod 17) ∈ V 1 7 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem gap_three : (0 : ZMod 17) ∉ V 3 6 ∧ (0 : ZMod 17) ∈ V 3 7 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem gap_sixteen : (7 : ZMod 17) ∉ V 16 6 ∧ (7 : ZMod 17) ∈ V 16 7 := by
  decide +kernel

private theorem separating_bounds : inefficiency 17 2 ≤ 6 ∧
    6 < inefficiency 17 1 ∧ 6 < inefficiency 17 3 ∧ 6 < inefficiency 17 16 := by
  exact ⟨inefficiency_le_of_cover 2 6 cover_two,
    inefficiency_gt_of_gap 1 10 6 7 gap_one.1 gap_one.2,
    inefficiency_gt_of_gap 3 0 6 7 gap_three.1 gap_three.2,
    inefficiency_gt_of_gap 16 7 6 7 gap_sixteen.1 gap_sixteen.2⟩

private def u1 : (ZMod 17)ˣ := ZMod.unitOfCoprime 1 (by decide)
private def u3 : (ZMod 17)ˣ := ZMod.unitOfCoprime 3 (by decide)
private def u16 : (ZMod 17)ˣ := ZMod.unitOfCoprime 16 (by decide)

theorem result : ¬ claim := by
  intro hc
  have hh := hc 17 (by decide) (by decide)
  have hb := separating_bounds
  have hs : ({u1, u3, u16} : Finset (ZMod 17)ˣ) ⊆
      Finset.univ.filter (fun s : (ZMod 17)ˣ => inefficiency 17 2 < inefficiency 17 (s : ZMod 17)) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · simpa [u1] using hb.1.trans_lt hb.2.1
    · simpa [u3] using hb.1.trans_lt hb.2.2.1
    · simpa [u16] using hb.1.trans_lt hb.2.2.2
  have hcard : ({u1, u3, u16} : Finset (ZMod 17)ˣ).card = 3 := by
    exact Eq.symm (Nat.eq_of_beq_eq_true rfl)
  have hle := Finset.card_le_card hs
  omega

end D5.S3.Arith.Congruence.KumarPengTranModularComplexity
