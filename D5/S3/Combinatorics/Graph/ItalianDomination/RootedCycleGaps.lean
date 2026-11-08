/- GID: D5/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ItalianDomination/RootedCycleGaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked labelled cycles correspond bijectively to ordered ordinary and exceptional gaps. -/

/-
admission_basis: escape-witness
escape_witness: rootedRefinedCycle_card
Frozen inputs after same-delivery inlining:
  CycleItalianDominationRecurrence.IsItalian: declaration statement_id sha256:9758047395f299db1257334e19147fe19dfb182c18c34bbd41fe742fe8457078.
  ArrowWilfGapData.GapsOn: declaration statement_id sha256:2ec3e595a3a4e7925968c40d0521dfc1c8cac88956d06fc0296eb201e7fd3fb6.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27880.
proof_shape: zeroFree_cycle_marking_count: content; escape_witness: ordinaryWord_card
proof_shape: rootedRefinedCycle_card: content; escape_witness: rootedRefinedCycleEquiv
proof_shape: refined_cycle_marking_count: content; escape_witness: rootedRefinedCycle_card
proof_shape: labelCount_sum: bind-only; escape_witness: none
proof_shape: weight_eq_labelCount: bind-only; escape_witness: none
proof_shape: zeroFree_twos_le_ones: bind-only; escape_witness: none
proof_shape: zeroContaining_inventory_bounds: content; escape_witness: lineOK_gap_iff
proof_shape: zeroContaining_parameter_equations: content; escape_witness: zeroContaining_inventory_bounds
proof_shape: zeroContaining_all_exceptional: content; escape_witness: lineOK_gap_iff
-/

import D5.S3.Combinatorics.Graph.ItalianDomination.OrdinaryWords
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic.NormNum

noncomputable section

namespace D5.S3.Combinatorics.Graph.ItalianDomination.RootedCycleGaps

open scoped BigOperators
open D5.S3.Combinatorics.Graph.ItalianDomination.OrdinaryWords

private theorem snoc_succ_eq {α : Type*} {n : ℕ} (f : Fin (n + 1) → α)
    (z : α) (i : Fin (n + 1)) :
    Fin.snoc (α := fun _ => α) f z i.succ = Fin.snoc (α := fun _ => α) (fun j => f j.succ) z i := by
  cases i using Fin.lastCases with
  | last => simp
  | cast i => simp [← Fin.castSucc_succ]

private theorem headD_ofFn_eq {n : ℕ} (f : Fin n → Fin 3) :
    (List.ofFn f).headD 0 = Fin.snoc (α := fun _ => Fin 3) f 0 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [List.ofFn_succ]

private theorem lineOK_ofFn (p : Fin 3) {n : ℕ} (f : Fin n → Fin 3) :
    LineOK p (List.ofFn f) ↔ ∀ i : Fin n, f i = 2 →
      ((Fin.cons (α := fun _ => Fin 3) p f) i.castSucc).val + ((Fin.snoc (α := fun _ => Fin 3) f 0) i.succ).val ≤ 2 := by
  induction n generalizing p with
  | zero => simp [LineOK]
  | succ n ih =>
    rw [List.ofFn_succ]
    change ((f 0 = 2 → p.val + ((List.ofFn fun i : Fin n => f i.succ).headD 0).val ≤ 2) ∧
      LineOK (f 0) (List.ofFn fun i : Fin n => f i.succ)) ↔ _
    rw [ih, Fin.forall_fin_succ]
    have hc : Fin.cons (α := fun _ => Fin 3) (f 0) (fun i => f i.succ) = f :=
      Fin.cons_self_tail f
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.castSucc_succ, Fin.cons_succ,
      snoc_succ_eq, headD_ofFn_eq, hc]
    try rfl

private theorem deficit_zero_iff_lineOK {n : ℕ} (y : Fin (n + 1) → Fin 3)
    (hy0 : y 0 = 0) :
    IsDeficit y ↔ LineOK 0 (List.ofFn fun i : Fin n => y i.succ) := by
  cases n with
  | zero =>
    constructor
    · intro _; trivial
    · intro _ i hi
      have heq : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      simp [hy0] at hi
  | succ n =>
    rw [lineOK_ofFn]
    have hp (i : Fin (n + 1)) : (finRotate (n + 2)).symm i.succ = i.castSucc := by
      apply (finRotate (n + 2)).injective
      rw [Equiv.apply_symm_apply]
      exact (finRotate_of_lt i.isLt).symm
    have hleft (i : Fin (n + 1)) :
        Fin.cons (α := fun _ => Fin 3) (0 : Fin 3) (fun j : Fin (n + 1) => y j.succ) i.castSucc = y i.castSucc := by
      cases i using Fin.cases with
      | zero => simp [hy0]
      | succ i => simp
    have hright (i : Fin (n + 1)) :
        Fin.snoc (α := fun _ => Fin 3) (fun j : Fin (n + 1) => y j.succ) (0 : Fin 3) i.succ =
          y (finRotate (n + 2) i.succ) := by
      cases i using Fin.lastCases with
      | last => simp [finRotate_last, hy0]
      | cast i => simp [finRotate_of_lt i.succ.isLt, ← Fin.castSucc_succ]
    simp only [hleft, hright]
    constructor
    · intro hy i hi
      simpa only [hp] using hy i.succ hi
    · intro h i hi
      cases i using Fin.cases with
      | zero => simp [hy0] at hi
      | succ i => simpa only [hp] using h i hi

private def GapOK (g : List (Fin 3)) : Prop :=
  (0 : Fin 3) ∉ g ∧ (g = [2, 2] ∨ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) g))

private theorem ordinary_not_exceptional (l : List (Fin 3)) (h : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)) :
    l ≠ [2, 2] := by
  intro heq
  rw [heq] at h
  simp [List.isChain_cons_cons] at h

private theorem split_zero_valid (l : List (Fin 3)) (h : LineOK 0 l) :
    ∀ g ∈ l.splitOn 0, GapOK g := by
  have h0 := splitOn_no_separator (0 : Fin 3) l
  have hh := (lineOK_intercalate (l.splitOn 0)).mp
    (by simpa only [List.intercalate_splitOn] using h)
  intro g hg
  exact ⟨h0 g hg, (lineOK_gap_iff g (h0 g hg)).mp (hh g hg)⟩

private def fixedZeroListEquiv (n : ℕ) :
    {y : Fin (n + 1) → Fin 3 // y 0 = 0} ≃
      {l : List (Fin 3) // l.length = n} where
  toFun y := ⟨List.ofFn (fun i : Fin n => y.val i.succ), List.length_ofFn⟩
  invFun l := ⟨Fin.cons 0 (fun i : Fin n => l.val[i.val]'(by rw [l.prop]; exact i.isLt)), by simp⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero => simpa using y.prop.symm
    | succ i => simp
  right_inv l := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [l.prop]
    · intro i h₁ h₂
      simp

private def fixedZeroValidListEquiv (n : ℕ) :
    {y : Fin (n + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y} ≃
      {l : List (Fin 3) // l.length = n ∧ LineOK 0 l} where
  toFun y := ⟨List.ofFn (fun i : Fin n => y.val i.succ), List.length_ofFn,
    (deficit_zero_iff_lineOK y.val y.prop.1).mp y.prop.2⟩
  invFun l := by
    let y := (fixedZeroListEquiv n).symm ⟨l.val, l.prop.1⟩
    refine ⟨y.val, y.prop, ?_⟩
    apply (deficit_zero_iff_lineOK y.val y.prop).mpr
    have heq := congrArg Subtype.val ((fixedZeroListEquiv n).apply_symm_apply ⟨l.val, l.prop.1⟩)
    change List.ofFn (fun i : Fin n => y.val i.succ) = l.val at heq
    rw [heq]
    exact l.prop.2
  left_inv y := by
    apply Subtype.ext
    exact congrArg (fun z : {y : Fin (n + 1) → Fin 3 // y 0 = 0} => z.val)
      ((fixedZeroListEquiv n).symm_apply_apply ⟨y.val, y.prop.1⟩)
  right_inv l := by
    apply Subtype.ext
    exact congrArg (fun z : {l : List (Fin 3) // l.length = n} => z.val)
      ((fixedZeroListEquiv n).apply_symm_apply ⟨l.val, l.prop.1⟩)

private def fixedZeroGapEquiv (n : ℕ) :
    {y : Fin (n + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y} ≃
      {gs : List (List (Fin 3)) // gs ≠ [] ∧
        (∀ g ∈ gs, GapOK g) ∧ ([0].intercalate gs).length = n} where
  toFun y :=
    let l := fixedZeroValidListEquiv n y
    ⟨l.val.splitOn 0, List.splitOn_ne_nil 0 _, split_zero_valid l.val l.prop.2,
      by rw [List.intercalate_splitOn]; exact l.prop.1⟩
  invFun gs := (fixedZeroValidListEquiv n).symm
    ⟨[0].intercalate gs.val, gs.prop.2.2,
      (lineOK_intercalate _).mpr (fun g hg =>
        (lineOK_gap_iff g (gs.prop.2.1 g hg).1).mpr (gs.prop.2.1 g hg).2)⟩
  left_inv y := by
    apply (fixedZeroValidListEquiv n).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact List.intercalate_splitOn 0
  right_inv gs := by
    apply Subtype.ext
    change ((fixedZeroValidListEquiv n)
      ((fixedZeroValidListEquiv n).symm _)).val.splitOn 0 = _
    rw [Equiv.apply_symm_apply]
    exact List.splitOn_intercalate 0 (fun g hg => (gs.prop.2.1 g hg).1) gs.prop.1

private abbrev GapWord := {g : List (Fin 3) // GapOK g}

private abbrev GapWithPositions {m b : ℕ} (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b)) :=
  {gs : Fin m → GapWord // ∀ i, (gs i).val = [2, 2] ↔ i ∈ e.val}

private def residualOrdinary {m b : ℕ} (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b))
    (gs : GapWithPositions e) (i : ↑((Finset.univ : Finset (Fin _)) \ (e).val)) : OrdinaryWord :=
  ⟨(gs.val i.val).val, (gs.val i.val).prop.1,
    (gs.val i.val).prop.2.resolve_left (fun h =>
      (Finset.mem_sdiff.mp i.prop).2 ((gs.prop i.val).mp h))⟩

private def fillGaps {m b : ℕ} (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b))
    (ls : ↑((Finset.univ : Finset (Fin _)) \ (e).val) → OrdinaryWord) : GapWithPositions e :=
  ⟨fun i => if h : i ∈ e.val then ⟨[2, 2], by decide, Or.inl rfl⟩ else
      ⟨(ls ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩).val,
        (ls ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩).prop.1,
        Or.inr (ls ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩).prop.2⟩,
    by
      intro i
      by_cases hi : i ∈ e.val
      · simp [hi]
      · simp only [dif_neg hi, Subtype.coe_mk, hi, iff_false]
        exact ordinary_not_exceptional _ (ls ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩).prop.2⟩

private def gapPositionsEquiv {m b : ℕ} (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b)) :
    GapWithPositions e ≃ (↑((Finset.univ : Finset (Fin _)) \ (e).val) → OrdinaryWord) where
  toFun := residualOrdinary e
  invFun := fillGaps e
  left_inv gs := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    by_cases hi : i ∈ e.val
    · simpa only [fillGaps, dif_pos hi] using ((gs.prop i).mpr hi).symm
    · simp [fillGaps, hi, residualOrdinary]
  right_inv ls := by
    funext i
    apply Subtype.ext
    have hi : i.val ∉ e.val := (Finset.mem_sdiff.mp i.prop).2
    simp [residualOrdinary, fillGaps, hi]

private abbrev RefinedGapWithPositions {m b : ℕ} (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b)) (c a : ℕ) :=
  {gs : GapWithPositions e //
    (∑ i : ↑((Finset.univ : Finset (Fin _)) \ (e).val), (residualOrdinary e gs i).val.count 1) = c ∧
    (∑ i : ↑((Finset.univ : Finset (Fin _)) \ (e).val), (residualOrdinary e gs i).val.count 2) = a}

private def refinedGapPositionsEquiv {m b : ℕ} (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b)) (c a : ℕ) :
    RefinedGapWithPositions e c a ≃ OrdinaryFamily (↑((Finset.univ : Finset (Fin _)) \ (e).val)) c a :=
  (gapPositionsEquiv e).subtypeEquiv (fun _ => Iff.rfl)

private abbrev MarkedGapFamily (m b c a : ℕ) :=
  (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b)) × RefinedGapWithPositions e c a

private theorem markedGapFamily_card (m b c a : ℕ) :
    Nat.card (MarkedGapFamily m b c a) =
      m.choose b * (c + (m - b) - 1).choose c * (c + (m - b)).choose a := by
  haveI (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b)) : Finite (RefinedGapWithPositions e c a) :=
    Finite.of_equiv (OrdinaryFamily (↑((Finset.univ : Finset (Fin _)) \ (e).val)) c a)
      (refinedGapPositionsEquiv e c a).symm
  rw [Nat.card_sigma]
  have hc (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b)) :
      Nat.card (RefinedGapWithPositions e c a) =
        (c + (m - b) - 1).choose c * (c + (m - b)).choose a := by
    rw [Nat.card_congr (refinedGapPositionsEquiv e c a), ordinaryFamily_card, residual_card]
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, chosen_card, Fintype.card_fin]
  exact (Nat.mul_assoc _ _ _).symm

private theorem joinZero_count_zero (gs : List (List (Fin 3)))
    (hno : ∀ g ∈ gs, (0 : Fin 3) ∉ g) :
    (joinZero gs).count 0 = gs.length := by
  induction gs with
  | nil => simp [joinZero]
  | cons g gs ih =>
    have hg : g.count 0 = 0 := List.count_eq_zero.mpr (hno g (by simp))
    have ht := ih (fun g hg => hno g (by simp [hg]))
    change ((0 :: g) ++ joinZero gs).count 0 = _
    simp [List.count_append, hg, ht, Nat.add_comm]

private theorem joinZero_count_nonzero (v : Fin 3) (hv : v ≠ 0)
    (gs : List (List (Fin 3))) :
    (joinZero gs).count v = (gs.map (List.count v)).sum := by
  induction gs with
  | nil => simp [joinZero]
  | cons g gs ih =>
    change ((0 :: g) ++ joinZero gs).count v = _
    simp [List.count_append, Ne.symm hv, ih]

private theorem joinZero_length (gs : List (List (Fin 3))) :
    (joinZero gs).length = gs.length + (gs.map List.length).sum := by
  induction gs with
  | nil => simp [joinZero]
  | cons g gs ih =>
    change ((0 :: g) ++ joinZero gs).length = _
    simp [List.length_append, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem labelCount_ofFn {n : ℕ} (y : Fin n → Fin 3) (v : Fin 3) :
    labelCount y v = (List.ofFn y).count v := by
  simpa only [labelCount, List.Vector.get_ofFn, List.Vector.toList_ofFn] using
    Fin.card_filter_univ_eq_vector_get_eq_count v (List.Vector.ofFn y)

private theorem fixedZeroGap_reconstruction {n : ℕ}
    (y : {y : Fin (n + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y}) :
    joinZero (fixedZeroGapEquiv n y).val = List.ofFn y.val := by
  change joinZero ((List.ofFn fun i : Fin n => y.val i.succ).splitOn 0) = _
  rw [joinZero_split, List.ofFn_succ, y.prop.1]

private theorem fixedZeroGap_count_zero {n : ℕ}
    (y : {y : Fin (n + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y}) :
    labelCount y.val 0 = (fixedZeroGapEquiv n y).val.length := by
  rw [labelCount_ofFn, ← fixedZeroGap_reconstruction y]
  apply joinZero_count_zero
  intro g hg
  exact ((fixedZeroGapEquiv n y).prop.2.1 g hg).1

private theorem fixedZeroGap_count_nonzero {n : ℕ}
    (y : {y : Fin (n + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y})
    (v : Fin 3) (hv : v ≠ 0) :
    labelCount y.val v = ((fixedZeroGapEquiv n y).val.map (List.count v)).sum := by
  rw [labelCount_ofFn, ← fixedZeroGap_reconstruction y, joinZero_count_nonzero v hv]

private def pair22 : List (Fin 3) → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: ys => (if x = 2 ∧ y = 2 then 1 else 0) + pair22 (y :: ys)

private theorem pair22_noAdjacent (l : List (Fin 3)) (h : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)) :
    pair22 l = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons y ys =>
      have hh := List.isChain_cons_cons.mp h
      have hn : ¬(x = 2 ∧ y = 2) := by tauto
      simp only [pair22, if_neg hn, Nat.zero_add]
      exact ih hh.2

private theorem pair22_gap (g : List (Fin 3)) (hg : GapOK g) :
    pair22 g = if g = [2, 2] then 1 else 0 := by
  rcases hg.2 with rfl | h
  · simp [pair22]
  · rw [if_neg (ordinary_not_exceptional g h)]
    exact pair22_noAdjacent g h

private theorem pair22_split_zero (l r : List (Fin 3)) :
    pair22 (l ++ 0 :: r) = pair22 l + pair22 r := by
  induction l with
  | nil =>
    cases r <;> simp [pair22]
  | cons x l ih =>
    cases l with
    | nil =>
      cases r <;> simp [pair22]
    | cons y ys =>
      change (if x = 2 ∧ y = 2 then 1 else 0) + pair22 ((y :: ys) ++ 0 :: r) =
        ((if x = 2 ∧ y = 2 then 1 else 0) + pair22 (y :: ys)) + pair22 r
      rw [ih, Nat.add_assoc]

private theorem pair22_joinZero (gs : List (List (Fin 3))) :
    pair22 (joinZero gs) = (gs.map pair22).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change pair22 (0 :: (g ++ joinZero gs)) = _
    have hstart (l : List (Fin 3)) : pair22 (0 :: l) = pair22 l := by
      simpa only [List.nil_append, pair22, Nat.zero_add] using pair22_split_zero [] l
    rw [hstart]
    cases gs with
    | nil => simp [joinZero]
    | cons h hs =>
      change pair22 (g ++ 0 :: (h ++ joinZero hs)) = _
      rw [pair22_split_zero]
      have ht : pair22 (h ++ joinZero hs) = ((h :: hs).map pair22).sum := by
        simpa only [show joinZero (h :: hs) = 0 :: (h ++ joinZero hs) from rfl,
          hstart] using ih
      simp [ht]

private theorem pair22_gap_count (gs : List (List (Fin 3))) (hgs : ∀ g ∈ gs, GapOK g) :
    pair22 (joinZero gs) = gs.count [2, 2] := by
  rw [pair22_joinZero]
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := pair22_gap g (hgs g (by simp))
    have ht := ih (fun h hh => hgs h (by simp [hh]))
    simp only [List.map_cons, List.sum_cons, hg, ht, List.count_cons, beq_iff_eq]
    split_ifs <;> omega

private theorem pair22_ofFn {n : ℕ} (f : Fin (n + 1) → Fin 3) :
    pair22 (List.ofFn f) =
      (Finset.univ.filter fun i : Fin n => f i.castSucc = 2 ∧ f i.succ = 2).card := by
  induction n with
  | zero => simp [List.ofFn_succ, pair22]
  | succ n ih =>
    rw [List.ofFn_succ]
    have ht : f (Fin.succ 0) :: List.ofFn (fun i : Fin n => f i.succ.succ) =
        List.ofFn (fun i : Fin (n + 1) => f i.succ) := (List.ofFn_succ (f := fun i : Fin (n + 1) => f i.succ)).symm
    conv_lhs => rw [List.ofFn_succ, pair22]
    rw [ht, ih, Fin.card_filter_univ_succ']
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_succ]
    rfl

private theorem doubleTwoCount_zero {n : ℕ} (y : Fin (n + 1) → Fin 3) (hy0 : y 0 = 0) :
    doubleTwoCount y = pair22 (List.ofFn y) := by
  classical
  rw [pair22_ofFn]
  unfold doubleTwoCount
  symm
  apply Finset.card_bij (fun i _ => i.castSucc)
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    have hn : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1, by rw [hn]; exact hh.2⟩
  · intro i hi j hj hij
    exact Fin.castSucc_injective n hij
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    have hib : i.val < n := by
      by_contra hn
      have heq : i = Fin.last n := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      have hbad := hh.2
      simp [heq, finRotate_last, hy0] at hbad
    have hei : (⟨i.val, hib⟩ : Fin n).castSucc = i := Fin.ext rfl
    have hn : finRotate (n + 1) i = (⟨i.val, hib⟩ : Fin n).succ := finRotate_of_lt hib
    refine ⟨⟨i.val, hib⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hei⟩
    constructor
    · simpa only [hei] using hh.1
    · simpa only [← hn] using hh.2

private theorem fixedZeroGap_count_pairs {n : ℕ}
    (y : {y : Fin (n + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y}) :
    doubleTwoCount y.val = (fixedZeroGapEquiv n y).val.count [2, 2] := by
  rw [doubleTwoCount_zero y.val y.prop.1]
  have hr : joinZero (fixedZeroGapEquiv n y).val = List.ofFn y.val := by exact fixedZeroGap_reconstruction y
  rw [← hr]
  exact pair22_gap_count _ (fixedZeroGapEquiv n y).prop.2.1

private def CyclicNoTwos {n : ℕ} (y : Fin n → Fin 3) : Prop :=
  ∀ i, y i ≠ 2 ∨ y (finRotate n i) ≠ 2

private theorem zeroFreeDeficit_iff {n : ℕ} (y : Fin n → Fin 3)
    (h0 : ∀ i, y i ≠ 0) : IsDeficit y ↔ CyclicNoTwos y := by
  rw [deficit_valid_iff]
  constructor
  · intro h i
    by_cases hi : y i = 2
    · right
      intro hs
      exact h0 ((finRotate n).symm i) ((h i hi).2 hs)
    · exact Or.inl hi
  · intro h i hi
    constructor
    · intro hp
      have hh := h ((finRotate n).symm i)
      simp only [Equiv.apply_symm_apply] at hh
      exact (hh.elim (fun hh => hh hp) (fun hh => hh hi)).elim
    · intro hs
      exact ((h i).elim (fun hh => hh hi) (fun hh => hh hs)).elim

private theorem fixedOne_noAdjacent_iff {n : ℕ} (y : Fin (n + 1) → Fin 3)
    (h1 : y 0 = 1) :
    CyclicNoTwos y ↔ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) (List.ofFn fun i : Fin n => y i.succ)) := by
  rw [List.isChain_ofFn]
  constructor
  · intro h k hk
    have hh := h (⟨k + 1, by omega⟩ : Fin (n + 1))
    have heq : finRotate (n + 1) (⟨k + 1, by omega⟩ : Fin (n + 1)) =
        (⟨k + 2, by omega⟩ : Fin (n + 1)) := finRotate_of_lt hk
    simpa only [heq, Fin.succ_mk, Nat.add_assoc] using hh
  · intro h i
    by_cases hi0 : i = 0
    · left; simp [hi0, h1]
    by_cases hil : i = Fin.last n
    · right; simp [hil, finRotate_last, h1]
    have hv0 : 0 < i.val := by
      have hne : i.val ≠ 0 := fun heq => hi0 (Fin.ext heq)
      omega
    have hvl : i.val < n := by
      have hne : i.val ≠ n := fun heq => hil (Fin.ext heq)
      have := i.isLt
      omega
    have hk : i.val - 1 + 1 < n := by omega
    have hh := h (i.val - 1) hk
    have heq₁ : (⟨i.val - 1, by omega⟩ : Fin n).succ = i := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have heq₂ : (⟨i.val - 1 + 1, hk⟩ : Fin n).succ = finRotate (n + 1) i := by
      rw [show finRotate (n + 1) i = (⟨i.val + 1, by omega⟩ : Fin (n + 1)) from
        finRotate_of_lt hvl]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    simpa only [heq₁, heq₂] using hh

private def fixedOneListEquiv (n : ℕ) :
    {y : Fin (n + 1) → Fin 3 // y 0 = 1} ≃
      {l : List (Fin 3) // l.length = n} where
  toFun y := ⟨List.ofFn (fun i : Fin n => y.val i.succ), List.length_ofFn⟩
  invFun l := ⟨Fin.cons 1 (fun i : Fin n => l.val[i.val]'(by rw [l.prop]; exact i.isLt)), by simp⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero => simpa using y.prop.symm
    | succ i => simp
  right_inv l := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [l.prop]
    · intro i h₁ h₂
      simp

private theorem nonzero_tail_iff {n : ℕ} (y : Fin (n + 1) → Fin 3) (h1 : y 0 = 1) :
    (∀ i, y i ≠ 0) ↔ (0 : Fin 3) ∉ List.ofFn (fun i : Fin n => y i.succ) := by
  simp only [List.mem_ofFn, not_exists]
  constructor
  · intro h i; exact h i.succ
  · intro h i
    cases i using Fin.cases with
    | zero => simp [h1]
    | succ i => exact h i

private def zeroFreeRootedEquiv (n : ℕ) :
    {y : Fin (n + 1) → Fin 3 // y 0 = 1 ∧ (∀ i, y i ≠ 0) ∧ IsDeficit y} ≃
      {l : List (Fin 3) // l.length = n ∧ (0 : Fin 3) ∉ l ∧ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)} where
  toFun y := ⟨List.ofFn (fun i : Fin n => y.val i.succ), List.length_ofFn,
    (nonzero_tail_iff y.val y.prop.1).mp y.prop.2.1,
    (fixedOne_noAdjacent_iff y.val y.prop.1).mp
      ((zeroFreeDeficit_iff y.val y.prop.2.1).mp y.prop.2.2)⟩
  invFun l := by
    let y := (fixedOneListEquiv n).symm ⟨l.val, l.prop.1⟩
    have heq := congrArg Subtype.val ((fixedOneListEquiv n).apply_symm_apply ⟨l.val, l.prop.1⟩)
    change List.ofFn (fun i : Fin n => y.val i.succ) = l.val at heq
    have h0 : ∀ i, y.val i ≠ 0 := (nonzero_tail_iff y.val y.prop).mpr (by rw [heq]; exact l.prop.2.1)
    refine ⟨y.val, y.prop, h0, (zeroFreeDeficit_iff y.val h0).mpr ?_⟩
    exact (fixedOne_noAdjacent_iff y.val y.prop).mpr (by rw [heq]; exact l.prop.2.2)
  left_inv y := by
    apply Subtype.ext
    exact congrArg (fun z : {y : Fin (n + 1) → Fin 3 // y 0 = 1} => z.val)
      ((fixedOneListEquiv n).symm_apply_apply ⟨y.val, y.prop.1⟩)
  right_inv l := by
    apply Subtype.ext
    exact congrArg (fun z : {l : List (Fin 3) // l.length = n} => z.val)
      ((fixedOneListEquiv n).apply_symm_apply ⟨l.val, l.prop.1⟩)

abbrev ZeroFreeWords (c a : ℕ) :=
  {y : Fin (c + a + 1) → Fin 3 // (∀ i, y i ≠ 0) ∧ IsDeficit y ∧
    labelCount y 1 = c + 1 ∧ labelCount y 2 = a}

private abbrev RootedZeroFreeWords (c a : ℕ) :=
  {y : Fin (c + a + 1) → Fin 3 // y 0 = 1 ∧ (∀ i, y i ≠ 0) ∧ IsDeficit y ∧
    labelCount y 1 = c + 1 ∧ labelCount y 2 = a}

private theorem labelCount_root_tail {n : ℕ} (y : Fin (n + 1) → Fin 3) (hy : y 0 = 1) :
    labelCount y 1 = (List.ofFn fun i : Fin n => y i.succ).count 1 + 1 ∧
      labelCount y 2 = (List.ofFn fun i : Fin n => y i.succ).count 2 := by
  rw [labelCount_ofFn, labelCount_ofFn, List.ofFn_succ, hy]
  simp [Nat.add_comm]

private def rootedZeroFreeCountEquiv (c a : ℕ) :
    RootedZeroFreeWords c a ≃
      {l : OrdinaryWord // l.val.count 1 = c ∧ l.val.count 2 = a} where
  toFun y := by
    let l := zeroFreeRootedEquiv (c + a) ⟨y.val, y.prop.1, y.prop.2.1, y.prop.2.2.1⟩
    have hh := labelCount_root_tail y.val y.prop.1
    refine ⟨⟨l.val, l.prop.2.1, l.prop.2.2⟩, ?_, ?_⟩
    · change (List.ofFn fun i : Fin (c + a) => y.val i.succ).count 1 = c
      omega
    · exact hh.2.symm.trans y.prop.2.2.2.2
  invFun l := by
    have hlen : l.val.val.length = c + a := by rw [← ordinary_length l.val, l.prop.1, l.prop.2]
    let y := (zeroFreeRootedEquiv (c + a)).symm
      ⟨l.val.val, hlen, l.val.prop.1, l.val.prop.2⟩
    have hh := labelCount_root_tail y.val y.prop.1
    have heq := congrArg Subtype.val ((zeroFreeRootedEquiv (c + a)).apply_symm_apply
      ⟨l.val.val, hlen, l.val.prop.1, l.val.prop.2⟩)
    change List.ofFn (fun i : Fin (c + a) => y.val i.succ) = l.val.val at heq
    rw [heq] at hh
    exact ⟨y.val, y.prop.1, y.prop.2.1, y.prop.2.2,
      hh.1.trans (by rw [l.prop.1]), hh.2.trans l.prop.2⟩
  left_inv y := by
    apply Subtype.ext
    have hh := (zeroFreeRootedEquiv (c + a)).symm_apply_apply
      (⟨y.val, y.prop.1, y.prop.2.1, y.prop.2.2.1⟩ :
        {y : Fin (c + a + 1) → Fin 3 // y 0 = 1 ∧ (∀ i, y i ≠ 0) ∧ IsDeficit y})
    exact congrArg (fun z : {y : Fin (c + a + 1) → Fin 3 //
      y 0 = 1 ∧ (∀ i, y i ≠ 0) ∧ IsDeficit y} => z.val) hh
  right_inv l := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {l : List (Fin 3) // l.length = c + a ∧
      (0 : Fin 3) ∉ l ∧ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)} => z.val)
      ((zeroFreeRootedEquiv (c + a)).apply_symm_apply _)

private theorem rootedZeroFreeWords_card (c a : ℕ) :
    Nat.card (RootedZeroFreeWords c a) = (c + 1).choose a := by
  rw [Nat.card_congr (rootedZeroFreeCountEquiv c a), ordinaryWord_card]

theorem zeroFree_cycle_marking_count (c a : ℕ) :
    (c + 1) * Nat.card (ZeroFreeWords c a) = (c + a + 1) * (c + 1).choose a := by
  let P : (Fin (c + a + 1) → Fin 3) → Prop := fun y =>
    (∀ i, y i ≠ 0) ∧ IsDeficit y ∧ labelCount y 1 = c + 1 ∧ labelCount y 2 = a
  have hP : ∀ y k, P ((fun v => y (finCycle k v))) ↔ P y := by
    intro y k
    change ((∀ i, (fun v => y (finCycle k v)) i ≠ 0) ∧ _) ↔ ((∀ i, y i ≠ 0) ∧ _)
    have hz' : (∀ i, y i ≠ 0) ↔ ∀ i, y (finCycle k i) ≠ 0 :=
      (finCycle k).surjective.forall
    have hz : (∀ i, (fun v => y (finCycle k v)) i ≠ 0) ↔ ∀ i, y i ≠ 0 := hz'.symm
    rw [hz, shift_valid_iff, labelCount_shift, labelCount_shift]
  have hm : ∀ y, P y → labelCount y 1 = c + 1 := fun y hy => hy.2.2.1
  have hh := marked_vertex_identity P hP 1 (c + 1) hm
  have heq : Nat.card {y : Fin (c + a + 1) → Fin 3 // P y ∧ y 0 = 1} =
      Nat.card (RootedZeroFreeWords c a) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun y => and_comm)
  rw [heq, rootedZeroFreeWords_card] at hh
  exact hh

private abbrev RefinedGapFamily (m b c a : ℕ) :=
  {gs : Fin m → GapWord //
    (Finset.univ.filter (fun i => (gs i).val = [2, 2])).card = b ∧
    (∑ i, (gs i).val.count 1) = c ∧ (∑ i, (gs i).val.count 2) = a + 2 * b}

private theorem gapWithPositions_sum {m b : ℕ} (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b))
    (gs : GapWithPositions e) (v : Fin 3) :
    (∑ i, (gs.val i).val.count v) =
      (∑ i : ↑((Finset.univ : Finset (Fin _)) \ (e).val), (residualOrdinary e gs i).val.count v) + b * ([2, 2].count v) := by
  have he : (∑ i ∈ e.val, (gs.val i).val.count v) = b * ([2, 2].count v) := by
    calc
      _ = ∑ _i ∈ e.val, [2, 2].count v := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(gs.prop i).mpr hi]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [(Finset.mem_powersetCard.mp e.prop).2]
        simp
  have hh := Finset.sum_sdiff (s₁ := e.val) (s₂ := Finset.univ)
    (f := fun i => (gs.val i).val.count v) (Finset.subset_univ e.val)
  rw [← hh, he]
  congr 1
  exact (Finset.sum_coe_sort (Finset.univ \ e.val) (fun i => (gs.val i).val.count v)).symm

private def gapFamilyPositions {m b c a : ℕ} (gs : RefinedGapFamily m b c a) : ↑((Finset.univ : Finset (Fin m)).powersetCard b) :=
  ⟨Finset.univ.filter (fun i => (gs.val i).val = [2, 2]),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, gs.prop.1⟩⟩

private def gapFamilyEncode {m b c a : ℕ} (gs : RefinedGapFamily m b c a) : MarkedGapFamily m b c a := by
  let e := gapFamilyPositions gs
  let g : GapWithPositions e := ⟨gs.val, by intro i; simp [e, gapFamilyPositions]⟩
  have h1 := gapWithPositions_sum e g 1
  have h2 := gapWithPositions_sum e g 2
  have hc : (∑ i, (g.val i).val.count 1) = c := gs.prop.2.1
  have ha : (∑ i, (g.val i).val.count 2) = a + 2 * b := gs.prop.2.2
  rw [hc] at h1
  rw [ha] at h2
  simp only [show ([2, 2] : List (Fin 3)).count 1 = 0 by decide,
    Nat.mul_zero, Nat.add_zero] at h1
  simp only [show ([2, 2] : List (Fin 3)).count 2 = 2 by decide] at h2
  refine ⟨e, g, h1.symm, ?_⟩
  omega

private def gapFamilyDecode {m b c a : ℕ} (d : MarkedGapFamily m b c a) : RefinedGapFamily m b c a := by
  refine ⟨d.2.val.val, ?_, ?_, ?_⟩
  · have he : Finset.univ.filter (fun i => (d.2.val.val i).val = [2, 2]) = d.1.val := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact d.2.val.prop i
    rw [he]
    exact (Finset.mem_powersetCard.mp d.1.prop).2
  · have hh := gapWithPositions_sum d.1 d.2.val 1
    simpa using hh.trans (by rw [d.2.prop.1]; simp)
  · have hh := gapWithPositions_sum d.1 d.2.val 2
    simpa [Nat.mul_comm] using hh.trans (by rw [d.2.prop.2]; simp)

private theorem gapFamilyDecode_injective {m b c a : ℕ} :
    Function.Injective (@gapFamilyDecode m b c a) := by
  intro d d' h
  rcases d with ⟨e, g⟩
  rcases d' with ⟨e', g'⟩
  have hg : g.val.val = g'.val.val := congrArg Subtype.val h
  have he : e = e' := by
    apply Subtype.ext
    ext i
    rw [← g.val.prop i, ← g'.val.prop i, hg]
  subst e'
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact hg

private def gapFamilyEquiv (m b c a : ℕ) : RefinedGapFamily m b c a ≃ MarkedGapFamily m b c a where
  toFun := gapFamilyEncode
  invFun := gapFamilyDecode
  left_inv gs := by apply Subtype.ext; rfl
  right_inv d := by
    apply gapFamilyDecode_injective
    apply Subtype.ext
    rfl

private theorem refinedGapFamily_card (m b c a : ℕ) :
    Nat.card (RefinedGapFamily m b c a) =
      m.choose b * (c + (m - b) - 1).choose c * (c + (m - b)).choose a := by
  rw [Nat.card_congr (gapFamilyEquiv m b c a), markedGapFamily_card]

private abbrev RawGapList (m : ℕ) :=
  {gs : List (List (Fin 3)) // gs.length = m ∧ ∀ g ∈ gs, GapOK g}

private def gapListEquiv (m : ℕ) : RawGapList m ≃ (Fin m → GapWord) where
  toFun gs i := ⟨gs.val[i.val]'(by rw [gs.prop.1]; exact i.isLt),
    gs.prop.2 _ (List.getElem_mem _)⟩
  invFun f := ⟨List.ofFn (fun i => (f i).val), by simp,
    by intro g hg; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg; exact (f i).prop⟩
  left_inv gs := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [gs.prop.1]
    · intro i hi hj; simp
  right_inv f := by
    funext i
    apply Subtype.ext
    simp

private theorem gapList_ofFn {m : ℕ} (gs : RawGapList m) :
    List.ofFn (fun i => (gapListEquiv m gs i).val) = gs.val :=
  congrArg Subtype.val ((gapListEquiv m).symm_apply_apply gs)

private theorem count_ofFn_eq {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] {m : ℕ} (f : Fin m → α) (v : α) :
    (List.ofFn f).count v = (Finset.univ.filter (fun i => f i = v)).card := by
  symm
  simpa only [List.Vector.get_ofFn, List.Vector.toList_ofFn, List.count_eq_countP,
    Bool.beq_eq_decide_eq] using
    Fin.card_filter_univ_eq_vector_get_eq_count v (List.Vector.ofFn f)

private theorem map_sum_ofFn_eq {α : Type*} {m : ℕ} (f : Fin m → α) (g : α → ℕ) :
    ((List.ofFn f).map g).sum = ∑ i, g (f i) := by
  rw [← List.ofFn_comp']
  exact Fin.sum_ofFn _

private abbrev GapListInventory (m b c a : ℕ) :=
  {gs : RawGapList m // gs.val.count [2, 2] = b ∧
    (gs.val.map (List.count 1)).sum = c ∧
    (gs.val.map (List.count 2)).sum = a + 2 * b}

private def gapListInventoryEquiv (m b c a : ℕ) :
    GapListInventory m b c a ≃ RefinedGapFamily m b c a :=
  (gapListEquiv m).subtypeEquiv (fun gs => by
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    have hh := gapList_ofFn gs
    rw [← hh, count_ofFn_eq, map_sum_ofFn_eq, map_sum_ofFn_eq])

private theorem gapListInventory_card (m b c a : ℕ) :
    Nat.card (GapListInventory m b c a) =
      m.choose b * (c + (m - b) - 1).choose c * (c + (m - b)).choose a := by
  rw [Nat.card_congr (gapListInventoryEquiv m b c a), refinedGapFamily_card]

private theorem gapListInventory_join_length {m b c a : ℕ} (gs : GapListInventory m b c a) :
    (joinZero gs.val.val).length = m + c + a + 2 * b := by
  rw [joinZero_length, gs.val.prop.1]
  have h : (gs.val.val.map List.length).sum =
      (gs.val.val.map (List.count 1)).sum + (gs.val.val.map (List.count 2)).sum := by
    have hall : ∀ g ∈ gs.val.val, g.length = g.count 1 + g.count 2 := by
      intro g hg
      have ht := ternary_count_length g
      rw [List.count_eq_zero.mpr (gs.val.prop.2 g hg).1, Nat.zero_add] at ht
      exact ht.symm
    calc
      _ = (gs.val.val.map (fun g => g.count 1 + g.count 2)).sum :=
        congrArg List.sum (List.map_congr_left hall)
      _ = _ := List.sum_map_add
  rw [h, gs.prop.2.1, gs.prop.2.2]
  omega

abbrev RootedRefinedCycle (N m b c a : ℕ) :=
  {y : Fin (N + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y ∧
    labelCount y 0 = m ∧ labelCount y 1 = c ∧
    labelCount y 2 = a + 2 * b ∧ doubleTwoCount y = b}

private def rootCycleToGaps {N m b c a : ℕ} (y : RootedRefinedCycle N m b c a) :
    GapListInventory m b c a := by
  let z : {y : Fin (N + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y} :=
    ⟨y.val, y.prop.1, y.prop.2.1⟩
  let gs := fixedZeroGapEquiv N z
  refine ⟨⟨gs.val, ?_, gs.prop.2.1⟩, ?_, ?_, ?_⟩
  · exact (fixedZeroGap_count_zero z).symm.trans y.prop.2.2.1
  · exact (fixedZeroGap_count_pairs z).symm.trans y.prop.2.2.2.2.2
  · exact (fixedZeroGap_count_nonzero z 1 (by decide)).symm.trans y.prop.2.2.2.1
  · exact (fixedZeroGap_count_nonzero z 2 (by decide)).symm.trans y.prop.2.2.2.2.1

private def rootGapsToCycle {N m b c a : ℕ} (hm : 0 < m) (hlen : N + 1 = m + c + a + 2 * b)
    (gs : GapListInventory m b c a) : RootedRefinedCycle N m b c a := by
  have hne : gs.val.val ≠ [] := by
    intro heq
    have hh := gs.val.prop.1
    rw [heq] at hh
    simp at hh
    omega
  have hl : ([0].intercalate gs.val.val).length = N := by
    have h := gapListInventory_join_length gs
    rw [joinZero_eq gs.val.val hne, List.length_cons] at h
    omega
  let z := (fixedZeroGapEquiv N).symm
    ⟨gs.val.val, hne, gs.val.prop.2, hl⟩
  have hg : (fixedZeroGapEquiv N z).val = gs.val.val :=
    congrArg Subtype.val ((fixedZeroGapEquiv N).apply_symm_apply
      ⟨gs.val.val, hne, gs.val.prop.2, hl⟩)
  refine ⟨z.val, z.prop.1, z.prop.2, ?_, ?_, ?_, ?_⟩
  · rw [fixedZeroGap_count_zero z, hg]
    exact gs.val.prop.1
  · rw [fixedZeroGap_count_nonzero z 1 (by decide), hg]
    exact gs.prop.2.1
  · rw [fixedZeroGap_count_nonzero z 2 (by decide), hg]
    exact gs.prop.2.2
  · rw [fixedZeroGap_count_pairs z, hg]
    exact gs.prop.1

private def rootedRefinedCycleEquiv {N m b c a : ℕ} (hm : 0 < m)
    (hlen : N + 1 = m + c + a + 2 * b) :
    RootedRefinedCycle N m b c a ≃ GapListInventory m b c a where
  toFun := rootCycleToGaps
  invFun := rootGapsToCycle hm hlen
  left_inv y := by
    apply Subtype.ext
    exact congrArg (fun z : {y : Fin (N + 1) → Fin 3 // y 0 = 0 ∧ IsDeficit y} => z.val)
      ((fixedZeroGapEquiv N).symm_apply_apply ⟨y.val, y.prop.1, y.prop.2.1⟩)
  right_inv gs := by
    apply Subtype.ext
    apply Subtype.ext
    change (fixedZeroGapEquiv N ((fixedZeroGapEquiv N).symm _)).val = gs.val.val
    exact congrArg Subtype.val ((fixedZeroGapEquiv N).apply_symm_apply _)

theorem rootedRefinedCycle_card {N m b c a : ℕ} (hm : 0 < m)
    (hlen : N + 1 = m + c + a + 2 * b) :
    Nat.card (RootedRefinedCycle N m b c a) =
      m.choose b * (c + (m - b) - 1).choose c * (c + (m - b)).choose a := by
  rw [Nat.card_congr (rootedRefinedCycleEquiv hm hlen), gapListInventory_card]

abbrev RefinedCycle (N m b c a : ℕ) :=
  {y : Fin (N + 1) → Fin 3 // IsDeficit y ∧
    labelCount y 0 = m ∧ labelCount y 1 = c ∧
    labelCount y 2 = a + 2 * b ∧ doubleTwoCount y = b}

theorem refined_cycle_marking_count {N m b c a : ℕ} (hm : 0 < m)
    (hlen : N + 1 = m + c + a + 2 * b) :
    m * Nat.card (RefinedCycle N m b c a) =
      (N + 1) * (m.choose b * (c + (m - b) - 1).choose c * (c + (m - b)).choose a) := by
  let P : (Fin (N + 1) → Fin 3) → Prop := fun y =>
    IsDeficit y ∧ labelCount y 0 = m ∧ labelCount y 1 = c ∧
      labelCount y 2 = a + 2 * b ∧ doubleTwoCount y = b
  have hP : ∀ y k, P ((fun v => y (finCycle k v))) ↔ P y := by
    intro y k
    change (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
    rw [shift_valid_iff, labelCount_shift, labelCount_shift, labelCount_shift, doubleTwoCount_shift]
  have hh := marked_vertex_identity P hP 0 m (fun _ hy => hy.2.1)
  have heq : Nat.card {y : Fin (N + 1) → Fin 3 // P y ∧ y 0 = 0} =
      Nat.card (RootedRefinedCycle N m b c a) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun _ => and_comm)
  rw [heq, rootedRefinedCycle_card hm hlen] at hh
  exact hh

theorem labelCount_sum {n : ℕ} (y : Fin n → Fin 3) :
    labelCount y 0 + labelCount y 1 + labelCount y 2 = n := by
  rw [labelCount_ofFn, labelCount_ofFn, labelCount_ofFn, ternary_count_length, List.length_ofFn]

theorem weight_eq_labelCount {n : ℕ} (y : Fin n → Fin 3) :
    (∑ i, (y i).val) = labelCount y 1 + 2 * labelCount y 2 := by
  have hh := Finset.sum_fiberwise' (Finset.univ : Finset (Fin n)) y
    (fun v : Fin 3 => v.val)
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  simpa [labelCount, Fin.sum_univ_succ, Nat.mul_comm] using hh.symm

theorem zeroFree_twos_le_ones {n : ℕ} (y : Fin n → Fin 3)
    (h0 : ∀ i, y i ≠ 0) (hy : IsDeficit y) :
    labelCount y 2 ≤ labelCount y 1 := by
  classical
  have hn := (zeroFreeDeficit_iff y h0).mp hy
  unfold labelCount
  apply Finset.card_le_card_of_injOn (finRotate n)
  · intro i hi
    have hi2 := (Finset.mem_filter.mp hi).2
    have hiN2 : y (finRotate n i) ≠ 2 := (hn i).resolve_left (not_not.mpr hi2)
    have hiN0 := h0 (finRotate n i)
    have hiv := (y (finRotate n i)).isLt
    have heq : y (finRotate n i) = 1 := by
      apply Fin.ext
      have hne0 : (y (finRotate n i)).val ≠ 0 := fun h => hiN0 (Fin.ext h)
      have hne2 : (y (finRotate n i)).val ≠ 2 := fun h => hiN2 (Fin.ext h)
      change (y (finRotate n i)).val = 1
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
  · exact (finRotate n).injective.injOn

private theorem exceptional_twos_bound (gs : List (List (Fin 3))) :
    2 * gs.count [2, 2] ≤ (gs.map (List.count 2)).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    by_cases hg : g = [2, 2]
    · subst g
      simpa only [List.count_cons_self, List.map_cons, List.sum_cons,
        show ([2, 2] : List (Fin 3)).count 2 = 2 by decide, Nat.mul_add, Nat.mul_one, Nat.add_comm]
        using Nat.add_le_add_left ih 2
    · have hc : (g :: gs).count [2, 2] = gs.count [2, 2] := by exact List.count_cons_of_ne hg
      rw [hc, List.map_cons, List.sum_cons]
      omega

theorem zeroContaining_inventory_bounds {N : ℕ} (y : Fin (N + 1) → Fin 3)
    (hy : IsDeficit y) (h0 : ∃ i, y i = 0) :
    doubleTwoCount y ≤ labelCount y 0 ∧ 2 * doubleTwoCount y ≤ labelCount y 2 := by
  obtain ⟨k, hk⟩ := h0
  let z : {z : Fin (N + 1) → Fin 3 // z 0 = 0 ∧ IsDeficit z} :=
    ⟨(fun v => y (finCycle k v)), by simpa only [finCycle_apply, zero_add] using hk,
      (shift_valid_iff y k).mpr hy⟩
  have hzB : doubleTwoCount z.val = doubleTwoCount y := doubleTwoCount_shift y k
  have hz0 : labelCount z.val 0 = labelCount y 0 := labelCount_shift y k 0
  have hz2 : labelCount z.val 2 = labelCount y 2 := labelCount_shift y k 2
  have hb : (fixedZeroGapEquiv N z).val.count [2, 2] ≤ (fixedZeroGapEquiv N z).val.length :=
    List.count_le_length
  have htw := exceptional_twos_bound (fixedZeroGapEquiv N z).val
  rw [← fixedZeroGap_count_pairs z, ← fixedZeroGap_count_zero z, hzB, hz0] at hb
  rw [← fixedZeroGap_count_pairs z,
    ← fixedZeroGap_count_nonzero z 2 (by decide), hzB, hz2] at htw
  exact ⟨hb, htw⟩

theorem zeroContaining_parameter_equations {N j : ℕ} (y : Fin (N + 1) → Fin 3)
    (hy : IsDeficit y) (h0 : ∃ i, y i = 0) (hj : (∑ i, (y i).val) = j) :
    let b := doubleTwoCount y
    let a := labelCount y 2 - 2 * b
    N + 1 = labelCount y 0 + labelCount y 1 + a + 2 * b ∧
      j = labelCount y 1 + 2 * a + 4 * b ∧ a ≤ j ∧ b ≤ j := by
  dsimp only
  have hb := zeroContaining_inventory_bounds y hy h0
  have hs := labelCount_sum y
  have hw := weight_eq_labelCount y
  rw [hj] at hw
  omega

theorem zeroContaining_all_exceptional {N : ℕ} (y : Fin (N + 1) → Fin 3)
    (hy : IsDeficit y) (h0 : ∃ i, y i = 0)
    (he : doubleTwoCount y = labelCount y 0) :
    labelCount y 1 = 0 ∧ labelCount y 2 = 2 * doubleTwoCount y := by
  obtain ⟨k, hk⟩ := h0
  let z : {z : Fin (N + 1) → Fin 3 // z 0 = 0 ∧ IsDeficit z} :=
    ⟨(fun v => y (finCycle k v)), by simpa only [finCycle_apply, zero_add] using hk,
      (shift_valid_iff y k).mpr hy⟩
  have hzB : doubleTwoCount z.val = doubleTwoCount y := doubleTwoCount_shift y k
  have hz0 : labelCount z.val 0 = labelCount y 0 := labelCount_shift y k 0
  have hz1 : labelCount z.val 1 = labelCount y 1 := labelCount_shift y k 1
  have hz2 : labelCount z.val 2 = labelCount y 2 := labelCount_shift y k 2
  have hc : (fixedZeroGapEquiv N z).val.count [2, 2] = (fixedZeroGapEquiv N z).val.length := by
    rw [← fixedZeroGap_count_pairs z, ← fixedZeroGap_count_zero z, hzB, hz0, he]
  have hr : List.replicate (doubleTwoCount y) [2, 2] = (fixedZeroGapEquiv N z).val := by
    simpa only [← fixedZeroGap_count_pairs z, hzB] using
      List.replicate_count_eq_of_count_eq_length hc
  have h1 := fixedZeroGap_count_nonzero z 1 (by decide)
  have h2 := fixedZeroGap_count_nonzero z 2 (by decide)
  rw [← hr] at h1 h2
  simp only [List.map_replicate, List.sum_replicate] at h1 h2
  norm_num at h1 h2
  rw [hz1] at h1
  rw [hz2] at h2
  exact ⟨h1, by simpa [Nat.mul_comm] using h2⟩

end D5.S3.Combinatorics.Graph.ItalianDomination.RootedCycleGaps
