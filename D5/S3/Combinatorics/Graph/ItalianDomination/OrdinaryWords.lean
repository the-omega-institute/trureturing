/- GID: D5/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ItalianDomination/OrdinaryWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Insertion slots enumerate ordinary ternary gaps and complemented cycle labels. -/

/-
admission_basis: escape-witness
escape_witness: lineOK_gap_iff
The coefficient count uses the literal preregistered weight sum, constructed directly by Finset.sum.
Frozen inputs after same-delivery inlining:
  CycleItalianDominationRecurrence.IsItalian: declaration statement_id sha256:9758047395f299db1257334e19147fe19dfb182c18c34bbd41fe742fe8457078.
  ArrowWilfGapData.GapsOn: declaration statement_id sha256:2ec3e595a3a4e7925968c40d0521dfc1c8cac88956d06fc0296eb201e7fd3fb6.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27880.
proof_shape: dI_eq_deficit_card: bind-only; escape_witness: none
proof_shape: deficit_valid_iff: bind-only; escape_witness: none
proof_shape: shift_valid_iff: bind-only; escape_witness: none
proof_shape: labelCount_shift: bind-only; escape_witness: none
proof_shape: marked_vertex_identity: bind-only; escape_witness: none
proof_shape: doubleTwoCount_shift: bind-only; escape_witness: none
proof_shape: lineOK_gap_iff: content; escape_witness: lineOK_classify
proof_shape: splitOn_no_separator: bind-only; escape_witness: none
proof_shape: joinZero_eq: bind-only; escape_witness: none
proof_shape: joinZero_split: bind-only; escape_witness: none
proof_shape: lineOK_intercalate: bind-only; escape_witness: none
proof_shape: chosen_card: bind-only; escape_witness: none
proof_shape: residual_card: bind-only; escape_witness: none
proof_shape: ordinaryFamily_card: content; escape_witness: ordinaryFamilyEquiv
proof_shape: ternary_count_length: bind-only; escape_witness: none
proof_shape: ordinary_length: bind-only; escape_witness: none
proof_shape: ordinaryWord_card: content; escape_witness: ordinaryFamily_card
-/

import D5.S3.Combinatorics.Graph.CycleItalianDominationRecurrence
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import D5.S3.Combinatorics.ArrowWilfGapData

noncomputable section

namespace D5.S3.Combinatorics.Graph.ItalianDomination.OrdinaryWords

open scoped BigOperators
open D5.S3.Combinatorics.Graph.CycleItalianDominationRecurrence (IsItalian)

noncomputable def dI (n k : ℕ) : ℕ :=
  Nat.card {f : Fin n → Fin 3 // IsItalian f ∧ (∑ i : Fin n, (f i).val) = k}

def IsDeficit {n : ℕ} (y : Fin n → Fin 3) : Prop :=
  ∀ i, y i = 2 → (y ((finRotate n).symm i)).val +
    (y (finRotate n i)).val ≤ 2

private theorem weight_deficit {n : ℕ} (f : Fin n → Fin 3) :
    (∑ i : Fin n, ((f i).rev).val) + (∑ i : Fin n, (f i).val) = 2 * n := by
  rw [← Finset.sum_add_distrib]
  have hv (i : Fin n) : ((fun i => (f i).rev) i).val + (f i).val = 2 := by
    change 3 - ((f i).val + 1) + (f i).val = 2
    omega
  simp_rw [hv]
  simp [Nat.mul_comm]

private theorem italian_iff_deficit {n : ℕ} (f : Fin n → Fin 3) :
    IsItalian f ↔ IsDeficit ((fun i => (f i).rev)) := by
  constructor
  · intro hf i hi
    have hzero : f i = 0 := by
      apply Fin.ext
      have hval := congrArg Fin.val hi
      change 3 - ((f i).val + 1) = 2 at hval
      omega
    have h := hf i hzero
    change 3 - ((f ((finRotate n).symm i)).val + 1) +
      (3 - ((f (finRotate n i)).val + 1)) ≤ 2
    have hp := (f ((finRotate n).symm i)).isLt
    have hs := (f (finRotate n i)).isLt
    omega
  · intro hy i hi
    have htwo : (fun i => (f i).rev) i = 2 := by
      change (f i).rev = 2
      rw [hi]
      rfl
    have h := hy i htwo
    change 3 - ((f ((finRotate n).symm i)).val + 1) +
      (3 - ((f (finRotate n i)).val + 1)) ≤ 2 at h
    have hp := (f ((finRotate n).symm i)).isLt
    have hs := (f (finRotate n i)).isLt
    omega

private theorem ternary_capacity_iff (u v : Fin 3) :
    u.val + v.val ≤ 2 ↔ (u = 2 → v = 0) ∧ (v = 2 → u = 0) := by
  constructor
  · intro h
    constructor
    · intro hu; apply Fin.ext; have hh := congrArg Fin.val hu; simp only [Fin.val_zero]; omega
    · intro hv; apply Fin.ext; have hh := congrArg Fin.val hv; simp only [Fin.val_zero]; omega
  · rintro ⟨hu, hv⟩
    by_cases hu2 : u = 2
    · have h := congrArg Fin.val (hu hu2); simp only [Fin.val_zero] at h
      have h' := congrArg Fin.val hu2
      omega
    · by_cases hv2 : v = 2
      · have h := congrArg Fin.val (hv hv2); simp only [Fin.val_zero] at h
        have h' := congrArg Fin.val hv2
        omega
      · have hu' : u.val ≠ 2 := fun h => hu2 (Fin.ext h)
        have hv' : v.val ≠ 2 := fun h => hv2 (Fin.ext h)
        have := u.isLt
        have := v.isLt
        omega

private def deficitSubtypeEquiv (n j : ℕ) (hj : j ≤ 2 * n) :
    {f : Fin n → Fin 3 // IsItalian f ∧ (∑ i : Fin n, (f i).val) = 2 * n - j} ≃
      {y : Fin n → Fin 3 // IsDeficit y ∧ (∑ i, (y i).val) = j} :=
  ((Equiv.piCongrRight (fun _ : Fin n => Fin.revPerm))).subtypeEquiv fun f => by
    change (IsItalian f ∧ (∑ i : Fin n, (f i).val) = 2 * n - j) ↔
      IsDeficit ((fun i => (f i).rev)) ∧ (∑ i : Fin n, ((f i).rev).val) = j
    rw [italian_iff_deficit]
    have h := weight_deficit f
    constructor <;> rintro ⟨hf, hw⟩ <;> exact ⟨hf, by omega⟩

theorem dI_eq_deficit_card (n j : ℕ) (hj : j ≤ 2 * n) :
    dI n (2 * n - j) =
      Nat.card {y : Fin n → Fin 3 // IsDeficit y ∧ (∑ i, (y i).val) = j} :=
  Nat.card_congr (deficitSubtypeEquiv n j hj)

theorem deficit_valid_iff {n : ℕ} (y : Fin n → Fin 3) :
    IsDeficit y ↔ ∀ i, y i = 2 →
      (y ((finRotate n).symm i) = 2 → y (finRotate n i) = 0) ∧
      (y (finRotate n i) = 2 → y ((finRotate n).symm i) = 0) := by
  unfold IsDeficit
  simp_rw [ternary_capacity_iff]

def labelCount {n : ℕ} (y : Fin n → Fin 3) (v : Fin 3) : ℕ :=
  (Finset.univ.filter fun i => y i = v).card

private theorem finCycle_comm_next {n : ℕ} [NeZero n] (k i : Fin n) :
    finCycle k (finRotate n i) = finRotate n (finCycle k i) := by
  simp only [finCycle_apply, finRotate_apply]
  ac_rfl

private theorem finCycle_comm_prev {n : ℕ} [NeZero n] (k i : Fin n) :
    finCycle k ((finRotate n).symm i) = (finRotate n).symm (finCycle k i) := by
  apply (finRotate n).injective
  rw [← finCycle_comm_next, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem shift_valid_iff {n : ℕ} [NeZero n] (y : Fin n → Fin 3) (k : Fin n) :
    IsDeficit ((fun v => y (finCycle k v))) ↔ IsDeficit y := by
  unfold IsDeficit
  simp_rw [finCycle_comm_prev, finCycle_comm_next]
  constructor
  · intro h i
    obtain ⟨a, rfl⟩ := (finCycle k).surjective i
    exact h a
  · intro h i
    exact h (finCycle k i)

theorem labelCount_shift {n : ℕ} (y : Fin n → Fin 3) (k : Fin n) (v : Fin 3) :
    labelCount ((fun v => y (finCycle k v))) v = labelCount y v := by
  classical
  have h := Nat.card_congr ((finCycle k).subtypeEquiv
    (p := fun i => (fun v => y (finCycle k v)) i = v) (q := fun i => y i = v) (fun _ => Iff.rfl))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, labelCount] using h

private theorem fixed_vertex_count {n : ℕ} [NeZero n]
    (P : (Fin n → Fin 3) → Prop)
    (hP : ∀ y k, P ((fun v => y (finCycle k v))) ↔ P y) (v : Fin 3) (i : Fin n) :
    Nat.card {y : Fin n → Fin 3 // P y ∧ y i = v} =
      Nat.card {y : Fin n → Fin 3 // P y ∧ y 0 = v} := by
  apply Nat.card_congr
  apply ((Equiv.arrowCongr (finCycle i).symm (Equiv.refl (Fin 3)))).subtypeEquiv
  intro y
  change (P y ∧ y i = v) ↔ (P ((fun v => y (finCycle i v))) ∧ (fun v => y (finCycle i v)) 0 = v)
  rw [hP]
  simp only [finCycle_apply, zero_add]

theorem marked_vertex_identity {n : ℕ} [NeZero n]
    (P : (Fin n → Fin 3) → Prop)
    (hP : ∀ y k, P ((fun v => y (finCycle k v))) ↔ P y) (v : Fin 3) (m : ℕ)
    (hm : ∀ y, P y → labelCount y v = m) :
    m * Nat.card {y : Fin n → Fin 3 // P y} =
      n * Nat.card {y : Fin n → Fin 3 // P y ∧ y 0 = v} := by
  classical
  let S : Finset (Fin n → Fin 3) := Finset.univ.filter P
  have heq := Finset.card_mul_eq_card_mul
    (r := fun y i => y i = v) (s := S) (t := Finset.univ)
    (m := m) (n := Nat.card {y : Fin n → Fin 3 // P y ∧ y 0 = v})
    (by
      intro y hy
      exact hm y (Finset.mem_filter.mp hy).2)
    (by
      intro i hi
      have h := fixed_vertex_count P hP v i
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
        Finset.bipartiteBelow, S, Finset.filter_filter] using h)
  simpa only [S, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_univ,
    Fintype.card_fin, mul_comm] using heq

def doubleTwoCount {n : ℕ} (y : Fin n → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => y i = 2 ∧ y (finRotate n i) = 2).card

theorem doubleTwoCount_shift {n : ℕ} [NeZero n] (y : Fin n → Fin 3) (k : Fin n) :
    doubleTwoCount ((fun v => y (finCycle k v))) = doubleTwoCount y := by
  classical
  have h := Nat.card_congr ((finCycle k).subtypeEquiv
    (p := fun i => (fun v => y (finCycle k v)) i = 2 ∧ (fun v => y (finCycle k v)) (finRotate n i) = 2)
    (q := fun i => y i = 2 ∧ y (finRotate n i) = 2)
    (fun i => by simp only [finCycle_comm_next]))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, doubleTwoCount] using h

def LineOK (p : Fin 3) : List (Fin 3) → Prop
  | [] => True
  | x :: xs => (x = 2 → p.val + (xs.headD 0).val ≤ 2) ∧ LineOK x xs

private theorem lineOK_mono (p q : Fin 3) (l : List (Fin 3))
    (hpq : p.val ≤ q.val) (h : LineOK q l) : LineOK p l := by
  cases l with
  | nil => trivial
  | cons x xs =>
    exact ⟨fun hx => le_trans (Nat.add_le_add_right hpq _) (h.1 hx), h.2⟩

private theorem lineOK_of_noAdjacent (p : Fin 3) (l : List (Fin 3))
    (hp : p = 2 → l.headD 0 ≠ 2) (hl : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)) : LineOK p l := by
  induction l generalizing p with
  | nil => trivial
  | cons x xs ih =>
    have hrel : x ≠ 2 ∨ xs.headD 0 ≠ 2 := by
      cases xs with
      | nil => right; decide
      | cons y ys => exact (List.isChain_cons_cons.mp hl).1
    constructor
    · intro hx
      have hp2 : p ≠ 2 := fun hp2 => hp hp2 hx
      have hn2 : xs.headD 0 ≠ 2 := hrel.resolve_left (not_not.mpr hx)
      have hpval : p.val ≠ 2 := fun h => hp2 (Fin.ext h)
      have hnval : (xs.headD 0).val ≠ 2 := fun h => hn2 (Fin.ext h)
      have := p.isLt
      have := (xs.headD 0).isLt
      omega
    · apply ih x (fun hx => hrel.resolve_left (not_not.mpr hx))
      cases xs with
      | nil => simp []
      | cons y ys => exact (List.isChain_cons_cons.mp hl).2

private theorem lineOK_classify (l : List (Fin 3)) (h0 : (0 : Fin 3) ∉ l)
    (hl : LineOK 0 l) : l = [2, 2] ∨ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l) := by
  induction l with
  | nil => right; simp []
  | cons a l ih =>
    have ha0 : a ≠ 0 := fun h => h0 (by simp [h])
    have hl0 : (0 : Fin 3) ∉ l := fun h => h0 (List.mem_cons_of_mem a h)
    cases l with
    | nil => right; simp []
    | cons b r =>
      have htail : LineOK 0 (b :: r) := lineOK_mono 0 a _ (Nat.zero_le _) hl.2
      rcases ih hl0 htail with h22 | hchain
      · have hbr : b :: r = [2, 2] := h22
        have hbound : LineOK a (b :: r) := hl.2
        rw [hbr] at hbound
        have hz := hbound.1 rfl
        have hav := a.isLt
        have ha : a = 0 := Fin.ext (by change a.val = 0; change a.val + 2 ≤ 2 at hz; omega)
        exact (ha0 ha).elim
      · by_cases hab : a = 2 ∧ b = 2
        · rcases hab with ⟨rfl, rfl⟩
          cases r with
          | nil => exact Or.inl rfl
          | cons c r =>
            have hc := hl.2.1 rfl
            have hc0 : c = 0 := Fin.ext (by change c.val = 0; change 2 + c.val ≤ 2 at hc; omega)
            exact (h0 (by simp [hc0])).elim
        · right
          exact List.isChain_cons_cons.mpr ⟨by tauto, hchain⟩

theorem lineOK_gap_iff (l : List (Fin 3)) (h0 : (0 : Fin 3) ∉ l) :
    LineOK 0 l ↔ l = [2, 2] ∨ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l) := by
  constructor
  · exact lineOK_classify l h0
  · rintro (rfl | hc)
    · simp [LineOK]
    · apply lineOK_of_noAdjacent 0 l _ hc
      intro h
      exact (by decide : (0 : Fin 3) ≠ 2) h |>.elim

private theorem lineOK_split_zero (p : Fin 3) (l r : List (Fin 3)) :
    LineOK p (l ++ 0 :: r) ↔ LineOK p (l ++ [0]) ∧ LineOK 0 r := by
  induction l generalizing p with
  | nil => simp [LineOK]
  | cons a l ih =>
    have hh : (l ++ 0 :: r).headD 0 = (l ++ [0]).headD 0 := by
      cases l <;> rfl
    change ((a = 2 → p.val + ((l ++ 0 :: r).headD 0).val ≤ 2) ∧
      LineOK a (l ++ 0 :: r)) ↔
      ((a = 2 → p.val + ((l ++ [0]).headD 0).val ≤ 2) ∧
      LineOK a (l ++ [0])) ∧ LineOK 0 r
    rw [hh, ih a]
    tauto

theorem splitOn_no_separator {α : Type*} [DecidableEq α]
    (sep : α) (l : List α) : ∀ g ∈ l.splitOn sep, sep ∉ g := by
  suffices h : ∀ (acc : List α), sep ∉ acc →
      ∀ g ∈ List.splitOnPPrepend (· == sep) l acc, sep ∉ g by
    exact h [] (by simp)
  induction l with
  | nil =>
    intro acc hacc g hg
    simp only [List.splitOnPPrepend, List.mem_singleton] at hg
    subst g
    simpa using hacc
  | cons a l ih =>
    intro acc hacc g hg
    by_cases ha : a = sep
    · subst a
      simp only [List.splitOnPPrepend, beq_self_eq_true, ↓reduceIte,
        List.mem_cons] at hg
      rcases hg with rfl | hg
      · simpa using hacc
      · exact ih [] (by simp) g hg
    · have hbeq : (a == sep) = false := beq_eq_false_iff_ne.mpr ha
      simp only [List.splitOnPPrepend, hbeq, Bool.false_eq_true, ↓reduceIte] at hg
      exact ih (a :: acc) (by simp [Ne.symm ha, hacc]) g hg

private theorem count_intercalate_ne {α : Type*} [DecidableEq α]
    (sep x : α) (hne : x ≠ sep) (gs : List (List α)) :
    ([sep].intercalate gs).count x = (gs.map (List.count x)).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    cases gs with
    | nil => simp
    | cons h hs =>
      simp only [List.intercalate_cons_cons, List.count_append, List.count_cons,
        List.map_cons, List.sum_cons] at *
      simp only [beq_eq_false_iff_ne.mpr (Ne.symm hne), Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero]
      exact congrArg (g.count x + ·) ih

private theorem count_intercalate_sep {α : Type*} [DecidableEq α]
    (sep : α) (gs : List (List α)) (hgs : gs ≠ [])
    (hno : ∀ g ∈ gs, sep ∉ g) :
    ([sep].intercalate gs).count sep + 1 = gs.length := by
  induction gs with
  | nil => contradiction
  | cons g gs ih =>
    have hg : g.count sep = 0 := List.count_eq_zero.mpr (hno g (by simp))
    cases gs with
    | nil => simp [hg]
    | cons h hs =>
      have ht := ih (by simp) (fun x hx => hno x (by simp [hx]))
      simp only [List.length_cons] at ht
      simp only [List.intercalate_cons_cons, List.count_append, List.count_cons,
        beq_self_eq_true, ↓reduceIte, List.length_cons, List.count_nil, hg, Nat.zero_add]
      omega

def joinZero (gs : List (List (Fin 3))) : List (Fin 3) :=
  (gs.map (fun g => (0 : Fin 3) :: g)).flatten

theorem joinZero_eq (gs : List (List (Fin 3))) (hne : gs ≠ []) :
    joinZero gs = 0 :: [0].intercalate gs := by
  induction gs with
  | nil => contradiction
  | cons g gs ih =>
    cases gs with
    | nil => simp [joinZero]
    | cons h hs =>
      have ht := ih (by simp)
      change (0 :: g) ++ joinZero (h :: hs) = _
      rw [ht]
      simp [List.intercalate_cons_cons]

theorem joinZero_split (l : List (Fin 3)) :
    joinZero (l.splitOn 0) = 0 :: l := by
  rw [joinZero_eq _ (List.splitOn_ne_nil 0 l), List.intercalate_splitOn]

private theorem lineOK_append_zero (p : Fin 3) (l : List (Fin 3)) :
    LineOK p (l ++ [0]) ↔ LineOK p l := by
  induction l generalizing p with
  | nil => simp [LineOK]
  | cons a l ih =>
    have hh : (l ++ [0]).headD 0 = l.headD 0 := by cases l <;> rfl
    change ((a = 2 → p.val + ((l ++ [0]).headD 0).val ≤ 2) ∧ LineOK a (l ++ [0])) ↔
      ((a = 2 → p.val + (l.headD 0).val ≤ 2) ∧ LineOK a l)
    rw [hh, ih a]

theorem lineOK_intercalate (gs : List (List (Fin 3))) :
    LineOK 0 ([0].intercalate gs) ↔ ∀ g ∈ gs, LineOK 0 g := by
  induction gs with
  | nil => simp [LineOK]
  | cons g gs ih =>
    cases gs with
    | nil => simp
    | cons h hs =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
        lineOK_split_zero, lineOK_append_zero, ih]
      simp

private theorem noAdjacent_split_one (l r : List (Fin 3)) :
    (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) (l ++ 1 :: r)) ↔ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l) ∧ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) r) := by
  induction l with
  | nil =>
    cases r <;> simp [List.isChain_cons_cons]
  | cons a l ih =>
    cases l with
    | nil =>
      cases r <;> simp [List.isChain_cons_cons]
    | cons b l =>
      simp only [List.cons_append, List.isChain_cons_cons] at ih ⊢
      tauto

private theorem noAdjacent_intercalate_one (gs : List (List (Fin 3))) :
    (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) ([1].intercalate gs)) ↔ ∀ g ∈ gs, (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) g) := by
  induction gs with
  | nil => simp []
  | cons g gs ih =>
    cases gs with
    | nil => simp
    | cons h hs =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
        noAdjacent_split_one, ih]
      simp

private theorem notMem_intercalate_ne {α : Type*} [DecidableEq α]
    (sep x : α) (hne : x ≠ sep) (gs : List (List α)) :
    x ∉ [sep].intercalate gs ↔ ∀ g ∈ gs, x ∉ g := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    cases gs with
    | nil => simp
    | cons h hs => simp [List.intercalate_cons_cons, hne, ih]

private theorem tiny_twos (l : List (Fin 3)) (h0 : (0 : Fin 3) ∉ l)
    (h1 : (1 : Fin 3) ∉ l) (hc : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)) :
    l = [] ∨ l = [2] := by
  have hv (x : Fin 3) (hx : x ∈ l) : x = 2 := by
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    have hx1 : x ≠ 1 := fun h => h1 (h ▸ hx)
    have hx0' : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
    have hx1' : x.val ≠ 1 := fun h => hx1 (Fin.ext h)
    apply Fin.ext
    have := x.isLt
    change x.val = 2
    omega
  cases l with
  | nil => exact Or.inl rfl
  | cons a l =>
    have ha : a = 2 := hv a (by simp)
    cases l with
    | nil => exact Or.inr (by simp [ha])
    | cons b l =>
      have hb : b = 2 := hv b (by simp)
      have hh := (List.isChain_cons_cons.mp hc).1
      exact (hh.elim (fun h => h ha) (fun h => h hb)).elim

private def pieceBit (g : List (Fin 3)) : Bool := decide (g = [2])

private def bitsOf (l : List (Fin 3)) : List Bool :=
  (l.splitOn 1).map pieceBit

private def insertTwos (bs : List Bool) : List (Fin 3) :=
  [1].intercalate (bs.map fun b => if b then [2] else [])

private theorem pieces_tiny (l : List (Fin 3)) (h0 : (0 : Fin 3) ∉ l)
    (hc : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)) :
    ∀ g ∈ l.splitOn 1, g = [] ∨ g = [2] := by
  have hrec : [1].intercalate (l.splitOn 1) = l := List.intercalate_splitOn 1
  have hn0 := (notMem_intercalate_ne (1 : Fin 3) 0 (by decide) (l.splitOn 1)).mp
    (hrec.symm ▸ h0)
  have hn1 := splitOn_no_separator (1 : Fin 3) l
  have hnc := (noAdjacent_intercalate_one (l.splitOn 1)).mp (hrec.symm ▸ hc)
  intro g hg
  exact tiny_twos g (hn0 g hg) (hn1 g hg) (hnc g hg)

private theorem insertTwos_bitsOf (l : List (Fin 3)) (h0 : (0 : Fin 3) ∉ l)
    (hc : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)) : insertTwos (bitsOf l) = l := by
  have hh : ((l.splitOn 1).map pieceBit).map (fun b => if b then [2] else []) =
      l.splitOn 1 := by
    rw [List.map_map]
    calc
      _ = (l.splitOn 1).map id := by
        apply List.map_congr_left
        intro g hg
        rcases pieces_tiny l h0 hc g hg with rfl | rfl <;> simp [pieceBit]
      _ = _ := List.map_id _
  unfold insertTwos bitsOf
  rw [hh]
  exact List.intercalate_splitOn 1

private theorem splitOn_insertTwos (bs : List Bool) (hne : bs ≠ []) :
    (insertTwos bs).splitOn 1 = bs.map (fun b => if b then [2] else []) := by
  apply List.splitOn_intercalate
  · intro g hg
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    cases b <;> decide
  · simpa using hne

private theorem bitsOf_insertTwos (bs : List Bool) (hne : bs ≠ []) :
    bitsOf (insertTwos bs) = bs := by
  unfold bitsOf
  rw [splitOn_insertTwos bs hne, List.map_map]
  calc
    _ = bs.map id := by
      apply List.map_congr_left
      intro b hb
      cases b <;> decide
    _ = bs := List.map_id _

private theorem insertTwos_nonzero (bs : List Bool) : (0 : Fin 3) ∉ insertTwos bs := by
  apply (notMem_intercalate_ne (1 : Fin 3) 0 (by decide) _).mpr
  intro g hg
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
  cases b <;> decide

private theorem insertTwos_noAdjacent (bs : List Bool) : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) (insertTwos bs)) := by
  apply (noAdjacent_intercalate_one _).mpr
  intro g hg
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
  cases b <;> simp []

private theorem bitsOf_nonempty (l : List (Fin 3)) : bitsOf l ≠ [] := by
  simpa [bitsOf] using List.splitOn_ne_nil (1 : Fin 3) l

private theorem count_one_insertTwos (bs : List Bool) (hne : bs ≠ []) :
    (insertTwos bs).count 1 + 1 = bs.length := by
  have h := count_intercalate_sep (1 : Fin 3)
    (bs.map fun b => if b then [2] else []) (by simpa using hne)
    (by
      intro g hg
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      cases b <;> decide)
  simpa [insertTwos] using h

private theorem count_two_insertTwos (bs : List Bool) :
    (insertTwos bs).count 2 = bs.count true := by
  unfold insertTwos
  rw [count_intercalate_ne (1 : Fin 3) 2 (by decide), List.map_map]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp_all [Nat.add_comm]

private theorem bitsOf_length (l : List (Fin 3)) (h0 : (0 : Fin 3) ∉ l)
    (hc : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)) : (bitsOf l).length = l.count 1 + 1 := by
  have h := count_one_insertTwos (bitsOf l) (bitsOf_nonempty l)
  rw [insertTwos_bitsOf l h0 hc] at h
  exact h.symm

private theorem bitsOf_count (l : List (Fin 3)) (h0 : (0 : Fin 3) ∉ l)
    (hc : (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)) : (bitsOf l).count true = l.count 2 := by
  have h := count_two_insertTwos (bitsOf l)
  rw [insertTwos_bitsOf l h0 hc] at h
  exact h.symm

private theorem count_true_ofFn {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).count true = (Finset.univ.filter fun i => f i).card := by
  simpa only [List.Vector.get_ofFn, List.Vector.toList_ofFn] using
    (Fin.card_filter_univ_eq_vector_get_eq_count true (List.Vector.ofFn f)).symm

private abbrev OrdinaryDataOn (α : Type*) [Fintype α] [DecidableEq α] (c a : ℕ) :=
  (g : D5.S3.Combinatorics.ArrowWilfGapData.GapsOn α c) × ↑((Finset.univ : Finset (((i : α) × Fin ((g).val i + 1)))).powersetCard a)

private theorem weakCompOn_card (α : Type*) [Fintype α] [DecidableEq α] (c : ℕ) :
    Nat.card (D5.S3.Combinatorics.ArrowWilfGapData.GapsOn α c) = (c + Fintype.card α - 1).choose c := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ]
  rw [Nat.add_comm (Fintype.card α) c]

private theorem slotsOn_card {α : Type*} [Fintype α] [DecidableEq α]
    {c : ℕ} (g : D5.S3.Combinatorics.ArrowWilfGapData.GapsOn α c) :
    Fintype.card (((i : α) × Fin ((g).val i + 1))) = c + Fintype.card α := by
  have hg := (Finset.mem_finsuppAntidiag.mp g.prop).1
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Finset.sum_add_distrib, hg]
  simp

theorem chosen_card (α : Type*) [Fintype α] [DecidableEq α] (a : ℕ) :
    Nat.card (↑((Finset.univ : Finset α).powersetCard a)) = (Fintype.card α).choose a := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ]

private theorem ordinaryDataOn_card (α : Type*) [Fintype α] [DecidableEq α] (c a : ℕ) :
    Nat.card (OrdinaryDataOn α c a) =
      (c + Fintype.card α - 1).choose c * (c + Fintype.card α).choose a := by
  rw [Nat.card_sigma]
  simp_rw [chosen_card, slotsOn_card]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, weakCompOn_card]
  simp

theorem residual_card {m b : ℕ} (e : ↑((Finset.univ : Finset (Fin m)).powersetCard b)) :
    Fintype.card (↑((Finset.univ : Finset (Fin _)) \ (e).val)) = m - b := by
  have hb := (Finset.mem_powersetCard.mp e.prop).2
  simp only [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, hb]

abbrev OrdinaryWord := {l : List (Fin 3) // (0 : Fin 3) ∉ l ∧ (List.IsChain (fun a b : Fin 3 => a ≠ 2 ∨ b ≠ 2) l)}

abbrev OrdinaryFamily (α : Type*) [Fintype α] (c a : ℕ) :=
  {ls : α → OrdinaryWord //
    (∑ i, (ls i).val.count 1) = c ∧ (∑ i, (ls i).val.count 2) = a}

private def bitsAt (l : OrdinaryWord) (k : Fin (l.val.count 1 + 1)) : Bool :=
  (bitsOf l.val)[k.val]'(by rw [bitsOf_length l.val l.prop.1 l.prop.2]; exact k.isLt)

private theorem ofFn_bitsAt (l : OrdinaryWord) : List.ofFn (bitsAt l) = bitsOf l.val := by
  apply List.ext_getElem
  · simp [bitsOf_length l.val l.prop.1 l.prop.2]
  · intro i h₁ h₂
    simp only [List.getElem_ofFn, bitsAt]

private theorem count_true_bitsAt (l : OrdinaryWord) :
    (Finset.univ.filter fun k => bitsAt l k).card = l.val.count 2 := by
  rw [← count_true_ofFn, ofFn_bitsAt, bitsOf_count l.val l.prop.1 l.prop.2]

private theorem card_slots_filter {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → ℕ) (f : (i : α) → Fin (g i + 1) → Bool) :
    (Finset.univ.filter fun p : (i : α) × Fin (g i + 1) => f p.1 p.2).card =
      ∑ i, (Finset.univ.filter fun k => f i k).card := by
  rw [← Finset.univ_sigma_univ, Finset.filter_sigma]
  exact Finset.card_sigma _ _

private def familyComp {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (ls : OrdinaryFamily α c a) : D5.S3.Combinatorics.ArrowWilfGapData.GapsOn α c :=
  ⟨Finsupp.equivFunOnFinite.symm (fun i => (ls.val i).val.count 1),
    Finset.mem_finsuppAntidiag.mpr ⟨ls.prop.1, Finset.subset_univ _⟩⟩

private def familySelected {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (ls : OrdinaryFamily α c a) : ↑((Finset.univ : Finset (((i : α) × Fin (((familyComp ls)).val i + 1)))).powersetCard a) :=
  ⟨Finset.univ.filter (fun p => bitsAt (ls.val p.1) p.2),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      change (Finset.univ.filter (fun p : (i : α) × Fin ((ls.val i).val.count 1 + 1) =>
        bitsAt (ls.val p.1) p.2)).card = a
      rw [card_slots_filter (fun i : α => (ls.val i).val.count 1)
        (fun i k => bitsAt (ls.val i) k)]
      simp_rw [count_true_bitsAt]
      exact ls.prop.2⟩⟩

private def familyEncode {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (ls : OrdinaryFamily α c a) : OrdinaryDataOn α c a :=
  ⟨familyComp ls, familySelected ls⟩

private def dataWord {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (d : OrdinaryDataOn α c a) (i : α) : OrdinaryWord :=
  ⟨insertTwos (List.ofFn fun k : Fin (d.1.val i + 1) => decide (⟨i, k⟩ ∈ d.2.val)),
    insertTwos_nonzero _, insertTwos_noAdjacent _⟩

private theorem dataWord_count_one {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (d : OrdinaryDataOn α c a) (i : α) : (dataWord d i).val.count 1 = d.1.val i := by
  have h := count_one_insertTwos
    (List.ofFn fun k : Fin (d.1.val i + 1) => decide (⟨i, k⟩ ∈ d.2.val))
    (by simp [List.ofFn_eq_nil_iff])
  simp only [List.length_ofFn] at h
  exact Nat.add_right_cancel h

private theorem dataWord_count_two {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (d : OrdinaryDataOn α c a) (i : α) :
    (dataWord d i).val.count 2 =
      (Finset.univ.filter fun k : Fin (d.1.val i + 1) => (⟨i, k⟩ : ((i : α) × Fin ((d.1).val i + 1))) ∈ d.2.val).card := by
  simp only [dataWord, count_two_insertTwos, count_true_ofFn, decide_eq_true_eq]

private def familyDecode {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (d : OrdinaryDataOn α c a) : OrdinaryFamily α c a :=
  ⟨dataWord d, by
    constructor
    · simp_rw [dataWord_count_one]
      exact (Finset.mem_finsuppAntidiag.mp d.1.prop).1
    · simp_rw [dataWord_count_two]
      have h := card_slots_filter (fun i => d.1.val i)
        (fun i k => decide ((⟨i, k⟩ : ((i : α) × Fin ((d.1).val i + 1))) ∈ d.2.val))
      simp only [decide_eq_true_eq, Sigma.eta, Finset.filter_mem_eq_inter, Finset.univ_inter] at h
      rw [← h]
      exact (Finset.mem_powersetCard.mp d.2.prop).2⟩

private theorem familyDecode_encode {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (ls : OrdinaryFamily α c a) : familyDecode (familyEncode ls) = ls := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  change insertTwos (List.ofFn fun k : Fin ((ls.val i).val.count 1 + 1) =>
    decide ((⟨i, k⟩ : ((i : α) × Fin (((familyComp ls)).val i + 1))) ∈ (familySelected ls).val)) = _
  have hh : (fun k : Fin ((ls.val i).val.count 1 + 1) =>
      decide ((⟨i, k⟩ : ((i : α) × Fin (((familyComp ls)).val i + 1))) ∈ (familySelected ls).val)) =
      bitsAt (ls.val i) := by
    funext k
    simp [familySelected]
  rw [hh, ofFn_bitsAt]
  exact insertTwos_bitsOf _ (ls.val i).prop.1 (ls.val i).prop.2

private theorem bitsAt_dataWord {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (d : OrdinaryDataOn α c a) (i : α) (k : Fin ((dataWord d i).val.count 1 + 1)) :
    bitsAt (dataWord d i) k =
      decide ((⟨i, ⟨k.val, by rw [← dataWord_count_one d i]; exact k.isLt⟩⟩ : ((i : α) × Fin ((d.1).val i + 1))) ∈ d.2.val) := by
  have hne : (List.ofFn fun k : Fin (d.1.val i + 1) =>
      decide ((⟨i, k⟩ : ((i : α) × Fin ((d.1).val i + 1))) ∈ d.2.val)) ≠ [] := by simp
  have hb : k.val < d.1.val i + 1 := by
    rw [← dataWord_count_one d i]
    exact k.isLt
  have heq := bitsOf_insertTwos
    (List.ofFn fun k : Fin (d.1.val i + 1) => decide ((⟨i, k⟩ : ((i : α) × Fin ((d.1).val i + 1))) ∈ d.2.val)) hne
  have hlen : k.val < (bitsOf (insertTwos
      (List.ofFn fun k : Fin (d.1.val i + 1) => decide ((⟨i, k⟩ : ((i : α) × Fin ((d.1).val i + 1))) ∈ d.2.val)))).length := by
    rw [congrArg List.length heq, List.length_ofFn]
    exact hb
  have hget := List.getElem_of_eq heq hlen
  simpa only [List.getElem_ofFn, bitsAt, dataWord] using hget

private theorem ordinaryData_ext {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    {g h : D5.S3.Combinatorics.ArrowWilfGapData.GapsOn α c} (s : ↑((Finset.univ : Finset (((i : α) × Fin ((g).val i + 1)))).powersetCard a)) (t : ↑((Finset.univ : Finset (((i : α) × Fin ((h).val i + 1)))).powersetCard a))
    (hgh : g = h)
    (hmem : ∀ i (k : Fin (g.val i + 1)) (l : Fin (h.val i + 1)),
      k.val = l.val → ((⟨i, k⟩ : ((i : α) × Fin ((g).val i + 1))) ∈ s.val ↔ (⟨i, l⟩ : ((i : α) × Fin ((h).val i + 1))) ∈ t.val)) :
    (⟨g, s⟩ : OrdinaryDataOn α c a) = ⟨h, t⟩ := by
  subst h
  congr 1
  apply Subtype.ext
  apply Finset.ext
  rintro ⟨i, k⟩
  exact hmem i k k rfl

private theorem familyEncode_decode {α : Type*} [Fintype α] [DecidableEq α] {c a : ℕ}
    (d : OrdinaryDataOn α c a) : familyEncode (familyDecode d) = d := by
  have hg : familyComp (familyDecode d) = d.1 := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact dataWord_count_one d i
  apply ordinaryData_ext _ _ hg
  intro i k l hkl
  simp only [familySelected, Finset.mem_filter, Finset.mem_univ, true_and]
  change bitsAt (dataWord d i) k = true ↔ (⟨i, l⟩ : ((i : α) × Fin ((d.1).val i + 1))) ∈ d.2.val
  change Fin ((dataWord d i).val.count 1 + 1) at k
  rw [bitsAt_dataWord d i k]
  simp only [decide_eq_true_eq]
  have hk : (⟨k.val, by rw [← dataWord_count_one d i]; exact k.isLt⟩ :
      Fin (d.1.val i + 1)) = l := Fin.ext hkl
  rw [hk]

private def ordinaryFamilyEquiv {α : Type*} [Fintype α] [DecidableEq α] (c a : ℕ) :
    OrdinaryFamily α c a ≃ OrdinaryDataOn α c a where
  toFun := familyEncode
  invFun := familyDecode
  left_inv := familyDecode_encode
  right_inv := familyEncode_decode

theorem ordinaryFamily_card (α : Type*) [Fintype α] [DecidableEq α] (c a : ℕ) :
    Nat.card (OrdinaryFamily α c a) =
      (c + Fintype.card α - 1).choose c * (c + Fintype.card α).choose a := by
  rw [Nat.card_congr (ordinaryFamilyEquiv (α := α) c a), ordinaryDataOn_card]

theorem ternary_count_length (l : List (Fin 3)) :
    l.count 0 + l.count 1 + l.count 2 = l.length := by
  have h := Multiset.sum_count_eq_card (s := Finset.univ) (m := (l : Multiset (Fin 3)))
    (fun a _ => Finset.mem_univ a)
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using h

theorem ordinary_length (l : OrdinaryWord) :
    l.val.count 1 + l.val.count 2 = l.val.length := by
  have h := ternary_count_length l.val
  rw [List.count_eq_zero.mpr l.prop.1, Nat.zero_add] at h
  exact h

private def ordinaryWordCountEquiv (c a : ℕ) :
    {l : OrdinaryWord // l.val.count 1 = c ∧ l.val.count 2 = a} ≃
      OrdinaryFamily Unit c a where
  toFun l := ⟨fun _ => l.val, by simpa using l.prop⟩
  invFun ls := ⟨ls.val (), by simpa using ls.prop⟩
  left_inv l := rfl
  right_inv ls := by
    apply Subtype.ext
    funext i
    cases i
    rfl

theorem ordinaryWord_card (c a : ℕ) :
    Nat.card {l : OrdinaryWord // l.val.count 1 = c ∧ l.val.count 2 = a} =
      (c + 1).choose a := by
  rw [Nat.card_congr (ordinaryWordCountEquiv c a), ordinaryFamily_card]
  simp

private instance ordinaryFamilyFinite {α : Type*} [Fintype α] [DecidableEq α]
    (c a : ℕ) : Finite (OrdinaryFamily α c a) :=
  Finite.of_equiv (OrdinaryDataOn α c a) (ordinaryFamilyEquiv c a).symm

end D5.S3.Combinatorics.Graph.ItalianDomination.OrdinaryWords
