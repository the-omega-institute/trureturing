/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Literal
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Literal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal five-row source arrays and their ordered scanner fibres. -/

/-
admission_basis: escape-witness
escape_witness: weight_one_seen and normalization_result
proof_shape: content: weight_one_seen, normalization_result.
The unbounded scanner inductions are retained here and consumed by symmetrized_count,
source_count, chromatic_source_count and HardinA233178Recurrence.result.
The remaining helpers and scanner_count are consumed bind-only steps; the source-count
conclusions retain content only through these same-delivery scanner inductions.
two_colour_unique directly specializes HardinA233260Literal.two_label_classification;
it is consumed by absence_count and supplies no separate escape witness.
absent_cons feeds weight_one_seen and normalization_result;
absent_swap and weight_one_seen feed normalization_result.
Direct frozen dependencies include HardinA233255LiteralBridge.scanner_fibres and rowWeight,
HardinA233255ShapeSymmetry.full_row, HardinA233260Literal.two_label_classification,
and HardinA233251TriangleStrip.colour_bond_iff.
utility none: these are unbounded scanner and source-cardinality identities, not bounded
instances, checker infrastructure, numerical premises or finite certified instances.
The source is the pinned OEIS A233178 revision cited by Library/Automata/hardin2013a233178.md.
No corresponding theory volume was found in the source-identifier and relation search.
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal

/-! The source predicates retain every literal restriction independently of the transfer. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal

open HardinA233175PairStrip (good good_iff allowed advance)
open HardinA233255LiteralBridge (rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

open HardinA233255LiteralBridge (rowWeight labelWeight rowFinish labelAdvance)

/-- Exchange the two complementary-pair labels other than the initial pair. -/
def swap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Absence of one label from the entire word. -/
def absent {k : ℕ} (q : Fin k → Fin 3) (c : Fin 3) : ℤ :=
  if ∀ j, q j ≠ c then 1 else 0

private theorem absent_cons {k : ℕ} (a c : Fin 3) (q : Fin k → Fin 3) :
    absent (Fin.cons a q) c = (if a = c then 0 else absent q c) := by
  simp only [absent, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  by_cases h : a = c <;> simp [h]

private theorem weight_one_seen (k : ℕ) (q : Fin k → Fin 3) :
    2 * rowWeight (true, false) q = 2^k * (1 + absent q 2) := by
  induction k with
  | zero => norm_num [rowWeight, absent]
  | succ k ih =>
    rw [← Fin.cons_self_tail q]
    simp only [rowWeight, Fin.cons_zero, Fin.tail_cons, absent_cons]
    have h := ih (Fin.tail q)
    have hc := (HardinA233255ShapeSymmetry.full_row k (Fin.tail q)).2
    generalize q 0 = a
    fin_cases a <;> norm_num [labelWeight, labelAdvance] <;>
      rw [pow_succ] <;> nlinarith

private theorem absent_swap {k : ℕ} (q : Fin k → Fin 3) (c : Fin 3) :
    absent (fun j => swap (q j)) c = absent q (swap c) := by
  have he : (∀ j, swap (q j) ≠ c) ↔ ∀ j, q j ≠ swap c := by
    apply forall_congr'
    intro j
    have hc : swap (swap c) = c := Equiv.swap_apply_self 1 2 c
    constructor
    · intro h heq
      exact h (heq ▸ hc)
    · intro h heq
      apply h
      have := congrArg swap heq
      simpa [swap] using this
  simp only [absent, he]

/-- Exact missing-label correction for the two possible orders of first appearance. -/
theorem normalization_result (k : ℕ) (q : Fin k → Fin 3) :
    4 * (rowWeight (false, false) q +
      rowWeight (false, false) (fun j => swap (q j))) =
    2^k * (1 + absent q 1 + absent q 2 + 5 * (absent q 1 * absent q 2)) := by
  induction k with
  | zero => norm_num [rowWeight, absent]
  | succ k ih =>
    rw [← Fin.cons_self_tail q]
    have hswap : (fun j => swap ((Fin.cons (q 0) (Fin.tail q) : Fin (k+1) → Fin 3) j)) =
        Fin.cons (swap (q 0)) (fun j => swap (Fin.tail q j)) :=
      Fin.comp_cons swap _ _
    rw [hswap]
    simp only [rowWeight, Fin.cons_zero, Fin.tail_cons, absent_cons]
    have h0 := ih (Fin.tail q)
    have h1 := weight_one_seen k (Fin.tail q)
    have h2 := weight_one_seen k (fun j => swap (Fin.tail q j))
    rw [absent_swap] at h2
    generalize q 0 = a
    fin_cases a <;>
      norm_num [labelWeight, labelAdvance, swap, Equiv.swap_apply_def] at * <;>
      rw [pow_succ] <;> nlinarith



abbrev Array (n : ℕ) (c : ℕ) := Fin 5 × Fin n → Fin c

/-- The literal strict row-major rank. -/
def rank {n : ℕ} (p : Fin 5 × Fin n) : ℕ := p.1.val * n + p.2.val

/-- Exactly the horizontal, diagonal and antidiagonal edges, oriented rightwards. -/
def Edges {n : ℕ} (p q : Fin 5 × Fin n) : Prop :=
  q.2.val = p.2.val + 1 ∧ p.1.val ≤ q.1.val + 1 ∧ q.1.val ≤ p.1.val + 1

def Normal {n : ℕ} (x : Array n 6) : Prop :=
  ∀ p, ((x p = 2 ∨ x p = 3 ∨ x p = 4) →
    ∃ q, rank q < rank p ∧ x q = 1) ∧
    (x p = 3 → ∃ q, rank q < rank p ∧ x q = 2)

def Legal {n : ℕ} (x : Array n 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ x (0, j) = 0) ∧
  (∀ p q, Edges p q → x p ≠ x q ∧ (x p).val + (x q).val ≠ 5) ∧ Normal x

instance {n : ℕ} (x : Array n 6) : Decidable (Legal x) := by
  unfold Legal Normal Edges
  infer_instance

/-- Source count: no surjectivity, vertical edge, wraparound edge or divisor. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun x : Array n 6 => Legal x)).card

/-- The unchanged all-width literal event, with integer recurrence arithmetic. -/
def FullE : Prop := ∀ n : ℕ, n > 11 →
  (a n : ℤ) = 192 * (a (n-1) : ℤ) + 31744 * (a (n-2) : ℤ) -
    3178496 * (a (n-3) : ℤ) - 170917888 * (a (n-4) : ℤ) +
    13992198144 * (a (n-5) : ℤ) + 99857989632 * (a (n-6) : ℤ) -
    17660905521152 * (a (n-7) : ℤ) + 211106232532992 * (a (n-8) : ℤ) +
    2533274790395904 * (a (n-9) : ℤ) - 40532396646334464 * (a (n-10) : ℤ)

/-- Pull an array into its row-major word, using the actual rank bijection. -/
def word {n c : ℕ} (x : Array n c) : Fin (5*n) → Fin c :=
  fun k => x (finProdFinEquiv.symm k)

private theorem rank_equiv {n : ℕ} (p : Fin 5 × Fin n) :
    (finProdFinEquiv p).val = rank p := by
  simp [rank, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

private theorem normal_scanner {n : ℕ} (x : Array n 6) :
    Normal x ↔ good (false, false) (word x) := by
  rw [good_iff]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · intro h i
    have hi := h (finProdFinEquiv.symm i)
    constructor
    · intro hc
      obtain ⟨q, hq, he⟩ := hi.1 hc
      exact ⟨finProdFinEquiv q, by
        simpa only [Fin.lt_def, rank_equiv, ← rank_equiv, Equiv.apply_symm_apply] using hq,
        by simpa [word] using he⟩
    · intro hc
      obtain ⟨q, hq, he⟩ := hi.2 hc
      exact ⟨finProdFinEquiv q, by
        simpa only [Fin.lt_def, rank_equiv, ← rank_equiv, Equiv.apply_symm_apply] using hq,
        by simpa [word] using he⟩
  · intro h p
    have hi := h (finProdFinEquiv p)
    simp only [word, Equiv.symm_apply_apply] at hi
    constructor
    · intro hc
      obtain ⟨j, hj, he⟩ := hi.1 hc
      exact ⟨finProdFinEquiv.symm j, by
        simpa only [Fin.lt_def, rank_equiv, ← rank_equiv, Equiv.apply_symm_apply] using hj, he⟩
    · intro hc
      obtain ⟨j, hj, he⟩ := hi.2 hc
      exact ⟨finProdFinEquiv.symm j, by
        simpa only [Fin.lt_def, rank_equiv, ← rank_equiv, Equiv.apply_symm_apply] using hj, he⟩

def Proper {n : ℕ} (q : Array n 3) : Prop := ∀ p r, Edges p r → q p ≠ q r

instance {n : ℕ} (q : Array n 3) : Decidable (Proper q) := by
  unfold Proper Edges
  infer_instance

def Anchored {n : ℕ} (q : Array n 3) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ q (0,j) = 0) ∧ Proper q

instance {n : ℕ} (q : Array n 3) : Decidable (Anchored q) := by
  unfold Anchored
  infer_instance

private theorem colour_edge (u v : Fin 6) :
    (u ≠ v ∧ u.val + v.val ≠ 5) ↔ beta u ≠ beta v :=
  HardinA233251TriangleStrip.colour_bond_iff u v

private def flip : Equiv.Perm (Fin 6) := Equiv.swap 0 5

private theorem flip_cell : ∀ (s : HardinA233175PairStrip.Seen) (c : Fin 6),
    beta (flip c) = beta c ∧ (allowed s (flip c) ↔ allowed s c) ∧
      advance s (flip c) = advance s c := by
  decide +kernel

private theorem good_flip {k : ℕ} (s : HardinA233175PairStrip.Seen) (x : Fin k → Fin 6) :
    good s (fun i => flip (x i)) ↔ good s x := by
  have hf (c : Fin 6) (d : Fin 6) (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4) :
      flip c = d ↔ c = d := by
    rcases hd with rfl | rfl | rfl | rfl <;> fin_cases c <;> decide +kernel
  simp only [good_iff, hf _ 1 (Or.inl rfl), hf _ 2 (Or.inr (Or.inl rfl)),
    hf _ 3 (Or.inr (Or.inr (Or.inl rfl))), hf _ 4 (Or.inr (Or.inr (Or.inr rfl)))]

private theorem beta_zero (c : Fin 6) : beta c = 0 ↔ c = 0 ∨ c = 5 := by
  fin_cases c <;> decide +kernel

private theorem legal_sum (n : ℕ) :
    (a n : ℤ) = ∑ x : Array n 6, if Legal x then 1 else 0 := by
  simp only [a, Finset.card_filter]
  push_cast
  rfl

private theorem lifted_sum (n : ℕ) :
    2 * (a n : ℤ) = ∑ x : Array n 6,
      if good (false,false) (word x) ∧ Anchored (fun p => beta (x p)) then 1 else 0 := by
  classical
  let L (d : Fin 6) (x : Array n 6) : Prop :=
    (∃ j : Fin n, j.val = 0 ∧ x (0,j) = d) ∧
      Proper (fun p => beta (x p)) ∧ good (false,false) (word x)
  have h0 (x : Array n 6) : L 0 x ↔ Legal x := by
    simp only [L, Legal, Proper, colour_edge, normal_scanner]
  let E : Array n 6 ≃ Array n 6 := Equiv.arrowCongr (Equiv.refl _) flip
  have hf (x : Array n 6) : L 5 (E x) ↔ L 0 x := by
    change ((∃ j : Fin n, j.val = 0 ∧ flip (x (0,j)) = 5) ∧
      Proper (fun p => beta (flip (x p))) ∧
      good (false,false) (fun i => flip (word x i))) ↔ L 0 x
    have he (c : Fin 6) : flip c = 5 ↔ c = 0 := by fin_cases c <;> decide +kernel
    have hb (c : Fin 6) : beta (flip c) = beta c := (flip_cell (false,false) c).1
    simp only [he, L, Proper, hb, good_flip]
  have hs : (∑ x : Array n 6, if L 5 x then (1:ℤ) else 0) = (a n : ℤ) := by
    rw [← E.sum_comp]
    simpa only [hf, h0] using (legal_sum n).symm
  have he (x : Array n 6) :
      (if good (false,false) (word x) ∧ Anchored (fun p => beta (x p)) then (1:ℤ) else 0) =
      (if L 0 x then 1 else 0) + (if L 5 x then 1 else 0) := by
    have hdis : ¬ (L 0 x ∧ L 5 x) := by
      rintro ⟨⟨⟨j,hj,hx⟩,_,_⟩, ⟨⟨k,hk,hy⟩,_,_⟩⟩
      have : j = k := Fin.ext (hj.trans hk.symm)
      subst k
      rw [hx] at hy
      exact (by decide : (0 : Fin 6) ≠ 5) hy
    have hex : (good (false,false) (word x) ∧ Anchored (fun p => beta (x p))) ↔
        L 0 x ∨ L 5 x := by
      simp only [Anchored, beta_zero, L]
      constructor
      · rintro ⟨hg,⟨j,hj,h0|h5⟩,hp⟩
        · exact Or.inl ⟨⟨j,hj,h0⟩,hp,hg⟩
        · exact Or.inr ⟨⟨j,hj,h5⟩,hp,hg⟩
      · rintro (⟨⟨j,hj,h0⟩,hp,hg⟩ | ⟨⟨j,hj,h5⟩,hp,hg⟩)
        · exact ⟨hg,⟨j,hj,Or.inl h0⟩,hp⟩
        · exact ⟨hg,⟨j,hj,Or.inr h5⟩,hp⟩
    simp only [hex]
    by_cases h : L 0 x <;> by_cases h' : L 5 x <;> simp_all
  simp_rw [he]
  rw [Finset.sum_add_distrib, hs]
  simp_rw [h0]
  rw [← legal_sum]
  ring

/-- Exact weighted source count on all widths, before the graph-specific absence correction. -/
theorem scanner_count (n : ℕ) :
    2 * (a n : ℤ) = ∑ q : Array n 3,
      if Anchored q then rowWeight (false,false) (word q) else 0 := by
  classical
  rw [lifted_sum]
  let E6 : (Fin (5*n) → Fin 6) ≃ Array n 6 :=
    Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl _)
  let E3 : (Fin (5*n) → Fin 3) ≃ Array n 3 :=
    Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl _)
  rw [← E6.sum_comp, ← E3.sum_comp]
  have h := scanner_fibres (5*n) (false,false)
    (fun _ q => if Anchored (E3 q) then (1:ℤ) else 0)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro x _
    have hw : word (E6 x) = x := by
      funext i
      change x (finProdFinEquiv (finProdFinEquiv.symm i)) = x i
      rw [Equiv.apply_symm_apply]
    rw [hw]
    change (if good (false,false) x ∧ Anchored (E3 (fun j => beta (x j))) then _ else _) = _
    split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro q _
    have hw : word (E3 q) = q := by
      funext i
      change q (finProdFinEquiv (finProdFinEquiv.symm i)) = q i
      rw [Equiv.apply_symm_apply]
    rw [hw]
    split_ifs <;> simp_all

/-- Anchored proper three-label arrays, with no scanner or surjectivity condition. -/
def pairCount (n : ℕ) : ℤ := ∑ q : Array n 3, if Anchored q then 1 else 0

private def absenceCount (n : ℕ) (c : Fin 3) : ℤ :=
  ∑ q : Array n 3, if Anchored q then absent (word q) c else 0

private def doubleAbsenceCount (n : ℕ) : ℤ :=
  ∑ q : Array n 3, if Anchored q then
    absent (word q) 1 *
      absent (word q) 2 else 0

private theorem anchored_swap {n : ℕ} (q : Array n 3) :
    Anchored (fun p => swap (q p)) ↔ Anchored q := by
  have hs : ∀ c : Fin 3, swap c = 0 ↔ c = 0 := by
    decide +kernel
  simp only [Anchored, Proper, hs, swap.injective.ne_iff]

private theorem symmetrized_count (n : ℕ) :
    16 * (a n : ℤ) = (2:ℤ)^(5*n) *
      (pairCount n + absenceCount n 1 + absenceCount n 2 + 5 * doubleAbsenceCount n) := by
  classical
  let E : Array n 3 ≃ Array n 3 :=
    Equiv.arrowCongr (Equiv.refl _) swap
  have hs : (∑ q : Array n 3, if Anchored q then
      rowWeight (false,false) (fun i => swap (word q i)) else 0) =
      2 * (a n : ℤ) := by
    rw [scanner_count, ← E.sum_comp]
    apply Finset.sum_congr rfl
    intro q _
    change (if Anchored (fun p => swap (q p)) then
      rowWeight (false,false) (fun i => swap
        (swap (word q i))) else 0) = _
    have hss (c : Fin 3) : swap
        (swap c) = c := Equiv.swap_apply_self 1 2 c
    simp only [anchored_swap, hss]
  have hi (q : Array n 3) :
      4 * ((if Anchored q then rowWeight (false,false) (word q) else 0) +
        (if Anchored q then rowWeight (false,false)
          (fun i => swap (word q i)) else 0)) =
      (2:ℤ)^(5*n) * (if Anchored q then
        1 + absent (word q) 1 +
          absent (word q) 2 +
          5 * (absent (word q) 1 *
            absent (word q) 2) else 0) := by
    split_ifs
    · exact normalization_result (5*n) (word q)
    · ring
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun q _ => hi q)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← scanner_count, hs, ← Finset.mul_sum] at hh
  have ht : (∑ q : Array n 3, if Anchored q then
      1 + absent (word q) 1 +
        absent (word q) 2 +
        5 * (absent (word q) 1 *
          absent (word q) 2) else 0) =
      pairCount n + absenceCount n 1 + absenceCount n 2 + 5 * doubleAbsenceCount n := by
    simp only [pairCount, absenceCount, doubleAbsenceCount, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> ring
  rw [ht] at hh
  linarith

private theorem two_colour_unique {n : ℕ} (hn : 2 ≤ n) (c : Fin 3)
    (q q' : Array n 3) (hq : Anchored q) (hq' : Anchored q')
    (hc : ∀ p, q p ≠ c) (hc' : ∀ p, q' p ≠ c) : q = q' := by
  have classify (f : Array n 3) (hf : Anchored f) (hm : ∀ p, f p ≠ c) :
      ∃ b : Fin 3, 0 ≠ b ∧ b ≠ c ∧
        f = (fun p => if p.2.val % 2 = 0 then 0 else b) := by
    have hp : HardinA233260Literal.Proper f := by
      intro j hj r s hrs
      apply hf.2 (r, j) (s, ⟨j.val + 1, hj⟩)
      rcases hrs with hrs | hrs
      · subst s
        simp [Edges]
      · simp only [Edges, true_and]
        omega
    obtain ⟨a, b, hab, he⟩ :=
      HardinA233260Literal.two_label_classification hn f hp c hm
    change f = (fun p => if p.2.val % 2 = 0 then a else b) at he
    have ha : a = 0 := by
      obtain ⟨j, hj, h0⟩ := hf.1
      rw [he] at h0
      simpa [hj] using h0
    subst a
    have hb : b ≠ c := by
      simpa [he] using hm (0, ⟨1, by omega⟩)
    exact ⟨b, hab, hb, he⟩
  obtain ⟨b, hb0, hbc, he⟩ := classify q hq hc
  obtain ⟨b', hb'0, hb'c, he'⟩ := classify q' hq' hc'
  have hb : b = b' := by
    have hc0 : (0 : Fin 3) ≠ c := by
      simpa [he] using hc (0, ⟨0, by omega⟩)
    fin_cases b <;> fin_cases b' <;> fin_cases c <;> simp_all
  rw [hb] at he
  exact he.trans he'.symm

private theorem alternating_spec (n : ℕ) (hn : 0 < n) (c : Fin 3)
    (hc : c = 1 ∨ c = 2) :
    Anchored (HardinA233260Literal.alternating n 0 (if c = 1 then 2 else 1)) ∧ ∀ p, HardinA233260Literal.alternating n 0 (if c = 1 then 2 else 1) p ≠ c := by
  rcases hc with rfl | rfl <;> constructor
  · refine ⟨⟨⟨0,hn⟩,rfl,by simp [HardinA233260Literal.alternating]⟩,?_⟩
    intro p q he
    have hj := he.1
    norm_num only [HardinA233260Literal.alternating, ite_true]
    split_ifs <;> (first | decide | omega)
  · intro p
    norm_num only [HardinA233260Literal.alternating, ite_true]
    split_ifs <;> decide
  · refine ⟨⟨⟨0,hn⟩,rfl,by simp [HardinA233260Literal.alternating]⟩,?_⟩
    intro p q he
    have hj := he.1
    norm_num only [HardinA233260Literal.alternating, show (2:Fin 3) ≠ 1 by decide, ite_false]
    split_ifs <;> (first | decide | omega)
  · intro p
    norm_num only [HardinA233260Literal.alternating, show (2:Fin 3) ≠ 1 by decide, ite_false]
    split_ifs <;> decide

private theorem absent_word {n : ℕ} (q : Array n 3) (c : Fin 3) :
    absent (word q) c = if ∀ p, q p ≠ c then 1 else 0 := by
  have he : (∀ j, word q j ≠ c) ↔ ∀ p, q p ≠ c := by
    constructor
    · intro h p
      simpa only [word, Equiv.symm_apply_apply] using h (finProdFinEquiv p)
    · intro h j
      exact h _
  simp only [absent, he]

private theorem absence_count {n : ℕ} (hn : 2 ≤ n) (c : Fin 3)
    (hc : c = 1 ∨ c = 2) : absenceCount n c = 1 := by
  classical
  have hs := alternating_spec n (by omega) c hc
  have he (q : Array n 3) :
      (if Anchored q then absent (word q) c else 0) =
      if q = HardinA233260Literal.alternating n 0 (if c = 1 then 2 else 1) then (1:ℤ) else 0 := by
    rw [absent_word]
    by_cases hq : q = HardinA233260Literal.alternating n 0 (if c = 1 then 2 else 1)
    · subst q
      simp [hs]
    · have hnq : ¬ (Anchored q ∧ ∀ p, q p ≠ c) := by
        rintro ⟨ha,hb⟩
        exact hq (two_colour_unique hn c q (HardinA233260Literal.alternating n 0 (if c = 1 then 2 else 1)) ha hs.1 hb hs.2)
      by_cases ha : Anchored q <;> simp_all
  unfold absenceCount
  simp_rw [he]
  simp

private theorem double_absence_count {n : ℕ} (hn : 2 ≤ n) : doubleAbsenceCount n = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  rw [absent_word, absent_word]
  split_ifs with ha h1 h2
  · let z : Fin n := ⟨0,by omega⟩
    let o : Fin n := ⟨1,by omega⟩
    have h := ha.2 (0,z) (0,o) (by simp [Edges,z,o])
    have hz : q (0,z) = 0 := by
      have h' := h1 (0,z)
      have h'' := h2 (0,z)
      have hfin := (q (0,z)).isLt
      apply Fin.ext
      change (q (0,z)).val = 0
      have hh1 : (q (0,z)).val ≠ 1 := by intro hh; exact h' (Fin.ext hh)
      have hh2 : (q (0,z)).val ≠ 2 := by intro hh; exact h'' (Fin.ext hh)
      omega
    have ho : q (0,o) = 0 := by
      have h' := h1 (0,o)
      have h'' := h2 (0,o)
      have hfin := (q (0,o)).isLt
      apply Fin.ext
      change (q (0,o)).val = 0
      have hh1 : (q (0,o)).val ≠ 1 := by intro hh; exact h' (Fin.ext hh)
      have hh2 : (q (0,o)).val ≠ 2 := by intro hh; exact h'' (Fin.ext hh)
      omega
    exact (h (hz.trans ho.symm)).elim
  all_goals ring

/-- Exact source-count bridge, including the two missing-label fibres. -/
theorem source_count (n : ℕ) (hn : 2 ≤ n) :
    16 * (a n : ℤ) = (32:ℤ)^n * (pairCount n + 2) := by
  have h := symmetrized_count n
  rw [absence_count hn 1 (Or.inl rfl), absence_count hn 2 (Or.inr rfl),
    double_absence_count hn] at h
  have hp : (2:ℤ)^(5*n) = 32^n := by rw [pow_mul]; norm_num
  rw [hp] at h
  convert h using 1 <;> ring

/-- All proper three-label arrays on the literal graph. -/
def chromaticCount (n : ℕ) : ℤ := ∑ q : Array n 3, if Proper q then 1 else 0

private theorem anchored_third (n : ℕ) (hn : 0 < n) :
    chromaticCount n = 3 * pairCount n := by
  classical
  let z : Fin n := ⟨0,hn⟩
  let C (c : Fin 3) : ℤ := ∑ q : Array n 3,
    if Proper q ∧ q (0,z) = c then 1 else 0
  have hc (c : Fin 3) : C c = pairCount n := by
    let e : Equiv.Perm (Fin 3) := Equiv.swap 0 c
    let E : Array n 3 ≃ Array n 3 := Equiv.arrowCongr (Equiv.refl _) e
    have he (d : Fin 3) : e d = c ↔ d = 0 := by
      have he0 : e 0 = c := by simp [e]
      rw [← he0, e.injective.eq_iff]
    have ha (q : Array n 3) : Anchored q ↔ Proper q ∧ q (0,z) = 0 := by
      constructor
      · rintro ⟨⟨j,hj,hv⟩,hp⟩
        have h : j = z := Fin.ext hj
        exact ⟨hp, h ▸ hv⟩
      · rintro ⟨hp,hv⟩
        exact ⟨⟨z,rfl,hv⟩,hp⟩
    unfold C pairCount
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro q _
    change (if Proper (fun p => e (q p)) ∧ e (q (0,z)) = c then _ else _) = _
    simp only [Proper, e.injective.ne_iff, he, ha]
  have hsum : chromaticCount n = ∑ c : Fin 3, C c := by
    unfold chromaticCount C
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hp : Proper q <;> simp [hp]
  rw [hsum]
  simp_rw [hc]
  simp

/-- Division-free source correspondence for the unrestricted chromatic count. -/
theorem chromatic_source_count (n : ℕ) (hn : 2 ≤ n) :
    48 * (a n : ℤ) = (32:ℤ)^n * (chromaticCount n + 6) := by
  have hs := source_count n hn
  rw [anchored_third n (by omega)]
  linarith

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
