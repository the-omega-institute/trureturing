/- GID: D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: The one-common-Zeckendorf-term greedy sequence permutes the positive integers. -/
module

public import D5.S0.Conventions.WDigits
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Tactic.Push

/-! The support uses canonical Fibonacci indices, and minimization uses the full actual history. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation
open D5.S0.Conventions

/-- Fibonacci indices, starting at index two, in the canonical representation. -/
def support (m : ℕ) : Finset ℕ := (wdigits m).toFinset

/-- Exactly one common canonical Fibonacci term. -/
def Adjacent (x y : ℕ) : Prop := (support x ∩ support y).card = 1

private instance gap_trans : IsTrans ℕ (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem support_ge {m i : ℕ} (hi : i ∈ support m) : 2 ≤ i := by
  have hc : (wdigits m ++ [0]).Pairwise (fun a b => b + 2 ≤ a) :=
    List.isChain_iff_pairwise.mp (wdigits_isCanonical m)
  have h := (List.pairwise_append.mp hc).2.2 i (List.mem_toFinset.mp hi) 0 (by simp)
  simpa using h

private theorem fib_le {m i : ℕ} (hi : i ∈ support m) : Nat.fib i ≤ m := by
  rw [← decode_wdigits m]
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
    (List.mem_map.mpr ⟨i, List.mem_toFinset.mp hi, rfl⟩)

private theorem index_bound {m i : ℕ} (hi : i ∈ support m) : i ≤ m + 1 := by
  have := fib_le hi
  have := Nat.le_fib_add_one i
  omega

private theorem support_nonempty (m : ℕ) (hm : 0 < m) : (support m).Nonempty := by
  by_contra hn
  have hz : wdigits m = [] := by
    simpa [support] using (Finset.not_nonempty_iff_eq_empty.mp hn)
  have hd := decode_wdigits m
  simp [hz] at hd
  omega

private theorem support_singleton (i : ℕ) (hi : 2 ≤ i) :
    support (Nat.fib i) = {i} := by
  have hc : [i].IsZeckendorfRep := by simp [List.IsZeckendorfRep, hi]
  have hz : [i] = wdigits (Nat.fib i) := wdigits_unique hc (by simp)
  simp [support, ← hz]

private theorem support_one : support 1 = {2} := by
  simpa using support_singleton 2 (by omega)

private theorem support_pair (i j : ℕ) (hi : 2 ≤ i) (hij : i + 2 ≤ j) :
    support (Nat.fib i + Nat.fib j) = {i, j} := by
  have hc : [j, i].IsZeckendorfRep := by
    simp [List.IsZeckendorfRep, hi, hij]
  have hz : [j, i] = wdigits (Nat.fib i + Nat.fib j) :=
    wdigits_unique hc (by simp; omega)
  simp [support, ← hz, Finset.pair_comm]

private theorem support_triple (r s t : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hrs : r + 2 ≤ s ∨ s + 2 ≤ r) (hrt : r + 2 ≤ t) (hst : s + 2 ≤ t) :
    support (Nat.fib r + Nat.fib s + Nat.fib t) = {r, s, t} := by
  rcases hrs with hrs | hrs
  · have hc : [t, s, r].IsZeckendorfRep := by
      simp [List.IsZeckendorfRep, hr, hrs, hst]
    have hz : [t, s, r] = wdigits (Nat.fib r + Nat.fib s + Nat.fib t) :=
      wdigits_unique hc (by simp; omega)
    simp only [support, ← hz, List.toFinset_cons, List.toFinset_nil]
    ext k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · have hc : [t, r, s].IsZeckendorfRep := by
      simp [List.IsZeckendorfRep, hs, hrs, hrt]
    have hz : [t, r, s] = wdigits (Nat.fib r + Nat.fib s + Nat.fib t) :=
      wdigits_unique hc (by simp; omega)
    simp only [support, ← hz, List.toFinset_cons, List.toFinset_nil]
    ext k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

private theorem pair_adjacent (c i j : ℕ) (hi : i ∈ support c)
    (hj : j ∉ support c) (hij : i + 2 ≤ j) :
    Adjacent c (Nat.fib i + Nat.fib j) := by
  unfold Adjacent
  rw [support_pair i j (support_ge hi) hij]
  have he : support c ∩ {i, j} = {i} := by
    ext k
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [he]
  simp

private theorem exists_next (l : List ℕ) (c : ℕ) (hc : 0 < c) :
    ∃ m, 0 < m ∧ m ∉ l ∧ Adjacent c m := by
  obtain ⟨i, hi⟩ := support_nonempty c hc
  let j := l.sum + c + i + 5
  have hij : i + 2 ≤ j := by dsimp [j]; omega
  have hj : j ∉ support c := by
    intro h
    have := index_bound h
    dsimp [j] at this
    omega
  have hfi : 0 < Nat.fib i := Nat.fib_pos.mpr (by have := support_ge hi; omega)
  have hfj := Nat.le_fib_add_one j
  have hlarge : l.sum < Nat.fib i + Nat.fib j := by
    dsimp [j] at hfj ⊢
    omega
  refine ⟨Nat.fib i + Nat.fib j, by omega, ?_, pair_adjacent c i j hi hj hij⟩
  intro hm
  have := List.single_le_sum (fun _ _ => Nat.zero_le _) _ hm
  omega

private noncomputable def pick (l : List ℕ) (c : ℕ) (hc : 0 < c) : ℕ :=
  by classical exact Nat.find (exists_next l c hc)

private theorem pick_spec (l : List ℕ) (c : ℕ) (hc : 0 < c) :
    0 < pick l c hc ∧ pick l c hc ∉ l ∧ Adjacent c (pick l c hc) :=
  by classical exact Nat.find_spec (exists_next l c hc)

private noncomputable def history : ℕ → List ℕ × {c : ℕ // 0 < c}
  | 0 => ([1], ⟨1, by omega⟩)
  | n + 1 =>
    let m := pick (history n).1 (history n).2.1 (history n).2.2
    (m :: (history n).1, ⟨m, (pick_spec _ _ _).1⟩)

private noncomputable def terms (n : ℕ) : List ℕ := (history n).1
private noncomputable def v (n : ℕ) : ℕ := (history n).2.1

private theorem v_zero : v 0 = 1 := rfl
private theorem v_pos (n : ℕ) : 0 < v n := (history n).2.2

private theorem step_spec (n : ℕ) :
    0 < v (n + 1) ∧ v (n + 1) ∉ terms n ∧ Adjacent (v n) (v (n + 1)) :=
  pick_spec (terms n) (v n) (v_pos n)

private theorem greedy (n m : ℕ) (hp : 0 < m) (hu : m ∉ terms n)
    (ha : Adjacent (v n) m) : v (n + 1) ≤ m :=
  by classical exact Nat.find_min' (exists_next (terms n) (v n) (v_pos n)) ⟨hp, hu, ha⟩

private theorem mem_terms (n m : ℕ) : m ∈ terms n ↔ ∃ i ≤ n, v i = m := by
  induction n with
  | zero =>
      change m ∈ [1] ↔ ∃ i ≤ 0, v i = m
      simp [v_zero, eq_comm]
  | succ n ih =>
      change m ∈ v (n + 1) :: terms n ↔ _
      rw [List.mem_cons, ih]
      constructor
      · rintro (he | ⟨i, hi, he⟩)
        · exact ⟨n + 1, le_rfl, he.symm⟩
        · exact ⟨i, by omega, he⟩
      · rintro ⟨i, hi, he⟩
        by_cases hn : i = n + 1
        · left; simpa [hn] using he.symm
        · right; exact ⟨i, by omega, he⟩

private theorem v_injective : Function.Injective v := by
  have distinct : ∀ i j, i < j → v i ≠ v j := by
    intro i j hij he
    cases j with
    | zero => omega
    | succ j =>
        exact (step_spec j).2.1 ((mem_terms j _).mpr ⟨i, by omega, he⟩)
  intro i j he
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (distinct i j h he)
  · exact h
  · exact False.elim (distinct j i h he.symm)

private def Visited (m : ℕ) : Prop := ∃ n, v n = m

private theorem omitted_not_mem {m : ℕ} (hm : ¬ Visited m) (n : ℕ) : m ∉ terms n := by
  rw [mem_terms]
  rintro ⟨i, _, hi⟩
  exact hm ⟨i, hi⟩

/-- OEIS indexing: `a 1 = 1`; the internal history at stage `n` gives `a (n+1)`. -/
noncomputable def a (n : ℕ) : ℕ := v (n - 1)

/-- The positive unused candidates after the complete one-based prefix. -/
def Eligible (s : ℕ → ℕ) (n m : ℕ) : Prop :=
  0 < m ∧ (∀ k, 1 ≤ k → k ≤ n → s k ≠ m) ∧ Adjacent (s n) m

/-- The whole totality, numerical leastness and positive-integer permutation assertion. -/
def IsGreedyPermutation (s : ℕ → ℕ) : Prop :=
  s 1 = 1 ∧
  (∀ n, 1 ≤ n → 0 < s n) ∧
  (∀ n, 1 ≤ n → Eligible s n (s (n + 1)) ∧
    ∀ m, Eligible s n m → s (n + 1) ≤ m) ∧
  (∀ i j, 1 ≤ i → 1 ≤ j → s i = s j → i = j) ∧
  ∀ m, 1 ≤ m → ∃ n, 1 ≤ n ∧ s n = m


private theorem neighbor_covers (m : ℕ) (hm : 0 < m)
    (hn : ∀ B, ∃ x, B < x ∧ Visited x ∧ Adjacent x m) : Visited m := by
  by_contra omitted
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (v_injective.nat_tendsto_atTop.eventually (Filter.eventually_gt_atTop m))
  obtain ⟨x, hx, ⟨n, hn⟩, ha⟩ := hn (terms N).sum
  have htime : N < n := by
    by_contra h
    have hmem := (mem_terms N x).mpr ⟨n, by omega, hn⟩
    have := List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
    omega
  have hadj : Adjacent (v n) m := by simpa [hn] using ha
  have hle := greedy n m hm (omitted_not_mem omitted n) hadj
  have := hN (n + 1) (by omega)
  omega

private theorem peak_mem (m : ℕ) (hm : 0 < m) : Nat.greatestFib m ∈ support m := by
  simp [support, wdigits, Nat.zeckendorf_of_pos hm]

private theorem le_peak {m i : ℕ} (hi : i ∈ support m) : i ≤ Nat.greatestFib m :=
  Nat.le_greatestFib.mpr (fib_le hi)

private theorem peak_pair (m i : ℕ) (hm : 0 < m) (hi : i ∈ support m)
    (hne : i ≠ Nat.greatestFib m) :
    i + 2 ≤ Nat.greatestFib m ∧ Nat.fib i + Nat.fib (Nat.greatestFib m) ≤ m := by
  let l := Nat.zeckendorf (m - Nat.fib (Nat.greatestFib m))
  have hz : wdigits m = Nat.greatestFib m :: l := Nat.zeckendorf_of_pos hm
  have hil : i ∈ l := by simpa [support, hz, hne] using hi
  have hc : (Nat.greatestFib m :: (l ++ [0])).Pairwise (fun a b => b + 2 ≤ a) := by
    simpa only [List.IsZeckendorfRep, hz, List.cons_append, List.isChain_iff_pairwise]
      using wdigits_isCanonical m
  have hgap := (List.pairwise_cons.mp hc).1 i (by simp [hil])
  have hsum := List.single_le_sum (fun _ _ => Nat.zero_le _) _
    (List.mem_map.mpr ⟨i, hil, rfl⟩ : Nat.fib i ∈ l.map Nat.fib)
  have hd := decode_wdigits m
  rw [hz] at hd
  simp only [List.map_cons, List.sum_cons] at hd
  exact ⟨hgap, by omega⟩

/-- Arbitrarily high first appearances are exactly two-term canonical supports. -/
private theorem record_pairs (B : ℕ) : ∃ i j, B < j ∧ 2 ≤ i ∧ i + 2 ≤ j ∧
    Visited (Nat.fib i + Nat.fib j) := by
  classical
  let C := B + 2
  have hex : ∃ n, ∃ j ∈ support (v n), C < j := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (v_injective.nat_tendsto_atTop.eventually
        (Filter.eventually_gt_atTop (Nat.fib (C + 1))))
    have hv := hN N le_rfl
    have hj : C + 1 ≤ Nat.greatestFib (v N) := Nat.le_greatestFib.mpr (by omega)
    exact ⟨N, Nat.greatestFib (v N), peak_mem _ (v_pos N), by omega⟩
  let n := Nat.find hex
  have hn : ∃ j ∈ support (v n), C < j := Nat.find_spec hex
  have before : ∀ t, t < n → ∀ j ∈ support (v t), j ≤ C := by
    intro t ht j hj
    by_contra h
    exact Nat.find_min hex ht ⟨j, hj, by omega⟩
  have hn0 : n ≠ 0 := by
    intro he
    rcases hn with ⟨j, hj, hlarge⟩
    rw [he, v_zero, support_one] at hj
    simp only [Finset.mem_singleton] at hj
    dsimp [C] at hlarge
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  let j := Nat.greatestFib (v (k + 1))
  have hlarge : C < j := by
    rcases hn with ⟨u, hu, hU⟩
    rw [hk] at hu
    have := le_peak hu
    dsimp [j]
    omega
  have ha := (step_spec k).2.2
  obtain ⟨i, he⟩ := Finset.card_eq_one.mp ha
  have himem : i ∈ support (v k) ∩ support (v (k + 1)) := by rw [he]; simp
  obtain ⟨hiold, hinew⟩ := Finset.mem_inter.mp himem
  have hiC := before k (by omega) i hiold
  have hi2 := support_ge hiold
  obtain ⟨hgap, hupper⟩ := peak_pair (v (k + 1)) i (v_pos _) hinew (by
    change i ≠ j
    omega)
  change i + 2 ≤ j at hgap
  change Nat.fib i + Nat.fib j ≤ v (k + 1) at hupper
  have hjold : j ∉ support (v k) := by
    intro h
    have := before k (by omega) j h
    omega
  have unused : Nat.fib i + Nat.fib j ∉ terms k := by
    rw [mem_terms]
    rintro ⟨t, ht, heq⟩
    have hjmem : j ∈ support (v t) := by rw [heq, support_pair i j hi2 hgap]; simp
    have := before t (by omega) j hjmem
    omega
  have hp : 0 < Nat.fib i + Nat.fib j := by
    have := Nat.fib_pos.mpr (show 0 < i by omega)
    omega
  have hle := greedy k _ hp unused (pair_adjacent (v k) i j hiold hjold hgap)
  have hv : v (k + 1) = Nat.fib i + Nat.fib j := by omega
  exact ⟨i, j, by dsimp [C] at hlarge; omega, hi2, hgap, k + 1, hv⟩

private theorem pair_forces_two (n i j : ℕ) (hi : 4 ≤ i) (hij : i + 2 ≤ j)
    (hv : v n = Nat.fib i + Nat.fib j) : Visited (Nat.fib i + 1) := by
  by_contra omitted
  let p := Nat.fib i + 1
  have hp : 0 < p := by dsimp [p]; omega
  have hps : support p = {2, i} := by
    have h := support_pair 2 i (by omega) hi
    simpa [p, Nat.add_comm] using h
  have hcur : support (v n) = {i, j} := by rw [hv, support_pair i j (by omega) hij]
  have ha : Adjacent (v n) p := by
    unfold Adjacent
    rw [hcur, hps]
    have he : ({i, j} : Finset ℕ) ∩ {2, i} = {i} := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [he]; simp
  have hle : v (n + 1) ≤ p := greedy n p hp (omitted_not_mem omitted n) ha
  have hfi1 : 1 < Nat.fib (i + 1) := by
    have := (Nat.fib_lt_fib (m := 2) (by omega)).mpr (show 2 < i + 1 by omega)
    simpa using this
  have hfj : p < Nat.fib j := by
    have hmon := Nat.fib_mono hij
    rw [Nat.fib_add_two] at hmon
    dsimp [p]
    omega
  have hjnot : j ∉ support (v (n + 1)) := by
    intro h
    have := fib_le h
    omega
  have hi_next : i ∈ support (v (n + 1)) := by
    have hadj := (step_spec n).2.2
    unfold Adjacent at hadj
    rw [hcur] at hadj
    obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < ({i, j} ∩ support (v (n + 1))).card by omega)
    obtain ⟨hkpair, hknew⟩ := Finset.mem_inter.mp hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkpair
    rcases hkpair with rfl | rfl
    · exact hknew
    · exact False.elim (hjnot hknew)
  have hlo := fib_le hi_next
  have hne : v (n + 1) ≠ p := fun h => omitted ⟨n + 1, h⟩
  have heq : v (n + 1) = Nat.fib i := by dsimp [p] at hle hne; omega
  have hsingle : support (v (n + 1)) = {i} := by rw [heq, support_singleton i (by omega)]
  have hap : Adjacent (v (n + 1)) p := by
    unfold Adjacent
    rw [hsingle, hps]
    have he : ({i} : Finset ℕ) ∩ {2, i} = {i} := by ext k; simp; omega
    rw [he]; simp
  have hle2 : v (n + 2) ≤ p := greedy (n + 1) p hp (omitted_not_mem omitted (n + 1)) hap
  have hi_next2 : i ∈ support (v (n + 2)) := by
    have hadj := (step_spec (n + 1)).2.2
    unfold Adjacent at hadj
    rw [hsingle] at hadj
    obtain ⟨k, hk⟩ := Finset.card_pos.mp
      (show 0 < ({i} ∩ support (v (n + 2))).card by omega)
    have hk' := Finset.mem_inter.mp hk
    simpa using hk'.2
  have hlo2 := fib_le hi_next2
  have hne2 : v (n + 2) ≠ Nat.fib i := by
    intro h
    have := v_injective (h.trans heq.symm)
    omega
  have hval : v (n + 2) = p := by dsimp [p] at hle2 ⊢; omega
  exact omitted ⟨n + 2, hval⟩

private def PairVisit (i j : ℕ) : Prop :=
  2 ≤ i ∧ i + 2 ≤ j ∧ Visited (Nat.fib i + Nat.fib j)

private theorem rooted_pairs : ∃ r, 2 ≤ r ∧ ∀ B, ∃ j, B < j ∧
    r + 2 ≤ j ∧ Visited (Nat.fib r + Nat.fib j) := by
  classical
  by_contra hn
  have cutoff : ∀ i, ∃ B, ∀ j, B < j → ¬ PairVisit i j := by
    intro i
    by_cases hi : 2 ≤ i
    · have h : ¬ (∀ B, ∃ j, B < j ∧ i + 2 ≤ j ∧ Visited (Nat.fib i + Nat.fib j)) :=
        fun h => hn ⟨i, hi, h⟩
      push_neg at h
      obtain ⟨B, hB⟩ := h
      exact ⟨B, fun j hj hpair => hB j hj hpair.2.1 hpair.2.2⟩
    · exact ⟨0, fun _ _ hpair => hi hpair.1⟩
  have finite_cutoff : ∀ I, ∃ B, ∀ i, i ≤ I → ∀ j, B < j → ¬ PairVisit i j := by
    intro I
    induction I with
    | zero =>
        obtain ⟨B, hB⟩ := cutoff 0
        exact ⟨B, by intro i hi; have : i = 0 := by omega; subst i; exact hB⟩
    | succ I ih =>
        obtain ⟨B, hB⟩ := ih
        obtain ⟨C, hC⟩ := cutoff (I + 1)
        refine ⟨B + C, ?_⟩
        intro i hi j hj hp
        by_cases he : i = I + 1
        · subst i; exact hC j (by omega) hp
        · exact hB i (by omega) j (by omega) hp
  apply hn
  refine ⟨2, by omega, ?_⟩
  intro B
  obtain ⟨C, hC⟩ := finite_cutoff (B + 4)
  obtain ⟨i, j, hj, hi, hij, hv⟩ := record_pairs C
  have hiB : B + 4 < i := by
    by_contra h
    exact hC i (by omega) j hj ⟨hi, hij, hv⟩
  obtain ⟨n, hn⟩ := hv
  have hvisit := pair_forces_two n i j (by omega) hij hn
  refine ⟨i, by omega, by omega, ?_⟩
  simpa [Nat.add_comm] using hvisit

private def Hub (r : ℕ) : Prop := ∀ m, 0 < m → r ∈ support m → Visited m

private theorem root_hub (r : ℕ) (hr : 2 ≤ r)
    (hp : ∀ B, ∃ j, B < j ∧ r + 2 ≤ j ∧ Visited (Nat.fib r + Nat.fib j)) : Hub r := by
  intro m hm hrm
  apply neighbor_covers m hm
  intro B
  obtain ⟨j, hj, hrj, hv⟩ := hp (B + m + 3)
  have hjm : j ∉ support m := by intro h; have := index_bound h; omega
  have hbound := Nat.le_fib_add_one j
  refine ⟨Nat.fib r + Nat.fib j, by omega, hv, ?_⟩
  unfold Adjacent
  rw [support_pair r j hr hrj]
  have he : ({r, j} : Finset ℕ) ∩ support m = {r} := by
    ext k
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [he]; simp

private theorem hub_propagates (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hgap : r + 2 ≤ s ∨ s + 2 ≤ r) (h : Hub r) : Hub s := by
  intro m hm hsm
  by_cases hrm : r ∈ support m
  · exact h m hm hrm
  apply neighbor_covers m hm
  intro B
  let t := B + m + r + s + 5
  have hrt : r + 2 ≤ t := by dsimp [t]; omega
  have hst : s + 2 ≤ t := by dsimp [t]; omega
  have htm : t ∉ support m := by intro ht; have := index_bound ht; dsimp [t] at this; omega
  have hsup := support_triple r s t hr hs hgap hrt hst
  have hpos : 0 < Nat.fib r + Nat.fib s + Nat.fib t := by
    have := Nat.fib_pos.mpr (show 0 < r by omega)
    omega
  have hv : Visited (Nat.fib r + Nat.fib s + Nat.fib t) := h _ hpos (by rw [hsup]; simp)
  have hlarge := Nat.le_fib_add_one t
  refine ⟨Nat.fib r + Nat.fib s + Nat.fib t, ?_, hv, ?_⟩
  · dsimp [t] at hlarge ⊢; omega
  · unfold Adjacent
    rw [hsup]
    have he : ({r, s, t} : Finset ℕ) ∩ support m = {s} := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [he]; simp

private theorem every_positive (m : ℕ) (hm : 0 < m) : Visited m := by
  obtain ⟨r, hr, hp⟩ := rooted_pairs
  have hubr := root_hub r hr hp
  let s := m + r + 4
  have hs : 2 ≤ s := by dsimp [s]; omega
  have hrs : r + 2 ≤ s := by dsimp [s]; omega
  have hubs := hub_propagates r s hr hs (Or.inl hrs) hubr
  obtain ⟨k, hk⟩ := support_nonempty m hm
  have hk2 := support_ge hk
  have hkm := index_bound hk
  have hks : k + 2 ≤ s := by dsimp [s]; omega
  have hsm : s ∉ support m := by intro h; have := index_bound h; dsimp [s] at this; omega
  apply neighbor_covers m hm
  intro B
  let t := B + m + s + k + 5
  have hkt : k + 2 ≤ t := by dsimp [t]; omega
  have hst : s + 2 ≤ t := by dsimp [t]; omega
  have htm : t ∉ support m := by intro h; have := index_bound h; dsimp [t] at this; omega
  have hsup := support_triple k s t hk2 hs (Or.inl hks) hkt hst
  have hpos : 0 < Nat.fib k + Nat.fib s + Nat.fib t := by
    have := Nat.fib_pos.mpr (show 0 < k by omega)
    omega
  have hv : Visited (Nat.fib k + Nat.fib s + Nat.fib t) := hubs _ hpos (by rw [hsup]; simp)
  have hlarge := Nat.le_fib_add_one t
  refine ⟨Nat.fib k + Nat.fib s + Nat.fib t, ?_, hv, ?_⟩
  · dsimp [t] at hlarge ⊢; omega
  · unfold Adjacent
    rw [hsup]
    have he : ({k, s, t} : Finset ℕ) ∩ support m = {k} := by
      ext q
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [he]; simp

/-- The exact one-based A370630 recursion is total and permutes the positive integers. -/
theorem result : IsGreedyPermutation a := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact v_pos (n - 1)
  · intro n hn
    have hnidx : n - 1 + 1 = n := by omega
    have hstep := step_spec (n - 1)
    have hnew : v n ∉ terms (n - 1) := by simpa [hnidx] using hstep.2.1
    have hadj : Adjacent (a n) (a (n + 1)) := by
      simpa only [a, Nat.add_sub_cancel, hnidx] using hstep.2.2
    refine ⟨⟨v_pos n, ?_, hadj⟩, ?_⟩
    · intro k hk hkn he
      apply hnew
      apply (mem_terms (n - 1) (v n)).mpr
      exact ⟨k - 1, by omega, he⟩
    · intro m hm
      apply greedy (n - 1) m hm.1
      · intro hmem
        obtain ⟨i, hi, he⟩ := (mem_terms (n - 1) m).mp hmem
        exact hm.2.1 (i + 1) (by omega) (by omega) (by simpa [a] using he)
      · exact hm.2.2
  · intro i j hi hj he
    have h := v_injective he
    dsimp [a] at h
    omega
  · intro m hm
    obtain ⟨n, hn⟩ := every_positive m (by omega)
    exact ⟨n + 1, by omega, by simpa [a] using hn⟩

end D5.S3.Combinatorics.Permutation.ZeckendorfGreedyPermutation
