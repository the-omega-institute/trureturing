/- GID: D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.claim; result=D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.result; claim=D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.claim
   digest: Binary words at distance one force arbitrarily many greedy swaps. -/

/-
admission_basis: open-problem-resolution (#19317; Refuted)
escape_witness: none
Direct frozen dependencies: none (only pinned Mathlib imports).
proof_shape: twoSwap: bind-only (definition); consumer(s): IsTwoSwapOf, vF_twoSwap
proof_shape: parikh: bind-only (definition); consumer(s): configGraph, AdmissibleOrder, claim, parikh_eq_length_occurrences
proof_shape: IsTwoSwapOf: bind-only (definition); consumer(s): swapGraph, family_isTwoSwap
proof_shape: swapGraph: bind-only (definition); consumer(s): configGraph, family_distance
proof_shape: configGraph: bind-only (definition); consumer(s): claim, family_distance, family_theorem
proof_shape: occurrences: bind-only (definition); consumer(s): stageSwaps, occurrences_eq_map, parikh_eq_length_occurrences
proof_shape: stageSwaps: bind-only (definition); consumer(s): greedySwaps, greedyLength_zero, greedyLength_one
proof_shape: applySwaps: bind-only (definition); consumer(s): greedySwaps
proof_shape: greedySwaps: bind-only (definition); consumer(s): greedyLength
proof_shape: greedyLength: bind-only (definition); consumer(s): claim, greedyLength_zero, greedyLength_one
proof_shape: AdmissibleOrder: bind-only (definition); consumer(s): claim, binary_admissible_order, family_all_runs, family_theorem
proof_shape: claim: bind-only (definition); consumer(s): result
proof_shape: wF: bind-only (definition); consumer(s): occurrences_wF_zero, occurrences_wF_one, vF_twoSwap, family_ne
proof_shape: vF: bind-only (definition); consumer(s): occurrences_vF_zero, occurrences_vF_one, vF_twoSwap, family_ne
proof_shape: idxV0: bind-only (definition); consumer(s): occurrences_vF_zero, greedyLength_zero
proof_shape: idxV1: bind-only (definition); consumer(s): occurrences_vF_one, greedyLength_one
proof_shape: occurrences_eq_map: bind-only; consumer(s): occurrences_wF_zero, occurrences_wF_one, occurrences_vF_zero, occurrences_vF_one
proof_shape: occurrences_wF_zero: bind-only; consumer(s): parikh_wF, greedyLength_zero
proof_shape: occurrences_wF_one: bind-only; consumer(s): parikh_wF, greedyLength_one
proof_shape: occurrences_vF_zero: bind-only; consumer(s): parikh_vF, greedyLength_zero
proof_shape: occurrences_vF_one: bind-only; consumer(s): parikh_vF, greedyLength_one
proof_shape: parikh_eq_length_occurrences: bind-only; consumer(s): parikh_wF, parikh_vF
proof_shape: parikh_wF: bind-only; consumer(s): parikh_family
proof_shape: parikh_vF: bind-only; consumer(s): parikh_family
proof_shape: parikh_family: bind-only; consumer(s): family_distance, family_theorem, result
proof_shape: vF_twoSwap: bind-only; consumer(s): family_isTwoSwap
proof_shape: family_isTwoSwap: bind-only; consumer(s): family_distance
proof_shape: family_ne: bind-only; consumer(s): family_distance
proof_shape: family_distance: bind-only; consumer(s): family_theorem
proof_shape: nontrivial_zip_length: bind-only; consumer(s): greedyLength_zero, greedyLength_one
proof_shape: greedyLength_zero: bind-only; consumer(s): family_all_runs
proof_shape: greedyLength_one: bind-only; consumer(s): family_all_runs
proof_shape: binary_admissible_order: bind-only; consumer(s): family_all_runs
proof_shape: family_all_runs: bind-only; consumer(s): family_theorem
proof_shape: family_theorem: bind-only; consumer(s): result
proof_shape: result: bind-only; consumer(s): none
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Escape-audit reference: https://github.com/the-omega-institute/trureturing/issues/19440
The module proves a structural theorem for an unbounded family and refutes claim at k=2.
The source uses one-based positions and symbols; Fin uses zero-based labels.
The claim asks only for equality of the swap count and graph distance, and allows
any maximal-count reference symbol and any non-increasing order of the others.
The counts include every pair with unequal indices, without requiring a legal path.
The initial and terminal occurrence inclusions use Fin.castAdd and Fin.natAdd directly.
-/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.FinCases

namespace D5.S3.Combinatorics.Permutation.AdamsonFlahertyPotapovSpirakisTwoSwapGreedy

variable {A : Type*} [DecidableEq A] {n : ℕ}

/-- Definition 1: for `i < j` with `w[i] ≠ w[j]`, the 2-swap `w ∘ (i,j)` is
`w[1,i-1] w[j] w[i+1,j-1] w[i] w[j+1,n]`, that is, `w` precomposed with the transposition of `i` and `j`. -/
def twoSwap (w : Fin n → A) (i j : Fin n) : Fin n → A :=
  w ∘ Equiv.swap i j

/-- The Parikh vector: `P(w)[a] = |{j ∈ [n] | w[j] = a}|`. -/
def parikh (w : Fin n → A) (a : A) : ℕ :=
  (Finset.univ.filter fun j => w j = a).card

/-- `v` is a 2-swap of `w`. -/
def IsTwoSwapOf (w v : Fin n → A) : Prop :=
  ∃ i j : Fin n, i < j ∧ w i ≠ w j ∧ v = twoSwap w i j

/-- The 2-swap relation on all words of length `n`, as a simple graph. -/
def swapGraph (n : ℕ) (A : Type*) [DecidableEq A] : SimpleGraph (Fin n → A) :=
  SimpleGraph.fromRel IsTwoSwapOf

/-- The configuration graph `G(P)`: one vertex for each word with Parikh vector `P`, and an edge for each 2-swap. -/
def configGraph (P : A → ℕ) : SimpleGraph {w : Fin n → A // parikh w = P} :=
  (swapGraph n A).induce {w | parikh w = P}

/-- The positions of the occurrences of `x` in `w`, in increasing order; its `k`-th entry is the index of the
`k`-th occurrence. -/
def occurrences (w : Fin n → A) (x : A) : List (Fin n) :=
  (List.finRange n).filter fun i => w i = x

/-- Lines 3–6 of Algorithm 1 for the symbol `x`: the pairs `(i, j)` with `i` the index of the `k`-th occurrence of
`x` in the current word and `j` the index of the `k`-th occurrence of `x` in `v`. -/
def stageSwaps (u v : Fin n → A) (x : A) : List (Fin n × Fin n) :=
  (occurrences u x).zip (occurrences v x)

/-- Line 8 of Algorithm 1: apply the swaps of the stage to the current word, in the order of `k`. -/
def applySwaps (u : Fin n → A) (S : List (Fin n × Fin n)) : Fin n → A :=
  S.foldl (fun c p => c ∘ Equiv.swap p.1 p.2) u

/-- Algorithm 1, run on the symbols of `o` in turn: every swap it generates, in order. -/
def greedySwaps (v : Fin n → A) : List A → (Fin n → A) → List (Fin n × Fin n)
  | [], _ => []
  | x :: t, u => stageSwaps u v x ++ greedySwaps v t (applySwaps u (stageSwaps u v x))

/-- The number of nontrivial swaps (`i ≠ j`) of Algorithm 1 on `o`, from `w` towards `v`. -/
def greedyLength (o : List A) (w v : Fin n → A) : ℕ :=
  ((greedySwaps v o w).filter fun p => p.1 ≠ p.2).length

/-- An admissible symbol order for Algorithm 1 on `w`: after the relabelling `P[1] ≥ P[2] ≥ ⋯ ≥ P[s]`, the loop
runs over `x ∈ Σ ∖ {1}` in label order, so `o` lists every symbol except one reference symbol `1` of maximal
count, each once, in non-increasing count. -/
def AdmissibleOrder [Fintype A] (w : Fin n → A) (o : List A) : Prop :=
  ∃ r : A, (∀ a, parikh w a ≤ parikh w r) ∧ o.Nodup ∧ r ∉ o ∧ (∀ a, a ≠ r → a ∈ o) ∧
    o.Pairwise fun a b => parikh w b ≤ parikh w a

/-- The closing conjecture: "the simple greedy algorithm used to derive the upper bound in Lemma 4 can be used to
find the shortest path between any pair of vertices" of `G(P)`, for every alphabet `[s]` and length `n`. -/
def claim : Prop :=
  ∀ (s n : ℕ) (w v : Fin n → Fin s) (h : parikh v = parikh w),
    ∃ o : List (Fin s), AdmissibleOrder w o ∧
      greedyLength o w v = (configGraph (parikh w)).dist ⟨w, rfl⟩ ⟨v, h⟩


set_option maxHeartbeats 800000
set_option maxRecDepth 2048

private def wF (k : ℕ) (i : Fin (2 * k)) : Fin 2 := if i.val < k then 0 else 1

private def vF (k : ℕ) (i : Fin (2 * k)) : Fin 2 :=
  if i.val = 0 then 1 else if i.val < k then 0 else if i.val + 1 = 2 * k then 0 else 1

private def idxV0 (k : ℕ) (hk : 2 ≤ k) (i : Fin k) : Fin (2 * k) :=
  ⟨if i.val + 1 < k then i.val + 1 else 2 * k - 1, by split <;> omega⟩
private def idxV1 (k : ℕ) (hk : 2 ≤ k) (i : Fin k) : Fin (2 * k) :=
  ⟨if i.val = 0 then 0 else k + i.val - 1, by split <;> omega⟩

private theorem occurrences_eq_map {m n : ℕ} (w : Fin n → Fin 2) (x : Fin 2)
    (f : Fin m → Fin n) (hf : StrictMono f)
    (hi : ∀ j, w j = x ↔ ∃ i, f i = j) :
    occurrences w x = (List.finRange m).map f := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
  · simpa only [List.ofFn_eq_map] using hf.sortedLT_ofFn
  · intro j
    simpa only [occurrences, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, List.mem_map] using hi j

private theorem occurrences_wF_zero (k : ℕ) :
    occurrences (wF k) 0 = (List.finRange k).map (fun i => Fin.cast (by omega) (Fin.castAdd k i)) := by
  apply occurrences_eq_map
  · intro a b hab
    exact hab
  · intro j
    constructor
    · intro h
      have hlt : j.val < k := by
        by_contra hn
        simp [wF, hn] at h
      exact ⟨⟨j.val, hlt⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      simp [wF, i.isLt]

private theorem occurrences_wF_one (k : ℕ) :
    occurrences (wF k) 1 = (List.finRange k).map (fun i => Fin.cast (by omega) (Fin.natAdd k i)) := by
  apply occurrences_eq_map
  · intro a b hab
    change k + a.val < k + b.val
    exact Nat.add_lt_add_left hab k
  · intro j
    constructor
    · intro h
      have hge : k ≤ j.val := by
        by_contra hn
        simp [wF, show j.val < k by omega] at h
      refine ⟨⟨j.val - k, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp
      omega
    · rintro ⟨i, rfl⟩
      simp [wF]

private theorem occurrences_vF_zero (k : ℕ) (hk : 2 ≤ k) :
    occurrences (vF k) 0 = (List.finRange k).map (idxV0 k hk) := by
  apply occurrences_eq_map
  · intro a b hab
    change (if a.val + 1 < k then a.val + 1 else 2 * k - 1) <
      (if b.val + 1 < k then b.val + 1 else 2 * k - 1)
    split_ifs <;> have := a.isLt <;> have := b.isLt <;> omega
  · intro j
    constructor
    · intro h
      by_cases hj : j.val + 1 = 2 * k
      · refine ⟨⟨k - 1, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp [idxV0]
        split_ifs <;> omega
      · have hpos : 0 < j.val ∧ j.val < k := by
          unfold vF at h
          split_ifs at h <;> simp_all; omega
        refine ⟨⟨j.val - 1, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp [idxV0]
        split_ifs <;> omega
    · rintro ⟨i, rfl⟩
      unfold vF idxV0
      dsimp
      split_ifs <;> have := i.isLt <;> simp_all <;> omega

private theorem occurrences_vF_one (k : ℕ) (hk : 2 ≤ k) :
    occurrences (vF k) 1 = (List.finRange k).map (idxV1 k hk) := by
  apply occurrences_eq_map
  · intro a b hab
    change (if a.val = 0 then 0 else k + a.val - 1) <
      (if b.val = 0 then 0 else k + b.val - 1)
    split_ifs <;> have := a.isLt <;> have := b.isLt <;> omega
  · intro j
    constructor
    · intro h
      by_cases hj : j.val = 0
      · refine ⟨⟨0, by omega⟩, ?_⟩
        apply Fin.ext
        simpa [idxV1] using hj.symm
      · have hpos : k ≤ j.val ∧ j.val + 1 < 2 * k := by
          unfold vF at h
          split_ifs at h <;> simp_all; omega
        refine ⟨⟨j.val - k + 1, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp [idxV1]
        omega
    · rintro ⟨i, rfl⟩
      unfold vF idxV1
      dsimp
      split_ifs <;> have := i.isLt <;> simp_all <;> omega


private theorem parikh_eq_length_occurrences {n : ℕ} (w : Fin n → Fin 2) (x : Fin 2) :
    parikh w x = (occurrences w x).length := by
  exact Eq.symm (Nat.add_zero (occurrences w x).length)

private theorem parikh_wF (k : ℕ) (a : Fin 2) : parikh (wF k) a = k := by
  fin_cases a
  · change parikh (wF k) 0 = k
    rw [parikh_eq_length_occurrences, occurrences_wF_zero]
    simp
  · change parikh (wF k) 1 = k
    rw [parikh_eq_length_occurrences, occurrences_wF_one]
    simp

private theorem parikh_vF (k : ℕ) (hk : 2 ≤ k) (a : Fin 2) : parikh (vF k) a = k := by
  fin_cases a
  · change parikh (vF k) 0 = k
    rw [parikh_eq_length_occurrences, occurrences_vF_zero k hk]
    simp
  · change parikh (vF k) 1 = k
    rw [parikh_eq_length_occurrences, occurrences_vF_one k hk]
    simp

private theorem parikh_family (k : ℕ) (hk : 2 ≤ k) : parikh (vF k) = parikh (wF k) := by
  funext a
  rw [parikh_wF, parikh_vF k hk]

private theorem vF_twoSwap (k : ℕ) (hk : 2 ≤ k) :
    vF k = twoSwap (wF k) ⟨0, by omega⟩ ⟨2 * k - 1, by omega⟩ := by
  funext i
  simp only [twoSwap, Function.comp_apply, Equiv.swap_apply_def]
  split_ifs with h0 hl
  · subst i
    simp [vF, wF, show ¬ 2 * k - 1 < k by omega]
  · subst i
    simp [vF, wF, show 2 * k - 1 ≠ 0 by omega, show ¬ 2 * k - 1 < k by omega,
      show 2 * k - 1 + 1 = 2 * k by omega, show 0 < k by omega]
  · have h0' : i.val ≠ 0 := Fin.val_ne_iff.mpr h0
    have hl' : i.val + 1 ≠ 2 * k := by
      intro he
      apply hl
      apply Fin.ext
      dsimp
      omega
    simp [vF, wF, h0', hl']

private theorem family_isTwoSwap (k : ℕ) (hk : 2 ≤ k) : IsTwoSwapOf (wF k) (vF k) := by
  refine ⟨⟨0, by omega⟩, ⟨2 * k - 1, by omega⟩, ?_, ?_, vF_twoSwap k hk⟩
  · change 0 < 2 * k - 1
    omega
  · simp [wF, show 0 < k by omega, show ¬ 2 * k - 1 < k by omega]

private theorem family_ne (k : ℕ) (hk : 2 ≤ k) : wF k ≠ vF k := by
  intro he
  have hz := congrFun he ⟨0, by omega⟩
  simp [wF, vF, show 0 < k by omega] at hz

private theorem family_distance (k : ℕ) (hk : 2 ≤ k) :
    (configGraph (parikh (wF k))).dist ⟨wF k, rfl⟩ ⟨vF k, parikh_family k hk⟩ = 1 := by
  apply SimpleGraph.dist_eq_one_iff_adj.mpr
  change (swapGraph (2 * k) (Fin 2)).Adj (wF k) (vF k)
  rw [swapGraph, SimpleGraph.fromRel_adj]
  exact ⟨family_ne k hk, Or.inl (family_isTwoSwap k hk)⟩

private theorem nontrivial_zip_length {m n : ℕ} (f g : Fin m → Fin n)
    (hne : ∀ i, f i ≠ g i) :
    ((((List.finRange m).map f).zip ((List.finRange m).map g)).filter
      (fun p => decide (p.1 ≠ p.2))).length = m := by
  rw [List.zip_map']
  have hf : ((List.finRange m).map (fun i => (f i, g i))).filter
      (fun p => decide (p.1 ≠ p.2)) = (List.finRange m).map (fun i => (f i, g i)) := by
    apply List.filter_eq_self.mpr
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    simpa using hne i
  rw [hf]
  simp

private theorem greedyLength_zero (k : ℕ) (hk : 2 ≤ k) :
    greedyLength [(0 : Fin 2)] (wF k) (vF k) = k := by
  simp only [greedyLength, greedySwaps, List.append_nil, stageSwaps]
  rw [occurrences_wF_zero, occurrences_vF_zero k hk]
  apply nontrivial_zip_length
  intro i he
  have hv := congrArg Fin.val he
  dsimp [idxV0] at hv
  split_ifs at hv <;> have := i.isLt <;> omega

private theorem greedyLength_one (k : ℕ) (hk : 2 ≤ k) :
    greedyLength [(1 : Fin 2)] (wF k) (vF k) = k := by
  simp only [greedyLength, greedySwaps, List.append_nil, stageSwaps]
  rw [occurrences_wF_one, occurrences_vF_one k hk]
  apply nontrivial_zip_length
  intro i he
  have hv := congrArg Fin.val he
  dsimp [idxV1] at hv
  split_ifs at hv <;> have := i.isLt <;> omega

private theorem binary_admissible_order {n : ℕ} (w : Fin n → Fin 2) (o : List (Fin 2))
    (ho : AdmissibleOrder w o) : o = [0] ∨ o = [1] := by
  obtain ⟨r, _, hnd, href, hall, _⟩ := ho
  fin_cases r
  · right
    apply List.Perm.eq_singleton
    apply (List.perm_ext_iff_of_nodup hnd (by simp)).mpr
    intro a
    fin_cases a <;> simp_all
  · left
    apply List.Perm.eq_singleton
    apply (List.perm_ext_iff_of_nodup hnd (by simp)).mpr
    intro a
    fin_cases a <;> simp_all

private theorem family_all_runs (k : ℕ) (hk : 2 ≤ k) (o : List (Fin 2))
    (ho : AdmissibleOrder (wF k) o) :
    greedyLength o (wF k) (vF k) = k := by
  rcases binary_admissible_order (wF k) o ho with rfl | rfl
  · exact greedyLength_zero k hk
  · exact greedyLength_one k hk

private theorem family_theorem (k : ℕ) (hk : 2 ≤ k) :
    (configGraph (parikh (wF k))).dist ⟨wF k, rfl⟩ ⟨vF k, parikh_family k hk⟩ = 1 ∧
    ∀ o, AdmissibleOrder (wF k) o → greedyLength o (wF k) (vF k) = k := by
  exact ⟨family_distance k hk, family_all_runs k hk⟩

theorem result : ¬ claim := by
  intro hc
  obtain ⟨o, ho, he⟩ := hc 2 4 (wF 2) (vF 2) (parikh_family 2 (by decide))
  obtain ⟨hd, hg⟩ := family_theorem 2 (by decide)
  have hlen := hg o ho
  rw [hd, hlen] at he
  contradiction



end D5.S3.Combinatorics.Permutation.AdamsonFlahertyPotapovSpirakisTwoSwapGreedy
