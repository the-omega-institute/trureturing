/- GID: D5/S1/Words/ArnouxRauzyLongestClusteringRefutation
   generality: I
   mirror-B: D5/B/S1/Words/ArnouxRauzyLongestClusteringRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.claim; result=D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.result; claim=D5/S1/Words/ArnouxRauzyLongestClusteringRefutation.claim
   digest: A longer perfectly clustering AR factor refutes the Ferenczi–Zamboni conjecture. -/

/-
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Public result: proof_shape: bind-only; escape_witness: none; admission_basis: open-problem-resolution (#15366; Refuted).
Direct frozen dependencies: none (all proof steps use pinned Mathlib computation and normalization).
The recurrence uses Nat.rec and Function.update; the non-strict rank order is the
negation of reverse List.lex. InfOften uses Filter.Frequently at Filter.atTop,
equivalently every letter occurs beyond every prescribed stage. The preceding
constant-run boundary is Nat.findGreatest of the last unequal-letter position
plus one. Lists of ranks and stage blocks use List.ofFn; the fixed directives
use List.getD for their seven-letter prefixes and modular periodic tails.
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.ArnouxRauzyLongestClusteringRefutation

private def arStep (r : Fin 3) (f : Fin 3 → List (Fin 3)) : Fin 3 → List (Fin 3) :=
  Function.update (fun x => f x ++ f r) r (f r)

def arBlocks (d : ℕ → Fin 3) (k : ℕ) (x : Fin 3) : List (Fin 3) :=
  Nat.rec (fun x => List.singleton x) (fun j f => arStep (d j) f) k x

private noncomputable def firstAt (d : ℕ → Fin 3) (x : Fin 3) (start : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, start ≤ k ∧ d k = x then Nat.find h else 0

def InfOften (d : ℕ → Fin 3) : Prop := ∀ x, ∃ᶠ k in Filter.atTop, d k = x

def Rabc (d : ℕ → Fin 3) : Prop :=
  d 0 = 0 ∧ ∃ k, d k ≠ 0 ∧ (∀ j < k, d j = 0) ∧ d k = 1

def arLang (d : ℕ → Fin 3) : Set (List (Fin 3)) :=
  {w | ∃ k x, w <:+: arBlocks d k x}

def IsStandardAR (w : List (Fin 3)) : Prop :=
  ∃ d, InfOften d ∧ ∃ k x, w = arBlocks d k x

def ConjugateToStandard (w : List (Fin 3)) : Prop :=
  ∃ r, IsStandardAR (w.rotate r)

def bwt (o : Equiv.Perm (Fin 3)) (w : List (Fin 3)) : List (Fin 3) :=
  let rs := (List.range w.length).map (fun i => w.rotate i)
  let sr := List.insertionSort (fun a b => (!(List.lex b a (fun x y => decide (o x < o y)))) = true) rs
  sr.filterMap List.getLast?

def IsClustering (w : List (Fin 3)) : Prop :=
  ∃ o π : Equiv.Perm (Fin 3), π ≠ 1 ∧
    bwt o w = (List.ofFn o.symm).flatMap (fun l => List.replicate (w.count (π l)) (π l))

private def sortedStageBlocks (d : ℕ → Fin 3) (k : ℕ) : List (List (Fin 3)) :=
  (List.ofFn (arBlocks d k)).insertionSort (fun u v => u.length ≤ v.length)

noncomputable def propLongWord (d : ℕ → Fin 3) : List (Fin 3) :=
  let lam2 := firstAt d 2 0
  let mua := firstAt d 0 (lam2 + 1)
  let mub := firstAt d 1 (lam2 + 1)
  let muy := if mua < mub then mub else mua
  let mu := Nat.findGreatest (fun j => d (j - 1) ≠ d (muy - 1)) muy
  let sb := sortedStageBlocks d muy
  let S := sb.getD 0 []
  let M := sb.getD 1 []
  (List.replicate (muy - mu + 1) S).flatten ++ M

def claim : Prop :=
  ∀ d, Rabc d → InfOften d → ∀ w ∈ arLang d, IsClustering w →
    ConjugateToStandard w → w.length ≤ (propLongWord d).length

private def dir (k : ℕ) : Fin 3 :=
  ([0,1,2,0,2,1,0] : List (Fin 3)).getD k (Fin.ofNat 3 (k - 7))

private def dir2 (k : ℕ) : Fin 3 :=
  ([0,1,2,0,0,2,2] : List (Fin 3)).getD k (Fin.ofNat 3 (k - 7))

private def Uw : List (Fin 3) :=
  arBlocks dir 3 0 ++ arBlocks dir 3 0 ++ arBlocks dir 4 2 ++
    arBlocks dir 3 0 ++ arBlocks dir 4 2

private theorem firstAt_eq (d : ℕ → Fin 3) (x : Fin 3) (start n : ℕ)
    (hn : start ≤ n ∧ d n = x)
    (hmin : ∀ j < n, ¬ (start ≤ j ∧ d j = x)) :
    firstAt d x start = n := by
  classical
  unfold firstAt
  split
  · next h => exact (Nat.find_eq_iff h).2 ⟨hn, hmin⟩
  · next h => exact False.elim (h ⟨n, hn⟩)

private theorem dir_inf : InfOften dir := by
  intro x
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨7 + 3 * N + x.val, ?_, ?_⟩
  · omega
  · have hx : x.val < 3 := x.isLt
    have hsub : 7 + 3 * N + x.val - 7 = 3 * N + x.val := by omega
    have hmod : (3 * N + x.val) % 3 = x.val := by omega
    simp only [dir]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    simp [Fin.ofNat, hsub, hmod]

private theorem dir2_inf : InfOften dir2 := by
  intro x
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨7 + 3 * N + x.val, ?_, ?_⟩
  · omega
  · have hx : x.val < 3 := x.isLt
    have hsub : 7 + 3 * N + x.val - 7 = 3 * N + x.val := by omega
    have hmod : (3 * N + x.val) % 3 = x.val := by omega
    simp only [dir2]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    simp [Fin.ofNat, hsub, hmod]

private theorem dir_rabc : Rabc dir := by
  refine ⟨by decide, ⟨1, by decide, ?_, by decide⟩⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  decide

private theorem dir_stages :
    firstAt dir 2 0 = 2 ∧ firstAt dir 0 3 = 3 ∧ firstAt dir 1 3 = 5 ∧ Nat.findGreatest (fun j => dir (j - 1) ≠ dir (5 - 1)) 5 = 4 := by
  have h2 : firstAt dir 2 0 = 2 := firstAt_eq dir 2 0 2 ⟨by omega, by decide⟩ (by
    intro j hj
    interval_cases j <;> decide)
  have h3 : firstAt dir 0 3 = 3 := firstAt_eq dir 0 3 3 ⟨by omega, by decide⟩ (by
    intro j hj
    interval_cases j <;> decide)
  have h5 : firstAt dir 1 3 = 5 := firstAt_eq dir 1 3 5 ⟨by omega, by decide⟩ (by
    intro j hj
    interval_cases j <;> decide)
  exact ⟨h2, h3, h5, by decide⟩

private theorem sorted5_0 : (sortedStageBlocks dir 5)[0]?.getD [] = (arBlocks dir 4 2) := by decide

private theorem sorted5_1 :
    (sortedStageBlocks dir 5)[1]?.getD [] = arBlocks dir 3 0 ++ arBlocks dir 4 2 := by decide

private theorem prop_dir :
    propLongWord dir = arBlocks dir 4 2 ++ arBlocks dir 4 2 ++ arBlocks dir 3 0 ++
      arBlocks dir 4 2 := by
  have hs := dir_stages
  have hlt : (3 : ℕ) < 5 := by decide
  simp only [propLongWord, hs.1, hs.2.1, hs.2.2.1, if_pos hlt, hs.2.2.2]
  change ((sortedStageBlocks dir 5)[0]?.getD [] ++
      ((sortedStageBlocks dir 5)[0]?.getD [] ++ [])) ++
    (sortedStageBlocks dir 5)[1]?.getD [] = _
  rw [sorted5_0, sorted5_1]
  simp only [List.append_nil, List.append_assoc]

private theorem prop_len : (propLongWord dir).length = 40 := by
  rw [prop_dir]
  decide

private theorem witness_mem : Uw ∈ arLang dir := by
  refine ⟨7, 2, ?_⟩
  decide

private theorem witness_cluster : IsClustering Uw := by
  refine ⟨Equiv.swap 1 2, Equiv.swap 0 1, ?_, ?_⟩
  · decide
  · decide

private theorem witness_standard_rotation : Uw.rotate 7 = arBlocks dir2 7 0 := by decide

private theorem witness_conjugate : ConjugateToStandard Uw := by
  refine ⟨7, dir2, dir2_inf, 7, 0, witness_standard_rotation⟩

theorem result : ¬ claim := by
  intro h
  have hh := h dir dir_rabc dir_inf Uw witness_mem witness_cluster witness_conjugate
  rw [prop_len] at hh
  have hu : Uw.length = 43 := by decide
  omega

end D5.S1.Words.ArnouxRauzyLongestClusteringRefutation
