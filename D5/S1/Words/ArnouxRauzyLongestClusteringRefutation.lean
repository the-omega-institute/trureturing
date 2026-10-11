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
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.ArnouxRauzyLongestClusteringRefutation

private def baseBlock (x : Fin 3) : List (Fin 3) :=
  if x = 0 then [0] else if x = 1 then [1] else [2]

private def arStep (r : Fin 3) (f : Fin 3 → List (Fin 3)) (x : Fin 3) : List (Fin 3) :=
  if r = 0 then (if x = 0 then f x else f x ++ f 0)
  else if r = 1 then (if x = 1 then f x else f x ++ f 1)
  else (if x = 2 then f x else f x ++ f 2)

def arBlocks (d : ℕ → Fin 3) (k : ℕ) (x : Fin 3) : List (Fin 3) :=
  Nat.rec baseBlock (fun j f => arStep (d j) f) k x

private noncomputable def firstAt (d : ℕ → Fin 3) (x : Fin 3) (start : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, start ≤ k ∧ d k = x then Nat.find h else 0

private def runStartAux (d : ℕ → Fin 3) (z : Fin 3) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if d j = z then runStartAux d z j else j + 1

private def runStart (d : ℕ → Fin 3) (n : ℕ) : ℕ :=
  if _ : n = 0 then 0 else runStartAux d (d (n - 1)) n

def InfOften (d : ℕ → Fin 3) : Prop := ∀ x N, ∃ k ≥ N, d k = x

def Rabc (d : ℕ → Fin 3) : Prop :=
  d 0 = 0 ∧ ∃ k, d k ≠ 0 ∧ (∀ j < k, d j = 0) ∧ d k = 1

def arLang (d : ℕ → Fin 3) : Set (List (Fin 3)) :=
  {w | ∃ k x, w <:+: arBlocks d k x}

def IsStandardAR (w : List (Fin 3)) : Prop :=
  ∃ d, InfOften d ∧ ∃ k x, w = arBlocks d k x

def ConjugateToStandard (w : List (Fin 3)) : Prop :=
  ∃ r, IsStandardAR (w.rotate r)

private def lexRank (o : Equiv.Perm (Fin 3)) : List (Fin 3) → List (Fin 3) → Bool
  | [], [] => true
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if o a < o b then true
      else if o b < o a then false
      else lexRank o as bs

private def insertBool {α : Type} (r : α → α → Bool) [Inhabited α] (a : α) : List α → List α
  | [] => [a]
  | b :: l => if r a b then a :: b :: l else b :: insertBool r a l

private def sortBool {α : Type} (r : α → α → Bool) [Inhabited α] : List α → List α
  | [] => []
  | a :: l => insertBool r a (sortBool r l)

def bwt (o : Equiv.Perm (Fin 3)) (w : List (Fin 3)) : List (Fin 3) :=
  let rs := (List.range w.length).map (fun i => w.rotate i)
  let sr := sortBool (lexRank o) rs
  sr.filterMap List.getLast?

private def orderedLetters (o : Equiv.Perm (Fin 3)) : List (Fin 3) :=
  [o.symm 0, o.symm 1, o.symm 2]

private def clusteringTarget (o π : Equiv.Perm (Fin 3)) (w : List (Fin 3)) : List (Fin 3) :=
  (orderedLetters o).flatMap (fun l => List.replicate (w.count (π l)) (π l))

def IsClustering (w : List (Fin 3)) : Prop :=
  ∃ o π : Equiv.Perm (Fin 3), π ≠ 1 ∧ bwt o w = clusteringTarget o π w

private def stageBlocks (d : ℕ → Fin 3) (k : ℕ) : List (List (Fin 3)) :=
  [arBlocks d k 0, arBlocks d k 1, arBlocks d k 2]

private def sortedStageBlocks (d : ℕ → Fin 3) (k : ℕ) : List (List (Fin 3)) :=
  (stageBlocks d k).insertionSort (fun u v => u.length ≤ v.length)

noncomputable def propLongWord (d : ℕ → Fin 3) : List (Fin 3) :=
  let lam2 := firstAt d 2 0
  let mua := firstAt d 0 (lam2 + 1)
  let mub := firstAt d 1 (lam2 + 1)
  let muy := if mua < mub then mub else mua
  let mu := runStart d muy
  let sb := sortedStageBlocks d muy
  let S := sb.getD 0 []
  let M := sb.getD 1 []
  (List.replicate (muy - mu + 1) S).flatten ++ M

def claim : Prop :=
  ∀ d, Rabc d → InfOften d → ∀ w ∈ arLang d, IsClustering w →
    ConjugateToStandard w → w.length ≤ (propLongWord d).length

private def dir (k : ℕ) : Fin 3 :=
  if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 2 else
  if k = 3 then 0 else if k = 4 then 2 else if k = 5 then 1 else if k = 6 then 0
  else ⟨(k - 7) % 3, by omega⟩

private def dir2 (k : ℕ) : Fin 3 :=
  if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 2 else
  if k = 3 then 0 else if k = 4 then 0 else if k = 5 then 2 else if k = 6 then 2
  else ⟨(k - 7) % 3, by omega⟩

private def Aw : List (Fin 3) := [0,1,0,2,0,1,0]
private def Cw : List (Fin 3) := [2,0,1,0]
private def Dw : List (Fin 3) := Cw ++ Aw
private def Uw : List (Fin 3) := Aw ++ Aw ++ Dw ++ Aw ++ Dw

private def ordACB : Equiv.Perm (Fin 3) := Equiv.swap 1 2
private def piAB : Equiv.Perm (Fin 3) := Equiv.swap 0 1

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
  intro x N
  refine ⟨7 + 3 * N + x.val, ?_, ?_⟩
  · omega
  · have hx : x.val < 3 := x.isLt
    have hneq (n : ℕ) (hn : n ≤ 6) : 7 + 3 * N + x.val ≠ n := by omega
    have hsub : 7 + 3 * N + x.val - 7 = 3 * N + x.val := by omega
    have hmod : (3 * N + x.val) % 3 = x.val := by omega
    simp [dir, hneq, hsub, hmod]

private theorem dir2_inf : InfOften dir2 := by
  intro x N
  refine ⟨7 + 3 * N + x.val, ?_, ?_⟩
  · omega
  · have hx : x.val < 3 := x.isLt
    have hneq (n : ℕ) (hn : n ≤ 6) : 7 + 3 * N + x.val ≠ n := by omega
    have hsub : 7 + 3 * N + x.val - 7 = 3 * N + x.val := by omega
    have hmod : (3 * N + x.val) % 3 = x.val := by omega
    simp [dir2, hneq, hsub, hmod]

private theorem dir_rabc : Rabc dir := by
  refine ⟨by decide, ⟨1, by decide, ?_, by decide⟩⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  decide

private theorem dir_stages :
    firstAt dir 2 0 = 2 ∧ firstAt dir 0 3 = 3 ∧ firstAt dir 1 3 = 5 ∧ runStart dir 5 = 4 := by
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

private theorem sorted5_0 : (sortedStageBlocks dir 5)[0]?.getD [] = Dw := by decide

private theorem sorted5_1 : (sortedStageBlocks dir 5)[1]?.getD [] = Aw ++ Dw := by decide

private theorem prop_dir : propLongWord dir = Dw ++ Dw ++ Aw ++ Dw := by
  have hs := dir_stages
  have hlt : (3 : ℕ) < 5 := by decide
  simp [propLongWord, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hlt]
  rw [sorted5_0, sorted5_1]

private theorem prop_len : (propLongWord dir).length = 40 := by
  rw [prop_dir]
  decide

private theorem witness_mem : Uw ∈ arLang dir := by
  refine ⟨7, 2, ?_⟩
  decide

private theorem witness_cluster : IsClustering Uw := by
  refine ⟨ordACB, piAB, ?_, ?_⟩
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
