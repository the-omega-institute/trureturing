/- GID: D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation
   generality: I
   mirror-B: D5/B/S1/Words/SymmetricOrderPalindromicComplexityRefutation
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.claim; result=D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.result; claim=D5/S1/Words/SymmetricOrderPalindromicComplexityRefutation.claim
   digest: A four-letter path language refutes the symmetric-order palindrome conjecture. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#15331; Refuted)
  Direct frozen dependencies: none
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The alphabet Fin 4 encodes source vertices 1, 2, 3, 4 as 0, 1, 2, 3.
The departure order is numerical and the arrival order is its reverse.
Only the four-letter instance at length three is asserted here.
Private proof classification (same-delivery helpers inlined):
  edge_all_from_two: proof_shape: bind-only; consumer: chain_left_extend
  edge_succ: proof_shape: bind-only; consumer: chain_right_extend
  chain_left_extend: proof_shape: bind-only; consumer: extendable
  chain_right_extend: proof_shape: bind-only; consumer: extendable
  factorial: proof_shape: bind-only; consumer: result
  extendable: proof_shape: bind-only; consumer: result
  usesAll: proof_shape: bind-only; consumer: result
  alt_last: proof_shape: bind-only; consumer: symOrder
  multi_incoming: proof_shape: bind-only; consumer: left_multi_first, symOrder
  left_multi_first: proof_shape: bind-only; consumer: only_empty_bispecial
  two_right_decomp: proof_shape: bind-only; consumer: only_empty_bispecial
  path_alt_noTwo: proof_shape: bind-only; consumer: only_empty_bispecial
  only_empty_bispecial: proof_shape: bind-only; consumer: noConnection
  symOrder: proof_shape: bind-only; consumer: result
  adjacent_refl_cases: proof_shape: bind-only; consumer: noConnection
  noConnection: proof_shape: bind-only; consumer: result
  pal_set: proof_shape: bind-only; consumer: pal3
  pal3: proof_shape: bind-only; consumer: result
Each private declaration has escape_witness: none and Direct frozen dependencies: none.
-/

import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.SymmetricOrderPalindromicComplexityRefutation

private def edge (a b : Fin 4) : Prop :=
  (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 3) ∨ (a = 2) ∨ (a = 3 ∧ b = 0)

private def L : Set (List (Fin 4)) := {w | List.IsChain edge w}

private theorem edge_all_from_two (b : Fin 4) : edge 2 b := by
  simp [edge]

private def succV (a : Fin 4) : Fin 4 := if a = 0 ∨ a = 1 then 3 else 0

private theorem edge_succ (a : Fin 4) : edge a (succV a) := by
  fin_cases a <;> simp [succV, edge]

private theorem chain_left_extend :
    ∀ w : List (Fin 4), List.IsChain edge w → ∃ a, List.IsChain edge (a :: w) := by
  intro w hw
  refine ⟨2, ?_⟩
  cases w with
  | nil => simp
  | cons b t =>
    exact List.IsChain.cons_cons (edge_all_from_two b) hw

private theorem chain_right_extend :
    ∀ w : List (Fin 4), List.IsChain edge w → ∃ b, List.IsChain edge (w ++ [b]) := by
  intro w hw
  rcases List.eq_nil_or_concat' w with rfl | ⟨u, a, rfl⟩
  · exact ⟨0, by simp⟩
  · refine ⟨succV a, hw.append (.singleton _) ?_⟩
    intro x hx y hy
    have hxa : a = x := by simpa using hx
    have hyb : succV a = y := by simpa using hy
    subst x y
    exact edge_succ a

def IsFactorial {k : ℕ} (K : Set (List (Fin k))) : Prop :=
  ∀ w ∈ K, ∀ u, List.IsInfix u w → u ∈ K

def IsExtendable {k : ℕ} (K : Set (List (Fin k))) : Prop :=
  ∀ w ∈ K, (∃ a, a :: w ∈ K) ∧ (∃ b, w ++ [b] ∈ K)

def UsesAllLetters {k : ℕ} (K : Set (List (Fin k))) : Prop := ∀ a, [a] ∈ K

def SymOrderCondition {k : ℕ} (K : Set (List (Fin k))) (sigma : Equiv.Perm (Fin k)) : Prop :=
  ∀ a b c d x, a :: (x ++ [b]) ∈ K → c :: (x ++ [d]) ∈ K → a ≠ c → b ≠ d →
    (sigma c < sigma a ↔ sigma b < sigma d)

def IsBispecial {k : ℕ} (K : Set (List (Fin k))) (w : List (Fin k)) : Prop :=
  (∃ a1 a2, a1 ≠ a2 ∧ a1 :: w ∈ K ∧ a2 :: w ∈ K) ∧
  (∃ b1 b2, b1 ≠ b2 ∧ w ++ [b1] ∈ K ∧ w ++ [b2] ∈ K)

def NoConnection {k : ℕ} (K : Set (List (Fin k))) (sigma : Equiv.Perm (Fin k)) : Prop :=
  ∀ w, IsBispecial K w → ∀ a ap b bp,
    (sigma ap < sigma a ∧ ∀ z, ¬ (sigma ap < sigma z ∧ sigma z < sigma a)) →
    (sigma b < sigma bp ∧ ∀ z, ¬ (sigma b < sigma z ∧ sigma z < sigma bp)) →
    a :: (w ++ [b]) ∈ K → ap :: (w ++ [bp]) ∈ K →
    a :: (w ++ [bp]) ∉ K → ap :: (w ++ [b]) ∉ K → False

noncomputable def palComplexity {k : ℕ} (K : Set (List (Fin k))) (n : ℕ) : ℕ :=
  Set.ncard {w | w ∈ K ∧ w.length = n ∧ w.reverse = w}

def claim : Prop := ∀ (k : ℕ) (K : Set (List (Fin k))) (sigma : Equiv.Perm (Fin k)),
  IsFactorial K → IsExtendable K → UsesAllLetters K →
  SymOrderCondition K sigma → NoConnection K sigma →
  ∀ n, palComplexity K n = if Even n then 1 else k

private theorem factorial : IsFactorial L := by
  intro w hw u hu
  exact List.IsChain.infix hw hu

private theorem extendable : IsExtendable L := by
  intro w hw
  exact ⟨chain_left_extend w hw, chain_right_extend w hw⟩

private theorem usesAll : UsesAllLetters L := by
  intro a; simp [L]

private theorem alt_last {y : Fin 4} (hy : y = 0 ∨ y = 3) :
    ∀ ys b d, List.IsChain edge (y :: ys ++ [b]) →
    List.IsChain edge (y :: ys ++ [d]) → b = d := by
  intro ys b d h1 h2
  have det : ∀ z, List.IsChain edge (y :: ys ++ [z]) →
      List.IsChain (fun a b => succV a = b) (y :: ys ++ [z]) := by
    intro z hz
    have carry : ∀ {a c : Fin 4}, edge a c → (a = 0 ∨ a = 3) → (c = 0 ∨ c = 3) := by
      intro a c hac ha
      rcases ha with rfl | rfl <;> fin_cases c <;> simp_all [edge]
    have cycle : ∀ v ∈ y :: ys ++ [z], v = 0 ∨ v = 3 :=
      hz.induction (fun v => v = 0 ∨ v = 3) _ @carry (fun _ => hy)
    apply hz.imp_of_mem_imp
    intro a c ha hc hac
    have ha0 := cycle a ha
    rcases ha0 with rfl | rfl <;> fin_cases c <;> simp_all [edge, succV]
  have hb := (det b h1).iterate_eq_of_apply_eq (ys.length + 1) (by simp)
  have hd := (det d h2).iterate_eq_of_apply_eq (ys.length + 1) (by simp)
  simpa using hb.symm.trans hd

private theorem multi_incoming {a c y : Fin 4} (hay : edge a y) (hcy : edge c y)
    (hac : a ≠ c) : y = 0 ∨ y = 3 := by
  fin_cases a <;> fin_cases c <;> fin_cases y <;> simp_all [edge]

private theorem left_multi_first {w : List (Fin 4)} {a c : Fin 4}
    (h1 : List.IsChain edge (a :: w)) (h2 : List.IsChain edge (c :: w))
    (hac : a ≠ c) (hw : w ≠ []) : ∃ y t, w = y :: t ∧ (y = 0 ∨ y = 3) := by
  cases w with
  | nil => contradiction
  | cons y t =>
      refine ⟨y, t, rfl, ?_⟩
      have hay : edge a y := (List.isChain_cons_cons.mp h1).1
      have hcy : edge c y := (List.isChain_cons_cons.mp h2).1
      exact multi_incoming hay hcy hac

private theorem two_right_decomp : ∀ (w : List (Fin 4)) (b d : Fin 4), w ≠ [] →
    List.IsChain edge (w ++ [b]) → List.IsChain edge (w ++ [d]) → b ≠ d → ∃ u, w = u ++ [2] := by
  intro w b d hn h1 h2 hbd
  rcases List.eq_nil_or_concat' w with hnil | ⟨u, a, rfl⟩
  · exact False.elim (hn hnil)
  · have e1 : edge a b := by
      simpa using h1.rel_getLast_head_of_append (by simp) (by simp)
    have e2 : edge a d := by
      simpa using h2.rel_getLast_head_of_append (by simp) (by simp)
    have ha : a = 2 := by
      fin_cases a <;> fin_cases b <;> fin_cases d <;> simp_all [edge]
    exact ⟨u, by simp [ha]⟩

private theorem path_alt_noTwo : ∀ (y : Fin 4) (ys : List (Fin 4)), y = 0 ∨ y = 3 →
    List.IsChain edge (y :: ys) → ∀ v, v ∈ y :: ys → v ≠ 2 := by
  intro y ys hy h v hv
  have carry : ∀ {x z : Fin 4}, edge x z → (x = 0 ∨ x = 3) → (z = 0 ∨ z = 3) := by
    intro x z hx hx0
    rcases hx0 with rfl | rfl <;> fin_cases z <;> simp_all [edge]
  have ha : v = 0 ∨ v = 3 := h.induction (fun z => z = 0 ∨ z = 3) (y :: ys)
    @carry (fun _ => hy) v hv
  rcases ha with rfl | rfl <;> decide

private theorem only_empty_bispecial : ∀ {w : List (Fin 4)}, IsBispecial L w → w = [] := by
  intro w hbis
  by_contra hne
  rcases hbis.1 with ⟨a, c, hac, h1, h2⟩
  rcases hbis.2 with ⟨b, d, hbd, hb1, hb2⟩
  obtain ⟨y, t, hwt, hy⟩ := left_multi_first h1 h2 hac hne
  obtain ⟨u, hu⟩ := two_right_decomp w b d hne hb1 hb2 hbd
  have hmem : (2 : Fin 4) ∈ w := by rw [hu]; simp
  have hwpath : List.IsChain edge w := List.IsChain.left_of_append hb1
  rw [hwt] at hwpath hmem
  exact path_alt_noTwo y t hy hwpath 2 hmem rfl

private theorem symOrder : SymOrderCondition L (Equiv.refl (Fin 4)) := by
  intro a b c d x hab hcd hac hbd
  change List.IsChain edge (a :: (x ++ [b])) at hab
  change List.IsChain edge (c :: (x ++ [d])) at hcd
  cases x with
  | nil =>
      change List.IsChain edge [a,b] at hab
      change List.IsChain edge [c,d] at hcd
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [edge] at hab hcd hac hbd ⊢
  | cons y ys =>
      change List.IsChain edge (a :: y :: (ys ++ [b])) at hab
      change List.IsChain edge (c :: y :: (ys ++ [d])) at hcd
      have hay : edge a y := (List.isChain_cons_cons.mp hab).1
      have hcy : edge c y := (List.isChain_cons_cons.mp hcd).1
      have hy : y = 0 ∨ y = 3 := multi_incoming hay hcy hac
      have hbd' : b = d := alt_last hy ys b d
        ((List.isChain_cons_cons.mp hab).2) ((List.isChain_cons_cons.mp hcd).2)
      exact False.elim (hbd hbd')


private theorem adjacent_refl_cases (a a' : Fin 4)
    (h : a' < a ∧ ∀ z, ¬ (a' < z ∧ z < a)) :
    (a' = 0 ∧ a = 1) ∨ (a' = 1 ∧ a = 2) ∨ (a' = 2 ∧ a = 3) := by
  fin_cases a <;> fin_cases a' <;> simp at h ⊢
  all_goals first
    | (have hz := h 1 (by decide); omega)
    | (have hz := h 2 (by decide); omega)

private theorem noConnection : NoConnection L (Equiv.refl (Fin 4)) := by
  intro w hw
  have hw0 := only_empty_bispecial hw
  subst w
  intro a a' b b' haa hbb hab1 hab2 hcross1 hcross2
  obtain haa' := adjacent_refl_cases a a' haa
  obtain hbb' := adjacent_refl_cases b' b hbb
  rcases haa' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hbb' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      simp [L, edge] at *

private theorem pal_set :
    {w : List (Fin 4) | w ∈ L ∧ w.length = 3 ∧ w.reverse = w} =
      ({[2, 2, 2], [0, 3, 0], [3, 0, 3]} : Set (List (Fin 4))) := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨hwL, hlen, hrev⟩
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [L, edge] at hwL hrev ⊢
  · intro hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl <;> simp [L, edge]

private theorem pal3 : palComplexity L 3 = 3 := by
  unfold palComplexity
  rw [pal_set]
  simp


theorem result : ¬ claim := by
  intro hc
  have h := hc 4 L (Equiv.refl (Fin 4)) factorial extendable usesAll symOrder noConnection 3
  rw [pal3] at h
  have hodd : ¬ Even (3 : ℕ) := by
    rintro ⟨r, hr⟩
    omega
  simp [hodd] at h

end D5.S1.Words.SymmetricOrderPalindromicComplexityRefutation
