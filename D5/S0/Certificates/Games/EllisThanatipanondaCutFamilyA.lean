/- GID: D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/EllisThanatipanondaCutFamilyA
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every Family A cut-set has the conjectured arithmetic-periodic nim-sequence. -/

/- result: proof_shape: content; escape_witness: exclusion.
   admission_basis: open-problem-resolution (#19674; Proved)
   Direct frozen dependencies: G, claim, guard_value, G_equation, nim_formula,
     result use GID D5/S0/Certificates/Games/AbukuEnforceNimberDomination.mex;
     declaration statement_id sha256:a5428f0bcf5c5073cd7c6a65f7783e70f736c5a73a3ab996fabd6f18423d8acc.
   All other source declarations have no direct frozen dependencies.
   Definitions: G, claim; private definitions: F, xs, V (non-Prop types).
   Private content witnesses: xor_le_add -> xor_le_add;
     xs_le_sum -> xor_le_add; large_exclusion -> xs_le_sum;
     reachability -> reachability; exclusion -> large_exclusion;
     nim_formula -> exclusion.
   Private theorems (bind-only declarations have escape_witness: none), with consumers:
     xor_le_add: content -> xs_le_sum;
     xs_le_sum: content -> large_exclusion;
     xs_mod_two: bind-only -> odd_exclusion;
     xs_div_two: bind-only -> large_exclusion;
     xs_replicate_even: bind-only -> option_even;
     F_div_two: bind-only -> large_exclusion;
     F_mod_two: bind-only -> sum_F_mod_two, odd_exclusion;
     sum_predecessors: bind-only -> odd_exclusion;
     sum_F_mod_two: bind-only -> odd_exclusion;
     quotient_budget: bind-only -> large_exclusion;
     odd_exclusion: bind-only -> exclusion;
     large_exclusion: content -> exclusion;
     list_part_lt: bind-only -> guard_value;
     guard_value: bind-only -> G_equation;
     G_equation: bind-only -> nim_formula;
     F_block: bind-only -> reachability;
     option_one: bind-only -> reachability;
     option_three: bind-only -> reachability;
     option_even: bind-only -> reachability;
     reachability: content -> nim_formula;
     exclusion: content -> nim_formula;
     nim_formula: content -> result.
   The public claim retains the source expressions; the proofs use the existing
   mex owner and Mathlib csInf_eq_iff directly, without a second mex declaration.
   Source and literature limits: https://github.com/the-omega-institute/trureturing/issues/19674.
   Four-slot registration of result is unfinished: https://github.com/the-omega-institute/trureturing/issues/19690.
-/

import Mathlib.Algebra.Order.BigOperators.Group.List
import D5.S0.Certificates.Games.AbukuEnforceNimberDomination
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! Binding conventions for P. Ellis and T. A. Thanatipanonda, "The Arithmetic-Periodicity of cut for C = {1, 2c}",
arXiv:2203.02457v1 (Discrete Appl. Math. 322 (2022) 391–403): the game cut with cut-set `C` (a legal move partitions a
pile into `d + 1` nonempty parts for some `d ∈ C`), its nim-sequence `G_C(n)` (Definition 1 and the Sprague–Grundy
recursion), and Section 7, Family A, Conjecture 1: for `C = {1, 3} ∪ X` or `C = {1, 3} ∪ X ∪ Y`, "The nim-sequence for
all games of cut in this family are all precisely (0, 1)^c (+2)". -/


namespace D5.S0.Certificates.Games.EllisThanatipanondaCutFamilyA

open D5.S0.Certificates.Games.AbukuEnforceNimberDomination (mex)
open scoped BigOperators

/-- The nim-sequence of cut with cut-set `C`: `G_C(n) = mex {G_C(h₀) ⊕ ⋯ ⊕ G_C(h_d)}` over the options
`(h₀, …, h_d)` of a pile of size `n`, i.e. `d ∈ C`, every `hᵢ ≥ 1` and `h₀ + ⋯ + h_d = n` (Definition 1). Every part of an
option with `d ≥ 1` is smaller than `n`; the `if` only guards the recursion and is inactive on options. -/
noncomputable def G (C : Set ℕ) (n : ℕ) : ℕ :=
  mex {g | ∃ d ∈ C, ∃ o : Fin (d + 1) → ℕ, (∀ i, 1 ≤ o i) ∧ ∑ i, o i = n ∧
    g = (List.ofFn fun i => if o i < n then G C (o i) else 0).foldr (· ^^^ ·) 0}
termination_by n

/-- Section 7, Family A, Conjecture 1: for `C = {1, 3} ∪ X` or `C = {1, 3} ∪ X ∪ Y`, where `X` is a nonempty set of
even numbers at least `4` with `min X = 2c` and `Y` is a nonempty set of odd numbers at least `5`, the nim-sequence is
`(0, 1)^c (+2)`: `G_C(n) = 2 ⌊(n - 1) / (2c)⌋ + ((n - 1) mod 2)` for every `n ≥ 1`. -/
def claim : Prop :=
  ∀ X Y : Set ℕ, X.Nonempty → (∀ x ∈ X, Even x ∧ 4 ≤ x) →
    (Y = ∅ ∨ (Y.Nonempty ∧ ∀ y ∈ Y, Odd y ∧ 5 ≤ y)) →
    ∀ c : ℕ, 2 * c = sInf X → ∀ n : ℕ, 1 ≤ n →
      G ({1, 3} ∪ X ∪ Y) n = 2 * ((n - 1) / (2 * c)) + (n - 1) % 2

end D5.S0.Certificates.Games.EllisThanatipanondaCutFamilyA

namespace D5.S0.Certificates.Games.EllisThanatipanondaCutFamilyA

open D5.S0.Certificates.Games.AbukuEnforceNimberDomination (mex)
open scoped BigOperators

private def F (b n : ℕ) : ℕ := 2 * ((n - 1) / b) + (n - 1) % 2

private def xs (l : List ℕ) : ℕ := l.foldr (· ^^^ ·) 0

private theorem xor_le_add (a b : ℕ) : a ^^^ b ≤ a + b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a = 0
    · simp [ha]
    have hi := ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2)
    have hdiv := Nat.xor_div_two (a := a) (b := b)
    have hmod := Nat.xor_mod_two_eq (m := a) (n := b)
    have hle := Nat.mod_le (a % 2 + b % 2) 2
    have hmod' : (a ^^^ b) % 2 ≤ a % 2 + b % 2 := by
      rw [hmod, Nat.add_mod]
      exact hle
    omega

private theorem xs_le_sum (l : List ℕ) : xs l ≤ l.sum := by
  unfold xs
  rw [List.sum_eq_foldr]
  exact List.foldr_rel (Nat.le_refl 0) (fun a _ x y h =>
    (xor_le_add a x).trans (Nat.add_le_add_left h a))

private theorem xs_mod_two (l : List ℕ) : xs l % 2 = l.sum % 2 := by
  unfold xs
  rw [List.sum_eq_foldr]
  refine List.foldr_rel (r := fun a b : ℕ => a%2=b%2) rfl ?_
  intro a _ x y h
  rw [Nat.xor_mod_two_eq, Nat.add_mod, h, ← Nat.add_mod]

private theorem xs_div_two (l : List ℕ) : xs l / 2 = xs (l.map (· / 2)) := by
  unfold xs
  exact (List.foldr_map_hom (g := fun n : ℕ => n/2) (f := fun a b : ℕ => a ^^^ b)
    (f' := fun a b : ℕ => a ^^^ b) (a := 0) (l := l)
    (fun a b => (Nat.xor_div_two (a := a) (b := b)).symm)).symm

private theorem xs_replicate_even (c a : ℕ) : xs (List.replicate (2*c) a) = 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [show 2 * (c + 1) = 2 * c + 2 by omega, List.replicate_add]
    simp only [xs, List.foldr_append, List.replicate_succ, List.replicate_zero,
      List.foldr_cons, List.foldr_nil, Nat.xor_zero, Nat.xor_self]
    exact ih


private theorem F_div_two (b n : ℕ) : F b n / 2 = (n - 1) / b := by
  unfold F
  omega

private theorem F_mod_two (b n : ℕ) : F b n % 2 = (n - 1) % 2 := by
  unfold F
  omega

private theorem sum_predecessors (l : List ℕ) (hp : ∀ a ∈ l, 1 ≤ a) :
    (l.map (· - 1)).sum + l.length = l.sum := by
  have hs : (l.map (· - 1)).sum = l.sum - l.length := by
    simpa using (Multiset.sum_map_tsub (l : Multiset ℕ)
      (f := fun x : ℕ => x) (g := fun _ => 1) hp)
  have hl := List.length_le_sum_of_one_le l hp
  omega

private theorem sum_F_mod_two (b : ℕ) (l : List ℕ) :
    (l.map (F b)).sum % 2 = (l.map (· - 1)).sum % 2 := by
  rw [List.sum_nat_mod (l.map (F b)) 2,
    List.sum_nat_mod (l.map (· - 1)) 2]
  simp only [List.map_map, Function.comp_def, F_mod_two]

private theorem quotient_budget (b : ℕ) (l : List ℕ) (hp : ∀ a ∈ l, 1 ≤ a) :
    b * (l.map (fun a => (a - 1) / b)).sum + l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hp a (by simp)
    have ht := ih (fun x hx => hp x (by simp [hx]))
    have hh : b * ((a - 1) / b) ≤ a - 1 := Nat.mul_div_le (a - 1) b
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add]
    omega

private theorem odd_exclusion (b n : ℕ) (l : List ℕ)
    (hp : ∀ a ∈ l, 1 ≤ a) (hs : l.sum = n) (hl : l.length % 2 = 0)
    (hn : 1 ≤ n) : xs (l.map (F b)) ≠ F b n := by
  intro heq
  have hm := congrArg (· % 2) heq
  rw [xs_mod_two, sum_F_mod_two, F_mod_two] at hm
  have ha := sum_predecessors l hp
  omega

private theorem large_exclusion (b n : ℕ) (hb : 0 < b) (l : List ℕ)
    (hp : ∀ a ∈ l, 1 ≤ a) (hs : l.sum = n) (hl : b < l.length)
    (hn : 1 ≤ n) : xs (l.map (F b)) < F b n := by
  have hbudget := quotient_budget b l hp
  have hdiv : xs (l.map (F b)) / 2 = xs (l.map (fun a => (a - 1) / b)) := by
    rw [xs_div_two, List.map_map]
    simp only [Function.comp_def, F_div_two]
  have hbound := xs_le_sum (l.map (fun a => (a - 1) / b))
  have hr := Nat.mod_lt (n - 1) hb
  have hnq := Nat.mod_add_div (n - 1) b
  have hq : (l.map (fun a => (a - 1) / b)).sum < (n - 1) / b := by
    by_contra hh
    have hh' : (n - 1) / b ≤ (l.map (fun a => (a - 1) / b)).sum := Nat.le_of_not_lt hh
    have hh'' := Nat.mul_le_mul_left b hh'
    omega
  have hf := F_div_two b n
  omega


private theorem list_part_lt (l : List ℕ) (hp : ∀ a ∈ l, 1 ≤ a) (hl : 2 ≤ l.length) :
    ∀ a ∈ l, a < l.sum := by
  cases l with
  | nil => simp at hl
  | cons x l =>
    have hx := hp x (by simp)
    have ht : ∀ a ∈ l, 1 ≤ a := fun a ha => hp a (by simp [ha])
    have hsum := List.length_le_sum_of_one_le l ht
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp only [List.length_cons] at hl
      simp only [List.sum_cons]
      omega
    · have hle : a ≤ l.sum := List.le_sum_of_mem ha
      simp only [List.sum_cons]
      omega

private theorem guard_value (C : Set ℕ) (b n d : ℕ) (hd : 1 ≤ d)
    (o : Fin (d + 1) → ℕ) (hp : ∀ i, 1 ≤ o i) (hs : ∑ i, o i = n)
    (ih : ∀ m < n, 1 ≤ m → G C m = F b m) :
    (List.ofFn fun i => if o i < n then G C (o i) else 0).foldr (· ^^^ ·) 0 =
      xs ((List.ofFn o).map (F b)) := by
  have hpos : ∀ a ∈ List.ofFn o, 1 ≤ a := by
    exact List.forall_mem_ofFn_iff.mpr hp
  have hlen : 2 ≤ (List.ofFn o).length := by
    simpa only [List.length_ofFn] using Nat.succ_le_succ hd
  have hsum : (List.ofFn o).sum = n := by rw [List.sum_ofFn]; exact hs
  have hlt := list_part_lt (List.ofFn o) hpos hlen
  have he : (fun i => if o i < n then G C (o i) else 0) = (F b ∘ o) := by
    funext i
    have hm : o i < n := by
      rw [← hsum]
      exact List.forall_mem_ofFn_iff.mp hlt i
    simp only [ite_eq_left hm, Function.comp_apply, ih (o i) hm (hp i)]
  simp only [he, xs, List.map_ofFn]

private def V (C : Set ℕ) (b n : ℕ) : Set ℕ :=
  {g | ∃ d ∈ C, ∃ l : List ℕ, l.length = d + 1 ∧ (∀ a ∈ l, 1 ≤ a) ∧
    l.sum = n ∧ g = xs (l.map (F b))}

private theorem G_equation (C : Set ℕ) (b n : ℕ) (hc : ∀ d ∈ C, 1 ≤ d)
    (ih : ∀ m < n, 1 ≤ m → G C m = F b m) : G C n = mex (V C b n) := by
  rw [G]
  congr 1
  ext g
  constructor
  · rintro ⟨d, hd, o, hp, hs, hg⟩
    refine ⟨d, hd, List.ofFn o, by simp, ?_, ?_, ?_⟩
    · exact List.forall_mem_ofFn_iff.mpr hp
    · rw [List.sum_ofFn]; exact hs
    · exact hg.trans (guard_value C b n d (hc d hd) o hp hs ih)
  · rintro ⟨d, hd, l, hl, hp, hs, hg⟩
    let o : Fin (d + 1) → ℕ := fun i => l[i.val]'(by omega)
    have ho : List.ofFn o = l := by
      exact (List.ofFn_congr hl.symm o).trans List.ofFn_getElem
    have hpo : ∀ i, 1 ≤ o i := by
      exact List.forall_mem_ofFn_iff.mp (ho.symm ▸ hp)
    have hso : ∑ i, o i = n := by rw [← List.sum_ofFn, ho]; exact hs
    refine ⟨d, hd, o, hpo, hso, ?_⟩
    rw [guard_value C b n d (hc d hd) o hpo hso ih, ho]
    exact hg


private theorem F_block (c x r : ℕ) (hc : 0 < c) (hr : 1 ≤ r) (hrb : r ≤ 2*c) :
    F (2*c) (2*c*x+r) = 2*x+(r-1)%2 := by
  have hb : 0 < 2*c := Nat.succ_mul_pos 1 hc
  have hrem : r-1 < 2*c := Nat.sub_one_lt_of_le hr hrb
  have he : 2*c*x+r-1 = (r-1)+(2*c)*x := by omega
  unfold F
  rw [he, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hrem]
  simp [Nat.add_mod, Nat.mul_mod]

private theorem option_one (C : Set ℕ) (c a : ℕ) (h1 : 1 ∈ C) (ha : 1 ≤ a) :
    F (2*c) a ∈ V C (2*c) (a+1) := by
  refine ⟨1, h1, [a,1], by simp, ?_, by simp, ?_⟩
  · simpa using ha
  · simp [xs, F]

private theorem option_three (C : Set ℕ) (c a t : ℕ) (h3 : 3 ∈ C)
    (ha : 1 ≤ a) (ht : 1 ≤ t) : F (2*c) a ∈ V C (2*c) (a+1+2*t) := by
  refine ⟨3, h3, [a,1,t,t], by simp, ?_, ?_, ?_⟩
  · simp [ha, ht]
  · simp
    omega
  · simp [xs, F]

private theorem option_even (C : Set ℕ) (c a t : ℕ) (hb : 2*c ∈ C)
    (ha : 1 ≤ a) (ht : 1 ≤ t) : F (2*c) a ∈ V C (2*c) (a+2*c*t) := by
  refine ⟨2*c, hb, a :: List.replicate (2*c) t, by simp, ?_, ?_, ?_⟩
  · simp [ha, ht]
  · simp [List.sum_replicate, Nat.mul_comm]
  · have hzero := xs_replicate_even c (F (2*c) t)
    change F (2*c) a = F (2*c) a ^^^ xs ((List.replicate (2*c) t).map (F (2*c)))
    rw [List.map_replicate, hzero, Nat.xor_zero]

private theorem reachability (C : Set ℕ) (c : ℕ) (hc : 0 < c)
    (h1 : 1 ∈ C) (h3 : 3 ∈ C) (hb : 2*c ∈ C)
    (n : ℕ) (hn : 1 ≤ n) : ∀ k < F (2*c) n, k ∈ V C (2*c) n := by
  intro k hk
  let q := (n-1)/(2*c)
  let r := (n-1)%(2*c)+1
  let x := k/2
  let e := k%2
  have hbpos : 0 < 2*c := Nat.succ_mul_pos 1 hc
  have hr1 : 1 ≤ r := Nat.le_add_left 1 ((n - 1) % (2 * c))
  have hrb : r ≤ 2*c := by
    exact Nat.succ_le_of_lt (Nat.mod_lt (n - 1) hbpos)
  have hnqr : n = 2*c*q+r := by
    have h := Nat.mod_add_div (n-1) (2*c)
    dsimp [q,r]; omega
  have hf : F (2*c) n = 2*q+(r-1)%2 := by
    rw [hnqr, F_block c q r hc hr1 hrb]
  have he : e < 2 := Nat.mod_lt k (by omega)
  have hkxe : k = 2*x+e := (Nat.div_add_mod k 2).symm
  rw [hf] at hk
  by_cases hpar : e = (r-1)%2
  · have hx : x < q := by omega
    have ha : 1 ≤ 2*c*x+r := Nat.le_add_left_of_le hr1
    have ht : 1 ≤ q-x := Nat.le_sub_of_add_le' hx
    have hsum : (2*c*x+r) + 2*c*(q-x) = n := by
      have hqx : x+(q-x)=q := by omega
      calc
        (2*c*x+r) + 2*c*(q-x) = 2*c*(x+(q-x))+r := by ring
        _ = n := by rw [hqx, ← hnqr]
    have hfa : F (2*c) (2*c*x+r) = k := by
      rw [F_block c x r hc hr1 hrb, ← hpar, ← hkxe]
    have hopt := option_even C c (2*c*x+r) (q-x) hb ha ht
    rwa [hsum, hfa] at hopt
  · have hx : x ≤ q := by omega
    let a := 2*c*x+(e+1)
    have ha : 1 ≤ a := Nat.le_add_left 1 ((2 * c * x).add e)
    have her : e+1 ≤ 2*c := le_mul_of_le_of_one_le he hc
    have hfa : F (2*c) a = k := by
      dsimp [a]
      rw [F_block c x (e+1) hc (by omega) her]
      omega
    have halt : a < n := by
      by_cases hxq : x = q
      · have he0 : e = 0 := by omega
        have hr2 : 2 ≤ r := by omega
        dsimp [a]
        rw [hxq, he0, hnqr]
        omega
      · have hxx : x+1 ≤ q := by omega
        have hmul := Nat.mul_le_mul_left (2*c) hxx
        simp only [Nat.mul_add, Nat.mul_one] at hmul
        dsimp [a]
        omega
    have hnp : n%2 = r%2 := by
      rw [hnqr]
      simp [Nat.add_mod, Nat.mul_mod]
    have hap : a%2 = (e+1)%2 := by
      dsimp [a]
      simp [Nat.add_mod, Nat.mul_mod]
    have hodd : (n-a)%2 = 1 := by omega
    by_cases hdelta : n-a=1
    · have hsum : a+1=n := by omega
      have hopt := option_one C c a h1 ha
      rwa [hsum, hfa] at hopt
    · let t := (n-a-1)/2
      have ht : 1 ≤ t := by dsimp [t]; omega
      have hsum : a+1+2*t=n := by dsimp [t]; omega
      have hopt := option_three C c a t h3 ha ht
      rwa [hsum, hfa] at hopt


private theorem exclusion (C : Set ℕ) (c : ℕ) (hc : 0 < c)
    (hcuts : ∀ d ∈ C, d%2=1 ∨ 2*c ≤ d)
    (n : ℕ) (hn : 1 ≤ n) : F (2*c) n ∉ V C (2*c) n := by
  rintro ⟨d,hd,l,hl,hp,hs,hval⟩
  rcases hcuts d hd with hodd | hbig
  · have hlen : l.length%2=0 := by omega
    exact odd_exclusion (2*c) n l hp hs hlen hn hval.symm
  · have hlen : 2*c < l.length := by omega
    have hlt := large_exclusion (2*c) n (by omega) l hp hs hlen hn
    omega

private theorem nim_formula (C : Set ℕ) (c : ℕ) (hc : 0 < c)
    (h1 : 1 ∈ C) (h3 : 3 ∈ C) (hb : 2*c ∈ C)
    (hcuts : ∀ d ∈ C, d%2=1 ∨ 2*c ≤ d) :
    ∀ n, 1 ≤ n → G C n = F (2*c) n := by
  have hpos : ∀ d ∈ C, 1 ≤ d := by
    intro d hd
    rcases hcuts d hd with hodd | hbig <;> omega
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [G_equation C (2*c) n hpos ih]
    change sInf (V C (2*c) n)ᶜ = F (2*c) n
    have hnot := exclusion C c hc hcuts n hn
    refine (csInf_eq_iff ⟨_, hnot⟩ _).2 ⟨hnot, ?_⟩
    intro k hk
    by_contra h
    exact hk (reachability C c hc h1 h3 hb n hn k (Nat.lt_of_not_ge h))

theorem result : claim := by
  intro X Y hX hEven hY c hc n hn
  have hmem : 2*c ∈ X := by rw [hc]; exact Nat.sInf_mem hX
  have hcpos : 0 < c := Nat.pos_of_lt_mul_left (hEven _ hmem).2
  let C := ({1,3} ∪ X ∪ Y : Set ℕ)
  have h1 : 1 ∈ C := by simp [C]
  have h3 : 3 ∈ C := by simp [C]
  have hb : 2*c ∈ C := by simp [C, hmem]
  have hcuts : ∀ d ∈ C, d%2=1 ∨ 2*c ≤ d := by
    intro d hd
    change d ∈ ({1,3} ∪ X) ∪ Y at hd
    rcases hd with hd | hd
    · rcases hd with hd | hd
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
        rcases hd with rfl | rfl <;> norm_num
      · right
        rw [hc]
        exact Nat.sInf_le hd
    · rcases hY with rfl | ⟨_,hy⟩
      · simp at hd
      · left
        exact Nat.odd_iff.mp (hy d hd).1
  exact nim_formula C c hcpos h1 h3 hb hcuts n hn

end D5.S0.Certificates.Games.EllisThanatipanondaCutFamilyA
