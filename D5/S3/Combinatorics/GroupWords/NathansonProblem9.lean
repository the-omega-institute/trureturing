/- GID: D5/S3/Combinatorics/GroupWords/NathansonProblem9
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GroupWords/NathansonProblem9
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every infinite group has a nontrivial proper product intersection spectrum. -/

/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
/-
Compatible port of Yann Pequignot, lean-infinite-ramsey,
revision b63066fd9f8075a30bc78d392405426bf084e226.
Source: https://github.com/yannpequignot/lean-infinite-ramsey/blob/b63066fd9f8075a30bc78d392405426bf084e226/InfiniteRamsey.lean
License: docs/reports/licenses/lean-infinite-ramsey-LICENSE.txt (Apache-2.0).
Changes: replace Mathlib.Data.Nat.Lattice with Mathlib.Order.Lattice.Nat,
Set.Infinite.diff with Set.Infinite.sdiff, and Set.diff_subset with Set.sdiff_subset;
add explicit imports, make consumed supplier declarations private, and omit the unused
infinite_ramsey_seq corollary and diagnostic commands. The consumed proof bodies are preserved.
Replace this port by direct application when this repository's own pinned Mathlib contains
an equivalent relativized, all-arity finite-colour infinite Ramsey theorem.
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Countable
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Choose
import Mathlib.Data.PNat.Interval
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Nth

/-!
# Nontrivial product intersection spectra in infinite groups

Nathanson, arXiv:2604.04781v2, Problem 9, asks whether every infinite torsion group
admits an asymptotically strictly decreasing sequence whose full positive product
intersection spectrum is neither {1} nor all positive integers. The theorem `result`
answers this existence question for every infinite group. It does not classify all spectra.
Products are ordered, repetitions are allowed, and the subsets remain in the given group.

The supplied relativized infinite Ramsey proof thins finite word supports. A recursive
diagonal handles countably many evaluation values without imposing countability on the group.
Finite cube range gives a common cube fibre and separates exponents 2 and 3; infinite cube
range gives disjoint inverse-pair tails and separates exponents 3 and 2.
-/

open Set

set_option autoImplicit false

noncomputable section

/-- Every infinite set of naturals is the range of a strictly monotone `e : ℕ → ℕ`. -/
private theorem Set.Infinite.exists_strictMono {s : Set ℕ} (hs : s.Infinite) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ i, e i ∈ s :=
  ⟨Nat.nth (· ∈ s), Nat.nth_strictMono hs, Nat.nth_mem_of_infinite hs⟩

/-- Pigeonhole over `ℕ`: some colour class of a finite colouring `f : ℕ → κ` is infinite. -/
private theorem exists_infinite_fiber_nat {κ : Type*} [Finite κ] (f : ℕ → κ) :
    ∃ k : κ, {n : ℕ | f n = k}.Infinite := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  exact ⟨k, Set.infinite_coe_iff.mp hk⟩

variable {κ : Type*}

/-- Intermediate state of the fan construction inside the inductive step of `infinite_ramsey`.
`vert` is a chosen vertex, `succ` an infinite set of naturals all above `vert`, and `hprop`
says: inserting `vert` into any `r`-subset of `succ` gives colour `col` under `c`. -/
private structure RamseyState (c : Finset ℕ → κ) (r : ℕ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hprop : ∀ t : Finset ℕ, ↑t ⊆ succ → t.card = r → c (insert vert t) = col

/-- **The infinite Ramsey theorem** (general arity, relativized). For every finite colouring
`c` of the `r`-element finite subsets of `ℕ` and every infinite `M ⊆ ℕ`, there is an infinite
`N ⊆ M` all of whose `r`-subsets receive one colour.

Proof by induction on `r`; see the module docstring for the fan argument driving the step. -/
private theorem infinite_ramsey [Finite κ] (r : ℕ) (c : Finset ℕ → κ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N ⊆ M, N.Infinite ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c t = col := by
  induction r generalizing c M with
  | zero =>
    -- The only `0`-subset is `∅`, so `M` itself is monochromatic of colour `c ∅`.
    refine ⟨M, subset_rfl, hM, c ∅, fun t _ ht => ?_⟩
    rw [Finset.card_eq_zero.mp ht]
  | succ r ih =>
    -- One fan step: from an infinite `S`, pick `a' = sInf S` and, by the IH applied to the link
    -- colouring `e ↦ c (insert a' e)` on `S \ {a'}`, an infinite monochromatic `N ⊆ S`.
    have stepCore : ∀ S : Set ℕ, S.Infinite →
        ∃ a' ∈ S, ∃ (col' : κ) (N : Set ℕ),
          N.Infinite ∧ N ⊆ S ∧ (∀ x ∈ N, a' < x) ∧
          ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c (insert a' t) = col' := by
      intro S hS
      refine ⟨sInf S, Nat.sInf_mem hS.nonempty, ?_⟩
      have hle : ∀ x ∈ S, sInf S ≤ x := fun x hx => Nat.sInf_le hx
      have hdiff : (S \ {sInf S}).Infinite := hS.sdiff (Set.finite_singleton _)
      obtain ⟨N, hNsub, hNinf, col', hmono⟩ := ih (fun e => c (insert (sInf S) e)) hdiff
      refine ⟨col', N, hNinf, hNsub.trans Set.sdiff_subset, ?_, hmono⟩
      intro x hxN
      have hxd := hNsub hxN
      exact lt_of_le_of_ne (hle x hxd.1) fun h => hxd.2 (h ▸ rfl)
    -- Package a step as a state transition.
    have advance : ∀ s : RamseyState c r, ∃ s' : RamseyState c r,
        s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
      intro s
      obtain ⟨a', ha'mem, col', N, hNinf, hNsub, hNgt, hNprop⟩ := stepCore s.succ s.hInf
      exact ⟨⟨a', col', N, hNinf, hNgt, hNprop⟩, ha'mem, hNsub⟩
    -- Initial state from `M`, then the fan sequence of states.
    obtain ⟨a₀, ha₀M, col₀, N₀, hN₀inf, hN₀sub, hN₀gt, hN₀prop⟩ := stepCore M hM
    let s₀ : RamseyState c r := ⟨a₀, col₀, N₀, hN₀inf, hN₀gt, hN₀prop⟩
    let states : ℕ → RamseyState c r := fun n => n.rec s₀ fun _ s => (advance s).choose
    have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
      fun n => (advance (states n)).choose_spec.1
    have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
      fun n => (advance (states n)).choose_spec.2
    have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
      fun n => (states n).hgt _ (I1 n)
    have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
      intro m n hmn
      induction n with
      | zero => simp [Nat.le_zero.mp hmn]
      | succ n ih2 =>
        rcases Nat.lt_or_eq_of_le hmn with h | rfl
        · exact (I2 n).trans (ih2 (Nat.lt_succ_iff.mp h))
        · exact subset_rfl
    have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
      intro m n hmn
      cases n with
      | zero => exact absurd hmn (Nat.not_lt_zero m)
      | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
    have vmono : StrictMono fun n => (states n).vert := strictMono_nat_of_lt_succ I3
    -- Every vertex lies in `M`.
    have hsuccM : ∀ n, (states n).succ ⊆ M := fun n => (I4 0 n (Nat.zero_le n)).trans hN₀sub
    have hvertM : ∀ n, (states n).vert ∈ M := by
      intro n
      cases n with
      | zero => exact ha₀M
      | succ n => exact hsuccM n (I1 n)
    -- Final pigeonhole on the fan colours.
    obtain ⟨col, hJinf⟩ := exists_infinite_fiber_nat (fun n => (states n).col)
    set V : ℕ → ℕ := fun n => (states n).vert with hV
    set J : Set ℕ := {n | (states n).col = col} with hJ
    refine ⟨V '' J, ?_, hJinf.image (vmono.injective.injOn), col, ?_⟩
    · rintro x ⟨n, _, rfl⟩; exact hvertM n
    · intro t htN htcard
      -- The least vertex `a` of `t` is `vertₘ` for some `m` with `colₘ = col`; the remaining
      -- `r` vertices have index `> m`, hence lie in `(states m).succ`, so `hprop` applies.
      have ht_ne : t.Nonempty := Finset.card_pos.mp (by rw [htcard]; exact Nat.succ_pos r)
      set a := t.min' ht_ne with ha
      have ha_mem : a ∈ t := Finset.min'_mem _ _
      obtain ⟨m, hmJ, hVm⟩ : ∃ m, (states m).col = col ∧ (states m).vert = a := by
        obtain ⟨m, hmJ, hVm⟩ := htN (Finset.mem_coe.mpr ha_mem)
        exact ⟨m, hmJ, hVm⟩
      have hsub : ↑(t.erase a) ⊆ (states m).succ := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_erase] at hx
        obtain ⟨hxne, hxt⟩ := hx
        obtain ⟨p, hpJ, hVp⟩ := htN (Finset.mem_coe.mpr hxt)
        have hax : a < x := lt_of_le_of_ne (Finset.min'_le t x hxt) (Ne.symm hxne)
        have hmp : m < p := by
          have h1 : (states m).vert < (states p).vert := by
            rw [hVm, show (states p).vert = x from hVp]; exact hax
          exact vmono.lt_iff_lt.mp h1
        have := I5 m p hmp
        rwa [show (states p).vert = x from hVp] at this
      have hcard : (t.erase a).card = r := by
        rw [Finset.card_erase_of_mem ha_mem, htcard]; omega
      have key := (states m).hprop (t.erase a) hsub hcard
      rw [hVm, Finset.insert_erase ha_mem, hmJ] at key
      exact key

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set
open scoped Pointwise

-- A Boolean homogeneous set must have the false colour if every infinite set has a counterexample.
private theorem ramsey_false (r : ℕ) (P : Finset ℕ → Prop)
    (hbad : ∀ S : Set ℕ, S.Infinite →
      ∃ t : Finset ℕ, (t : Set ℕ) ⊆ S ∧ t.card = r ∧ ¬ P t)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N ⊆ M, N.Infinite ∧ ∀ t : Finset ℕ, (t : Set ℕ) ⊆ N → t.card = r → ¬ P t := by
  classical
  obtain ⟨N, hNM, hN, c, hc⟩ := infinite_ramsey r (fun t => decide (P t)) hM
  have hfalse : c = false := by
    obtain ⟨t, htN, htr, ht⟩ := hbad N hN
    have heq := hc t htN htr
    simpa [ht] using heq.symm
  refine ⟨N, hNM, hN, ?_⟩
  intro t htN htr hp
  have heq := hc t htN htr
  simp [hp, hfalse] at heq

-- The diagonal is chosen above its predecessor in S_(n+1), never in the intersection of all S_j.
private theorem diagonal_nested (S : ℕ → Set ℕ) (hS : ∀ n, (S n).Infinite)
    (hsub : ∀ n, S (n+1) ⊆ S n) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ j n, j ≤ n → f n ∈ S j := by
  classical
  have hstep : ∀ n x, ∃ y, y ∈ S (n+1) ∧ x < y := by
    intro n x
    exact (hS (n+1)).exists_gt x
  let f : ℕ → ℕ := Nat.rec (hS 0).nonempty.choose
    (fun n x => (hstep n x).choose)
  have hmem : ∀ n, f n ∈ S n := by
    intro n
    cases n with
    | zero => exact (hS 0).nonempty.choose_spec
    | succ n => exact (hstep n (f n)).choose_spec.1
  have hmono : StrictMono f := strictMono_nat_of_lt_succ
    (fun n => (hstep n (f n)).choose_spec.2)
  have hanti : Antitone S := antitone_nat_of_succ_le hsub
  exact ⟨f, hmono, fun j n hjn => hanti hjn (hmem n)⟩

-- One Ramsey refinement for each requirement gives a tail on which that requirement is false.
private theorem countable_ramsey_avoid (r : ℕ → ℕ) (P : ℕ → Finset ℕ → Prop)
    (hbad : ∀ j S, S.Infinite →
      ∃ t : Finset ℕ, (t : Set ℕ) ⊆ S ∧ t.card = r j ∧ ¬ P j t) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ j (t : Finset ℕ),
      (t : Set ℕ) ⊆ f '' {n | j+1 ≤ n} → t.card = r j → ¬ P j t := by
  classical
  have hstep : ∀ j (S : Set ℕ), S.Infinite →
      ∃ N ⊆ S, N.Infinite ∧ ∀ t : Finset ℕ,
        (t : Set ℕ) ⊆ N → t.card = r j → ¬ P j t := by
    intro j S hS
    exact ramsey_false (r j) (P j) (hbad j) hS
  choose T hTsub hTinf hTavoid using hstep
  let S : ℕ → {S : Set ℕ // S.Infinite} := Nat.rec ⟨Set.univ, Set.infinite_univ⟩
    (fun j S => ⟨T j S.1 S.2, hTinf j S.1 S.2⟩)
  have hsub : ∀ j, (S (j+1)).1 ⊆ (S j).1 := fun j => hTsub j (S j).1 (S j).2
  obtain ⟨f, hf, hmem⟩ := diagonal_nested (fun j => (S j).1) (fun j => (S j).2) hsub
  refine ⟨f, hf, ?_⟩
  intro j t ht hcard
  apply hTavoid j (S j).1 (S j).2 t _ hcard
  intro x hx
  obtain ⟨n, hn, rfl⟩ := ht hx
  exact hmem (j+1) n hn

variable {G : Type*} [Group G]

private def signed (b : Bool) (x : G) : G := if b then x⁻¹ else x

private theorem signed_injective (b : Bool) : Function.Injective (signed (G := G) b) := by
  cases b <;> simp [signed, Function.Injective]

private theorem square_injective_on_cube_fiber (b : G) :
    Set.InjOn (fun x : G => x^2) {x | x^3 = b} := by
  intro x hx y hy hsq
  have h : x^2 * x = y^2 * y := by simpa only [← pow_succ] using hx.trans hy.symm
  change x^2 = y^2 at hsq
  rw [hsq] at h
  exact mul_left_cancel h

-- The four pure signed triple words require no commutativity.
private theorem pure_signed_triple (x : G) (a b c : Bool) :
    signed a x * signed b x * signed c x ∈ ({x^3, x, x⁻¹, (x^3)⁻¹} : Set G) := by
  cases a <;> cases b <;> cases c <;> simp [signed, pow_succ, mul_assoc]

-- A direct ordered-support adapter uses the existing unique increasing enumeration API.
private theorem support_adapter {k : ℕ} (a : Fin k → ℕ) (ha : StrictMono a) :
    (Finset.univ.image a).card = k ∧
    a = (Finset.univ.image a).orderEmbOfFin (by simp [Finset.card_image_of_injective, ha.injective]) := by
  classical
  refine ⟨by simp [Finset.card_image_of_injective, ha.injective], ?_⟩
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image_of_mem a (Finset.mem_univ i)
  · exact ha

end D5.S3.Combinatorics.GroupWords.NathansonProblem9

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set

-- A function with one cancellable support coordinate cannot be constant on all k-subsets.
private theorem ordered_support_nonconstant {k : ℕ} {α : Type*}
    (F : (Fin k → ℕ) → α) (j : Fin k)
    (hj : ∀ a b : Fin k → ℕ, (∀ i, i ≠ j → a i = b i) → F a = F b → a j = b j)
    {S : Set ℕ} (hS : S.Infinite) (g : α) :
    ∃ t : Finset ℕ, ∃ ht : t.card = k,
      (t : Set ℕ) ⊆ S ∧ F (t.orderEmbOfFin ht) ≠ g := by
  classical
  obtain ⟨e, he, heS⟩ := hS.exists_strictMono
  let a : Fin k → ℕ := fun i => e (j.succ.succAbove i).val
  let b : Fin k → ℕ := fun i => e (j.castSucc.succAbove i).val
  have ha : StrictMono a := he.comp (Fin.val_strictMono.comp (Fin.strictMono_succAbove _))
  have hb : StrictMono b := he.comp (Fin.val_strictMono.comp (Fin.strictMono_succAbove _))
  have hab : ∀ i, i ≠ j → a i = b i := by
    intro i hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp [a, b, Fin.succAbove_succ_of_le _ _ hlt.le, Fin.succAbove_castSucc_of_lt _ _ hlt]
    · simp [a, b, Fin.succAbove_succ_of_lt _ _ hgt, Fin.succAbove_castSucc_of_le _ _ hgt.le]
  have hne : a j ≠ b j := by
    simp only [a, b, Fin.succAbove_succ_self, Fin.succAbove_castSucc_self]
    exact ne_of_lt (he (Nat.lt_succ_self _))
  have hF : F a ≠ g ∨ F b ≠ g := by
    by_contra! h
    exact hne (hj a b hab (h.1.trans h.2.symm))
  rcases hF with hFa | hFb
  · obtain ⟨hcard, hadapt⟩ := support_adapter a ha
    refine ⟨Finset.univ.image a, hcard, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact heS _
    · simpa only [← hadapt] using hFa
  · obtain ⟨hcard, hbadapt⟩ := support_adapter b hb
    refine ⟨Finset.univ.image b, hcard, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact heS _
    · simpa only [← hbadapt] using hFb

-- Countably many target values are enough even if the ambient value type has arbitrary cardinality.
private theorem countable_support_thinning {ι α : Type*} [Countable ι] [Nonempty ι]
    (k : ι → ℕ) (F : (i : ι) → (Fin (k i) → ℕ) → α)
    (hj : ∀ i, ∃ j : Fin (k i), ∀ a b : Fin (k i) → ℕ,
      (∀ l, l ≠ j → a l = b l) → F i a = F i b → a j = b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i g, ∃ N : ℕ,
      ∀ a : Fin (k i) → ℕ, StrictMono a →
      (∀ l, N ≤ a l) → F i (f ∘ a) ≠ g := by
  classical
  let V : Set α := Set.range (fun x : (i : ι) × (Fin (k i) → ℕ) => F x.1 x.2)
  have hVc : V.Countable := Set.countable_range _
  have hVne : V.Nonempty := by
    let i : ι := Classical.arbitrary ι
    exact ⟨F i (fun _ => 0), ⟨⟨i, fun _ => 0⟩, rfl⟩⟩
  letI : Countable V := hVc.to_subtype
  letI : Nonempty V := hVne.to_subtype
  obtain ⟨req, hreq⟩ := (countable_iff_exists_surjective (α := ι × V)).mp inferInstance
  let r (n : ℕ) : ℕ := k (req n).1
  let P (n : ℕ) (t : Finset ℕ) : Prop :=
    ∃ ht : t.card = r n, F (req n).1 (t.orderEmbOfFin ht) = (req n).2.1
  have hbad : ∀ n (S : Set ℕ), S.Infinite →
      ∃ t : Finset ℕ, (t : Set ℕ) ⊆ S ∧ t.card = r n ∧ ¬ P n t := by
    intro n S hS
    obtain ⟨j, hj⟩ := hj (req n).1
    obtain ⟨t, ht, htS, htne⟩ := ordered_support_nonconstant (F (req n).1) j hj hS (req n).2.1
    refine ⟨t, htS, ht, ?_⟩
    rintro ⟨ht', heq⟩
    exact htne heq
  obtain ⟨f, hf, havoid⟩ := countable_ramsey_avoid r P hbad
  refine ⟨f, hf, ?_⟩
  intro i g
  by_cases hg : g ∈ V
  · obtain ⟨n, hn⟩ := hreq (i, ⟨g, hg⟩)
    have hn1 : (req n).1 = i := congrArg Prod.fst hn
    have hn2 : (req n).2.1 = g := congrArg (fun p : ι × V => p.2.1) hn
    refine ⟨n+1, ?_⟩
    intro a ha hbound heq
    let b : Fin (k (req n).1) → ℕ := fun l => f (a (Fin.cast (congrArg k hn1) l))
    have hb : StrictMono b := hf.comp (ha.comp (Fin.castOrderIso (congrArg k hn1)).strictMono)
    obtain ⟨hcard, hadapt⟩ := support_adapter b hb
    apply havoid n (Finset.univ.image b) _ hcard
    · refine ⟨hcard, ?_⟩
      rw [← hadapt]
      subst i
      exact heq.trans hn2.symm
    · intro x hx
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨a (Fin.cast (congrArg k hn1) l), hbound _, rfl⟩
  · refine ⟨0, ?_⟩
    intro a _ _ heq
    exact hg ⟨⟨i, f ∘ a⟩, heq⟩

end D5.S3.Combinatorics.GroupWords.NathansonProblem9

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set
open scoped Pointwise
variable {G : Type*} [Group G]

private def tripleEval {k : ℕ} (u : ℕ → G) (α : Fin 3 → Fin k) (ε : Fin 3 → Bool)
    (a : Fin k → ℕ) : G :=
  signed (ε 0) (u (a (α 0))) * signed (ε 1) (u (a (α 1))) * signed (ε 2) (u (a (α 2)))

private theorem singleton_triple_coordinate {k : ℕ} (u : ℕ → G) (hu : Function.Injective u)
    (α : Fin 3 → Fin k) (ε : Fin 3 → Bool) (p : Fin 3)
    (hp : ∀ q, α q = α p → q = p) :
    ∀ a b : Fin k → ℕ, (∀ i, i ≠ α p → a i = b i) →
      tripleEval u α ε a = tripleEval u α ε b → a (α p) = b (α p) := by
  intro a b hab heq
  have fixed : ∀ q, q ≠ p → a (α q) = b (α q) := by
    intro q hqp
    exact hab (α q) (fun h => hqp (hp q h))
  fin_cases p
  · have h1 := fixed 1 (by decide)
    have h2 := fixed 2 (by decide)
    simp only [tripleEval, h1, h2] at heq
    exact hu (signed_injective (ε 0) (mul_right_cancel (mul_right_cancel heq)))
  · have h0 := fixed 0 (by decide)
    have h2 := fixed 2 (by decide)
    simp only [tripleEval, h0, h2] at heq
    exact hu (signed_injective (ε 1) (mul_left_cancel (mul_right_cancel heq)))
  · have h0 := fixed 0 (by decide)
    have h1 := fixed 1 (by decide)
    simp only [tripleEval, h0, h1] at heq
    exact hu (signed_injective (ε 2) (mul_left_cancel heq))

-- These are exact finite logical support cases, not numerical approximations.
private theorem onto_two_has_singleton :
    ∀ α : Fin 3 → Fin 2, Function.Surjective α → ∃ p, ∀ q, α q = α p → q = p := by
  unfold Function.Surjective
  decide

private theorem onto_three_has_singleton :
    ∀ α : Fin 3 → Fin 3, Function.Surjective α → ∃ p, ∀ q, α q = α p → q = p := by
  unfold Function.Surjective
  decide

private theorem all_signed_triples_thin (u : ℕ → G) (hu : Function.Injective u) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      (∀ (α : Fin 3 → Fin 2), Function.Surjective α → ∀ (ε : Fin 3 → Bool) (g : G),
        ∃ N, ∀ a : Fin 2 → ℕ, StrictMono a → (∀ l, N ≤ a l) → tripleEval u α ε (f ∘ a) ≠ g) ∧
      (∀ (α : Fin 3 → Fin 3), Function.Surjective α → ∀ (ε : Fin 3 → Bool) (g : G),
        ∃ N, ∀ a : Fin 3 → ℕ, StrictMono a → (∀ l, N ≤ a l) → tripleEval u α ε (f ∘ a) ≠ g) := by
  classical
  let I := ((Fin 3 → Fin 2) × (Fin 3 → Bool)) ⊕ ((Fin 3 → Fin 3) × (Fin 3 → Bool))
  let good : I → Prop := Sum.elim (fun p => Function.Surjective p.1) (fun p => Function.Surjective p.1)
  let J := {i : I // good i}
  have hn : Nonempty J := by
    refine ⟨⟨Sum.inr (id, fun _ => false), ?_⟩⟩
    exact Function.surjective_id
  letI : Nonempty J := hn
  let k : J → ℕ := fun j => match j.1 with | .inl _ => 2 | .inr _ => 3
  let F (j : J) : (Fin (k j) → ℕ) → G :=
    match j with
    | ⟨.inl (α, ε), _⟩ => tripleEval u α ε
    | ⟨.inr (α, ε), _⟩ => tripleEval u α ε
  have hsingle : ∀ j, ∃ p : Fin (k j), ∀ a b : Fin (k j) → ℕ,
      (∀ l, l ≠ p → a l = b l) → F j a = F j b → a p = b p := by
    rintro ⟨(⟨α, ε⟩ | ⟨α, ε⟩), hgood⟩
    · obtain ⟨p, hp⟩ := onto_two_has_singleton α hgood
      exact ⟨α p, singleton_triple_coordinate u hu α ε p hp⟩
    · obtain ⟨p, hp⟩ := onto_three_has_singleton α hgood
      exact ⟨α p, singleton_triple_coordinate u hu α ε p hp⟩
  obtain ⟨f, hf, hthin⟩ := countable_support_thinning k F hsingle
  refine ⟨f, hf, ?_, ?_⟩
  · intro α hα ε g
    exact hthin ⟨.inl (α, ε), hα⟩ g
  · intro α hα ε g
    exact hthin ⟨.inr (α, ε), hα⟩ g

end D5.S3.Combinatorics.GroupWords.NathansonProblem9

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set
open scoped Pointwise
variable {G : Type*} [Group G]

private theorem infinite_cube_fiber_stock [Infinite G]
    (hC : (Set.range (fun x : G => x^3)).Finite) :
    ∃ b : G, ∃ u : ℕ → G, Function.Injective u ∧
      (∀ n, (u n)^3 = b) ∧ Function.Injective (fun n => (u n)^2) := by
  classical
  let C : Set G := Set.range (fun x : G => x^3)
  letI : Finite C := hC.to_subtype
  let c : G → C := fun x => ⟨x^3, x, rfl⟩
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber c
  have hinf : {x : G | x^3 = b.1}.Infinite := by
    have hh := Set.infinite_coe_iff.mp hb
    convert hh using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, c]
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  let e := hinf.natEmbedding _
  let u : ℕ → G := fun n => (e n).1
  have hu : Function.Injective u := Subtype.val_injective.comp e.injective
  have hcub : ∀ n, (u n)^3 = b.1 := fun n => (e n).2
  refine ⟨b.1, u, hu, hcub, ?_⟩
  intro m n h
  exact hu (square_injective_on_cube_fiber b.1 (hcub m) (hcub n) h)

-- Cubes chosen outside all earlier cube inverse-orbits give disjoint root inverse-orbits.
private theorem infinite_cube_range_stock
    (hC : (Set.range (fun x : G => x^3)).Infinite) :
    ∃ u : ℕ → G, (∀ m n, m ≠ n → (u m)^3 ≠ (u n)^3 ∧ (u m)^3 ≠ ((u n)^3)⁻¹) ∧
      (∀ m n, m ≠ n → u m ≠ u n ∧ u m ≠ (u n)⁻¹) := by
  classical
  have next : ∀ F : Finset G, ∃ x : G, x^3 ∉ F ∧ (x^3)⁻¹ ∉ F := by
    intro F
    obtain ⟨c, hc, hcF⟩ := hC.exists_notMem_finite (F.finite_toSet.union (F.finite_toSet.image Inv.inv))
    obtain ⟨x, rfl⟩ := hc
    refine ⟨x, ?_, ?_⟩
    · exact fun h => hcF (Or.inl h)
    · intro h
      exact hcF (Or.inr ⟨(x^3)⁻¹, h, inv_inv _⟩)
  let S : ℕ → Finset G := Nat.rec ∅ (fun _ F =>
    insert (((next F).choose)^3) (insert ((((next F).choose)^3)⁻¹) F))
  let u : ℕ → G := fun n => (next (S n)).choose
  have hS : Monotone S := monotone_nat_of_le_succ (fun n => by
    intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
  have hmem : ∀ m n, m < n → (u m)^3 ∈ S n := by
    intro m n hmn
    exact hS (Nat.succ_le_of_lt hmn) (Finset.mem_insert_self _ _)
  have hne : ∀ m n, m < n → (u n)^3 ≠ (u m)^3 ∧ ((u n)^3)⁻¹ ≠ (u m)^3 := by
    intro m n hmn
    exact ⟨fun h => (next (S n)).choose_spec.1 (h ▸ hmem m n hmn),
      fun h => (next (S n)).choose_spec.2 (h ▸ hmem m n hmn)⟩
  have hcubes : ∀ m n, m ≠ n → (u m)^3 ≠ (u n)^3 ∧ (u m)^3 ≠ ((u n)^3)⁻¹ := by
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with h | h
    · have hh := hne m n h
      exact ⟨Ne.symm hh.1, Ne.symm hh.2⟩
    · have hh := hne n m h
      refine ⟨hh.1, ?_⟩
      intro heq
      apply hh.2
      simpa using congrArg Inv.inv heq
  refine ⟨u, hcubes, ?_⟩
  intro m n hmn
  refine ⟨fun h => (hcubes m n hmn).1 (congrArg (fun x : G => x^3) h), ?_⟩
  intro h
  apply (hcubes m n hmn).2
  simpa only [← inv_pow] using congrArg (fun x : G => x^3) h

end D5.S3.Combinatorics.GroupWords.NathansonProblem9

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set
open scoped Pointwise
variable {G : Type*} [Group G]

private def blockTail (B : ℕ → Set G) (q : ℕ+) : Set G := {x | ∃ n, (q : ℕ) ≤ n ∧ x ∈ B n}
def ASD (A : ℕ+ → Set G) : Prop :=
  (∀ q, A (q+1) ⊆ A q) ∧ {q | A q ≠ A (q+1)}.Infinite
def spectrum (A : ℕ+ → Set G) : Set ℕ :=
  {h | 0 < h ∧ (⋂ q, A q)^h = ⋂ q, (A q)^h}

private theorem block_tails_strict_core (B : ℕ → Set G) (hne : ∀ n, (B n).Nonempty)
    (hidx : ∀ {m n x}, x ∈ B m → x ∈ B n → m = n) :
    ASD (blockTail B) ∧ (⋂ q, blockTail B q) = ∅ := by
  have hmono : ∀ q, blockTail B (q+1) ⊆ blockTail B q := by
    intro q x hx
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨n, by change (q : ℕ)+1 ≤ n at hn; omega, hx⟩
  have hstrict : ∀ q : ℕ+, blockTail B q ≠ blockTail B (q+1) := by
    intro q heq
    obtain ⟨x, hx⟩ := hne q.val
    have hmem : x ∈ blockTail B q := ⟨q.val, le_rfl, hx⟩
    rw [heq] at hmem
    obtain ⟨n, hn, hxn⟩ := hmem
    have heqn := hidx hx hxn
    have : (q : ℕ)+1 ≤ n := hn
    omega
  refine ⟨⟨hmono, ?_⟩, ?_⟩
  · have : {q | blockTail B q ≠ blockTail B (q+1)} = Set.univ := Set.eq_univ_of_forall hstrict
    rw [this]
    exact Set.infinite_univ
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxall := Set.mem_iInter.mp hx
    obtain ⟨n, _, hxn⟩ := hxall 1
    obtain ⟨m, hm, hxm⟩ := hxall ⟨n+1, Nat.succ_pos _⟩
    have := hidx hxn hxm
    change n+1 ≤ m at hm
    omega

private theorem eventual_ne_of_injective (u : ℕ → G) (hu : Function.Injective u) (g : G) :
    ∃ N : ℕ, ∀ n, N ≤ n → u n ≠ g := by
  classical
  by_cases h : ∃ n, u n = g
  · obtain ⟨m, hm⟩ := h
    refine ⟨m+1, ?_⟩
    intro n hn heq
    have := hu (heq.trans hm.symm)
    omega
  · exact ⟨0, fun n _ heq => h ⟨n, heq⟩⟩

private theorem pair_thinning (u : ℕ → G) (hu : Function.Injective u) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ g : G, ∃ N : ℕ,
      ∀ m n, N ≤ m → N ≤ n → m ≠ n → u (f m) * u (f n) ≠ g := by
  classical
  let F (b : Bool) (a : Fin 2 → ℕ) : G := if b then u (a 1) * u (a 0) else u (a 0) * u (a 1)
  have hs : ∀ b, ∃ j : Fin 2, ∀ a c : Fin 2 → ℕ,
      (∀ l, l ≠ j → a l = c l) → F b a = F b c → a j = c j := by
    intro b
    refine ⟨0, ?_⟩
    intro a c hac heq
    have hh := hac 1 (by decide)
    cases b
    · simp only [F, Bool.false_eq_true, ↓reduceIte, hh] at heq
      exact hu (mul_right_cancel heq)
    · simp only [F, ↓reduceIte, hh] at heq
      exact hu (mul_left_cancel heq)
  obtain ⟨f, hf, hthin⟩ := countable_support_thinning (fun _ : Bool => 2) F hs
  refine ⟨f, hf, ?_⟩
  intro g
  obtain ⟨N₀, h₀⟩ := hthin false g
  obtain ⟨N₁, h₁⟩ := hthin true g
  refine ⟨max N₀ N₁, ?_⟩
  intro m n hm hn hmn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have ha : StrictMono (![m,n] : Fin 2 → ℕ) := by simpa [Fin.strictMono_iff_lt_succ] using hlt
    have hbound : ∀ l : Fin 2, N₀ ≤ (![m,n] : Fin 2 → ℕ) l := by
      intro l; fin_cases l <;> simp <;> omega
    exact h₀ ![m,n] ha hbound
  · have ha : StrictMono (![n,m] : Fin 2 → ℕ) := by simpa [Fin.strictMono_iff_lt_succ] using hgt
    have hbound : ∀ l : Fin 2, N₁ ≤ (![n,m] : Fin 2 → ℕ) l := by
      intro l; fin_cases l <;> simp <;> omega
    exact h₁ ![n,m] ha hbound

end D5.S3.Combinatorics.GroupWords.NathansonProblem9

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set
variable {G : Type*} [Group G]

private theorem support_factorization {m : ℕ} (v : Fin m → ℕ) :
    ∃ k, k ≤ m ∧ ∃ a : Fin k → ℕ, StrictMono a ∧
      ∃ α : Fin m → Fin k, Function.Surjective α ∧
        (∀ l, a (α l) = v l) ∧ (∀ i, ∃ l, a i = v l) := by
  classical
  let s := Finset.univ.image v
  let a : Fin s.card → ℕ := s.orderEmbOfFin rfl
  let α (l : Fin m) : Fin s.card :=
    (s.orderIsoOfFin rfl).symm ⟨v l, Finset.mem_image_of_mem v (Finset.mem_univ l)⟩
  have hrep : ∀ l, a (α l) = v l := by
    intro l
    change ((s.orderIsoOfFin rfl) ((s.orderIsoOfFin rfl).symm _)).val = v l
    simp
  have ha : ∀ i, ∃ l, a i = v l := by
    intro i
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem rfl i)
    exact ⟨l, hl.symm⟩
  refine ⟨s.card, ?_, a, (s.orderEmbOfFin rfl).strictMono, α, ?_, hrep, ha⟩
  · exact le_trans (Finset.card_image_le) (by simp)
  · intro i
    obtain ⟨l, hl⟩ := ha i
    exact ⟨l, (s.orderEmbOfFin rfl).injective ((hrep l).trans hl.symm)⟩

private theorem mixed_signed_triples_avoid (u : ℕ → G) (hu : Function.Injective u) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ g : G, ∃ N : ℕ,
      ∀ (v : Fin 3 → ℕ) (ε : Fin 3 → Bool), (∀ l, N ≤ v l) →
      ¬ (v 0 = v 1 ∧ v 1 = v 2) →
      signed (ε 0) (u (f (v 0))) * signed (ε 1) (u (f (v 1))) *
        signed (ε 2) (u (f (v 2))) ≠ g := by
  classical
  obtain ⟨f, hf, h₂, h₃⟩ := all_signed_triples_thin u hu
  refine ⟨f, hf, ?_⟩
  intro g
  have hh₂ : ∀ p : (Fin 3 → Fin 2) × (Fin 3 → Bool), ∃ N : ℕ,
      ∀ a : Fin 2 → ℕ, StrictMono a → (∀ l, N ≤ a l) →
        Function.Surjective p.1 → tripleEval u p.1 p.2 (f ∘ a) ≠ g := by
    intro p
    by_cases hp : Function.Surjective p.1
    · obtain ⟨N, hN⟩ := h₂ p.1 hp p.2 g
      exact ⟨N, fun a ha hbd _ => hN a ha hbd⟩
    · exact ⟨0, fun _ _ _ h => (hp h).elim⟩
  have hh₃ : ∀ p : (Fin 3 → Fin 3) × (Fin 3 → Bool), ∃ N : ℕ,
      ∀ a : Fin 3 → ℕ, StrictMono a → (∀ l, N ≤ a l) →
        Function.Surjective p.1 → tripleEval u p.1 p.2 (f ∘ a) ≠ g := by
    intro p
    by_cases hp : Function.Surjective p.1
    · obtain ⟨N, hN⟩ := h₃ p.1 hp p.2 g
      exact ⟨N, fun a ha hbd _ => hN a ha hbd⟩
    · exact ⟨0, fun _ _ _ h => (hp h).elim⟩
  choose N₂ hN₂ using hh₂
  choose N₃ hN₃ using hh₃
  let M₂ := Finset.univ.sup N₂
  let M₃ := Finset.univ.sup N₃
  refine ⟨max M₂ M₃, ?_⟩
  intro v ε hbd hmixed
  obtain ⟨k, hk, a, ha, α, hα, hrep, harange⟩ := support_factorization v
  have hk2 : 2 ≤ k := by
    by_contra! h
    have hh : ∀ i j : Fin k, i = j := by intro i j; apply Fin.ext; omega
    apply hmixed
    exact ⟨(hrep 0).symm.trans ((congrArg a (hh (α 0) (α 1))).trans (hrep 1)),
      (hrep 1).symm.trans ((congrArg a (hh (α 1) (α 2))).trans (hrep 2))⟩
  have habd : ∀ l, max M₂ M₃ ≤ a l := by
    intro l
    obtain ⟨j, hj⟩ := harange l
    rw [hj]
    exact hbd j
  have casesk : k = 2 ∨ k = 3 := by omega
  rcases casesk with rfl | rfl
  · have hle : N₂ (α, ε) ≤ M₂ := Finset.le_sup (Finset.mem_univ _)
    have hno := hN₂ (α, ε) a ha (fun l => le_trans hle (le_trans (le_max_left _ _) (habd l))) hα
    simpa only [tripleEval, Function.comp_apply, hrep] using hno
  · have hle : N₃ (α, ε) ≤ M₃ := Finset.le_sup (Finset.mem_univ _)
    have hno := hN₃ (α, ε) a ha (fun l => le_trans hle (le_trans (le_max_right _ _) (habd l))) hα
    simpa only [tripleEval, Function.comp_apply, hrep] using hno

end D5.S3.Combinatorics.GroupWords.NathansonProblem9

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set
open scoped Pointwise
variable {G : Type*} [Group G]

private theorem spectrum_separation (A : ℕ+ → Set G) (hcore : (⋂ q, A q) = ∅)
    (s t : ℕ) (hs : 0 < s) (hs1 : s ≠ 1) (ht : 0 < t)
    (hin : (⋂ q, (A q)^s) = ∅) (hout : (⋂ q, (A q)^t).Nonempty) :
    spectrum A ≠ {1} ∧ spectrum A ≠ {h : ℕ | 0 < h} := by
  have hsin : s ∈ spectrum A := by
    refine ⟨hs, ?_⟩
    rw [hcore, Set.empty_pow (Nat.ne_of_gt hs), hin]
  have htnot : t ∉ spectrum A := by
    intro h
    have hh := h.2
    rw [hcore, Set.empty_pow (Nat.ne_of_gt ht)] at hh
    rw [← hh] at hout
    exact Set.not_nonempty_empty hout
  constructor
  · intro heq
    rw [heq, Set.mem_singleton_iff] at hsin
    exact hs1 hsin
  · intro heq
    apply htnot
    rw [heq]
    exact ht

private theorem finite_cube_range_case [Infinite G]
    (hC : (Set.range (fun x : G => x^3)).Finite) :
    ∃ A : ℕ+ → Set G, ASD A ∧ spectrum A ≠ {1} ∧ spectrum A ≠ {h : ℕ | 0 < h} := by
  classical
  obtain ⟨b, u, hu, hcube, hsquare⟩ := infinite_cube_fiber_stock hC
  obtain ⟨f, hf, hmix⟩ := pair_thinning u hu
  let v : ℕ → G := u ∘ f
  have hv : Function.Injective v := hu.comp hf.injective
  have hv2 : Function.Injective (fun n => (v n)^2) := hsquare.comp hf.injective
  have hv3 : ∀ n, (v n)^3 = b := fun n => hcube (f n)
  let B (n : ℕ) : Set G := {v n}
  let A := blockTail B
  have hBne : ∀ n, (B n).Nonempty := fun n => ⟨v n, rfl⟩
  have hBidx : ∀ {m n x}, x ∈ B m → x ∈ B n → m = n := by
    intro m n x hx hy
    exact hv (hx.symm.trans hy)
  obtain ⟨hasd, hcore⟩ := block_tails_strict_core B hBne hBidx
  have htwo : (⋂ q, (A q)^2) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    obtain ⟨Nm, hNm⟩ := hmix g
    obtain ⟨Np, hNp⟩ := eventual_ne_of_injective (fun n => (v n)^2) hv2 g
    let q : ℕ+ := ⟨max Nm Np + 1, Nat.succ_pos _⟩
    have hprod := Set.mem_iInter.mp hg q
    rw [pow_two] at hprod
    obtain ⟨x, hx, y, hy, heq⟩ := hprod
    obtain ⟨n, hn, hxn⟩ := hx
    obtain ⟨m, hm, hym⟩ := hy
    change x = v n at hxn
    change y = v m at hym
    subst x; subst y
    have hnN : Nm ≤ n := by change max Nm Np + 1 ≤ n at hn; omega
    have hmN : Nm ≤ m := by change max Nm Np + 1 ≤ m at hm; omega
    by_cases hnm : n = m
    · subst m
      apply hNp n (by change max Nm Np + 1 ≤ n at hn; omega)
      simpa only [pow_two] using heq
    · exact hNm n m hnN hmN hnm heq
  have hthree : (⋂ q, (A q)^3).Nonempty := by
    refine ⟨b, Set.mem_iInter.mpr ?_⟩
    intro q
    have hmem : v q.val ∈ A q := ⟨q.val, le_rfl, rfl⟩
    have hpow := Set.pow_mem_pow (n := 3) hmem
    rwa [hv3] at hpow
  exact ⟨A, hasd, spectrum_separation A hcore 2 3 (by decide) (by decide) (by decide) htwo hthree⟩

end D5.S3.Combinatorics.GroupWords.NathansonProblem9

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set
open scoped Pointwise
variable {G : Type*} [Group G]

private theorem pure_signed_eventual (v : ℕ → G) (hv : Function.Injective v)
    (hc : Function.Injective (fun n => (v n)^3)) (g : G) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ ε : Fin 3 → Bool,
      signed (ε 0) (v n) * signed (ε 1) (v n) * signed (ε 2) (v n) ≠ g := by
  obtain ⟨N₁, h₁⟩ := eventual_ne_of_injective v hv g
  obtain ⟨N₂, h₂⟩ := eventual_ne_of_injective (fun n => (v n)⁻¹) (inv_injective.comp hv) g
  obtain ⟨N₃, h₃⟩ := eventual_ne_of_injective (fun n => (v n)^3) hc g
  obtain ⟨N₄, h₄⟩ := eventual_ne_of_injective (fun n => ((v n)^3)⁻¹) (inv_injective.comp hc) g
  refine ⟨max (max N₁ N₂) (max N₃ N₄), ?_⟩
  intro n hn ε heq
  have hp := pure_signed_triple (v n) (ε 0) (ε 1) (ε 2)
  rw [heq] at hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h | h
  · exact h₃ n (by omega) h.symm
  · exact h₁ n (by omega) h.symm
  · exact h₂ n (by omega) h.symm
  · exact h₄ n (by omega) h.symm

private theorem infinite_cube_range_case
    (hC : (Set.range (fun x : G => x^3)).Infinite) :
    ∃ A : ℕ+ → Set G, ASD A ∧ spectrum A ≠ {1} ∧ spectrum A ≠ {h : ℕ | 0 < h} := by
  classical
  obtain ⟨u, hcubes, hroots⟩ := infinite_cube_range_stock hC
  have hu : Function.Injective u := by
    intro m n h
    by_contra hmn
    exact (hroots m n hmn).1 h
  obtain ⟨f, hf, hmix⟩ := mixed_signed_triples_avoid u hu
  let v : ℕ → G := u ∘ f
  have hv : Function.Injective v := hu.comp hf.injective
  have hvc : Function.Injective (fun n => (v n)^3) := by
    intro m n h
    by_contra hmn
    exact (hcubes (f m) (f n) (fun h => hmn (hf.injective h))).1 h
  have hvr : ∀ m n, m ≠ n → v m ≠ v n ∧ v m ≠ (v n)⁻¹ := by
    intro m n hmn
    exact hroots (f m) (f n) (fun h => hmn (hf.injective h))
  let B (n : ℕ) : Set G := {v n, (v n)⁻¹}
  let A := blockTail B
  have hBne : ∀ n, (B n).Nonempty := fun n => ⟨v n, Or.inl rfl⟩
  have hBidx : ∀ {m n x}, x ∈ B m → x ∈ B n → m = n := by
    intro m n x hx hy
    by_contra hmn
    change x = v m ∨ x = (v m)⁻¹ at hx
    change x = v n ∨ x = (v n)⁻¹ at hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (hvr m n hmn).1 (hx.symm.trans hy)
    · exact (hvr m n hmn).2 (hx.symm.trans hy)
    · exact (hvr n m (Ne.symm hmn)).2 (hy.symm.trans hx)
    · exact (hvr m n hmn).1 (inv_injective (hx.symm.trans hy))
  obtain ⟨hasd, hcore⟩ := block_tails_strict_core B hBne hBidx
  have hthree : (⋂ q, (A q)^3) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    obtain ⟨Nm, hNm⟩ := hmix g
    obtain ⟨Np, hNp⟩ := pure_signed_eventual v hv hvc g
    let q : ℕ+ := ⟨max Nm Np + 1, Nat.succ_pos _⟩
    have hprod := Set.mem_iInter.mp hg q
    rw [show (3 : ℕ) = 2+1 from rfl, pow_succ, pow_two] at hprod
    obtain ⟨xy, hxy, z, hz, heq⟩ := hprod
    obtain ⟨x, hx, y, hy, hxy⟩ := hxy
    subst xy
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hyj⟩ := hy
    obtain ⟨k, hk, hzk⟩ := hz
    have signs : ∀ n x, x ∈ B n → ∃ b : Bool, x = signed b (v n) := by
      intro n x hx
      rcases hx with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨a, rfl⟩ := signs i x hxi
    obtain ⟨b, rfl⟩ := signs j y hyj
    obtain ⟨c, rfl⟩ := signs k z hzk
    change max Nm Np + 1 ≤ i at hi
    change max Nm Np + 1 ≤ j at hj
    change max Nm Np + 1 ≤ k at hk
    by_cases hall : i = j ∧ j = k
    · have hij := hall.1
      have hki : k = i := (hall.1.trans hall.2).symm
      rw [← hij, hki] at heq
      exact hNp i (by omega) ![a,b,c] heq
    · apply hNm ![i,j,k] ![a,b,c] _ hall heq
      intro l
      fin_cases l <;> simp <;> omega
  have htwo : (⋂ q, (A q)^2).Nonempty := by
    refine ⟨1, Set.mem_iInter.mpr ?_⟩
    intro q
    rw [pow_two]
    refine ⟨v q.val, ⟨q.val, le_rfl, Or.inl rfl⟩,
      (v q.val)⁻¹, ⟨q.val, le_rfl, Or.inr rfl⟩, ?_⟩
    exact mul_inv_cancel _
  exact ⟨A, hasd, spectrum_separation A hcore 3 2 (by decide) (by decide) (by decide) hthree htwo⟩

end D5.S3.Combinatorics.GroupWords.NathansonProblem9

namespace D5.S3.Combinatorics.GroupWords.NathansonProblem9
open Set
open scoped Pointwise

/-- Every infinite group has a nontrivial proper positive product intersection spectrum. -/
theorem result {G : Type*} [Group G] [Infinite G] :
    ∃ A : ℕ+ → Set G, ASD A ∧ spectrum A ≠ {1} ∧ spectrum A ≠ {h : ℕ | 0 < h} := by
  classical
  by_cases hC : (Set.range (fun x : G => x^3)).Finite
  · exact finite_cube_range_case hC
  · exact infinite_cube_range_case hC

end D5.S3.Combinatorics.GroupWords.NathansonProblem9
