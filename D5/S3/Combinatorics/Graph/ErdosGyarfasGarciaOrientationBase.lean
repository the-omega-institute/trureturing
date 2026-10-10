/- GID: D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationBase
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Parametric affine replacement infrastructure for Garcia orientation certificates. -/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Tactic
import D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationAveraging
import D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationExpansion

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationBase

open Finset
open D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationAveraging
open D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationExpansion

private def scalarAut {p : ℕ} (x : (ZMod p)ˣ) : MulAut (Multiplicative (ZMod p)) :=
  (show ZMod p ≃+ ZMod p from
    { toFun := fun y => (x : ZMod p) * y
      invFun := fun y => (↑x⁻¹ : ZMod p) * y
      left_inv := by intro y; simp [-ZMod.inv_coe_unit]
      right_inv := by intro y; simp [-ZMod.inv_coe_unit]
      map_add' := by intro y z; exact mul_add _ _ _ }).toMultiplicative

private def scalarAction {p : ℕ} : (ZMod p)ˣ →* MulAut (Multiplicative (ZMod p)) where
  toFun := scalarAut
  map_one' := by ext y; simp [-ZMod.inv_coe_unit, scalarAut]
  map_mul' := by intro x z; ext y; simp [-ZMod.inv_coe_unit, scalarAut, mul_assoc]

abbrev Affine (p : ℕ) := SemidirectProduct (Multiplicative (ZMod p)) ((ZMod p)ˣ) scalarAction

private instance affineFintype {p : ℕ} [Fact (Nat.Prime p)] : Fintype (Affine p) :=
  Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

private def multiplier (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ) : (ZMod p)ˣ :=
  if h : (a : ZMod p) ≠ 0 then Units.mk0 (a : ZMod p) h else 1

def generator {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ) (j : Fin 3) : Affine p :=
  if j = 0 then ⟨Multiplicative.ofAdd 0, -1⟩
  else if j = 1 then ⟨Multiplicative.ofAdd 1, multiplier p a⟩
  else (⟨Multiplicative.ofAdd 1, multiplier p a⟩ : Affine p)⁻¹

def inverseType (j : Fin 3) : Fin 3 := if j = 0 then 0 else if j = 1 then 2 else 1

private theorem generator_inverse {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ) (j : Fin 3) :
    generator (p := p) a (inverseType j) = (generator a j)⁻¹ := by
  fin_cases j
  · apply SemidirectProduct.ext
    · change (0 : ZMod p) = (↑(-1 : (ZMod p)ˣ)⁻¹ : ZMod p) * (-0)
      simp only [neg_zero, mul_zero]
    · change (-1 : (ZMod p)ˣ) = (-1 : (ZMod p)ˣ)⁻¹
      simp [-ZMod.inv_coe_unit]
  · rfl
  · change (⟨Multiplicative.ofAdd 1, multiplier p a⟩ : Affine p) =
      (⟨Multiplicative.ofAdd 1, multiplier p a⟩ : Affine p)⁻¹⁻¹
    exact (inv_inv _).symm

def cycleVertex {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ) (w : Fin 14 → Fin 3) (i : Fin 14) : Affine p :=
  ((List.ofFn w).take i.val).foldl (fun x j => x * generator a j) 1

def outgoing (w : Fin 14 → Fin 3) (i : Fin 14) : Fin 3 := w i

def incoming (w : Fin 14 → Fin 3) (i : Fin 14) : Fin 3 := inverseType (outgoing w (i - 1))

def unused (w : Fin 14 → Fin 3) (i : Fin 14) : Fin 3 :=
  if outgoing w i ≠ 0 ∧ incoming w i ≠ 0 then 0
  else if outgoing w i ≠ 1 ∧ incoming w i ≠ 1 then 1 else 2

private def h7Edges : List (ℕ × ℕ) :=
  [(1, 3), (3, 4), (4, 2), (5, 1), (2, 6), (3, 5), (5, 0), (0, 6), (6, 4)]

private def h15Edges : List (ℕ × ℕ) :=
  h7Edges ++ h7Edges.map (fun e => (e.1 + 7, e.2 + 7)) ++
    [(1, 8), (2, 14), (14, 9)]

private def h15Adj (x y : Fin 15) : Prop :=
  (x.val, y.val) ∈ h15Edges ∨ (y.val, x.val) ∈ h15Edges

private instance : DecidableRel h15Adj := by
  intro x y
  unfold h15Adj
  infer_instance

private def H15 : SimpleGraph (Fin 15) where
  Adj := h15Adj
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel H15.Adj := fun _ _ => inferInstanceAs (Decidable (h15Adj _ _))

private def port (p : Fin 3) : Fin 15 :=
  if p = 0 then 14 else if p = 1 then 7 else 0

private def path (p q : Fin 3) (short : Bool) : List (Fin 15) :=
  if p = q then [] else
  if p = 0 then
    if q = 1 then
      if short then [14, 9, 13, 7] else [14, 9, 11, 10, 12, 7]
    else if short then [14, 2, 6, 0] else [14, 2, 4, 3, 5, 0]
  else if q = 0 then
    if p = 1 then
      if short then [7, 13, 9, 14] else [7, 12, 10, 11, 9, 14]
    else if short then [0, 6, 2, 14] else [0, 5, 3, 4, 2, 14]
  else if p = 1 then [7, 12, 8, 1, 5, 0] else [0, 5, 1, 8, 12, 7]

private theorem path_length (p q : Fin 3) (short : Bool) (hd : p ≠ q)
    (hs : short = true → p = 0 ∨ q = 0) :
    (path p q short).length = if short then 4 else 6 := by
  revert hd hs
  fin_cases p <;> fin_cases q <;> cases short <;> decide

private theorem path_head (p q : Fin 3) (short : Bool) (hd : p ≠ q) :
    (path p q short).head? = some (port p) := by
  revert hd
  fin_cases p <;> fin_cases q <;> cases short <;> decide

private theorem path_last (p q : Fin 3) (short : Bool) (hd : p ≠ q) :
    (path p q short).getLast? = some (port q) := by
  revert hd
  fin_cases p <;> fin_cases q <;> cases short <;> decide

private theorem path_nodup (p q : Fin 3) (short : Bool) :
    (path p q short).Nodup := by
  fin_cases p <;> fin_cases q <;> cases short <;> decide

private theorem path_chain (p q : Fin 3) (short : Bool) :
    (path p q short).IsChain H15.Adj := by
  fin_cases p <;> fin_cases q <;> cases short <;> decide

private def base {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ) : SimpleGraph (Affine p) :=
  SimpleGraph.mulCayley (Set.range (generator a))

def replacement {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ) (tau : Affine p → (Fin 3 ≃ Fin 3)) :
    SimpleGraph (Affine p × Fin 15) :=
  SimpleGraph.fromRel (fun x y =>
    (x.1 = y.1 ∧ H15.Adj x.2 y.2) ∨
    ((base a).Adj x.1 y.1 ∧ ∃ j : Fin 3,
      y.1 = x.1 * generator a j ∧ x.2 = port (tau x.1 j) ∧
      y.2 = port (tau y.1 (inverseType j)) ∧
      x.1 = y.1 * generator a (inverseType j)))

theorem refutes_of_certificates {p : ℕ} [Fact (Nat.Prime p)] (a : ℕ)
    (w4 w6 : Fin 14 → Fin 3)
    (h4inj : Function.Injective (cycleVertex (p := p) a w4))
    (h4step : ∀ i, cycleVertex (p := p) a w4 (i + 1) = cycleVertex (p := p) a w4 i * generator a (outgoing w4 i))
    (h4types : ∀ i, outgoing w4 i ≠ incoming w4 i ∧
      ∀ j, j ≠ unused w4 i ↔ j = outgoing w4 i ∨ j = incoming w4 i)
    (h4hist : ∀ j : Fin 3, (∑ i : Fin 14, if unused w4 i = j then 1 else 0 : ℕ) =
      if j = 0 then 6 else 4)
    (h6inj : Function.Injective (cycleVertex (p := p) a w6))
    (h6step : ∀ i, cycleVertex (p := p) a w6 (i + 1) = cycleVertex (p := p) a w6 i * generator a (outgoing w6 i))
    (h6types : ∀ i, outgoing w6 i ≠ incoming w6 i ∧
      ∀ j, j ≠ unused w6 i ↔ j = outgoing w6 i ∨ j = incoming w6 i)
    (h6hist : ∀ j : Fin 3, (∑ i : Fin 14, if unused w6 i = j then 1 else 0 : ℕ) =
      if j = 0 then 2 else 6) :
    ¬ (∃ sigma : Affine p → Fin 3, ∃ tau : Affine p → (Fin 3 ≃ Fin 3),
      (∀ v, tau v (sigma v) = 0) ∧
      ∀ v : Affine p × Fin 15, ∀ q : (replacement a tau).Walk v v,
        q.IsCycle → q.length ≠ 64) := by
  classical
  rintro ⟨sigma, tau, htau, havoid⟩
  have lift (w : Fin 14 → Fin 3) (hinj : Function.Injective (cycleVertex (p := p) a w))
      (hstep : ∀ i, cycleVertex (p := p) a w (i + 1) = cycleVertex (p := p) a w i * generator a (outgoing w i))
      (htypes : ∀ i, outgoing w i ≠ incoming w i ∧
        ∀ j, j ≠ unused w i ↔ j = outgoing w i ∨ j = incoming w i)
      (h : Affine p) (six : Bool)
      (hu : 10 ≤ uCount (fun x y : Affine p => x * y) sigma
        (cycleVertex (p := p) a w) (unused w) h) :
      ∃ v : Affine p × Fin 15, ∃ q : (replacement a tau).Walk v v,
        q.IsCycle ∧ q.length = 64 := by
    let c (i : Fin 14) : Affine p := h * cycleVertex (p := p) a w i
    have cinj : Function.Injective c := by
      intro i j hij
      exact hinj (mul_left_cancel hij)
    let eligible : Finset (Fin 14) := univ.filter (fun i => sigma (c i) ≠ unused w i)
    have helig : 10 ≤ eligible.card := by
      change 10 ≤ (univ.filter (fun i : Fin 14 => sigma (c i) ≠ unused w i)).card
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact hu
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq helig
    let ptype (i : Fin 14) : Fin 3 := tau (c i) (incoming w i)
    let qtype (i : Fin 14) : Fin 3 := tau (c i) (outgoing w i)
    let short (i : Fin 14) : Bool := decide (i ∈ S)
    have hd (i : Fin 14) : ptype i ≠ qtype i := by
      intro hh
      exact (htypes i).1 ((tau (c i)).injective hh).symm
    have hs (i : Fin 14) : short i = true → ptype i = 0 ∨ qtype i = 0 := by
      intro hi
      have him : i ∈ S := by simpa [short] using hi
      have hu := (Finset.mem_filter.mp (hS him)).2
      rcases ((htypes i).2 (sigma (c i))).mp hu with hh | hh
      · right; simpa [qtype, hh] using htau (c i)
      · left; simpa [ptype, hh] using htau (c i)
    let blocks (i : Fin 14) : List (Affine p × Fin 15) :=
      (path (ptype i) (qtype i) (short i)).map (fun z => (c i, z))
    have bhead (i : Fin 14) : (blocks i).head? = some (c i, port (ptype i)) := by
      simp [blocks, path_head _ _ _ (hd i)]
    have blast (i : Fin 14) : (blocks i).getLast? = some (c i, port (qtype i)) := by
      simp [blocks, path_last _ _ _ (hd i)]
    have bn (i : Fin 14) : blocks i ≠ [] := by
      intro hh; have hhh := bhead i; rw [hh] at hhh; simp at hhh
    have bnodup (i : Fin 14) : (blocks i).Nodup := by
      apply List.Nodup.map (fun z w hh => by exact congrArg Prod.snd hh)
      exact path_nodup _ _ _
    have bchain (i : Fin 14) : (blocks i).IsChain (replacement a tau).Adj := by
      apply List.isChain_map_of_isChain
      · intro z w hzw
        simp only [replacement, SimpleGraph.fromRel]
        exact ⟨fun hh => H15.ne_of_adj hzw (congrArg Prod.snd hh), Or.inl (Or.inl ⟨by trivial, hzw⟩)⟩
      · exact path_chain _ _ _
    have bdisjoint (i j : Fin 14) (hij : i ≠ j) : List.Disjoint (blocks i) (blocks j) := by
      intro z hzi hzj
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hzi
      obtain ⟨y, hy, hye⟩ := List.mem_map.mp hzj
      exact hij (cinj (by simpa using congrArg Prod.fst (hxe.trans hye.symm)))
    have step (i : Fin 14) : c (i + 1) = c i * generator a (outgoing w i) := by
      simp only [c, hstep, mul_assoc]
    have nextincoming (i : Fin 14) : incoming w (finRotate 14 i) = inverseType (outgoing w i) := by
      simp [incoming, finRotate_apply]
    have bedge (i : Fin 14) : ∀ x ∈ (blocks i).getLast?, ∀ y ∈ (blocks (finRotate 14 i)).head?,
        (replacement a tau).Adj x y := by
      rw [blast, bhead]; intro x hx y hy
      simp only [Option.mem_some_iff] at hx hy; subst x; subst y
      have hneq : c i ≠ c (finRotate 14 i) := by
        intro hh
        have heq := cinj hh
        have hrot : i ≠ finRotate 14 i := by simp [finRotate_apply, eq_comm]
        exact hrot heq
      have hnext : c (finRotate 14 i) = c i * generator a (outgoing w i) := by
        simpa [finRotate_apply] using step i
      simp only [replacement, SimpleGraph.fromRel]
      refine ⟨fun hh => hneq (congrArg Prod.fst hh), Or.inl (Or.inr ⟨?_, ?_⟩)⟩
      · apply (SimpleGraph.mulCayley_adj' _ _ _).mpr
        exact ⟨hneq, generator a (outgoing w i), ⟨outgoing w i, rfl⟩, Or.inl hnext.symm⟩
      · refine ⟨outgoing w i, hnext, rfl, ?_, ?_⟩
        · change port (tau (c (finRotate 14 i)) (incoming w (finRotate 14 i))) = _; rw [nextincoming]
        · rw [hnext, generator_inverse]; simp [mul_assoc]
    have blength (i : Fin 14) : (blocks i).length = if i ∈ S then 4 else 6 := by
      simpa [blocks, short] using path_length (ptype i) (qtype i) (short i) (hd i) (hs i)
    have total : (∑ i, (blocks i).length) = 64 := by
      simp_rw [blength]
      have hc : (univ.filter (fun i : Fin 14 => i ∈ S)) = S := by ext i; simp
      have hnc : (univ.filter (fun i : Fin 14 => i ∉ S)) = univ \ S := by ext i; simp
      rw [Finset.sum_ite, hc, hnc]; simp [Finset.card_sdiff, hcard]
    obtain ⟨v, q, hq, hqlen⟩ := cycle_of_disjoint_blocks (replacement a tau)
      (n := 13) blocks bn bnodup bchain bdisjoint bedge (by rw [total]; decide)
    exact ⟨v, q, hq, hqlen.trans total⟩
  obtain ⟨h, hh⟩ := exists_many_u (fun x y : Affine p => x * y)
    (fun v => ⟨mul_left_injective v, fun z => ⟨z * v⁻¹, by simp⟩⟩)
    (Fintype.card_pos_iff.mpr ⟨1⟩) sigma
    (cycleVertex (p := p) a w4) (cycleVertex (p := p) a w6) (unused w4) (unused w6)
    h4hist h6hist
  have hcycle := hh.elim
    (lift w4 h4inj h4step h4types h false)
    (lift w6 h6inj h6step h6types h true)
  obtain ⟨v, q, hq, hlen⟩ := hcycle
  exact havoid v q hq hlen

end D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationBase
