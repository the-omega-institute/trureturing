/- GID: D5/S3/Combinatorics/Partitions/SpechtThreeRowGram
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtThreeRowGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint ordered-colouring characters have a finite three-by-three contingency Gram matrix. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors of the selected supplier: The Tau Ceti contributors.
The three private counting suppliers are selected A17.2PORT from
TauCeti/GroupTheory/Perm/FiberSubgroup.lean at
5a01f5fe3621126cccf9ba22e700493cbc7b7156. Their proof bodies are unchanged.
The joint integer-margin counting argument and signed-character comparison are local.
See Library/FiniteGroups/tauceti2026spechtpolytabloids.md for the existing full
license, attribution, no-NOTICE assessment and retirement against OUR Mathlib pin.
Source only: native elaboration, axiom closure, proof-term liveness and admission
are not established. Unfinished audit: https://github.com/the-omega-institute/trureturing/issues/24542.
No standalone firstfreeze is asserted. utility none: arbitrary degree, not a bounded instance.
-/
import D5.S3.Combinatorics.Partitions.SpechtYoungTrace
import Mathlib.Algebra.Order.Antidiag.Pi

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti
open _root_.Equiv _root_.Equiv.Perm Finset

section CountingSupplier
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
private theorem natCard_fiberSubgroup (f : α → ι) :
    Nat.card (fiberSubgroup f) = ∏ i, (#{a | f a = i}).factorial := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun σ => by
      rw [mem_fiberSubgroup, funext_iff]; rfl :
      fiberSubgroup f ≃ {g : Equiv.Perm α // f ∘ g = f}),
    Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
  simp only [Fintype.card_subtype]

/-- **Every distribution of the points of `α` among the colours is the fiber-size function of some
colouring**: a function `d : ι → ℕ` with total `card α` is `i ↦ #{a | f a = i}` for some
`f : α → ι`. -/
private theorem exists_forall_card_filter_eq {d : ι → ℕ} (hd : ∑ i, d i = Fintype.card α) :
    ∃ f : α → ι, ∀ i, #{a | f a = i} = d i := by
  -- label the points of `α` by the points of `Σ i, Fin (d i)` and colour each by its block
  let e := Fintype.equivOfCardEq (show Fintype.card α = Fintype.card (Σ i, Fin (d i)) by
    simp [hd])
  refine ⟨fun a => (e a).1, fun i => ?_⟩
  rw [← Fintype.card_subtype, Fintype.card_congr (e.subtypeEquiv fun a => Iff.rfl :
      {a // (e a).1 = i} ≃ {x : Σ i, Fin (d i) // x.1 = i}),
    Fintype.card_congr (Equiv.sigmaSubtype i), Fintype.card_fin]

/-- **Summing the orders of the fiber subgroups over all colourings**, each colouring weighted by
a function of its fiber sizes: the colourings with a given fiber-size function `d` form one orbit
of `Equiv.Perm α`, whose stabilizers are their fiber subgroups, so together they contribute
`(card α)!` times the weight of `d`, and every `d` of total `card α` occurs. -/
private theorem sum_natCard_fiberSubgroup_smul [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (F : (ι → ℕ) → M) :
    ∑ f : α → ι, Nat.card (fiberSubgroup f) • F (fun i => #{a | f a = i}) =
      (Fintype.card α).factorial • ∑ d ∈ piAntidiag univ (Fintype.card α), F d := by
  set c : (α → ι) → ι → ℕ := fun f i => #{a | f a = i} with hc_def
  have hc : ∀ f ∈ (univ : Finset (α → ι)), c f ∈ piAntidiag univ (Fintype.card α) :=
    fun f _ => by
      rw [mem_piAntidiag]
      refine ⟨?_, fun i _ => mem_univ i⟩
      rw [hc_def]
      exact (card_eq_sum_card_fiberwise fun a _ => mem_univ (f a)).symm
  -- group the colourings by their fiber-size functions
  rw [← sum_fiberwise_of_maps_to hc, smul_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_congr rfl fun f hf => by
    rw [show (fun i => #{a | f a = i}) = d from (mem_filter.1 hf).2], ← sum_smul]
  congr 1
  -- the colourings with fiber sizes `d` are the rearrangements of one of them, `f₀`
  obtain ⟨f₀, hf₀⟩ := exists_forall_card_filter_eq (α := α) ((mem_piAntidiag.1 hd).1)
  have hfib : ∀ f ∈ univ.filter fun f => c f = d,
      Nat.card (fiberSubgroup f) = Nat.card (fiberSubgroup f₀) := fun f hf => by
    rw [natCard_fiberSubgroup, natCard_fiberSubgroup]
    exact prod_congr rfl fun i _ => by
      rw [show #{a | f a = i} = d i from congrFun (mem_filter.1 hf).2 i, hf₀]
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul]
  have hq : #(univ.filter fun f => c f = d) = Nat.card (Equiv.Perm α ⧸ fiberSubgroup f₀) := by
    rw [Nat.card_congr (quotientFiberSubgroupEquiv f₀), ← Fintype.card_subtype,
      Nat.card_eq_fintype_card]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    rw [hc_def, funext_iff]
    refine forall_congr' fun i => ?_
    rw [← hf₀ i]
    -- the two sides differ only in the instance deciding equality of colours
    convert Iff.rfl
  rw [hq, ← Subgroup.card_eq_card_quotient_mul_card_subgroup, Nat.card_eq_fintype_card,
    Fintype.card_perm]


end CountingSupplier

namespace ThreeRowGram

/-- Ordered colours retain their labels even when two sizes agree or a size is zero. -/
def Colourings (n : ℕ) (a : Fin 3 → ℤ) :=
  {f : Fin n → Fin 3 // ∀ i, (#{x | f x = i} : ℤ) = a i}

/-- A negative margin gives no colourings; no integer-to-natural truncation occurs. -/
def fixedColourings {n : ℕ} (a : Fin 3 → ℤ) (π : Perm (Fin n)) : ℕ :=
  #{f : Fin n → Fin 3 | f ∘ π = f ∧ ∀ i, (#{x | f x = i} : ℤ) = a i}

instance colouringsFinite (n : ℕ) (a : Fin 3 → ℤ) : Finite (Colourings n a) :=
  inferInstanceAs (Finite {f : Fin n → Fin 3 // ∀ i, (#{x | f x = i} : ℤ) = a i})

instance colouringsMulAction (n : ℕ) (a : Fin 3 → ℤ) : MulAction (Perm (Fin n)) (Colourings n a) where
  smul π f := ⟨f.1 ∘ (π⁻¹ : Perm (Fin n)), fun i => by
    rw [show #{x | (f.1 ∘ (π⁻¹ : Perm (Fin n))) x = i} = #{x | f.1 x = i} from
      card_filter_comp_perm f.1 π⁻¹ i]
    exact f.2 i⟩
  one_smul f := by apply Subtype.ext; rfl
  mul_smul π τ f := by
    apply Subtype.ext
    funext x
    simp only [Function.comp_apply, mul_inv_rev, Equiv.Perm.mul_apply]

/-- This is the actual representation on the ordered colourings, independently of its character. -/
abbrev colouringRepresentation (n : ℕ) (a : Fin 3 → ℤ) : _root_.FDRep ℂ (Perm (Fin n)) :=
  _root_.FDRep.of (Representation.ofMulAction ℂ (Perm (Fin n)) (Colourings n a))

private theorem colouring_fixed_iff {n : ℕ} (a : Fin 3 → ℤ) (π : Perm (Fin n))
    (f : Colourings n a) : π • f = f ↔ f.1 ∘ π = f.1 := by
  change (⟨f.1 ∘ (π⁻¹ : Perm (Fin n)), _⟩ : Colourings n a) = f ↔ _
  rw [Subtype.ext_iff]
  constructor
  · intro h
    funext x
    have hx := congrFun h (π x)
    change f.1 (π.symm (π x)) = f.1 (π x) at hx
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hx.symm
  · intro h
    funext x
    have hx := congrFun h (π⁻¹ x)
    change f.1 (π (π.symm x)) = f.1 (π.symm x) at hx
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx.symm

/-- The ordered-colouring count is a trace of the actual permutation representation. -/
theorem character_colouringRepresentation {n : ℕ} (a : Fin 3 → ℤ) (π : Perm (Fin n)) :
    (colouringRepresentation n a).character π = (fixedColourings a π : ℂ) := by
  classical
  change (Representation.ofMulAction ℂ (Perm (Fin n)) (Colourings n a)).character π = _
  rw [char_ofMulAction]
  congr 1
  rw [fixedColourings, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (((Equiv.subtypeEquivRight fun f : Colourings n a =>
    colouring_fixed_iff a π f).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun f : Fin n → Fin 3 => f ∘ π = f))).trans ?_)
  exact Equiv.subtypeEquivRight fun _ => and_comm

/-- Entries have total n; the row and column equations are integer equations. -/
def contingencyTables (n : ℕ) (a b : Fin 3 → ℤ) : Finset (Fin 3 × Fin 3 → ℕ) :=
  (piAntidiag univ n).filter fun A =>
    (∀ i, ((∑ j, A (i, j) : ℕ) : ℤ) = a i) ∧
    (∀ j, ((∑ i, A (i, j) : ℕ) : ℤ) = b j)

def contingencyCount (n : ℕ) (a b : Fin 3 → ℤ) : ℕ :=
  (contingencyTables n a b).card

private theorem paired_fixed_count {n : ℕ} (a b : Fin 3 → ℤ) (π : Perm (Fin n)) :
    fixedColourings a π * fixedColourings b π =
      #{h : Fin n → Fin 3 × Fin 3 | h ∘ π = h ∧
        (∀ i, (#{x | (h x).1 = i} : ℤ) = a i) ∧
        (∀ j, (#{x | (h x).2 = j} : ℤ) = b j)} := by
  classical
  rw [fixedColourings, fixedColourings, ← card_product]
  apply card_equiv (arrowProdEquivProdArrow (Fin n) (fun _ => Fin 3) (fun _ => Fin 3)).symm
  intro x
  simp only [mem_product, mem_filter, mem_univ, true_and, funext_iff,
    Function.comp_apply, arrowProdEquivProdArrow, coe_fn_symm_mk, Prod.ext_iff, forall_and]
  tauto

private theorem paired_fixed_sum {n : ℕ} (a b : Fin 3 → ℤ) (π : Perm (Fin n)) :
    fixedColourings a π * fixedColourings b π =
      ∑ h : Fin n → Fin 3 × Fin 3,
        if h ∘ π = h ∧
          (∀ i, (#{x | (h x).1 = i} : ℤ) = a i) ∧
          (∀ j, (#{x | (h x).2 = j} : ℤ) = b j) then (1 : ℕ) else 0 := by
  rw [← sum_filter, ← card_eq_sum_ones]
  exact paired_fixed_count a b π

/-- Both fixed-point conditions use the same permutation. Pairing the two colourings
and grouping by the nine joint fibre sizes proves the unnormalised Gram identity. -/
theorem sum_fixedColourings_mul (n : ℕ) (a b : Fin 3 → ℤ) :
    ∑ π : Perm (Fin n), fixedColourings a π * fixedColourings b π =
      n.factorial * contingencyCount n a b := by
  classical
  let F : (Fin 3 × Fin 3 → ℕ) → ℕ := fun A =>
    if (∀ i, ((∑ j, A (i, j) : ℕ) : ℤ) = a i) ∧
       (∀ j, ((∑ i, A (i, j) : ℕ) : ℤ) = b j) then 1 else 0
  have hrow (h : Fin n → Fin 3 × Fin 3) (i : Fin 3) :
      #{x | (h x).1 = i} = ∑ j, #{x | h x = (i, j)} := by
    rw [card_eq_sum_card_fiberwise (f := fun x => (h x).2) (t := univ) fun _ _ => mem_univ _]
    apply sum_congr rfl
    intro j _
    rw [filter_filter]
    exact congrArg card (filter_congr fun x _ => by simp [Prod.ext_iff])
  have hcol (h : Fin n → Fin 3 × Fin 3) (j : Fin 3) :
      #{x | (h x).2 = j} = ∑ i, #{x | h x = (i, j)} := by
    rw [card_eq_sum_card_fiberwise (f := fun x => (h x).1) (t := univ) fun _ _ => mem_univ _]
    apply sum_congr rfl
    intro i _
    rw [filter_filter]
    exact congrArg card (filter_congr fun x _ => by simp [Prod.ext_iff, and_comm])
  have hstab (h : Fin n → Fin 3 × Fin 3) :
      ∑ π : Perm (Fin n),
        (if h ∘ π = h ∧
          (∀ i, (#{x | (h x).1 = i} : ℤ) = a i) ∧
          (∀ j, (#{x | (h x).2 = j} : ℤ) = b j) then (1 : ℕ) else 0) =
      Nat.card (fiberSubgroup h) • F (fun k => #{x | h x = k}) := by
    have hc : Nat.card (fiberSubgroup h) = #{π : Perm (Fin n) | h ∘ π = h} := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun π => by
        rw [mem_fiberSubgroup, funext_iff]; rfl)
    simp only [F, ← hrow, ← hcol, hc]
    split_ifs with hm
    · simp only [hm, forall_const, and_true]
      rw [← sum_filter, sum_const]
    · simp [hm]
  simp_rw [paired_fixed_sum]
  rw [sum_comm]
  simp_rw [hstab]
  rw [sum_natCard_fiberSubgroup_smul]
  simp only [F, nsmul_eq_mul, Fintype.card_fin]
  congr 1
  simp [contingencyCount, contingencyTables, sum_boole]

/-- The same identity with actual complex traces of ordered permutation modules. -/
theorem sum_colouringTrace_mul (n : ℕ) (a b : Fin 3 → ℤ) :
    ∑ π : Perm (Fin n),
      (colouringRepresentation n a).character π * (colouringRepresentation n b).character π =
      (n.factorial : ℂ) * (contingencyCount n a b : ℂ) := by
  simp_rw [character_colouringRepresentation]
  exact_mod_cast sum_fixedColourings_mul n a b

/-- All shifts are performed in Z. -/
def shifted (μ : Fin 3 → ℕ) (σ : Perm (Fin 3)) (i : Fin 3) : ℤ :=
  (μ i : ℤ) - (i : ℕ) + (σ i : ℕ)

def virtualCharacter (n : ℕ) (μ : Fin 3 → ℕ) (π : Perm (Fin n)) : ℤ :=
  ∑ σ : Perm (Fin 3), (sign σ : ℤ) * (fixedColourings (shifted μ σ) π : ℤ)

def signedContingencyGram (n : ℕ) (μ ν : Fin 3 → ℕ) : ℤ :=
  ∑ σ : Perm (Fin 3), ∑ τ : Perm (Fin 3),
    (sign σ : ℤ) * (sign τ : ℤ) *
      (contingencyCount n (shifted μ σ) (shifted ν τ) : ℤ)

/-- The finite signed six-by-six contingency sum is the Gram matrix of the
actual signed permutation characters in every degree. -/
theorem sum_virtualCharacter_mul (n : ℕ) (μ ν : Fin 3 → ℕ) :
    ∑ π : Perm (Fin n), virtualCharacter n μ π * virtualCharacter n ν π =
      (n.factorial : ℤ) * signedContingencyGram n μ ν := by
  classical
  simp only [virtualCharacter, signedContingencyGram]
  simp_rw [sum_mul]
  simp_rw [mul_sum]
  calc
    _ = ∑ σ : Perm (Fin 3), ∑ τ : Perm (Fin 3), ∑ π : Perm (Fin n),
        (sign σ : ℤ) * (fixedColourings (shifted μ σ) π : ℤ) *
          ((sign τ : ℤ) * (fixedColourings (shifted ν τ) π : ℤ)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro σ _
      rw [sum_comm]
    _ = ∑ σ : Perm (Fin 3), ∑ τ : Perm (Fin 3),
        (sign σ : ℤ) * (sign τ : ℤ) *
          ((n.factorial : ℤ) * (contingencyCount n (shifted μ σ) (shifted ν τ) : ℤ)) := by
      apply sum_congr rfl
      intro σ _
      apply sum_congr rfl
      intro τ _
      have hz : (∑ π : Perm (Fin n),
          (fixedColourings (shifted μ σ) π : ℤ) *
          (fixedColourings (shifted ν τ) π : ℤ)) =
          (n.factorial : ℤ) * (contingencyCount n (shifted μ σ) (shifted ν τ) : ℤ) := by
        have hc := sum_colouringTrace_mul n (shifted μ σ) (shifted ν τ)
        simp only [character_colouringRepresentation] at hc
        exact_mod_cast hc
      calc
        _ = (sign σ : ℤ) * (sign τ : ℤ) *
            ∑ π : Perm (Fin n),
              (fixedColourings (shifted μ σ) π : ℤ) *
              (fixedColourings (shifted ν τ) π : ℤ) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro π _
          ring
        _ = _ := by rw [hz]
    _ = _ := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro σ _
      apply sum_congr rfl
      intro τ _
      ring

end ThreeRowGram
end TauCeti
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
