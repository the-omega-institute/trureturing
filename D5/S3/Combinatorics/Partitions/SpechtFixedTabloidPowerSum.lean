/- GID: D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-cycle power-sum coefficients count fixed tabloids over every finite alphabet. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected A17.2PORT from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: selected declarations and surrounding namespaces; exact pinned Mathlib
and existing D5 suppliers are reused. Library/FiniteGroups/tauceti2026spechtpolytabloids.md
records immutable locators, license, consumers and retirement against OUR Mathlib pin.
Historical initial source-stage status: no Lean/Lake invocation, native elaboration, axiom closure, proof-term
liveness, admission, validated Reg, emission, firstfreeze, deposit, PR or CI claim.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
These are necessary suppliers/comparisons for the full HSW target. No independent
firstfreeze or new-content qualification is claimed. Both original ordinary weighted
identities remain unfinished. No character is defined by a polynomial coefficient.
utility: none: arbitrary degrees and finite alphabets, no bounded enumeration.
-/
import D5.S3.Combinatorics.Partitions.SpechtMonomialCoordinates
import D5.S3.Combinatorics.Partitions.SpechtOrdinaryTrace
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Dynamics.PeriodicPts.Defs

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid

noncomputable section
open scoped BigOperators
namespace Function.Semiconj
variable {α γ : Type*} {σ : _root_.Equiv.Perm α} {τ : _root_.Equiv.Perm γ} {g : α → γ}

theorem perm_zpow_right (hg : Function.Semiconj g σ τ) (k : ℤ) :
    Function.Semiconj g ⇑(σ ^ k) ⇑(τ ^ k) := by
  intro z
  have hinv : Function.Semiconj g (σ⁻¹ : Equiv.Perm α) (τ⁻¹ : Equiv.Perm γ) :=
    Function.Semiconj.inverses_right hg σ.right_inv τ.left_inv
  cases k with
  | ofNat m =>
      simpa only [Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow] using
        (Function.Semiconj.iterate_right hg m z)
  | negSucc m =>
      simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow] using
        (Function.Semiconj.iterate_right hinv (m + 1) z)

end Function.Semiconj

namespace Equiv.Perm.SameCycle
variable {α : Type*} {β : Sort*} {σ : _root_.Equiv.Perm α} {x y : α} {f : α → β}

theorem apply_eq_of_apply_eq (hσ : σ.SameCycle x y) (hf : ∀ z, f (σ z) = f z) : f x = f y := by
  obtain ⟨k, rfl⟩ := hσ
  have hmap := Function.Semiconj.perm_zpow_right (τ := 1) (g := fun z => PLift.up (f z))
    (fun z => congrArg PLift.up (hf z)) k x
  exact congrArg PLift.down (by simpa only [one_zpow, Equiv.Perm.one_apply] using hmap.symm)

end Equiv.Perm.SameCycle

namespace TauCeti
open _root_.Equiv _root_.Equiv.Perm Finset MvPolynomial
open Equiv.Perm.SameCycle
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def fullCycleType (σ : Equiv.Perm α) : Multiset ℕ :=
  σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1

theorem fullCycleType_def (σ : Equiv.Perm α) :
    fullCycleType σ = σ.partition.parts := by
  rw [fullCycleType, Equiv.Perm.parts_partition]

open scoped Classical in
theorem fullCycleType_eq_map_card_filter {γ : Type*}
    (σ : Equiv.Perm α) (m : α → γ) (hm : ∀ x y, σ.SameCycle x y ↔ m x = m y) :
    fullCycleType σ =
      (Finset.univ.image m).val.map fun c => (Finset.univ.filter fun x => m x = c).card := by
  classical
  set T := Finset.univ.image m
  set fib : γ → ℕ := fun c => (Finset.univ.filter fun x => m x = c).card
  -- A value of `m` is either hit by the support of `σ` or only by fixed points.
  set R : γ → Prop := fun c => ∃ x ∈ σ.support, m x = c
  -- The values hit by the support match the cycle factors, each fibre being a cycle's support.
  have hcycle : (T.filter R).val.map fib = σ.cycleType := by
    rw [cycleType_def, Function.comp_def]
    refine (Multiset.map_eq_map_of_bij_of_nodup _ _ σ.cycleFactorsFinset.nodup
      (T.filter R).nodup
      (fun c hc => m (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose)
      ?_ ?_ ?_ ?_).symm
    · intro c hc
      have hx := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose_spec
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        _, mem_cycleFactorsFinset_support_le hc hx, rfl⟩
    · intro c hc d hd hcd
      have hx := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose_spec
      have hy := (mem_cycleFactorsFinset_iff.mp hd).1.nonempty_support.choose_spec
      rw [cycle_is_cycleOf hx hc, cycle_is_cycleOf hy hd]
      exact ((hm _ _).mpr hcd).cycleOf_eq
    · intro c hc
      obtain ⟨-, x, hx, rfl⟩ := Finset.mem_filter.mp hc
      have hmem : σ.cycleOf x ∈ σ.cycleFactorsFinset :=
        cycleOf_mem_cycleFactorsFinset_iff.mpr hx
      refine ⟨_, hmem, ?_⟩
      have hy := (mem_cycleFactorsFinset_iff.mp hmem).1.nonempty_support.choose_spec
      exact ((hm _ _).mp ((mem_support_cycleOf_iff' (mem_support.mp hx)).mp hy)).symm
    · intro c hc
      have hx := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose_spec
      set x := (mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support.choose
      have hxs : σ x ≠ x := mem_support.mp (mem_cycleFactorsFinset_support_le hc hx)
      rw [cycle_is_cycleOf hx hc]
      congr 1
      ext y
      rw [mem_support_cycleOf_iff' hxs, hm]
      simp [eq_comm]
  -- The remaining values are the images of the fixed points, each with a singleton fibre.
  have hfixed : (T.filter fun c => ¬ R c).val.map fib =
      Multiset.replicate (Fintype.card α - σ.support.card) 1 := by
    have himage : T.filter (fun c => ¬ R c) = σ.supportᶜ.image m := by
      ext c
      simp only [T, R, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_compl, not_exists, not_and]
      constructor
      · rintro ⟨⟨x, rfl⟩, hx⟩
        exact ⟨x, fun h => hx x h rfl, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, rfl⟩, fun y hy hxy => mem_support.mp hy
          (((hm y x).mpr hxy).apply_eq_self_iff.mpr (notMem_support.mp hx))⟩
    rw [himage, Multiset.eq_replicate]
    refine ⟨?_, fun n hn => ?_⟩
    · rw [Multiset.card_map, Finset.card_val, Finset.card_image_of_injOn, Finset.card_compl]
      intro x hx y _ hxy
      exact ((hm x y).mpr hxy).eq_of_left (notMem_support.mp (Finset.mem_compl.mp hx))
    · obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hn
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      refine Finset.card_eq_one.mpr ⟨x, ?_⟩
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      refine ⟨fun hxy => ?_, fun h => h ▸ rfl⟩
      exact (((hm x y).mpr hxy.symm).eq_of_left
        (notMem_support.mp (Finset.mem_compl.mp hx))).symm
  rw [fullCycleType, ← hcycle, ← hfixed, ← Multiset.map_add, Finset.filter_val,
    Finset.filter_val, Multiset.filter_add_not]

variable {σ : Type*}

def invariantColouringEquiv (π : Perm α) :
    (Quotient (SameCycle.setoid π) → σ) ≃ {f : α → σ // f ∘ π = f} where
  toFun g := ⟨fun a => g (Quotient.mk _ a), funext fun a =>
    congrArg g (Quotient.sound (sameCycle_apply_left.mpr (SameCycle.refl π a)))⟩
  invFun f := Quotient.lift f.1 fun _ _ h =>
    D5.S3.Combinatorics.Partitions.SpechtPolytabloid.Equiv.Perm.SameCycle.apply_eq_of_apply_eq h (congrFun f.2)
  left_inv _ := funext fun c => Quotient.inductionOn c fun _ => rfl
  right_inv _ := rfl

@[simp]
theorem invariantColouringEquiv_apply_coe (π : Perm α)
    (g : Quotient (SameCycle.setoid π) → σ) (a : α) :
    (invariantColouringEquiv π g : α → σ) a = g (Quotient.mk _ a) :=
  (rfl)

theorem card_filter_comp_perm {ι : Type*} [Fintype α] [DecidableEq ι]
    (f : α → ι) (g : Perm α) (i : ι) :
    (Finset.univ.filter fun a => f (g a) = i).card =
      (Finset.univ.filter fun a => f a = i).card :=
  Finset.card_equiv g fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]

variable {ι κ : Type*}

theorem fiberSubgroup_comp_of_injective {g : ι → κ} (hg : Function.Injective g) (f : α → ι) :
    fiberSubgroup (g ∘ f) = fiberSubgroup f := by
  ext σ
  simp only [mem_fiberSubgroup, Function.comp_apply, hg.eq_iff]

noncomputable local instance : DecidableEq ι := Classical.decEq ι

noncomputable def quotientFiberSubgroupEquiv (f : α → ι) :
    Equiv.Perm α ⧸ fiberSubgroup f ≃ {c : α → ι // ∀ i, #{a | c a = i} = #{a | f a = i}} :=
  Equiv.ofBijective
    (Quotient.lift (fun g : Equiv.Perm α => ⟨f ∘ ⇑g⁻¹, card_filter_comp_perm f g⁻¹⟩)
      fun g h hgh => Subtype.ext <| funext fun a => by
        have hk := mem_fiberSubgroup.mp (QuotientGroup.leftRel_apply.mp hgh)
        simpa only [Equiv.Perm.coe_inv, Function.comp_apply, Equiv.Perm.mul_apply,
          Equiv.apply_symm_apply] using hk (h⁻¹ a))
    ⟨fun p q => Quotient.inductionOn₂ p q fun g h hgh => by
      refine Quotient.sound (QuotientGroup.leftRel_apply.mpr (mem_fiberSubgroup.mpr fun a => ?_))
      have := congrFun (congrArg Subtype.val hgh) (h a)
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Quotient.lift_mk, Function.comp_apply,
        Equiv.symm_apply_apply] using this,
    fun c => by
      have hcard : ∀ i, Fintype.card {a // c.1 a = i} = Fintype.card {a // f a = i} := fun i => by
        rw [Fintype.card_subtype, Fintype.card_subtype, c.2 i]
      -- Matching the fibers of `c` with those of `f` produces `e` with `f ∘ e = c`.
      let e : Equiv.Perm α := Equiv.ofFiberEquiv fun i => Fintype.equivOfCardEq (hcard i)
      refine ⟨Quotient.mk _ e⁻¹, Subtype.ext (funext fun a => ?_)⟩
      exact (inv_inv e).symm ▸ Equiv.ofFiberEquiv_map _ a⟩

@[simp]
theorem quotientFiberSubgroupEquiv_mk (f : α → ι) (g : Equiv.Perm α) :
    (quotientFiberSubgroupEquiv f (g : Equiv.Perm α ⧸ fiberSubgroup f) : α → ι) = f ∘ ⇑g⁻¹ :=
  (rfl)

@[simp]
theorem quotientFiberSubgroupEquiv_smul (f : α → ι) (π : Equiv.Perm α)
    (q : Equiv.Perm α ⧸ fiberSubgroup f) :
    (quotientFiberSubgroupEquiv f (π • q) : α → ι) = quotientFiberSubgroupEquiv f q ∘ ⇑π⁻¹ :=
  QuotientGroup.induction_on q fun g => by
    rw [MulAction.Quotient.smul_mk, quotientFiberSubgroupEquiv_mk, quotientFiberSubgroupEquiv_mk,
      smul_eq_mul, mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_assoc]

@[simp]
theorem smul_eq_self_iff_quotientFiberSubgroupEquiv (f : α → ι) (π : Equiv.Perm α)
    (q : Equiv.Perm α ⧸ fiberSubgroup f) :
    π • q = q ↔ (quotientFiberSubgroupEquiv f q : α → ι) ∘ ⇑π = quotientFiberSubgroupEquiv f q := by
  rw [← (quotientFiberSubgroupEquiv f).apply_eq_iff_eq, Subtype.ext_iff,
    quotientFiberSubgroupEquiv_smul]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Function.comp_assoc, Equiv.Perm.coe_inv, Equiv.symm_comp_self, Function.comp_id]
  · intro h
    conv_lhs => rw [← h]
    rw [Function.comp_assoc, Equiv.Perm.coe_inv, Equiv.self_comp_symm, Function.comp_id]

theorem card_fixedPoints_quotient_fiberSubgroup [Fintype ι] (f : α → ι)
    (π : Equiv.Perm α) :
    Nat.card {q : Equiv.Perm α ⧸ fiberSubgroup f // π • q = q} =
      #{c : α → ι | c ∘ π = c ∧ ∀ i, #{a | c a = i} = #{a | f a = i}} := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (((quotientFiberSubgroupEquiv f).subtypeEquiv
    (q := fun c : {c : α → ι // ∀ i, #{a | c a = i} = #{a | f a = i}} => c.1 ∘ π = c.1)
    fun q =>
      smul_eq_self_iff_quotientFiberSubgroupEquiv f π q).trans ?_)
  exact (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun c : α → ι => c ∘ π = c)).trans
    (Equiv.subtypeEquivRight fun _ => and_comm)

section PowerSum
variable [Fintype σ] (R : Type*) [CommSemiring R]

theorem psumPart_isSymmetric [Fintype σ] {n : ℕ} (μ : n.Partition) :
    (psumPart σ R μ).IsSymmetric := by
  rw [psumPart]
  refine Multiset.prod_induction _ _ (fun _ _ => IsSymmetric.mul) IsSymmetric.one fun p hp => ?_
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hp
  exact psum_isSymmetric σ R k

noncomputable local instance : DecidableEq σ := Classical.decEq σ

theorem psumPart_partition_eq_sum_prod_X (π : Perm α) :
    psumPart σ R π.partition =
      ∑ f ∈ univ.filter fun f : α → σ => f ∘ π = f, ∏ a, X (f a) := by
  let m : α → Quotient (SameCycle.setoid π) := Quotient.mk _
  -- `TauCeti.fullCycleType_eq_map_card_filter` is stated with classical decidability; working with
  -- the same instance on the cycles keeps its fibre cardinalities literally the ones below.
  let _ : DecidableEq (Quotient (SameCycle.setoid π)) := fun a b => Classical.propDecidable (a = b)
  let _ : Fintype (Quotient (SameCycle.setoid π)) := Fintype.ofFinite _
  -- The parts of the cycle type are the sizes of the cycles, that is, of the fibres of `m`.
  have hparts : π.partition.parts =
      (univ : Finset (Quotient (SameCycle.setoid π))).val.map
        fun c => Fintype.card {a // m a = c} := by
    rw [← fullCycleType_def, fullCycleType_eq_map_card_filter π m
        fun x y => (@Quotient.eq _ (SameCycle.setoid π) x y).symm,
      image_univ_of_surjective Quotient.mk_surjective]
    exact Multiset.map_congr rfl fun c _ => (Fintype.card_subtype _).symm
  -- Expanding the product of power sums chooses one colour for each cycle.
  rw [psumPart, hparts, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  simp only [Function.comp_apply, psum]
  rw [Fintype.prod_sum, Finset.sum_subtype (univ.filter fun f : α → σ => f ∘ π = f)
    (p := fun f => f ∘ π = f) fun f => by rw [mem_filter, and_iff_right (mem_univ f)]]
  refine Fintype.sum_equiv (invariantColouringEquiv π) _ _ fun g => ?_
  simp only [invariantColouringEquiv_apply_coe]
  rw [← Fintype.prod_fiberwise' m fun c => X (g c)]
  exact Finset.prod_congr rfl fun c _ => by rw [Finset.prod_const, Finset.card_univ]

theorem coeff_psumPart_partition (π : Perm α) (d : σ →₀ ℕ) :
    (psumPart σ R π.partition).coeff d =
      #{f : α → σ | f ∘ π = f ∧ ∀ i, #{a | f a = i} = d i} := by
  classical
  have hX : ∀ f : α → σ, ∏ a, (X (f a) : MvPolynomial σ R) =
      monomial (Multiset.toFinsupp (univ.val.map f)) 1 := fun f => by
    rw [← prod_map_X_eq_monomial, Multiset.map_map]
    rfl
  have hcontent : ∀ f : α → σ,
      Multiset.toFinsupp (univ.val.map f) = d ↔ ∀ i, #{a | f a = i} = d i := fun f => by
    rw [Finsupp.ext_iff]
    refine forall_congr' fun i => ?_
    rw [Multiset.toFinsupp_apply, Multiset.count_map, Finset.card_def, Finset.filter_val]
    simp only [eq_comm]
  rw [psumPart_partition_eq_sum_prod_X, coeff_sum]
  simp only [hX, coeff_monomial, sum_boole, filter_filter, hcontent]

end PowerSum

noncomputable def youngBlockEquiv {n : ℕ} (μ : n.Partition)
    (i : Fin (μ.parts.sort (· ≥ ·)).length) :
    Fin ((μ.parts.sort (· ≥ ·))[(i : ℕ)]) ≃
      {j : Fin n // youngBlock μ j = i} :=
  Equiv.ofBijective
    (fun j => ⟨youngBlocksEquiv μ ⟨i, j⟩, youngBlock_youngBlocksEquiv μ ⟨i, j⟩⟩)
    ⟨by
      intro a b h
      have hs : (⟨i, a⟩ : Σ k, Fin ((μ.parts.sort (· ≥ ·)).get k)) = ⟨i, b⟩ :=
        (youngBlocksEquiv μ).injective (Subtype.ext_iff.mp h)
      cases hs
      rfl,
    by
      rintro ⟨j, hj⟩
      obtain ⟨⟨k, x⟩, rfl⟩ := (youngBlocksEquiv μ).surjective j
      simp only [youngBlock_youngBlocksEquiv] at hj
      subst k
      exact ⟨x, rfl⟩⟩

section FixedTabloids
variable [Fintype σ] (R : Type*) [CommSemiring R] {n : ℕ}

private theorem length_sort_parts_le (ν : n.Partition) (hν : ν.parts.card ≤ Fintype.card σ) :
    (ν.parts.sort (· ≥ ·)).length ≤ Fintype.card σ :=
  (Multiset.length_sort _).trans_le hν

theorem psumPart_eq_psumPart_partition {ρ : n.Partition} {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) :
    psumPart σ R ρ = psumPart σ R π.partition := by
  rw [psumPart, psumPart, ← (partitionEquivConjClasses n).symm_apply_apply ρ, ← hπ,
    parts_partitionEquivConjClasses_symm_mk]

private noncomputable def youngColouring (ν : n.Partition) (hν : ν.parts.card ≤ Fintype.card σ) :
    Fin n → σ :=
  (Fintype.equivFin σ).symm ∘ Fin.castLE (length_sort_parts_le ν hν) ∘ youngBlock ν

private theorem fiberSubgroup_youngColouring (ν : n.Partition)
    (hν : ν.parts.card ≤ Fintype.card σ) :
    fiberSubgroup (youngColouring ν hν) = youngSubgroup ν := by
  rw [youngColouring, ← Function.comp_assoc, youngSubgroup_eq_fiberSubgroup]
  exact fiberSubgroup_comp_of_injective
    ((Fintype.equivFin σ).symm.injective.comp (Fin.castLE_injective _)) _

private theorem card_filter_youngColouring [DecidableEq σ] (ν : n.Partition)
    (hν : ν.parts.card ≤ Fintype.card σ) (x : σ) :
    #{j | youngColouring ν hν j = x} = partWeight σ ν x := by
  rw [partWeight_apply, YoungDiagram.rowLen_ofPartition]
  rcases lt_or_ge (Fintype.equivFin σ x : ℕ) (ν.parts.sort (· ≥ ·)).length with hx | hx
  · -- The letter `x` is the row `i`, whose cells are the fibre of `youngBlock ν` over `i`.
    let i : Fin (ν.parts.sort (· ≥ ·)).length := ⟨Fintype.equivFin σ x, hx⟩
    have hfilter : (univ.filter fun j => youngColouring ν hν j = x) =
        univ.filter fun j => youngBlock ν j = i := by
      refine Finset.filter_congr fun j _ => ?_
      rw [youngColouring, Function.comp_apply, Function.comp_apply, Equiv.symm_apply_eq,
        Fin.ext_iff, Fin.ext_iff, Fin.val_castLE, eq_comm]
    rw [hfilter, ← Fintype.card_subtype, ← Fintype.card_congr (youngBlockEquiv ν i),
      Fintype.card_fin, List.getD_eq_getElem _ _ hx]
  · -- The letter `x` lies beyond the last row, so it is not used.
    rw [List.getD_eq_default _ _ hx, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    rw [youngColouring, Function.comp_apply, Function.comp_apply, Equiv.symm_apply_eq,
      Fin.ext_iff, Fin.val_castLE] at hj
    omega

theorem coeff_partWeight_psumPart_partition (π : Perm (Fin n)) (ν : n.Partition)
    (hν : ν.parts.card ≤ Fintype.card σ) :
    (psumPart σ R π.partition).coeff (partWeight σ ν) =
      Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} := by
  classical
  rw [coeff_psumPart_partition, ← fiberSubgroup_youngColouring ν hν,
    card_fixedPoints_quotient_fiberSubgroup]
  congr 3
  ext f
  exact and_congr_right' (forall_congr' fun i => by rw [card_filter_youngColouring ν hν i])

noncomputable local instance : DecidableEq σ := Classical.decEq σ

theorem coeff_psumPart_eq_card_fixedPoints {ρ : n.Partition} {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) {d : σ →₀ ℕ}
    (h : d.degree = n) :
    (psumPart σ R ρ).coeff d =
      Nat.card {q : Perm (Fin n) ⧸ youngSubgroup (weightPartition d h) // π • q = q} := by
  rw [coeff_eq_coeff_partWeight (psumPart_isSymmetric R ρ) h, psumPart_eq_psumPart_partition R hπ,
    coeff_partWeight_psumPart_partition R π _ (card_parts_weightPartition_le d h)]

end FixedTabloids
end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
