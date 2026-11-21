/- GID: D5/S3/Combinatorics/SubsetSpectrum/AdditiveDigitCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/AdditiveDigitCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative additive orders bound the capacity of weighted digits at integer levels. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Bounded-digit fibers in additive groups and integer levels of real weight sums. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity

open Finset

private def span {G : Type*} [AddCommGroup G] {r : ℕ} (w : Fin r → G) : AddSubgroup G :=
  AddSubgroup.closure (Set.range w)

private def mass {G : Type*} [AddCommGroup G] {r k : ℕ} (w : Fin r → G)
    (d : Fin r → Fin (k + 1)) : G :=
  ∑ j, (d j).val • w j

private theorem mass_mem_span {G : Type*} [AddCommGroup G] {r k : ℕ} (w : Fin r → G)
    (d : Fin r → Fin (k + 1)) : mass w d ∈ span w := by
  apply (span w).sum_mem
  intro j _
  exact (span w).nsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self j)) _

private theorem mass_split {G : Type*} [AddCommGroup G] {r k : ℕ} (w : Fin (r + 1) → G)
    (d : Fin (r + 1) → Fin (k + 1)) :
    mass w d = mass (Fin.init w) (Fin.init d) + (d (Fin.last r)).val • w (Fin.last r) := by
  exact Fin.sum_univ_castSucc _

private theorem quot_digit_injective {G : Type*} [AddCommGroup G] (x y : G) (k : ℕ) :
    Function.Injective (fun d : {d : Fin (k + 1) // d.val • x = y} =>
      ((Subtype.val d).val / addOrderOf x)) := by
  let c := addOrderOf x
  have aux (d e : {d : Fin (k + 1) // d.val • x = y}) (ord : (Subtype.val d).val ≤ (Subtype.val e).val)
      (same : (Subtype.val d).val / c = (Subtype.val e).val / c) : d = e := by
    have zero : ((Subtype.val e).val - (Subtype.val d).val) • x = 0 := by
      have eqe := e.property
      change (Subtype.val e).val • x = y at eqe
      rw [← Nat.sub_add_cancel ord, add_nsmul, d.property] at eqe
      exact add_right_cancel (eqe.trans (zero_add y).symm)
    have dvd : c ∣ (Subtype.val e).val - (Subtype.val d).val := addOrderOf_dvd_iff_nsmul_eq_zero.mpr zero
    by_cases pos : 0 < c
    · have h1 := Nat.mod_add_div (Subtype.val d).val c
      have h2 := Nat.mod_add_div (Subtype.val e).val c
      rw [same] at h1
      have hm1 := Nat.mod_lt (Subtype.val d).val pos
      have hm2 := Nat.mod_lt (Subtype.val e).val pos
      have less : (Subtype.val e).val - (Subtype.val d).val < c := by omega
      have eq := (Nat.mod_eq_of_lt less).symm.trans (Nat.mod_eq_zero_of_dvd dvd)
      exact Subtype.ext (Fin.ext (by omega))
    · have cZero : c = 0 := by omega
      rw [cZero, zero_dvd_iff] at dvd
      exact Subtype.ext (Fin.ext (by omega))
  intro d e same
  rcases le_total (Subtype.val d).val (Subtype.val e).val with h | h
  · exact aux d e h same
  · exact (aux e d h same.symm).symm

private theorem digit_fiber_card_le {G : Type*} [AddCommGroup G] (x y : G) (k : ℕ) :
    Nat.card {d : Fin (k + 1) // d.val • x = y} ≤ k / addOrderOf x + 1 := by
  classical
  let code (d : {d : Fin (k + 1) // d.val • x = y}) : Fin (k / addOrderOf x + 1) :=
    ⟨(Subtype.val d).val / addOrderOf x, Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_of_lt_succ d.val.isLt))⟩
  have injective : Function.Injective code := fun _ _ eq =>
    quot_digit_injective x y k (congrArg Fin.val eq)
  simpa using Nat.card_le_card_of_injective code injective


private theorem mass_fiber_step {G : Type*} [AddCommGroup G] {r k N : ℕ}
    (w : Fin (r + 1) → G)
    (limit : ∀ y : G, Nat.card {d : Fin r → Fin (k + 1) // mass (Fin.init w) d = y} ≤ N)
    (y : G) :
    Nat.card {d : Fin (r + 1) → Fin (k + 1) // mass w d = y} ≤
      (k / addOrderOf (QuotientAddGroup.mk' (span (Fin.init w)) (w (Fin.last r))) + 1) * N := by
  classical
  let H := span (Fin.init w)
  let π := QuotientAddGroup.mk' H
  let x := w (Fin.last r)
  let B := {t : Fin (k+1) // t.val • π x = π y}
  let T (t : B) := {d : Fin r → Fin (k+1) // mass (Fin.init w) d = y - t.val.val • x}
  have Bprop (d : Fin (r+1) → Fin (k+1)) (eq : mass w d = y) :
      (d (Fin.last r)).val • π x = π y := by
    rw [mass_split] at eq
    have eqMap := congrArg π eq
    have mp : π (mass (Fin.init w) (Fin.init d)) = 0 := by
      change mass (Fin.init w) (Fin.init d) ∈ π.ker
      rw [QuotientAddGroup.ker_mk']
      exact mass_mem_span _ _
    simpa only [map_add, map_nsmul, mp, zero_add, x] using eqMap
  let encode (d : {d : Fin (r+1) → Fin (k+1) // mass w d = y}) : Σ t : B, T t :=
    ⟨⟨d.val (Fin.last r), Bprop d.val d.property⟩, ⟨Fin.init d.val, by
      apply eq_sub_of_add_eq
      exact (mass_split w d.val).symm.trans d.property⟩⟩
  have injective : Function.Injective encode := by
    intro a b same
    have last : a.val (Fin.last r) = b.val (Fin.last r) :=
      congrArg (fun z : Σ t : B, T t => z.1.val) same
    have init : Fin.init a.val = Fin.init b.val :=
      congrArg (fun z : Σ t : B, T t => z.2.val) same
    apply Subtype.ext
    funext j
    refine Fin.lastCases last (fun t => congrFun init t) j
  have Bcard : Nat.card B ≤ k / addOrderOf (π x) + 1 := digit_fiber_card_le (π x) (π y) k
  calc
    _ ≤ Nat.card (Σ t : B, T t) := Nat.card_le_card_of_injective encode injective
    _ ≤ Nat.card B * N := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
      calc
        _ ≤ ∑ t : B, N := Finset.sum_le_sum (fun t _ => by simpa using limit (y - t.val.val • x))
        _ = _ := by simp
    _ ≤ _ := Nat.mul_le_mul_right N Bcard


private theorem capacity_factors {G : Type*} [AddCommGroup G] {r k : ℕ} (w : Fin r → G) :
    ∃ p : Fin r → ℕ,
      (∀ z ∈ span w, (∏ j, p j) • z = 0) ∧
      ∀ y : G, Nat.card {d : Fin r → Fin (k + 1) // mass w d = y} ≤
        ∏ j, (k / p j + 1) := by
  classical
  induction r with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro z mem
      have eq : span w = ⊥ := by
        have empty : Set.range w = ∅ := by ext x; simp
        simp [span, empty]
      simpa [eq] using mem
    · intro y
      have atMostOne :
          Nat.card {d : Fin 0 → Fin (k + 1) // mass w d = y} ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr inferInstance
      simpa using atMostOne
  | succ r ih =>
    obtain ⟨p, kill, bound⟩ := ih (Fin.init w)
    let H := span (Fin.init w)
    let π := QuotientAddGroup.mk' H
    let x := w (Fin.last r)
    let c := addOrderOf (π x)
    let t := ∏ j, p j
    refine ⟨Fin.snoc p c, ?_, ?_⟩
    · simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      have hcx : c • x ∈ H := by
        rw [← QuotientAddGroup.ker_mk' H]
        change π (c • x) = 0
        rw [map_nsmul]
        exact addOrderOf_nsmul_eq_zero (π x)
      have hspan : span w ≤ (nsmulAddMonoidHom (t * c) : G →+ G).ker := by
        rw [span, AddSubgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        change (t * c) • w j = 0
        refine Fin.lastCases ?_ (fun i => ?_) j
        · rw [mul_comm t c, mul_nsmul]
          exact kill _ hcx
        · have mem : w i.castSucc ∈ H :=
            AddSubgroup.subset_closure (Set.mem_range_self i)
          have killed : t • w i.castSucc = 0 := kill _ mem
          rw [mul_nsmul, killed, nsmul_zero]
      intro z hz
      exact hspan hz
    · intro y
      simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      rw [mul_comm]
      exact mass_fiber_step w bound y


private theorem collapse_two (k a b : ℕ) (ap : 0 < a) (bp : 0 < b) :
    (k + a) * (k + b) ≤ (k + 1) * (k + a * b) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ap.ne'
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero bp.ne'
  have e : (k + 1) * (k + (p + 1) * (q + 1)) =
      (k + (p + 1)) * (k + (q + 1)) + k * p * q := by ring
  rw [e]
  exact Nat.le_add_right _ _

private theorem collapse_factors {r : ℕ} (k : ℕ) (p : Fin (r + 1) → ℕ)
    (positive : ∀ j, 0 < p j) :
    (∏ j, (k + p j)) ≤ (k + 1)^r * (k + ∏ j, p j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    let before := Fin.init p
    let last := p (Fin.last (r + 1))
    have left : (∏ j, (k + p j)) = (∏ j, (k + before j)) * (k + last) :=
      Fin.prod_univ_castSucc _
    have prod : (∏ j, p j) = (∏ j, before j) * last := Fin.prod_univ_castSucc _
    rw [left, prod, pow_succ]
    have before_le := ih before (fun j => positive j.castSucc)
    have mul_ge := Finset.prod_pos (s := Finset.univ) (f := before)
      (fun j _ => positive j.castSucc)
    calc
      _ ≤ ((k + 1)^r * (k + ∏ j, before j)) * (k + last) :=
        Nat.mul_le_mul_right _ before_le
      _ = (k + 1)^r * ((k + ∏ j, before j) * (k + last)) := Nat.mul_assoc ..
      _ ≤ (k + 1)^r * ((k + 1) * (k + (∏ j, before j) * last)) :=
        Nat.mul_le_mul_left _ (collapse_two k _ _ mul_ge (positive _))
      _ = _ := (Nat.mul_assoc ..).symm


private theorem fiber_capacity {G : Type*} [AddCommGroup G] {r k : ℕ} (w : Fin (r + 1) → G)
    (y : G) :
    let b := addOrderOf (∑ j, w j)
    b * Nat.card {d : Fin (r + 1) → Fin (k + 1) // mass w d = y} ≤
      (b + k) * (k + 1)^r := by
  classical
  let b := addOrderOf (∑ j, w j)
  let N := Nat.card {d : Fin (r + 1) → Fin (k + 1) // mass w d = y}
  change b * N ≤ (b + k) * (k + 1)^r
  obtain ⟨p, kill, ct⟩ := capacity_factors (k := k) w
  have count : N ≤ ∏ j, (k / p j + 1) := ct y
  by_cases noOrder : ∃ j, p j = 0
  · obtain ⟨i, eq⟩ := noOrder
    have pad : (∏ j, (k / p j + 1)) ≤ (k + 1)^r := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), eq, Nat.div_zero, zero_add, mul_one]
      calc
        _ ≤ ∏ _ ∈ (Finset.univ : Finset (Fin (r + 1))).erase i, (k + 1) :=
          Finset.prod_le_prod (fun j _ => Nat.add_le_add_right (Nat.div_le_self _ _) _)
        _ = _ := by simp [Finset.card_erase_of_mem]
    exact (Nat.mul_le_mul_left _ (count.trans pad)).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · have positive (i : Fin (r + 1)) : 0 < p i := Nat.pos_of_ne_zero (fun h => noOrder ⟨i, h⟩)
    let D := ∏ j, p j
    have Dpos : 0 < D := Finset.prod_pos (fun j _ => positive j)
    have sum_mem : (∑ j, w j) ∈ span w := by
      apply (span w).sum_mem
      intro j _
      exact AddSubgroup.subset_closure (Set.mem_range_self j)
    have ofD : b ∣ D := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (kill _ sum_mem)
    have bLE : b ≤ D := Nat.le_of_dvd Dpos ofD
    have prod_bound : N * D ≤ (k + 1)^r * (k + D) := by
      calc
        _ ≤ (∏ j, (k / p j + 1)) * D := Nat.mul_le_mul_right _ count
        _ = ∏ j, (k / p j + 1) * p j := (Finset.prod_mul_distrib).symm
        _ ≤ ∏ j, (k + p j) := by
          apply Finset.prod_le_prod
          intro j _
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
        _ ≤ _ := collapse_factors _ p positive
    have cross : b * (k + D) ≤ (b + k) * D := by
      calc
        _ = b * D + k * b := by ring
        _ ≤ b * D + k * D := Nat.add_le_add_left (Nat.mul_le_mul_left _ bLE) _
        _ = _ := by ring
    apply Nat.le_of_mul_le_mul_right _ Dpos
    calc
      _ = b * (N * D) := by ring
      _ ≤ b * ((k + 1)^r * (k + D)) := Nat.mul_le_mul_left _ prod_bound
      _ = (k + 1)^r * (b * (k + D)) := by ring
      _ ≤ (k + 1)^r * ((b + k) * D) := Nat.mul_le_mul_left _ cross
      _ = _ := by ring



/-- The reduced denominator of the total weight bounds how many distinct integer levels
can be covered by bounded digits. -/
theorem integral_levels_capacity {r k n b : ℕ} {A : ℤ} (positive : 0 < b) (coprime : A.natAbs.Coprime b)
    (w : Fin (r + 1) → ℝ) (total : (∑ j, w j) = (A : ℝ) / b)
    (level : Fin n → ℤ) (distinct : Function.Injective level)
    (cover : ∀ x : Fin n, ∃ d : Fin (r+1) → Fin (k+1),
      (∑ j, ((d j).val : ℝ) * w j) = (level x : ℝ)) :
    b * n ≤ (b + k) * (k + 1)^r := by
  classical
  let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  let wt (j : Fin (r+1)) := q (w j)
  choose digit eq using cover
  have vanish (z : ℤ) : q (z : ℝ) = 0 := by
    change (z : ℝ) ∈ q.ker
    rw [QuotientAddGroup.ker_mk']
    exact ⟨z, by simp [zsmul_eq_mul]⟩
  let encode (x : Fin n) : {d : Fin (r+1) → Fin (k+1) // mass wt d = 0} :=
    ⟨digit x, by
      calc
        _ = q (∑ j, ((digit x j).val : ℝ) * w j) := by simp only [mass, wt, map_sum, map_nsmul, ← nsmul_eq_mul]
        _ = 0 := (congrArg q (eq x)).trans (vanish (level x))⟩
  have injective : Function.Injective encode := by
    intro x y same
    have dEq : digit x = digit y := congrArg Subtype.val same
    apply distinct
    exact_mod_cast ((eq x).symm.trans (dEq ▸ eq y))
  have count : n ≤ Nat.card {d : Fin (r+1) → Fin (k+1) // mass wt d = 0} := by
    simpa using Nat.card_le_card_of_injective encode injective
  have weight : (∑ j, wt j) = ((A : ℝ) / b : ℝ) := by
    change (∑ j, q (w j)) = q ((A : ℝ) / b)
    rw [← map_sum, total]
  have order : addOrderOf (∑ j, wt j) = b := by
    rw [weight]
    change addOrderOf (((A : ℝ) / b : ℝ) : AddCircle (1 : ℝ)) = b
    simpa only [mul_one] using AddCircle.addOrderOf_div_of_gcd_eq_one' (p := (1 : ℝ)) positive coprime
  have bound := fiber_capacity (k := k) wt 0
  dsimp only at bound
  rw [order] at bound
  exact (Nat.mul_le_mul_left b count).trans bound


end D5.S3.Combinatorics.SubsetSpectrum.AdditiveDigitCapacity
