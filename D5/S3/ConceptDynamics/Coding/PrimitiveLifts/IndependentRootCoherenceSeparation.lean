/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/IndependentRootCoherenceSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/IndependentRootCoherenceSeparation
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: A nonzero element has roots of every positive degree in a reduced abelian group. -/

import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A concrete quotient of a direct sum separates arbitrary roots from rational coherence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation

open scoped DirectSum

/-- The index j represents the positive degree j+1. -/
abbrev B := ⨁ j : ℕ, ZMod (2 * (j + 1))

def generator (j : ℕ) : B := DirectSum.of (fun j => ZMod (2 * (j + 1))) j 1

def relations : AddSubgroup B :=
  AddSubgroup.closure (Set.range fun j : ℕ => (j + 1) • generator j - generator 0)

/-- The common half-period of all the cyclic summands is identified. -/
abbrev G := B ⧸ relations

def c : G := QuotientAddGroup.mk' relations (generator 0)

def root (j : ℕ) : G := QuotientAddGroup.mk' relations (generator j)

private theorem root_relation (j : ℕ) : (j + 1) • root j = c := by
  apply sub_eq_zero.mp
  change (QuotientAddGroup.mk' relations) ((j + 1) • generator j - generator 0) = 0
  exact (QuotientAddGroup.eq_zero_iff _).mpr
    (AddSubgroup.subset_closure ⟨j, rfl⟩)

private theorem two_c : (2 : ℕ) • c = 0 := by
  change (QuotientAddGroup.mk' relations) (2 • generator 0) = 0
  have h : (2 : ℕ) • generator 0 = 0 := by
    change (2 : ℕ) • DirectSum.of (fun j => ZMod (2 * (j + 1))) 0 1 = 0
    rw [← map_nsmul]
    rw [show (2 : ℕ) • (1 : ZMod (2 * (0 + 1))) = 0 by decide, map_zero]
  rw [h, map_zero]

/-- The purely algebraic rational circle; no topology is imposed. -/
abbrev QZ := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

private def qclass : ℚ →+ QZ := QuotientAddGroup.mk' _

private theorem qclass_one : qclass 1 = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples _)

private def componentCharacter (j : ℕ) : ZMod (2 * (j + 1)) →+ QZ :=
  ZMod.lift _ ⟨zmultiplesHom QZ (qclass (1 / (2 * (j + 1) : ℚ))), by
    change ((2 * (j + 1) : ℕ) : ℤ) • qclass (1 / (2 * (j + 1) : ℚ)) = 0
    rw [← map_zsmul, zsmul_eq_mul]
    convert qclass_one using 1
    push_cast
    field_simp⟩

private def character : B →+ QZ := DirectSum.toAddMonoid componentCharacter

private theorem character_generator (j : ℕ) :
    character (generator j) = qclass (1 / (2 * (j + 1) : ℚ)) := by
  simp only [character, generator, DirectSum.toAddMonoid_of]
  change ZMod.lift _ _ ((1 : ℤ) : ZMod (2 * (j + 1))) = _
  rw [ZMod.lift_coe]
  exact one_zsmul _

private theorem character_relations : relations ≤ character.ker := by
  apply (AddSubgroup.closure_le character.ker).mpr
  rintro _ ⟨j, rfl⟩
  change character ((j + 1) • generator j - generator 0) = 0
  rw [map_sub, map_nsmul, character_generator,
    character_generator, sub_eq_zero, ← map_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  field_simp
  <;> ring

private theorem c_ne_zero : c ≠ 0 := by
  intro hc
  have hmem : generator 0 ∈ relations := (QuotientAddGroup.eq_zero_iff _).mp hc
  have hz := character_relations hmem
  rw [AddMonoidHom.mem_ker, character_generator] at hz
  have hm := (QuotientAddGroup.eq_zero_iff _).mp hz
  obtain ⟨k, hk⟩ := hm
  have he : (k : ℚ) = 1 / 2 := by simpa [zsmul_eq_mul] using hk
  have hk0 : 0 ≤ k := by exact_mod_cast (show (0 : ℚ) ≤ k by linarith)
  have hk1 : k < 1 := by exact_mod_cast (show (k : ℚ) < 1 by linarith)
  have : k = 0 := by omega
  norm_num [this] at he

/-- The residual direct sum records the coordinates modulo their positive degrees. -/
abbrev D := ⨁ j : ℕ, ZMod (j + 1)

private def reduction (j : ℕ) : ZMod (2 * (j + 1)) →+ ZMod (j + 1) :=
  (ZMod.castHom (dvd_mul_left (j + 1) 2) (ZMod (j + 1))).toAddMonoidHom

private def beta : B →+ D := DirectSum.map reduction

private theorem beta_generator_zero : beta (generator 0) = 0 := by
  have hz : (1 : ZMod (0 + 1)) = 0 := by decide
  simp [beta, generator, reduction, hz]

private theorem beta_relations : relations ≤ beta.ker := by
  apply (AddSubgroup.closure_le beta.ker).mpr
  rintro _ ⟨j, rfl⟩
  change beta ((j + 1) • generator j - generator 0) = 0
  rw [map_sub, map_nsmul]
  have hj : (j + 1) • beta (generator j) = 0 := by
    simp only [beta, generator, DirectSum.map_of]
    rw [← map_nsmul]
    simp [reduction, nsmul_eq_mul, ZMod.natCast_self]
  rw [hj, beta_generator_zero, sub_self]

def projection : G →+ D := QuotientAddGroup.lift relations beta beta_relations

private theorem coefficient_kernel (j : ℕ) (x : ZMod (2 * (j + 1)))
    (hx : reduction j x = 0) :
    (QuotientAddGroup.mk' relations) (DirectSum.of (fun j => ZMod (2 * (j + 1))) j x)
      ∈ AddSubgroup.zmultiples c := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  have ha : (a : ZMod (j + 1)) = 0 := by simpa [reduction] using hx
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a (j + 1)).mp ha
  refine ⟨k, ?_⟩
  rw [hk]
  have hcast : ((((j + 1 : ℕ) : ℤ) * k : ℤ) : ZMod (2 * (j + 1))) =
      k • ((j + 1) • (1 : ZMod (2 * (j + 1)))) := by
    push_cast
    simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one]
    push_cast
    ring
  rw [hcast, map_zsmul, map_nsmul, map_zsmul, map_nsmul]
  change k • c = k • ((j + 1) • root j)
  rw [root_relation]

private theorem kernel_projection (g : G) :
    projection g = 0 ↔ g ∈ AddSubgroup.zmultiples c := by
  constructor
  · obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective relations g
    intro hb
    change beta b = 0 at hb
    rw [← DirectSum.sum_support_of b, map_sum]
    apply AddSubgroup.sum_mem
    intro j _
    apply coefficient_kernel
    have h := congrArg (fun d : D => d j) hb
    simpa [beta] using h
  · rintro ⟨k, rfl⟩
    rw [map_zsmul]
    have hc : projection c = 0 := beta_generator_zero
    rw [hc, zsmul_zero]

private theorem rational_projection_zero (f : ℚ →+ G) (q : ℚ) : projection (f q) = 0 := by
  ext j
  have hj : (j + 1 : ℚ) ≠ 0 := by positivity
  have hq : q = (j + 1) • (q / (j + 1)) := by
    rw [nsmul_eq_mul]
    push_cast
    field_simp
  rw [hq, map_nsmul, map_nsmul, DFinsupp.nsmul_apply, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul]
  rfl

private theorem rational_hom_zero (f : ℚ →+ G) : f = 0 := by
  ext q
  obtain ⟨k, hk⟩ := (kernel_projection (f (q / 2))).mp (rational_projection_zero f (q / 2))
  have hq : q = (2 : ℕ) • (q / 2) := by rw [nsmul_eq_mul]; ring
  rw [hq, map_nsmul, ← hk, smul_comm, two_c, zsmul_zero]
  rfl

/-- Independently chosen roots of every positive degree need not extend to rational time. -/
theorem independent_roots_without_rational_coherence :
    c ≠ 0 ∧ (2 : ℕ) • c = 0 ∧
      (∀ n : ℕ, 0 < n → ∃ b : G, n • b = c) ∧
      (∀ f : ℚ →+ G, f = 0) := by
  refine ⟨c_ne_zero, two_c, ?_, rational_hom_zero⟩
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact ⟨root j, root_relation j⟩

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation
