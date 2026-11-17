/- GID: D5/S3/FiniteGroups/Partitions/OrbitSymmetryDynamics
   generality: G
   mirror-B: none(waiver:no-separate-boolean-mirror-claimed)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orbit relations classify the full ambient symmetry, its centralizer, and its cyclic normalizer. -/

import D5.S3.FiniteGroups.SuccessorQuotient
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Aesop
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The complete orbit relation and its dynamic symmetry group. -/

namespace D5.S3.FiniteGroups.OrbitSymmetryDynamics

open Equiv Equiv.Perm

variable {X : Type*}

/-- The actual ambient subgroup preserving and reflecting the complete orbit relation. -/
abbrev orbitAut (t : Perm X) : Subgroup (Perm X) :=
  SuccessorQuotient.relationAut t.SameCycle

private theorem sameCycle_of_square_eq_one (t : Perm X) (ht : t ^ 2 = 1)
    (x y : X) : t.SameCycle x y ↔ y = x ∨ y = t x := by
  constructor
  · rintro ⟨i, hi⟩
    rw [zpow_eq_zpow_emod' i ht] at hi
    have hm : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases hm with hm | hm
    · exact Or.inl (by simpa [hm] using hi.symm)
    · exact Or.inr (by simpa [hm] using hi.symm)
  · rintro (rfl | rfl)
    · exact SameCycle.rfl
    · exact (SameCycle.refl t x).apply_right

private theorem swap_mem_orbitAut [DecidableEq X] (t : Perm X) (x y : X)
    (hxy : t.SameCycle x y) :
    Equiv.swap x y ∈ orbitAut t := by
  classical
  have hmove (z : X) : t.SameCycle z (Equiv.swap x y z) := by
    by_cases hx : z = x
    · simpa only [hx, Equiv.swap_apply_left] using hxy
    by_cases hy : z = y
    · simpa only [hy, Equiv.swap_apply_right] using hxy.symm
    rw [Equiv.swap_apply_of_ne_of_ne hx hy]
  intro u v
  constructor
  · intro h
    exact (hmove u).trans (h.trans (hmove v).symm)
  · intro h
    exact (hmove u).symm.trans (h.trans (hmove v))

/-- Commuting with the dynamics preserves and reflects its orbit relation. -/
theorem centralizer_le_orbitAut (t : Perm X) :
    Subgroup.centralizer ({t} : Set (Perm X)) ≤ orbitAut t := by
  intro p hp
  have hc : p * t = t * p := Subgroup.mem_centralizer_singleton_iff.mp hp
  have hconj : p * t * p⁻¹ = t := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  intro x y
  have h := sameCycle_conj (f := t) (g := p) (x := p x) (y := p y)
  simpa [hconj] using h

/-- The full orbit relation reconstructs the dynamics exactly for involutions,
including identity permutations, empty types, and infinite types. -/
theorem orbit_relation_determines_iff (t : Perm X) :
    (∀ s : Perm X, (∀ x y, s.SameCycle x y ↔ t.SameCycle x y) → s = t) ↔
      t ^ 2 = 1 := by
  constructor
  · intro h
    have hi : t⁻¹ = t := h t⁻¹ (fun _ _ => sameCycle_inv)
    calc
      t ^ 2 = t * t := pow_two t
      _ = t * t⁻¹ := congrArg (fun u : Perm X => t * u) hi.symm
      _ = 1 := mul_inv_cancel t
  · intro ht s hs
    ext x
    have hstep : t.SameCycle x (s x) :=
      (hs x (s x)).mp (SameCycle.refl s x).apply_right
    rcases (sameCycle_of_square_eq_one t ht x (s x)).mp hstep with hfix | hnext
    · have hpair : s.SameCycle x (t x) :=
        (hs x (t x)).mpr (SameCycle.refl t x).apply_right
      exact hfix.trans (hpair.eq_of_left hfix)
    · exact hnext

/-- Forgetting the direction and parametrization of every orbit adds no ambient
permutation symmetries exactly when the original dynamics is involutive. -/
theorem centralizer_eq_orbitAut_iff (t : Perm X) :
    Subgroup.centralizer ({t} : Set (Perm X)) = orbitAut t ↔ t ^ 2 = 1 := by
  classical
  constructor
  · intro heq
    ext x
    have hp := swap_mem_orbitAut t x (t x) (SameCycle.refl t x).apply_right
    rw [← heq] at hp
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hp
    have h := congrArg (fun q : Perm X => q x) hc
    simpa only [pow_two, mul_apply, one_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right] using h.symm
  · intro ht
    apply le_antisymm (centralizer_le_orbitAut t)
    intro p hp
    have hconj : p * t * p⁻¹ = t := by
      apply (orbit_relation_determines_iff t).mpr ht
      intro x y
      rw [sameCycle_conj]
      simpa using (hp (p⁻¹ x) (p⁻¹ y)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hconj)



private abbrev A (t : Perm X) := orbitAut t
private abbrev N (t : Perm X) :=
  Subgroup.normalizer (Subgroup.zpowers t : Set (Perm X))

/-- Both directions use actual integer powers of the same generator. -/
theorem normalizer_le_orbitAut (t : Perm X) :
    Subgroup.normalizer (Subgroup.zpowers t : Set (Perm X)) ≤
      orbitAut t := by
  have forward (p : Perm X) (hp : p ∈ N t) {x y : X}
      (hxy : t.SameCycle x y) : t.SameCycle (p x) (p y) := by
    obtain ⟨k, hk⟩ := hxy
    have hconj : p * t ^ k * p⁻¹ ∈ Subgroup.zpowers t :=
      ((Subgroup.mem_normalizer_iff.mp hp) (t ^ k)).mp
        (Subgroup.zpow_mem_zpowers t k)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hconj
    refine ⟨m, ?_⟩
    rw [hm]
    simpa only [mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using congrArg p hk
  intro p hp x y
  constructor
  · intro h
    have hi : p⁻¹ ∈ N t := (N t).inv_mem hp
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using forward p⁻¹ hi h
  · exact forward p hp

private theorem normalizes_of_conjugate (t p : Perm X)
    (h : p * t * p⁻¹ = t ∨ p * t * p⁻¹ = t⁻¹) : p ∈ N t := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (p * t * p⁻¹) = Subgroup.zpowers t
  rcases h with h | h
  · rw [h]
  · rw [h, Subgroup.zpowers_inv]

private theorem centralizer_le_normalizer (t : Perm X) :
    Subgroup.centralizer ({t} : Set (Perm X)) ≤ N t := by
  intro p hp
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hp
  apply normalizes_of_conjugate t p
  left
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

/-- Reuse the canonical same-file swap proof. -/
private theorem orbit_swap_power [DecidableEq X] (t : Perm X) (heq : N t = A t) (x : X) :
    ∃ k : ℤ, Equiv.swap x (t x) * t * Equiv.swap x (t x) = t ^ k := by
  classical
  have hs : Equiv.swap x (t x) ∈ A t :=
    swap_mem_orbitAut t x (t x)
      (SameCycle.refl t x).apply_right
  rw [← heq] at hs
  have hu := ((Subgroup.mem_normalizer_iff.mp hs) t).mp (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ⟨k, by simpa only [Equiv.swap_inv] using hk.symm⟩

private theorem swap_forces_cube (t : Perm X) (heq : N t = A t)
    (x : X) (hx : t (t x) ≠ x) : t (t (t x)) = x := by
  classical
  obtain ⟨k, hk⟩ := orbit_swap_power t heq x
  have htx : t x ≠ x := by
    intro h
    exact hx (by rw [h, h])
  have h2 : t (t x) ≠ t x := fun h => htx (t.injective h)
  have hc : (Equiv.swap x (t x) * t * Equiv.swap x (t x)) * t =
      t * (Equiv.swap x (t x) * t * Equiv.swap x (t x)) := by
    rw [hk]
    simpa only [zpow_one] using zpow_mul_comm t k (1 : ℤ)
  have h := congrArg (fun f : Perm X => f x) hc
  have hs : Equiv.swap x (t x) (t (t x)) = t (t x) :=
    Equiv.swap_apply_of_ne_of_ne hx h2
  simpa only [mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, hs] using h.symm

private def Small (t : Perm X) : Prop :=
  ∀ x, t (t x) = x ∨ t (t (t x)) = x

private theorem sixth_of_small (t : Perm X) (hs : Small t) : t ^ 6 = 1 := by
  ext x
  rcases hs x with h | h <;>
    simp only [pow_succ, pow_zero, mul_apply, one_apply, h]

private theorem zpow_six_cases (t : Perm X) (h6 : t ^ 6 = 1) (k : ℤ) :
    t ^ k = 1 ∨ t ^ k = t ∨ t ^ k = t ^ 2 ∨
      t ^ k = t ^ 3 ∨ t ^ k = t ^ 4 ∨ t ^ k = t ^ 5 := by
  have hm : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨
      k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by omega
  rw [zpow_eq_zpow_emod' k h6]
  rcases hm with hm | hm | hm | hm | hm | hm <;> simp [hm]

private theorem sameCycle_small (t : Perm X) (hs : Small t) (x y : X) :
    t.SameCycle x y ↔ y = x ∨ y = t x ∨ y = t (t x) := by
  constructor
  · rintro ⟨k, hk⟩
    rcases zpow_six_cases t (sixth_of_small t hs) k with h | h | h | h | h | h <;>
      rw [h] at hk <;>
      rcases hs x with h2 | h3 <;>
      simp_all only [pow_succ, pow_zero, mul_apply, one_apply] <;> aesop
  · rintro (rfl | rfl | rfl)
    · exact SameCycle.rfl
    · exact (SameCycle.refl t x).apply_right
    · exact (SameCycle.refl t x).apply_right.apply_right

private theorem sameCycle_two (t : Perm X) (hs : Small t) (x y : X)
    (hx : t (t x) = x) : t.SameCycle x y ↔ y = x ∨ y = t x := by
  constructor
  · intro h
    rcases (sameCycle_small t hs x y).mp h with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl (h.trans hx)
  · rintro (h | h)
    · exact (sameCycle_small t hs x y).mpr (Or.inl h)
    · exact (sameCycle_small t hs x y).mpr (Or.inr (Or.inl h))

private def ThreeOrbit (t : Perm X) (a x : X) : Prop :=
  x = a ∨ x = t a ∨ x = t (t a)

/-- A consumed explicit unique-three-orbit predicate; there are no restrictions on
    the cardinality of the ambient type or of its two-point-orbit family. -/
private structure ThreeCore (t : Perm X) (a : X) : Prop where
  square_ne : t (t a) ≠ a
  cube : t (t (t a)) = a
  all_moved : ∀ x, t (t x) ≠ x → ThreeOrbit t a x

private theorem ThreeCore.small {t : Perm X} {a : X} (c : ThreeCore t a) : Small t := by
  intro x
  by_cases h : t (t x) = x
  · exact Or.inl h
  right
  rcases c.all_moved x h with rfl | rfl | rfl
  · exact c.cube
  · exact congrArg t c.cube
  · exact congrArg (fun z => t (t z)) c.cube

private theorem ThreeCore.moved_iff {t : Perm X} {a x : X} (c : ThreeCore t a) :
    t (t x) ≠ x ↔ ThreeOrbit t a x := by
  constructor
  · exact c.all_moved x
  · rintro (rfl | rfl | rfl)
    · exact c.square_ne
    · exact fun h => c.square_ne (t.injective h)
    · exact fun h => c.square_ne (t.injective (t.injective h))

private theorem equality_threeCore (t : Perm X) (heq : N t = A t)
    (hne : t ^ 2 ≠ 1) : ∃ a, ThreeCore t a := by
  classical
  have hs : Small t := fun x => by
    by_cases h : t (t x) = x
    · exact Or.inl h
    · exact Or.inr (swap_forces_cube t heq x h)
  have h6 := sixth_of_small t hs
  obtain ⟨a, ha⟩ : ∃ a, t (t a) ≠ a := by
    by_contra h
    apply hne
    ext x
    simpa only [pow_two, mul_apply, one_apply] using
      (not_exists_not.mp h x)
  have ha3 := swap_forces_cube t heq a ha
  have ha1 : t a ≠ a := by intro h; exact ha (by rw [h, h])
  have ha21 : t (t a) ≠ t a := fun h => ha1 (t.injective h)
  let s : Perm X := Equiv.swap a (t a)
  let v : Perm X := s * t * s
  have hva : v a = t (t a) := by
    simp only [v, s, mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne ha ha21]
  obtain ⟨k, hk⟩ := orbit_swap_power t heq a
  have hvk : v = t ^ k := hk
  -- This is ONE global k. It is never replaced by separate orbit exponents.
  have hv : v = t ^ 2 ∨ v = t ^ 5 := by
    rcases zpow_six_cases t h6 k with h | h | h | h | h | h
    · have hh := hva
      rw [hvk, h] at hh
      exact False.elim (ha (by simpa using hh.symm))
    · have hh := hva
      rw [hvk, h] at hh
      exact False.elim (ha21 hh.symm)
    · exact Or.inl (hvk.trans h)
    · have hh := hva
      rw [hvk, h] at hh
      simp only [pow_succ, pow_zero, mul_apply, one_apply, ha3] at hh
      exact False.elim (ha hh.symm)
    · have hh := hva
      rw [hvk, h] at hh
      simp only [pow_succ, pow_zero, mul_apply, one_apply, ha3] at hh
      exact False.elim (ha21 hh.symm)
    · exact Or.inr (hvk.trans h)
  refine ⟨a, ⟨ha, ha3, ?_⟩⟩
  intro y hy
  by_contra hO
  have hya : y ≠ a := fun h => hO (Or.inl h)
  have hyta : y ≠ t a := fun h => hO (Or.inr (Or.inl h))
  have hyt2a : y ≠ t (t a) := fun h => hO (Or.inr (Or.inr h))
  have htya : t y ≠ a := by
    intro h
    exact hyt2a (t.injective (h.trans ha3.symm))
  have htyta : t y ≠ t a := fun h => hya (t.injective h)
  have hsy : s y = y := Equiv.swap_apply_of_ne_of_ne hya hyta
  have hsty : s (t y) = t y := Equiv.swap_apply_of_ne_of_ne htya htyta
  have hvy : v y = t y := by simp only [v, mul_apply, hsy, hsty]
  have hy3 : t (t (t y)) = y := (hs y).resolve_left hy
  have hy21 : t (t y) = t y := by
    rcases hv with hv | hv <;> rw [hv] at hvy <;>
      simpa only [pow_succ, pow_zero, mul_apply, one_apply, hy3] using hvy
  have hy1 : t y = y := t.injective hy21
  exact hy (by rw [hy1, hy1])

private theorem zpow_cube_cases (f : Perm X) (h3 : f ^ 3 = 1) (k : ℤ) :
    f ^ k = 1 ∨ f ^ k = f ∨ f ^ k = f ^ 2 := by
  have hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [zpow_eq_zpow_emod' k h3]
  rcases hm with hm | hm | hm <;> simp [hm]

private theorem sameCycle_cube (f : Perm X) (h3 : f ^ 3 = 1)
    {x y : X} (h : f.SameCycle x y) : y = x ∨ y = f x ∨ y = f (f x) := by
  obtain ⟨k, hk⟩ := h
  rcases zpow_cube_cases f h3 k with h | h | h
  · exact Or.inl (by simpa only [h, one_apply] using hk.symm)
  · exact Or.inr (Or.inl (by simpa only [h] using hk.symm))
  · exact Or.inr (Or.inr (by simpa only [h, pow_two, mul_apply] using hk.symm))

/-- Exact bridge to the requested arbitrary-type Mathlib predicate. -/
private theorem threeCore_literal_iff (t : Perm X) :
    (∃ a, ThreeCore t a) ↔ (t ^ 2).IsCycle ∧ t ^ 6 = 1 := by
  constructor
  · rintro ⟨a, c⟩
    refine ⟨⟨a, ?_, ?_⟩, sixth_of_small t c.small⟩
    · simpa only [pow_two, mul_apply] using c.square_ne
    · intro y hy
      have hy' : t (t y) ≠ y := by simpa only [pow_two, mul_apply] using hy
      rcases c.all_moved y hy' with rfl | rfl | rfl
      · exact SameCycle.rfl
      · refine ⟨2, ?_⟩
        change t (t (t (t a))) = t a
        exact congrArg t c.cube
      · refine ⟨1, ?_⟩
        simp only [zpow_one, pow_two, mul_apply]
  · rintro ⟨hc, h6⟩
    obtain ⟨a, ha, hall⟩ := hc
    have ha' : t (t a) ≠ a := by simpa only [pow_two, mul_apply] using ha
    have hq3 : (t ^ 2) ^ 3 = 1 := by simpa only [← pow_mul] using h6
    have hta : (t ^ 2) (t a) ≠ t a := by
      simpa only [pow_two, mul_apply] using (fun h => ha' (t.injective h))
    have hstep := sameCycle_cube (t ^ 2) hq3 (hall hta)
    simp only [pow_two, mul_apply] at hstep
    have ha3 : t (t (t a)) = a := by
      rcases hstep with h | h | h
      · exact False.elim (ha' (by rw [h, h]))
      · have h1 : a = t a := t.injective h
        exact False.elim (ha' (by rw [← h1, ← h1]))
      · exact (t.injective h).symm
    refine ⟨a, ⟨ha', ha3, ?_⟩⟩
    intro y hy
    have hy' : (t ^ 2) y ≠ y := by simpa only [pow_two, mul_apply] using hy
    have h := sameCycle_cube (t ^ 2) hq3 (hall hy')
    simpa only [ThreeOrbit, pow_two, mul_apply, ha3, or_left_comm, or_comm,
      or_assoc] using h

/-- Orbit-relation automorphisms preserve three-point versus at-most-two-point
    classes. The proof uses three distinct actual images, not orbit-cardinality
    assumptions or a finite ambient type. -/
private theorem preserves_square_moved (t : Perm X) (hs : Small t)
    (p : Perm X) (hp : p ∈ A t) (x : X) :
    t (t (p x)) ≠ p x ↔ t (t x) ≠ x := by
  have forward (q : Perm X) (hq : q ∈ A t) (z : X) (hz : t (t z) ≠ z) :
      t (t (q z)) ≠ q z := by
    intro h2
    have hz1 : t z ≠ z := by intro h; exact hz (by rw [h, h])
    have hz21 : t (t z) ≠ t z := fun h => hz1 (t.injective h)
    have h1 := (sameCycle_two t hs (q z) (q (t z)) h2).mp
      ((hq z (t z)).mpr (SameCycle.refl t z).apply_right)
    have h2' := (sameCycle_two t hs (q z) (q (t (t z))) h2).mp
      ((hq z (t (t z))).mpr (SameCycle.refl t z).apply_right.apply_right)
    have h1' : q (t z) = t (q z) := h1.resolve_left (fun h => hz1 (q.injective h))
    have h2'' : q (t (t z)) = t (q z) :=
      h2'.resolve_left (fun h => hz (q.injective h))
    exact hz21 (q.injective (h2''.trans h1'.symm))
  constructor
  · intro h
    have hi := forward p⁻¹ ((A t).inv_mem hp) (p x) h
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hi
  · exact forward p hp x

/-- This explicitly constructs both invariant subtypes. In particular p preserves
    the complement before the existing involution centralizer theorem is used. -/
private theorem complement_commutes (t : Perm X) (a : X) (c : ThreeCore t a)
    (p : Perm X) (hp : p ∈ A t) :
    ∀ x, ¬ ThreeOrbit t a x → p (t x) = t (p x) := by
  have hOt (x : X) : ThreeOrbit t a (t x) ↔ ThreeOrbit t a x := by
    rw [← c.moved_iff, ← c.moved_iff]
    exact not_congr t.injective.eq_iff
  have hOp (x : X) : ThreeOrbit t a (p x) ↔ ThreeOrbit t a x := by
    rw [← c.moved_iff, ← c.moved_iff]
    exact preserves_square_moved t c.small p hp x
  have hYt (x : X) : (¬ ThreeOrbit t a (t x)) ↔ ¬ ThreeOrbit t a x :=
    not_congr (hOt x)
  have hYp (x : X) : (¬ ThreeOrbit t a (p x)) ↔ ¬ ThreeOrbit t a x :=
    not_congr (hOp x)
  let Y := {x : X // ¬ ThreeOrbit t a x}
  let tY : Perm Y := t.subtypePerm hYt
  let pY : Perm Y := p.subtypePerm hYp
  have htY : tY ^ 2 = 1 := by
    ext x
    change t (t x.val) = x.val
    by_contra h
    exact x.property (c.all_moved x.val h)
  have hpY : pY ∈ orbitAut tY := by
    intro x y
    change (t.subtypePerm hYt).SameCycle ((p.subtypePerm hYp) x) ((p.subtypePerm hYp) y) ↔
      (t.subtypePerm hYt).SameCycle x y
    rw [sameCycle_subtypePerm, sameCycle_subtypePerm]
    exact hp x.val y.val
  rw [← (centralizer_eq_orbitAut_iff tY).mpr htY] at hpY
  have hcY : pY * tY = tY * pY := Subgroup.mem_centralizer_singleton_iff.mp hpY
  intro x hx
  have h := congrArg (fun q : Perm Y => (q ⟨x, hx⟩).val) hcY
  exact h

private theorem three_point_orientation (t v : Perm X) (a : X) (c : ThreeCore t a)
    (hO : ∀ x, ThreeOrbit t a (v x) ↔ ThreeOrbit t a x)
    (hfree : ∀ x, ThreeOrbit t a x → v x ≠ x) :
    (∀ x, ThreeOrbit t a x → v x = t x) ∨
      (∀ x, ThreeOrbit t a x → v x = t⁻¹ x) := by
  have h10 : t a ≠ a := by intro h; exact c.square_ne (by rw [h, h])
  have h20 : t (t a) ≠ a := c.square_ne
  have h21 : t (t a) ≠ t a := fun h => h10 (t.injective h)
  have ha := (hO a).mpr (Or.inl rfl)
  have hb := (hO (t a)).mpr (Or.inr (Or.inl rfl))
  have hd := (hO (t (t a))).mpr (Or.inr (Or.inr rfl))
  have hfa := hfree a (Or.inl rfl)
  have hfb := hfree (t a) (Or.inr (Or.inl rfl))
  have hfd := hfree (t (t a)) (Or.inr (Or.inr rfl))
  have hi10 : v (t a) ≠ v a := v.injective.ne h10
  have hi20 : v (t (t a)) ≠ v a := v.injective.ne h20
  have hi21 : v (t (t a)) ≠ v (t a) := v.injective.ne h21
  have htia : t⁻¹ a = t (t a) := by
    calc
      t⁻¹ a = t⁻¹ (t (t (t a))) := congrArg (fun z => t⁻¹ z) c.cube.symm
      _ = t (t a) := t.symm_apply_apply _
  have htib : t⁻¹ (t a) = a := t.symm_apply_apply a
  have htid : t⁻¹ (t (t a)) = t a := t.symm_apply_apply (t a)
  rcases ha with ha | ha | ha
  · exact False.elim (hfa ha)
  · have hd' : v (t (t a)) = a := by
      rcases hd with hd | hd | hd <;> simp_all
    have hb' : v (t a) = t (t a) := by
      rcases hb with hb | hb | hb <;> simp_all
    left
    rintro x (rfl | rfl | rfl) <;> simp only [ha, hb', hd', c.cube]
  · have hb' : v (t a) = a := by
      rcases hb with hb | hb | hb <;> simp_all
    have hd' : v (t (t a)) = t a := by
      rcases hd with hd | hd | hd <;> simp_all
    right
    rintro x (rfl | rfl | rfl) <;> simp only [ha, hb', hd', htia, htib, htid]

private theorem unique_three_normalizes (t : Perm X) (a : X) (c : ThreeCore t a)
    (p : Perm X) (hp : p ∈ A t) : p ∈ N t := by
  have hOt (x : X) : ThreeOrbit t a (t x) ↔ ThreeOrbit t a x := by
    rw [← c.moved_iff, ← c.moved_iff]
    exact not_congr t.injective.eq_iff
  have hOp (x : X) : ThreeOrbit t a (p x) ↔ ThreeOrbit t a x := by
    rw [← c.moved_iff, ← c.moved_iff]
    exact preserves_square_moved t c.small p hp x
  have hOpi (x : X) : ThreeOrbit t a (p⁻¹ x) ↔ ThreeOrbit t a x := by
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hOp (p⁻¹ x)).symm
  let v : Perm X := p * t * p⁻¹
  have hOv (x : X) : ThreeOrbit t a (v x) ↔ ThreeOrbit t a x :=
    (hOp (t (p⁻¹ x))).trans ((hOt (p⁻¹ x)).trans (hOpi x))
  have hfree (x : X) (hx : ThreeOrbit t a x) : v x ≠ x := by
    intro h
    have hh : t (p⁻¹ x) = p⁻¹ x := by
      simpa only [v, mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        congrArg (fun z => p⁻¹ z) h
    have hm : t (t (p⁻¹ x)) ≠ p⁻¹ x := c.moved_iff.mpr ((hOpi x).mpr hx)
    exact hm (by rw [hh, hh])
  have hY := complement_commutes t a c p hp
  have hvY (x : X) (hx : ¬ ThreeOrbit t a x) : v x = t x := by
    have hix : ¬ ThreeOrbit t a (p⁻¹ x) := fun h => hx ((hOpi x).mp h)
    simpa only [v, mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hY (p⁻¹ x) hix
  have hinvY (x : X) (hx : ¬ ThreeOrbit t a x) : t⁻¹ x = t x := by
    have h2 : t (t x) = x := by
      by_contra h
      exact hx (c.all_moved x h)
    calc
      t⁻¹ x = t⁻¹ (t (t x)) := congrArg (fun z => t⁻¹ z) h2.symm
      _ = t x := t.symm_apply_apply _
  apply normalizes_of_conjugate t p
  rcases three_point_orientation t v a c hOv hfree with h | h
  · left
    ext x
    by_cases hx : ThreeOrbit t a x
    · exact h x hx
    · exact hvY x hx
  · right
    ext x
    by_cases hx : ThreeOrbit t a x
    · exact h x hx
    · exact (hvY x hx).trans (hinvY x hx).symm

/-- Full sharp statement over arbitrary X, including empty X and infinitely many
    two-point orbits. -/
theorem normalizer_eq_orbitAut_iff (t : Equiv.Perm X) :
    Subgroup.normalizer (Subgroup.zpowers t : Set (Equiv.Perm X)) =
      orbitAut t ↔
      (t ^ 2 = 1) ∨ ((t ^ 2).IsCycle ∧ t ^ 6 = 1) := by
  classical
  constructor
  · intro heq
    by_cases ht : t ^ 2 = 1
    · exact Or.inl ht
    · exact Or.inr ((threeCore_literal_iff t).mp (equality_threeCore t heq ht))
  · rintro (ht | ht)
    · apply le_antisymm (normalizer_le_orbitAut t)
      rw [← (centralizer_eq_orbitAut_iff t).mpr ht]
      exact centralizer_le_normalizer t
    · obtain ⟨a, c⟩ := (threeCore_literal_iff t).mpr ht
      exact le_antisymm (normalizer_le_orbitAut t) (fun p hp =>
        unique_three_normalizes t a c p hp)

end D5.S3.FiniteGroups.OrbitSymmetryDynamics
