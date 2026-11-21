/- GID: D5/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported fixed outputs characterize seed stabilizers for equivariant finite kernels. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers

universe u v w

variable {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X] [MulAction G Y]

private abbrev Table (P : X → Y → ℝ) := (x : X) → {y : Y // 0 < P x y}

@[instance_reducible] private def tableAction (P : X → Y → ℝ)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) : MulAction G (Table P) where
  smul g t x := ⟨g • (t (g⁻¹ • x)).val, by
    have same := cov g (g⁻¹ • x) (t (g⁻¹ • x)).val
    rw [smul_inv_smul] at same
    exact same.symm ▸ (t (g⁻¹ • x)).property⟩
  one_smul t := funext fun x => Subtype.ext (by
    change (1 : G) • (t ((1 : G)⁻¹ • x)).val = (t x).val
    rw [inv_one, one_smul, one_smul])
  mul_smul g h t := funext fun x => Subtype.ext (by
    change (g * h) • (t ((g * h)⁻¹ • x)).val = g • h • (t (h⁻¹ • g⁻¹ • x)).val
    rw [mul_inv_rev, mul_smul h⁻¹ g⁻¹, mul_smul g h])

private theorem selector {P : X → Y → ℝ} (H : Subgroup G)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y)
    (fixed : ∀ x : X, ∃ y : Y, 0 < P x y ∧ ∀ h : H, h • x = x → h • y = y) :
    ∃ t : Table P, ∀ h : H, ∀ x, (t (h • x)).val = h • (t x).val := by
  classical
  let q (x : X) : MulAction.orbitRel.Quotient H X := Quotient.mk'' x
  let rep (x : X) : X := Quotient.out (q x)
  have equivalent (x : X) : MulAction.orbitRel H X x (rep x) :=
    Quotient.exact (Quotient.out_eq (q x)).symm
  have reach (x : X) : ∃ h : H, h • rep x = x := equivalent x
  choose move hmove using reach
  choose pick hpos hfix using fixed
  have reps (h : H) (x : X) : rep (h • x) = rep x := by
    apply congrArg Quotient.out
    exact Quotient.sound (show MulAction.orbitRel H X (h • x) x from ⟨h, rfl⟩)
  refine ⟨fun x => ⟨move x • pick (rep x), ?_⟩, ?_⟩
  · have same := cov (move x).val (rep x) (pick (rep x))
    change P (move x • rep x) (move x • pick (rep x)) = _ at same
    rw [hmove x] at same
    exact same.symm ▸ hpos (rep x)
  · intro h x
    simp only
    let d : H := (move (h • x))⁻¹ * h * move x
    have eq : d • rep x = rep x := by
      dsimp only [d]
      rw [mul_smul, mul_smul, hmove x]
      exact (inv_smul_eq_iff.mpr (hmove (h • x)).symm).trans (reps h x)
    have holds := hfix (rep x) d eq
    dsimp only [d] at holds
    rw [reps]
    rw [mul_smul, mul_smul] at holds
    exact (inv_smul_eq_iff.mp holds).symm

theorem row_sum {X Y : Type*} [Fintype Y] (P : X → Y → ℝ)
    (nn : ∀ x y, 0 ≤ P x y) (x : X) (F : Y → ℝ)
    (zero : ∀ y, P x y = 0 → F y = 0) :
    (∑ y : {y : Y // 0 < P x y}, F y.val) = ∑ y, F y := by
  classical
  rw [← Finset.sum_subtype (univ.filter fun y => 0 < P x y) (by simp) F, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : 0 < P x y
  · exact ite_eq_left h
  · rw [ite_eq_right h, zero y (le_antisymm (le_of_not_gt h) (nn x y))]

/-- A subgroup can fix a seed exactly when every row has a supported output fixed
by that row's stabilizer inside the subgroup. -/
theorem stabilizer_possible_iff [Fintype X] [Fintype Y] [DecidableEq Y]
    (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y) (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) (H : Subgroup G) :
    (∃ (S : Type (max v w)) (_ : Fintype S) (_ : MulAction G S) (w : S → ℝ) (f : X → S → Y),
      (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧ (∀ g : G, ∀ s, w (g • s) = w s) ∧
      (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
      (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
      (∃ s : S, H ≤ MulAction.stabilizer G s)) ↔
    (∀ x : X, ∃ y : Y, 0 < P x y ∧ ∀ h : H, h • x = x → h • y = y) := by
  classical
  constructor
  · rintro ⟨S, _, _, w, f, pos, _, _, mass, equivariant, s, stab⟩ x
    refine ⟨f x s, ?_, ?_⟩
    · rw [← mass]
      apply lt_of_lt_of_le (pos s)
      simpa using Finset.single_le_sum
        (s := univ) (f := fun t => if f x t = f x s then w t else 0)
        (fun t _ => by split <;> first | exact (pos t).le | rfl) (mem_univ s)
    · intro h hx
      change (h : G) • f x s = f x s
      simpa only [show (h : G) • x = x from hx,
        MulAction.mem_stabilizer_iff.mp (stab h.property)] using
          (equivariant h.val x s).symm
  · intro fixed
    let _ : MulAction G (Table P) := tableAction P cov
    let w (t : Table P) : ℝ := ∏ x, P x (t x).val
    let f (x : X) (t : Table P) : Y := (t x).val
    have row (x : X) : ∑ y : {y : Y // 0 < P x y}, P x y.val = 1 :=
      (row_sum P nn x (P x) (fun _ h => h)).trans (normalized x)
    refine ⟨Table P, inferInstance, inferInstance, w, f, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t
      exact Finset.prod_pos fun x _ => (t x).property
    · change ∑ t : Table P, ∏ x, P x (t x).val = 1
      rw [← Fintype.prod_sum (fun (a : X) (b : {y : Y // 0 < P a y}) => P a b.val)]
      simp [row]
    · intro g t
      calc
        w (g • t) = ∏ x, P (g • x) ((g • t) (g • x)).val :=
          (Equiv.prod_comp (MulAction.toPerm g) (fun x : X => P x ((g • t) x).val)).symm
        _ = w t := by
          apply Finset.prod_congr rfl
          intro x _
          change P (g • x) (g • (t (g⁻¹ • (g • x))).val) = P x (t x).val
          rw [inv_smul_smul, cov]
    · intro x y
      let L (a : X) (b : Y) := if a = x then (if b = y then P a b else 0) else P a b
      have entry (t : Table P) :
          (if f x t = y then w t else 0) = ∏ a, L a (t a).val := by
        by_cases eq : f x t = y
        · rw [ite_eq_left eq]
          exact Finset.prod_congr rfl fun a _ => by
            by_cases e : a = x
            · subst a
              have same : (t x).val = y := eq
              simp [L, same]
            · simp [L, e]
        · rw [ite_eq_right eq]
          symm
          have ne : (t x).val ≠ y := eq
          exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [L, ne])
      rw [Finset.sum_congr rfl (fun t _ => entry t),
        ← Fintype.prod_sum (fun (a : X) (b : {y : Y // 0 < P a y}) => L a b.val)]
      have each (a : X) : (∑ b : {b : Y // 0 < P a b}, L a b.val) =
          if a = x then P x y else 1 := by
        by_cases eq : a = x
        · subst a
          simp only [L, ite_eq_left rfl]
          rw [row_sum P nn x (fun b => if b = y then P x b else 0)
            (fun b h => by simp [h])]
          simp
        · simpa [L, eq] using row a
      simp_rw [each]
      exact Fintype.prod_ite_eq' x (fun _ => P x y)
    · intro g x t
      change g • (t (g⁻¹ • (g • x))).val = g • (t x).val
      rw [inv_smul_smul]
    · obtain ⟨t, ht⟩ := selector H cov fixed
      refine ⟨t, fun g hg => MulAction.mem_stabilizer_iff.mpr ?_⟩
      funext x
      apply Subtype.ext
      change g • (t (g⁻¹ • x)).val = (t x).val
      have eq := (ht (⟨g, hg⟩ : H) (g⁻¹ • x)).symm
      change g • (t (g⁻¹ • x)).val = (t (g • (g⁻¹ • x))).val at eq
      rwa [smul_inv_smul] at eq

/-- A uniform independent coset coordinate restricts the selected seed stabilizer
to the prescribed subgroup while preserving the calibration. -/
theorem exact_stabilizer_possible_iff [Fintype X] [Fintype Y] [DecidableEq Y]
    (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y) (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) (H : Subgroup G) :
    (∃ (S : Type (max u v w)) (_ : Fintype S) (_ : MulAction G S) (w : S → ℝ) (f : X → S → Y),
      (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧ (∀ g : G, ∀ s, w (g • s) = w s) ∧
      (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
      (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
      (∃ s : S, MulAction.stabilizer G s = H)) ↔
    Finite (G ⧸ H) ∧
      (∀ x : X, ∃ y : Y, 0 < P x y ∧ ∀ h : H, h • x = x → h • y = y) := by
  classical
  constructor
  · rintro ⟨S, _, _, w, f, pos, _, _, mass, equivariant, s, stab⟩
    have index : Finite (G ⧸ H) := by
      rw [← stab]
      exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G s)
    refine ⟨index, fun x => ⟨f x s, ?_, ?_⟩⟩
    · rw [← mass]
      apply lt_of_lt_of_le (pos s)
      simpa using Finset.single_le_sum
        (s := univ) (f := fun t => if f x t = f x s then w t else 0)
        (fun t _ => by split <;> first | exact (pos t).le | rfl) (mem_univ s)
    · intro h hx
      change (h : G) • f x s = f x s
      simpa only [show (h : G) • x = x from hx,
        MulAction.mem_stabilizer_iff.mp (stab.ge h.property)] using
          (equivariant h.val x s).symm
  · rintro ⟨index, fixed⟩
    let _ : Finite (G ⧸ H) := index
    obtain ⟨S, _, _, w, f, pos, total, wi, mass, equiv, s, stab⟩ :=
      (stabilizer_possible_iff P nn normalized cov H).mpr fixed
    let Q := G ⧸ H
    let _ : Fintype Q := Fintype.ofFinite Q
    let q : Q := ((1 : G) : G ⧸ H)
    have positive : 0 < (Fintype.card Q : ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨q⟩
    let w' (t : S × Q) := w t.1 / Fintype.card Q
    let f' (x : X) (t : S × Q) := f x t.1
    have marginal (weight : S → ℝ) (t : S) : (∑ _ : Q, weight t / Fintype.card Q) = weight t := by
      simp [nsmul_eq_mul, mul_div_cancel₀ _ positive.ne']
    refine ⟨S × Q, inferInstance, inferInstance, w', f', ?_, ?_, ?_, ?_, ?_, (s, q), ?_⟩
    · intro z
      exact div_pos (pos z.1) positive
    · rw [Fintype.sum_prod_type]
      exact (Finset.sum_congr rfl fun t _ => marginal w t).trans total
    · intro g z
      change w (g • z.1) / Fintype.card Q = w z.1 / Fintype.card Q
      rw [wi]
    · intro x y
      rw [Fintype.sum_prod_type]
      convert mass x y using 1
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : f x t = y <;> simp [w', f', h, marginal]
    · intro g x z
      exact equiv g x z.1
    · ext g
      rw [MulAction.mem_stabilizer_iff]
      change (g • s, g • q) = (s, q) ↔ g ∈ H
      rw [Prod.mk.injEq, ← MulAction.mem_stabilizer_iff, ← MulAction.mem_stabilizer_iff]
      rw [show MulAction.stabilizer G q = H from MulAction.stabilizer_quotient H]
      exact ⟨And.right, fun h => ⟨stab h, h⟩⟩

end D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
