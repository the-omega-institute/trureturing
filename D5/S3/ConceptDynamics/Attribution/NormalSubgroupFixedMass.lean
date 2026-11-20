/- GID: D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The row bound is attained for every normal subgroup of a finite-kernel action. -/

import D5.S3.ConceptDynamics.Attribution.FixedKernelMass
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-! Normal subgroups retain their sharp fixed-seed mass upon symmetrizing table laws. -/

set_option autoImplicit false

open Finset
open D5.S3.ConceptDynamics.Attribution.FixedKernelMass

namespace D5.S3.ConceptDynamics.Attribution.NormalSubgroupFixedMass

universe u v w s

variable {G : Type u} {X : Type v} {Y : Type w}
variable [Group G] [MulAction G X] [MulAction G Y]

local instance (priority := 2000) tableSMul : SMul G (X → Y) where
  smul g t x := g • t (g⁻¹ • x)

local instance (priority := 2000) tableAction : MulAction G (X → Y) where
  toSMul := tableSMul
  one_smul t := funext fun x => by
    change (1 : G) • t ((1 : G)⁻¹ • x) = t x
    rw [inv_one, one_smul, one_smul]
  mul_smul g h t := funext fun x => by
    change (g * h) • t ((g * h)⁻¹ • x) = g • (h • t (h⁻¹ • (g⁻¹ • x)))
    rw [mul_inv_rev, mul_smul h⁻¹, mul_smul g]

private theorem readout_smul (g : G) (t : X → Y) (x : X) :
    (g • t) (g • x) = g • t x := by
  change g • t (g⁻¹ • (g • x)) = _
  rw [inv_smul_smul]

private theorem fixed_smul_iff (H : Subgroup G) [H.Normal] (g : G) (t : X → Y) :
    g • t ∈ MulAction.fixedPoints H (X → Y) ↔ t ∈ MulAction.fixedPoints H (X → Y) := by
  refine ⟨?_, smul_mem_fixedPoints_of_normal g⟩
  intro fixed
  simpa only [inv_smul_smul] using smul_mem_fixedPoints_of_normal g⁻¹ fixed

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

private theorem symmetrize (H : Subgroup G) [H.Normal] (P : X → Y → ℝ)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y)
    (p : (X → Y) → ℝ) (nn : ∀ t, 0 ≤ p t) (total : ∑ t, p t = 1)
    (marginal : ∀ x y, (∑ t, if t x = y then p t else 0) = P x y) :
    ∃ q : (X → Y) → ℝ,
      (∀ t, 0 ≤ q t) ∧ (∑ t, q t = 1) ∧ (∀ (g : G) t, q (g • t) = q t) ∧
      (∀ x y, (∑ t, if t x = y then q t else 0) = P x y) ∧
      seedFixedMass (G := H) q = seedFixedMass (G := H) p := by
  classical
  let ρ := MulAction.toPermHom G (X → Y)
  let K := ρ.range
  let _ : Fintype K := Fintype.ofFinite _
  let translate (a : K) (t : X → Y) := a.val.symm t
  let n : ℝ := Fintype.card K
  have npos : 0 < n := Nat.cast_pos.mpr (Fintype.card_pos (α := K))
  let q (t : X → Y) := (∑ a : K, p (translate a t)) / n
  have average (A : Finset (X → Y)) (c : ℝ)
      (hA : ∀ a : K, (∑ t ∈ A, p (translate a t)) = c) : (∑ t ∈ A, q t) = c := by
    simp only [q, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp_rw [hA, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change n * c / n = c
    rw [mul_comm, mul_div_cancel_right₀ _ npos.ne']
  have shift (a : K) (A : Finset (X → Y))
      (stable : ∀ t, t ∈ A ↔ a.val t ∈ A) :
      (∑ t ∈ A, p (translate a t)) = ∑ t ∈ A, p t := by
    apply Finset.sum_bij' (fun t _ => a.val.symm t) (fun t _ => a.val t)
    · intro t ht
      exact (stable (a.val.symm t)).mpr (by simpa using ht)
    · intro t ht
      exact (stable t).mp ht
    · intro t _
      exact a.val.apply_symm_apply t
    · intro t _
      exact a.val.symm_apply_apply t
    · intro t _
      rfl
  refine ⟨q, fun t => div_nonneg (sum_nonneg fun a _ => nn (translate a t)) npos.le,
    average univ 1 (fun a => (shift a univ (fun _ => by simp)).trans total),
    ?_, ?_, ?_⟩
  · intro g t
    let k : K := ⟨ρ g, ⟨g, rfl⟩⟩
    change (∑ a : K, p (translate a (g • t))) / n = (∑ a, p (translate a t)) / n
    apply congrArg (· / n)
    rw [← Equiv.sum_comp (Equiv.mulLeft k)]
    apply Finset.sum_congr rfl
    intro a _
    change p ((k.val * a.val).symm (g • t)) = p (a.val.symm t)
    change p (a.val.symm (k.val.symm (k.val t))) = _
    rw [Equiv.symm_apply_apply]
  · intro x y
    rw [← Finset.sum_filter]
    apply average
    intro a
    obtain ⟨g, hg⟩ := a.property
    have action (t : X → Y) : a.val t = g • t := by rw [← hg]; rfl
    have mapped (t : X → Y) : t (g⁻¹ • x) = g⁻¹ • y ↔ a.val t x = y := by
      rw [action]
      change t (g⁻¹ • x) = g⁻¹ • y ↔ g • t (g⁻¹ • x) = y
      exact eq_inv_smul_iff
    calc
      _ = ∑ t ∈ univ.filter (fun t : X → Y => t (g⁻¹ • x) = g⁻¹ • y), p t := by
        apply Finset.sum_bij' (fun t _ => a.val.symm t) (fun t _ => a.val t)
        · intro t ht
          apply mem_filter.mpr
          exact ⟨mem_univ _, (mapped _).mpr (by simpa using (mem_filter.mp ht).2)⟩
        · intro t ht
          exact mem_filter.mpr ⟨mem_univ _, (mapped t).mp (mem_filter.mp ht).2⟩
        · intro t _
          exact a.val.apply_symm_apply t
        · intro t _
          exact a.val.symm_apply_apply t
        · intro t _
          rfl
      _ = P (g⁻¹ • x) (g⁻¹ • y) := by simpa only [Finset.sum_filter] using marginal _ _
      _ = P x y := by
        simpa only [smul_inv_smul] using (cov g (g⁻¹ • x) (g⁻¹ • y)).symm
  · unfold seedFixedMass
    apply average
    intro a
    obtain ⟨g, hg⟩ := a.property
    apply shift
    intro t
    simp only [mem_filter, mem_univ, true_and]
    have action : a.val t = g • t := by rw [← hg]; rfl
    rw [action]
    exact (fixed_smul_iff H g t).symm

omit [DecidableEq X] in
/-- For a normal subgroup, the least mass on outputs fixed by a row stabilizer
inside that subgroup is the sharp bound on the subgroup's fixed seed mass. -/
theorem maximal_normal_subgroup_fixed_seed_mass [Nonempty X] (H : Subgroup G) [H.Normal]
    (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y) (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) :
    ∃ x₀ : X, (∀ x, rowFixedMass (G := H) P x₀ ≤ rowFixedMass (G := H) P x) ∧
      (∀ (T : Type s) [Fintype T] [MulAction G T] (weights : T → ℝ) (readout : X → T → Y),
        (∀ t, 0 ≤ weights t) →
        (∀ x y, (∑ t, if readout x t = y then weights t else 0) = P x y) →
        (∀ g : G, ∀ x t, readout (g • x) (g • t) = g • readout x t) →
        seedFixedMass (G := H) weights ≤ rowFixedMass (G := H) P x₀) ∧
      ∃ (T : Type (max v w)) (_ : Fintype T) (_ : MulAction G T)
        (weights : T → ℝ) (readout : X → T → Y),
        (∀ t, 0 < weights t) ∧ (∑ t, weights t = 1) ∧
        (∀ g : G, ∀ t, weights (g • t) = weights t) ∧
        (∀ x y, (∑ t, if readout x t = y then weights t else 0) = P x y) ∧
        (∀ g : G, ∀ x t, readout (g • x) (g • t) = g • readout x t) ∧
        seedFixedMass (G := H) weights = rowFixedMass (G := H) P x₀ := by
  classical
  obtain ⟨x₀, least, upperBound, S, _, _, weights, readout, positive, total, _, marginal,
    covariant, attained⟩ :=
    maximal_fixed_seed_mass.{u,v,w,s} (G := H) P nn normalized (fun h => cov h.val)
  have upper (T : Type s) [Fintype T] [MulAction G T] (a : T → ℝ) (f : X → T → Y)
      (hn : ∀ t, 0 ≤ a t) (hp : ∀ x y, (∑ t, if f x t = y then a t else 0) = P x y)
      (hc : ∀ g : G, ∀ x t, f (g • x) (g • t) = g • f x t) :
      seedFixedMass (G := H) a ≤ rowFixedMass (G := H) P x₀ :=
    upperBound T a f hn hp (fun h => hc h.val)
  refine ⟨x₀, least, upper, ?_⟩
  let table (s : S) (x : X) := readout x s
  let p (t : X → Y) := ∑ s, if table s = t then weights s else 0
  have push (A : Finset (X → Y)) :
      (∑ t ∈ A, p t) = ∑ s ∈ univ.filter (fun s => table s ∈ A), weights s := by
    simpa only [p, Finset.sum_filter] using
      Finset.sum_fiberwise_eq_sum_filter univ A table weights
  have pn (t : X → Y) : 0 ≤ p t := by
    exact sum_nonneg (fun s _ => by split <;> first | exact (positive s).le | rfl)
  have ptotal : ∑ t, p t = 1 := by simpa using (push univ).trans (by simpa using total)
  have pmarginal (x : X) (y : Y) : (∑ t, if t x = y then p t else 0) = P x y := by
    rw [← Finset.sum_filter, push]
    simpa only [Finset.sum_filter, mem_filter, mem_univ, true_and, table] using marginal x y
  have pushFixed : seedFixedMass (G := H) weights ≤ seedFixedMass (G := H) p := by
    unfold seedFixedMass
    rw [push]
    apply sum_le_sum_of_subset_of_nonneg
    · intro s hs
      refine mem_filter.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
      intro h
      apply funext
      intro x
      change h.val • readout (h.val⁻¹ • x) s = readout x s
      have moved := covariant h (h.val⁻¹ • x) s
      change readout (h.val • (h.val⁻¹ • x)) (h • s) =
        h.val • readout (h.val⁻¹ • x) s at moved
      rw [smul_inv_smul, (mem_filter.mp hs).2 h] at moved
      exact moved.symm
    · exact fun s _ _ => (positive s).le
  obtain ⟨q, qn, qtotal, invariant, qmarginal, qfixed⟩ :=
    symmetrize H P cov p pn ptotal pmarginal
  let T := {t : X → Y // 0 < q t}
  let action : MulAction G T := {
    smul := fun g t => ⟨g • t.val, invariant g t.val ▸ t.property⟩
    one_smul := fun t => Subtype.ext (one_smul G t.val)
    mul_smul := fun g h t => Subtype.ext (mul_smul g h t.val) }
  let weight (t : T) := q t.val
  let eval (x : X) (t : T) := t.val x
  have supportSum (a : (X → Y) → ℝ) (zero : ∀ t, q t = 0 → a t = 0) :
      (∑ t : T, a t.val) = ∑ t, a t :=
    FiniteKernelStabilizers.row_sum (fun (_ : Unit) => q) (fun _ => qn) () a zero
  let _ := action
  have newMarginal (x : X) (y : Y) : (∑ t, if eval x t = y then weight t else 0) = P x y :=
    (supportSum (fun t => if t x = y then q t else 0) (fun t z => by simp [z])).trans (qmarginal x y)
  have newCovariant (g : G) (x : X) (t : T) : eval (g • x) (g • t) = g • eval x t :=
    readout_smul g t.val x
  refine ⟨T, inferInstance, action, weight, eval, fun t => t.property,
    (supportSum q (fun _ z => z)).trans qtotal, fun g t => invariant g t.val,
    newMarginal, newCovariant, ?_⟩
  obtain ⟨x₁, leastAtSupport, boundAtSupport, _⟩ :=
    maximal_fixed_seed_mass.{u,v,w,max v w} (G := H) P nn normalized (fun h => cov h.val)
  apply le_antisymm
  · exact (boundAtSupport T weight eval (fun t => t.property.le) newMarginal
      (fun h => newCovariant h.val)).trans (leastAtSupport x₀)
  · have sameFixed : seedFixedMass (G := H) weight = seedFixedMass (G := H) q := by
      unfold seedFixedMass
      simp only [Finset.sum_filter]
      have same (t : T) : (∀ h : H, h • t = t) ↔ ∀ h : H, h • t.val = t.val := by
        exact ⟨fun fixed h => congrArg Subtype.val (fixed h), fun fixed h => Subtype.ext (fixed h)⟩
      simpa only [same, weight] using supportSum
        (fun t => if ∀ h : H, h • t = t then q t else 0) (fun t z => by simp [z])
    rw [sameFixed, qfixed, ← attained]
    exact pushFixed

end D5.S3.ConceptDynamics.Attribution.NormalSubgroupFixedMass
