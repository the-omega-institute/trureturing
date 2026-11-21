/- GID: D5/S3/ConceptDynamics/Attribution/NormalClosureFixedMass
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/NormalClosureFixedMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full subgroup-fixed seed mass is a row support property of the normal closure. -/

import D5.S3.ConceptDynamics.Attribution.NormalSubgroupFixedMass

/-! Full fixed mass for a subgroup in a finite equivariant calibration. -/

set_option autoImplicit false

open Finset
open D5.S3.ConceptDynamics.Attribution.FixedKernelMass

namespace D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass

universe u v w
variable {G : Type u} {X : Type v} {Y : Type w} [Group G]
variable [MulAction G X] [MulAction G Y] [Fintype X] [Fintype Y]
variable [DecidableEq Y]

private theorem forall_of_sum_filter_eq_total {S : Type*} [Fintype S]
    {predicate : S → Prop} [DecidablePred predicate]
    {mass : S → ℝ} (positive : ∀ s, 0 < mass s)
    (full : ∑ s ∈ univ.filter predicate, mass s = ∑ s, mass s) :
    ∀ s, predicate s := by
  have split := sum_filter_add_sum_filter_not univ predicate mass
  rw [full] at split
  have zero : ∑ s ∈ univ.filter (fun s => ¬ predicate s), mass s = 0 := by linarith
  intro s
  by_contra excluded
  have found := (sum_eq_zero_iff_of_nonneg (fun s _ => (positive s).le)).mp zero s
    (mem_filter.mpr ⟨mem_univ _, excluded⟩)
  exact (positive s).ne' found

omit [Fintype X] [DecidableEq Y] in
private theorem row_mass_one_of_supported (H : Subgroup G)
    (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y) (normalized : ∀ x, ∑ y, P x y = 1)
    (supported : ∀ x y, 0 < P x y → ∀ h : H, h • x = x → h • y = y) :
    ∀ x, rowFixedMass (G := H) P x = 1 := by
  classical
  intro x
  unfold rowFixedMass
  rw [← normalized x]
  rw [sum_filter]
  apply sum_congr rfl
  intro y _
  split
  · rfl
  · next excluded =>
      exact (lt_or_eq_of_le (nn x y)).resolve_left (fun pos => excluded (supported x y pos))

/-- A finite equivariant calibration can concentrate all its seed mass on the fixed points
of a subgroup precisely when each row is supported on outputs fixed by that row's
stabilizer inside the subgroup's normal closure. -/
theorem full_subgroup_fixed_seed_mass_iff
    (H : Subgroup G) (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y)
    (normalized : ∀ x, ∑ y, P x y = 1) (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) :
    let N := Subgroup.normalClosure (H : Set G)
    (∃ (S : Type (max v w)) (_ : Fintype S) (_ : MulAction G S)
      (a : S → ℝ) (f : X → S → Y),
      (∀ s, 0 < a s) ∧ (∑ s, a s = 1) ∧ (∀ g : G, ∀ s, a (g • s) = a s) ∧
      (∀ x y, (∑ s, if f x s = y then a s else 0) = P x y) ∧
      (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
      seedFixedMass (G := H) a = 1) ↔
    ∀ x y, 0 < P x y → ∀ n : N, n • x = x → n • y = y := by
  classical
  let N := Subgroup.normalClosure (H : Set G)
  constructor
  · rintro ⟨S, _, _, a, f, positive, total, _, marginal, equivariant, full⟩
    have allFixed (s : S) (h : H) : h • s = s :=
      forall_of_sum_filter_eq_total positive (full.trans total.symm) s h
    have allNormalFixed (s : S) (n : N) : n • s = s := by
      let action := MulAction.toPermHom G S
      have included : N ≤ action.ker := Subgroup.normalClosure_le_normal fun g hg =>
        Equiv.ext fun s => allFixed s ⟨g, hg⟩
      exact Equiv.congr_fun (included n.property) s
    intro x y pos n fixX
    by_contra notFixY
    have noHit (s : S) : f x s ≠ y := by
      intro hit
      apply notFixY
      have he := equivariant n.val x s
      change f (n • x) (n • s) = n • f x s at he
      simpa only [fixX, allNormalFixed s n, hit] using he.symm
    have row := marginal x y
    simp only [noHit, ite_false, sum_const_zero] at row
    exact pos.ne' row.symm
  · intro supported
    rcases isEmpty_or_nonempty X with empty | inhabited
    · let S := PUnit.{max v w + 1}
      let action : MulAction G S := {
        smul := fun _ s => s
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl }
      let _ := action
      let f (x : X) (_ : S) : Y := (empty.false x).elim
      refine ⟨S, inferInstance, action, fun _ => 1, f, fun _ => zero_lt_one,
        by simp [S], fun _ _ => rfl, fun x _ => (empty.false x).elim,
        fun _ x _ => (empty.false x).elim, ?_⟩
      have allFixed (s : S) (h : H) : h • s = s := rfl
      simp [seedFixedMass, allFixed, S]
    · letI : Nonempty X := inhabited
      obtain ⟨x₀, _, _, S, _, _, a, f, positive, total, invariant, marginal, equivariant, fixed⟩ :=
        D5.S3.ConceptDynamics.Attribution.NormalSubgroupFixedMass.maximal_normal_subgroup_fixed_seed_mass.{u,v,w,0}
          N P nn normalized cov
      have full : seedFixedMass (G := N) a = 1 :=
        fixed.trans (row_mass_one_of_supported N P nn normalized supported x₀)
      have allNormalFixed (s : S) (n : N) : n • s = s :=
        forall_of_sum_filter_eq_total positive (full.trans total.symm) s n
      refine ⟨S, inferInstance, inferInstance, a, f, positive, total, invariant, marginal, equivariant, ?_⟩
      unfold seedFixedMass
      have fixedByH (s : S) (h : H) : h • s = s :=
        allNormalFixed s ⟨h.val, Subgroup.le_normalClosure h.property⟩
      simpa only [fixedByH, implies_true, filter_true_of_mem] using total

end D5.S3.ConceptDynamics.Attribution.NormalClosureFixedMass
