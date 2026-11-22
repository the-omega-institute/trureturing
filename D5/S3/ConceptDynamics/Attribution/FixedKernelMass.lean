/- GID: D5/S3/ConceptDynamics/Attribution/FixedKernelMass
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/FixedKernelMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp maximum all-group fixed seed mass for an equivariant finite probability kernel. -/

import D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Tactic.Linarith

/-! Maximum mass of globally fixed seeds in an equivariant calibration. -/

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.FixedKernelMass

section UpperBound

variable {G X Y S : Type*} [Group G] [MulAction G X] [MulAction G Y] [MulAction G S]
variable [Fintype Y] [DecidableEq Y] [Fintype S]

private theorem subgroup_fixed_mass_le (H : Subgroup G) (w : S → ℝ) (nn : ∀ s, 0 ≤ w s)
    (f : X → S → Y) (P : X → Y → ℝ)
    (mass : ∀ x y, (∑ s, if f x s = y then w s else 0) = P x y)
    (covariant : ∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s)
    (x : X) [DecidablePred (fun s : S => H ≤ MulAction.stabilizer G s)]
    [DecidablePred (fun y : Y => ∀ h : H, h • x = x → h • y = y)] :
    (∑ s ∈ univ.filter (fun s => H ≤ MulAction.stabilizer G s), w s) ≤
      ∑ y ∈ univ.filter (fun y => ∀ h : H, h • x = x → h • y = y), P x y := by
  classical
  let A (y : Y) : Prop := ∀ h : H, h • x = x → h • y = y
  have permitted (s : S) (fixed : H ≤ MulAction.stabilizer G s) : A (f x s) := by
    intro h hx
    change (h : G) • f x s = f x s
    simpa only [show (h : G) • x = x from hx,
      MulAction.mem_stabilizer_iff.mp (fixed h.property)] using (covariant h.val x s).symm
  calc
    _ ≤ ∑ s ∈ univ.filter (fun s => A (f x s)), w s :=
      sum_le_sum_of_subset_of_nonneg
        (fun s hs => mem_filter.mpr ⟨mem_univ s, permitted s (mem_filter.mp hs).2⟩)
        (fun s _ _ => nn s)
    _ = _ := by
      change _ = ∑ y ∈ univ.filter A, P x y
      simp_rw [← mass, ← Finset.sum_filter]
      symm
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        Finset.sum_fiberwise_eq_sum_filter univ (univ.filter A) (f x) w

end UpperBound

open D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers (stabilizer_possible_iff)

universe u v w

variable {G : Type u} {X : Type v} {Y : Type w} [Group G] [MulAction G X] [MulAction G Y]
variable [Fintype X] [Fintype Y] [DecidableEq Y]

private theorem law_with_fixed_seeds (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y)
    (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y)
    (supported : ∀ x y, 0 < P x y → ∀ g : G, g • x = x → g • y = y) :
    ∃ (S : Type (max v w)) (_ : Fintype S) (w : S → ℝ) (f : X → S → Y),
      (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧
      (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
      (∀ g : G, ∀ x s, f (g • x) s = g • f x s) := by
  classical
  let O := MulAction.orbitRel.Quotient G X
  let _ : Finite O := inferInstance
  let _ : Fintype O := Fintype.ofFinite _
  let orbit (x : X) : O := Quotient.mk'' x
  let rep (o : O) : X := Quotient.out o
  let row (o : O) (y : Y) := P (rep o) y
  let small := @stabilizer_possible_iff PUnit.{1} O Y _ _ _ _ _ _
  have anySupport (x : X) : ∃ y, 0 < P x y := by
    have positive : 0 < ∑ y, P x y := by rw [normalized]; exact zero_lt_one
    simpa only [mem_univ, true_and] using
      (sum_pos_iff_of_nonneg fun y _ => nn x y).mp positive
  obtain ⟨S, _, _, w, sample, pos, total, _, mass, _, _⟩ :=
    (small row (fun o y => nn (rep o) y) (fun o => normalized (rep o))
      (fun g _ _ => by cases g; rfl) ⊥).mpr (fun o => by
        obtain ⟨y, hy⟩ := anySupport (rep o)
        exact ⟨y, hy, fun h _ => by cases h with | mk h hmem => cases h; rfl⟩)
  have reach (x : X) : ∃ g : G, g • rep (orbit x) = x :=
    Quotient.exact (Quotient.out_eq (orbit x)).symm
  choose move hmove using reach
  let f (x : X) (s : S) := move x • sample (orbit x) s
  have samplePos (o : O) (s : S) : 0 < row o (sample o s) := by
    rw [← mass]
    apply lt_of_lt_of_le (pos s)
    simpa using Finset.single_le_sum
        (s := univ) (f := fun t => if sample o t = sample o s then w t else 0)
        (fun t _ => by split <;> first | exact (pos t).le | rfl) (mem_univ s)
  refine ⟨S, inferInstance, w, f, pos, total, ?_, ?_⟩
  · intro x y
    have hit (s : S) : f x s = y ↔ sample (orbit x) s = (move x)⁻¹ • y := by
      exact (eq_inv_smul_iff (g := move x)).symm
    simp_rw [hit]
    rw [mass]
    change P (rep (orbit x)) ((move x)⁻¹ • y) = P x y
    have equal := (cov (move x) (rep (orbit x)) ((move x)⁻¹ • y)).symm
    rwa [hmove, smul_inv_smul] at equal
  · intro g x s
    have same : orbit (g • x) = orbit x :=
      MulAction.orbitRel.Quotient.quotient_smul_eq
    let difference := (move (g • x))⁻¹ * g * move x
    have fixes : difference • rep (orbit x) = rep (orbit x) := by
      dsimp only [difference]
      rw [mul_smul, mul_smul, hmove]
      exact (inv_smul_eq_iff.mpr (hmove (g • x)).symm).trans (congrArg rep same)
    have outputFixed := supported (rep (orbit x)) (sample (orbit x) s)
      (samplePos (orbit x) s) difference fixes
    dsimp only [difference] at outputFixed
    rw [mul_smul, mul_smul] at outputFixed
    change move (g • x) • sample (orbit (g • x)) s = g • move x • sample (orbit x) s
    rw [same]
    exact (inv_smul_eq_iff.mp outputFixed).symm

private def FixedOutput (x : X) (y : Y) : Prop := ∀ g : G, g • x = x → g • y = y

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
private theorem fixed_times_smul (g : G) (x : X) (y : Y) :
    FixedOutput (G := G) (g • x) (g • y) ↔ FixedOutput (G := G) x y := by
  constructor
  · intro fixed h hx
    have input : (g * h * g⁻¹) • (g • x) = g • x := by
      rw [mul_smul, inv_smul_smul, mul_smul, hx]
    have output := fixed (g * h * g⁻¹) input
    rw [mul_smul, inv_smul_smul, mul_smul] at output
    exact (MulAction.toPerm g).injective output
  · intro fixed h hx
    have input : (g⁻¹ * h * g) • x = x := by
      rw [mul_smul, mul_smul, hx, inv_smul_smul]
    have output := congrArg (g • ·) (fixed (g⁻¹ * h * g) input)
    simpa only [mul_smul, smul_inv_smul] using output

private theorem exists_without_constraint (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y)
    (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) :
    ∃ (S : Type (max v w)) (_ : Fintype S) (_ : MulAction G S) (w : S → ℝ) (f : X → S → Y),
      (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧ (∀ g : G, ∀ s, w (g • s) = w s) ∧
      (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
      (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) := by
  classical
  have condition (x : X) : ∃ y : Y, 0 < P x y ∧
      ∀ h : (⊥ : Subgroup G), h • x = x → h • y = y := by
    have positive : 0 < ∑ y, P x y := by rw [normalized]; exact zero_lt_one
    obtain ⟨y, _, hy⟩ := (sum_pos_iff_of_nonneg fun y _ => nn x y).mp positive
    refine ⟨y, hy, fun h _ => ?_⟩
    change h.val • y = y
    rw [Subgroup.mem_bot.mp h.property, one_smul]
  obtain ⟨S, fS, act, w, f, pos, total, wi, mass, equiv, _⟩ :=
    (stabilizer_possible_iff P nn normalized cov (⊥ : Subgroup G)).mpr condition
  exact ⟨S, fS, act, w, f, pos, total, wi, mass, equiv⟩

private theorem fixed_seed_mass_attain (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y)
    (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y)
    (a : ℝ) (ap : 0 < a) (alt : a < 1)
    [∀ x : X, DecidablePred (FixedOutput (G := G) (Y := Y) x)]
    (bound : ∀ x : X, a ≤ ∑ y ∈ univ.filter (FixedOutput (G := G) (Y := Y) x), P x y) :
    ∃ (S : Type (max v w)) (_ : Fintype S) (_ : MulAction G S) (w : S → ℝ) (f : X → S → Y),
      (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧ (∀ g : G, ∀ s, w (g • s) = w s) ∧
      (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
      (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
      ∃ A : Finset S, (∀ s ∈ A, ∀ g : G, g • s = s) ∧ (∑ s ∈ A, w s) = a := by
  classical
  let V (x : X) (y : Y) := if FixedOutput (G := G) x y then P x y else 0
  let M (x : X) := ∑ y, V x y
  have Mp (x : X) : 0 < M x := ap.trans_le (by simpa only [M, V, Finset.sum_filter] using bound x)
  have MA (x : X) : a ≤ M x := by simpa only [M, V, Finset.sum_filter] using bound x
  have VC (g : G) (x : X) (y : Y) : V (g • x) (g • y) = V x y := by
    simp only [V, fixed_times_smul, cov]
  have MC (g : G) (x : X) : M (g • x) = M x := by
    calc
      M (g • x) = ∑ y, V (g • x) (g • y) :=
        (Equiv.sum_comp (MulAction.toPerm g) (V (g • x))).symm
      _ = M x := Finset.sum_congr rfl (fun y _ => VC g x y)
  let Q (x : X) (y : Y) := V x y / M x
  have Qn (x : X) (y : Y) : 0 ≤ Q x y :=
    div_nonneg (by dsimp only [V]; split <;> first | exact nn x y | rfl) (Mp x).le
  have Qt (x : X) : ∑ y, Q x y = 1 := by
    simp only [Q, ← Finset.sum_div]
    exact div_self (Mp x).ne'
  have Qc (g : G) (x : X) (y : Y) : Q (g • x) (g • y) = Q x y := by
    rw [show Q (g • x) (g • y) = V (g • x) (g • y) / M (g • x) from rfl, VC, MC]
  have Qs (x : X) (y : Y) (p : 0 < Q x y) : FixedOutput (G := G) x y := by
    by_contra h
    simp [Q, V, h] at p
  have compare (x : X) (y : Y) : a * Q x y ≤ P x y := by
    by_cases h : FixedOutput (G := G) x y
    · dsimp only [Q, V]
      rw [ite_eq_left h, ← mul_div_assoc]
      exact (div_le_iff₀ (Mp x)).mpr (by
        simpa only [mul_comm (M x)] using mul_le_mul_of_nonneg_right (MA x) (nn x y))
    · simp [Q, V, h, nn x y]
  let R (x : X) (y : Y) := (P x y - a * Q x y) / (1 - a)
  have Rp : 0 < 1 - a := sub_pos.mpr alt
  have Rn (x : X) (y : Y) : 0 ≤ R x y := div_nonneg (sub_nonneg.mpr (compare x y)) Rp.le
  have Rt (x : X) : ∑ y, R x y = 1 := by
    simp only [R, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, Qt, mul_one, normalized]
    exact div_self Rp.ne'
  have Rc (g : G) (x : X) (y : Y) : R (g • x) (g • y) = R x y := by
    simp only [R, cov, Qc]
  obtain ⟨T, _, wt, ft, wtPos, wtTotal, mt, et⟩ :=
    law_with_fixed_seeds Q Qn Qt Qc Qs
  obtain ⟨U, _, _, wu, fu, wuPos, wuTotal, iu, mu, eu⟩ :=
    exists_without_constraint R Rn Rt Rc
  let _ : MulAction G T := {smul := fun _ t => t, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl}
  let S := T ⊕ U
  let w : S → ℝ := Sum.elim (fun t => a * wt t) (fun u => (1 - a) * wu u)
  let f (x : X) : S → Y := Sum.elim (ft x) (fu x)
  refine ⟨S, inferInstance, inferInstance, w, f, ?_, ?_, ?_, ?_, ?_,
    Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩, ?_, ?_⟩
  · intro s
    cases s with
    | inl t => exact mul_pos ap (wtPos t)
    | inr u => exact mul_pos Rp (wuPos u)
  · rw [Fintype.sum_sum_type]
    change (∑ t, a * wt t) + (∑ u, (1 - a) * wu u) = 1
    rw [← Finset.mul_sum, ← Finset.mul_sum, wtTotal, wuTotal, mul_one, mul_one]
    linarith
  · intro g s
    cases s with
    | inl _ => rfl
    | inr u =>
      change (1-a) * wu (g • u) = (1-a) * wu u
      rw [iu]
  · intro x y
    rw [Fintype.sum_sum_type]
    have lterm (t : T) : (if ft x t = y then a * wt t else 0) =
        a * (if ft x t = y then wt t else 0) := by split <;> simp
    have rterm (u : U) : (if fu x u = y then (1-a) * wu u else 0) =
        (1-a) * (if fu x u = y then wu u else 0) := by split <;> simp
    change (∑ t, if ft x t = y then a * wt t else 0) +
      (∑ u, if fu x u = y then (1-a) * wu u else 0) = P x y
    simp_rw [lterm, rterm, ← Finset.mul_sum, mt, mu]
    dsimp only [R]
    have cancelled : (1 - a) * ((P x y - a * Q x y) / (1 - a)) = P x y - a * Q x y :=
      by rw [mul_comm, div_mul_cancel₀ _ Rp.ne']
    rw [cancelled]
    linarith
  · intro g x s
    cases s with
    | inl t => exact et g x t
    | inr u => exact eu g x u
  · intro s hs g
    obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hs
    rfl
  · rw [Finset.sum_map]
    change (∑ t, a * wt t) = a
    rw [← Finset.mul_sum, wtTotal, mul_one]

noncomputable def rowFixedMass (P : X → Y → ℝ) (x : X) : ℝ := by
  classical
  exact ∑ y ∈ univ.filter (FixedOutput (G := G) x), P x y

noncomputable def seedFixedMass {S : Type*} [Fintype S] [MulAction G S] (w : S → ℝ) : ℝ := by
  classical
  exact ∑ s ∈ univ.filter (fun s : S => ∀ g : G, g • s = s), w s

omit [Fintype X] in
private theorem seedFixedMass_le {S : Type*} [Fintype S] [MulAction G S]
    (w : S → ℝ) (nn : ∀ s, 0 ≤ w s) (f : X → S → Y) (P : X → Y → ℝ)
    (mass : ∀ x y, (∑ s, if f x s = y then w s else 0) = P x y)
    (covariant : ∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) (x : X) :
    seedFixedMass (G := G) w ≤ rowFixedMass (G := G) P x := by
  classical
  have rowEq (y : Y) : (∀ h : (⊤ : Subgroup G), h • x = x → h • y = y) ↔
      FixedOutput (G := G) x y := by
    exact ⟨fun hy g => hy ⟨g, trivial⟩, fun hy g => hy g.val⟩
  have seedEq (s : S) : ((⊤ : Subgroup G) ≤ MulAction.stabilizer G s) ↔
      ∀ g : G, g • s = s :=
    ⟨fun h g => MulAction.mem_stabilizer_iff.mp (h (by trivial)),
      fun h g _ => MulAction.mem_stabilizer_iff.mpr (h g)⟩
  simpa only [rowFixedMass, seedFixedMass, rowEq, seedEq] using
    subgroup_fixed_mass_le (⊤ : Subgroup G) w nn f P mass covariant x

theorem maximal_fixed_seed_mass [Nonempty X] (P : X → Y → ℝ)
    (nn : ∀ x y, 0 ≤ P x y) (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ g : G, ∀ x y, P (g • x) (g • y) = P x y) :
    ∃ x₀ : X, (∀ x, rowFixedMass (G := G) P x₀ ≤ rowFixedMass (G := G) P x) ∧
      (∀ (T : Type*) [Fintype T] [MulAction G T] (v : T → ℝ) (F : X → T → Y),
        (∀ t, 0 ≤ v t) →
        (∀ x y, (∑ t, if F x t = y then v t else 0) = P x y) →
        (∀ g : G, ∀ x t, F (g • x) (g • t) = g • F x t) →
        seedFixedMass (G := G) v ≤ rowFixedMass (G := G) P x₀) ∧
      ∃ (S : Type (max v w)) (_ : Fintype S) (_ : MulAction G S)
        (w : S → ℝ) (f : X → S → Y),
        (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧ (∀ g : G, ∀ s, w (g • s) = w s) ∧
        (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) ∧
        (∀ g : G, ∀ x s, f (g • x) (g • s) = g • f x s) ∧
        seedFixedMass (G := G) w = rowFixedMass (G := G) P x₀ := by
  classical
  let R := rowFixedMass (G := G) P
  obtain ⟨x₀, _, hmin⟩ := Finset.exists_min_image univ R univ_nonempty
  let a := R x₀
  have lower (x : X) : a ≤ R x := hmin x (mem_univ x)
  refine ⟨x₀, lower, ?_, ?_⟩
  · intro T _ _ v F hv mass equiv
    exact seedFixedMass_le v hv F P mass equiv x₀
  have an : 0 ≤ a := sum_nonneg (fun y _ => nn x₀ y)
  have a1 : a ≤ 1 := by
    rw [← normalized x₀]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun y _ _ => nn x₀ y)
  rcases an.eq_or_lt with hz | hp
  · obtain ⟨S, _, _, w, f, pos, total, wi, mass, equiv⟩ :=
      exists_without_constraint P nn normalized cov
    refine ⟨S, inferInstance, inferInstance, w, f, pos, total, wi, mass, equiv, ?_⟩
    exact le_antisymm (seedFixedMass_le w (fun s => (pos s).le) f P mass equiv x₀)
      (hz.symm.trans_le (sum_nonneg fun s _ => (pos s).le))
  rcases a1.eq_or_lt with ho | hlt
  · have supported (x : X) (y : Y) (hy : 0 < P x y) :
        FixedOutput (G := G) x y := by
      by_contra outside
      have rest : 0 < ∑ z ∈ univ.filter (fun z => ¬ FixedOutput (G := G) x z), P x z :=
        hy.trans_le (single_le_sum (fun z _ => nn x z) (mem_filter.mpr ⟨mem_univ y, outside⟩))
      have partition :
          R x + (∑ z ∈ univ.filter (fun z => ¬ FixedOutput (G := G) x z), P x z) = 1 := by
        exact (sum_filter_add_sum_filter_not univ (FixedOutput (G := G) x) (P x)).trans (normalized x)
      have atLeast : 1 ≤ R x := ho ▸ lower x
      linarith
    obtain ⟨S, _, w, f, pos, total, mass, equiv⟩ :=
      law_with_fixed_seeds P nn normalized cov supported
    let : MulAction G S := {smul := fun _ s => s, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl}
    refine ⟨S, inferInstance, inferInstance, w, f, pos, total, fun _ _ => rfl, mass, equiv, ?_⟩
    change seedFixedMass (G := G) w = a
    simpa [seedFixedMass, show ∀ (s : S) (g : G), g • s = s from fun _ _ => rfl, ho] using total
  obtain ⟨S, _, _, w, f, pos, total, wi, mass, equiv, A, hA, hweight⟩ :=
    fixed_seed_mass_attain P nn normalized cov a hp hlt lower
  refine ⟨S, inferInstance, inferInstance, w, f, pos, total, wi, mass, equiv, ?_⟩
  apply le_antisymm (seedFixedMass_le w (fun s => (pos s).le) f P mass equiv x₀)
  change a ≤ seedFixedMass (G := G) w
  rw [← hweight]
  exact sum_le_sum_of_subset_of_nonneg
    (fun s hs => mem_filter.mpr ⟨mem_univ s, hA s hs⟩) (fun s _ _ => (pos s).le)

end D5.S3.ConceptDynamics.Attribution.FixedKernelMass
