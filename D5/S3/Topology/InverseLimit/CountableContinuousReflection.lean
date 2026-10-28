/- GID: D5/S3/Topology/InverseLimit/CountableContinuousReflection
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/CountableContinuousReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Each continuous real test descends exactly to a proper stage above any base. -/

import D5.S3.Topology.InverseLimit.CountableClopenReflection
import Mathlib.Topology.ContinuousMap.LocallyConstant
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic.Positivity

/-!
# Continuous real tests reflect below omega-one

A countable sequence of locally constant uniform approximants admits one
proper common stage. Equal projections at that stage force equality of
all approximants, hence of the original real test. Surjectivity of the
actual limit projection then permits continuous quotient descent.

This is standard compact inverse-limit background. The stage depends on
the chosen test; no universal stage for all continuous tests is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Set Function
open scoped Ordinal

namespace D5.S3.Topology.InverseLimit.CountableContinuousReflection

open CountableClopenReflection

/-- Every continuous real test on an actual omega-one profinite limit
factors exactly and continuously through a proper stage above any base. -/
theorem exists_stage (F : CountableStageᵒᵖ ⥤ Profinite.{1})
    [∀ j, Nonempty (F.obj j)] (C : Cone F) (hC : IsLimit C)
    (hs : ∀ {i j} (a : i ⟶ j), Surjective (F.map a))
    (base : CountableStage) (f : C(C.pt, ℝ)) :
    ∃ β : CountableStage, base ≤ β ∧
      ∃ g : C(F.obj (op β), ℝ), ∀ x, f x = g (C.π.app (op β) x) := by
  classical
  let A : Subalgebra ℝ C(C.pt, ℝ) := (LocallyConstant.toContinuousMapAlgHom ℝ).range
  have hA : A.SeparatesPoints :=
    LocallyConstant.separatesPoints_range_toContinuousMapAlgHom ℝ
  have happ : ∀ n : ℕ, ∃ l : LocallyConstant C.pt ℝ,
      ∀ x, ‖l x - f x‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨a, ha⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
        A hA f f.continuous (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨l, hl⟩ := a.property
    refine ⟨l, fun x => ?_⟩
    have hlx := congrArg (fun t : C(C.pt, ℝ) => t x) hl
    change l x = (a : C(C.pt, ℝ)) x at hlx
    rw [hlx]
    exact ha x
  choose l hl using happ
  choose j g hg using fun n => Profinite.exists_locallyConstant.{0, 1} C hC (l n)
  let b : Option ℕ → Ordinal.{0} := fun i => i.elim base.1 (fun n => (j n).unop.1)
  have hb : ∀ i, b i < ω₁ := by
    intro i
    cases i with
    | none => exact base.2
    | some n => exact (j n).unop.2
  let β : CountableStage := ⟨⨆ n, b n, Ordinal.iSup_lt_omega_one hb⟩
  have hbase : base ≤ β := Ordinal.le_iSup b none
  have hj : ∀ n, (j n).unop ≤ β := fun n => Ordinal.le_iSup b (some n)
  let q : ∀ n, op β ⟶ j n := fun n => (homOfLE (hj n)).op
  have hfiber : (f : C.pt → ℝ).FactorsThrough (C.π.app (op β)) := by
    intro x y hxy
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    have hlxy : l n x = l n y := by
      rw [hg n]
      change g n (C.π.app (j n) x) = g n (C.π.app (j n) y)
      apply congrArg (g n)
      calc
        C.π.app (j n) x = F.map (q n) (C.π.app (op β) x) :=
          (ConcreteCategory.congr_hom (C.w (q n)) x).symm
        _ = F.map (q n) (C.π.app (op β) y) := congrArg (F.map (q n)) hxy
        _ = C.π.app (j n) y := ConcreteCategory.congr_hom (C.w (q n)) y
    have hx : dist (f x) (l n x) < ε / 2 := by
      rw [dist_comm, dist_eq_norm]
      exact (hl n x).trans hn
    have hy : dist (l n y) (f y) < ε / 2 := by
      rw [dist_eq_norm]
      exact (hl n y).trans hn
    calc
      dist (f x) (f y) ≤ dist (f x) (l n x) + dist (l n x) (f y) :=
        dist_triangle _ _ _
      _ = dist (f x) (l n x) + dist (l n y) (f y) := by rw [hlxy]
      _ ≤ ε / 2 + ε / 2 := add_le_add hx.le hy.le
      _ = ε := add_halves ε
  obtain ⟨g₀, hg₀⟩ := (Function.factorsThrough_iff (f : C.pt → ℝ)).mp hfiber
  have hp := projection_surjective.{0, 1} F C hC hs (op β)
  have hquot : Topology.IsQuotientMap (C.π.app (op β)) :=
    .of_surjective_continuous hp (C.π.app (op β)).hom.hom.continuous
  have hgcont : Continuous g₀ := hquot.continuous_iff.mpr (by
    rw [← hg₀]
    exact f.continuous)
  exact ⟨β, hbase, ⟨g₀, hgcont⟩, fun x => congrFun hg₀ x⟩

end D5.S3.Topology.InverseLimit.CountableContinuousReflection
