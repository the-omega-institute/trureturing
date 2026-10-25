import CFMPGenericInteriorCap1483Transient
import Mathlib.Topology.Constructions.SumProd

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.DoubleHalfPlane1490Candidate
open Topology Set
abbrev HalfPlane := {p : ℝ × ℝ // 0 ≤ p.2}
abbrev DoublePlane := HalfPlane ⊕ HalfPlane

def reflect : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1,-p.2)
  invFun p := (p.1,-p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def fold : DoublePlane → ℝ × ℝ :=
  Sum.elim Subtype.val (reflect ∘ Subtype.val)

def seam : DoublePlane → DoublePlane → Prop
  | .inl p,.inr q => p = q ∧ p.val.2 = 0
  | _,_ => False

theorem fold_surjective : Function.Surjective fold := by
  rintro ⟨x,y⟩
  by_cases hy : 0 ≤ y
  · exact ⟨Sum.inl ⟨(x,y),hy⟩,rfl⟩
  · refine ⟨Sum.inr ⟨(x,-y),by linarith⟩,?_⟩
    simp [fold,reflect]

theorem fold_isQuotientMap : IsQuotientMap fold := by
  have hc : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} :=
    isClosed_le continuous_const continuous_snd
  have hclosed : IsClosedMap fold :=
    hc.isClosedMap_subtype_val.sumElim
      (reflect.isClosedMap.comp hc.isClosedMap_subtype_val)
  have hcont : Continuous fold :=
    continuous_subtype_val.sumElim (reflect.continuous.comp continuous_subtype_val)
  exact hclosed.isQuotientMap hcont fold_surjective

theorem full_kernel (a b : DoublePlane) :
    Relation.EqvGen seam a b ↔ fold a = fold b := by
  constructor
  · intro hab
    induction hab with
    | rel a b hab =>
      cases a with
      | inl p =>
        cases b with
        | inl q => exact False.elim hab
        | inr q =>
          obtain ⟨rfl,hp⟩ := hab
          change p.val = (p.val.1,-p.val.2)
          exact Prod.ext rfl (by linarith)
      | inr p => cases b <;> exact False.elim hab
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro he
    cases a with
    | inl p =>
      cases b with
      | inl q =>
        have hpq : p = q := Subtype.ext he
        rw [hpq]
        exact Relation.EqvGen.refl _
      | inr q =>
        change p.val = (q.val.1,-q.val.2) at he
        have hx := congrArg Prod.fst he
        have hy := congrArg Prod.snd he
        have hp : p.val.2 = 0 := by linarith [p.property,q.property]
        have hq : q.val.2 = 0 := by linarith [p.property,q.property]
        have hpq : p = q := Subtype.ext (Prod.ext hx (hp.trans hq.symm))
        exact Relation.EqvGen.rel _ _ ⟨hpq,hp⟩
    | inr p =>
      cases b with
      | inl q =>
        change (p.val.1,-p.val.2) = q.val at he
        have hx := congrArg Prod.fst he
        have hy := congrArg Prod.snd he
        have hp : p.val.2 = 0 := by linarith [p.property,q.property]
        have hq : q.val.2 = 0 := by linarith [p.property,q.property]
        have hqp : q = p := Subtype.ext (Prod.ext hx.symm (hq.trans hp.symm))
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hqp,hq⟩)
      | inr q =>
        have hpq : p = q := Subtype.ext (reflect.injective he)
        rw [hpq]
        exact Relation.EqvGen.refl _

def doubleHalfPlaneHomeomorph :
    Quotient (Relation.EqvGen.setoid seam) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.Quotient.congrRight full_kernel).trans (Topology.IsQuotientMap.homeomorph
    (f := (⟨fold,fold_isQuotientMap.continuous⟩ : C(DoublePlane,ℝ × ℝ))) fold_isQuotientMap)

end D5.S3.Geometry.Gluing.DoubleHalfPlane1490Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.DoubleHalfPlane1490Candidate.fold_surjective,
      ``D5.S3.Geometry.Gluing.DoubleHalfPlane1490Candidate.fold_isQuotientMap,
      ``D5.S3.Geometry.Gluing.DoubleHalfPlane1490Candidate.full_kernel,
      ``D5.S3.Geometry.Gluing.DoubleHalfPlane1490Candidate.doubleHalfPlaneHomeomorph] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1490 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1490 disallowed {ax}"
    Lean.logInfo m!"CFMP1490 CHECKED {name} axioms={axioms}"
