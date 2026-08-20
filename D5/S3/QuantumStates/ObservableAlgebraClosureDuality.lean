/- GID: D5/S3/QuantumStates/ObservableAlgebraClosureDuality
   generality: G
   mirror-B: D5/B/S3/QuantumStates/ObservableAlgebraClosureDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Iterated pullbacks generate exactly the stable relation fiber algebra. -/

import Mathlib

namespace D5.S3.QuantumStates.ObservableAlgebraClosureDuality

variable {Y : Type*}

/-- Functions constant on the fibers of a source relation. -/
def fiberStarAlgebra (R : Y → Y → Prop) : StarSubalgebra ℂ (Y → ℂ) where
  carrier := {f | ∀ ⦃y z⦄, R y z → f y = f z}
  zero_mem' := by intro y z _; rfl
  add_mem' := by
    intro f g hf hg y z h
    simp [hf h, hg h]
  mul_mem' := by
    intro f g hf hg y z h
    simp [hf h, hg h]
  one_mem' := by intro y z _; rfl
  algebraMap_mem' := by intro r y z _; rfl
  star_mem' := by
    intro f hf y z h
    simp [hf h]

/-- The relation agreeing under every finite-time iterate of the transition. -/
def stableRelation (R : Y → Y → Prop) (tau : Y → Y) : Y → Y → Prop :=
  fun y z => ∀ n, R ((tau : Y → Y)^[n] y) ((tau : Y → Y)^[n] z)

/-- The pullback orbit of the source fiber algebra, closed under algebra operations. -/
def koopmanGenerators (R : Y → Y → Prop) (tau : Y → Y) : Set (Y → ℂ) :=
  {f | ∃ n g, g ∈ fiberStarAlgebra R ∧ f = g ∘ (tau : Y → Y)^[n]}

noncomputable def koopmanClosure (R : Y → Y → Prop) (tau : Y → Y) : StarSubalgebra ℂ (Y → ℂ) :=
  StarAlgebra.adjoin ℂ (koopmanGenerators R tau)

noncomputable def stableClassIndicator
    (R : Y → Y → Prop) (tau : Y → Y) (y : Y) : Y → ℂ :=
  fun z => @ite ℂ (stableRelation R tau z y) (Classical.propDecidable _) 1 0

private theorem stableRelation_equivalence
    {R : Y → Y → Prop} {tau : Y → Y} (hR : Equivalence R) :
    Equivalence (stableRelation R tau) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y n
    exact hR.refl _
  · intro y z h n
    exact hR.symm (h n)
  · intro x y z hxy hyz n
    exact hR.trans (hxy n) (hyz n)

private theorem stable_class_indicator_mem
    [Finite Y] {R : Y → Y → Prop} {tau : Y → Y}
    (S : StarSubalgebra ℂ (Y → ℂ))
    (hconstant : ∀ f ∈ S, ∀ ⦃y z⦄, stableRelation R tau y z → f y = f z)
    (hseparates : ∀ y z, ¬ stableRelation R tau y z →
      ∃ f, f ∈ S ∧ f y ≠ f z) (y : Y) :
    stableClassIndicator R tau y ∈ S := by
  classical
  letI : Fintype Y := Fintype.ofFinite Y
  let outside : Finset Y := Finset.univ.filter (fun z => ¬ stableRelation R tau z y)
  have witnesses : ∀ z, ∃ f, f ∈ S ∧
      (stableRelation R tau z y ∨ f y ≠ f z) := by
    intro z
    by_cases hz : stableRelation R tau z y
    · exact ⟨0, S.zero_mem, Or.inl hz⟩
    · exact (hseparates z y hz).imp fun f hf => ⟨hf.1, Or.inr hf.2.symm⟩
  choose g hg hprop using witnesses
  have hdiff : ∀ z ∈ outside, g z y ≠ g z z := by
    intro z hz
    exact (hprop z).resolve_left (Finset.mem_filter.mp hz).2
  let factor (z : Y) : Y → ℂ :=
    (algebraMap ℂ (Y → ℂ) (g z z) - g z)
  let normalized (z : Y) : Y → ℂ :=
    (g z z - g z y)⁻¹ • factor z
  have hfactor : ∀ z ∈ outside, normalized z ∈ S := by
    intro z hz
    apply S.smul_mem (S.sub_mem (S.algebraMap_mem' _) (hg z))
  let product : Y → ℂ := ∏ z ∈ outside, normalized z
  have hproduct : product ∈ S := by
    exact S.prod_mem (by intro z hz; exact hfactor z hz)
  have hproduct_value : ∀ x, product x = stableClassIndicator R tau y x := by
    intro x
    by_cases hxy : stableRelation R tau x y
    · have hone : ∀ z ∈ outside, normalized z x = 1 := by
        intro z hz
        have hzg : g z x = g z y := hconstant (g z) (hg z) hxy
        have hnonzero : g z z - g z y ≠ 0 := sub_ne_zero.mpr (hdiff z hz).symm
        simp [normalized, factor, hzg, hnonzero]
      rw [show stableClassIndicator R tau y x = 1 by
        simp [stableClassIndicator, hxy]]
      simp only [product, Finset.prod_apply]
      exact Finset.prod_eq_one hone
    · have hxmem : x ∈ outside := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
      have hzero : normalized x x = 0 := by
        simp [normalized, factor]
      rw [show stableClassIndicator R tau y x = 0 by
        simp [stableClassIndicator, hxy]]
      simp only [product, Finset.prod_apply]
      exact Finset.prod_eq_zero hxmem hzero
  have heq : product = stableClassIndicator R tau y := funext hproduct_value
  rw [← heq]
  exact hproduct

private theorem stable_separation
    {R : Y → Y → Prop} {tau : Y → Y} (hR : Equivalence R) :
    ∀ y z, ¬ stableRelation R tau y z →
      ∃ f, f ∈ koopmanClosure R tau ∧ f y ≠ f z := by
  classical
  intro y z hnot
  rcases not_forall.mp hnot with ⟨n, hn⟩
  let target := ((tau : Y → Y)^[n] y)
  let sourceFiber : Y → ℂ := fun w => if R w target then 1 else 0
  have hsource : sourceFiber ∈ fiberStarAlgebra R := by
    intro a b hab
    by_cases ha : R a target
    · have hb : R b target := hR.trans (hR.symm hab) ha
      simp [sourceFiber, ha, hb]
    · have hb : ¬ R b target := by
        intro hb
        exact ha (hR.trans hab hb)
      simp [sourceFiber, ha, hb]
  let pullback := sourceFiber ∘ (tau : Y → Y)^[n]
  have hpullback : pullback ∈ koopmanClosure R tau := by
    exact StarAlgebra.subset_adjoin (ℂ) (koopmanGenerators R tau)
      ⟨n, sourceFiber, hsource, rfl⟩
  refine ⟨pullback, hpullback, ?_⟩
  have hself : R ((tau : Y → Y)^[n] y) target := by
    exact hR.refl _
  have hznot : ¬ R ((tau : Y → Y)^[n] z) target := by
    intro hz
    exact hn (hR.symm hz)
  simp [pullback, sourceFiber, target, hself, hznot]

/-- The iterated pullback algebra is exactly the algebra of the stable relation. -/
theorem koopman_closure_eq_stable_fiber_algebra
    [Finite Y] {R : Y → Y → Prop} (tau : Y → Y) (hR : Equivalence R) :
    koopmanClosure R tau = fiberStarAlgebra (stableRelation R tau) := by
  classical
  letI : Fintype Y := Fintype.ofFinite Y
  let stable := stableRelation R tau
  let closure := koopmanClosure R tau
  have hclosure_le : closure ≤ fiberStarAlgebra stable := by
    apply StarAlgebra.adjoin_le
    intro f hf
    rcases hf with ⟨n, g, hg, rfl⟩
    intro y z hyz
    exact hg (hyz n)
  have hconstant : ∀ f ∈ closure, ∀ ⦃y z⦄, stable y z → f y = f z := by
    intro f hf y z hyz
    exact hclosure_le hf hyz
  have hseparates : ∀ y z, ¬ stable y z →
      ∃ f, f ∈ closure ∧ f y ≠ f z := by
    exact stable_separation hR
  have hindicator : ∀ y, stableClassIndicator R tau y ∈ closure := by
    intro y
    exact stable_class_indicator_mem closure hconstant hseparates y
  apply le_antisymm hclosure_le
  intro f hf
  let setoid : Setoid Y :=
    { r := stable
      iseqv := stableRelation_equivalence hR }
  let quotient := Quotient setoid
  let fbar : quotient → ℂ := Quotient.lift f (by
    intro a b hab
    exact hf hab)
  let indicator (q : quotient) : Y → ℂ := fun x =>
    if q = Quotient.mk setoid x then 1 else 0
  have hindicator : ∀ q, indicator q ∈ closure := by
    intro q
    induction q using Quotient.inductionOn with
    | _ y =>
      have hiff : ∀ x, (Quotient.mk setoid y = Quotient.mk setoid x) ↔ stable x y := by
        intro x
        constructor
        · intro h
          exact (stableRelation_equivalence hR).symm (Quotient.exact h)
        · intro h
          exact Quotient.sound ((stableRelation_equivalence hR).symm h)
      have heq : indicator (Quotient.mk setoid y) = stableClassIndicator R tau y := by
        funext x
        simp [indicator, stableClassIndicator, stable, hiff x]
      rw [heq]
      exact hindicator y
  let expansion : Y → ℂ := ∑ q : quotient, fbar q • indicator q
  have hexpansion : expansion ∈ closure := by
    exact closure.sum_mem (by
      intro q hq
      exact closure.smul_mem (hindicator q) (fbar q))
  have hexpansion_eq : expansion = f := by
    funext x
    have hsum : (∑ q : quotient, fbar q • indicator q x) =
        fbar (Quotient.mk setoid x) • indicator (Quotient.mk setoid x) x := by
      apply Finset.sum_eq_single
      · intro q _ hq
        have hzero : indicator q x = 0 := by simp [indicator, hq]
        simp [hzero]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    change (∑ q : quotient, fbar q • indicator q) x = f x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    rw [hsum]
    simp [indicator, fbar]
  rw [← hexpansion_eq]
  exact hexpansion

#print axioms koopman_closure_eq_stable_fiber_algebra

end D5.S3.QuantumStates.ObservableAlgebraClosureDuality
