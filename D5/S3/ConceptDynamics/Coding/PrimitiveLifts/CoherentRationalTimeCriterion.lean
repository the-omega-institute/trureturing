/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/CoherentRationalTimeCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/CoherentRationalTimeCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Finite isotypic classes exactly control coherent rational time on arbitrary families. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RationalTimeAction
import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RationalReturnAtlasCriterion

/-! A single rational action on an arbitrary dependent family of complete return charts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.CoherentRationalTimeCriterion

open PrimitiveLiftRootCriterion PrimeOrbitRootCriterion FiniteOrbitRootCriterion
universe u v w z

private theorem finite_rational_hom_trivial {K : Type z} [Group K] [Finite K]
    (f : Multiplicative ℚ →* K) (q : Multiplicative ℚ) : f q = 1 := by
  have hn : (Nat.card K : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := K)).ne'
  have hq : (Multiplicative.ofAdd (q.toAdd / Nat.card K)) ^ Nat.card K = q := by
    apply Multiplicative.toAdd.injective
    change (Nat.card K : ℚ) * (q.toAdd / Nat.card K) = q.toAdd
    field_simp
  rw [← hq, map_pow, pow_card_eq_one']

section Family
variable {H : Type u} [Group H] {ι : Type w} {X : ι → Type v}
  (A : ∀ i, ReturnAtlas H (X i))

private theorem restrict_finite_class
    (ρ : Multiplicative ℚ →* Equiv.Perm (Σ i, X i))
    (hd : ∀ q a x, ρ q (jointDeck A a x) = jointDeck A a (ρ q x))
    (ht : (ρ (Multiplicative.ofAdd (1 : ℚ)) : (Σ i, X i) → Σ i, X i) = jointTime A)
    (i : ι) [Finite {j // Isotypic A i j}] :
    ∃ ψ : Multiplicative ℚ →* Equiv.Perm (X i),
      (∀ q, (A i).Equivariant (ψ q)) ∧
      (ψ (Multiplicative.ofAdd (1 : ℚ)) : X i → X i) = (A i).time := by
  have hc (q : Multiplicative ℚ) : Function.Commute (ρ q) (jointTime A) := by
    intro x
    rw [← ht]
    change (ρ q * ρ (Multiplicative.ofAdd (1 : ℚ))) x =
      (ρ (Multiplicative.ofAdd (1 : ℚ)) * ρ q) x
    rw [← map_mul, ← map_mul, mul_comm q]
  let tag (q : Multiplicative ℚ) (j : ι) := (ρ q ⟨j,(A j).point 0 1⟩).1
  have routing (q : Multiplicative ℚ) (x : Σ j, X j) :
      (ρ q x).1 = tag q x.1 := component_constant A (ρ q) (hd q) (hc q) x.1 x.2
  let σ : Multiplicative ℚ →* Function.End ι := {
    toFun := tag
    map_one' := by
      funext j
      change (ρ 1 ⟨j,(A j).point 0 1⟩).1 = j
      rw [map_one]
      rfl
    map_mul' := by
      intro p q
      funext j
      change (ρ (p*q) ⟨j,(A j).point 0 1⟩).1 = tag p (tag q j)
      rw [map_mul]
      exact routing p (ρ q ⟨j,(A j).point 0 1⟩) }
  have hiso (q : Multiplicative ℚ) : ∀ j, Isotypic A j (σ q j) :=
    routing_isotypic A (ρ q) (hd q) (hc q) (ρ q).injective (σ q) (routing q)
  let C := {j // Isotypic A i j}
  let τ : Multiplicative ℚ →* Function.End C := {
    toFun q j := ⟨σ q j, isotypic_trans A j.property (hiso q j)⟩
    map_one' := by
      funext j
      apply Subtype.ext
      exact congrFun σ.map_one j
    map_mul' := by
      intro p q
      funext j
      apply Subtype.ext
      exact congrFun (σ.map_mul p q) j }
  have fixed (q : Multiplicative ℚ) : σ q i = i := by
    have h := congrArg (fun f : Equiv.Perm C => (f ⟨i,isotypic_refl A i⟩).val)
      (finite_rational_hom_trivial τ.toHomPerm q)
    exact h
  have stays (q : Multiplicative ℚ) (x : X i) : (ρ q ⟨i,x⟩).1 = i :=
    (routing q ⟨i,x⟩).trans (fixed q)
  let Y := {x : Σ j, X j // x.1 = i}
  let η : Multiplicative ℚ →* Function.End Y := {
    toFun q x := ⟨ρ q x.val, by
      rcases x with ⟨⟨j,x⟩,hx⟩
      change j = i at hx
      subst j
      exact stays q x⟩
    map_one' := by
      funext x
      apply Subtype.ext
      exact congrArg (fun f : Equiv.Perm (Σ j, X j) => f x.val) ρ.map_one
    map_mul' := by
      intro p q
      funext x
      apply Subtype.ext
      exact congrArg (fun f : Equiv.Perm (Σ j, X j) => f x.val) (ρ.map_mul p q) }
  let e : Y ≃ X i := Equiv.sigmaSubtype i
  let ψ := e.permCongrHom.toMonoidHom.comp η.toHomPerm
  have lift (q : Multiplicative ℚ) (x : X i) :
      (⟨i,ψ q x⟩ : Σ j, X j) = ρ q ⟨i,x⟩ :=
    congrArg Subtype.val (e.symm_apply_apply (η q (e.symm x)))
  refine ⟨ψ, ?_, ?_⟩
  · intro q a x
    have h : (⟨i,ψ q ((A i).deck a x)⟩ : Σ j, X j) =
        ⟨i,(A i).deck a (ψ q x)⟩ := by
      rw [lift]
      change ρ q (jointDeck A a ⟨i,x⟩) = jointDeck A a ⟨i,ψ q x⟩
      rw [hd, lift]
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
  · funext x
    have h := lift (Multiplicative.ofAdd (1 : ℚ)) x
    rw [congrFun ht] at h
    simpa only [jointTime, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

private theorem finite_class_invariant {i j : ι} (hij : Isotypic A i j) :
    Finite {k // Isotypic A i k} ↔ Finite {k // Isotypic A j k} := by
  let e : {k // Isotypic A i k} ≃ {k // Isotypic A j k} :=
    Equiv.subtypeEquivRight (fun k =>
      ⟨fun h => isotypic_trans A (isotypic_symm A hij) h,
       fun h => isotypic_trans A hij h⟩)
  exact ⟨fun h => by haveI := h; exact Finite.of_equiv _ e,
    fun h => by haveI := h; exact Finite.of_equiv _ e.symm⟩

private theorem assemble_action
    (h : ∀ i, Finite {j // Isotypic A i j} →
      (A i).period = 1 ∧ ∃ φ : Multiplicative ℚ →* H,
        φ (Multiplicative.ofAdd (1 : ℚ)) = (A i).holonomy) :
    ∃ ρ : Multiplicative ℚ →* Equiv.Perm (Σ i, X i),
      (∀ q a x, ρ q (jointDeck A a x) = jointDeck A a (ρ q x)) ∧
      (ρ (Multiplicative.ofAdd (1 : ℚ)) : (Σ i, X i) → Σ i, X i) = jointTime A := by
  classical
  let F (i : ι) := Finite {j // Isotypic A i j}
  let Af (i : Subtype F) := A i.val
  let An (i : Subtype (fun i => ¬ F i)) := A i.val
  have actions (i : Subtype F) :=
    (RationalReturnAtlasCriterion.rational_time_action_criterion (Af i)).2 (h i.val i.property)
  choose ψ hψd hψt using actions
  let ρf : Multiplicative ℚ →* Equiv.Perm (Σ i : Subtype F, X i.val) := {
    toFun q := Equiv.Perm.sigmaCongrRight (fun i => ψ i q)
    map_one' := by
      apply Equiv.ext
      rintro ⟨i,x⟩
      change (⟨i,ψ i 1 x⟩ : Σ i : Subtype F, X i.val) = ⟨i,x⟩
      rw [map_one]
      rfl
    map_mul' := by
      intro p q
      apply Equiv.ext
      rintro ⟨i,x⟩
      change (⟨i,ψ i (p*q) x⟩ : Σ i : Subtype F, X i.val) = ⟨i,ψ i p (ψ i q x)⟩
      rw [map_mul]
      rfl }
  have inf (i : Subtype (fun i => ¬ F i)) : Infinite {j // Isotypic An i j} := by
    let e : {j // Isotypic An i j} ≃ {j // Isotypic A i.val j} := {
      toFun j := ⟨j.val.val,j.property⟩
      invFun j := ⟨⟨j.val,fun hj => i.property ((finite_class_invariant A j.property).2 hj)⟩,
        j.property⟩
      left_inv j := rfl
      right_inv j := rfl }
    haveI : Infinite {j // Isotypic A i.val j} := not_finite_iff_infinite.mp i.property
    exact Infinite.of_injective e.symm e.symm.injective
  obtain ⟨ρn,hnd,hnt⟩ := RationalTimeAction.exists_rational_time_action An inf
  let Yf := Σ i : Subtype F, X i.val
  let Yn := Σ i : Subtype (fun i => ¬ F i), X i.val
  let E : Yf ⊕ Yn ≃ (Σ i, X i) :=
    (Equiv.sumCongr (Equiv.subtypeSigmaEquiv X F).symm
      (Equiv.subtypeSigmaEquiv X (fun i => ¬F i)).symm).trans
      (Equiv.sumCompl (fun x : Σ i, X i => F x.1))
  let G := (Equiv.Perm.sumCongrHom Yf Yn).comp (ρf.prod ρn)
  let T : Yf ⊕ Yn → Yf ⊕ Yn := Sum.map (jointTime Af) (jointTime An)
  let D (a : H) : Yf ⊕ Yn → Yf ⊕ Yn := Sum.map (jointDeck Af a) (jointDeck An a)
  have et (x : Yf ⊕ Yn) : E (T x) = jointTime A (E x) := by
    rcases x with ⟨i,x⟩ | ⟨i,x⟩ <;> rfl
  have ed (a : H) (x : Yf ⊕ Yn) : E (D a x) = jointDeck A a (E x) := by
    rcases x with ⟨i,x⟩ | ⟨i,x⟩ <;> rfl
  have gt : (G (Multiplicative.ofAdd (1 : ℚ)) : Yf ⊕ Yn → Yf ⊕ Yn) = T := by
    funext x
    rcases x with ⟨i,x⟩ | x
    · change (Sum.inl (⟨i,ψ i (Multiplicative.ofAdd (1 : ℚ)) x⟩ : Yf) : Yf ⊕ Yn) =
        Sum.inl ⟨i,(Af i).time x⟩
      rw [congrFun (hψt i)]
    · change Sum.inr (ρn (Multiplicative.ofAdd (1 : ℚ)) x) = Sum.inr (jointTime An x)
      rw [congrFun hnt]
  have gd (q : Multiplicative ℚ) (a : H) (x : Yf ⊕ Yn) : G q (D a x) = D a (G q x) := by
    rcases x with ⟨i,x⟩ | x
    · change (Sum.inl (⟨i,ψ i q ((Af i).deck a x)⟩ : Yf) : Yf ⊕ Yn) =
        Sum.inl ⟨i,(Af i).deck a (ψ i q x)⟩
      rw [hψd i q a x]
    · change Sum.inr (ρn q (jointDeck An a x)) = Sum.inr (jointDeck An a (ρn q x))
      rw [hnd]
  let ρ := E.permCongrHom.toMonoidHom.comp G
  have law (q : Multiplicative ℚ) (x : Yf ⊕ Yn) : ρ q (E x) = E (G q x) := by
    change E (G q (E.symm (E x))) = _
    rw [E.symm_apply_apply]
  refine ⟨ρ,?_,?_⟩
  · intro q a x
    obtain ⟨x,rfl⟩ := E.surjective x
    rw [← ed,law,gd,ed,law]
  · funext x
    obtain ⟨x,rfl⟩ := E.surjective x
    rw [law,gt,et]

/-- One genuine deck-equivariant rational action exists exactly when every finite
actual isotypic class has period one and coherently rationally extensible holonomy. -/
theorem coherent_rational_time_iff :
    (∃ ρ : Multiplicative ℚ →* Equiv.Perm (Σ i, X i),
      (∀ q a x, ρ q (jointDeck A a x) = jointDeck A a (ρ q x)) ∧
      (ρ (Multiplicative.ofAdd (1 : ℚ)) : (Σ i, X i) → Σ i, X i) = jointTime A) ↔
    ∀ i, Finite {j // Isotypic A i j} →
      (A i).period = 1 ∧
      ∃ φ : Multiplicative ℚ →* H,
        φ (Multiplicative.ofAdd (1 : ℚ)) = (A i).holonomy := by
  constructor
  · rintro ⟨ρ,hd,ht⟩ i hi
    haveI := hi
    exact (RationalReturnAtlasCriterion.rational_time_action_criterion (A i)).1
      (restrict_finite_class A ρ hd ht i)
  · exact assemble_action A

end Family
end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.CoherentRationalTimeCriterion
