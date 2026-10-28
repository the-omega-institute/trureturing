/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Prime families admit roots exactly locally or by cycling isotypic charts. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.ReturnAtlasFiniteCovers
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Fintype.Card

/-! Prime roots on dependent families of complete signed return charts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PrimeOrbitRootCriterion

open PrimitiveLiftRootCriterion
open TwoOrbitSquareRootCriterion (transport transport_point transport_deck)
universe u v w

section Family
variable {H : Type u} [Group H] {ι : Type w} {X : ι → Type v}
  (A : ∀ i, ReturnAtlas H (X i))

/-- Time on the entire dependent disjoint union. -/
def jointTime : (Σ i, X i) → Σ i, X i := fun q => ⟨q.1, (A q.1).time q.2⟩

/-- The specified left deck action, on every component. -/
def jointDeck (a : H) : (Σ i, X i) → Σ i, X i := fun q => ⟨q.1, (A q.1).deck a q.2⟩

theorem jointTime_injective : Function.Injective (jointTime A) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  exact congrArg (Sigma.mk i) ((A i).time_injective (by simpa [jointTime] using h))

theorem component_constant (f : (Σ i, X i) → Σ i, X i)
    (hf : ∀ a q, f (jointDeck A a q) = jointDeck A a (f q))
    (ht : ∀ q, f (jointTime A q) = jointTime A (f q)) (i : ι) :
    ∀ x, (f ⟨i,x⟩).1 = (f ⟨i,(A i).point 0 1⟩).1 := by
  have hp : ∀ n : ℕ, ∀ z, (f ⟨i,(A i).point n z⟩).1 =
      (f ⟨i,(A i).point 0 1⟩).1 := by
    intro n
    induction n with
    | zero =>
      intro z
      have h := congrArg Sigma.fst (hf z ⟨i,(A i).point 0 1⟩)
      simpa only [jointDeck, (A i).deck_point, mul_one, Nat.cast_zero] using h
    | succ n ih =>
      intro z
      rw [show ((n+1 : ℕ) : ℤ) = (n : ℤ)+1 by omega, ← (A i).time_point]
      have h := congrArg Sigma.fst (ht ⟨i,(A i).point n z⟩)
      exact h.trans (ih z)
  intro x
  obtain ⟨⟨n,z⟩,rfl⟩ := (A i).coordinates.surjective x
  exact hp n.val z

private theorem factorization (f : (Σ i, X i) → Σ i, X i)
    (σ : ι → ι) (hσ : ∀ q, (f q).1 = σ q.1) :
    ∃ g : ∀ i, X i → X (σ i), ∀ i x, f ⟨i,x⟩ = ⟨σ i,g i x⟩ := by
  have image : ∀ i x, ∃ y : X (σ i), f ⟨i,x⟩ = ⟨σ i,y⟩ := by
    intro i x
    cases he : f ⟨i,x⟩ with
    | mk j y =>
      have hj : j = σ i := by simpa only [he] using hσ ⟨i,x⟩
      subst j
      exact ⟨y,rfl⟩
  choose g hg using image
  exact ⟨g,hg⟩

def Isotypic (i j : ι) : Prop :=
  (A i).period = (A j).period ∧ ∃ b : H, b * (A j).holonomy = (A i).holonomy * b

theorem isotypic_trans {i j k : ι} (hij : Isotypic A i j)
    (hjk : Isotypic A j k) : Isotypic A i k := by
  obtain ⟨hd,b,hb⟩ := hij
  obtain ⟨he,c,hc⟩ := hjk
  refine ⟨hd.trans he,b*c,?_⟩
  calc
    (b*c)*(A k).holonomy = b*(c*(A k).holonomy) := mul_assoc _ _ _
    _ = b*((A j).holonomy*c) := by rw [hc]
    _ = (A i).holonomy*(b*c) := by rw [← mul_assoc,hb,mul_assoc]

theorem isotypic_symm {i j : ι} (hij : Isotypic A i j) : Isotypic A j i := by
  obtain ⟨hd,b,hb⟩ := hij
  refine ⟨hd.symm,b⁻¹,?_⟩
  apply mul_left_cancel (a := b)
  simpa [mul_assoc] using congrArg (· * b⁻¹) hb.symm

private theorem injective_factor_isotypic {i j : ι} (f : X i → X j)
    (hf : ∀ a x, f ((A i).deck a x) = (A j).deck a (f x))
    (ht : ∀ x, f ((A i).time x) = (A j).time (f x))
    (hinj : Function.Injective f) : Isotypic A i j := by
  obtain ⟨⟨m,r,b⟩,⟨hm,hd,hb,law⟩,_⟩ := ReturnAtlasFiniteCovers.normal_form (A i) (A j) f hf ht
  let e := ReturnAtlasFiniteCovers.fiberEquiv (A i) (A j) f m hd r b hb law ((A j).point 0 1)
  have hmone : m = 1 := by
    by_contra hn
    have hm2 : 1 < m := by omega
    let j₀ : Fin m := ⟨0,hm⟩
    let j₁ : Fin m := ⟨1,hm2⟩
    have he : e j₀ = e j₁ := Subtype.ext (hinj ((e j₀).property.trans (e j₁).property.symm))
    have hz := congrArg Fin.val (e.injective he)
    change 0 = 1 at hz
    omega
  exact ⟨by simpa [hmone] using hd,b,by simpa [hmone] using hb⟩

theorem routing_isotypic (f : (Σ i, X i) → Σ i, X i)
    (hf : ∀ a q, f (jointDeck A a q) = jointDeck A a (f q))
    (ht : ∀ q, f (jointTime A q) = jointTime A (f q))
    (hinj : Function.Injective f) (σ : ι → ι) (hσ : ∀ q, (f q).1 = σ q.1) :
    ∀ i, Isotypic A i (σ i) := by
  obtain ⟨g,hg⟩ := factorization f σ hσ
  intro i
  apply injective_factor_isotypic A (g i)
  · intro a x
    have h := hf a ⟨i,x⟩
    change f ⟨i,(A i).deck a x⟩ = jointDeck A a (f ⟨i,x⟩) at h
    rw [hg,hg] at h
    simpa only [jointDeck,id_eq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  · intro x
    have h := ht ⟨i,x⟩
    change f ⟨i,(A i).time x⟩ = jointTime A (f ⟨i,x⟩) at h
    rw [hg,hg] at h
    simpa only [jointTime,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  · intro x y h
    have hxy : (⟨i,x⟩ : Σ i, X i) = ⟨i,y⟩ := hinj (by rw [hg,hg,h])
    simpa using hxy

end Family

def cycleStep {Y : Type v} (p : ℕ) (hp : 0 < p) (t : Y → Y) :
    Fin p × Y → Fin p × Y := fun q =>
  (⟨(q.1.val+1)%p,Nat.mod_lt _ hp⟩,t^[(q.1.val+1)/p] q.2)

theorem cycleStep_iterate {Y : Type v} (p : ℕ) (hp : 0 < p) (t : Y → Y)
    (n : ℕ) (i : Fin p) (y : Y) :
    (cycleStep p hp t)^[n] (i,y) =
      (⟨(i.val+n)%p,Nat.mod_lt _ hp⟩,t^[(i.val+n)/p] y) := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt i.isLt,Nat.div_eq_of_lt i.isLt]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change ((⟨(((i.val+n)%p)+1)%p,Nat.mod_lt _ hp⟩ : Fin p),
      t^[(((i.val+n)%p)+1)/p] (t^[(i.val+n)/p] y)) = _
    have hmod : (((i.val+n)%p)+1)%p = (i.val+(n+1))%p := by
      rw [Nat.mod_add_mod,Nat.add_assoc]
    have hdiv : (((i.val+n)%p)+1)/p + (i.val+n)/p = (i.val+(n+1))/p := by
      have he : i.val+(n+1) = (((i.val+n)%p)+1) + p*((i.val+n)/p) := by
        have := Nat.mod_add_div (i.val+n) p
        omega
      rw [he,Nat.add_mul_div_left _ _ hp]
    rw [← Function.iterate_add_apply,hdiv]
    exact Prod.ext (Fin.ext hmod) rfl

private theorem cycleStep_root {Y : Type v} (p : ℕ) (hp : 0 < p) (t : Y → Y) :
    (cycleStep p hp t)^[p] = fun q => (q.1,t q.2) := by
  funext ⟨i,y⟩
  rw [cycleStep_iterate]
  have hm : (i.val+p)%p = i.val := by
    rw [Nat.add_mod_right,Nat.mod_eq_of_lt i.isLt]
  have hd : (i.val+p)/p = 1 := by
    rw [Nat.add_div_right _ hp,Nat.div_eq_of_lt i.isLt]
  rw [hd]
  exact Prod.ext (Fin.ext hm) rfl

section PrimeFamily
variable {H : Type u} [Group H] {p : ℕ} {X : Fin p → Type v}
  (A : ∀ i, ReturnAtlas H (X i))

private theorem isotypic_root (hp : 0 < p) (hall : ∀ i j, Isotypic A i j) :
    ∃ R : (Σ i, X i) → Σ i, X i,
      (∀ a q, R (jointDeck A a q) = jointDeck A a (R q)) ∧
      R^[p] = jointTime A := by
  classical
  let o : Fin p := ⟨0,hp⟩
  choose b hb using fun i => (hall o i).2
  have hd : ∀ i, (A o).period = (A i).period := fun i => (hall o i).1
  have hi : ∀ i, (b i)⁻¹ * (A o).holonomy = (A i).holonomy * (b i)⁻¹ := by
    intro i
    apply mul_left_cancel (a := b i)
    simpa [mul_assoc] using congrArg (· * (b i)⁻¹) (hb i).symm
  let e : (Σ i, X i) ≃ Fin p × X o := {
    toFun := fun q => (q.1,transport (A q.1) (A o) (b q.1)⁻¹ q.2)
    invFun := fun q => ⟨q.1,transport (A o) (A q.1) (b q.1) q.2⟩
    left_inv := by
      rintro ⟨i,x⟩
      obtain ⟨t,z,rfl⟩ := (A i).covers x
      change (⟨i,transport (A o) (A i) (b i)
        (transport (A i) (A o) (b i)⁻¹ ((A i).point t z))⟩ : Σ i, X i) = _
      rw [transport_point (A i) (A o) (hd i).symm _ (hi i),
        transport_point (A o) (A i) (hd i) _ (hb i),inv_mul_cancel_right]
    right_inv := by
      rintro ⟨i,x⟩
      obtain ⟨t,z,rfl⟩ := (A o).covers x
      change (i,transport (A i) (A o) (b i)⁻¹
        (transport (A o) (A i) (b i) ((A o).point t z))) = _
      rw [transport_point (A o) (A i) (hd i) _ (hb i),
        transport_point (A i) (A o) (hd i).symm _ (hi i),mul_inv_cancel_right] }
  let τ : Fin p × X o → Fin p × X o := fun q => (q.1,(A o).time q.2)
  let δ : H → Fin p × X o → Fin p × X o := fun a q => (q.1,(A o).deck a q.2)
  have et : ∀ q, e (jointTime A q) = τ (e q) := by
    rintro ⟨i,x⟩
    obtain ⟨t,z,rfl⟩ := (A i).covers x
    change (i,transport (A i) (A o) (b i)⁻¹ ((A i).time ((A i).point t z))) =
      (i,(A o).time (transport (A i) (A o) (b i)⁻¹ ((A i).point t z)))
    rw [(A i).time_point,transport_point (A i) (A o) (hd i).symm _ (hi i),
      transport_point (A i) (A o) (hd i).symm _ (hi i),(A o).time_point]
  have ed : ∀ a q, e (jointDeck A a q) = δ a (e q) := by
    rintro a ⟨i,x⟩
    exact Prod.ext rfl (transport_deck (A i) (A o) (hd i).symm _ (hi i) a x)
  have td : ∀ a, Function.Commute (A o).time ((A o).deck a) := by
    intro a x
    obtain ⟨t,z,rfl⟩ := (A o).covers x
    rw [(A o).deck_point,(A o).time_point,(A o).time_point,(A o).deck_point]
  let c := cycleStep p hp (A o).time
  have cd : ∀ a q, c (δ a q) = δ a (c q) := by
    rintro a ⟨i,x⟩
    exact Prod.ext rfl (((td a).iterate_left ((i.val+1)/p)) x)
  let R := fun q => e.symm (c (e q))
  have er : Function.Semiconj e R c := fun q => e.apply_symm_apply _
  refine ⟨R,?_,?_⟩
  · intro a q
    apply e.injective
    rw [er,ed,cd,ed,er]
  · funext q
    apply e.injective
    rw [er.iterate_right p,cycleStep_root,et]

/-- The exact signed local p-root equation; the return exponent may be negative. -/
def Local (p : ℕ) {Y : Type v} (B : ReturnAtlas H Y) : Prop :=
  ∃ s : Fin B.period, ∃ m : ℤ, ∃ b : H, Commute b B.holonomy ∧
    (p : ℤ) * (s.val : ℤ) = 1 + (B.period : ℤ) * m ∧ b^p * B.holonomy^m = 1

private theorem preserving_root (R : (Σ i, X i) → Σ i, X i)
    (hr : ∀ a q, R (jointDeck A a q) = jointDeck A a (R q))
    (hs : R^[p] = jointTime A) (hfix : ∀ q, (R q).1 = q.1) :
    ∀ i, Local p (A i) := by
  obtain ⟨f,hf⟩ := factorization R id hfix
  intro i
  apply ((A i).root_criterion p).1
  refine ⟨f i,?_,?_⟩
  · intro a x
    have h := hr a ⟨i,x⟩
    change R ⟨i,(A i).deck a x⟩ = jointDeck A a (R ⟨i,x⟩) at h
    rw [hf,hf] at h
    simpa only [jointDeck,id_eq,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  · funext x
    have hc : Function.Semiconj (Sigma.mk i) (f i) R := fun x => (hf i x).symm
    have h := hc.iterate_right p x
    rw [hs] at h
    simpa only [jointTime,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h

/-- For a prime number of complete charts, every root is either local in all charts,
or its component orbit forces equal periods and pairwise conjugate holonomies. -/
theorem prime_root_criterion (hp : p.Prime) :
    (∃ R : (Σ i, X i) → Σ i, X i,
      (∀ a q, R (jointDeck A a q) = jointDeck A a (R q)) ∧
      R^[p] = jointTime A) ↔
    ((∀ i, Local p (A i)) ∨
      (∀ i j, (A i).period = (A j).period ∧
        ∃ b : H, b * (A j).holonomy = (A i).holonomy * b)) := by
  classical
  constructor
  · rintro ⟨R,hr,hs⟩
    have ht : Function.Commute R (jointTime A) := by
      rw [← hs]
      exact Function.Commute.self_iterate R p
    have hinj : Function.Injective R := by
      intro x y h
      apply jointTime_injective A
      rw [← hs]
      have h' := congrArg (R^[p-1]) h
      simpa only [← Function.iterate_succ_apply,Nat.succ_eq_add_one,Nat.sub_add_cancel hp.one_le] using h'
    let σ : Fin p → Fin p := fun i => (R ⟨i,(A i).point 0 1⟩).1
    have htag : Function.Semiconj Sigma.fst R σ := by
      rintro ⟨i,x⟩
      exact component_constant A R hr ht i x
    have hpow : σ^[p] = id := by
      funext i
      have h := htag.iterate_right p ⟨i,(A i).point 0 1⟩
      rw [hs] at h
      exact h.symm
    by_cases hfixed : ∀ i, σ i = i
    · left
      apply preserving_root A R hr hs
      intro q
      exact (htag q).trans (hfixed q.1)
    · right
      obtain ⟨o,ho⟩ := not_forall.mp hfixed
      haveI : Fact p.Prime := ⟨hp⟩
      have hperiod : Function.minimalPeriod σ o = p :=
        Function.minimalPeriod_eq_prime (congrFun hpow o) ho
      let orbit : Fin p → Fin p := fun n => σ^[n.val] o
      have orbit_inj : Function.Injective orbit := by
        intro n m h
        apply Fin.ext
        exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
          (by rw [hperiod]; exact n.isLt) (by rw [hperiod]; exact m.isLt)).1 h
      have hbase : ∀ j, Isotypic A o j := by
        intro j
        obtain ⟨n,hn⟩ := Finite.surjective_of_injective orbit_inj j
        have hrn : ∀ a q, R^[n.val] (jointDeck A a q) = jointDeck A a (R^[n.val] q) := by
          intro a
          exact (Function.Commute.iterate_left (hr a) n.val)
        have hniso := routing_isotypic A (R^[n.val]) hrn (ht.iterate_left n.val)
          (hinj.iterate n.val) (σ^[n.val]) (htag.iterate_right n.val) o
        exact hn ▸ hniso
      intro i j
      exact isotypic_trans A (isotypic_symm A (hbase i)) (hbase j)
  · rintro (hl | hi)
    · choose f hf hs using fun i => ((A i).root_criterion p).2 (hl i)
      let R : (Σ i, X i) → Σ i, X i := fun q => ⟨q.1,f q.1 q.2⟩
      refine ⟨R,?_,?_⟩
      · rintro a ⟨i,x⟩
        exact congrArg (Sigma.mk i) (hf i a x)
      · funext ⟨i,x⟩
        have hc : Function.Semiconj (Sigma.mk i) (f i) R := fun _ => rfl
        have h := hc.iterate_right p x
        rw [hs i] at h
        exact h.symm
    · exact isotypic_root A hp.pos hi

end PrimeFamily

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PrimeOrbitRootCriterion
