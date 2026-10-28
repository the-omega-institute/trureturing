/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteOrbitRootCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Finite chart families admit roots exactly by allowed isotypic block multiplicities. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PrimeOrbitRootCriterion
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Quotient
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Exact finite multiplicities for roots of complete return-chart families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteOrbitRootCriterion

open PrimitiveLiftRootCriterion PrimeOrbitRootCriterion
open TwoOrbitSquareRootCriterion (transport transport_point transport_deck)
universe u v w z

private def chartGauge {H : Type u} [Group H] {Y : Type v} {Z : Type w}
    (B : ReturnAtlas H Y) (C : ReturnAtlas H Z) (hd : B.period = C.period) (b : H) : Y ≃ Z :=
  B.coordinates.symm.trans ((Equiv.prodCongr (finCongr hd) (Equiv.mulRight b)).trans C.coordinates)

private theorem chartGauge_apply {H : Type u} [Group H] {Y : Type v} {Z : Type w}
    (B : ReturnAtlas H Y) (C : ReturnAtlas H Z) (hd : B.period = C.period) (b : H) (y : Y) :
    chartGauge B C hd b y = transport B C b y := rfl

private theorem chartGauge_time {H : Type u} [Group H] {Y : Type v} {Z : Type w}
    (B : ReturnAtlas H Y) (C : ReturnAtlas H Z) (hd : B.period = C.period) (b : H)
    (hb : b * C.holonomy = B.holonomy * b) :
    Function.Semiconj (chartGauge B C hd b) B.time C.time := by
  intro y
  obtain ⟨t,a,rfl⟩ := B.covers y
  simp only [chartGauge_apply,B.time_point,transport_point B C hd b hb,C.time_point]

private def orbitEquiv {S : Type w} [Finite S] (σ : Equiv.Perm S) (x : S)
    (hp : 0 < Function.minimalPeriod σ x) :
    Fin (Function.minimalPeriod σ x) ≃ {y // σ.SameCycle x y} :=
  Equiv.ofBijective (fun n => ⟨σ^[n.val] x,⟨(n.val : ℤ),by
    simp only [zpow_natCast,Equiv.Perm.coe_pow]⟩⟩) (by
    constructor
    · intro n m h
      exact Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod n.isLt m.isLt).1
        (congrArg Subtype.val h))
    · rintro ⟨y,hy⟩
      obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
      refine ⟨⟨n % Function.minimalPeriod σ x,Nat.mod_lt _ hp⟩,Subtype.ext ?_⟩
      simpa only [Function.iterate_mod_minimalPeriod_eq,← Equiv.Perm.coe_pow] using hn)

private theorem periodic_lengths {S : Type w} [Fintype S] (σ : Equiv.Perm S)
    {k : ℕ} (hk : 0 < k) (hs : (σ : S → S)^[k] = id) (P : ℕ → Prop)
    (hP : ∀ x, P (Function.minimalPeriod σ x)) :
    ∃ L : List ℕ, L.sum = Fintype.card S ∧ ∀ n ∈ L, 0 < n ∧ n ∣ k ∧ P n := by
  classical
  let s := Equiv.Perm.SameCycle.setoid σ
  let Q := Quotient s
  letI : Fintype Q := Fintype.ofFinite Q
  let r : Q → S := Quotient.out
  have hp (x : S) : Function.IsPeriodicPt σ k x := congrFun hs x
  have hpos (x : S) := (hp x).minimalPeriod_pos hk
  let fiber (c : Q) : Type w := {x : S // Quotient.mk s x = c}
  have ef (c : Q) : fiber c ≃ {y // σ.SameCycle (r c) y} :=
    Equiv.subtypeEquivRight (fun y => by
      change Quotient.mk s y = c ↔ s.r (r c) y
      constructor
      · intro h
        exact s.symm (Quotient.exact (h.trans (Quotient.out_eq c).symm))
      · intro h
        exact (Quotient.sound (s.symm h)).trans (Quotient.out_eq c))
  have hc (c : Q) : Fintype.card (fiber c) = Function.minimalPeriod σ (r c) := by
    rw [Fintype.card_congr (ef c),← Fintype.card_congr (orbitEquiv σ (r c) (hpos _)),
      Fintype.card_fin]
  let e := Fintype.equivFin Q
  let L := List.ofFn (fun j : Fin (Fintype.card Q) => Function.minimalPeriod σ (r (e.symm j)))
  refine ⟨L,?_,?_⟩
  · change (List.ofFn _).sum = _
    rw [List.sum_ofFn]
    have hsum : (∑ j : Fin (Fintype.card Q), Function.minimalPeriod σ (r (e.symm j))) =
        ∑ c : Q, Fintype.card (fiber c) := by
      simpa only [hc] using (Equiv.sum_comp e.symm (fun c => Function.minimalPeriod σ (r c)))
    rw [hsum,← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk s))
  · intro n hn
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hn
    exact ⟨hpos _,(hp _).minimalPeriod_dvd,hP _⟩

section Family
variable {H : Type u} [Group H] {ι : Type w} {X : ι → Type v}
  (A : ∀ i, ReturnAtlas H (X i))

private theorem isotypic_refl (i : ι) : Isotypic A i i := ⟨rfl,1,by simp⟩

private def atlasSetoid : Setoid ι :=
  ⟨Isotypic A,⟨isotypic_refl A, isotypic_symm A, isotypic_trans A⟩⟩

private theorem local_of_isotypic {i j : ι} (hij : Isotypic A i j) (q : ℕ)
    (hl : Local q (A j)) : Local q (A i) := by
  obtain ⟨hd,b,hb⟩ := hij
  let e := chartGauge (A i) (A j) hd b
  have et := chartGauge_time (A i) (A j) hd b hb
  have ed : ∀ a x, e ((A i).deck a x) = (A j).deck a (e x) := by
    intro a x
    exact transport_deck (A i) (A j) hd b hb a x
  obtain ⟨f,hf,hs⟩ := ((A j).root_criterion q).2 hl
  let g := fun x => e.symm (f (e x))
  have eg : Function.Semiconj e g f := fun x => e.apply_symm_apply _
  apply ((A i).root_criterion q).1
  refine ⟨g,?_,?_⟩
  · intro a x
    apply e.injective
    rw [eg,ed,hf,ed,eg]
  · funext x
    apply e.injective
    rw [eg.iterate_right q,hs,et]

private theorem root_routing {k : ℕ} (hk : 0 < k)
    (R : (Σ i, X i) → Σ i, X i)
    (hr : ∀ a q, R (jointDeck A a q) = jointDeck A a (R q))
    (hs : R^[k] = jointTime A) :
    ∃ σ : Equiv.Perm ι, (∀ q, (R q).1 = σ q.1) ∧
      (σ : ι → ι)^[k] = id ∧ (∀ i, Isotypic A i (σ i)) := by
  have ht : Function.Commute R (jointTime A) := by
    rw [← hs]
    exact Function.Commute.self_iterate R k
  have hinj : Function.Injective R := by
    intro x y h
    apply jointTime_injective A
    rw [← hs]
    have h' := congrArg (R^[k-1]) h
    simpa only [← Function.iterate_succ_apply,Nat.succ_eq_add_one,Nat.sub_add_cancel hk] using h'
  let f : ι → ι := fun i => (R ⟨i,(A i).point 0 1⟩).1
  have htag : Function.Semiconj Sigma.fst R f := by
    rintro ⟨i,x⟩
    exact component_constant A R hr ht i x
  have hpow : f^[k] = id := by
    funext i
    have h := htag.iterate_right k ⟨i,(A i).point 0 1⟩
    rw [hs] at h
    exact h.symm
  have hleft : Function.LeftInverse (f^[k-1]) f := by
    intro i
    simpa only [← Function.iterate_succ_apply,Nat.succ_eq_add_one,Nat.sub_add_cancel hk,id_eq]
      using congrFun hpow i
  have hright : Function.RightInverse (f^[k-1]) f := by
    intro i
    simpa only [← Function.iterate_succ_apply',Nat.succ_eq_add_one,Nat.sub_add_cancel hk,id_eq]
      using congrFun hpow i
  let σ : Equiv.Perm ι := ⟨f,f^[k-1],hleft,hright⟩
  exact ⟨σ,htag,hpow,routing_isotypic A R hr ht hinj f htag⟩

private theorem local_return_root {k ℓ : ℕ} (hℓ : ℓ ∣ k)
    (R : (Σ i, X i) → Σ i, X i)
    (hr : ∀ a q, R (jointDeck A a q) = jointDeck A a (R q))
    (hs : R^[k] = jointTime A) (σ : ι → ι)
    (htag : Function.Semiconj Sigma.fst R σ) (i : ι) (hret : σ^[ℓ] i = i) :
    Local (k/ℓ) (A i) := by
  have hcomp : ∀ x, ∃ y : X i, R^[ℓ] ⟨i,x⟩ = ⟨i,y⟩ := by
    intro x
    have h := (htag.iterate_right ℓ) ⟨i,x⟩
    rw [hret] at h
    cases he : R^[ℓ] ⟨i,x⟩ with
    | mk j y =>
      have hj : j = i := by simpa only [he] using h
      subst j
      exact ⟨y,rfl⟩
  choose g hg using hcomp
  have eg : Function.Semiconj (Sigma.mk i) g (R^[ℓ]) := fun x => (hg x).symm
  apply ((A i).root_criterion (k/ℓ)).1
  refine ⟨g,?_,?_⟩
  · intro a x
    have h := (Function.Commute.iterate_left (hr a) ℓ) ⟨i,x⟩
    change R^[ℓ] ⟨i,(A i).deck a x⟩ = jointDeck A a (R^[ℓ] ⟨i,x⟩) at h
    rw [hg,hg] at h
    simpa only [jointDeck,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  · funext x
    have h := eg.iterate_right (k/ℓ) x
    rw [← Function.iterate_mul,Nat.mul_div_cancel' hℓ,hs] at h
    simpa only [jointTime,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h

private noncomputable def infinite_block_equiv {C : Type w} [Infinite C] {k : ℕ} (hk : 0 < k) :
    C ≃ C × Fin k := by
  have hcard : Cardinal.mk (C × Fin k) = Cardinal.mk C := by
    rw [Cardinal.mk_prod]
    simp only [Cardinal.lift_id', Cardinal.mk_fintype, Fintype.card_fin,
      Cardinal.lift_natCast]
    apply Cardinal.mul_eq_left (Cardinal.aleph0_le_mk C)
    · exact Cardinal.natCast_le_aleph0.trans (Cardinal.aleph0_le_mk C)
    · exact_mod_cast Nat.ne_of_gt hk
  exact (Cardinal.eq.mp hcard).some.symm

private theorem local_one {Y : Type v} (B : ReturnAtlas H Y) : Local 1 B := by
  apply (B.root_criterion 1).1
  refine ⟨B.time, ?_, by simp⟩
  intro a x
  obtain ⟨t,z,rfl⟩ := B.covers x
  rw [B.deck_point, B.time_point, B.time_point, B.deck_point]

private theorem root_lengths_finite {k : ℕ} (hk : 0 < k)
    (R : (Σ i, X i) → Σ i, X i)
    (hr : ∀ a q, R (jointDeck A a q) = jointDeck A a (R q))
    (hs : R^[k] = jointTime A) (i : ι) [Finite {j // Isotypic A i j}] :
    ∃ L : List ℕ, L.sum = Nat.card {j // Isotypic A i j} ∧
      ∀ ℓ ∈ L, 0 < ℓ ∧ ℓ ∣ k ∧ Local (k/ℓ) (A i) := by
  classical
  obtain ⟨σ,htag,hpow,hiso⟩ := root_routing A hk R hr hs
  let C := {j // Isotypic A i j}
  letI : Fintype C := Fintype.ofFinite C
  let f : C → C := fun j => ⟨σ j,isotypic_trans A j.property (hiso j)⟩
  have hfinj : Function.Injective f := fun a b h => Subtype.ext (σ.injective (congrArg Subtype.val h))
  let τ : Equiv.Perm C := Equiv.ofBijective f ⟨hfinj,Finite.surjective_of_injective hfinj⟩
  have ht : Function.Semiconj Subtype.val τ σ := fun _ => rfl
  have htau : (τ : C → C)^[k] = id := by
    funext j
    apply Subtype.ext
    rw [ht.iterate_right k,hpow]
    rfl
  obtain ⟨L,hL,hallow⟩ := periodic_lengths τ hk htau (fun ℓ => Local (k/ℓ) (A i)) (by
    intro j
    have hp : Function.IsPeriodicPt τ k j := congrFun htau j
    have hd := hp.minimalPeriod_dvd
    apply local_of_isotypic A j.property
    apply local_return_root A hd R hr hs σ htag j.val
    have h := ht.iterate_right (Function.minimalPeriod τ j) j
    rw [Function.iterate_minimalPeriod] at h
    exact h.symm)
  exact ⟨L,hL.trans (Nat.card_eq_fintype_card.symm),hallow⟩

private theorem root_lengths {k : ℕ} (hk : 0 < k)
    (R : (Σ i, X i) → Σ i, X i)
    (hr : ∀ a q, R (jointDeck A a q) = jointDeck A a (R q))
    (hs : R^[k] = jointTime A) (i : ι) :
    ∃ L : List ℕ, L.sum = Nat.card {j // Isotypic A i j} ∧
      ∀ ℓ ∈ L, 0 < ℓ ∧ ℓ ∣ k ∧ Local (k/ℓ) (A i) := by
  classical
  let C := {j // Isotypic A i j}
  by_cases hC : Finite C
  · letI : Finite C := hC
    exact root_lengths_finite A hk R hr hs i
  · letI : Infinite C := not_finite_iff_infinite.mp hC
    exact ⟨[], Nat.card_eq_zero_of_infinite.symm, by simp⟩

private theorem roots_of_blocks {B : Type z} (ℓ : B → ℕ) (hpos : ∀ b, 0 < ℓ b)
    {k : ℕ} (hdvd : ∀ b, ℓ b ∣ k) (r : B → ι)
    (e : ι ≃ Σ b, Fin (ℓ b)) (hi : ∀ i, Isotypic A i (r (e i).1))
    (hl : ∀ b, Local (k/ℓ b) (A (r b))) :
    ∃ R : (Σ i, X i) → Σ i, X i,
      (∀ a q, R (jointDeck A a q) = jointDeck A a (R q)) ∧ R^[k] = jointTime A := by
  classical
  choose c hc using fun i => (hi i).2
  let g (i : ι) := chartGauge (A i) (A (r (e i).1)) (hi i).1 (c i)
  let E : (Σ i, X i) ≃ Σ b : B, Fin (ℓ b) × X (r b) :=
    (Equiv.sigmaCongr e g).trans ((Equiv.sigmaAssoc (fun b (_ : Fin (ℓ b)) => X (r b))).trans
      (Equiv.sigmaCongrRight (fun b => Equiv.sigmaEquivProd (Fin (ℓ b)) (X (r b)))))
  let T : (Σ b : B, Fin (ℓ b) × X (r b)) → Σ b : B, Fin (ℓ b) × X (r b) :=
    fun q => ⟨q.1,q.2.1,(A (r q.1)).time q.2.2⟩
  let D (a : H) : (Σ b : B, Fin (ℓ b) × X (r b)) → Σ b : B, Fin (ℓ b) × X (r b) :=
    fun q => ⟨q.1,q.2.1,(A (r q.1)).deck a q.2.2⟩
  have et : Function.Semiconj E (jointTime A) T := by
    rintro ⟨i,x⟩
    exact congrArg (fun y => (⟨(e i).1,(e i).2,y⟩ : Σ b : B, Fin (ℓ b) × X (r b)))
      (chartGauge_time (A i) (A (r (e i).1)) (hi i).1 (c i) (hc i) x)
  have ed : ∀ a q, E (jointDeck A a q) = D a (E q) := by
    rintro a ⟨i,x⟩
    exact congrArg (fun y => (⟨(e i).1,(e i).2,y⟩ : Σ b : B, Fin (ℓ b) × X (r b)))
      (transport_deck (A i) (A (r (e i).1)) (hi i).1 (c i) (hc i) a x)
  choose f hf hs using fun b => ((A (r b)).root_criterion (k/ℓ b)).2 (hl b)
  let C : (Σ b : B, Fin (ℓ b) × X (r b)) → Σ b : B, Fin (ℓ b) × X (r b) :=
    fun q => ⟨q.1,cycleStep (ℓ q.1) (hpos q.1) (f q.1) q.2⟩
  have ct : C^[k] = T := by
    funext ⟨b,j,x⟩
    have he : Function.Semiconj (Sigma.mk b) (cycleStep (ℓ b) (hpos b) (f b)) C := fun _ => rfl
    rw [← he.iterate_right k,cycleStep_iterate]
    have hm : (j.val+k) % ℓ b = j.val := by
      rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd (hdvd b),Nat.add_zero,Nat.mod_eq_of_lt j.isLt]
      exact Nat.mod_eq_of_lt j.isLt
    have hd : (j.val+k) / ℓ b = k/ℓ b := by
      have hk : k = ℓ b * (k/ℓ b) := (Nat.mul_div_cancel' (hdvd b)).symm
      conv_lhs => rw [hk]
      rw [Nat.add_mul_div_left _ _ (hpos b),Nat.div_eq_of_lt j.isLt,Nat.zero_add]
    simp only [hd,hs]
    exact congrArg (Sigma.mk b) (Prod.ext (Fin.ext hm) rfl)
  have cd : ∀ a q, C (D a q) = D a (C q) := by
    rintro a ⟨b,j,x⟩
    exact congrArg (Sigma.mk b) (Prod.ext rfl
      ((Function.Commute.iterate_left (hf b a) ((j.val+1)/ℓ b)) x))
  let R := fun q => E.symm (C (E q))
  have er : Function.Semiconj E R C := fun _ => E.apply_symm_apply _
  refine ⟨R,?_,?_⟩
  · intro a q
    apply E.injective
    rw [er,ed,cd,ed,er]
  · funext q
    apply E.injective
    rw [er.iterate_right k,ct,et]

/-- An unrestricted equivariant root exists exactly when each isotypic multiplicity is
an actual sum of allowed positive block lengths. -/
theorem finite_root_criterion [Finite ι] {k : ℕ} (hk : 0 < k) :
    (∃ R : (Σ i, X i) → Σ i, X i,
      (∀ a q, R (jointDeck A a q) = jointDeck A a (R q)) ∧ R^[k] = jointTime A) ↔
    (∀ i, ∃ L : List ℕ, L.sum = Nat.card {j // Isotypic A i j} ∧
      ∀ ℓ ∈ L, 0 < ℓ ∧ ℓ ∣ k ∧ Local (k/ℓ) (A i)) := by
  classical
  letI := Fintype.ofFinite ι
  constructor
  · rintro ⟨R,hr,hs⟩ i
    exact root_lengths A hk R hr hs i
  · intro h
    let s := atlasSetoid A
    let Q := Quotient s
    letI : Fintype Q := Fintype.ofFinite Q
    let r : Q → ι := Quotient.out
    choose L hsum hallow using fun c : Q => h (r c)
    let fiber (c : Q) := {i : ι // Quotient.mk s i = c}
    have ef (c : Q) : fiber c ≃ {j // Isotypic A (r c) j} :=
      Equiv.subtypeEquivRight (fun j => by
        change Quotient.mk s j = c ↔ s.r (r c) j
        constructor
        · intro h
          exact s.symm (Quotient.exact (h.trans (Quotient.out_eq c).symm))
        · intro h
          exact (Quotient.sound (s.symm h)).trans (Quotient.out_eq c))
    have hcard (c : Q) : Fintype.card (fiber c) =
        Fintype.card (Σ t : Fin (L c).length, Fin ((L c).get t)) := by
      rw [Fintype.card_congr (ef c),Fintype.card_sigma]
      simp only [Fintype.card_fin]
      rw [← List.sum_ofFn,List.ofFn_get]
      exact (Nat.card_eq_fintype_card.symm.trans (hsum c).symm)
    let eC (c : Q) := Fintype.equivOfCardEq (hcard c)
    let B := Σ c : Q, Fin (L c).length
    let n (b : B) := (L b.1).get b.2
    let E : ι ≃ Σ b : B, Fin (n b) :=
      (Equiv.sigmaFiberEquiv (Quotient.mk s)).symm.trans
        ((Equiv.sigmaCongrRight eC).trans
          (Equiv.sigmaAssoc (fun c (t : Fin (L c).length) => Fin ((L c).get t))).symm)
    have hclass (i : ι) : (E i).1.1 = Quotient.mk s i := rfl
    have hi (i : ι) : Isotypic A i (r (E i).1.1) := by
      change s.r i (r (E i).1.1)
      apply Quotient.exact
      exact (hclass i).symm.trans (Quotient.out_eq (E i).1.1).symm
    exact roots_of_blocks A n (fun b => (hallow b.1 _ (List.get_mem _ _)).1)
      (fun b => (hallow b.1 _ (List.get_mem _ _)).2.1) (fun b => r b.1) E hi
      (fun b => (hallow b.1 _ (List.get_mem _ _)).2.2)

/-- The same root criterion for an arbitrary index type.  Infinite isotypic fibers have
no finite multiplicity obstruction: they are partitioned into full `k`-blocks. -/
theorem arbitrary_root_criterion {k : ℕ} (hk : 0 < k) :
    (∃ R : (Σ i, X i) → Σ i, X i,
      (∀ a q, R (jointDeck A a q) = jointDeck A a (R q)) ∧ R^[k] = jointTime A) ↔
    (∀ i, ∃ L : List ℕ, L.sum = Nat.card {j // Isotypic A i j} ∧
      ∀ ℓ ∈ L, 0 < ℓ ∧ ℓ ∣ k ∧ Local (k/ℓ) (A i)) := by
  classical
  constructor
  · rintro ⟨R,hr,hs⟩ i
    exact root_lengths A hk R hr hs i
  · intro h
    let s := atlasSetoid A
    let Q := Quotient s
    let r : Q → ι := Quotient.out
    choose L hsum hallow using fun c : Q => h (r c)
    let fiber (c : Q) := {i : ι // Quotient.mk s i = c}
    let Qfin := {c : Q // Finite (fiber c)}
    let Qinf := {c : Q // Infinite (fiber c)}
    let eSigma : (Σ c : Q, fiber c) ≃
        (Σ c : Qfin, fiber c.1) ⊕ (Σ c : Qinf, fiber c.1) :=
      { toFun := fun p =>
          if hfin : Finite (fiber p.1) then
            Sum.inl ⟨⟨p.1, hfin⟩, p.2⟩
          else
            Sum.inr ⟨⟨p.1, not_finite_iff_infinite.mp hfin⟩, p.2⟩
        invFun := Sum.elim (fun p => ⟨p.1.1, p.2⟩) (fun p => ⟨p.1.1, p.2⟩)
        left_inv := by
          intro p
          by_cases hfin : Finite (fiber p.1) <;> simp [hfin]
        right_inv := by
          rintro (⟨c,x⟩ | ⟨c,x⟩)
          · simp [c.2]
          · have hnot : ¬Finite (fiber c.1) := not_finite_iff_infinite.mpr c.2
            simp [hnot] }
    have efin (c : Qfin) : fiber c.1 ≃
        Σ t : Fin (L c.1).length, Fin ((L c.1).get t) := by
      letI : Finite (fiber c.1) := c.2
      letI : Fintype (fiber c.1) := Fintype.ofFinite _
      have ef0 : fiber c.1 ≃ {j // Isotypic A (r c.1) j} :=
        Equiv.subtypeEquivRight (fun j => by
          change Quotient.mk s j = c.1 ↔ s.r (r c.1) j
          constructor
          · intro hj
            exact s.symm (Quotient.exact (hj.trans (Quotient.out_eq c.1).symm))
          · intro hj
            exact (Quotient.sound (s.symm hj)).trans (Quotient.out_eq c.1))
      letI : Finite {j // Isotypic A (r c.1) j} :=
        Finite.of_injective ef0.symm ef0.symm.injective
      letI : Fintype {j // Isotypic A (r c.1) j} := Fintype.ofFinite _
      have hcard : Fintype.card (fiber c.1) =
          Fintype.card (Σ t : Fin (L c.1).length, Fin ((L c.1).get t)) := by
        rw [Fintype.card_congr ef0, Fintype.card_sigma]
        simp only [Fintype.card_fin]
        rw [← List.sum_ofFn, List.ofFn_get]
        exact (Nat.card_eq_fintype_card.symm.trans (hsum c.1).symm)
      exact Fintype.equivOfCardEq hcard
    have einf (c : Qinf) : fiber c.1 ≃ Σ b : fiber c.1, Fin k := by
      letI : Infinite (fiber c.1) := c.2
      exact (infinite_block_equiv (C := fiber c.1) hk).trans
        (Equiv.sigmaEquivProd (fiber c.1) (Fin k)).symm
    let Bfin := Σ c : Qfin, Fin (L c.1).length
    let Binf := Σ c : Qinf, fiber c.1
    let B := Bfin ⊕ Binf
    let n : B → ℕ := Sum.elim
      (fun b => (L b.1.1).get b.2) (fun _ => k)
    let qOfBlock : B → Q := Sum.elim (fun b => b.1.1) (fun b => b.1.1)
    let rBlock : B → ι := fun b => r (qOfBlock b)
    let efinBlocks : (Σ c : Qfin, fiber c.1) ≃
        Σ b : Bfin, Fin (n (Sum.inl b)) := by
      simpa [n, Bfin] using
        (Equiv.sigmaCongrRight (fun c => efin c)).trans
          (Equiv.sigmaAssoc (fun (c : Qfin) (t : Fin (L c.1).length) =>
            Fin ((L c.1).get t))).symm
    let einfBlocks : (Σ c : Qinf, fiber c.1) ≃
        Σ b : Binf, Fin (n (Sum.inr b)) := by
      simpa [n, Binf] using
        (Equiv.sigmaCongrRight (fun c => einf c)).trans
          (Equiv.sigmaAssoc (fun (c : Qinf) (b : fiber c.1) => Fin k)).symm
    let eblocks :
        ((Σ c : Qfin, fiber c.1) ⊕ (Σ c : Qinf, fiber c.1)) ≃
          Σ b : B, Fin (n b) :=
      (Equiv.sumCongr efinBlocks einfBlocks).trans
        (Equiv.sumSigmaDistrib (fun b : B => Fin (n b))).symm
    let E : ι ≃ Σ b : B, Fin (n b) :=
      (Equiv.sigmaFiberEquiv (Quotient.mk s)).symm.trans
        (eSigma.trans eblocks)
    have hqfin (x : Σ c : Qfin, fiber c.1) :
        qOfBlock (eblocks (Sum.inl x)).1 = x.1.1 := by
      rfl
    have hqinf (x : Σ c : Qinf, fiber c.1) :
        qOfBlock (eblocks (Sum.inr x)).1 = x.1.1 := by
      rfl
    have hclass (i : ι) : qOfBlock (E i).1 = Quotient.mk s i := by
      let y := (Equiv.sigmaFiberEquiv (Quotient.mk s)).symm i
      have hy : y.1 = Quotient.mk s i := rfl
      change qOfBlock (eblocks (eSigma y)).1 = Quotient.mk s i
      by_cases hfin : Finite (fiber (Quotient.mk s i))
      · have he : eSigma y = Sum.inl ⟨⟨y.1, hfin⟩, y.2⟩ := by
          have hyfin : Finite (fiber y.1) := by simpa [hy] using hfin
          simp [eSigma, hyfin]
        rw [he, hqfin]
        exact hy
      · have hynot : ¬Finite (fiber y.1) := by simpa [hy] using hfin
        have he : eSigma y =
            Sum.inr ⟨⟨y.1, not_finite_iff_infinite.mp hynot⟩, y.2⟩ := by
          simp [eSigma, hynot]
        rw [he, hqinf]
        exact hy
    have hi (i : ι) : Isotypic A i (rBlock (E i).1) := by
      change s.r i (r (qOfBlock (E i).1))
      apply Quotient.exact
      exact (hclass i).symm.trans (Quotient.out_eq (qOfBlock (E i).1)).symm
    have hpos : ∀ b : B, 0 < n b := by
      rintro (b | b)
      · exact (hallow b.1.1 _ (List.get_mem _ _)).1
      · exact hk
    have hdvd : ∀ b : B, n b ∣ k := by
      rintro (b | b)
      · exact (hallow b.1.1 _ (List.get_mem _ _)).2.1
      · exact dvd_rfl
    have hl : ∀ b : B, Local (k / n b) (A (rBlock b)) := by
      rintro (b | b)
      · simpa [n, rBlock, qOfBlock] using
          (hallow b.1.1 _ (List.get_mem _ _)).2.2
      · simpa [n, rBlock, qOfBlock, Nat.div_self hk] using
          local_one (A (rBlock (Sum.inr b)))
    exact roots_of_blocks A n hpos hdvd rBlock E hi hl

end Family

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteOrbitRootCriterion
