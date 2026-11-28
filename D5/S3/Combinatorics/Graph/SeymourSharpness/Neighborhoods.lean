/- GID: D5/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SeymourSharpness/Neighborhoods
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact neighborhoods in complete directed compositions with dependent clusters. -/

module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.SetTheory.Cardinal.Finite

/-! Exact two-step neighborhoods and directed walks in dependent graph compositions. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.SeymourSharpness

variable {V W : Type*}

/-- Exact second neighbors exclude the root and its first outneighbors. -/
def ExactSecond (R : V → V → Prop) (x z : V) : Prop :=
  z ≠ x ∧ ¬ R x z ∧ ∃ y, R x y ∧ R y z

/-- Directed walks, including the walk of length zero. -/
inductive Walk (R : V → V → Prop) : ℕ → V → V → Prop
  | nil (x : V) : Walk R 0 x x
  | cons {k : ℕ} {x y z : V} : R x y → Walk R k y z → Walk R (k + 1) x z

noncomputable def outDegree (R : V → V → Prop) (x : V) : ℕ :=
  Nat.card {y // R x y}

noncomputable def secondDegree (R : V → V → Prop) (x : V) : ℕ :=
  Nat.card {z // ExactSecond R x z}

def Good (R : V → V → Prop) (x : V) : Prop := outDegree R x ≤ secondDegree R x

variable {I : Type*} {C : I → Type*}

/-- All edges of the base relation are replaced by complete cross-cluster edges. -/
def composition (B : I → I → Prop) (A : (i : I) → C i → C i → Prop) :
    (Σ i, C i) → (Σ i, C i) → Prop
  | ⟨i, a⟩, ⟨j, b⟩ => B i j ∨ ∃ h : j = i, A i a (h ▸ b)

theorem composition_asymm (B : I → I → Prop) (A : (i : I) → C i → C i → Prop)
    (hB : ∀ ⦃i j⦄, B i j → ¬ B j i)
    (hA : ∀ i, ∀ ⦃a b⦄, A i a b → ¬ A i b a) :
    ∀ ⦃x y⦄, composition B A x y → ¬ composition B A y x := by
  rintro ⟨i,a⟩ ⟨j,b⟩ (hij | ⟨h,hab⟩) (hji | ⟨h,hba⟩)
  · exact hB hij hji
  · subst j
    exact hB hij hij
  · subst j
    exact hB hji hji
  · subst j
    exact hA i hab hba

/-- In a dependent composition, an exact second neighbor is either internal
or lies above an exact second neighbor of the base. -/
theorem composition_exact_second (B : I → I → Prop)
    (A : (i : I) → C i → C i → Prop)
    (hB : ∀ ⦃i j⦄, B i j → ¬ B j i) (inh : ∀ i, Nonempty (C i))
    (i j : I) (a : C i) (b : C j) :
    ExactSecond (composition B A) ⟨i,a⟩ ⟨j,b⟩ ↔
      (∃ h : j = i, ExactSecond (A i) a (h ▸ b)) ∨ ExactSecond B i j := by
  constructor
  · rintro ⟨hne,hnadj,⟨⟨k,c⟩,hac,hcb⟩⟩
    rcases hac with hik | ⟨h,hac⟩
    · rcases hcb with hkj | ⟨h,hcb⟩
      · right
        refine ⟨?_,fun hij => hnadj (Or.inl hij),⟨k,hik,hkj⟩⟩
        intro h
        subst j
        exact hB hik hkj
      · subst k
        exact (hnadj (Or.inl hik)).elim
    · subst k
      rcases hcb with hij | ⟨h,hcb⟩
      · exact (hnadj (Or.inl hij)).elim
      · subst j
        left
        refine ⟨rfl,?_,?_,⟨c,hac,hcb⟩⟩
        · intro h
          change b = a at h
          exact hne (congrArg (Sigma.mk i) h)
        · intro hab
          exact hnadj (Or.inr ⟨rfl,hab⟩)
  · rintro (⟨h,hne,hnadj,⟨c,hac,hcb⟩⟩ | ⟨hne,hnadj,⟨k,hik,hkj⟩⟩)
    · subst j
      refine ⟨?_,?_,⟨⟨i,c⟩,Or.inr ⟨rfl,hac⟩,Or.inr ⟨rfl,hcb⟩⟩⟩
      · intro h
        apply hne
        exact eq_of_heq (Sigma.mk.inj h).2
      · rintro (hii | ⟨h,hab⟩)
        · exact hB hii hii
        · exact hnadj hab
    · obtain ⟨c⟩ := inh k
      refine ⟨?_,?_,⟨⟨k,c⟩,Or.inl hik,Or.inl hkj⟩⟩
      · intro h
        exact hne (congrArg Sigma.fst h)
      · rintro (hij | ⟨h,hab⟩)
        · exact hnadj hij
        · exact hne h

private noncomputable def fiberEquiv (i : I) (P : C i → Prop) :
    {a // P a} ≃ {z : Σ j, C j // ∃ h : z.1 = i, P (h ▸ z.2)} := by
  classical
  apply Equiv.ofBijective (fun a : {a // P a} =>
    (⟨⟨i,a.1⟩,rfl,a.2⟩ : {z : Σ j, C j // ∃ h : z.1 = i, P (h ▸ z.2)}))
  constructor
  · intro a b h
    apply Subtype.ext
    exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
  · rintro ⟨⟨j,b⟩,h,hb⟩
    change j = i at h
    subst j
    exact ⟨⟨b,hb⟩,rfl⟩

private lemma fiber_card (i : I) (P : C i → Prop) :
    Nat.card {z : Σ j, C j // ∃ h : z.1 = i, P (h ▸ z.2)} = Nat.card {a // P a} :=
  Nat.card_congr (fiberEquiv i P).symm

/-- Only the root and the two relevant neighbor fibers need be finite. -/
theorem composition_degrees
    (B : I → I → Prop) (A : (i : I) → C i → C i → Prop)
    (hB : ∀ ⦃i j⦄, B i j → ¬ B j i) (inh : ∀ i, Nonempty (C i))
    (i s t : I) [Finite (C i)] [Finite (C s)] [Finite (C t)] (a : C i)
    (hfirst : ∀ j, B i j ↔ j = s)
    (hsecond : ∀ j, ExactSecond B i j ↔ j = t) :
    outDegree (composition B A) ⟨i,a⟩ = outDegree (A i) a + Nat.card (C s) ∧
    secondDegree (composition B A) ⟨i,a⟩ = secondDegree (A i) a + Nat.card (C t) := by
  classical
  have hc (j : I) : Nat.card {z : Σ j, C j // z.1 = j} = Nat.card (C j) :=
    Nat.card_congr (Equiv.sigmaSubtype j)
  constructor
  · let P : (Σ j, C j) → Prop := fun z => B i z.1
    let Q : (Σ j, C j) → Prop := fun z => ∃ h : z.1 = i, A i a (h ▸ z.2)
    have hd : Disjoint P Q := by
      apply disjoint_iff.mpr
      funext z
      apply propext
      constructor
      · rintro ⟨hz,⟨h,_⟩⟩
        have hii : B i i := by simpa only [P,h] using hz
        exact (hB hii hii).elim
      · exact False.elim
    let ep : {z // P z} ≃ C s :=
      (Equiv.subtypeEquivRight (fun z : Σ j, C j => hfirst z.1)).trans
        (Equiv.sigmaSubtype s)
    let eq : {z // Q z} ≃ {b // A i a b} := (fiberEquiv i (A i a)).symm
    haveI : Finite {z // P z} := Finite.of_injective ep ep.injective
    haveI : Finite {z // Q z} := Finite.of_injective eq eq.injective
    change Nat.card {z // P z ∨ Q z} = _
    rw [Nat.card_congr (subtypeOrEquiv P Q hd),Nat.card_sum]
    have hp : Nat.card {z // P z} = Nat.card (C s) := by
      change Nat.card {z : Σ j, C j // B i z.1} = _
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun z : Σ j, C j => hfirst z.1))]
      exact hc s
    have hq : Nat.card {z // Q z} = outDegree (A i) a := fiber_card i (A i a)
    rw [hp,hq]
    omega
  · let P : (Σ j, C j) → Prop := fun z => ∃ h : z.1 = i, ExactSecond (A i) a (h ▸ z.2)
    let Q : (Σ j, C j) → Prop := fun z => ExactSecond B i z.1
    have hd : Disjoint P Q := by
      apply disjoint_iff.mpr
      funext z
      apply propext
      constructor
      · rintro ⟨⟨h,_⟩,hz⟩
        exact (hz.1 h).elim
      · exact False.elim
    unfold secondDegree
    have he : ∀ z : Σ j, C j, ExactSecond (composition B A) ⟨i,a⟩ z ↔ P z ∨ Q z := by
      rintro ⟨j,b⟩
      exact composition_exact_second B A hB inh i j a b
    rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
    let ep : {z // P z} ≃ {b // ExactSecond (A i) a b} :=
      (fiberEquiv i (ExactSecond (A i) a)).symm
    let eq : {z // Q z} ≃ C t :=
      (Equiv.subtypeEquivRight (fun z : Σ j, C j => hsecond z.1)).trans
        (Equiv.sigmaSubtype t)
    haveI : Finite {z // P z} := Finite.of_injective ep ep.injective
    haveI : Finite {z // Q z} := Finite.of_injective eq eq.injective
    change Nat.card {z // P z ∨ Q z} = _
    rw [Nat.card_congr (subtypeOrEquiv P Q hd),Nat.card_sum]
    have hp : Nat.card {z // P z} = secondDegree (A i) a :=
      fiber_card i (ExactSecond (A i) a)
    have hq : Nat.card {z // Q z} = Nat.card (C t) := by
      change Nat.card {z : Σ j, C j // ExactSecond B i z.1} = _
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun z : Σ j, C j => hsecond z.1))]
      exact hc t
    change Nat.card {z // P z} + Nat.card {z // Q z} = secondDegree (A i) a + _
    rw [hp,hq]

end D5.S3.Combinatorics.Graph.SeymourSharpness
