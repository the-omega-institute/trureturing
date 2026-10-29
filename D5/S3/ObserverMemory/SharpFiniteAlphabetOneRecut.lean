/- GID: D5/S3/ObserverMemory/SharpFiniteAlphabetOneRecut
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/SharpFiniteAlphabetOneRecut
   mirror-E: none(waiver:symbolic-finite-language-family)
   anchors: []
   utility: none
   digest: Finite-alphabet derivative tables classify actual one-credit boundaries and attain all sharp fiber bounds. -/

import D5.S3.ObserverMemory.SharpBinaryOneRecut
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
namespace D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut
open StrictAnchoredBoundary
variable {A : Type}

def derivative (S : Set (List A)) (b : A) : Set (List A) := {f | b :: f ∈ S}
def oneBoundary (C : Set (List A)) (k : Nat) : Set (Set (List A) × A) :=
  {z | z.1 ∈ residualSet C (k - 1) ∧ (derivative z.1 z.2).Nonempty}
def forward (z : Set (List A) × A) : Set (List A) := derivative z.1 z.2
def currentFiber (C : Set (List A)) (k : Nat) (E : Set (List A)) :
    Set (Set (List A) × A) := {z | z ∈ oneBoundary C k ∧ forward z = E}
def fixedFiber (C : Set (List A)) (k : Nat) (E : Set (List A)) (b : A) :
    Set (Set (List A)) := {S | S ∈ residualSet C (k - 1) ∧ derivative S b = E}
def FullBranching (C : Set (List A)) (k : Nat) : Prop :=
  ∀ v : List A, v.length = k - 1 → (∃ f, v ++ f ∈ C) →
    ∀ b : A, ∃ f, (v ++ [b]) ++ f ∈ C
abbrev Remaining (A : Type) (b : A) := {a : A // a ≠ b}

def Bounds [Finite A] (C : Set (List A)) (k B : Nat) : Prop :=
  (∀ E ∈ residualSet C k,
    (∀ b, Nat.card (fixedFiber C k E b) ≤ B ^ (Nat.card A - 1)) ∧
    Nat.card (currentFiber C k E) ≤ Nat.card A * B ^ (Nat.card A - 1)) ∧
  Nat.card (oneBoundary C k) ≤ Nat.card A * Nat.card (residualSet C k) * B ^ (Nat.card A - 1)

def StrictIdentification (C : Set (List A)) (k : Nat) : Prop :=
  ∃ e : oneBoundary C k ≃ image C (k, 1),
    (∀ z, (e z).val = (z.val.1, [z.val.2])) ∧
    (∀ z, {f | (e z).val.2 ++ f ∈ (e z).val.1} = forward z.val) ∧
    (∀ z, (e z).val.2 = [z.val.2])

private theorem residual_finite [Finite A] (C : Set (List A)) (k : Nat) :
    (residualSet C k).Finite := by
  exact ((List.finite_length_eq A k).image (residual C)).subset
    (by rintro S ⟨v,hv,_,rfl⟩; exact ⟨v,hv,rfl⟩)

private theorem residual_nonempty {C : Set (List A)} {k : Nat}
    {S : Set (List A)} (hS : S ∈ residualSet C k) : S.Nonempty := by
  obtain ⟨v,_,⟨f,hf⟩,rfl⟩ := hS
  exact ⟨f,hf⟩

private theorem shift (C : Set (List A)) (v : List A) (b : A) :
    residual C (v ++ [b]) = derivative (residual C v) b := by
  ext f; simp [residual,derivative,List.append_assoc]

private theorem derivative_member {C : Set (List A)} {k : Nat} (hk : 1 ≤ k)
    {S : Set (List A)} (hS : S ∈ residualSet C (k - 1)) (b : A)
    (he : (derivative S b).Nonempty) : derivative S b ∈ residualSet C k := by
  obtain ⟨v,hv,_,rfl⟩ := hS
  obtain ⟨f,hf⟩ := he
  refine ⟨v ++ [b],?_,⟨f,?_⟩,shift C v b⟩
  · simp only [List.length_append,List.length_singleton]; omega
  · simpa [derivative,residual,List.append_assoc] using hf

private theorem previous_no_nil {n k : Nat} {C : Set (List A)}
    (hl : ∀ w ∈ C, w.length = n) (hk : 1 ≤ k) (hkn : k ≤ n)
    {S : Set (List A)} (hS : S ∈ residualSet C (k - 1)) : [] ∉ S := by
  obtain ⟨v,hv,_,rfl⟩ := hS
  intro h
  have he := hl _ h
  simp only [List.append_nil] at he
  omega

private theorem derivative_ext {S T : Set (List A)} (hS : [] ∉ S) (hT : [] ∉ T)
    (h : ∀ b, derivative S b = derivative T b) : S = T := by
  ext f
  cases f with
  | nil => simp [hS,hT]
  | cons b f => exact Set.ext_iff.mp (h b) f

private theorem remaining_card [Finite A] (b : A) :
    Nat.card (Remaining A b) = Nat.card A - 1 := by
  letI := Fintype.ofFinite A
  simp [Remaining,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]

private theorem sigma_card [Finite A] {B : Type} [Finite B] :
    Nat.card (Σ b : A, Remaining A b → B) = Nat.card A * Nat.card B ^ (Nat.card A - 1) := by
  letI := Fintype.ofFinite A
  rw [Nat.card_sigma]
  simp [Nat.card_fun,remaining_card,Nat.card_eq_fintype_card]

private theorem strict_identification [Finite A] [Nonempty A]
    (n : Nat) (C : Set (List A)) (hl : ∀ w ∈ C, w.length = n) (hc : C.Nonempty)
    (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n) : StrictIdentification C k := by
  have hi := (strict_anchored_specialization n C hl hc k 1 hk hkn).2.2.1
  have member : ∀ S b, (S,[b]) ∈ image C (k,1) ↔ (S,b) ∈ oneBoundary C k := by
    intro S b
    rw [hi]
    simp [pref,oneBoundary,derivative]
  let to : oneBoundary C k → image C (k,1) := fun z =>
    ⟨(z.val.1,[z.val.2]),(member _ _).mpr z.property⟩
  have onto : Function.Surjective to := by
    rintro ⟨⟨S,t⟩,ht⟩
    have ht' := ht
    rw [hi] at ht'
    have len : t.length = 1 := ht'.2.1
    obtain ⟨b,rfl⟩ := List.length_eq_one.mp len
    exact ⟨⟨(S,b),(member _ _).mp ht⟩,rfl⟩
  have inj : Function.Injective to := by
    intro z w he
    apply Subtype.ext
    have h := congrArg Subtype.val he
    simpa [to,Prod.mk.injEq] using h
  refine ⟨Equiv.ofBijective to ⟨inj,onto⟩,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

private theorem bounds_with [Finite A] (n : Nat) (C : Set (List A))
    (hl : ∀ w ∈ C, w.length = n) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n)
    (B : Set (Set (List A))) (hB : B.Finite)
    (hder : ∀ S ∈ residualSet C (k-1), ∀ b, derivative S b ∈ B) :
    Bounds C k (Nat.card B) := by
  letI := hB.fintype
  letI := (residual_finite C k).fintype
  let other (S : residualSet C (k-1)) (b : A) : Remaining A b → B :=
    fun a => ⟨derivative S.val a.val,hder _ S.property _⟩
  have reconstruct : ∀ (S T : residualSet C (k-1)) (b : A),
      derivative S.val b = derivative T.val b → other S b = other T b → S = T := by
    intro S T b hb ho
    apply Subtype.ext
    apply derivative_ext (previous_no_nil hl hk hkn S.property)
      (previous_no_nil hl hk hkn T.property)
    intro a
    by_cases ha : a = b
    · simpa [ha] using hb
    · exact congrArg Subtype.val (congrFun ho ⟨a,ha⟩)
  have point_inj : Function.Injective (fun z : oneBoundary C k =>
      ((⟨forward z.val,derivative_member hk z.property.1 z.val.2 z.property.2⟩ : residualSet C k),
        (⟨z.val.2,other ⟨z.val.1,z.property.1⟩ z.val.2⟩ : Σ b : A, Remaining A b → B))) := by
    intro z w he
    have hb : z.val.2 = w.val.2 := congrArg (fun p => p.2.1) he
    apply Subtype.ext
    apply Prod.ext ?_ hb
    apply congrArg Subtype.val (reconstruct ⟨z.val.1,z.property.1⟩ ⟨w.val.1,w.property.1⟩ z.val.2 ?_ ?_)
    · simpa [forward,hb] using congrArg (fun p => p.1.val) he
    · have hh := congrArg Prod.snd he
      cases z with | mk z hz =>
        cases w with | mk w hw =>
          rcases z with ⟨S,b⟩
          rcases w with ⟨T,c⟩
          dsimp at hb hh ⊢
          subst c
          exact (Sigma.mk.inj_iff.mp hh).2
  constructor
  · intro E hE
    constructor
    · intro b
      let f : fixedFiber C k E b → (Remaining A b → B) :=
        fun S => other ⟨S.val,S.property.1⟩ b
      have hf : Function.Injective f := by
        intro S T he
        apply Subtype.ext
        exact congrArg Subtype.val (reconstruct ⟨S.val,S.property.1⟩ ⟨T.val,T.property.1⟩ b
          (S.property.2.trans T.property.2.symm) he)
      simpa [Nat.card_fun,remaining_card] using Nat.card_le_card_of_injective f hf
    · let f : currentFiber C k E → (Σ b : A, Remaining A b → B) :=
        fun z => ⟨z.val.2,other ⟨z.val.1,z.property.1.1⟩ z.val.2⟩
      have hf : Function.Injective f := by
        intro z w he
        have hp := point_inj (a₁ := ⟨z.val,z.property.1⟩) (a₂ := ⟨w.val,w.property.1⟩)
        apply Subtype.ext
        apply congrArg Subtype.val (hp ?_)
        apply Prod.ext ?_ he
        exact Subtype.ext (z.property.2.trans w.property.2.symm)
      simpa [sigma_card] using Nat.card_le_card_of_injective f hf
  · have hc := Nat.card_le_card_of_injective _ point_inj
    simpa [Nat.card_prod,sigma_card,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hc

end D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut
