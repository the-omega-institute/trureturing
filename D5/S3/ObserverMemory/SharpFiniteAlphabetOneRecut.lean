/- GID: D5/S3/ObserverMemory/SharpFiniteAlphabetOneRecut
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/SharpFiniteAlphabetOneRecut
   mirror-E: none(waiver:symbolic-finite-language-family)
   anchors: []
   utility: none
   digest: Actual finite-alphabet derivative tables attain sharp one-credit fiber bounds. -/

import D5.S3.ObserverMemory.SharpBinaryOneRecut
import Mathlib.Computability.MyhillNerode

/-! Actual derivative-table reconstruction and finite-alphabet sharpness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
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

def FullBounds [Finite A] (C : Set (List A)) (k : Nat) : Prop :=
  (∀ E ∈ residualSet C k,
    (∀ b, Nat.card (fixedFiber C k E b) ≤ Nat.card (residualSet C k) ^ (Nat.card A - 1)) ∧
    Nat.card (currentFiber C k E) ≤ Nat.card A * Nat.card (residualSet C k) ^ (Nat.card A - 1)) ∧
  Nat.card (oneBoundary C k) ≤ Nat.card A * Nat.card (residualSet C k) ^ Nat.card A

def FiniteCarriers (C : Set (List A)) (k : Nat) : Prop :=
  C.Finite ∧
  (∀ j, (pref C j).Finite ∧ (residualSet C j).Finite ∧
    ∀ S ∈ residualSet C j, S.Finite) ∧
  (oneBoundary C k).Finite ∧ (image C (k,1)).Finite ∧
  ∀ E, (currentFiber C k E).Finite ∧ ∀ b, (fixedFiber C k E b).Finite

def Attains [Finite A] (N : Nat) (full : Bool) : Prop :=
  ∃ (n k : Nat) (C : Set (List A)),
    C.Nonempty ∧ (∀ w ∈ C, w.length = n) ∧ 1 ≤ k ∧ k ≤ n ∧
    (full = true → FullBranching C k) ∧
    Nat.card (residualSet C k) = N ∧
    (∀ E ∈ residualSet C k,
      (∀ b, Nat.card (fixedFiber C k E b) =
        (if full then N else N+1) ^ (Nat.card A - 1)) ∧
      Nat.card (currentFiber C k E) = Nat.card A * (if full then N else N+1) ^ (Nat.card A - 1)) ∧
    Nat.card (oneBoundary C k) =
      if full then Nat.card A * N ^ Nat.card A
      else Nat.card A * N * (N+1) ^ (Nat.card A - 1)

def StrictIdentification (C : Set (List A)) (k : Nat) : Prop :=
  ∃ e : oneBoundary C k ≃ image C (k, 1),
    (∀ z, (e z).val = (z.val.1, [z.val.2])) ∧
    (∀ z, {f | (e z).val.2 ++ f ∈ (e z).val.1} = forward z.val) ∧
    (∀ z, (e z).val.2 = [z.val.2])

private theorem residual_finite [Finite A] (C : Set (List A)) (k : Nat) :
    (residualSet C k).Finite := by
  classical
  exact ((List.finite_length_eq A k).image (residual C)).subset
    (by rintro S ⟨v,hv,_,rfl⟩; exact ⟨v,hv,rfl⟩)

private theorem residual_nonempty {C : Set (List A)} {k : Nat}
    {S : Set (List A)} (hS : S ∈ residualSet C k) : S.Nonempty := by
  classical
  obtain ⟨v,_,⟨f,hf⟩,rfl⟩ := hS
  exact ⟨f,hf⟩

private theorem shift (C : Set (List A)) (v : List A) (b : A) :
    residual C (v ++ [b]) = derivative (residual C v) b := by
  exact Language.leftQuotient_append C v [b]

private theorem derivative_member {C : Set (List A)} {k : Nat} (hk : 1 ≤ k)
    {S : Set (List A)} (hS : S ∈ residualSet C (k - 1)) (b : A)
    (he : (derivative S b).Nonempty) : derivative S b ∈ residualSet C k := by
  classical
  obtain ⟨v,hv,_,rfl⟩ := hS
  obtain ⟨f,hf⟩ := he
  refine ⟨v ++ [b],?_,⟨f,?_⟩,shift C v b⟩
  · simp only [List.length_append,List.length_singleton]; omega
  · simpa [derivative,StrictAnchoredBoundary.residual,List.append_assoc] using hf

private theorem previous_no_nil {n k : Nat} {C : Set (List A)}
    (hl : ∀ w ∈ C, w.length = n) (hk : 1 ≤ k) (hkn : k ≤ n)
    {S : Set (List A)} (hS : S ∈ residualSet C (k - 1)) : [] ∉ S := by
  classical
  obtain ⟨v,hv,_,rfl⟩ := hS
  intro h
  have he := hl _ h
  simp only [List.append_nil] at he
  omega

private theorem derivative_ext {S T : Set (List A)} (hS : [] ∉ S) (hT : [] ∉ T)
    (h : ∀ b, derivative S b = derivative T b) : S = T := by
  classical
  ext f
  cases f with
  | nil => simp [hS,hT]
  | cons b f => exact Set.ext_iff.mp (h b) f

private theorem remaining_card [Finite A] (b : A) :
    Nat.card (Remaining A b) = Nat.card A - 1 := by
  classical
  let := Fintype.ofFinite A
  simp [Remaining,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]

private theorem sigma_card [Finite A] {B : Type} [Finite B] :
    Nat.card (Σ b : A, Remaining A b → B) = Nat.card A * Nat.card B ^ (Nat.card A - 1) := by
  classical
  let := Fintype.ofFinite A
  rw [Nat.card_sigma]
  simp [Nat.card_fun,Nat.card_eq_fintype_card]

private theorem strict_identification [Finite A] [Nonempty A]
    (n : Nat) (C : Set (List A)) (hl : ∀ w ∈ C, w.length = n) (hc : C.Nonempty)
    (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n) : StrictIdentification C k := by
  classical
  have hi := (strict_anchored_specialization n C hl hc k 1 hk hkn).2.2.1
  have member : ∀ S b, (S,[b]) ∈ image C (k,1) ↔ (S,b) ∈ oneBoundary C k := by
    intro S b
    rw [hi]
    simp [pref,oneBoundary,derivative,Set.Nonempty]
  let liftBoundary : oneBoundary C k → image C (k,1) := fun z =>
    ⟨(z.val.1,[z.val.2]),(member _ _).mpr z.property⟩
  have onto : Function.Surjective liftBoundary := by
    rintro ⟨⟨S,t⟩,ht⟩
    have ht' := ht
    rw [hi] at ht'
    have len : t.length = 1 := ht'.2.1
    obtain ⟨b,rfl⟩ := List.length_eq_one_iff.mp len
    exact ⟨⟨(S,b),(member _ _).mp ht⟩,rfl⟩
  have inj : Function.Injective liftBoundary := by
    intro z w he
    apply Subtype.ext
    have h := congrArg Subtype.val he
    have hh : z.val.1 = w.val.1 ∧ z.val.2 = w.val.2 := by
      simpa [liftBoundary,Prod.mk.injEq] using h
    exact Prod.ext hh.1 hh.2
  refine ⟨Equiv.ofBijective liftBoundary ⟨inj,onto⟩,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

private theorem bounds_with [Finite A] (n : Nat) (C : Set (List A))
    (hl : ∀ w ∈ C, w.length = n) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n)
    (B : Set (Set (List A))) (hB : B.Finite)
    (hder : ∀ S ∈ residualSet C (k - 1), ∀ b, derivative S b ∈ B) :
    Bounds C k (Nat.card B) := by
  classical
  let := hB.fintype
  let := (residual_finite C k).fintype
  let other (S : residualSet C (k - 1)) (b : A) : Remaining A b → B :=
    fun a => ⟨derivative S.val a.val,hder _ S.property _⟩
  have reconstruct : ∀ (S T : residualSet C (k - 1)) (b : A),
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
    apply congrArg Subtype.val
      (reconstruct ⟨z.val.1,z.property.1⟩ ⟨w.val.1,w.property.1⟩ z.val.2 ?_ ?_)
    · simpa [forward,hb] using congrArg (fun p => p.1.val) he
    · have hh := congrArg Prod.snd he
      cases z with | mk z hz =>
        cases w with | mk w hw =>
          rcases z with ⟨S,b⟩
          rcases w with ⟨T,c⟩
          dsimp at hb hh ⊢
          subst c
          exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  constructor
  · intro E hE
    constructor
    · intro b
      let f : fixedFiber C k E b → (Remaining A b → B) :=
        fun S => other ⟨S.val,S.property.1⟩ b
      have hf : Function.Injective f := by
        intro S T he
        apply Subtype.ext
        exact congrArg (fun S : residualSet C (k - 1) => S.val)
          (reconstruct ⟨S.val,S.property.1⟩ ⟨T.val,T.property.1⟩ b
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


private def encoded {N : Nat} (e : Bool ↪ A) (i : Option (Fin N)) : List A :=
  (SharpBinaryOneRecut.word i).map e
private theorem encoded_length {N : Nat} (e : Bool ↪ A) (i : Option (Fin N)) :
    (encoded e i).length = N := by simp [encoded,SharpBinaryOneRecut.word_length]
private theorem encoded_injective (N : Nat) (e : Bool ↪ A) :
    Function.Injective (@encoded A N e) := by
  classical
  intro i j h
  exact SharpBinaryOneRecut.word_injective N ((List.map_injective_iff.mpr e.injective) h)

private def blocks {N : Nat} (e : Bool ↪ A) (xs : List A) (t : A → Option (Fin N)) : List A :=
  xs.flatMap (fun a => encoded e (t a))
private theorem blocks_length {N : Nat} (e : Bool ↪ A) (xs : List A) (t : A → Option (Fin N)) :
    (blocks e xs t).length = xs.length * N := by
  classical
  simp [blocks,encoded_length]
private theorem blocks_recover {N : Nat} (e : Bool ↪ A) (xs : List A)
    (t u : A → Option (Fin N)) (h : blocks e xs t = blocks e xs u) :
    ∀ a ∈ xs, t a = u a := by
  classical
  have he : xs.map (fun a => encoded e (t a)) = xs.map (fun a => encoded e (u a)) := by
    apply List.eq_iff_flatten_eq.mpr
    refine ⟨h,?_⟩
    simp [encoded_length]
  intro a ha
  exact encoded_injective N e ((List.map_inj_left.mp he) a ha)

private def anchor [Fintype A] {N : Nat} (e : Bool ↪ A) (t : A → Option (Fin N)) : List A :=
  blocks e Finset.univ.toList t
private theorem anchor_length [Fintype A] {N : Nat} (e : Bool ↪ A) (t : A → Option (Fin N)) :
    (anchor e t).length = Nat.card A * N := by simp [anchor,blocks_length,Nat.card_eq_fintype_card]
private theorem anchor_injective [Fintype A] (N : Nat) (e : Bool ↪ A) :
    Function.Injective (@anchor A _ N e) := by
  classical
  intro t u h
  funext a
  exact blocks_recover e _ t u h a (by simp)

private def Admissible {N : Nat} (full : Bool) (t : A → Option (Fin N)) : Prop :=
  (∃ b s, t b = some s) ∧ (full = true → ∀ b, t b ≠ none)
private def predecessor {N : Nat} (e : Bool ↪ A) (t : A → Option (Fin N)) : Set (List A) :=
  {f | ∃ b s, t b = some s ∧ f = b :: encoded e (some s)}
private def payload {N : Nat} (e : Bool ↪ A) (i : Option (Fin N)) : Set (List A) :=
  {f | ∃ s, i = some s ∧ f = encoded e (some s)}
private def relation [Fintype A] (e : Bool ↪ A) (N : Nat) (full : Bool) : Set (List A) :=
  {w | ∃ t : A → Option (Fin N), Admissible full t ∧
    ∃ b s, t b = some s ∧ w = anchor e t ++ b :: encoded e (some s)}

private theorem derivative_predecessor {N : Nat} (e : Bool ↪ A) (t : A → Option (Fin N)) (b : A) :
    derivative (predecessor e t) b = payload e (t b) := by
  classical
  ext f
  simp [derivative,predecessor,payload]
private theorem payload_injective (N : Nat) (e : Bool ↪ A) :
    Function.Injective (@payload A N e) := by
  classical
  intro i j he
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some t =>
      have hh : encoded e (some t) ∈ payload e (some t) := ⟨t,rfl,rfl⟩
      rw [← he] at hh
      simp [payload] at hh
  | some s =>
    have hh : encoded e (some s) ∈ payload e (some s) := ⟨s,rfl,rfl⟩
    rw [he] at hh
    obtain ⟨t,rfl,ht⟩ := hh
    exact encoded_injective N e ht
private theorem predecessor_injective (N : Nat) (e : Bool ↪ A) :
    Function.Injective (@predecessor A N e) := by
  classical
  intro t u h
  funext b
  apply payload_injective N e
  simpa only [derivative_predecessor] using congrArg (fun S => derivative S b) h

private theorem residual_anchor [Fintype A] (N : Nat) (full : Bool)
    (e : Bool ↪ A) (t : A → Option (Fin N)) (ht : Admissible full t) :
    residual (relation e N full) (anchor e t) = predecessor e t := by
  classical
  ext f
  constructor
  · rintro ⟨u,hu,b,s,hs,he⟩
    have he' := List.append_inj he ((anchor_length e t).trans (anchor_length e u).symm)
    have htu := anchor_injective N e he'.1
    subst u
    exact ⟨b,s,hs,he'.2⟩
  · rintro ⟨b,s,hs,rfl⟩
    exact ⟨t,ht,b,s,hs,rfl⟩

private theorem previous_prefix_complete [Fintype A] {N : Nat} {full : Bool}
    (e : Bool ↪ A) {v : List A} (hv : v.length = Nat.card A * N) :
    (∃ f, v ++ f ∈ relation e N full) ↔
      ∃ t : A → Option (Fin N), Admissible full t ∧ v = anchor e t := by
  classical
  constructor
  · rintro ⟨f,t,ht,b,s,hs,he⟩
    exact ⟨t,ht,(List.append_inj he (hv.trans (anchor_length e t).symm)).1⟩
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨b,s,hs⟩ := ht.1
    exact ⟨b :: encoded e (some s),t,ht,b,s,hs,rfl⟩

private theorem current_prefix_complete [Fintype A] {N : Nat} {full : Bool}
    (e : Bool ↪ A) {v : List A} (hv : v.length = Nat.card A * N + 1) :
    (∃ f, v ++ f ∈ relation e N full) ↔
      ∃ t : A → Option (Fin N), Admissible full t ∧
        ∃ b s, t b = some s ∧ v = anchor e t ++ [b] := by
  classical
  constructor
  · rintro ⟨f,t,ht,b,s,hs,he⟩
    have he' : v ++ f = (anchor e t ++ [b]) ++ encoded e (some s) := by
      simpa [List.append_assoc] using he
    refine ⟨t,ht,b,s,hs,(List.append_inj he' ?_).1⟩
    simp [anchor_length,hv]
  · rintro ⟨t,ht,b,s,hs,rfl⟩
    exact ⟨encoded e (some s),t,ht,b,s,hs,by simp [List.append_assoc]⟩

private theorem residual_selected [Fintype A] {N : Nat} {full : Bool}
    (e : Bool ↪ A) (t : A → Option (Fin N)) (ht : Admissible full t)
    (b : A) (s : Fin N) (hs : t b = some s) :
    residual (relation e N full) (anchor e t ++ [b]) = {encoded e (some s)} := by
  classical
  rw [shift,residual_anchor N full e t ht,derivative_predecessor,hs]
  ext f
  simp [payload]

private theorem previous_residuals [Fintype A] (N : Nat) (full : Bool) (e : Bool ↪ A) :
    residualSet (relation e N full) (Nat.card A * N) =
      {S | ∃ t : A → Option (Fin N), Admissible full t ∧ predecessor e t = S} := by
  classical
  ext S
  constructor
  · rintro ⟨v,hv,hC,rfl⟩
    obtain ⟨t,ht,rfl⟩ := (previous_prefix_complete e hv).mp hC
    exact ⟨t,ht,(residual_anchor N full e t ht).symm⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨anchor e t,anchor_length e t,
      (previous_prefix_complete e (anchor_length e t)).mpr ⟨t,ht,rfl⟩,
      residual_anchor N full e t ht⟩

private theorem current_residuals [Fintype A] (N : Nat) (full : Bool) (e : Bool ↪ A) :
    residualSet (relation e N full) (Nat.card A * N + 1) =
      Set.range (fun s : Fin N => ({encoded e (some s)} : Set (List A))) := by
  classical
  ext S
  constructor
  · rintro ⟨v,hv,hC,rfl⟩
    obtain ⟨t,ht,b,s,hs,rfl⟩ := (current_prefix_complete e hv).mp hC
    exact ⟨s,(residual_selected e t ht b s hs).symm⟩
  · rintro ⟨s,rfl⟩
    let t : A → Option (Fin N) := fun _ => some s
    have ht : Admissible full t := ⟨⟨e false,s,rfl⟩,by simp [t]⟩
    refine ⟨anchor e t ++ [e false],by simp [anchor_length],?_,residual_selected e t ht _ s rfl⟩
    exact ⟨encoded e (some s),t,ht,e false,s,rfl,by simp [List.append_assoc]⟩

private theorem actual_boundary [Fintype A] (N : Nat) (full : Bool) (e : Bool ↪ A) :
    oneBoundary (relation e N full) (Nat.card A * N + 1) =
      {z | ∃ t : A → Option (Fin N), Admissible full t ∧
        ∃ s, t z.2 = some s ∧ z.1 = predecessor e t} := by
  classical
  ext z
  rcases z with ⟨S,b⟩
  simp only [oneBoundary,Set.mem_ofPred_eq,Nat.add_sub_cancel,previous_residuals]
  constructor
  · rintro ⟨⟨t,ht,rfl⟩,f,hf⟩
    rw [derivative_predecessor] at hf
    obtain ⟨s,hs,_⟩ := hf
    exact ⟨t,ht,s,hs,rfl⟩
  · rintro ⟨t,ht,s,hs,rfl⟩
    refine ⟨⟨t,ht,rfl⟩,encoded e (some s),?_⟩
    rw [derivative_predecessor]
    exact ⟨s,hs,rfl⟩

private theorem full_branching [Fintype A] (N : Nat) (e : Bool ↪ A) :
    FullBranching (relation e N true) (Nat.card A * N + 1) := by
  classical
  intro v hv hC b
  have hv' : v.length = Nat.card A * N := by omega
  obtain ⟨t,ht,rfl⟩ := (previous_prefix_complete e hv').mp hC
  obtain ⟨s,hs⟩ := Option.ne_none_iff_exists'.mp (ht.2 rfl b)
  exact ⟨encoded e (some s),t,ht,b,s,hs,by simp [List.append_assoc]⟩


private theorem boundary_finite [Finite A] (C : Set (List A)) (k : Nat) :
    (oneBoundary C k).Finite := by
  classical
  exact ((residual_finite C (k - 1)).prod (Set.finite_univ : (Set.univ : Set A).Finite)).subset
    (fun _ hz => ⟨hz.1,Set.mem_univ _⟩)
private theorem fixed_finite [Finite A] (C : Set (List A)) (k : Nat) (E : Set (List A)) (b : A) :
    (fixedFiber C k E b).Finite :=
  (residual_finite C (k - 1)).subset (fun _ h => h.1)
private theorem current_finite [Finite A] (C : Set (List A)) (k : Nat) (E : Set (List A)) :
    (currentFiber C k E).Finite := (boundary_finite C k).subset (fun _ h => h.1)

private theorem current_fiber_card [Fintype A] (C : Set (List A)) (k : Nat)
    (E : Set (List A)) (hE : E.Nonempty) :
    Nat.card (currentFiber C k E) = ∑ b : A, Nat.card (fixedFiber C k E b) := by
  classical
  let (b : A) : Finite (fixedFiber C k E b) := (fixed_finite C k E b).to_subtype
  let e : currentFiber C k E ≃ Σ b : A, fixedFiber C k E b := {
    toFun := fun z => ⟨z.val.2,⟨z.val.1,z.property.1.1,z.property.2⟩⟩
    invFun := fun z => ⟨(z.2.val,z.1),⟨z.2.property.1,by
      change (derivative z.2.val z.1).Nonempty
      rw [z.2.property.2]; exact hE⟩,z.2.property.2⟩
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨b,S⟩; rfl }
  rw [Nat.card_congr e,Nat.card_sigma]

private def fill {N : Nat} {full : Bool} (b : A) (s : Fin N)
    (r : Remaining A b → SharpBinaryOneRecut.Spare N full) : A → Option (Fin N) :=
  by
    classical
    exact fun a => if h : a = b then some s else (r ⟨a,h⟩).val
private theorem fill_admissible {N : Nat} {full : Bool} (b : A) (s : Fin N)
    (r : Remaining A b → SharpBinaryOneRecut.Spare N full) : Admissible full (fill b s r) := by
  classical
  refine ⟨⟨b,s,by simp [fill]⟩,?_⟩
  intro hf a
  by_cases ha : a = b
  · simp [fill,ha]
  · simpa [fill,ha] using (r ⟨a,ha⟩).property hf

private def boundary_equiv [Fintype A] {N : Nat} (full : Bool) (e : Bool ↪ A) :
    (Fin N × (Σ b : A, Remaining A b → SharpBinaryOneRecut.Spare N full)) ≃
      oneBoundary (relation e N full) (Nat.card A * N + 1) := by
  classical
  let f : (Fin N × (Σ b : A, Remaining A b → SharpBinaryOneRecut.Spare N full)) →
      oneBoundary (relation e N full) (Nat.card A * N + 1) :=
    fun z => ⟨(predecessor e (fill z.2.1 z.1 z.2.2),z.2.1),by
      rw [actual_boundary]
      exact ⟨fill z.2.1 z.1 z.2.2,fill_admissible _ _ _,z.1,by simp [fill],rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨s,b,r⟩ ⟨u,c,v⟩ he
    have hb : b = c := congrArg (fun z => z.val.2) he
    subst c
    have ht := predecessor_injective N e (congrArg (fun z => z.val.1) he)
    have hs : s = u := Option.some.inj (by simpa [fill] using congrFun ht b)
    subst u
    have hr : r = v := by
      funext a
      apply Subtype.ext
      simpa [fill,a.property] using congrFun ht a.val
    subst v
    rfl
  · intro z
    have hz := (Set.ext_iff.mp (actual_boundary N full e) z.val).mp z.property
    obtain ⟨t,ht,s,hs,he⟩ := hz
    let r : Remaining A z.val.2 → SharpBinaryOneRecut.Spare N full :=
      fun a => ⟨t a.val,fun hf => ht.2 hf a.val⟩
    have hr : fill z.val.2 s r = t := by
      funext a
      by_cases ha : a = z.val.2
      · simpa [fill,ha] using hs.symm
      · simp [fill,ha,r]
    refine ⟨⟨s,z.val.2,r⟩,Subtype.ext ?_⟩
    change (predecessor e (fill z.val.2 s r),z.val.2) = z.val
    apply Prod.ext
    · rw [hr,← he]
    · rfl

private def fixed_fiber_equiv [Fintype A] {N : Nat} (full : Bool)
    (e : Bool ↪ A) (s : Fin N) (b : A) :
    (Remaining A b → SharpBinaryOneRecut.Spare N full) ≃
      fixedFiber (relation e N full) (Nat.card A * N + 1) {encoded e (some s)} b := by
  classical
  let f : (Remaining A b → SharpBinaryOneRecut.Spare N full) →
      fixedFiber (relation e N full) (Nat.card A * N + 1) {encoded e (some s)} b :=
    fun r => ⟨predecessor e (fill b s r),by
      constructor
      · rw [Nat.add_sub_cancel,previous_residuals]
        exact ⟨fill b s r,fill_admissible b s r,rfl⟩
      · rw [derivative_predecessor]
        simp [fill,payload]⟩
  apply Equiv.ofBijective f
  constructor
  · intro r u he
    have ht := predecessor_injective N e (congrArg Subtype.val he)
    funext a
    apply Subtype.ext
    have hh := congrFun ht a.val
    simpa [fill,a.property] using hh
  · intro S
    have hp := S.property.1
    rw [Nat.add_sub_cancel,previous_residuals] at hp
    obtain ⟨t,ht,he⟩ := hp
    have hb : t b = some s := by
      apply payload_injective N e
      have hh := S.property.2
      rw [← he,derivative_predecessor] at hh
      simpa [payload] using hh
    let r : Remaining A b → SharpBinaryOneRecut.Spare N full :=
      fun a => ⟨t a.val,fun hf => ht.2 hf a.val⟩
    have hr : fill b s r = t := by
      funext a
      by_cases ha : a = b
      · simpa [fill,ha] using hb.symm
      · simp [fill,ha,r]
    refine ⟨r,Subtype.ext ?_⟩
    change predecessor e (fill b s r) = S.val
    rw [hr,he]

private theorem attained_counts [Fintype A] (N : Nat) (full : Bool) (e : Bool ↪ A) :
    Nat.card (residualSet (relation e N full) (Nat.card A * N + 1)) = N ∧
    (∀ E ∈ residualSet (relation e N full) (Nat.card A * N + 1),
      (∀ b, Nat.card (fixedFiber (relation e N full) (Nat.card A * N + 1) E b) =
        (N + if full then 0 else 1) ^ (Nat.card A - 1)) ∧
      Nat.card (currentFiber (relation e N full) (Nat.card A * N + 1) E) =
        Nat.card A * (N + if full then 0 else 1) ^ (Nat.card A - 1)) ∧
    Nat.card (oneBoundary (relation e N full) (Nat.card A * N + 1)) =
      Nat.card A * N * (N + if full then 0 else 1) ^ (Nat.card A - 1) := by
  classical
  have width : Nat.card (residualSet (relation e N full) (Nat.card A * N + 1)) = N := by
    rw [current_residuals,Nat.card_range_of_injective]
    · simp
    · intro s t h
      exact Option.some.inj (encoded_injective N e (Set.singleton_injective h))
  have fibers : ∀ E ∈ residualSet (relation e N full) (Nat.card A * N + 1),
      (∀ b, Nat.card (fixedFiber (relation e N full) (Nat.card A * N + 1) E b) =
        (N + if full then 0 else 1) ^ (Nat.card A - 1)) ∧
      Nat.card (currentFiber (relation e N full) (Nat.card A * N + 1) E) =
        Nat.card A * (N + if full then 0 else 1) ^ (Nat.card A - 1) := by
    intro E hE
    have fixed : ∀ b, Nat.card (fixedFiber (relation e N full) (Nat.card A * N + 1) E b) =
        (N + if full then 0 else 1) ^ (Nat.card A - 1) := by
      intro b
      rw [current_residuals] at hE
      obtain ⟨s,rfl⟩ := hE
      rw [← Nat.card_congr (fixed_fiber_equiv full e s b),Nat.card_fun,
        SharpBinaryOneRecut.spare_card,remaining_card]
    refine ⟨fixed,?_⟩
    rw [current_fiber_card _ _ E (residual_nonempty hE)]
    simp_rw [fixed]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,← Nat.card_eq_fintype_card]
  refine ⟨width,fibers,?_⟩
  rw [← Nat.card_congr (boundary_equiv full e),Nat.card_prod,sigma_card,
    SharpBinaryOneRecut.spare_card,Nat.card_fin]
  ring


private theorem finite_carriers [Finite A] [Nonempty A] (n : Nat) (C : Set (List A))
    (hl : ∀ w ∈ C, w.length = n) (hc : C.Nonempty) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n) :
    FiniteCarriers C k := by
  classical
  refine ⟨(List.finite_length_eq A n).subset hl,?_,boundary_finite C k,?_,?_⟩
  · intro j
    refine ⟨(List.finite_length_eq A j).subset (fun _ h => h.1),residual_finite C j,?_⟩
    rintro S ⟨v,hv,_,rfl⟩
    apply (List.finite_length_eq A (n-j)).subset
    intro f hf
    have hh := hl (v ++ f) hf
    simp only [List.length_append] at hh
    change f.length = n-j
    omega
  · obtain ⟨e,_⟩ := strict_identification n C hl hc k hk hkn
    let := (boundary_finite C k).to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ e)
  · intro E
    exact ⟨current_finite C k E,fixed_finite C k E⟩

private theorem universal_bounds [Finite A] [Nonempty A] (hq : 2 ≤ Nat.card A)
    (n : Nat) (C : Set (List A)) (hl : ∀ w ∈ C, w.length = n) (hc : C.Nonempty)
    (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n) :
    FiniteCarriers C k ∧ 0 < Nat.card (residualSet C k) ∧
    StrictIdentification C k ∧
    (∀ z ∈ oneBoundary C k, forward z ∈ residualSet C k) ∧
    Bounds C k (Nat.card (residualSet C k)+1) ∧
    (FullBranching C k → FullBounds C k) := by
  classical
  have hfin := residual_finite C k
  let := hfin.fintype
  have hn : 0 < Nat.card (residualSet C k) := by
    obtain ⟨w,hw⟩ := hc
    have hR : residual C (w.take k) ∈ residualSet C k := by
      refine ⟨w.take k,?_,⟨w.drop k,by simpa using hw⟩,rfl⟩
      simp [List.length_take,hl w hw,Nat.min_eq_left hkn]
    exact Nat.card_pos_iff.mpr ⟨⟨⟨_,hR⟩⟩,inferInstance⟩
  refine ⟨finite_carriers n C hl hc k hk hkn,hn,
    strict_identification n C hl hc k hk hkn,
    fun z hz => derivative_member hk hz.1 z.2 hz.2,?_,?_⟩
  · have hempty : (∅ : Set (List A)) ∉ residualSet C k := by
      intro h; exact (residual_nonempty h).ne_empty rfl
    have hB := hfin.insert (∅ : Set (List A))
    let := hB.fintype
    have hcard : Nat.card (insert (∅ : Set (List A)) (residualSet C k) : Set (Set (List A))) =
        Nat.card (residualSet C k)+1 := by
      rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Set.card_insert _ hempty]
    rw [← hcard]
    apply bounds_with n C hl k hk hkn _ hB
    intro S hS b
    by_cases he : derivative S b = ∅
    · exact Or.inl he
    · exact Or.inr (derivative_member hk hS b (Set.nonempty_iff_ne_empty.mpr he))
  · intro hb
    have hbound := bounds_with n C hl k hk hkn _ hfin (by
      rintro S ⟨v,hv,hvC,rfl⟩ b
      refine ⟨v ++ [b],?_,hb v hv hvC b,shift C v b⟩
      simp only [List.length_append,List.length_singleton]; omega)
    refine ⟨hbound.1,?_⟩
    have hp : Nat.card (residualSet C k) ^ Nat.card A =
        Nat.card (residualSet C k) * Nat.card (residualSet C k) ^ (Nat.card A - 1) := by
      conv_lhs => rw [show Nat.card A = (Nat.card A - 1)+1 by omega]
      rw [pow_succ]; ring
    simpa only [hp,Nat.mul_assoc] using hbound.2

private theorem attainment [Finite A] (hq : 2 ≤ Nat.card A) (N : Nat) (hN : 1 ≤ N)
    (full : Bool) : Attains (A := A) N full := by
  classical
  let := Fintype.ofFinite A
  obtain ⟨e⟩ : Nonempty (Bool ↪ A) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_bool,Nat.card_eq_fintype_card] using hq)
  let s : Fin N := ⟨0,by omega⟩
  let t : A → Option (Fin N) := fun _ => some s
  have ht : Admissible full t := ⟨⟨e false,s,rfl⟩,by simp [t]⟩
  have counts := attained_counts N full e
  refine ⟨Nat.card A * N + 1 + N,Nat.card A * N + 1,relation e N full,
    ⟨anchor e t ++ e false :: encoded e (some s),t,ht,e false,s,rfl,rfl⟩,
    ?_,by omega,by omega,?_,counts.1,?_,?_⟩
  · rintro w ⟨u,_,b,i,_,rfl⟩
    simp [anchor_length,encoded_length]
    omega
  · intro hf; subst full; exact full_branching N e
  · cases full <;> simpa using counts.2.1
  · have hp : N ^ Nat.card A = N * N ^ (Nat.card A - 1) := by
      conv_lhs => rw [show Nat.card A = (Nat.card A - 1)+1 by omega]
      rw [pow_succ]; ring
    cases full <;> simpa only [Bool.false_eq_true,ite_false,ite_true,
      Nat.add_zero,hp,Nat.mul_assoc] using counts.2.2

/-- Actual one-credit fibers have sharp finite-alphabet bounds, attained simultaneously
over the same alphabet at every prescribed positive current width. -/
theorem sharp_finite_alphabet_one_recut :
    ∀ (A : Type) [Finite A], 2 ≤ Nat.card A →
    (∀ (n : Nat) (C : Set (List A)), (∀ w ∈ C, w.length = n) → C.Nonempty →
      ∀ k : Nat, 1 ≤ k → k ≤ n →
      FiniteCarriers C k ∧ 0 < Nat.card (residualSet C k) ∧
      StrictIdentification C k ∧
      (∀ z ∈ oneBoundary C k, forward z ∈ residualSet C k) ∧
      Bounds C k (Nat.card (residualSet C k)+1) ∧
      (FullBranching C k → FullBounds C k)) ∧
    (∀ N : Nat, 1 ≤ N → Attains (A := A) N false ∧ Attains (A := A) N true) := by
  classical
  intro A _ hq
  let := Fintype.ofFinite A
  have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [← Nat.card_eq_fintype_card] using (show 1 < Nat.card A by omega))
  exact ⟨universal_bounds hq,fun N hN => ⟨attainment hq N hN false,attainment hq N hN true⟩⟩

#print axioms sharp_finite_alphabet_one_recut
end D5.S3.ObserverMemory.SharpFiniteAlphabetOneRecut
