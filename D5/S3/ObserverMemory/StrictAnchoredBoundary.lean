/- GID: D5/S3/ObserverMemory/StrictAnchoredBoundary
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/StrictAnchoredBoundary
   mirror-E: none(waiver:finite-state-capacity-without-numeric-experiment)
   anchors: []
   utility: none
   digest: Supplied append and credit-limited deletion runs identify the exact anchored residual boundary on its actual image. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.ObserverMemory.StrictAnchoredBoundary
open D5.S0.Automata.TypedPartialDFAOOverBase
variable {A : Type}
inductive Action (A : Type) where
  | append : A → Action A
  | delete : A → Action A
  deriving DecidableEq

def residual (C : Set (List A)) (v : List A) : Set (List A) := {f | v ++ f ∈ C}
def actual (C : Set (List A)) (s : List A × List A) : Prop :=
  ∃ f, (s.1 ++ s.2) ++ f ∈ C
def publicType (s : List A × List A) : Nat × Nat :=
  (s.1.length + s.2.length, s.2.length)
def boundary (C : Set (List A)) (s : List A × List A) : Set (List A) × List A :=
  (residual C s.1, s.2)
noncomputable def step (n : Nat) (C : Set (List A))
    (s : List A × List A) : Action A → Option (List A × List A)
  | .append a => by
    classical
    exact if s.1.length + s.2.length < n ∧ actual C (s.1, s.2 ++ [a]) then
      match s.2 with
      | [] => some (s.1 ++ [a], [])
      | c :: w => some (s.1 ++ [c], w ++ [a])
    else none
  | .delete a => by
    classical
    exact match s.2.reverse with
    | [] => none
    | b :: w => if a = b then some (s.1, w.reverse) else none

def legal (n : Nat) (C : Set (List A)) (s : List A × List A) : Set (List (Action A)) :=
  {w | (runTransition (step n C) s w).isSome = true}
noncomputable def boundaryStep (n : Nat) (p : Nat × Nat)
    (b : Set (List A) × List A) : Action A →
    Option ((Nat × Nat) × (Set (List A) × List A))
  | .append a => by
    classical
    exact if p.1 < n ∧ (∃ f, (b.2 ++ [a]) ++ f ∈ b.1) then
      match b.2 with
      | [] => some ((p.1 + 1, p.2), ({f | a :: f ∈ b.1}, []))
      | c :: w => some ((p.1 + 1, p.2), ({f | c :: f ∈ b.1}, w ++ [a]))
    else none
  | .delete a => by
    classical
    exact match b.2.reverse with
    | [] => none
    | c :: w => if a = c then some ((p.1 - 1, p.2 - 1), (b.1, w.reverse)) else none

abbrev typedState (C : Set (List A)) (p : Nat × Nat) :=
  {s : List A × List A // publicType s = p ∧ actual C s}
def image (C : Set (List A)) (p : Nat × Nat) : Set (Set (List A) × List A) :=
  Set.range (fun s : typedState C p => boundary C s.val)
def residualSet (C : Set (List A)) (m : Nat) : Set (Set (List A)) :=
  {S | ∃ v : List A, v.length = m ∧ (∃ f, v ++ f ∈ C) ∧ residual C v = S}
def pref (S : Set (List A)) (d : Nat) : Set (List A) :=
  {t | t.length = d ∧ ∃ f, t ++ f ∈ S}
def Exact {X : Type} (n : Nat) (C : Set (List A)) (a : List A × List A → X) : Prop :=
  ∀ s s' i, actual C s → actual C s' → publicType s = publicType s' → a s = a s' →
    Option.map (fun r => (publicType r, a r)) (step n C s i) =
      Option.map (fun r => (publicType r, a r)) (step n C s' i)

/-- For a finite fixed-length relation, actual supplied actions have the anchored
residual kernel, strict boundary updates, joint image count, and unique onto
factor of minimum conditional cardinality. -/
theorem strict_anchored_specialization [Finite A] [Nonempty A]
    (n : Nat) (C : Set (List A)) (fixedLength : ∀ f ∈ C, f.length = n)
    (_nonempty : C.Nonempty) (k d : Nat) (hd : d ≤ k) (hk : k ≤ n) :
    (∀ s a, actual C s →
      Option.map (fun r => (publicType r, boundary C r)) (step n C s a) =
        boundaryStep n (publicType s) (boundary C s) a) ∧
    (∀ s s', actual C s → actual C s' → publicType s = publicType s' →
      (legal n C s = legal n C s' ↔ boundary C s = boundary C s')) ∧
    image C (k,d) = {b | b.1 ∈ residualSet C (k-d) ∧ b.2 ∈ pref b.1 d} ∧
    (∃ inst : Fintype (residualSet C (k-d)), letI := inst;
      Nat.card (image C (k,d)) = ∑ S : residualSet C (k-d), Nat.card (pref S.val d)) ∧
    (∀ (X : Type) (a : List A × List A → X), Exact n C a →
      ∃! factor : Set.range (fun s : typedState C (k,d) => a s.val) → image C (k,d),
        (Set.rangeFactorization (fun s : typedState C (k,d) => boundary C s.val) =
          factor ∘ Set.rangeFactorization (fun s : typedState C (k,d) => a s.val)) ∧
        Function.Surjective factor ∧
        Nat.card (image C (k,d)) ≤ Nat.card (Set.range (fun s : typedState C (k,d) => a s.val))) := by
  classical
  have actualPrefix : ∀ v t : List A, (∃ f, (v ++ t) ++ f ∈ C) → ∃ f, v ++ f ∈ C := by
    rintro v t ⟨f, hf⟩
    exact ⟨t ++ f, by simpa [List.append_assoc] using hf⟩
  have bound : ∀ v : List A, (∃ f, v ++ f ∈ C) → v.length ≤ n := by
    rintro v ⟨f, hf⟩
    have h := fixedLength _ hf
    simp only [List.length_append] at h
    omega
  have shift : ∀ (v : List A) (a : A),
      residual C (v ++ [a]) = {f | a :: f ∈ residual C v} := by
    intros v a
    ext f
    simp [residual, List.append_assoc]
  have projected : ∀ s a, actual C s →
      Option.map (fun r => (publicType r, boundary C r)) (step n C s a) =
        boundaryStep n (publicType s) (boundary C s) a := by
    rintro ⟨v,t⟩ a hs
    cases a with
    | append a =>
      have hg : actual C (v, t ++ [a]) ↔
          ∃ f, (t ++ [a]) ++ f ∈ residual C v := by
        simp [actual, residual, List.append_assoc]
      cases t with
      | nil => simp [step, boundaryStep, publicType, boundary, shift, actual, residual, List.append_assoc]
      | cons c w =>
        simp [step, boundaryStep, publicType, boundary, shift, actual, residual, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
    | delete a =>
      cases hr : t.reverse with
      | nil => simp [step, boundaryStep, boundary, hr]
      | cons b w =>
        have ht : t = w.reverse ++ [b] := by
          have h := congrArg List.reverse hr
          simpa using h
        subst t
        simp [step, boundaryStep, publicType, boundary, Nat.add_assoc]
  have preserves : ∀ s a r, actual C s → step n C s a = some r → actual C r := by
    rintro ⟨v,t⟩ a r hs hr
    cases a with
    | append a =>
      simp only [step, Prod.fst, Prod.snd] at hr
      split_ifs at hr with h
      · cases t with
        | nil =>
          simp only at hr
          cases hr
          simpa [actual] using h.2
        | cons c w =>
          simp only at hr
          cases hr
          simpa [actual, List.append_assoc] using h.2
    | delete a =>
      simp only [step, Prod.fst, Prod.snd] at hr
      cases ht : t.reverse with
      | nil => simp [ht] at hr
      | cons b w =>
        simp only [ht] at hr
        split_ifs at hr with hab
        · cases hr
          have ht' : t = w.reverse ++ [b] := by
            have h := congrArg List.reverse ht
            simpa using h
          rcases hs with ⟨f,hf⟩
          refine ⟨b :: f, ?_⟩
          simpa [ht', List.append_assoc] using hf
  have forward : ∀ w s s', actual C s → actual C s' →
      publicType s = publicType s' → boundary C s = boundary C s' →
      (runTransition (step n C) s w).isSome =
        (runTransition (step n C) s' w).isSome := by
    intro w
    induction w with
    | nil => intros; rfl
    | cons a w ih =>
      intro s s' hs hs' hp hb
      have h : Option.map (fun r => (publicType r, boundary C r)) (step n C s a) =
          Option.map (fun r => (publicType r, boundary C r)) (step n C s' a) := by
        rw [projected s a hs, projected s' a hs', hp, hb]
      cases h1 : step n C s a with
      | none =>
        cases h2 : step n C s' a with
        | none => simp [runTransition, h1, h2]
        | some r' => simp [h1,h2] at h
      | some r =>
        cases h2 : step n C s' a with
        | none => simp [h1,h2] at h
        | some r' =>
          have he : publicType r = publicType r' ∧ boundary C r = boundary C r' := by
            simpa [h1,h2, Prod.mk.injEq] using h
          simp only [runTransition,h1,h2]
          exact ih r r' (preserves s a r hs h1) (preserves s' a r' hs' h2) he.1 he.2
  have deletes : ∀ z t v : List A, z.length = t.length →
      runTransition (step n C) (v,t) (z.reverse.map Action.delete) =
        if z = t then some (v,[]) else none := by
    intro z
    induction z using List.reverseRecOn with
    | nil =>
      intro t v ht
      have : t = [] := List.length_eq_zero_iff.mp (by simpa using ht.symm)
      subst t
      simp [runTransition]
    | append_singleton z a ih =>
      intro t v ht
      induction t using List.reverseRecOn with
      | nil => simp at ht
      | append_singleton t b _ =>
        have hlen : z.length = t.length := by simpa using ht
        by_cases hab : a = b
        · subst b
          simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
            List.map_cons, runTransition, step, List.reverse_reverse, if_pos rfl]
          simpa only [List.append_cancel_right_eq, ite_true] using ih t v hlen
        · have hne : z ++ [a] ≠ t ++ [b] := by
            intro h
            have h' := List.append_inj h hlen
            exact hab (by simpa using h'.2)
          simp [List.reverse_append, List.map_append, runTransition, step, hab, hne]
  have appends : ∀ f v : List A, (∃ g, v ++ g ∈ C) →
      runTransition (step n C) (v,[]) (f.map Action.append) =
        if (∃ g, (v ++ f) ++ g ∈ C) then some (v ++ f,[]) else none := by
    intro f
    induction f with
    | nil => intro v hv; simp [runTransition,hv]
    | cons a f ih =>
      intro v hv
      have hguard : (∃ g, (v ++ (a :: f)) ++ g ∈ C) →
          v.length < n ∧ actual C (v,[a]) := by
        rintro ⟨g,hg⟩
        constructor
        · have h := fixedLength _ hg
          simp only [List.length_append,List.length_cons] at h
          omega
        · exact ⟨f ++ g, by simpa [List.append_assoc] using hg⟩
      by_cases hg : v.length < n ∧ actual C (v,[a])
      · have hn : ∃ g, (v ++ [a]) ++ g ∈ C := by simpa [actual] using hg.2
        simpa [runTransition, step, hg, List.append_assoc] using ih (v ++ [a]) hn
      · have hn : ¬ ∃ g, (v ++ (a :: f)) ++ g ∈ C := fun h => hg (hguard h)
        simp only [List.map_cons,runTransition,step,Prod.fst,Prod.snd,List.length_nil,Nat.add_zero,List.nil_append,if_neg hg, if_neg hn]
  have full : ∀ v f : List A, v.length + f.length = n →
      ((∃ g, (v ++ f) ++ g ∈ C) ↔ v ++ f ∈ C) := by
    intro v f hlen
    constructor
    · rintro ⟨g,hg⟩
      have h := fixedLength _ hg
      simp only [List.length_append] at h
      have hz : g.length = 0 := by omega
      have he := List.length_eq_zero_iff.mp hz
      subst g
      simpa using hg
    · intro h; exact ⟨[],by simpa using h⟩
  have kernel : (∀ s s', actual C s → actual C s' → publicType s = publicType s' →
      (legal n C s = legal n C s' ↔ boundary C s = boundary C s')) := by
    rintro ⟨v,t⟩ ⟨v',t'⟩ hs hs' hp
    constructor
    · intro hlang
      have hlen : t.length = t'.length := congrArg Prod.snd hp
      have ht : t = t' := by
        have h : (t.reverse.map Action.delete) ∈ legal n C (v,t) := by
          change (runTransition (step n C) (v,t) (t.reverse.map Action.delete)).isSome = true
          rw [deletes t t v rfl]
          simp
        rw [hlang] at h
        have hrun := deletes t t' v' hlen
        by_contra hne
        change (runTransition (step n C) (v',t') (t.reverse.map Action.delete)).isSome = true at h
        rw [hrun, if_neg hne] at h
        simp at h
      subst t'
      have hvlen : v.length = v'.length := by
        have h := congrArg Prod.fst hp
        simp [publicType] at h
        omega
      have hv : ∃ f, v ++ f ∈ C := actualPrefix v t hs
      have hv' : ∃ f, v' ++ f ∈ C := actualPrefix v' t hs'
      apply Prod.ext
      · ext f
        change v ++ f ∈ C ↔ v' ++ f ∈ C
        by_cases hlen : v.length + f.length = n
        · have combine : ∀ x : List A, x.length = v.length → (∃ g, x ++ g ∈ C) →
              runTransition (step n C) (x,t)
                (t.reverse.map Action.delete ++ f.map Action.append) =
                  if x ++ f ∈ C then some (x ++ f,[]) else none := by
            intro x hxv hx
            have hc := PartialDFA.evalFrom_append
              {start := (x,t), step := step n C} (x,t)
              (t.reverse.map Action.delete) (f.map Action.append)
            simp only [PartialDFA.evalFrom] at hc
            rw [hc, deletes t t x rfl]
            simp only [ite_true, Option.bind_some]
            rw [appends f x hx]
            have hxlen : x.length + f.length = n := by omega
            rw [full x f hxlen]
          have h1 := combine v rfl hv
          have h2 := combine v' hvlen.symm hv'
          have he := Set.ext_iff.mp hlang
            (t.reverse.map Action.delete ++ f.map Action.append)
          change ((runTransition (step n C) (v,t) _).isSome = true) ↔
            ((runTransition (step n C) (v',t) _).isSome = true) at he
          rw [h1,h2] at he
          simpa only [Option.isSome_ite, Option.isSome_some, Option.isSome_none,
            Bool.if_true_right, Bool.false_eq_true, ite_true, ite_false] using he
        · constructor <;> intro hf
          · have h := fixedLength _ hf
            simp only [List.length_append] at h
            exact (hlen h).elim
          · have h := fixedLength _ hf
            simp only [List.length_append] at h
            exact (hlen (by omega)).elim
      · rfl
    · intro hb
      ext w
      change _ = true ↔ _ = true
      rw [forward w (v,t) (v',t') hs hs' hp hb]
  have core := And.intro projected kernel
  have im : image C (k,d) = {b | b.1 ∈ residualSet C (k-d) ∧ b.2 ∈ pref b.1 d} := by
    ext b
    constructor
    · rintro ⟨s,rfl⟩
      rcases s with ⟨⟨v,t⟩,hp,hs⟩
      have hlen : t.length = d := congrArg Prod.snd hp
      have hvlen : v.length = k-d := by
        have h := congrArg Prod.fst hp
        simp [publicType] at h
        omega
      rcases hs with ⟨f,hf⟩
      refine ⟨⟨v,hvlen,⟨t ++ f,?_⟩,rfl⟩,hlen, f, ?_⟩ <;>
        simpa [actual,boundary,residual,List.append_assoc] using hf
    · rintro ⟨⟨v,hvlen,hv,he⟩,htlen,f,hf⟩
      refine ⟨⟨(v,b.2),?_,?_⟩,?_⟩
      · apply Prod.ext <;> simp only [publicType,Prod.fst,Prod.snd]
        · omega
        · exact htlen
      · refine ⟨f,?_⟩
        rw [← he] at hf
        simpa [residual,List.append_assoc] using hf
      · exact Prod.ext he rfl
  have fr : (residualSet C (k-d)).Finite := by
    apply ((List.finite_length_eq A (k-d)).image (residual C)).subset
    rintro S ⟨v,hv,_,rfl⟩
    exact ⟨v,hv,rfl⟩
  letI : Finite (residualSet C (k-d)) := fr.to_subtype
  letI : Fintype (residualSet C (k-d)) := Fintype.ofFinite _
  have fp : ∀ S : residualSet C (k-d), (pref S.val d).Finite := by
    intro S
    exact (List.finite_length_eq A d).subset (fun t ht => ht.1)
  letI (S : residualSet C (k-d)) : Finite (pref S.val d) := (fp S).to_subtype
  have him := Set.ext_iff.mp im
  have eqv : image C (k,d) ≃ Σ S : residualSet C (k-d), pref S.val d := {
    toFun := fun b => ⟨⟨b.val.1, ((him b.val).mp b.property).1⟩, ⟨b.val.2,((him b.val).mp b.property).2⟩⟩
    invFun := fun b => ⟨(b.1.val,b.2.val), (him (b.1.val,b.2.val)).mpr ⟨b.1.property,b.2.property⟩⟩
    left_inv := by intro b; rfl
    right_inv := by intro b; rfl }
  have ft : Finite (typedState C (k,d)) := by
    letI : Finite {v : List A // v.length = k} := (List.finite_length_eq A k).to_subtype
    let encode : typedState C (k,d) → {v : List A // v.length = k} :=
      fun s => ⟨s.val.1 ++ s.val.2, by
        have h := congrArg Prod.fst s.property.1
        simpa [publicType] using h⟩
    apply Finite.of_injective encode
    intro s s' he
    apply Subtype.ext
    have ht : s.val.2.length = s'.val.2.length :=
      (congrArg Prod.snd s.property.1).trans (congrArg Prod.snd s'.property.1).symm
    have hv : s.val.1.length = s'.val.1.length := by
      have h : s.val.1 ++ s.val.2 = s'.val.1 ++ s'.val.2 := congrArg Subtype.val he
      have hlen := congrArg List.length h
      simp only [List.length_append] at hlen
      omega
    have h := List.append_inj (congrArg Subtype.val he) hv
    exact Prod.ext h.1 h.2
  letI : Finite (typedState C (k,d)) := ft
  refine ⟨core.1,core.2,im,⟨inferInstance,?_⟩,?_⟩
  · rw [Nat.card_congr eqv, Nat.card_sigma]
  · intro X a ha
    have preservation : ∀ w s s', actual C s → actual C s' →
        publicType s = publicType s' → a s = a s' →
        (runTransition (step n C) s w).isSome = (runTransition (step n C) s' w).isSome := by
      intro w
      induction w with
      | nil => intros; rfl
      | cons i w ih =>
        intro s s' hs hs' hp he
        have h := ha s s' i hs hs' hp he
        cases h1 : step n C s i with
        | none =>
          cases h2 : step n C s' i with
          | none => simp [runTransition,h1,h2]
          | some r' => simp [h1,h2] at h
        | some r =>
          cases h2 : step n C s' i with
          | none => simp [h1,h2] at h
          | some r' =>
            have he' : publicType r = publicType r' ∧ a r = a r' := by
              simpa [h1,h2,Prod.mk.injEq] using h
            simp only [runTransition,h1,h2]
            exact ih r r' (preserves s i r hs h1) (preserves s' i r' hs' h2) he'.1 he'.2
    have hker : Setoid.ker (fun s : typedState C (k,d) => a s.val) ≤
        Setoid.ker (fun s : typedState C (k,d) => boundary C s.val) := by
      intro s s' he
      apply (core.2 s.val s'.val s.property.2 s'.property.2
        (s.property.1.trans s'.property.1.symm)).mp
      ext w
      change _ = true ↔ _ = true
      rw [preservation w s.val s'.val s.property.2 s'.property.2
        (s.property.1.trans s'.property.1.symm) he]
    obtain ⟨factor,hfactor,hunique⟩ :=
      (D5.S3.ConceptDynamics.RefinementFactorization.RealizedImageKernelFactorization.realized_image_unique_factorization_iff_reverse_kernel
        (fun s : typedState C (k,d) => boundary C s.val)
        (fun s : typedState C (k,d) => a s.val)).mpr hker
    have onto : Function.Surjective factor := by
      intro b
      obtain ⟨s,hs⟩ := Set.rangeFactorization_surjective b
      refine ⟨Set.rangeFactorization (fun s : typedState C (k,d) => a s.val) s,?_⟩
      exact (congrFun hfactor s).symm.trans hs
    refine ⟨factor,⟨hfactor,onto,?_⟩,?_⟩
    · exact Nat.card_le_card_of_surjective factor onto
    · intro other hother
      exact hunique other hother.1

#print axioms strict_anchored_specialization
end D5.S3.ObserverMemory.StrictAnchoredBoundary
