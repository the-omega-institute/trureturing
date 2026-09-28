/- GID: D5/S3/Observer/Separation/SurjectiveColumnSharpWidth
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/SurjectiveColumnSharpWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A single surjective column gives the sharp coefficient-one selector width bound. -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Observer.Separation.SurjectiveColumnSharpWidth

abbrev Coord (r : ℕ) := Fin r ⊕ (Bool ⊕ Fin r)

def Alphabet {r : ℕ} (A B : Type) (D : Fin r → Type) : Coord r → Type
  | .inl _ => Bool
  | .inr (.inl false) => A
  | .inr (.inl true) => B
  | .inr (.inr i) => D i

def piPosition {r : ℕ} (h : ℕ) : Coord r → ℕ
  | .inl i => if i.val < h then i.val else i.val + 1
  | .inr (.inl false) => h
  | .inr (.inl true) => r + 1
  | .inr (.inr i) => r + 2 + i.val

def rhoPosition {r : ℕ} : Coord r → ℕ
  | .inl i => 2 + 2 * i.val
  | .inr (.inl false) => 0
  | .inr (.inl true) => 1
  | .inr (.inr i) => 3 + 2 * i.val

noncomputable def response {I : Type} (X : I → Type) {O : Type}
    (F : (∀ i, X i) → O) (p : I → Prop) :
    (∀ i : {i // p i}, X i.val) → (∀ i : {i // ¬p i}, X i.val) → O := by
  classical
  exact fun x y => F ((Equiv.piEquivPiSubtypeProd p X).symm (x,y))

noncomputable def capacity {I : Type} (X : I → Type) {O : Type}
    (F : (∀ i, X i) → O) (p : I → Prop) : ℕ :=
  Nat.card (Set.range (response X F p))

noncomputable def width {r : ℕ} (X : Coord r → Type) {O : Type}
    (F : (∀ i, X i) → O) (pos : Coord r → ℕ) : ℕ :=
  Finset.univ.sup (fun k : Fin (2*r+3) => capacity X F (fun i => pos i < k.val))

def task {r : ℕ} {A B Z O : Type} {D : Fin r → Type}
    (ψ : A → B → Z) (G : (Fin r → Bool) → Z → O)
    (x : ∀ i, Alphabet A B D i) : O :=
  G (fun i => x (.inl i)) (ψ (x (.inr (.inl false))) (x (.inr (.inl true))))

noncomputable def count {U V : Type} (f : U → V) : ℕ := Nat.card (Set.range f)

noncomputable def join {I : Type} (s : I → Prop)
    (p : {i // s i} → Bool) (w : {i // ¬s i} → Bool) : I → Bool := by
  classical
  exact (Equiv.piEquivPiSubtypeProd s (fun _ => Bool)).symm (p,w)

noncomputable def coreA {I A B Z O : Type} (ψ : A → B → Z)
    (G : (I → Bool) → Z → O) (s : I → Prop) :
    (({i // s i} → Bool) × A) → (({i // ¬s i} → Bool) × B) → O :=
  fun x y => G (join s x.1 y.1) (ψ x.2 y.2)

noncomputable def coreZ {I Z O : Type} (G : (I → Bool) → Z → O) (s : I → Prop) :
    (({i // s i} → Bool) × Z) → ({i // ¬s i} → Bool) → O :=
  fun x y => G (join s x.1 y) x.2

abbrev Table (I : Type) (m : ℕ) := (I → Bool) → ZMod m

noncomputable def zeroTask {I : Type} {m : ℕ} (t : I → Bool) (z : Table I m) : Bool := by
  classical
  exact decide (z t = 0)

def input {r : ℕ} {A B : Type} {D : Fin r → Type}
    (t : Fin r → Bool) (a : A) (b : B) (d : ∀ i, D i) : ∀ i, Alphabet A B D i
  | .inl i => t i
  | .inr (.inl false) => a
  | .inr (.inl true) => b
  | .inr (.inr i) => d i

noncomputable def coreBefore {I A B Z O : Type} (ψ : A → B → Z)
    (G : (I → Bool) → Z → O) (s : I → Prop) :
    ({i // s i} → Bool) → (({i // ¬s i} → Bool) × A × B) → O :=
  fun x y => G (join s x y.1) (ψ y.2.1 y.2.2)

def piCount (r h m k : ℕ) : ℕ :=
  if k ≤ h then 2^k else if k ≤ r+1 then 2^(k-1)*m^(2^(r-(k-1))) else 2

def rhoCount (r m k : ℕ) : ℕ :=
  if k=0 then 1 else if k=1 then m^(2^r) else 2^(2^(r-((k-1)/2)))

noncomputable def sharpCapacity {r : ℕ} (D : Fin r → Type) (m : ℕ)
    (pos : Coord r → ℕ) (k : ℕ) : ℕ :=
  capacity (Alphabet (Table (Fin r) m) (Table (Fin r) m) D)
    (task (fun a b : Table (Fin r) m => a+b) zeroTask) (fun c => pos c < k)

noncomputable def sharpWidth {r : ℕ} (D : Fin r → Type) (m : ℕ)
    (pos : Coord r → ℕ) : ℕ :=
  width (Alphabet (Table (Fin r) m) (Table (Fin r) m) D)
    (task (fun a b : Table (Fin r) m => a+b) zeroTask) pos

/-- Actual labelled-complement response widths, all raw layers, the sharp finite
addition-table family, its minimal uniform real exponent, and constant-task width. -/
theorem result {r : ℕ} (_hr : 1 ≤ r) (h : ℕ) (hh : h ≤ r)
    (D : Fin r → Type) [∀ i, Finite (D i)] [∀ i, Nonempty (D i)] :
    (∀ (A B Z O : Type) [Finite A] [Finite B] [Finite Z] [Finite O]
      [Nonempty A] [Nonempty B] [Nonempty O]
      (ψ : A → B → Z) (G : (Fin r → Bool) → Z → O) (b₀ : B),
      Function.Surjective (fun a => ψ a b₀) →
      width (Alphabet A B D) (task ψ G) rhoPosition ≤
        width (Alphabet A B D) (task ψ G) (piPosition h) ^ (2^h)) ∧
    (∀ m : ℕ, 2 ≤ m →
      (∀ k : Fin (2*r+3), sharpCapacity D m (piPosition h) k.val = piCount r h m k.val) ∧
      (∀ k : Fin (2*r+3), sharpCapacity D m rhoPosition k.val = rhoCount r m k.val) ∧
      sharpWidth D m (piPosition h) = 2^h*m^(2^(r-h)) ∧
      sharpWidth D m rhoPosition = m^(2^r)) ∧
    (∀ α C : ℝ, α < (2:ℝ)^h → 0<C → ∃ m : ℕ, 2 ≤ m ∧
      C * (sharpWidth D m (piPosition h) : ℝ)^α < (sharpWidth D m rhoPosition : ℝ)) ∧
    (∀ (A B Z O : Type) [Finite A] [Finite B] [Finite Z] [Finite O]
      [Nonempty A] [Nonempty B] (ψ : A → B → Z) (o : O),
      width (Alphabet A B D) (task ψ (fun _ _ => o)) (piPosition h) = 1 ∧
      width (Alphabet A B D) (task ψ (fun _ _ => o)) rhoPosition = 1 ∧
      ∀ C : ℝ,
        (width (Alphabet A B D) (task ψ (fun _ _ => o)) rhoPosition : ℝ) ≤
          C * (width (Alphabet A B D) (task ψ (fun _ _ => o)) (piPosition h) : ℝ)^(2^h : ℕ) →
        1 ≤ C) := by
  classical
  letI alphabetFinite {r : ℕ} {A B : Type} {D : Fin r → Type}
      [Finite A] [Finite B] [∀ i, Finite (D i)] (c : Coord r) : Finite (Alphabet A B D c) := by
    rcases c with i | (b | i)
    · exact inferInstanceAs (Finite Bool)
    · cases b
      · exact inferInstanceAs (Finite A)
      · exact inferInstanceAs (Finite B)
    · exact inferInstanceAs (Finite (D i))
  letI alphabetNonempty {r : ℕ} {A B : Type} {D : Fin r → Type}
      [Nonempty A] [Nonempty B] [∀ i, Nonempty (D i)] (c : Coord r) :
      Nonempty (Alphabet A B D c) := by
    rcases c with i | (b | i)
    · exact inferInstanceAs (Nonempty Bool)
    · cases b
      · exact inferInstanceAs (Nonempty A)
      · exact inferInstanceAs (Nonempty B)
    · exact inferInstanceAs (Nonempty (D i))
  have transport {U V Y Z O : Type} [Finite U] [Finite V] [Finite Y] [Finite Z] [Finite O]
      (f : U → Y → O) (g : V → Z → O) (a : U → V) (b : Y → Z)
      (ha : Function.Surjective a) (hb : Function.Surjective b)
      (hf : ∀ x y, f x y = g (a x) (b y)) : count f = count g := by
    classical
    let pull : (Z → O) → Y → O := fun v y => v (b y)
    have hi : Function.Injective pull := by
      intro v w he
      funext z
      obtain ⟨y,rfl⟩ := hb z
      exact congrFun he y
    have hr : Set.range f = pull '' Set.range g := by
      ext v
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨g (a x),⟨a x,rfl⟩, funext fun y => (hf x y).symm⟩
      · rintro ⟨_,⟨z,rfl⟩,rfl⟩
        obtain ⟨x,rfl⟩ := ha z
        exact ⟨x,funext fun y => hf x y⟩
    unfold count
    rw [hr,Nat.card_image_of_injective hi]
  have stageA {r : ℕ} {A B Z O : Type} {D : Fin r → Type}
      [Finite A] [Finite B] [Finite Z] [Finite O] [∀ i, Finite (D i)]
      [Nonempty A] [Nonempty B] [∀ i, Nonempty (D i)]
      (ψ : A → B → Z) (G : (Fin r → Bool) → Z → O)
      (p : Coord r → Prop) (ha : p (.inr (.inl false))) (hb : ¬p (.inr (.inl true))) :
      capacity (Alphabet A B D) (task ψ G) p = count (coreA ψ G (fun i => p (.inl i))) := by
    classical
    let s : Fin r → Prop := fun i => p (.inl i)
    let a₀ : A := Classical.choice inferInstance
    let b₀ : B := Classical.choice inferInstance
    let d₀ : ∀ i, D i := fun _ => Classical.choice inferInstance
    let pre (x : ∀ i : {i // p i}, Alphabet A B D i.val) : ({i // s i} → Bool) × A :=
      ((fun i => x ⟨.inl i.val,i.property⟩),x ⟨.inr (.inl false),ha⟩)
    let suf (y : ∀ i : {i // ¬p i}, Alphabet A B D i.val) : ({i // ¬s i} → Bool) × B :=
      ((fun i => y ⟨.inl i.val,i.property⟩),y ⟨.inr (.inl true),hb⟩)
    apply transport (response (Alphabet A B D) (task ψ G) p) (coreA ψ G s) pre suf
    · rintro ⟨t,a⟩
      refine ⟨(fun c => input (join s t (fun _ => false)) a b₀ d₀ c.val),?_⟩
      apply Prod.ext
      · funext i
        simp [pre,input,join,Equiv.piEquivPiSubtypeProd,i.property]
      · rfl
    · rintro ⟨w,b⟩
      refine ⟨(fun c => input (join s (fun _ => false) w) a₀ b d₀ c.val),?_⟩
      apply Prod.ext
      · funext i
        simp [suf,input,join,Equiv.piEquivPiSubtypeProd,i.property]
      · rfl
    · intro x y
      simp only [response,task,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,
        dif_pos ha,dif_neg hb,coreA,pre,suf,join]
      rfl
  have stageZ {r : ℕ} {A B Z O : Type} {D : Fin r → Type}
      [Finite A] [Finite B] [Finite Z] [Finite O] [∀ i, Finite (D i)]
      [Nonempty A] [Nonempty B] [∀ i, Nonempty (D i)]
      (ψ : A → B → Z) (G : (Fin r → Bool) → Z → O)
      (b₀ : B) (hcol : Function.Surjective (fun a => ψ a b₀))
      (p : Coord r → Prop) (ha : p (.inr (.inl false))) (hb : p (.inr (.inl true))) :
      capacity (Alphabet A B D) (task ψ G) p = count (coreZ G (fun i => p (.inl i))) := by
    classical
    let s : Fin r → Prop := fun i => p (.inl i)
    let a₀ : A := Classical.choice inferInstance
    let d₀ : ∀ i, D i := fun _ => Classical.choice inferInstance
    let pre (x : ∀ i : {i // p i}, Alphabet A B D i.val) : ({i // s i} → Bool) × Z :=
      ((fun i => x ⟨.inl i.val,i.property⟩),ψ (x ⟨.inr (.inl false),ha⟩) (x ⟨.inr (.inl true),hb⟩))
    let suf (y : ∀ i : {i // ¬p i}, Alphabet A B D i.val) : ({i // ¬s i} → Bool) :=
      fun i => y ⟨.inl i.val,i.property⟩
    apply transport (response (Alphabet A B D) (task ψ G) p) (coreZ G s) pre suf
    · rintro ⟨t,z⟩
      obtain ⟨a,ha'⟩ := hcol z
      refine ⟨(fun c => input (join s t (fun _ => false)) a b₀ d₀ c.val),?_⟩
      apply Prod.ext
      · funext i
        simp [pre,input,join,Equiv.piEquivPiSubtypeProd,i.property]
      · exact ha'
    · intro w
      refine ⟨(fun c => input (join s (fun _ => false) w) a₀ b₀ d₀ c.val),?_⟩
      funext i
      simp [suf,input,join,Equiv.piEquivPiSubtypeProd,i.property]
    · intro x y
      simp only [response,task,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,
        dif_pos ha,dif_pos hb,coreZ,pre,suf,join]
      rfl
  have stageBefore {r : ℕ} {A B Z O : Type} {D : Fin r → Type}
      [Finite A] [Finite B] [Finite Z] [Finite O] [∀ i, Finite (D i)]
      [Nonempty A] [Nonempty B] [∀ i, Nonempty (D i)]
      (ψ : A → B → Z) (G : (Fin r → Bool) → Z → O)
      (p : Coord r → Prop) (ha : ¬p (.inr (.inl false))) (hb : ¬p (.inr (.inl true))) :
      capacity (Alphabet A B D) (task ψ G) p = count (coreBefore ψ G (fun i => p (.inl i))) := by
    classical
    let s : Fin r → Prop := fun i => p (.inl i)
    let a₀ : A := Classical.choice inferInstance
    let b₀ : B := Classical.choice inferInstance
    let d₀ : ∀ i, D i := fun _ => Classical.choice inferInstance
    let pre (x : ∀ i : {i // p i}, Alphabet A B D i.val) : {i // s i} → Bool :=
      fun i => x ⟨.inl i.val,i.property⟩
    let suf (y : ∀ i : {i // ¬p i}, Alphabet A B D i.val) : ({i // ¬s i} → Bool) × A × B :=
      ((fun i => y ⟨.inl i.val,i.property⟩),y ⟨.inr (.inl false),ha⟩,y ⟨.inr (.inl true),hb⟩)
    apply transport (response (Alphabet A B D) (task ψ G) p) (coreBefore ψ G s) pre suf
    · intro t
      refine ⟨(fun c => input (join s t (fun _ => false)) a₀ b₀ d₀ c.val),?_⟩
      funext i
      simp [pre,input,join,Equiv.piEquivPiSubtypeProd,i.property]
    · rintro ⟨w,a,b⟩
      refine ⟨(fun c => input (join s (fun _ => false) w) a b d₀ c.val),?_⟩
      apply Prod.ext
      · funext i
        simp [suf,input,join,Equiv.piEquivPiSubtypeProd,i.property]
      · rfl
    · intro x y
      simp only [response,task,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,
        dif_neg ha,dif_neg hb,coreBefore,pre,suf,join]
      rfl
  have upper {r : ℕ} (h : ℕ) (hh : h ≤ r) {A B Z O : Type} {D : Fin r → Type}
      [Finite A] [Finite B] [Finite Z] [Finite O] [∀ i, Finite (D i)]
      [Nonempty A] [Nonempty B] [Nonempty O] [∀ i, Nonempty (D i)]
      (ψ : A → B → Z) (G : (Fin r → Bool) → Z → O)
      (b₀ : B) (hcol : Function.Surjective (fun a => ψ a b₀)) :
      width (Alphabet A B D) (task ψ G) rhoPosition ≤
        width (Alphabet A B D) (task ψ G) (piPosition h) ^ (2^h) := by
    classical
    have boundZ {I A B Z O : Type} [Finite I] [Finite A] [Finite B] [Finite Z] [Finite O]
        (ψ : A → B → Z) (G : (I → Bool) → Z → O)
        (b₀ : B) (hcol : Function.Surjective (fun a => ψ a b₀))
        (s e : I → Prop) (hse : ∀ i, s i → e i) :
        count (coreZ G s) ≤ (count (coreA ψ G e)) ^ (2 ^ Nat.card {i // e i}) := by
      classical
      let σ := Function.surjInv hcol
      have hσ (z : Z) : ψ (σ z) b₀ = z := Function.surjInv_eq hcol z
      let R := coreA ψ G e
      let H := coreZ G s
      let code : Set.range H → ({i // e i} → Bool) → Set.range R := fun f u =>
        let x := Classical.choose f.property
        ⟨R ((fun i => if hi : s i.val then x.1 ⟨i.val,hi⟩ else u i), σ x.2), ⟨_,rfl⟩⟩
      have hc : Function.Injective code := by
        intro f g he
        apply Subtype.ext
        funext y
        let u : {i // e i} → Bool := fun i => if hi : s i.val then false else y ⟨i.val,hi⟩
        let w : {i // ¬e i} → Bool := fun i => y ⟨i.val, fun hi => i.property (hse _ hi)⟩
        have hh := congrFun (congrArg Subtype.val (congrFun he u)) (w,b₀)
        have hj (x : ({i // s i} → Bool) × Z) :
            join e (fun i => if hi : s i.val then x.1 ⟨i.val,hi⟩ else u i) w =
              join s x.1 y := by
          funext i
          simp only [join, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk]
          by_cases hs : s i
          · simp [hs, hse _ hs]
          · by_cases he : e i <;> simp [hs, he, u, w]
        change G (join e _ w) (ψ (σ _) b₀) = G (join e _ w) (ψ (σ _) b₀) at hh
        rw [hj, hj, hσ, hσ] at hh
        change H (Classical.choose f.property) y = H (Classical.choose g.property) y at hh
        rwa [Classical.choose_spec f.property, Classical.choose_spec g.property] at hh
      have hcard := Nat.card_le_card_of_injective code hc
      simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_bool, count, H, R]
        using hcard
    have lateZ {I A B Z O : Type} [Finite I] [Finite A] [Finite B] [Finite Z] [Finite O]
        (ψ : A → B → Z) (G : (I → Bool) → Z → O)
        (b₀ : B) (hcol : Function.Surjective (fun a => ψ a b₀)) (s : I → Prop) :
        count (coreZ G s) ≤ count (coreA ψ G s) := by
      classical
      let σ := Function.surjInv hcol
      have hσ (z : Z) : ψ (σ z) b₀ = z := Function.surjInv_eq hcol z
      let R := coreA ψ G s
      let H := coreZ G s
      let code : Set.range H → Set.range R := fun f =>
        let x := Classical.choose f.property
        ⟨R (x.1, σ x.2), ⟨_,rfl⟩⟩
      have hc : Function.Injective code := by
        intro f g he
        apply Subtype.ext
        funext y
        have hh := congrFun (congrArg Subtype.val he) (y,b₀)
        change G (join s _ y) (ψ (σ _) b₀) = G (join s _ y) (ψ (σ _) b₀) at hh
        rw [hσ, hσ] at hh
        change H (Classical.choose f.property) y = H (Classical.choose g.property) y at hh
        rwa [Classical.choose_spec f.property, Classical.choose_spec g.property] at hh
      exact Nat.card_le_card_of_injective code hc
    have boundA {I A B Z O : Type} [Finite I] [Finite A] [Finite B] [Finite Z] [Finite O]
        (ψ : A → B → Z) (G : (I → Bool) → Z → O)
        (s e : I → Prop) (hse : ∀ i, s i → e i) :
        count (coreA ψ G s) ≤ (count (coreA ψ G e)) ^ (2 ^ Nat.card {i // e i}) := by
      classical
      let R := coreA ψ G e
      let H := coreA ψ G s
      let code : Set.range H → ({i // e i} → Bool) → Set.range R := fun f u =>
        let x := Classical.choose f.property
        ⟨R ((fun i => if hi : s i.val then x.1 ⟨i.val,hi⟩ else u i), x.2), ⟨_,rfl⟩⟩
      have hc : Function.Injective code := by
        intro f g he
        apply Subtype.ext
        funext y
        let u : {i // e i} → Bool := fun i => if hi : s i.val then false else y.1 ⟨i.val,hi⟩
        let w : {i // ¬e i} → Bool := fun i => y.1 ⟨i.val, fun hi => i.property (hse _ hi)⟩
        have hh := congrFun (congrArg Subtype.val (congrFun he u)) (w,y.2)
        have hj (x : ({i // s i} → Bool) × A) :
            join e (fun i => if hi : s i.val then x.1 ⟨i.val,hi⟩ else u i) w =
              join s x.1 y.1 := by
          funext i
          simp only [join, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk]
          by_cases hs : s i
          · simp [hs, hse _ hs]
          · by_cases he : e i <;> simp [hs, he, u, w]
        change G (join e _ w) (ψ _ y.2) = G (join e _ w) (ψ _ y.2) at hh
        rw [hj,hj] at hh
        change H (Classical.choose f.property) y = H (Classical.choose g.property) y at hh
        rwa [Classical.choose_spec f.property, Classical.choose_spec g.property] at hh
      have hcard := Nat.card_le_card_of_injective code hc
      simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_bool, count, H, R]
        using hcard
    let X := Alphabet A B D
    let F := @task r A B Z O D ψ G
    let W := width X F (piPosition h)
    let early : Fin r → Prop := fun i => i.val < h
    have hc : Nat.card {i : Fin r // early i} = h := by
      let eqv : Fin h ≃ {i : Fin r // early i} :=
        { toFun := fun i => ⟨⟨i.val,lt_of_lt_of_le i.isLt hh⟩,i.isLt⟩
          invFun := fun i => ⟨i.val.val,i.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      simpa using (Nat.card_congr eqv).symm
    have hlayer (j : ℕ) (hj : h ≤ j) (hjr : j ≤ r) :
        count (coreA ψ G (fun i : Fin r => i.val < j)) ≤ W := by
      let k : Fin (2*r+3) := ⟨j+1,by omega⟩
      have hs : (fun i : Fin r => piPosition h (.inl i) < k.val) = (fun i => i.val < j) := by
        funext i
        simp only [piPosition,k]
        split <;> apply propext <;> omega
      have heq := stageA ψ G (D := D) (fun c => piPosition h c < k.val)
        (by simp only [piPosition,k]; omega) (by simp only [piPosition,k]; omega)
      have heqc := congrArg (fun s : Fin r → Prop => count (coreA ψ G s)) hs
      rw [heqc] at heq
      rw [← heq]
      exact Finset.le_sup (s := Finset.univ) (f := fun k : Fin (2*r+3) =>
        capacity X F (fun c => piPosition h c < k.val)) (Finset.mem_univ k)
    have hk : count (coreA ψ G early) ≤ W := hlayer h le_rfl hh
    have hw : 1 ≤ W := by
      have hp : 0 < capacity X F (fun c => piPosition h c < 0) := by
        unfold capacity
        exact Nat.card_pos
      exact hp.trans_le (Finset.le_sup (s := Finset.univ) (f := fun k : Fin (2*r+3) =>
        capacity X F (fun c => piPosition h c < k.val)) (b := ⟨0,by omega⟩) (by simp))
    have hwp : W ≤ W ^ (2^h) := le_self_pow hw (by positivity)
    have hcount {U V : Type} [Finite U] [Finite V] (f : U → V) : count f ≤ Nat.card U := by
      exact Nat.card_le_card_of_surjective (fun u => (⟨f u,⟨u,rfl⟩⟩ : Set.range f))
        (by rintro ⟨_,u,rfl⟩; exact ⟨u,rfl⟩)
    apply Finset.sup_le
    intro k _
    by_cases hk0 : k.val = 0
    · have hs : (fun i : Fin r => rhoPosition (.inl i) < k.val) = (fun _ => False) := by
        simp only [hk0,Nat.not_lt_zero]
      have heq := stageBefore ψ G (D := D) (fun c => rhoPosition c < k.val)
        (by simp [rhoPosition,hk0]) (by simp [rhoPosition,hk0])
      rw [heq]
      rw [congrArg (fun s : Fin r → Prop => count (coreBefore ψ G s)) hs]
      have hb := hcount (coreBefore ψ G (fun _ : Fin r => False))
      have ht : Nat.card ({i : Fin r // False} → Bool) = 1 := by simp
      rw [ht] at hb
      exact hb.trans (hw.trans hwp)
    by_cases hk1 : k.val = 1
    · rw [stageA ψ G (D := D) (fun c => rhoPosition c < k.val)
        (by simp [rhoPosition,hk1]) (by simp [rhoPosition,hk1])]
      have hb := boundA ψ G (fun i : Fin r => rhoPosition (.inl i) < k.val) early
        (by intro i hi; simp [rhoPosition,hk1] at hi)
      rw [hc] at hb
      exact hb.trans (pow_le_pow_left' hk _)
    have hge : 2 ≤ k.val := by omega
    rw [stageZ ψ G (D := D) b₀ hcol (fun c => rhoPosition c < k.val)
        (by simp only [rhoPosition]; omega) (by simp only [rhoPosition]; omega)]
    let j := (k.val-1)/2
    have hjr : j ≤ r := by have := k.isLt; dsimp [j]; omega
    have hs : (fun i : Fin r => rhoPosition (.inl i) < k.val) = (fun i => i.val < j) := by
      funext i
      simp only [rhoPosition]
      apply propext
      dsimp [j]
      omega
    rw [congrArg (fun s : Fin r → Prop => count (coreZ G s)) hs]
    by_cases hj : j ≤ h
    · have hb := boundZ ψ G b₀ hcol (fun i : Fin r => i.val < j) early
        (by intro i hi; exact lt_of_lt_of_le hi hj)
      rw [hc] at hb
      exact hb.trans (pow_le_pow_left' hk _)
    · exact (lateZ ψ G b₀ hcol (fun i : Fin r => i.val < j)).trans
        ((hlayer j (by omega) hjr).trans hwp)
  have layers {r : ℕ} (h : ℕ) (hh : h ≤ r) (m : ℕ) (hm : 2 ≤ m)
      (D : Fin r → Type) [∀ i, Finite (D i)] [∀ i, Nonempty (D i)] :
      (∀ k : Fin (2*r+3), sharpCapacity D m (piPosition h) k.val = piCount r h m k.val) ∧
      (∀ k : Fin (2*r+3), sharpCapacity D m rhoPosition k.val = rhoCount r m k.val) := by
    classical
    let : NeZero m := ⟨by omega⟩
    let : Fact (1<m) := ⟨by omega⟩
    have countA {I : Type} [Finite I] (m : ℕ) (hm : 2 ≤ m) (s : I → Prop) :
        count (coreA (fun a b : Table I m => a+b) zeroTask s) =
          2 ^ Nat.card {i // s i} * m ^ (2 ^ Nat.card {i // ¬s i}) := by
      classical
      let : NeZero m := ⟨by omega⟩
      let : Fact (1 < m) := ⟨by omega⟩
      let P := {i // s i} → Bool
      let W := {i // ¬s i} → Bool
      let R := coreA (fun a b : Table I m => a+b) zeroTask s
      let Q : (P × (W → ZMod m)) → (W × Table I m) → Bool :=
        fun x y => decide (x.2 y.1 + y.2 (join s x.1 y.1) = 0)
      have hi : Function.Injective Q := by
        rintro ⟨p,v⟩ ⟨q,w⟩ he
        have hpq : p=q := by
          by_contra hne
          have hj : join s p (fun _ => false) ≠ join s q (fun _ => false) := by
            intro hh
            apply hne
            funext i
            have := congrFun hh i.val
            simpa [join, Equiv.piEquivPiSubtypeProd, i.property] using this
          let b : Table I m := fun t =>
            if t = join s p (fun _ => false) then -v (fun _ => false)
            else -w (fun _ => false) + 1
          have hh := congrFun he ((fun _ => false),b)
          have hrev := Ne.symm hj
          simp [Q,b,hrev] at hh
        subst q
        congr 1
        funext y
        have hh := congrFun he (y,fun _ => -v y)
        have hv : w y + -v y = 0 := by simpa [Q] using hh.symm
        exact (eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hv)).symm
      have hr : Set.range R = Set.range Q := by
        ext f
        constructor
        · rintro ⟨⟨p,a⟩,rfl⟩
          refine ⟨(p,fun w => a (join s p w)),rfl⟩
        · rintro ⟨⟨p,v⟩,rfl⟩
          refine ⟨(p,fun t => v (fun i => t i.val)),?_⟩
          funext y
          have hj : (fun i : {i // ¬s i} => join s p y.1 i.val) = y.1 := by
            funext i
            simp [join,Equiv.piEquivPiSubtypeProd,i.property]
          simp only [R,coreA,zeroTask,Pi.add_apply,Q,hj]
      unfold count
      rw [hr,Nat.card_range_of_injective hi,Nat.card_prod,Nat.card_fun,Nat.card_fun,Nat.card_fun]
      simp only [Nat.card_eq_fintype_card, Fintype.card_bool, ZMod.card]
    have countZ {I : Type} [Finite I] (m : ℕ) (hm : 2 ≤ m) (s : I → Prop) :
        count (coreZ (@zeroTask I m) s) = 2 ^ (2 ^ Nat.card {i // ¬s i}) := by
      classical
      let : NeZero m := ⟨by omega⟩
      let : Fact (1 < m) := ⟨by omega⟩
      have hs : Function.Surjective (coreZ (@zeroTask I m) s) := by
        intro f
        refine ⟨((fun _ => false),fun t => if f (fun i => t i.val) then 0 else 1),?_⟩
        funext w
        have hw : (fun i : {i // ¬s i} => join s (fun _ => false) w i.val) = w := by
          funext i
          simp [join,Equiv.piEquivPiSubtypeProd,i.property]
        simp only [coreZ,zeroTask,hw]
        cases f w <;> simp
      unfold count
      rw [hs.range_eq,Nat.card_univ,Nat.card_fun,Nat.card_fun]
      simp only [Nat.card_eq_fintype_card,Fintype.card_bool]
    have countBefore {I : Type} [Finite I] (m : ℕ) (hm : 2 ≤ m) (s : I → Prop) :
        count (coreBefore (fun a b : Table I m => a+b) zeroTask s) = 2 ^ Nat.card {i // s i} := by
      classical
      let : NeZero m := ⟨by omega⟩
      let : Fact (1 < m) := ⟨by omega⟩
      have hi : Function.Injective (coreBefore (fun a b : Table I m => a+b) zeroTask s) := by
        intro p q he
        by_contra hne
        have hj : join s p (fun _ => false) ≠ join s q (fun _ => false) := by
          intro hh
          apply hne
          funext i
          have := congrFun hh i.val
          simpa [join,Equiv.piEquivPiSubtypeProd,i.property] using this
        let a : Table I m := fun t => if t = join s p (fun _ => false) then 0 else 1
        have hh := congrFun he ((fun _ => false),a,0)
        simp [coreBefore,zeroTask,a,Ne.symm hj] at hh
      unfold count
      rw [Nat.card_range_of_injective hi,Nat.card_fun]
      simp only [Nat.card_eq_fintype_card,Fintype.card_bool]
    let ψ := fun a b : Table (Fin r) m => a+b
    let G := @zeroTask (Fin r) m
    have hcol : Function.Surjective (fun a => ψ a 0) := by intro a; exact ⟨a,add_zero a⟩
    have cardPrefix (j : ℕ) (hj : j ≤ r) : Nat.card {i : Fin r // i.val < j} = j := by
      let eqv : Fin j ≃ {i : Fin r // i.val < j} :=
        { toFun := fun i => ⟨⟨i.val,lt_of_lt_of_le i.isLt hj⟩,i.isLt⟩
          invFun := fun i => ⟨i.val.val,i.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      simpa using (Nat.card_congr eqv).symm
    have cardSuffix (s : Fin r → Prop) : Nat.card {i // ¬s i} = r - Nat.card {i // s i} := by
      simp [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    constructor
    · intro k
      by_cases kh : k.val ≤ h
      · have hs : (fun i : Fin r => piPosition h (.inl i) < k.val) = (fun i => i.val < k.val) := by
          funext i
          simp only [piPosition]
          split <;> apply propext <;> omega
        have heq := stageBefore ψ G (D := D) (fun c => piPosition h c < k.val)
          (by simp only [piPosition]; omega) (by simp only [piPosition]; omega)
        have heqc := congrArg (fun s : Fin r → Prop => count (coreBefore ψ G s)) hs
        rw [heqc] at heq
        change sharpCapacity D m (piPosition h) k.val = _ at heq
        rw [heq,countBefore m hm,cardPrefix k.val (by omega)]
        simp [piCount,kh]
      · by_cases kr : k.val ≤ r+1
        · have hs : (fun i : Fin r => piPosition h (.inl i) < k.val) =
              (fun i => i.val < k.val-1) := by
            funext i
            simp only [piPosition]
            split <;> apply propext <;> omega
          have heq := stageA ψ G (D := D) (fun c => piPosition h c < k.val)
            (by simp only [piPosition]; omega) (by simp only [piPosition]; omega)
          have heqc := congrArg (fun s : Fin r → Prop => count (coreA ψ G s)) hs
          rw [heqc] at heq
          change sharpCapacity D m (piPosition h) k.val = _ at heq
          rw [heq,countA m hm,cardSuffix,cardPrefix (k.val-1) (by omega)]
          simp [piCount,kh,kr]
        · have hs : (fun i : Fin r => piPosition h (.inl i) < k.val) = (fun i => i.val < r) := by
            funext i
            have := i.isLt
            simp only [piPosition]
            split <;> apply propext <;> omega
          have heq := stageZ ψ G (D := D) 0 hcol (fun c => piPosition h c < k.val)
            (by simp only [piPosition]; omega) (by simp only [piPosition]; omega)
          have heqc := congrArg (fun s : Fin r → Prop => count (coreZ G s)) hs
          rw [heqc] at heq
          change sharpCapacity D m (piPosition h) k.val = _ at heq
          rw [heq,countZ m hm,cardSuffix,cardPrefix r le_rfl]
          simp [piCount,kh,kr]
    · intro k
      by_cases hk0 : k.val=0
      · have hs : (fun i : Fin r => rhoPosition (.inl i) < k.val) = (fun i => i.val < 0) := by
          simp [hk0]
        have heq := stageBefore ψ G (D := D) (fun c => rhoPosition c < k.val)
          (by simp [rhoPosition,hk0]) (by simp [rhoPosition,hk0])
        have heqc := congrArg (fun s : Fin r → Prop => count (coreBefore ψ G s)) hs
        rw [heqc] at heq
        change sharpCapacity D m rhoPosition k.val = _ at heq
        rw [heq,countBefore m hm,cardPrefix 0 (by omega)]
        simp [rhoCount,hk0]
      by_cases hk1 : k.val=1
      · have hs : (fun i : Fin r => rhoPosition (.inl i) < k.val) = (fun i => i.val < 0) := by
          funext i
          simp [rhoPosition,hk1]
        have heq := stageA ψ G (D := D) (fun c => rhoPosition c < k.val)
          (by simp [rhoPosition,hk1]) (by simp [rhoPosition,hk1])
        have heqc := congrArg (fun s : Fin r → Prop => count (coreA ψ G s)) hs
        rw [heqc] at heq
        change sharpCapacity D m rhoPosition k.val = _ at heq
        rw [heq,countA m hm,cardSuffix,cardPrefix 0 (by omega)]
        simp [rhoCount,hk1]
      · have hs : (fun i : Fin r => rhoPosition (.inl i) < k.val) =
            (fun i => i.val < (k.val-1)/2) := by
          funext i
          simp only [rhoPosition]
          apply propext
          omega
        have heq := stageZ ψ G (D := D) 0 hcol (fun c => rhoPosition c < k.val)
          (by simp only [rhoPosition]; omega) (by simp only [rhoPosition]; omega)
        have heqc := congrArg (fun s : Fin r → Prop => count (coreZ G s)) hs
        rw [heqc] at heq
        change sharpCapacity D m rhoPosition k.val = _ at heq
        rw [heq,countZ m hm,cardSuffix,cardPrefix ((k.val-1)/2) (by have := k.isLt; omega)]
        simp [rhoCount,hk0,hk1]
  have maxima (r h m : ℕ) (hh : h ≤ r) (hm : 2 ≤ m) :
      (Finset.univ.sup (fun k : Fin (2*r+3) => piCount r h m k.val) = 2^h*m^(2^(r-h))) ∧
      (Finset.univ.sup (fun k : Fin (2*r+3) => rhoCount r m k.val) = m^(2^r)) := by
    have hm1 : 1 ≤ m := by omega
    have hp (n : ℕ) : 1 ≤ m^n := one_le_pow₀ hm1
    have hstep (n : ℕ) (hn : n < r) :
        2^(n+1)*m^(2^(r-(n+1))) ≤ 2^n*m^(2^(r-n)) := by
      have he : r-n = (r-(n+1))+1 := by omega
      have hb : 2 ≤ m^(2^(r-(n+1))) := hm.trans (le_self_pow hm1 (by positivity))
      rw [he,pow_succ 2 (r-(n+1)),show 2^(r-(n+1))*2 = 2^(r-(n+1))+2^(r-(n+1)) by omega]
      simp only [pow_add,pow_one]
      simpa only [mul_assoc] using
        Nat.mul_le_mul_left (2^n) (Nat.mul_le_mul_right (m^(2^(r-(n+1)))) hb)
    have hdesc (j : ℕ) (hj : h ≤ j) (hjr : j ≤ r) :
        2^j*m^(2^(r-j)) ≤ 2^h*m^(2^(r-h)) := by
      induction j, hj using Nat.le_induction with
      | base => exact le_rfl
      | succ n hn ih => exact (hstep n (by omega)).trans (ih (by omega))
    have hbig : 2 ≤ 2^h*m^(2^(r-h)) := by
      have hb : 2 ≤ m^(2^(r-h)) := hm.trans (le_self_pow hm1 (by positivity))
      have hh1 : 1 ≤ (2:ℕ)^h := one_le_pow₀ (by omega)
      nlinarith
    constructor
    · apply le_antisymm
      · apply Finset.sup_le
        intro k _
        unfold piCount
        split
        · rename_i hk
          exact (pow_le_pow_right' (by omega : 1 ≤ (2:ℕ)) hk).trans
            (Nat.le_mul_of_pos_right _ (by positivity))
        · split
          · rename_i hk hr
            exact hdesc (k.val-1) (by omega) (by omega)
          · exact hbig
      · have ht := Finset.le_sup (s := Finset.univ)
          (f := fun k : Fin (2*r+3) => piCount r h m k.val)
          (b := ⟨h+1,by omega⟩) (by simp)
        simpa [piCount,show ¬h+1 ≤ h by omega,show h+1 ≤ r+1 by omega] using ht
    · apply le_antisymm
      · apply Finset.sup_le
        intro k _
        unfold rhoCount
        split
        · exact hp _
        · split
          · exact le_rfl
          · exact (pow_le_pow_left' hm _).trans
              (pow_le_pow_right' hm1 (pow_le_pow_right' (by omega : 1 ≤ (2:ℕ)) (Nat.sub_le _ _)))
      · have ht := Finset.le_sup (s := Finset.univ) (f := fun k : Fin (2*r+3) => rhoCount r m k.val)
          (b := ⟨1,by omega⟩) (by simp)
        simpa [rhoCount] using ht
  have exponents (r h : ℕ) (hh : h ≤ r) (α C : ℝ) (hα : α < (2:ℝ)^h) (hC : 0<C) :
      ∃ m : ℕ, 2 ≤ m ∧ (C * ((2^h*m^(2^(r-h)) : ℕ) : ℝ)^α < ((m^(2^r) : ℕ) : ℝ)) := by
    let β : ℝ := (2:ℝ)^r - (2:ℝ)^(r-h)*α
    have hβ : 0<β := by
      have he : (2:ℝ)^r = (2:ℝ)^h * (2:ℝ)^(r-h) := by
        rw [← pow_add,Nat.add_sub_of_le hh]
      have hp : 0 < (2:ℝ)^(r-h) := by positivity
      dsimp [β]
      rw [he]
      nlinarith
    let T := C * ((2:ℝ)^h)^α
    have hT : 0<T := by dsimp [T]; positivity
    obtain ⟨m,hm⟩ := exists_nat_gt (max (2:ℝ) (T^(β⁻¹)))
    have hm2 : 2 ≤ m := by have := (le_max_left (2:ℝ) (T^(β⁻¹))).trans_lt hm; exact_mod_cast this.le
    have hm0 : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
    have ht : T < (m:ℝ)^β := by
      have hpow := Real.rpow_lt_rpow (by positivity : 0 ≤ T^(β⁻¹))
        ((le_max_right (2:ℝ) (T^(β⁻¹))).trans_lt hm) hβ
      rwa [← Real.rpow_mul hT.le,inv_mul_cancel₀ hβ.ne',Real.rpow_one] at hpow
    dsimp [β] at ht
    rw [Real.rpow_sub hm0] at ht
    have ht' := (lt_div_iff₀ (Real.rpow_pos_of_pos hm0 _)).mp ht
    have e1 : (2:ℝ)^r = ((2^r:ℕ):ℝ) := by norm_cast
    have e2 : (2:ℝ)^(r-h) = ((2^(r-h):ℕ):ℝ) := by norm_cast
    rw [e1,e2,Real.rpow_natCast,Real.rpow_natCast_mul hm0.le] at ht'
    refine ⟨m,hm2,?_⟩
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    simpa only [T,mul_assoc] using ht'
  have constantWidth {r : ℕ} {A B Z O : Type} {D : Fin r → Type}
      [Finite A] [Finite B] [Finite Z] [Finite O] [∀ i, Finite (D i)]
      [Nonempty A] [Nonempty B] [∀ i, Nonempty (D i)]
      (ψ : A → B → Z) (o : O) (pos : Coord r → ℕ) :
      width (Alphabet A B D) (task ψ (fun _ _ => o)) pos = 1 := by
    classical
    have hc (p : Coord r → Prop) : capacity (Alphabet A B D) (task ψ (fun _ _ => o)) p = 1 := by
      have hr : response (Alphabet A B D) (task ψ (fun _ _ => o)) p = (fun _ _ => o) := rfl
      unfold capacity
      rw [hr,Set.range_const]
      simp
    simp only [width,hc]
    exact Finset.sup_const (by simp : (Finset.univ : Finset (Fin (2*r+3))).Nonempty) (1:ℕ)
  have sharp (m : ℕ) (hm : 2 ≤ m) :
      sharpWidth D m (piPosition h) = 2^h*m^(2^(r-h)) ∧
      sharpWidth D m rhoPosition = m^(2^r) := by
    obtain ⟨hp,hn⟩ := layers h hh m hm D
    obtain ⟨mp,mn⟩ := maxima r h m hh hm
    constructor
    · change Finset.univ.sup (fun k : Fin (2*r+3) => sharpCapacity D m (piPosition h) k.val) = _
      simp only [hp]
      exact mp
    · change Finset.univ.sup (fun k : Fin (2*r+3) => sharpCapacity D m rhoPosition k.val) = _
      simp only [hn]
      exact mn
  refine ⟨?_,?_,?_,?_⟩
  · intro A B Z O _ _ _ _ _ _ _ ψ G b₀ hcol
    exact upper h hh ψ G b₀ hcol
  · intro m hm
    exact ⟨(layers h hh m hm D).1,(layers h hh m hm D).2,(sharp m hm).1,(sharp m hm).2⟩
  · intro α C hα hC
    obtain ⟨m,hm,he⟩ := exponents r h hh α C hα hC
    refine ⟨m,hm,?_⟩
    rw [(sharp m hm).1,(sharp m hm).2]
    exact he
  · intro A B Z O _ _ _ _ _ _ ψ o
    refine ⟨constantWidth ψ o (piPosition h),constantWidth ψ o rhoPosition,?_⟩
    intro C hC
    simpa only [constantWidth ψ o (piPosition h),constantWidth ψ o rhoPosition,
      Nat.cast_one,one_pow,mul_one] using hC

#print axioms result

end D5.S3.Observer.Separation.SurjectiveColumnSharpWidth
