/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveImageGuard
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite Presburger synthesis for simultaneous canonical native image filters. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeEffectiveAtomicGuard
import Mathlib.Data.List.Pi

/-! Finite syntax tests and post-fixed Boolean obligation graphs for original
affine native systems and their unrestricted completed canonical outputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveImageGuard

open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeGuardedFreeExtension NativeGuardedImageSaturation NativeAffineImageSaturation
open NativeEffectiveAtomicGuard NativeGuardedAtomicReplacement NativeImageSaturationInterface
open GenealogicalFiberTransport (Source substitution)
open PresburgerArithmetic

/-- Finite ground parsing retains both exceptional native terminals. -/
def groundImage {n k m s : Nat} (I : Input n k m) (mode : Mode s m) :
    Source → Nat → Formula
  | .of b, t => .or (atomicGuard I mode (.ground (.of b)) t)
      (atomicGuard I mode (.ground (.of b)) (t+1))
  | .mul A B, t => .or (atomicGuard I mode (.ground (.mul A B)) t)
      (.or (atomicGuard I mode (.ground (.mul A B)) (t+1))
        (.and (groundImage I mode A t) (groundImage I mode B t)))

private theorem groundImage_holds {n k m s : Nat} (I : Input n k m)
    (guarded : Guarded I.equations) (mode : Mode s m) (p : Fin n → Nat)
    (legal : Legal I p) (g : Source) (t : Nat) :
    (groundImage I mode g t).holds (environment p) ↔ NativeImage t (embed g) := by
  induction g with
  | of b =>
    simp only [groundImage, Formula.holds, atomic_guard_correct I guarded mode p legal]
    conv_rhs => rw [native_image_iff]
    constructor
    · rintro (h | h) <;> tauto
    · rintro (h | h | ⟨U, V, h, _, _⟩)
      · exact Or.inl h
      · exact Or.inr h
      · have tag := congrArg (fun X => (PFunctor.M.dest X).1) h
        cases tag
  | mul A B ihA ihB =>
    simp only [groundImage, Formula.holds, atomic_guard_correct I guarded mode p legal,
      ihA, ihB]
    conv_rhs => rw [native_image_iff]
    constructor
    · rintro (h | h | ⟨ha, hb⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨embed A, embed B, rfl, ha, hb⟩)
    · rintro (h | h | ⟨U, V, eq, ha, hb⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · have sides := node_inj eq
        exact Or.inr (Or.inr ⟨sides.1.symm ▸ ha, sides.2.symm ▸ hb⟩)

private theorem atomic_image_iff (r t : Nat) : NativeImage t (atomic r) ↔ t ≤ r := by
  constructor
  · rintro ⟨X, eq⟩
    obtain ⟨j, rank, _⟩ := atomic_predecessor t r X eq
    omega
  · intro h
    refine ⟨atomic (r-t), ?_⟩
    change rho^[t] (rho^[r-t] (leaf true)) = rho^[r] (leaf true)
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le h]

/-- An affine inequality on the original shared valuation. -/
def rankAtLeast (a : Affine) (c t : Nat) : Formula :=
  .qf (.atom (.le (a.add (.const ((c : Int) - t)))))

private theorem rankAtLeast_holds (a : Affine) (c t : Nat) (xs : List Int)
    (legal : 0 ≤ a.eval xs) :
    (rankAtLeast a c t).holds xs ↔ t ≤ (a.eval xs).toNat + c := by
  have cast := Int.toNat_of_nonneg legal
  simp only [rankAtLeast, Formula.holds, QF.eval, Atom.eval, decide_eq_true_eq,
    Affine.eval_add, Affine.eval_const]
  omega

def tokenImage {n k m : Nat} (I : Input n k m) (j : Fin (k + 1)) (c t : Nat) : Formula :=
  Fin.lastCases (constant true) (fun i => rankAtLeast (I.indices i) c t) j

private theorem tokenImage_holds {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (legal : Legal I p) (v : Fin m → CompletionTree) (j : Fin (k + 1)) (c t : Nat) :
    (tokenImage I j c t).holds (environment p) ↔
      NativeImage t (evaluate (ranks I p) v (.token j c)) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [tokenImage, Fin.lastCases_last, constant_holds]
    simp only [evaluate, CompletionPositiveDriftRegion.value, tokenKind, tokenRank,
      Fin.lastCases_last, Bool.false_eq_true, ite_false]
    exact ⟨fun _ => ⟨Omega, iterate_omega t⟩, fun _ => trivial⟩
  · simp only [tokenImage, Fin.lastCases_castSucc]
    rw [rankAtLeast_holds _ _ _ _ (legal.2 i)]
    simp only [evaluate, CompletionPositiveDriftRegion.value, tokenKind, tokenRank,
      Fin.lastCases_castSucc, ite_true]
    change t ≤ ranks I p i + c ↔ NativeImage t (atomic (ranks I p i + c))
    exact (atomic_image_iff _ _).symm

/-- A Boolean state obligation is indexed by an original state and a threshold. -/
abbrev Configuration (m s : Nat) := Fin m → Fin (s + 1) → Bool

/-- Positive finite expression syntax over the state obligations. -/
def expressionImage {n k m s : Nat} (I : Input n k m) (mode : Mode s m)
    (cfg : Configuration m s) : Expression k m → (t : Nat) → t ≤ s → Formula
  | .ground g, t, _ => groundImage I mode g t
  | .token j c, t, _ => tokenImage I j c t
  | .var a i, t, ht => if h : t ≤ a then constant true
      else constant (cfg i ⟨t-a, by omega⟩)
  | .pair A B, t, ht => .or (atomicGuard I mode (.pair A B) t)
      (.or (atomicGuard I mode (.pair A B) (t+1))
        (.and (expressionImage I mode cfg A t ht) (expressionImage I mode cfg B t ht)))

/-- The finite closure constraint for one state and threshold. -/
def stateImage {n k m s : Nat} (I : Input n k m) (mode : Mode s m)
    (cfg : Configuration m s) (i : Fin m) (t : Fin (s + 1)) : Formula :=
  match I.equations i with
  | some E => expressionImage I mode cfg E t.val (by omega)
  | none => match mode i with
    | none => constant true
    | some j => constant (decide (t.val ≤ j.val))

/-- The pinned finite Cartesian-product constructor supplies all Boolean labels.
Outside the finite key list the extension has the fixed false default. -/
def configurations {K : Type} [DecidableEq K] (l : List K) : List (K → Bool) :=
  (List.pi l (fun _ => [false,true])).map fun f i =>
    if h : i ∈ l then f i h else false

private theorem configurations_complete {K : Type} [DecidableEq K] (l : List K)
    (f : K → Bool) : ∃ g ∈ configurations l, ∀ i ∈ l, g i = f i := by
  let g : ∀ i ∈ l, Bool := fun i _ => f i
  have hg : g ∈ List.pi l (fun _ => [false,true]) := by
    apply (List.mem_pi _ g).mpr
    intro i hi
    cases h : f i <;> simp [g,h]
  refine ⟨_,List.mem_map.mpr ⟨g,hg,rfl⟩,?_⟩
  intro i hi
  exact dite_eq_left hi

def keys (m s : Nat) : List (Fin m × Fin (s + 1)) :=
  (List.finRange m).flatMap fun i => (List.finRange (s + 1)).map fun t => (i, t)

private theorem mem_keys {m s : Nat} (i : Fin m) (t : Fin (s + 1)) : (i, t) ∈ keys m s := by
  simp [keys]

def conjunction : List Formula → Formula
  | [] => constant true
  | p :: ps => .and p (conjunction ps)

def disjunction : List Formula → Formula
  | [] => constant false
  | p :: ps => .or p (disjunction ps)

private theorem conjunction_holds (ps : List Formula) (xs : List Int) :
    (conjunction ps).holds xs ↔ ∀ p ∈ ps, p.holds xs := by
  induction ps with
  | nil => simp [conjunction, constant_holds]
  | cons p ps ih => simp [conjunction, Formula.holds, ih]

private theorem disjunction_holds (ps : List Formula) (xs : List Int) :
    (disjunction ps).holds xs ↔ ∃ p ∈ ps, p.holds xs := by
  induction ps with
  | nil => simp [disjunction, constant_holds]
  | cons p ps ih => simp [disjunction, Formula.holds, ih]

/-- Every selected obligation has its defining positive clause. -/
def closedConfiguration {n k m s : Nat} (I : Input n k m) (mode : Mode s m)
    (cfg : Configuration m s) : Formula :=
  conjunction ((keys m s).map fun q =>
    if cfg q.1 q.2 then stateImage I mode cfg q.1 q.2 else constant true)

private theorem closedConfiguration_holds {n k m s : Nat} (I : Input n k m)
    (mode : Mode s m) (cfg : Configuration m s) (xs : List Int) :
    (closedConfiguration I mode cfg).holds xs ↔
      ∀ i t, cfg i t = true → (stateImage I mode cfg i t).holds xs := by
  simp only [closedConfiguration, conjunction_holds, List.forall_mem_map]
  constructor
  · intro h i t ht
    have law := h (i, t) (mem_keys i t)
    simpa only [ht, ite_true] using law
  · intro h q hq
    cases hc : cfg q.1 q.2
    · simp [constant_holds]
    · exact h q.1 q.2 hc

/-- Original legal guards remain explicit conjuncts. -/
def legalGuard {n k m : Nat} (I : Input n k m) : Formula :=
  .and I.guard (conjunction ((List.finRange k).map fun j => .qf (.atom (.le (I.indices j)))))

private theorem legalGuard_holds {n k m : Nat} (I : Input n k m) (p : Fin n → Nat) :
    (legalGuard I).holds (environment p) ↔ Legal I p := by
  simp [legalGuard, Formula.holds, conjunction_holds, QF.eval, Atom.eval, Legal]

/-- The formula is built from finite syntax and a finite Boolean graph. No
completed value, parameter enumeration or semantic choice is used. -/
def imageGuard {n k m : Nat} (I : Input n k m) (mode : Mode (threshold I.filters) m) : Formula :=
  let s := threshold I.filters
  .and (legalGuard I) (disjunction ((configurations (keys m s)).map fun f =>
    let cfg : Configuration m s := fun i t => f (i, t)
    .and (closedConfiguration I mode cfg)
      (conjunction (I.filters.attach.map fun q =>
        expressionImage I mode cfg q.val.1 q.val.2 (by
          have ht : q.val.2 ≤ threshold I.filters := by
            unfold threshold
            exact List.le_max_of_le (List.mem_map.mpr ⟨q.val, q.property, rfl⟩) le_rfl
          exact ht)))))

private theorem expressionImage_exact {n k m s : Nat} (I : Input n k m)
    (guarded : Guarded I.equations) (mode : Mode s m) (p : Fin n → Nat)
    (legal : Legal I p) (cfg : Configuration m s)
    (exactStates : ∀ i t, cfg i t = true ↔
      NativeImage t.val (canonical I.equations (ranks I p) guarded mode i))
    (E : Expression k m) (t : Nat) (ht : t ≤ s) :
    (expressionImage I mode cfg E t ht).holds (environment p) ↔
      NativeImage t (evaluate (ranks I p)
        (canonical I.equations (ranks I p) guarded mode) E) := by
  induction E with
  | ground g => exact groundImage_holds I guarded mode p legal g t
  | token j c => exact tokenImage_holds I p legal _ j c t
  | var a i =>
    simp only [expressionImage]
    by_cases h : t ≤ a
    · rw [dite_eq_left h, constant_holds]
      exact ⟨fun _ => image_shift_large t a _ h, fun _ => rfl⟩
    · rw [dite_eq_right h, constant_holds, exactStates]
      exact (image_shift_cancel t a _ (by omega)).symm
  | pair A B ihA ihB =>
    simp only [expressionImage, Formula.holds, atomic_guard_correct I guarded mode p legal,
      ihA, ihB]
    conv_rhs => rw [native_image_iff]
    constructor
    · rintro (h | h | ⟨ha, hb⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨_, _, rfl, ha, hb⟩)
    · rintro (h | h | ⟨U, V, eq, ha, hb⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · have sides :
            evaluate (ranks I p) (canonical I.equations (ranks I p) guarded mode) A = U ∧
            evaluate (ranks I p) (canonical I.equations (ranks I p) guarded mode) B = V :=
          node_inj eq
        exact Or.inr (Or.inr ⟨sides.1.symm ▸ ha, sides.2.symm ▸ hb⟩)

private theorem closedConfiguration_sound {n k m s : Nat} (I : Input n k m)
    (guarded : Guarded I.equations) (mode : Mode s m) (p : Fin n → Nat)
    (legal : Legal I p) (cfg : Configuration m s)
    (closed : (closedConfiguration I mode cfg).holds (environment p)) :
    ∀ E t (ht : t ≤ s), (expressionImage I mode cfg E t ht).holds (environment p) →
      NativeImage t (evaluate (ranks I p)
        (canonical I.equations (ranks I p) guarded mode) E) := by
  let K := canonical I.equations (ranks I p) guarded mode
  have law : Satisfies I.equations (ranks I p) K ∧
      Extends I.equations (canonicalFree mode) K := Classical.choose_spec
    (guarded_extension I.equations (ranks I p) guarded (canonicalFree mode)).exists
  have post := (closedConfiguration_holds I mode cfg _).mp closed
  suffices sound : ∀ t, ∀ ht : t ≤ s, ∀ E,
      (expressionImage I mode cfg E t ht).holds (environment p) →
        NativeImage t (evaluate (ranks I p) K E) by
    intro E t ht; exact sound t ht E
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht E accept
    by_cases zero : t = 0
    · subst t; exact ⟨evaluate (ranks I p) K E, rfl⟩
    let R (X : CompletionTree) : Prop := NativeImage t X ∨
      ∃ E : Expression k m, X = evaluate (ranks I p) K E ∧
        (expressionImage I mode cfg E t ht).holds (environment p)
    have known : ∀ X, NativeImage t X → X = atomic t ∨ X = atomic (t+1) ∨
        ∃ U V, X = node U V ∧ R U ∧ R V := by
      intro X hx
      rcases (native_image_iff t X).mp hx with h | h | ⟨U, V, eq, ha, hb⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨U, V, eq, Or.inl ha, Or.inl hb⟩)
    have pair_step : ∀ A B : Expression k m,
        (expressionImage I mode cfg (.pair A B) t ht).holds (environment p) →
        evaluate (ranks I p) K (.pair A B) = atomic t ∨
        evaluate (ranks I p) K (.pair A B) = atomic (t+1) ∨
        ∃ U V, evaluate (ranks I p) K (.pair A B) = node U V ∧ R U ∧ R V := by
      intro A B pass
      simp only [expressionImage, Formula.holds,
        atomic_guard_correct I guarded mode p legal] at pass
      rcases pass with terminal | terminal | ⟨ha, hb⟩
      · exact Or.inl terminal
      · exact Or.inr (Or.inl terminal)
      · exact Or.inr (Or.inr ⟨_, _, rfl, Or.inr ⟨A, rfl, ha⟩,
          Or.inr ⟨B, rfl, hb⟩⟩)
    have analyze : ∀ E : Expression k m,
        (expressionImage I mode cfg E t ht).holds (environment p) →
        evaluate (ranks I p) K E = atomic t ∨
        evaluate (ranks I p) K E = atomic (t+1) ∨
        ∃ U V, evaluate (ranks I p) K E = node U V ∧ R U ∧ R V := by
      intro F pass
      cases F with
      | ground g => exact known _ ((groundImage_holds I guarded mode p legal g t).mp pass)
      | token j c => exact known _ ((tokenImage_holds I p legal K j c t).mp pass)
      | pair A B => exact pair_step A B pass
      | var a i =>
        by_cases large : t ≤ a
        · exact known _ (image_shift_large t a (K i) large)
        · simp only [expressionImage, dite_eq_right large, constant_holds] at pass
          cases a with
          | succ a =>
            have lower : (expressionImage I mode cfg (.var 0 i) (t-(a+1))
                (by omega)).holds (environment p) := by
              simp only [expressionImage]
              split_ifs
              · exact (constant_holds _ _).mpr rfl
              · exact (constant_holds _ _).mpr pass
            have accepted := ih (t-(a+1)) (by omega) (by omega) (.var 0 i) lower
            exact known _ ((image_shift_cancel t (a+1) (K i) (by omega)).mpr accepted)
          | zero =>
            have selected : cfg i ⟨t, by omega⟩ = true := by simpa only [Nat.sub_zero] using pass
            have statePass := post i ⟨t, by omega⟩ selected
            change K i = atomic t ∨ K i = atomic (t+1) ∨
              ∃ U V, K i = node U V ∧ R U ∧ R V
            cases eq : I.equations i with
            | none =>
              apply known
              rw [law.2 i eq]
              cases hm : mode i with
              | none =>
                simp only [canonicalFree, hm]
                exact ⟨Omega, iterate_omega t⟩
              | some r =>
                simp only [stateImage, eq, hm, constant_holds, decide_eq_true_eq] at statePass
                simp only [canonicalFree, hm]
                exact (atomic_image_iff r.val t).mpr statePass
            | some F =>
              simp only [stateImage, eq] at statePass
              rw [law.1 i F eq]
              cases F with
              | ground g =>
                exact known _ ((groundImage_holds I guarded mode p legal g t).mp statePass)
              | token j c => exact known _ ((tokenImage_holds I p legal K j c t).mp statePass)
              | pair A B => exact pair_step A B statePass
              | var a j => exact (guarded i a j eq).elim
    apply image_coinduction t R
      (fun X hx => by
        rcases hx with h | ⟨F, rfl, h⟩
        · exact known X h
        · exact analyze F h)
      _ (Or.inr ⟨E, rfl, accept⟩)

private theorem filters_bound {k m : Nat} (fs : List (Filter k m))
    (E : Expression k m) (t : Nat) (mem : (E, t) ∈ fs) : t ≤ threshold fs := by
  unfold threshold
  exact List.le_max_of_le (List.mem_map.mpr ⟨(E, t), mem, rfl⟩) le_rfl

/-- A finite Presburger formula, constructed from the original syntax, is
exactly the simultaneous canonical actual-image condition on every legal
original affine tuple. Completed outputs have no rationality restriction. -/
theorem effective_image_guard {n k m : Nat} (I : Input n k m)
    (guarded : Guarded I.equations) (mode : Mode (threshold I.filters) m)
    (p : Fin n → Nat) :
    (imageGuard I mode).holds (environment p) ↔
      Legal I p ∧ Passes (ranks I p)
        (canonical I.equations (ranks I p) guarded mode) I.filters := by
  classical
  let s := threshold I.filters
  let K := canonical I.equations (ranks I p) guarded mode
  simp only [imageGuard, Formula.holds, legalGuard_holds, disjunction_holds]
  constructor
  · rintro ⟨legal, F, hF, accepted⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hF
    rcases accepted with ⟨closed, filters⟩
    refine ⟨legal, ?_⟩
    intro E t mem
    have pass := (conjunction_holds _ _).mp filters _
      (List.mem_map.mpr ⟨⟨(E, t),mem⟩,List.mem_attach _ _,rfl⟩)
    exact closedConfiguration_sound I guarded mode p legal _ closed E t
      (filters_bound I.filters E t mem) pass
  · rintro ⟨legal, filters⟩
    let exactCfg : Configuration m s := fun i t => decide (NativeImage t.val (K i))
    obtain ⟨f, hf, same⟩ := configurations_complete (keys m s) (fun q => exactCfg q.1 q.2)
    have exactStates : ∀ i t, f (i, t) = true ↔ NativeImage t.val (K i) := by
      intro i t
      rw [same (i, t) (mem_keys i t)]
      exact decide_eq_true_iff
    refine ⟨legal, _, List.mem_map.mpr ⟨f,hf,rfl⟩, ?_, ?_⟩
    · apply (closedConfiguration_holds I mode _ _).mpr
      intro i t selected
      have accepted := (exactStates i t).mp selected
      have law : Satisfies I.equations (ranks I p) K ∧
          Extends I.equations (canonicalFree mode) K := Classical.choose_spec
        (guarded_extension I.equations (ranks I p) guarded (canonicalFree mode)).exists
      cases eq : I.equations i with
      | some E =>
        simp only [stateImage, eq]
        apply (expressionImage_exact I guarded mode p legal _ exactStates E t.val (by omega)).mpr
        rw [← law.1 i E eq]
        exact accepted
      | none =>
        simp only [stateImage, eq]
        rw [law.2 i eq] at accepted
        cases hm : mode i with
        | none => simp [constant_holds]
        | some j =>
          simp only [hm, canonicalFree] at accepted ⊢
          rw [constant_holds, decide_eq_true_eq]
          exact (atomic_image_iff j.val t.val).mp accepted
    · apply (conjunction_holds _ _).mpr
      intro F hF
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hF
      exact (expressionImage_exact I guarded mode p legal _ exactStates q.val.1 q.val.2
        (filters_bound I.filters q.val.1 q.val.2 q.property)).mpr
          (filters q.val.1 q.val.2 q.property)


open NativeRootLinkNormalization

/-- A parsed root occurrence, with equality evidence obtained from syntax. -/
abbrev RootLink {k m : Nat} (S : System k m) :=
  {q : Fin m × Nat × Fin m // S q.1 = some (.var q.2.1 q.2.2)}

def rootAt {k m : Nat} (S : System k m) (i : Fin m) : Option (RootLink S) :=
  match h : S i with
  | some (.var a j) => some ⟨(i, a, j),h⟩
  | _ => none

/-- Inspect original state names in their finite order. -/
def findRoot {k m : Nat} (S : System k m) : Option (RootLink S) :=
  (List.finRange m).findSome? (rootAt S)

private theorem findRoot_none {k m : Nat} (S : System k m)
    (none : findRoot S = Option.none) : Guarded S := by
  have all := List.findSome?_eq_none_iff.mp none
  intro i a j eq
  have absent := all i (by simp)
  unfold rootAt at absent
  split at absent <;> simp_all

def rootStep {k m : Nat} (S : System k m) (r : RootLink S) : Presentation k m :=
  if r.val.2.2 = r.val.1 then selfStep S r.val.1 r.val.2.1
  else linkStep S r.val.1 r.val.2.1 r.val.2.2

private theorem rootStep_correct {k m : Nat} (S : System k m) (r : RootLink S) :
    Correct S (rootStep S r) := by
  unfold rootStep
  split_ifs with h
  · exact selfStep_correct S _ _ (by simpa only [h] using r.property)
  · exact linkStep_correct S _ _ _ h r.property

private theorem rootStep_decreases {k m : Nat} (S : System k m) (r : RootLink S) :
    (roots (rootStep S r).equations).card < (roots S).card := by
  unfold rootStep
  split_ifs with h
  · exact selfStep_decreases S _ _ (by simpa only [h] using r.property)
  · exact linkStep_decreases S _ _ _ r.property

def initialPresentation {k m : Nat} (S : System k m) : Presentation k m :=
  ⟨S, identity, identity⟩

private theorem initialPresentation_correct {k m : Nat} (S : System k m) :
    Correct S (initialPresentation S) := by
  intro p
  constructor <;> intro v sat <;> exact ⟨sat,rfl⟩

/-- A total finite syntactic program with an explicit input-size fuel bound. -/
def normalizeFuel {k m : Nat} : Nat → System k m → Presentation k m
  | 0, S => initialPresentation S
  | f+1, S => match findRoot S with
    | none => initialPresentation S
    | some r => let T := rootStep S r
      compose T (normalizeFuel f T.equations)

private theorem normalizeFuel_correct {k m : Nat} (f : Nat) (S : System k m) :
    Correct S (normalizeFuel f S) := by
  induction f generalizing S with
  | zero => exact initialPresentation_correct S
  | succ f ih =>
    simp only [normalizeFuel]
    cases h : findRoot S with
    | none => exact initialPresentation_correct S
    | some r => exact compose_correct S _ _ (rootStep_correct S r) (ih _)

private theorem normalizeFuel_guarded {k m : Nat} (f : Nat) (S : System k m)
    (enough : (roots S).card ≤ f) : Guarded (normalizeFuel f S).equations := by
  classical
  induction f generalizing S with
  | zero =>
    change Guarded S
    intro i a j eq
    have mem := (mem_roots S i).mpr ⟨a,j,eq⟩
    have positive := Finset.card_pos.mpr ⟨i,mem⟩
    omega
  | succ f ih =>
    simp only [normalizeFuel]
    cases h : findRoot S with
    | none => exact findRoot_none S h
    | some r =>
      change Guarded (normalizeFuel f (rootStep S r).equations).equations
      apply ih
      have decrease := rootStep_decreases S r
      omega

/-- Compute root-link normalization while retaining both original expression maps. -/
def effectiveNormalForm {k m : Nat} (S : System k m) : Presentation k m := normalizeFuel m S

theorem effectiveNormalForm_law {k m : Nat} (S : System k m) :
    Guarded (effectiveNormalForm S).equations ∧ Correct S (effectiveNormalForm S) := by
  classical
  refine ⟨normalizeFuel_guarded m S ?_,normalizeFuel_correct m S⟩
  exact (Finset.card_le_card (Finset.subset_univ (roots S))).trans_eq (Fintype.card_fin m)

/-- Every original filter is substituted through its retained reconstruction. -/
def normalizedInput {n k m : Nat} (I : Input n k m) : Input n k m where
  equations := (effectiveNormalForm I.equations).equations
  filters := transformedFilters (effectiveNormalForm I.equations) I.filters
  indices := I.indices
  guard := I.guard

abbrev EffectiveMode {n k m : Nat} (I : Input n k m) :=
  {i : Fin m // (normalizedInput I).equations i = none} →
    Option (Fin (threshold (normalizedInput I).filters + 2))

/-- Extend the mode on the actual free list by inert entries at defined names. -/
def effectiveTotalMode {n k m : Nat} (I : Input n k m) (mode : EffectiveMode I) :
    Mode (threshold (normalizedInput I).filters) m := fun i =>
  match h : (normalizedInput I).equations i with
  | none => mode ⟨i,h⟩
  | some _ => none

def originalImageGuard {n k m : Nat} (I : Input n k m) (mode : EffectiveMode I) : Formula :=
  imageGuard (normalizedInput I) (effectiveTotalMode I mode)

noncomputable def effectiveCanonical {n k m : Nat} (I : Input n k m)
    (mode : EffectiveMode I) (p : Fin n → Nat) : Fin m → CompletionTree :=
  mapValues (ranks I p) (effectiveNormalForm I.equations).reconstruct
    (canonical (normalizedInput I).equations (ranks I p)
      (effectiveNormalForm_law I.equations).1 (effectiveTotalMode I mode))

def EffectiveInMode {n k m : Nat} (I : Input n k m) (mode : EffectiveMode I)
    (p : Fin n → Nat) (v : Fin m → CompletionTree) : Prop :=
  InMode (normalizedInput I).equations (threshold (normalizedInput I).filters)
    (effectiveTotalMode I mode)
    (mapValues (ranks I p) (effectiveNormalForm I.equations).project v)

/-- Effective acceptance and simultaneous existence in the entire original
completed relation, with every original name and filter reconstructed. -/
theorem original_effective_image_guard {n k m : Nat} (I : Input n k m)
    (mode : EffectiveMode I) (p : Fin n → Nat) :
    ((originalImageGuard I mode).holds (environment p) ↔
      Legal I p ∧ SourcePasses I p (effectiveCanonical I mode p)) ∧
    ((originalImageGuard I mode).holds (environment p) ↔
      Legal I p ∧ ∃ v, SourceSatisfies I p v ∧
        EffectiveInMode I mode p v ∧ SourcePasses I p v) := by
  let T := effectiveNormalForm I.equations
  let J := normalizedInput I
  have guard : Guarded T.equations := (effectiveNormalForm_law I.equations).1
  have corr := (effectiveNormalForm_law I.equations).2 (ranks I p)
  let md := effectiveTotalMode I mode
  let K := canonical T.equations (ranks I p) guard md
  have sat := normalized_saturation T.equations (ranks I p) guard J.filters md
  have accepted := effective_image_guard J guard md p
  have filters := filters_correspond T (ranks I p) K I.filters
  have canonicalTest : (originalImageGuard I mode).holds (environment p) ↔
      Legal I p ∧ SourcePasses I p (effectiveCanonical I mode p) := by
    exact accepted.trans (and_congr Iff.rfl filters)
  refine ⟨canonicalTest, canonicalTest.trans ?_⟩
  apply and_congr_right
  intro legal
  constructor
  · intro passes
    have back := corr.2 K sat.1
    refine ⟨mapValues (ranks I p) T.reconstruct K,back.1,?_,passes⟩
    change InMode T.equations (threshold J.filters) md
      (mapValues (ranks I p) T.project (mapValues (ranks I p) T.reconstruct K))
    rw [back.2]
    exact sat.2.1
  · rintro ⟨v, hv, vm, pass⟩
    have forward := corr.1 v hv
    have transformed : Passes (ranks I p) (mapValues (ranks I p) T.project v) J.filters := by
      apply (filters_correspond T (ranks I p) _ I.filters).mpr
      rw [forward.2]
      exact pass
    exact filters.mp (sat.2.2.mp ⟨_,forward.1,vm,transformed⟩)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveImageGuard
