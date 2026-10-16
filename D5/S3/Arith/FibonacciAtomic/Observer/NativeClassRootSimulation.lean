/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Legal root-experiment compilation preserves truthful joint padded-origin executions. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootImage
import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootPadding
import D5.S3.Arith.FibonacciAtomic.Observer.NativePassiveServiceRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCutPartitionRecovery (LiteralRow evaluateRow CutSet CutPrefixFree canonicalRow)
open NativeCutFibers
open NativeClassRootImage
open NativeClassRootPadding
open NativePassiveServiceRealization (Dialogue)

/-- A finite experiment tree asks only an appearing class, with exactly three
reached replies. Each visit, including repeated questions, is one call. -/
inductive RootTree (C : LiteralRow) (O : Type) where
  | stop : O → RootTree C O
  | ask : Classes C → RootTree C O → RootTree C O → RootTree C O → RootTree C O

/-- Execute a finite native dialogue on one stationary register. -/
def nativeRun {O : Type} (reply : Address → Reply) : Dialogue O → O × Nat
  | .stop o => (o,0)
  | .read a A B C D =>
      let out := match reply a with
        | .alpha => nativeRun reply A
        | .beta => nativeRun reply B
        | .branch => nativeRun reply C
        | .absent => nativeRun reply D
      (out.1,out.2+1)

/-- Execute a root tree against one unchanged joint type assignment. -/
def rootRun {C : LiteralRow} {O : Type} (θ : Classes C → Option Bool) : RootTree C O → O × Nat
  | .stop o => (o,0)
  | .ask d A B E =>
      let out := match θ d with
        | some true => rootRun θ A
        | some false => rootRun θ B
        | none => rootRun θ E
      (out.1,out.2+1)

/-- The maximum number of native calls on any reply path. -/
def nativeDepth {O : Type} : Dialogue O → Nat
  | .stop _ => 0
  | .read _ A B C D => max (max (nativeDepth A) (nativeDepth B))
      (max (nativeDepth C) (nativeDepth D)) + 1

/-- The maximum number of class experiments on any reply path. -/
def rootDepth {C : LiteralRow} {O : Type} : RootTree C O → Nat
  | .stop _ => 0
  | .ask _ A B E => max (max (rootDepth A) (rootDepth B)) (rootDepth E) + 1

/-- All address lengths in the finite dialogue, including unrealized edges. -/
def wordBound {O : Type} : Dialogue O → Nat
  | .stop _ => 0
  | .read a A B C D => max a.length
      (max (max (wordBound A) (wordBound B)) (max (wordBound C) (wordBound D)))

def firstClass : (C : LiteralRow) → Address → Sum Reply (Classes C × Bool)
  | .of (.inl b), a => .inl (readout a (.of b))
  | .of (.inr n), a => .inr (⟨n,by simp [labels]⟩,!a.isEmpty)
  | .mul _ _, [] => .inl .branch
  | .mul l r, false :: a => (firstClass l a).map id
      (fun p => (⟨p.1.val,Finset.mem_union_left _ p.1.property⟩,p.2))
  | .mul l r, true :: a => (firstClass r a).map id
      (fun p => (⟨p.1.val,Finset.mem_union_right _ p.1.property⟩,p.2))

def classReply (below : Bool) (t : Option Bool) : Reply :=
  if below then if t = none then .branch else .absent else rootReply t

private theorem query_congr (C : LiteralRow) (f g : Nat → Option Bool)
    (same : ∀ n ∈ labels C, f n = g n) (a : Address) :
    queryReply f a C = queryReply g a C := by
  induction C generalizing a with
  | of c => cases c with
    | inl b => cases a <;> rfl
    | inr n => cases a <;> simp only [queryReply,same n (by simp [labels])]
  | mul l r ihl ihr =>
      cases a with
      | nil => rfl
      | cons b a =>
          cases b
          · exact ihl (fun n hn => same n (Finset.mem_union_left _ hn)) a
          · exact ihr (fun n hn => same n (Finset.mem_union_right _ hn)) a

theorem firstClass_reply (C : LiteralRow) (a : Address)
    (θ : Classes C → Option Bool) :
    queryReply (typeExtend C θ) a C =
      match firstClass C a with
      | .inl y => y
      | .inr p => classReply p.2 (θ p.1) := by
  induction C generalizing a with
  | of b => cases b with
    | inl b => cases a <;> rfl
    | inr n =>
        cases a with
        | nil => simp [firstClass,queryReply,classReply,typeExtend,labels]
        | cons b a => simp [firstClass,queryReply,classReply,typeExtend,labels]
  | mul l r ihl ihr =>
      cases a with
      | nil => rfl
      | cons b a =>
          cases b
          · let θl : Classes l → Option Bool :=
              fun d => θ ⟨d.val,Finset.mem_union_left _ d.property⟩
            have eq : ∀ n ∈ labels l, typeExtend (.mul l r) θ n = typeExtend l θl n := by
              intro n hn
              simp [typeExtend,hn,labels,Finset.mem_union_left (labels r) hn,θl]
            simp only [queryReply,firstClass]
            rw [query_congr l _ _ eq a,ihl a θl]
            cases firstClass l a <;> rfl
          · let θr : Classes r → Option Bool :=
              fun d => θ ⟨d.val,Finset.mem_union_right _ d.property⟩
            have eq : ∀ n ∈ labels r, typeExtend (.mul l r) θ n = typeExtend r θr n := by
              intro n hn
              simp [typeExtend,hn,labels,Finset.mem_union_right (labels l) hn,θr]
            simp only [queryReply,firstClass]
            rw [query_congr r _ _ eq a,ihr a θr]
            cases firstClass r a <;> rfl

/-- Constant exterior queries select a continuation for free. A class query
asks that class once; a proper suffix sends both leaf types to absent. -/
def compileRoot {O : Type} (C : LiteralRow) : Dialogue O → RootTree C O
  | .stop o => .stop o
  | .read a A B E D =>
      let k : Reply → RootTree C O := fun y => match y with
        | .alpha => compileRoot C A
        | .beta => compileRoot C B
        | .branch => compileRoot C E
        | .absent => compileRoot C D
      match firstClass C a with
      | .inl y => k y
      | .inr p => .ask p.1 (k (classReply p.2 (some true)))
          (k (classReply p.2 (some false))) (k (classReply p.2 none))

private theorem compile_simulation {O : Type} (C : LiteralRow) (T : Dialogue O)
    (θ : Classes C → Option Bool) (reply : Address → Reply) (L : Nat)
    (words : wordBound T ≤ L)
    (same : ∀ a, a.length ≤ L → reply a = queryReply (typeExtend C θ) a C) :
    (rootRun θ (compileRoot C T)).1 = (nativeRun reply T).1 ∧
      (rootRun θ (compileRoot C T)).2 ≤ (nativeRun reply T).2 ∧
      rootDepth (compileRoot C T) ≤ nativeDepth T := by
  induction T with
  | stop o => exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  | read a A B E D ihA ihB ihE ihD =>
      have w : a.length ≤ L ∧ wordBound A ≤ L ∧ wordBound B ≤ L ∧
          wordBound E ≤ L ∧ wordBound D ≤ L := by simpa [wordBound,max_le_iff] using words
      have hA := ihA w.2.1
      have hB := ihB w.2.2.1
      have hE := ihE w.2.2.2.1
      have hD := ihD w.2.2.2.2
      have current := (same a w.1).trans (firstClass_reply C a θ)
      have bound : ∀ y : Reply,
          rootDepth (match y with
            | .alpha => compileRoot C A | .beta => compileRoot C B
            | .branch => compileRoot C E | .absent => compileRoot C D) ≤
          max (max (nativeDepth A) (nativeDepth B)) (max (nativeDepth E) (nativeDepth D)) := by
        intro y
        cases y <;> dsimp only <;> omega
      cases hp : firstClass C a with
      | inl y =>
          have hy : reply a = y := by simpa [hp] using current
          simp only [compileRoot,hp,nativeRun,hy]
          cases y <;> dsimp only <;> refine ⟨?_,?_,?_⟩ <;>
            (try simp only [nativeDepth]) <;>
            first | exact hA.1 | exact hB.1 | exact hE.1 | exact hD.1 | omega
      | inr p =>
          have hy : reply a = classReply p.2 (θ p.1) := by simpa [hp] using current
          have db := bound (classReply p.2 (some true))
          have dc := bound (classReply p.2 (some false))
          have de := bound (classReply p.2 none)
          have depth : rootDepth (compileRoot C (.read a A B E D)) ≤
              nativeDepth (.read a A B E D) := by
            simp only [compileRoot,hp,rootDepth,nativeDepth]
            exact Nat.add_le_add_right (max_le (max_le db dc) de) 1
          refine ⟨?_,?_,depth⟩
          · cases ht : θ p.1 with
            | none =>
                cases hb : p.2 <;> simp [compileRoot,hp,rootRun,nativeRun,hy,ht,
                  classReply,rootReply,hb] <;> exact hE.1
            | some b =>
                cases b <;> cases hb : p.2 <;>
                  simp [compileRoot,hp,rootRun,nativeRun,hy,ht,classReply,rootReply,hb] <;>
                  first | exact hA.1 | exact hB.1 | exact hD.1
          · cases ht : θ p.1 with
            | none =>
                cases hb : p.2 <;> simp [compileRoot,hp,rootRun,nativeRun,hy,ht,
                  classReply,rootReply,hb] <;> omega
            | some b =>
                cases b <;> cases hb : p.2 <;>
                  simp [compileRoot,hp,rootRun,nativeRun,hy,ht,classReply,rootReply,hb] <;> omega

/-- The finite set of exactly attained root assignments. -/
abbrev Chart (C : LiteralRow) := {θ : Classes C → Option Bool // Admissible C θ}

/-- For arbitrary complete-value supplements and finite native reader trees,
choose one actual origin per admissible type and compile its truthful run.
The origin, its injective acquired values, and its exported value remain fixed
through the run. The output is the complete predecessor row. -/
theorem truthful_joint_root_simulation (P : CutSet) (hP : CutPrefixFree P)
    (t₀ : Source) (S : Type) [Finite S]
    (σ : ImageValues (canonicalRow P t₀) → S) (E : S → Dialogue LiteralRow) (q : Nat)
    (budget : ∀ s, nativeDepth (E s) ≤ q)
    (correct : ∀ (v : ImageValues (canonicalRow P t₀))
      (u : OriginFiber P (canonicalRow P t₀)),
      substitution u.val = evaluateRow (extend (canonicalRow P t₀) v.val.val) (canonicalRow P t₀) →
      (nativeRun (fun a => readout a (substitution u.val)) (E (σ v))).1 = canonicalRow P u.val) :
    ∃ (v : Chart (canonicalRow P t₀) → ImageValues (canonicalRow P t₀))
      (u : Chart (canonicalRow P t₀) → OriginFiber P (canonicalRow P t₀))
      (c : Chart (canonicalRow P t₀) → S),
      ∀ θ,
        substitution (u θ).val = evaluateRow (extend (canonicalRow P t₀) (v θ).val.val) (canonicalRow P t₀) ∧
        types (canonicalRow P t₀) (v θ).val.val = θ.val ∧
        c θ = σ (v θ) ∧
        (rootRun θ.val (compileRoot (canonicalRow P t₀) (E (c θ)))).1 = canonicalRow P (u θ).val ∧
        (rootRun θ.val (compileRoot (canonicalRow P t₀) (E (c θ)))).2 ≤
          (nativeRun (fun a => readout a (substitution (u θ).val)) (E (σ (v θ)))).2 ∧
        rootDepth (compileRoot (canonicalRow P t₀) (E (c θ))) ≤ q := by
  classical
  let _ := Fintype.ofFinite S
  let C := canonicalRow P t₀
  let L := (Finset.univ.image (fun s => wordBound (E s))).sup id
  have words (s : S) : wordBound (E s) ≤ L :=
    Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩)
  have padded (θ : Chart C) := padded_native_query_chart P hP t₀ L θ.val θ.property
  choose v u image ht deep replies using padded
  refine ⟨v,u,fun θ => σ (v θ),?_⟩
  intro θ
  have sim := compile_simulation C (E (σ (v θ))) θ.val
    (fun a => readout a (substitution (u θ).val)) L (words _) (replies θ)
  exact ⟨image θ,ht θ,rfl,sim.1.trans (correct (v θ) (u θ) (image θ)),
    sim.2.1,sim.2.2.trans (budget _)⟩

#print axioms truthful_joint_root_simulation
end D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
