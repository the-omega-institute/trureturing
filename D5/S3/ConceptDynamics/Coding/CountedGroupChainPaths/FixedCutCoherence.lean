/- GID: D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGroupChainPaths/FixedCutCoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete endpoint-preserving fixed-cut coherence and the literal positive U/V chain. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths
import D5.S3.ConceptDynamics.Coding.FixedPositivePartitionSseDistance
import Mathlib.Data.Nat.Dist

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths.FixedCutCoherence

open CountedGroupOverlap RectangularNilpotenceBarrier
universe u
variable {H : Type u} [Group H] [Fintype H] [LinearOrder H]

noncomputable section
-- Fixed-cut operations preserve the complete original numbered edge data.
abbrev E {n : ℕ} (A : GroupMat H n n) := Σ i : Fin n, Σ j : Fin n, At A i j
def edges {n : ℕ} {A : GroupMat H n n} :
    (d : ℕ) → {i j : Fin n} → Word A d i j → List (E A)
  | 0, _, _, _ => []
  | d+1, i, _, p => ⟨i,p.1,⟨p.2.1,p.2.2.1⟩⟩ :: edges d p.2.2.2
private theorem edges_len {n d : ℕ} {A : GroupMat H n n}
    {i j : Fin n} (p : Word A d i j) : (edges d p).length = d := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih => exact congrArg Nat.succ (ih p.2.2.2)
def wc {n d e : ℕ} {A : GroupMat H n n} {i j : Fin n}
    (h : d=e) (p : Word A d i j) : Word A e i j := h ▸ p
private theorem edges_wc {n d e : ℕ} {A : GroupMat H n n} {i j : Fin n}
    (h : d=e) (p : Word A d i j) : edges e (wc h p) = edges d p := by cases h; rfl
def app {n : ℕ} {A : GroupMat H n n} :
    (d : ℕ) → {i j w : Fin n} → Word A d i j → At A j w → Word A (d+1) i w
  | 0, _, _, _, ⟨⟨v,hvi,hvj⟩⟩, a => by subst v; subst_vars; exact ⟨_,a.1,a.2,nilPath _⟩
  | d+1, _, _, _, p, a => ⟨p.1,p.2.1,p.2.2.1,app d p.2.2.2 a⟩
private theorem edges_app {n d : ℕ} {A : GroupMat H n n} {i j w : Fin n}
    (p : Word A d i j) (a : At A j w) :
    edges (d+1) (app d p a) = edges d p ++ [⟨j,w,a⟩] := by
  induction d generalizing i with
  | zero => rcases p with ⟨⟨v,hvi,hvj⟩⟩; subst v; subst j; rfl
  | succ d ih => exact congrArg (List.cons ⟨i,p.1,⟨p.2.1,p.2.2.1⟩⟩) (ih p.2.2.2)
private theorem edges_inj {n : ℕ} {A : GroupMat H n n} :
    ∀ {d : ℕ} {i j : Fin n} (p q : Word A d i j), edges d p = edges d q → p=q := by
  intro d
  induction d with
  | zero =>
    intro i j p q h
    rcases p with ⟨⟨v,hvi,hvj⟩⟩
    rcases q with ⟨⟨w,hwi,hwj⟩⟩
    subst v; subst w; rfl
  | succ d ih =>
    intro i j p q h
    rcases p with ⟨v,g,a,p⟩
    rcases q with ⟨w,k,b,q⟩
    have hh := (List.cons.inj h).1
    have hv : v=w := congrArg (fun x : E A => x.2.1) hh
    subst w
    have hmid : (⟨v,⟨g,a⟩⟩ : Σ x : Fin n, At A i x) = ⟨v,⟨k,b⟩⟩ :=
      eq_of_heq (Sigma.mk.inj hh).2
    have he : (⟨g,a⟩ : At A i v) = ⟨k,b⟩ := eq_of_heq (Sigma.mk.inj hmid).2
    cases he
    have hp := ih p q (List.cons.inj h).2
    cases hp
    rfl
abbrev Split {n : ℕ} (A : GroupMat H n n) (d e : ℕ) (i w : Fin n) :=
  Σ j : Fin n, Word A d i j × Word A e j w
def cut {n : ℕ} {A : GroupMat H n n} :
    (d e : ℕ) → {i w : Fin n} → Word A (d+e) i w → Split A d e i w
  | 0,e,i,_,p => ⟨i,nilPath i,wc (Nat.zero_add e) p⟩
  | d+1,e,_,_,p =>
    let t := wc (Nat.succ_add d e) p
    let q := cut d e t.2.2.2
    ⟨q.1,⟨t.1,t.2.1,t.2.2.1,q.2.1⟩,q.2.2⟩
private theorem edges_cut {n : ℕ} {A : GroupMat H n n}
    (d e : ℕ) {i w : Fin n} (p : Word A (d+e) i w) :
    edges d (cut d e p).2.1 ++ edges e (cut d e p).2.2 = edges (d+e) p := by
  induction d generalizing i with
  | zero => simp only [cut,edges,List.nil_append,edges_wc]
  | succ d ih =>
    let t := wc (Nat.succ_add d e) p
    have ht : edges (d+1+e) p =
      (⟨i,t.1,⟨t.2.1,t.2.2.1⟩⟩ : E A) :: edges (d+e) t.2.2.2 := by
      exact (edges_wc (Nat.succ_add d e) p).symm
    change (⟨i,t.1,⟨t.2.1,t.2.2.1⟩⟩ : E A) ::
      (edges d (cut d e t.2.2.2).2.1 ++ edges e (cut d e t.2.2.2).2.2) = _
    rw [ih]
    exact ht.symm
private def repeatWord {n : ℕ} {A : GroupMat H n n} (i : Fin n) (a : At A i i) :
    (d : ℕ) → Word A d i i
  | 0 => nilPath i
  | d+1 => ⟨i,a.1,a.2,repeatWord i a d⟩
abbrev Pair {n m k : ℕ} (A : GroupMat H n m) (B : GroupMat H m k)
    (i : Fin n) (w : Fin k) := Σ j : Fin m, At A i j × At B j w
def sweep {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} (phi : ∀ i z, Pair A T i z ≃ Pair T B i z) :
    (d : ℕ) → (i : Fin n) → (z : Fin m) →
      (Σ j : Fin n, Word A d i j × At T j z) →
      Σ y : Fin m, At T i y × Word B d y z
  | 0,i,z,⟨j,⟨⟨v,hvi,hvj⟩⟩,r⟩ => by subst v; subst j; exact ⟨z,r,nilPath z⟩
  | d+1,i,z,⟨j,alpha,r⟩ =>
    let q := sweep phi d alpha.1 z ⟨j,alpha.2.2.2,r⟩
    let p := phi i q.1 ⟨alpha.1,⟨alpha.2.1,alpha.2.2.1⟩,q.2.1⟩
    ⟨p.1,p.2.1,⟨q.1,p.2.2.1,p.2.2.2,q.2.2⟩⟩
-- A full endpoint-preserving record. The two cuts and every original edge remain data.
structure FlatOut {n m : ℕ} (A : GroupMat H n n)
    (T : GroupMat H n m) (U : GroupMat H m n) (d : ℕ) (i w : Fin n) where
  vertex : Fin n
  middle : Fin m
  left : At T i middle
  right : At U middle vertex
  word : Word A d vertex w

structure FlatCell {n m : ℕ} (A : GroupMat H n n)
    (T : GroupMat H n m) (U : GroupMat H m n) (i w : Fin n) where
  vertex : Fin n
  middle : Fin m
  left : At T i middle
  right : At U middle vertex
  edge : At A vertex w

def square {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    {i j w : Fin n} (a : At A i j) (rs : Pair T U j w) : FlatCell A T U i w :=
  let p := phi i rs.1 ⟨j,a,rs.2.1⟩
  let q := chi p.1 w ⟨rs.1,p.2.2,rs.2.2⟩
  ⟨q.1,p.1,p.2.1,q.2.1,q.2.2⟩

def attach {n m d : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n} {i v w : Fin n}
    (p : FlatCell A T U i v) (alpha : Word A d v w) : FlatOut A T U (d+1) i w :=
  ⟨p.vertex,p.middle,p.left,p.right,⟨v,p.edge.1,p.edge.2,alpha⟩⟩

-- Legal fibre products only: no operation or default on incompatible inputs.
def flatRun {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w) :
    (d : ℕ) → {i j w : Fin n} → Word A d i j → Pair T U j w → FlatOut A T U d i w
  | 0,_,_,_,⟨⟨v,hvi,hvj⟩⟩,rs => by
      subst v; subst_vars
      exact ⟨_,rs.1,rs.2.1,rs.2.2,nilPath _⟩
  | d+1,_,_,_,p,rs =>
      let t := flatRun phi chi d p.2.2.2 rs
      attach (square phi chi ⟨p.2.1,p.2.2.1⟩ ⟨t.middle,t.left,t.right⟩) t.word

def flatDouble {n m d : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    {i j w : Fin n} (alpha : Word A d i j) (rs : Pair T U j w) : FlatOut A T U d i w :=
  let p := sweep phi d i rs.1 ⟨j,alpha,rs.2.1⟩
  let q := sweep chi d p.1 w ⟨rs.1,p.2.2,rs.2.2⟩
  ⟨q.1,p.1,p.2.1,q.2.1,q.2.2⟩

-- Independent front and back fibre-product operations exchange; all shared endpoints stay fixed.
theorem run_path {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w) :
    ∀ (d : ℕ) {i j w : Fin n} (alpha : Word A d i j) (rs : Pair T U j w),
    flatRun phi chi d alpha rs = flatDouble phi chi alpha rs := by
  intro d
  induction d with
  | zero =>
      intro i j w alpha rs
      rcases alpha with ⟨⟨v,hvi,hvj⟩⟩
      subst v; subst j
      rfl
  | succ d ih =>
      intro i j w alpha rs
      rcases alpha with ⟨v,g,a,alpha⟩
      rcases rs with ⟨z,r,s⟩
      let first := sweep phi d v z ⟨j,alpha,r⟩
      let second := sweep chi d first.1 w ⟨z,first.2.2,s⟩
      have ht := ih alpha (⟨z,r,s⟩ : Pair T U j w)
      change attach (square phi chi ⟨g,a⟩
        ⟨(flatRun phi chi d alpha ⟨z,r,s⟩).middle,
          (flatRun phi chi d alpha ⟨z,r,s⟩).left,
          (flatRun phi chi d alpha ⟨z,r,s⟩).right⟩)
        (flatRun phi chi d alpha ⟨z,r,s⟩).word = _
      refine (congrArg (fun t : FlatOut A T U d v w =>
        attach (square phi chi ⟨g,a⟩ ⟨t.middle,t.left,t.right⟩) t.word) ht).trans ?_
      rfl

def concat {n : ℕ} {A : GroupMat H n n} :
    (d e : ℕ) → {i j w : Fin n} → Word A d i j → Word A e j w → Word A (d+e) i w
  | 0,e,_,_,_,⟨⟨v,hvi,hvj⟩⟩,q => by subst v; subst_vars; exact wc (Nat.zero_add e).symm q
  | d+1,e,_,_,_,p,q => wc (Nat.succ_add d e).symm
      ⟨p.1,p.2.1,p.2.2.1,concat d e p.2.2.2 q⟩

private theorem edges_concat {n : ℕ} {A : GroupMat H n n}
    (d e : ℕ) {i j w : Fin n} (p : Word A d i j) (q : Word A e j w) :
    edges (d+e) (concat d e p q) = edges d p ++ edges e q := by
  induction d generalizing i with
  | zero => rcases p with ⟨⟨v,hvi,hvj⟩⟩; subst v; subst j; exact edges_wc _ q
  | succ d ih =>
      rw [concat,edges_wc]
      exact congrArg (List.cons (⟨i,p.1,⟨p.2.1,p.2.2.1⟩⟩ : E A)) (ih p.2.2.2)

private theorem split_inj {n : ℕ} {A : GroupMat H n n} (d e : ℕ)
    {i w : Fin n} (x y : Split A d e i w)
    (h : edges d x.2.1 ++ edges e x.2.2 = edges d y.2.1 ++ edges e y.2.2) : x=y := by
  induction d generalizing i with
  | zero =>
      rcases x with ⟨v,⟨⟨t,hti,htv⟩⟩,q⟩
      rcases y with ⟨v',⟨⟨t',ht'i,ht'v⟩⟩,q'⟩
      subst t; subst v; subst t'; subst v'
      exact congrArg (fun z => (⟨i,nilPath i,z⟩ : Split A 0 e i w)) (edges_inj q q' h)
  | succ d ih =>
      rcases x with ⟨v,⟨j,g,a,p⟩,q⟩
      rcases y with ⟨v',⟨j',g',a',p'⟩,q'⟩
      have hh := (List.cons.inj h).1
      have hj : j=j' := congrArg (fun e : E A => e.2.1) hh
      subst j'
      have he : (⟨g,a⟩ : At A i j)=⟨g',a'⟩ :=
        eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hh).2)).2
      cases he
      exact congrArg (fun x : Split A d e j w =>
        (⟨x.1,⟨j,g,a,x.2.1⟩,x.2.2⟩ : Split A (d+1) e i w))
          (ih ⟨v,p,q⟩ ⟨v',p',q'⟩ (List.cons.inj h).2)

def concatEquiv {n : ℕ} (A : GroupMat H n n) (d e : ℕ) (i w : Fin n) :
    Split A d e i w ≃ Word A (d+e) i w where
  toFun p := concat d e p.2.1 p.2.2
  invFun := cut d e
  left_inv p := split_inj d e _ _ ((edges_cut d e _).trans (edges_concat d e p.2.1 p.2.2))
  right_inv p := edges_inj _ _ ((edges_concat d e _ _).trans (edges_cut d e p))

def pairRecord {n m L : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (d : ℕ) (i w : Fin n) :
    FlatOut A T U d i w ≃ Split A L d i w where
  toFun p := ⟨p.vertex,psi i p.vertex ⟨p.middle,p.left,p.right⟩,p.word⟩
  invFun p := let q := (psi i p.1).symm p.2.1
    ⟨p.1,q.1,q.2.1,q.2.2,p.2.2⟩
  left_inv := by
    rintro ⟨v,z,r,s,gamma⟩
    change (let q := (psi i v).symm (psi i v ⟨z,r,s⟩);
      FlatOut.mk v q.1 q.2.1 q.2.2 gamma) = _
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨v,alpha,gamma⟩
    change (⟨v,psi i v ((psi i v).symm alpha),gamma⟩ : Split A L d i w) = _
    rw [Equiv.apply_symm_apply]

def encoding {n m L : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (d : ℕ) (i w : Fin n) :
    FlatOut A T U d i w ≃ Word A (L+d) i w :=
  (pairRecord psi d i w).trans (concatEquiv A L d i w)

theorem exact_fixed_cut {n m L d : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (i w : Fin n)
    (p : FlatOut A T U d i w) : (encoding psi d i w).symm (encoding psi d i w p) = p :=
  (encoding psi d i w).symm_apply_apply p


-- This partial computational view is defined only on legal endpoint matches.
-- None is failure of a match, never a replacement edge or boundary.
private abbrev Boundary {n m : ℕ} (T : GroupMat H n m) (U : GroupMat H m n) :=
  Σ i : Fin n, Σ w : Fin n, Pair T U i w
private def view {n m d : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n} {i w : Fin n}
    (p : FlatOut A T U d i w) : Boundary T U × List (E A) :=
  (⟨i,p.vertex,p.middle,p.left,p.right⟩,edges d p.word)
private def partialCell {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (a : E A) (q : Boundary T U) : Option (Boundary T U × E A) := by
  classical
  by_cases h : a.2.1 = q.1
  · let rs : Pair T U a.2.1 q.2.1 := h.symm ▸ q.2.2
    let p := square phi chi a.2.2 rs
    exact some (⟨a.1,p.vertex,p.middle,p.left,p.right⟩,⟨p.vertex,q.2.1,p.edge⟩)
  · exact none
private theorem partialCell_typed {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    {i j w : Fin n} (a : At A i j) (rs : Pair T U j w) :
    partialCell phi chi ⟨i,j,a⟩ ⟨j,w,rs⟩ =
      some (let p := square phi chi a rs
        (⟨i,p.vertex,p.middle,p.left,p.right⟩,⟨p.vertex,w,p.edge⟩)) := by
  unfold partialCell
  rw [dif_pos rfl]
private def partialRun {X Q : Type u} (f : X → Q → Option (Q × X)) :
    List X → Q → Option (Q × List X)
  | [],q => some (q,[])
  | a::l,q => match partialRun f l q with
      | none => none
      | some t => match f a t.1 with
        | none => none
        | some p => some (p.1,p.2::t.2)
private theorem partialRun_append {X Q : Type u} (f : X → Q → Option (Q × X))
    (l r : List X) (q : Q) : partialRun f (l++r) q =
      (match partialRun f r q with
       | none => none
       | some t => match partialRun f l t.1 with
         | none => none
         | some p => some (p.1,p.2++t.2)) := by
  induction l with
  | nil =>
    simp only [List.nil_append,partialRun]
    cases partialRun f r q <;> rfl
  | cons a l ih =>
    simp only [List.cons_append,partialRun,ih]
    cases hr : partialRun f r q with
    | none => rfl
    | some t =>
      simp only
      cases hl : partialRun f l t.1 with
      | none => rfl
      | some p =>
        simp only
        cases hf : f a p.1 <;> rfl
private theorem partialRun_flat {n m : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w) :
    ∀ (d : ℕ) {i j w : Fin n} (alpha : Word A d i j) (rs : Pair T U j w),
    partialRun (partialCell phi chi) (edges d alpha) ⟨j,w,rs⟩ =
      some (view (flatRun phi chi d alpha rs)) := by
  intro d
  induction d with
  | zero =>
    intro i j w alpha rs
    rcases alpha with ⟨⟨v,hvi,hvj⟩⟩
    subst v; subst j
    rfl
  | succ d ih =>
    intro i j w alpha rs
    rcases alpha with ⟨v,g,a,alpha⟩
    simp only [edges,partialRun,ih]
    simp only [view]
    rw [partialCell_typed]
    rfl
private def code {n m L : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (q : Boundary T U) : List (E A) :=
  edges L (psi q.1 q.2.1 q.2.2)
abbrev FlatBalanced {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) :=
  ∀ {i j w : Fin n} (alpha : Word A L i j) (rs : Pair T U j w),
    flatRun phi chi L alpha rs =
      (let p := (psi i j).symm alpha
       ⟨j,p.1,p.2.1,p.2.2,psi j w rs⟩)
private theorem partialRun_balanced {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (hb : FlatBalanced phi chi psi)
    {i j w : Fin n} (alpha : Word A L i j) (rs : Pair T U j w) :
    partialRun (partialCell phi chi) (edges L alpha) ⟨j,w,rs⟩ =
      some (⟨i,j,(psi i j).symm alpha⟩,code psi ⟨j,w,rs⟩) := by
  rw [partialRun_flat,hb]
  rfl
private theorem partialRun_prefix {n m L d : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (hb : FlatBalanced phi chi psi)
    {i j v w : Fin n} (alpha : Word A L i j) (beta : Word A d j v)
    (rs : Pair T U v w) (q' : Boundary T U) (out : List (E A))
    (h : partialRun (partialCell phi chi) (edges L alpha ++ edges d beta) ⟨v,w,rs⟩ =
      some (q',out)) : code psi q' = edges L alpha := by
  rw [partialRun_append,partialRun_flat] at h
  simp only [view] at h
  rw [partialRun_balanced phi chi psi hb] at h
  have ht := congrArg (fun x : Boundary T U × List (E A) => code psi x.1)
    (Option.some.inj h)
  simpa only [code,Equiv.apply_symm_apply] using ht.symm
abbrev Aligned {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) :=
  ∀ (i j w : Fin n) (z : Fin m) (a : At A i j) (r : At T j z) (s : At U z w),
    let p := phi i z ⟨j,a,r⟩
    let q := chi p.1 w ⟨z,p.2.2,s⟩
    app L (psi i q.1 ⟨p.1,p.2.1,q.2.1⟩) q.2.2 =
      (⟨j,a.1,a.2,psi j w ⟨z,r,s⟩⟩ : Word A (L+1) i w)
theorem finite_overlap {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (hb : FlatBalanced phi chi psi)
    (hL : 0<L) (hloop : ∀ i : Fin n, Nonempty (At A i i)) : Aligned phi chi psi := by
  classical
  intro i j w z a r s
  let f := partialCell phi chi
  let q : Boundary T U := ⟨j,w,z,r,s⟩
  let e : E A := ⟨i,j,a⟩
  let cell := square phi chi a (⟨z,r,s⟩ : Pair T U j w)
  let q1 : Boundary T U := ⟨i,cell.vertex,cell.middle,cell.left,cell.right⟩
  let e1 : E A := ⟨cell.vertex,w,cell.edge⟩
  have hcell : f e q = some (q1,e1) := partialCell_typed phi chi a ⟨z,r,s⟩
  let alpha := psi j w ⟨z,r,s⟩
  let beta := repeatWord w (Classical.choice (hloop w)) L
  let rs := (psi w w).symm beta
  let q2 : Boundary T U := ⟨w,w,rs⟩
  let p : Word A (L+1) i w := ⟨j,a.1,a.2,alpha⟩
  let parts := cut L 1 p
  have hsplit := edges_cut L 1 p
  have hr : partialRun f (edges L alpha) q2 = some (q,edges L beta) := by
    simpa only [f,q2,rs,alpha,q,code,Equiv.symm_apply_apply,Equiv.apply_symm_apply] using
      partialRun_balanced phi chi psi hb alpha rs
  have hlong : partialRun f (edges L parts.2.1 ++ edges 1 parts.2.2) q2 =
      some (q1,e1::edges L beta) := by
    rw [hsplit]
    change partialRun f (e::edges L alpha) q2 = _
    simp only [partialRun,hr]
    rw [hcell]
  have hstate : code psi q1 = edges L parts.2.1 :=
    partialRun_prefix phi chi psi hb parts.2.1 parts.2.2 rs q1 _ hlong
  let eta := repeatWord i (Classical.choice (hloop i)) (L-1)
  let p0 : Word A L i j := wc (show L-1+1=L by omega) (app (L-1) eta a)
  let out := flatRun phi chi (L-1) eta (⟨cell.middle,cell.left,cell.right⟩ :
    Pair T U i cell.vertex)
  let pre := edges (L-1) out.word
  have hp0 : partialRun f (edges L p0) q =
      some ((view out).1,pre++[e1]) := by
    rw [show edges L p0 = edges (L-1) eta ++ [e] by rw [edges_wc,edges_app]]
    rw [partialRun_append]
    have hone : partialRun f [e] q = some (q1,[e1]) := by
      simp only [partialRun]
      rw [hcell]
    rw [hone]
    simp only [view]
    rw [partialRun_flat]
    rfl
  have hcode : code psi q = pre++[e1] := by
    have h := (partialRun_balanced phi chi psi hb p0 ⟨z,r,s⟩).symm.trans hp0
    exact (congrArg Prod.snd (Option.some.inj h))
  have hlen : pre.length = L-1 := edges_len out.word
  have hfirst : (edges L parts.2.1).length=L := edges_len _
  have hpref : edges L parts.2.1 = e::pre := by
    have h := congrArg (List.take L) hsplit
    change List.take L (edges L parts.2.1 ++ edges 1 parts.2.2) =
      List.take L (e::code psi q) at h
    have hl : List.take L (edges L parts.2.1 ++ edges 1 parts.2.2) = edges L parts.2.1 := by
      have htake : ∀ (l r : List (E A)), List.take l.length (l++r)=l := by
        intro l r
        rw [List.take_append,Nat.sub_self,List.take_length,List.take_zero,List.append_nil]
      simpa only [hfirst] using htake (edges L parts.2.1) (edges 1 parts.2.2)
    have hr' : List.take L (e::code psi q) = e::pre := by
      rw [hcode,← List.cons_append]
      have hm : (e::pre).length=L := by simp only [List.length_cons,hlen]; omega
      rw [← hm,List.take_append,Nat.sub_self,List.take_length,List.take_zero,List.append_nil]
    exact hl.symm.trans (h.trans hr')
  have hlocal : code psi q1 ++ [e1] = e::code psi q := by
    rw [hstate,hpref,hcode]
    rfl
  apply edges_inj
  rw [edges_app]
  exact hlocal

private theorem full_word_invariant {n m L : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (ha : Aligned phi chi psi) :
    ∀ (d : ℕ) {i j w : Fin n} (alpha : Word A d i j) (rs : Pair T U j w),
    let out := flatRun phi chi d alpha rs
    edges L (psi i out.vertex ⟨out.middle,out.left,out.right⟩) ++ edges d out.word =
      edges d alpha ++ edges L (psi j w rs) := by
  intro d
  induction d with
  | zero =>
    intro i j w alpha rs
    rcases alpha with ⟨⟨v,hvi,hvj⟩⟩
    subst v; subst j
    exact List.append_nil _
  | succ d ih =>
    intro i j w alpha rs
    rcases alpha with ⟨v,g,a,alpha⟩
    let tail := flatRun phi chi d alpha rs
    let p := square phi chi (⟨g,a⟩ : At A i v) ⟨tail.middle,tail.left,tail.right⟩
    have hlocal : edges L (psi i p.vertex ⟨p.middle,p.left,p.right⟩) ++
        [(⟨p.vertex,tail.vertex,p.edge⟩ : E A)] =
        (⟨i,v,⟨g,a⟩⟩ : E A)::edges L (psi v tail.vertex ⟨tail.middle,tail.left,tail.right⟩) := by
      have h := congrArg (edges (A:=A) (L+1))
        (ha i v tail.vertex tail.middle ⟨g,a⟩ tail.left tail.right)
      change edges (A:=A) (L+1) (app L (psi i p.vertex ⟨p.middle,p.left,p.right⟩) p.edge) =
        edges (A:=A) (L+1) (⟨v,g,a,psi v tail.vertex ⟨tail.middle,tail.left,tail.right⟩⟩ :
          Word A (L+1) i tail.vertex) at h
      rw [edges_app] at h
      exact h
    change edges L (psi i p.vertex ⟨p.middle,p.left,p.right⟩) ++
      ((⟨p.vertex,tail.vertex,p.edge⟩ : E A)::edges d tail.word) =
      (⟨i,v,⟨g,a⟩⟩ : E A)::(edges d alpha ++ edges L (psi j w rs))
    calc
      _ = (edges L (psi i p.vertex ⟨p.middle,p.left,p.right⟩) ++
          [(⟨p.vertex,tail.vertex,p.edge⟩ : E A)]) ++ edges d tail.word := by
        rw [List.append_assoc]; rfl
      _ = ((⟨i,v,⟨g,a⟩⟩ : E A)::
          edges L (psi v tail.vertex ⟨tail.middle,tail.left,tail.right⟩)) ++ edges d tail.word :=
        congrArg (fun x => x ++ edges d tail.word) hlocal
      _ = (⟨i,v,⟨g,a⟩⟩ : E A)::(edges d alpha ++ edges L (psi j w rs)) :=
        congrArg (List.cons (⟨i,v,⟨g,a⟩⟩ : E A)) (ih alpha rs)
abbrev FlatInput {n m : ℕ} (A : GroupMat H n n)
    (T : GroupMat H n m) (U : GroupMat H m n) (d : ℕ) (i w : Fin n) :=
  Σ j : Fin n, Word A d i j × Pair T U j w
private def wordLengthEquiv {n d e : ℕ} {A : GroupMat H n n} (h : d=e)
    (i w : Fin n) : Word A d i w ≃ Word A e i w where
  toFun := wc h
  invFun := wc h.symm
  left_inv p := by cases h; rfl
  right_inv p := by cases h; rfl
def inputEncoding {n m L : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (d : ℕ) (i w : Fin n) :
    FlatInput A T U d i w ≃ Word A (L+d) i w :=
  ((Equiv.sigmaCongrRight fun j : Fin n =>
    Equiv.prodCongr (Equiv.refl (Word A d i j)) (psi j w)).trans
      (concatEquiv A d L i w)).trans
        (wordLengthEquiv (Nat.add_comm d L) i w)
private theorem inputEncoding_edges {n m L d : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) {i w : Fin n}
    (p : FlatInput A T U d i w) :
    edges (L+d) (inputEncoding psi d i w p) =
      edges d p.2.1 ++ edges L (psi p.1 w p.2.2) := by
  change edges (L+d) (wc (Nat.add_comm d L) (concat d L p.2.1 (psi p.1 w p.2.2))) = _
  rw [edges_wc,edges_concat]
def fixedCutDouble {n m L : ℕ} {A : GroupMat H n n}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (d : ℕ) (i w : Fin n) :
    FlatInput A T U d i w ≃ FlatOut A T U d i w :=
  (inputEncoding psi d i w).trans (encoding psi d i w).symm
theorem full_overlap {n m L d : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (ha : Aligned phi chi psi)
    {i w : Fin n} (p : FlatInput A T U d i w) :
    flatDouble phi chi p.2.1 p.2.2 = fixedCutDouble psi d i w p := by
  rw [← run_path]
  apply (encoding psi d i w).injective
  change encoding psi d i w (flatRun phi chi d p.2.1 p.2.2) =
    encoding psi d i w ((encoding psi d i w).symm (inputEncoding psi d i w p))
  rw [Equiv.apply_symm_apply]
  apply edges_inj
  rw [inputEncoding_edges]
  change edges (L+d) (concat L d _ _) = _
  rw [edges_concat]
  exact full_word_invariant phi chi psi ha d p.2.1 p.2.2
theorem full_inverse_coherence {n m L d : ℕ} {A : GroupMat H n n} {B : GroupMat H m m}
    {T : GroupMat H n m} {U : GroupMat H m n}
    (phi : ∀ i z, Pair A T i z ≃ Pair T B i z)
    (chi : ∀ z w, Pair B U z w ≃ Pair U A z w)
    (psi : ∀ i w, Pair T U i w ≃ Word A L i w) (ha : Aligned phi chi psi)
    (i w : Fin n) :
    (∀ p : FlatInput A T U d i w,
      (fixedCutDouble psi d i w).symm (flatDouble phi chi p.2.1 p.2.2) = p) ∧
    (∀ out : FlatOut A T U d i w,
      let p := (fixedCutDouble psi d i w).symm out
      flatDouble phi chi p.2.1 p.2.2 = out) := by
  constructor
  · intro p
    rw [full_overlap phi chi psi ha,Equiv.symm_apply_apply]
  · intro out
    dsimp only
    rw [full_overlap phi chi psi ha,Equiv.apply_symm_apply]

open FixedPositivePartitionSseDistance InvolutionUniformExchange
def T (n t : ℕ) : Mat ℕ n n :=
  Matrix.of fun i j => if i.val+1=j.val ∧ i.val<t-1 then 1 else 0
def D (n t : ℕ) : Mat ℕ n n :=
  Matrix.diagonal (fun i : Fin n => if i.val<t-1 then 1 else 0)
private theorem D_entry (n t : ℕ) (i j : Fin n) :
    D n t i j = if i=j ∧ i.val<t-1 then 1 else 0 := by
  classical
  by_cases h : i=j <;> simp [D,Matrix.diagonal_apply,h]
private theorem DT (n t : ℕ) : D n t * T n t = T n t := by
  classical
  ext i j
  simp only [D,Matrix.diagonal_mul,T,Matrix.of_apply]
  split_ifs <;> omega
private theorem TD (n t : ℕ) : T n t * D n t = T n (t-1) := by
  classical
  ext i j
  simp only [D,Matrix.mul_diagonal,T,Matrix.of_apply]
  split_ifs <;> omega
def actualU (n t : ℕ) : GroupMat H n n := Matrix.of fun i j =>
  toNat (Fintype.card H • uniform H + D n t i j •
    (Fintype.card H • (1 : MonoidAlgebra ℤ H)-uniform H))
def actualV (n t : ℕ) : GroupMat H n n := Matrix.of fun i j =>
  toNat (Fintype.card H • uniform H + T n t i j •
    (Fintype.card H • (1 : MonoidAlgebra ℤ H)-uniform H))
def actualAt (n t : ℕ) : GroupMat H n n := Matrix.of fun i j =>
  toNat ((Fintype.card H^3*n) • uniform H + (Fintype.card H*T n t i j) •
    (Fintype.card H • (1 : MonoidAlgebra ℤ H)-uniform H))
theorem factorPositive [Nontrivial H] (n t : ℕ) :
    (∀ i j g, 0 < (actualU (H:=H) n t i j).coeff g) ∧
      (∀ i j g, 0 < (actualV (H:=H) n t i j).coeff g) := by
  classical
  have hD (i j : Fin n) : D n t i j ≤ 1 := by rw [D_entry]; split_ifs <;> omega
  have hT (i j : Fin n) : T n t i j ≤ 1 := by simp only [T,Matrix.of_apply]; split_ifs <;> omega
  constructor
  · intro i j g
    exact Int.pos_iff_toNat_pos.mp (uniform_perturbation_positive H _ (hD i j) g)
  · intro i j g
    exact Int.pos_iff_toNat_pos.mp (uniform_perturbation_positive H _ (hT i j) g)
theorem prescribedProducts [Nontrivial H] (n t : ℕ) :
    actualU (H:=H) n t * actualV n t = actualAt n t ∧
      actualV (H:=H) n t * actualU n t = actualAt n (t-1) := by
  classical
  let q := Fintype.card H
  let z : MonoidAlgebra ℤ H := q • 1 - uniform H
  let UZ : Mat (MonoidAlgebra ℤ H) n n := Matrix.of fun i j => q • uniform H + D n t i j • z
  let VZ : Mat (MonoidAlgebra ℤ H) n n := Matrix.of fun i j => q • uniform H + T n t i j • z
  have lift_toNat (x : MonoidAlgebra ℤ H) (hx : ∀ g, 0 ≤ x.coeff g) :
      liftNat H (toNat x)=x := by ext g; simp [liftNat,toNat,Int.toNat_of_nonneg (hx g)]
  have toNat_lift (x : MonoidAlgebra ℕ H) : toNat (liftNat H x)=x := by
    ext g; simp [liftNat,toNat]
  have hU : (actualU (H:=H) n t).map (liftNat H)=UZ := by
    apply Matrix.ext
    intro i j
    change liftNat H (toNat _) = _
    apply lift_toNat
    intro g
    apply (uniform_perturbation_positive H _ _ g).le
    rw [D_entry]; split_ifs <;> omega
  have hV : (actualV (H:=H) n t).map (liftNat H)=VZ := by
    apply Matrix.ext
    intro i j
    change liftNat H (toNat _) = _
    apply lift_toNat
    intro g
    apply (uniform_perturbation_positive H _ _ g).le
    simp only [T,Matrix.of_apply]; split_ifs <;> omega
  have mulmap (X Y : GroupMat H n n) :
      (X*Y).map (liftNat H)=X.map (liftNat H)*Y.map (liftNat H) := by
    ext i j
    simp [Matrix.mul_apply,map_sum,map_mul]
  constructor
  · have hz : (actualU (H:=H) n t * actualV n t).map (liftNat H) =
        (Matrix.of fun i j => (q^3*n) • uniform H + (q*T n t i j) • z) := by
      rw [mulmap,hU,hV]
      have h := uniform_perturbation_product H n (D n t) (T n t)
      apply Matrix.ext
      intro i j
      simpa only [UZ,VZ,q,z,DT,Matrix.of_apply] using congrFun (congrFun h i) j
    have hh := congrArg (fun X : Mat (MonoidAlgebra ℤ H) n n => fun i j => toNat (X i j)) hz
    apply Matrix.ext
    intro i j
    have hij := congrFun (congrFun hh i) j
    simpa only [Matrix.map_apply,Matrix.of_apply,toNat_lift,actualAt,q,z] using hij
  · have hz : (actualV (H:=H) n t * actualU n t).map (liftNat H) =
        (Matrix.of fun i j => (q^3*n) • uniform H + (q*T n (t-1) i j) • z) := by
      rw [mulmap,hV,hU]
      have h := uniform_perturbation_product H n (T n t) (D n t)
      apply Matrix.ext
      intro i j
      simpa only [UZ,VZ,q,z,TD,Matrix.of_apply] using congrFun (congrFun h i) j
    have hh := congrArg (fun X : Mat (MonoidAlgebra ℤ H) n n => fun i j => toNat (X i j)) hz
    apply Matrix.ext
    intro i j
    have hij := congrFun (congrFun hh i) j
    simpa only [Matrix.map_apply,Matrix.of_apply,toNat_lift,actualAt,q,z] using hij
def down [Nontrivial H] (n r : ℕ) : (k : ℕ) →
    Chain H (actualAt (H:=H) n (r+k)) (actualAt n r) k
  | 0 => .nil (actualAt n r)
  | k+1 => .cons (actualU n (r+k+1)) (actualV n (r+k+1))
      (by simpa only [Nat.add_assoc] using (prescribedProducts (H:=H) n (r+k+1)).1.symm)
      (by simpa only [Nat.add_sub_cancel] using (prescribedProducts (H:=H) n (r+k+1)).2.symm)
      (down n r k)
def up [Nontrivial H] (n r : ℕ) : (k : ℕ) →
    Chain H (actualAt (H:=H) n r) (actualAt n (r+k)) k
  | 0 => .nil (actualAt n r)
  | k+1 => by
    have tail := up n (r+1) k
    have hstart := (prescribedProducts (H:=H) n (r+1)).2.symm
    have hend := (prescribedProducts (H:=H) n (r+1)).1.symm
    exact (by simpa only [Nat.add_sub_cancel,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Chain.cons (actualV n (r+1)) (actualU n (r+1)) hstart hend tail)
def prescribedChain [Nontrivial H] (n t r : ℕ) :
    Chain H (actualAt (H:=H) n t) (actualAt n r) (Nat.dist t r) := by
  by_cases h : t≤r
  · have c := up (H:=H) n t (r-t)
    simpa only [Nat.add_sub_of_le h,Nat.dist,Nat.sub_eq_zero_of_le h,Nat.zero_add] using c
  · have h' : r≤t := by omega
    have c := down (H:=H) n r (t-r)
    simpa only [Nat.add_sub_of_le h',Nat.dist,Nat.sub_eq_zero_of_le h',Nat.add_zero] using c
private theorem dependent_app_heq {α : Sort u} {β : α → Sort _}
    (f : ∀ x, β x) {a b : α} (h : a=b) : HEq (f a) (f b) := by cases h; rfl
theorem prescribedSelf [Nontrivial H] (n t : ℕ) :
    HEq (prescribedChain (H:=H) n t t) (Chain.nil (actualAt (H:=H) n t)) := by
  simp [prescribedChain,Nat.dist]
  exact dependent_app_heq (up (H:=H) n t) (Nat.sub_self t)

theorem actualLoops (n : ℕ) (hn : 0<n) (t : ℕ) (i : Fin n) :
    Nonempty (At (actualAt (H:=H) n t) i i) := by
  classical
  have hT : T n t i i = 0 := by
    simp only [T,Matrix.of_apply]
    split_ifs with h
    · omega
    · rfl
  refine ⟨⟨1,⟨0,?_⟩⟩⟩
  change 0 < (((Fintype.card H^3*n) • uniform H + (Fintype.card H*T n t i i) •
    (Fintype.card H • (1 : MonoidAlgebra ℤ H)-uniform H)).coeff (1:H)).toNat
  rw [hT,Nat.mul_zero,zero_smul,add_zero]
  have huc : (uniform H).coeff (1:H) = 1 := by
    simp [uniform,basis,MonoidAlgebra.coeff_sum]
  apply Int.pos_iff_toNat_pos.mp
  rw [MonoidAlgebra.coeff_smul_apply,huc]
  simp only [nsmul_eq_mul,mul_one]
  exact_mod_cast Nat.mul_pos (pow_pos (show 0 < Fintype.card H from Fintype.card_pos) 3) hn

/-- Coefficients of the literal original endpoint, before any factorization. -/
theorem actualAt_coefficient (n t : ℕ) (i j : Fin n) (g : H) :
    (actualAt (H:=H) n t i j).coeff g =
      (((Fintype.card H^3*n : ℕ) : ℤ) +
        ((Fintype.card H*T n t i j : ℕ) : ℤ) *
          ((Fintype.card H : ℤ) * (if (1:H)=g then 1 else 0) - 1)).toNat := by
  classical
  have huc : (uniform H).coeff g = 1 := by
    simp [uniform,basis,MonoidAlgebra.coeff_sum]
  have hsm (k : ℕ) (x : MonoidAlgebra ℤ H) :
      (k • x).coeff g = (k : ℤ) * x.coeff g := by
    rw [MonoidAlgebra.coeff_smul_apply]
    exact nsmul_eq_mul k (x.coeff g)
  change (((Fintype.card H^3*n) • uniform H + (Fintype.card H*T n t i j) •
    (Fintype.card H • (1 : MonoidAlgebra ℤ H)-uniform H)).coeff g).toNat = _
  congr 1
  simp only [MonoidAlgebra.coeff_add,Finsupp.add_apply,hsm,MonoidAlgebra.coeff_sub,
    Finsupp.sub_apply,huc,MonoidAlgebra.one_def,MonoidAlgebra.coeff_single,
    Finsupp.single_apply,mul_one]
/-- Every coordinate and every H-labelled copy fibre is positive. -/
theorem actualAt_positive [Nontrivial H] (n t : ℕ) (hn : 2≤n) :
    ∀ i j g, 0 < (actualAt (H:=H) n t i j).coeff g := by
  classical
  intro i j g
  rw [actualAt_coefficient]
  apply Int.pos_iff_toNat_pos.mp
  let q := Fintype.card H
  have hq : 2≤q := Fintype.one_lt_card
  have hp : 0<q^3 := pow_pos (show 0<q by omega) 3
  have hle : q≤q^3 := by
    have hh : 1≤q*q := by nlinarith
    have h := Nat.mul_le_mul_left q hh
    simpa only [Nat.mul_one,show q*(q*q)=q^3 by ring] using h
  have hmul : q^3<q^3*n := by
    simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left (show 1<n by omega) hp
  have hc : (q : ℤ) < ((q^3*n : ℕ) : ℤ) := by exact_mod_cast (lt_of_le_of_lt hle hmul)
  have hqi : (2 : ℤ)≤q := by exact_mod_cast hq
  have hT : T n t i j = 0 ∨ T n t i j = 1 := by
    simp only [T,Matrix.of_apply]; split_ifs <;> simp
  change 0 < ((q^3*n : ℕ) : ℤ) + ((q*T n t i j : ℕ) : ℤ) *
    ((q : ℤ) * (if (1:H)=g then 1 else 0) - 1)
  by_cases hg : (1:H)=g
  · rw [if_pos hg]
    rcases hT with hz | ho
    · rw [hz]; simp only [Nat.mul_zero,Nat.cast_zero,zero_mul,add_zero]; omega
    · rw [ho]; simp only [Nat.mul_one,mul_one]; nlinarith
  · rw [if_neg hg]
    rcases hT with hz | ho
    · rw [hz]; simp only [Nat.mul_zero,Nat.cast_zero,zero_mul,add_zero]; omega
    · rw [ho]; simp only [Nat.mul_one,mul_zero,zero_sub,mul_neg,mul_one]; omega

open InertGroupBlockConjugacy
private def suppressAugmentation : (ℚ × Reduced H) →ₙ+* (ℚ × Reduced H) where
  toFun x := (0,x.2)
  map_zero' := rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp
/-- The actual rational nonunital homomorphism removing the uniform summand. -/
def rationalComplement (H : Type u) [Group H] [Fintype H] :
    MonoidAlgebra ℚ H →ₙ+* MonoidAlgebra ℚ H :=
  (augmentationSplit H).symm.toRingHom.toNonUnitalRingHom.comp
    (suppressAugmentation.comp (augmentationSplit H).toRingHom.toNonUnitalRingHom)
private theorem rationalComplement_split (x : MonoidAlgebra ℚ H) :
    augmentationSplit H (rationalComplement H x) = (0,(augmentationSplit H x).2) := by
  change augmentationSplit H ((augmentationSplit H).symm (0,(augmentationSplit H x).2)) = _
  exact (augmentationSplit H).apply_symm_apply _
/-- This identifies the nonunital homomorphism with the original complement formula. -/
theorem rationalComplement_apply (x : MonoidAlgebra ℚ H) :
    rationalComplement H x = x - rationalAugmentation x • average H := by
  apply (augmentationSplit H).injective
  rw [rationalComplement_split]
  apply Prod.ext
  · change 0 = rationalAugmentation (x - rationalAugmentation x • average H)
    rw [map_sub,map_smul,augmentation_average,smul_eq_mul,mul_one,sub_self]
  · change Ideal.Quotient.mk (uniformIdeal H) x =
      Ideal.Quotient.mk (uniformIdeal H) (x - rationalAugmentation x • average H)
    rw [map_sub]
    have hz : Ideal.Quotient.mk (uniformIdeal H) (rationalAugmentation x • average H) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      intro g
      rw [MonoidAlgebra.coeff_smul_apply,MonoidAlgebra.coeff_smul_apply,
        average_coeff,average_coeff]
    rw [hz,sub_zero]

end
end D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths.FixedCutCoherence
