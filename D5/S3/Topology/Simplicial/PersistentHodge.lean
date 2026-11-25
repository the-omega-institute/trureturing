/- GID: D5/S3/Topology/Simplicial/PersistentHodge
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Single-window persistent Hodge theory over scalar-valued positive forms. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import D5.S0.FiniteGeometry.Simplicial.Coboundary

/-!
Omega original.

Single-window persistent Hodge theory over scalar-valued positive forms.
The incoming domain is the full pullback of the boundary and the inclusion.
Adjoint identities and an ordinary orthogonal splitting supply harmonic
representatives; no homology or Laplacian conclusion is an input law.
-/

noncomputable section
@[expose] public section
namespace Omega.PersistentHodge

structure Space (F : Type _) (A : Type _) where
  group : AddCommGroup A
  smul : F → A → A

def SpaceLaws {F : Type _} {A : Type _} (V : Space F A) : Prop :=
  ∀ result : Prop,
    ((V.group.Laws) →
     (∀ a b c d, Eq (V.group.sub (V.group.add a b) (V.group.add c d))
    (V.group.add (V.group.sub a c) (V.group.sub b d))) →
     (∀ t a b, Eq (V.smul t (V.group.sub a b)) (V.group.sub (V.smul t a) (V.smul t b))) → result) → result

namespace SpaceLaws
theorem intro {F : Type _} {A : Type _} (V : Space F A)
    (group : V.group.Laws)
    (sub_add : ∀ a b c d, Eq (V.group.sub (V.group.add a b) (V.group.add c d))
    (V.group.add (V.group.sub a c) (V.group.sub b d)))
    (smul_sub : ∀ t a b, Eq (V.smul t (V.group.sub a b)) (V.group.sub (V.smul t a) (V.smul t b))) : SpaceLaws V :=
  fun _ use => use group sub_add smul_sub

theorem group {F : Type _} {A : Type _} {V : Space F A} (law : SpaceLaws V) :
    V.group.Laws :=
  law _ (fun h0 _ _ => h0)

theorem sub_add {F : Type _} {A : Type _} {V : Space F A} (law : SpaceLaws V) :
    ∀ a b c d, Eq (V.group.sub (V.group.add a b) (V.group.add c d))
    (V.group.add (V.group.sub a c) (V.group.sub b d)) :=
  law _ (fun _ h1 _ => h1)

theorem smul_sub {F : Type _} {A : Type _} {V : Space F A} (law : SpaceLaws V) :
    ∀ t a b, Eq (V.smul t (V.group.sub a b)) (V.group.sub (V.smul t a) (V.smul t b)) :=
  law _ (fun _ _ h2 => h2)
end SpaceLaws

structure Linear {F : Type _} {A : Type _} {B : Type _} (V : Space F A) (W : Space F B) where
  apply : A → B

def LinearLaws {F : Type _} {A : Type _} {B : Type _} {V : Space F A} {W : Space F B}
    (f : Linear V W) : Prop :=
  ∀ result : Prop,
    ((Eq (f.apply V.group.zero) W.group.zero) →
     (∀ x y, Eq (f.apply (V.group.add x y)) (W.group.add (f.apply x) (f.apply y))) →
     (∀ x y, Eq (f.apply (V.group.sub x y)) (W.group.sub (f.apply x) (f.apply y))) →
     (∀ t x, Eq (f.apply (V.smul t x)) (W.smul t (f.apply x))) → result) → result

namespace LinearLaws
theorem intro {F : Type _} {A : Type _} {B : Type _} {V : Space F A} {W : Space F B}
    (f : Linear V W)
    (zero : Eq (f.apply V.group.zero) W.group.zero)
    (add : ∀ x y, Eq (f.apply (V.group.add x y)) (W.group.add (f.apply x) (f.apply y)))
    (sub : ∀ x y, Eq (f.apply (V.group.sub x y)) (W.group.sub (f.apply x) (f.apply y)))
    (smul : ∀ t x, Eq (f.apply (V.smul t x)) (W.smul t (f.apply x))) : LinearLaws f :=
  fun _ use => use zero add sub smul

theorem zero {F : Type _} {A : Type _} {B : Type _} {V : Space F A} {W : Space F B}
    {f : Linear V W} (law : LinearLaws f) :
    Eq (f.apply V.group.zero) W.group.zero :=
  law _ (fun h0 _ _ _ => h0)

theorem add {F : Type _} {A : Type _} {B : Type _} {V : Space F A} {W : Space F B}
    {f : Linear V W} (law : LinearLaws f) :
    ∀ x y, Eq (f.apply (V.group.add x y)) (W.group.add (f.apply x) (f.apply y)) :=
  law _ (fun _ h1 _ _ => h1)

theorem sub {F : Type _} {A : Type _} {B : Type _} {V : Space F A} {W : Space F B}
    {f : Linear V W} (law : LinearLaws f) :
    ∀ x y, Eq (f.apply (V.group.sub x y)) (W.group.sub (f.apply x) (f.apply y)) :=
  law _ (fun _ _ h2 _ => h2)

theorem smul {F : Type _} {A : Type _} {B : Type _} {V : Space F A} {W : Space F B}
    {f : Linear V W} (law : LinearLaws f) :
    ∀ t x, Eq (f.apply (V.smul t x)) (W.smul t (f.apply x)) :=
  law _ (fun _ _ _ h3 => h3)
end LinearLaws

structure Window (F : Type _) (B : Type _) (C : Type _) (X : Type _) (Y : Type _) (Z : Type _) where
  scalar : AddCommGroup F
  source : Space F B
  lower : Space F C
  incoming : Space F X
  target : Space F Y
  targetLower : Space F Z
  d : Linear source lower
  b : Linear incoming target
  e : Linear target targetLower
  i : Linear source target
  j : Linear lower targetLower

variable {F : Type _} {B : Type _} {C : Type _} {X : Type _} {Y : Type _} {Z : Type _}

def WindowLaws (W : Window F B C X Y Z) (nonnegative : F → Prop) : Prop :=
  ∀ result : Prop,
    ((W.scalar.Laws) →
     (SpaceLaws W.source) →
     (SpaceLaws W.lower) →
     (SpaceLaws W.incoming) →
     (SpaceLaws W.target) →
     (SpaceLaws W.targetLower) →
     (LinearLaws W.d) →
     (LinearLaws W.b) →
     (LinearLaws W.e) →
     (LinearLaws W.i) →
     (LinearLaws W.j) →
     (∀ a b, nonnegative a → nonnegative b → Eq (W.scalar.add a b) W.scalar.zero →
    And (Eq a W.scalar.zero) (Eq b W.scalar.zero)) →
     (∀ x y, Eq (W.i.apply x) (W.i.apply y) → Eq x y) →
     (∀ x, Eq (W.e.apply (W.b.apply x)) W.targetLower.group.zero) →
     (∀ x, Eq (W.e.apply (W.i.apply x)) (W.j.apply (W.d.apply x))) → result) → result

namespace WindowLaws
theorem intro (W : Window F B C X Y Z) (nonnegative : F → Prop)
    (scalar : W.scalar.Laws)
    (source : SpaceLaws W.source)
    (lower : SpaceLaws W.lower)
    (incoming : SpaceLaws W.incoming)
    (target : SpaceLaws W.target)
    (targetLower : SpaceLaws W.targetLower)
    (d : LinearLaws W.d)
    (b : LinearLaws W.b)
    (e : LinearLaws W.e)
    (i : LinearLaws W.i)
    (j : LinearLaws W.j)
    (sum_zero : ∀ a b, nonnegative a → nonnegative b → Eq (W.scalar.add a b) W.scalar.zero →
    And (Eq a W.scalar.zero) (Eq b W.scalar.zero))
    (i_injective : ∀ x y, Eq (W.i.apply x) (W.i.apply y) → Eq x y)
    (square : ∀ x, Eq (W.e.apply (W.b.apply x)) W.targetLower.group.zero)
    (commute : ∀ x, Eq (W.e.apply (W.i.apply x)) (W.j.apply (W.d.apply x))) : WindowLaws W nonnegative :=
  fun _ use => use scalar source lower incoming target targetLower d b e i j sum_zero i_injective square commute

theorem scalar {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    W.scalar.Laws :=
  law _ (fun h0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => h0)

theorem source {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    SpaceLaws W.source :=
  law _ (fun _ h1 _ _ _ _ _ _ _ _ _ _ _ _ _ => h1)

theorem lower {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    SpaceLaws W.lower :=
  law _ (fun _ _ h2 _ _ _ _ _ _ _ _ _ _ _ _ => h2)

theorem d {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    LinearLaws W.d :=
  law _ (fun _ _ _ _ _ _ h6 _ _ _ _ _ _ _ _ => h6)

theorem b {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    LinearLaws W.b :=
  law _ (fun _ _ _ _ _ _ _ h7 _ _ _ _ _ _ _ => h7)

theorem i {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    LinearLaws W.i :=
  law _ (fun _ _ _ _ _ _ _ _ _ h9 _ _ _ _ _ => h9)

theorem j {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    LinearLaws W.j :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ h10 _ _ _ _ => h10)

theorem sum_zero {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    ∀ a b, nonnegative a → nonnegative b → Eq (W.scalar.add a b) W.scalar.zero →
    And (Eq a W.scalar.zero) (Eq b W.scalar.zero) :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ _ h11 _ _ _ => h11)

theorem i_injective {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    ∀ x y, Eq (W.i.apply x) (W.i.apply y) → Eq x y :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ _ _ h12 _ _ => h12)

theorem square {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    ∀ x, Eq (W.e.apply (W.b.apply x)) W.targetLower.group.zero :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h14 _ => h14)

theorem commute {W : Window F B C X Y Z} {nonnegative : F → Prop} (law : WindowLaws W nonnegative) :
    ∀ x, Eq (W.e.apply (W.i.apply x)) (W.j.apply (W.d.apply x)) :=
  law _ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h15 => h15)
end WindowLaws

/-- A pair becomes a pullback vector precisely when `Coherent` holds. -/
structure Pullback (W : Window F B C X Y Z) where
  fillingAt : True → X
  boundaryAt : True → B

namespace Pullback
variable {W : Window F B C X Y Z}
def filling (u : Pullback W) : X := u.fillingAt True.intro
def boundary (u : Pullback W) : B := u.boundaryAt True.intro
def pair (c : X) (y : B) : Pullback W := ⟨fun _ => c, fun _ => y⟩
def Coherent (u : Pullback W) : Prop := Eq (W.b.apply u.filling) (W.i.apply u.boundary)
end Pullback

namespace Window
variable (W : Window F B C X Y Z) {nn : F → Prop} (law : WindowLaws W nn)

def zero : Pullback W :=
  Pullback.pair W.incoming.group.zero W.source.group.zero

def T (u : Pullback W) : B := u.boundary

def Cycle (x : B) : Prop := Eq (W.d.apply x) W.lower.group.zero

def Null (x : B) : Prop := Exists fun c => Eq (W.b.apply c) (W.i.apply x)

/-- Both full-filling witnesses are constructed, without choosing a basis. -/
theorem range_T (x : B) : Iff (W.Null x)
    (Exists fun u : Pullback W => And u.Coherent (Eq (W.T u) x)) :=
  Iff.intro
    (fun h => h.elim fun c hc => Exists.intro (Pullback.pair c x) (And.intro hc (Eq.refl _)))
    (fun h => h.elim fun u hu => Exists.intro u.filling
      (hu.left.trans (congrArg W.i.apply hu.right)))

include law in
theorem T_cycle (hj : ∀ x y, Eq (W.j.apply x) (W.j.apply y) → Eq x y)
    (u : Pullback W) (hu : u.Coherent) : W.Cycle (W.T u) :=
  hj _ _ ((law.commute u.boundary).symm.trans
    (((congrArg W.e.apply hu).symm.trans (law.square u.filling)).trans law.j.zero.symm))

include law in
theorem null_cycle (hj : ∀ x y, Eq (W.j.apply x) (W.j.apply y) → Eq x y)
    (x : B) (h : W.Null x) : W.Cycle x :=
  ((W.range_T x).mp h).elim fun u hu => Eq.subst (motive := W.Cycle) hu.right (W.T_cycle law hj u hu.left)

include law in
/-- A pullback vector is uniquely determined by its incoming filling. -/
theorem filling_injective (u v : Pullback W) (hu : u.Coherent) (hv : v.Coherent)
    (h : Eq u.filling v.filling) :
    Eq u.boundary v.boundary :=
  law.i_injective _ _ (hu.symm.trans ((congrArg W.b.apply h).trans hv))

include law in
theorem null_sub (x y : B) (hx : W.Null x) (hy : W.Null y) :
    W.Null (W.source.group.sub x y) :=
  hx.elim fun c hc => hy.elim fun t ht => Exists.intro (W.incoming.group.sub c t)
    ((law.b.sub c t).trans
      ((congrArg (fun a => W.target.group.sub a (W.b.apply t)) hc).trans
        ((congrArg (W.target.group.sub (W.i.apply x)) ht).trans (law.i.sub x y).symm)))

end Window

structure Form {F : Type _} {A : Type _} (S : AddCommGroup F) (V : Space F A) where
  inner : A → A → F

def FormLaws {W : Window F B C X Y Z} {A : Type _} {V : Space F A}
    (form : Form W.scalar V) (nonnegative : F → Prop) : Prop :=
  ∀ result : Prop,
    ((∀ x y z, Eq (form.inner (V.group.add x y) z)
    (W.scalar.add (form.inner x z) (form.inner y z))) →
     (∀ x y z, Eq (form.inner x (V.group.sub y z))
    (W.scalar.sub (form.inner x y) (form.inner x z))) →
     (∀ x, Eq (form.inner V.group.zero x) W.scalar.zero) →
     (∀ x, Eq (form.inner x V.group.zero) W.scalar.zero) →
     (∀ x, nonnegative (form.inner x x)) →
     (∀ x, Eq (form.inner x x) W.scalar.zero → Eq x V.group.zero) → result) → result

namespace FormLaws
theorem intro {W : Window F B C X Y Z} {A : Type _} {V : Space F A}
    (form : Form W.scalar V) (nonnegative : F → Prop)
    (add_left : ∀ x y z, Eq (form.inner (V.group.add x y) z)
    (W.scalar.add (form.inner x z) (form.inner y z)))
    (sub_right : ∀ x y z, Eq (form.inner x (V.group.sub y z))
    (W.scalar.sub (form.inner x y) (form.inner x z)))
    (zero_left : ∀ x, Eq (form.inner V.group.zero x) W.scalar.zero)
    (zero_right : ∀ x, Eq (form.inner x V.group.zero) W.scalar.zero)
    (positive : ∀ x, nonnegative (form.inner x x))
    (definite : ∀ x, Eq (form.inner x x) W.scalar.zero → Eq x V.group.zero) : FormLaws form nonnegative :=
  fun _ use => use add_left sub_right zero_left zero_right positive definite

theorem add_left {W : Window F B C X Y Z} {A : Type _} {V : Space F A}
    {form : Form W.scalar V} {nonnegative : F → Prop} (law : FormLaws form nonnegative) :
    ∀ x y z, Eq (form.inner (V.group.add x y) z)
    (W.scalar.add (form.inner x z) (form.inner y z)) :=
  law _ (fun h0 _ _ _ _ _ => h0)

theorem sub_right {W : Window F B C X Y Z} {A : Type _} {V : Space F A}
    {form : Form W.scalar V} {nonnegative : F → Prop} (law : FormLaws form nonnegative) :
    ∀ x y z, Eq (form.inner x (V.group.sub y z))
    (W.scalar.sub (form.inner x y) (form.inner x z)) :=
  law _ (fun _ h1 _ _ _ _ => h1)

theorem zero_left {W : Window F B C X Y Z} {A : Type _} {V : Space F A}
    {form : Form W.scalar V} {nonnegative : F → Prop} (law : FormLaws form nonnegative) :
    ∀ x, Eq (form.inner V.group.zero x) W.scalar.zero :=
  law _ (fun _ _ h2 _ _ _ => h2)

theorem zero_right {W : Window F B C X Y Z} {A : Type _} {V : Space F A}
    {form : Form W.scalar V} {nonnegative : F → Prop} (law : FormLaws form nonnegative) :
    ∀ x, Eq (form.inner x V.group.zero) W.scalar.zero :=
  law _ (fun _ _ _ h3 _ _ => h3)

theorem nonnegative {W : Window F B C X Y Z} {A : Type _} {V : Space F A}
    {form : Form W.scalar V} {nonnegative : F → Prop} (law : FormLaws form nonnegative) :
    ∀ x, nonnegative (form.inner x x) :=
  law _ (fun _ _ _ _ h4 _ => h4)

theorem definite {W : Window F B C X Y Z} {A : Type _} {V : Space F A}
    {form : Form W.scalar V} {nonnegative : F → Prop} (law : FormLaws form nonnegative) :
    ∀ x, Eq (form.inner x x) W.scalar.zero → Eq x V.group.zero :=
  law _ (fun _ _ _ _ _ h5 => h5)
end FormLaws

structure AdjointData (W : Window F B C X Y Z) where
  sourceForm : Form W.scalar W.source
  lowerForm : Form W.scalar W.lower
  incomingForm : Form W.scalar W.incoming
  star : B → Pullback W
  dstar : C → B

def AdjointLaws {W : Window F B C X Y Z} (H : AdjointData W)
    (nonnegative : F → Prop) : Prop :=
  ∀ result : Prop,
    ((FormLaws H.sourceForm nonnegative) →
     (FormLaws H.lowerForm nonnegative) →
     (FormLaws H.incomingForm nonnegative) →
     (∀ x, (H.star x).Coherent) →
     (Eq (H.dstar W.lower.group.zero) W.source.group.zero) →
     (∀ u, u.Coherent → ∀ x, Eq (H.sourceForm.inner (W.T u) x)
    (H.incomingForm.inner u.filling (H.star x).filling)) →
     (∀ v x, Eq (H.sourceForm.inner (H.dstar v) x)
    (H.lowerForm.inner v (W.d.apply x))) → result) → result

namespace AdjointLaws
theorem intro {W : Window F B C X Y Z} (H : AdjointData W)
    (nonnegative : F → Prop)
    (sourceForm : FormLaws H.sourceForm nonnegative)
    (lowerForm : FormLaws H.lowerForm nonnegative)
    (incomingForm : FormLaws H.incomingForm nonnegative)
    (star_coherent : ∀ x, (H.star x).Coherent)
    (dstar_zero : Eq (H.dstar W.lower.group.zero) W.source.group.zero)
    (incoming_adjoint : ∀ u, u.Coherent → ∀ x, Eq (H.sourceForm.inner (W.T u) x)
    (H.incomingForm.inner u.filling (H.star x).filling))
    (outgoing_adjoint : ∀ v x, Eq (H.sourceForm.inner (H.dstar v) x)
    (H.lowerForm.inner v (W.d.apply x))) : AdjointLaws H nonnegative :=
  fun _ use => use sourceForm lowerForm incomingForm star_coherent dstar_zero incoming_adjoint outgoing_adjoint

theorem sourceForm {W : Window F B C X Y Z} {H : AdjointData W}
    {nonnegative : F → Prop} (law : AdjointLaws H nonnegative) :
    FormLaws H.sourceForm nonnegative :=
  law _ (fun h0 _ _ _ _ _ _ => h0)

theorem lowerForm {W : Window F B C X Y Z} {H : AdjointData W}
    {nonnegative : F → Prop} (law : AdjointLaws H nonnegative) :
    FormLaws H.lowerForm nonnegative :=
  law _ (fun _ h1 _ _ _ _ _ => h1)

theorem incomingForm {W : Window F B C X Y Z} {H : AdjointData W}
    {nonnegative : F → Prop} (law : AdjointLaws H nonnegative) :
    FormLaws H.incomingForm nonnegative :=
  law _ (fun _ _ h2 _ _ _ _ => h2)

theorem star_coherent {W : Window F B C X Y Z} {H : AdjointData W}
    {nonnegative : F → Prop} (law : AdjointLaws H nonnegative) :
    ∀ x, (H.star x).Coherent :=
  law _ (fun _ _ _ h3 _ _ _ => h3)

theorem dstar_zero {W : Window F B C X Y Z} {H : AdjointData W}
    {nonnegative : F → Prop} (law : AdjointLaws H nonnegative) :
    Eq (H.dstar W.lower.group.zero) W.source.group.zero :=
  law _ (fun _ _ _ _ h4 _ _ => h4)

theorem incoming_adjoint {W : Window F B C X Y Z} {H : AdjointData W}
    {nonnegative : F → Prop} (law : AdjointLaws H nonnegative) :
    ∀ u, u.Coherent → ∀ x, Eq (H.sourceForm.inner (W.T u) x)
    (H.incomingForm.inner u.filling (H.star x).filling) :=
  law _ (fun _ _ _ _ _ h5 _ => h5)

theorem outgoing_adjoint {W : Window F B C X Y Z} {H : AdjointData W}
    {nonnegative : F → Prop} (law : AdjointLaws H nonnegative) :
    ∀ v x, Eq (H.sourceForm.inner (H.dstar v) x)
    (H.lowerForm.inner v (W.d.apply x)) :=
  law _ (fun _ _ _ _ _ _ h6 => h6)
end AdjointLaws

namespace AdjointData
variable {W : Window F B C X Y Z} (H : AdjointData W) {nn : F → Prop}
  (law : WindowLaws W nn) (hl : AdjointLaws H nn)

def laplacian (x : B) : B := W.source.group.add (W.T (H.star x)) (H.dstar (W.d.apply x))

def Harmonic (x : B) : Prop := Eq (H.laplacian x) W.source.group.zero

def Orthogonal (x : B) : Prop := ∀ n, W.Null n →
  Eq (H.sourceForm.inner n x) W.scalar.zero

include hl in
/-- Energy is derived from the two adjoint identities. -/
theorem energy (x : B) : Eq (H.sourceForm.inner (H.laplacian x) x)
    (W.scalar.add (H.incomingForm.inner (H.star x).filling (H.star x).filling)
      (H.lowerForm.inner (W.d.apply x) (W.d.apply x))) :=
  (hl.sourceForm.add_left _ _ x).trans
    ((congrArg (fun a => W.scalar.add a
      (H.sourceForm.inner (H.dstar (W.d.apply x)) x))
      (hl.incoming_adjoint (H.star x) (hl.star_coherent x) x)).trans
      (congrArg (W.scalar.add
        (H.incomingForm.inner (H.star x).filling (H.star x).filling))
        (hl.outgoing_adjoint (W.d.apply x) x)))

include law hl in
/-- Positivity separates the incoming and outgoing energies. -/
theorem harmonic_iff (x : B) : Iff (H.Harmonic x)
    (And (Eq (H.star x).filling W.incoming.group.zero) (W.Cycle x)) :=
  Iff.intro
    (fun hx =>
      have energies := law.sum_zero _ _ (hl.incomingForm.nonnegative _)
        (hl.lowerForm.nonnegative _)
        ((H.energy hl x).symm.trans ((congrArg (fun z => H.sourceForm.inner z x) hx).trans
          (hl.sourceForm.zero_left x)))
      And.intro (hl.incomingForm.definite _ energies.left)
        (hl.lowerForm.definite _ energies.right))
    (fun hx =>
      have boundaryZero := W.filling_injective law (H.star x) W.zero (hl.star_coherent x)
        (law.b.zero.trans law.i.zero.symm) hx.left
      (congrArg (fun a => W.source.group.add a (H.dstar (W.d.apply x))) boundaryZero).trans
        ((congrArg (W.source.group.add W.source.group.zero)
          ((congrArg H.dstar hx.right).trans hl.dstar_zero)).trans
          (law.source.group.zero_add W.source.group.zero)))

include hl in
/-- Orthogonality to actual filling boundaries is precisely adjoint vanishing. -/
theorem orthogonal_iff (x : B) : Iff (H.Orthogonal x)
    (Eq (H.star x).filling W.incoming.group.zero) :=
  Iff.intro
    (fun hx => hl.incomingForm.definite _
      ((hl.incoming_adjoint (H.star x) (hl.star_coherent x) x).symm.trans
        (hx (W.T (H.star x)) (Exists.intro (H.star x).filling (hl.star_coherent x)))))
    (fun hx n hn => ((W.range_T n).mp hn).elim fun u hu =>
      (congrArg (fun a => H.sourceForm.inner a x) hu.right).symm.trans
        ((hl.incoming_adjoint u hu.left x).trans
          ((congrArg (H.incomingForm.inner u.filling) hx).trans
            (hl.incomingForm.zero_right u.filling))))

include law hl in
theorem harmonic_classification (x : B) : Iff (H.Harmonic x)
    (And (W.Cycle x) (H.Orthogonal x)) :=
  Iff.intro
    (fun hx => have h := (H.harmonic_iff law hl x).mp hx
      And.intro h.right ((H.orthogonal_iff hl x).mpr h.left))
    (fun hx => (H.harmonic_iff law hl x).mpr
      (And.intro ((H.orthogonal_iff hl x).mp hx.right) hx.left))

include law hl in
/-- Two harmonic representatives of the same filling class coincide. -/
theorem harmonic_unique (h k : B) (hh : H.Harmonic h) (hk : H.Harmonic k)
    (sameClass : W.Null (W.source.group.sub h k)) : Eq h k :=
  have oh := ((H.harmonic_classification law hl h).mp hh).right
  have ok := ((H.harmonic_classification law hl k).mp hk).right
  have differenceZero : Eq (W.source.group.sub h k) W.source.group.zero :=
    hl.sourceForm.definite _ ((hl.sourceForm.sub_right _ h k).trans
      ((congrArg (fun a => W.scalar.sub a
        (H.sourceForm.inner (W.source.group.sub h k) k)) (oh _ sameClass)).trans
        ((congrArg (W.scalar.sub W.scalar.zero) (ok _ sameClass)).trans
          (W.scalar.sub_self law.scalar W.scalar.zero))))
  (W.source.group.sub_add_cancel law.source.group h k).symm.trans
    ((congrArg (fun a => W.source.group.add a k) differenceZero).trans (law.source.group.zero_add k))

end AdjointData

/-- An ordinary orthogonal projection onto filling boundaries. -/
structure Splitting {W : Window F B C X Y Z} (H : AdjointData W) where
  projection : Linear W.source W.source

def SplittingLaws {W : Window F B C X Y Z} {H : AdjointData W}
    (P : Splitting H) : Prop :=
  ∀ result : Prop,
    ((LinearLaws P.projection) →
     (∀ x, W.Null (P.projection.apply x)) →
     (∀ x, H.Orthogonal (W.source.group.sub x (P.projection.apply x))) → result) → result

namespace SplittingLaws
theorem intro {W : Window F B C X Y Z} {H : AdjointData W}
    (P : Splitting H)
    (projection : LinearLaws P.projection)
    (in_null : ∀ x, W.Null (P.projection.apply x))
    (residual_orthogonal : ∀ x, H.Orthogonal (W.source.group.sub x (P.projection.apply x))) : SplittingLaws P :=
  fun _ use => use projection in_null residual_orthogonal

theorem projection {W : Window F B C X Y Z} {H : AdjointData W}
    {P : Splitting H} (law : SplittingLaws P) :
    LinearLaws P.projection :=
  law _ (fun h0 _ _ => h0)

theorem in_null {W : Window F B C X Y Z} {H : AdjointData W}
    {P : Splitting H} (law : SplittingLaws P) :
    ∀ x, W.Null (P.projection.apply x) :=
  law _ (fun _ h1 _ => h1)

theorem residual_orthogonal {W : Window F B C X Y Z} {H : AdjointData W}
    {P : Splitting H} (law : SplittingLaws P) :
    ∀ x, H.Orthogonal (W.source.group.sub x (P.projection.apply x)) :=
  law _ (fun _ _ h2 => h2)
end SplittingLaws

namespace Splitting
variable {W : Window F B C X Y Z} {H : AdjointData W} (P : Splitting H)
  {nn : F → Prop} (law : WindowLaws W nn) (hl : AdjointLaws H nn) (pl : SplittingLaws P)

def representative (x : B) : B := W.source.group.sub x (P.projection.apply x)

include law pl in
theorem representative_add (x y : B) : Eq (P.representative (W.source.group.add x y))
    (W.source.group.add (P.representative x) (P.representative y)) :=
  (congrArg (W.source.group.sub (W.source.group.add x y)) (pl.projection.add x y)).trans
    (law.source.sub_add x y (P.projection.apply x) (P.projection.apply y))

include law pl in
theorem representative_smul (t : F) (x : B) :
    Eq (P.representative (W.source.smul t x)) (W.source.smul t (P.representative x)) :=
  (congrArg (W.source.group.sub (W.source.smul t x)) (pl.projection.smul t x)).trans
    (law.source.smul_sub t x (P.projection.apply x)).symm

include law pl in
theorem representative_same_class (x : B) : W.Null (W.source.group.sub x (P.representative x)) :=
  Eq.subst (motive := W.Null)
    ((congrArg (fun a => W.source.group.sub a (P.representative x))
        (W.source.group.sub_add_cancel law.source.group x (P.projection.apply x)).symm).trans
      ((congrArg (fun a => W.source.group.sub a (P.representative x))
        (law.source.group.add_comm (P.representative x) (P.projection.apply x))).trans
        (W.source.group.add_sub_cancel_right law.source.group (P.projection.apply x)
          (P.representative x)))).symm
    (pl.in_null x)

include law hl pl in
/-- Orthogonal splitting constructs a harmonic representative of every cycle. -/
theorem representative_harmonic
    (hj : ∀ x y, Eq (W.j.apply x) (W.j.apply y) → Eq x y) (x : B) (hx : W.Cycle x) : H.Harmonic (P.representative x) :=
  (H.harmonic_classification law hl _).mpr (And.intro
    ((law.d.sub x (P.projection.apply x)).trans
      ((congrArg (fun a => W.lower.group.sub a (W.d.apply (P.projection.apply x))) hx).trans
        ((congrArg (W.lower.group.sub W.lower.group.zero)
          (W.null_cycle law hj _ (pl.in_null x))).trans
          (W.lower.group.sub_self law.lower.group W.lower.group.zero))))
    (pl.residual_orthogonal x))

include law hl pl in
/-- Existence and uniqueness are derived, rather than supplied as splitting laws. -/
theorem unique_representative
    (hj : ∀ x y, Eq (W.j.apply x) (W.j.apply y) → Eq x y) (x : B) (hx : W.Cycle x) :
    And (H.Harmonic (P.representative x))
      (And (W.Null (W.source.group.sub x (P.representative x)))
        (∀ h, H.Harmonic h → W.Null (W.source.group.sub x h) → Eq h (P.representative x))) :=
  And.intro (P.representative_harmonic law hl pl hj x hx)
    (And.intro (P.representative_same_class law pl x) (fun h hh same =>
      H.harmonic_unique law hl h (P.representative x) hh (P.representative_harmonic law hl pl hj x hx)
        (Eq.subst (motive := W.Null)
          ((congrArg (fun a => W.source.group.sub a (W.source.group.sub x h))
            ((law.source.group.add_comm (W.source.group.sub h (P.representative x))
              (W.source.group.sub x h)).trans
                (W.source.group.sub_add_sub_cancel law.source.group x h (P.representative x))).symm).trans
            (W.source.group.add_sub_cancel_right law.source.group
              (W.source.group.sub h (P.representative x)) (W.source.group.sub x h)))
          (W.null_sub law (W.source.group.sub x (P.representative x)) (W.source.group.sub x h)
            (P.representative_same_class law pl x) same))))

end Splitting
end Omega.PersistentHodge
