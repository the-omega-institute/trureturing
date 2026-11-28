module
public import Lean
public import Init.Data.Sum.Lemmas
import Lean.Replay
import all Lean.Util.CollectAxioms
import all Init.Grind.Ring.Envelope
import all Init.Grind.Module.Envelope
import all Init.Prelude
import all Init.WF
public import OmegaChecks.InitInventory.Logic

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

/-- A dependent function on a sum agrees as a function with the recursor on its two restrictions. -/
def SumFunctionEta : Prop :=
  ∀ {α : Type u} {β : Type v} {γ : Sum α β → Sort w} (f : (s : Sum α β) → γ s),
    f = Sum.rec (fun a => f (.inl a)) (fun b => f (.inr b))

theorem sumEtaOfForall (rule : type_of% @Sum.forall_sum.{u,v,w}) : SumFunctionEta.{u,v,w} := by
  intro α β γ
  exact (@rule α β γ (fun f => f = Sum.rec (fun a => f (.inl a)) (fun b => f (.inr b)))).mpr
    (fun _ _ => rfl)

theorem sumForallIffEta : (type_of% @Sum.forall_sum.{u,v,w}) ↔ SumFunctionEta.{u,v,w} := by
  refine ⟨sumEtaOfForall, ?_⟩
  intro eta α β γ p
  exact ⟨fun all l r => all _, fun branches f => (eta f).symm ▸ branches _ _⟩

theorem funextFromFunextIff (rule : type_of% @funext_iff.{u,v}) : type_of% @funext.{u,v} :=
  fun {_ _ _ _} => rule.mpr

/-- Evaluation factors through the setoid of pointwise-equal functions. -/
theorem funextFromQuotientSound (sound : type_of% (@Quotient.sound.{imax u v})) :
    type_of% (@funext.{u,v}) := by
  intro α β f g h
  let s : Setoid ((a : α) → β a) := ⟨fun f g => ∀ a, f a = g a,
    ⟨fun _ _ => rfl, fun h a => (h a).symm, fun h₁ h₂ a => (h₁ a).trans (h₂ a)⟩⟩
  let app (q : Quotient s) (a : α) : β a :=
    Quot.lift (r := s.r) (fun t => t a) (fun _ _ eq => eq a) q
  exact congrArg app (@sound _ s f g h)

/-- Each fiber of values equal to a fixed value is a subsingleton. -/
theorem funextFromPiSubsingleton (ss : type_of% (@Pi.instSubsingleton.{u, max 1 v})) :
    type_of% (@funext.{u,v}) := by
  intro α β f g h
  let F (a : α) := {x : β a // x = f a}
  let fibers (a : α) : Subsingleton (F a) := ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
  have eq := (@ss α F fibers).elim (fun a => ⟨f a, rfl⟩) (fun a => ⟨g a, (h a).symm⟩)
  exact congrArg (fun z : ∀ a, F a => fun a => (z a).val) eq

/-- Evaluate a squashed function by restricting to a single pointwise equality class. -/
theorem funextFromSquashSubsingleton (ss : type_of% (@instSubsingletonSquash.{max 1 (imax u v)})) :
    type_of% (@funext.{u,v}) := by
  intro α β f g h
  let F := {t : (a : α) → β a // ∀ a, t a = f a}
  let app (s : Squash F) (a : α) : β a :=
    Quot.lift (fun t : F => t.val a) (fun t t' _ => (t.2 a).trans (t'.2 a).symm) s
  have eq := (@ss F).elim (Squash.mk (⟨f, fun _ => rfl⟩ : F))
    (Squash.mk (⟨g, fun a => (h a).symm⟩ : F))
  exact congrArg app eq

run_cmd
  for n in [``funextFromQuotientSound, ``funextFromPiSubsingleton, ``funextFromSquashSubsingleton] do
    unless (← collectAxioms n).isEmpty do throwError "function extensionality witness {n} uses axioms"

namespace MeasuredRecursion

/-- The root returns a dependent function, and each child returns its value at that point. -/
private def Result {α : Type u} (B : α → Type u) : Option α → Type u
  | none => (x : α) → B x
  | some x => B x

private def branch {α : Type u} {B : α → Type u} (empty : α → False) (f : (x : α) → B x) :
    (a : Option α) → ((b : Option α) → InvImage (· < ·) (fun _ => 0) b a → Result B b) → Result B a
  | none, rec => fun x => rec (some x) (empty x).elim
  | some x, _ => f x

/-- Any two dependent functions with an empty domain are equal. -/
def EmptyDomainExtensionality : Prop :=
  ∀ {α : Type u} {B : α → Type u}, (α → False) → ∀ f g : (x : α) → B x, f = g

theorem ofFuelCongruence (go : type_of% @WellFounded.Nat.fix.go_congr.{u+1, u+1}) :
    EmptyDomainExtensionality.{u} := by
  intro α B empty f g
  have step (k : (x : α) → B x) : (fun x => (empty x).elim) = k :=
    go (motive := Result B) (fun _ => 0) (branch empty k)
      none 1 2 (by decide) (by decide)
  exact (step f).symm.trans (step g)

theorem ofFixEquation (eq : type_of% @WellFounded.Nat.fix_eq.{u+1, u+1}) :
    EmptyDomainExtensionality.{u} := by
  intro α B empty f g
  have step (k : (x : α) → B x) : (fun x => (empty x).elim) = k :=
    eq (motive := Result B) (fun _ => 0) (branch empty k) none
  exact (step f).symm.trans (step g)

variable {α : Sort u} {motive : α → Sort v} (h : α → Nat)
variable (F : (x : α) → ((y : α) → InvImage (· < ·) h y x → motive y) → motive x)

/-- The step preserves pointwise agreement of recursive calls on smaller arguments. -/
def RespectsCalls : Prop :=
  ∀ x f g, (∀ y hy, f y hy = g y hy) → F x f = F x g

theorem goCongrOfRespectsCalls (step : RespectsCalls h F) (x : α)
    (n m : Nat) (hn : h x < n) (hm : h x < m) :
    WellFounded.Nat.fix.go h F n x hn = WellFounded.Nat.fix.go h F m x hm := by
  induction n generalizing x m with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
    cases m with
    | zero => exact (Nat.not_lt_zero _ hm).elim
    | succ m => exact step x _ _ fun y _ => ih y m _ _

theorem fixEqOfRespectsCalls (step : RespectsCalls h F) (x : α) :
    WellFounded.Nat.fix h F x = F x (fun y _ => WellFounded.Nat.fix h F y) := by
  unfold WellFounded.Nat.fix
  apply Eq.trans (b := WellFounded.Nat.fix.go h F (h x + 1) x (Nat.lt_succ_self _))
  · apply goCongrOfRespectsCalls h F step
  · exact step x _ _ fun y _ => goCongrOfRespectsCalls h F step y _ _ _ _

run_cmd
  for n in [``ofFuelCongruence, ``ofFixEquation, ``goCongrOfRespectsCalls, ``fixEqOfRespectsCalls] do
    unless (← collectAxioms n).isEmpty do throwError "measured recursion witness {n} uses axioms"

end MeasuredRecursion

namespace Envelope

open _root_.Lean.Grind _root_.Lean.Grind.Ring.OfSemiring

/-- Equal quotient representatives distinguished by a Boolean observation imply function extensionality. -/
private theorem quotientPointsGiveFunext {A : Sort w} {r : A → A → Prop} (pick : A → Bool)
    {p q : A} (hp : pick p = false) (hq : pick q = true) (same : Quot.mk r p = Quot.mk r q) :
    type_of% (@funext.{u,v}) := by
  intro α β f g h
  let F (x : A) (i : α) : β i := bif pick x then g i else f i
  have stable (i : α) (x y : A) (_ : r x y) : F x i = F y i := by
    dsimp only [F]
    cases pick x <;> cases pick y <;> first | rfl | exact h i | exact (h i).symm
  let app (z : Quot r) (i : α) : β i := Quot.lift (fun x => F x i) (stable i) z
  have sides := congrArg app same
  change (fun i => bif pick p then g i else f i) = (fun i => bif pick q then g i else f i) at sides
  rw [hp, hq] at sides
  exact sides

@[expose] def natPositive : Nat → Bool
  | 0 => false
  | _ + 1 => true

local instance boolSemiring : Semiring Bool where
  add := Bool.or
  mul := Bool.and
  natCast := ⟨natPositive⟩
  ofNat n := ⟨natPositive n⟩
  nsmul := ⟨fun k a => natPositive k && a⟩
  npow := ⟨fun a k => if natPositive k then a else true⟩
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_mul a := rfl
  mul_zero a := by cases a <;> rfl
  pow_zero a := rfl
  pow_succ a k := by cases a <;> cases k <;> rfl
  ofNat_succ n := by cases n <;> rfl
  ofNat_eq_natCast _ := rfl
  nsmul_eq_natCast_mul _ _ := rfl

/-- The Boolean semiring gives two related pairs with different first coordinates. -/
private theorem envelopeFunext
    (same : Q.mk (α := Bool) (false, false) = Q.mk (α := Bool) (true, true)) :
    type_of% (@funext.{u,v}) :=
  quotientPointsGiveFunext (fun p : Bool × Bool => p.1) (p := (false,false)) (q := (true,true)) rfl rfl same

theorem funextFromNegRespect (respect : type_of% (@neg._proof_1.{0})) : type_of% (@funext.{u,v}) :=
  envelopeFunext (@respect Bool _ (false,false) (true,true) ⟨false,rfl⟩)

theorem funextFromAddRespect (respect : type_of% (@add._proof_1.{0})) : type_of% (@funext.{u,v}) :=
  envelopeFunext (@respect Bool _ (false,false) (false,false) (true,true) (false,false) ⟨false,rfl⟩ ⟨false,rfl⟩)

theorem funextFromSubRespect (respect : type_of% (@sub._proof_5.{0})) : type_of% (@funext.{u,v}) :=
  envelopeFunext (@respect Bool _ (false,false) (false,false) (true,true) (false,false) ⟨false,rfl⟩ ⟨false,rfl⟩)

theorem funextFromMulRespect (respect : type_of% (@mul._proof_1.{0})) : type_of% (@funext.{u,v}) :=
  envelopeFunext (@respect Bool _ (false,false) (true,false) (true,true) (true,false) ⟨false,rfl⟩ ⟨false,rfl⟩)

/-- Cancellation together with the representative computation rules at a single input suffices. -/
theorem funextFromCancellation
    (plus : Q Bool → Q Bool → Q Bool) (minus : Q Bool → Q Bool)
    (negValue : minus (Q.mk (true, false)) = Q.mk (false, true))
    (sumValue : plus (Q.mk (false, true)) (Q.mk (true, false)) = Q.mk (true, true))
    (cancel : ∀ z, plus (minus z) z = Q.mk (false, false)) :
    type_of% (@funext.{u,v}) := by
  have eq := cancel (Q.mk (true, false))
  rw [negValue, sumValue] at eq
  intro α β f g h
  exact envelopeFunext eq.symm h

/-- Three computations of the proposed ring on the Boolean semiring's quotient. -/
structure RingComputes (s : Ring (Q Bool)) : Prop where
  negValue : s.toNeg.neg (Q.mk (true, false)) = Q.mk (false, true)
  addValue : s.toSemiring.toAdd.add (Q.mk (false, true)) (Q.mk (true, false)) = Q.mk (true, true)
  zeroValue : (s.toSemiring.ofNat 0).ofNat = Q.mk (false, false)

private theorem RingComputes.funext {s : Ring (Q Bool)} (h : RingComputes s) :
    type_of% @funext.{u,v} :=
  @funextFromCancellation s.toSemiring.toAdd.add s.toNeg.neg h.negValue h.addValue
    (fun z => (s.neg_add_cancel z).trans h.zeroValue)

theorem funextFromEnvelopeRing (ring : type_of% @ofSemiring.{0})
    (computes : RingComputes (@ring Bool boolSemiring)) : type_of% @funext.{u,v} :=
  @RingComputes.funext _ computes

local instance boolCommSemiring : CommSemiring Bool where
  toSemiring := boolSemiring
  mul_comm a b := by cases a <;> cases b <;> rfl

theorem funextFromEnvelopeCommRing (ring : type_of% @CommRing.OfCommSemiring.ofCommSemiring.{0})
    (computes : RingComputes (@ring Bool boolCommSemiring).toRing) : type_of% @funext.{u,v} :=
  @RingComputes.funext _ computes

local instance boolNatModule : NatModule Bool where
  zero := false
  add := Bool.or
  nsmul := ⟨fun k a => natPositive k && a⟩
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_nsmul _ := rfl
  add_one_nsmul n a := by cases n <;> cases a <;> rfl

/-- Three computations of the proposed integer module on the Boolean additive monoid's quotient. -/
structure IntModuleComputes (s : IntModule (IntModule.OfNatModule.Q Bool)) : Prop where
  negValue : s.toAddCommGroup.toNeg.neg (IntModule.OfNatModule.Q.mk (true, false)) =
    IntModule.OfNatModule.Q.mk (false, true)
  addValue : s.toAddCommGroup.toAddCommMonoid.toAdd.add
    (IntModule.OfNatModule.Q.mk (false, true)) (IntModule.OfNatModule.Q.mk (true, false)) =
    IntModule.OfNatModule.Q.mk (true, true)
  zeroValue : s.toAddCommGroup.toAddCommMonoid.toZero.zero = IntModule.OfNatModule.Q.mk (false, false)

theorem funextFromEnvelopeIntModule (mod : type_of% @IntModule.OfNatModule.ofNatModule.{0})
    (computes : IntModuleComputes (@mod Bool boolNatModule)) : type_of% @funext.{u,v} := by
  let s := (@mod Bool boolNatModule).toAddCommGroup
  exact @funextFromCancellation s.toAddCommMonoid.toAdd.add s.toNeg.neg computes.negValue computes.addValue
    (fun z => (s.neg_add_cancel z).trans computes.zeroValue)

example : RingComputes (ofSemiring (α := Bool)) := ⟨rfl, rfl, rfl⟩
example : RingComputes (CommRing.OfCommSemiring.ofCommSemiring (α := Bool)).toRing := ⟨rfl, rfl, rfl⟩
example : IntModuleComputes (IntModule.OfNatModule.ofNatModule (α := Bool)) := ⟨rfl, rfl, rfl⟩

run_cmd
  for n in [``funextFromNegRespect, ``funextFromAddRespect, ``funextFromSubRespect,
      ``funextFromMulRespect, ``funextFromCancellation, ``funextFromEnvelopeRing,
      ``funextFromEnvelopeCommRing, ``funextFromEnvelopeIntModule] do
    unless (← collectAxioms n).isEmpty do throwError "ring envelope witness {n} uses axioms"

end Envelope

/-- Reader binding exposes the entire continuation as its result. -/
theorem funextFromBindCongr
    (combine : type_of% (@bind_congr.{u,u})) {α β : Type u} {f g : α → β}
    (pointwise : ∀ x, f x = g x) : f = g := by
  let read (γ : Type u) := α → γ
  letI : Bind read := ⟨fun x k a => k (x a) a⟩
  have eq := @combine read α β _ (fun a => a)
    (fun a _ => f a) (fun a _ => g a)
    (fun a => congrArg (fun y _ => y) (pointwise a))
  exact eq

/-- Mapping over the identity reader exposes the mapped function itself. -/
theorem funextFromMapCongr
    (combine : type_of% (@map_congr.{u,u})) {α β : Type u} {f g : α → β}
    (pointwise : ∀ x, f x = g x) : f = g := by
  let read (γ : Type u) := α → γ
  letI : Functor read := ⟨fun h x a => h (x a), fun c _ _ => c⟩
  exact @combine read α β _ (fun a => a) f g pointwise

private def graphStep {α : Sort u} {β : α → Sort v} (f : (x : α) → β x)
    (x : PLift (PSum α (PSigma β))) : PLift (PSum α (PSigma β)) :=
  PSum.casesOn x.down (fun a => ⟨.inr ⟨a, f a⟩⟩) (fun _ => x)

/-- Equal endomorphisms identify dependent sections by their graphs. -/
theorem funextFromEndomorphisms
    (ext : ∀ {T : Type (max 1 u v)} {f g : T → T}, (∀ x, f x = g x) → f = g) :
    type_of% @funext.{u,v} := by
  intro α β f g agree
  have stepEq : graphStep f = graphStep g := ext
    (T := PLift (PSum α (PSigma β))) (f := graphStep f) (g := graphStep g) (by
    rintro ⟨x⟩
    cases x with
    | inl a => exact congrArg (fun y => PLift.up (.inr ⟨a, y⟩ : PSum α (PSigma β))) (agree a)
    | inr => rfl)
  let graph (h : (a : α) → β a) (a : α) : PSigma β := ⟨a, h a⟩
  let observe (k : PLift (PSum α (PSigma β)) → PLift (PSum α (PSigma β))) (a : α) : PSigma β :=
    PSum.casesOn (k ⟨.inl a⟩).down (fun _ => ⟨a, f a⟩) id
  have graphEq : graph f = graph g := congrArg observe stepEq
  let unpack (t : {t : α → PSigma β // ∀ x, (t x).1 = x}) (a : α) : β a :=
    (t.property a) ▸ (t.val a).2
  exact congrArg unpack (Subtype.ext (a1 := ⟨graph f, fun _ => rfl⟩)
    (a2 := ⟨graph g, fun _ => rfl⟩) graphEq)

/-- Congruence under binding in the identity reader entails dependent function extensionality. -/
theorem dependentFunextFromBindCongr (combine : type_of% @bind_congr.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (fun {_ _ _} h => funextFromBindCongr combine h)

/-- Congruence of mapping over a reader entails dependent function extensionality. -/
theorem dependentFunextFromMapCongr (combine : type_of% @map_congr.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (fun {_ _ _} h => funextFromMapCongr combine h)

theorem funextFromReaderExt (ext : type_of% @ReaderT.ext.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms fun {T f g} h => @ext T (fun _ => T) T f g h

theorem funextFromReaderExtIff (ext : type_of% @ReaderT.ext_iff.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromReaderExt fun {_ _ _ _ _} => ext.mpr

theorem funextFromStateExt (ext : type_of% @StateT.ext.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms fun {T f g} h => @ext T (fun _ => T) T f g h

theorem funextFromStateExtIff (ext : type_of% @StateT.ext_iff.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromStateExt fun {_ _ _ _ _} => ext.mpr

/-- On the graph of f, replacing each value by its pointwise equal g gives an identity map. -/
private theorem endomorphismsOfPointwiseId
    (fixes : ∀ {S : Type w} (k : S → S), (∀ s, k s = s) → k = id)
    {T : Type w} {f g : T → T} (h : ∀ x, f x = g x) : f = g := by
  let graph := {p : T × T // p.2 = f p.1}
  let k (p : graph) : graph := ⟨(p.val.1, g p.val.1), (h p.val.1).symm⟩
  have eq := fixes k fun p => Subtype.ext (Prod.ext rfl ((h p.val.1).symm.trans p.property.symm))
  exact (congrArg (fun (j : graph → graph) x => (j ⟨(x, f x), rfl⟩).val.2) eq).symm

theorem funextFromLeftInverseId
    (inv : type_of% @Function.LeftInverse.id.{(max 1 u v)+1,(max 1 u v)+1}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms fun {_ _ _} h =>
    endomorphismsOfPointwiseId (fun {S} k hk => @inv S S k id hk) h

theorem funextFromRightInverseId
    (inv : type_of% @Function.RightInverse.id.{(max 1 u v)+1,(max 1 u v)+1}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms fun {_ _ _} h =>
    endomorphismsOfPointwiseId (fun {S} k hk => @inv S S id k hk) h

/-- A reader iterator returns the callback's value at the supplied element. -/
theorem funextFromForInEq
    (loop : type_of% @forIn'_eq_forIn.{max 1 u v,0,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  let read (α : Type (max 1 u v)) := T → α
  letI : Membership T Unit := ⟨fun _ _ => True⟩
  letI : ForIn' read Unit T inferInstance := ⟨fun _ b visit x => (visit x True.intro b x).value⟩
  let body (k : T → T) (a : T) (_ : T → T) : read (ForInStep (T → T)) :=
    fun _ => .yield fun _ => k a
  have eq := @loop T Unit read _ _ (T → T) () id (fun a _ => body f a) (body g)
    (fun a _ _ => congrArg (fun (y : T) (_ : T) => ForInStep.yield fun _ : T => y) (h a))
  have diagonal := congrArg (fun (k : T → T → T) x => k x x) eq
  exact diagonal

open Lean in
run_cmd
  for n in [``dependentFunextFromBindCongr, ``dependentFunextFromMapCongr,
      ``funextFromReaderExt, ``funextFromReaderExtIff, ``funextFromStateExt, ``funextFromStateExtIff,
      ``funextFromLeftInverseId, ``funextFromRightInverseId, ``funextFromForInEq] do
    unless (← collectAxioms n).isEmpty do throwError "reader congruence witness {n} uses axioms"

end OmegaChecks.InitBoundaries
