module
public import Lean
public import OmegaChecks.InitInventory.EqualityNormalization
public import OmegaChecks.InitInventory.FiniteCollectionLogic
import Lean.Replay
import all Lean.Util.CollectAxioms

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

/-- The official option selector returns a value on every inhabited input.
Lifting a sort into a type also covers propositional inputs to choice. -/
def choiceFromOptionPresence (select : type_of% (@Option.choice.{u}))
    (present : ∀ (α : Type u), Nonempty α → (select α).isSome) :
    type_of% (@Classical.choice.{u}) := by
  intro α h
  have nonempty : Nonempty (PLift α) := h.elim fun a => ⟨⟨a⟩⟩
  exact ((select (PLift α)).get (present _ nonempty)).down

namespace ExistentialConjunction

def ClosedEquality : Prop := (∃ _ : True, True) = (True ∧ True)

theorem ofRule (rule : type_of% @Lean.Grind.exists_prop) : ClosedEquality := rule

run_cmd
  let env ← getEnv
  let some (.defnInfo closed) := env.find? ``ClosedEquality | throwError "missing closed existential equation"
  let args := closed.value.getAppArgs
  unless closed.value.getAppFn.constName? == some `Eq && args.size == 3 &&
      args[1]!.getAppFn.constName? == some `Exists && args[2]!.getAppFn.constName? == some `And &&
      !Kernel.isDefEqGuarded env {} args[1]! args[2]! do
    throwError "expected distinct existential and conjunction heads in the closed equation"

end ExistentialConjunction

namespace OptionSelector

/-- On the subsingleton type of proofs of a proposition, the selector's tag decides it. -/
def decideFromSingleton (select : type_of% @Option.choice.{0})
    (law : ∀ {α : Type} [Subsingleton α] (a : α), select α = some a) (p : Prop) : Decidable p := by
  cases h : select (PLift p) with
  | some x => exact isTrue x.down
  | none => exact isFalse fun hp => nomatch h.symm.trans (law (PLift.up hp))

def decideFromDefault (select : type_of% @Option.choice.{0})
    (law : ∀ {α : Type} [Subsingleton α] [Inhabited α], select α = some default) (p : Prop) : Decidable p :=
  decideFromSingleton select (fun {α} sub a => @law α sub ⟨a⟩) p

noncomputable example : ∀ p : Prop, Decidable p := decideFromSingleton Option.choice (@Option.choice_eq_some)
noncomputable example : ∀ p : Prop, Decidable p := decideFromDefault Option.choice (@Option.choice_eq_default)

def fromSome (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u} [Nonempty α], (select α).isSome) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => @law α h

def fromSomeIff (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u}, (select α).isSome ↔ Nonempty α) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun _ => law.mpr

def fromNoneEq (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u}, select α = none ↔ ¬Nonempty α) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  cases e : select α with
  | none => exact False.elim (law.mp e h)
  | some a => rfl

def fromNoneIff (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u}, (select α).isNone ↔ ¬Nonempty α) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  cases e : select α with
  | none => exact False.elim (law.mp (e ▸ rfl) h)
  | some a => rfl

def fromNoneFalse (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u} [Nonempty α], (select α).isNone = false) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  have eq := @law α h
  cases e : select α with
  | none => rw [e] at eq; contradiction
  | some a => rfl

def fromListLength (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u} [Nonempty α], (select α).toList.length = 1) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  have eq := @law α h
  cases e : select α with
  | none => rw [e] at eq; contradiction
  | some a => rfl

def fromArraySize (select : type_of% (@Option.choice.{u}))
    (law : ∀ {α : Type u} [Nonempty α], (select α).toArray.size = 1) :
    type_of% (@Classical.choice.{u}) := choiceFromOptionPresence select fun α h => by
  have eq := @law α h
  cases e : select α with
  | none => rw [e] at eq; contradiction
  | some a => rfl
/-- An arbitrary well-typed witness for the dependent projection suffices.
Eliminating the inhabited input into the tag proposition is constructive. -/
def fromGetD (select : type_of% @Option.choice.{u})
    (law : ∀ {α : Type u} {a : α}, ∃ h : (select α).isSome, (select α).getD a = (select α).get h) :
    type_of% @Classical.choice.{u} :=
  choiceFromOptionPresence select fun α ne => ne.elim fun a => (@law α a).elim fun h _ => h

def fromGetBang (select : type_of% @Option.choice.{u})
    (law : ∀ {α : Type u} [Inhabited α], ∃ h : (select α).isSome, (select α).get! = (select α).get h) :
    type_of% @Classical.choice.{u} :=
  choiceFromOptionPresence select fun α ne => ne.elim fun a => (@law α ⟨a⟩).elim fun h _ => h

/-- For each law, every selector satisfying its exact public statement yields unrestricted choice. -/
def laws : List (Name × Name × Name) := [
  (`Init.Data.Option.Lemmas, ``Option.getD_choice, ``fromGetD),
  (`Init.Data.Option.Lemmas, ``Option.get!_choice, ``fromGetBang),
  (`Init.Data.Option.Lemmas, ``Option.isSome_choice, ``fromSome),
  (`Init.Data.Option.Lemmas, ``Option.isSome_choice_iff_nonempty, ``fromSomeIff),
  (`Init.Data.Option.Lemmas, ``Option.choice_eq_none_iff_not_nonempty, ``fromNoneEq),
  (`Init.Data.Option.Lemmas, ``Option.isNone_choice_iff_not_nonempty, ``fromNoneIff),
  (`Init.Data.Option.Lemmas, ``Option.isNone_choice_eq_false, ``fromNoneFalse),
  (`Init.Data.Option.List, ``Option.length_toList_choice_eq_one, ``fromListLength),
  (`Init.Data.Option.Array, ``Option.size_toArray_choice_eq_one, ``fromArraySize)]

def usesSelector (owner name : Name) : Bool :=
  laws.any fun (m, n, _) => m == owner && n == name

end OptionSelector

def choiceFromChoose (select : type_of% (@Classical.choose.{u})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @select α (fun _ => True) (inhabited.elim fun x => ⟨x, trivial⟩)

def choiceFromExistsChoose (select : type_of% (@Exists.choose.{u})) : type_of% (@Classical.choice.{u}) :=
  choiceFromChoose (@select)

def choiceFromEpsilon (select : type_of% (@Classical.epsilon.{u})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @select α inhabited (fun _ => True)

def choiceFromDescription (select : type_of% (@Classical.indefiniteDescription.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α (fun _ => True) (inhabited.elim fun x => ⟨x, trivial⟩)).val

def choiceFromInhabited (select : type_of% (@Classical.inhabited_of_nonempty.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α inhabited).default

theorem propextFromIffIffEq (equiv : type_of% (@iff_iff_eq)) : type_of% (@propext) :=
  fun {a b} h => (@equiv a b).mp h

theorem propextFromEqIffIff (equiv : type_of% (@eq_iff_iff)) : type_of% (@propext) :=
  fun {a b} h => (@equiv a b).mpr h

theorem propextFromPropIntro (intro : type_of% (@Eq.propIntro)) : type_of% (@propext) :=
  fun {a b} h => @intro a b h.mp h.mpr

def choiceFromOfNonempty (select : type_of% (@Classical.ofNonempty.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @select α inhabited

def choiceFromInhabitedOfExists (select : type_of% (@Classical.inhabited_of_exists.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α (fun _ => True) (inhabited.elim fun x => ⟨x, trivial⟩)).default

def choiceFromStrongDescription (select : type_of% (@Classical.strongIndefiniteDescription.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => (@select α (fun _ => True) inhabited).val

def choiceFromTypeDecidable (decideType : type_of% (@Classical.typeDecidable.{u})) :
    type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => match decideType α with
    | .inl value => value
    | .inr empty => False.elim (inhabited.elim empty)

theorem propextFromIffSubst (subst : type_of% (@Iff.subst)) : type_of% (@propext) :=
  fun {a b} eqv => @subst a b (Eq a) eqv rfl

theorem propextFromPropextIff (equiv : type_of% (@propext_iff)) : type_of% (@propext) :=
  fun {a b} h => (@equiv a b).mpr h

theorem propextFromPropComplete (complete : type_of% (@Classical.propComplete)) : type_of% (@propext) := by
  intro a b hab
  rcases complete a with ha | ha <;> rcases complete b with hb | hb
  · exact ha.trans hb.symm
  · exact False.elim (hb.mp (hab.mp (ha.mpr trivial)))
  · exact False.elim (ha.mp (hab.mpr (hb.mpr trivial)))
  · exact ha.trans hb.symm

theorem propextFromIteIffLeft (h : type_of% (@ite_iff_left_iff)) : type_of% (@propext) :=
  fun {a b} eqv => (@h False (.isFalse id) b a).mp eqv id

theorem propextFromIteIffRight (h : type_of% (@ite_iff_right_iff)) : type_of% (@propext) :=
  fun {a b} eqv => (@h True (.isTrue trivial) a b).mp eqv trivial

theorem propextFromLeftIffIte (h : type_of% (@left_iff_ite_iff)) : type_of% (@propext) :=
  fun {a b} eqv => (@h False (.isFalse id) a b).mp eqv id

theorem propextFromRightIffIte (h : type_of% (@right_iff_ite_iff)) : type_of% (@propext) :=
  fun {a b} eqv => (@h True (.isTrue trivial) b a).mp eqv trivial

theorem propextFromGrindIffEq (h : type_of% (@Lean.Grind.iff_eq)) : type_of% (@propext) :=
  fun {a b} eqv => (h a b).mp eqv

private theorem neNegationOfIff {p q : Prop} (equiv : p ↔ q) : p ≠ ¬q := by
  intro eq
  have np : ¬p := fun hp => (eq.mp hp) (equiv.mp hp)
  exact np (eq.mpr (fun hq => np (equiv.mpr hq)))

/-- Taking the second proposition to be the negation of the first gives
double-negation elimination. Apply it to equality of equivalent propositions. -/
theorem propextFromNotEqProp (norm : type_of% @Lean.Grind.not_eq_prop) : type_of% @propext := by
  have dne (p : Prop) : ¬¬p → p :=
    ((norm p (¬p)).mp (neNegationOfIff (Iff.rfl (a := p)))).mpr
  intro p q equiv
  exact dne _ fun ne => neNegationOfIff equiv ((norm p q).mp ne)


def choiceFromFix (fix : type_of% (@WellFounded.extrinsicFix.{u,v})) : type_of% (@Classical.choice.{v}) :=
  fun {α} inhabited => @fix PUnit.{u} (fun _ => α) (fun _ => inhabited) (fun _ _ => True)
    (fun x next => next x trivial) PUnit.unit

def choiceFromFix₂ (fix : type_of% (@WellFounded.extrinsicFix₂.{u,v,w})) : type_of% (@Classical.choice.{w}) :=
  fun {α} inhabited => @fix PUnit.{u} (fun _ => PUnit.{v}) (fun _ _ => α) (fun _ _ => inhabited)
    (fun _ _ => True) (fun x y next => next x y trivial) PUnit.unit PUnit.unit

def choiceFromFix₃ (fix : type_of% (@WellFounded.extrinsicFix₃.{u,v,w,z})) : type_of% (@Classical.choice.{z}) :=
  fun {α} inhabited => @fix PUnit.{u} (fun _ => PUnit.{v}) (fun _ _ => PUnit.{w}) (fun _ _ _ => α)
    (fun _ _ _ => inhabited) (fun _ _ => True) (fun x y z next => next x y z trivial)
    PUnit.unit PUnit.unit PUnit.unit

def sorryAxFromUnsafeCast (castAny : type_of% (@unsafeCast.{u,v})) : type_of% (@sorryAx.{v}) :=
  fun α _ => @castAny PUnit.{u} α PUnit.unit

def choiceFromLeftInv (leftInv : type_of% (@Lean.Grind.leftInv.{u,u+1})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited => @leftInv α (Option (PLift α)) (fun a => some ⟨a⟩)
    (fun _ _ h => congrArg PLift.down (Option.some.inj h)) inhabited none

def choiceFromRepeatAtType (loop : type_of% (@repeatM.{u,u})) : type_of% (@Classical.choice.{u+1}) :=
  fun {α} inhabited =>
    @loop PUnit.{u+1} Id inferInstance α inhabited (fun x => Sum.inl x) PUnit.unit

def choiceFromRepeatM (loop : type_of% (@repeatM.{u,u})) : type_of% (@Classical.choice.{u}) :=
  fun {α} inhabited =>
    let wrapped : Nonempty (PLift α) := inhabited.elim (fun a => ⟨⟨a⟩⟩)
    (@choiceFromRepeatAtType loop (PLift α) wrapped).down

/- Specialize each range interface to a singleton. Its comparison expresses any proposition
and its size is one. Double negation is exactly what the zero-size law needs. -/
theorem dneFromClosedRange (range : type_of% (@Std.Rxc.size_pos_iff_le.{0}))
    (p : Prop) (nn : ¬¬p) : p := by
  letI : LE Unit := ⟨fun _ _ => p⟩
  letI : Std.PRange.UpwardEnumerable Unit := ⟨fun _ => none, fun _ _ => none⟩
  letI : Std.Rxc.HasSize Unit := ⟨fun _ _ => 1⟩
  letI : Std.Rxc.LawfulHasSize Unit :=
    ⟨fun _ _ denied => (nn denied).elim, fun _ _ _ _ => rfl,
      fun _ _ _ _ impossible => nomatch impossible⟩
  exact (@range Unit _ _ _ _ () ()).mp (Nat.lt_succ_self 0)

theorem dneFromOpenRange (range : type_of% (@Std.Rxo.size_pos_iff_lt.{0}))
    (p : Prop) (nn : ¬¬p) : p := by
  letI : LT Unit := ⟨fun _ _ => p⟩
  letI : Std.PRange.UpwardEnumerable Unit := ⟨fun _ => none, fun _ _ => none⟩
  letI : Std.Rxo.HasSize Unit := ⟨fun _ _ => 1⟩
  letI : Std.Rxo.LawfulHasSize Unit :=
    ⟨fun _ _ denied => (nn denied).elim, fun _ _ _ _ => rfl,
      fun _ _ _ _ impossible => nomatch impossible⟩
  exact (@range Unit _ _ _ _ () ()).mp (Nat.lt_succ_self 0)

theorem excludedMiddleFromDNE (dne : ∀ p : Prop, ¬¬p → p) (p : Prop) : p ∨ ¬p :=
  dne _ fun neither => neither (.inr fun hp => neither (.inl hp))

namespace PropositionalChoice

/-- Existence of one selector for all nonempty sorts at this universe. -/
abbrev Selection := Nonempty (type_of% (@Classical.choice.{u}))

private def unliftChoice (select : (t : NonemptyType.{u}) → t.type) : type_of% (@Classical.choice.{u}) :=
  fun {α} h => (select ⟨PLift α, h.elim fun a => ⟨⟨a⟩⟩⟩).down

theorem ofProducts (product : type_of% (@Pi.instNonempty.{u+2,u+1})) : Selection.{u} := by
  have inhabited (t : NonemptyType.{u}) : Nonempty t.type := t.property
  exact (@product NonemptyType (fun t => t.type) inhabited).elim fun select => ⟨unliftChoice select⟩

theorem ofChoice (choose : type_of% (@Classical.axiomOfChoice.{u+2,u+1})) : Selection.{u} := by
  have entries (t : NonemptyType.{u}) : ∃ _ : t.type, True :=
    t.property.elim fun x => ⟨x, trivial⟩
  obtain ⟨select, _⟩ := choose entries
  exact ⟨unliftChoice select⟩

theorem ofSkolem (split : type_of% (@Classical.skolem.{u+2,u+1})) : Selection.{u} :=
  ofChoice (@split _ _ _ |>.mp)

/-- Skolemization and relational choice have equivalent full statements at the same universes. -/
theorem choiceIffSkolem :
    (type_of% @Classical.axiomOfChoice.{u,v}) ↔ (type_of% @Classical.skolem.{u,v}) :=
  ⟨fun choice {_ _ _} => ⟨choice, fun ⟨f, hf⟩ x => ⟨f x, hf x⟩⟩,
   fun skolem {_ _ _} => skolem.mp⟩

/-- A nonempty dependent product supplies a simultaneous family of witnesses by using subtype fibers. -/
theorem choiceIffProducts :
    (type_of% @Classical.axiomOfChoice.{u,v+1}) ↔ (type_of% @Pi.instNonempty.{u,v+1}) := by
  constructor
  · intro choose α β fibers
    obtain ⟨f, _⟩ := @choose α β (fun _ _ => True) (fun i => (fibers i).elim fun x => ⟨x, trivial⟩)
    exact ⟨f⟩
  · intro product α β r witnesses
    have fibers (i : α) : Nonempty {y : β i // r i y} :=
      (witnesses i).elim fun y hy => ⟨⟨y, hy⟩⟩
    exact (@product α (fun i => {y : β i // r i y}) fibers).elim fun f =>
      ⟨fun i => (f i).val, fun i => (f i).property⟩

/-- Choice into propositions admits a term uniform in the universe of the index. -/
theorem choiceIntoProp : type_of% @Classical.axiomOfChoice.{u,0} := by
  intro α β r witnesses
  let f (i : α) : β i := (witnesses i).elim fun h _ => h
  exact ⟨f, fun i => (witnesses i).elim fun _ hy => hy⟩

theorem skolemIntoProp : type_of% @Classical.skolem.{u,0} :=
  choiceIffSkolem.mp @choiceIntoProp

theorem productsIntoProp : type_of% @Pi.instNonempty.{u,0} :=
  fun {_ _} fibers => ⟨fun i => (fibers i).elim id⟩

end PropositionalChoice

namespace GrindQuantifiers

theorem ofNormalizedAlternatives (law : type_of% @Lean.Grind.em) : type_of% @Classical.em := law

theorem ofNegatedForall (law : type_of% @Lean.Grind.not_forall.{0}) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn =>
    ((@law p (fun _ => False)).mp nn).elim fun hp _ => hp

theorem ofNegatedImplication (law : type_of% @Lean.Grind.not_implies) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn => ((law p False).mp nn).1

theorem ofForallImplication (law : type_of% @Lean.Grind.forall_imp_eq_or.{0}) : type_of% @Classical.em :=
  fun p => ((@law True (fun _ => p) p).mp (fun f => f trivial)).elim
    (fun h => h.elim fun _ np => Or.inr np) Or.inl

theorem ofForallOr (law : type_of% @Lean.Grind.forall_or_forall.{0,0}) : type_of% @Classical.em :=
  fun p => (@law True (fun _ => p) (fun _ => p) (fun _ _ => False)).mpr
    (fun _ hp => Or.inl hp) trivial

theorem ofOrForall (law : type_of% @Lean.Grind.forall_forall_or.{0,0}) : type_of% @Classical.em :=
  fun p => ((@law True (fun _ => p) (fun _ => p) (fun _ _ => False)).mpr
    (fun _ hp => Or.inr hp) trivial).elim Or.inr Or.inl

theorem ofNegatedConjunction (law : type_of% @Lean.Grind.not_and) (p : Prop) : ¬p ∨ ¬¬p :=
  (law p (¬p)).mp fun ⟨hp, np⟩ => np hp

end GrindQuantifiers

namespace ClassicalDecisionEquations

abbrev Transfer := type_of% @Classical.decidable_of_decidable_not
theorem decideNot (transfer : Transfer) (p : Prop) [hn : Decidable (¬p)] :
    @decide (¬p) hn = !(@decide p (@transfer p hn)) := by
  generalize @transfer p hn = d
  cases hn <;> cases d <;> first | rfl | contradiction

private theorem dependent {α : Sort u} {p : Prop} (d : Decidable p) (hn : Decidable (¬p))
    (x : ¬p → α) (y : ¬¬p → α) :
    @dite α (¬p) hn x y = @dite α p d (fun h => y (fun n => n h)) x := by
  cases hn <;> cases d <;> first | rfl | contradiction

theorem diteNot (transfer : Transfer) {p : Prop} {α : Sort u} [hn : Decidable (¬p)]
    (x : ¬p → α) (y : ¬¬p → α) :
    @dite α (¬p) hn x y = @dite α p (@transfer p hn) (fun h => y (fun n => n h)) x :=
  dependent (@transfer p hn) hn x y

theorem iteNot (transfer : Transfer) {α : Sort u} (p : Prop) [hn : Decidable (¬p)] (x y : α) :
    @ite α (¬p) hn x y = @ite α p (@transfer p hn) y x :=
  dependent (@transfer p hn) hn (fun _ => x) (fun _ => y)

def rules : List (Name × Name) := [
  (``Classical.decide_not, ``decideNot), (``Classical.dite_not, ``diteNot), (``Classical.ite_not, ``iteNot)]

/- Check the exact physical type with its decision transfer replaced by an arbitrary
function of the same type, retaining all the other binders and both equality endpoints. -/
run_cmd
  let env ← getEnv
  let some idx := env.getModuleIdx? `Init.Classical | throwError "missing Init.Classical"
  let transfer ← getConstInfo ``Classical.decidable_of_decidable_not
  for (name, witness) in rules do
    let some source := env.header.moduleData[idx]!.constants.find? (·.name == name)
      | throwError "missing decision equation {name}"
    let proof ← getConstInfo witness
    let levels := proof.levelParams.map Level.param
    unless levels.length == source.numLevelParams do throwError "incorrect universes for {name}"
    let original := source.type.instantiateLevelParams source.levelParams levels
    unless original.getUsedConstantsAsSet.contains transfer.name do throwError "no decision transfer in {name}"
    let expected ← Elab.Command.liftCoreM <| Meta.MetaM.run' <|
      Meta.withLocalDeclD `port transfer.type fun port => do
        let law := original.replace fun e => if e.isConstOf transfer.name then some port else none
        Meta.mkForallFVars #[port] law
    unless Kernel.isDefEqGuarded env {} expected proof.type do throwError "equation mismatch for {name}"

end ClassicalDecisionEquations

namespace ClassicalConsequences

/-- A test for equality with the zero stream whose answer cannot be determined on any finite prefix. -/
def DiscontinuousZeroTest : Prop :=
  ∃ test : (Nat → Bool) → Bool,
    (∀ f, test f = true ↔ f = fun _ => false) ∧
    ¬ ∃ bound : Nat, ∀ f, (∀ i, i < bound → f i = false) → test f = test (fun _ => false)

theorem ofTypeDecidableEq (classify : type_of% @Classical.typeDecidableEq.{1}) :
    DiscontinuousZeroTest := by
  let zero : Nat → Bool := fun _ => false
  let test (f : Nat → Bool) := @decide (f = zero) (classify (Nat → Bool) f zero)
  have correct (f : Nat → Bool) : test f = true ↔ f = zero := by
    letI := classify (Nat → Bool) f zero
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  refine ⟨test, correct, ?_⟩
  intro ⟨bound, same⟩
  let spike (i : Nat) := decide (i = bound)
  have off (i : Nat) (hi : i < bound) : spike i = false :=
    decide_eq_false (Nat.ne_of_lt hi)
  have eq := (correct spike).mp ((same spike off).trans ((correct zero).mpr rfl))
  exact Bool.noConfusion ((decide_eq_true (rfl : bound = bound)).symm.trans (congrFun eq bound))

/-- De Morgan's law on a proposition and its negation yields weak excluded middle. -/
theorem weakMiddleOfDeMorgan (law : type_of% @Classical.not_and_iff_not_or_not) (p : Prop) :
    ¬p ∨ ¬¬p :=
  (@law p (¬p)).mp fun ⟨hp, hn⟩ => hn hp

/-- Weak excluded middle is sufficient at arbitrary propositions. -/
theorem deMorganOfWeakMiddle (weak : ∀ p : Prop, ¬p ∨ ¬¬p) :
    type_of% @Classical.not_and_iff_not_or_not := by
  intro a b
  constructor
  · intro h
    exact (weak a).elim Or.inl (fun nna => Or.inr fun hb => nna (fun ha => h ⟨ha, hb⟩))
  · intro h ab
    exact h.elim (fun na => na ab.1) (fun nb => nb ab.2)


theorem ofByCases (cases : type_of% @Classical.byCases) : type_of% @Classical.em :=
  fun _ => cases Or.inl Or.inr

theorem ofContradiction (dne : type_of% @Classical.byContradiction) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun _ => dne

theorem ofNotNot (law : type_of% @Classical.not_not) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun _ => law.mp

private theorem ofDecision {p : Prop} : Decidable p → p ∨ ¬p
  | .isTrue yes => .inl yes
  | .isFalse no => .inr no

theorem ofPropDecidable (dec : type_of% @Classical.propDecidable) : type_of% @Classical.em :=
  fun p => ofDecision (dec p)

theorem ofInhabitedDecision (dec : type_of% @Classical.decidableInhabited) : type_of% @Classical.em :=
  fun p => ofDecision (dec p).default

theorem ofNonemptyDecision (dec : type_of% @Classical.instNonemptyDecidable) : type_of% @Classical.em :=
  fun p => (dec p).elim ofDecision

theorem ofDecidableNot (transfer : type_of% @Classical.decidable_of_decidable_not) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn => match @transfer p (.isFalse nn) with
    | .isTrue hp => hp
    | .isFalse np => (nn np).elim

theorem ofNotForall (law : type_of% @Classical.not_forall.{0}) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn => ((@law p (fun _ => False)).mp nn).elim fun hp _ => hp

theorem ofNotForallNot (law : type_of% @Classical.not_forall_not.{1}) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn =>
    ((@law Unit (fun _ => p)).mp (fun denied => nn (denied ()))).elim fun _ hp => hp

theorem ofNotExistsNot (law : type_of% @Classical.not_exists_not.{1}) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn =>
    (@law Unit (fun _ => p)).mp (fun ex => ex.elim fun _ np => nn np) ()

theorem ofForallOrExists (law : type_of% @Classical.forall_or_exists_not.{1}) : type_of% @Classical.em :=
  fun p => (@law Unit (fun _ => p)).elim (fun all => .inl (all ())) (fun ex => ex.elim fun _ np => .inr np)

theorem ofExistsOrForall (law : type_of% @Classical.exists_or_forall_not.{1}) : type_of% @Classical.em :=
  fun p => (@law Unit (fun _ => p)).elim (fun ex => ex.elim fun _ hp => .inl hp) (fun none => .inr (none ()))

theorem ofOrImpLeft (law : type_of% @Classical.or_iff_not_imp_left) : type_of% @Classical.em :=
  fun p => (@law p (¬p)).mpr id

theorem ofOrImpRight (law : type_of% @Classical.or_iff_not_imp_right) : type_of% @Classical.em :=
  fun p => ((@law (¬p) p).mpr id).elim Or.inr Or.inl

theorem ofNotImp (law : type_of% @Classical.not_imp) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn => ((@law p False).mp nn).1

theorem ofNotIff (law : type_of% @Classical.not_iff) : type_of% @Classical.em :=
  excludedMiddleFromDNE fun p nn =>
    ((@law False p).mp (fun equiv => nn equiv.mpr)).mp id

theorem ofImpLeft (law : type_of% @Classical.imp_iff_left_iff) : type_of% @Classical.em :=
  fun p => (@law (¬p) p).mp ⟨fun np _ => np, fun both hp => both hp hp⟩

theorem ofImpRight (law : type_of% @Classical.imp_iff_right_iff) : type_of% @Classical.em :=
  fun p => (@law p (¬p)).mp ⟨fun both hp => both hp hp, fun np _ => np⟩

theorem ofAndOrImp (law : type_of% @Classical.and_or_imp) : type_of% @Classical.em :=
  fun p => ((@law p True False).mpr (fun _ => .inl trivial)).elim (fun yes => .inl yes.1) Or.inr

theorem ofTwoImplications (law : type_of% @Classical.imp_and_neg_imp_iff) : type_of% @Classical.em :=
  fun p => (law p).mp ⟨Or.inl, Or.inr⟩

theorem ofExcludedMiddle (law : type_of% @Classical.em) : type_of% @Classical.em := law

/-- Names are paired with reductions so the gap report and the fresh replay use the same witnesses. -/
def witnesses : List (Name × Name) := [
  (``Classical.byCases, ``ofByCases), (``Classical.byContradiction, ``ofContradiction),
  (``Classical.not_not, ``ofNotNot), (``Classical.propDecidable, ``ofPropDecidable),
  (``Classical.decidableInhabited, ``ofInhabitedDecision), (``Classical.instNonemptyDecidable, ``ofNonemptyDecision),
  (``Classical.decidable_of_decidable_not, ``ofDecidableNot), (``Classical.not_forall, ``ofNotForall),
  (``Classical.not_forall_not, ``ofNotForallNot), (``Classical.not_exists_not, ``ofNotExistsNot),
  (``Classical.forall_or_exists_not, ``ofForallOrExists), (``Classical.exists_or_forall_not, ``ofExistsOrForall),
  (``Classical.or_iff_not_imp_left, ``ofOrImpLeft), (``Classical.or_iff_not_imp_right, ``ofOrImpRight),
  (``Classical.not_imp, ``ofNotImp), (``Classical.not_imp_iff_and_not, ``ofNotImp),
  (``Classical.not_iff, ``ofNotIff), (``Classical.imp_iff_left_iff, ``ofImpLeft),
  (``Classical.imp_iff_right_iff, ``ofImpRight), (``Classical.and_or_imp, ``ofAndOrImp),
  (``Classical.imp_and_neg_imp_iff, ``ofTwoImplications), (``Classical.em, ``ofExcludedMiddle)]

end ClassicalConsequences

namespace EmbeddingRange

/-- A retraction of the inclusion of {false} ∪ {true | p} must decide p at true. -/
theorem ofExists (split : type_of% @Function.Injective.exists_leftInverse.{1,1}) : type_of% @Classical.em := by
  intro p
  let T := {b : Bool // b = false ∨ p}
  letI : Nonempty T := ⟨⟨false, .inl rfl⟩⟩
  obtain ⟨back, retract⟩ := @split T Bool Subtype.val (fun _ _ => Subtype.ext) _
  cases h : (back true).val with
  | false =>
    right
    intro hp
    have atTrue := congrArg Subtype.val (retract (⟨true, .inr hp⟩ : T))
    exact Bool.noConfusion (h.symm.trans atTrue)
  | true =>
    exact (back true).property.elim (fun atFalse => Bool.noConfusion (h.symm.trans atFalse)) Or.inl

set_option linter.deprecated false in
theorem ofLeftInverse (split : type_of% @Function.Injective.leftInverse.{1,1}) : type_of% @Classical.em :=
  ofExists fun {α β f} hf hα => @split α β f hf hα

/-- Propositional unique choice for a small family of inhabited subsingleton fibers. -/
abbrev UniqueSections : Prop := ∀ {ι : Type} (F : ι → Type) [∀ i, Subsingleton (F i)],
  (∀ i, Nonempty (F i)) → Nonempty (∀ i, F i)

/-- An inverse to the injective projection of a subsingleton family supplies a section.
The extra point makes the source inhabited even when the index type is empty. -/
theorem sectionsOfExists (split : type_of% @Function.Injective.exists_leftInverse.{1,1}) : UniqueSections := by
  intro ι F fibers inhabited
  let forget : Option ((i : ι) × F i) → Option ι := Option.map Sigma.fst
  have inj : Function.Injective forget := by
    intro x y h
    cases x with
    | none => cases y with | none => rfl | some b => nomatch h
    | some a =>
      cases y with
      | none => nomatch h
      | some b =>
        obtain ⟨i, x⟩ := a
        obtain ⟨j, y⟩ := b
        have eq : i = j := Option.some.inj h
        subst j
        exact congrArg (fun z => some (Sigma.mk i z)) (Subsingleton.elim x y)
  obtain ⟨back, law⟩ := @split _ _ forget inj ⟨none⟩
  have covers (i : ι) : forget (back (some i)) = some i := (inhabited i).elim fun a =>
    congrArg forget (law (some ⟨i, a⟩))
  refine ⟨fun i => ?_⟩
  generalize h : back (some i) = v
  have index := (congrArg forget h).symm.trans (covers i)
  cases v with
  | none => nomatch index
  | some v => exact (Option.some.inj index) ▸ v.2

/-- The small-universe splitting principle combines excluded middle and unique choice. -/
abbrev SplittingPrinciple : Prop := (type_of% @Classical.em) ∧ UniqueSections

/-- Off the image a chosen default suffices. In the image, injectivity makes the
preimage unique, so the fibers below require only propositional unique choice. -/
theorem existsIff : (type_of% @Function.Injective.exists_leftInverse.{1,1}) ↔
    SplittingPrinciple := by
  constructor
  · exact fun split => ⟨ofExists split, sectionsOfExists split⟩
  · rintro ⟨em, choose⟩ α β f inj ⟨a₀⟩
    let F (b : β) := {a : α // (∀ x, f x = b → a = x) ∧ ((¬ ∃ x, f x = b) → a = a₀)}
    letI (b : β) : Subsingleton (F b) := ⟨fun x y => by
      apply Subtype.ext
      cases em (∃ a, f a = b) with
      | inl image => obtain ⟨a, h⟩ := image; exact (x.2.1 a h).trans (y.2.1 a h).symm
      | inr absent => exact (x.2.2 absent).trans (y.2.2 absent).symm⟩
    have inhabited (b : β) : Nonempty (F b) := by
      cases em (∃ a, f a = b) with
      | inl image =>
        obtain ⟨a, h⟩ := image
        exact ⟨a, fun x hx => inj (h.trans hx.symm), fun no => (no ⟨a,h⟩).elim⟩
      | inr no => exact ⟨a₀, fun x hx => (no ⟨x,hx⟩).elim, fun _ => rfl⟩
    obtain ⟨sectionFn⟩ := choose F inhabited
    exact ⟨fun b => (sectionFn b).1, fun a => (sectionFn (f a)).2.1 a rfl⟩

set_option linter.deprecated false in
theorem leftInverseIff : (type_of% @Function.Injective.leftInverse.{1,1}) ↔
    SplittingPrinciple :=
  ⟨fun split => existsIff.mp fun {α β f} hf hα => @split α β f hf hα,
   fun h {_ _} _ hf _ => existsIff.mpr h hf⟩

end EmbeddingRange

namespace LexicographicOrder

/-- Lexicographic comparison of one-element sequences can represent any proposition. -/
private theorem singletonMiddle (caseSplit : ∀ p : Prop,
    letI : LT Unit := ⟨fun _ _ => p⟩
    ¬ ¬ (([()] : List Unit) < [()]) → ([()] : List Unit) < [()]) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LT Unit := ⟨fun _ _ => q⟩
  have lt := caseSplit q (fun absent => nn (fun h => absent (List.Lex.rel h)))
  cases lt with
  | rel h => exact h
  | cons h => cases h

theorem ofListNotLE (law : type_of% (@List.not_le.{0})) : type_of% @Classical.em :=
  singletonMiddle fun p => @law Unit ⟨fun _ _ => p⟩ [()] [()] |>.mp

theorem ofArrayNotLE (law : type_of% (@Array.not_le.{0})) : type_of% @Classical.em :=
  singletonMiddle fun p => @law Unit ⟨fun _ _ => p⟩ #[()] #[()] |>.mp

theorem ofVectorNotLE (law : type_of% (@Vector.not_le.{0})) : type_of% @Classical.em :=
  singletonMiddle fun p => @law Unit 1 ⟨fun _ _ => p⟩ #v[()] #v[()] |>.mp

end LexicographicOrder

/-- The comparison from the upper Boolean point back to the lower point can encode any proposition. -/
theorem dneOfNotLT (notLT : type_of% (@Std.not_lt.{0})) (p : Prop) (nn : ¬¬p) : p := by
  let le (a b : Bool) : Prop := Bool.rec (motive := fun _ => Prop) True (Bool.rec (motive := fun _ => Prop) p True b) a
  letI : LE Bool := ⟨le⟩
  letI : LT Bool := ⟨fun a b => le a b ∧ ¬le b a⟩
  letI : Std.Total (α := Bool) (· ≤ ·) := ⟨fun a =>
    Bool.rec (motive := fun a => ∀ b, le a b ∨ le b a)
      (fun _ => Or.inl True.intro)
      (Bool.rec (motive := fun b => le true b ∨ le b true) (Or.inr True.intro) (Or.inl True.intro)) a⟩
  letI : Std.LawfulOrderLT Bool := ⟨fun _ _ => Iff.rfl⟩
  exact (@notLT Bool _ _ _ _ false true).mp (fun h => nn h.2)

theorem excludedMiddleOfNotLT (notLT : type_of% (@Std.not_lt.{0})) (p : Prop) : p ∨ ¬p :=
  excludedMiddleFromDNE (dneOfNotLT (@notLT)) p

/-- On a singleton both comparisons can express the same arbitrary proposition. -/
theorem excludedMiddleOfNotLTIff (notLT : type_of% (@Std.not_lt_iff_not_le_or_ge.{0}))
    (p : Prop) : p ∨ ¬p := by
  letI : LE Unit := ⟨fun _ _ => p⟩
  letI : LT Unit := ⟨fun _ _ => p ∧ ¬p⟩
  letI : Std.LawfulOrderLT Unit := ⟨fun _ _ => Iff.rfl⟩
  exact ((@notLT Unit _ _ _ () ()).mp (fun h => h.2 h.1)).elim Or.inr Or.inl

namespace GrindOrder

private def relation (p : Prop) (a b : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop) True (Bool.rec (motive := fun _ => Prop) p True b) a

/-- A linear preorder can encode an arbitrary proposition in its reverse comparison. -/
theorem excludedMiddleFromComparison
    (compare : type_of% (@Lean.Grind.Order.le_of_not_lt.{0})) (p : Prop) : p ∨ ¬p := by
  apply excludedMiddleFromDNE _ p
  intro q nn
  letI : LE Bool := ⟨relation q⟩
  letI : LT Bool := ⟨fun a b => relation q a b ∧ ¬ relation q b a⟩
  letI : Std.LawfulOrderLT Bool := ⟨fun _ _ => Iff.rfl⟩
  letI : Std.IsLinearPreorder Bool := {
    le_refl := by intro a; cases a <;> exact True.intro
    le_trans := by
      intro a b c ab bc
      cases a <;> cases b <;> cases c <;> first | exact True.intro | exact ab | exact bc
    le_total := by
      intro a b
      cases a <;> cases b <;> first | exact Or.inl True.intro | exact Or.inr True.intro
  }
  exact @compare Bool _ _ _ _ false true (fun lt => nn lt.2)

theorem excludedMiddleFromImplication (imp : type_of% @Lean.Grind.imp_eq) (p : Prop) : p ∨ ¬p :=
  ((imp p p).mp id).elim Or.inr Or.inl

theorem excludedMiddleFromNotNot (nn : type_of% @Lean.Grind.not_not) (p : Prop) : p ∨ ¬p :=
  (nn (p ∨ ¬p)).mp fun neither => neither (.inr fun hp => neither (.inl hp))

theorem excludedMiddleFromLookahead (look : type_of% @Lean.Grind.of_lookahead) (p : Prop) : p ∨ ¬p :=
  (look (p ∨ ¬p) fun neither => neither (.inr fun hp => neither (.inl hp))).mpr True.intro

end GrindOrder

/-- Every inhabited proposition is equal to True. -/
def InhabitedPropExt := ∀ p : Prop, p → p = True

/-- Every refuted proposition is equal to False. -/
def RefutedPropExt := ∀ p : Prop, (¬p) → p = False

theorem inhabitedPropExtOfDecision (rule : type_of% @Lean.Grind.of_decide_eq_true) :
    InhabitedPropExt :=
  fun p hp => @rule p (.isTrue hp) rfl

theorem refutedPropExtOfDecision (rule : type_of% @Lean.Grind.of_decide_eq_false) :
    RefutedPropExt :=
  fun p hn => @rule p (.isFalse hn) rfl

theorem inhabitedPropExtOfEqTrueRule (rule : type_of% @eq_true) : InhabitedPropExt :=
  fun _ hp => rule hp

theorem refutedPropExtOfEqFalseRule (rule : type_of% @eq_false) : RefutedPropExt :=
  fun _ hn => rule hn

theorem inhabitedPropExtOfProofHEq (proofHEq : type_of% @proof_irrel_heq) :
    InhabitedPropExt :=
  fun _ hp => type_eq_of_heq (proofHEq hp True.intro)

theorem inhabitedPropExtOfEqTrue (eqTrue : type_of% @eq_true_eq_id) :
    InhabitedPropExt :=
  fun p hp => ((congrFun eqTrue p).mpr hp).symm

namespace GrindNormalization

theorem normalizePositive (rule : type_of% @Lean.Grind.eq_true_eq) : InhabitedPropExt :=
  fun p hp => (rule p).mpr hp

theorem normalizeNegative (rule : type_of% @Lean.Grind.eq_false_eq) : RefutedPropExt :=
  fun p hp => (rule p).mpr hp

theorem normalizePositiveLeft (rule : type_of% @Lean.Grind.eq_eq_of_eq_true_left) : InhabitedPropExt :=
  fun p hp => ((@rule True p rfl).mpr hp).symm

theorem normalizePositiveRight (rule : type_of% @Lean.Grind.eq_eq_of_eq_true_right) : InhabitedPropExt :=
  fun p hp => (@rule p True rfl).mpr hp

/-- Lookahead classifies the inhabited case. Normalization of equality to False
then supplies the refuted case required by classical propositional completeness. -/
theorem completeIff :
    (type_of% @Classical.propComplete) ↔
      ((type_of% @Lean.Grind.of_lookahead) ∧ (type_of% @Lean.Grind.eq_false_eq)) := by
  constructor
  · intro complete
    refine ⟨fun p nn => ?_, fun p => propextFromPropComplete complete ?_⟩
    · cases complete p with
      | inl pos => exact pos
      | inr neg => exact (nn neg.mp).elim
    · refine ⟨fun neg => neg.mp, fun np => ?_⟩
      cases complete p with
      | inl pos => exact (np (pos.mpr trivial)).elim
      | inr neg => exact neg
  · rintro ⟨look, norm⟩ p
    cases GrindOrder.excludedMiddleFromLookahead look p with
    | inl hp => exact Or.inl (look p (fun np => np hp))
    | inr np => exact Or.inr (normalizeNegative norm p np)

theorem propextOfLookaheadAndNegative (look : type_of% @Lean.Grind.of_lookahead)
    (norm : type_of% @Lean.Grind.eq_false_eq) : type_of% @propext :=
  propextFromPropComplete (completeIff.mpr ⟨look, norm⟩)

/-- The non-dependent version suffices for the heterogeneous crossed congruence
at the same universe. Heterogeneous equality elimination aligns both types. -/
theorem crossedCongruences :
    (type_of% @Lean.Grind.eq_congr'.{u}) ↔ (type_of% @Lean.Grind.heq_congr'.{u}) := by
  constructor
  · intro rule α β a₁ b₁ a₂ b₂ h₁ h₂
    cases h₁
    cases h₂
    exact rule rfl rfl
  · intro rule α a₁ b₁ a₂ b₂ h₁ h₂
    exact rule (heq_of_eq h₁) (heq_of_eq h₂)

/-- Equality of the two closed, oppositely oriented Boolean equality propositions. -/
abbrev FlippedBooleanEquality : Prop := (false = true) = (true = false)

theorem booleanFlipBoundary :
    (type_of% @Lean.Grind.flip_bool_eq) ↔ FlippedBooleanEquality := by
  constructor
  · exact fun flip => flip false true
  · intro unequal a b
    cases a <;> cases b
    · rfl
    · exact unequal
    · exact unequal.symm
    · rfl

theorem booleanFlipOfCrossed
    (rule : type_of% @Lean.Grind.eq_congr'.{1}) : FlippedBooleanEquality :=
  @rule Bool false true true false rfl rfl

theorem booleanFlipOfHeterogeneousCrossed
    (rule : type_of% @Lean.Grind.heq_congr'.{1}) : FlippedBooleanEquality :=
  booleanFlipOfCrossed (crossedCongruences.mpr rule)

theorem booleanFlipOfNormalization (rule : type_of% @Lean.Grind.flip_bool_eq) :
    FlippedBooleanEquality := booleanFlipBoundary.mp rule

end GrindNormalization

end OmegaChecks.InitBoundaries
