module
public import Lean
import Lean.Replay
import all Lean.Util.CollectAxioms
import all Init.Data.Iterators.Basic
import all Init.Data.Array.Basic
import Init.Data.Array.Monadic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.List.Control
import Init.Data.List.ToArray
import Init.Data.Array.Lemmas
import all Init.Data.Array.MapIdx
import all Init.Data.List.MapIdx
import all Init.Data.Iterators.Consumers.Monadic.Loop
import all Init.Prelude
public import OmegaChecks.InitInventory.Extensionality

public section

open Lean
namespace OmegaChecks.InitBoundaries
universe u v w z

namespace MonadicTraversal

private def action {T : Type w} (k : T → T) (b : Option T) (flag : Bool) : ReaderM T (Option T) :=
  match flag with
  | false => fun x => some x
  | true => fun _ => b.map k

private theorem agree {T : Type w} {f g : T → T} (h : ∀ x, f x = g x)
    (b : Option T) (flag : Bool) : action f b flag = action g b flag := by
  cases flag with
  | false => rfl
  | true =>
    cases b with
    | none => rfl
    | some x => exact congrArg (fun y (_ : T) => some y) (h x)

private def extract {T : Type w} (r : ReaderM T (Option T)) (x : T) : T := (r x).getD x

private abbrev marked := { _b : Bool // True }

private def forward : List marked := [⟨false, trivial⟩, ⟨true, trivial⟩]
private def backward : List marked := [⟨true, trivial⟩, ⟨false, trivial⟩]

private theorem lawful (T : Type w) : LawfulMonad (ReaderM T) where
  id_map := by intros; rfl
  comp_map := by intros; rfl
  seq_pure := by intros; rfl
  seq_assoc := by intros; rfl
  map_pure := by intros; rfl
  map_const := by intros; rfl
  seqLeft_eq := by intros; rfl
  seqRight_eq := by intros; rfl
  pure_seq := by intros; rfl
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl
  pure_bind := by intros; rfl
  bind_assoc := by intros; rfl

/-- A two-element left fold observes the callback on every reader input. -/
public theorem fromListFoldl (law : type_of% @List.foldlM_subtype.{max 1 u v,max 1 u v,0}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  have eq := @law (ReaderM T) Bool (Option T) _ _ forward
    (fun b a => action f b a.val) (action g) none (fun b a _ => agree h b a)
  exact congrArg extract eq

public theorem fromListFoldr (law : type_of% @List.foldrM_subtype.{max 1 u v,max 1 u v,0}) :
    type_of% @funext.{u,v} := by
  apply funextFromEndomorphisms
  intro T f g h
  have eq := @law (ReaderM T) Bool (Option T) _ (lawful T) _ backward
    (fun a b => action f b a.val) (fun a b => action g b a) none (fun a _ b => agree h b a)
  exact congrArg extract eq

open Lean in
run_cmd
  for n in [``fromListFoldl, ``fromListFoldr] do
    unless (← collectAxioms n).isEmpty do throwError "monadic traversal witness {n} uses axioms"

example (rule : type_of% @Array.foldlM_subtype.{u,u,0}) : type_of% @List.foldlM_subtype.{u,u,0} := by
  intro m α β mon p xs f g x agree
  have eq := @rule m α β xs.length mon p xs.toArray f g x agree rfl
  change xs.toArray.foldlM f x = xs.toArray.unattach.foldlM g x 0 xs.toArray.size at eq
  rw [← Array.foldlM_toList (xs := xs.toArray)] at eq
  rw [← Array.size_unattach (xs := xs.toArray), ← Array.foldlM_toList, Array.toList_unattach] at eq
  exact eq
example (rule : type_of% @Array.foldrM_subtype.{u,u,0}) : type_of% @List.foldrM_subtype.{u,u,0} := by
  intro m α β mon laws p xs f g x agree
  have eq := @rule m α β xs.length mon laws p xs.toArray f g x agree rfl
  change xs.toArray.foldrM f x = xs.toArray.unattach.foldrM g x xs.toArray.size 0 at eq
  rw [← Array.foldrM_toList (xs := xs.toArray)] at eq
  rw [← Array.size_unattach (xs := xs.toArray), ← Array.foldrM_toList, Array.toList_unattach] at eq
  exact eq

namespace IndexedMap

/-- Two successive effects, with the conversion to an array performed after the list traversal. -/
def PairConversion := ∀ {m : Type u → Type v} [Monad m] [LawfulMonad m] {β : Type u} (x y : m β),
  (x >>= fun a => y >>= fun b => pure #[a, b]) =
    List.toArray <$> (x >>= fun a => y >>= fun b => pure [a, b])

/-- For one action the conversion follows from composition of functor maps. -/
theorem singleton [Monad m] [LawfulMonad m] (x : m β) :
    (x >>= fun a => pure #[a]) = List.toArray <$> (x >>= fun a => pure [a]) := by
  rw [bind_pure_comp, bind_pure_comp, ← LawfulFunctor.comp_map]
  rfl

private def pick {m : Type u → Type v} {β : Type u} (x y : m β) : Bool → m β
  | false => x
  | true => y

theorem fromList (rule : type_of% @List.mapIdxM_toArray.{u,v,0}) : PairConversion.{u,v} := by
  intro m mon law β x y
  exact rule (l := [false, true]) (f := fun _ b => pick x y b)

private theorem arrayAfterList [Monad m] [LawfulMonad m] (x : m (Array β)) :
    List.toArray <$> (Array.toList <$> x) = x := by
  rw [← LawfulFunctor.comp_map]
  exact id_map x

theorem fromArray (rule : type_of% @Array.toList_mapIdxM.{u,v,0}) : PairConversion.{u,v} := by
  intro m mon law β x y
  have eq := rule (xs := #[false, true]) (f := fun _ b => pick x y b)
  exact (arrayAfterList _).symm.trans (congrArg (List.toArray <$> ·) eq)

/-- The bounded callbacks specialize to the same two effects at indices zero and one. -/
example (rule : type_of% @List.mapFinIdxM_toArray.{u,v,0}) : PairConversion.{u,v} := by
  intro m mon law β x y
  exact rule (l := [false, true]) (f := fun _ b _ => pick x y b)

example (rule : type_of% @Array.toList_mapFinIdxM.{u,v,0}) : PairConversion.{u,v} := by
  intro m mon law β x y
  have eq := rule (xs := #[false, true]) (f := fun _ b _ => pick x y b)
  exact (arrayAfterList _).symm.trans (congrArg (List.toArray <$> ·) eq)

end IndexedMap

namespace SingletonSearch

/- The forward monadic search correspondences are open. Each public law specializes to
one of these reader equations. Constructor cases establish pointwise agreement. -/
private abbrev Acc (α : Type) := Option (Option α) × Unit

private def finish {m : Type → Type} [Monad m] {α : Type} (step : m (ForInStep (Acc α))) : m (Option α) := do
  let result ← (step >>= fun | .done x => pure x | .yield x => pure x)
  match result.1 with
  | some x => pure x
  | none => pure none

private def boolStep {m : Type → Type} [Monad m] (test : m Bool) : m (ForInStep (Acc Unit)) := do
  if (← test) then return .done (some (some ()), ())
  else return .yield (none, ())

/-- The pinned wildcard matcher tests bit `x.ctorIdx` of the mask `2`. Specializing
the first argument of bitwise and to `1` eliminates its termination proof. -/
private def wildcardGuard (x : Option Bool) : Prop :=
  let n := Nat.shiftRight 2 x.ctorIdx
  let masked := if _h : n = 0 then 0
    else if _h : decide (n % 2 = 1) = true then 1 else 0
  masked ≠ 1

set_option smartUnfolding false
attribute [local semireducible] Nat.bitwise
example : wildcardGuard = (fun x => Nat.hasNotBit 2 x.ctorIdx) := by
  delta Nat.hasNotBit Nat.land Nat.bitwise Nat.bitwise._unary wildcardGuard
  rfl

private noncomputable def optionStep {m : Type → Type} [Monad m] (test : m (Option Bool)) : m (ForInStep (Acc Bool)) := do
  let result ← test
  let motive (x : Option Bool) :=
    (wildcardGuard x → m (ForInStep (Acc Bool))) → m (ForInStep (Acc Bool))
  Option.rec (motive := motive) (fun tail => tail Nat.zero_ne_one)
    (fun b _ => pure (.done (some (some b), ()))) result
    (fun _ => pure (.yield (none, ())))

private def boolResult {m : Type → Type} [Monad m] (test : m Bool) : m (Option Unit) := do
  match (← test) with | true => pure (some ()) | false => pure none

private def optionResult {m : Type → Type} [Monad m] (test : m (Option Bool)) : m (Option Bool) := do
  match (← test) with
  | some b => return some b
  | none => return none

private abbrev readBool : ReaderM Bool Bool := read
private abbrev readOption : ReaderM (Option Bool) (Option Bool) := read
/-- The two singleton Boolean searches as complete reader functions. -/
def BoolFusion : Prop := finish (boolStep readBool) = boolResult readBool
/-- The two singleton option searches as complete reader functions. -/
def OptionFusion : Prop := finish (optionStep readOption) = optionResult readOption

private def taggedPredicate : ReaderM Bool (Option Unit) := do
  let tagged ← (do return if (← readBool) then some () else none)
  match tagged with
  | some a => return some a
  | none => return none

/-- On a singleton, the conversion equates the direct Boolean branch with an
option branch on the tagged result of that same predicate. -/
def PredicateFusion : Prop := boolResult readBool = taggedPredicate

example (b : Bool) : boolResult readBool b = taggedPredicate b := by cases b <;> rfl

theorem predicateOfList (rule : type_of% @List.findM?_eq_findSomeM?.{0}) : PredicateFusion := by
  letI := lawful Bool
  with_unfolding_all exact rule (m := ReaderM Bool) (p := fun _ : Unit => readBool) (as := [()])

def BoolSingleton := ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (p : m Bool),
  finish (boolStep p) = boolResult p
def OptionSingleton := ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (p : m (Option Bool)),
  finish (optionStep p) = optionResult p

theorem boolOfSingleton (h : BoolSingleton) : BoolFusion :=
  @h (ReaderM Bool) _ (lawful Bool) readBool
theorem optionOfSingleton (h : OptionSingleton) : OptionFusion :=
  @h (ReaderM (Option Bool)) _ (lawful _) readOption

example (h : type_of% @List.findM?_toArray.{0}) : BoolSingleton := by
  intro m mon laws p
  exact @h m Unit mon laws (fun _ => p) [()]

example (h : type_of% @List.findSomeM?_toArray.{0,0,0}) : OptionSingleton := by
  intro m mon laws p
  exact @h m Unit Bool mon laws (fun _ => p) [()]

example (h : type_of% @Array.findM?_toList.{0}) : BoolSingleton := by
  intro m mon laws p
  exact (@h m Unit mon laws (fun _ => p) #[()]).symm

example (h : type_of% @Array.findSomeM?_toList.{0,0,0}) : OptionSingleton := by
  intro m mon laws p
  exact (@h m Unit Bool mon laws (fun _ => p) #[()]).symm

example (b : Bool) : finish (boolStep readBool) b = boolResult readBool b := by cases b <;> rfl
example (v : Option Bool) : finish (optionStep readOption) v = optionResult readOption v := by cases v <;> rfl

run_cmd
  let env ← getEnv
  for name in [``BoolFusion, ``OptionFusion, ``PredicateFusion] do
    let some (.defnInfo law) := env.find? name | throwError "missing singleton search law {name}"
    let some (_, left, right) := law.value.eq? | throwError "expected an equality in {name}"
    if Kernel.isDefEqGuarded env {} left right then
      throwError "the two readers in {name} are now definitionally equal"
  for witness in [``boolOfSingleton, ``optionOfSingleton, ``predicateOfList] do
    unless (← collectAxioms witness).isEmpty do throwError "singleton search witness {witness} uses axioms"

end SingletonSearch

end MonadicTraversal

namespace RangeMap

open Std.PRange

@[instance_reducible] private def successor {T : Type w} (f : T → T) : UpwardEnumerable T where
  succ? x := some (f x)
  succMany? _ x := some x

private theorem endomorphisms {T : Type w}
    (commutes : type_of% @UpwardEnumerable.Map.succ?_toFun'.{w,w})
    {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  let φ : @UpwardEnumerable.Map T T (successor g) (successor f) :=
    @UpwardEnumerable.Map.mk T T (successor g) (successor f) id (fun {_ _} h => h)
      (fun x => congrArg some (agree x)) (fun _ _ => rfl)
  have e := @commutes T T (successor g) (successor f) φ
  exact congrArg (fun k x => (k x).getD x) e

/-- The function equality for successor-preserving maps entails dependent function extensionality. -/
public theorem funextFromSuccMap (commutes : type_of% @UpwardEnumerable.Map.succ?_toFun'.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (endomorphisms commutes)

open Lean in
run_cmd
  unless (← collectAxioms ``funextFromSuccMap).isEmpty do
    throwError "the range-map extensionality witness depends on axioms"

end RangeMap

namespace IteratorLoopCongruence

open Std Std.Iterators

private abbrev State := ULift.{u} Bool

private def wrap {α : Type u} (x : α) : Shrink α :=
  cast (congrFun (Std.Internal.idOpaque (α := Type u)).property.symm α) x

@[instance_reducible] private def itInst (T : Type u) : Iterator State.{u} Id T where
  IsPlausibleStep it step := match step with
    | .done => True
    | .yield next _ => it.internalState.down = true ∧ next.internalState.down = false
    | .skip _ => False
  step _ := wrap ⟨.done, trivial⟩

private theorem finite (T : Type u) : letI := itInst T; Finite State.{u} Id := by
  letI := itInst T
  apply Finite.of_finitenessRelation
  let measure := fun it : IterM (α := State.{u}) Id T => Bool.toNat it.internalState.down
  refine ⟨InvImage Nat.lt measure, InvImage.wf _ Nat.lt_wfRel.wf, ?_⟩
  intro it next h
  obtain ⟨step, dest, h⟩ := h
  cases step with
  | yield j b =>
    cases Option.some.inj dest
    change it.internalState.down = true ∧ next.internalState.down = false at h
    change next.internalState.down.toNat < it.internalState.down.toNat
    rw [h.1, h.2]
    exact Nat.zero_lt_one
  | skip j => contradiction
  | done => cases dest

@[instance_reducible] private def reading (T : Type u) :
    letI := itInst T; IteratorLoop State.{u} Id (ReaderM T) := by
  letI := itInst T
  refine ⟨fun _ γ Pl it init f x => ?_⟩
  cases active : it.internalState.down with
  | false => exact init
  | true =>
    have out : it.IsPlausibleIndirectOutput x :=
      .direct ⟨⟨⟨false⟩⟩, ⟨active, rfl⟩⟩
    exact ForInStep.casesOn (f x out init x).val id id

private theorem endomorphisms (combine : type_of% (@Iter.forIn_congr.{u,u}))
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := itInst T
  letI := finite T
  letI := reading T
  let i : Iter (α := State.{u}) T := ⟨⟨true⟩⟩
  let finish (y : T) : ReaderM T (ForInStep (Option T)) := fun _ => .done (some y)
  have eq := combine (ita := i) (itb := i) rfl (b := (none : Option T)) rfl
    (f := fun x _ => finish (f x)) (g := fun x _ => finish (g x)) (fun x _ => congrArg finish (agree x))
  exact congrArg (fun (k : T → Option T) x => (k x).getD x) eq


private theorem monadicEndomorphisms (combine : type_of% (@IterM.forIn_congr.{u,u,u}))
    {T : Type u} {f g : T → T} (agree : ∀ x, f x = g x) : f = g := by
  letI := itInst T
  letI := reading T
  letI : MonadLift Id (ReaderM T) := ⟨fun x _ => x⟩
  let i : IterM (α := State.{u}) Id T := ⟨⟨true⟩⟩
  let finish (y : T) : ReaderM T (ForInStep (Option T)) := fun _ => .done (some y)
  have eq := combine (ita := i) (itb := i) rfl (b := (none : Option T)) rfl
    (f := fun x _ => finish (f x)) (g := fun x _ => finish (g x)) (fun x _ => congrArg finish (agree x))
  exact congrArg (fun (k : T → Option T) x => (k x).getD x) eq

private theorem forgetMonadicMembership (combine : type_of% @IterM.forIn'_congr.{u,u,u}) :
    type_of% @IterM.forIn_congr.{u,u,u} := by
  intro α β m n monN monM iterator loop lift γ ita itb w b b' hb f g agree
  cases w
  exact combine rfl hb (fun a _ c => agree a c)

public theorem funextFromMonadicCongr (combine : type_of% @IterM.forIn_congr.{max 1 u v, max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (monadicEndomorphisms combine)

public theorem funextFromMonadicCongr' (combine : type_of% @IterM.forIn'_congr.{max 1 u v, max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromMonadicCongr (forgetMonadicMembership combine)

/-- Membership-dependent loop congruence specializes to ordinary loop congruence. -/
private theorem forgetMembership (combine : type_of% (@Iter.forIn'_congr.{u,u})) :
    type_of% (@Iter.forIn_congr.{u,u}) := by
  intro α β m monad iterator fin loop γ ita itb w b b' hb f g agree
  cases w
  exact combine rfl hb (fun a _ c => agree a c)

/-- A loop on a reader can select an output at each argument of the reader. -/
public theorem funextFromCongr (combine : type_of% @Iter.forIn_congr.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromEndomorphisms (endomorphisms combine)

public theorem funextFromCongr' (combine : type_of% @Iter.forIn'_congr.{max 1 u v, max 1 u v}) :
    type_of% @funext.{u,v} :=
  funextFromCongr (forgetMembership combine)

open Lean in
run_cmd
  for n in [``funextFromCongr, ``funextFromCongr', ``funextFromMonadicCongr, ``funextFromMonadicCongr'] do
    unless (← collectAxioms n).isEmpty do throwError "iterator congruence witness {n} uses axioms"

end IteratorLoopCongruence

namespace ArrayLoopCongruence

private def sample (f : T → T) : Option T → Bool → ReaderM T (Option T)
  | _, false => fun x => some x
  | none, true => fun _ => none
  | some a, true => fun _ => some (f a)

private theorem sampleCongr {f g : T → T} (h : ∀ x, f x = g x) :
    ∀ s bit, sample f s bit = sample g s bit := by
  intro s bit
  cases bit with
  | false => rfl
  | true =>
    cases s with
    | none => rfl
    | some x => exact congrArg (fun y _ => some y) (h x)

private def readBack (k : ReaderM T (Option T)) (x : T) := (k x).getD x

private theorem fromLeft (fold : type_of% @Array.foldlM_congr.{u,0,u}) {T : Type u}
    {f g : T → T} (h : ∀ x, f x = g x) : f = g := by
  have e := fold (m := ReaderM T) (xs := #[false,true]) (b := none) rfl (sampleCongr h)
    (start := 0) (stop := 2) rfl rfl
  exact congrArg readBack e

private theorem fromRight (fold : type_of% @Array.foldrM_congr.{0,u,u}) {T : Type u}
    {f g : T → T} (h : ∀ x, f x = g x) : f = g := by
  have e := fold (m := ReaderM T) (xs := #[true,false]) (b := none) (f := fun bit s => sample f s bit)
    (g := fun bit s => sample g s bit) rfl (fun bit s => sampleCongr h s bit)
    (start := 2) (stop := 0) rfl rfl
  exact congrArg readBack e

private def sampleStep (f : T → T) (bit : Bool) (s : Option T) (x : T) : ForInStep (Option T) :=
  .yield (sample f s bit x)

private theorem stepCongr {f g : T → T} (h : ∀ x, f x = g x) (bit : Bool) (s : Option T) :
    sampleStep f bit s = sampleStep g bit s :=
  congrArg (fun k x => ForInStep.yield (k x)) (sampleCongr h s bit)

/-- The pinned array loop using the membership proof from the underlying list. -/
public def arrayLoop {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] (Array.Mem.mk (List.getElem_mem this)) b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

public abbrev ArrayCongruence.{levelIn,levelOut} :=
  ∀ {m : Type levelIn → Type levelOut} {α : Type} {β : Type levelIn} [Monad m] {as bs : Array α} (w : as = bs)
    {b b' : β} (_hb : b = b') {f : (a : α) → a ∈ as → β → m (ForInStep β)}
    {g : (a : α) → a ∈ bs → β → m (ForInStep β)},
    (∀ a h s, f a (w.symm ▸ h) s = g a h s) → arrayLoop as b f = arrayLoop bs b' g

public abbrev VectorCongruence.{levelIn,levelOut} :=
  ∀ {m : Type levelIn → Type levelOut} {α : Type} {n : Nat} {β : Type levelIn} [Monad m] {xs ys : Vector α n} (w : xs = ys)
    {b b' : β} (_hb : b = b') {f : (a : α) → a ∈ xs → β → m (ForInStep β)}
    {g : (a : α) → a ∈ ys → β → m (ForInStep β)},
    (∀ a h s, f a (w.symm ▸ h) s = g a h s) → arrayLoop xs.toArray b (fun a ha => f a ((Vector.mem_toArray_iff a xs).mp ha)) =
      arrayLoop ys.toArray b' (fun a ha => g a ((Vector.mem_toArray_iff a ys).mp ha))

private theorem arrayLoop_eq : @arrayLoop = @Array.forIn' := by
  delta arrayLoop Array.forIn' Array.forIn'.loop Array.forIn'.loop._f arrayLoop.loop arrayLoop.loop._f
  rfl
example : ArrayCongruence.{u,u} := by
  unfold ArrayCongruence
  rw [arrayLoop_eq]
  exact @Array.forIn'_congr.{u,u,0}
example : VectorCongruence.{u,u} := by
  unfold VectorCongruence
  rw [arrayLoop_eq]
  exact @Vector.forIn'_congr.{u,u,0}

private theorem fromForIn (combine : ArrayCongruence.{u,u}) {T : Type u}
    {f g : T → T} (h : ∀ x, f x = g x) : f = g := by
  have e := combine (m := ReaderM T) (as := #[false,true]) (b := none) rfl rfl
    (f := fun bit _ => sampleStep f bit) (g := fun bit _ => sampleStep g bit) (fun bit _ s => stepCongr h bit s)
  exact congrArg readBack e

private theorem fromVecForIn (combine : VectorCongruence.{u,u}) {T : Type u}
    {f g : T → T} (h : ∀ x, f x = g x) : f = g := by
  have e := combine (m := ReaderM T) (xs := #v[false,true]) (b := none) rfl rfl
    (f := fun bit _ => sampleStep f bit) (g := fun bit _ => sampleStep g bit) (fun bit _ s => stepCongr h bit s)
  exact congrArg readBack e
public theorem forInCongr (combine : ArrayCongruence.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromForIn combine)

private theorem appendHead (before : List α) (a : α) (after : List α) :
    (before ++ [a]) ++ after = before ++ a :: after := by
  induction before with
  | nil => rfl
  | cons x _ ih => exact congrArg (x :: ·) ih

public def listLoop {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : List α) (init : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec loop : (as' : List α) → (b : β) → Exists (fun bs => bs ++ as' = as) → m β
    | [], b, _    => pure b
    | a::as', b, h => do
      have : a ∈ as := by
        clear f
        have ⟨bs, h⟩ := h
        subst h
        exact List.mem_append_right _ (List.Mem.head ..)
      match (← f a this b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b =>
        have : Exists (fun bs => bs ++ as' = as) := have ⟨bs, h⟩ := h; ⟨bs ++ [a], (appendHead bs a as').trans h⟩
        loop as' b this
  loop as init ⟨[], rfl⟩

public abbrev ListCongruence.{levelIn,levelOut} :=
  ∀ {m : Type levelIn → Type levelOut} {α : Type} {β : Type levelIn} [Monad m] {as bs : List α} (w : as = bs)
    {b b' : β} (_hb : b = b') {f : (a : α) → a ∈ as → β → m (ForInStep β)}
    {g : (a : α) → a ∈ bs → β → m (ForInStep β)},
    (∀ a h s, f a (w.symm ▸ h) s = g a h s) → listLoop as b f = listLoop bs b' g

private theorem listLoop_eq : @listLoop = @List.forIn' := by
  delta listLoop List.forIn' listLoop.loop List.forIn'.loop
  rfl
example : ListCongruence.{u,u} := by
  unfold ListCongruence
  rw [listLoop_eq]
  exact @List.forIn'_congr.{u,u,0}
private theorem fromListForIn (combine : ListCongruence.{u,u}) {T : Type u}
    {f g : T → T} (h : ∀ x, f x = g x) : f = g := by
  have e := combine (m := ReaderM T) (as := [false,true]) (b := none) rfl rfl
    (f := fun bit _ => sampleStep f bit) (g := fun bit _ => sampleStep g bit) (fun bit _ s => stepCongr h bit s)
  exact congrArg readBack e
public theorem listForInCongr (combine : ListCongruence.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromListForIn combine)

public theorem vectorForInCongr (combine : VectorCongruence.{max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromVecForIn combine)

public theorem foldlCongr (combine : type_of% @Array.foldlM_congr.{max 1 u v,0,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromLeft combine)

public theorem foldrCongr (combine : type_of% @Array.foldrM_congr.{0,max 1 u v,max 1 u v}) :
    type_of% @funext.{u,v} := funextFromEndomorphisms (fromRight combine)

example (rule : type_of% @List.forIn'_loop_congr.{u,u,0}) : ListCongruence.{u,u} := by
  intro m α β mon as bs w b b' hb f g agree
  subst bs
  subst b'
  rw [listLoop_eq]
  exact rule (as := as) (bs := as) (xs := as) (b := b) ⟨[],rfl⟩ ⟨[],rfl⟩ (fun a h _ s => agree a h s)

open Lean in
run_cmd
  for n in [``foldlCongr, ``foldrCongr, ``forInCongr, ``vectorForInCongr, ``listForInCongr] do
    unless (← collectAxioms n).isEmpty do throwError "array congruence witness {n} uses axioms"

end ArrayLoopCongruence

namespace PublicAlgorithmEquations

/-- Prepend a fixed number of entries, with no assumption on the element type. -/
private def prepend {α : Type u} : (n : Nat) → (Fin n → α) → List α → List α
  | 0, _, xs => xs
  | n + 1, f, xs => f ⟨0, Nat.zero_lt_succ _⟩ :: prepend n (fun i => f i.succ) xs

private theorem prefixAux (n acc : Nat) :
    (fun (α : Type u) (f : Fin n → α) (xs : List α) => (prepend n f xs).lengthTRAux acc) =
    (fun (α : Type u) (_ : Fin n → α) (xs : List α) => xs.lengthTRAux (acc + n)) := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    have h := congrArg (fun g => fun (α : Type u) (f : Fin (n + 1) → α) (xs : List α) =>
      g α (fun i => f (Fin.succ i)) xs) (ih (acc + 1))
    change _ = (fun (α : Type u) (_ : Fin (n + 1) → α) (xs : List α) =>
      xs.lengthTRAux (acc.succ + n)) at h
    rw [Nat.succ_add] at h
    exact h

/-- Prepending `n` entries to ordinary length agrees as a function with starting
the tail-recursive accumulator at `n`, uniformly in the element type and suffix. -/
def PrefixLength := ∀ n : Nat,
  (fun (α : Type u) (f : Fin n → α) (xs : List α) => (prepend n f xs).length) =
  (fun (α : Type u) (_ : Fin n → α) (xs : List α) => xs.lengthTRAux n)

theorem ofLength : (type_of% @List.length_eq_lengthTR.{u}) ↔ PrefixLength.{u} := by
  constructor
  · intro h n
    have mapped := congrArg (fun (len : {α : Type u} → List α → Nat) =>
      fun (α : Type u) (f : Fin n → α) (xs : List α) => @len α (prepend n f xs)) h
    have shift := prefixAux.{u} n 0
    rw [Nat.zero_add] at shift
    exact mapped.trans shift
  · intro h
    exact congrArg (fun g => fun {α : Type u} (xs : List α) => g α Fin.elim0 xs) (h 0)

/-- Testing for absence after any optional step, as an equality of the operations
which take the step and the initial value as arguments. -/
def BindClassifier := ∀ (α β : Type u),
  (fun (step : α → Option β) (start : Option α) => !(start.bind step).isSome) =
  (fun (step : α → Option β) (start : Option α) => (start.bind step).isNone)

theorem ofClassifier : (type_of% @Option.not_comp_isSome.{u}) ↔ BindClassifier.{u} := by
  constructor
  · intro law α β
    exact congrArg (fun pred => fun (step : α → Option β) (start : Option α) =>
      pred (start.bind step)) (@law β)
  · intro law α
    exact congrArg (fun fusion => fun o : Option α => fusion id (some o)) (law (Option α) α)

private theorem addShift (k : Nat) :
    (fun n => (n+1)+k) = (fun n => n+(k+1)) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun g => fun n => Nat.succ (g n)) ih

/-- Move a fixed number of copies from the replication count to the initial accumulator. -/
def ReplicateAccumulator := ∀ k : Nat,
  (fun (α : Type u) (n : Nat) (a : α) => List.replicateTR.loop a n (List.replicate k a)) =
  (fun _ n a => List.replicate (n+k) a)

theorem ofReplicate : (type_of% @List.replicate_eq_replicateTR.{u}) ↔ ReplicateAccumulator.{u} := by
  constructor
  · intro law k
    induction k with
    | zero => exact congrArg (fun g => fun (α : Type u) n (a : α) => @g α n a) law.symm
    | succ k ih =>
      have shift := congrArg (fun g => fun (α : Type u) n (a : α) => g α (n+1) a) ih
      exact shift.trans (congrArg (fun g => fun (α : Type u) n (a : α) => List.replicate (g n) a) (addShift k))
  · intro law
    exact congrArg (fun g => fun {α : Type u} n (a : α) => g α n a) (law 0).symm

/-- Concatenate any sequence of chunks onto a suffix using the reverse-accumulator algorithm. -/
def AppendChunks :=
  (fun (α : Type u) (chunks : List (List α)) (tail : List α) => chunks.foldr List.append tail) =
  (fun _ chunks tail => chunks.foldr (fun xs acc => List.reverseAux (List.reverseAux xs []) acc) tail)

theorem ofAppend : (type_of% @List.append_eq_appendTR.{u}) ↔ AppendChunks.{u} := by
  constructor
  · intro law
    exact congrArg (fun g => fun (α : Type u) (chunks : List (List α)) tail =>
      chunks.foldr (@g α) tail) law
  · intro law
    exact congrArg (fun g => fun {α : Type u} (xs ys : List α) => g α [xs] ys) law

private def prefixAccumulator {α : Type u} {β : Type v} :
    (k : Nat) → (Fin k → α) → (α → β) → List β → List β
  | 0, _, _, acc => acc
  | k+1, p, f, acc => prefixAccumulator k (fun i => p i.succ) f (f (p ⟨0, Nat.zero_lt_succ _⟩) :: acc)

private theorem runPrefix (k : Nat) :
    (fun (α : Type u) (β : Type v) (f : α → β) (p : Fin k → α) (xs : List α) (acc : List β) =>
      List.mapTR.loop f (prepend k p xs) acc) =
    (fun _ _ f p xs acc => List.mapTR.loop f xs (prefixAccumulator k p f acc)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun g => fun (α : Type u) (β : Type v) (f : α → β) (p : Fin (k+1) → α) xs acc =>
      g α β f (fun i => p i.succ) xs (f (p ⟨0, Nat.zero_lt_succ _⟩) :: acc)) ih

/-- Resume the map loop after consuming a prefix of arbitrary elements. -/
def MapAfterPrefix := ∀ k : Nat,
  (fun (α : Type u) (β : Type v) (f : α → β) (p : Fin k → α) xs =>
    List.map f (prepend k p xs)) =
  (fun _ _ f p xs => List.mapTR.loop f xs (prefixAccumulator k p f []))

theorem ofMap : (type_of% @List.map_eq_mapTR.{u,v}) ↔ MapAfterPrefix.{v,u} := by
  constructor
  · intro law k
    have mapped := congrArg (fun g => fun (α : Type v) (β : Type u) (f : α → β) (p : Fin k → α) xs =>
      @g α β f (prepend k p xs)) law
    exact mapped.trans (congrArg (fun g => fun (α : Type v) (β : Type u) (f : α → β) (p : Fin k → α) xs =>
      g α β f p xs []) (runPrefix k))
  · intro law
    exact congrArg (fun g => fun {α : Type v} {β : Type u} (f : α → β) xs => g α β f Fin.elim0 xs) (law 0)

/-- Append arbitrary byte chunks to an initial buffer, taking the three array slices of the pinned copy. -/
def ByteCopyChunks :=
  (fun (initial : Array UInt8) (chunks : List (Array UInt8)) =>
    chunks.foldl (fun acc src => Array.mk (acc.toList ++ src.toList)) initial) =
  (fun initial chunks => chunks.foldl (fun acc src =>
    acc.extract 0 acc.size ++ src.extract 0 (0 + src.size) ++
      acc.extract (acc.size + min src.size (src.size - 0)) acc.size) initial)

theorem ofByteCopy : (type_of% @ByteArray.append_eq_fastAppend) ↔ ByteCopyChunks := by
  constructor
  · intro law
    exact congrArg (fun g => fun (initial : Array UInt8) (chunks : List (Array UInt8)) =>
      chunks.foldl (fun a b => (g (ByteArray.mk a) (ByteArray.mk b)).data) initial) law
  · intro law
    exact congrArg (fun g => fun (a b : ByteArray) => ByteArray.mk (g a.data [b.data])) law

end PublicAlgorithmEquations

namespace MonadicCollectionEquations

/-- Mapping the two inverse container conversions across a lawful functor transports
the complete traversal equality in either direction. -/
private theorem mapToArrayIff {m : Type u → Type v} [Functor m] [LawfulFunctor m] {α : Type u}
    (x : m (Array α)) (y : m (List α)) : x = List.toArray <$> y ↔ Array.toList <$> x = y := by
  constructor
  · intro eqn
    rw [eqn, Functor.map_map]
    exact id_map' y
  · intro eqn
    rw [← eqn, Functor.map_map]
    exact (id_map' x).symm

theorem filterM : (type_of% @Array.toList_filterM.{v}) ↔
    (type_of% @List.filterM_toArray.{v}) := by
  constructor
  · intro law m α inst lm l p
    exact (mapToArrayIff _ _).mpr (law (xs := l.toArray) (p := p))
  · intro law m α inst lm xs p
    cases xs with
    | mk l => exact (mapToArrayIff _ _).mp (law (l := l) (p := p))

theorem filterMBound : (type_of% @List.filterM_toArray'.{v}) ↔
    (type_of% @List.filterM_toArray.{v}) := by
  constructor
  · intro law m α inst lm l p
    exact law (l := l) (p := p) rfl
  · intro law m α limit inst lm l p bound
    cases bound
    exact law

theorem filterMapM : (type_of% @Array.toList_filterMapM.{u,v,w}) ↔
    (type_of% @List.filterMapM_toArray.{u,v,w}) := by
  constructor
  · intro law m α β inst lm l f
    exact (mapToArrayIff _ _).mpr (law (xs := l.toArray) (f := f))
  · intro law m α β inst lm xs f
    cases xs with
    | mk l => exact (mapToArrayIff _ _).mp (law (l := l) (f := f))

theorem filterMapMBound : (type_of% @List.filterMapM_toArray'.{u,v,w}) ↔
    (type_of% @List.filterMapM_toArray.{u,v,w}) := by
  constructor
  · intro law m α β inst lm l f
    exact law (l := l) (f := f) rfl
  · intro law m α β limit inst lm l f bound
    cases bound
    exact law

theorem flatMapM : (type_of% @Array.toList_flatMapM.{u,v,w}) ↔
    (type_of% @List.flatMapM_toArray.{u,v,w}) := by
  constructor
  · intro law m α β inst lm l f
    exact (mapToArrayIff _ _).mpr (law (xs := l.toArray) (f := f))
  · intro law m α β inst lm xs f
    cases xs with
    | mk l => exact (mapToArrayIff _ _).mp (law (l := l) (f := f))

def comparisons : List (Name × Name × Name) := [
  (``Array.toList_filterM, ``List.filterM_toArray, ``filterM),
  (``List.filterM_toArray', ``List.filterM_toArray, ``filterMBound),
  (``Array.toList_filterMapM, ``List.filterMapM_toArray, ``filterMapM),
  (``List.filterMapM_toArray', ``List.filterMapM_toArray, ``filterMapMBound),
  (``Array.toList_flatMapM, ``List.flatMapM_toArray, ``flatMapM)
]

end MonadicCollectionEquations

end OmegaChecks.InitBoundaries
