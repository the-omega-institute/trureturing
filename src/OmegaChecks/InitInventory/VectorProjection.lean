module
public import Init.Data.Vector.Monadic
public import Init.Data.Vector.Count
public import Init.Data.Fin.Fold
public import Lean
import all Lean.Util.CollectAxioms

/-! The fixed-size projection admits a Kleisli decoder with an existing computation as its fallback.
For arbitrary computations the round trip below uses pointwise congruence under their binds.
The pure and reader specializations hold under their original hypotheses. -/

public section
namespace OmegaChecks.InitBoundaries.VectorProjection
universe u v w
variable {α : Type u} {n : Nat} {m : Type u → Type v} [Monad m] [LawfulMonad m]

private def decode (fallback : m (Vector α n)) (a : Array α) : m (Vector α n) :=
  if h : a.size = n then pure ⟨a, h⟩ else fallback

omit [LawfulMonad m] in
private theorem decode_toArray (fallback : m (Vector α n)) (x : Vector α n) :
    decode fallback x.toArray = pure x :=
  dite_eq_left x.size_toArray

private theorem decode_pure (fallback : m (Vector α n)) (x : Vector α n) :
    ((Vector.toArray <$> (pure x : m (Vector α n))) >>= decode fallback) = pure x :=
  (congrArg (· >>= decode fallback) (map_pure Vector.toArray x)).trans
    ((pure_bind _ _).trans (decode_toArray fallback x))

theorem pureMapInjective (x y : Vector α n) :
    (Vector.toArray <$> (pure x : m (Vector α n))) = (Vector.toArray <$> (pure y : m (Vector α n))) ↔
      (pure x : m (Vector α n)) = pure y := by
  let fallback : m (Vector α n) := pure x
  exact ⟨fun h => (decode_pure fallback x).symm.trans
    ((congrArg (· >>= decode fallback) h).trans (decode_pure fallback y)),
    congrArg (Vector.toArray <$> ·)⟩

theorem readerMapInjective {σ : Type w} {x y : σ → Vector α n}
    (h : (fun s => (x s).toArray) = (fun s => (y s).toArray)) : x = y := by
  let recover (pair : {f : σ → Array α // ∀ s, (f s).size = n}) (s : σ) :
      Vector α n := ⟨pair.val s, pair.property s⟩
  let package (k : σ → Vector α n) : {f : σ → Array α // ∀ s, (f s).size = n} :=
    ⟨fun s => (k s).toArray, fun s => (k s).size_toArray⟩
  exact congrArg recover (show package x = package y from Subtype.ext h)

private theorem roundtrip (fallback z : m (Vector α n))
    (underBind : ∀ (f g : Vector α n → m (Vector α n)), (∀ v, f v = g v) → z >>= f = z >>= g) :
    (Vector.toArray <$> z) >>= decode fallback = z := by
  calc
    _ = (z >>= fun v => pure v.toArray) >>= decode fallback :=
      congrArg (· >>= decode fallback) (bind_pure_comp Vector.toArray z).symm
    _ = z >>= (fun v => pure v.toArray >>= decode fallback) := bind_assoc _ _ _
    _ = z >>= pure := underBind _ _ (fun v => (pure_bind _ _).trans (decode_toArray fallback v))
    _ = z := bind_pure z

theorem ofCallbackCongruence {x y : m (Vector α n)}
    (forX : ∀ (f g : Vector α n → m (Vector α n)), (∀ v, f v = g v) → x >>= f = x >>= g)
    (forY : ∀ (f g : Vector α n → m (Vector α n)), (∀ v, f v = g v) → y >>= f = y >>= g) :
    Vector.toArray <$> x = Vector.toArray <$> y ↔ x = y :=
  ⟨fun h => (roundtrip x x forX).symm.trans ((congrArg (· >>= decode x) h).trans
    (roundtrip x y forY)), congrArg (Vector.toArray <$> ·)⟩

/-- Function extensionality suffices for the two bind congruences. -/
theorem ofFunctionExtensionality (ext : type_of% @funext.{u + 1, v + 1}) :
    type_of% @Vector.map_toArray_inj.{u,v} := by
  intro m α n _ _ x y
  apply ofCallbackCongruence <;>
    exact fun f g h => congrArg _ (ext h)

@[instance_reducible] private def continuationMonad (R : Type v) :
    Monad (fun A : Type u => (A → R) → R) where
  pure a k := k a
  bind x f k := x (fun a => f a k)

private theorem continuationLaws (R : Type v) :
    letI := continuationMonad.{u,v} R
    LawfulMonad (fun A : Type u => (A → R) → R) := by
  letI := continuationMonad.{u,v} R
  exact {
    map_const := rfl, id_map := fun _ => rfl, comp_map := fun _ _ _ => rfl
    seqLeft_eq := fun _ _ => rfl, seqRight_eq := fun _ _ => rfl, pure_seq := fun _ _ => rfl
    map_pure := fun _ _ => rfl, seq_pure := fun _ _ => rfl, seq_assoc := fun _ _ _ => rfl
    bind_pure_comp := fun _ _ => rfl, bind_map := fun _ _ => rfl, pure_bind := fun _ _ => rfl
    bind_assoc := fun _ _ _ => rfl }

/-- Equality of the two functions restricted to array callbacks reflects equality of the observers. -/
def ArrayTests : Prop := ∀ {α : Type u} {R : Type v} {n : Nat}
    {x y : (Vector α n → R) → R},
    (fun k : Array α → R => x (fun v => k v.toArray)) =
    (fun k : Array α → R => y (fun v => k v.toArray)) → x = y

theorem arrayTestsOfOriginal (original : type_of% @Vector.map_toArray_inj.{u,max u v}) :
    ArrayTests.{u,v} := by
  intro α R n x y h
  letI := continuationMonad.{u,v} R
  letI := continuationLaws.{u,v} R
  exact (original (m := fun A : Type u => (A → R) → R) (xs := x) (ys := y)).mp h

open Lean in
run_cmd
  for name in [``pureMapInjective, ``readerMapInjective, ``ofCallbackCongruence,
      ``ofFunctionExtensionality, ``arrayTestsOfOriginal] do
    unless (← collectAxioms name).isEmpty do throwError "vector projection witness {name} uses axioms"

end OmegaChecks.InitBoundaries.VectorProjection

namespace OmegaChecks.InitBoundaries.VectorCount
universe u

/-- The pinned `Vector.countP` unfolds to the underlying array count. This indexed fold
runs the same right-to-left traversal using the length in the vector type. -/
@[expose] def count (p : α → Bool) (xs : Vector α n) : Nat :=
  Fin.foldr n (fun i acc => bif p (xs.get i) then acc + 1 else acc) 0

theorem count_true {α : Type u} {n : Nat} :
    count (fun (_ : α) => true) = (fun (_ : Vector α n) => n) := by
  have number : Fin.foldr n (fun _ (acc : Nat) => acc + 1) 0 = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact (Fin.foldr_succ _ _).trans (congrArg Nat.succ ih)
  exact congrArg (fun k => fun _ : Vector α n => k) number

theorem count_false {α : Type u} {n : Nat} :
    count (fun (_ : α) => false) = (fun (_ : Vector α n) => 0) := by
  have number : Fin.foldr n (fun _ (acc : Nat) => acc) 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => exact (Fin.foldr_succ _ _).trans ih
  exact congrArg (fun k => fun _ : Vector α n => k) number
/-- The indexed fold returns the result of the pinned array fold on every vector. -/
theorem agreement (xs : Vector α n) (p : α → Bool) : count p xs = xs.countP p := by
  rcases xs with ⟨⟨l⟩, rfl⟩
  let step (x : α) (a : Nat) := bif p x then a + 1 else a
  change Fin.foldr l.length (fun i acc => step l[i.val] acc) 0 = (Array.mk l).foldr step 0
  rw [← Array.foldr_toList]
  induction l with
  | nil => rfl
  | cons x l ih => exact (Fin.foldr_succ _ _).trans (congrArg (step x) ih)

/-- Composing the pinned array zero count with the vector projection gives the entire vector zero count. -/
theorem ofArrayFalse (law : type_of% @Array.countP_false.{u}) : type_of% @Vector.countP_false.{u} := by
  intro α n
  exact congrArg (fun k => fun xs : Vector α n => k xs.toArray) (@law α)

/-- Agreement of the two counting functions for an entire length-indexed vector domain. -/
@[expose] def IndexedAgreement (b : Bool) : Prop :=
  ∀ {α : Type u} {n : Nat}, (Vector.countP fun (_ : α) => b) = @count α n (fun _ => b)

abbrev TrueAgreement := IndexedAgreement.{u} true
abbrev FalseAgreement := IndexedAgreement.{u} false

theorem trueIffIndexed : (type_of% @Vector.countP_true.{u}) ↔ TrueAgreement.{u} := by
  constructor
  · intro law α n
    exact (@law α n).trans count_true.symm
  · intro eq α n
    exact (@eq α n).trans count_true

theorem falseIffIndexed : (type_of% @Vector.countP_false.{u}) ↔ FalseAgreement.{u} := by
  constructor
  · intro law α n
    exact (@law α n).trans count_false.symm
  · intro eq α n
    exact (@eq α n).trans count_false

def equivalences := [(``Vector.countP_true, ``TrueAgreement, ``trueIffIndexed),
  (``Vector.countP_false, ``FalseAgreement, ``falseIffIndexed)]

end OmegaChecks.InitBoundaries.VectorCount
