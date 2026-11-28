module
public import Lean
public import Init.Control.Lawful.MonadLift.Instances

public section

open Lean
namespace OmegaChecks.InitBoundaries.TransformerLaws
universe u v w

namespace ReturnImage

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
         {n : Type u → Type w} [Monad n] [LawfulMonad n] [MonadAttach n] [LawfulMonadAttach n]
         [MonadLiftT m n] [LawfulMonadLiftT m n]

/-- A computation factors through the subtype of results satisfying P. -/
def IsImage {α : Type u} (P : α → Prop) (x : m α) : Prop :=
  ∃ y : m (Subtype P), Subtype.val <$> y = x

/-- Lawful attachment constructs a witness for every postcondition on the possible results. -/
theorem imageIff {α : Type u} {P : α → Prop} {x : m α} :
    IsImage P x ↔ (∀ a, MonadAttach.CanReturn x a → P a) := by
  constructor
  · rintro ⟨y, rfl⟩ a h
    exact LawfulMonadAttach.canReturn_map_imp h
  · intro ensures
    let pack (a : Subtype (MonadAttach.CanReturn x)) : Subtype P := ⟨a.val, ensures a.val a.property⟩
    refine ⟨pack <$> MonadAttach.attach x, ?_⟩
    exact (comp_map pack Subtype.val _).symm.trans WeaklyLawfulMonadAttach.map_attach

/-- Lifting an action projected from the subtype of P still factors through that subtype. -/
def LiftImages (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n] [MonadLiftT m n] : Prop :=
  ∀ {α : Type u} (P : α → Prop) (x : m (Subtype P)), IsImage P (liftM (n := n) (Subtype.val <$> x))

omit [LawfulMonad m] [LawfulMonadLiftT m n] in
theorem liftIff :
    (∀ {α : Type u} (x : m α) (a : α), MonadAttach.CanReturn (liftM (n := n) x) a → MonadAttach.CanReturn x a) ↔
      LiftImages m n := by
  constructor
  · intro lift α P x
    exact imageIff.mpr fun a h => LawfulMonadAttach.canReturn_map_imp (lift _ a h)
  · intro images α x a h
    have e := images (MonadAttach.CanReturn x) (MonadAttach.attach x)
    rw [WeaklyLawfulMonadAttach.map_attach] at e
    exact imageIff.mp e a h

/-- Given a certified input and a continuation whose reachable outputs factor through Q,
sequencing the input and continuation also factors through Q. -/
def BindImages (m : Type u → Type v) [Monad m] : Prop :=
  ∀ {α β : Type u} (P : α → Prop) (Q : β → Prop) (x : m (Subtype P)) (f : α → m β),
    (∀ a, P a → IsImage Q (f a)) → IsImage Q ((Subtype.val <$> x) >>= f)

theorem bindIff :
    (∀ {α β : Type u} (x : m α) (f : α → m β) (b : β), MonadAttach.CanReturn (x >>= f) b →
      ∃ a, MonadAttach.CanReturn x a ∧ MonadAttach.CanReturn (f a) b) ↔ BindImages m := by
  constructor
  · intro law α β P Q x f restrict
    apply imageIff.mpr
    intro b hb
    obtain ⟨a, ha, hfb⟩ := law _ f b hb
    exact imageIff.mp (restrict a (LawfulMonadAttach.canReturn_map_imp ha)) b hfb
  · intro images α β x f b hb
    let P (a : α) := MonadAttach.CanReturn x a
    let Q (b : β) := ∃ a, P a ∧ MonadAttach.CanReturn (f a) b
    have hx := images P Q (MonadAttach.attach x) f (fun a ha =>
      imageIff.mpr fun _ h => ⟨a, ha, h⟩)
    rw [WeaklyLawfulMonadAttach.map_attach] at hx
    exact imageIff.mp hx b hb

abbrev PreservesBindImages := ∀ (m : Type u → Type v) [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m],
  BindImages m

abbrev PreservesLiftImages := ∀ (m : Type u → Type v) (n : Type u → Type w)
  [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
  [Monad n] [MonadAttach n] [LawfulMonad n] [LawfulMonadAttach n]
  [MonadLiftT m n] [LawfulMonadLiftT m n], LiftImages m n

theorem bindRule : (type_of% @LawfulMonadAttach.canReturn_bind_imp'.{u,v}) ↔ PreservesBindImages.{u,v} := by
  constructor
  · intro rule m _ _ _ _
    exact bindIff.mp fun x f b h => rule (x := x) (f := f) (b := b) h
  · intro images m α β b _ _ _ _ x f h
    exact bindIff.mpr (images m) x f b h

theorem liftRule : (type_of% @LawfulMonadAttach.canReturn_liftM_imp'.{u,v,w}) ↔ PreservesLiftImages.{u,v,w} := by
  constructor
  · intro rule m n _ _ _ _ _ _ _ _ _ _
    exact liftIff.mp fun x a h => rule (m := m) (n := n) (x := x) (a := a) h
  · intro images m n α _ _ _ _ _ _ _ _ _ _ x a h
    exact liftIff.mpr (images m n) x a h

def equivalences : List (Name × Name × Name) := [
  (``LawfulMonadAttach.canReturn_bind_imp', ``PreservesBindImages, ``bindRule),
  (``LawfulMonadAttach.canReturn_liftM_imp', ``PreservesLiftImages, ``liftRule)]

end ReturnImage

end OmegaChecks.InitBoundaries.TransformerLaws
