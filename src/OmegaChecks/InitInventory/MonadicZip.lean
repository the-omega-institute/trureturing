module
import all Init.Data.List.Monadic
import all Init.Data.List.Control
import all Init.Data.List.ToArray
public import OmegaChecks.InitInventory.Traversal
import all OmegaChecks.InitInventory.Traversal

/-!
The two list implementations recurse with different accumulators. Their agreement is
equivalent to the optimized implementation's cons equation. The unary traversal
comparison and the two array conversions below also take the indicated official
law as a hypothesis. The five original zip theorems remain open.
-/

public section

namespace OmegaChecks.InitBoundaries.MonadicZip
universe u v w x

/-- The recursive version has the cons equation by reduction. -/
theorem consOfConversion (same : type_of% @List.zipWithM'_eq_zipWithM.{u,v,w,x}) :
    type_of% @List.zipWithM_cons_cons.{u,v,w,x} := by
  intro m α β γ a as b bs mon law f
  exact (same (f := f)).symm.trans (congrArg
    (fun tail => f a b >>= fun z => tail >>= fun zs => pure (z :: zs))
    (same (f := f) (l := as) (l' := bs)))

theorem conversionOfCons (consLaw : type_of% @List.zipWithM_cons_cons.{u,v,w,x}) :
    type_of% @List.zipWithM'_eq_zipWithM.{u,v,w,x} := by
  intro m α β γ mon law f xs ys
  induction xs generalizing ys with
  | nil => rfl
  | cons a xs ih =>
    cases ys with
    | nil => rfl
    | cons b ys =>
      exact (congrArg (fun tail => f a b >>= fun z => tail >>= fun zs => pure (z :: zs))
        (ih (ys := ys))).trans (consLaw (f := f)).symm

/-- Ordinary unary traversal of a zipped list, before its accumulator transformation. -/
private theorem zipPrimeMapPrime [Monad m] (f : α → β → m γ) (xs : List α) (ys : List β) :
    List.zipWithM' f xs ys = List.mapM' id (List.zipWith f xs ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons a xs ih =>
    cases ys with
    | nil => rfl
    | cons b ys =>
      exact congrArg (fun tail => f a b >>= fun z => tail >>= fun zs => pure (z :: zs)) (ih ys)

theorem ofUnaryTraversal (same : type_of% @List.mapM'_eq_mapM.{u,v,v}) :
    type_of% @List.zipWithM'_eq_mapM_id_zipWith.{u,v,w,x} := by
  intro α β γ m mon law f xs ys
  exact (zipPrimeMapPrime f xs ys).trans (same (f := id))

private theorem zipDiagonal [Monad m] (f : α → m γ) (xs : List α) :
    List.zipWithM' (fun a (_ : α) => f a) xs xs = List.mapM' f xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    exact congrArg (fun tail => f a >>= fun z => tail >>= fun zs => pure (z :: zs)) ih

private theorem pureDiagonal (f : α → γ) (xs : List α) :
    List.zipWith (fun a (_ : α) => f a) xs xs = xs.map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact congrArg (f a :: ·) ih

private theorem mappedActions [Monad m] (f : α → m γ) (xs : List α) :
    List.mapM id (xs.map f) = xs.mapM f := by
  have equation (ys : List α) : List.mapM.loop id (ys.map f) = List.mapM.loop f ys := by
    induction ys with
    | nil => rfl
    | cons a ys ih => exact congrArg (fun tail acc => f a >>= fun v => tail (v :: acc)) ih
  exact congrFun (equation xs) []

theorem unaryTraversalOfZip (same : type_of% @List.zipWithM'_eq_mapM_id_zipWith.{u,v,w,w}) :
    type_of% @List.mapM'_eq_mapM.{u,v,w} := by
  intro m α γ mon law f xs
  have diag := same (f := fun a (_ : α) => f a) (as := xs) (bs := xs)
  rw [pureDiagonal, mappedActions] at diag
  exact (zipDiagonal f xs).symm.trans diag

private def choose {δ : Type u} (x y : δ) : Bool → Unit → δ
  | false, _ => x
  | true, _ => y

theorem pairOfArrayConversion (rule : type_of% @List.zipWithM_toArray.{u,v,0,0}) :
    OmegaChecks.InitBoundaries.MonadicTraversal.IndexedMap.PairConversion.{u,v} := by
  intro m mon law γ x y
  with_unfolding_all exact (rule (choose x y) [false,true] [(),()]).trans (bind_pure_comp ..)

/-- The two-effect conversion with an arbitrary initial accumulator. -/
def PairWithPrefix := ∀ {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {γ : Type u} (x y : m γ) (acc : Array γ),
    (x >>= fun a => y >>= fun b => pure ((acc.push a).push b)) =
      ((x >>= fun a => y >>= fun b => pure [a,b]) >>= fun zs => pure (acc ++ zs.toArray))

theorem pairOfAccumulatorConversion (rule : type_of% @List.zipWithMAux_toArray_zero.{u,v,0,0}) :
    PairWithPrefix.{u,v} := by
  intro m mon law γ x y acc
  with_unfolding_all exact rule (choose x y) [false,true] [(),()] acc

end OmegaChecks.InitBoundaries.MonadicZip
