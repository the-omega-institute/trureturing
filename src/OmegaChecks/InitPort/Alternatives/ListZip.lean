module
import all Init.Data.List.Zip

/-! Zip lookups and symmetries by the constructors of the inputs. -/
namespace OmegaChecks.InitPort.Alternatives.List
open _root_.List

public theorem getElem?_zipWith' : type_of% @_root_.List.getElem?_zipWith' := by
  intro α β γ xs ys f i
  rw [getElem?_zipWith]
  cases xs[i]? <;> cases ys[i]? <;> rfl

public theorem getElem?_zipWith_eq_some : type_of% @_root_.List.getElem?_zipWith_eq_some := by
  intro α β γ f xs ys z i
  rw [getElem?_zipWith]
  cases xs[i]? with
  | none =>
    exact ⟨(fun h => nomatch h), fun ⟨_, _, hx, _, _⟩ => nomatch hx⟩
  | some x =>
    cases ys[i]? with
    | none => exact ⟨(fun h => nomatch h), fun ⟨_, _, _, hy, _⟩ => nomatch hy⟩
    | some y =>
      constructor
      · exact fun h => ⟨x, y, rfl, rfl, Option.some.inj h⟩
      · rintro ⟨_, _, hx, hy, eq⟩
        cases Option.some.inj hx
        cases Option.some.inj hy
        exact congrArg some eq

public theorem getElem?_zip_eq_some : type_of% @_root_.List.getElem?_zip_eq_some := by
  intro α β xs ys z i
  apply (_root_.List.getElem?_zipWith_eq_some (f := Prod.mk)).trans
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨hx, hy⟩
  · exact fun ⟨hx, hy⟩ => ⟨_, _, hx, hy, rfl⟩

public theorem head_zipWith._proof_1 : type_of% (private_decl% @_root_.List.head_zipWith._proof_1) := by
  rintro α β γ _ ys f h rfl
  exact h rfl

public theorem head_zipWith._proof_2 : type_of% (private_decl% @_root_.List.head_zipWith._proof_2) := by
  rintro α β γ xs _ f h rfl
  exact h zipWith_nil_right

public theorem head_zipWith : type_of% @_root_.List.head_zipWith := by
  intro α β γ xs ys f h
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons x xs =>
    cases ys with
    | nil => exact False.elim (h rfl)
    | cons y ys => rfl

public theorem map_prod_left_eq_zip : type_of% @_root_.List.map_prod_left_eq_zip := by
  intro α β xs f
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg ((x, f x) :: ·) ih

public theorem map_prod_right_eq_zip : type_of% @_root_.List.map_prod_right_eq_zip := by
  intro α β xs f
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg ((f x, x) :: ·) ih

public theorem zipWith_comm_of_comm : type_of% @_root_.List.zipWith_comm_of_comm := by
  intro α β f comm xs ys
  induction xs generalizing ys with
  | nil => exact zipWith_nil_right.symm
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      exact (congrArg (· :: zipWith f xs ys) (comm x y)).trans
        (congrArg (f y x :: ·) ih)

end OmegaChecks.InitPort.Alternatives.List
