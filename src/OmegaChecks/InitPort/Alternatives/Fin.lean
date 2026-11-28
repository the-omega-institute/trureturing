module

public import Init.Data.Fin.Lemmas
public import Init.Data.Fin.Fold
import all Init.Data.Fin.Fold
import all Init.Data.Fin.Lemmas

namespace OmegaChecks.InitPort.Alternatives

private def offsetVal (n i : Nat) : Nat :=
  match n with
  | 0 => i
  | k + 1 => (k + 1) + i

private theorem offsetVal_eq (n i : Nat) : offsetVal n i = n + i := by
  cases n with
  | zero => exact (Nat.zero_add i).symm
  | succ => rfl

public def Fin.natAdd {m : Nat} (n : Nat) (i : Fin m) : Fin (n + m) :=
  ⟨offsetVal n i.val, (offsetVal_eq n i.val).symm ▸ Nat.add_lt_add_left i.isLt n⟩

public theorem Fin.val_natAdd (n : Nat) {m : Nat} (i : Fin m) : (Fin.natAdd n i).val = n + i.val :=
  offsetVal_eq n i.val

public theorem Fin.coe_natAdd (n : Nat) {m : Nat} (i : Fin m) : (Fin.natAdd n i).val = n + i.val :=
  Fin.val_natAdd n i

public theorem Fin.le_coe_natAdd (m : Nat) (i : Fin n) : m ≤ (Fin.natAdd m i).val :=
  (Fin.val_natAdd m i).symm ▸ Nat.le_add_right m i.val

public theorem Fin.cast_natAdd_left {n m m' : Nat} (i : Fin n) (h : m' + n = m + n) :
    (Fin.natAdd m' i).cast h = Fin.natAdd m i := by
  cases Nat.add_right_cancel h
  rfl

public theorem Fin.natAdd_natAdd (m n : Nat) {p : Nat} (i : Fin p) :
    Fin.natAdd m (Fin.natAdd n i) = (Fin.natAdd (m + n) i).cast (Nat.add_assoc ..) :=
  _root_.Fin.ext ((Fin.val_natAdd m _).trans ((congrArg (m + ·) (Fin.val_natAdd n i)).trans
    ((Nat.add_assoc m n i.val).symm.trans (Fin.val_natAdd (m+n) i).symm)))

public theorem Fin.cast_natAdd (n : Nat) {m : Nat} (i : Fin m) :
    (Fin.natAdd n i).cast (Nat.add_comm ..) = i.addNat n :=
  _root_.Fin.ext ((Fin.val_natAdd n i).trans (Nat.add_comm ..))

public theorem Fin.cast_addNat {n : Nat} (m : Nat) (i : Fin n) :
    (i.addNat m).cast (Nat.add_comm ..) = Fin.natAdd m i :=
  _root_.Fin.ext ((Nat.add_comm i.val m).trans (Fin.val_natAdd m i).symm)

public theorem Fin.natAdd_last {m n : Nat} : Fin.natAdd n (_root_.Fin.last m) = _root_.Fin.last (n+m) :=
  _root_.Fin.ext (Fin.val_natAdd n (_root_.Fin.last m))

public theorem Fin.natAdd_eq_addNat (n : Nat) (i : Fin n) : Fin.natAdd n i = i.addNat n :=
  _root_.Fin.ext ((Fin.val_natAdd n i).trans (Nat.add_comm ..))

public theorem Fin.natAdd_subNat_cast {n m : Nat} {i : Fin (n+m)} (h : n ≤ i.val) :
    Fin.natAdd n (_root_.Fin.subNat n (i.cast (Nat.add_comm ..)) h) = i :=
  _root_.Fin.ext ((Fin.val_natAdd n _).trans (Nat.add_sub_of_le h))

public theorem Fin.natAdd_mk (n i : Nat) (h : i < m) :
    Fin.natAdd n ⟨i, h⟩ = ⟨n+i, Nat.add_lt_add_left h n⟩ :=
  _root_.Fin.ext (offsetVal_eq n i)

public theorem Fin.natAdd_zero {n : Nat} : Fin.natAdd 0 = _root_.Fin.cast (Nat.zero_add n).symm := by rfl

public theorem Fin.eq_or_lt_of_le : type_of% @_root_.Fin.eq_or_lt_of_le := by
  intro n a b h
  exact (Nat.eq_or_lt_of_le h).imp _root_.Fin.eq_of_val_eq id

public theorem Fin.lt_or_eq_of_le : type_of% @_root_.Fin.lt_or_eq_of_le := by
  intro n a b h
  exact (Fin.eq_or_lt_of_le h).symm

public theorem Fin.rev_le_rev : type_of% @_root_.Fin.rev_le_rev := by
  intro n i j
  exact (Nat.sub_le_sub_iff_left (Nat.succ_le_iff.mpr j.isLt)).trans Nat.succ_le_succ_iff

public theorem Fin.rev_lt_rev : type_of% @_root_.Fin.rev_lt_rev := by
  intro n i j
  exact _root_.Fin.not_le.symm.trans ((not_congr Fin.rev_le_rev).trans _root_.Fin.not_le)

public theorem Fin.last_eq_zero_iff : type_of% @_root_.Fin.last_eq_zero_iff := by
  intro n
  exact eq_comm.trans _root_.Fin.zero_eq_last_iff

public theorem Fin.one_lt_succ_succ : type_of% @_root_.Fin.one_lt_succ_succ := by
  intro n a
  exact Nat.succ_lt_succ (Nat.zero_lt_succ a.val)

public theorem Fin.add_one_pos : type_of% @_root_.Fin.add_one_pos := by
  intro n i h
  change 0 < (i + 1).val
  rw [_root_.Fin.val_add_one_of_lt h]
  exact Nat.zero_lt_succ _

public theorem Fin.add_one_le_iff : type_of% @_root_.Fin.add_one_le_iff := by
  intro n k
  constructor
  · intro h
    apply _root_.Fin.eq_last_of_not_lt
    intro lt
    have le : (k+1).val ≤ k.val := h
    rw [_root_.Fin.val_add_one_of_lt lt] at le
    exact Nat.not_succ_le_self _ le
  · intro eq
    rw [eq, _root_.Fin.last_add_one]
    exact Nat.zero_le _

public theorem Fin.lt_add_one_iff : type_of% @_root_.Fin.lt_add_one_iff := by
  intro n k
  constructor
  · intro lt
    apply Nat.lt_of_le_of_ne (_root_.Fin.le_last k)
    exact fun eq => _root_.Fin.not_le.mpr lt (Fin.add_one_le_iff.mpr (_root_.Fin.eq_of_val_eq eq))
  · intro lt
    change k.val < (k + 1).val
    rw [_root_.Fin.val_add_one_of_lt lt]
    exact Nat.lt_succ_self _

public theorem Fin.succ_eq_last_succ : type_of% @_root_.Fin.succ_eq_last_succ := by
  intro n i
  rw [← _root_.Fin.succ_last]
  exact _root_.Fin.succ_inj

public theorem Fin.reverseInduction_castSucc_aux {n : Nat} {motive : Fin (n + 1) → Sort _} {step}
    (i : Fin n) (j : Nat) (hj) (lt : i.val < j) (x : motive ⟨j, hj⟩) :
    _root_.Fin.reverseInduction.go (motive := motive) step i.castSucc j hj (Nat.le_of_lt lt) x =
      step i (_root_.Fin.reverseInduction.go step i.succ j hj lt x) := by
  induction j generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero _ lt)
  | succ j ih =>
    rw [_root_.Fin.reverseInduction.go, dite_eq_right (show i.castSucc.val ≠ j + 1 from Nat.ne_of_lt lt)]
    if equal : i.val = j then
      subst j
      dsimp only
      rw [_root_.Fin.reverseInduction.go, dite_eq_left (show i.castSucc.val = i.val from rfl),
        _root_.Fin.reverseInduction.go, dite_eq_left (show i.succ.val = i.val + 1 from rfl)]
      rfl
    else
      have smaller := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ lt) equal
      dsimp only
      rw [ih _ _ smaller]
      conv => rhs; rw [_root_.Fin.reverseInduction.go, dite_eq_right (show i.succ.val ≠ j + 1 from Nat.succ_ne_succ_iff.mpr equal)]

open _root_.Fin

private theorem foldl_pointwise {α : Sort _} {n : Nat} {f g : α → Fin n → α}
    (steps : ∀ x i, f x i = g x i) (x : α) : foldl n f x = foldl n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [foldl_succ, foldl_succ, steps x 0]
    exact ih (fun x i => steps x i.succ) _

private theorem foldr_pointwise {α : Sort _} {n : Nat} {f g : Fin n → α → α}
    (steps : ∀ i x, f i x = g i x) (x : α) : foldr n f x = foldr n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [foldr_succ, foldr_succ, steps]
    exact congrArg (g 0) (ih (fun i x => steps i.succ x) _)

public theorem Fin.foldr_succ_last : type_of% @_root_.Fin.foldr_succ_last := by
  intro n α f x
  have loops (i : Nat) (h : i ≤ n) (x : α) :
      foldr.loop (n+1) f i (Nat.le_succ_of_le h) x =
        foldr.loop n (fun j => f j.castSucc) i h x := by
    induction i generalizing x with
    | zero => rfl
    | succ i ih => exact ih (Nat.le_of_lt h) (f ⟨i, Nat.le_succ_of_le h⟩ x)
  exact loops n (Nat.le_refl n) (f (last n) x)

public theorem Fin.foldl_add : type_of% @_root_.Fin.foldl_add := by
  intro α n m f x
  induction m with
  | zero => rfl
  | succ m ih =>
    apply (foldl_succ_last (n := n+m) f x).trans
    rw [ih, foldl_succ_last (n := m), _root_.Fin.natAdd_last]
    exact congrArg (fun z => f z (last (n+m))) (foldl_pointwise
      (fun a i => congrArg (f a) (_root_.Fin.castSucc_natAdd n i)) _)

public theorem Fin.foldr_add : type_of% @_root_.Fin.foldr_add := by
  intro n m α f x
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    apply (Fin.foldr_succ_last (n := n+m) f x).trans
    rw [ih, Fin.foldr_succ_last (f := fun i => f (i.natAdd n)), _root_.Fin.natAdd_last]
    exact congrArg (foldr n (fun i => f (i.castLE (Nat.le_add_right n (m+1))))) (foldr_pointwise
      (fun i a => congrArg (fun j => f j a) (_root_.Fin.castSucc_natAdd n i)) _)

public theorem Fin.foldl_rev : type_of% @_root_.Fin.foldl_rev := by
  intro n α f x
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [foldl_succ, Fin.foldr_succ_last, ← ih, rev_zero]
    exact foldl_pointwise (fun a i => congrArg (fun j => f j a) (rev_succ i)) _

public theorem Fin.foldr_rev : type_of% @_root_.Fin.foldr_rev := by
  intro α n f x
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [foldr_succ, foldl_succ_last, ← ih, rev_zero]
    exact congrArg (fun a => f a (last n))
      (foldr_pointwise (fun i a => congrArg (f a) (rev_succ i)) _)

private def foldlFuel [Monad m] (n : Nat) (f : α → Fin n → m α)
    (i : Nat) (fuel : {k // n-i < k}) (x : α) : m α :=
  let measure : ((_ : α) ×' Nat) → Nat := fun p => p.casesOn fun _ j => n-j
  WellFounded.Nat.fix.go (motive := fun _ => m α) measure
    (fun p => p.casesOn (motive := fun p =>
      ((q : (_ : α) ×' Nat) →
        InvImage (· < ·) measure q p → m α) → m α)
      fun a j recurse => if h : j < n then
          f a ⟨j,h⟩ >>= fun b => recurse ⟨b,j+1⟩ (by
            change n-(j+1) < n-j
            omega)
        else pure a)
    fuel.val ⟨x,i⟩ fuel.property

private theorem unfoldFoldl [Monad m] (n : Nat) (f : α → Fin n → m α) (i : Nat)
    (k : Nat) (hk : n-i+1 = k) :
    (fun a => foldlM.loop n f a i) = foldlFuel n f i ⟨k, by omega⟩ := by
  let eager := WellFounded.Nat.eager (n-i+1)
  have value : eager = k := (WellFounded.Nat.eager_eq _).trans hk
  have enough : n-i < eager := by omega
  delta foldlM.loop foldlM.loop._unary WellFounded.Nat.fix
  exact congrArg (fun fuel => foldlFuel n f i fuel)
    (Subtype.ext (a1 := ⟨eager,enough⟩) (a2 := ⟨k,by omega⟩) value)

private theorem positiveBranch {p : Prop} [d : Decidable p] (hp : p) {α β : Sort _}
    (yes : α → p → β) (no : α → ¬p → β) :
    (fun a => if h : p then yes a h else no a h) = (fun a => yes a hp) := by
  cases d with
  | isTrue => rfl
  | isFalse h => exact (h hp).elim

private theorem foldlMLt [Monad m] {n i : Nat} (f : α → Fin n → m α) (h : i < n) :
    (fun a => foldlM.loop n f a i) =
      fun a => f a ⟨i,h⟩ >>= fun b => foldlM.loop n f b (i+1) := by
  rw [unfoldFoldl n f i _ rfl, unfoldFoldl n f (i+1) (n-i) (by omega)]
  delta foldlFuel WellFounded.Nat.fix.go
  exact positiveBranch h _ _

private theorem negativeBranch {p : Prop} [d : Decidable p] (hp : ¬p) {α β : Sort _}
    (yes : α → p → β) (no : α → ¬p → β) :
    (fun a => if h : p then yes a h else no a h) = (fun a => no a hp) := by
  cases d with
  | isTrue h => exact (hp h).elim
  | isFalse => rfl

public theorem Fin.foldlM.loop._unary.eq_def :
    type_of% (private_decl% @_root_.Fin.foldlM.loop._unary.eq_def) := by
  intro m α inst n f p
  obtain ⟨a, i⟩ := p
  dsimp only
  by_cases h : i < n
  · rw [dite_eq_left h]
    with_unfolding_all exact congrFun (foldlMLt f h) a
  · rw [dite_eq_right h]
    have e := congrFun (unfoldFoldl n f i (Nat.succ 0) (by change n - i + 1 = 1; omega)) a
    with_unfolding_all change foldlM.loop n f a i = pure a
    exact e.trans (by
      delta foldlFuel WellFounded.Nat.fix.go
      dsimp only
      rw [dite_eq_right h])

private theorem foldlMEnd [Monad m] {n : Nat} (f : α → Fin n → m α) :
    (fun a => foldlM.loop n f a n) = pure := by
  rw [unfoldFoldl n f n 1 (by omega)]
  delta foldlFuel WellFounded.Nat.fix.go
  exact negativeBranch (Nat.lt_irrefl n) _ (fun a _ => pure a)

private theorem foldlMShift [Monad m] {n : Nat} (f : α → Fin (n+1) → m α)
    (k i : Nat) (sum : i+k=n) :
    (fun x => foldlM.loop (n+1) f x (i+1)) =
      fun x => foldlM.loop n (fun a j => f a j.succ) x i := by
  induction k generalizing i with
  | zero =>
    rw [Nat.add_zero] at sum
    subst i
    exact (foldlMEnd f).trans (foldlMEnd _).symm
  | succ k ih =>
    have hi : i < n := by omega
    rw [foldlMLt f (Nat.succ_lt_succ hi), foldlMLt _ hi]
    exact congrArg (fun cont => fun a => f a ⟨i+1, Nat.succ_lt_succ hi⟩ >>= cont)
      (ih (i+1) (by omega))

public theorem Fin.foldlM_loop._unary :
    type_of% (private_decl% @_root_.Fin.foldlM_loop._unary) := by
  intro m α n inst f p
  obtain ⟨i, x, h⟩ := p
  exact (congrFun (foldlMLt f h) x).trans (congrArg
    (fun cont => f x ⟨i, h⟩ >>= cont) (foldlMShift f (n - i) i (by omega)))

public theorem Fin.foldlM_succ : type_of% @_root_.Fin.foldlM_succ := by
  intro m α n inst f
  exact (foldlMLt f (Nat.zero_lt_succ n)).trans (congrArg
    (fun cont => fun x => f x 0 >>= cont) (foldlMShift f n 0 (Nat.zero_add n)))

private theorem unfoldFix {α : Sort _} {C : α → Sort _} {r : α → α → Prop}
    (w : WellFounded r) (F : ∀ a, (∀ b, r b a → C b) → C a) :
    w.fix F = fun a => F a (fun b _ => w.fix F b) := by
  calc w.fix F = (fun a => WellFounded.fixF F a (.intro a (fun b _ => w.apply b))) := rfl
       _ = _ := rfl

public theorem Fin.foldrM_zero : type_of% @_root_.Fin.foldrM_zero := by
  intro m α inst f
  delta foldrM foldrM.loop foldrM.loop._unary
  rw [unfoldFix]

private theorem unfoldFoldrM [Monad m] {n i : Nat} (f : Fin n → α → m α) (h : i < n) :
    foldrM.loop n f ⟨i+1,h⟩ =
      fun x => f ⟨i,h⟩ x >>= foldrM.loop n f ⟨i, Nat.le_of_lt h⟩ := by
  delta foldrM.loop foldrM.loop._unary
  conv => lhs; rw [unfoldFix]

private theorem emptyFoldrM [Monad m] {n : Nat} (f : Fin n → α → m α) :
    foldrM.loop n f ⟨0,Nat.zero_le _⟩ = pure := by
  delta foldrM.loop foldrM.loop._unary
  rw [unfoldFix]

public theorem Fin.foldrM_succ_last : type_of% @_root_.Fin.foldrM_succ_last := by
  intro m n α inst laws f
  have loops (i : Nat) (h : i ≤ n) :
      foldrM.loop (n+1) f ⟨i,Nat.le_succ_of_le h⟩ =
        foldrM.loop n (fun j => f j.castSucc) ⟨i,h⟩ := by
    induction i with
    | zero => exact (emptyFoldrM f).trans (emptyFoldrM _).symm
    | succ i ih =>
      rw [unfoldFoldrM, unfoldFoldrM (fun j => f j.castSucc)]
      exact congrArg (fun cont => fun x => f ⟨i,Nat.le_succ_of_le h⟩ x >>= cont) (ih (Nat.le_of_lt h))
  exact (unfoldFoldrM f (Nat.lt_succ_self n)).trans
    (congrArg (fun cont => fun x => f (last n) x >>= cont) (loops n (Nat.le_refl n)))

public theorem Fin.foldrM_pure : type_of% @_root_.Fin.foldrM_pure := by
  intro m α x inst laws n f
  have loops (i : Nat) (h : i ≤ n) (x : α) :
      foldrM.loop n (fun j a => pure (f j a)) ⟨i,h⟩ x =
        (pure (foldr.loop n f i h x) : m α) := by
    induction i generalizing x with
    | zero => rw [foldrM_loop_zero]; rfl
    | succ i ih =>
      rw [foldrM_loop_succ, pure_bind]
      exact ih (Nat.le_of_lt h) _
  exact loops n (Nat.le_refl n) x

public theorem Fin.foldr_eq_foldrM : type_of% @_root_.Fin.foldr_eq_foldrM := by
  intro n α f x
  exact (Fin.foldrM_pure (m := Id) (x := x) (f := f)).symm

public theorem Fin.foldlM_pure : type_of% @_root_.Fin.foldlM_pure := by
  intro m α x inst laws n f
  have loops (k i : Nat) (sum : i+k=n) (x : α) :
      foldlM.loop n (fun a j => pure (f a j)) x i =
        (pure (foldl.loop n f x i) : m α) := by
    induction k generalizing i x with
    | zero =>
      rw [Nat.add_zero] at sum
      subst i
      rw [congrFun (foldlMEnd _) _, foldl_loop_eq]
    | succ k ih =>
      have lt : i < n := by omega
      rw [congrFun (foldlMLt _ lt) _, pure_bind, foldl_loop_lt _ _ lt]
      exact ih (i+1) (by omega) _
  have direct {k : Nat} (g : α → Fin k → α) (a : α) : foldl.loop k g a 0 = foldl k g a := by
    induction k generalizing a with
    | zero => exact (foldl_loop_eq g a).trans (foldl_zero g a).symm
    | succ k ih =>
      rw [foldl_loop g a (Nat.zero_lt_succ k), foldl_succ, ih]
      rfl
  exact (loops n 0 (Nat.zero_add _) x).trans (congrArg (pure (f := m)) (direct f x))

public theorem Fin.foldl_eq_foldlM : type_of% @_root_.Fin.foldl_eq_foldlM := by
  intro α n f x
  exact (Fin.foldlM_pure (m := Id) (x := x) (f := f)).symm

public def Fin.foldlTR : type_of% @_root_.Fin.foldlTR := @_root_.Fin.foldl

end OmegaChecks.InitPort.Alternatives
