module

public import Init.Data.Fin.Lemmas

namespace OmegaChecks.InitPort.Alternatives

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

end OmegaChecks.InitPort.Alternatives
