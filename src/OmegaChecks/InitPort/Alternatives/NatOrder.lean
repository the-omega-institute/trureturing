module

public import Init.Data.Nat.Lemmas
public import Init.Data.Nat.Gcd
import all Init.Data.Nat.Lemmas

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.instLawfulBEq : type_of% @_root_.Nat.instLawfulBEq where
  eq_of_beq := _root_.Nat.eq_of_beq_eq_true
  rfl := _root_.Nat.beq_refl _

public theorem Nat.lt_sub_iff_add_lt' : type_of% @_root_.Nat.lt_sub_iff_add_lt' := by
  intro a b c
  rw [Nat.add_comm b a]
  exact ⟨Nat.add_lt_of_lt_sub, Nat.lt_sub_of_add_lt⟩

public theorem Nat.mod_two_eq_zero_or_one : type_of% @_root_.Nat.mod_two_eq_zero_or_one := by
  intro n
  have classify (r : Nat) (small : r < 2) : r = 0 ∨ r = 1 := by
    cases r with
    | zero => exact Or.inl rfl
    | succ r =>
      cases r with
      | zero => exact Or.inr rfl
      | succ r =>
        exact False.elim (Nat.not_lt_zero r (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ small)))
  exact classify (n % 2) (Nat.mod_lt n (Nat.zero_lt_succ 1))

public theorem Nat.exists_ne_zero : type_of% @_root_.Nat.exists_ne_zero := by
  intro P
  constructor
  · rintro ⟨n, nz, h⟩
    cases n with
    | zero => exact False.elim (nz rfl)
    | succ n => exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨n+1, Nat.succ_ne_zero _, h⟩

public theorem Nat.pred_eq_self_iff : type_of% @_root_.Nat.pred_eq_self_iff := by
  intro n
  cases n with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n => exact ⟨fun eq => False.elim (Nat.ne_of_lt (Nat.lt_succ_self _) eq),
      fun eq => False.elim (Nat.succ_ne_zero _ eq)⟩

public theorem Nat.div_lt_one_iff : type_of% @_root_.Nat.div_lt_one_iff := by
  intro b a hb
  apply (_root_.Nat.div_lt_iff_lt_mul hb).trans
  rw [Nat.one_mul]

public theorem Nat.div_eq_zero_iff : type_of% @_root_.Nat.div_eq_zero_iff := by
  intro a b
  constructor
  · intro eq
    if zero : b = 0 then exact Or.inl zero
    else
      apply Or.inr
      apply (Nat.div_lt_one_iff (Nat.pos_of_ne_zero zero)).mp
      rw [eq]
      exact Nat.zero_lt_one
  · rintro (rfl | lt)
    · exact Nat.div_zero _
    · exact Nat.div_eq_of_lt lt

public theorem Nat.div_ne_zero_iff : type_of% @_root_.Nat.div_ne_zero_iff := by
  intro a b
  exact ⟨fun nz => ⟨fun z => nz (Nat.div_eq_zero_iff.mpr (Or.inl z)),
    Nat.le_of_not_gt (fun lt => nz (Nat.div_eq_zero_iff.mpr (Or.inr lt)))⟩,
    fun ⟨nz,le⟩ zero => (Nat.div_eq_zero_iff.mp zero).elim nz (Nat.not_lt_of_ge le)⟩

public theorem Nat.div_pos_iff : type_of% @_root_.Nat.div_pos_iff := by
  intro a b
  exact Nat.pos_iff_ne_zero.trans (Nat.div_ne_zero_iff.trans (and_congr_left' Nat.pos_iff_ne_zero.symm))

public theorem Nat.le_iff_ne_zero_of_dvd : type_of% @_root_.Nat.le_iff_ne_zero_of_dvd := by
  intro a b ha dvd
  exact ⟨fun le => Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero ha) le),
    fun nz => Nat.le_of_dvd (Nat.pos_of_ne_zero nz) dvd⟩

public theorem Nat.div_ne_zero_iff_of_dvd : type_of% @_root_.Nat.div_ne_zero_iff_of_dvd := by
  intro b a dvd
  exact ⟨fun nz =>
    let ⟨bn,le⟩ := Nat.div_ne_zero_iff.mp nz
    ⟨(Nat.le_iff_ne_zero_of_dvd bn dvd).mp le, bn⟩,
    fun ⟨an,bn⟩ => Nat.div_ne_zero_iff.mpr ⟨bn,(Nat.le_iff_ne_zero_of_dvd bn dvd).mpr an⟩⟩

public theorem Nat.eq_zero_of_dvd_of_lt : type_of% @_root_.Nat.eq_zero_of_dvd_of_lt := by
  intro a b dvd lt
  exact Nat.eq_zero_of_dvd_of_div_eq_zero dvd (Nat.div_eq_of_lt lt)

public theorem Nat.lt_div_iff_mul_lt_of_dvd : type_of% @_root_.Nat.lt_div_iff_mul_lt_of_dvd := by
  intro c b a _ dvd
  apply (_root_.Nat.lt_div_iff_mul_lt' dvd a).trans
  rw [Nat.mul_comm]

public theorem Nat.mod_two_not_eq_one : type_of% @_root_.Nat.mod_two_not_eq_one := by
  intro n
  exact ⟨(_root_.Nat.mod_two_eq_zero_or_one n).resolve_right,
    fun zero one => Nat.noConfusion (zero.symm.trans one)⟩

public theorem Nat.mod_two_not_eq_zero : type_of% @_root_.Nat.mod_two_not_eq_zero := by
  intro n
  exact ⟨(_root_.Nat.mod_two_eq_zero_or_one n).resolve_left,
    fun one zero => Nat.noConfusion (zero.symm.trans one)⟩

public theorem Nat.pow_lt_pow_iff_left : type_of% @_root_.Nat.pow_lt_pow_iff_left := by
  intro a b n hn
  exact ⟨fun lt => Nat.lt_of_not_ge (fun rev => Nat.not_le_of_lt lt (Nat.pow_le_pow_left rev _)),
    fun lt => _root_.Nat.pow_lt_pow_left lt hn⟩

public theorem Nat.one_lt_pow_iff : type_of% @_root_.Nat.one_lt_pow_iff := by
  intro n hn a
  have h := Nat.pow_lt_pow_iff_left (a := 1) (b := a) hn
  rw [Nat.one_pow] at h
  exact h

public theorem Nat.pow_le_one_iff : type_of% @_root_.Nat.pow_le_one_iff := by
  intro n a hn
  exact Nat.not_lt.symm.trans ((not_congr (Nat.one_lt_pow_iff hn)).trans Nat.not_lt)

public theorem Nat.pow_right_inj : type_of% @_root_.Nat.pow_right_inj := by
  intro a m n base
  constructor
  · intro eq
    exact Nat.le_antisymm ((Nat.pow_le_pow_iff_right base).mp (Nat.le_of_eq eq))
      ((Nat.pow_le_pow_iff_right base).mp (Nat.le_of_eq eq.symm))
  · exact congrArg (a ^ ·)

public theorem Nat.pow_eq_self_iff : type_of% @_root_.Nat.pow_eq_self_iff := by
  intro a b base
  have h := Nat.pow_right_inj (m := b) (n := 1) base
  rw [Nat.pow_one] at h
  exact h

public theorem Nat.pow_eq_zero : type_of% @_root_.Nat.pow_eq_zero := by
  intro a n
  constructor
  · intro eq
    cases a with
    | succ a => exact False.elim (Nat.ne_of_gt (Nat.pow_pos (Nat.succ_pos _)) eq)
    | zero =>
      exact ⟨rfl, fun z => by cases z; exact Nat.noConfusion eq⟩
  · rintro ⟨rfl, nz⟩
    exact Nat.zero_pow (Nat.pos_of_ne_zero nz)

public theorem Nat.pow_pos_iff : type_of% @_root_.Nat.pow_pos_iff := by
  intro a n
  constructor
  · intro positive
    if nz : a = 0 then
      apply Or.inr
      cases n with
      | zero => rfl
      | succ n => exact False.elim (Nat.ne_of_gt positive (Nat.pow_eq_zero.mpr ⟨nz,Nat.succ_ne_zero _⟩))
    else exact Or.inl (Nat.pos_of_ne_zero nz)
  · rintro (positive | rfl)
    · exact Nat.pow_pos positive
    · exact Nat.zero_lt_one

public theorem Nat.mul_add_div : type_of% @_root_.Nat.mul_add_div := by
  intro m positive x y
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ positive, Nat.add_comm]

public theorem Nat.eq_of_dvd_of_lt_two_mul : type_of% @_root_.Nat.eq_of_dvd_of_lt_two_mul := by
  intro a b nz dvd small
  obtain ⟨k, rfl⟩ := dvd
  cases k with
  | zero => exact False.elim (nz (Nat.mul_zero _))
  | succ k =>
    cases k with
    | zero => exact Nat.mul_one _
    | succ k =>
      have le := Nat.mul_le_mul_left b (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))
      rw [Nat.mul_comm 2 b] at small
      exact False.elim (Nat.not_le_of_lt small le)

public theorem Nat.one_mod_eq_one : type_of% @_root_.Nat.one_mod_eq_one := by
  intro n
  constructor
  · intro eq one
    subst n
    exact Nat.noConfusion ((Nat.mod_one _).symm.trans eq)
  · intro ne
    cases n with
    | zero => exact Nat.mod_zero _
    | succ n =>
      cases n with
      | zero => exact False.elim (ne rfl)
      | succ n => exact _root_.Nat.one_mod n

public theorem Nat.div_mul_div_le : type_of% @_root_.Nat.div_mul_div_le := by
  intro a b c d
  if bz : b = 0 then
    rw [bz, Nat.div_zero, Nat.zero_mul, Nat.zero_mul, Nat.div_zero]
    exact Nat.le_refl _
  else if dz : d = 0 then
    rw [dz, Nat.div_zero, Nat.mul_zero, Nat.mul_zero, Nat.div_zero]
    exact Nat.le_refl _
  else
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.pos_of_ne_zero bz) (Nat.pos_of_ne_zero dz))).mpr
    rw [Nat.mul_mul_mul_comm]
    exact Nat.mul_le_mul (Nat.div_mul_le_self ..) (Nat.div_mul_le_self ..)

public theorem Nat.div_pow : type_of% @_root_.Nat.div_pow := by
  intro a b c dvd
  if z : a = 0 then
    subst a
    have eq := Nat.zero_dvd.mp dvd
    subst b
    cases c with
    | zero => rfl
    | succ c => rw [Nat.div_zero, Nat.zero_pow (Nat.succ_pos _), Nat.div_zero]
  else
    obtain ⟨k, rfl⟩ := dvd
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero z), Nat.mul_pow,
      Nat.mul_div_cancel_left _ (Nat.pow_pos (Nat.pos_of_ne_zero z))]

public theorem Nat.mul_sub_mod : type_of% @_root_.Nat.mul_sub_mod := by
  intro x n p h
  have pos : 0 < n := Nat.pos_of_mul_pos_right (Nat.lt_of_le_of_lt (Nat.zero_le x) h)
  have smaller : x / n < p := (Nat.div_lt_iff_lt_mul pos).mpr (Nat.mul_comm n p ▸ h)
  rw [Nat.mod_eq_sub_div_mul, Nat.mul_sub_div _ _ _ h, Nat.sub_sub, Nat.add_comm, ← Nat.sub_sub,
    Nat.mul_comm _ n, ← Nat.mul_sub_left_distrib, Nat.sub_sub_self (Nat.succ_le_iff.mpr smaller),
    Nat.mul_succ, Nat.add_comm]
  conv in (_ + 1) => rw [← Nat.mod_add_div x n, Nat.add_right_comm]
  exact Nat.add_sub_add_right _ _ _

public theorem Nat.allLTTR_loop_eq_true : type_of% (private_decl% @_root_.Nat.allLTTR_loop_eq_true) := by
  intro n f j
  induction j with
  | zero =>
    intro hj
    exact ⟨fun _ i lo hi => False.elim (Nat.not_le_of_lt hi lo), fun _ => rfl⟩
  | succ j ih =>
    intro hj
    apply Bool.and_eq_true_iff.trans
    apply (and_congr_right' (ih (Nat.le_of_succ_le hj))).trans
    constructor
    · rintro ⟨head,tail⟩ i lo hi
      obtain eq | lt := Nat.eq_or_lt_of_le lo
      · subst i; exact head
      · exact tail i (by omega) hi
    · intro all
      exact ⟨all _ (Nat.le_refl _) (by omega),
        fun i lo hi => all i (Nat.le_trans (Nat.sub_le_sub_left (Nat.le_succ j) _) lo) hi⟩

public theorem Nat.allLTTR_eq_true : type_of% @_root_.Nat.allLTTR_eq_true := by
  intro n f
  apply ((private_decl% _root_.Nat.allLTTR_loop_eq_true) n (Nat.le_refl n)).trans
  exact ⟨fun all i hi => all i (Nat.sub_self n ▸ Nat.zero_le i) hi, fun all i _ hi => all i hi⟩

public theorem Nat.anyLTTR_loop_eq_true : type_of% (private_decl% @_root_.Nat.anyLTTR_loop_eq_true) := by
  intro n f j
  induction j with
  | zero =>
    intro hj
    exact ⟨fun eq => Bool.noConfusion eq, fun ⟨_,hi,lo,_⟩ => False.elim (Nat.not_le_of_lt hi lo)⟩
  | succ j ih =>
    intro hj
    apply Bool.or_eq_true_iff.trans
    apply (or_congr Iff.rfl (ih (Nat.le_of_succ_le hj))).trans
    constructor
    · rintro (head | ⟨i,hi,lo,ok⟩)
      · exact ⟨_, by omega, Nat.le_refl _, head⟩
      · exact ⟨i,hi,Nat.le_trans (Nat.sub_le_sub_left (Nat.le_succ j) _) lo,ok⟩
    · rintro ⟨i,hi,lo,ok⟩
      obtain eq | lt := Nat.eq_or_lt_of_le lo
      · subst i; exact Or.inl ok
      · exact Or.inr ⟨i, hi, by omega, ok⟩

public theorem Nat.anyLTTR_eq_true : type_of% @_root_.Nat.anyLTTR_eq_true := by
  intro n f
  apply ((private_decl% _root_.Nat.anyLTTR_loop_eq_true) n (Nat.le_refl n)).trans
  exact ⟨fun ⟨i,hi,_,ok⟩ => ⟨i,hi,ok⟩, fun ⟨i,hi,ok⟩ => ⟨i,hi,Nat.sub_self n ▸ Nat.zero_le i,ok⟩⟩

public noncomputable def Nat.decidableBallLTTR : type_of% @_root_.Nat.decidableBallLTTR :=
  @_root_.Nat.decidableBallLT

@[instance_reducible] public noncomputable def Nat.decidableExistsLTTR : type_of% @_root_.Nat.decidableExistsLTTR :=
  @_root_.Nat.decidableExistsLT

public noncomputable def Nat.decidableExistsLT'TR : type_of% @_root_.Nat.decidableExistsLT'TR :=
  @_root_.Nat.decidableExistsLT'

public theorem Nat.succ_div_of_not_dvd : type_of% @_root_.Nat.succ_div_of_not_dvd :=
  fun h => Nat.succ_div_of_mod_ne_zero (fun eq => h (Nat.dvd_of_mod_eq_zero eq))

public theorem Nat.succ_div_of_dvd : type_of% @_root_.Nat.succ_div_of_dvd :=
  fun h => Nat.succ_div_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd h)

public theorem Nat.succ_div : type_of% @_root_.Nat.succ_div := by
  intro a b
  if divides : b ∣ a+1 then rw [ite_eq_left divides, Nat.succ_div_of_dvd divides]
  else rw [ite_eq_right divides, Nat.succ_div_of_not_dvd divides, Nat.add_zero]

public theorem Nat.mod_eq_mod_iff : type_of% @_root_.Nat.mod_eq_mod_iff := by
  intro x y z
  constructor
  · intro eq
    refine ⟨y/z, x/z, ?_⟩
    have xParts := Nat.mod_add_div' x z
    have yParts := Nat.mod_add_div' y z
    omega
  · rintro ⟨m, n, eq⟩
    have remainders := congrArg (fun a => a % z) eq
    simpa only [Nat.add_mul_mod_self_right] using remainders

public theorem Nat.pow_dvd_pow_iff : type_of% @_root_.Nat.pow_dvd_pow_iff := by
  intro a b n nonzero
  refine Nat.gcd_eq_left_iff_dvd.symm.trans ?_
  rw [Nat.pow_gcd_pow]
  exact (Nat.pow_left_inj nonzero).trans Nat.gcd_eq_left_iff_dvd

public theorem Nat.mul_min_mul_right : type_of% @_root_.Nat.mul_min_mul_right := by
  intro a b c
  rcases Nat.le_total a b with ab | ba
  · rw [Nat.min_eq_left ab, Nat.min_eq_left (Nat.mul_le_mul_right c ab)]
  · rw [Nat.min_eq_right ba, Nat.min_eq_right (Nat.mul_le_mul_right c ba)]

public theorem Nat.mul_max_mul_right : type_of% @_root_.Nat.mul_max_mul_right := by
  intro a b c
  rcases Nat.le_total a b with ab | ba
  · rw [Nat.max_eq_right ab, Nat.max_eq_right (Nat.mul_le_mul_right c ab)]
  · rw [Nat.max_eq_left ba, Nat.max_eq_left (Nat.mul_le_mul_right c ba)]

public theorem Nat.min_eq_zero_iff : type_of% @_root_.Nat.min_eq_zero_iff := by
  intro m n
  constructor
  · intro h
    cases Nat.le_total m n with
    | inl le => exact Or.inl ((Nat.min_eq_left le).symm.trans h)
    | inr le => exact Or.inr ((Nat.min_eq_right le).symm.trans h)
  · rintro (rfl | rfl)
    · exact Nat.zero_min _
    · exact Nat.min_zero _

end OmegaChecks.InitPort.Alternatives
