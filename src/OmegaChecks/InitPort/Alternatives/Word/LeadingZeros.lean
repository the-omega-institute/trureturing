module

public import OmegaChecks.InitPort.Alternatives.Word.Order

namespace OmegaChecks.InitPort.Alternatives

public theorem BitVec.le_toNat_iff_getLsbD_eq_true : type_of% @_root_.BitVec.le_toNat_iff_getLsbD_eq_true := by
  intro w i x _
  constructor
  · intro le
    obtain ⟨j, ge, bit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow le
    refine ⟨j-i, ?_⟩
    rw [Nat.add_sub_of_le ge]
    exact bit
  · rintro ⟨k, bit⟩
    exact Nat.le_trans (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_add_right i k))
      (Nat.ge_two_pow_of_testBit bit)

public theorem BitVec.toNat_lt_iff_getLsbD_eq_false : type_of% @_root_.BitVec.toNat_lt_iff_getLsbD_eq_false := by
  intro w x i _
  constructor
  · intro lt k
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le lt
      (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_add_right i k)))
  · intro clear
    apply Nat.lt_pow_two_of_testBit
    intro j ge
    have bit := clear (j-i)
    rw [Nat.add_sub_of_le ge] at bit
    exact bit

public theorem BitVec.clzAuxRec_eq_clzAuxRec_of_getLsbD_false :
    type_of% @_root_.BitVec.clzAuxRec_eq_clzAuxRec_of_getLsbD_false := by
  intro w n k x tail
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, _root_.BitVec.clzAuxRec_succ, ite_eq_right (show ¬ x.getLsbD (n+k+1) = true from
      fun h => Bool.noConfusion ((tail _ (by omega)).symm.trans h))]
    exact ih

private theorem clz_none {w : Nat} (x : BitVec w) (n : Nat) :
    x.clzAuxRec n = _root_.BitVec.ofNat w w ↔ ∀ j, j ≤ n → x.getLsbD j = false := by
  cases w with
  | zero => exact ⟨fun _ j _ => _root_.BitVec.getLsbD_of_ge _ _ (Nat.zero_le j),
      fun _ => (_root_.BitVec.eq_nil _).trans (_root_.BitVec.eq_nil _).symm⟩
  | succ w =>
    have fits := Nat.lt_pow_self (a := 2) (n := w+1) Nat.one_lt_two
    have different (j : Nat) : _root_.BitVec.ofNat (w+1) (w-j) ≠ _root_.BitVec.ofNat (w+1) (w+1) := by
      intro eq
      have bad := congrArg _root_.BitVec.toNat eq
      rw [_root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_trans (Nat.lt_succ_self _) fits)),
        Nat.mod_eq_of_lt fits] at bad
      omega
    induction n with
    | zero =>
      rw [_root_.BitVec.clzAuxRec_zero]
      cases bit : x.getLsbD 0 with
      | false => exact ⟨fun _ j lo => (Nat.eq_zero_of_le_zero lo) ▸ bit, fun _ => rfl⟩
      | true =>
        exact ⟨fun eq => False.elim (different 0 eq), fun h => False.elim (Bool.noConfusion (bit.symm.trans
          (h 0 (Nat.le_refl _))))⟩
    | succ n ih =>
      rw [_root_.BitVec.clzAuxRec_succ]
      cases bit : x.getLsbD (n+1) with
      | false =>
        constructor
        · intro eq j bound
          obtain eqj | earlier := Nat.eq_or_lt_of_le bound
          · exact eqj ▸ bit
          · exact ih.mp eq _ (Nat.le_of_lt_succ earlier)
        · intro clear
          exact ih.mpr (fun j bound => clear j (Nat.le_succ_of_le bound))
      | true =>
        exact ⟨fun eq => False.elim (different (n+1) eq), fun h => False.elim (Bool.noConfusion
          (bit.symm.trans (h (n+1) (Nat.le_refl _))))⟩

public theorem BitVec.clzAuxRec_eq_iff_of_getLsbD_false : type_of% @_root_.BitVec.clzAuxRec_eq_iff_of_getLsbD_false := by
  intro w n x _
  exact clz_none x n

public theorem BitVec.clz_eq_iff_eq_zero : type_of% @_root_.BitVec.clz_eq_iff_eq_zero := by
  intro w x
  apply (clz_none x (w-1)).trans
  apply Iff.trans ?_ _root_.BitVec.zero_iff_eq_false.symm
  exact ⟨fun clear i => if bound : i ≤ w-1 then clear i bound else
    _root_.BitVec.getLsbD_of_ge x i (by omega), fun clear j _ => clear j⟩

public theorem BitVec.clz_lt_iff_ne_zero : type_of% @_root_.BitVec.clz_lt_iff_ne_zero := by
  intro w x
  exact ⟨fun lt zero => _root_.BitVec.ne_of_lt lt (BitVec.clz_eq_iff_eq_zero.mpr zero),
    fun nz => Nat.lt_of_le_of_ne _root_.BitVec.clz_le
      (fun same => nz (BitVec.clz_eq_iff_eq_zero.mp (_root_.BitVec.eq_of_toNat_eq same)))⟩

public theorem BitVec.getLsbD_true_of_eq_clzAuxRec_of_ne_zero :
    type_of% @_root_.BitVec.getLsbD_true_of_eq_clzAuxRec_of_ne_zero := by
  intro w n x nonzero tail
  cases w with
  | zero => exact False.elim (nonzero ((_root_.BitVec.eq_nil x).trans (_root_.BitVec.eq_nil _).symm))
  | succ w =>
    have fits := Nat.lt_pow_self (a := 2) (n := w+1) Nat.one_lt_two
    have read (i : Nat) (bit : x.getLsbD i = true) :
        x.getLsbD (w - (_root_.BitVec.ofNat (w+1) (w-i)).toNat) = true := by
      rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le ..)
        (Nat.lt_trans (Nat.lt_succ_self _) fits)),
        Nat.sub_sub_self (Nat.le_of_lt_succ (_root_.BitVec.lt_of_getLsbD bit))]
      exact bit
    induction n with
    | zero =>
      rw [_root_.BitVec.clzAuxRec_zero]
      cases bit : x.getLsbD 0 with
      | true => exact read 0 bit
      | false =>
        apply False.elim (nonzero (_root_.BitVec.zero_iff_eq_false.mpr ?_))
        intro i
        cases i with
        | zero => exact bit
        | succ i => exact tail _ (Nat.zero_lt_succ i)
    | succ n ih =>
      rw [_root_.BitVec.clzAuxRec_succ]
      cases bit : x.getLsbD (n+1) with
      | true => exact read (n+1) bit
      | false =>
        apply ih
        intro i hi
        obtain eq | later := Nat.eq_or_lt_of_le hi
        · exact eq ▸ bit
        · exact tail _ later

public theorem BitVec.clzAuxRec_eq_zero_iff : type_of% @_root_.BitVec.clzAuxRec_eq_zero_iff := by
  intro w n x tail positive
  have fits := Nat.lt_pow_self (a := 2) (n := w) Nat.one_lt_two
  have top : w-1 < w := Nat.sub_lt positive Nat.zero_lt_one
  have decode (j : Nat) (bit : x.getLsbD j = true) (past : ∀ i, j < i → x.getLsbD i = false) :
      (_root_.BitVec.ofNat w (w-1-j)).toNat = 0 ↔ x[w-1] = true := by
    rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le ..)
      (Nat.lt_trans top fits))]
    constructor
    · intro eq
      have bound := _root_.BitVec.lt_of_getLsbD bit
      have atTop : j = w-1 := by omega
      exact atTop ▸ bit
    · intro head
      by_cases atTop : j = w-1
      · exact atTop ▸ Nat.sub_self _
      · have bound := _root_.BitVec.lt_of_getLsbD bit
        exact False.elim (Bool.noConfusion ((past (w-1) (by omega)).symm.trans head))
  induction n with
  | zero =>
    rw [_root_.BitVec.clzAuxRec_zero]
    cases bit : x.getLsbD 0 with
    | true => exact decode 0 bit tail
    | false =>
      change (_root_.BitVec.ofNat w w).toNat = 0 ↔ _
      rw [_root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
      constructor
      · intro zero; exact False.elim (Nat.ne_of_gt positive zero)
      · intro head
        change x.getLsbD (w-1) = true at head
        if eq : w-1 = 0 then
          rw [eq] at head
          exact False.elim (Bool.noConfusion (bit.symm.trans head))
        else exact False.elim (Bool.noConfusion ((tail (w-1) (Nat.pos_of_ne_zero eq)).symm.trans head))
  | succ n ih =>
    rw [_root_.BitVec.clzAuxRec_succ]
    cases bit : x.getLsbD (n+1) with
    | true => exact decode (n+1) bit tail
    | false =>
      apply ih
      intro i hi
      obtain eq | later := Nat.eq_or_lt_of_le hi
      · exact eq ▸ bit
      · exact tail _ later

public theorem BitVec.toNat_lt_two_pow_sub_clz : type_of% @_root_.BitVec.toNat_lt_two_pow_sub_clz := by
  intro w x
  apply Nat.lt_pow_two_of_testBit
  intro j ge
  have upper := _root_.BitVec.getLsbD_false_of_clzAuxRec (x := x) (n := w-1)
    (fun i hi => _root_.BitVec.getLsbD_of_ge x i (by omega)) (j-(w-x.clz.toNat))
  change x.getLsbD (w-x.clz.toNat+(j-(w-x.clz.toNat))) = false at upper
  rw [Nat.add_sub_of_le ge] at upper
  exact upper

end OmegaChecks.InitPort.Alternatives
