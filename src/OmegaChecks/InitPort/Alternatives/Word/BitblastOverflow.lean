module

public import OmegaChecks.InitPort.Alternatives.Word.Bitblast

namespace OmegaChecks.InitPort.Alternatives

public theorem BitVec.uppcRec_true_iff : type_of% @_root_.BitVec.uppcRec_true_iff := by
  intro w x s hs
  induction s with
  | zero =>
    change x.msb = true ↔ 2^(w-1) ≤ x.toNat
    rw [_root_.BitVec.msb_eq_toNat]
    exact decide_eq_true_iff
  | succ s ih =>
    let low := w-1-s
    let previous := w-1-(s-1)
    have compare : low ≤ previous := by dsimp [low, previous]; omega
    have adjacent : previous ≤ low+1 := by dsimp [low, previous]; omega
    change (x[low] || _root_.BitVec.uppcRec x s _) = true ↔ 2^low ≤ x.toNat
    apply Bool.or_eq_true_iff.trans
    constructor
    · rintro (bit | rest)
      · exact Nat.ge_two_pow_of_testBit bit
      · exact Nat.le_trans (Nat.pow_le_pow_right Nat.zero_lt_two compare) ((ih (by omega)).mp rest)
    · intro lower
      if high : 2^previous ≤ x.toNat then exact Or.inr ((ih (by omega)).mpr high)
      else
        exact Or.inl (Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt lower
          (Nat.lt_of_lt_of_le (Nat.lt_of_not_ge high) (Nat.pow_le_pow_right Nat.zero_lt_two adjacent)))

public theorem BitVec.resRec_true_iff : type_of% @_root_.BitVec.resRec_true_iff := by
  intro w x y s hs hp
  induction s with
  | zero => exact (Nat.not_lt_zero 0 hp).elim
  | succ k ih =>
    cases k with
    | zero =>
      constructor
      · intro bit
        exact ⟨1, Nat.le_refl _, Nat.zero_lt_succ _, bit⟩
      · rintro ⟨j, hj, positive, bit⟩
        have eq : j = 1 := by omega
        subst j
        exact bit
    | succ k =>
      change (_root_.BitVec.resRec x y (k+1) _ _ || _root_.BitVec.aandRec x y (k+2) _) = true ↔ _
      apply Bool.or_eq_true_iff.trans
      constructor
      · rintro (earlier | last)
        · obtain ⟨j, bound, positive, bit⟩ := (ih (by omega) (by omega)).mp earlier
          exact ⟨j, Nat.le_succ_of_le bound, positive, bit⟩
        · exact ⟨_, Nat.le_refl _, Nat.zero_lt_succ _, last⟩
      · rintro ⟨j, bound, positive, bit⟩
        rcases Nat.le_or_eq_of_le_succ bound with le | eq
        · exact Or.inl ((ih (by omega) (by omega)).mpr ⟨j, le, positive, bit⟩)
        · subst j
          exact Or.inr bit

public theorem BitVec.resRec_of_clz_le : type_of% @_root_.BitVec.resRec_of_clz_le := by
  intro w x y width hx hy total
  have pos : 0 < w := by omega
  apply (BitVec.resRec_true_iff ..).mpr
  refine ⟨w-1-y.clz.toNat, by omega, by omega, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · rw [← _root_.BitVec.getLsbD_eq_getElem (by omega)]
    exact _root_.BitVec.getLsbD_true_clz_of_ne_zero pos hy
  · apply (BitVec.uppcRec_true_iff ..).mpr
    refine Nat.le_trans (Nat.pow_le_pow_right Nat.zero_lt_two ?_) (_root_.BitVec.two_pow_sub_clz_le_toNat_of_ne_zero pos hx)
    omega

public theorem BitVec.saddOverflow_eq : type_of% @_root_.BitVec.saddOverflow_eq := by
  intro w x y
  cases w with
  | zero =>
    rw [_root_.BitVec.of_length_zero (x := x), _root_.BitVec.of_length_zero (x := y)]
    decide
  | succ w =>
    let half : Int := 2^w
    have xl : -half ≤ x.toInt := _root_.BitVec.le_toInt x
    have yl : -half ≤ y.toInt := _root_.BitVec.le_toInt y
    have xu : x.toInt < half := _root_.BitVec.toInt_lt
    have yu : y.toInt < half := _root_.BitVec.toInt_lt
    have wide : ((2^(w+1) : Nat) : Int) = half+half := by
      rw [Nat.pow_succ, Nat.mul_two, Int.natCast_add, Int.natCast_pow]
      rfl
    have sign : (x + y).msb = decide ((-half ≤ x.toInt+y.toInt ∧ x.toInt+y.toInt < 0) ∨ half ≤ x.toInt+y.toInt) := by
      rw [_root_.BitVec.msb_eq_toInt, _root_.BitVec.toInt_add]
      apply Bool.eq_iff_iff.mpr
      apply decide_eq_true_iff.trans
      apply Iff.trans (Int.bmod_neg_iff (by omega) (by omega))
      apply Iff.trans ?_ decide_eq_true_iff.symm
      rw [Nat.pow_succ, Nat.mul_two]
      have halfNat : ((2^w : Nat) : Int) = half := by rw [Int.natCast_pow]; rfl
      omega
    rw [sign, _root_.BitVec.msb_eq_toInt (x := x), _root_.BitVec.msb_eq_toInt (x := y)]
    change (decide (half ≤ x.toInt+y.toInt) || decide (x.toInt+y.toInt < -half)) = _
    cases dx : decide (x.toInt < 0) <;> cases dy : decide (y.toInt < 0) <;>
      cases high : decide (half ≤ x.toInt+y.toInt) <;> cases low : decide (x.toInt+y.toInt < -half) <;>
      cases wrapped : decide ((-half ≤ x.toInt+y.toInt ∧ x.toInt+y.toInt < 0) ∨ half ≤ x.toInt+y.toInt)
    all_goals first
      | rfl
      | exfalso
        first | have hx := of_decide_eq_true dx | have hx := of_decide_eq_false dx
        first | have hy := of_decide_eq_true dy | have hy := of_decide_eq_false dy
        first | have hhi := of_decide_eq_true high | have hhi := of_decide_eq_false high
        first | have hlo := of_decide_eq_true low | have hlo := of_decide_eq_false low
        first | have hsign := of_decide_eq_true wrapped | have hsign := of_decide_eq_false wrapped
        omega

public theorem BitVec.fastUmulOverflow : type_of% @_root_.BitVec.fastUmulOverflow := by
  intro w x y
  if small : w ≤ 1 then
    rw [dite_eq_left small]
    apply decide_eq_false
    cases w with
    | zero => have hx := x.isLt; have hy := y.isLt; change x.toNat < 1 at hx; change y.toNat < 1 at hy; simp only [show x.toNat = 0 by omega, Nat.zero_mul]; decide
    | succ w =>
      have eq : w = 0 := by omega
      subst w
      have hx := x.isLt
      have hy := y.isLt
      have bound := Nat.mul_le_mul (show x.toNat ≤ 1 by omega) (show y.toNat ≤ 1 by omega)
      omega
  else
    have hw : 1 < w := Nat.lt_of_not_ge small
    have hi := Nat.lt_succ_self w
    rw [dite_eq_right small, _root_.BitVec.getElem_eq_testBit_toNat _ _ _, _root_.BitVec.toNat_mul,
      _root_.BitVec.toNat_setWidth_of_le (Nat.le_succ w), _root_.BitVec.toNat_setWidth_of_le (Nat.le_succ w),
      Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    refine decide_eq_true_iff.trans ((Iff.intro ?_ ?_).trans Bool.or_eq_true_iff.symm)
    · intro enough
      if below : x.toNat*y.toNat < 2^(w+1) then
        exact Or.inl (Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt enough below)
      else
        have hx : x ≠ 0#w := by
          intro z
          rw [z, _root_.BitVec.toNat_zero, Nat.zero_mul] at enough
          exact Nat.not_le_of_gt (Nat.two_pow_pos _) enough
        have hy : y ≠ 0#w := by
          intro z
          rw [z, _root_.BitVec.toNat_zero, Nat.mul_zero] at enough
          exact Nat.not_le_of_gt (Nat.two_pow_pos _) enough
        have cx := _root_.BitVec.clz_lt_iff_ne_zero.mpr hx
        have cy := _root_.BitVec.clz_lt_iff_ne_zero.mpr hy
        apply Or.inr (BitVec.resRec_of_clz_le hw hx hy ?_)
        apply Decidable.byContradiction
        intro tooMany
        have strict := Nat.mul_lt_mul'' (_root_.BitVec.toNat_lt_two_pow_sub_clz (x := x))
          (_root_.BitVec.toNat_lt_two_pow_sub_clz (x := y))
        rw [← Nat.pow_add] at strict
        exact below (Nat.lt_of_lt_of_le strict (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    · rintro (bit | flag)
      · exact Nat.ge_two_pow_of_testBit bit
      · obtain ⟨k, hk, positive, both⟩ := (BitVec.resRec_true_iff ..).mp flag
        obtain ⟨bit, prefixBit⟩ := Bool.and_eq_true_iff.mp both
        have bound := Nat.mul_le_mul ((BitVec.uppcRec_true_iff ..).mp prefixBit)
          (_root_.BitVec.two_pow_le_toNat_of_getElem_eq_true _ bit)
        rw [← Nat.pow_add, show w-1-(k-1)+k = w by omega] at bound
        exact bound

public theorem BitVec.msb_sdiv_eq_decide : type_of% @_root_.BitVec.msb_sdiv_eq_decide := by
  intro w x y
  cases w with
  | zero =>
    rw [_root_.BitVec.of_length_zero (x := x), _root_.BitVec.of_length_zero (x := y)]
    decide
  | succ w =>
    have pos := Nat.zero_lt_succ w
    rw [_root_.BitVec.sdiv_eq, decide_eq_true pos, Bool.true_and]
    have signNeg (a : BitVec (w+1)) : a.msb = true →
        (-a).msb = decide (a = _root_.BitVec.intMin (w+1)) := by
      intro s
      if m : a = _root_.BitVec.intMin (w+1) then
        rw [decide_eq_true m, m, _root_.BitVec.neg_intMin, _root_.BitVec.msb_intMin, decide_eq_true pos]
      else
        rw [decide_eq_false m, BitVec.msb_neg_of_ne_intMin_of_ne_zero m (_root_.BitVec.ne_zero_of_msb_true s), s]
        rfl
    have negQuotient (a b : BitVec (w+1)) (sa : a.msb = false) :
        (-(a / b)).msb = (decide (b ≠ 0#(w+1)) && decide (b ≤ a)) := by
      have s := _root_.BitVec.msb_udiv_eq_false_of (y := b) sa
      if z : a / b = 0#(w+1) then
        rw [z, _root_.BitVec.neg_zero, _root_.BitVec.msb_zero]
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro impossible; cases impossible
        · intro bits
          obtain ⟨nonzero, le⟩ := Bool.and_eq_true_iff.mp bits
          exact False.elim ((_root_.BitVec.udiv_ne_zero_iff_ne_zero_and_le.mpr
            ⟨of_decide_eq_true nonzero, of_decide_eq_true le⟩) z)
      else
        obtain ⟨nonzero, le⟩ := _root_.BitVec.udiv_ne_zero_iff_ne_zero_and_le.mp z
        rw [BitVec.msb_neg_of_ne_intMin_of_ne_zero (_root_.BitVec.ne_intMin_of_msb_eq_false pos s) z,
          s, decide_eq_true nonzero, decide_eq_true le]
        rfl
    cases sx : x.msb <;> cases sy : y.msb
    all_goals simp only [_root_.BitVec.udiv_eq, Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true,
      Bool.false_or, Bool.or_false, Bool.and_false, Bool.and_true]
    · exact _root_.BitVec.msb_udiv_eq_false_of sx
    · rw [negQuotient _ _ sx, decide_eq_true (show -y ≠ 0#(w+1) from fun h =>
        _root_.BitVec.ne_zero_of_msb_true sy (_root_.BitVec.neg_eq_zero_iff.mp h)), Bool.true_and]
    · if m : x = _root_.BitVec.intMin (w+1) then
        rw [m, _root_.BitVec.neg_intMin]
        if z : y = 0#(w+1) then
          rw [z, _root_.BitVec.udiv_zero, _root_.BitVec.neg_zero, _root_.BitVec.msb_zero, decide_eq_true rfl, Bool.not_true, Bool.and_false]
        else
          if one : y = 1#(w+1) then
            rw [one, _root_.BitVec.udiv_one, _root_.BitVec.neg_intMin, _root_.BitVec.msb_intMin, decide_eq_true pos]
            have valid := (_root_.BitVec.udiv_ne_zero_iff_ne_zero_and_le (x := _root_.BitVec.intMin (w+1)) (y := y)).mp
            rw [one] at valid
            have ⟨nz, order⟩ := valid (by rw [_root_.BitVec.udiv_one]; exact _root_.BitVec.ne_zero_of_msb_true (by rw [_root_.BitVec.msb_intMin, decide_eq_true pos]))
            rw [decide_eq_true order, decide_eq_false nz]
            rfl
          else
            have sm : (_root_.BitVec.intMin (w+1) / y).msb = false := by
              rw [_root_.BitVec.msb_udiv, _root_.BitVec.msb_intMin, decide_eq_true pos, Bool.true_and]
              exact decide_eq_false one
            if order : y ≤ _root_.BitVec.intMin (w+1) then
              have nz := _root_.BitVec.udiv_ne_zero_iff_ne_zero_and_le.mpr ⟨z, order⟩
              rw [BitVec.msb_neg_of_ne_intMin_of_ne_zero (_root_.BitVec.ne_intMin_of_msb_eq_false pos sm) nz, sm,
                decide_eq_true order, decide_eq_false z]
              rfl
            else
              have q := _root_.BitVec.udiv_eq_zero_iff_eq_zero_or_lt.mpr (Or.inr (_root_.BitVec.not_le.mp order))
              rw [q, _root_.BitVec.neg_zero, _root_.BitVec.msb_zero, decide_eq_false order]
              rfl
      else
        have negSign := signNeg x sx
        rw [decide_eq_false m] at negSign
        rw [negQuotient _ _ negSign]
        if z : y = 0#(w+1) then rw [decide_eq_true z, decide_eq_false (fun h => h z), Bool.false_and, Bool.not_true, Bool.and_false]
        else rw [decide_eq_false z, decide_eq_true z, Bool.true_and, Bool.not_false, Bool.and_true]
    · rw [_root_.BitVec.msb_udiv, signNeg x sx]
      apply congrArg (fun b => decide (x = _root_.BitVec.intMin (w+1)) && b)
      apply Bool.eq_iff_iff.mpr
      change decide (-y = 1#(w+1)) = true ↔ decide (y = -1#(w+1)) = true
      exact decide_eq_true_iff.trans (_root_.BitVec.neg_eq_iff_eq_neg.trans decide_eq_true_iff.symm)

end OmegaChecks.InitPort.Alternatives
