module

public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.Int.Gcd

namespace OmegaChecks.InitPort.Alternatives

public theorem Int.ediv_eq_neg_one_of_neg_of_le : type_of% @_root_.Int.ediv_eq_neg_one_of_neg_of_le := by
  intro a b neg le
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero neg
  obtain ⟨m, rfl⟩ := Int.eq_succ_of_zero_lt (a := b) (by omega)
  change Int.negSucc (n / (m+1)) = Int.negSucc 0
  exact congrArg Int.negSucc (Nat.div_eq_of_lt (by omega))

public theorem Int.ediv_eq_one_of_neg_of_le : type_of% @_root_.Int.ediv_eq_one_of_neg_of_le := by
  intro a b neg le
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero neg
  obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero (Int.lt_of_le_of_lt le neg)
  change Int.ofNat (n / (m+1) + 1) = Int.ofNat 1
  rw [Nat.div_eq_of_lt (show n < m+1 by omega)]

public theorem Int.neg_ediv : type_of% @_root_.Int.neg_ediv := by
  intro a b
  if zero : b = 0 then
    subst b
    rw [Int.ediv_zero, Int.ediv_zero, Int.sign_zero, ite_self]
    rfl
  else
    conv => lhs; rw [← Int.mul_ediv_add_emod a b]
    rw [Int.neg_add, ← Int.mul_neg, Int.mul_add_ediv_left _ _ zero, Int.add_comm]
    if divides : b ∣ a then
      rw [ite_eq_left divides, Int.emod_eq_zero_of_dvd divides, Int.neg_zero, Int.zero_ediv]
      omega
    else
      rw [ite_eq_right divides]
      have positive := (Int.emod_pos_of_not_dvd divides).resolve_left zero
      if sign : 0 < b then
        have limit := Int.emod_lt_of_pos a sign
        rw [Int.sign_eq_one_of_pos sign, Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)]
        omega
      else
        have negative : b < 0 := by omega
        have limit := Int.emod_lt_of_neg a negative
        rw [Int.sign_eq_neg_one_of_neg negative, Int.ediv_eq_one_of_neg_of_le (by omega) (by omega)]
        omega

public theorem Int.neg_emod : type_of% @_root_.Int.neg_emod := by
  intro a b
  if divides : b ∣ a then
    rw [ite_eq_left divides, Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr divides)]
  else
    rw [ite_eq_right divides, Int.emod_def, Int.emod_def, Int.neg_ediv, ite_eq_right divides,
      Int.mul_sub, Int.mul_neg, Int.mul_sign_self]
    omega

public theorem Int.fmod_eq_emod : type_of% @_root_.Int.fmod_eq_emod := by
  intro a b
  if pos : 0 ≤ b then
    rw [ite_eq_left (Or.inl pos), Int.add_zero, Int.fmod_eq_emod_of_nonneg _ pos]
  else if divides : b ∣ a then
    rw [ite_eq_left (Or.inr divides), Int.fmod_eq_zero_of_dvd divides, Int.emod_eq_zero_of_dvd divides]
    rfl
  else
    have neg : 0 ≤ -b := by omega
    rw [ite_eq_right (fun h => h.elim pos divides)]
    calc
      a.fmod b = -((-a).fmod (-b)) := by rw [Int.neg_fmod_neg, Int.neg_neg]
      _ = -((-a) % b) := by rw [Int.fmod_eq_emod_of_nonneg _ neg, Int.emod_neg]
      _ = a % b + b := by
        rw [Int.neg_emod, ite_eq_right divides]
        have abs := Int.natAbs_of_nonneg neg
        rw [Int.natAbs_neg] at abs
        omega

public theorem Int.fdiv_eq_ediv : type_of% @_root_.Int.fdiv_eq_ediv := by
  intro a b
  if zero : b = 0 then
    subst b
    rw [Int.fdiv_zero, Int.ediv_zero, ite_eq_left (Or.inl (Int.le_refl 0))]
    rfl
  else
    apply Int.eq_of_mul_eq_mul_left zero
    have difference := Int.fmod_eq_emod (a := a) (b := b)
    rw [Int.fmod_def, Int.emod_def] at difference
    if noCorrection : 0 ≤ b ∨ b ∣ a then
      rw [ite_eq_left noCorrection, Int.sub_zero]
      rw [ite_eq_left noCorrection, Int.add_zero] at difference
      omega
    else
      rw [ite_eq_right noCorrection, Int.mul_sub, Int.mul_one]
      rw [ite_eq_right noCorrection] at difference
      omega

public theorem Int.add_mul_fdiv_right : type_of% @_root_.Int.add_mul_fdiv_right := by
  intro a b c nz
  rw [_root_.Int.fdiv_eq_ediv, Int.add_mul_ediv_right _ _ nz, _root_.Int.fdiv_eq_ediv]
  have divides := Int.dvd_add_left (b := a) (Int.dvd_mul_left b c)
  if normal : 0 ≤ c ∨ c ∣ a then
    rw [ite_eq_left normal, ite_eq_left (normal.imp id divides.mpr)]
    omega
  else
    rw [ite_eq_right normal, ite_eq_right (fun h => normal (h.imp id divides.mp))]
    omega

public theorem Int.add_fdiv_of_dvd_right : type_of% @_root_.Int.add_fdiv_of_dvd_right := by
  intro a b c divides
  if zero : c = 0 then
    subst c
    rw [Int.fdiv_zero, Int.fdiv_zero, Int.fdiv_zero, Int.add_zero]
  else
    obtain ⟨d, rfl⟩ := divides
    rw [_root_.Int.add_mul_fdiv_left _ _ zero, Int.mul_fdiv_cancel_left _ zero]

public theorem Int.tdiv_nonneg_of_nonpos_of_nonpos : type_of% @_root_.Int.tdiv_nonneg_of_nonpos_of_nonpos := by
  intro a b ha hb
  rw [← Int.neg_tdiv_neg]
  exact Int.tdiv_nonneg (Int.neg_nonneg_of_nonpos ha) (Int.neg_nonneg_of_nonpos hb)

public theorem Int.tdiv_eq_zero_iff_natAbs_lt_or_eq_zero : type_of% @_root_.Int.tdiv_eq_zero_iff_natAbs_lt_or_eq_zero := by
  intro a b
  if zero : b = 0 then exact ⟨fun _ => Or.inr zero, fun _ => zero ▸ Int.tdiv_zero a⟩
  else
    have positive := Nat.pos_of_ne_zero (fun z => zero (Int.natAbs_eq_zero.mp z))
    apply Int.natAbs_eq_zero.symm.trans
    rw [Int.natAbs_tdiv]
    exact (Nat.div_eq_zero_iff_lt positive).trans ⟨Or.inl, fun h => h.resolve_right zero⟩

public theorem Int.dvd_antisymm : type_of% @_root_.Int.dvd_antisymm := by
  intro a b ha hb
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  exact fun ab ba => congrArg Int.ofNat (Nat.dvd_antisymm (Int.ofNat_dvd.mp ab) (Int.ofNat_dvd.mp ba))

public theorem Int.ediv_dvd_iff_dvd_mul : type_of% @_root_.Int.ediv_dvd_iff_dvd_mul := by
  intro a b c divides nz
  refine ⟨Int.dvd_mul_of_ediv_dvd divides, ?_⟩
  rintro ⟨k, eq⟩
  refine ⟨k, Int.eq_of_mul_eq_mul_left nz ?_⟩
  rw [← Int.mul_assoc, Int.mul_ediv_cancel_of_dvd divides]
  exact eq

public theorem Int.sign_emod : type_of% @_root_.Int.sign_emod := by
  intro a b nz
  if divides : b ∣ a then rw [ite_eq_left divides, Int.emod_eq_zero_of_dvd divides, Int.sign_zero]
  else rw [ite_eq_right divides, Int.sign_eq_one_of_pos ((Int.emod_pos_of_not_dvd divides).resolve_left nz)]

private theorem scaledDivisionCondition (a b c q : Int) (pos : 0 < a) :
    (0 ≤ a * q ∨ a*c ∣ a*b) ↔ (0 ≤ q ∨ c ∣ b) :=
  or_congr ⟨fun h => Int.nonneg_of_mul_nonneg_right h pos,
    fun h => Int.mul_nonneg (Int.le_of_lt pos) h⟩ (Int.mul_dvd_mul_iff_left (Int.ne_of_gt pos))

public theorem Int.mul_tdiv_mul_of_pos : type_of% @_root_.Int.mul_tdiv_mul_of_pos := by
  intro a b c pos
  rw [_root_.Int.tdiv_eq_ediv, _root_.Int.tdiv_eq_ediv, Int.mul_ediv_mul_of_pos _ _ pos,
    Int.sign_mul, Int.sign_eq_one_of_pos pos, Int.one_mul]
  if normal : 0 ≤ b ∨ c ∣ b then
    rw [ite_eq_left normal, ite_eq_left ((scaledDivisionCondition a b c b pos).mpr normal)]
  else
    rw [ite_eq_right normal, ite_eq_right (fun h => normal ((scaledDivisionCondition a b c b pos).mp h))]

public theorem Int.mul_fdiv_mul_of_pos : type_of% @_root_.Int.mul_fdiv_mul_of_pos := by
  intro a b c pos
  rw [Int.fdiv_eq_ediv, Int.fdiv_eq_ediv, Int.mul_ediv_mul_of_pos _ _ pos]
  if normal : 0 ≤ c ∨ c ∣ b then
    rw [ite_eq_left normal, ite_eq_left ((scaledDivisionCondition a b c c pos).mpr normal)]
  else
    rw [ite_eq_right normal, ite_eq_right (fun h => normal ((scaledDivisionCondition a b c c pos).mp h))]

public theorem Int.le_emod_self_add_one_iff : type_of% @_root_.Int.le_emod_self_add_one_iff := by
  intro a b pos
  have lower := Int.emod_nonneg a (Int.ne_of_gt pos)
  have upper := Int.emod_lt_of_pos a pos
  have equivalent : b ∣ a+1 ↔ b ∣ a%b+1 := by
    calc
      b ∣ a+1 ↔ b ∣ b*(a/b)+(a%b+1) := by rw [← Int.add_assoc, Int.mul_ediv_add_emod]
      _ ↔ b ∣ a%b+1 := Int.dvd_add_right (Int.dvd_mul_right b (a/b))
  constructor
  · intro le
    apply equivalent.mpr
    rw [show a%b+1 = b by omega]
    exact Int.dvd_refl b
  · intro divides
    exact Int.le_of_dvd (by omega) (equivalent.mp divides)

public theorem Int.natAbs_fdiv_le_natAbs : type_of% @_root_.Int.natAbs_fdiv_le_natAbs := by
  intro a b
  if pos : 0 ≤ b then
    rw [Int.fdiv_eq_ediv_of_nonneg _ pos]
    exact Int.natAbs_ediv_le_natAbs ..
  else
    rw [← Int.neg_fdiv_neg, Int.fdiv_eq_ediv_of_nonneg _ (show 0 ≤ -b by omega),
      ← Int.natAbs_neg a]
    exact Int.natAbs_ediv_le_natAbs ..

public theorem Int.sign_ediv : type_of% @_root_.Int.sign_ediv := by
  intro a b
  have withPositive (n : Int) (hn : 0 < n) :
      (a/n).sign = if 0 ≤ a ∧ a < n then 0 else a.sign := by
    if small : 0 ≤ a ∧ a < n then
      rw [ite_eq_left small, Int.ediv_eq_zero_of_lt small.1 small.2, Int.sign_zero]
    else
      rw [ite_eq_right small]
      if neg : a < 0 then
        rw [Int.sign_eq_neg_one_of_neg neg, Int.sign_eq_neg_one_of_neg (Int.ediv_neg_of_neg_of_pos neg hn)]
      else
        have lower : n ≤ a := by omega
        have qpos : 1 ≤ a/n := Int.le_ediv_of_mul_le hn ((Int.one_mul n).symm ▸ lower)
        rw [Int.sign_eq_one_of_pos (show 0 < a by omega), Int.sign_eq_one_of_pos (by omega : 0 < a/n)]
  if zero : b = 0 then
    subst b
    rw [Int.ediv_zero, Int.sign_zero, Int.mul_zero, ite_self]
  else if pos : 0 < b then
    rw [Int.sign_eq_one_of_pos pos, Int.mul_one, Int.natAbs_of_nonneg (Int.le_of_lt pos)]
    exact withPositive b pos
  else
    have neg : b < 0 := by omega
    have pos := Int.neg_pos_of_neg neg
    have eq := withPositive (-b) pos
    rw [Int.ediv_neg, Int.sign_neg] at eq
    have abs := Int.natAbs_of_nonneg (Int.le_of_lt pos)
    rw [Int.natAbs_neg] at abs
    rw [abs, Int.sign_eq_neg_one_of_neg neg, Int.mul_neg, Int.mul_one]
    if small : 0 ≤ a ∧ a < -b then
      rw [ite_eq_left small] at eq ⊢
      omega
    else
      rw [ite_eq_right small] at eq ⊢
      omega

public theorem Int.sign_tdiv : type_of% @_root_.Int.sign_tdiv := by
  intro a b
  have nonneg (m : Int) (positive : 0 ≤ m) (n : Int) :
      (m.tdiv n).sign = if m.natAbs < n.natAbs then 0 else m.sign * n.sign := by
    rw [Int.tdiv_eq_ediv_of_nonneg positive, Int.sign_ediv]
    have abs := Int.natAbs_of_nonneg positive
    if small : m.natAbs < n.natAbs then
      rw [ite_eq_left small, ite_eq_left ⟨positive, by omega⟩]
    else rw [ite_eq_right small, ite_eq_right (fun h => small (by omega))]
  if pos : 0 ≤ a then exact nonneg a pos b
  else
    have h := nonneg (-a) (show 0 ≤ -a by omega) b
    rw [Int.neg_tdiv, Int.sign_neg, Int.natAbs_neg, Int.sign_neg, Int.neg_mul] at h
    if small : a.natAbs < b.natAbs then
      rw [ite_eq_left small] at h ⊢
      omega
    else
      rw [ite_eq_right small] at h ⊢
      omega

public theorem Int.add_one_tdiv_of_pos : type_of% @_root_.Int.add_one_tdiv_of_pos := by
  intro a b pos
  obtain ⟨m, rfl⟩ := Int.eq_succ_of_zero_lt pos
  cases a with
  | ofNat n =>
    have nonneg : 0 ≤ Int.ofNat n := Int.natCast_nonneg n
    have posNext : 0 < Int.ofNat n + 1 := by omega
    if divides : m+1 ∣ n+1 then
      have integer : (Int.ofNat (m+1)) ∣ Int.ofNat n + 1 := Int.ofNat_dvd.mpr divides
      rw [ite_eq_left (Or.inl ⟨posNext, integer⟩)]
      change ((↑((n+1)/(m+1))) : Int) = ↑(n/(m+1)) + 1
      rw [Nat.succ_div_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd divides)]
      rfl
    else
      rw [ite_eq_right (fun h => h.elim (fun d => divides (Int.ofNat_dvd.mp d.2))
        (fun d => Int.not_lt.mpr nonneg d.1))]
      change ((↑((n+1)/(m+1))) : Int) = ↑(n/(m+1)) + 0
      rw [Nat.succ_div_of_mod_ne_zero (fun eq => divides (Nat.dvd_of_mod_eq_zero eq)), Int.add_zero]
  | negSucc n =>
    have current : Int.negSucc n = -(Int.ofNat (n+1)) := rfl
    have next : Int.negSucc n + 1 = -Int.ofNat n := by
      change -((n : Int)+1)+1 = -(n : Int)
      omega
    have neg := Int.negSucc_lt_zero n
    rw [next, current, Int.neg_tdiv, Int.neg_tdiv]
    if divides : m+1 ∣ n+1 then
      have integer : (Int.ofNat (m+1)) ∣ -(Int.ofNat (n+1)) := Int.dvd_neg.mpr (Int.ofNat_dvd.mpr divides)
      rw [ite_eq_left (Or.inr ⟨neg, integer⟩)]
      change -(↑(n/(m+1)) : Int) = -(↑((n+1)/(m+1)) : Int) + 1
      rw [Nat.succ_div_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd divides), Int.natCast_add]
      omega
    else
      have notPositive : ¬0 < -Int.ofNat n := by omega
      rw [ite_eq_right (fun h => h.elim (fun d => notPositive d.1)
        (fun d => divides (Int.ofNat_dvd.mp (Int.dvd_neg.mp d.2))))]
      change -(↑(n/(m+1)) : Int) = -(↑((n+1)/(m+1)) : Int) + 0
      rw [Nat.succ_div_of_mod_ne_zero (fun eq => divides (Nat.dvd_of_mod_eq_zero eq)), Int.add_zero]

public theorem Int.add_one_tdiv : type_of% @_root_.Int.add_one_tdiv := by
  intro a b
  if zero : b = 0 then
    subst b
    rw [Int.tdiv_zero, Int.tdiv_zero, Int.sign_zero, ite_self, Int.add_zero]
  else if pos : 0 < b then
    rw [Int.sign_eq_one_of_pos pos]
    exact Int.add_one_tdiv_of_pos pos
  else
    have neg : b < 0 := by omega
    have eq := Int.add_one_tdiv_of_pos (a := a) (Int.neg_pos_of_neg neg)
    rw [Int.tdiv_neg, Int.tdiv_neg] at eq
    rw [Int.sign_eq_neg_one_of_neg neg]
    have equivalent : ((0 < a+1 ∧ -b ∣ a+1) ∨ (a < 0 ∧ -b ∣ a)) ↔
        ((0 < a+1 ∧ b ∣ a+1) ∨ (a < 0 ∧ b ∣ a)) :=
      or_congr (and_congr_right fun _ => Int.neg_dvd) (and_congr_right fun _ => Int.neg_dvd)
    if step : (0 < a+1 ∧ b ∣ a+1) ∨ (a < 0 ∧ b ∣ a) then
      rw [ite_eq_left (equivalent.mpr step)] at eq
      rw [ite_eq_left step]
      omega
    else
      rw [ite_eq_right (fun h => step (equivalent.mp h))] at eq
      rw [ite_eq_right step]
      omega

public theorem Int.tdiv_le_tdiv : type_of% @_root_.Int.tdiv_le_tdiv := by
  intro a b c pos le
  obtain ⟨d,rfl⟩ := Int.exists_add_of_le le
  induction d with
  | zero => rw [Int.natCast_zero, Int.add_zero]; exact Int.le_refl _
  | succ d ih =>
    rw [Int.natCast_succ, ← Int.add_assoc, Int.add_one_tdiv_of_pos pos]
    split <;> omega

public theorem Int.ediv_gcd_ne_zero_of_ne_zero_left : type_of% @_root_.Int.ediv_gcd_ne_zero_of_ne_zero_left :=
  fun b nz q => nz (Int.eq_zero_of_ediv_eq_zero (Int.gcd_dvd_left _ b) q)

public theorem Int.ediv_gcd_ne_zero_of_ne_zero_right : type_of% @_root_.Int.ediv_gcd_ne_zero_of_ne_zero_right :=
  fun a nz q => nz (Int.eq_zero_of_ediv_eq_zero (Int.gcd_dvd_right a _) q)

public theorem Int.gcd_ne_zero_left : type_of% @_root_.Int.gcd_ne_zero_left :=
  fun nz g => nz (Int.eq_zero_of_gcd_eq_zero_left g)

public theorem Int.gcd_ne_zero_right : type_of% @_root_.Int.gcd_ne_zero_right :=
  fun nz g => nz (Int.eq_zero_of_gcd_eq_zero_right g)

public theorem Int.pow_dvd_pow_iff : type_of% @_root_.Int.pow_dvd_pow_iff := by
  intro a b n nz
  apply Int.natAbs_dvd_natAbs.symm.trans
  rw [Int.natAbs_pow, Int.natAbs_pow]
  exact (Nat.pow_dvd_pow_iff nz).trans Int.natAbs_dvd_natAbs

end OmegaChecks.InitPort.Alternatives
