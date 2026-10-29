/- GID: D5/S3/Combinatorics/Circle/RunFirstEarTransport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/RunFirstEarTransport
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Native same-cut dyadic transport of joint physical source orders. -/
import D5.S3.Combinatorics.Circle.PeriodicShortening
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Same-cut transport of native joint source completions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.RunFirstEarTransport
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening
open scoped BigOperators

/-- Insert the new physical label, retaining every old physical occurrence. -/
def earWord (d : ℕ) (sigma : List (Fin d)) (r : ℕ) : List (Fin (d + 1)) :=
  (sigma.take r).map Fin.castSucc ++ [Fin.last d] ++ (sigma.drop r).map Fin.castSucc

/-- Extend old-source rotation by fixing the inserted physical label. -/
def earRelabel (d h : ℕ) : Equiv.Perm (Fin (d + 1)) where
  toFun := Fin.lastCases (Fin.last d)
    (fun i => (((finRotate d : Equiv.Perm (Fin d)) ^ h) i).castSucc)
  invFun := Fin.lastCases (Fin.last d)
    (fun i => (((finRotate d : Equiv.Perm (Fin d)) ^ h).symm i).castSucc)
  left_inv j := by
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  right_inv j := by
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

private theorem ear_prefix (d : ℕ) (sigma : List (Fin d)) (r : ℕ)
    (hr : r ≤ sigma.length) (f : Fin (d + 1) → ℤ) (n : ℕ) :
    (((earWord d sigma r).take n).map f).sum =
      ((sigma.take (if n ≤ r then n else n - 1)).map (fun i => f i.castSucc)).sum +
        (if n ≤ r then 0 else f (Fin.last d)) := by
  induction sigma generalizing r n with
  | nil =>
    have : r = 0 := by simpa using hr
    subst r
    cases n <;> simp [earWord]
  | cons x xs ih =>
    cases r with
    | zero =>
      cases n with
      | zero => simp [earWord]
      | succ n => simp [earWord, List.map_map, Function.comp_def, add_comm]
    | succ r =>
      have hr' : r ≤ xs.length := by simpa using hr
      cases n with
      | zero => simp [earWord]
      | succ n =>
        have he := ih r hr' n
        simp only [earWord, List.take_succ_cons, List.drop_succ_cons, List.map_cons,
          List.cons_append, List.take_succ_cons, List.sum_cons] at he ⊢
        split_ifs with hn
        · have hn' : n ≤ r := by omega
          simpa [hn', List.take_succ_cons, List.sum_cons, add_assoc] using congrArg (f x.castSucc + ·) he
        · have hn' : ¬ n ≤ r := by omega
          simpa [hn', show n + 1 - 1 = (n - 1) + 1 by omega,
            List.take_succ_cons, List.sum_cons, add_assoc] using congrArg (f x.castSucc + ·) he

private theorem ear_perm (d : ℕ) (sigma : List (Fin d)) (r : ℕ)
    (hs : sigma.Perm (List.finRange d)) :
    (earWord d sigma r).Perm (List.finRange (d + 1)) := by
  have he : (earWord d sigma r).Perm (sigma.map Fin.castSucc ++ [Fin.last d]) := by
    unfold earWord
    rw [List.map_take, List.map_drop]
    have hp := (List.perm_append_comm :
        ([Fin.last d] ++ (sigma.map Fin.castSucc).drop r).Perm
          ((sigma.map Fin.castSucc).drop r ++ [Fin.last d])).append_left
            ((sigma.map Fin.castSucc).take r)
    have hj : (sigma.map Fin.castSucc).take r ++
        ((sigma.map Fin.castSucc).drop r ++ [Fin.last d]) =
        sigma.map Fin.castSucc ++ [Fin.last d] := by
      rw [← List.append_assoc, List.take_append_drop]
    rw [hj] at hp
    simpa only [List.append_assoc] using hp
  exact he.trans (by simpa [List.finRange_succ_last] using (hs.map Fin.castSucc).append_right [Fin.last d])


private theorem sum_linear {α : Type*} (l : List α) (f g : α → ℤ) :
    (l.map (fun i => 2 * f i - g i)).sum =
      2 * (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

private theorem charge_comparison {α : Type*} (l : List α) (f g : α → ℤ)
    (hf : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    0 ≤ (l.map f).sum ∧ (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; constructor <;> linarith [hf x, hfg x]

private theorem common_cycle (d h : ℕ) (hh : h < d) (j : Fin (d + 1)) :
    let rho := (finRotate (d + 1) : Equiv.Perm (Fin (d + 1))) ^ h
    let C := rho.symm.trans (earRelabel d h)
    (C j).val = if h = 0 then j.val else if j.val = d then 0
      else if j.val + 1 < h then j.val + 1 else if j.val + 1 = h then d else j.val := by
  have rot (n : ℕ) (hn : h < n) (i : Fin n) :
      (((finRotate n : Equiv.Perm (Fin n)) ^ h) i).val = (i.val + h) % n := by
    have he := congrFun (finCycle_eq_finRotate_iterate (k := (⟨h, hn⟩ : Fin n))) i
    simpa [Equiv.Perm.coe_pow, finCycle, Fin.val_add] using (congrArg Fin.val he).symm
  let rho := (finRotate (d + 1) : Equiv.Perm (Fin (d + 1))) ^ h
  obtain ⟨l, rfl⟩ := rho.surjective j
  change ((earRelabel d h) (rho.symm (rho l))).val = _
  rw [Equiv.symm_apply_apply]
  have hr := rot (d + 1) (by omega) l
  change (rho l).val = _ at hr
  refine Fin.lastCases ?_ (fun i => ?_) l
  · have hr := rot (d + 1) (by omega) (Fin.last d)
    simp only [Fin.val_last] at hr
    have el : earRelabel d h (Fin.last d) = Fin.last d := by simp [earRelabel]
    rw [el, Fin.val_last]
    by_cases h0 : h = 0
    · subst h; simp [rho]
    · have hm : (d + h) % (d + 1) = h - 1 := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [rho, hr, hm]
      split_ifs <;> omega
  · have hr := rot (d + 1) (by omega) i.castSucc
    have ht := rot d hh i
    simp only [Fin.val_castSucc] at hr
    have el : earRelabel d h i.castSucc =
        (((finRotate d : Equiv.Perm (Fin d)) ^ h) i).castSucc := by simp [earRelabel]
    rw [el, Fin.val_castSucc, ht]
    change (rho i.castSucc).val = _ at hr
    rw [hr]
    by_cases h0 : h = 0
    · subst h
      simp [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt (by omega : i.val < d + 1)]
    · by_cases hs : i.val + h < d
      · rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (by omega : i.val + h < d + 1)]
        split_ifs <;> omega
      · by_cases he : i.val + h = d
        · rw [he, Nat.mod_self, Nat.mod_eq_of_lt (by omega : d < d + 1)]
          simp [h0]
        · rw [Nat.mod_eq_sub_mod (by omega : d ≤ i.val + h),
            Nat.mod_eq_of_lt (by omega : i.val + h - d < d),
            Nat.mod_eq_sub_mod (by omega : d + 1 ≤ i.val + h),
            Nat.mod_eq_of_lt (by omega : i.val + h - (d + 1) < d + 1)]
          split_ifs <;> omega

set_option maxHeartbeats 2000000 in
/-- Carry any supplied joint completion down a dyadic run, at the identical cut.
The parameter a is arbitrary positive; it need not begin its sign run. -/
theorem native_dyadic_joint_transport (d a h : ℕ) (hd : 2 ≤ d) (ha : 1 ≤ a)
    (hb : 2 ^ h * a < 2 ^ (d - 1)) (sigma : List (Fin d)) (r : ℕ) (hr : r ≤ d)
    (hold : OriginalOrder d (2 ^ h * a) sigma)
    (hnew : OriginalOrder (d + 1) (2 * (2 ^ h * a)) (earWord d sigma r)) :
    let tau := (finRotate d : Equiv.Perm (Fin d)) ^ h
    let sigmaA := sigma.map tau
    let rho := (finRotate (d + 1) : Equiv.Perm (Fin (d + 1))) ^ h
    let C := rho.symm.trans (earRelabel d h)
    OriginalOrder d a sigmaA ∧
    OriginalOrder (d + 1) (2 * a) (earWord d sigmaA r) ∧
    (∀ n : ℕ, ((sigmaA.take n).map (actualSource d a)).sum =
      ((sigma.take n).map (actualSource d (2 ^ h * a))).sum) ∧
    earWord d sigmaA r = (earWord d sigma r).map (earRelabel d h) ∧
    (∀ j : Fin (d + 1), (C j).val =
      if h = 0 then j.val else if j.val = d then 0 else if j.val + 1 < h then j.val + 1
      else if j.val + 1 = h then d else j.val) ∧
    (∀ j : Fin (d + 1), actualSource (d + 1) (2 * (2 ^ h * a)) j =
      actualSource (d + 1) (2 * a) (rho j)) ∧
    actualSource (d + 1) (2 * a) (Fin.last d) = (a : ℤ) ∧
    (∀ j : Fin (d + 1), j.val < h →
      actualSource (d + 1) (2 * a) j = (2 : ℤ) ^ (j.val + 1) * a ∧
      0 < actualSource (d + 1) (2 * a) j ∧
      actualSource (d + 1) (2 * a) j < (2 : ℤ) ^ (d - 1)) ∧
    (Odd a →
      actualSource (d + 1) (2 * a) ⟨d - 1, by omega⟩ =
        -(modulus (d + 1) - (a : ℤ)) / 2 ∧
      actualSource (d + 1) (2 * a) ⟨d - 1, by omega⟩ ≤ -(2 : ℤ) ^ (d - 1)) := by
  classical
  let tau := (finRotate d : Equiv.Perm (Fin d)) ^ h
  let sigmaA := sigma.map tau
  let alpha := fun i => charge d a (tau i)
  let beta := charge d (2 ^ h * a)
  let v := actualSource d (2 ^ h * a)
  have hab : a ≤ 2 ^ h * a := by
    have := Nat.one_le_two_pow (n := h)
    nlinarith
  have hwa : a ≤ 2 ^ (d - 1) - 1 := by omega
  have hwb : 2 ^ h * a ≤ 2 ^ (d - 1) - 1 := by omega
  have hh : h < d := by
    have hp : 2 ^ h < 2 ^ (d - 1) := by nlinarith
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hp
    omega
  have align := native_charge_alignment d a h hd ha hb
  have hvalues (x : ℕ) (hx : x ≤ 2 ^ (d - 1) - 1) :
      (∀ i : Fin d, actualSource (d + 1) (2 * x) i.castSucc =
        2 * actualSource d x i - charge d x i) ∧
      actualSource (d + 1) (2 * x) (Fin.last d) = (x : ℤ) := by
    constructor
    · intro i
      convert (digit_data d x hd hx i).2.2 using 1
      unfold actualSource
      congr 1
      simp only [Fin.val_castSucc, Fin.val_mk, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      ring
    · unfold actualSource
      have he : (2 : ℤ) ^ (Fin.last d).val * (2 * x : ℕ) = (2 : ℤ) ^ (d + 1) * x := by
        simp only [Fin.val_last, Nat.cast_mul, Nat.cast_ofNat, pow_succ]; ring
      rw [he, centered_full_period]
      obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd (d + 1) (by omega)
      have hp : (x : ℤ) < (2 : ℤ) ^ (d - 1) := by
        exact_mod_cast (show x < 2 ^ (d - 1) by have := Nat.one_le_two_pow (n := d - 1); omega)
      have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show d - 1 ≤ d by omega)
      have hhalf : modulus (d + 1) / 2 = (2 : ℤ) ^ d - 1 := by
        unfold modulus; rw [pow_succ]; omega
      exact centered_unique hN ho (centered_bounds hN ho _) (by rw [hhalf]; constructor <;> omega)
        (centered_mod _ _)
  have va := hvalues a hwa
  have vb := hvalues (2 ^ h * a) hwb
  have hnonneg : ∀ i, 0 ≤ alpha i := fun i => (digit_data d a hd hwa (tau i)).1
  have hdom : ∀ i, alpha i ≤ beta i := by
    intro i
    have he := (align i).2
    have hn : 0 ≤ (if (tau i).val < h then (2 : ℤ) ^ (tau i).val * a else 0) := by
      split_ifs <;> positivity
    change beta i = alpha i + _ at he
    linarith
  have hperm : sigmaA.Perm (List.finRange d) :=
    (hold.1.map tau).trans tau.map_finRange_perm
  have heights (n : ℕ) :
      ((sigmaA.take n).map (actualSource d a)).sum = ((sigma.take n).map v).sum := by
    apply congrArg List.sum
    simp only [sigmaA, ← List.map_take, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i _
    exact (align i).1.symm
  have oldA : OriginalOrder d a sigmaA := by
    refine ⟨hperm, ?_, ?_⟩
    · have he : (sigmaA.map (actualSource d a)).sum = (sigma.map v).sum := by
        simpa [sigmaA, ← List.map_take] using heights sigma.length
      exact he.trans hold.2.1
    · intro n
      rw [heights]
      exact hold.2.2 n
  have tota : (sigma.map alpha).sum = (a : ℤ) := by
    have he : (sigma.map alpha).sum = ((List.finRange d).map (charge d a)).sum := by
      simpa [sigmaA, List.map_map, alpha, Function.comp_def] using
        (hperm.map (charge d a)).sum_eq
    rw [he]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact charge_sum d a hd hwa
  have totb : (sigma.map beta).sum = (2 ^ h * a : ℕ) := by
    rw [(hold.1.map beta).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact charge_sum d (2 ^ h * a) hd hwb
  have hlen : sigma.length = d := by simpa using hold.1.length_eq
  have hcut : r ≤ sigma.length := by omega
  have prefixA (n : ℕ) :
      (((earWord d sigmaA r).take n).map (actualSource (d + 1) (2 * a))).sum =
        2 * ((sigma.take (if n ≤ r then n else n - 1)).map v).sum -
          ((sigma.take (if n ≤ r then n else n - 1)).map alpha).sum +
          (if n ≤ r then 0 else (a : ℤ)) := by
    rw [ear_prefix d sigmaA r (by simpa [sigmaA] using hcut)]
    simp only [sigmaA, ← List.map_take, List.map_map, Function.comp_def]
    have he : (fun i => actualSource (d + 1) (2 * a) (tau i).castSucc) =
        (fun i => 2 * v i - alpha i) := by
      funext i
      rw [va.1, ← (align i).1]
    rw [he, sum_linear, va.2]
  have prefixB (n : ℕ) :
      (((earWord d sigma r).take n).map (actualSource (d + 1) (2 * (2 ^ h * a)))).sum =
        2 * ((sigma.take (if n ≤ r then n else n - 1)).map v).sum -
          ((sigma.take (if n ≤ r then n else n - 1)).map beta).sum +
          (if n ≤ r then 0 else ((2 ^ h * a : ℕ) : ℤ)) := by
    rw [ear_prefix d sigma r hcut]
    have he : (fun i : Fin d => actualSource (d + 1) (2 * (2 ^ h * a)) i.castSucc) =
        (fun i => 2 * v i - beta i) := by funext i; exact vb.1 i
    rw [he, sum_linear, vb.2]
  have hstrip (n : ℕ) :
      (((earWord d sigmaA r).take n).map (actualSource (d + 1) (2 * a))).sum ∈
        Set.Icc (0 : ℤ) (modulus (d + 1) / 2) := by
    have bn := hnew.2.2 n
    rw [prefixB] at bn
    rw [prefixA]
    simp only [Set.mem_Icc] at bn ⊢
    by_cases hn : n ≤ r
    · simp only [if_pos hn] at bn ⊢
      have vn := hold.2.2 n
      have cn := charge_comparison (sigma.take n) alpha beta hnonneg hdom
      have hB : 2 * (modulus d / 2) ≤ modulus (d + 1) / 2 := by
        unfold modulus; rw [pow_succ]; omega
      change 0 ≤ ((sigma.take n).map v).sum ∧
        ((sigma.take n).map v).sum ≤ modulus d / 2 at vn
      constructor
      · linarith only [bn.1, cn.2]
      · linarith only [vn.2, cn.1, hB]
    · simp only [if_neg hn] at bn ⊢
      have vn := hold.2.2 (n - 1)
      change 0 ≤ ((sigma.take (n - 1)).map v).sum ∧ _ at vn
      have cd := charge_comparison (sigma.drop (n - 1)) alpha beta hnonneg hdom
      have asplit : ((sigma.take (n - 1)).map alpha).sum +
          ((sigma.drop (n - 1)).map alpha).sum = (a : ℤ) := by
        rw [← List.sum_append, ← List.map_append, List.take_append_drop, tota]
      have bsplit : ((sigma.take (n - 1)).map beta).sum +
          ((sigma.drop (n - 1)).map beta).sum = (2 ^ h * a : ℕ) := by
        rw [← List.sum_append, ← List.map_append, List.take_append_drop, totb]
      constructor
      · linarith only [vn.1, cd.1, asplit]
      · linarith only [bn.2, cd.2, asplit, bsplit]
  have newA : OriginalOrder (d + 1) (2 * a) (earWord d sigmaA r) := by
    refine ⟨ear_perm d sigmaA r hperm, ?_, hstrip⟩
    rw [((ear_perm d sigmaA r hperm).map (actualSource (d + 1) (2 * a))).sum_eq]
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact (ZeroSumSubsets.source_cycle (by omega : 0 < d + 1) (2 * a)).2.1

  have normalized (j : Fin (d + 1)) :
      actualSource (d + 1) (2 * (2 ^ h * a)) j =
        actualSource (d + 1) (2 * a)
          (((finRotate (d + 1) : Equiv.Perm (Fin (d + 1))) ^ h) j) := by
    let jj := (((finRotate (d + 1) : Equiv.Perm (Fin (d + 1))) ^ h) j)
    have he := congrFun (finCycle_eq_finRotate_iterate
      (k := (⟨h, by omega⟩ : Fin (d + 1)))) j
    have hv : jj.val = (j.val + h) % (d + 1) := by
      simpa [jj, Equiv.Perm.coe_pow, finCycle, Fin.val_add] using (congrArg Fin.val he).symm
    change centered (modulus (d + 1)) ((2 : ℤ) ^ j.val * (2 * (2 ^ h * a) : ℕ)) =
      centered (modulus (d + 1)) ((2 : ℤ) ^ jj.val * (2 * a : ℕ))
    by_cases hj : j.val + h < d + 1
    · have hidx : jj.val = j.val + h := by rw [hv, Nat.mod_eq_of_lt hj]
      congr 1
      simp only [hidx, pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    · have hidx : jj.val = j.val + h - (d + 1) := by
        rw [hv, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      apply centered_congr
      have heq : (2 : ℤ) ^ j.val * (2 * (2 ^ h * a) : ℕ) =
          (2 : ℤ) ^ jj.val * (2 * a : ℕ) +
            ((2 : ℤ) ^ jj.val * (2 * a : ℕ)) * modulus (d + 1) := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, modulus]
        have hexp : j.val + h = d + 1 + jj.val := by omega
        have hp : (2 : ℤ) ^ j.val * 2 ^ h = (2 : ℤ) ^ (d + 1) * 2 ^ jj.val := by
          rw [← pow_add, hexp, pow_add]
        nlinarith
      rw [heq, Int.add_mul_emod_self_right]
  have small_values (j : Fin (d + 1)) (hj : j.val < h) :
      actualSource (d + 1) (2 * a) j = (2 : ℤ) ^ (j.val + 1) * a ∧
      0 < actualSource (d + 1) (2 * a) j ∧
      actualSource (d + 1) (2 * a) j < (2 : ℤ) ^ (d - 1) := by
    have hu : 2 ^ (j.val + 1) * a ≤ 2 ^ h * a :=
      Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by omega) (by omega))
    have hub : (2 : ℤ) ^ (j.val + 1) * a < (2 : ℤ) ^ (d - 1) := by
      exact_mod_cast (show 2 ^ (j.val + 1) * a < 2 ^ (d - 1) by omega)
    have hup : 0 < (2 : ℤ) ^ (j.val + 1) * a :=
      mul_pos (by positivity) (by exact_mod_cast (show 0 < a by omega))
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show d - 1 ≤ d by omega)
    have hhalf : modulus (d + 1) / 2 = (2 : ℤ) ^ d - 1 := by
      unfold modulus; rw [pow_succ]; omega
    obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd (d + 1) (by omega)
    have heq : actualSource (d + 1) (2 * a) j = (2 : ℤ) ^ (j.val + 1) * a := by
      apply centered_unique hN ho (centered_bounds hN ho _) (by rw [hhalf]; constructor <;> omega)
      rw [centered_mod]
      congr 1
      simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      ring
    exact ⟨heq, by rw [heq]; exact hup, by rw [heq]; exact hub⟩
  have odd_predecessor (ho : Odd a) :
      actualSource (d + 1) (2 * a) ⟨d - 1, by omega⟩ =
        -(modulus (d + 1) - (a : ℤ)) / 2 ∧
      actualSource (d + 1) (2 * a) ⟨d - 1, by omega⟩ ≤ -(2 : ℤ) ^ (d - 1) := by
    obtain ⟨t, ht⟩ := ho
    have hat : (a : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
    have hp : (a : ℤ) < (2 : ℤ) ^ (d - 1) := by
      exact_mod_cast (show a < 2 ^ (d - 1) by omega)
    have hpow : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
      conv_lhs => rw [show d = d - 1 + 1 by omega, pow_succ]
      ring
    have hhalf : modulus (d + 1) / 2 = (2 : ℤ) ^ d - 1 := by
      unfold modulus; rw [pow_succ]; omega
    obtain ⟨hN, hno⟩ := TwoRunSource.modulus_positive_odd (d + 1) (by omega)
    have hv : actualSource (d + 1) (2 * a) ⟨d - 1, by omega⟩ =
        (t : ℤ) + 1 - (2 : ℤ) ^ d := by
      apply centered_unique hN hno (centered_bounds hN hno _)
        (by rw [hhalf]; constructor <;> omega)
      rw [centered_mod]
      have heq : (2 : ℤ) ^ (d - 1) * (2 * a : ℕ) =
          (t : ℤ) + 1 - (2 : ℤ) ^ d + modulus (d + 1) * ((t : ℤ) + 1) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat, modulus, pow_succ]
        rw [hat, hpow]
        ring
      change ((2 : ℤ) ^ (d - 1) * (2 * a : ℕ)) % _ = _
      rw [heq, Int.add_mul_emod_self_left]
    rw [hv]
    unfold modulus
    rw [pow_succ]
    constructor <;> omega

  refine ⟨oldA, newA, heights, ?_, common_cycle d h hh, normalized, va.2,
    small_values, odd_predecessor⟩
  simp [earWord, sigmaA, ← List.map_take, ← List.map_drop, List.map_append, List.map_map, earRelabel, Function.comp_def]


end D5.S3.Combinatorics.Circle.RunFirstEarTransport
