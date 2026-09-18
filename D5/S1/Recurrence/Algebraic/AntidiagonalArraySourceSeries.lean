/- GID: D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The unique A392095 array equals the shifted natural coefficients of A088713. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
The definitions are those of Mikhail Kurkov's OEIS A392095 and Paul D. Hanna's
OEIS A088713, as preregistered in trureturing issue 8186. The source statements
are in the official OEIS export at commit 892a05dd4941ae76caee5906ea33ceedf3389b1d,
paths `seq/A392/A392095.seq` and `seq/A088/A088713.seq` (OEIS Foundation,
CC-BY-SA 4.0). No other source equation or program is used as a premise.

`sourceCoeff` is constructed from the rational functional equation alone.
The single result proves both uniqueness statements before identifying the
array column with these independent coefficients. All auxiliary identities
are local to its proof. Reciprocals have constant coefficient one and all
inner substitution series have constant coefficient zero.
-/

set_option autoImplicit false

open PowerSeries Finset

namespace D5.S1.Recurrence.Algebraic.AntidiagonalArraySourceSeries

/-- The natural array, recursively constructed by antidiagonal and then row. -/
def array : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => array n (k + 1) +
      ∑ j : Fin (k + 1), array n j * array (k - j) 0
termination_by n k => (n + k, n)
decreasing_by
  all_goals simp_wf
  · have he : n + (k + 1) = n + 1 + k := by omega
    rw [he]
    exact Prod.Lex.right _ (by omega)
  · apply Prod.Lex.left; omega
  · apply Prod.Lex.left; omega

/-- All clauses of the source array definition, with both endpoints included. -/
def IsArray (T : ℕ → ℕ → ℕ) : Prop :=
  (∀ k, T 0 k = 1) ∧ ∀ n k,
    T (n + 1) k = T n (k + 1) + ∑ j ∈ range (k + 1), T n j * T (k - j) 0

/-- Normalized rational source equation; division means multiplicative inverse. -/
def IsSource (F : PowerSeries ℚ) : Prop :=
  constantCoeff F = 1 ∧
    F.subst (X * invOfUnit F 1) = invOfUnit (1 - X) 1

/-- The substitution operator, defined without reference to the array. -/
noncomputable def phi (F : PowerSeries ℚ) : PowerSeries ℚ :=
  F.subst (X * invOfUnit F 1)

/-- Triangular rational construction from the functional equation alone. -/
noncomputable def sourceCoeff (n : ℕ) : ℚ :=
  if hn : n = 0 then 1 else
    1 - coeff n (phi (PowerSeries.mk fun k =>
      if _hk : k < n then sourceCoeff k else 0))
termination_by n

/-- The independently constructed normalized rational series. -/
noncomputable def sourceSeries : PowerSeries ℚ := PowerSeries.mk sourceCoeff

/-- The complete claim: a unique total array, an independently constructed unique
normalized rational source, a unique natural source sequence, and the shifted
first-column identity for every natural index, including zero. -/
theorem result :
    IsArray array ∧ (∀ T, IsArray T → T = array) ∧
    IsSource sourceSeries ∧ (∀ F, IsSource F → F = sourceSeries) ∧
    ∃ b : ℕ → ℕ,
      IsSource (PowerSeries.mk fun m => (b m : ℚ)) ∧
      (∀ b' : ℕ → ℕ, IsSource (PowerSeries.mk fun m => (b' m : ℚ)) → b' = b) ∧
      b 0 = 1 ∧ (∀ m, coeff m sourceSeries = (b m : ℚ)) ∧
      ∀ n, array n 0 = b (n + 1) := by
  classical
  let row (T : ℕ → ℕ → ℕ) (r : ℕ) : PowerSeries ℚ :=
    PowerSeries.mk fun k => (T r k : ℚ)
  let column (T : ℕ → ℕ → ℕ) : PowerSeries ℚ :=
    PowerSeries.mk fun r => (T r 0 : ℚ)
  have ha : IsArray array := by
    refine ⟨fun k => by rw [array], ?_⟩
    intro n k
    rw [array]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j => array n j * array (k-j) 0) (k+1)
  have hu : ∀ T, IsArray T → T = array := by
    intro T hT
    have heq : ∀ d n k, n + k = d → T n k = array n k := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro n
        induction n with
        | zero => intro k hk; rw [hT.1, ha.1]
        | succ n hn =>
          intro k hk
          rw [hT.2, ha.2, hn (k + 1) (by omega)]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have hj' : j < k+1 := mem_range.mp hj
          rw [ih (n + j) (by omega) n j rfl,
            ih (k - j + 0) (by omega) (k - j) 0 rfl]
    funext n k
    exact heq (n + k) n k rfl
  have hrow : ∀ r, (1 + X * column array) * row array r =
      C (array r 0 : ℚ) + X * row array (r + 1) := by
    intro r
    ext k
    cases k with
    | zero => simp [row]
    | succ k =>
      rw [add_mul, one_mul, mul_assoc, map_add, coeff_succ_X_mul,
        map_add, coeff_succ_X_mul]
      rw [mul_comm (column array) (row array r)]
      simp only [row, coeff_mk, coeff_C, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, zero_add]
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [column, coeff_mk]
      rw [ha.2]
      push_cast
      rfl
  -- Lower coefficients control products, reciprocals and substitution.
  have hpow : ∀ i n (U V : PowerSeries ℚ),
      (∀ k, k ≤ n → coeff k U = coeff k V) → coeff n (U ^ i) = coeff n (V ^ i) := by
    intro i
    induction i with
    | zero => intros; rfl
    | succ i ih =>
      intro n U V h
      rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
      apply Finset.sum_congr rfl
      rintro ⟨a,b⟩ hab
      have hab' := Finset.mem_antidiagonal.mp hab
      rw [h b (by omega), ih a U V (fun k hk => h k (by omega))]
  have hinv : ∀ n (U V : PowerSeries ℚ),
      (∀ k, k ≤ n → coeff k U = coeff k V) →
      coeff n (invOfUnit U 1) = coeff n (invOfUnit V 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U V h
      rw [coeff_invOfUnit, coeff_invOfUnit]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn, if_neg hn]
        congr 1
        apply Finset.sum_congr rfl
        rintro ⟨a,b⟩ hab
        have hab' := Finset.mem_antidiagonal.mp hab
        by_cases hb : b < n
        · rw [if_pos hb, if_pos hb, h a (by omega),
            ih b hb U V (fun k hk => h k (by omega))]
        · rw [if_neg hb, if_neg hb]
  have hsubst : ∀ (U V : PowerSeries ℚ) n,
      coeff n (U.subst (X * V)) =
      ∑ i ∈ range (n + 1), coeff i U * coeff (n - i) (V ^ i) := by
    intro U V n
    rw [coeff_subst' (HasSubst.of_constantCoeff_zero' (by simp))]
    rw [finsum_eq_finsetSum_of_support_subset _ (s := range (n + 1))]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow, coeff_X_pow_mul', if_pos (by simpa using Nat.le_of_lt_succ (mem_range.mp hi))]
      rfl
    · intro i hi
      apply mem_range.mpr
      by_contra hn
      have hni : ¬ i ≤ n := by omega
      have hz : coeff i U • coeff n ((X * V) ^ i) = 0 := by
        rw [mul_pow, coeff_X_pow_mul', if_neg hni, smul_zero]
      exact hi hz
  have hphi : ∀ (U : PowerSeries ℚ) n,
      coeff n (phi U) = coeff n U +
      ∑ i ∈ range n, coeff i U * coeff (n - i) ((invOfUnit U 1) ^ i) := by
    intro U n
    rw [phi, hsubst, sum_range_succ]
    simp only [Nat.sub_self, coeff_zero_eq_constantCoeff, map_pow,
      constantCoeff_invOfUnit, inv_one, Units.val_one, one_pow, mul_one]
    exact add_comm _ _
  have htri : ∀ (U V : PowerSeries ℚ) n,
      (∀ k, k < n → coeff k U = coeff k V) →
      coeff n (phi U) - coeff n (phi V) = coeff n U - coeff n V := by
    intro U V n h
    rw [hphi, hphi]
    have hs : (∑ i ∈ range n, coeff i U * coeff (n-i) ((invOfUnit U 1)^i)) =
        ∑ i ∈ range n, coeff i V * coeff (n-i) ((invOfUnit V 1)^i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := mem_range.mp hi
      rw [h i (mem_range.mp hi)]
      by_cases hi0 : i = 0
      · subst i
        rfl
      · congr 1
        apply hpow i (n-i)
        intro k hk
        apply hinv k
        intro j hj
        exact h j (by omega)
    rw [hs]
    ring
  have hgeo : invOfUnit (1 - X : PowerSeries ℚ) 1 = PowerSeries.mk 1 := by
    have h1 := invOfUnit_mul (1-X : PowerSeries ℚ) 1 (by simp)
    have h2 := mk_one_mul_one_sub_eq_one ℚ
    calc
      invOfUnit (1-X : PowerSeries ℚ) 1 =
          invOfUnit (1-X : PowerSeries ℚ) 1 * ((1-X) * PowerSeries.mk 1) := by
            rw [mul_comm (1-X), h2, mul_one]
      _ = PowerSeries.mk 1 := by rw [← mul_assoc, h1, one_mul]
  have hsource : IsSource sourceSeries := by
    constructor
    · rw [sourceSeries, constantCoeff_mk, sourceCoeff, dif_pos rfl]
    · change phi sourceSeries = _
      rw [hgeo]
      ext n
      simp only [coeff_mk, Pi.one_apply]
      cases n with
      | zero =>
        rw [hphi]
        simp only [sum_range_zero, add_zero, sourceSeries, coeff_mk]
        rw [sourceCoeff, dif_pos rfl]
      | succ n =>
        let P : PowerSeries ℚ := PowerSeries.mk fun k =>
          if k < n+1 then sourceCoeff k else 0
        have h := htri sourceSeries P (n+1) (by
          intro k hk
          simp only [sourceSeries, P, coeff_mk, if_pos hk])
        have hp : coeff (n+1) P = 0 := by simp [P]
        have hq : coeff (n+1) sourceSeries = 1 - coeff (n+1) (phi P) := by
          rw [sourceSeries, coeff_mk]
          rw [sourceCoeff, dif_neg (by omega)]
          simp only [dite_eq_ite]
          rfl
        rw [hp, hq] at h
        linear_combination h
  have hunique : ∀ F, IsSource F → F = sourceSeries := by
    intro F hF
    ext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have ht := htri F sourceSeries n ih
      have he : phi F = phi sourceSeries := hF.2.trans hsource.2.symm
      rw [he, sub_self] at ht
      exact sub_eq_zero.mp ht.symm
  -- The all-row bridge is finite at each coefficient; no limit is taken.
  let H : PowerSeries ℚ := 1 + X * column array
  let I : PowerSeries ℚ := invOfUnit H 1
  let Y : PowerSeries ℚ := X * I
  have hH0 : constantCoeff H = 1 := by simp [H]
  have hIH : I * H = 1 := invOfUnit_mul H 1 hH0
  have hHI : H * I = 1 := mul_invOfUnit H 1 hH0
  have hY0 : constantCoeff Y = 0 := by simp [Y]
  have hYS : HasSubst Y := HasSubst.of_constantCoeff_zero' hY0
  have hrowrec : ∀ r, row array r = I * C (array r 0 : ℚ) + Y * row array (r+1) := by
    intro r
    calc
      row array r = I * (H * row array r) := by rw [← mul_assoc, hIH, one_mul]
      _ = I * (C (array r 0 : ℚ) + X * row array (r+1)) := by rw [hrow]
      _ = I * C (array r 0 : ℚ) + Y * row array (r+1) := by dsimp [Y]; ring
  have htel : ∀ N, row array 0 =
      I * (∑ i ∈ range N, C (array i 0 : ℚ) * Y ^ i) + Y ^ N * row array N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      calc
        row array 0 = I * (∑ i ∈ range N, C (array i 0 : ℚ) * Y ^ i) +
            Y ^ N * (I * C (array N 0 : ℚ) + Y * row array (N+1)) := by
              conv_lhs => rw [ih]
              rw [hrowrec N]
        _ = I * (∑ i ∈ range (N+1), C (array i 0 : ℚ) * Y ^ i) +
            Y ^ (N+1) * row array (N+1) := by rw [sum_range_succ, pow_succ]; ring
  have hbridge : (column array).subst Y = H * row array 0 := by
    ext d
    have ht : H * row array 0 =
        (∑ i ∈ range (d+1), C (array i 0 : ℚ) * Y ^ i) +
        H * (Y ^ (d+1) * row array (d+1)) := by
      conv_lhs => rw [htel (d+1)]
      rw [mul_add, ← mul_assoc H I, hHI, one_mul]
    have hdiv : X ^ (d+1) ∣ H * (Y ^ (d+1) * row array (d+1)) := by
      refine ⟨H * (I ^ (d+1) * row array (d+1)), ?_⟩
      dsimp [Y]
      rw [mul_pow]
      ring
    have hz := X_pow_dvd_iff.mp hdiv d (by omega)
    have ht' := congrArg (coeff d) ht
    rw [map_add, hz, add_zero, map_sum] at ht'
    rw [ht']
    change coeff d ((column array).subst (X * I)) = _
    rw [hsubst]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ d := by have := mem_range.mp hi; omega
    rw [coeff_C_mul]
    change coeff i (column array) * coeff (d-i) (I^i) =
      (array i 0 : ℚ) * coeff d ((X*I)^i)
    rw [mul_pow, coeff_X_pow_mul', if_pos hi']
    simp only [column, coeff_mk]
  have hrow0 : row array 0 = PowerSeries.mk 1 := by
    ext n
    simp only [row, coeff_mk, ha.1, Nat.cast_one, Pi.one_apply]
  have hgeostep : 1 + X * row array 0 = row array 0 := by
    ext n
    cases n with
    | zero => simp [row, ha.1]
    | succ n => simp [row, ha.1]
  have hHsource : IsSource H := by
    refine ⟨hH0, ?_⟩
    change H.subst Y = _
    calc
      H.subst Y = 1 + Y * (column array).subst Y := by
        dsimp [H]
        rw [subst_add hYS, subst_mul hYS, subst_X hYS]
        congr 1
        rw [← coe_substAlgHom (R := ℚ) hYS, map_one]
      _ = 1 + Y * (H * row array 0) := by rw [hbridge]
      _ = 1 + X * row array 0 := by
        dsimp [Y]
        rw [mul_assoc X I, ← mul_assoc I H, hIH, one_mul]
      _ = invOfUnit (1-X) 1 := by rw [hgeostep, hrow0, hgeo]
  have hident : H = sourceSeries := hunique H hHsource
  have hshift : ∀ n, coeff (n+1) sourceSeries = (array n 0 : ℚ) := by
    intro n
    rw [← hident]
    simp [H, column]
  have hnat : ∀ m, ∃ a : ℕ, coeff m sourceSeries = (a : ℚ) := by
    intro m
    cases m with
    | zero => exact ⟨1, by simpa only [coeff_zero_eq_constantCoeff, Nat.cast_one] using hsource.1⟩
    | succ n => exact ⟨array n 0, hshift n⟩
  choose b hb using hnat
  have hbseries : (PowerSeries.mk fun m => (b m : ℚ)) = sourceSeries := by
    ext m
    rw [coeff_mk, hb]
  have hbsource : IsSource (PowerSeries.mk fun m => (b m : ℚ)) := by
    rw [hbseries]
    exact hsource
  have hbunique : ∀ b' : ℕ → ℕ,
      IsSource (PowerSeries.mk fun m => (b' m : ℚ)) → b' = b := by
    intro b' hb'
    have he := hunique _ hb'
    funext m
    have hc := congrArg (coeff m) he
    rw [coeff_mk, hb] at hc
    exact_mod_cast hc
  refine ⟨ha, hu, hsource, hunique, b, hbsource, hbunique, ?_, hb, ?_⟩
  · have h := hb 0
    rw [coeff_zero_eq_constantCoeff, hsource.1] at h
    exact_mod_cast h.symm
  · intro n
    have h := (hshift n).symm.trans (hb (n+1))
    exact_mod_cast h

end D5.S1.Recurrence.Algebraic.AntidiagonalArraySourceSeries
