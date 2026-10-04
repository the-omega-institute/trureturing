/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelData
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelData
   mirror-E: none(waiver:quadratic-cycle-data)
   anchors: [mathlib/module/Mathlib.RingTheory.AdicCompletion.Completeness]
   utility: none
   digest: Triple induction constructs the metallic cycle and evaluates its weight and sign. -/

import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDefs
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelTransfer
import Mathlib.RingTheory.AdicCompletion.Completeness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelData

open PowerSeries MetallicHankelTransfer

/-- States of the rotated metallic quadratic cycle. -/
inductive TailState where
  | u₀ : ℕ → TailState
  | u₁ : ℕ → TailState
  | u₂ : ℕ → TailState
  | v₀ | v₁ | v₂ | v₃
  | w₀ : ℕ → TailState
  | w₁ : ℕ → TailState
  | w₂ : ℕ → TailState

/-- Exactly the indices occurring in one metallic cycle. -/
def validState (n : ℕ) : TailState → Prop
  | .u₀ i | .u₁ i | .u₂ i | .w₀ i => i ≤ n - 2
  | .w₁ i | .w₂ i => i < n - 2
  | .v₀ | .v₁ | .v₂ | .v₃ => True

/-- The state following a quadratic transition. -/
def nextState (n : ℕ) : TailState → TailState
  | .u₀ i => .u₁ i
  | .u₁ i => .u₂ i
  | .u₂ i => if i = n - 2 then .v₀ else .u₀ (i + 1)
  | .v₀ => .v₁
  | .v₁ => .v₂
  | .v₂ => .v₃
  | .v₃ => .w₀ 0
  | .w₀ i => if i = n - 2 then .u₀ 0 else .w₁ i
  | .w₁ i => .w₂ i
  | .w₂ i => .w₀ (i + 1)

/-- Integral quadratic triples, with the quadratic coefficient divided by `X`. -/
noncomputable def quadraticData (n : ℕ) : TailState →
    PowerSeries ℤ × PowerSeries ℤ × PowerSeries ℤ :=
  let I := invOfUnit (1 - X : PowerSeries ℤ) 1
  let E := (X : PowerSeries ℤ) ^ 2 - X + 1
  let T := X * (1 - X ^ n) * I + (1 + X ^ n) * (1 - X)
  fun state => match state with
  | .u₀ i =>
      (E * X ^ (n - i - 2), -E * (2 * X ^ (n - i) - X ^ n - 1) * I,
        X * (E * (X ^ (n - i) - X ^ n - 1) + X ^ (i + 1)) * I ^ 2)
  | .u₁ i =>
      (X ^ i, E * (1 - X ^ n) * I, -E * X ^ (n - i - 1))
  | .u₂ i =>
      if i = n - 2 then
        (1 + X ^ 2 * (1 - X ^ (n - 1)) * I, T - 2 * X ^ n, -X ^ (n - 1))
      else
        (-(E * (X ^ (n - i - 1) - X ^ n - 1) + X ^ (i + 2)) * I ^ 2,
          (E * (X ^ n + 1) - 2 * X ^ (i + 2)) * I, -X ^ (i + 1))
  | .v₀ =>
      (-X ^ (n - 1), T + 2 * X ^ (n + 1),
        -X - X ^ 3 * (1 - X ^ (n - 1)) * I)
  | .v₁ => (X ^ n, T, -X ^ n)
  | .v₂ => (X ^ (n - 1), T, -X ^ (n + 1))
  | .v₃ =>
      (-1 - X ^ 2 * (1 - X ^ (n - 1)) * I, T + 2 * X ^ (n + 1), -X ^ n)
  | .w₀ i =>
      (X ^ (n - i - 2), (E * (X ^ n + 1) - 2 * X ^ (n - i)) * I,
        X * (E * (X ^ (i + 1) - X ^ n - 1) + X ^ (n - i)) * I ^ 2)
  | .w₁ i => (E * X ^ i, E * (1 - X ^ n) * I, -X ^ (n - i - 1))
  | .w₂ i =>
      (-(E * (X ^ (i + 2) - X ^ n - 1) + X ^ (n - i - 1)) * I ^ 2,
        -E * (2 * X ^ (i + 2) - X ^ n - 1) * I, -E * X ^ (i + 1))

/-- Degrees, signs, and finite denominators attached to the quadratic states. -/
noncomputable def fractionData (n : ℕ) : TailState → ℕ × ℤ × PowerSeries ℤ :=
  let I := invOfUnit (1 - X : PowerSeries ℤ) 1
  let T := X * (1 - X ^ n) * I + (1 + X ^ n) * (1 - X)
  fun state => match state with
  | .u₀ i => (n - i - 2, -1, (1 - X ^ (n - i)) * I)
  | .u₁ i => (i, -1, (1 - X ^ (i + 2)) * I - X)
  | .u₂ i => (0, -1, if i = n - 2 then 1 else 1 - X)
  | .v₀ => (n - 1, 1, T + X ^ (n + 1))
  | .v₁ => (n, -1, T)
  | .v₂ => (n - 1, -1, T + X ^ (n + 1))
  | .v₃ => (0, 1, 1)
  | .w₀ i => (n - i - 2, -1, (1 - X ^ (n - i)) * I - X)
  | .w₁ i => (i, -1, (1 - X ^ (i + 2)) * I)
  | .w₂ _ => (0, -1, 1 - X)

/-- The rotated state itinerary, including the exceptional terminal triples. -/
def cycle (n : ℕ) : List TailState :=
  [.v₂, .v₃] ++
    (List.range (n - 2)).flatMap (fun i => [.w₀ i, .w₁ i, .w₂ i]) ++
    [.w₀ (n - 2)] ++
    (List.range (n - 1)).flatMap (fun i => [.u₀ i, .u₁ i, .u₂ i]) ++
    [.v₀, .v₁]

/-- The triple itinerary closes, and its length and degree weight are exact. -/
theorem cycle_data (n : ℕ) (hn : 2 ≤ n) :
    (cycle n).length = 6 * n - 4 ∧
    (∀ a ∈ cycle n, validState n a) ∧
    List.IsChain (fun a b => nextState n a = b) (cycle n ++ [.v₂]) ∧
    ((cycle n).map (fun a => (fractionData n a).1 + 1)).sum = 2 * n * (n + 1) ∧
    (cycle n).map (fun a =>
      (coeff ((fractionData n a).1 + 1) (fractionData n a).2.2,
        (fractionData n a).2.1)) = topWord n ∧
    (∀ a, validState n a →
      constantCoeff (fractionData n a).2.2 = 1 ∧
      ∀ r, (fractionData n a).1 + 1 < r → coeff r (fractionData n a).2.2 = 0) := by
  let W (i : ℕ) : List TailState := [.w₀ i, .w₁ i, .w₂ i]
  let U (i : ℕ) : List TailState := [.u₀ i, .u₁ i, .u₂ i]
  let ws (m : ℕ) := (List.range m).flatMap W
  let us (m : ℕ) := (List.range m).flatMap U
  have ws_step (m : ℕ) : ws (m + 1) = ws m ++ W m := by
    simp [ws, List.range_succ]
  have us_step (m : ℕ) : us (m + 1) = us m ++ U m := by
    simp [us, List.range_succ]
  have length_blocks (m : ℕ) : (ws m).length = 3 * m ∧ (us m).length = 3 * m := by
    induction m with
    | zero => simp [ws, us]
    | succ m ih =>
      rw [ws_step, us_step]
      simp only [List.length_append, W, U, List.length_cons, List.length_nil] at *
      omega
  have weight_blocks (m : ℕ) (hm : m ≤ n - 1) :
      ((ws m).map (fun a => (fractionData n a).1 + 1)).sum = m * (n + 1) ∧
      ((us m).map (fun a => (fractionData n a).1 + 1)).sum = m * (n + 1) := by
    induction m with
    | zero => simp [ws, us]
    | succ m ih =>
      have hmn : m ≤ n - 2 := by omega
      obtain ⟨hw, hu⟩ := ih (by omega)
      rw [ws_step, us_step]
      simp only [List.map_append, List.sum_append]
      rw [hw, hu]
      simp only [W, U, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, fractionData]
      have hs : n - m - 2 + m + 3 = n + 1 := by omega
      constructor <;> nlinarith [hs]
  have w_chain (m : ℕ) (hm : m ≤ n - 2) :
      List.IsChain (fun a b => nextState n a = b) (.v₃ :: (ws m ++ [.w₀ m])) := by
    induction m with
    | zero => simp [ws, List.isChain_cons_cons, nextState]
    | succ m ih =>
      rw [ws_step, List.append_assoc]
      change List.IsChain _ (.v₃ ::
        (ws m ++ .w₀ m :: .w₁ m :: .w₂ m :: [.w₀ (m + 1)]))
      rw [List.isChain_cons_split]
      refine ⟨ih (by omega), ?_⟩
      simp [List.isChain_cons_cons, nextState, show m ≠ n - 2 by omega]
  have u_chain (m : ℕ) (hm : m ≤ n - 2) :
      List.IsChain (fun a b => nextState n a = b) (.w₀ (n - 2) :: (us m ++ [.u₀ m])) := by
    induction m with
    | zero => simp [us, List.isChain_cons_cons, nextState]
    | succ m ih =>
      rw [us_step, List.append_assoc]
      change List.IsChain _ (.w₀ (n - 2) ::
        (us m ++ .u₀ m :: .u₁ m :: .u₂ m :: [.u₀ (m + 1)]))
      rw [List.isChain_cons_split]
      refine ⟨ih (by omega), ?_⟩
      simp [List.isChain_cons_cons, nextState, show m ≠ n - 2 by omega]
  have cyc : cycle n =
      [.v₂, .v₃] ++ ws (n - 2) ++ [.w₀ (n - 2)] ++ us (n - 1) ++ [.v₀, .v₁] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cyc]
    simp only [List.length_append, List.length_cons, List.length_nil,
      (length_blocks (n - 2)).1, (length_blocks (n - 1)).2]
    omega
  · intro a ha
    simp only [cycle, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap, List.mem_range, or_assoc] at ha
    rcases ha with ha | ha | ⟨i, hi, ha⟩ | ha | ⟨i, hi, ha⟩ | ha | ha
    · subst a; trivial
    · subst a; trivial
    · rcases ha with ha | ha | ha <;> subst a <;> simp [validState] <;> omega
    · subst a; simp [validState]
    · rcases ha with ha | ha | ha <;> subst a <;> simp [validState] <;> omega
    · subst a; trivial
    · subst a; trivial
  · have un : n - 1 = (n - 2) + 1 := by omega
    rw [cyc, un, us_step]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [List.isChain_cons_cons]
    refine ⟨rfl, ?_⟩
    rw [List.isChain_cons_split]
    refine ⟨w_chain (n - 2) (by omega), ?_⟩
    simp only [U, List.cons_append, List.nil_append]
    rw [List.isChain_cons_split]
    refine ⟨u_chain (n - 2) (by omega), ?_⟩
    simp [List.isChain_cons_cons, nextState]
  · rw [cyc]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    rw [(weight_blocks (n - 2) (by omega)).1,
      (weight_blocks (n - 1) (by omega)).2]
    simp only [fractionData]
    have hs : n - (n - 2) - 2 = 0 := by omega
    rw [hs]
    nlinarith [show n - 1 = n - 2 + 1 by omega,
      show n - 2 + 2 = n by omega]
  · let I : PowerSeries ℤ := invOfUnit (1 - X) 1
    have hI : (1 - X : PowerSeries ℤ) * I = 1 := by
      exact mul_invOfUnit _ _ (by simp)
    have coeffI (r : ℕ) : coeff r I = 1 := by
      induction r with
      | zero => simp [I]
      | succ r ih =>
        have hc := congrArg (coeff (r + 1)) hI
        rw [sub_mul, one_mul, map_sub] at hc
        have hx : coeff (r + 1) (X * I) = coeff r I := by
          simpa only [pow_one, Nat.add_sub_cancel] using coeff_X_pow_mul I 1 r
        rw [hx, ih] at hc
        simp only [coeff_one, Nat.succ_ne_zero, ite_false] at hc
        omega
    have geom (m r : ℕ) :
        coeff r ((1 - X ^ m) * I) = if r < m then 1 else 0 := by
      rw [sub_mul, one_mul, map_sub, coeffI, coeff_X_pow_mul']
      split_ifs <;> simp_all <;> omega
    dsimp only [I] at geom
    let scalar (a : TailState) : ℤ × ℤ :=
      (coeff ((fractionData n a).1 + 1) (fractionData n a).2.2,
        (fractionData n a).2.1)
    have wtop (i : ℕ) (hi : i < n - 2) :
        (W i).map scalar = [(1, -1), (1, -1), (-1, -1)] := by
      have hk : 1 < n - i - 2 + 1 := by omega
      have hki : n - i - 2 + 1 < n - i := by omega
      simp [W, scalar, fractionData,  map_sub, geom, coeff_X, coeff_one,
        show n - i - 2 ≠ 0 by omega, hki, show i + 1 < i + 2 by omega]
    have utop (i : ℕ) (hi : i < n - 2) :
        (U i).map scalar =
          [(1, -1), (if i = 0 then 0 else 1, -1), (-1, -1)] := by
      have hki : n - i - 2 + 1 < n - i := by omega
      simp [U, scalar, fractionData,  map_sub, geom, coeff_X, coeff_one,
        hki, show i + 1 < i + 2 by omega, show i ≠ n - 2 by omega]
      split_ifs <;> simp_all <;> omega
    have uend : (U (n - 2)).map scalar =
        [(1, -1), (if n = 2 then 0 else 1, -1), (0, -1)] := by
      have hk : n - (n - 2) - 2 = 0 := by omega
      have hd : n - (n - 2) = 2 := by omega
      simp [U, scalar, fractionData,  hk, hd, map_sub, geom, coeff_X, coeff_one]
      split_ifs <;> simp_all <;> omega
    have wend : scalar (.w₀ (n - 2)) = (0, -1) := by
      have hk : n - (n - 2) - 2 = 0 := by omega
      have hd : n - (n - 2) = 2 := by omega
      simp [scalar, fractionData,  hk, hd, map_sub, geom, coeff_X]
    have vt : scalar .v₂ = (2, -1) ∧ scalar .v₃ = (0, 1) ∧
        scalar .v₀ = (2, 1) ∧ scalar .v₁ = (-1, -1) := by
      have hk : n - 1 + 1 = n := by omega
      simp only [scalar, fractionData, hk]
      have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      have hTn : coeff n
          (X * (1 - X ^ n) * I + (1 + X ^ n) * (1 - X)) = 2 := by
        rw [mul_assoc]
        rw [show X * ((1 - X ^ n) * I) = X ^ 1 * ((1 - X ^ n) * I) by simp,
          map_add, coeff_X_pow_mul' ]
        simp only [I]
        simp [map_add, mul_sub, add_mul, mul_one, geom, coeff_X_pow_mul',
          coeff_X_pow, coeff_X, coeff_one, hn0, hn1, show n - 1 < n by omega, show 1 ≤ n by omega,
          ← pow_succ, show n ≠ n + 1 by omega]
      have hTnp : coeff (n + 1)
          (X * (1 - X ^ n) * I + (1 + X ^ n) * (1 - X)) = -1 := by
        rw [mul_assoc]
        rw [show X * ((1 - X ^ n) * I) = X ^ 1 * ((1 - X ^ n) * I) by simp,
          map_add, coeff_X_pow_mul' ]
        simp only [I]
        simp [map_add, mul_sub, add_mul, mul_one, geom, coeff_X_pow_mul',
          coeff_X_pow, coeff_X, coeff_one, hn0, hn1, ← pow_succ]
      have hEn : coeff n
          (X * (1 - X ^ n) * I + (1 + X ^ n) * (1 - X) + X ^ (n + 1)) = 2 := by
        rw [map_add, hTn]
        simp [coeff_X_pow]
      change (coeff n (_ + _ + X ^ (n + 1)), (-1 : ℤ)) = (2, -1) ∧
        (coeff 1 1, (1 : ℤ)) = (0, 1) ∧
        (coeff n (_ + _ + X ^ (n + 1)), (1 : ℤ)) = (2, 1) ∧
        (coeff (n + 1) (_ + _), (-1 : ℤ)) = (-1, -1)
      rw [hEn, hTnp]
      simp
    have wordW (m : ℕ) (hm : m ≤ n - 2) :
        (ws m).map scalar =
          (List.replicate m [(1, -1), (1, -1), (-1, -1)]).flatten := by
      induction m with
      | zero => simp [ws]
      | succ m ih =>
        rw [ws_step, List.map_append, ih (by omega), wtop m (by omega)]
        simp only [List.replicate_succ', List.flatten_append, List.flatten_cons,
          List.flatten_nil, List.append_nil]
    change (cycle n).map scalar = topWord n
    rw [cyc, List.map_append, List.map_append, List.map_append, List.map_append]
    simp only [List.map_cons, List.map_nil, vt.1, vt.2.1, vt.2.2.1, vt.2.2.2, wend]
    rw [wordW (n - 2) (by omega)]
    by_cases hn2 : n = 2
    · subst n
      have hu : us 1 = U 0 := by simp [us]
      rw [hu]
      simpa [topWord] using congrArg
        (fun l => l ++ [(2, (1 : ℤ)), (-1, -1)])
          uend
    · obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have first : (U 0).map scalar = [(1, -1), (0, -1), (-1, -1)] := by
        simpa using utop 0 (by omega)
      have rest (r : ℕ) (hr : r ≤ n - 3) :
          ((List.range' 1 r).flatMap U).map scalar =
            (List.replicate r [(1, -1), (1, -1), (-1, -1)]).flatten := by
        induction r with
        | zero => simp
        | succ r ih =>
          rw [List.range'_1_concat, List.flatMap_append, List.map_append]
          rw [ih (by omega)]
          simp only [List.flatMap_singleton]
          rw [utop (1 + r) (by omega)]
          simp [List.replicate_succ', show 1 + r ≠ 0 by omega]
      have hu : us (n - 1) = U 0 ++ (List.range' 1 (n - 3)).flatMap U ++ U (n - 2) := by
        have hx : n - 1 = (n - 2) + 1 := by omega
        rw [hx, us_step]
        simp only [us, List.range_eq_range']
        rw [show n - 2 = 1 + (n - 3) by omega, ← List.range'_append_1]
        simp [List.flatMap_append, List.append_assoc]
      rw [hu, List.map_append, List.map_append, first, rest _ (by omega), uend,
        if_neg hn2]
      simp [topWord, hn2, List.append_assoc]
  · let I : PowerSeries ℤ := invOfUnit (1 - X) 1
    have hI : (1 - X : PowerSeries ℤ) * I = 1 := mul_invOfUnit _ _ (by simp)
    have coeffI (r : ℕ) : coeff r I = 1 := by
      induction r with
      | zero => simp [I]
      | succ r ih =>
        have hc := congrArg (coeff (r + 1)) hI
        rw [sub_mul, one_mul, map_sub] at hc
        have hx : coeff (r + 1) (X * I) = coeff r I := by
          simpa only [pow_one, Nat.add_sub_cancel] using coeff_X_pow_mul I 1 r
        rw [hx, ih] at hc
        simp only [coeff_one, Nat.succ_ne_zero, ite_false] at hc
        omega
    have geom (m r : ℕ) :
        coeff r ((1 - X ^ m) * I) = if r < m then 1 else 0 := by
      rw [sub_mul, one_mul, map_sub, coeffI, coeff_X_pow_mul']
      split_ifs <;> simp_all <;> omega
    dsimp only [I] at geom
    intro a ha
    constructor
    · cases a <;> simp only [validState] at ha <;>
        simp [fractionData, show n ≠ 0 by omega, show n + 1 ≠ 0 by omega,
          show n - 2 < n by omega, show n - 1 ≠ 0 by omega] <;>
        simp_all <;> (try split_ifs) <;> (try simp_all) <;> omega
    · intro r hr
      cases a with
      | u₀ i | w₀ i =>
        simp only [validState] at ha
        have hdeg : ¬r < n - i := by simp only [fractionData] at hr; omega
        have hr1 : r ≠ 1 := by simp only [fractionData] at hr; omega
        simp [fractionData, map_sub, geom, hdeg, coeff_X, hr1]
      | u₁ i | w₁ i =>
        have hdeg : ¬r < i + 2 := by simp only [fractionData] at hr; omega
        have hr1 : r ≠ 1 := by simp only [fractionData] at hr; omega
        simp [fractionData, map_sub, geom, hdeg, coeff_X, hr1]
      | u₂ i | w₂ i | v₃ =>
        have hr0 : r ≠ 0 := by simp only [fractionData] at hr; omega
        have hr1 : r ≠ 1 := by simp only [fractionData] at hr; omega
        simp [fractionData, map_sub, coeff_X, coeff_one, hr0, hr1] <;>
          split_ifs <;> simp [map_sub, coeff_X, coeff_one, hr0, hr1]
      | v₀ | v₂ =>
        have hdeg : n < r := by simp only [fractionData] at hr; omega
        have heq : (X : PowerSeries ℤ) * (1 - X ^ n) * (invOfUnit (1 - X) 1) +
            (1 + X ^ n) * (1 - X) + X ^ (n + 1) =
            X * ((1 - X ^ n) * (invOfUnit (1 - X) 1)) + 1 - X + X ^ n := by
          rw [pow_succ]
          ring
        simp only [fractionData]
        rw [heq]
        simp only [map_add, map_sub]
        have hx : coeff r ((X : PowerSeries ℤ) * ((1 - X ^ n) * invOfUnit (1 - X) 1)) = 0 := by
          rw [show X = (X : PowerSeries ℤ) ^ 1 by simp, coeff_X_pow_mul']
          simp [geom, show 1 ≤ r by omega, show ¬r - 1 < n by omega]
        simp [hx, coeff_X_pow, coeff_X, coeff_one,
          show r ≠ 0 by omega, show r ≠ 1 by omega, show r ≠ n by omega]
      | v₁ =>
        have hdeg : n + 1 < r := by simp only [fractionData] at hr; omega
        simp only [fractionData]
        rw [mul_assoc]
        have hx : coeff r ((X : PowerSeries ℤ) * ((1 - X ^ n) * invOfUnit (1 - X) 1)) = 0 := by
          rw [show X = (X : PowerSeries ℤ) ^ 1 by simp, coeff_X_pow_mul']
          simp [geom, show 1 ≤ r by omega, show ¬r - 1 < n by omega]
        simp [map_add, mul_sub, add_mul, mul_one, hx, ← pow_succ,
          coeff_X_pow, coeff_X, coeff_one, show r ≠ 0 by omega,
          show r ≠ 1 by omega, show r ≠ n by omega, show r ≠ n + 1 by omega]

/-- Pairing the two identical triple runs cancels their determinant multipliers. -/
theorem cycle_sign (n : ℕ) (hn : 2 ≤ n) :
    ((cycle n).map (fun a => (fractionData n a).2.1)).prod = 1 ∧
    (∏ i ∈ Finset.range (cycle n).length,
      let a := (cycle n).getD i .v₂
      let k := (fractionData n a).1
      let h := -(∏ j ∈ Finset.range (i + 1),
        (fractionData n ((cycle n).getD j .v₂)).2.1)
      (-1 : ℤ) ^ (k * (k + 1) / 2) * h ^ (k + 1)) = (-1) ^ n := by
  let σ (k : ℕ) : ℤ := (-1) ^ (k * (k + 1) / 2)
  let step (z : ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
    (-z.1, z.2 * σ k * (-z.1) ^ (k + 1))
  have run_formula (ks : List ℕ) (h a : ℤ) :
      ks.foldl step (h, a) =
        ((-1) ^ ks.length * h,
          a * (ks.foldl step (1, 1)).2 * h ^ (ks.map (· + 1)).sum) := by
    induction ks generalizing h a with
    | nil => simp
    | cons k ks ih =>
      simp only [List.foldl_cons, List.length_cons, List.map_cons, List.sum_cons]
      change ks.foldl step (-h, a * σ k * (-h) ^ (k + 1)) = _
      have hs : step (1, 1) k = (-1, σ k * (-1) ^ (k + 1)) := by
        simp only [step, one_mul]
      rw [hs]
      rw [ih, ih (-1) (σ k * (-1) ^ (k + 1))]
      apply Prod.ext
      · simp only [pow_succ]
        ring
      · have hp (r : ℕ) : (-h) ^ r = (-1) ^ r * h ^ r := by
          rw [show -h = (-1) * h by ring, mul_pow]
        simp only [hp, pow_add]
        ring
  have run_square (ks : List ℕ) (h a : ℤ) (hh : h ^ 2 = 1) (ha : a ^ 2 = 1) :
      (ks.foldl step (h, a)).1 ^ 2 = 1 ∧ (ks.foldl step (h, a)).2 ^ 2 = 1 := by
    induction ks generalizing h a with
    | nil => exact ⟨hh, ha⟩
    | cons k ks ih =>
      simp only [List.foldl_cons]
      apply ih
      · simp [step, hh]
      · dsimp [step]
        have hσ : (σ k) ^ 2 = 1 := by
          dsimp [σ]
          rw [← pow_mul, Nat.mul_comm, pow_mul]
          norm_num
        rw [mul_pow, mul_pow, ha, hσ, one_mul, one_mul, ← pow_mul,
          show (k + 1) * 2 = 2 * (k + 1) by omega, pow_mul, neg_sq, hh, one_pow]
  let ks (r : ℕ) : List ℕ :=
    (List.range r).flatMap (fun i => [n - i - 2, i, 0])
  have ks_step (r : ℕ) : ks (r + 1) = ks r ++ [n - r - 2, r, 0] := by
    simp [ks, List.range_succ]
  have run_weight (r : ℕ) (hr : r ≤ n - 1) :
      (ks r).length = 3 * r ∧ ((ks r).map (· + 1)).sum = r * (n + 1) := by
    induction r with
    | zero => simp [ks]
    | succ r ih =>
      obtain ⟨hl, hw⟩ := ih (by omega)
      rw [ks_step]
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, hl, hw]
      constructor
      · omega
      · have hdeg : n - r - 2 + r + 3 = n + 1 := by omega
        nlinarith
  let kb (a : TailState) : ℕ × ℤ := ((fractionData n a).1, (fractionData n a).2.1)
  let transfer (z : ℤ × ℤ) (a : ℕ × ℤ) : ℤ × ℤ :=
    (z.1 * a.2, z.2 * σ a.1 * (z.1 * a.2) ^ (a.1 + 1))
  have layout : (cycle n).tail.map kb =
      [(0, 1)] ++ (ks (n - 2)).map (fun k => (k, (-1 : ℤ))) ++ [(0, -1)] ++
      (ks (n - 2)).map (fun k => (k, (-1 : ℤ))) ++
      [(0, -1), (n - 2, -1), (0, -1), (n - 1, 1), (n, -1)] := by
    have hx : n - 1 = n - 2 + 1 := by omega
    simp only [cycle, List.cons_append, List.nil_append, List.tail_cons,
      List.map_cons, List.map_append, List.map_nil, kb, fractionData, hx,
      List.range_succ, List.flatMap_append, List.flatMap_singleton]
    simp only [ks, List.map_flatMap, List.map_cons, List.map_nil]
    have heq : n - (n - 2) - 2 = 0 := by omega
    simp only [heq, List.append_assoc, List.cons_append, List.nil_append]
  have fold_minus (l : List ℕ) (z : ℤ × ℤ) :
      (l.map (fun k => (k, (-1 : ℤ)))).foldl transfer z = l.foldl step z := by
    simp only [List.foldl_map]
    congr 1
    funext z k
    simp [step, transfer]
  let q := n - 2
  let H : ℤ := (-1) ^ (3 * q)
  let C : ℤ := ((ks q).foldl step (1, 1)).2
  have hc : C ^ 2 = 1 := (run_square (ks q) 1 1 (by norm_num) (by norm_num)).2
  have hH : H ^ 2 = 1 := by
    dsimp [H]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hhpow : (-H) ^ (q * (n + 1)) = 1 := by
    have heven : ((3 * q + 1) * (q * (n + 1))) % 2 = 0 := by
      have hq : q % 2 < 2 := Nat.mod_lt _ (by decide)
      have hnmod : n % 2 < 2 := Nat.mod_lt _ (by decide)
      have hprod : ((3 * q + 1) * q) % 2 = 0 := by
        rw [Nat.mul_mod]
        by_cases hq0 : q % 2 = 0
        · simp [hq0]
        · have hq1 : q % 2 = 1 := by omega
          have hleft : (3 * q + 1) % 2 = 0 := by omega
          simp [hq1, hleft]
      rw [← Nat.mul_assoc, Nat.mul_mod, hprod]
      simp
    have he : Even ((3 * q + 1) * (q * (n + 1))) := by
      exact Nat.even_iff.mpr heven
    rw [show -H = (-1 : ℤ) ^ (3 * q + 1) by simp [H, pow_succ], ← pow_mul]
    exact he.neg_one_pow
  have hws := run_weight q (by dsimp [q]; omega)
  have paired (a : ℤ) :
      (ks q).foldl step
        (transfer ((ks q).foldl step (1, a)) (0, -1)) = (-1, a * -H) := by
    have hw : (ks q).foldl step (1, a) = (H, a * C) := by
      rw [run_formula, hws.1, hws.2]
      simp [H, C]
    rw [hw]
    have hz : transfer (H, a * C) (0, -1) = (-H, a * C * -H) := by
      simp [transfer, σ]
    rw [hz]
    rw [run_formula, hws.1, hws.2, hhpow]
    apply Prod.ext
    · change H * -H = -1
      nlinarith [hH]
    · change a * C * -H * C * 1 = a * -H
      calc
        _ = (a * -H) * C ^ 2 := by ring
        _ = _ := by rw [hc, mul_one]
  have sigma_square (k : ℕ) : (σ k) ^ 2 = 1 := by
    dsimp [σ]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have ending : σ (n - 2) * σ n * (-1) ^ (n + 1) = (-1) ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have ht : (m + 2) * (m + 3) = m * (m + 1) + 2 * (2 * m + 3) := by ring
    have hdiv : (m + 2) * (m + 3) / 2 = m * (m + 1) / 2 + (2 * m + 3) := by
      rw [ht, Nat.add_mul_div_left]
      omega
    dsimp [σ]
    simp only [Nat.add_sub_cancel]
    rw [show m + 2 + 1 = m + 3 by omega, hdiv, pow_add]
    have hs : ((-1 : ℤ) ^ (m * (m + 1) / 2)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have he : (-1 : ℤ) ^ (2 * m + 3) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [he]
    have hp : (-1 : ℤ) ^ (m + 3) = -((-1) ^ (m + 2)) := by
      rw [show m + 3 = (m + 2) + 1 by omega, pow_succ]
      ring
    rw [hp]
    calc
      _ = ((-1 : ℤ) ^ (m * (m + 1) / 2)) ^ 2 * (-1) ^ (m + 2) := by ring
      _ = _ := by rw [hs, one_mul]
  constructor
  · have blocks (r : ℕ) :
        (((List.range r).flatMap (fun i =>
          [.w₀ i, .w₁ i, .w₂ i])).map (fun a => (fractionData n a).2.1)).prod =
            (-1 : ℤ) ^ (3 * r) ∧
        (((List.range r).flatMap (fun i =>
          [.u₀ i, .u₁ i, .u₂ i])).map (fun a => (fractionData n a).2.1)).prod =
            (-1 : ℤ) ^ (3 * r) := by
      induction r with
      | zero => simp
      | succ r ih =>
        simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton,
          List.map_append, List.prod_append, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil]
        rw [ih.1, ih.2]
        simp only [fractionData]
        constructor <;> rw [show 3 * (r + 1) = 3 * r + 3 by omega, pow_add] <;>
          norm_num
    simp only [cycle, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil]
    rw [(blocks (n - 2)).1, (blocks (n - 1)).2]
    simp only [fractionData, one_mul, mul_one]
    rw [show 3 * (n - 1) = 3 * (n - 2) + 3 by omega, pow_add]
    nlinarith [hH]
  · have fold_end : (cycle n).tail.foldl (fun z a => transfer z (kb a))
        (1, σ (n - 1)) = (-1, (-1) ^ n) := by
      rw [← List.foldl_map, layout]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hstart : transfer (1, σ (n - 1)) (0, 1) = (1, σ (n - 1)) := by
        simp [transfer, σ]
      rw [hstart, fold_minus, fold_minus, paired]
      have hneg : -H = (-1 : ℤ) ^ (n - 2 + 1) := by
        have hq : 3 * q = q + 2 * q := by omega
        simp only [H, hq, pow_add, pow_mul, neg_one_sq, one_pow, mul_one,
          pow_succ]
        dsimp [q]
        ring
      simp only [transfer, mul_one, mul_neg_one, neg_neg, zero_add,
        show σ 0 = 1 by simp [σ], pow_one, one_pow]
      apply Prod.ext
      · simp
      · rw [hneg]
        have hp : ((-1 : ℤ) ^ (n - 2 + 1)) ^ 2 = 1 := by
          rw [← pow_mul, Nat.mul_comm, pow_mul]
          norm_num
        calc
          _ = (σ (n - 1)) ^ 2 * ((-1 : ℤ) ^ (n - 2 + 1)) ^ 2 *
              (σ (n - 2) * σ n * (-1) ^ (n + 1)) := by ring
          _ = (-1) ^ n := by rw [sigma_square, hp, ending]; ring

    let b (i : ℕ) : ℤ := (fractionData n ((cycle n).getD i .v₂)).2.1
    let k (i : ℕ) : ℕ := (fractionData n ((cycle n).getD i .v₂)).1
    let h (i : ℕ) : ℤ := -(∏ j ∈ Finset.range (i + 1), b j)
    let r (i : ℕ) : ℤ := σ (k i) * h i ^ (k i + 1)
    have fold_prefix (i : ℕ) (hi : i ≤ (cycle n).length) :
        ((cycle n).take i).foldl (fun z a => transfer z (kb a)) (-1, 1) =
          (-(∏ j ∈ Finset.range i, b j), ∏ j ∈ Finset.range i, r j) := by
      induction i with
      | zero => simp
      | succ i ih =>
        have hil : i < (cycle n).length := by omega
        rw [List.take_succ_eq_append_getElem hil, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (by omega), Finset.prod_range_succ, Finset.prod_range_succ]
        have hb : (kb ((cycle n)[i])).2 = b i := by
          change (fractionData n ((cycle n)[i])).2.1 =
            (fractionData n ((cycle n).getD i .v₂)).2.1
          rw [List.getD_eq_getElem (cycle n) .v₂ hil]
        have hk : (kb ((cycle n)[i])).1 = k i := by
          change (fractionData n ((cycle n)[i])).1 =
            (fractionData n ((cycle n).getD i .v₂)).1
          rw [List.getD_eq_getElem (cycle n) .v₂ hil]
        simp only [transfer, hb, hk]
        change (-(∏ j ∈ Finset.range i, b j) * b i,
          (∏ j ∈ Finset.range i, r j) * σ (k i) *
            (-(∏ j ∈ Finset.range i, b j) * b i) ^ (k i + 1)) = _
        have hh : h i = -(∏ j ∈ Finset.range i, b j) * b i := by
          simp [h, Finset.prod_range_succ]
        rw [← hh]
        apply Prod.ext <;> simp [r, hh, mul_assoc]
    have full_end : (cycle n).foldl (fun z a => transfer z (kb a)) (-1, 1) =
        (-1, (-1) ^ n) := by
      have hfirst : (cycle n).head? = some .v₂ := by simp [cycle]
      have hcons : cycle n = .v₂ :: (cycle n).tail := by simp [cycle]
      rw [hcons, List.foldl_cons]
      have he : transfer (-1, 1) (kb .v₂) = (1, σ (n - 1)) := by
        simp [transfer, kb, fractionData]
      rw [he]
      exact fold_end
    have he := congrArg Prod.snd (fold_prefix (cycle n).length (by omega))
    simp only [List.take_length, full_end, Prod.snd] at he
    exact he.symm

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelData
