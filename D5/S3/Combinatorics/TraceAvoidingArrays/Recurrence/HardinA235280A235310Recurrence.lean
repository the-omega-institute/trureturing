/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The common recurrences of orders 9, 14, and 18 for Hardin's constant-stress rectangles. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Alternating row profiles yield the published common recurrences in both dimensions. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence

open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
  (C Grid block Low count_eq)
open Polynomial hiding C
open scoped BigOperators

noncomputable section

private abbrev Sequence := ℕ → ℤ

/-- Advance the argument of a sequence by one. -/
private def shift : Module.End ℤ Sequence where
  toFun f n := f (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shift_pow_apply (f : Sequence) (n r : ℕ) :
    (shift ^ r) f n = f (n + r) := by
  induction r generalizing f with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    rfl

private def Kills (P : ℤ[X]) (f : Sequence) : Prop := (aeval shift P) f = 0

private theorem kills_of_dvd {P Q : ℤ[X]} {f : Sequence} (hPQ : Q ∣ P) (hQ : Kills Q f) :
    Kills P f := by
  obtain ⟨R, rfl⟩ := hPQ
  unfold Kills at *
  rw [mul_comm, map_mul, Module.End.mul_apply, hQ, map_zero]

private theorem kills_zero (P : ℤ[X]) : Kills P 0 := by
  exact map_zero (aeval shift P)

private theorem kills_sum {α : Type} [Fintype α] {P : ℤ[X]} (f : α → Sequence)
    (h : ∀ a, Kills P (f a)) : Kills P (∑ a, f a) := by
  unfold Kills at *
  rw [map_sum]
  simp only [h, Finset.sum_const_zero]

private theorem kills_smul {P : ℤ[X]} {f : Sequence} (c : ℤ) (h : Kills P f) :
    Kills P (c • f) := by
  unfold Kills at *
  rw [map_smul, h, smul_zero]

private theorem eval_C_mul_X_pow (a : ℤ) (r : ℕ) (f : Sequence) (n : ℕ) :
    (aeval shift (Polynomial.C a * X ^ r : ℤ[X])) f n = a * f (n + r) := by
  rw [map_mul, Module.End.mul_apply, aeval_C, Algebra.algebraMap_eq_smul_one,
    LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply, map_pow, aeval_X,
    shift_pow_apply, zsmul_eq_mul, Int.cast_id]

private theorem kills_step {d : ℕ} {a : ℤ} {f : Sequence}
    (h : ∀ n, f (n + d) = a * f n) : Kills (X ^ d - Polynomial.C a) f := by
  unfold Kills
  funext n
  rw [map_sub, LinearMap.sub_apply, Pi.sub_apply, map_pow, aeval_X,
    shift_pow_apply, aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
    Module.End.one_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id, h, sub_self]
  rfl

private abbrev Row (d k : ℕ) := Fin (k + 1) → Fin (d + 1)
private abbrev Profile (d k : ℕ) := Fin k → Fin (d + 1)

private def edge {d k : ℕ} (r : Row d k) (j : Fin k) : ℕ :=
  (r j.castSucc).val + (r j.succ).val

private def Fiber {d k : ℕ} (p : Profile d k) := {r : Row d k // ∀ j, edge r j = (p j).val}

private instance {d k : ℕ} (p : Profile d k) : Finite (Fiber p) := by
  unfold Fiber
  infer_instance

private def flip {d k : ℕ} (p : Profile d k) : Profile d k := fun j => (p j).rev

private def profileAt {d k : ℕ} (p : Profile d k) (i : ℕ) : Profile d k :=
  if i % 2 = 0 then p else flip p

@[local simp] private theorem profileAt_zero {d k : ℕ} (p : Profile d k) : profileAt p 0 = p := by
  simp [profileAt]

@[local simp] private theorem profileAt_one {d k : ℕ} (p : Profile d k) : profileAt p 1 = flip p := by
  simp [profileAt]

private theorem profileAt_add_two {d k : ℕ} (p : Profile d k) (i : ℕ) :
    profileAt p (i + 2) = profileAt p i := by
  unfold profileAt
  have e : (i + 2) % 2 = i % 2 := by omega
  rw [e]

private theorem profileAt_adj {d k : ℕ} (p : Profile d k) (i : ℕ) (j : Fin k) :
    (profileAt p i j).val + (profileAt p (i + 1) j).val = d := by
  have hj := (p j).isLt
  by_cases h : i % 2 = 0
  · have h' : (i + 1) % 2 ≠ 0 := by omega
    simp only [profileAt, h, h', ite_true, ite_false, flip, Fin.val_rev]
    omega
  · have h' : (i + 1) % 2 = 0 := by omega
    simp only [profileAt, h, h', ite_true, ite_false, flip, Fin.val_rev]
    omega

private theorem low_edges {d n k : ℕ} {a : Grid d n k} (h : Low d a) (i : Fin n) (j : Fin k) :
    edge ((fun c => a (i.castSucc, c))) j + edge ((fun c => a (i.succ, c))) j = d := by
  simpa only [edge, block, Nat.add_assoc] using h i j

private def firstProfile {d n k : ℕ} (a : {a : Grid d (n + 1) k // Low d a}) : Profile d k :=
  fun j => ⟨edge ((fun c => a.1 (0, c))) j, by
    have h := low_edges a.2 0 j
    have e : (0 : Fin (n + 1)).castSucc = 0 := rfl
    rw [e] at h
    omega⟩

private theorem low_profiles {d n k : ℕ} (a : {a : Grid d (n + 1) k // Low d a})
    (i : Fin (n + 2)) (j : Fin k) :
    edge ((fun c => a.1 (i, c))) j = (profileAt (firstProfile a) i.val j).val := by
  induction i using Fin.induction with
  | zero => simp [firstProfile]
  | succ i ih =>
    have h := low_edges a.2 i j
    have h' := profileAt_adj (firstProfile a) i.val j
    have e1 : i.castSucc.val = i.val := rfl
    have e2 : i.succ.val = i.val + 1 := rfl
    rw [e1] at ih
    rw [e2]
    omega

private abbrev AltRows {d k : ℕ} (p : Profile d k) (h : ℕ) :=
  (i : Fin h) → Fiber (profileAt p i.val)

private def rowsToLow (d n k : ℕ) (s : Σ p : Profile d k, AltRows p (n + 2)) :
    {a : Grid d (n + 1) k // Low d a} :=
  ⟨fun (i, j) => (s.2 i).1 j, fun i j => by
    have h1 := (s.2 i.castSucc).2 j
    have h2 := (s.2 i.succ).2 j
    have h := profileAt_adj s.1 i.val j
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    simp only [block, edge] at *
    omega⟩

private theorem rowsToLow_first (d n k : ℕ) (s : Σ p : Profile d k, AltRows p (n + 2)) :
    firstProfile (rowsToLow d n k s) = s.1 := by
  funext j
  apply Fin.ext
  change edge ((s.2 0).1) j = (s.1 j).val
  simpa only [Fin.val_zero, profileAt_zero] using (s.2 0).2 j

private theorem rowsToLow_injective (d n k : ℕ) : Function.Injective (rowsToLow d n k) := by
  rintro ⟨p, f⟩ ⟨q, g⟩ h
  have hp := congrArg firstProfile h
  rw [rowsToLow_first, rowsToLow_first] at hp
  change p = q at hp
  subst q
  congr 1
  funext i
  apply Subtype.ext
  funext j
  exact congrFun (congrArg Subtype.val h) (i, j)

private theorem rowsToLow_surjective (d n k : ℕ) : Function.Surjective (rowsToLow d n k) := by
  intro a
  exact ⟨⟨firstProfile a, fun i => ⟨(fun c => a.1 (i, c)), low_profiles a i⟩⟩, Subtype.ext rfl⟩

private def lowEquiv (d n k : ℕ) :
    (Σ p : Profile d k, AltRows p (n + 2)) ≃ {a : Grid d (n + 1) k // Low d a} :=
  Equiv.ofBijective (rowsToLow d n k) ⟨rowsToLow_injective d n k, rowsToLow_surjective d n k⟩

private def b {d k : ℕ} (p : Profile d k) : ℕ := Nat.card (Fiber p)

private def profileCount {d k : ℕ} (p : Profile d k) (h : ℕ) : ℕ :=
  ∏ i : Fin h, b (profileAt p i.val)

private theorem card_altRows {d k : ℕ} (p : Profile d k) (h : ℕ) :
    Nat.card (AltRows p h) = profileCount p h := by
  rw [Nat.card_pi]
  rfl

/-- The low-array count is the sum of the alternating row-profile counts. -/
private theorem low_count (d n k : ℕ) :
    Nat.card {a : Grid d (n + 1) k // Low d a} =
      ∑ p : Profile d k, profileCount p (n + 2) := by
  rw [← Nat.card_congr (lowEquiv d n k), Nat.card_sigma]
  simp_rw [card_altRows]

/-- The initial cell uniquely determines a row with prescribed edge sums. -/
private theorem fiber_bound {d k : ℕ} (p : Profile d (k + 1)) :
    b p ≤ (p 0).val + 1 := by
  let f (r : Fiber p) : Fin ((p 0).val + 1) :=
    ⟨(r.1 0).val, by
      have h := r.2 0
      change (r.1 (0 : Fin (k + 1)).castSucc).val +
        (r.1 (0 : Fin (k + 1)).succ).val = (p 0).val at h
      have e : (0 : Fin (k + 1)).castSucc = 0 := rfl
      rw [e] at h
      omega⟩
  have hf : Function.Injective f := by
    intro r s h
    apply Subtype.ext
    funext i
    apply Fin.ext
    induction i using Fin.induction with
    | zero => exact congrArg (fun x : Fin ((p 0).val + 1) => x.val) h
    | succ i ih =>
      have h1 := r.2 i
      have h2 := s.2 i
      change (r.1 i.castSucc).val + (r.1 i.succ).val = (p i).val at h1
      change (s.1 i.castSucc).val + (s.1 i.succ).val = (p i).val at h2
      omega
  have hb := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fin] at hb

private theorem pair_bound {d k : ℕ} (p : Profile d (k + 1)) :
    b p + b (flip p) ≤ d + 2 := by
  have h1 := fiber_bound p
  have h2 := fiber_bound (flip p)
  have h3 := (p 0).isLt
  simp only [flip, Fin.val_rev] at h2
  omega

private theorem profileCount_two_step {d k : ℕ} (p : Profile d k) (h : ℕ) :
    profileCount p (h + 2) = b p * b (flip p) * profileCount p h := by
  unfold profileCount
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, profileAt_zero, profileAt_add_two]
  rw [profileAt_one]
  ring

private theorem profileCount_eq_pow {d k : ℕ} (p : Profile d k) (c : ℕ)
    (h1 : b p = c) (h2 : b (flip p) = c) (h : ℕ) :
    profileCount p h = c ^ h := by
  unfold profileCount
  have he (i : Fin h) : b (profileAt p i.val) = c := by
    unfold profileAt
    split <;> assumption
  simp_rw [he]
  simp

/-- Positive-index literal cardinality as a sum of shifted profile counts. -/
private theorem literal_sum (M d n k : ℕ) (hd : d < M) :
    C M (2 * M - d) (n + 1) (k + 1) =
      2 * ∑ p : Profile d (k + 1), profileCount p (n + 2) := by
  rw [count_eq M d (n + 1) (k + 1) hd (Nat.succ_pos _) (Nat.succ_pos _), low_count]

private def transpose {M n k : ℕ} (a : Grid M n k) : Grid M k n :=
  fun (i, j) => a (j, i)

private theorem transpose_low {M d n k : ℕ} (a : Grid M n k) :
    Low d (transpose a) ↔ Low d a := by
  constructor <;> intro h i j
  · have e := h j i
    simpa only [transpose, block, Nat.add_assoc, Nat.add_left_comm] using e
  · have e := h j i
    simpa only [transpose, block, Nat.add_assoc, Nat.add_left_comm] using e

private theorem C_transpose (M d n k : ℕ) (hd : d < M) (hn : 0 < n) (hk : 0 < k) :
    C M (2 * M - d) n k = C M (2 * M - d) k n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have e :
      {a : Grid d (n + 1) (k + 1) // Low d a} ≃
        {a : Grid d (k + 1) (n + 1) // Low d a} :=
    { toFun := fun a => ⟨transpose a.1, (transpose_low a.1).mpr a.2⟩
      invFun := fun a => ⟨transpose a.1, (transpose_low a.1).mpr a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [count_eq M d (n + 1) (k + 1) hd (Nat.succ_pos _) (Nat.succ_pos _),
    count_eq M d (k + 1) (n + 1) hd (Nat.succ_pos _) (Nat.succ_pos _), Nat.card_congr e]

/-- The polynomial for the descending lag list published in A235279. -/
private def P9 : ℤ[X] :=
  X ^ 9 - (Polynomial.C 1 * X ^ 8 + Polynomial.C 15 * X ^ 7 +
    Polynomial.C (-15) * X ^ 6 + Polynomial.C (-80) * X ^ 5 +
    Polynomial.C 80 * X ^ 4 + Polynomial.C 180 * X ^ 3 +
    Polynomial.C (-180) * X ^ 2 + Polynomial.C (-144) * X ^ 1 + Polynomial.C 144 * X ^ 0)

/-- The polynomial for the descending lag list published in A235304. -/
private def P14 : ℤ[X] :=
  X ^ 14 - (Polynomial.C 4 * X ^ 13 + Polynomial.C 25 * X ^ 12 +
    Polynomial.C (-112) * X ^ 11 + Polynomial.C (-231) * X ^ 10 +
    Polynomial.C 1260 * X ^ 9 + Polynomial.C 875 * X ^ 8 +
    Polynomial.C (-7280) * X ^ 7 + Polynomial.C (-224) * X ^ 6 +
    Polynomial.C 22736 * X ^ 5 + Polynomial.C (-7980) * X ^ 4 +
    Polynomial.C (-36288) * X ^ 3 + Polynomial.C 21456 * X ^ 2 +
    Polynomial.C 23040 * X ^ 1 + Polynomial.C (-17280) * X ^ 0)

private def linear (a : ℤ) : ℤ[X] := X - Polynomial.C a
private def quadratic (a : ℤ) : ℤ[X] := X ^ 2 - Polynomial.C a

private def factors9 : List ℤ[X] :=
  [linear 1, quadratic 2, quadratic 3, quadratic 4, quadratic 6]

private def factors14 : List ℤ[X] :=
  [linear 1, linear 3, quadratic 2, quadratic 3, quadratic 4, quadratic 5, quadratic 6, quadratic 8]

private theorem P9_factorization : P9 = factors9.prod := by
  simp only [P9, factors9, List.prod_cons, List.prod_nil, linear, quadratic, Polynomial.C_1,
    map_neg, Polynomial.C_ofNat]
  ring

private theorem P14_factorization : P14 = factors14.prod := by
  simp only [P14, factors14, List.prod_cons, List.prod_nil, linear, quadratic, Polynomial.C_1,
    map_neg, Polynomial.C_ofNat]
  ring

private def profileSequence {d k : ℕ} (p : Profile d k) : Sequence :=
  fun n => (profileCount p (n + 2) : ℤ)

private theorem profile_zero {d k : ℕ} (p : Profile d k) (h : b p * b (flip p) = 0) :
    profileSequence p = 0 := by
  funext n
  simp [profileSequence, profileCount_two_step p n, h]

private theorem profile_kills_linear {d k : ℕ} (p : Profile d k) (a : ℕ)
    (h₁ : b p = a) (h₂ : b (flip p) = a) : Kills (linear (a : ℤ)) (profileSequence p) := by
  rw [linear, ← pow_one (X : ℤ[X])]
  apply kills_step
  intro n
  change (profileCount p ((n + 2) + 1) : ℤ) = (a : ℤ) * (profileCount p (n + 2) : ℤ)
  rw [profileCount_eq_pow p a h₁ h₂, profileCount_eq_pow p a h₁ h₂, pow_succ]
  simp only [Nat.cast_mul]
  exact mul_comm _ _

private theorem profile_kills_quadratic {d k : ℕ} (p : Profile d k) (a : ℕ)
    (h : b p * b (flip p) = a) : Kills (quadratic (a : ℤ)) (profileSequence p) := by
  apply kills_step (d := 2)
  intro n
  change (profileCount p ((n + 2) + 2) : ℤ) = (a : ℤ) * (profileCount p (n + 2) : ℤ)
  rw [profileCount_two_step, h, Nat.cast_mul]

private theorem cases9 (a b : ℕ) (h : a + b ≤ 5) :
    a * b = 0 ∨ (a = 1 ∧ b = 1) ∨ a * b = 2 ∨ a * b = 3 ∨ a * b = 4 ∨ a * b = 6 := by
  have ha : a ≤ 5 := by omega
  have hb : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;> norm_num at *

private theorem cases14 (a b : ℕ) (h : a + b ≤ 6) :
    a * b = 0 ∨ (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 3) ∨
    a * b = 2 ∨ a * b = 3 ∨ a * b = 4 ∨ a * b = 5 ∨ a * b = 6 ∨ a * b = 8 := by
  have ha : a ≤ 6 := by omega
  have hb : b ≤ 6 := by omega
  interval_cases a <;> interval_cases b <;> norm_num at *

private theorem profile_annihilated9 {k : ℕ} (p : Profile 3 (k + 1)) : Kills P9 (profileSequence p) := by
  rw [P9_factorization]
  rcases cases9 _ _ (pair_bound p) with hz | ⟨h₁, h₂⟩ | h | h | h | h
  · rw [profile_zero p hz]
    exact kills_zero _
  · exact kills_of_dvd (List.dvd_prod (by simp [factors9])) (profile_kills_linear p 1 h₁ h₂)
  all_goals
    apply kills_of_dvd (List.dvd_prod ?_) (profile_kills_quadratic p _ h)
    simp [factors9]

private theorem profile_annihilated14 {k : ℕ} (p : Profile 4 (k + 1)) : Kills P14 (profileSequence p) := by
  rw [P14_factorization]
  rcases cases14 _ _ (pair_bound p) with hz | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | h | h | h | h | h | h
  · rw [profile_zero p hz]
    exact kills_zero _
  · exact kills_of_dvd (List.dvd_prod (by simp [factors14])) (profile_kills_linear p 1 h₁ h₂)
  · exact kills_of_dvd (List.dvd_prod (by simp [factors14])) (profile_kills_linear p 3 h₁ h₂)
  all_goals
    apply kills_of_dvd (List.dvd_prod ?_) (profile_kills_quadratic p _ h)
    simp [factors14]

private theorem literal_annihilated {M d : ℕ} (hd : d < M) {P : ℤ[X]} (k : ℕ)
    (h : ∀ p : Profile d (k + 1), Kills P (profileSequence p)) :
    Kills P (fun n => (C M (2 * M - d) (n + 1) (k + 1) : ℤ)) := by
  have e : (fun n => (C M (2 * M - d) (n + 1) (k + 1) : ℤ)) =
      (2 : ℤ) • (∑ p : Profile d (k + 1), profileSequence p) := by
    funext n
    rw [literal_sum M d n k hd, Nat.cast_mul, Nat.cast_sum, Pi.smul_apply, Finset.sum_apply]
    rfl
  rw [e]
  exact kills_smul _ (kills_sum _ h)

private theorem literal_annihilated9 (k : ℕ) :
    Kills P9 (fun n => (C 4 5 (n + 1) (k + 1) : ℤ)) :=
  literal_annihilated (M := 4) (d := 3) (by decide) k profile_annihilated9

private theorem literal_annihilated14 (k : ℕ) :
    Kills P14 (fun n => (C 5 6 (n + 1) (k + 1) : ℤ)) :=
  literal_annihilated (M := 5) (d := 4) (by decide) k profile_annihilated14

/-- The exact published lag equation is equivalent to polynomial annihilation. -/
private theorem kills_P9_iff (f : Sequence) :
    Kills P9 f ↔ ∀ n : ℕ, f (n + 9) =
      f (n + 8) + 15 * f (n + 7) - 15 * f (n + 6)
       - 80 * f (n + 5) + 80 * f (n + 4) + 180 * f (n + 3)
       - 180 * f (n + 2) - 144 * f (n + 1) + 144 * f n := by
  unfold Kills P9
  rw [funext_iff]
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply,
    Pi.add_apply, Pi.zero_apply, eval_C_mul_X_pow, map_pow, aeval_X, shift_pow_apply,
    Nat.add_zero, sub_eq_zero]
  constructor <;> intro h n <;> have hn := h n <;> linarith


/-- The exact published lag equation is equivalent to polynomial annihilation. -/
private theorem kills_P14_iff (f : Sequence) :
    Kills P14 f ↔ ∀ n : ℕ, f (n + 14) =
      4 * f (n + 13) + 25 * f (n + 12) - 112 * f (n + 11)
       - 231 * f (n + 10) + 1260 * f (n + 9) + 875 * f (n + 8)
       - 7280 * f (n + 7) - 224 * f (n + 6) + 22736 * f (n + 5)
       - 7980 * f (n + 4) - 36288 * f (n + 3) + 21456 * f (n + 2)
       + 23040 * f (n + 1) - 17280 * f n := by
  unfold Kills P14
  rw [funext_iff]
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply,
    Pi.add_apply, Pi.zero_apply, eval_C_mul_X_pow, map_pow, aeval_X, shift_pow_apply,
    Nat.add_zero, sub_eq_zero]
  constructor <;> intro h n <;> have hn := h n <;> linarith


private theorem a235280_first_axis (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (C 4 5 (n + 9) k : ℤ) =
      (C 4 5 (n + 8) k : ℤ) + 15 * (C 4 5 (n + 7) k : ℤ) - 15 * (C 4 5 (n + 6) k : ℤ)
       - 80 * (C 4 5 (n + 5) k : ℤ) + 80 * (C 4 5 (n + 4) k : ℤ) + 180 * (C 4 5 (n + 3) k : ℤ)
       - 180 * (C 4 5 (n + 2) k : ℤ) - 144 * (C 4 5 (n + 1) k : ℤ) + 144 * (C 4 5 n k : ℤ) := by
  cases n with
  | zero => omega
  | succ n =>
    cases k with
    | zero => omega
    | succ k => exact (kills_P9_iff _).mp (literal_annihilated9 k) n

/-- A235280 with the source coefficients, in both axes from the first positive-index window. -/
theorem a235280_all_rows_and_columns (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ((C 4 5 (n + 9) k : ℤ) =
      (C 4 5 (n + 8) k : ℤ) + 15 * (C 4 5 (n + 7) k : ℤ) - 15 * (C 4 5 (n + 6) k : ℤ)
       - 80 * (C 4 5 (n + 5) k : ℤ) + 80 * (C 4 5 (n + 4) k : ℤ) + 180 * (C 4 5 (n + 3) k : ℤ)
       - 180 * (C 4 5 (n + 2) k : ℤ) - 144 * (C 4 5 (n + 1) k : ℤ) + 144 * (C 4 5 n k : ℤ)) ∧
    ((C 4 5 n (k + 9) : ℤ) =
      (C 4 5 n (k + 8) : ℤ) + 15 * (C 4 5 n (k + 7) : ℤ) - 15 * (C 4 5 n (k + 6) : ℤ)
       - 80 * (C 4 5 n (k + 5) : ℤ) + 80 * (C 4 5 n (k + 4) : ℤ) + 180 * (C 4 5 n (k + 3) : ℤ)
       - 180 * (C 4 5 n (k + 2) : ℤ) - 144 * (C 4 5 n (k + 1) : ℤ) + 144 * (C 4 5 n k : ℤ)) := by
  refine ⟨a235280_first_axis n k hn hk, ?_⟩
  have h := a235280_first_axis k n hk hn
  have swap (j : ℕ) : C 4 5 (k + j) n = C 4 5 n (k + j) :=
    C_transpose 4 3 (k + j) n (by decide) (by omega) hn
  have swapBase : C 4 5 k n = C 4 5 n k := swap 0
  simp only [swap, swapBase] at h
  exact h

private theorem a235310_first_axis (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (C 5 6 (n + 14) k : ℤ) =
      4 * (C 5 6 (n + 13) k : ℤ) + 25 * (C 5 6 (n + 12) k : ℤ) - 112 * (C 5 6 (n + 11) k : ℤ)
       - 231 * (C 5 6 (n + 10) k : ℤ) + 1260 * (C 5 6 (n + 9) k : ℤ) + 875 * (C 5 6 (n + 8) k : ℤ)
       - 7280 * (C 5 6 (n + 7) k : ℤ) - 224 * (C 5 6 (n + 6) k : ℤ) + 22736 * (C 5 6 (n + 5) k : ℤ)
       - 7980 * (C 5 6 (n + 4) k : ℤ) - 36288 * (C 5 6 (n + 3) k : ℤ) + 21456 * (C 5 6 (n + 2) k : ℤ)
       + 23040 * (C 5 6 (n + 1) k : ℤ) - 17280 * (C 5 6 n k : ℤ) := by
  cases n with
  | zero => omega
  | succ n =>
    cases k with
    | zero => omega
    | succ k => exact (kills_P14_iff _).mp (literal_annihilated14 k) n

/-- A235310 with the source coefficients, in both axes from the first positive-index window. -/
theorem a235310_all_rows_and_columns (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ((C 5 6 (n + 14) k : ℤ) =
      4 * (C 5 6 (n + 13) k : ℤ) + 25 * (C 5 6 (n + 12) k : ℤ) - 112 * (C 5 6 (n + 11) k : ℤ)
       - 231 * (C 5 6 (n + 10) k : ℤ) + 1260 * (C 5 6 (n + 9) k : ℤ) + 875 * (C 5 6 (n + 8) k : ℤ)
       - 7280 * (C 5 6 (n + 7) k : ℤ) - 224 * (C 5 6 (n + 6) k : ℤ) + 22736 * (C 5 6 (n + 5) k : ℤ)
       - 7980 * (C 5 6 (n + 4) k : ℤ) - 36288 * (C 5 6 (n + 3) k : ℤ) + 21456 * (C 5 6 (n + 2) k : ℤ)
       + 23040 * (C 5 6 (n + 1) k : ℤ) - 17280 * (C 5 6 n k : ℤ)) ∧
    ((C 5 6 n (k + 14) : ℤ) =
      4 * (C 5 6 n (k + 13) : ℤ) + 25 * (C 5 6 n (k + 12) : ℤ) - 112 * (C 5 6 n (k + 11) : ℤ)
       - 231 * (C 5 6 n (k + 10) : ℤ) + 1260 * (C 5 6 n (k + 9) : ℤ) + 875 * (C 5 6 n (k + 8) : ℤ)
       - 7280 * (C 5 6 n (k + 7) : ℤ) - 224 * (C 5 6 n (k + 6) : ℤ) + 22736 * (C 5 6 n (k + 5) : ℤ)
       - 7980 * (C 5 6 n (k + 4) : ℤ) - 36288 * (C 5 6 n (k + 3) : ℤ) + 21456 * (C 5 6 n (k + 2) : ℤ)
       + 23040 * (C 5 6 n (k + 1) : ℤ) - 17280 * (C 5 6 n k : ℤ)) := by
  refine ⟨a235310_first_axis n k hn hk, ?_⟩
  have h := a235310_first_axis k n hk hn
  have swap (j : ℕ) : C 5 6 (k + j) n = C 5 6 n (k + j) :=
    C_transpose 5 4 (k + j) n (by decide) (by omega) hn
  have swapBase : C 5 6 k n = C 5 6 n k := swap 0
  simp only [swap, swapBase] at h
  exact h

/-- The monic characteristic polynomial from the signed A235317 lag list. -/
private def P18 : ℤ[X] :=
  X ^ 18 - (
      Polynomial.C 4 * X ^ 17 + Polynomial.C 47 * X ^ 16 + Polynomial.C (-200) * X ^ 15
      + Polynomial.C (-901) * X ^ 14 + Polynomial.C 4204 * X ^ 13 + Polynomial.C 8957 * X ^ 12
      + Polynomial.C (-48440) * X ^ 11 + Polynomial.C (-47194) * X ^ 10 + Polynomial.C 334096 * X ^ 9
      + Polynomial.C 101948 * X ^ 8 + Polynomial.C (-1410080) * X ^ 7 + Polynomial.C 170136 * X ^ 6
      + Polynomial.C 3549696 * X ^ 5 + Polynomial.C (-1446912) * X ^ 4 + Polynomial.C (-4861440) * X ^ 3
      + Polynomial.C 2954880 * X ^ 2 + Polynomial.C 2764800 * X ^ 1 + Polynomial.C (-2073600) * X ^ 0)

private def factors18 : List ℤ[X] :=
  factors14 ++ [quadratic 10, quadratic 12]

private theorem P18_factorization : P18 = factors18.prod := by
  rw [factors18, List.prod_append, ← P14_factorization]
  simp only [P18, P14, List.prod_cons, List.prod_nil, quadratic, map_neg, Polynomial.C_ofNat]
  ring

/-- Exhaust all ordered pairs of complementary fiber sizes with sum at most 7. -/
private theorem cases18 (a b : ℕ) (h : a + b ≤ 7) :
    a * b = 0 ∨ (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 3) ∨
    a * b = 2 ∨ a * b = 3 ∨ a * b = 4 ∨ a * b = 5 ∨
    a * b = 6 ∨ a * b = 8 ∨ a * b = 10 ∨ a * b = 12 := by
  have ha : a ≤ 7 := by omega
  have hb : b ≤ 7 := by omega
  interval_cases a <;> interval_cases b <;> norm_num at *

private theorem profile_annihilated18 {k : ℕ} (p : Profile 5 (k + 1)) :
    Kills P18 (profileSequence p) := by
  rw [P18_factorization]
  rcases cases18 _ _ (pair_bound p) with hz | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
    h | h | h | h | h | h | h | h
  · rw [profile_zero p hz]
    exact kills_zero _
  · exact kills_of_dvd (List.dvd_prod (by simp [factors18, factors14])) (profile_kills_linear p 1 h₁ h₂)
  · exact kills_of_dvd (List.dvd_prod (by simp [factors18, factors14])) (profile_kills_linear p 3 h₁ h₂)
  all_goals
    apply kills_of_dvd (List.dvd_prod ?_) (profile_kills_quadratic p _ h)
    simp [factors18, factors14]

private theorem kills_P18_iff (f : Sequence) :
    Kills P18 f ↔ ∀ n : ℕ, f (n + 18) =
      4 * f (n + 17) + 47 * f (n + 16) - 200 * f (n + 15)
      - 901 * f (n + 14) + 4204 * f (n + 13) + 8957 * f (n + 12)
      - 48440 * f (n + 11) - 47194 * f (n + 10) + 334096 * f (n + 9)
      + 101948 * f (n + 8) - 1410080 * f (n + 7) + 170136 * f (n + 6)
      + 3549696 * f (n + 5) - 1446912 * f (n + 4) - 4861440 * f (n + 3)
      + 2954880 * f (n + 2) + 2764800 * f (n + 1) - 2073600 * f n := by
  unfold Kills P18
  rw [funext_iff]
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply,
    Pi.add_apply, Pi.zero_apply, eval_C_mul_X_pow, map_pow, aeval_X, shift_pow_apply,
    Nat.add_zero, sub_eq_zero]
  constructor <;> intro h n <;> have hn := h n <;> linarith

private theorem a235319_first_axis (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (C 6 7 (n + 18) k : ℤ) =
      4 * (C 6 7 (n + 17) k : ℤ) + 47 * (C 6 7 (n + 16) k : ℤ) - 200 * (C 6 7 (n + 15) k : ℤ)
      - 901 * (C 6 7 (n + 14) k : ℤ) + 4204 * (C 6 7 (n + 13) k : ℤ) + 8957 * (C 6 7 (n + 12) k : ℤ)
      - 48440 * (C 6 7 (n + 11) k : ℤ) - 47194 * (C 6 7 (n + 10) k : ℤ) + 334096 * (C 6 7 (n + 9) k : ℤ)
      + 101948 * (C 6 7 (n + 8) k : ℤ) - 1410080 * (C 6 7 (n + 7) k : ℤ) + 170136 * (C 6 7 (n + 6) k : ℤ)
      + 3549696 * (C 6 7 (n + 5) k : ℤ) - 1446912 * (C 6 7 (n + 4) k : ℤ) - 4861440 * (C 6 7 (n + 3) k : ℤ)
      + 2954880 * (C 6 7 (n + 2) k : ℤ) + 2764800 * (C 6 7 (n + 1) k : ℤ) - 2073600 * (C 6 7 n k : ℤ) := by
  cases n with
  | zero => omega
  | succ n =>
    cases k with
    | zero => omega
    | succ k =>
      exact (kills_P18_iff _).mp
        (literal_annihilated (M := 6) (d := 5) (by decide) k profile_annihilated18) n

/-- A235319 with the source coefficients, in both axes from the first positive-index window. -/
theorem a235319_all_rows_and_columns (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ((C 6 7 (n + 18) k : ℤ) =
      4 * (C 6 7 (n + 17) k : ℤ) + 47 * (C 6 7 (n + 16) k : ℤ) - 200 * (C 6 7 (n + 15) k : ℤ)
      - 901 * (C 6 7 (n + 14) k : ℤ) + 4204 * (C 6 7 (n + 13) k : ℤ) + 8957 * (C 6 7 (n + 12) k : ℤ)
      - 48440 * (C 6 7 (n + 11) k : ℤ) - 47194 * (C 6 7 (n + 10) k : ℤ) + 334096 * (C 6 7 (n + 9) k : ℤ)
      + 101948 * (C 6 7 (n + 8) k : ℤ) - 1410080 * (C 6 7 (n + 7) k : ℤ) + 170136 * (C 6 7 (n + 6) k : ℤ)
      + 3549696 * (C 6 7 (n + 5) k : ℤ) - 1446912 * (C 6 7 (n + 4) k : ℤ) - 4861440 * (C 6 7 (n + 3) k : ℤ)
      + 2954880 * (C 6 7 (n + 2) k : ℤ) + 2764800 * (C 6 7 (n + 1) k : ℤ) - 2073600 * (C 6 7 n k : ℤ)) ∧
    ((C 6 7 n (k + 18) : ℤ) =
      4 * (C 6 7 n (k + 17) : ℤ) + 47 * (C 6 7 n (k + 16) : ℤ) - 200 * (C 6 7 n (k + 15) : ℤ)
      - 901 * (C 6 7 n (k + 14) : ℤ) + 4204 * (C 6 7 n (k + 13) : ℤ) + 8957 * (C 6 7 n (k + 12) : ℤ)
      - 48440 * (C 6 7 n (k + 11) : ℤ) - 47194 * (C 6 7 n (k + 10) : ℤ) + 334096 * (C 6 7 n (k + 9) : ℤ)
      + 101948 * (C 6 7 n (k + 8) : ℤ) - 1410080 * (C 6 7 n (k + 7) : ℤ) + 170136 * (C 6 7 n (k + 6) : ℤ)
      + 3549696 * (C 6 7 n (k + 5) : ℤ) - 1446912 * (C 6 7 n (k + 4) : ℤ) - 4861440 * (C 6 7 n (k + 3) : ℤ)
      + 2954880 * (C 6 7 n (k + 2) : ℤ) + 2764800 * (C 6 7 n (k + 1) : ℤ) - 2073600 * (C 6 7 n k : ℤ)) := by
  refine ⟨a235319_first_axis n k hn hk, ?_⟩
  have h := a235319_first_axis k n hk hn
  have swap (j : ℕ) : C 6 7 (k + j) n = C 6 7 n (k + j) :=
    C_transpose 6 5 (k + j) n (by decide) (by omega) hn
  have swapBase : C 6 7 k n = C 6 7 n k := swap 0
  simpa only [swap, swapBase] using h

end

end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
