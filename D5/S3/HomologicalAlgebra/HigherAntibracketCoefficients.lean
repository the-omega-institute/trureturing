/- GID: D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/HigherAntibracketCoefficients
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Manetti-Ricciardi's closed form for the higher-antibracket coefficients c_i^n holds. -/

/-
proof_shape: result: content (the coordinate calculus of ρ_k on End(ℚ[x]), the binomial expansion
  of ρ_1^t on lattice points, the evaluation of every row by the alternating binomial identity,
  and uniqueness by triangularity)
escape_witness: result (form (2) of §3.2: the public conclusion itself is produced by the row
  evaluations and the uniqueness argument; no step instantiates an existing statement)
admission_basis: open-problem-resolution (issue #12104; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.HomologicalAlgebra.HigherAntibracketCoefficients

open Polynomial Finset

/-- `Φ^{m,i}`: the linear endomorphism of `ℚ[x]` sending `x^i` to `x^{m-i}/(m-i)!` and every
other monomial to `0`. -/
noncomputable def phi (m i : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (lcoeff ℚ i).smulRight ((1 / ((m - i).factorial : ℚ)) • (X : ℚ[X]) ^ (m - i))

/-- The higher Koszul bracket `Φ^m = ∑_{i=1}^m (-1)^{m-i} Φ^{m,i}`. -/
noncomputable def koszul (m : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  ∑ i ∈ Icc 1 m, ((-1 : ℚ) ^ (m - i)) • phi m i

/-- `ρ_k(Ψ) = (x^k/k! − x^{k+1}∂/(k+1)!) ∘ Ψ − Ψ ∘ (x ∂^{k+1}/(k+1)!)`. -/
noncomputable def rho (k : ℕ) (Ψ : ℚ[X] →ₗ[ℚ] ℚ[X]) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  ((1 / (k.factorial : ℚ)) • LinearMap.mulLeft ℚ ((X : ℚ[X]) ^ k) -
      (1 / ((k + 1).factorial : ℚ)) •
        (LinearMap.mulLeft ℚ ((X : ℚ[X]) ^ (k + 1)) ∘ₗ derivative)) ∘ₗ Ψ -
    Ψ ∘ₗ ((1 / ((k + 1).factorial : ℚ)) •
      (LinearMap.mulLeft ℚ (X : ℚ[X]) ∘ₗ derivative ^ (k + 1)))

/-- The coefficient conjectured by Manetti and Ricciardi (arXiv:1509.09032, Conjecture 2.4). -/
def formula (n i : ℕ) : ℚ :=
  (-1) ^ n * (∏ j ∈ Icc 2 i, (((n : ℚ) * ((n : ℚ) - 1) - ((j : ℚ) - 1) * ((j : ℚ) - 2)) / 2)) /
    ∑ h ∈ Icc 2 n, (h : ℚ) *
      (∏ j ∈ Icc 2 h, (((n : ℚ) * ((n : ℚ) - 1) - ((j : ℚ) - 1) * ((j : ℚ) - 2)) / 2)) *
      ∏ j ∈ Icc h (n - 1), ((1 - (j : ℚ)) * ((j : ℚ) + 2)) / 2

/-! ### Coordinates -/

/-- The coordinate of `Ψ` at the lattice point `(d, s)`: `d!` times the coefficient of `x^d` in
`Ψ(x^s)`. -/
private noncomputable def coord (Ψ : ℚ[X] →ₗ[ℚ] ℚ[X]) (d s : ℕ) : ℚ :=
  (d.factorial : ℚ) * (Ψ (X ^ s)).coeff d

private theorem eq_of_coord (Ψ Ψ' : ℚ[X] →ₗ[ℚ] ℚ[X]) (h : ∀ d s, coord Ψ d s = coord Ψ' d s) :
    Ψ = Ψ' := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, ← X_pow_eq_monomial]
  ext d
  have := h d n
  unfold coord at this
  have hd : (d.factorial : ℚ) ≠ 0 := by positivity
  exact mul_left_cancel₀ hd this

private theorem coord_add (Ψ Ψ' : ℚ[X] →ₗ[ℚ] ℚ[X]) (d s : ℕ) :
    coord (Ψ + Ψ') d s = coord Ψ d s + coord Ψ' d s := by
  simp [coord, mul_add]

private theorem coord_smul (a : ℚ) (Ψ : ℚ[X] →ₗ[ℚ] ℚ[X]) (d s : ℕ) :
    coord (a • Ψ) d s = a * coord Ψ d s := by
  simp [coord]; ring

private theorem coord_sum (t : Finset ℕ) (f : ℕ → ℚ[X] →ₗ[ℚ] ℚ[X]) (d s : ℕ) :
    coord (∑ i ∈ t, f i) d s = ∑ i ∈ t, coord (f i) d s := by
  simp [coord, LinearMap.sum_apply, finsetSum_coeff, mul_sum]

private theorem coord_phi (m i d s : ℕ) :
    coord (phi m i) d s = if s = i ∧ d = m - i then 1 else 0 := by
  simp only [coord, phi, LinearMap.smulRight_apply, lcoeff_apply, coeff_X_pow]
  by_cases hs : s = i
  · subst hs
    simp only [if_true, coeff_smul, coeff_X_pow, smul_eq_mul, true_and]
    by_cases hd : d = m - s
    · subst hd; simp [Nat.factorial_ne_zero]
    · simp [hd]
  · simp [hs, Ne.symm hs]

private theorem rho_apply_X_pow (k : ℕ) (Ψ : ℚ[X] →ₗ[ℚ] ℚ[X]) (s : ℕ) :
    rho k Ψ (X ^ s) = (1 / (k.factorial : ℚ)) • (X ^ k * Ψ (X ^ s)) -
      (1 / ((k + 1).factorial : ℚ)) • (X ^ (k + 1) * derivative (Ψ (X ^ s))) -
      ((1 / ((k + 1).factorial : ℚ)) * (s.descFactorial (k + 1) : ℚ)) • Ψ (X ^ (s - k)) := by
  have hpow : (derivative ^ (k + 1) : ℚ[X] →ₗ[ℚ] ℚ[X]) (X ^ s) =
      (s.descFactorial (k + 1) : ℚ) • X ^ (s - (k + 1)) := by
    rw [Module.End.pow_apply]; exact iterate_derivative_X_pow_eq_smul s (k + 1)
  have hX : (s.descFactorial (k + 1) : ℚ) • Ψ ((X : ℚ[X]) * X ^ (s - (k + 1))) =
      (s.descFactorial (k + 1) : ℚ) • Ψ (X ^ (s - k)) := by
    rcases Nat.lt_or_ge s (k + 1) with hlt | hge
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]; simp
    · rw [← pow_succ']; congr 3; omega
  simp only [rho, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.mulLeft_apply, hpow, map_smul]
  rw [hX, smul_smul]

private theorem coord_rho (k : ℕ) (Ψ : ℚ[X] →ₗ[ℚ] ℚ[X]) (d s : ℕ) :
    coord (rho k Ψ) d s =
      (if k ≤ d then ((d.choose k : ℚ) - d.choose (k + 1)) * coord Ψ (d - k) s else 0) -
        (s.choose (k + 1) : ℚ) * coord Ψ d (s - k) := by
  rw [coord, rho_apply_X_pow]
  simp only [coeff_sub, coeff_smul, smul_eq_mul, coeff_X_pow_mul', coeff_derivative, coord]
  set a := (Ψ (X ^ s)).coeff (d - k)
  set b := (Ψ (X ^ (s - k))).coeff d
  have hk : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  have hk' : (k.factorial : ℚ) ≠ 0 := by positivity
  have e3 : (d.factorial : ℚ) * (1 / ((k + 1).factorial : ℚ) * (s.descFactorial (k + 1) : ℚ)) =
      (s.choose (k + 1) : ℚ) * d.factorial := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; field_simp
  by_cases hkd : k ≤ d
  · have e1 : (d.factorial : ℚ) * (1 / (k.factorial : ℚ)) =
        (d.choose k : ℚ) * (d - k).factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hkd]; push_cast; field_simp
    by_cases hk1 : k + 1 ≤ d
    · have hsub : d - (k + 1) + 1 = d - k := by omega
      have e2 : (d.factorial : ℚ) * (1 / ((k + 1).factorial : ℚ)) * (((d - (k + 1) : ℕ) : ℚ) + 1) =
          (d.choose (k + 1) : ℚ) * (d - k).factorial := by
        rw [← Nat.choose_mul_factorial_mul_factorial hk1, show d - k = (d - (k + 1)) + 1 by omega,
          Nat.factorial_succ (d - (k + 1))]
        push_cast; field_simp
      simp only [hkd, hk1, if_true, hsub]
      linear_combination a * e1 - a * e2 - b * e3
    · have hdk : d = k := by omega
      subst hdk
      simp only [le_refl, if_true, hk1, if_false, Nat.sub_self, Nat.choose_self,
        Nat.choose_succ_self, Nat.factorial_zero]
      have e1' : (d.factorial : ℚ) * (1 / (d.factorial : ℚ)) = 1 := by field_simp
      push_cast
      linear_combination a * e1' - b * e3
  · simp only [hkd, if_false, show ¬ (k + 1 ≤ d) by omega]
    linear_combination (-b) * e3

/-! ### The lattice model -/

/-- `ρ_k` in coordinates. -/
private def R (k : ℕ) (a : ℕ → ℕ → ℚ) (d s : ℕ) : ℚ :=
  (if k ≤ d then ((d.choose k : ℚ) - d.choose (k + 1)) * a (d - k) s else 0) -
    (s.choose (k + 1) : ℚ) * a d (s - k)

private theorem coord_rho' (k : ℕ) (Ψ : ℚ[X] →ₗ[ℚ] ℚ[X]) : coord (rho k Ψ) = R k (coord Ψ) := by
  funext d s; exact coord_rho k Ψ d s

private theorem coord_iterate (t : ℕ) (Ψ : ℚ[X] →ₗ[ℚ] ℚ[X]) :
    coord ((rho 1)^[t] Ψ) = (R 1)^[t] (coord Ψ) := by
  induction t generalizing Ψ with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, coord_rho']

private theorem R_sub (k : ℕ) (a b : ℕ → ℕ → ℚ) : R k (a - b) = R k a - R k b := by
  funext d s; simp only [R, Pi.sub_apply]; split_ifs <;> ring

private theorem R_iterate_sub (t : ℕ) (a b : ℕ → ℕ → ℚ) :
    (R 1)^[t] (a - b) = (R 1)^[t] a - (R 1)^[t] b := by
  induction t generalizing a b with
  | zero => rfl
  | succ t ih => simp only [Function.iterate_succ_apply, R_sub, ih]

/-- The weight of a `d`-step of `ρ_1` from `u` to `u + 1`. -/
private def α (u : ℕ) : ℚ := ((u + 1).choose 1 : ℚ) - (u + 1).choose 2

/-- The weight of an `s`-step of `ρ_1` from `u` to `u + 1`. -/
private def β (u : ℕ) : ℚ := -((u + 1).choose 2 : ℚ)

private def Ap (a b : ℕ) : ℚ := ∏ u ∈ Ico a b, α u
private def Bp (a b : ℕ) : ℚ := ∏ u ∈ Ico a b, β u

private def δ (d₀ s₀ : ℕ) (d s : ℕ) : ℚ := if d = d₀ ∧ s = s₀ then 1 else 0

private theorem Ap_succ {a b : ℕ} (h : a ≤ b) : Ap a (b + 1) = Ap a b * α b := by
  simp only [Ap]; rw [Finset.prod_Ico_succ_top h]

private theorem Bp_succ {a b : ℕ} (h : a ≤ b) : Bp a (b + 1) = Bp a b * β b := by
  simp only [Bp]; rw [Finset.prod_Ico_succ_top h]

/-- `ρ_1^t` applied to a single lattice point. -/
private theorem R_iterate_δ (t d₀ s₀ d s : ℕ) (hs₀ : 1 ≤ s₀) :
    (R 1)^[t] (δ d₀ s₀) d s =
      if d₀ ≤ d ∧ s₀ ≤ s ∧ (d - d₀) + (s - s₀) = t then
        (t.choose (d - d₀) : ℚ) * Ap d₀ d * Bp s₀ s else 0 := by
  induction t generalizing d s with
  | zero =>
    simp only [Function.iterate_zero, id, δ]
    by_cases h : d = d₀ ∧ s = s₀
    · obtain ⟨rfl, rfl⟩ := h; simp [Ap, Bp]
    · rw [if_neg h, if_neg]; omega
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simp only [R, ih]
    have hw : ((d.choose 1 : ℚ) - d.choose 2) = α (d - 1) ∨ d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact Or.inr h
      · left; simp only [α]; rw [Nat.sub_add_cancel h]
    have hβ : -((s.choose 2 : ℚ)) = β (s - 1) ∨ s = 0 := by
      rcases Nat.eq_zero_or_pos s with h | h
      · exact Or.inr h
      · left; simp only [β]; rw [Nat.sub_add_cancel h]
    by_cases hd : d₀ + 1 ≤ d
    · have hd1 : 1 ≤ d := by omega
      rcases hw with hw | hw
      · by_cases hs : s₀ + 1 ≤ s
        · rcases hβ with hβ | hβ
          · have e1 := Ap_succ (show d₀ ≤ d - 1 by omega)
            have e2 := Bp_succ (show s₀ ≤ s - 1 by omega)
            rw [show d - 1 + 1 = d by omega] at e1
            rw [show s - 1 + 1 = s by omega] at e2
            simp only [hd1, if_true, show d₀ ≤ d - 1 by omega, show d₀ ≤ d by omega,
              show s₀ ≤ s by omega, show s₀ ≤ s - 1 by omega, true_and]
            by_cases ht : d - d₀ + (s - s₀) = t + 1
            · rw [if_pos (by omega), if_pos (by omega), if_pos ht]
              rw [show d - d₀ = (d - 1 - d₀) + 1 by omega, Nat.choose_succ_succ', e1, e2, hw]
              have : s.choose 2 = - β (s - 1) := by rw [← hβ]; ring
              push_cast; rw [this]; ring
            · rw [if_neg (by omega), if_neg (by omega), if_neg ht]; ring
          · omega
        · have hss : s = s₀ ∨ s < s₀ := by omega
          have e1 := Ap_succ (show d₀ ≤ d - 1 by omega)
          rw [show d - 1 + 1 = d by omega] at e1
          simp only [hd1, if_true, show d₀ ≤ d - 1 by omega, show d₀ ≤ d by omega, true_and]
          rcases hss with hss | hlt
          · subst hss
            rw [if_neg (show ¬ (s ≤ s - 1 ∧ _) by omega)]
            by_cases ht : d - d₀ + (s - s) = t + 1
            · rw [if_pos ⟨le_refl _, by omega⟩, if_pos ⟨le_refl _, ht⟩]
              rw [show d - d₀ = (d - 1 - d₀) + 1 by omega, e1, hw]
              rw [show d - 1 - d₀ = t by omega]
              simp only [Nat.choose_self, Nat.cast_one]
              ring
            · rw [if_neg (by omega), if_neg (by omega)]; ring
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
      · omega
    · -- `d = d₀` or `d < d₀`: only the `s`-step contributes
      have hfirst : (if 1 ≤ d then ((d.choose 1 : ℚ) - d.choose 2) *
          (if d₀ ≤ d - 1 ∧ s₀ ≤ s ∧ d - 1 - d₀ + (s - s₀) = t then
            (t.choose (d - 1 - d₀) : ℚ) * Ap d₀ (d - 1) * Bp s₀ s else 0) else 0) = 0 := by
        split_ifs with h1 h2 <;> first | rfl | (exfalso; omega) | ring
      rw [hfirst, zero_sub]
      by_cases hdd : d = d₀
      · subst hdd
        by_cases hs : s₀ + 1 ≤ s
        · rcases hβ with hβ | hβ
          · have e2 := Bp_succ (show s₀ ≤ s - 1 by omega)
            rw [show s - 1 + 1 = s by omega] at e2
            simp only [le_refl, true_and, show s₀ ≤ s - 1 by omega, show s₀ ≤ s by omega,
              Nat.sub_self, zero_add]
            by_cases ht : s - s₀ = t + 1
            · rw [if_pos (by omega), if_pos ht, e2]
              have : s.choose 2 = - β (s - 1) := by rw [← hβ]; ring
              push_cast; rw [this]; simp; ring
            · rw [if_neg (by omega), if_neg ht]; ring
          · omega
        · rw [if_neg (by omega), if_neg (by omega)]; ring
      · rw [if_neg (by omega), if_neg (by omega)]; ring

private theorem coord_koszul (m d s : ℕ) :
    coord (koszul m) d s = if 1 ≤ s ∧ s ≤ m ∧ d + s = m then (-1 : ℚ) ^ (m - s) else 0 := by
  simp only [koszul, coord_sum, coord_smul, coord_phi, mul_ite, mul_one, mul_zero]
  by_cases h : 1 ≤ s ∧ s ≤ m ∧ d + s = m
  · rw [if_pos h, Finset.sum_eq_single s]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro i _ hi; rw [if_neg]; omega
    · intro hs; exact absurd (Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩) hs
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi; rw [Finset.mem_Icc] at hi; rw [if_neg]; omega

private theorem coord_koszul_one : coord (koszul 1) = δ 0 1 := by
  funext d s; rw [coord_koszul, δ]
  by_cases h : d = 0 ∧ s = 1
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h, if_neg]; omega

private theorem R_δ01 (i : ℕ) (hi : 1 ≤ i) : R i (δ 0 1) = δ i 1 - δ 0 (i + 1) := by
  funext d s
  simp only [R, δ, Pi.sub_apply]
  by_cases h1 : d = i ∧ s = 1
  · obtain ⟨rfl, rfl⟩ := h1
    rw [if_pos le_rfl, if_pos (show d - d = 0 ∧ 1 = 1 from ⟨Nat.sub_self d, rfl⟩),
      if_neg (show ¬ (d = 0 ∧ 1 - d = 1) by omega), if_pos (show d = d ∧ 1 = 1 from ⟨rfl, rfl⟩),
      if_neg (show ¬ (d = 0 ∧ 1 = d + 1) by omega), Nat.choose_self,
      Nat.choose_eq_zero_of_lt (show d < d + 1 by omega)]
    simp
  · by_cases h2 : d = 0 ∧ s = i + 1
    · obtain ⟨rfl, rfl⟩ := h2
      rw [if_neg (show ¬ i ≤ 0 by omega), if_pos (show 0 = 0 ∧ i + 1 - i = 1 by omega),
        if_neg (show ¬ (0 = i ∧ i + 1 = 1) by omega),
        if_pos (show 0 = 0 ∧ i + 1 = i + 1 from ⟨rfl, rfl⟩), Nat.choose_self]
      simp
    · rw [if_neg h1, if_neg h2, if_neg (show ¬ (d = 0 ∧ s - i = 1) by omega)]
      have e1 : (if i ≤ d then ((d.choose i : ℚ) - d.choose (i + 1)) *
          (if d - i = 0 ∧ s = 1 then 1 else 0) else 0) = 0 := by
        by_cases a : i ≤ d
        · rw [if_pos a, if_neg (show ¬ (d - i = 0 ∧ s = 1) by omega)]; simp
        · rw [if_neg a]
      rw [e1]; simp

/-- The coordinate of `ρ_1^{n-i} ρ_i Φ^1` at the lattice point `(d, n + 1 - d)`. -/
private def g (n i d : ℕ) : ℚ :=
  (if i ≤ d then ((n - i).choose (d - i) : ℚ) * Ap i d * Bp 1 (n + 1 - d) else 0) -
    ((n - i).choose d : ℚ) * Ap 0 d * Bp (i + 1) (n + 1 - d)

private theorem G_eq (n i d s : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ((R 1)^[n - i] (δ i 1) - (R 1)^[n - i] (δ 0 (i + 1))) d s =
      if 1 ≤ s ∧ d + s = n + 1 then g n i d else 0 := by
  rw [Pi.sub_apply, Pi.sub_apply, R_iterate_δ _ _ _ _ _ le_rfl, R_iterate_δ _ _ _ _ _ (by omega)]
  by_cases h : 1 ≤ s ∧ d + s = n + 1
  · rw [if_pos h, g, show n + 1 - d = s by omega]
    congr 1
    · by_cases hid : i ≤ d
      · rw [if_pos ⟨hid, h.1, by omega⟩, if_pos hid]
      · rw [if_neg (by omega), if_neg hid]
    · by_cases hdi : d ≤ n - i
      · rw [if_pos ⟨Nat.zero_le _, by omega, by omega⟩, Nat.sub_zero]
      · rw [if_neg (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · rw [if_neg h, if_neg (by omega), if_neg (by omega)]; simp

/-- The operator identity of Theorem 6.4 is equivalent to the `n + 1` row equations. -/
private theorem identity_iff_rows (n : ℕ) (c : ℕ → ℚ) :
    koszul (n + 1) = ∑ i ∈ Icc 1 n, c i • (rho 1)^[n - i] (rho i (koszul 1)) ↔
      ∀ d ≤ n, ∑ i ∈ Icc 1 n, c i * g n i d = (-1) ^ d := by
  have hcoord : ∀ d s, coord (∑ i ∈ Icc 1 n, c i • (rho 1)^[n - i] (rho i (koszul 1))) d s =
      if 1 ≤ s ∧ d + s = n + 1 then ∑ i ∈ Icc 1 n, c i * g n i d else 0 := by
    intro d s
    rw [coord_sum]
    have : ∀ i ∈ Icc 1 n, coord (c i • (rho 1)^[n - i] (rho i (koszul 1))) d s =
        c i * (if 1 ≤ s ∧ d + s = n + 1 then g n i d else 0) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [coord_smul, coord_iterate, coord_rho', coord_koszul_one, R_δ01 i hi.1,
        R_iterate_sub, G_eq n i d s hi.1 hi.2]
    rw [Finset.sum_congr rfl this]
    split_ifs <;> simp
  constructor
  · intro h d hd
    have := congrArg (fun Ψ => coord Ψ d (n + 1 - d)) h
    rw [coord_koszul, hcoord, if_pos (by omega), if_pos (by omega)] at this
    rw [← this, show n + 1 - (n + 1 - d) = d by omega]
  · intro h
    apply eq_of_coord
    intro d s
    rw [coord_koszul, hcoord]
    by_cases hs : 1 ≤ s ∧ d + s = n + 1
    · rw [if_pos ⟨hs.1, by omega, hs.2⟩, if_pos hs, h d (by omega),
        show n + 1 - s = d by omega]
    · rw [if_neg (by omega), if_neg hs]

/-! ### Binomial sums and closed forms -/

open fwdDiff in
/-- `Σ_i (-1)^{M-i} C(M,i) C(i+a,b) = C(a, b-M)` for `M ≤ b`, and `0` for `M > b`. -/
private theorem alt_sum_choose (M a b : ℕ) :
    ∑ i ∈ range (M + 1), (-1 : ℚ) ^ (M - i) * (M.choose i : ℚ) * ((i + a).choose b : ℚ) =
      if M ≤ b then (a.choose (b - M) : ℚ) else 0 := by
  have key : ∀ M b, Δ_[1]^[M] (fun i : ℕ => ((i + a).choose b : ℚ)) =
      if M ≤ b then (fun i : ℕ => ((i + a).choose (b - M) : ℚ)) else 0 := by
    intro M
    induction M with
    | zero => intro b; simp
    | succ M ih =>
      intro b
      rw [Function.iterate_succ_apply]
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · have h0 : Δ_[1] (fun i : ℕ => ((i + a).choose 0 : ℚ)) = 0 := by
          funext i; simp [fwdDiff]
        rw [h0, if_neg (by omega)]
        clear ih
        induction M with
        | zero => rfl
        | succ M ihM =>
          rw [Function.iterate_succ_apply]; convert ihM using 2; funext i; simp [fwdDiff]
      · have h1 : Δ_[1] (fun i : ℕ => ((i + a).choose b : ℚ)) =
            fun i : ℕ => ((i + a).choose (b - 1) : ℚ) := by
          funext i
          obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
          simp only [fwdDiff, show i + 1 + a = (i + a) + 1 by ring, Nat.choose_succ_succ',
            Nat.add_sub_cancel]
          push_cast; ring
        rw [h1, ih (b - 1)]
        by_cases hM : M ≤ b - 1
        · rw [if_pos hM, if_pos (by omega), show b - 1 - M = b - (M + 1) by omega]
        · rw [if_neg hM, if_neg (by omega)]
  have := congrFun (key M b) 0
  rw [fwdDiff_iter_eq_sum_shift] at this
  have hrhs : (if M ≤ b then (fun i : ℕ => ((i + a).choose (b - M) : ℚ)) else 0) 0 =
      if M ≤ b then (a.choose (b - M) : ℚ) else 0 := by split_ifs <;> simp
  rw [hrhs] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro i _
  simp [zsmul_eq_mul]

private theorem α_zero : α 0 = 1 := by simp [α]
private theorem α_one : α 1 = 1 := by norm_num [α]
private theorem α_two : α 2 = 0 := by norm_num [α, Nat.choose]
private theorem α_ge (u : ℕ) : α u = -((u : ℚ) + 1) * ((u : ℚ) - 2) / 2 := by
  simp only [α, Nat.choose_one_right, Nat.cast_choose_two]; push_cast; ring

private theorem β_eq (u : ℕ) : β u = -((u : ℚ) + 1) * (u : ℚ) / 2 := by
  simp only [β, Nat.cast_choose_two]; push_cast; ring

private theorem Ap_self (a : ℕ) : Ap a a = 1 := by simp [Ap]
private theorem Bp_self (a : ℕ) : Bp a a = 1 := by simp [Bp]

/-- `Ap i d = 0` once the path crosses `u = 2`. -/
private theorem Ap_zero {i d : ℕ} (hi : i ≤ 2) (hd : 3 ≤ d) : Ap i d = 0 := by
  apply Finset.prod_eq_zero (i := 2) (by simp [Finset.mem_Ico]; omega) α_two

private theorem Bp_closed (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Bp a b = (-1) ^ (b - a) * (((b - 1).factorial * b.factorial : ℕ) : ℚ) /
      ((((a - 1).factorial * a.factorial : ℕ) : ℚ) * 2 ^ (b - a)) := by
  induction b, hab using Nat.le_induction with
  | base => rw [Bp_self, Nat.sub_self]; field_simp
  | succ b hab ih =>
    rw [Bp_succ hab, ih, β_eq, show b + 1 - a = (b - a) + 1 by omega,
      show b + 1 - 1 = (b - 1) + 1 by omega, Nat.factorial_succ (b - 1), Nat.factorial_succ b]
    have hb : ((b - 1 : ℕ) : ℚ) + 1 = b := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast
    rw [hb]
    field_simp
    ring

private theorem Ap_closed (i d : ℕ) (hi : 3 ≤ i) (hid : i ≤ d) :
    Ap i d = (-1) ^ (d - i) * ((d.factorial * (d - 3).factorial : ℕ) : ℚ) /
      (((i.factorial * (i - 3).factorial : ℕ) : ℚ) * 2 ^ (d - i)) := by
  induction d, hid using Nat.le_induction with
  | base => rw [Ap_self, Nat.sub_self]; field_simp
  | succ d hid ih =>
    rw [Ap_succ hid, ih, α_ge, show d + 1 - i = (d - i) + 1 by omega,
      show d + 1 - 3 = (d - 3) + 1 by omega, Nat.factorial_succ (d - 3), Nat.factorial_succ d]
    have hd : ((d - 3 : ℕ) : ℚ) + 1 = (d : ℚ) - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast
    rw [hd]
    field_simp
    ring

/-- `P n i = (n+i-2)! / ((n-i)! 2^{i-1})`, the numerator of the conjectured formula. -/
private def P (n i : ℕ) : ℚ := ((n + i - 2).factorial : ℚ) / ((n - i).factorial * 2 ^ (i - 1))

private theorem num_eq (n i : ℕ) (hn : 2 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∏ j ∈ Icc 2 i, (((n : ℚ) * ((n : ℚ) - 1) - ((j : ℚ) - 1) * ((j : ℚ) - 2)) / 2) = P n i := by
  induction i, hi using Nat.le_induction with
  | base =>
    simp only [P, show n + 1 - 2 = n - 1 by omega, Nat.sub_self, pow_zero, mul_one]
    rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty, div_self (by positivity)]
  | succ i hi ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih (by omega)]
    simp only [P, show n + (i + 1) - 2 = (n + i - 2) + 1 by omega, Nat.factorial_succ,
      show n - i = (n - (i + 1)) + 1 by omega, show i + 1 - 1 = (i - 1) + 1 by omega, pow_succ]
    have h1 : ((n + i - 2 : ℕ) : ℚ) + 1 = (n : ℚ) + i - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h2 : ((n - (i + 1) : ℕ) : ℚ) + 1 = (n : ℚ) - i := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : (n : ℚ) - i ≠ 0 := by
      have : (i : ℚ) < n := by exact_mod_cast (show i < n by omega)
      linarith
    push_cast
    rw [h1, h2]
    field_simp
    ring

private theorem Q_closed (n h : ℕ) (hh : 2 ≤ h) (hhn : h ≤ n) :
    ∏ j ∈ Icc h (n - 1), ((1 - (j : ℚ)) * ((j : ℚ) + 2)) / 2 =
      (-1) ^ (n - h) * (((n - 2).factorial * (n + 1).factorial : ℕ) : ℚ) /
        ((((h - 2).factorial * (h + 1).factorial : ℕ) : ℚ) * 2 ^ (n - h)) := by
  induction n, hhn using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty, Nat.sub_self, pow_zero, pow_zero,
      one_mul, mul_one, div_self]
    positivity
  | succ n hhn ih =>
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, Finset.prod_Icc_succ_top (by omega), ih,
      show n - 1 + 1 = n by omega, show n + 1 - h = (n - h) + 1 by omega,
      show n + 1 - 2 = (n - 2) + 1 by omega, Nat.factorial_succ (n - 2),
      Nat.factorial_succ (n + 1)]
    have h1 : ((n - 2 : ℕ) : ℚ) + 1 = (n : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast
    rw [h1]
    field_simp
    ring

/-- `Γ n = (n-2)! (n+1)! / 2^{n-1}`. -/
private def Γ (n : ℕ) : ℚ := ((n - 2).factorial : ℚ) * (n + 1).factorial / 2 ^ (n - 1)

private theorem Γ_pos (n : ℕ) : 0 < Γ n := by
  unfold Γ
  have h1 : (0 : ℚ) < (n - 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have h2 : (0 : ℚ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  exact div_pos (mul_pos h1 h2) (by positivity)

/-- The printed denominator equals `Γ n` for `n ≥ 3`. -/
private theorem den_eq (N : ℕ) :
    ∑ h ∈ Icc 2 (N + 3), (h : ℚ) *
      (∏ j ∈ Icc 2 h, ((((N + 3 : ℕ) : ℚ) * (((N + 3 : ℕ) : ℚ) - 1) -
        ((j : ℚ) - 1) * ((j : ℚ) - 2)) / 2)) *
      ∏ j ∈ Icc h (N + 3 - 1), ((1 - (j : ℚ)) * ((j : ℚ) + 2)) / 2 = Γ (N + 3) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show N + 3 + 1 - 2 = N + 1 + 1 by omega]
  have hterm : ∀ k ∈ range (N + 1 + 1), ((2 + k : ℕ) : ℚ) *
      (∏ j ∈ Icc 2 (2 + k), ((((N + 3 : ℕ) : ℚ) * (((N + 3 : ℕ) : ℚ) - 1) -
        ((j : ℚ) - 1) * ((j : ℚ) - 2)) / 2)) *
      ∏ j ∈ Icc (2 + k) (N + 3 - 1), ((1 - (j : ℚ)) * ((j : ℚ) + 2)) / 2 =
      ((N + 4).factorial : ℚ) / 2 ^ (N + 2) *
        ((-1) ^ (N + 1 - k) * ((N + 1).choose k : ℚ) * ((k + (N + 3)).choose (N + 1) : ℚ) *
            (N + 1).factorial -
          (-1) ^ (N + 1 - k) * ((N + 1).choose k : ℚ) * ((k + (N + 3)).choose N : ℚ) *
            N.factorial) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [num_eq (N + 3) (2 + k) (by omega) (by omega) (by omega),
      Q_closed (N + 3) (2 + k) (by omega) (by omega), P,
      Nat.cast_choose ℚ (show k ≤ N + 1 by omega),
      Nat.cast_choose ℚ (show N + 1 ≤ k + (N + 3) by omega),
      Nat.cast_choose ℚ (show N ≤ k + (N + 3) by omega)]
    rw [show N + 3 + (2 + k) - 2 = k + (N + 3) by omega, show N + 3 - (2 + k) = N + 1 - k by omega,
      show 2 + k - 1 = k + 1 by omega, show N + 3 - 2 = N + 1 by omega,
      show 2 + k - 2 = k by omega, show 2 + k + 1 = k + 3 by omega,
      show k + (N + 3) - (N + 1) = k + 2 by omega, show k + (N + 3) - N = k + 3 by omega,
      show N + 3 + 1 = N + 4 by omega]
    rw [show k + 3 = (k + 2) + 1 by ring, Nat.factorial_succ (k + 2)]
    have h2 : (2 : ℚ) ^ (N + 2) = 2 ^ (k + 1) * 2 ^ (N + 1 - k) := by
      rw [← pow_add]; congr 1; omega
    rw [h2]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul]
  have e1 := alt_sum_choose (N + 1) (N + 3) (N + 1)
  have e2 := alt_sum_choose (N + 1) (N + 3) N
  rw [if_pos le_rfl, Nat.sub_self, Nat.choose_zero_right] at e1
  rw [if_neg (by omega)] at e2
  rw [e1, e2, Γ, show N + 3 - 2 = N + 1 by omega, show N + 3 - 1 = N + 2 by omega]
  push_cast
  ring

private theorem sum_Icc_one (n M : ℕ) (hM : M ≤ n) (g : ℕ → ℚ) (hg : ∀ i, M < i → g i = 0) :
    ∑ i ∈ Icc 1 n, g i = ∑ i ∈ range (M + 1), g i - g 0 := by
  have h1 : ∑ i ∈ range (n + 1), g i = ∑ i ∈ range (M + 1), g i := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    exact hg i (by omega)
  rw [← h1, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Finset.Ico_add_one_right_eq_Icc]
  ring

/-- The sums in the rows `d = 0, 1, 2`. -/
private theorem row_sum (N r : ℕ) (hr : r ≤ 2) :
    ∑ i ∈ Icc 1 (N + 3), P (N + 3) i * ((N + 3 - i).choose r : ℚ) * Bp (i + 1) (N + 3 + 1 - r) =
      -((-1) ^ (N + 3 - r) * ((N + 1).factorial : ℚ) * (N + 4 - r).factorial /
        (2 ^ (N + 2 - r) * r.factorial)) := by
  set M := N + 3 - r with hMdef
  set κ : ℚ := ((N + 4 - r).factorial : ℚ) * N.factorial / (2 ^ (M - 1) * r.factorial)
  have key : ∀ i ∈ Icc 1 (N + 3),
      P (N + 3) i * ((N + 3 - i).choose r : ℚ) * Bp (i + 1) (N + 3 + 1 - r) =
        κ * ((-1) ^ (M - i) * (M.choose i : ℚ) * ((i + (N + 1)).choose N : ℚ)) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    by_cases hiM : i ≤ M
    · rw [Bp_closed (i + 1) (N + 3 + 1 - r) (by omega) (by omega), P,
        Nat.cast_choose ℚ (show r ≤ N + 3 - i by omega), Nat.cast_choose ℚ hiM,
        Nat.cast_choose ℚ (show N ≤ i + (N + 1) by omega)]
      rw [show N + 3 + i - 2 = i + (N + 1) by omega, show N + 3 - i - r = M - i by omega,
        show N + 3 + 1 - r - (i + 1) = M - i by omega, show N + 3 + 1 - r - 1 = M by omega,
        show N + 3 + 1 - r = N + 4 - r by omega, show i + 1 - 1 = i by omega,
        show i + (N + 1) - N = i + 1 by omega]
      have h2 : (2 : ℚ) ^ (M - 1) = 2 ^ (i - 1) * 2 ^ (M - i) := by
        rw [← pow_add]; congr 1; omega
      simp only [κ]
      rw [h2]
      push_cast
      field_simp
    · rw [Nat.choose_eq_zero_of_lt (show N + 3 - i < r by omega),
        Nat.choose_eq_zero_of_lt (show M < i by omega)]
      simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum,
    sum_Icc_one (N + 3) M (by omega) _ (fun i hi => by
      rw [Nat.choose_eq_zero_of_lt hi]; simp),
    alt_sum_choose M (N + 1) N, if_neg (by omega)]
  simp only [κ, Nat.sub_zero, Nat.choose_zero_right, zero_add, Nat.choose_succ_self_right]
  rw [show M - 1 = N + 2 - r by omega, Nat.factorial_succ N]
  push_cast
  field_simp
  ring

/-- The sums in the rows `d ≥ 3`. -/
private theorem row_sum_high (N D : ℕ) (hD : D ≤ N) :
    ∑ i ∈ Icc 3 (D + 3), P (N + 3) i * ((N + 3 - i).choose (D + 3 - i) : ℚ) * Ap i (D + 3) =
      ((N + 1).factorial : ℚ) * (N + 4).factorial /
        (2 ^ (D + 2) * (N - D).factorial * (N + 1 - D).factorial) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show D + 3 + 1 - 3 = D + 1 by omega]
  set κ : ℚ := ((D + 3).factorial : ℚ) * (N + 1).factorial / (2 ^ (D + 2) * (N - D).factorial)
  have key : ∀ k ∈ range (D + 1),
      P (N + 3) (3 + k) * ((N + 3 - (3 + k)).choose (D + 3 - (3 + k)) : ℚ) * Ap (3 + k) (D + 3) =
        κ * ((-1) ^ (D - k) * (D.choose k : ℚ) * ((k + (N + 4)).choose (N + 1) : ℚ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Ap_closed (3 + k) (D + 3) (by omega) (by omega), P,
      Nat.cast_choose ℚ (show D + 3 - (3 + k) ≤ N + 3 - (3 + k) by omega),
      Nat.cast_choose ℚ (show k ≤ D by omega),
      Nat.cast_choose ℚ (show N + 1 ≤ k + (N + 4) by omega)]
    rw [show N + 3 + (3 + k) - 2 = k + (N + 4) by omega, show N + 3 - (3 + k) = N - k by omega,
      show D + 3 - (3 + k) = D - k by omega, show N - k - (D - k) = N - D by omega,
      show 3 + k - 1 = k + 2 by omega, show D + 3 - 3 = D by omega, show 3 + k - 3 = k by omega,
      show k + (N + 4) - (N + 1) = k + 3 by omega, show 3 + k = k + 3 by omega]
    have h2 : (2 : ℚ) ^ (D + 2) = 2 ^ (k + 2) * 2 ^ (D - k) := by
      rw [← pow_add]; congr 1; omega
    simp only [κ]
    rw [h2]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, alt_sum_choose D (N + 4) (N + 1),
    if_pos (by omega), Nat.cast_choose ℚ (show N + 1 - D ≤ N + 4 by omega),
    show N + 4 - (N + 1 - D) = D + 3 by omega]
  simp only [κ]
  field_simp

/-- For `3 ≤ d ≤ n`, only the indices `3 ≤ i ≤ d` contribute to row `d`. -/
private theorem row_high (n d : ℕ) (hd : 3 ≤ d) (hdn : d ≤ n) (x : ℕ → ℚ) :
    ∑ i ∈ Icc 1 n, x i * g n i d =
      ∑ i ∈ Icc 3 d, x i * (((n - i).choose (d - i) : ℚ) * Ap i d * Bp 1 (n + 1 - d)) := by
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc (by omega) hdn)
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hi
    simp only [g, Ap_zero (show 0 ≤ 2 by omega) hd]
    by_cases hid : i ≤ d
    · rw [if_pos hid, Ap_zero (by omega) hd]; ring
    · rw [if_neg hid]; ring
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    simp only [g, if_pos hi.2, Ap_zero (show 0 ≤ 2 by omega) hd]
    ring

private theorem Bp_ne_zero (a b : ℕ) (ha : 1 ≤ a) : Bp a b ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro u hu
  rw [Finset.mem_Ico] at hu
  rw [β_eq]
  have : (0 : ℚ) < u := by exact_mod_cast (show 0 < u by omega)
  intro h
  have : ((u : ℚ) + 1) * u = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h' <;> linarith

private theorem P_pos (n i : ℕ) : 0 < P n i := by
  unfold P
  have h1 : (0 : ℚ) < (n + i - 2).factorial := by exact_mod_cast Nat.factorial_pos _
  have h2 : (0 : ℚ) < (n - i).factorial := by exact_mod_cast Nat.factorial_pos _
  exact div_pos h1 (mul_pos h2 (by positivity))

private theorem formula_eq (N i : ℕ) (hi : 1 ≤ i) (hin : i ≤ N + 3) :
    formula (N + 3) i = (-1) ^ (N + 3) * P (N + 3) i / Γ (N + 3) := by
  rw [formula, num_eq (N + 3) i (by omega) hi hin, den_eq]

private theorem low_sum (n d : ℕ) (hdn : d ≤ n) (F : ℕ → ℚ) :
    ∑ i ∈ Icc 1 n, (if i ≤ d then F i else 0) = ∑ i ∈ Icc 1 d, F i := by
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc le_rfl hdn)
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hi
    rw [if_neg (by omega)]
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [if_pos hi.2]

private theorem Bp_one (m : ℕ) (hm : 1 ≤ m) :
    Bp 1 m = (-1) ^ (m - 1) * ((m - 1).factorial : ℚ) * m.factorial / 2 ^ (m - 1) := by
  rw [Bp_closed 1 m le_rfl hm]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.factorial_one, mul_one, Nat.cast_mul,
    Nat.cast_one]
  ring

private theorem Ap01 : Ap 0 1 = 1 := by rw [Ap_succ le_rfl, Ap_self, α_zero, one_mul]
private theorem Ap02 : Ap 0 2 = 1 := by rw [Ap_succ (by omega), Ap01, α_one, one_mul]
private theorem Ap12 : Ap 1 2 = 1 := by rw [Ap_succ le_rfl, Ap_self, α_one, one_mul]

/-- Splitting a row into the part with `i ≤ d` and the part through `(0, ·)`. -/
private theorem row_split (n d : ℕ) (hdn : d ≤ n) (x : ℕ → ℚ) :
    ∑ i ∈ Icc 1 n, x i * g n i d =
      ∑ i ∈ Icc 1 d, x i * (((n - i).choose (d - i) : ℚ) * Ap i d * Bp 1 (n + 1 - d)) -
        Ap 0 d * ∑ i ∈ Icc 1 n, x i * ((n - i).choose d : ℚ) * Bp (i + 1) (n + 1 - d) := by
  rw [← low_sum n d hdn, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [g]
  split_ifs <;> ring

/-- The conjectured coefficients satisfy every row (`n ≥ 3`). -/
private theorem rows_hold (N d : ℕ) (hd : d ≤ N + 3) :
    ∑ i ∈ Icc 1 (N + 3), formula (N + 3) i * g (N + 3) i d = (-1) ^ d := by
  have hP1 : P (N + 3) 1 = 1 := by
    simp only [P, show N + 3 + 1 - 2 = N + 3 - 1 by omega, Nat.sub_self, pow_zero, mul_one]
    exact div_self (by positivity)
  have hΓ : Γ (N + 3) = ((N + 1).factorial : ℚ) * (N + 4).factorial / 2 ^ (N + 2) := by
    simp only [Γ, show N + 3 - 2 = N + 1 by omega, show N + 3 - 1 = N + 2 by omega]
  have hS : ∑ i ∈ Icc 1 (N + 3), P (N + 3) i * g (N + 3) i d =
      (-1) ^ (N + 3) * (-1) ^ d * Γ (N + 3) := by
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with rfl | rfl | rfl | hd3
    · rw [row_split _ _ (by omega), Finset.Icc_eq_empty (by omega), Finset.sum_empty,
        row_sum N 0 (by omega), Ap_self, hΓ]
      simp only [Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero]
      ring
    · rw [row_split _ _ (by omega), Finset.Icc_self, Finset.sum_singleton,
        row_sum N 1 (by omega), Ap01, Ap_self, hP1, Bp_one (N + 3 + 1 - 1) (by omega), hΓ]
      simp only [show N + 3 + 1 - 1 = N + 3 by omega, show N + 3 - 1 = N + 2 by omega,
        show N + 2 - 1 = N + 1 by omega,
        show (1 : ℕ) - 1 = 0 by rfl, Nat.choose_zero_right, Nat.factorial_succ,
        Nat.factorial_zero, pow_one]
      push_cast; field_simp; ring
    · rw [row_split _ _ (by omega), Finset.sum_Icc_succ_top (by omega), Finset.Icc_self,
        Finset.sum_singleton, row_sum N 2 le_rfl, Ap02, Ap12, Ap_self, hP1,
        Bp_one (N + 3 + 1 - 2) (by omega), hΓ]
      simp only [P, show N + 3 + 1 - 2 = N + 2 by omega, show N + 2 - 1 = N + 1 by omega,
        show N + 3 - 2 = N + 1 by omega,
        show N + 3 - 1 = N + 2 by omega, show N + 3 + (1 + 1) - 2 = N + 3 by omega,
        show N + 2 - 2 = N by omega,
        show (2 : ℕ) - 1 = 1 by rfl, show (2 : ℕ) - (1 + 1) = 0 by rfl,
        Nat.choose_zero_right, Nat.choose_one_right,
        Nat.factorial_succ, Nat.factorial_zero, pow_one]
      push_cast; field_simp; ring
    · obtain ⟨D, rfl⟩ : ∃ D, d = D + 3 := ⟨d - 3, by omega⟩
      obtain ⟨e, rfl⟩ : ∃ e, N = D + e := ⟨N - D, by omega⟩
      rw [row_high (D + e + 3) (D + 3) (by omega) hd (P (D + e + 3))]
      have hre : ∀ i ∈ Icc 3 (D + 3), P (D + e + 3) i *
          (((D + e + 3 - i).choose (D + 3 - i) : ℚ) * Ap i (D + 3) *
            Bp 1 (D + e + 3 + 1 - (D + 3))) =
          (P (D + e + 3) i * ((D + e + 3 - i).choose (D + 3 - i) : ℚ) * Ap i (D + 3)) *
            Bp 1 (D + e + 3 + 1 - (D + 3)) := fun i _ => by ring
      rw [Finset.sum_congr rfl hre, ← Finset.sum_mul, row_sum_high (D + e) D (by omega),
        Bp_one (D + e + 3 + 1 - (D + 3)) (by omega), hΓ]
      simp only [show D + e + 3 + 1 - (D + 3) = e + 1 by omega, show e + 1 - 1 = e by omega,
        show D + e - D = e by omega, show D + e + 1 - D = e + 1 by omega]
      have hs : ((-1 : ℚ) ^ (D + e + 3)) * (-1) ^ (D + 3) = (-1) ^ e := by
        rw [← pow_add, show D + e + 3 + (D + 3) = e + 2 * (D + 3) by ring, pow_add, pow_mul]
        norm_num
      have h2 : (2 : ℚ) ^ (D + e + 2) = 2 ^ e * 2 ^ (D + 2) := by
        rw [← pow_add]; ring_nf
      rw [hs, h2, Nat.factorial_succ e]
      push_cast; field_simp
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [formula_eq N i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2])]
  have hΓ0 := (Γ_pos (N + 3)).ne'
  calc ∑ i ∈ Icc 1 (N + 3), (-1) ^ (N + 3) * P (N + 3) i / Γ (N + 3) * g (N + 3) i d
      = (-1) ^ (N + 3) / Γ (N + 3) * ∑ i ∈ Icc 1 (N + 3), P (N + 3) i * g (N + 3) i d := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ = (-1) ^ d := by
        rw [hS]; field_simp
        rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

private theorem Bp_cons {a b : ℕ} (h : a < b) : Bp a b = β a * Bp (a + 1) b := by
  simp only [Bp]; rw [Finset.prod_eq_prod_Ico_succ_bot h]

/-- The row system has at most one solution (`n ≥ 3`). -/
private theorem rows_unique (N : ℕ) (e : ℕ → ℚ)
    (h : ∀ d ≤ N + 3, ∑ i ∈ Icc 1 (N + 3), e i * g (N + 3) i d = 0) :
    ∀ i ∈ Icc 1 (N + 3), e i = 0 := by
  set n := N + 3 with hn
  have hhigh : ∀ d, 3 ≤ d → d ≤ n → e d = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro hd hdn
      have hrow := h d hdn
      rw [row_high n d hd hdn e, ← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_succ_top (by omega), Finset.sum_eq_zero (fun i hi => by
          rw [Finset.mem_Ico] at hi; rw [ih i (by omega) hi.1 (by omega)]; ring),
        zero_add, Nat.sub_self, Nat.choose_zero_right, Ap_self] at hrow
      have hB := Bp_ne_zero 1 (n + 1 - d) le_rfl
      simpa [hB] using hrow
  have hsplit : ∀ d ≤ n, ∑ i ∈ Icc 1 n, e i * g n i d = e 1 * g n 1 d + e 2 * g n 2 d := by
    intro d _
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_zero (fun i hi => by
        rw [Finset.mem_Ico] at hi; rw [hhigh i (by omega) (by omega)]; ring)]
    ring
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  rw [hsplit 0 (by omega)] at h0
  rw [hsplit 1 (by omega)] at h1
  simp only [g, if_neg (show ¬ (1 ≤ 0) by omega), if_neg (show ¬ (2 ≤ 0) by omega),
    if_pos (le_refl 1), if_neg (show ¬ (2 ≤ 1) by omega), Nat.choose_zero_right, Ap_self, Ap01,
    Nat.sub_self, Nat.choose_one_right, Nat.sub_zero, Nat.add_sub_cancel,
    show (1 : ℕ) + 1 = 2 from rfl, show (2 : ℕ) + 1 = 3 from rfl, Nat.cast_one, one_mul,
    mul_one] at h0 h1
  have hβn : β n ≠ 0 := by
    rw [β_eq]; have : (0 : ℚ) < n := by positivity
    intro h'; have : ((n : ℚ) + 1) * n = 0 := by linarith
    rcases mul_eq_zero.mp this with h'' | h'' <;> linarith
  rw [Bp_succ (show 2 ≤ n by omega), Bp_succ (show 3 ≤ n by omega)] at h0
  rw [Bp_cons (show 1 < n by omega), show Bp (1 + 1) n = Bp 2 n from rfl] at h1
  have hβ1 : β 1 = -1 := by norm_num [β]
  rw [hβ1] at h1
  have hB2 := Bp_ne_zero 2 n (by omega)
  have hB3 := Bp_ne_zero 3 n (by omega)
  have e0 : e 1 * Bp 2 n + e 2 * Bp 3 n = 0 := by
    have : β n * (e 1 * Bp 2 n + e 2 * Bp 3 n) = 0 := by linear_combination -h0
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hβn
    · exact h'
  have hn2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; rfl
  have hn1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; rfl
  rw [hn2, hn1] at h1
  have e2 : e 2 * Bp 3 n = 0 := by linear_combination ((n : ℚ) * e0 + h1) / 2
  have he2 : e 2 = 0 := by
    rcases mul_eq_zero.mp e2 with h' | h'
    · exact h'
    · exact absurd h' hB3
  have he1 : e 1 = 0 := by
    rw [he2, zero_mul, add_zero] at e0
    rcases mul_eq_zero.mp e0 with h' | h'
    · exact h'
    · exact absurd h' hB2
  intro i hi
  rw [Finset.mem_Icc] at hi
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | hi3
  · exact he1
  · exact he2
  · exact hhigh i hi3 hi.2

/-- The case `n = 2`: `c_1 = c_2 = 1/2`. -/
private theorem case_two (c : ℕ → ℚ) :
    (∀ d ≤ 2, ∑ i ∈ Icc 1 2, c i * g 2 i d = (-1) ^ d) ↔ ∀ i ∈ Icc 1 2, c i = formula 2 i := by
  have hsum : ∀ d, ∑ i ∈ Icc 1 2, c i * g 2 i d = c 1 * g 2 1 d + c 2 * g 2 2 d := by
    intro d; rw [Finset.sum_Icc_succ_top (by omega), Finset.Icc_self, Finset.sum_singleton]
  have g10 : g 2 1 0 = 3 := by norm_num [g, Bp, Ap, β, Finset.prod_Ico_succ_top]
  have g20 : g 2 2 0 = -1 := by norm_num [g, Bp, Ap]
  have g11 : g 2 1 1 = -2 := by norm_num [g, Bp, Ap, β, α]
  have g21 : g 2 2 1 = 0 := by norm_num [g, Bp, Ap]
  have g12 : g 2 1 2 = 1 := by norm_num [g, Bp, Ap, α]
  have g22 : g 2 2 2 = 1 := by norm_num [g, Bp, Ap]
  have f1 : formula 2 1 = 1 / 2 := by norm_num [formula]
  have f2 : formula 2 2 = 1 / 2 := by norm_num [formula]
  constructor
  · intro h i hi
    have r1 := h 1 (by omega)
    have r2 := h 2 (by omega)
    rw [hsum, g11, g21] at r1
    rw [hsum, g12, g22] at r2
    rw [Finset.mem_Icc] at hi
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · rw [f1]; linarith
    · rw [f2]; linarith
  · intro h d hd
    rw [hsum, h 1 (by simp), h 2 (by simp), f1, f2]
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
    · rw [g10, g20]; norm_num
    · rw [g11, g21]; norm_num
    · rw [g12, g22]; norm_num

/-- The conjecture of Manetti and Ricciardi (arXiv:1509.09032, Conjecture 2.4), stated through
the identity of their Theorem 6.4 in `End_ℚ(ℚ[x])`: for every `n ≥ 2`, a sequence `c` satisfies
`Φ^{n+1} = (c_1 ρ_1^n + c_2 ρ_1^{n-2} ρ_2 + ⋯ + c_n ρ_n) Φ^1` exactly when `c_i` is the printed
expression for `1 ≤ i ≤ n`; moreover `(-1)^n c_i^n > 0`. -/
def claim : Prop :=
  ∀ n ≥ 2,
    (∀ c : ℕ → ℚ, koszul (n + 1) = ∑ i ∈ Icc 1 n, c i • (rho 1)^[n - i] (rho i (koszul 1)) ↔
        ∀ i ∈ Icc 1 n, c i = formula n i) ∧
      ∀ i ∈ Icc 1 n, 0 < (-1) ^ n * formula n i

theorem result : claim := by
  intro n hn
  rcases (show n = 2 ∨ ∃ N, n = N + 3 from by
    rcases Nat.lt_or_ge n 3 with h | h
    · left; omega
    · right; exact ⟨n - 3, by omega⟩) with rfl | ⟨N, rfl⟩
  · refine ⟨fun c => (identity_iff_rows 2 c).trans (case_two c), fun i hi => ?_⟩
    rw [Finset.mem_Icc] at hi
    rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl <;> norm_num [formula]
  · refine ⟨fun c => (identity_iff_rows (N + 3) c).trans ⟨fun hrows => ?_, fun hc d hd => ?_⟩,
      fun i hi => ?_⟩
    · have := rows_unique N (fun i => c i - formula (N + 3) i) (fun d hd => by
        simp only [sub_mul, Finset.sum_sub_distrib, hrows d hd, rows_hold N d hd, sub_self])
      intro i hi
      exact sub_eq_zero.mp (this i hi)
    · rw [Finset.sum_congr rfl (fun i hi => by rw [hc i hi])]
      exact rows_hold N d hd
    · rw [Finset.mem_Icc] at hi
      rw [formula_eq N i hi.1 hi.2, ← mul_div_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
        neg_one_sq, one_pow, one_mul]
      exact div_pos (P_pos _ _) (Γ_pos _)

end D5.S3.HomologicalAlgebra.HigherAntibracketCoefficients
