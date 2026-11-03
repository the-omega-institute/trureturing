/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelBlocks
   mirror-E: none(waiver:actual-continuant-block-action)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: Cyclic ordinary transfers act on the supplied metallic continuants. -/

import D5.S3.Combinatorics.MetallicHankel.MetallicHankelData
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic

/-! Ordinary block actions for the actual metallic recurrence data. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelBlocks

open PowerSeries Finset MetallicHankelData
open scoped Matrix

/-- Ordered left multiplication of the first `p` transitions. -/
noncomputable def transferPrefix
    (A : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
    ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) :=
  Nat.rec 1 (fun p M => A p * M)

private theorem prefix_period
    (A : ℕ → Matrix (Fin 2) (Fin 2) (PowerSeries ℤ))
    (L : ℕ) (hA : ∀ p, A (p + L) = A p) (K : ℕ) :
    transferPrefix A (K * L) = transferPrefix A L ^ K := by
  have add (p : ℕ) : transferPrefix A (p + L) =
      transferPrefix A p * transferPrefix A L := by
    induction p with
    | zero => simp [transferPrefix]
    | succ p ih =>
      rw [show p + 1 + L = (p + L) + 1 by omega]
      change A (p + L) * transferPrefix A (p + L) =
        (A p * transferPrefix A p) * transferPrefix A L
      rw [hA, ih, Matrix.mul_assoc]
  induction K with
  | zero => simp [transferPrefix]
  | succ K ih => rw [Nat.succ_mul, add, ih, pow_succ]

private theorem periodic_multiple {α : Type*} (f : ℕ → α) (L : ℕ)
    (hf : ∀ p, f (p + L) = f p) (p K : ℕ) : f (p + K * L) = f p := by
  exact (Function.Periodic.nat_mul hf K) p

private theorem source_period
    (n L : ℕ) (hn : 1 ≤ n)
    (k : ℕ → ℕ) (b : ℕ → ℤ) (D : ℕ → PowerSeries ℤ)
    (hL : L = if n = 1 then 3 else 6 * n - 4)
    (data : ∀ p, let z := Nat.rec TailState.v₂ (fun _ z => nextState (max n 2) z) p
      k p = (if n = 1 then (if p % 3 = 2 then 1 else 0)
        else (fractionData (max n 2) z).1) ∧
      b p = (if n = 1 then (if p % 3 = 1 then 1 else -1)
        else (fractionData (max n 2) z).2.1) ∧
      D p = (if n = 1 then (if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X)
        else (fractionData (max n 2) z).2.2)) :
    0 < L ∧ (∀ p, k (p + L) = k p) ∧ (∀ p, b (p + L) = b p) ∧
      (∀ p, D (p + L) = D p) ∧ (∀ p, constantCoeff (D p) = 1) ∧
      (∏ i ∈ range L, b i) = 1 ∧
      (∑ i ∈ range L, (k i + 1)) = 2 * n * (n + 1) ∧ k (L - 1) = n ∧
      (∀ p r, k p + 1 < r → coeff r (D p) = 0) ∧
      List.ofFn (fun i : Fin L => (coeff (k i + 1) (D i), b i)) =
        (if n = 1 then [(1, -1), (1, 1), (-1, -1)] else MetallicHankelTransfer.topWord n) := by
  classical
  by_cases hn1 : n = 1
  · subst n
    simp only [ite_true] at hL
    subst L
    have hk (p : ℕ) : k p = if p % 3 = 2 then 1 else 0 := by simpa using (data p).1
    have hb (p : ℕ) : b p = if p % 3 = 1 then 1 else -1 := by simpa using (data p).2.1
    have hd (p : ℕ) : D p = if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X := by simpa using (data p).2.2
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p; simp [hk]
    · intro p; simp [hb]
    · intro p; simp [hd]
    · intro p; rw [hd]; split_ifs <;> simp
    · norm_num [hb, prod_range_succ]
    · norm_num [hk, sum_range_succ]
    · norm_num [hk]
    · intro p r hr
      by_cases hp : p % 3 = 2
      · have h : 2 < r := by simpa [hk, hp] using hr
        simp [hd, hp, coeff_X, coeff_X_pow, show r ≠ 0 by omega,
          show r ≠ 1 by omega, show r ≠ 2 by omega]
      · have h : 1 < r := by simpa [hk, hp] using hr
        simp [hd, hp, coeff_X, show r ≠ 0 by omega, show r ≠ 1 by omega]
    · norm_num [List.ofFn_succ, hk, hb, hd, coeff_X, coeff_X_pow]
  have hn2 : 2 ≤ n := by omega
  have hmax : max n 2 = n := max_eq_left hn2
  let z : ℕ → TailState := Nat.rec .v₂ (fun _ a => nextState n a)
  obtain ⟨hlen, hvalid, hchain, hweight, hword, hden⟩ := cycle_data n hn2
  have hl : L = (cycle n).length := by rw [hL, ite_eq_right hn1, hlen]
  have hpos : 0 < L := by rw [hL, ite_eq_right hn1]; omega
  clear hL
  have segment : ∀ p, p ≤ L → z p = (cycle n ++ [TailState.v₂]).getD p .v₂ := by
    intro p
    induction p with
    | zero => simp [z, cycle]
    | succ p ih =>
      intro hp
      have hlt : p + 1 < (cycle n ++ [TailState.v₂]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hc := hchain.getElem p hlt
      rw [List.getElem_eq_getD TailState.v₂, List.getElem_eq_getD TailState.v₂] at hc
      change nextState n (z p) = _
      rw [ih (by omega)]
      exact hc
  have hend : z L = .v₂ := by
    rw [segment L le_rfl, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    simp [hl]
  have period (p : ℕ) : z (p + L) = z p := by
    induction p with
    | zero => simpa [z] using hend
    | succ p ih =>
      rw [show p + 1 + L = (p + L) + 1 by omega]
      change nextState n (z (p + L)) = nextState n (z p)
      rw [ih]
  have state_at (i : ℕ) (hi : i < L) : z i = (cycle n)[i]'(by omega) := by
    rw [segment i (by omega), ← List.getElem_eq_getD TailState.v₂]
    · exact List.getElem_append_left (by omega)
    · simp only [List.length_append, List.length_singleton]; omega
  have mod (p : ℕ) : z p = z (p % L) := by
    have h := periodic_multiple z L period (p % L) (p / L)
    rw [Nat.mul_comm (p / L) L, Nat.mod_add_div] at h
    exact h
  have hd (p : ℕ) : k p = (fractionData n (z p)).1 ∧
      b p = (fractionData n (z p)).2.1 ∧ D p = (fractionData n (z p)).2.2 := by
    simpa only [hn1, ite_false, hmax, z] using data p
  have listk : List.ofFn (fun i : Fin L => k i + 1) =
      (cycle n).map (fun a => (fractionData n a).1 + 1) := by
    subst L
    conv_rhs => rw [← List.ofFn_getElem (xs := cycle n), List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rw [(hd i).1, state_at i i.isLt]
    rfl
  have listb : List.ofFn (fun i : Fin L => b i) =
      (cycle n).map (fun a => (fractionData n a).2.1) := by
    subst L
    conv_rhs => rw [← List.ofFn_getElem (xs := cycle n), List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rw [(hd i).2.1, state_at i i.isLt]
    rfl
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; rw [(hd _).1, (hd _).1, period]
  · intro p; rw [(hd _).2.1, (hd _).2.1, period]
  · intro p; rw [(hd _).2.2, (hd _).2.2, period]
  · intro p
    rw [(hd p).2.2, mod, state_at _ (Nat.mod_lt _ hpos)]
    exact (hden _ (hvalid _ (List.getElem_mem _))).1
  · rw [← Fin.prod_univ_eq_prod_range, ← List.prod_ofFn, listb]
    exact (cycle_sign n hn2).1
  · rw [← Fin.sum_univ_eq_sum_range, ← List.sum_ofFn, listk, hweight]
  · rw [(hd _).1, state_at _ (by omega)]
    have last : (cycle n)[L - 1]'(by omega) = TailState.v₁ := by
      subst L
      rw [List.getElem_length_sub_one_eq_getLast]
      simp [cycle]
    rw [last]
    rfl
  · intro p r hr
    rw [(hd p).1] at hr
    rw [(hd p).2.2]
    rw [mod, state_at _ (Nat.mod_lt _ hpos)] at hr ⊢
    exact (hden _ (hvalid _ (List.getElem_mem _))).2 r hr
  · rw [ite_eq_right hn1]
    subst L
    conv_rhs => rw [← hword, ← List.ofFn_getElem (xs := cycle n), List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rw [(hd i).1, (hd i).2.1, (hd i).2.2, state_at i i.isLt]
    rfl

/-- The cyclic ordinary step retains the preceding degree increment. -/
noncomputable def ordinaryStep (L : ℕ) (k : ℕ → ℕ) (b : ℕ → ℤ)
    (D : ℕ → PowerSeries ℤ) (p : ℕ) :
    Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) :=
  !![D p, -C (b p) * X ^ (k (p + L - 1) + k p + 2); 1, 0]

/-- Every parity block acts on the supplied continuants, with the exact determinant,
trace constant term, and preceding degree increment. -/
theorem ordinary_blocks (n L : ℕ) (hn : 1 ≤ n)
    (k : ℕ → ℕ) (b : ℕ → ℤ) (D Q : ℕ → PowerSeries ℤ)
    (hL : L = if n = 1 then 3 else 6 * n - 4)
    (data : ∀ p, let z := Nat.rec TailState.v₂ (fun _ z => nextState (max n 2) z) p
      k p = (if n = 1 then (if p % 3 = 2 then 1 else 0)
        else (fractionData (max n 2) z).1) ∧
      b p = (if n = 1 then (if p % 3 = 1 then 1 else -1)
        else (fractionData (max n 2) z).2.1) ∧
      D p = (if n = 1 then (if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X)
        else (fractionData (max n 2) z).2.2))
    (qzero : Q 0 = 1) (qone : Q 1 = D 0)
    (qstep : ∀ p, Q (p + 2) = D (p + 1) * Q (p + 1) -
      C (b (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p) :
    let ν := if n % 2 = 0 then 1 else 2
    let ρ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
    let U := transferPrefix (ordinaryStep L k b D) L ^ ν
    constantCoeff (Matrix.trace U) = 1 ∧ U.det = X ^ (2 * ρ) ∧
      (∀ K : ℕ, 1 ≤ K →
        let p := (K * ν) * L
        U ^ K *ᵥ ![1, 0] = ![Q p, Q (p - 1)]) ∧
      ∀ (s : ℕ → ℕ), (∀ p, s (p + 1) = s p + k p + 1) →
        ∀ K : ℕ, 1 ≤ K →
          let p := (K * ν) * L
          s p = s (p - 1) + (n + 1) := by
  classical
  obtain ⟨hpos, hk, hb, hd, hconstant, hsign, hweight, hlast, _, _⟩ :=
    source_period n L hn k b D hL data
  dsimp only
  let ν := if n % 2 = 0 then 1 else 2
  let ρ := if n % 2 = 0 then 2 * n * (n + 1) else 4 * n * (n + 1)
  let A := ordinaryStep L k b D
  let M := transferPrefix A L
  have hpν : 0 < ν := by dsimp [ν]; split_ifs <;> omega
  have weightν : (2 * n * (n + 1)) * ν = ρ := by
    dsimp [ν, ρ]; split_ifs <;> ring
  have period (p : ℕ) : A (p + L) = A p := by
    dsimp [A, ordinaryStep]
    rw [hd, hb, hk, show p + L + L - 1 = (p + L - 1) + L by omega, hk]
  have state : ∀ p, transferPrefix A p *ᵥ ![1, 0] =
      ![Q p, if p = 0 then 0 else Q (p - 1)] := by
    intro p
    induction p with
    | zero => simp [transferPrefix, qzero]
    | succ p ih =>
      change (A p * transferPrefix A p) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ih]
      cases p with
      | zero =>
        funext i; fin_cases i <;>
          simp [A, ordinaryStep, qzero, qone, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      | succ p =>
        have hp : p + 1 + L - 1 = p + L := by omega
        funext i; fin_cases i <;>
          simp [A, ordinaryStep, hp, hk, qstep, Matrix.mulVec, dotProduct,
            Fin.sum_univ_two, sub_eq_add_neg]
  have rotate (f : ℕ → ℕ) (hf : ∀ p, f (p + L) = f p) (p : ℕ) :
      (∑ i ∈ range L, f (p + i)) = ∑ i ∈ range L, f i := by
    obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    induction p with
    | zero => simp
    | succ p ih =>
      calc
        _ = (∑ i ∈ range m, f (p + 1 + i)) + f p := by
          rw [hm, sum_range_succ, show p + 1 + m = p + L by omega, hf]
        _ = (∑ i ∈ range m, f (p + (i + 1))) + f p := by simp only [Nat.add_assoc, Nat.add_comm 1]
        _ = ∑ i ∈ range L, f (p + i) := by rw [hm, sum_range_succ']; simp
        _ = _ := ih
  have exponent : (∑ i ∈ range L, (k (i + L - 1) + k i + 2)) =
      2 * (2 * n * (n + 1)) := by
    have hrot : (∑ i ∈ range L, k (i + L - 1)) = ∑ i ∈ range L, k i := by
      apply Eq.trans _ (rotate k hk (L - 1))
      apply sum_congr rfl
      intro i hi
      congr 1
      omega
    have hw := hweight
    simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul] at hw ⊢
    rw [hrot]
    omega
  have determinant : M.det = X ^ (2 * (2 * n * (n + 1))) := by
    have h (p : ℕ) : (transferPrefix A p).det =
        C (∏ i ∈ range p, b i) * X ^ (∑ i ∈ range p, (k (i + L - 1) + k i + 2)) := by
      induction p with
      | zero => simp [transferPrefix]
      | succ p ih =>
        change (A p * transferPrefix A p).det = _
        rw [Matrix.det_mul, ih, prod_range_succ, sum_range_succ, map_mul, pow_add]
        simp only [A, ordinaryStep, Matrix.det_fin_two_of, mul_zero, mul_one]
        ring
    simpa only [M, hsign, map_one, one_mul, exponent] using h L
  let E : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 0]
  have eval (p : ℕ) : (transferPrefix A (p + 1)).map constantCoeff = E := by
    have step0 (i : ℕ) : (A i).map constantCoeff = E := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [A, ordinaryStep, E, hconstant, Matrix.map_apply]
    induction p with
    | zero => simpa [transferPrefix] using step0 0
    | succ p ih =>
      change (A (p + 1) * transferPrefix A (p + 1)).map constantCoeff = E
      rw [Matrix.map_mul, step0, ih]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [E, Matrix.mul_apply, Fin.sum_univ_two]
  have evalM : M.map constantCoeff = E := by
    obtain ⟨p, hp⟩ : ∃ p, L = p + 1 := ⟨L - 1, by omega⟩
    simpa [M, hp] using eval p
  have evalU : (M ^ ν).map constantCoeff = E := by
    dsimp [ν]
    split_ifs <;> simp only [pow_one, pow_two, Matrix.map_mul, evalM]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [E, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change constantCoeff (Matrix.trace (M ^ ν)) = 1
    have h := congrArg Matrix.trace evalU
    simpa [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum, E,
      Fin.sum_univ_two] using h
  · change (M ^ ν).det = X ^ (2 * ρ)
    rw [Matrix.det_pow, determinant, ← pow_mul,
      show 2 * (2 * n * (n + 1)) * ν = 2 * ((2 * n * (n + 1)) * ν) by ring, weightν]
  · intro K hK
    have he := state ((K * ν) * L)
    have hp : (K * ν) * L ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by omega) hpν) hpos)
    rw [prefix_period A L period, ite_eq_right hp] at he
    have hpow : transferPrefix A L ^ (K * ν) = (M ^ ν) ^ K := by
      rw [Nat.mul_comm K ν, pow_mul]
    rw [hpow] at he
    exact he
  · intro s hs K hK
    let t := K * ν
    have ht : 0 < t := Nat.mul_pos (by omega) hpν
    have hp : 0 < t * L := Nat.mul_pos ht hpos
    have he : t * L - 1 = (L - 1) + (t - 1) * L := by
      calc
        _ = ((t - 1) + 1) * L - 1 := by rw [Nat.sub_add_cancel ht]
        _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hprev : k (t * L - 1) = n := by
      rw [he, periodic_multiple k L hk, hlast]
    have h := hs (t * L - 1)
    rw [Nat.sub_add_cancel hp, hprev] at h
    simpa only [t, Nat.add_assoc] using h


/-- Reversal at a specified support bound, including leading zero coefficients. -/
noncomputable def reverseAt (d : ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  ((trunc (d + 1) f).reflect d : Polynomial ℤ)

theorem reverse_coeff (d r : ℕ) (f : PowerSeries ℤ) :
    coeff r (reverseAt d f) = if r ≤ d then coeff (d - r) f else 0 := by
  simp only [reverseAt, Polynomial.coeff_coe, Polynomial.coeff_reflect, coeff_trunc]
  by_cases hr : r ≤ d
  · rw [Polynomial.revAt_le hr, ite_eq_left (by omega), ite_eq_left hr]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega), ite_eq_right (by omega), ite_eq_right hr]

private theorem trunc_supported (d : ℕ) (f : PowerSeries ℤ)
    (hf : ∀ r, d < r → coeff r f = 0) :
    ((trunc (d + 1) f : Polynomial ℤ) : PowerSeries ℤ) = f := by
  ext r
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with h
  · rfl
  · exact (hf r (by omega)).symm

private theorem reverse_polynomial (d : ℕ) (f : Polynomial ℤ)
    (hf : f.natDegree ≤ d) :
    reverseAt d (f : PowerSeries ℤ) = (f.reflect d : Polynomial ℤ) := by
  simp only [reverseAt, trunc_coe_eq_self (by omega : f.natDegree < d + 1)]

private theorem reverse_mul (a b : ℕ) (f g : PowerSeries ℤ)
    (hf : ∀ r, a < r → coeff r f = 0)
    (hg : ∀ r, b < r → coeff r g = 0) :
    reverseAt (a + b) (f * g) = reverseAt a f * reverseAt b g := by
  let F := trunc (a + 1) f
  let G := trunc (b + 1) g
  have hF : F.natDegree ≤ a := Nat.le_of_lt_succ (natDegree_trunc_lt f a)
  have hG : G.natDegree ≤ b := Nat.le_of_lt_succ (natDegree_trunc_lt g b)
  rw [← trunc_supported a f hf, ← trunc_supported b g hg]
  change reverseAt (a + b) ((F : PowerSeries ℤ) * (G : PowerSeries ℤ)) =
    reverseAt a (F : PowerSeries ℤ) * reverseAt b (G : PowerSeries ℤ)
  rw [← Polynomial.coe_mul, reverse_polynomial _ _ ((Polynomial.natDegree_mul_le ..).trans
    (Nat.add_le_add hF hG)), Polynomial.reflect_mul F G hF hG,
    reverse_polynomial a F hF, reverse_polynomial b G hG, Polynomial.coe_mul]

private theorem reverse_sub (d : ℕ) (f g : PowerSeries ℤ) :
    reverseAt d (f - g) = reverseAt d f - reverseAt d g := by
  ext r
  simp only [map_sub, reverse_coeff]
  split_ifs <;> simp

private theorem reverse_shift (a d : ℕ) (c : ℤ) (f : PowerSeries ℤ) :
    reverseAt (a + d) (C c * X ^ a * f) = C c * reverseAt d f := by
  ext r
  rw [reverse_coeff, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_C_mul,
    reverse_coeff]
  by_cases hr : r ≤ d
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hr,
      show a + d - r - a = d - r by omega]
  · by_cases ha : r ≤ a + d
    · rw [ite_eq_left ha, ite_eq_right (by omega), ite_eq_right hr]
    · rw [ite_eq_right ha, ite_eq_right hr]; simp

/-- The reversed step has no power of X in its off-diagonal entry. -/
noncomputable def reversedStep (k : ℕ → ℕ) (b : ℕ → ℤ)
    (D : ℕ → PowerSeries ℤ) (p : ℕ) :
    Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) :=
  !![reverseAt (k p + 1) (D p), -C (b p); 1, 0]

/-- Reversing the same supported continuants gives identity constant monodromy
and the exact action at every positive parity-block endpoint. -/
theorem reversed_blocks (n L : ℕ) (hn : 1 ≤ n)
    (k : ℕ → ℕ) (b : ℕ → ℤ) (D Q : ℕ → PowerSeries ℤ) (s : ℕ → ℕ)
    (hL : L = if n = 1 then 3 else 6 * n - 4)
    (data : ∀ p, let z := Nat.rec TailState.v₂ (fun _ z => nextState (max n 2) z) p
      k p = (if n = 1 then (if p % 3 = 2 then 1 else 0)
        else (fractionData (max n 2) z).1) ∧
      b p = (if n = 1 then (if p % 3 = 1 then 1 else -1)
        else (fractionData (max n 2) z).2.1) ∧
      D p = (if n = 1 then (if p % 3 = 2 then 1 + X - X ^ 2 else 1 + X)
        else (fractionData (max n 2) z).2.2))
    (s0 : s 0 = 0) (ss : ∀ p, s (p + 1) = s p + k p + 1)
    (qzero : Q 0 = 1) (qone : Q 1 = D 0)
    (qstep : ∀ p, Q (p + 2) = D (p + 1) * Q (p + 1) -
      C (b (p + 1)) * X ^ (k p + k (p + 1) + 2) * Q p)
    (support : ∀ p r, s p < r → coeff r (Q p) = 0) :
    let ν := if n % 2 = 0 then 1 else 2
    let R := transferPrefix (reversedStep k b D) L ^ ν
    R.map constantCoeff = 1 ∧ ∀ K : ℕ, 1 ≤ K →
      let p := (K * ν) * L
      R ^ K *ᵥ ![1, 0] = ![reverseAt (s p) (Q p), reverseAt (s (p - 1)) (Q (p - 1))] := by
  classical
  obtain ⟨hpos, hk, hb, hd, _, _, _, _, hsupport, hword⟩ :=
    source_period n L hn k b D hL data
  let B := reversedStep k b D
  have period (p : ℕ) : B (p + L) = B p := by simp only [B, reversedStep, hk, hb, hd]
  have qrec (p : ℕ) : reverseAt (s (p + 2)) (Q (p + 2)) =
      reverseAt (k (p + 1) + 1) (D (p + 1)) * reverseAt (s (p + 1)) (Q (p + 1)) -
        C (b (p + 1)) * reverseAt (s p) (Q p) := by
    have h1 := ss p
    have h2 := ss (p + 1)
    rw [show p + 1 + 1 = p + 2 by omega] at h2
    rw [qstep, reverse_sub,
      show s (p + 2) = (k (p + 1) + 1) + s (p + 1) by omega,
      reverse_mul _ _ _ _ (hsupport (p + 1)) (support (p + 1))]
    rw [show (k (p + 1) + 1) + s (p + 1) =
      (k p + k (p + 1) + 2) + s p by omega, reverse_shift]
  have state : ∀ p, transferPrefix B p *ᵥ ![1, 0] =
      ![reverseAt (s p) (Q p), if p = 0 then 0 else reverseAt (s (p - 1)) (Q (p - 1))] := by
    intro p
    induction p with
    | zero =>
      have hr : reverseAt 0 (1 : PowerSeries ℤ) = 1 := by
        ext r; simp [reverse_coeff, coeff_one]
      simp [transferPrefix, s0, qzero, hr]
    | succ p ih =>
      change (B p * transferPrefix B p) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ih]
      cases p with
      | zero =>
        have hs1 : s 1 = k 0 + 1 := by simpa [s0] using ss 0
        funext i; fin_cases i <;>
          simp [B, reversedStep, hs1, qone, qzero, s0, reverseAt,
            Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      | succ p =>
        funext i; fin_cases i <;>
          simp [B, reversedStep, qrec, Matrix.mulVec, dotProduct,
            Fin.sum_univ_two, sub_eq_add_neg]
  let step (z a : ℤ × ℤ) : ℤ × ℤ := (a.1 * z.1 - a.2 * z.2, z.1)
  let word (p : ℕ) := List.ofFn (fun i : Fin p => (coeff (k i + 1) (D i), b i))
  have rc (d : ℕ) (f : PowerSeries ℤ) :
      constantCoeff (reverseAt d f) = coeff d f := by
    rw [← coeff_zero_eq_constantCoeff_apply, reverse_coeff]
    simp
  have fold (p : ℕ) (z : ℤ × ℤ) :
      (transferPrefix B p).map constantCoeff *ᵥ ![z.1, z.2] =
        ![(word p).foldl step z |>.1, (word p).foldl step z |>.2] := by
    induction p with
    | zero =>
      change (1 : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)).map constantCoeff *ᵥ _ = _
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
      simp [word]
    | succ p ih =>
      change (B p * transferPrefix B p).map constantCoeff *ᵥ _ = _
      rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, ih]
      have hw : word (p + 1) = (word p).concat (coeff (k p + 1) (D p), b p) := by
        simp only [word, List.ofFn_succ']; rfl
      rw [hw, List.concat_eq_append, List.foldl_concat]
      funext i; fin_cases i <;>
        simp [B, reversedStep, Matrix.map_apply, rc,
          step, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]
  have evalM : (transferPrefix B L).map constantCoeff = 1 := by
    have act (z : ℤ × ℤ) : (word L).foldl step z = z := by
      dsimp only [word]
      rw [hword]
      by_cases hn1 : n = 1
      · simp only [ite_eq_left hn1, List.foldl_cons, List.foldl_nil, step]
        ext <;> ring
      · rw [ite_eq_right hn1]
        exact MetallicHankelTransfer.top_word_identity n (by omega) z
    have hv (z : ℤ × ℤ) := fold L z
    simp only [act] at hv
    ext i j
    fin_cases j
    · have h := congrFun (hv (1, 0)) i
      fin_cases i <;> simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
    · have h := congrFun (hv (0, 1)) i
      fin_cases i <;> simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  dsimp only
  let ν := if n % 2 = 0 then 1 else 2
  refine ⟨?_, ?_⟩
  · change (transferPrefix B L ^ ν).map constantCoeff = 1
    dsimp only [ν]
    split_ifs <;> simp [pow_two, Matrix.map_mul, evalM]
  · intro K hK
    have hν : 0 < ν := by dsimp [ν]; split_ifs <;> omega
    have hp : (K * ν) * L ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by omega) hν) hpos)
    have he := state ((K * ν) * L)
    rw [prefix_period B L period, ite_eq_right hp] at he
    have hpow : transferPrefix B L ^ (K * ν) = (transferPrefix B L ^ ν) ^ K := by
      rw [Nat.mul_comm K ν, pow_mul]
    rw [hpow] at he
    exact he

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelBlocks
