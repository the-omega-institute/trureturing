/- GID: D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:148fce9b2a685f895d65e8a92b6e15e15097f5b36b12cbd8570b32957f1bff67
   digest: The OEIS A392208 EGF equation forces coefficient parity with period three. -/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.PowerSeries.Exp
open Module
open scoped TensorProduct
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree
private abbrev F2 := ZMod 2
private abbrev SAlg := SymmetricAlgebra F2 F2
private abbrev Series := WithConv (SAlg →ₗ[F2] F2)
private noncomputable def b : Basis Unit F2 F2 := Basis.singleton Unit F2
private noncomputable def sb : Basis (Unit →₀ Nat) F2 SAlg := b.symmetricAlgebra
private noncomputable def X : SAlg := SymmetricAlgebra.ι F2 F2 1
private noncomputable def coeff (f : Series) (n : Nat) : F2 := f.ofConv (X ^ n)
example : b () = 1 := by simp [b]
private theorem sb_single (n : Nat) : sb (Finsupp.single () n) = X ^ n := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  rw [show X = SymmetricAlgebra.ι F2 F2 (b ()) by simp [X, b], map_pow,
    SymmetricAlgebra.equivMvPolynomial_ι_apply]
  simp [sb, b, Basis.symmetricAlgebra, MvPolynomial.basisMonomials,
    MvPolynomial.X_pow_eq_monomial]; rfl
private noncomputable def seriesLinear (s : Nat → F2) : SAlg →ₗ[F2] F2 := sb.constr F2 (fun p => s (p ()))
example (s : Nat → F2) (n : Nat) : seriesLinear s (X ^ n) = s n := by rw [← sb_single n]; simp [seriesLinear]
private theorem coeff_mul (f g : Series) (n : Nat) :
    coeff (f * g) n = ∑ k ∈ Finset.range (n + 1), n.choose k * coeff f k * coeff g (n - k) := by
  simp only [coeff, LinearMap.convMul_apply]; rw [Bialgebra.comul_pow]
  simp only [X, SymmetricAlgebra.comul_ι]; rw [add_pow]; simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_pow, mul_one, one_mul]
  rw [mul_comm _ (n.choose k : TensorProduct F2 SAlg SAlg)]
  have hcast : (n.choose k : TensorProduct F2 SAlg SAlg) =
      algebraMap F2 (TensorProduct F2 SAlg SAlg) (n.choose k : F2) :=
    (map_natCast (algebraMap F2 (TensorProduct F2 SAlg SAlg)) _).symm
  rw [hcast, ← Algebra.smul_def, map_smul, map_smul]
  simp [TensorProduct.map_tmul, LinearMap.mul'_apply, mul_assoc]
private theorem series_ext {f g : Series} (h : ∀ n, coeff f n = coeff g n) : f = g := by
  ext p
  have hfg : f.ofConv = g.ofConv := by
    apply sb.ext; intro i
    have hi : i = Finsupp.single () (i ()) := by
      ext u; simpa using congrArg i (Subsingleton.elim u ())
    rw [hi, sb_single]; exact h _
  exact LinearMap.congr_fun hfg p
/-- Binomial convolution for the exponential generating function in OEIS A392208 (2026-01-24). -/
def egfMul {R : Type*} [CommSemiring R] (f g : Nat → R) (n : Nat) : R := ∑ k ∈ Finset.range (n + 1), n.choose k * f k * g (n - k)
private theorem coeff_mul_egf (f g : Series) (n : Nat) :
    coeff (f * g) n = egfMul (coeff f) (coeff g) n := coeff_mul f g n
private def egfOne {R : Type*} [CommSemiring R] (n : Nat) : R := if n = 0 then 1 else 0
/-- Iterated binomial convolution for the exponential generating function in OEIS A392208 (2026-01-24). -/
def egfPow {R : Type*} [CommSemiring R] (f : Nat → R) : Nat → Nat → R
  | 0 => egfOne
  | m + 1 => egfMul f (egfPow f m)
private theorem egfMul_congr_at {R : Type*} [CommSemiring R] {f f' g g' : Nat → R} {n : Nat}
    (hf : ∀ k ≤ n, f k = f' k) (hg : ∀ k ≤ n, g k = g' k) : egfMul f g n = egfMul f' g' n := by
  apply Finset.sum_congr rfl; intro k hk
  have hk' : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  rw [hf k hk', hg (n - k) (Nat.sub_le n k)]
private theorem egfPow_congr_at {R : Type*} [CommSemiring R] {f f' : Nat → R} {m n : Nat}
    (hf : ∀ k ≤ n, f k = f' k) : egfPow f m n = egfPow f' m n := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
      apply egfMul_congr_at hf; intro k hk
      exact ih (fun j hj => hf j (hj.trans hk))
/-- The next coefficient expression used by the recursive table for OEIS A392208 (2026-01-24). -/
def recurrenceRhs (s : Nat → Int) (n : Nat) : Int := egfPow (fun j => s (j + 1)) 5 n +
  3 * egfMul (egfMul s (egfPow (fun j => s (j + 1)) 3)) (fun j => if j < n then s (j + 2) else 0) n
/-- The finite recursive coefficient table used to define the integer sequence for OEIS A392208 (2026-01-24). -/
def table : Nat → List Int
  | 0 => [0, 1]
  | n + 1 =>
      let xs := table n; xs ++ [recurrenceRhs (fun k => xs.getD k 0) n]
/-- The recursively generated integer sequence from the equation in OEIS A392208 (2026-01-24). -/
def a : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => (table (n + 1)).getD (n + 2) 0
/-- The initial residue triple of the recurrence-defined sequence modulo two. -/
theorem initial_residues_mod_two :
    ((a 0 : ZMod 2) = 0 ∧ ((a 1 : ZMod 2) = 1 ∧ (a 2 : ZMod 2) = 1)) := by decide
@[simp] private theorem table_length (n : Nat) : (table n).length = n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table, ih, Nat.add_assoc]
private theorem table_getD_eq_a {n k : Nat} (hk : k < n + 2) :
    (table n).getD k 0 = a k := by
  induction n with
  | zero =>
      have hk0 : k = 0 ∨ k = 1 := by omega
      rcases hk0 with rfl | rfl <;> rfl
  | succ n ih =>
      by_cases hold : k < n + 2
      · rw [table, List.getD_append (table n) _ 0 k (by simpa [table_length] using hold)]; exact ih hold
      · have hkeq : k = n + 2 := by omega
        subst k; rfl
@[simp] private theorem a_zero : a 0 = 0 := rfl
@[simp] private theorem a_one : a 1 = 1 := rfl
private def secondPrefix (n : Nat) (j : Nat) : Int := if j < n then a (j + 2) else 0
private theorem a_recurrence_truncated (n : Nat) :
    a (n + 2) = egfPow (fun j => a (j + 1)) 5 n + 3 * egfMul (egfMul a (egfPow (fun j => a (j + 1)) 3)) (secondPrefix n) n := by
  change (table (n + 1)).getD (n + 2) 0 = _; rw [table, List.getD_append_right]
  · rw [table_length, Nat.sub_self]
    change recurrenceRhs (fun k => (table n).getD k 0) n = _; unfold recurrenceRhs
    congr 1
    · apply egfPow_congr_at; intro k hk; apply table_getD_eq_a; omega
    · congr 1; apply egfMul_congr_at
      · intro k hk
        apply egfMul_congr_at
        · intro j hj; apply table_getD_eq_a; omega
        · intro j hj; apply egfPow_congr_at; intro i hi; apply table_getD_eq_a; omega
      · intro k hk
        simp only [secondPrefix]; by_cases hkn : k < n
        · rw [if_pos hkn, if_pos hkn]; apply table_getD_eq_a; omega
        · rw [if_neg hkn, if_neg hkn]
  · simp [table_length]
private theorem restore_second_derivative_int (n : Nat) :
    egfMul (egfMul a (egfPow (fun j => a (j + 1)) 3)) (secondPrefix n) n = egfMul (egfMul a (egfPow (fun j => a (j + 1)) 3)) (fun j => a (j + 2)) n := by
  unfold egfMul; apply Finset.sum_congr rfl; intro k hk
  have hk_le : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  by_cases hk0 : k = 0
  · subst k; simp [a_zero]
  · have hsub : n - k < n := Nat.sub_lt (by omega) (by omega)
    simp [secondPrefix, hsub]
/-- The triangular integer recurrence extracted from the ODE for OEIS A392208 (2026-01-24). -/
theorem a_recurrence (n : Nat) :
    a (n + 2) = egfPow (fun j => a (j + 1)) 5 n + 3 * egfMul (egfMul a (egfPow (fun j => a (j + 1)) 3)) (fun j => a (j + 2)) n := by rw [a_recurrence_truncated, restore_second_derivative_int]
example : a 0 = 0 := by decide
example : a 1 = 1 := by decide
example : a 2 = 1 := by decide
example : a 3 = 8 := by decide
example : a 4 = 129 := by decide
example : a 5 = 3171 := by decide
example : a 6 = 105252 := by decide
example : a 7 = 4408983 := by decide
example : a 8 = 223281351 := by decide
example : a 9 = 13270085748 := by decide
example : a 10 = 905661982179 := by decide
private noncomputable def seriesOf (s : Nat → F2) : Series := WithConv.toConv (seriesLinear s)
@[simp] private theorem coeff_seriesOf (s : Nat → F2) (n : Nat) : coeff (seriesOf s) n = s n := by rw [coeff, seriesOf, WithConv.ofConv_toConv, ← sb_single]; simp [seriesLinear]
private theorem coeff_one (n : Nat) : coeff (1 : Series) n = egfOne n := by
  cases n with
  | zero => simp [coeff, egfOne, LinearMap.convOne_apply]
  | succ n => simp [coeff, egfOne, LinearMap.convOne_apply, X, Bialgebra.counit_mul]
private theorem coeff_pow (f : Series) (m n : Nat) : coeff (f ^ m) n = egfPow (coeff f) m n := by
  induction m generalizing n with
  | zero => simpa [egfPow] using coeff_one n
  | succ m ih =>
      rw [pow_succ', coeff_mul]; unfold egfPow egfMul
      apply Finset.sum_congr rfl; intro k hk; rw [ih]
private theorem intCast_egfMul (f g : Nat → Int) (n : Nat) :
    ((egfMul f g n : Int) : F2) = egfMul (fun k => (f k : F2)) (fun k => (g k : F2)) n := by simp [egfMul]
private theorem intCast_egfPow (f : Nat → Int) (m n : Nat) :
    ((egfPow f m n : Int) : F2) = egfPow (fun k => (f k : F2)) m n := by
  induction m generalizing n with
  | zero => simp [egfPow, egfOne]
  | succ m ih =>
      rw [egfPow, intCast_egfMul, egfPow]; apply egfMul_congr_at
      · intro k hk; rfl
      · intro k hk; exact ih k
private theorem restore_second_derivative (n : Nat) :
    egfMul (egfMul (fun j => (a j : F2)) (egfPow (fun j => (a (j + 1) : F2)) 3)) (fun j => (secondPrefix n j : F2)) n =
      egfMul (egfMul (fun j => (a j : F2)) (egfPow (fun j => (a (j + 1) : F2)) 3)) (fun j => (a (j + 2) : F2)) n := by
  unfold egfMul; apply Finset.sum_congr rfl; intro k hk
  have hk_le : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  by_cases hk0 : k = 0
  · subst k; simp [egfMul, a_zero]
  · have hsub : n - k < n := Nat.sub_lt (by omega) (by omega)
    simp [secondPrefix, hsub]
private theorem mod2_recurrence (n : Nat) :
    (a (n + 2) : F2) = egfPow (fun j => (a (j + 1) : F2)) 5 n + egfMul (egfMul (fun j => (a j : F2)) (egfPow (fun j => (a (j + 1) : F2)) 3)) (fun j => (a (j + 2) : F2)) n := by
  have h := congrArg (fun z : Int => (z : F2)) (a_recurrence_truncated n)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] at h; rw [intCast_egfPow, intCast_egfMul] at h
  have hinner : ∀ k, ((egfMul a (egfPow (fun j => a (j + 1)) 3) k : Int) : F2) =
      egfMul (fun j => (a j : F2)) (egfPow (fun j => (a (j + 1) : F2)) 3) k := by
    intro k; rw [intCast_egfMul]
    apply egfMul_congr_at
    · intro j hj; rfl
    · intro j hj; exact intCast_egfPow (fun i => a (i + 1)) 3 j
  have houter : egfMul (fun k => ((egfMul a (egfPow (fun j => a (j + 1)) 3) k : Int) : F2)) (fun k => (secondPrefix n k : F2)) n =
      egfMul (egfMul (fun j => (a j : F2)) (egfPow (fun j => (a (j + 1) : F2)) 3)) (fun k => (secondPrefix n k : F2)) n := by
    apply egfMul_congr_at
    · intro k hk; exact hinner k
    · intro k hk; rfl
  rw [houter] at h
  have hthree : (3 : F2) = 1 := by decide
  rw [hthree, one_mul, restore_second_derivative] at h; exact h
private noncomputable def shift (f : Series) : Series := WithConv.toConv (f.ofConv.comp (LinearMap.mulLeft F2 X))
@[simp] private theorem shift_apply (f : Series) (p : SAlg) : (shift f).ofConv p = f.ofConv (X * p) := rfl
@[simp] private theorem coeff_shift (f : Series) (n : Nat) : coeff (shift f) n = coeff f (n + 1) := by simp [coeff, shift_apply, pow_succ']
private theorem shift_mul (f g : Series) : shift (f * g) = shift f * g + f * shift g := by
  ext p; rw [shift_apply, LinearMap.convMul_apply, Bialgebra.comul_mul]
  simp only [X, SymmetricAlgebra.comul_ι]
  change _ = (LinearMap.mul' F2 F2) ((TensorProduct.map (shift f).ofConv g.ofConv) (Coalgebra.comul (R := F2) p)) +
    (LinearMap.mul' F2 F2) ((TensorProduct.map f.ofConv (shift g).ofConv) (Coalgebra.comul (R := F2) p))
  generalize hq : Coalgebra.comul (R := F2) p = q at *; clear hq p
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [add_mul, shift, X, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => (simp_all [mul_add] ; abel)
private theorem exists_eq_counit_add_X_mul (p : SAlg) : ∃ q : SAlg, p = algebraMap F2 SAlg (Coalgebra.counit (R := F2) p) + X * q := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap r => exact ⟨0, by simp⟩
  | ι x =>
      refine ⟨algebraMap F2 SAlg x, ?_⟩; rw [SymmetricAlgebra.counit_ι]
      simp only [map_zero, zero_add]
      calc
        SymmetricAlgebra.ι F2 F2 x = SymmetricAlgebra.ι F2 F2 (x • (1 : F2)) := by simp
        _ = x • X := by simpa [X] using (SymmetricAlgebra.ι F2 F2).map_smul x (1 : F2)
        _ = X * algebraMap F2 SAlg x := by rw [mul_comm, Algebra.smul_def]
  | mul x y hx hy =>
      obtain ⟨u, hu⟩ := hx; obtain ⟨v, hv⟩ := hy
      refine ⟨algebraMap F2 SAlg (Coalgebra.counit (R := F2) x) * v +
        algebraMap F2 SAlg (Coalgebra.counit (R := F2) y) * u + X * u * v, ?_⟩
      calc
        x * y = (algebraMap F2 SAlg (Coalgebra.counit (R := F2) x) + X * u) * (algebraMap F2 SAlg (Coalgebra.counit (R := F2) y) + X * v) := congrArg₂ (· * ·) hu hv
        _ = algebraMap F2 SAlg (Coalgebra.counit (R := F2) x * Coalgebra.counit (R := F2) y) +
            X * (algebraMap F2 SAlg (Coalgebra.counit (R := F2) x) * v +
              algebraMap F2 SAlg (Coalgebra.counit (R := F2) y) * u + X * u * v) := by
          rw [map_mul]; ring
        _ = algebraMap F2 SAlg (Coalgebra.counit (R := F2) (x * y)) +
            X * (algebraMap F2 SAlg (Coalgebra.counit (R := F2) x) * v +
              algebraMap F2 SAlg (Coalgebra.counit (R := F2) y) * u + X * u * v) := by rw [Bialgebra.counit_mul]
  | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx; obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      calc
        x + y = (algebraMap F2 SAlg (Coalgebra.counit (R := F2) x) + X * u) + (algebraMap F2 SAlg (Coalgebra.counit (R := F2) y) + X * v) := congrArg₂ (· + ·) hu hv
        _ = algebraMap F2 SAlg (Coalgebra.counit (R := F2) x + Coalgebra.counit (R := F2) y) + X * (u + v) := by rw [map_add]; ring
        _ = algebraMap F2 SAlg (Coalgebra.counit (R := F2) (x + y)) + X * (u + v) := by
          congr 1; exact congrArg (algebraMap F2 SAlg) (map_add (Coalgebra.counit (R := F2)) x y).symm
private theorem eq_algebraMap_eval_one_of_shift_eq_zero (f : Series) (hf : shift f = 0) :
    f = algebraMap F2 Series (f.ofConv 1) := by
  ext p; obtain ⟨q, hp⟩ := exists_eq_counit_add_X_mul p
  have hxq : f.ofConv (X * q) = 0 := by
    have h := congrArg (fun s : Series => s.ofConv q) hf
    simpa [shift_apply] using h
  calc
    f.ofConv p = f.ofConv (algebraMap F2 SAlg (Coalgebra.counit (R := F2) p) + X * q) := congrArg f.ofConv hp
    _ = f.ofConv (algebraMap F2 SAlg (Coalgebra.counit (R := F2) p)) := by rw [map_add, hxq, add_zero]
    _ = Coalgebra.counit (R := F2) p * f.ofConv 1 := by
      rw [show algebraMap F2 SAlg (Coalgebra.counit (R := F2) p) =
          Coalgebra.counit (R := F2) p • (1 : SAlg) by simp [Algebra.smul_def], map_smul]
      rfl
    _ = f.ofConv 1 * Coalgebra.counit (R := F2) p := mul_comm _ _
    _ = (algebraMap F2 Series (f.ofConv 1)).ofConv p := by rw [LinearMap.convAlgebraMap_apply]; simp
private theorem square_collapse (f : Series) : f * f = algebraMap F2 Series (f.ofConv 1 * f.ofConv 1) := by
  have hs : shift (f * f) = 0 := by
    rw [shift_mul]
    have htwo : (2 : Series) = 0 := by
      calc
        (2 : Series) = algebraMap F2 Series (2 : F2) := (map_ofNat (algebraMap F2 Series) 2).symm
        _ = algebraMap F2 Series 0 := congrArg (algebraMap F2 Series) (by decide)
        _ = 0 := map_zero _
    rw [mul_comm (shift f) f, ← two_mul, htwo, zero_mul]
  calc
    f * f = algebraMap F2 Series ((f * f).ofConv 1) := eq_algebraMap_eval_one_of_shift_eq_zero (f * f) hs
    _ = algebraMap F2 Series (f.ofConv 1 * f.ofConv 1) := by
      congr 1; simp [LinearMap.convMul_apply, Algebra.TensorProduct.one_def]
private theorem two_series_eq_zero : (2 : Series) = 0 := by
  calc
    (2 : Series) = algebraMap F2 Series (2 : F2) := (map_ofNat (algebraMap F2 Series) 2).symm
    _ = algebraMap F2 Series 0 := congrArg (algebraMap F2 Series) (by decide)
    _ = 0 := map_zero _
private theorem series_add_self (f : Series) : f + f = 0 := by rw [← two_mul, two_series_eq_zero, zero_mul]
@[simp] private theorem shift_add (f g : Series) : shift (f + g) = shift f + shift g := rfl
@[simp] private theorem shift_one : shift (1 : Series) = 0 := by ext p; simp [shift_apply, X, Bialgebra.counit_mul, LinearMap.convOne_apply]
private theorem period_three_series_of_ode (A : Series) (hA0 : A.ofConv 1 = 0)
    (hA1 : (shift A).ofConv 1 = 1) (hA2 : (shift (shift A)).ofConv 1 = 1)
    (hode : (1 + A * (shift A) ^ 3) * shift (shift A) = (shift A) ^ 5) : shift (shift (shift A)) = A := by
  let B : Series := shift A; let C : Series := shift B
  change B.ofConv 1 = 1 at hA1; change C.ofConv 1 = 1 at hA2
  change (1 + A * B ^ 3) * C = B ^ 5 at hode
  have hAsq : A * A = 0 := by rw [square_collapse A, hA0, zero_mul, map_zero]
  have hBsq : B * B = 1 := by rw [square_collapse B, hA1, one_mul, map_one]
  have hCsq : C * C = 1 := by rw [square_collapse C, hA2, one_mul, map_one]
  have hB3 : B ^ 3 = B := by
    calc
      B ^ 3 = B * (B * B) := by ring
      _ = B := by rw [hBsq, mul_one]
  have hB5 : B ^ 5 = B := by
    calc
      B ^ 5 = B * (B * B) * (B * B) := by ring
      _ = B := by rw [hBsq, mul_one, mul_one]
  rw [hB3, hB5] at hode; have hd := congrArg shift hode
  rw [shift_mul, shift_add, shift_one, zero_add, shift_mul] at hd
  change ((B * B + A * C) * C + (1 + A * B) * shift C) = C at hd
  have hfirst : (B * B + A * C) * C = C + A := by
    calc
      (B * B + A * C) * C = (1 + A * C) * C := by rw [hBsq]
      _ = C + A * (C * C) := by ring
      _ = C + A := by rw [hCsq, mul_one]
  rw [hfirst] at hd
  have hsum : A + (1 + A * B) * shift C = 0 := by
    calc
      A + (1 + A * B) * shift C = (C + A + (1 + A * B) * shift C) - C := by ring
      _ = C - C := by rw [hd]
      _ = 0 := sub_self C
  have hder : (1 + A * B) * shift C = A := by
    have hAA := series_add_self A; linear_combination hsum - hAA
  have hABsq : (A * B) * (A * B) = 0 := by
    calc
      (A * B) * (A * B) = (A * A) * (B * B) := by ring
      _ = 0 := by rw [hAsq, zero_mul]
  have hfactorSq : (1 + A * B) * (1 + A * B) = 1 := by
    calc
      (1 + A * B) * (1 + A * B) = 1 + ((A * B) + (A * B)) + (A * B) * (A * B) := by ring
      _ = 1 := by rw [series_add_self, hABsq, add_zero, add_zero]
  have hfactorA : (1 + A * B) * A = A := by
    calc
      (1 + A * B) * A = A + (A * A) * B := by ring
      _ = A := by rw [hAsq, zero_mul, add_zero]
  change shift C = A
  calc
    shift C = 1 * shift C := by rw [one_mul]
    _ = ((1 + A * B) * (1 + A * B)) * shift C := by rw [hfactorSq]
    _ = (1 + A * B) * ((1 + A * B) * shift C) := by ring
    _ = (1 + A * B) * A := by rw [hder]
    _ = A := hfactorA
private theorem coefficient_zero_iff_three_dvd_of_ode (A : Series) (hA0 : A.ofConv 1 = 0)
    (hA1 : (shift A).ofConv 1 = 1) (hA2 : (shift (shift A)).ofConv 1 = 1)
    (hode : (1 + A * (shift A) ^ 3) * shift (shift A) = (shift A) ^ 5) : ∀ n, coeff A n = 0 ↔ 3 ∣ n := by
  have hperiod := congrArg (fun f : Series => fun n => coeff f n) (period_three_series_of_ode A hA0 hA1 hA2 hode)
  have hc0 : coeff A 0 = 0 := by simpa [coeff] using hA0
  have hc1 : coeff A 1 = 1 := by simpa [coeff, shift_apply] using hA1
  have hc2 : coeff A 2 = 1 := by simpa [coeff, shift_apply, pow_two] using hA2
  intro n
  have hp : ∀ r q, coeff A (r + 3 * q) = coeff A r := by
    intro r q; induction q with
    | zero => simp
    | succ q ih =>
        rw [show r + 3 * (q + 1) = (r + 3 * q) + 3 by omega]
        calc
          coeff A ((r + 3 * q) + 3) = coeff A (r + 3 * q) := by
            have hh := congrFun hperiod (r + 3 * q); simp only [coeff_shift] at hh
            convert hh using 1 <;> omega
          _ = coeff A r := ih
  have hn : n % 3 + 3 * (n / 3) = n := Nat.mod_add_div n 3
  have hcoeff : coeff A n = coeff A (n % 3) := by
    calc
      coeff A n = coeff A (n % 3 + 3 * (n / 3)) := congrArg (coeff A) hn.symm
      _ = coeff A (n % 3) := hp (n % 3) (n / 3)
  rw [hcoeff, Nat.dvd_iff_mod_eq_zero]
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have := Nat.mod_lt n (by decide : 0 < 3); omega
  rcases hr with hr | hr | hr
  · simp [hr, hc0]
  · simp [hr, hc1]
  · simp [hr, hc2]
private noncomputable def Aseries : Series := seriesOf (fun n => (a n : F2))
@[simp] private theorem coeff_Aseries (n : Nat) : coeff Aseries n = (a n : F2) := by
  simp [Aseries]
private theorem recurrence_series_ode : (1 + Aseries * (shift Aseries) ^ 3) * shift (shift Aseries) = (shift Aseries) ^ 5 := by
  let B : Series := shift Aseries; let C : Series := shift B; let T : Series := Aseries * B ^ 3 * C
  have hAcoeff : coeff Aseries = fun j => (a j : F2) := by
    funext j; exact coeff_Aseries j
  have hBcoeff : coeff B = fun j => (a (j + 1) : F2) := by
    funext j; simp [B, coeff_shift]
  have hCcoeff : coeff C = fun j => (a (j + 2) : F2) := by
    funext j; simp [C, B, coeff_shift, Nat.add_assoc]
  have hB3coeff : coeff (B ^ 3) = egfPow (fun j => (a (j + 1) : F2)) 3 := by
    funext j; rw [coeff_pow, hBcoeff]
  have hABcoeff : coeff (Aseries * B ^ 3) = egfMul (fun j => (a j : F2)) (egfPow (fun j => (a (j + 1) : F2)) 3) := by
    funext j; rw [coeff_mul_egf, hAcoeff, hB3coeff]
  have hrec : C = B ^ 5 + T := by
    apply series_ext; intro n
    change coeff C n = coeff (B ^ 5) n + coeff (Aseries * B ^ 3 * C) n
    rw [coeff_pow, coeff_mul_egf, hBcoeff, hABcoeff, hCcoeff]
    exact mod2_recurrence n
  change (1 + Aseries * B ^ 3) * C = B ^ 5
  calc
    (1 + Aseries * B ^ 3) * C = C + T := by simp [T]; ring
    _ = (B ^ 5 + T) + T := congrArg (fun z => z + T) hrec
    _ = B ^ 5 := by rw [add_assoc, series_add_self, add_zero]
private theorem recurrence_series_period_three : shift (shift (shift Aseries)) = Aseries := by
  apply period_three_series_of_ode Aseries
  · simpa [coeff] using (show coeff Aseries 0 = 0 by simp)
  · simpa [coeff] using (show coeff (shift Aseries) 0 = 1 by simp [coeff_shift])
  · have ha2 : a 2 = 1 := by decide
    have hcoeff := coeff_Aseries 2
    simpa [coeff, pow_two, ha2] using hcoeff
  · exact recurrence_series_ode
/-- The recurrence-defined coefficients of OEIS A392208 (2026-01-24) have period three modulo two. -/
theorem recurrence_coefficient_period_three (n : Nat) : a (n + 3) ≡ a n [ZMOD 2] := by
  have h := congrArg (fun f : Series => coeff f n) recurrence_series_period_three
  have hz : (a (n + 3) : F2) = (a n : F2) := by
    simpa [coeff_shift, Nat.add_assoc] using h
  rw [Int.modEq_iff_dvd]; exact (ZMod.intCast_eq_intCast_iff_dvd_sub (a (n + 3)) (a n) 2).mp hz
private theorem recurrence_parity_iff_three_dvd (n : Nat) : Even (a n) ↔ 3 ∣ n := by
  have hzero : ∀ m, coeff Aseries m = 0 ↔ 3 ∣ m :=
    coefficient_zero_iff_three_dvd_of_ode Aseries
      (by simpa [coeff] using (show coeff Aseries 0 = 0 by simp))
      (by simpa [coeff] using (show coeff (shift Aseries) 0 = 1 by simp [coeff_shift]))
      (by
        have ha2 : a 2 = 1 := by decide
        have hcoeff := coeff_Aseries 2
        simpa [coeff, pow_two, ha2] using hcoeff)
      recurrence_series_ode
  constructor
  · intro he
    have hd : (2 : Int) ∣ a n := even_iff_two_dvd.mp he
    have hz : (a n : F2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 2).mpr hd
    exact (hzero n).mp (by simpa using hz)
  · intro hd
    apply even_iff_two_dvd.mpr; apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 2).mp
    have hz := (hzero n).mpr hd
    simpa using hz
private theorem recurrence_defined_parity_conjecture : ∀ n ≥ 1, Even (a n) ↔ 3 ∣ n := by intro n hn; exact recurrence_parity_iff_three_dvd n
/-- The formal power-series equation stated in OEIS A392208 (2026-01-24). -/
def ExpDefines (A : PowerSeries ℚ) : Prop := PowerSeries.constantCoeff A = 0 ∧ PowerSeries.derivative ℚ A =
  (PowerSeries.exp ℚ).subst (A * (PowerSeries.derivative ℚ A) ^ 3)
/-- Differentiating the equation in OEIS A392208 (2026-01-24) yields its autonomous ODE. -/
theorem exp_definition_implies_ode {A : PowerSeries ℚ} (h : ExpDefines A) :
    (1 - 3 * A * (PowerSeries.derivative ℚ A) ^ 3) * PowerSeries.derivative ℚ (PowerSeries.derivative ℚ A) = (PowerSeries.derivative ℚ A) ^ 5 := by
  rcases h with ⟨hA0, hexp⟩; let B : PowerSeries ℚ := PowerSeries.derivative ℚ A
  let U : PowerSeries ℚ := A * B ^ 3
  have hU0 : PowerSeries.constantCoeff U = 0 := by simp [U, hA0]
  have hsubst : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero' hU0
  have hd := congrArg (PowerSeries.derivative ℚ) hexp
  change PowerSeries.derivative ℚ B = PowerSeries.derivative ℚ ((PowerSeries.exp ℚ).subst U) at hd
  rw [PowerSeries.derivative_subst hsubst, PowerSeries.derivative_exp] at hd
  have hUder : PowerSeries.derivative ℚ U = B ^ 4 + 3 * A * B ^ 2 * PowerSeries.derivative ℚ B := by
    rw [show U = A * B ^ 3 by rfl, (PowerSeries.derivative ℚ).leibniz,
      PowerSeries.derivative_pow]
    simp only [smul_eq_mul]; change A * (3 * B ^ (3 - 1) * PowerSeries.derivative ℚ B) + B ^ 3 * B = _; ring
  rw [hUder, ← hexp] at hd
  change (1 - 3 * A * B ^ 3) * PowerSeries.derivative ℚ B = B ^ 5
  linear_combination hd
/-- The rational exponential generating function used for OEIS A392208 (2026-01-24). -/
def egfSeries (s : Nat → ℚ) : PowerSeries ℚ := PowerSeries.mk (fun n => s n / Nat.factorial n)
@[simp] private theorem coeff_egfSeries (s : Nat → ℚ) (n : Nat) : PowerSeries.coeff n (egfSeries s) = s n / Nat.factorial n := by simp [egfSeries]
private theorem egfSeries_injective : Function.Injective egfSeries := by
  intro f g h; funext n; have hn := congrArg (PowerSeries.coeff n) h
  simp only [coeff_egfSeries] at hn
  exact (div_left_inj' (by positivity : ((Nat.factorial n : Nat) : ℚ) ≠ 0)).mp hn
@[simp] private theorem egfSeries_add (f g : Nat → ℚ) : egfSeries (fun n => f n + g n) = egfSeries f + egfSeries g := by ext n; simp [egfSeries, add_div]
@[simp] private theorem egfSeries_smul_nat (m : Nat) (f : Nat → ℚ) :
    egfSeries (fun n => m * f n) = m * egfSeries f := by
  ext n
  rw [show (m : PowerSeries ℚ) = PowerSeries.C (m : ℚ) by
    rw [PowerSeries.C_eq_algebraMap, map_natCast]]
  rw [PowerSeries.coeff_C_mul]; simp [egfSeries, mul_div_assoc]
@[simp] private theorem egfSeries_smul_q (q : ℚ) (f : Nat → ℚ) :
    egfSeries (fun n => q * f n) = PowerSeries.C q * egfSeries f := by ext n; rw [PowerSeries.coeff_C_mul]; simp [egfSeries, mul_div_assoc]
private theorem egfSeries_mul (f g : Nat → ℚ) : egfSeries (egfMul f g) = egfSeries f * egfSeries g := by
  ext n
  rw [coeff_egfSeries, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [egfMul, coeff_egfSeries]; rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro k hk
  have hk_le : k ≤ n := by simpa using Finset.mem_range.mp hk
  have hfac := Nat.choose_mul_factorial_mul_factorial hk_le
  have hfacQ : (n.choose k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ) = (Nat.factorial n : ℚ) := by exact_mod_cast hfac
  field_simp; linear_combination (f k * g (n - k)) * hfacQ
private theorem egfSeries_pow (f : Nat → ℚ) (m : Nat) : egfSeries (egfPow f m) = egfSeries f ^ m := by
  induction m with
  | zero =>
      ext n; cases n <;> simp [egfPow, egfOne, egfSeries]
  | succ m ih => rw [egfPow, egfSeries_mul, ih, pow_succ']
private theorem derivative_egfSeries (f : Nat → ℚ) : PowerSeries.derivative ℚ (egfSeries f) = egfSeries (fun n => f (n + 1)) := by
  ext n; rw [PowerSeries.coeff_derivative]; simp only [coeff_egfSeries]
  rw [Nat.factorial_succ]; push_cast; field_simp
/-- The equation in OEIS A392208 (2026-01-24) forces the first coefficient to be one. -/
theorem exp_definition_derivative_zero {A : PowerSeries ℚ} (h : ExpDefines A) :
    PowerSeries.constantCoeff (PowerSeries.derivative ℚ A) = 1 := by
  rcases h with ⟨hA0, hexp⟩; let B : PowerSeries ℚ := PowerSeries.derivative ℚ A
  let U : PowerSeries ℚ := A * B ^ 3
  have hU0 : PowerSeries.constantCoeff U = 0 := by simp [U, hA0]
  have hsubst : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero' hU0
  have hc := congrArg PowerSeries.constantCoeff hexp
  change PowerSeries.constantCoeff B = PowerSeries.constantCoeff ((PowerSeries.exp ℚ).subst U) at hc
  change MvPowerSeries.constantCoeff B = MvPowerSeries.constantCoeff ((PowerSeries.exp ℚ).subst U) at hc
  have hU0' : MvPowerSeries.constantCoeff U = 0 := hU0
  rw [PowerSeries.constantCoeff_subst hsubst,
    finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hU0', zero_pow hd, smul_zero])] at hc
  change MvPowerSeries.constantCoeff B = 1; simpa using hc
/-- The triangular coefficient recurrence for the ODE from OEIS A392208 (2026-01-24). -/
def EgfOde (s : Nat → ℚ) : Prop := ∀ n, s (n + 2) = egfPow (fun j => s (j + 1)) 5 n +
  3 * egfMul (egfMul s (egfPow (fun j => s (j + 1)) 3)) (fun j => s (j + 2)) n
private def secondPrefixQ (s : Nat → ℚ) (n j : Nat) : ℚ := if j < n then s (j + 2) else 0
private theorem restore_second_derivative_q (s : Nat → ℚ) (h0 : s 0 = 0) (n : Nat) :
    egfMul (egfMul s (egfPow (fun j => s (j + 1)) 3)) (secondPrefixQ s n) n = egfMul (egfMul s (egfPow (fun j => s (j + 1)) 3)) (fun j => s (j + 2)) n := by
  unfold egfMul; apply Finset.sum_congr rfl; intro k hk
  have hk_le : k ≤ n := by simpa using Finset.mem_range.mp hk
  by_cases hk0 : k = 0
  · subst k; simp [egfMul, h0]
  · have hsub : n - k < n := Nat.sub_lt (by omega) (by omega)
    simp [secondPrefixQ, hsub]
private theorem egfOde_truncated {s : Nat → ℚ} (h0 : s 0 = 0) (h : EgfOde s) (n : Nat) :
    s (n + 2) = egfPow (fun j => s (j + 1)) 5 n + 3 * egfMul (egfMul s (egfPow (fun j => s (j + 1)) 3)) (secondPrefixQ s n) n := by rw [h n, restore_second_derivative_q s h0 n]
/-- The ODE recurrence from OEIS A392208 (2026-01-24) has a unique rational solution with initial coefficients zero and one. -/
theorem egfOde_unique {s t : Nat → ℚ}
    (hs0 : s 0 = 0) (hs1 : s 1 = 1) (ht0 : t 0 = 0) (ht1 : t 1 = 1)
    (hs : EgfOde s) (ht : EgfOde t) : s = t := by
  funext m; induction m using Nat.strong_induction_on with
  | h m ih =>
      rcases m with (_ | _ | n)
      · exact hs0.trans ht0.symm
      · exact hs1.trans ht1.symm
      · rw [egfOde_truncated hs0 hs n, egfOde_truncated ht0 ht n]
        congr 1
        · apply egfPow_congr_at; intro k hk; exact ih (k + 1) (by omega)
        · congr 1; apply egfMul_congr_at
          · intro k hk
            apply egfMul_congr_at
            · intro j hj; exact ih j (by omega)
            · intro j hj; apply egfPow_congr_at; intro i hi; exact ih (i + 1) (by omega)
          · intro k hk
            simp only [secondPrefixQ]; by_cases hkn : k < n
            · rw [if_pos hkn, if_pos hkn]; exact ih (k + 2) (by omega)
            · rw [if_neg hkn, if_neg hkn]
private theorem intCastQ_egfMul (f g : Nat → Int) (n : Nat) :
    ((egfMul f g n : Int) : ℚ) = egfMul (fun k => (f k : ℚ)) (fun k => (g k : ℚ)) n := by simp [egfMul]
private theorem intCastQ_egfPow (f : Nat → Int) (m n : Nat) :
    ((egfPow f m n : Int) : ℚ) = egfPow (fun k => (f k : ℚ)) m n := by
  induction m generalizing n with
  | zero => simp [egfPow, egfOne]
  | succ m ih =>
      rw [egfPow, intCastQ_egfMul, egfPow]; apply egfMul_congr_at
      · intro k hk; rfl
      · intro k hk; exact ih k
private theorem recurrence_rational_egfOde : EgfOde (fun n => (a n : ℚ)) := by
  intro n
  have h := congrArg (fun z : Int => (z : ℚ)) (a_recurrence n)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] at h
  rw [intCastQ_egfPow] at h
  rw [intCastQ_egfMul] at h
  have hinner : ∀ k,
      ((egfMul a (egfPow (fun j => a (j + 1)) 3) k : Int) : ℚ) =
        egfMul (fun j => (a j : ℚ))
          (egfPow (fun j => (a (j + 1) : ℚ)) 3) k := by
    intro k
    rw [intCastQ_egfMul]
    apply egfMul_congr_at
    · intro j hj
      rfl
    · intro j hj
      exact intCastQ_egfPow (fun i => a (i + 1)) 3 j
  have houter :
      egfMul
          (fun k => ((egfMul a (egfPow (fun j => a (j + 1)) 3) k : Int) : ℚ))
          (fun k => (a (k + 2) : ℚ)) n =
        egfMul
          (egfMul (fun j => (a j : ℚ))
            (egfPow (fun j => (a (j + 1) : ℚ)) 3))
          (fun k => (a (k + 2) : ℚ)) n := by
    apply egfMul_congr_at
    · intro k hk
      exact hinner k
    · intro k hk
      rfl
  rw [houter] at h
  exact h
private theorem egfOde_implies_egfSeries_ode {s : Nat → ℚ} (h : EgfOde s) :
    (1 - 3 * egfSeries s *
          (PowerSeries.derivative ℚ (egfSeries s)) ^ 3) *
          PowerSeries.derivative ℚ (PowerSeries.derivative ℚ (egfSeries s)) =
        (PowerSeries.derivative ℚ (egfSeries s)) ^ 5 := by
  let s1 : Nat → ℚ := fun n => s (n + 1)
  let s2 : Nat → ℚ := fun n => s (n + 2)
  have hseq : s2 = fun n => egfPow s1 5 n +
      3 * egfMul (egfMul s (egfPow s1 3)) s2 n := by
    funext n
    simpa [s1, s2] using h n
  have hseries := congrArg egfSeries hseq
  rw [egfSeries_add, egfSeries_smul_q, egfSeries_mul, egfSeries_mul,
    egfSeries_pow, egfSeries_pow] at hseries
  have hthree : (3 : PowerSeries ℚ) = PowerSeries.C (3 : ℚ) := by
    rw [PowerSeries.C_eq_algebraMap]
    exact (map_natCast (algebraMap ℚ (PowerSeries ℚ)) 3).symm
  rw [← hthree] at hseries
  rw [derivative_egfSeries, derivative_egfSeries]
  change (1 - 3 * egfSeries s * egfSeries s1 ^ 3) * egfSeries s2 =
    egfSeries s1 ^ 5
  linear_combination hseries
private theorem powerSeries_linear_ode_unique
    (U f g : PowerSeries ℚ)
    (h0 : PowerSeries.constantCoeff f = PowerSeries.constantCoeff g)
    (hf : PowerSeries.derivative ℚ f = U * f)
    (hg : PowerSeries.derivative ℚ g = U * g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
      · have hf' := congrArg (PowerSeries.coeff n) hf
        have hg' := congrArg (PowerSeries.coeff n) hg
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hf' hg'
        have hsum :
            (∑ p ∈ Finset.antidiagonal n,
                PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 f) =
              ∑ p ∈ Finset.antidiagonal n,
                PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 g := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [ih p.2 (Finset.Nat.antidiagonal.snd_lt hp)]
        exact mul_right_cancel₀ (by positivity) (hf'.trans (hsum.trans hg'.symm))
private theorem exp_definition_of_ode
    (A : PowerSeries ℚ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hA1 : PowerSeries.constantCoeff (PowerSeries.derivative ℚ A) = 1)
    (hode : (1 - 3 * A * (PowerSeries.derivative ℚ A) ^ 3) *
          PowerSeries.derivative ℚ (PowerSeries.derivative ℚ A) =
        (PowerSeries.derivative ℚ A) ^ 5) : ExpDefines A := by
  let B : PowerSeries ℚ := PowerSeries.derivative ℚ A
  let U : PowerSeries ℚ := A * B ^ 3
  let E : PowerSeries ℚ := (PowerSeries.exp ℚ).subst U
  have hU0 : PowerSeries.constantCoeff U = 0 := by simp [U, hA0]
  have hsubst : PowerSeries.HasSubst U :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hU0
  have hUder : PowerSeries.derivative ℚ U =
      B ^ 4 + 3 * A * B ^ 2 * PowerSeries.derivative ℚ B := by
    rw [show U = A * B ^ 3 by rfl, (PowerSeries.derivative ℚ).leibniz,
      PowerSeries.derivative_pow]
    simp only [smul_eq_mul]
    change A * (3 * B ^ (3 - 1) * PowerSeries.derivative ℚ B) + B ^ 3 * B = _
    ring
  have hBder : PowerSeries.derivative ℚ B =
      PowerSeries.derivative ℚ U * B := by
    rw [hUder]
    change PowerSeries.derivative ℚ B =
      (B ^ 4 + 3 * A * B ^ 2 * PowerSeries.derivative ℚ B) * B
    change (1 - 3 * A * B ^ 3) * PowerSeries.derivative ℚ B = B ^ 5 at hode
    linear_combination hode
  have hEder : PowerSeries.derivative ℚ E =
      PowerSeries.derivative ℚ U * E := by
    change PowerSeries.derivative ℚ ((PowerSeries.exp ℚ).subst U) =
      PowerSeries.derivative ℚ U * (PowerSeries.exp ℚ).subst U
    rw [PowerSeries.derivative_subst hsubst, PowerSeries.derivative_exp]
    ring
  have hE0 : PowerSeries.constantCoeff E = 1 := by
    change MvPowerSeries.constantCoeff ((PowerSeries.exp ℚ).subst U) = 1
    have hU0' : MvPowerSeries.constantCoeff U = 0 := hU0
    rw [PowerSeries.constantCoeff_subst hsubst,
      finsum_eq_single _ 0 (fun d hd => by
        rw [map_pow, hU0', zero_pow hd, smul_zero])]
    simp
  refine ⟨hA0, ?_⟩
  change B = E
  exact powerSeries_linear_ode_unique (PowerSeries.derivative ℚ U) B E
    (hA1.trans hE0.symm) hBder hEder
private theorem egfSeries_ode_implies_egfOde {s : Nat → ℚ}
    (h : (1 - 3 * egfSeries s *
          (PowerSeries.derivative ℚ (egfSeries s)) ^ 3) *
          PowerSeries.derivative ℚ (PowerSeries.derivative ℚ (egfSeries s)) =
        (PowerSeries.derivative ℚ (egfSeries s)) ^ 5) : EgfOde s := by
  let s1 : Nat → ℚ := fun n => s (n + 1)
  let s2 : Nat → ℚ := fun n => s (n + 2)
  have hd1 : PowerSeries.derivative ℚ (egfSeries s) = egfSeries s1 := by
    simpa [s1] using derivative_egfSeries s
  have hd12 : PowerSeries.derivative ℚ (egfSeries s1) =
      egfSeries s2 := by
    simpa [s1, s2, Nat.add_assoc] using derivative_egfSeries s1
  rw [hd1, hd12] at h
  have hrearr : egfSeries s2 =
      (egfSeries s1) ^ 5 + 3 * egfSeries s * (egfSeries s1) ^ 3 * egfSeries s2 := by
    linear_combination h
  have hthree : (3 : PowerSeries ℚ) = PowerSeries.C (3 : ℚ) := by
    rw [PowerSeries.C_eq_algebraMap]
    exact (map_natCast (algebraMap ℚ (PowerSeries ℚ)) 3).symm
  have heq : s2 = fun n => egfPow s1 5 n +
      3 * egfMul (egfMul s (egfPow s1 3)) s2 n := by
    apply egfSeries_injective
    rw [egfSeries_add, egfSeries_smul_q, egfSeries_mul, egfSeries_mul,
      egfSeries_pow, egfSeries_pow]
    rw [← hthree]
    simpa [mul_assoc] using hrearr
  intro n
  simpa [s1, s2] using congrFun heq n
private noncomputable def egfCoeffs (A : PowerSeries ℚ) (n : Nat) : ℚ :=
  Nat.factorial n * PowerSeries.coeff n A
private theorem egfSeries_egfCoeffs (A : PowerSeries ℚ) : egfSeries (egfCoeffs A) = A := by
  ext n
  simp only [coeff_egfSeries, egfCoeffs]
  field_simp
private theorem powerSeries_ode_implies_egfOde {A : PowerSeries ℚ}
    (h : (1 - 3 * A * (PowerSeries.derivative ℚ A) ^ 3) *
          PowerSeries.derivative ℚ (PowerSeries.derivative ℚ A) =
        (PowerSeries.derivative ℚ A) ^ 5) : EgfOde (egfCoeffs A) := by
  apply egfSeries_ode_implies_egfOde
  simpa only [egfSeries_egfCoeffs] using h
private theorem ode_solution_unique (A : PowerSeries ℚ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hA1 : PowerSeries.constantCoeff (PowerSeries.derivative ℚ A) = 1)
    (hode : (1 - 3 * A * (PowerSeries.derivative ℚ A) ^ 3) *
          PowerSeries.derivative ℚ (PowerSeries.derivative ℚ A) =
        (PowerSeries.derivative ℚ A) ^ 5) :
    A = egfSeries (fun n => (a n : ℚ)) := by
  let s : Nat → ℚ := egfCoeffs A
  have hs0 : s 0 = 0 := by
    simpa [s, egfCoeffs, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hA0
  have hs1 : s 1 = 1 := by
    have hA1' := hA1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative] at hA1'
    simpa [s, egfCoeffs] using hA1'
  have hsode : EgfOde s := powerSeries_ode_implies_egfOde hode
  have heq : s = fun n => (a n : ℚ) :=
    egfOde_unique hs0 hs1 (by simp) (by simp) hsode recurrence_rational_egfOde
  calc
    A = egfSeries s := (egfSeries_egfCoeffs A).symm
    _ = egfSeries (fun n => (a n : ℚ)) := congrArg egfSeries heq
/-- The exact EGF predicate used by OEIS A392208 (2026-01-24), including its zero constant term. -/
def OEISDefines (s : Nat → Int) : Prop :=
  ExpDefines (egfSeries (fun n => (s n : ℚ)))
/-- The recurrence-defined sequence satisfies the exact EGF predicate from OEIS A392208 (2026-01-24). -/
theorem a_oeisDefines : OEISDefines a := by
  unfold OEISDefines
  apply exp_definition_of_ode
  · simp [egfSeries]
  · rw [derivative_egfSeries]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, egfSeries]
  · exact egfOde_implies_egfSeries_ode recurrence_rational_egfOde
/-- Every integer sequence satisfying OEIS A392208 (2026-01-24) is the recurrence-defined sequence. -/
theorem oeis_defined_eq_recurrence {s : Nat → Int} (h : OEISDefines s) : s = a := by
  let A : PowerSeries ℚ := egfSeries (fun n => (s n : ℚ))
  have hexp : ExpDefines A := h
  have hA0 : PowerSeries.constantCoeff A = 0 := hexp.1
  have hA1 : PowerSeries.constantCoeff (PowerSeries.derivative ℚ A) = 1 :=
    exp_definition_derivative_zero hexp
  have hode := exp_definition_implies_ode hexp
  have hseries := ode_solution_unique A hA0 hA1 hode
  funext n
  have hn := congrArg (PowerSeries.coeff n) hseries
  simp only [A, coeff_egfSeries] at hn
  have hfac : ((Nat.factorial n : Nat) : ℚ) ≠ 0 := by positivity
  have hcast : (s n : ℚ) = (a n : ℚ) := (div_left_inj' hfac).mp hn
  exact_mod_cast hcast
/-- Every sequence satisfying OEIS A392208 (2026-01-24) has period three modulo two. -/
theorem oeis_coefficient_period_three {s : Nat → Int} (h : OEISDefines s) (n : Nat) :
    s (n + 3) ≡ s n [ZMOD 2] := by
  rw [oeis_defined_eq_recurrence h]
  exact recurrence_coefficient_period_three n
/-- Every integer sequence satisfying OEIS A392208 (2026-01-24) obeys its parity law. -/
theorem parity_conjecture_of_oeisDefines {s : Nat → Int} (h : OEISDefines s) :
    ∀ n ≥ 1, Even (s n) ↔ 3 ∣ n := by
  rw [oeis_defined_eq_recurrence h]
  exact recurrence_defined_parity_conjecture
/-- The recurrence-defined sequence satisfies the parity conjecture stated in OEIS A392208 (2026-01-24). -/
theorem a392208_parity_conjecture (n : Nat) (hn : 1 ≤ n) : Even (a n) ↔ 3 ∣ n := by
  exact parity_conjecture_of_oeisDefines a_oeisDefines n hn
set_option maxHeartbeats 2000000 in
example : table 17 =
    [0, 1, 1, 8, 129, 3171, 105252, 4408983, 223281351, 13270085748,
      905661982179, 69812320196385, 5999337450957816, 568724629221848817,
      58959671016467593233, 6635892489298476577488, 805834151277899880194361,
      105021896272478014882848507, 14621423624844610787449584876] := by
  decide +kernel
set_option maxHeartbeats 2000000 in
example : a 11 = 69812320196385 := by decide +kernel
set_option maxHeartbeats 2000000 in
example : a 12 = 5999337450957816 := by decide +kernel
set_option maxHeartbeats 2000000 in
example : a 13 = 568724629221848817 := by decide +kernel
set_option maxHeartbeats 2000000 in
example : a 14 = 58959671016467593233 := by decide +kernel
set_option maxHeartbeats 2000000 in
example : a 15 = 6635892489298476577488 := by decide +kernel
set_option maxHeartbeats 2000000 in
example : a 16 = 805834151277899880194361 := by decide +kernel
set_option maxHeartbeats 2000000 in
example : a 17 = 105021896272478014882848507 := by decide +kernel
set_option maxHeartbeats 2000000 in
example : a 18 = 14621423624844610787449584876 := by decide +kernel
-- Fidelity witnesses: the sequence domain is inhabited, and the OEIS hypothesis is satisfiable.
example : Nat → Int := a
end D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.initial_residues_mod_two
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.a_recurrence
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.recurrence_coefficient_period_three
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.exp_definition_implies_ode
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.exp_definition_derivative_zero
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.egfOde_unique
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.a_oeisDefines
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.oeis_defined_eq_recurrence
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.oeis_coefficient_period_three
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.parity_conjecture_of_oeisDefines
#print axioms D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree.a392208_parity_conjecture
