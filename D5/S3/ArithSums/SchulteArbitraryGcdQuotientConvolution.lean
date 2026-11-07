/- GID: D5/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution
   generality: I
   mirror-B: D5/B/S3/ArithSums/SchulteArbitraryGcdQuotientConvolution
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Arbitrary complex weights on the A350900 gcd quotient give a totient convolution. -/

import D5.S3.Arith.RoldanCirculantEnergyP2Q3
import D5.S3.ArithSums.SchulteGcdQuotientRowSumConvolution
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.PNat.Basic

open scoped BigOperators
open ArithmeticFunction
namespace D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable def square (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
    f (Nat.gcd i n / Nat.gcd (Nat.gcd i k) n)

noncomputable def H (n : ℕ) : ℂ :=
  ∑ e ∈ n.divisors, (e : ℂ) * (Nat.totient e : ℂ)

private theorem gcd_sum (n : ℕ) (hn : 0 < n) (F : ℕ → ℂ) :
    (∑ j ∈ Finset.range n, F (n.gcd j)) =
      ∑ e ∈ n.divisors, (Nat.totient (n / e) : ℂ) * F e := by
  apply Complex.ext
  · simpa using D5.S3.Arith.RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity n hn
      (fun d => (F d).re)
  · simpa using D5.S3.Arith.RoldanCirculantEnergyP2Q3.sum_gcd_multiplicity n hn
      (fun d => (F d).im)

private theorem sum_periodic (f : ℕ → ℂ) (g q : ℕ) (hf : Function.Periodic f g) :
    ∑ k ∈ Finset.range (q * g), f k =
      (q : ℂ) * ∑ k ∈ Finset.range g, f k := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hblock : ∀ k, f (q * g + k) = f k := by
        intro k
        simpa [Nat.add_comm] using hf.nat_mul q k
      simp_rw [hblock]
      simp [Nat.cast_add, add_mul]

private theorem icc_range (n : ℕ) (f : ℕ → ℂ) (hfn : f 0 = f n) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f k := by
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by ext k; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  have hfull := (Finset.sum_range_succ' f n).symm.trans (Finset.sum_range_succ f n)
  rw [hfn] at hfull
  exact add_right_cancel hfull

private theorem inner (f : ℕ → ℂ) (n g : ℕ) (hgn : g ∣ n) (hg : 0 < g) :
    ∑ k ∈ Finset.range n, f (g / Nat.gcd g k) =
      (n / g : ℕ) * ∑ d ∈ g.divisors, (Nat.totient d : ℂ) * f d := by
  have hp : Function.Periodic (fun k => f (g / Nat.gcd g k)) g :=
    (Nat.periodic_gcd g).comp (fun e => f (g / e))
  calc
    _ = ∑ k ∈ Finset.range ((n / g) * g), f (g / Nat.gcd g k) := by
      rw [Nat.div_mul_cancel hgn]
    _ = ((n / g : ℕ) : ℂ) * ∑ k ∈ Finset.range g, f (g / Nat.gcd g k) :=
      sum_periodic _ g (n / g) hp
    _ = _ := by
      rw [gcd_sum g hg (fun e => f (g / e))]
      congr 1
      exact Nat.sum_div_divisors g (fun d => (Nat.totient d : ℂ) * f d)

private theorem square_range (f : ℕ → ℂ) (n : ℕ) :
    square f n = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
      f (Nat.gcd n i / Nat.gcd (Nat.gcd n i) k) := by
  unfold square
  calc
    _ = ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range n,
          f (Nat.gcd i n / Nat.gcd (Nat.gcd i k) n) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply icc_range
      simp
    _ = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
          f (Nat.gcd i n / Nat.gcd (Nat.gcd i k) n) := by
      apply icc_range
      apply Finset.sum_congr rfl
      intro k hk
      simp [Nat.gcd_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      simp [Nat.gcd_comm, Nat.gcd_left_comm]

noncomputable private def lift (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

private def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
noncomputable private def G (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  (lift f).pmul (phi : ArithmeticFunction ℂ)
noncomputable private def B : ArithmeticFunction ℂ :=
  ((ArithmeticFunction.id.pmul phi : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
noncomputable private def Z : ArithmeticFunction ℂ := (ArithmeticFunction.zeta : ArithmeticFunction ℕ)

private theorem G_apply_pos (f : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    G f n = f n * (Nat.totient n : ℂ) := by
  change (if n = 0 then 0 else f n) * (Nat.totient n : ℂ) = _
  rw [ite_eq_right hn.ne']

private theorem B_apply (n : ℕ) : B n = (n : ℂ) * (Nat.totient n : ℂ) := by
  change ((n * Nat.totient n : ℕ) : ℂ) = _
  exact Nat.cast_mul n (Nat.totient n)

private theorem H_eq (n : ℕ) : H n = (B * Z) n := by
  rw [Z, coe_mul_zeta_apply]
  simp only [H, B_apply]

private theorem inner_AF (f : ℕ → ℂ) (g : ℕ) :
    (∑ d ∈ g.divisors, (Nat.totient d : ℂ) * f d) = (Z * G f) g := by
  rw [Z, coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [G_apply_pos f d (Nat.pos_of_mem_divisors hd), mul_comm]

private theorem square_AF (f : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    square f n = (G f * (B * Z)) n := by
  calc
    square f n = ∑ i ∈ Finset.range n,
        ((n / Nat.gcd n i : ℕ) : ℂ) *
          ∑ d ∈ (Nat.gcd n i).divisors, (Nat.totient d : ℂ) * f d := by
      rw [square_range]
      apply Finset.sum_congr rfl
      intro i hi
      exact inner f n (Nat.gcd n i) (Nat.gcd_dvd_left n i)
        (Nat.gcd_pos_of_pos_left i hn)
    _ = ∑ g ∈ n.divisors, (Nat.totient (n / g) : ℂ) *
        (((n / g : ℕ) : ℂ) * (Z * G f) g) := by
      simp_rw [inner_AF]
      exact gcd_sum n hn (fun g => ((n / g : ℕ) : ℂ) * (Z * G f) g)
    _ = (B * (Z * G f)) n := by
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => B a * (Z * G f) b)]
      apply Finset.sum_congr rfl
      intro g hg
      rw [B_apply]
      ring
    _ = (G f * (B * Z)) n := by
      congr 1
      ac_rfl

private theorem identity (f : ℕ → ℂ) (n : ℕ) (hn : 0 < n) :
    square f n = ∑ d ∈ n.divisors, f d * (Nat.totient d : ℂ) * H (n / d) := by
  rw [square_AF f n hn, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => G f a * (B * Z) b)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [G_apply_pos f d (Nat.pos_of_mem_divisors hd), H_eq]

private theorem phi_mult : phi.IsMultiplicative := by
  refine ⟨Nat.totient_one, ?_⟩
  intro a b hab
  exact Nat.totient_mul hab

private theorem lift_mult (f : ℕ → ℂ) (h1 : f 1 = 1)
    (hm : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a*b) = f a * f b) :
    (lift f).IsMultiplicative := by
  refine ⟨by simpa [lift] using h1, ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · subst a; simp [lift]
  by_cases hb : b = 0
  · subst b; simp [lift]
  simpa [lift, ha, hb, mul_ne_zero ha hb] using hm a b (Nat.pos_of_ne_zero ha)
    (Nat.pos_of_ne_zero hb) hab

private theorem closure (f : ℕ → ℂ) (h1 : f 1 = 1)
    (hm : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a*b) = f a * f b) :
    square f 1 = 1 ∧ ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b →
      square f (a*b) = square f a * square f b := by
  have hG : (G f).IsMultiplicative :=
    (lift_mult f h1 hm).pmul phi_mult.natCast
  have hB : B.IsMultiplicative :=
    (ArithmeticFunction.isMultiplicative_id.pmul phi_mult).natCast
  have hZ : Z.IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.natCast
  have hA := hG.mul (hB.mul hZ)
  constructor
  · rw [square_AF f 1 (by decide)]
    exact hA.map_one
  · intro a b ha hb hab
    rw [square_AF f (a*b) (Nat.mul_pos ha hb), square_AF f a ha, square_AF f b hb]
    exact hA.map_mul_of_coprime hab

private theorem quotient_fidelity (n i k : ℕ) (hn : 0 < n) :
    0 < Nat.gcd i n / Nat.gcd (Nat.gcd i k) n ∧
    (Nat.gcd i n / Nat.gcd (Nat.gcd i k) n) * Nat.gcd (Nat.gcd i k) n = Nat.gcd i n ∧
    (Nat.gcd i n / Nat.gcd (Nat.gcd i k) n) ∣ n := by
  have hg : 0 < Nat.gcd i n := Nat.gcd_pos_of_pos_right i hn
  have hh : 0 < Nat.gcd (Nat.gcd i k) n := Nat.gcd_pos_of_pos_right _ hn
  have hdiv : Nat.gcd (Nat.gcd i k) n ∣ Nat.gcd i n :=
    Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _))
      (Nat.gcd_dvd_right _ _)
  exact ⟨Nat.div_pos (Nat.le_of_dvd hg hdiv) hh, Nat.div_mul_cancel hdiv,
    dvd_trans (Nat.div_dvd_of_dvd hdiv) (Nat.gcd_dvd_right i n)⟩

private theorem square_congr_positive (f g : ℕ → ℂ)
    (hfg : ∀ d : ℕ, 0 < d → f d = g d) (n : ℕ) (hn : 0 < n) :
    square f n = square g n := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  exact hfg _ (quotient_fidelity n i k hn).1

noncomputable def positiveLift (f : ℕ+ → ℂ) (n : ℕ) : ℂ :=
  if hn : 0 < n then f ⟨n, hn⟩ else 0

noncomputable def A (f : ℕ+ → ℂ) (n : ℕ) : ℂ := square (positiveLift f) n

def PositiveMultiplicative (f : ℕ+ → ℂ) : Prop :=
  f 1 = 1 ∧ ∀ a b : ℕ+, Nat.Coprime a.val b.val → f (a*b) = f a * f b

set_option backward.isDefEq.respectTransparency false in

private theorem positive_closure (f : ℕ+ → ℂ) (hf : PositiveMultiplicative f) :
    A f 1 = 1 ∧ ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b →
      A f (a*b) = A f a * A f b := by
  apply closure (positiveLift f)
  · simpa [positiveLift] using hf.1
  · intro a b ha hb hab
    have hm := hf.2 ⟨a, ha⟩ ⟨b, hb⟩ hab
    have he : (⟨a, ha⟩ : ℕ+) * (⟨b, hb⟩ : ℕ+) = ⟨a*b, Nat.mul_pos ha hb⟩ := by
      apply PNat.coe_injective
      exact PNat.mul_coe _ _
    rw [he] at hm
    simpa only [positiveLift, dite_eq_left ha, dite_eq_left hb, dite_eq_left (Nat.mul_pos ha hb)] using hm

private theorem positive_extension (f : ℕ+ → ℂ) (z : ℂ) (n : ℕ) (hn : 0 < n) :
    square (fun d => if hd : 0 < d then f ⟨d, hd⟩ else z) n = A f n := by
  apply square_congr_positive _ _ _ n hn
  intro d hd
  simp [positiveLift, hd]

private theorem row_sum_specialization (n : ℕ) :
    A (fun d : ℕ+ => (d.val : ℂ)) n =
      (D5.S3.ArithSums.SchulteGcdQuotientRowSumConvolution.rowSum n : ℂ) := by
  have he : positiveLift (fun d : ℕ+ => (d.val : ℂ)) = fun d : ℕ => (d : ℂ) := by
    funext d
    by_cases hd : 0 < d
    · simp [positiveLift, hd]
    · simp [positiveLift, Nat.eq_zero_of_not_pos hd]
  rw [A, he]
  simp only [square, D5.S3.ArithSums.SchulteGcdQuotientRowSumConvolution.rowSum,
    Nat.cast_sum]

theorem result (f : ℕ+ → ℂ) :
    (∀ n : ℕ, 0 < n →
      A f n = ∑ d ∈ n.divisors, positiveLift f d * (Nat.totient d : ℂ) * H (n / d)) ∧
    (PositiveMultiplicative f →
      A f 1 = 1 ∧ ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b →
        A f (a*b) = A f a * A f b) ∧
    (∀ z : ℂ, ∀ n : ℕ, 0 < n →
      square (fun d => if hd : 0 < d then f ⟨d, hd⟩ else z) n = A f n) ∧
    (∀ n : ℕ, A (fun d : ℕ+ => (d.val : ℂ)) n =
      (D5.S3.ArithSums.SchulteGcdQuotientRowSumConvolution.rowSum n : ℂ)) := by
  exact ⟨fun n hn => identity (positiveLift f) n hn, positive_closure f,
    positive_extension f, row_sum_specialization⟩

end D5.S3.ArithSums.SchulteArbitraryGcdQuotientConvolution
