/- GID: D5/S3/Quantum/Transport/FibonacciPrefix
   generality: I
   mirror-B: D5/B/S3/Quantum/Transport/FibonacciPrefix
   mirror-E: none(waiver:finite-prefix-transport)
   anchors: []
   utility: none
   digest: Canonical Fibonacci carry prefixes separate labels with an explicit golden threshold. -/

import D5.S3.Fourier.GoldenModelSetDelone
import D5.S1.Eigenstructure.GoldenPowerLog
import D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Fibonacci prefix transport

The iterated constructions use canonical modular representatives. The low
trajectory is the source Fibonacci action (a₀,a₁) ↦ (a₁,a₀+a₁).
The prefix estimate is sufficient, uniform in the high modulus, and does not
assert optimality or coherence at every shorter prefix. The operational claims
concern every moving time in a prefix, rather than a single endpoint.
-/

noncomputable section
namespace D5.S3.Quantum.Transport.FibonacciPrefix

open D5.S0.Carrier D5.S1.Scale
open D5.S3.Fourier.GoldenModelSetDelone
open D5.S1.Eigenstructure.GoldenPowerLog
open scoped Matrix Kronecker
set_option autoImplicit false

/-- The low permutation iterated for the indicated number of steps. -/
def lowTrajectory (d : ℕ) : ℕ → (ZMod d × ZMod d) ≃ (ZMod d × ZMod d)
  | 0 => Equiv.refl _
  | n + 1 => (lowTrajectory d n).trans
      (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci d)

/-- Actual integer carries along the low trajectory, including time zero. -/
def carryHistory (d : ℕ) (a : ZMod d × ZMod d) (j : ℕ) : ℕ :=
  D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry d
    (lowTrajectory d j a)

/-- The entire finite prefix, with no identification of distinct positions. -/
def carryPrefix (d N : ℕ) (a : ZMod d × ZMod d) : Fin N → ℕ :=
  fun j => carryHistory d a j

/-- Canonical integer representatives in the golden basis at each time. -/
def integerTrajectory (d t : ℕ) (a : ZMod d × ZMod d) : GoldenInt :=
  ⟨(lowTrajectory d t a).1.val, (lowTrajectory d t a).2.val⟩

/-- The exact nonnegative integer sufficient threshold. -/
def prefixThreshold (d : ℕ) : ℕ :=
  ⌊3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1)⌋₊ + 1

/-- High-fibre permutations iterated along an actual low history. -/
def fibreTrajectory (d e : ℕ) (a : ZMod d × ZMod d) :
    ℕ → (ZMod e × ZMod e) ≃ (ZMod e × ZMod e)
  | 0 => Equiv.refl _
  | n + 1 => (fibreTrajectory d e a n).trans
      { toFun := fun h => (h.2, h.1 + h.2 + (carryHistory d a n : ZMod e))
        invFun := fun h => (h.2 - h.1 - (carryHistory d a n : ZMod e), h.1)
        left_inv := by intro h; ext <;> simp; ring
        right_inv := by intro h; ext <;> simp; ring }

/-- The iterated joint permutation, with its moving low coordinate and high fibre. -/
def jointTrajectory (d e t : ℕ) :
    ((ZMod d × ZMod d) × (ZMod e × ZMod e)) ≃
      ((ZMod d × ZMod d) × (ZMod e × ZMod e)) where
  toFun x := (lowTrajectory d t x.1, fibreTrajectory d e x.1 t x.2)
  invFun x := ((lowTrajectory d t).symm x.1,
    (fibreTrajectory d e ((lowTrajectory d t).symm x.1) t).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- Moving low observation followed by the joint pullback, expressed by reindexing. -/
def movingPullback (d e t : ℕ) [NeZero d] [NeZero e] :
    Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ →ₐ[ℂ]
      Matrix ((ZMod d × ZMod d) × (ZMod e × ZMod e))
        ((ZMod d × ZMod d) × (ZMod e × ZMod e)) ℂ :=
  ((Matrix.reindexAlgEquiv ℂ ℂ (jointTrajectory d e t).symm).toAlgHom).comp
    ((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e).comp
      (Matrix.reindexAlgEquiv ℂ ℂ (lowTrajectory d t)).toAlgHom)

/-- The operational full-prefix algebra: every positive moving time lands in low⊗I. -/
def prefixAlgebra (d e : ℕ) [NeZero d] [NeZero e] (N : ℕ) : Subalgebra ℂ
    (Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :=
  ⨅ t : Fin (N + 1), ⨅ (_ : 0 < t.val),
    (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e).range.comap
      (movingPullback d e t)

/-- The independently defined computational diagonal algebra. -/
def diagonalAlgebra (d : ℕ) [NeZero d] : Subalgebra ℂ
    (Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :=
  (Matrix.diagonalAlgHom (n := ZMod d × ZMod d) (α := ℂ) ℂ).range

/-- Integer prefix evolution, collision bound, period rigidity and strict threshold. -/
theorem fibonacci_prefix_transport (d e : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (he : 2 ≤ e) :
    (∀ N (a b : ZMod d × ZMod d), carryPrefix d N a = carryPrefix d N b →
      ∀ j ≤ N, integerTrajectory d j a - integerTrajectory d j b =
        phi ^ j * (integerTrajectory d 0 a - integerTrajectory d 0 b)) ∧
    (∀ N (a b : ZMod d × ZMod d), 1 ≤ N → a ≠ b →
      carryPrefix d N a = carryPrefix d N b →
      Real.goldenRatio ^ N ≤ Real.goldenRatio ^ 3 * ((d : ℝ) - 1) ^ 2) ∧
    (∀ P, 1 ≤ P → (∀ a, lowTrajectory d P a = a) →
      Function.Injective (carryPrefix d P)) ∧
    (∀ N : ℕ, 3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1) < (N : ℝ) →
      Function.Injective (carryPrefix d N)) ∧
    (∀ a b : ZMod d × ZMod d,
      (∀ j, carryHistory d a j = carryHistory d b j) → a = b) ∧
    (prefixThreshold d : ℤ) = ⌊3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1)⌋ + 1 ∧
    (∀ N, prefixThreshold d ≤ N → Function.Injective (carryPrefix d N)) ∧
    prefixThreshold 2 = 4 ∧
    (∀ t (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      movingPullback d e t B =
        (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary d e ^ t)ᴴ *
          (((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary d) ^ t * B *
            ((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary d) ^ t)ᴴ) ⊗ₖ
              (1 : Matrix (ZMod e × ZMod e) (ZMod e × ZMod e) ℂ)) *
          D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary d e ^ t) ∧
    (∀ N (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      B ∈ prefixAlgebra d e N ↔
        ∀ a b, carryPrefix d N a ≠ carryPrefix d N b → B a b = 0) ∧
    (∀ N (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      B ∈ prefixAlgebra d e N → ∀ t, 1 ≤ t → t ≤ N →
        movingPullback d e t B = D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e B) ∧
    Antitone (prefixAlgebra d e) ∧
    (⨅ N : ℕ, ⨅ (_ : 1 ≤ N), prefixAlgebra d e N) = diagonalAlgebra d ∧
    (∀ P, 1 ≤ P → (∀ a, lowTrajectory d P a = a) →
      prefixAlgebra d e P = diagonalAlgebra d) ∧
    (∀ N, prefixThreshold d ≤ N → prefixAlgebra d e N = diagonalAlgebra d) := by
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi1 := Real.one_lt_goldenRatio
  have hD : 1 ≤ (d : ℝ) - 1 := by exact_mod_cast (show 1 ≤ (d : ℤ) - 1 by omega)
  have hsource_action : ∀ (a : ZMod d × ZMod d) (h : ZMod e × ZMod e),
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.transport d e (a, h) =
        (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci d a,
          (h.2, h.1 + h.2 +
            (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry d a : ZMod e))) := by
    have hc := (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.result d e hd he).1
    simpa using hc
  have hsource_low : lowTrajectory d 1 =
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci d := by
    apply Equiv.ext
    intro a
    simp [lowTrajectory,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci]
  have hsource_carry (a : ZMod d × ZMod d) :
      carryHistory d a 0 =
        D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry d a := by
    simp [carryHistory, lowTrajectory,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry]
  have hsource_joint : jointTrajectory d e 1 =
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.transport d e := by
    apply Equiv.ext
    rintro ⟨a, h⟩
    rw [hsource_action]
    rw [← hsource_carry a]
    simp [jointTrajectory, lowTrajectory, fibreTrajectory, carryHistory,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci]
  have hstep (a : ZMod d × ZMod d) (j : ℕ) :
      integerTrajectory d (j + 1) a = phi * integerTrajectory d j a -
        ((d * carryHistory d a j : ℕ) : GoldenInt) * phi := by
    have hdiv := Nat.div_add_mod
      ((lowTrajectory d j a).1.val + (lowTrajectory d j a).2.val) d
    have hz := congrArg (fun n : ℕ => (n : ℤ)) hdiv
    simp only [Nat.cast_add, Nat.cast_mul] at hz
    apply GoldenInt.ext
    · simp [integerTrajectory, lowTrajectory,
        D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci,
        Equiv.trans_apply, phi, sub_eq_add_neg]
    · simp only [integerTrajectory, lowTrajectory, Equiv.trans_apply, Equiv.coe_fn_mk,
        ZMod.val_add, sub_eq_add_neg, b_add, b_neg, b_mul,
        phi_a, phi_b, a_natCast, b_natCast,
        D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci]
      unfold carryHistory
      unfold D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry
      simp only [Nat.cast_mul]
      omega
  have hevolution : ∀ N (a b : ZMod d × ZMod d),
      carryPrefix d N a = carryPrefix d N b → ∀ j ≤ N,
      integerTrajectory d j a - integerTrajectory d j b =
        phi ^ j * (integerTrajectory d 0 a - integerTrajectory d 0 b) := by
    intro N a b hab j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hc := congrFun hab (⟨j, by omega⟩ : Fin N)
      change carryHistory d a j = carryHistory d b j at hc
      rw [hstep a j, hstep b j, hc]
      calc
        _ = phi * (integerTrajectory d j a - integerTrajectory d j b) := by ring
        _ = _ := by rw [ih (by omega), pow_succ]; ring
  have hlift : Function.Injective (integerTrajectory d 0) := by
    intro a b hab
    have h0 := congrArg GoldenInt.a hab
    have h1 := congrArg GoldenInt.b hab
    apply Prod.ext <;> apply ZMod.val_injective d <;>
      dsimp [integerTrajectory, lowTrajectory] at h0 h1 ⊢ <;> omega
  have hcoord (a b : ZMod d × ZMod d) (j : ℕ) :
      |((lowTrajectory d j a).1.val : ℝ) - (lowTrajectory d j b).1.val| ≤ (d : ℝ) - 1 ∧
      |((lowTrajectory d j a).2.val : ℝ) - (lowTrajectory d j b).2.val| ≤ (d : ℝ) - 1 := by
    have ha0 := (lowTrajectory d j a).1.val_lt
    have hb0 := (lowTrajectory d j b).1.val_lt
    have ha1 := (lowTrajectory d j a).2.val_lt
    have hb1 := (lowTrajectory d j b).2.val_lt
    have ha0' : ((lowTrajectory d j a).1.val : ℝ) ≤ (d : ℝ) - 1 := by
      exact_mod_cast (show ((lowTrajectory d j a).1.val : ℤ) ≤ (d : ℤ) - 1 by omega)
    have hb0' : ((lowTrajectory d j b).1.val : ℝ) ≤ (d : ℝ) - 1 := by
      exact_mod_cast (show ((lowTrajectory d j b).1.val : ℤ) ≤ (d : ℤ) - 1 by omega)
    have ha1' : ((lowTrajectory d j a).2.val : ℝ) ≤ (d : ℝ) - 1 := by
      exact_mod_cast (show ((lowTrajectory d j a).2.val : ℤ) ≤ (d : ℤ) - 1 by omega)
    have hb1' : ((lowTrajectory d j b).2.val : ℝ) ≤ (d : ℝ) - 1 := by
      exact_mod_cast (show ((lowTrajectory d j b).2.val : ℤ) ≤ (d : ℤ) - 1 by omega)
    have ha0z := Nat.cast_nonneg (α := ℝ) ((lowTrajectory d j a).1.val)
    have hb0z := Nat.cast_nonneg (α := ℝ) ((lowTrajectory d j b).1.val)
    have ha1z := Nat.cast_nonneg (α := ℝ) ((lowTrajectory d j a).2.val)
    have hb1z := Nat.cast_nonneg (α := ℝ) ((lowTrajectory d j b).2.val)
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith
  have hexpand (a b : ZMod d × ZMod d) (j : ℕ) :
      |embedding (integerTrajectory d j a) - embedding (integerTrajectory d j b)| ≤
        Real.goldenRatio ^ 2 * ((d : ℝ) - 1) := by
    obtain ⟨h0, h1⟩ := hcoord a b j
    calc
      _ = |(((lowTrajectory d j a).1.val : ℝ) - (lowTrajectory d j b).1.val) +
          (((lowTrajectory d j a).2.val : ℝ) - (lowTrajectory d j b).2.val) *
            Real.goldenRatio| := by simp [integerTrajectory, embedding_apply]; congr 1; ring
      _ ≤ |((lowTrajectory d j a).1.val : ℝ) - (lowTrajectory d j b).1.val| +
          |((lowTrajectory d j a).2.val : ℝ) - (lowTrajectory d j b).2.val| *
            Real.goldenRatio := by
          have ht := abs_add_le
            (((lowTrajectory d j a).1.val : ℝ) - (lowTrajectory d j b).1.val)
            ((((lowTrajectory d j a).2.val : ℝ) - (lowTrajectory d j b).2.val) *
              Real.goldenRatio)
          simpa only [abs_mul, abs_of_pos hphi] using ht
      _ ≤ ((d : ℝ) - 1) + ((d : ℝ) - 1) * Real.goldenRatio :=
        add_le_add h0 (mul_le_mul_of_nonneg_right h1 hphi.le)
      _ = _ := by rw [Real.goldenRatio_sq]; ring
  have hconj (a b : ZMod d × ZMod d) :
      |embedding (conj (integerTrajectory d 0 a)) -
        embedding (conj (integerTrajectory d 0 b))| ≤
          Real.goldenRatio * ((d : ℝ) - 1) := by
    obtain ⟨h0, h1⟩ := hcoord a b 0
    have hneg : 1 - Real.goldenRatio < 0 := by linarith
    calc
      _ = |(((lowTrajectory d 0 a).1.val : ℝ) - (lowTrajectory d 0 b).1.val) +
          (((lowTrajectory d 0 a).2.val : ℝ) - (lowTrajectory d 0 b).2.val) *
            (1 - Real.goldenRatio)| := by
              simp [integerTrajectory, embedding_apply, conj]; congr 1; ring
      _ ≤ |((lowTrajectory d 0 a).1.val : ℝ) - (lowTrajectory d 0 b).1.val| +
          |((lowTrajectory d 0 a).2.val : ℝ) - (lowTrajectory d 0 b).2.val| *
            (Real.goldenRatio - 1) := by
              have habs : |1 - Real.goldenRatio| = Real.goldenRatio - 1 := by
                rw [abs_of_neg hneg]; ring
              rw [← habs, ← abs_mul]
              exact abs_add_le _ _
      _ ≤ ((d : ℝ) - 1) + ((d : ℝ) - 1) * (Real.goldenRatio - 1) :=
        add_le_add h0 (mul_le_mul_of_nonneg_right h1 (by linarith))
      _ = _ := by ring
  have hbound : ∀ N (a b : ZMod d × ZMod d), 1 ≤ N → a ≠ b →
      carryPrefix d N a = carryPrefix d N b →
      Real.goldenRatio ^ N ≤ Real.goldenRatio ^ 3 * ((d : ℝ) - 1) ^ 2 := by
    intro N a b _ hne hab
    have hs := norm_separation (integerTrajectory d 0 a) (integerTrajectory d 0 b)
      (fun h => hne (hlift h)) (Real.goldenRatio * ((d : ℝ) - 1)) (hconj a b)
    have he := congrArg embedding (hevolution N a b hab N le_rfl)
    simp only [map_sub, map_mul, map_pow, embedding_phi] at he
    have hh := hexpand a b N
    have hpow : 0 ≤ Real.goldenRatio ^ N := (pow_pos hphi _).le
    have hm := mul_le_mul_of_nonneg_left hs hpow
    rw [mul_one] at hm
    have heabs : |embedding (integerTrajectory d N a) - embedding (integerTrajectory d N b)| =
        Real.goldenRatio ^ N *
          |embedding (integerTrajectory d 0 a) - embedding (integerTrajectory d 0 b)| := by
      rw [he, abs_mul, abs_of_nonneg hpow]
    rw [← mul_assoc, ← heabs] at hm
    have hu := mul_le_mul_of_nonneg_right hh
      (mul_nonneg hphi.le (le_trans zero_le_one hD))
    calc
      _ ≤ _ := hm
      _ ≤ _ := hu
      _ = _ := by ring
  have hperiod : ∀ P, 1 ≤ P → (∀ a, lowTrajectory d P a = a) →
      Function.Injective (carryPrefix d P) := by
    intro P hP hp a b hab
    have he := congrArg embedding (hevolution P a b hab P le_rfl)
    have ha : integerTrajectory d P a = integerTrajectory d 0 a := by
      simp [integerTrajectory, hp, lowTrajectory]
    have hb : integerTrajectory d P b = integerTrajectory d 0 b := by
      simp [integerTrajectory, hp, lowTrajectory]
    rw [ha, hb, map_mul, map_pow, embedding_phi] at he
    have hpow : 1 < Real.goldenRatio ^ P := one_lt_pow₀ hphi1 (by omega)
    have hz : embedding (integerTrajectory d 0 a - integerTrajectory d 0 b) = 0 := by
      nlinarith
    exact hlift (sub_eq_zero.mp ((embedding_eq_zero_iff _).mp hz))
  have hlog : 0 ≤ Real.logb Real.goldenRatio ((d : ℝ) - 1) :=
    Real.logb_nonneg hphi1 hD
  have hstrict : ∀ N : ℕ, 3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1) < (N : ℝ) →
      Function.Injective (carryPrefix d N) := by
    intro N hN a b hab
    by_contra hne
    have hNpos : 1 ≤ N := by
      have : (0 : ℝ) < N := by linarith
      have : 0 < N := by exact_mod_cast this
      omega
    have hb := hbound N a b hNpos hne hab
    have hh := Real.logb_le_logb_of_le hphi1 (pow_pos hphi N) hb
    rw [golden_power_logb_nat] at hh
    rw [Real.logb_mul (ne_of_gt (pow_pos hphi 3))
      (ne_of_gt (pow_pos (by linarith : 0 < (d : ℝ) - 1) 2)),
      golden_power_logb_nat, Real.logb_pow] at hh
    norm_num at hh
    linarith
  have hthreshold : ∀ N, prefixThreshold d ≤ N → Function.Injective (carryPrefix d N) := by
    intro N hN
    apply hstrict N
    have hh := Nat.lt_floor_add_one (3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1))
    have hn : (prefixThreshold d : ℝ) ≤ N := by exact_mod_cast hN
    have hn' : (⌊3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1)⌋₊ : ℝ) + 1 ≤ N := by
      simpa only [prefixThreshold, Nat.cast_add, Nat.cast_one] using hn
    exact lt_of_lt_of_le hh hn'
  have harithmetic :
      (∀ a b : ZMod d × ZMod d,
        (∀ j, carryHistory d a j = carryHistory d b j) → a = b) ∧
      (prefixThreshold d : ℤ) = ⌊3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1)⌋ + 1 ∧
      prefixThreshold 2 = 4 := by
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      apply hthreshold (prefixThreshold d) le_rfl
      funext j
      exact hab j
    · unfold prefixThreshold
      rw [Nat.cast_add, Nat.cast_one, Int.natCast_floor_eq_floor (by positivity)]
    · norm_num [prefixThreshold, Real.logb_one]
  have hcarry (a : ZMod d × ZMod d) (j : ℕ) : carryHistory d a j < 2 := by
    unfold carryHistory
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).2
    have h0 := (lowTrajectory d j a).1.val_lt
    have h1 := (lowTrajectory d j a).2.val_lt
    omega
  have hcast (a b : ZMod d × ZMod d) (j : ℕ) :
      (carryHistory d a j : ZMod e) = (carryHistory d b j : ZMod e) →
        carryHistory d a j = carryHistory d b j := by
    intro h
    have hh := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le (hcarry a j) he),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le (hcarry b j) he)] at hh
    exact hh
  have hfibres (N : ℕ) (a b : ZMod d × ZMod d) :
      (∀ t ≤ N, fibreTrajectory d e a t = fibreTrajectory d e b t) ↔
        carryPrefix d N a = carryPrefix d N b := by
    constructor
    · intro h
      funext j
      apply hcast a b j
      have hj := h j (by omega)
      have hs := congrArg (fun q => (q (0, 0)).2) (h (j + 1) (by omega))
      simp only [fibreTrajectory, Equiv.trans_apply, Equiv.coe_fn_mk] at hs
      rw [hj] at hs
      exact add_left_cancel hs
    · intro h t ht
      induction t with
      | zero => rfl
      | succ t ih =>
        have hc := congrFun h (⟨t, by omega⟩ : Fin N)
        change carryHistory d a t = carryHistory d b t at hc
        simp only [fibreTrajectory, ih (by omega), hc]
  have hentry (t : ℕ) (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ)
      (a b : ZMod d × ZMod d) (h h' : ZMod e × ZMod e) :
      movingPullback d e t B (a,h) (b,h') =
        if fibreTrajectory d e a t h = fibreTrajectory d e b t h' then B a b else 0 := by
    simp [movingPullback, Matrix.reindex_apply, jointTrajectory,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor, Matrix.one_apply, mul_ite]
  have hlowentry (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ)
      (a b : ZMod d × ZMod d) (h h' : ZMod e × ZMod e) :
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e B (a,h) (b,h') = if h = h' then B a b else 0 := by
    simp [D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor, Matrix.one_apply, mul_ite]
  have htime (t : ℕ) (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
      movingPullback d e t B ∈ (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e).range ↔
        ∀ a b, B a b ≠ 0 → fibreTrajectory d e a t = fibreTrajectory d e b t := by
    constructor
    · rintro ⟨C, hC⟩ a b hB
      change D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e C = movingPullback d e t B at hC
      apply Equiv.ext
      intro h
      let h' := (fibreTrajectory d e b t).symm (fibreTrajectory d e a t h)
      have hh : h' = h := by
        by_contra hne
        have heq := congrArg (fun X => X (a,h) (b,h')) hC
        rw [hentry, hlowentry] at heq
        have hneq : h ≠ h' := Ne.symm hne
        have himg : fibreTrajectory d e a t h = fibreTrajectory d e b t h' := by
          simp [h']
        rw [if_neg hneq, if_pos himg] at heq
        exact hB heq.symm
      have himg : fibreTrajectory d e b t h' = fibreTrajectory d e a t h := by
        simp [h']
      rw [hh] at himg
      exact himg.symm
    · intro h
      refine ⟨B, ?_⟩
      change D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e B = movingPullback d e t B
      ext ⟨a,u⟩ ⟨b,v⟩
      rw [hentry, hlowentry]
      by_cases hB : B a b = 0
      · simp [hB]
      · rw [h a b hB]
        simp only [Equiv.apply_eq_iff_eq]
  have hmem (N : ℕ) (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
      B ∈ prefixAlgebra d e N ↔
        ∀ t, 1 ≤ t → t ≤ N → movingPullback d e t B ∈ (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e).range := by
    simp only [prefixAlgebra, Algebra.mem_iInf, Subalgebra.mem_comap]
    constructor
    · intro h t ht htN
      exact h (⟨t, Nat.lt_succ_of_le htN⟩ : Fin (N + 1))
        (show 0 < t from by omega)
    · intro h t ht
      exact h t (by omega) (by omega)
  have hsupport (N : ℕ) (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
      B ∈ prefixAlgebra d e N ↔
        ∀ a b, carryPrefix d N a ≠ carryPrefix d N b → B a b = 0 := by
    rw [hmem]
    constructor
    · intro h a b hne
      by_contra hB
      apply hne
      apply (hfibres N a b).1
      intro t ht
      by_cases hz : t = 0
      · subst t; rfl
      · exact (htime t B).1 (h t (by omega) ht) a b hB
    · intro h t ht htN
      apply (htime t B).2
      intro a b hB
      have hab : carryPrefix d N a = carryPrefix d N b := by
        by_contra hne
        exact hB (h a b hne)
      exact (hfibres N a b).2 hab t htN
  have hexact (N : ℕ) (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ)
      (hB : B ∈ prefixAlgebra d e N) (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ N) :
      movingPullback d e t B = D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e B := by
    have hh := (htime t B).1 ((hmem N B).1 hB t ht htN)
    ext ⟨a,u⟩ ⟨b,v⟩
    rw [hentry, hlowentry]
    by_cases hz : B a b = 0
    · simp [hz]
    · rw [hh a b hz]
      simp only [Equiv.apply_eq_iff_eq]
  have hdiag (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
      B ∈ diagonalAlgebra d ↔ ∀ a b, a ≠ b → B a b = 0 := by
    constructor
    · rintro ⟨v, rfl⟩ a b hab
      change Matrix.diagonal v a b = 0
      simp [Matrix.diagonal, hab]
    · intro h
      refine ⟨fun a => B a a, ?_⟩
      change Matrix.diagonal (fun a => B a a) = B
      ext a b
      by_cases hab : a = b
      · subst b; simp
      · simp [Matrix.diagonal, hab, h a b hab]
  have hcollapse (N : ℕ) (hinj : Function.Injective (carryPrefix d N)) :
      prefixAlgebra d e N = diagonalAlgebra d := by
    ext B
    rw [hsupport, hdiag]
    constructor
    · intro h a b hab
      exact h a b (fun heq => hab (hinj heq))
    · intro h a b hab
      exact h a b (fun heq => hab (congrArg (carryPrefix d N) heq))
  have hanti : Antitone (prefixAlgebra d e) := by
    intro N K hNK B hB
    apply (hmem N B).2
    intro t ht htN
    exact (hmem K B).1 hB t ht (htN.trans hNK)
  have hinter : (⨅ N : ℕ, ⨅ (_ : 1 ≤ N), prefixAlgebra d e N) = diagonalAlgebra d := by
    apply le_antisymm
    · calc
        _ ≤ prefixAlgebra d e (prefixThreshold d) :=
          iInf_le_of_le (prefixThreshold d) (iInf_le _ (by simp [prefixThreshold]))
        _ = _ := hcollapse _ (hthreshold _ le_rfl)
    · intro B hB
      simp only [Algebra.mem_iInf]
      intro N _
      apply (hsupport N B).2
      intro a b hab
      exact (hdiag B).1 hB a b (fun heq => hab (congrArg (carryPrefix d N) heq))
  have hlowpow : ∀ t, lowTrajectory d t = (lowTrajectory d 1) ^ t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [pow_succ', ← ih]
      simp [lowTrajectory, Equiv.Perm.mul_def]
  have hjointstep (t : ℕ) :
      jointTrajectory d e (t + 1) = jointTrajectory d e 1 * jointTrajectory d e t := by
    apply Equiv.ext
    rintro ⟨a,h⟩
    simp [jointTrajectory, lowTrajectory, fibreTrajectory, carryHistory,
      Equiv.Perm.mul_def, Equiv.trans_apply]
  have hjointpow : ∀ t, jointTrajectory d e t = (jointTrajectory d e 1) ^ t := by
    intro t
    induction t with
    | zero => apply Equiv.ext; intro x; rfl
    | succ t ih => rw [pow_succ', ← ih, hjointstep]
  have hconjugate {X : Type} [Fintype X] [DecidableEq X]
      (q : Equiv.Perm X) (B : Matrix X X ℂ) :
      q.permMatrix ℂ * B * Equiv.Perm.permMatrix ℂ q.symm = B.submatrix q q := by
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have hmatrix_old (t : ℕ) (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
      movingPullback d e t B =
        ((Matrix.permMatrixHom (R := ℂ) (jointTrajectory d e 1)) ^ t)ᴴ *
          (((Matrix.permMatrixHom (R := ℂ) (lowTrajectory d 1)) ^ t * B *
            ((Matrix.permMatrixHom (R := ℂ) (lowTrajectory d 1)) ^ t)ᴴ) ⊗ₖ
              (1 : Matrix (ZMod e × ZMod e) (ZMod e × ZMod e) ℂ)) *
          (Matrix.permMatrixHom (R := ℂ) (jointTrajectory d e 1)) ^ t := by
    have hl : (Matrix.permMatrixHom (R := ℂ) (lowTrajectory d 1)) ^ t =
        Matrix.permMatrixHom (R := ℂ) (lowTrajectory d t) := by
      rw [← map_pow, ← hlowpow]
    have hj : (Matrix.permMatrixHom (R := ℂ) (jointTrajectory d e 1)) ^ t =
        Matrix.permMatrixHom (R := ℂ) (jointTrajectory d e t) := by
      rw [← map_pow, ← hjointpow]
    rw [hl, hj]
    change _ = (Equiv.Perm.permMatrix ℂ (jointTrajectory d e t).symm)ᴴ *
      ((Equiv.Perm.permMatrix ℂ (lowTrajectory d t).symm * B *
        (Equiv.Perm.permMatrix ℂ (lowTrajectory d t).symm)ᴴ) ⊗ₖ
          (1 : Matrix (ZMod e × ZMod e) (ZMod e × ZMod e) ℂ)) *
      Equiv.Perm.permMatrix ℂ (jointTrajectory d e t).symm
    rw [Matrix.conjTranspose_permMatrix, Matrix.conjTranspose_permMatrix]
    simp only [Equiv.Perm.inv_def, Equiv.symm_symm]
    have hlowconj := hconjugate (lowTrajectory d t).symm B
    simp only [Equiv.symm_symm] at hlowconj
    rw [hconjugate (jointTrajectory d e t), hlowconj]
    rfl
  have hmatrix (t : ℕ) (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
      movingPullback d e t B =
        (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary d e ^ t)ᴴ *
          (((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary d) ^ t * B *
            ((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary d) ^ t)ᴴ) ⊗ₖ
              (1 : Matrix (ZMod e × ZMod e) (ZMod e × ZMod e) ℂ)) *
          D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary d e ^ t := by
    simpa [D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary,
      hsource_joint, hsource_low] using hmatrix_old t B
  exact ⟨hevolution, hbound, hperiod, hstrict, harithmetic.1, harithmetic.2.1,
    hthreshold, harithmetic.2.2, hmatrix, hsupport, hexact, hanti, hinter,
    fun P hP hp => hcollapse P (hperiod P hP hp),
    fun N hN => hcollapse N (hthreshold N hN)⟩

#print axioms fibonacci_prefix_transport
end D5.S3.Quantum.Transport.FibonacciPrefix
