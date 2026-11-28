/- GID: D5/S3/LinearAlgebra/Matrix/RationalGraph/Toeplitz
   generality: G
   mirror-B: none(waiver:existing-library-proof-without-a-dedicated-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The graph index of the reciprocal lower-triangular Toeplitz matrix -/

import OmegaBuild.Commands
import D5.S3.LinearAlgebra.Matrix.RationalGraph.Rational
import Mathlib.NumberTheory.PrimeCounting

/-! Omega original.

# The graph index of the reciprocal lower-triangular Toeplitz matrix

At a prime `p` with `p ≤ n < p²`, reduction of the scaled matrix modulo `p`
has its first nonzero diagonal at shift `p - 1`, with ones on that diagonal.
The local quotient therefore has `n - p + 1` independent residue coordinates.
A valuation bound controls the other local factors, and the rational matrix
graph index is the product of all local factors over the primes through `n`.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset Omega.RationalMatrixGraph.Rational
open scoped BigOperators Padic

namespace Omega.RationalMatrixGraph.Toeplitz

/-- The literal rational Toeplitz matrix with first column `1, 1/2, …, 1/n`. -/
def toeplitz (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j.val ≤ i.val then 1 / ((i.val - j.val + 1 : ℕ) : ℚ) else 0

/-- The index counts the cosets of integral inputs with integral rational output. -/
noncomputable def graphIndex (n : ℕ) : ℕ := (graphDomain (toeplitz n)).index

theorem graphIndex_pos (n : ℕ) : 0 < graphIndex n := by
  let : NeZero (denominator (toeplitz n)) := ⟨denominator_ne_zero _⟩
  change 0 < (Omega.RationalMatrixGraph.CRT.graphKernel _ (cleared (toeplitz n))).index
  rw [Omega.RationalMatrixGraph.CRT.kernel_card]
  exact Nat.card_pos

private theorem entry_denominator (n : ℕ) (i j : Fin n) :
    (toeplitz n i j).den = if j.val ≤ i.val then i.val - j.val + 1 else 1 := by
  unfold toeplitz
  split_ifs
  · let k := i.val - j.val + 1
    change (1 / (k : ℚ)).den = k
    rw [one_div, Rat.den_inv_of_ne_zero (by dsimp [k]; positivity), Rat.num_natCast]
    exact Int.natAbs_natCast k
  · rfl

/-- The primes in the common denominator are exactly the primes through the dimension.
The entry at row `p-1`, column zero supplies the denominator `p`. -/
theorem denominator_primeFactors (n : ℕ) :
    (denominator (toeplitz n)).primeFactors = Nat.primesLE n := by
  classical
  ext p
  rw [Nat.mem_primeFactors, Nat.mem_primesLE]
  refine ⟨?_, ?_⟩
  · rintro ⟨hp, hd, _⟩
    obtain ⟨⟨i, j⟩, _, hij⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
    rw [entry_denominator] at hij
    split_ifs at hij
    · exact ⟨(Nat.le_of_dvd (by omega) hij).trans (by have := i.isLt; omega), hp⟩
    · exact (hp.not_dvd_one hij).elim
  · rintro ⟨hpn, hp⟩
    let i : Fin n := ⟨p - 1, by have := hp.pos; omega⟩
    let j : Fin n := ⟨0, hp.pos.trans_le hpn⟩
    have hd : (toeplitz n i j).den = p := by
      rw [entry_denominator, ite_eq_left (Nat.zero_le _)]
      change p - 1 - 0 + 1 = p
      have := hp.pos
      omega
    refine ⟨hp, ?_, denominator_ne_zero _⟩
    rw [← hd]
    exact dvd_prod_of_mem _ (mem_univ (i, j))

/-- Every coefficient has valuation at least the negative of the integer logarithm. -/
theorem entry_valuation (n p : ℕ) [Fact p.Prime] (i j : Fin n) :
    -(Nat.log p n : ℤ) ≤ padicValRat p (toeplitz n i j) := by
  unfold toeplitz
  split_ifs
  · let k := i.val - j.val + 1
    change -(Nat.log p n : ℤ) ≤ padicValRat p (1 / (k : ℚ))
    rw [one_div, padicValRat.inv, padicValRat.of_nat, neg_le_neg_iff]
    suffices padicValNat p k ≤ Nat.log p n by exact_mod_cast this
    have hkn : k ≤ n := by dsimp [k]; have := i.isLt; omega
    exact (padicValNat_le_nat_log k).trans (Nat.log_mono_right hkn)
  · simp

noncomputable section Padic

variable (p : ℕ) [Fact p.Prime]

private def ratInt (x : ℚ) (hx : 0 ≤ padicValRat p x) : ℤ_[p] :=
  ⟨(x : ℚ_[p]), (Padic.norm_le_one_iff_val_nonneg (x : ℚ_[p])).mpr
    (by rwa [Padic.valuation_ratCast])⟩

private theorem scaled_nonneg (a : ℕ) (x : ℚ) (hx : -(a : ℤ) ≤ padicValRat p x) :
    0 ≤ padicValRat p ((p : ℚ)^a * x) := by
  by_cases hz : x = 0
  · simp [hz]
  have hpn : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  rw [padicValRat.mul (pow_ne_zero _ hpn) hz, padicValRat.pow,
    padicValRat.self (Fact.out : Nat.Prime p).one_lt]
  omega

private def scaledMatrix {ι : Type*} (E : Matrix ι ι ℚ) (a : ℕ)
    (h : ∀ i j, -(a : ℤ) ≤ padicValRat p (E i j)) : Matrix ι ι ℤ_[p] :=
  fun i j => ratInt p _ (scaled_nonneg p a _ (h i j))

private theorem scaledMatrix_mulVec {ι : Type*} [Fintype ι] (E : Matrix ι ι ℚ) (a : ℕ)
    (h : ∀ i j, -(a : ℤ) ≤ padicValRat p (E i j)) (v : ι → ℤ_[p]) (i : ι) :
    ((scaledMatrix p E a h *ᵥ v) i : ℚ_[p]) =
      (p : ℚ_[p])^a * ((E.map (algebraMap ℚ ℚ_[p])) *ᵥ fun j => (v j : ℚ_[p])) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sum]
  change PadicInt.Coe.ringHom (∑ j, scaledMatrix p E a h i j * v j) = _
  rw [map_sum]
  simp only [map_mul]
  apply sum_congr rfl
  intro j _
  change (((p : ℚ)^a * E i j : ℚ) : ℚ_[p]) * (v j : ℚ_[p]) =
    (p : ℚ_[p])^a * ((E i j : ℚ_[p]) * (v j : ℚ_[p]))
  push_cast
  exact mul_assoc _ _ _

private theorem localized_mem_scaled {ι : Type*} [Fintype ι] (E : Matrix ι ι ℚ)
    (q : (denominator E).primeFactors) (a : ℕ)
    (h : ∀ i j, -(a : ℤ) ≤ padicValRat q.val (E i j)) :
    let : Fact q.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.property⟩
    ∀ v : ι → ℤ_[q.val], v ∈ localizedDomain E q ↔
      ∀ i, (q.val : ℤ_[q.val])^a ∣ (scaledMatrix q.val E a h *ᵥ v) i := by
  let : Fact q.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.property⟩
  dsimp only
  intro v
  rw [localized_mem]
  apply forall_congr'
  intro i
  have hm := scaledMatrix_mulVec q.val E a h v i
  have hpn : (q.val : ℚ_[q.val]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime q.val).ne_zero
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, PadicInt.coe_inj.mp ?_⟩
    rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, hm, hx]
  · rintro ⟨x, hx⟩
    refine ⟨x, mul_left_cancel₀ (pow_ne_zero a hpn) ?_⟩
    rw [← hm, hx, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]

/-- A uniform lower valuation bound gives a divisibility bound for the local index. -/
theorem local_index_dvd_pow {ι : Type*} [Fintype ι] (E : Matrix ι ι ℚ)
    (q : (denominator E).primeFactors) (a : ℕ)
    (h : ∀ i j, -(a : ℤ) ≤ padicValRat q.val (E i j)) :
    (localizedDomain E q).index ∣ q.val^(a * Fintype.card ι) := by
  let : Fact q.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.property⟩
  let f := Omega.RationalMatrixGraph.Padic.reduceVecPow (n := ι) q.val a
  have hsub : f.ker ≤ localizedDomain E q := by
    intro v hv
    rw [localized_mem_scaled E q a h]
    have hdiv (j : ι) : (q.val : ℤ_[q.val])^a ∣ v j := by
      have hj := congrFun (AddMonoidHom.mem_ker.mp hv) j
      change PadicInt.toZModPow a (v j) = 0 at hj
      rwa [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hj
    intro i
    exact dvd_sum fun j _ => dvd_mul_of_dvd_right (hdiv j) _
  have hf : f.ker.index = q.val^(a * Fintype.card ι) := by
    change Nat.card ((ι → ℤ_[q.val]) ⧸ f.ker) = _
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f
      (Omega.RationalMatrixGraph.Padic.reduceVecPow_surj q.val a)).toEquiv]
    let : NeZero (q.val ^ a) :=
      ⟨pow_ne_zero _ (Fact.out : Nat.Prime q.val).ne_zero⟩
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, pow_mul]
  exact hf ▸ AddSubgroup.index_dvd_of_le hsub

end Padic

/-- The bound applies at every prime of the denominator, including all small primes. -/
theorem local_index_bound (n : ℕ) (q : (denominator (toeplitz n)).primeFactors) :
    (localizedDomain (toeplitz n) q).index ∣ q.val^(Nat.log q.val n * n) := by
  let : Fact q.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.property⟩
  simpa only [Fintype.card_fin] using
    local_index_dvd_pow (toeplitz n) q (Nat.log q.val n) (entry_valuation n q.val)

/-- All entries are integral at any prime greater than the dimension. -/
theorem entry_integral_of_lt_prime (n p : ℕ) [Fact p.Prime] (h : n < p) (i j : Fin n) :
    0 ≤ padicValRat p (toeplitz n i j) := by
  simpa [Nat.log_of_lt h] using entry_valuation n p i j

noncomputable section LargePrime

variable (p : ℕ) [Fact p.Prime]

private theorem large_entry_valuation (n : ℕ) (hpn : p ≤ n) (hbig : n < p^2) (i j : Fin n) :
    -((1 : ℕ) : ℤ) ≤ padicValRat p (toeplitz n i j) := by
  have hlog : Nat.log p n = 1 :=
    Nat.log_eq_one_iff'.mpr ⟨hpn, by simpa [pow_two] using hbig⟩
  simpa only [hlog] using entry_valuation n p i j

private def residueMatrix (n : ℕ) (hpn : p ≤ n) (hbig : n < p^2) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  (scaledMatrix p (toeplitz n) 1 (large_entry_valuation p n hpn hbig)).map PadicInt.toZMod

-- The first possible nonzero diagonal is at shift p-1.
private theorem residue_zero (n : ℕ) (hpn : p ≤ n) (hbig : n < p^2) (i j : Fin n)
    (hij : i.val + 1 < j.val + p) : residueMatrix p n hpn hbig i j = 0 := by
  have hval : 0 ≤ padicValRat p (toeplitz n i j) := by
    unfold toeplitz
    split_ifs with hji
    · let k := i.val - j.val + 1
      change 0 ≤ padicValRat p (1 / (k : ℚ))
      have hnd : ¬p ∣ k := fun hd => by
        have := Nat.le_of_dvd (show 0 < k by dsimp [k]; omega) hd
        dsimp [k] at this
        omega
      rw [one_div, padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
      simp
    · simp
  let B := scaledMatrix p (toeplitz n) 1 (large_entry_valuation p n hpn hbig)
  have hb : B i j = (p : ℤ_[p]) * ratInt p (toeplitz n i j) hval := by
    apply PadicInt.coe_inj.mp
    rw [PadicInt.coe_mul, PadicInt.coe_natCast]
    change (((p : ℚ)^1 * toeplitz n i j : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) * (toeplitz n i j : ℚ_[p])
    push_cast
    rw [pow_one]
  change PadicInt.toZMod (B i j) = 0
  rw [hb, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

private theorem residue_pivot (n : ℕ) (hpn : p ≤ n) (hbig : n < p^2) (i j : Fin n)
    (hij : i.val + 1 = j.val + p) : residueMatrix p n hpn hbig i j = 1 := by
  have hp := (Fact.out : Nat.Prime p).pos
  have he : toeplitz n i j = 1 / (p : ℚ) := by
    rw [toeplitz, ite_eq_left (by omega), show i.val - j.val + 1 = p by omega]
  let B := scaledMatrix p (toeplitz n) 1 (large_entry_valuation p n hpn hbig)
  have hb : B i j = 1 := by
    apply PadicInt.coe_inj.mp
    change (((p : ℚ)^1 * toeplitz n i j : ℚ) : ℚ_[p]) = 1
    rw [he, pow_one, mul_one_div_cancel (show (p : ℚ) ≠ 0 by exact_mod_cast hp.ne')]
    simp
  change PadicInt.toZMod (B i j) = 1
  rw [hb, map_one]

private theorem residue_mulVec_eq_zero (n : ℕ) (hpn : p ≤ n) (hbig : n < p^2)
    (v : Fin n → ZMod p) :
    (∀ i, (residueMatrix p n hpn hbig *ᵥ v) i = 0) ↔
      ∀ j : Fin n, j.val < n - p + 1 → v j = 0 := by
  have hp := (Fact.out : Nat.Prime p).pos
  constructor
  · intro hv
    have vanishes (a : ℕ) (ha : a < n) (hb : a < n - p + 1) :
        v ⟨a, ha⟩ = 0 := by
      induction a using Nat.strong_induction_on with
      | h a ih =>
        let i : Fin n := ⟨a + (p - 1), by omega⟩
        let j : Fin n := ⟨a, ha⟩
        have hi := hv i
        rw [Matrix.mulVec, dotProduct, sum_eq_single j] at hi
        · rwa [residue_pivot p n hpn hbig i j (by
            change a + (p - 1) + 1 = a + p
            omega), one_mul] at hi
        · intro k _ hk
          by_cases hka : k.val < a
          · rw [ih k.val hka k.isLt (hka.trans hb), mul_zero]
          · have hne : k.val ≠ a := fun h => hk (Fin.ext h)
            rw [residue_zero p n hpn hbig i k (by
              change a + (p - 1) + 1 < k.val + p
              omega), zero_mul]
        · simp
    exact fun j hj => vanishes j.val j.isLt hj
  · intro hv i
    rw [Matrix.mulVec, dotProduct]
    apply sum_eq_zero
    intro j _
    by_cases hj : j.val < n - p + 1
    · rw [hv j hj, mul_zero]
    · rw [residue_zero p n hpn hbig i j (by have := i.isLt; omega), zero_mul]

end LargePrime

/-- At a prime with `p² > n`, the local index is exactly `p^(n-p+1)`. -/
theorem local_index_large (n : ℕ) (q : (denominator (toeplitz n)).primeFactors)
    (hbig : n < q.val^2) :
    (localizedDomain (toeplitz n) q).index = q.val^(n - q.val + 1) := by
  let p := q.val
  let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors q.property⟩
  have hp := (Fact.out : Nat.Prime p).pos
  have hpn : p ≤ n := by
    have hq : p ∈ Nat.primesLE n :=
      (congrArg (fun S : Finset ℕ => p ∈ S) (denominator_primeFactors n)).mp q.property
    exact (Nat.mem_primesLE.mp hq).1
  let k := n - p + 1
  have hkn : k ≤ n := by dsimp [k]; omega
  let f : (Fin n → ℤ_[p]) →+ (Fin k → ZMod p) :=
    { toFun := fun v j => PadicInt.toZMod (v (Fin.castLE hkn j))
      map_zero' := by ext j; exact map_zero _
      map_add' := by intro v w; ext j; exact map_add _ _ _ }
  have hsurj : Function.Surjective f := by
    intro w
    let v (i : Fin n) : ℤ_[p] := if h : i.val < k then (w ⟨i.val, h⟩).val else 0
    refine ⟨v, ?_⟩
    funext j
    change PadicInt.toZMod (v (Fin.castLE hkn j)) = w j
    simp only [v, Fin.val_castLE, dite_eq_left j.isLt, Fin.eta, map_natCast, ZMod.natCast_zmod_val]
  have hker : localizedDomain (toeplitz n) q = f.ker := by
    ext v
    rw [localized_mem_scaled (toeplitz n) q 1 (large_entry_valuation p n hpn hbig) v,
      AddMonoidHom.mem_ker]
    let B := scaledMatrix p (toeplitz n) 1 (large_entry_valuation p n hpn hbig)
    have hred (i : Fin n) : (p : ℤ_[p])^1 ∣ (B *ᵥ v) i ↔
        (residueMatrix p n hpn hbig *ᵥ (PadicInt.toZMod ∘ v)) i = 0 := by
      rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
        ← PadicInt.ker_toZMod, RingHom.mem_ker]
      rw [RingHom.map_mulVec]
      rfl
    change (∀ i, (p : ℤ_[p])^1 ∣ (B *ᵥ v) i) ↔ f v = 0
    simp only [hred]
    rw [residue_mulVec_eq_zero p n hpn hbig]
    constructor
    · intro hv
      funext j
      exact hv (Fin.castLE hkn j) j.isLt
    · intro hv j hj
      exact congrFun hv ⟨j.val, hj⟩
  rw [hker]
  change Nat.card ((Fin n → ℤ_[p]) ⧸ f.ker) = p^k
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_fin]

/-- The local graph index at `p`, with value one outside the denominator support. -/
noncomputable def primeFactor (n p : ℕ) : ℕ :=
  if h : p ∈ (denominator (toeplitz n)).primeFactors then
    (localizedDomain (toeplitz n) ⟨p, h⟩).index else 1

/-- Even outside the denominator support the same divisibility bound holds. -/
theorem primeFactor_dvd (n p : ℕ) : primeFactor n p ∣ p^(Nat.log p n * n) := by
  unfold primeFactor
  split_ifs with h
  · exact local_index_bound n ⟨p, h⟩
  · exact one_dvd _

theorem primeFactor_pos (n p : ℕ) : 0 < primeFactor n p := by
  unfold primeFactor
  split_ifs with h
  · have hd := local_index_bound n ⟨p, h⟩
    exact Nat.pos_of_dvd_of_pos hd (pow_pos (Nat.prime_of_mem_primeFactors h).pos _)
  · exact Nat.one_pos

theorem primeFactor_eq_one_of_lt {n p : ℕ} (h : n < p) : primeFactor n p = 1 := by
  have hmem : p ∉ (denominator (toeplitz n)).primeFactors := by
    rw [denominator_primeFactors]
    exact fun hp => h.not_ge (Nat.mem_primesLE.mp hp).1
  rw [primeFactor, dite_eq_right hmem]

theorem primeFactor_large (n p : ℕ) (hp : p ∈ Nat.primesLE n) (hbig : n < p^2) :
    primeFactor n p = p^(n-p+1) := by
  have hmem : p ∈ (denominator (toeplitz n)).primeFactors := by
    rwa [denominator_primeFactors]
  rw [primeFactor, dite_eq_left hmem]
  exact local_index_large n ⟨p, hmem⟩ hbig

/-- The exact global graph index is the product of the local factors. -/
theorem graphIndex_eq_prod (n : ℕ) : graphIndex n = ∏ p ∈ Nat.primesLE n, primeFactor n p := by
  unfold graphIndex
  rw [global_index, ← denominator_primeFactors,
    ← prod_coe_sort ((denominator (toeplitz n)).primeFactors) (primeFactor n)]
  apply prod_congr rfl
  intro q _
  simp only [primeFactor, dite_eq_left q.property]

end Omega.RationalMatrixGraph.Toeplitz
