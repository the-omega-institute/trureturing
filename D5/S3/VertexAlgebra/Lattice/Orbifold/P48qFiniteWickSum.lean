/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFiniteWickSum
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factorial-weighted Wick sums at a symbolic positive source degree. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qWickPermutation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Factorial-weighted finite Wick sums in the positive-degree source variable.

For the cover-graded application, fix the cover exponent and the matrix
element before choosing the retained-word readout. At source degree d use
native oscillator indices of levels 1 through d for the alphabet. Every
word contributing to degree d has total level d, so the input level shift
in the all-jet Wick coefficient cancels and the leaf depends only on the
retained word and the fixed cover exponent.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteWickSum

open P48qArbitraryWickRecursion (normalWick normalWick_nil normalWick_step normalWick_perm)
open PowerSeries (coeff constantCoeff C)

variable {I J R : Type*}

/-- The list of jet labels, with one entry for each tuple position. -/
def word (ι : J → I) {n : ℕ} (f : Fin n → J) : List I :=
  List.ofFn (fun i => ι (f i))

@[simp] theorem word_length (ι : J → I) {n : ℕ} (f : Fin n → J) :
    (word ι f).length = n := List.length_ofFn

private theorem word_succ (ι : J → I) {n : ℕ} (f : Fin (n + 1) → J) :
    word ι f = ι (f 0) :: word ι (Fin.tail f) := List.ofFn_succ

private theorem word_get (ι : J → I) {n : ℕ} (f : Fin n → J) (j : Fin n) :
    (word ι f).get (Fin.cast (word_length ι f).symm j) = ι (f j) := by
  exact List.get_ofFn (fun i => ι (f i)) (Fin.cast (word_length ι f).symm j)

private theorem tail_removeNth_succ {n : ℕ} (j : Fin (n + 1)) (f : Fin (n + 2) → J) :
    Fin.tail (j.succ.removeNth f) = j.removeNth (Fin.tail f) := by
  funext i
  simp only [Fin.tail, Fin.removeNth_apply, Fin.succ_succAbove_succ]

private theorem head_removeNth_succ {n : ℕ} (j : Fin (n + 1)) (f : Fin (n + 2) → J) :
    j.succ.removeNth f 0 = f 0 := by
  simp only [Fin.removeNth_apply, Fin.succ_succAbove_zero]

private theorem word_erase (ι : J → I) {n : ℕ} (p : Fin (n + 1)) (f : Fin (n + 1) → J) :
    (word ι f).eraseIdx p.val = word ι (p.removeNth f) := by
  induction n with
  | zero =>
    have hp : p = 0 := Fin.eq_zero p
    subst p
    simp only [word_succ ι f, Fin.removeNth_zero, Fin.val_zero, List.eraseIdx_cons_zero]
  | succ n ih =>
    cases p using Fin.cases with
    | zero =>
      simp only [word_succ ι f, Fin.removeNth_zero, Fin.val_zero, List.eraseIdx_cons_zero]
    | succ p =>
      change (word ι f).eraseIdx (p.val + 1) = word ι (p.succ.removeNth f)
      rw [word_succ ι f, List.eraseIdx_cons_succ, ih p (Fin.tail f),
        word_succ ι (p.succ.removeNth f), head_removeNth_succ, tail_removeNth_succ]

private theorem word_perm_marked (ι : J → I) {n : ℕ} (p : Fin (n + 1))
    (f : Fin (n + 1) → J) :
    (word ι f).Perm (ι (f p) :: word ι (p.removeNth f)) := by
  have hp : p.val < (word ι f).length := (word_length ι f).symm ▸ p.isLt
  have h := (List.getElem_cons_eraseIdx_perm hp).symm
  change (word ι f).Perm
    ((word ι f).get (Fin.cast (word_length ι f).symm p) :: (word ι f).eraseIdx p.val) at h
  rwa [word_get, word_erase] at h

variable [CommRing R]

/-- Product of the weights of all positions of a tuple. -/
def weight (s : J → PowerSeries R) {n : ℕ} (f : Fin n → J) : PowerSeries R :=
  ∏ i, s (f i)

private abbrev D : Derivation R (PowerSeries R) (PowerSeries R) :=
  PowerSeries.derivative

private theorem derivative_mul (a b : PowerSeries R) :
    D (a * b) = D a * b + a * D b := by
  simpa only [smul_eq_mul, mul_comm b (D a), add_comm] using
    (PowerSeries.derivative (R := R)).leibniz a b

private theorem derivative_weight_succ (s : J → PowerSeries R) {n : ℕ}
    (f : Fin (n + 1) → J) :
    D (weight s f) =
      ∑ p : Fin (n + 1), D (s (f p)) * weight s (p.removeNth f) := by
  induction n with
  | zero =>
    simp only [weight, Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ,
      Fin.sum_univ_zero, mul_one, add_zero]
  | succ n ih =>
    have hweight : weight s f = s (f 0) * weight s (Fin.tail f) :=
      Fin.prod_univ_succ (fun i => s (f i))
    have htail : ∀ p : Fin (n + 1),
        weight s (p.succ.removeNth f) =
          s (f 0) * weight s (p.removeNth (Fin.tail f)) := by
      intro p
      unfold weight
      rw [Fin.prod_univ_succ (fun i => s (p.succ.removeNth f i)),
        head_removeNth_succ]
      change _ * weight s (Fin.tail (p.succ.removeNth f)) = _
      exact congrArg (fun g => s (f 0) * weight s g) (tail_removeNth_succ p f)
    rw [hweight, derivative_mul, ih (Fin.tail f),
      Fin.sum_univ_succ (fun p : Fin (n + 2) => D (s (f p)) * weight s (p.removeNth f)),
      Fin.removeNth_zero, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [htail p]
    change s (f 0) * (D (s (f p.succ)) * weight s (p.removeNth (Fin.tail f))) = _
    ring

variable [Fintype J]

private def weightedSum (ι : J → I) (s : J → PowerSeries R) (n : ℕ)
    (K : List I → PowerSeries R) : PowerSeries R :=
  ∑ f : Fin n → J, weight s f * K (word ι f)

/-- Split a fixed marked occurrence from a tuple. The remainder stays in its original order. -/
theorem sum_marked (ι : J → I) (s b : J → PowerSeries R) {n : ℕ}
    (p : Fin (n + 1)) (K : J → List I → PowerSeries R) :
    (∑ f : Fin (n + 1) → J, b (f p) * weight s (p.removeNth f) *
        K (f p) (word ι (p.removeNth f))) =
      ∑ x : J, b x * (∑ g : Fin n → J, weight s g * K x (word ι g)) := by
  classical
  calc
    _ = ∑ xg : J × (Fin n → J), b xg.1 * weight s xg.2 * K xg.1 (word ι xg.2) :=
      Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => J) p).symm _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.mul_sum, mul_assoc]

section Algebra

variable [Algebra ℂ R]

private abbrev scalar : ℂ →+* PowerSeries R := algebraMap ℂ (PowerSeries R)

private theorem scalar_eq_C (c : ℂ) : scalar (R := R) c = C (algebraMap ℂ R c) :=
  PowerSeries.algebraMap_apply

private theorem C_smul (c : ℂ) (r : R) :
    C (c • r) = scalar (R := R) c * C r := by
  rw [Algebra.smul_def, scalar_eq_C, map_mul]

private theorem derivative_scalar_mul (c : ℂ) (g : PowerSeries R) :
    D (scalar (R := R) c * g) = scalar (R := R) c * D g := by
  simp only [derivative_mul, scalar_eq_C, PowerSeries.derivative_C, zero_mul, zero_add]

/-- The length-n summand, including the inverse factorial. -/
def factorialSum (ι : J → I) (s : J → PowerSeries R) (n : ℕ)
    (K : List I → PowerSeries R) : PowerSeries R :=
  scalar (R := R) ((n.factorial : ℂ)⁻¹) * weightedSum ι s n K

private theorem factorialSum_add (ι : J → I) (s : J → PowerSeries R) (n : ℕ)
    (K L : List I → PowerSeries R) :
    factorialSum ι s n (fun w => K w + L w) =
      factorialSum ι s n K + factorialSum ι s n L := by
  simp only [factorialSum, weightedSum, mul_add, Finset.sum_add_distrib]

private theorem factorialSum_mul_left (ι : J → I) (s : J → PowerSeries R) (n : ℕ)
    (a : PowerSeries R) (K : List I → PowerSeries R) :
    factorialSum ι s n (fun w => a * K w) = a * factorialSum ι s n K := by
  simp only [factorialSum, weightedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

@[simp] private theorem factorialSum_zero (ι : J → I) (s : J → PowerSeries R)
    (K : List I → PowerSeries R) : factorialSum ι s 0 K = K [] := by
  classical
  simp [factorialSum, weightedSum, word, weight]

private theorem cancel_factorial_succ (n : ℕ) (a : PowerSeries R) :
    scalar (R := R) (((n + 1).factorial : ℂ)⁻¹) * ((↑(n + 1 : ℕ) : PowerSeries R) * a) =
      scalar (R := R) ((n.factorial : ℂ)⁻¹) * a := by
  have hn : ((↑(n + 1 : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h : (((n + 1).factorial : ℂ)⁻¹) * (↑(n + 1 : ℕ) : ℂ) =
      (n.factorial : ℂ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp [hn, hf]
  rw [← mul_assoc, ← map_natCast (scalar (R := R)), ← map_mul, h]

/-- The pointed Leibniz identity with arbitrary permutation-invariant readout. -/
theorem derivative_factorialSum_succ (ι : J → I) (s : J → PowerSeries R)
    (K : List I → R) (hK : ∀ {u v : List I}, u.Perm v → K u = K v) (n : ℕ) :
    D (factorialSum ι s (n + 1) (fun w => C (K w))) =
      ∑ x : J, D (s x) * factorialSum ι s n (fun w => C (K (ι x :: w))) := by
  classical
  have hsum :
      D (weightedSum ι s (n + 1) (fun w => C (K w))) =
        (↑(n + 1 : ℕ) : PowerSeries R) *
          ∑ x : J, D (s x) * weightedSum ι s n (fun w => C (K (ι x :: w))) := by
    calc
      _ = ∑ f : Fin (n + 1) → J, ∑ p : Fin (n + 1),
          D (s (f p)) * weight s (p.removeNth f) *
            C (K (ι (f p) :: word ι (p.removeNth f))) := by
        unfold weightedSum
        simp only [map_sum, derivative_mul, PowerSeries.derivative_C, mul_zero, add_zero,
          derivative_weight_succ]
        apply Finset.sum_congr rfl
        intro f _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        simp only [hK (word_perm_marked ι p f)]
      _ = _ := by
        rw [Finset.sum_comm]
        simp_rw [sum_marked ι s (fun x => D (s x)) _
          (fun x w => C (K (ι x :: w)))]
        simp [weightedSum, Finset.sum_const, nsmul_eq_mul]
  simp only [factorialSum, derivative_scalar_mul, hsum, cancel_factorial_succ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Sum a readout over the choice of one occurrence and its ordered remainder. -/
def sumErase (K : I → List I → PowerSeries R) (w : List I) : PowerSeries R :=
  ∑ p : Fin w.length, K (w.get p) (w.eraseIdx p.val)

omit [Fintype J] [Algebra ℂ R] in
private theorem sumErase_word (ι : J → I) {n : ℕ} (f : Fin (n + 1) → J)
    (K : I → List I → PowerSeries R) :
    sumErase K (word ι f) =
      ∑ p : Fin (n + 1), K (ι (f p)) (word ι (p.removeNth f)) := by
  unfold sumErase
  apply Fintype.sum_equiv (finCongr (word_length ι f))
  intro p
  let q := Fin.cast (word_length ι f) p
  change K ((word ι f).get p) ((word ι f).eraseIdx p.val) =
    K (ι (f q)) (word ι (q.removeNth f))
  have hget := word_get ι f q
  have herase := word_erase ι q f
  simpa [q] using congrArg₂ K hget herase

/-- Apply the same marked-occurrence split to the tail partner in the Wick recursion. -/
theorem factorialSum_sumErase_succ (ι : J → I) (s : J → PowerSeries R) (n : ℕ)
    (K : I → List I → PowerSeries R) :
    factorialSum ι s (n + 1) (sumErase K) =
      ∑ x : J, s x * factorialSum ι s n (K (ι x)) := by
  classical
  have hsum :
      weightedSum ι s (n + 1) (sumErase K) =
        (↑(n + 1 : ℕ) : PowerSeries R) *
          ∑ x : J, s x * weightedSum ι s n (K (ι x)) := by
    calc
      _ = ∑ f : Fin (n + 1) → J, ∑ p : Fin (n + 1),
          s (f p) * weight s (p.removeNth f) *
            K (ι (f p)) (word ι (p.removeNth f)) := by
        unfold weightedSum
        apply Finset.sum_congr rfl
        intro f _
        rw [sumErase_word, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [show weight s f = s (f p) * weight s (p.removeNth f) from
          Fin.prod_univ_succAbove (fun i => s (f i)) p]
      _ = _ := by
        rw [Finset.sum_comm]
        simp_rw [sum_marked ι s s _ (fun x => K (ι x))]
        simp [weightedSum, Finset.sum_const, nsmul_eq_mul]
  simp only [factorialSum, hsum, cancel_factorial_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private def VanishesBelow (n : ℕ) (g : PowerSeries R) : Prop :=
  ∀ d < n, coeff d g = 0

omit [Algebra ℂ R] in
private theorem vanishes_mul {m n : ℕ} {f g : PowerSeries R}
    (hf : VanishesBelow m f) (hg : VanishesBelow n g) : VanishesBelow (m + n) (f * g) := by
  intro d hd
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hdegree := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : p.1 < m
  · rw [hf _ h, zero_mul]
  · rw [hg _ (by omega), mul_zero]

omit [Fintype J] [Algebra ℂ R] in
private theorem weight_vanishes (s : J → PowerSeries R) (hs : ∀ j, constantCoeff (s j) = 0)
    {n : ℕ} (f : Fin n → J) : VanishesBelow n (weight s f) := by
  induction n with
  | zero => intro d hd; omega
  | succ n ih =>
    have hhead : VanishesBelow 1 (s (f 0)) := by
      intro d hd
      have h : d = 0 := by omega
      rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply, hs]
    rw [show weight s f = s (f 0) * weight s (Fin.tail f) from
      Fin.prod_univ_succ (fun i => s (f i))]
    simpa only [Nat.add_comm 1 n] using vanishes_mul hhead (ih (Fin.tail f))

private theorem factorialSum_vanishes (ι : J → I) (s : J → PowerSeries R)
    (hs : ∀ j, constantCoeff (s j) = 0) (n : ℕ) (K : List I → PowerSeries R) :
    VanishesBelow n (factorialSum ι s n K) := by
  have h : VanishesBelow n (weightedSum ι s n K) := by
    intro d hd
    rw [weightedSum, map_sum]
    apply Finset.sum_eq_zero
    intro f _
    have hterm := vanishes_mul (weight_vanishes s hs f)
      (show VanishesBelow 0 (K (word ι f)) from fun k hk => by omega)
    exact hterm d (by simpa using hd)
  simpa only [zero_add, factorialSum] using
    (vanishes_mul (show VanishesBelow 0 (scalar (R := R) ((n.factorial : ℂ)⁻¹)) from
      fun k hk => by omega) h)

/-- In degree d, sum all lengths from zero through d. -/
def sumByDegree (T : ℕ → PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun d => ∑ n ∈ Finset.range (d + 1), coeff d (T n))

omit [Algebra ℂ R] in
@[simp] theorem coeff_sumByDegree (T : ℕ → PowerSeries R) (d : ℕ) :
    coeff d (sumByDegree T) = ∑ n ∈ Finset.range (d + 1), coeff d (T n) :=
  PowerSeries.coeff_mk _ _

omit [Algebra ℂ R] in
private theorem coeff_sumByDegree_to (T : ℕ → PowerSeries R)
    (hT : ∀ n, VanishesBelow n (T n)) (d k : ℕ) (hk : d + 1 ≤ k) :
    coeff d (sumByDegree T) = ∑ n ∈ Finset.range k, coeff d (T n) := by
  rw [coeff_sumByDegree]
  apply Finset.sum_subset (Finset.range_mono hk)
  intro n _ hn
  simp only [Finset.mem_range] at hn
  exact hT n d (by omega)

omit [Algebra ℂ R] in
private theorem sumByDegree_add (T U : ℕ → PowerSeries R) :
    sumByDegree (fun n => T n + U n) = sumByDegree T + sumByDegree U := by
  apply PowerSeries.ext
  intro d
  simp only [coeff_sumByDegree, map_add, Finset.sum_add_distrib]

omit [Algebra ℂ R] in
private theorem sumByDegree_sum {B : Type*} [Fintype B] (T : B → ℕ → PowerSeries R) :
    sumByDegree (fun n => ∑ b, T b n) = ∑ b, sumByDegree (T b) := by
  apply PowerSeries.ext
  intro d
  simp only [coeff_sumByDegree, map_sum]
  rw [Finset.sum_comm]

omit [Algebra ℂ R] in
private theorem sumByDegree_mul_left (a : PowerSeries R) (T : ℕ → PowerSeries R)
    (hT : ∀ n, VanishesBelow n (T n)) :
    sumByDegree (fun n => a * T n) = a * sumByDegree T := by
  apply PowerSeries.ext
  intro d
  simp only [coeff_sumByDegree]
  simp only [PowerSeries.coeff_mul d a]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpd := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [coeff_sumByDegree_to T hT p.2 (d + 1) (by omega), Finset.mul_sum]

private def shiftMul (a : PowerSeries R) (T : ℕ → PowerSeries R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => a * T n

omit [Algebra ℂ R] in
/-- The partner uses an extra positive-degree letter, which lets its length be shifted. -/
private theorem sumByDegree_shiftMul (a : PowerSeries R) (ha : constantCoeff a = 0)
    (T : ℕ → PowerSeries R) (hT : ∀ n, VanishesBelow n (T n)) :
    sumByDegree (shiftMul a T) = a * sumByDegree T := by
  apply PowerSeries.ext
  intro d
  rw [coeff_sumByDegree, Finset.sum_range_succ']
  simp only [shiftMul, map_zero, add_zero, PowerSeries.coeff_mul d a]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpd := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : p.1 = 0
  · simp [h, PowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
  · rw [coeff_sumByDegree_to T hT p.2 d (by omega), Finset.mul_sum]

omit [Algebra ℂ R] in
private theorem derivative_sumByDegree (T : ℕ → PowerSeries R) (hzero : D (T 0) = 0) :
    D (sumByDegree T) = sumByDegree (fun n => D (T (n + 1))) := by
  apply PowerSeries.ext
  intro d
  have h := congrArg (coeff d) hzero
  rw [PowerSeries.coeff_derivative, map_zero] at h
  rw [PowerSeries.coeff_derivative, coeff_sumByDegree, Finset.sum_range_succ',
    coeff_sumByDegree, add_mul, Finset.sum_mul, h, add_zero]
  simp only [PowerSeries.coeff_derivative]

/-- Coefficientwise factorial-weighted sum with a fixed word readout. -/
def wordSeries (ι : J → I) (s : J → PowerSeries R) (K : List I → R) : PowerSeries R :=
  sumByDegree (fun n => factorialSum ι s n (fun w => C (K w)))

@[simp] theorem constantCoeff_wordSeries (ι : J → I) (s : J → PowerSeries R)
    (K : List I → R) : constantCoeff (wordSeries ι s K) = K [] := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [wordSeries]

private theorem derivative_wordSeries (ι : J → I) (s : J → PowerSeries R)
    (hs : ∀ j, constantCoeff (s j) = 0)
    (K : List I → R) (hK : ∀ {u v : List I}, u.Perm v → K u = K v) :
    D (wordSeries ι s K) = ∑ x : J, D (s x) * wordSeries ι s (fun w => K (ι x :: w)) := by
  unfold wordSeries
  have hzero : D (factorialSum ι s 0 (fun w => C (K w))) = 0 := by simp
  rw [derivative_sumByDegree _ hzero]
  simp_rw [derivative_factorialSum_succ ι s K hK, sumByDegree_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact sumByDegree_mul_left _ _ (fun n => factorialSum_vanishes ι s hs n _)

variable (ι : J → I) (s : J → PowerSeries R) (A : Matrix I I ℂ) (μ : I → ℂ)
variable (N : List I → R)

/-- The finite Wick expansion, summed coefficientwise over all input lengths. -/
def wickSeries (pre : List I) : PowerSeries R :=
  wordSeries ι s (fun w => normalWick A μ N w pre)

/-- The series of retained words with an arbitrary retained prefix. -/
def retainedSeries (pre : List I) : PowerSeries R :=
  wordSeries ι s (fun w => N (pre ++ w))

/-- The singleton primitive in the source variable. -/
def singletonPrimitive : PowerSeries R :=
  ∑ x : J, μ (ι x) • s x

private def pairRow (x : J) : PowerSeries R :=
  ∑ y : J, scalar (A (ι x) (ι y)) * s y

/-- The ordered pair primitive. The exponential uses half of this series. -/
def pairPrimitive : PowerSeries R :=
  ∑ x : J, s x * pairRow ι s A x

theorem pairPrimitive_eq_sum :
    pairPrimitive ι s A =
      ∑ x : J, ∑ y : J, A (ι x) (ι y) • (s x * s y) := by
  simp only [pairPrimitive, pairRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Algebra.smul_def]
  change s x * (scalar (A (ι x) (ι y)) * s y) = scalar (A (ι x) (ι y)) * (s x * s y)
  ring

private theorem constantCoeff_pairRow (hs : ∀ j, constantCoeff (s j) = 0) (x : J) :
    constantCoeff (pairRow ι s A x) = 0 := by
  simp only [pairRow, map_sum, map_mul, hs, mul_zero, Finset.sum_const_zero]

private theorem headWick_factorialSum (x : J) (pre : List I) (n : ℕ) :
    factorialSum ι s n (fun w => C (normalWick A μ N (ι x :: w) pre)) =
      factorialSum ι s n (fun w => C (normalWick A μ N w (pre ++ [ι x]))) +
      scalar (μ (ι x)) * factorialSum ι s n (fun w => C (normalWick A μ N w pre)) +
      shiftMul (pairRow ι s A x)
        (fun m => factorialSum ι s m (fun w => C (normalWick A μ N w pre))) n := by
  have hstep : (fun w => C (normalWick A μ N (ι x :: w) pre)) =
      (fun w => C (normalWick A μ N w (pre ++ [ι x])) +
        scalar (μ (ι x)) * C (normalWick A μ N w pre) +
        sumErase (fun j rest => scalar (A (ι x) j) * C (normalWick A μ N rest pre)) w) := by
    funext w
    rw [normalWick_step]
    simp only [map_add, map_sum, C_smul, sumErase]
  rw [hstep, factorialSum_add, factorialSum_add, factorialSum_mul_left]
  congr 1
  cases n with
  | zero => simp [shiftMul, sumErase]
  | succ n =>
    rw [factorialSum_sumErase_succ]
    simp only [shiftMul, factorialSum_mul_left, pairRow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring

private theorem headWick_wordSeries (hs : ∀ j, constantCoeff (s j) = 0)
    (x : J) (pre : List I) :
    wordSeries ι s (fun w => normalWick A μ N (ι x :: w) pre) =
      wickSeries ι s A μ N (pre ++ [ι x]) +
      scalar (μ (ι x)) * wickSeries ι s A μ N pre +
      pairRow ι s A x * wickSeries ι s A μ N pre := by
  unfold wickSeries wordSeries
  simp_rw [headWick_factorialSum, sumByDegree_add]
  rw [sumByDegree_mul_left _ _ (fun n => factorialSum_vanishes ι s hs n _),
    sumByDegree_shiftMul _ (constantCoeff_pairRow ι s A hs x) _
      (fun n => factorialSum_vanishes ι s hs n _)]

private def prefixRhs (ι : J → I) (s : J → PowerSeries R)
    (b : PowerSeries R) (H : List I → PowerSeries R) (pre : List I) : PowerSeries R :=
  (∑ x : J, D (s x) * H (pre ++ [ι x])) + b * H pre

private def wickSlope : PowerSeries R :=
  ∑ x : J, D (s x) * (scalar (μ (ι x)) + pairRow ι s A x)

private theorem derivative_wickSeries (hs : ∀ j, constantCoeff (s j) = 0)
    (hA : ∀ x y, A x y = A y x)
    (hN : ∀ {u v : List I}, u.Perm v → N u = N v) (pre : List I) :
    D (wickSeries ι s A μ N pre) =
      prefixRhs ι s (wickSlope ι s A μ) (wickSeries ι s A μ N) pre := by
  change D (wordSeries ι s (fun w => normalWick A μ N w pre)) = _
  rw [derivative_wordSeries ι s hs _ (fun h => normalWick_perm A μ N hA hN h pre)]
  simp_rw [headWick_wordSeries ι s A μ N hs]
  simp only [prefixRhs, wickSlope, Finset.sum_mul, mul_add, add_mul, mul_assoc,
    Finset.sum_add_distrib, add_assoc]

private theorem derivative_retainedSeries (hs : ∀ j, constantCoeff (s j) = 0)
    (hN : ∀ {u v : List I}, u.Perm v → N u = N v) (pre : List I) :
    D (retainedSeries ι s N pre) =
      ∑ x : J, D (s x) * retainedSeries ι s N (pre ++ [ι x]) := by
  unfold retainedSeries
  rw [derivative_wordSeries ι s hs _ (fun h => hN (h.append_left pre))]
  simp only [List.append_assoc, List.singleton_append]

private def primitive : PowerSeries R :=
  singletonPrimitive ι s μ + (1 / 2 : ℂ) • pairPrimitive ι s A

private theorem constantCoeff_primitive (hs : ∀ j, constantCoeff (s j) = 0) :
    constantCoeff (primitive ι s A μ) = 0 := by
  simp only [primitive, Algebra.smul_def, singletonPrimitive, pairPrimitive,
    map_add, map_sum, map_mul, hs, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

private theorem derivative_pairPrimitive (hA : ∀ x y, A x y = A y x) :
    D (pairPrimitive ι s A) = 2 * ∑ x : J, D (s x) * pairRow ι s A x := by
  have hswap :
      (∑ x : J, s x * D (pairRow ι s A x)) =
        ∑ x : J, D (s x) * pairRow ι s A x := by
    simp only [pairRow, map_sum, derivative_scalar_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hA (ι y) (ι x)]
    ring
  simp only [pairPrimitive, map_sum, derivative_mul, Finset.sum_add_distrib]
  rw [hswap, two_mul]

private theorem derivative_primitive (hA : ∀ x y, A x y = A y x) :
    D (primitive ι s A μ) = wickSlope ι s A μ := by
  have hhalf : scalar (R := R) (1 / 2 : ℂ) * (2 : PowerSeries R) = 1 := by
    have htwo : scalar (R := R) (2 : ℂ) = (2 : PowerSeries R) :=
      map_ofNat (scalar (R := R)) 2
    rw [← htwo, ← map_mul]
    norm_num
  rw [primitive, map_add, Algebra.smul_def, derivative_scalar_mul,
    derivative_pairPrimitive ι s A hA, ← mul_assoc, hhalf, one_mul]
  simp only [singletonPrimitive, wickSlope, Algebra.smul_def, map_sum, derivative_scalar_mul,
    mul_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

/-- Uniqueness for the indicated prefix equations, by induction on degree for every prefix. -/
private theorem prefix_uniqueness (ι : J → I) (s : J → PowerSeries R) (b : PowerSeries R)
    (H K : List I → PowerSeries R)
    (hH : ∀ pre, D (H pre) = prefixRhs ι s b H pre)
    (hK : ∀ pre, D (K pre) = prefixRhs ι s b K pre)
    (h0 : ∀ pre, constantCoeff (H pre) = constantCoeff (K pre)) (pre : List I) :
    H pre = K pre := by
  have hall : ∀ d pre, coeff d (H pre) = coeff d (K pre) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro pre
      cases d with
      | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0 pre
      | succ d =>
        have hmul (a : PowerSeries R) (p : List I) :
            coeff d (a * H p) = coeff d (a * K p) := by
          rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
          apply Finset.sum_congr rfl
          intro ij hij
          have hdegree := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
          rw [ih ij.2 (by omega) p]
        have hrhs : coeff d (prefixRhs ι s b H pre) =
            coeff d (prefixRhs ι s b K pre) := by
          simp only [prefixRhs, map_add, map_sum, hmul]
        have h := (congrArg (coeff d) (hH pre)).trans
          (hrhs.trans (congrArg (coeff d) (hK pre)).symm)
        simp only [PowerSeries.coeff_derivative] at h
        have hn : (d + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
        apply (smul_right_inj hn).mp
        simpa [Algebra.smul_def, mul_comm] using h
  exact PowerSeries.ext (fun d => hall d pre)

variable [Algebra ℚ R]

/--
The finite Wick sum factors in the actual source variable. All input lengths
are included at each coefficient according to their positive source degrees.
The retained-word evaluation is any permutation-invariant function, and
the retained prefix is arbitrary.
-/
theorem wickSeries_eq_exp_mul_retainedSeries
    (hs : ∀ j, constantCoeff (s j) = 0)
    (hA : ∀ x y, A x y = A y x)
    (hN : ∀ {u v : List I}, u.Perm v → N u = N v) (pre : List I) :
    wickSeries ι s A μ N pre =
      (PowerSeries.exp R).subst
        (singletonPrimitive ι s μ + (1 / 2 : ℂ) • pairPrimitive ι s A) *
        retainedSeries ι s N pre := by
  let E := (PowerSeries.exp R).subst (primitive ι s A μ)
  change wickSeries ι s A μ N pre = E * retainedSeries ι s N pre
  have hp := constantCoeff_primitive ι s A μ hs
  have hE : D E = E * wickSlope ι s A μ := by
    dsimp only [E]
    rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hp),
      PowerSeries.derivative_exp, derivative_primitive ι s A μ hA]
  have hE0 : constantCoeff E = 1 := by
    change MvPowerSeries.constantCoeff ((PowerSeries.exp R).subst (primitive ι s A μ)) = 1
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hp]
    simp
  have hprod (p : List I) :
      D (E * retainedSeries ι s N p) =
        prefixRhs ι s (wickSlope ι s A μ) (fun q => E * retainedSeries ι s N q) p := by
    rw [derivative_mul, hE, derivative_retainedSeries ι s N hs hN]
    unfold prefixRhs
    have hkeep :
        E * (∑ x : J, D (s x) * retainedSeries ι s N (p ++ [ι x])) =
          ∑ x : J, D (s x) * (E * retainedSeries ι s N (p ++ [ι x])) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hkeep]
    ring
  exact prefix_uniqueness ι s (wickSlope ι s A μ) (wickSeries ι s A μ N)
    (fun p => E * retainedSeries ι s N p)
    (derivative_wickSeries ι s A μ N hs hA hN) hprod
    (fun p => by simp [wickSeries, retainedSeries, hE0, normalWick_nil]) pre

#print axioms word_length
#print axioms sum_marked
#print axioms derivative_factorialSum_succ
#print axioms factorialSum_sumErase_succ
#print axioms coeff_sumByDegree
#print axioms constantCoeff_wordSeries
#print axioms pairPrimitive_eq_sum
#print axioms wickSeries_eq_exp_mul_retainedSeries

end Algebra

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteWickSum
