import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport

/-! The actual signed BBH weak associativity in the two prescribed expansion
domains. The truncation of the first field on the input fixes the cutoff. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBHUniformWeakAssociativity

open ActualLeechHyperbolic (leechData)
open NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open NativeBBOCoefficientTransport (P Q bb fixedH)
open FourPoint.NativeBBHHActualVectorJacobi (bbhh_actual_vector_coefficient_jacobi)

open private p_tail bb_tail choose_int bb_hahn_iterate from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport

local notation "B" => TwistedOdd
local notation "H" => TwistedEven

/-- The degree-`j` Taylor contribution to the coefficient at `(s,t)`.
The outer variable has integer exponents. The exponents of the third or
inner variable may lie in any fixed coset of the integers. In the BBH
application the labels denote `y^s z^(t-1/2)`. -/
def taylorTerm {V : Type*} [SMul ℂ V] (a : ℂ) (F : ℤ → ℤ → V)
    (s t : ℤ) (j : ℕ) : V :=
  (a ^ j * Ring.choose ((s : ℂ) + j) j) • F (s + j) (t - j)

/-- Coefficient array of Taylor translation by `a*z`, in nonnegative
powers of `z`. The summands are finitely supported for a lower `z`-bound. -/
def taylor {V : Type*} [AddCommMonoid V] [SMul ℂ V] (a : ℂ)
    (F : ℤ → ℤ → V) (s t : ℤ) : V :=
  ∑ᶠ j : ℕ, taylorTerm a F s t j

private theorem finite_of_tail {V : Type*} [Zero V] (f : ℕ → V) (N : ℕ)
    (hz : ∀ j ≥ N, f j = 0) : Function.HasFiniteSupport f :=
  (Set.finite_lt_nat N).subset fun j hj => lt_of_not_ge fun h => hj (hz j h)

/-- If `F` vanishes below inner label `T`, precisely the range
`0 ≤ j < max(0,t-T+1)` can contribute to Taylor translation. -/
theorem taylorTerm_eq_zero {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (a : ℂ) (F : ℤ → ℤ → V) (T : ℤ) (hF : ∀ s t, t < T → F s t = 0)
    (s t : ℤ) (j : ℕ) (hj : (t - T + 1).toNat ≤ j) :
    taylorTerm a F s t j = 0 := by
  rw [taylorTerm, hF _ _ (by omega), smul_zero]

theorem taylor_eq_sum_range {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (a : ℂ) (F : ℤ → ℤ → V) (T : ℤ) (hF : ∀ s t, t < T → F s t = 0)
    (s t : ℤ) :
    taylor a F s t = ∑ j ∈ Finset.range (t - T + 1).toNat, taylorTerm a F s t j := by
  unfold taylor
  exact finsum_eq_sum_of_support_subset _ (fun j hj => Finset.mem_range.mpr
    (lt_of_not_ge fun h => hj (taylorTerm_eq_zero a F T hF s t j h)))

/-- The coefficient of `y^s z^(t-1/2)` in
`y^(L+1/2) X_b(y) X_c(z) h`. The assignments are `P_b` on H and
`-Q_b` on O, in physical mode labels `n+1/2`. -/
def weightedProduct (b c : B) (h : H) (L s t : ℤ) : H :=
  -(Q b (L - s - 1) (P c (-t - 1) h))

/-- The coefficient of `y^s z^t` in the unweighted native BBH iterate.
Here `bb` is the ordinary extension product and `fixedH` is the native
fixed action on the complementary twisted states. -/
def iterate (b c : B) (h : H) (s t : ℤ) : H :=
  fixedH (bb b c (-s - 1)) (-t - 1) h

/-- The degree-`j` contribution to `y^s z^(t-1/2)` from
`(z+y)^(L+1/2)` expanded in nonnegative powers of `y`. -/
def iterateTerm (b c : B) (h : H) (L s t : ℤ) (j : ℕ) : H :=
  Ring.choose ((L : ℂ) + 1 / 2) j • iterate b c h (s - j) (t - L + j - 1)

/-- Coefficients in the iterate chart, with nonnegative powers of `y`
in the binomial factor. -/
def weightedIterate (b c : B) (h : H) (L s t : ℤ) : H :=
  ∑ᶠ j : ℕ, iterateTerm b c h L s t j

theorem weightedProduct_lower (b c : B) (h : H) (L C : ℤ)
    (hC : ∀ n ≥ C, P c n h = 0) (s t : ℤ) (ht : t < -C) :
    weightedProduct b c h L s t = 0 := by
  rw [weightedProduct, hC _ (by omega : C ≤ -t - 1), map_zero]
  apply Subtype.ext
  simp only [Submodule.coe_neg, Submodule.coe_zero, neg_zero]

theorem iterateTerm_eq_zero (b c : B) (h : H) (L M s t : ℤ)
    (hM : ∀ n ≥ M, bb b c n = 0) (j : ℕ) (hj : (M + s + 1).toNat ≤ j) :
    iterateTerm b c h L s t j = 0 := by
  have hzero : bb b c (-(s - (j : ℤ)) - 1) = 0 := hM _ (by omega)
  unfold iterateTerm iterate
  rw [hzero]
  apply Subtype.ext
  change Ring.choose ((L : ℂ) + 1 / 2) j •
    (LatticeHalfFockCorrectedField.correctedField leechData leechUnit 0).coeff
      (2 * (t - L + j - 1)) h.val = 0
  simp

/-- Explicit finite ranges for both BBH expansions. `C` comes from the
literal inner mixed field and `M` from the native extension product. -/
theorem bbh_expansion_support (b c : B) (h : H) (L C M s t : ℤ)
    (hC : ∀ n ≥ C, P c n h = 0) (hM : ∀ n ≥ M, bb b c n = 0) :
    Function.HasFiniteSupport (taylorTerm 1 (weightedProduct b c h L) s t) ∧
    Function.HasFiniteSupport (iterateTerm b c h L s t) := by
  exact ⟨finite_of_tail _ (t - (-C) + 1).toNat
      (fun j => taylorTerm_eq_zero 1 _ (-C) (weightedProduct_lower b c h L C hC) s t j),
    finite_of_tail _ (M + s + 1).toNat
      (iterateTerm_eq_zero b c h L M s t hM)⟩

theorem bbh_expansions_finite (b c : B) (h : H) (L s t : ℤ) :
    Function.HasFiniteSupport (taylorTerm 1 (weightedProduct b c h L) s t) ∧
    Function.HasFiniteSupport (iterateTerm b c h L s t) := by
  obtain ⟨C, hC⟩ := p_tail c h
  obtain ⟨M, hM⟩ := bb_tail b c
  exact bbh_expansion_support b c h L C M s t hC hM

theorem weightedIterate_eq_sum_range (b c : B) (h : H) (L M s t : ℤ)
    (hM : ∀ n ≥ M, bb b c n = 0) :
    weightedIterate b c h L s t =
      ∑ j ∈ Finset.range (M + s + 1).toNat, iterateTerm b c h L s t j := by
  unfold weightedIterate
  exact finsum_eq_sum_of_support_subset _ (fun j hj => Finset.mem_range.mpr
    (lt_of_not_ge fun hj' => hj (iterateTerm_eq_zero b c h L M s t hM j hj')))

private theorem reflect_choose (r : ℂ) (j : ℕ) :
    Ring.choose ((j : ℂ) - r - 1) j = (-1 : ℂ)^j * Ring.choose r j := by
  have h := Ring.choose_neg (-r) j
  rw [neg_neg] at h
  rw [show (j : ℂ) - r - 1 = -r + j - 1 by ring, h]
  simp only [Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- Exact coefficient extraction for the Taylor side at
`y^(-r-1) z^(-p-3/2)`. -/
theorem taylorTerm_bbh (b c : B) (h : H) (L p r : ℤ) (j : ℕ) :
    taylorTerm 1 (weightedProduct b c h L) (-r - 1) (-p - 1) j =
    -(((-1 : ℂ)^j * Ring.choose (r : ℂ) j) • Q b (L + r - j) (P c (p + j) h)) := by
  unfold taylorTerm weightedProduct
  rw [show L - (-r - 1 + j) - 1 = L + r - j by omega,
    show -(-p - 1 - j) - 1 = p + j by omega]
  push_cast
  rw [show -(r : ℂ) - 1 + j = (j : ℂ) - r - 1 by ring, reflect_choose]
  simp only [one_pow, one_mul]
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_neg, smul_neg]

/-- Exact coefficient extraction in the opposite nested expansion. -/
theorem iterateTerm_bbh (b c : B) (h : H) (L p r : ℤ) (j : ℕ) :
    iterateTerm b c h L (-r - 1) (-p - 1) j =
      Ring.choose ((L : ℂ) + 1 / 2) j • fixedH (bb b c (r + j)) (p + L + 1 - j) h := by
  unfold iterateTerm iterate
  rw [show -(-r - 1 - j) - 1 = r + j by omega,
    show -(-p - 1 - L + j - 1) - 1 = p + L + 1 - j by omega]

/-- Every truncation cutoff for the literal first mixed field gives BBH
weak associativity with every second state. -/
theorem bbh_weak_associativity_of_tail (b : B) (h : H) (L : ℤ)
    (hL : ∀ n ≥ L, P b n h = 0) (c : B) :
    taylor 1 (weightedProduct b c h L) = weightedIterate b c h L := by
  funext s t
  let r := -s - 1
  let p := -t - 1
  have hs : -r - 1 = s := by dsimp [r]; omega
  have ht : -p - 1 = t := by dsimp [p]; omega
  rw [← hs, ← ht, taylor, weightedIterate]
  simp only [taylorTerm_bbh, iterateTerm_bbh]
  refine (finsum_neg_distrib (fun j : ℕ =>
    ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) • Q b (L + r - j) (P c (p + j) h))).trans ?_
  have he := bbhh_actual_vector_coefficient_jacobi b c h L p r
  simp only [choose_int,
    show ∀ j : ℕ, -2*(L+r)-3+2*(j : ℤ) = -2*(L+r-j)-3 by intro; ring,
    show ∀ j : ℕ, -2*(p+r)-3+2*(j : ℤ) = -2*(p+r-j)-3 by intro; ring,
    show ∀ j : ℕ, -2*p-3-2*(j : ℤ) = -2*(p+j)-3 by intro; ring,
    show ∀ j : ℕ, -2*L-3-2*(j : ℤ) = -2*(L+j)-3 by intro; ring,
    show ∀ j : ℕ, -2*r-2-2*(j : ℤ) = -2*(r+j)-2 by intro; ring,
    show ∀ j : ℕ, -2*(L+p+1)-2+2*(j : ℤ) = -2*(p+L+1-j)-2 by intro; ring,
    bb_hahn_iterate] at he
  have hz (j : ℕ) : P b (L + (j : ℤ)) h = 0 :=
    hL (L + j) (by omega)
  change _ + (∑ᶠ j : ℕ, ((-1 : ℂ) ^ (r + (j : ℤ)) * Ring.choose (r : ℂ) j) •
    Q c (p + r - j) (P b (L + j) h)) = _ at he
  have hswap :
      (∑ᶠ j : ℕ, ((-1 : ℂ) ^ (r + (j : ℤ)) * Ring.choose (r : ℂ) j) •
        Q c (p + r - j) (P b (L + j) h)) = 0 := by
    simp only [hz, map_zero, smul_zero, finsum_zero]
  rw [hswap, add_zero] at he
  exact he

/-- The actual uniform BBH weak associativity. The cutoff is obtained from
`X_b(z)h` and works for every `c` in the native odd twisted sector. -/
theorem bbh_uniform_weak_associativity (b : B) (h : H) :
    ∃ L : ℤ, (∀ n ≥ L, P b n h = 0) ∧
      ∀ c : B, taylor 1 (weightedProduct b c h L) = weightedIterate b c h L := by
  obtain ⟨L, hL⟩ := p_tail b h
  exact ⟨L, hL, bbh_weak_associativity_of_tail b h L hL⟩


section Translation

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Coefficientwise linear maps pass through finite Taylor translation. -/
theorem taylor_map {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W)
    (a : ℂ) (F : ℤ → ℤ → V) (T : ℤ) (hF : ∀ s t, t < T → F s t = 0) :
    taylor a (fun s t => g (F s t)) = fun s t => g (taylor a F s t) := by
  funext s t
  rw [taylor_eq_sum_range a _ T (fun s' t' ht => by rw [hF s' t' ht, map_zero]),
    taylor_eq_sum_range a F T hF, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [taylorTerm, map_smul]

theorem taylor_lower (a : ℂ) (F : ℤ → ℤ → V)
    (T : ℤ) (hF : ∀ s t, t < T → F s t = 0) (s t : ℤ) (ht : t < T) :
    taylor a F s t = 0 := by
  rw [taylor_eq_sum_range a F T hF, show (t - T + 1).toNat = 0 by omega]
  simp

omit [Module ℂ V] in
private theorem sum_triangle (n : ℕ) (f : ℕ → ℕ → V) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1), f i j) =
      ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1), f i (k - i) := by
  rw [Finset.sum_sigma' (σ := fun _ => ℕ) _ _ f,
    Finset.sum_sigma' (σ := fun _ => ℕ) _ _ (fun k i => f i (k-i))]
  refine Finset.sum_bij (fun ij _ => ⟨ij.1 + ij.2, ij.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨i,j⟩ hij
    simp only [Finset.mem_sigma, Finset.mem_range] at hij ⊢
    omega
  · rintro ⟨i,j⟩ _ ⟨i',j'⟩ _ he
    have hadd : i + j = i' + j' := congrArg Sigma.fst he
    have hi : i = i' := congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.2) he
    subst i'
    have : j = j' := by omega
    subst j'
    rfl
  · rintro ⟨k,i⟩ hki
    simp only [Finset.mem_sigma, Finset.mem_range] at hki
    refine ⟨⟨i, k - i⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · simp only [show i + (k - i) = k by omega]
  · rintro ⟨i,j⟩ _
    simp

private theorem taylorTerm_comp (a b : ℂ) (F : ℤ → ℤ → V) (s t : ℤ)
    (k i : ℕ) (hi : i ≤ k) :
    (a ^ i * Ring.choose ((s : ℂ) + i) i) •
      taylorTerm b F (s + i) (t - i) (k - i) =
    ((k.choose i : ℂ) * (a ^ i * b ^ (k - i))) •
      (Ring.choose ((s : ℂ) + k) k • F (s + k) (t - k)) := by
  have hchoose := Ring.choose_smul_choose ((s : ℂ) + k) (show k - i ≤ k by omega)
  simp only [Nat.choose_symm hi, nsmul_eq_mul, show k - (k - i) = i by omega,
    show (s : ℂ) + k - (↑(k - i : ℕ) : ℂ) = (s : ℂ) + i by rw [Nat.cast_sub hi]; ring]
    at hchoose
  unfold taylorTerm
  rw [show s + (i : ℤ) + ((k - i : ℕ) : ℤ) = s + k by omega,
      show t - (i : ℤ) - ((k - i : ℕ) : ℤ) = t - k by omega]
  push_cast
  rw [show (s : ℂ) + i + (↑(k - i : ℕ) : ℂ) = (s : ℂ) + k by
    rw [Nat.cast_sub hi]; ring]
  simp only [smul_smul]
  calc
    _ = (a ^ i * b ^ (k - i) *
        (Ring.choose ((s : ℂ) + k) (k - i) * Ring.choose ((s : ℂ) + i) i)) •
        F (s + k) (t - k) := by congr 1; ring
    _ = _ := by rw [← hchoose]; congr 1; ring

/-- Finite composition of Taylor translations on a uniformly lower
bounded inner exponent. Outer exponents are bilateral. -/
theorem taylor_comp (a b : ℂ) (F : ℤ → ℤ → V) (T : ℤ)
    (hF : ∀ s t, t < T → F s t = 0) :
    taylor a (taylor b F) = taylor (a + b) F := by
  funext s t
  by_cases ht : t < T
  · rw [taylor_lower a _ T (taylor_lower b F T hF) s t ht,
      taylor_lower (a + b) F T hF s t ht]
  let n := (t - T).toNat
  have hn : (n : ℤ) = t - T := Int.toNat_of_nonneg (by omega)
  have hrange : (t - T + 1).toNat = n + 1 := by omega
  rw [taylor_eq_sum_range a _ T (taylor_lower b F T hF),
    taylor_eq_sum_range (a + b) F T hF, hrange]
  calc
    _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1),
        (a ^ i * Ring.choose ((s : ℂ) + i) i) • taylorTerm b F (s + i) (t - i) j := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [taylorTerm, taylor_eq_sum_range b F T hF, Finset.smul_sum,
        show (t - (i : ℤ) - T + 1).toNat = n - i + 1 by omega]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (k + 1),
        (a ^ i * Ring.choose ((s : ℂ) + i) i) • taylorTerm b F (s + i) (t - i) (k - i) :=
      sum_triangle n _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      calc
        _ = ∑ i ∈ Finset.range (k + 1),
            ((k.choose i : ℂ) * (a ^ i * b ^ (k - i))) •
              (Ring.choose ((s : ℂ) + k) k • F (s + k) (t - k)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact taylorTerm_comp a b F s t k i (by have := Finset.mem_range.mp hi; omega)
        _ = _ := by
          rw [← Finset.sum_smul, taylorTerm, add_pow]
          simp only [smul_smul]
          congr 2
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem taylor_zero (F : ℤ → ℤ → V) : taylor 0 F = F := by
  funext s t
  unfold taylor
  rw [finsum_eq_single _ 0]
  · simp [taylorTerm]
  · intro j hj
    simp [taylorTerm, zero_pow hj]

/-- A bounded-below input stays in the domain of inverse translation. -/
theorem taylor_inverse (a : ℂ) (F : ℤ → ℤ → V) (T : ℤ)
    (hF : ∀ s t, t < T → F s t = 0) :
    taylor (-a) (taylor a F) = F := by
  rw [taylor_comp (-a) a F T hF, neg_add_cancel, taylor_zero]

/-- Translate the two bilateral outer coordinates by the same `a*z`.
The innermost variable retains its original exponent lattice coset. -/
def simultaneousTaylor (a : ℂ) (F : ℤ → ℤ → ℤ → V) (s u t : ℤ) : V :=
  taylor a (fun s' t' => taylor a (F s') u t') s t

/-- Exact finite double Taylor sum. Terms with `i+j > t-T` vanish by
the same third-coordinate cutoff, so a finite square may be used. -/
theorem simultaneousTaylor_eq_sum (a : ℂ) (F : ℤ → ℤ → ℤ → V) (T : ℤ)
    (hF : ∀ s u t, t < T → F s u t = 0) (s u t : ℤ) :
    simultaneousTaylor a F s u t =
      ∑ i ∈ Finset.range (t - T + 1).toNat, ∑ j ∈ Finset.range (t - T + 1).toNat,
        (a^i * Ring.choose ((s : ℂ) + i) i) •
          ((a^j * Ring.choose ((u : ℂ) + j) j) • F (s + i) (u + j) (t - i - j)) := by
  rw [simultaneousTaylor, taylor_eq_sum_range a _ T
    (fun s' t' ht => taylor_lower a (F s') T (hF s') u t' ht)]
  apply Finset.sum_congr rfl
  intro i _
  rw [taylorTerm, taylor_eq_sum_range a (F (s + i)) (T - i)
    (fun u' t' ht => hF _ u' t' (by omega)),
    show t - (i : ℤ) - (T - i) + 1 = t - T + 1 by omega, Finset.smul_sum]
  rfl

theorem simultaneousTaylor_lower (a : ℂ) (F : ℤ → ℤ → ℤ → V) (T : ℤ)
    (hF : ∀ s u t, t < T → F s u t = 0) (s u t : ℤ) (ht : t < T) :
    simultaneousTaylor a F s u t = 0 := by
  exact taylor_lower a _ T (fun s' t' h => taylor_lower a (F s') T (hF s') u t' h) s t ht

theorem simultaneousTaylor_swap (a : ℂ) (F : ℤ → ℤ → ℤ → V) (T : ℤ)
    (hF : ∀ s u t, t < T → F s u t = 0) (s u t : ℤ) :
    simultaneousTaylor a F s u t = simultaneousTaylor a (fun u' s' => F s' u') u s t := by
  rw [simultaneousTaylor_eq_sum a F T hF, simultaneousTaylor_eq_sum a _ T
    (fun u' s' => hF s' u'), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [show t - (i : ℤ) - j = t - (j : ℤ) - i by omega, smul_comm]

/-- Invert by undoing the first coordinate and then the second. Each step
acts on a coefficient array with the same uniform inner lower bound. -/
theorem simultaneousTaylor_inverse (a : ℂ) (F : ℤ → ℤ → ℤ → V) (T : ℤ)
    (hF : ∀ s u t, t < T → F s u t = 0) :
    simultaneousTaylor (-a) (simultaneousTaylor a F) = F := by
  have h₁ (u : ℤ) : ∀ s t, t < T → taylor a (F s) u t = 0 :=
    fun s t ht => taylor_lower a (F s) T (hF s) u t ht
  funext s u t
  rw [simultaneousTaylor_swap (-a) (simultaneousTaylor a F) T
    (simultaneousTaylor_lower a F T hF)]
  change taylor (-a) (fun u' t' =>
    taylor (-a) (fun s' t'' => taylor a (fun x z => taylor a (F x) u' z) s' t'') s t') u t =
    F s u t
  have hcancel :
      (fun u' t' =>
        taylor (-a) (taylor a (fun x z => taylor a (F x) u' z)) s t') = taylor a (F s) := by
    funext u' t'
    exact congrFun (congrFun (taylor_inverse a _ T (h₁ u')) s) t'
  rw [hcancel]
  rw [taylor_inverse a (F s) T (hF s)]

end Translation

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBHUniformWeakAssociativity
