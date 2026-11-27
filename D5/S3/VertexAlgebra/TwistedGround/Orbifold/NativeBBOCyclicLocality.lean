import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBHUniformWeakAssociativity
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeakAssociativity

/-! Uniform three-field locality for the literal Leech mixed fields.
A mode label `n` of P or Q denotes physical mode `n + 1/2`,
with field exponent `-n - 3/2` (doubled exponent `-2*n - 3`).
After weighting the first two variables by `x^(L+1/2)` and `y^(M+1/2)`,
the three array indices represent exponents `x^s y^u z^(t-1/2)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCyclicLocality

open NativeBBHUniformWeakAssociativity
open FieldNormalProductLocality (Triple shiftXY)
open NativeBBOCoefficientTransport (P Q bb ba fixedH)
open NativeOddTwistedIntertwiner (TwistedOdd TwistedEven OddCarrier leechUnit)
open ActualLeechHyperbolic (leechData)
open LatticeInvolution (FixedCarrier)
open private p_tail bb_tail applyP from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport

section Translation

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private abbrev ThirdLower (F : Triple V) (T : ℤ) : Prop :=
  ∀ x y z, z < T → F x y z = 0

private theorem taylor_inner_shift (F : ℤ → ℤ → V) (T k : ℤ)
    (hF : ∀ x z, z < T → F x z = 0) (x z : ℤ) :
    taylor 1 (fun x z => F x (z + k)) x z = taylor 1 F x (z + k) := by
  rw [taylor_eq_sum_range 1 _ (T - k) (fun x z hz => hF x _ (by omega)),
    taylor_eq_sum_range 1 F T hF,
    show z - (T - k) + 1 = z + k - T + 1 by omega]
  apply Finset.sum_congr rfl
  intro j _
  simp only [taylorTerm, show z - (j : ℤ) + k = z + k - j by omega]

private theorem taylor_outer_shift (F : ℤ → ℤ → V) (T : ℤ)
    (hF : ∀ x z, z < T → F x z = 0) (x z : ℤ) :
    taylor 1 (fun x z => F (x - 1) z) x z =
      taylor 1 F (x - 1) z + taylor 1 F x (z - 1) := by
  by_cases hz : z < T
  · rw [taylor_lower 1 _ T (fun x => hF (x - 1)) x z hz,
      taylor_lower 1 F T hF (x - 1) z hz, taylor_lower 1 F T hF x (z - 1) (by omega),
      add_zero]
  let n := (z - T).toNat
  have h₁ : (z - T + 1).toNat = n + 1 := by dsimp [n]; omega
  have h₂ : (z - 1 - T + 1).toNat = n := by dsimp [n]; omega
  rw [taylor_eq_sum_range 1 _ T (fun x => hF (x - 1)),
    taylor_eq_sum_range 1 F T hF, taylor_eq_sum_range 1 F T hF, h₁, h₂,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [taylorTerm, one_pow, one_mul, Nat.cast_zero, add_zero, sub_zero,
    Ring.choose_zero_right, one_smul]
  rw [add_right_comm _ (F (x - 1) z), add_left_inj, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  rw [show (x : ℂ) + (j + 1) = ((x : ℂ) - 1 + (j + 1)) + 1 by ring,
    Ring.choose_succ_succ, add_smul]
  rw [show (x : ℂ) - 1 + (j + 1) = (x : ℂ) + j by ring,
    show x + ((j : ℤ) + 1) - 1 = x + j by omega,
    show x - 1 + ((j : ℤ) + 1) = x + j by omega,
    show z - ((j : ℤ) + 1) = z - 1 - j by omega, add_comm]

/-- Multiplication by `x-y` in exponent coordinates. The library's
`plainXY` uses mode (increasing) coordinates. -/
private def difference (F : Triple V) : Triple V := fun x y z =>
  shiftXY (fun i j k => F (-i) (-j) k) (-x) (-y) z

omit [Module ℂ V] in
private theorem difference_apply (F : Triple V) (x y z : ℤ) :
    difference F x y z = F (x - 1) y z - F x (y - 1) z := by
  simp only [difference, shiftXY, neg_neg, neg_add_rev, sub_eq_add_neg, add_comm]

omit [Module ℂ V] in
private theorem difference_lower (F : Triple V) (T : ℤ) (hF : ThirdLower F T) :
    ThirdLower (difference F) T := by
  intro x y z hz
  rw [difference_apply, hF _ _ _ hz, hF _ _ _ hz, sub_zero]

private theorem simultaneous_sub (F G : Triple V) (T : ℤ)
    (hF : ThirdLower F T) (hG : ThirdLower G T) :
    simultaneousTaylor 1 (F - G) = simultaneousTaylor 1 F - simultaneousTaylor 1 G := by
  funext x y z
  change simultaneousTaylor 1 (F - G) x y z =
    simultaneousTaylor 1 F x y z - simultaneousTaylor 1 G x y z
  rw [simultaneousTaylor_eq_sum 1 _ T (fun i j k hk => by
      simp [hF i j k hk, hG i j k hk]),
    simultaneousTaylor_eq_sum 1 F T hF, simultaneousTaylor_eq_sum 1 G T hG]
  simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

private theorem simultaneous_shift_first (F : Triple V) (T : ℤ)
    (hF : ThirdLower F T) (x y z : ℤ) :
    simultaneousTaylor 1 (fun i j k => F (i - 1) j k) x y z =
      simultaneousTaylor 1 F (x - 1) y z + simultaneousTaylor 1 F x y (z - 1) :=
  taylor_outer_shift (fun x z => taylor 1 (F x) y z) T
    (fun x => taylor_lower 1 (F x) T (hF x) y) x z

private theorem simultaneous_shift_second (F : Triple V) (T : ℤ)
    (hF : ThirdLower F T) (x y z : ℤ) :
    simultaneousTaylor 1 (fun i j k => F i (j - 1) k) x y z =
      simultaneousTaylor 1 F x (y - 1) z + simultaneousTaylor 1 F x y (z - 1) := by
  rw [simultaneousTaylor_swap 1 _ T (fun i j => hF i (j - 1)),
    simultaneous_shift_first _ T (fun i j => hF j i),
    ← simultaneousTaylor_swap 1 F T hF, ← simultaneousTaylor_swap 1 F T hF]

private theorem simultaneous_difference (F : Triple V) (T : ℤ)
    (hF : ThirdLower F T) (N : ℕ) :
    simultaneousTaylor 1 (difference^[N] F) = difference^[N] (simultaneousTaylor 1 F) := by
  induction N generalizing F with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih _ (difference_lower F T hF)]
    congr 1
    have hsplit : difference F =
        (fun x y z => F (x - 1) y z) - (fun x y z => F x (y - 1) z) := by
      funext x y z
      exact difference_apply F x y z
    rw [hsplit, simultaneous_sub _ _ T (fun x y => hF (x - 1) y)
      (fun x y => hF x (y - 1))]
    funext x y z
    simp only [Pi.sub_apply, simultaneous_shift_first _ T hF,
      simultaneous_shift_second _ T hF, difference_apply]
    abel

end Translation

section Binomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private abbrev FirstLower (F : Triple V) (A : ℤ) : Prop :=
  ∀ x y z, x < A → F x y z = 0

private abbrev SecondLower (F : Triple V) (B : ℤ) : Prop :=
  ∀ x y z, y < B → F x y z = 0

private abbrev FirstSliceLower (F : Triple V) : Prop :=
  ∀ y, ∃ A : ℤ, ∀ x z, x < A → F x y z = 0

private abbrev SecondSliceLower (F : Triple V) : Prop :=
  ∀ x, ∃ B : ℤ, ∀ y z, y < B → F x y z = 0

private def binomialFirst (a : ℂ) (k : ℤ) (F : Triple V) (x y z : ℤ) : V :=
  ∑ᶠ j : ℕ, Ring.choose a j • F (x - j) y (z - k + j)

private def binomialSecond (a : ℂ) (k : ℤ) (F : Triple V) (x y z : ℤ) : V :=
  ∑ᶠ j : ℕ, Ring.choose a j • F x (y - j) (z - k + j)

open private finite_of_tail from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBHUniformWeakAssociativity

private theorem binomial_support (a : ℂ) (k x z A : ℤ) (F : ℤ → ℤ → V)
    (h : ∀ i j, i < A → F i j = 0) :
    Function.HasFiniteSupport (fun j : ℕ => Ring.choose a j • F (x - j) (z - k + j)) :=
  finite_of_tail _ (x - A + 1).toNat fun j hj => by rw [h _ _ (by omega), smul_zero]

private theorem binomial_range (a : ℂ) (k x z A : ℤ) (F : ℤ → ℤ → V)
    (h : ∀ i j, i < A → F i j = 0) :
    (∑ᶠ j : ℕ, Ring.choose a j • F (x - j) (z - k + j)) =
      ∑ j ∈ Finset.range (x - A + 1).toNat, Ring.choose a j • F (x - j) (z - k + j) := by
  apply finsum_eq_sum_of_support_subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra! hj'
  apply hj
  change Ring.choose a j • F (x - j) (z - k + j) = 0
  rw [h _ _ (by omega), smul_zero]

omit [Module ℂ V] in
private theorem difference_firstSliceLower (F : Triple V) (h : FirstSliceLower F) :
    FirstSliceLower (difference F) := by
  intro y
  obtain ⟨A, hA⟩ := h y
  obtain ⟨B, hB⟩ := h (y - 1)
  exact ⟨min A B, fun x z hx => by
    rw [difference_apply, hA _ _ (by omega), hB _ _ (by omega), sub_zero]⟩

omit [Module ℂ V] in
private theorem difference_secondSliceLower (F : Triple V) (h : SecondSliceLower F) :
    SecondSliceLower (difference F) := by
  intro x
  obtain ⟨A, hA⟩ := h (x - 1)
  obtain ⟨B, hB⟩ := h x
  exact ⟨min A B, fun y z hy => by
    rw [difference_apply, hA _ _ (by omega), hB _ _ (by omega), sub_zero]⟩

private theorem binomialFirst_difference (a : ℂ) (k : ℤ) (F : Triple V)
    (hF : FirstSliceLower F) (N : ℕ) :
    binomialFirst a k (difference^[N] F) = difference^[N] (binomialFirst a k F) := by
  induction N generalizing F with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih _ (difference_firstSliceLower F hF)]
    congr 1
    funext x y z
    obtain ⟨A, hA⟩ := hF y
    obtain ⟨B, hB⟩ := hF (y - 1)
    rw [binomialFirst, difference_apply]
    simp only [difference_apply, show ∀ j : ℕ, x - (j : ℤ) - 1 = x - 1 - j by intro; omega,
      smul_sub, binomialFirst]
    exact finsum_sub_distrib (binomial_support a k (x - 1) z A (fun i j => F i y j) hA)
      (binomial_support a k x z B (fun i j => F i (y - 1) j) hB)

private theorem binomialSecond_difference (a : ℂ) (k : ℤ) (F : Triple V)
    (hF : SecondSliceLower F) (N : ℕ) :
    binomialSecond a k (difference^[N] F) = difference^[N] (binomialSecond a k F) := by
  induction N generalizing F with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih _ (difference_secondSliceLower F hF)]
    congr 1
    funext x y z
    obtain ⟨A, hA⟩ := hF (x - 1)
    obtain ⟨B, hB⟩ := hF x
    rw [binomialSecond, difference_apply]
    simp only [difference_apply, show ∀ j : ℕ, y - (j : ℤ) - 1 = y - 1 - j by intro; omega,
      smul_sub, binomialSecond]
    exact finsum_sub_distrib (binomial_support a k y z A (F (x - 1)) hA)
      (binomial_support a k (y - 1) z B (F x) hB)

private theorem binomialFirst_secondLower (a : ℂ) (k B : ℤ) (F : Triple V)
    (hF : SecondLower F B) : SecondLower (binomialFirst a k F) B := by
  intro x y z hy
  simp only [binomialFirst, hF _ _ _ hy, smul_zero, finsum_zero]

private theorem binomialSecond_firstLower (a : ℂ) (k A : ℤ) (F : Triple V)
    (hF : FirstLower F A) : FirstLower (binomialSecond a k F) A := by
  intro x y z hx
  simp only [binomialSecond, hF _ _ _ hx, smul_zero, finsum_zero]

private theorem binomial_swap (a b : ℂ) (k l A B : ℤ) (F : Triple V)
    (hA : FirstLower F A) (hB : SecondLower F B) :
    binomialSecond b l (binomialFirst a k F) = binomialFirst a k (binomialSecond b l F) := by
  funext x y z
  change (∑ᶠ j : ℕ, Ring.choose b j • binomialFirst a k F x (y - j) (z - l + j)) =
    ∑ᶠ j : ℕ, Ring.choose a j • binomialSecond b l F (x - j) y (z - k + j)
  rw [binomial_range b l y z B (fun y z => binomialFirst a k F x y z)
    (fun y z hy => binomialFirst_secondLower a k B F hB x y z hy),
    binomial_range a k x z A (fun x z => binomialSecond b l F x y z)
      (fun x z hx => binomialSecond_firstLower b l A F hA x y z hx)]
  have hFirst (u v : ℤ) : binomialFirst a k F x u v =
      ∑ j ∈ Finset.range (x - A + 1).toNat, Ring.choose a j • F (x - j) u (v - k + j) :=
    binomial_range a k x v A (fun i j => F i u j) (fun i j hi => hA i u j hi)
  have hSecond (u v : ℤ) : binomialSecond b l F u y v =
      ∑ j ∈ Finset.range (y - B + 1).toNat, Ring.choose b j • F u (y - j) (v - l + j) :=
    binomial_range b l y v B (F u) (fun i j hi => hB u i j hi)
  simp only [hFirst, hSecond, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_comm, show z - l + (j : ℤ) - k + i = z - k + i - l + j by omega]

end Binomial

section Native

local notation "A" => FixedCarrier leechData
local notation "B" => TwistedOdd
local notation "H" => TwistedEven
local notation "O" => OddCarrier leechData

open NativeMixedPairWeakAssociativity (mu_true_reversed_weak_associativity)
open ActualLeechExtensionVertexAlgebra (leechVertexAlgebra stateField_eq)
open NativeBBOCoefficientTransport (Extension extension_borcherds_after_P)
open private ext_bb ext_ba from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCoefficientTransport
open private has_mode_tail from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField

private abbrev weight (L : ℤ) : ℂ := (L : ℂ) + 1 / 2

private def mixedProduct (b : B) (a : A) (h : H) (L : ℤ) (x z : ℤ) : O :=
  P b (L - x - 1) (fixedH a (-z - 1) h)

private def extensionProduct (b c d : B) (x y : ℤ) : B :=
  ba b (bb c d (-y - 1)) (-x - 1)

private def tripleProduct (b c d : B) (h : H) (L M : ℤ) (x y z : ℤ) : O :=
  -(P b (L - x - 1) (Q c (M - y - 1) (P d (-z - 1) h)))

-- The unweighted iterate has exponent z^(z-3/2) at third index z.
-- The two half-powers together shift the weighted exponent to z^(z-1/2).
private def extensionAfterP (b c d : B) (h : H) (x y z : ℤ) : O :=
  P (extensionProduct b c d x y) (-z) h

private theorem ba_eq (b : B) (a : A) (n : ℤ) :
    ba b a n = MixedIntertwiner.originalRightCoefficient leechData leechUnit n b a := by
  unfold ba
  rw [OriginalOrbifoldField.Y_ncoeff_apply]
  simp

private theorem mixedProduct_weak_assoc (b : B) (h : H) :
    ∃ L : ℤ, (∀ n ≥ L, P b n h = 0) ∧ ∀ (a : A) (x z : ℤ),
      taylor 1 (mixedProduct b a h L) x z =
        ∑ᶠ j : ℕ, Ring.choose (weight L) j •
          P (ba b a (-(x - j) - 1)) (-(z - L + j) - 1) h := by
  obtain ⟨L, hL, hWA⟩ := mu_true_reversed_weak_associativity b h
  refine ⟨L, hL, fun a x z => ?_⟩
  have he := (hWA a (-z - 1) (-x - 1)).2.2
  unfold taylor
  refine (finsum_congr (fun j => ?_)).trans (he.trans (finsum_congr (fun j => ?_)))
  · simp only [taylorTerm, one_pow, one_mul, mixedProduct]
    rw [show (x : ℂ) + j = (j : ℂ) - ((-x - 1 : ℤ) : ℂ) - 1 by push_cast; ring]
    change _ • P b ((L : ℤ) - (x + j) - 1) (fixedH a (-(z - j) - 1) h) =
      _ • P b ((L : ℤ) + (-x - 1) - j) (fixedH a (-z - 1 + j) h)
    rw [show (L : ℤ) - (x + j) - 1 = (L : ℤ) + (-x - 1) - j by omega,
      show -(z - (j : ℤ)) - 1 = -z - 1 + j by omega]
  · change Ring.choose ((L : ℂ) + 1 / 2) j •
      P (MixedIntertwiner.originalRightCoefficient leechData leechUnit (-x - 1 + j) b a)
        (-z - 1 + (L : ℤ) - j) h = _
    rw [ba_eq, show -(x - (j : ℤ)) - 1 = -x - 1 + j by omega,
      show -(z - (L : ℤ) + (j : ℤ)) - 1 = -z - 1 + L - j by omega]
    rfl

private theorem tripleProduct_lower (b c d : B) (h : H) (L M D : ℤ)
    (hD : ∀ n ≥ D, P d n h = 0) : ThirdLower (tripleProduct b c d h L M) (-D) := by
  intro x y z hz
  simp only [tripleProduct, hD _ (by omega : D ≤ -z - 1), map_zero, neg_zero]

private theorem extensionProduct_secondLower (b c d : B) (C : ℤ)
    (hC : ∀ n ≥ C, bb c d n = 0) (x y : ℤ) (hy : y < -C) :
    extensionProduct b c d x y = 0 := by
  rw [extensionProduct, hC _ (by omega), ba_eq]
  exact (map_zero (MixedIntertwiner.originalRightCoefficient leechData leechUnit (-x - 1) b))

private theorem extensionAfterP_secondLower (b c d : B) (h : H) (C : ℤ)
    (hC : ∀ n ≥ C, bb c d n = 0) :
    SecondLower (extensionAfterP b c d h) (-C) := by
  intro x y z hy
  change applyP h (-z) (extensionProduct b c d x y) = 0
  rw [extensionProduct_secondLower b c d C hC x y hy, map_zero]

private theorem extensionAfterP_firstSliceLower (b c d : B) (h : H) :
    FirstSliceLower (extensionAfterP b c d h) := by
  intro y
  obtain ⟨N, hN⟩ := has_mode_tail (leechVertexAlgebra.stateField ((0, b) : Extension))
    ((bb c d (-y - 1), 0) : Extension)
  refine ⟨-N, ?_⟩
  intro x z hx
  have he := hN (-x - 1) (by omega)
  rw [stateField_eq, ext_ba] at he
  change applyP h (-z) (ba b (bb c d (-y - 1)) (-x - 1)) = 0
  have hb : ba b (bb c d (-y - 1)) (-x - 1) = 0 := congrArg Prod.snd he
  rw [hb, map_zero]

private theorem taylor_sum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Finset ℕ) (f : ℕ → ℤ → ℤ → V)
    (hf : ∀ j ∈ S, ∃ T : ℤ, ∀ x z, z < T → f j x z = 0) (x z : ℤ) :
    taylor 1 (fun i k => ∑ j ∈ S, f j i k) x z = ∑ j ∈ S, taylor 1 (f j) x z := by
  obtain ⟨T, hT⟩ : ∃ T : ℤ, ∀ j ∈ S, ∀ i k, k < T → f j i k = 0 := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j S hj ih =>
      obtain ⟨U, hU⟩ := hf j (Finset.mem_insert_self _ _)
      obtain ⟨T, hT⟩ := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      refine ⟨min U T, ?_⟩
      intro k hk i z hz
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hU i z (by omega)
      · exact hT k hk i z (by omega)
  rw [taylor_eq_sum_range 1 _ T (fun i k hk => Finset.sum_eq_zero
    (fun j hj => hT j hj i k hk))]
  calc
    _ = ∑ j ∈ S, ∑ i ∈ Finset.range (z - T + 1).toNat, taylorTerm 1 (f j) x z i := by
      rw [Finset.sum_comm]
      simp only [taylorTerm, Finset.smul_sum]
    _ = _ := by
      exact Finset.sum_congr rfl fun j hj => (taylor_eq_sum_range 1 (f j) T (hT j hj) x z).symm

private theorem taylor_weighted_mixed (b : B) (a : A) (h : H) (L k : ℤ)
    (w : ℂ) (x z : ℤ) :
    taylor 1 (fun i j => w • mixedProduct b a h L i (j + k)) x z =
      w • taylor 1 (mixedProduct b a h L) x (z + k) := by
  obtain ⟨N, hN⟩ := has_mode_tail
    (HalfFock.LatticeHalfFockParityField.fixedParitySlice leechData leechUnit 1 a) h
  have hF : ∀ i j, j < -N → mixedProduct b a h L i j = 0 := by
    intro i j hj
    have hz : fixedH a (-j - 1) h = 0 := hN _ (by omega)
    rw [mixedProduct, hz, map_zero]
  have hShift : ∀ i j, j < -N - k → mixedProduct b a h L i (j + k) = 0 :=
    fun i j hj => hF _ _ (by omega)
  simpa only [LinearMap.lsmul_apply] using
    (congrFun (congrFun (taylor_map (LinearMap.lsmul ℂ O w) 1 _ (-N - k) hShift) x) z).trans
      (congrArg (fun v : O => w • v) (taylor_inner_shift _ (-N) k hF x z))

private theorem tripleProduct_translate (b c d : B) (h : H) (L M D : ℤ)
    (hD : ∀ n ≥ D, P d n h = 0) (hM : ∀ n ≥ M, P c n h = 0)
    (hL : ∀ (a : A) (x z : ℤ), taylor 1 (mixedProduct b a h L) x z =
      ∑ᶠ j : ℕ, Ring.choose (weight L) j •
        P (ba b a (-(x - j) - 1)) (-(z - L + j) - 1) h) :
    simultaneousTaylor 1 (tripleProduct b c d h L M) =
      binomialSecond (weight M) M (binomialFirst (weight L) L (extensionAfterP b c d h)) := by
  obtain ⟨C, hC⟩ := bb_tail c d
  funext x y z
  have hInner (i : ℤ) : taylor 1 (tripleProduct b c d h L M i) =
      fun j k => P b (L - i - 1) (weightedIterate c d h M j k) := by
    have hprod : tripleProduct b c d h L M i =
        fun j k => P b (L - i - 1) (weightedProduct c d h M j k) := by
      funext j k
      exact (map_neg (P b (L - i - 1)) _).symm
    rw [hprod, taylor_map _ 1 _ (-D) (weightedProduct_lower c d h M D hD),
      bbh_weak_associativity_of_tail c h M hM d]
  let S := Finset.range (C + y + 1).toNat
  let f (j : ℕ) (i k : ℤ) := Ring.choose (weight M) j •
    mixedProduct b (bb c d (-(y - j) - 1)) h L i (k + (-(M + 1) + j))
  have hrewrite : (fun i k => taylor 1 (tripleProduct b c d h L M i) y k) =
      fun i k => ∑ j ∈ S, f j i k := by
    funext i k
    rw [hInner i]
    change P b (L - i - 1) (weightedIterate c d h M y k) = _
    rw [weightedIterate_eq_sum_range c d h M C y k hC, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [iterateTerm, iterate, map_smul]
    dsimp only [f, mixedProduct]
    rw [show k - M + (j : ℤ) - 1 = k + (-(M + 1) + j) by omega]
  unfold simultaneousTaylor
  rw [hrewrite, taylor_sum S f]
  · change _ = binomialSecond (weight M) M _ x y z
    rw [binomialSecond, binomial_range _ _ _ _ (-C) _
      (fun i k hi => binomialFirst_secondLower _ _ (-C) _
        (extensionAfterP_secondLower b c d h C hC) x i k hi)]
    apply Finset.sum_congr (by dsimp [S]; congr 2; omega)
    intro j _
    dsimp only [f]
    rw [taylor_weighted_mixed, hL]
    unfold binomialFirst extensionAfterP extensionProduct
    congr 1
    apply finsum_congr
    intro i
    rw [show -(z + (-(M + 1) + (j : ℤ)) - L + i) - 1 =
      -(z - M + j - L + i) by omega]
  · intro j _
    obtain ⟨N, hN⟩ := has_mode_tail
      (HalfFock.LatticeHalfFockParityField.fixedParitySlice leechData leechUnit 1
        (bb c d (-(y - j) - 1))) h
    refine ⟨-N + (M + 1) - j, fun i k hk => ?_⟩
    dsimp only [f, mixedProduct]
    have hz : fixedH (bb c d (-(y - j) - 1)) (-(k + (-(M + 1) + j)) - 1) h = 0 :=
      hN _ (by omega)
    rw [hz, map_zero, smul_zero]

open UniformGradedLocalCorrelator (Distribution polynomialAction pairPolynomial action_pair shift)
open private pair_power_apply from
  D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

private theorem difference_iterate_sum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Triple V) (N : ℕ) (x y z : ℤ) :
    difference^[N] F x y z =
      ∑ j ∈ Finset.range (N + 1), (((-1 : ℂ)^j) * (N.choose j : ℂ)) •
        F (x - N + j) (y - j) z := by
  let embed (G : Triple V) : Distribution 3 V := fun e => G (e 0) (e 1) (e 2)
  have hstep (G : Triple V) :
      embed (difference G) = UniformGradedLocalCorrelator.difference 0 1 (embed G) := by
    funext e
    simp only [embed, difference_apply, UniformGradedLocalCorrelator.difference,
      LinearMap.sub_apply, Pi.sub_apply, shift, LinearMap.coe_mk, AddHom.coe_mk]
    congr 2 <;> simp
  have heq : embed (difference^[N] F) = polynomialAction (pairPolynomial 0 1 ^ N) (embed F) := by
    rw [map_pow, action_pair]
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [Function.iterate_succ_apply', hstep, ih, pow_succ', Module.End.mul_apply]
  have hadjust := congrFun heq ![x,y,z]
  rw [pair_power_apply] at hadjust
  change difference^[N] F x y z = _ at hadjust
  rw [hadjust]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := by simpa using Finset.mem_range.mp hj
  have hcoords : (![x, y, z] : Fin 3 → ℤ) - (N - j) • Pi.single 0 1 -
      j • Pi.single 1 1 = ![x - N + j, y - j, z] := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply]
    fin_cases i <;> simp [Pi.single_apply, nsmul_eq_mul, Int.natCast_sub hjN] <;> omega
  rw [hcoords]
  rfl

private def swap {V : Type*} (F : Triple V) : Triple V := fun x y z => F y x z

private theorem extension_difference (b c d : B) (h : H) (N : ℕ)
    (hN : ∀ n ≥ (N : ℤ), bb b c n = 0) :
    difference^[N] (extensionAfterP b c d h) =
      difference^[N] (swap (extensionAfterP c b d h)) := by
  funext x y z
  rw [difference_iterate_sum, difference_iterate_sum]
  let u := -x - 1
  let v := -y - 1
  have he := extension_borcherds_after_P b c d h (-z) u v N
  have hzero : (∑ᶠ j : ℕ, Ring.choose (u : ℂ) j •
    P (NativeBBOCoefficientTransport.ab (bb b c ((N : ℤ) + j)) d (u + v - j)) (-z) h) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    simp only [hN _ (by omega : (N : ℤ) ≤ (N : ℤ) + j)]
    have hab : NativeBBOCoefficientTransport.ab 0 d (u + v - j) = 0 := by
      unfold NativeBBOCoefficientTransport.ab
      have hmode : (((leechVertexAlgebra.stateField (0 : Extension))[[u + v - j]]) (0, d)) =
          (0 : Extension) := by
        rw [map_zero, map_zero]
        rfl
      rw [stateField_eq] at hmode
      exact congrArg Prod.snd hmode
    change Ring.choose (u : ℂ) j • applyP h (-z)
      (NativeBBOCoefficientTransport.ab 0 d (u + v - j)) = 0
    rw [hab, map_zero, smul_zero]
  simp only [Int.cast_natCast, Ring.choose_natCast, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    zpow_natCast] at he
  have hrange {f : ℕ → O} (hf : ∀ j > N, f j = 0) :
      (∑ᶠ j, f j) = ∑ j ∈ Finset.range (N + 1), f j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra! hout
    exact hj (hf j (by simpa using hout))
  rw [hzero, hrange (fun j hj => by simp [Nat.choose_eq_zero_of_lt hj]),
    hrange (fun j hj => by simp [Nat.choose_eq_zero_of_lt hj])] at he
  have hfirst : (∑ j ∈ Finset.range (N + 1), (((-1 : ℂ)^j) * (N.choose j : ℂ)) •
        extensionAfterP b c d h (x - N + j) (y - j) z) =
      ∑ j ∈ Finset.range (N + 1), (((-1 : ℂ)^j) * (N.choose j : ℂ)) •
        P (ba b (bb c d (v + j)) (u + N - j)) (-z) h := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [extensionAfterP, extensionProduct, u, v]
    rw [show -(y - (j : ℤ)) - 1 = -y - 1 + j by omega,
      show -(x - (N : ℤ) + (j : ℤ)) - 1 = -x - 1 + N - j by omega]
  rw [hfirst, sub_eq_zero.mp he.symm]
  -- Reflect the second Borcherds product, where the offset was on b.
  rw [← Finset.sum_range_reflect (fun j => (((-1 : ℂ)^N * (-1 : ℂ)^j) *
    (N.choose j : ℂ)) • P (ba c (bb b d (u + j)) (v + N - j)) (-z) h)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := by simpa using Finset.mem_range.mp hj
  have hsign : (-1 : ℂ)^N * (-1 : ℂ)^(N - j) = (-1 : ℂ)^j := by
    rw [← pow_add, show N + (N - j) = 2 * (N - j) + j by omega, pow_add, pow_mul]
    norm_num
  rw [show N + 1 - 1 - j = N - j by omega, hsign, Nat.choose_symm hjN]
  simp only [swap, extensionAfterP, extensionProduct, u, v, Int.natCast_sub hjN]
  rw [show -x - 1 + ((N : ℤ) - j) = -(x - N + j) - 1 by omega,
    show -y - 1 + (N : ℤ) - ((N : ℤ) - j) = -(y - j) - 1 by omega]

/-- The uniform ordinary extension cutoff clears the actual signed triple
products on every mixed-field coefficient. N is independent of d, h and
all three extracted mode labels. -/
private theorem c3_of_tail (b c : B) (N : ℕ) (hN : ∀ n ≥ (N : ℤ), bb b c n = 0)
    (d : B) (h : H) (t u s : ℤ) :
    (∑ j ∈ Finset.range (N + 1), (((-1 : ℂ)^j) * (N.choose j : ℂ)) •
      (P b (t + N - j) (Q c (u + j) (P d s h)) -
       P c (u + j) (Q b (t + N - j) (P d s h)))) = 0 := by
  obtain ⟨L, hL, hLb⟩ := mixedProduct_weak_assoc b h
  obtain ⟨M, hM, hMc⟩ := mixedProduct_weak_assoc c h
  obtain ⟨D, hD⟩ := p_tail d h
  obtain ⟨E, hE⟩ := bb_tail c d
  obtain ⟨G, hG⟩ := bb_tail b d
  let F := tripleProduct b c d h L M
  let R := swap (tripleProduct c b d h M L)
  let U := extensionAfterP b c d h
  let W := swap (extensionAfterP c b d h)
  have hFl : ThirdLower F (-D) := tripleProduct_lower b c d h L M D hD
  have hRl : ThirdLower R (-D) := fun x y z =>
    tripleProduct_lower c b d h M L D hD y x z
  have hU₂ : SecondLower U (-E) := extensionAfterP_secondLower b c d h E hE
  have hW₁ : FirstLower W (-G) := fun x y z =>
    extensionAfterP_secondLower c b d h G hG y x z
  have hU₁ : FirstSliceLower U := extensionAfterP_firstSliceLower b c d h
  have hW₂ : SecondSliceLower W := extensionAfterP_firstSliceLower c b d h
  have hforward : simultaneousTaylor 1 F =
      binomialSecond (weight M) M (binomialFirst (weight L) L U) :=
    tripleProduct_translate b c d h L M D hD hM hLb
  have hreverse : simultaneousTaylor 1 R =
      binomialFirst (weight L) L (binomialSecond (weight M) M W) := by
    funext x y z
    rw [simultaneousTaylor_swap 1 R (-D) hRl]
    exact congrFun (congrFun (congrFun
      (tripleProduct_translate c b d h M L D hD hL hMc) y) x) z
  have hcommon : difference^[N] U = difference^[N] W := extension_difference b c d h N hN
  have hcommon₂ : SecondLower (difference^[N] U) (-E) := by
    intro x y z hy
    rw [difference_iterate_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [hU₂ _ _ _ (by omega), smul_zero]
  have hcommon₁ : FirstLower (difference^[N] U) (-G) := by
    rw [hcommon]
    intro x y z hx
    rw [difference_iterate_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hjN : j ≤ N := by simpa using Finset.mem_range.mp hj
    rw [hW₁ _ _ _ (by omega), smul_zero]
  have hFt : ThirdLower (difference^[N] F) (-D) := by
    intro x y z hz
    rw [difference_iterate_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [hFl _ _ _ hz, smul_zero]
  have hRt : ThirdLower (difference^[N] R) (-D) := by
    intro x y z hz
    rw [difference_iterate_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [hRl _ _ _ hz, smul_zero]
  have htranslated : simultaneousTaylor 1 (difference^[N] F) =
      simultaneousTaylor 1 (difference^[N] R) := by
    rw [simultaneous_difference F (-D) hFl, simultaneous_difference R (-D) hRl,
      hforward, hreverse, ← binomialSecond_difference _ _ _
        (fun _ => ⟨-E, fun y z => binomialFirst_secondLower _ _ (-E) U hU₂ _ y z⟩),
      ← binomialFirst_difference _ _ _
        (fun _ => ⟨-G, fun x z => binomialSecond_firstLower _ _ (-G) W hW₁ x _ z⟩),
      ← binomialFirst_difference _ _ U hU₁,
      ← binomialSecond_difference _ _ W hW₂, ← hcommon]
    exact binomial_swap _ _ _ _ (-G) (-E) _ hcommon₁ hcommon₂
  have hproducts := congrArg (simultaneousTaylor (-1)) htranslated
  rw [simultaneousTaylor_inverse 1 _ (-D) hFt, simultaneousTaylor_inverse 1 _ (-D) hRt] at hproducts
  have he := congrFun (congrFun (congrFun hproducts (L - t - 1)) (M - u - 1)) (-s - 1)
  rw [difference_iterate_sum, difference_iterate_sum] at he
  simp only [F, R, tripleProduct, swap,
    show ∀ j : ℕ, L - (L - t - 1 - N + j) - 1 = t + N - j by intro; omega,
    show ∀ j : ℕ, M - (M - u - 1 - j) - 1 = u + j by intro; omega,
    show -(-s - 1) - 1 = s by omega,
    smul_neg, Finset.sum_neg_distrib, neg_inj] at he
  rw [Finset.sum_congr rfl (fun _ _ => smul_sub _ _ _), Finset.sum_sub_distrib, sub_eq_zero]
  exact he

/-- A uniform degree for C3 with the original half-integer field modes. -/
theorem c3 (b c : B) : ∃ N : ℕ, ∀ (d : B) (h : H) (t u s : ℤ),
    (∑ j ∈ Finset.range (N + 1), (((-1 : ℂ)^j) * (N.choose j : ℂ)) •
      (P b (t + N - j) (Q c (u + j) (P d s h)) -
       P c (u + j) (Q b (t + N - j) (P d s h)))) = 0 := by
  obtain ⟨N, hN⟩ := bb_tail b c
  exact ⟨N.toNat, c3_of_tail b c N.toNat (fun n hn => hN n (by omega))⟩

/-- The same C3 polynomial vanishes on the entire odd untwisted carrier,
by the span of the actual mixed-field coefficients. -/
theorem locality_on_odd (b c : B) : ∃ N : ℕ, ∀ (o : O) (t u : ℤ),
    (∑ j ∈ Finset.range (N + 1), (((-1 : ℂ)^j) * (N.choose j : ℂ)) •
      (P b (t + N - j) (Q c (u + j) o) -
       P c (u + j) (Q b (t + N - j) o))) = 0 := by
  obtain ⟨N, hN⟩ := c3 b c
  refine ⟨N, fun o t u => ?_⟩
  let D : O →ₗ[ℂ] O := ∑ j ∈ Finset.range (N + 1),
    (((-1 : ℂ)^j) * (N.choose j : ℂ)) •
      ((P b (t + N - j)).comp (Q c (u + j)) -
       (P c (u + j)).comp (Q b (t + N - j)))
  have hD (x : O) : D x = ∑ j ∈ Finset.range (N + 1),
      (((-1 : ℂ)^j) * (N.choose j : ℂ)) •
        (P b (t + N - j) (Q c (u + j) x) -
         P c (u + j) (Q b (t + N - j) x)) := by
    simp only [D, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.comp_apply]
  have hle : NativeMixedPairBorcherds.mixedImageSpan ≤ LinearMap.ker D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨s, d, h⟩, rfl⟩
    change D (P d s h) = 0
    rw [hD]
    exact hN d h t u s
  rw [NativeBBOCoefficientTransport.mixedImageSpan_eq_top] at hle
  rw [← hD]
  exact hle (Submodule.mem_top (x := o))

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCyclicLocality.c3' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms c3

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCyclicLocality.locality_on_odd' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms locality_on_odd

open NativeBBOCoefficientTransport
  (bboDefect bboDefect_eq_zero_iff_on_coefficients bboDefect_eq_zero_iff_jacobi)
open NativeOddTwistedIntertwiner (oddMode)

/-- Once the ordinary collision modes of b and c vanish, C3 gives the
literal signed BBO Jacobi identity for that collision index. -/
private theorem bboDefect_at_tail (b c : B) (r : ℕ)
    (hr : ∀ n ≥ (r : ℤ), bb b c n = 0) (p q : ℤ) :
    bboDefect b c p q r = 0 := by
  apply (bboDefect_eq_zero_iff_on_coefficients b c p q r).2
  intro d s h
  let o := P d s h
  apply (bboDefect_eq_zero_iff_jacobi b c o p q r).2
  change -(∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose ((r : ℤ) : ℂ) j) •
    P b (q + r - j) (Q c (p + j) o)) +
    (∑ᶠ j : ℕ, ((-1 : ℂ)^((r : ℤ) + (j : ℤ)) * Ring.choose ((r : ℤ) : ℂ) j) •
      P c (p + r - j) (Q b (q + j) o)) =
    ∑ᶠ j : ℕ, Ring.choose ((q : ℂ) + 1 / 2) j •
      oddMode leechData (bb b c ((r : ℤ) + j)) (p + q + 1 - j) o
  have hzero : (∑ᶠ j : ℕ, Ring.choose ((q : ℂ) + 1 / 2) j •
      oddMode leechData (bb b c ((r : ℤ) + j)) (p + q + 1 - j) o) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hz : oddMode leechData (0 : A) (p + q + 1 - j) o = 0 := by
      apply Subtype.ext
      change (((LatticeAllStateField.Y leechData 0)[[p + q + 1 - j]]) o.val) = 0
      simp
    rw [hr _ (by omega : (r : ℤ) ≤ (r : ℤ) + j), hz, smul_zero]
  let f (j : ℕ) : O := P b (q + r - j) (Q c (p + j) o)
  let g (j : ℕ) : O := P c (p + r - j) (Q b (q + j) o)
  have hFinite (f' : ℕ → O) (a : ℂ) :
      (∑ᶠ j : ℕ, (a * (-1 : ℂ)^j * (r.choose j : ℂ)) • f' j) =
        ∑ j ∈ Finset.range (r + 1), (a * (-1 : ℂ)^j * (r.choose j : ℂ)) • f' j := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra! hout
    exact hj (by simp [Nat.choose_eq_zero_of_lt (by simpa using hout : r < j)])
  have hreflect : (∑ j ∈ Finset.range (r + 1),
      ((-1 : ℂ)^r * (-1 : ℂ)^j * (r.choose j : ℂ)) • g j) =
      ∑ j ∈ Finset.range (r + 1), ((-1 : ℂ)^j * (r.choose j : ℂ)) •
        P c (p + j) (Q b (q + r - j) o) := by
    rw [← Finset.sum_range_reflect (fun j =>
      ((-1 : ℂ)^r * (-1 : ℂ)^j * (r.choose j : ℂ)) • g j)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
    have hs : (-1 : ℂ)^r * (-1 : ℂ)^(r - j) = (-1 : ℂ)^j := by
      rw [← pow_add, show r + (r - j) = 2 * (r - j) + j by omega, pow_add, pow_mul]
      norm_num
    rw [show r + 1 - 1 - j = r - j by omega, hs, Nat.choose_symm hjr]
    simp only [g, Int.natCast_sub hjr]
    rw [show p + (r : ℤ) - ((r : ℤ) - j) = p + j by omega,
      show q + ((r : ℤ) - j) = q + r - j by omega]
  have hc := c3_of_tail b c r hr d h q p s
  simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hc
  simp only [Int.cast_natCast, Ring.choose_natCast,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
  change -(∑ᶠ j : ℕ, ((-1 : ℂ)^j * (r.choose j : ℂ)) • f j) +
    (∑ᶠ j : ℕ, ((-1 : ℂ)^r * (-1 : ℂ)^j * (r.choose j : ℂ)) • g j) = _
  rw [hzero, hFinite g ((-1 : ℂ)^r), hreflect]
  have hf := hFinite f 1
  simp only [one_mul] at hf
  rw [hf]
  change -(∑ j ∈ Finset.range (r + 1), ((-1 : ℂ)^j * (r.choose j : ℂ)) •
    P b (q + r - j) (Q c (p + j) (P d s h))) +
    (∑ j ∈ Finset.range (r + 1), ((-1 : ℂ)^j * (r.choose j : ℂ)) •
      P c (p + j) (Q b (q + r - j) (P d s h))) = 0
  rw [hc, neg_add_cancel]

/-- All sufficiently high collision indices satisfy actual BBO Jacobi
uniformly in both external mode labels and every odd input. -/
theorem bboDefect_collision_tail (b c : B) :
    ∃ N : ℕ, ∀ (r : ℤ), (N : ℤ) ≤ r → ∀ p q : ℤ, bboDefect b c p q r = 0 := by
  obtain ⟨N, hN⟩ := bb_tail b c
  refine ⟨N.toNat, fun r hr p q => ?_⟩
  have hr' : (r.toNat : ℤ) = r := by omega
  rw [← hr']
  exact bboDefect_at_tail b c r.toNat (fun n hn => hN n (by omega)) p q

/--
info: 'D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCyclicLocality.bboDefect_collision_tail' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bboDefect_collision_tail

end Native

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOCyclicLocality
