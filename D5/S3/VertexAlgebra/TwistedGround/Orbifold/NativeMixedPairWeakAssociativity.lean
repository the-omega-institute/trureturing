import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOProductBPZ

/-!
The native mixed pair field on the even twisted sector has the physical
translation law. Extension skew then transposes actual mixed mode Jacobi.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeakAssociativity

open ActualLeechHyperbolic (leechData)
open NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit paritySign oddMode)
open NativeMixedPairField (mu mu_coeff_of_grade)
open NativeMixedPairBorcherds (mu_true_commutator mu_true_borcherds pair_tail)
open NativeMixedPairState (mixedPairWeight mixedPairState_grade mixedPairState_nonintegral_zero)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice)
open LatticeHalfFockGradedTrace (actualGrade actualTensorL0)
open LatticeHalfFockCorrectedField
open LatticeHalfFock (tensorL tensorStressField stressCoeff)
open LatticeInvolution (FixedCarrier)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (epsilon)
open private stress stress_twisted_mode from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
open private stress_odd_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeBBOProductBPZ
open private fixedParityMode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private projected_basis_grade from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private pairMap mode_tail from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairBorcherds
open private divided_succ_right from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
open private finsum_range reflect_choose sign_square from
  D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

local notation "ℒ" => leechData
local notation "U" => leechUnit
private abbrev A := FixedCarrier ℒ
private abbrev State (s : Bool) := Twisted ℒ U s
private abbrev B := State true
private abbrev H := State false
private abbrev O := OddCarrier ℒ
private abbrev T : Module.End ℂ B := MixedIntertwiner.translation ℒ U
private abbrev P (b : B) (n : ℤ) : H →ₗ[ℂ] O := (mu true b).coeff (-2*n-3)
private abbrev fixMode (s : Bool) (a : A) (n : ℤ) : Module.End ℂ (State s) :=
  (fixedParitySlice ℒ U (paritySign s) a)[[n]]
private abbrev twistedWeight (M : ℕ) : ℂ := (leechData.rank : ℂ) / 16 + (M : ℂ) / 2

private theorem stress_twisted_one (s : Bool) (M : ℕ) (x : State s)
    (hx : x.val ∈ actualGrade ℒ U M) :
    fixMode s (stress ℒ) 1 x = twistedWeight M • x := by
  apply Subtype.ext
  rw [fixedParityMode_val, Submodule.coe_smul]
  change ((correctedField ℒ U (LatticeActualConformalState.omega ℒ
    (HalfFockSpectralFiberSource.actualInverse ℒ))).coeff (-4)) x.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega ℒ U _
    (HalfFockSpectralFiberSource.actualInverse_left ℒ U)]
  have weight : actualTensorL0 ℒ U x.val = twistedWeight M • x.val := by
    simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hx
  simpa only [tensorStressField, HVertexOperator.coeff_of_coeff, stressCoeff,
    show (-4 : ℤ) % 2 = 0 by decide, ite_true,
    show (-(-4 : ℤ)-4)/2 = 0 by decide, actualTensorL0, tensorL] using weight

private theorem stress_pair_one (b : B) (h : H) (M K : ℕ) (q : ℤ)
    (hb : b.val ∈ actualGrade ℒ U M) (hh : h.val ∈ actualGrade ℒ U K) :
    oddMode ℒ (stress ℒ) 1 (P b q h) =
      (twistedWeight M + twistedWeight K - (q : ℂ) - 3/2) • P b q h := by
  change oddMode ℒ (stress ℒ) 1 ((mu true b).coeff (-2*q-3) h) =
    _ • ((mu true b).coeff (-2*q-3) h)
  rw [mu_coeff_of_grade true M K q b h hb hh]
  by_cases hwt : 2 * mixedPairWeight M K q = (M : ℤ) + (K : ℤ) + 3 - 2*q
  · rw [stress_odd_one _ _ (mixedPairState_grade true M K q b h)]
    have hcast : (2 : ℂ) * (mixedPairWeight M K q : ℂ) =
        (M : ℂ) + (K : ℂ) + 3 - 2*(q : ℂ) := by exact_mod_cast hwt
    congr 1
    simp only [twistedWeight, ActualLeechHyperbolic.leech_spec.1, Nat.cast_ofNat]
    linear_combination hcast / 2
  · rw [mixedPairState_nonintegral_zero true M K q b h hb hh hwt, map_zero, smul_zero]

private theorem choose_one_finsum (f : ℕ → O) :
    (∑ᶠ j : ℕ, Ring.choose (1 : ℂ) j • f j) = f 0 + f 1 := by
  rw [finsum_range (N := 2) (f := fun j => Ring.choose (1 : ℂ) j • f j)]
  · simp [Finset.sum_range_succ]
  · intro j hj
    have hchoose : Ring.choose (1 : ℂ) j = 0 := by
      rw [← Nat.cast_one (R := ℂ), Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [hchoose, zero_smul]

private theorem homogeneous_derivative (b : B) (h : H) (M K : ℕ) (n : ℤ)
    (hb : b.val ∈ actualGrade ℒ U M) (hh : h.val ∈ actualGrade ℒ U K) :
    P (T b) n h = -((n : ℂ) + 1/2) • P b (n-1) h := by
  have hc := (mu_true_commutator (stress ℒ) b h 1 (n-1)).2
  simp only [Int.cast_one] at hc
  change oddMode ℒ (stress ℒ) 1 (P b (n-1) h) -
      P b (n-1) (fixMode false (stress ℒ) 1 h) =
    ∑ᶠ j : ℕ, Ring.choose (1 : ℂ) j • P (fixMode true (stress ℒ) j b)
      (1+(n-1)-j) h at hc
  rw [choose_one_finsum] at hc
  simp only [Nat.cast_zero, Nat.cast_one, sub_zero, show 1 + (n-1) = n by omega] at hc
  change _ = P (T b) n h + P (fixMode true (stress ℒ) 1 b) (n-1) h at hc
  rw [stress_pair_one b h M K _ hb hh, stress_twisted_one false K h hh,
    stress_twisted_one true M b hb] at hc
  change _ = P (T b) n h + pairMap (n-1) (twistedWeight M • b) h at hc
  rw [map_smul, map_smul, LinearMap.smul_apply, Int.cast_sub, Int.cast_one] at hc
  let v : O := P b (n-1) h
  change (twistedWeight M + twistedWeight K - ((n : ℂ)-1) - 3/2) • v -
    twistedWeight K • v = P (T b) n h + twistedWeight M • v at hc
  calc
    P (T b) n h =
      ((twistedWeight M + twistedWeight K - ((n : ℂ)-1) - 3/2) • v -
        twistedWeight K • v) - twistedWeight M • v := by
      have hc' := congrArg (fun w : O => w - twistedWeight M • v) hc
      convert hc'.symm using 1
      module
    _ = -((n : ℂ) + 1/2) • v := by module

private theorem expand_states (s : Bool) (x : State s) (F G : State s →ₗ[ℂ] O)
    (h : ∀ (M : ℕ) (y : State s), y.val ∈ actualGrade ℒ U M → F y = G y) :
    F x = G x := by
  classical
  rw [← sum_projectedBasis s x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  congr 1
  exact h _ _ (projected_basis_grade s i)

/-- Physical translation of the actual B-on-H field. The operator on B is
the twisted component of the ordinary extension's translation. -/
theorem mu_true_derivative (b : B) (h : H) (n : ℤ) :
    (mu true (MixedIntertwiner.translation ℒ U b)).coeff (-2*n-3) h =
      -((n : ℂ) + 1/2) • (mu true b).coeff (-2*(n-1)-3) h := by
  let F := (LinearMap.applyₗ (R := ℂ) h).comp ((pairMap n).comp T)
  let G := (-((n : ℂ) + 1/2)) • (LinearMap.applyₗ (R := ℂ) h).comp (pairMap (n-1))
  change F b = G b
  apply expand_states true b F G
  intro M b' hb
  let F' := P (T b') n
  let G' := (-((n : ℂ) + 1/2)) • P b' (n-1)
  change F' h = G' h
  exact expand_states false h F' G' fun K h' hh =>
    homogeneous_derivative b' h' M K n hb hh


private theorem choose_step (x : ℂ) (j : ℕ) :
    ((j : ℂ) + 1) * Ring.choose x (j + 1) =
      Ring.choose x j * (x - j) := by
  have h := Ring.choose_smul_choose x (Nat.le_succ j)
  simpa only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.cast_succ,
    show j.succ - j = 1 by omega, Ring.choose_one_right] using h

/-- Divided state translation with the signed physical half-integer binomial. -/
theorem mu_true_divided_derivative (j : ℕ) (b : B) (h : H) (n : ℤ) :
    P (dividedTranslation T j b) n h =
      (((-1 : ℂ)^j) * Ring.choose ((n : ℂ) + 1/2) j) • P b (n-j) h := by
  induction j generalizing n b with
  | zero => simp [dividedTranslation]
  | succ j ih =>
    have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    apply (smul_right_inj hj).mp
    change _ • pairMap n _ h = _
    rw [← LinearMap.smul_apply, ← map_smul, divided_succ_right]
    change P (dividedTranslation T j (T b)) n h = _
    have step : P (T b) (n-j) h = -(((n-(j : ℤ) : ℤ) : ℂ)+1/2) • P b (n-j-1) h :=
      mu_true_derivative b h (n-j)
    rw [ih, step]
    simp only [smul_smul, Nat.cast_succ, pow_succ]
    rw [show n - (j : ℤ) - 1 = n - ((j + 1 : ℕ) : ℤ) by omega]
    push_cast
    congr 1
    have step := choose_step ((n : ℂ) + 1/2) j
    linear_combination ((-1 : ℂ)^j) * step

private theorem diagonal (x y : ℂ) (l : ℕ) :
    (∑ i ∈ Finset.range (l + 1), (-1 : ℂ)^i * Ring.choose x i *
      Ring.choose (x + y - (i : ℂ)) (l - i)) = Ring.choose y l := by
  have vandermonde := Ring.add_choose_eq (R := ℂ)
    (r := x) (s := -x - y + (l : ℂ) - 1) l (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
  calc
    _ = ∑ i ∈ Finset.range (l + 1), (-1 : ℂ)^l *
        (Ring.choose x i * Ring.choose (-x - y + (l : ℂ) - 1) (l - i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hle : i ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hreflect : (-1 : ℂ)^(l-i) * Ring.choose (x+y-(i : ℂ)) (l-i) =
          Ring.choose (-x-y+(l : ℂ)-1) (l-i) := by
        rw [reflect_choose, Nat.cast_sub hle]
        congr 1
        ring
      have hsign : (-1 : ℂ)^l * (-1 : ℂ)^(l-i) = (-1 : ℂ)^i := by
        conv_lhs => enter [1, 2]; rw [show l = i+(l-i) by omega]
        rw [pow_add, mul_assoc, ← mul_pow]
        norm_num
      rw [← hreflect]
      calc
        _ = ((-1 : ℂ)^l * (-1 : ℂ)^(l-i)) *
            (Ring.choose x i * Ring.choose (x+y-(i : ℂ)) (l-i)) := by rw [hsign]; ring
        _ = _ := by ring
    _ = (-1 : ℂ)^l * Ring.choose (-y+(l : ℂ)-1) l := by
      rw [← Finset.mul_sum, ← vandermonde]
      congr 2
      ring
    _ = _ := by rw [← reflect_choose, ← mul_assoc, ← mul_pow]; norm_num

open MixedIntertwiner (originalRightCoefficient)
open private rightTerm from D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
open private epsilon_add epsilon_nat from
  D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

private abbrev rightMode (b : B) (a : A) (n : ℤ) : B :=
  originalRightCoefficient ℒ U n b a

private theorem right_mode_range (b : B) (a : A) (r : ℤ) (N : ℕ)
    (tail : ∀ i : ℕ, N ≤ i → fixMode true a (r+i) b = 0) (i : ℕ) :
    rightMode b a (r+i) = ∑ j ∈ Finset.range (N-i),
      epsilon (r+i+j+1) • dividedTranslation T j (fixMode true a (r+i+j) b) := by
  change (∑ᶠ j : ℕ, rightTerm ℒ U (r+i) b a j) = _
  rw [finsum_range (N := N-i) (f := fun j => rightTerm ℒ U (r+i) b a j)]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [rightTerm, dividedTranslation, LinearMap.smul_apply, smul_smul, epsilon]
    rfl
  · intro j hj
    change (epsilon (r+i+j+1) * (j.factorial : ℂ)⁻¹) •
      (T^j) (fixMode true a (r+i+j) b) = 0
    rw [show r+(i : ℤ)+j = r+((i+j : ℕ) : ℤ) by push_cast; ring,
      tail (i+j) (by omega), map_zero, smul_zero]

private abbrev reversedIterate (b : B) (a : A) (h : H) (q p r : ℤ) (i : ℕ) : O :=
  Ring.choose ((q : ℂ) + 1/2) i • P (rightMode b a (r+i)) (p+q-i) h

private abbrev forwardIterate (a : A) (b : B) (h : H) (p q r : ℤ) (i : ℕ) : O :=
  Ring.choose (p : ℂ) i • P (fixMode true a (r+i) b) (p+q-i) h

private theorem transpose_iterate (b : B) (a : A) (h : H) (q p r : ℤ) :
    Function.HasFiniteSupport (reversedIterate b a h q p r) ∧
    (∑ᶠ i, reversedIterate b a h q p r i) =
      epsilon (r+1) • ∑ᶠ i, forwardIterate a b h p q r i := by
  obtain ⟨N, tail⟩ := mode_tail true a b r
  have skew := right_mode_range b a r N tail
  have out (i : ℕ) (hi : N ≤ i) : rightMode b a (r+i) = 0 := by
    rw [skew i, Nat.sub_eq_zero_of_le hi, Finset.range_zero, Finset.sum_empty]
  have hrev (i : ℕ) (hi : N ≤ i) : reversedIterate b a h q p r i = 0 := by
    change Ring.choose ((q : ℂ)+1/2) i • pairMap (p+q-i) (rightMode b a (r+i)) h = 0
    rw [out i hi, map_zero, LinearMap.zero_apply, smul_zero]
  have hfwd (i : ℕ) (hi : N ≤ i) : forwardIterate a b h p q r i = 0 := by
    change Ring.choose (p : ℂ) i • pairMap (p+q-i) (fixMode true a (r+i) b) h = 0
    rw [tail i hi, map_zero, LinearMap.zero_apply, smul_zero]
  refine ⟨(Finset.range N).finite_toSet.subset ?_, ?_⟩
  · intro i hi
    exact Finset.mem_range.mpr (Nat.lt_of_not_ge fun hg => hi (hrev i hg))
  rw [finsum_range (f := reversedIterate b a h q p r) hrev,
    finsum_range (f := forwardIterate a b h p q r) hfwd]
  let x : ℂ := (q : ℂ) + 1/2
  let y : ℂ := p
  let f : ℕ → O := fun l => P (fixMode true a (r+l) b) (p+q-l) h
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N-i),
        (epsilon (r+1) * ((-1 : ℂ)^i * Ring.choose x i *
          Ring.choose (x+y-(i : ℂ)) j)) • f (i+j) := by
      apply Finset.sum_congr rfl
      intro i _
      change Ring.choose x i • pairMap (p+q-i) (rightMode b a (r+i)) h = _
      rw [skew i, map_sum, LinearMap.sum_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      change _ • P (dividedTranslation T j _) (p+q-i) h = _
      rw [mu_true_divided_derivative, smul_smul]
      simp only [f, Nat.cast_add]
      rw [show p+q-(i : ℤ)-j = p+q-((i : ℤ)+j) by omega, add_assoc r (i : ℤ) (j : ℤ)]
      congr 1
      have sign : epsilon (r+((i : ℤ)+j)+1) * (-1 : ℂ)^j =
          epsilon (r+1) * (-1 : ℂ)^i := by
        rw [show r+((i : ℤ)+j)+1 = (r+1)+i+j by omega, epsilon_add ((r+1)+i),
          epsilon_add (r+1), epsilon_nat, epsilon_nat, mul_assoc, ← mul_pow]
        norm_num
      have index : ((p+q-(i : ℤ) : ℤ) : ℂ)+1/2 = x+y-(i : ℂ) := by
        simp only [x, y, Int.cast_add, Int.cast_sub, Int.cast_natCast]
        ring
      rw [index]
      calc
        _ = (epsilon (r+((i : ℤ)+j)+1) * (-1 : ℂ)^j) *
            (Ring.choose x i * Ring.choose (x+y-(i : ℂ)) j) := by ring
        _ = _ := by rw [sign]; ring
    _ = ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range (l+1),
        (epsilon (r+1) * ((-1 : ℂ)^i * Ring.choose x i *
          Ring.choose (x+y-(i : ℂ)) (l-i))) • f l := by
      rw [← Finset.sum_range_diag_flip]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    _ = _ := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro l _
      simp_rw [mul_smul (epsilon (r+1))]
      rw [← Finset.smul_sum, ← Finset.sum_smul, diagonal]

private abbrev productWeight (r : ℤ) (j : ℕ) : ℂ :=
  (-1 : ℂ)^j * Ring.choose (r : ℂ) j

/-- The signed B,A,H mode Jacobi identity for native B, A and H states.
The integer q labels the B mode q+1/2. The iterate uses the actual B-on-A
coefficient of the ordinary extension. -/
theorem mu_true_reversed_borcherds (b : B) (a : A) (h : H) (q p r : ℤ) :
    let iterate := fun j : ℕ => Ring.choose ((q : ℂ)+1/2) j •
      (mu true (originalRightCoefficient ℒ U (r+j) b a)).coeff (-2*(p+q-j)-3) h
    let first := fun j : ℕ => productWeight r j •
      (mu true b).coeff (-2*(q+r-j)-3) (((fixedParitySlice ℒ U 1 a)[[p+j]]) h)
    let second := fun j : ℕ => (epsilon r * productWeight r j) •
      oddMode ℒ a (p+r-j) ((mu true b).coeff (-2*(q+j)-3) h)
    Function.HasFiniteSupport iterate ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ j, iterate j) = (∑ᶠ j, first j) - (∑ᶠ j, second j) := by
  obtain ⟨hiter, hit⟩ := transpose_iterate b a h q p r
  obtain ⟨_, hab, hba, heq⟩ := mu_true_borcherds a b h p q r
  let first : ℕ → O := fun j => productWeight r j • P b (q+r-j) (fixMode false a (p+j) h)
  let second : ℕ → O := fun j => productWeight r j • oddMode ℒ a (p+r-j) (P b (q+j) h)
  change Function.HasFiniteSupport second at hab
  change Function.HasFiniteSupport (fun j => (epsilon r * productWeight r j) •
    P b (q+r-j) (fixMode false a (p+j) h)) at hba
  have support_scale (g : ℕ → O) (hg : Function.HasFiniteSupport g) (c : ℂ) :
      Function.HasFiniteSupport (fun j => c • g j) :=
    hg.subset (fun j hj hzero => hj (by simp [hzero]))
  have hs : ∀ v : O, epsilon r • (epsilon r • v) = v := by
    intro v
    rw [smul_smul, sign_square, one_smul]
  simp only [mul_smul (epsilon r)] at hba
  change Function.HasFiniteSupport (fun j => epsilon r • first j) at hba
  have hf : Function.HasFiniteSupport first := by
    have hf' := support_scale _ hba (epsilon r)
    simpa only [hs] using hf'
  have hg : Function.HasFiniteSupport (fun j => epsilon r • second j) :=
    support_scale second hab (epsilon r)
  change (∑ᶠ j, forwardIterate a b h p q r j) =
    (∑ᶠ j, second j) - ∑ᶠ j, (epsilon r * productWeight r j) •
      P b (q+r-j) (fixMode false a (p+j) h) at heq
  simp only [mul_smul (epsilon r)] at heq
  change (∑ᶠ j, forwardIterate a b h p q r j) =
    (∑ᶠ j, second j) - ∑ᶠ j, epsilon r • first j at heq
  dsimp only
  simp only [mul_smul (epsilon r)]
  change Function.HasFiniteSupport (reversedIterate b a h q p r) ∧
    Function.HasFiniteSupport first ∧ Function.HasFiniteSupport (fun j => epsilon r • second j) ∧
    (∑ᶠ j, reversedIterate b a h q p r j) =
      (∑ᶠ j, first j) - ∑ᶠ j, epsilon r • second j
  refine ⟨hiter, hf, hg, ?_⟩
  have hfirst := (smul_finsum (epsilon r) first).symm
  have hsecond := (smul_finsum (epsilon r) second).symm
  rw [hit, heq, hfirst, hsecond]
  have hsign : epsilon (r+1) = -epsilon r := by
    rw [epsilon_add, show epsilon 1 = -1 by norm_num [epsilon], mul_neg, mul_one]
  have swap {V : Type} [AddCommGroup V] [Module ℂ V] (x y : V) :
      -epsilon r • (y - epsilon r • x) = x - epsilon r • y := by
    rw [neg_smul, smul_sub, smul_smul, sign_square, one_smul, neg_sub]
  rw [hsign]
  exact swap (V := O) (∑ᶠ j, first j) (∑ᶠ j, second j)

/-- Uniform B,A,H weak associativity in coefficients. The two sums are the
coefficient of y^(-r-1) z^(-p-1) in the two prescribed expansions. The product
uses Taylor in z of the integer power y^(L+1/2) P_b(y). The iterate multiplies
the literal B-on-A modes by the binomial in y of (z+y)^(L+1/2). -/
theorem mu_true_reversed_weak_associativity (b : B) (h : H) :
    ∃ L : ℕ, (∀ n : ℤ, (L : ℤ) ≤ n → (mu true b).coeff (-2*n-3) h = 0) ∧
      ∀ (a : A) (p r : ℤ),
        let product := fun j : ℕ => Ring.choose ((j : ℂ)-(r : ℂ)-1) j •
          (mu true b).coeff (-2*((L : ℤ)+r-j)-3) (((fixedParitySlice ℒ U 1 a)[[p+j]]) h)
        let iterate := fun j : ℕ => Ring.choose ((L : ℂ)+1/2) j •
          (mu true (originalRightCoefficient ℒ U (r+j) b a)).coeff
            (-2*(p+(L : ℤ)-j)-3) h
        Function.HasFiniteSupport product ∧ Function.HasFiniteSupport iterate ∧
          (∑ᶠ j, product j) = ∑ᶠ j, iterate j := by
  obtain ⟨L, tail⟩ := pair_tail b h 0
  have htail (n : ℤ) (hn : (L : ℤ) ≤ n) : P b n h = 0 := by
    have hn' : n = (n.toNat : ℤ) := by omega
    rw [hn']
    simpa only [zero_add] using tail n.toNat (by omega)
  refine ⟨L, htail, ?_⟩
  intro a p r
  obtain ⟨hi, hf, _, heq⟩ := mu_true_reversed_borcherds b a h L p r
  have hsecond (j : ℕ) :
      (epsilon r * productWeight r j) • oddMode ℒ a (p+r-j) (P b ((L : ℤ)+j) h) = 0 := by
    rw [htail _ (by omega), map_zero, smul_zero]
  have hweight (j : ℕ) : Ring.choose ((j : ℂ)-(r : ℂ)-1) j = productWeight r j := by
    rw [productWeight, reflect_choose]
    congr 1
    ring
  simp only [hweight]
  change (∑ᶠ j, reversedIterate b a h L p r j) =
    (∑ᶠ j : ℕ, productWeight r j • P b ((L : ℤ)+r-j) (fixMode false a (p+j) h)) -
      ∑ᶠ j, (epsilon r * productWeight r j) • oddMode ℒ a (p+r-j) (P b ((L : ℤ)+j) h)
    at heq
  have hz : (∑ᶠ j, (epsilon r * productWeight r j) •
      oddMode ℒ a (p+r-j) (P b ((L : ℤ)+j) h)) = 0 := by
    simp only [hsecond, finsum_zero]
  rw [hz] at heq
  have heq' : (∑ᶠ j, reversedIterate b a h L p r j) =
      ∑ᶠ j : ℕ, productWeight r j • P b ((L : ℤ)+r-j) (fixMode false a (p+j) h) := by
    rw [heq]
    module
  refine ⟨hf, by simpa only [Int.cast_natCast] using hi, ?_⟩
  change (∑ᶠ j : ℕ, productWeight r j • P b ((L : ℤ)+r-j) (fixMode false a (p+j) h)) =
    ∑ᶠ j : ℕ, Ring.choose ((L : ℂ)+1/2) j • P (rightMode b a (r+j)) (p+(L : ℤ)-j) h
  simpa only [reversedIterate, Int.cast_natCast] using heq'.symm

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeakAssociativity
