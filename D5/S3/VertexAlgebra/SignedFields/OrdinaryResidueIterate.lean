/- GID: D5/S3/VertexAlgebra/SignedFields/OrdinaryResidueIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SignedFields/OrdinaryResidueIterate
   mirror-E: none(waiver:algebraic-signed-field-calculus)
   anchors: []
   utility: none
   digest: Ordinary local-field residue iterates at negative first indices. -/

import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality
import D5.S3.VertexAlgebra.Analysis.IntegerNewton
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

/-! Ordinary local-field iterates from finite Newton reconstruction.

The two normally ordered terms use the contact coefficients of the second
and third fields. The remaining two terms convolve the signed kernels with
the positive and negative mode parts of the first and third commutator.
All infinite index sets are summed with vectorwise finite support. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.OrdinaryResidueIterate

open FieldNormalProductLocality (delta deltaEnd)
local notation "modeComm" => FieldNormalProductLocality.commutator
open SignedFieldNormalProductLocality (signedComm forward_finite reverse_finite)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open BinomialKernelDelta (chooseSign chooseSign_pascal finsum_split)
open Analysis.IntegerNewton (delta_newton)
open LatticeHalfFockGroundRightCurrentTransport.Calculus (R Z)
open private R_mode Z_mode ext_modes from
  D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private diagonal_difference contactCoefficient_eq_difference from
  D5.S3.VertexAlgebra.Analysis.IntegerNewton

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The coefficient at modes `a,b` of the signed ordered residue distribution. -/
def residueDistribution (s : ℂ) (A B : VertexOperator ℂ V) (r a b : ℤ) :
    Module.End ℂ V :=
  (residueField s r (Z (-a) A) B).operator [[b]]

private theorem distribution_apply (s : ℂ) (A B : VertexOperator ℂ V)
    (r a b : ℤ) (v : V) :
    residueDistribution s A B r a b v =
      (∑ᶠ j : ℕ, chooseSign r j • (A [[a+r-j]]) ((B [[b+j]]) v)) -
        (epsilon r * s) • ∑ᶠ j : ℕ, chooseSign r j •
          (B [[r+b-j]]) ((A [[a+j]]) v) := by
  simp only [residueDistribution, (residueField s r (Z (-a) A) B).coefficient,
    residueCoefficient, residueLeft, residueRight, Z_mode, sub_neg_eq_add,
    integerBinomial, chooseSign]
  simp only [show ∀ j : ℕ, r-(j:ℤ)+a = a+r-j by intro j; omega,
    show ∀ j : ℕ, (j:ℤ)+a = a+j by intro j; omega]

private theorem weighted_pascal (r : ℤ) (f : ℕ → V)
    (hf : Function.HasFiniteSupport f) :
    (∑ᶠ j : ℕ, chooseSign r j • f j) -
      (∑ᶠ j : ℕ, chooseSign r j • f (j+1)) =
      ∑ᶠ j : ℕ, chooseSign (r+1) j • f j := by
  let F := fun j : ℕ => chooseSign r j • f j
  let G := fun j : ℕ => chooseSign r j • f (j+1)
  let H := fun j : ℕ => chooseSign (r+1) j • f j
  have hF : Function.HasFiniteSupport F := hf.smul_right _
  have hG : Function.HasFiniteSupport G :=
    (hf.comp_of_injective (fun j k h => Nat.add_right_cancel h)).smul_right _
  have hH : Function.HasFiniteSupport H := hf.smul_right _
  change (∑ᶠ j, F j) - (∑ᶠ j, G j) = ∑ᶠ j, H j
  have hTail : Function.HasFiniteSupport (fun j : ℕ => F (j+1)) :=
    hF.comp_of_injective (fun j k h => Nat.add_right_cancel h)
  rw [finsum_split F hF, finsum_split H hH, add_sub_assoc,
    ← finsum_sub_distrib hTail hG]
  congr 1
  · simp [F, H]
  · apply finsum_congr
    intro j
    simp only [F, G, H, chooseSign_pascal, sub_smul]

private theorem epsilon_succ (r : ℤ) : epsilon (r+1) = -epsilon r := by
  simp [epsilon, zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num)]

private theorem distribution_delta (s : ℂ) (A B : VertexOperator ℂ V) (r : ℤ) :
    delta (residueDistribution s A B r) = residueDistribution s A B (r+1) := by
  funext a b
  apply LinearMap.ext
  intro v
  let f (j : ℕ) := (A [[a+r+1-j]]) ((B [[b+j]]) v)
  let g (j : ℕ) := (B [[r+b+1-j]]) ((A [[a+j]]) v)
  have hf : Function.HasFiniteSupport f := forward_finite A B (a+r+1) b v
  have hg : Function.HasFiniteSupport g := by
    refine BddAbove.finite (bddAbove_def.mpr ⟨
      (-((HahnModule.of ℂ).symm (A v)).order - a - 1).toNat, ?_⟩)
    intro j hj
    contrapose! hj
    have hz : (A [[a+j]]) v = 0 :=
      VertexOperator.ncoeff_eq_zero_of_lt_order A _ _ (by omega)
    simp [g, hz]
  simp only [delta, LinearMap.sub_apply, distribution_apply]
  have ff := weighted_pascal r f hf
  have gg := weighted_pascal r g hg
  simp only [f, g, Nat.cast_add, Nat.cast_one,
    show ∀ j : ℕ, a+r+1-((j:ℤ)+1) = a+r-j by intro j; omega,
    show ∀ j : ℕ, b+((j:ℤ)+1) = b+1+j by intro j; omega,
    show ∀ j : ℕ, r+b+1-((j:ℤ)+1) = r+b-j by intro j; omega,
    show ∀ j : ℕ, a+((j:ℤ)+1) = a+1+j by intro j; omega] at ff gg
  rw [show a+1+r = a+r+1 by omega, show r+(b+1) = r+b+1 by omega,
    show a+(r+1) = a+r+1 by omega, show r+1+b = r+b+1 by omega, epsilon_succ]
  rw [← ff, ← gg, neg_mul, neg_smul, smul_sub]
  abel

private theorem distribution_iterate (s : ℂ) (A B : VertexOperator ℂ V)
    (r : ℤ) (k : ℕ) :
    delta^[k] (residueDistribution s A B r) = residueDistribution s A B (r+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, distribution_delta]
    congr 1
    omega

private theorem distribution_zero (s : ℂ) (A B : VertexOperator ℂ V) :
    residueDistribution s A B 0 = signedComm s A B := by
  funext a b
  apply LinearMap.ext
  intro v
  rw [distribution_apply, finsum_eq_single _ 0, finsum_eq_single _ 0]
  · simp [signedComm, epsilon]
  · intro j hj
    simp [chooseSign, Ring.choose_zero_ite, hj]
  · intro j hj
    simp [chooseSign, Ring.choose_zero_ite, hj]

private theorem shifted_zero_mode (s : ℂ) (A B : VertexOperator ℂ V) (r b : ℤ) :
    residueDistribution s A B r 0 b = (residueField s r A B).operator [[b]] := by
  have h : Z 0 A = A := by
    apply ext_modes
    intro n
    simp [Z_mode]
  unfold residueDistribution
  rw [neg_zero, h]

/-- Locality gives a finite Newton expansion in every pair of integer modes,
including for negative residue exponents. -/
theorem residueDistribution_newton (s : ℂ) (A B : VertexOperator ℂ V)
    (K : ℕ) (locality : delta^[K] (signedComm s A B) = 0) (r a b : ℤ) :
    residueDistribution s A B r a b =
      ∑ i ∈ Finset.range ((K : ℤ)-r).toNat,
        (Ring.choose a i : ℤ) • ((residueField s (r+i) A B).operator [[a+b-i]]) := by
  have atCutoff : residueDistribution s A B (K : ℤ) = 0 := by
    simpa only [distribution_iterate, zero_add] using
      (show delta^[K] (residueDistribution s A B 0) = 0 by rw [distribution_zero, locality])
  have killed : delta^[((K : ℤ)-r).toNat] (residueDistribution s A B r) = 0 := by
    rw [distribution_iterate]
    let k := (r-(K : ℤ)).toNat
    have index : r + (((K : ℤ)-r).toNat : ℤ) = (K : ℤ) + (k : ℤ) := by
      dsimp [k]
      omega
    rw [index, ← distribution_iterate, atCutoff]
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[k] 0 = 0
    rw [← Module.End.pow_apply, map_zero]
  rw [delta_newton _ _ killed]
  apply Finset.sum_congr rfl
  intro i _
  rw [contactCoefficient_eq_difference, diagonal_difference, distribution_iterate, sub_zero,
    shifted_zero_mode]

/-- The ordinary transport residue is the exchange-scalar-one signed residue. -/
theorem ordinary_residue (A B : VertexOperator ℂ V) (r : ℤ) :
    R A B r = (residueField 1 r A B).operator := by
  apply ext_modes
  intro b
  apply LinearMap.ext
  intro v
  rw [R_mode, (residueField 1 r A B).coefficient]
  have castChoose (j : ℕ) : (↑(Ring.choose r j) : ℂ) = Ring.choose (r : ℂ) j :=
    Ring.map_choose (Int.castRingHom ℂ) r j
  simp only [residueCoefficient, residueLeft, residueRight, epsilon, mul_one,
    LatticeHalfFockGroundRightCurrentTransport.residueWeight, integerBinomial,
    castChoose, add_comm r b]

private theorem weight_negative (i j : ℕ) :
    chooseSign (-(i : ℤ)-1) j = ((i+j).choose i : ℂ) := by
  have square : (-1 : ℂ)^j * (-1 : ℂ)^j = 1 := by rw [← mul_pow]; norm_num
  rw [chooseSign, show -(i : ℤ)-1 = -((i : ℤ)+1) by omega, Ring.choose_neg,
    show (i : ℤ)+1+j-1 = ((i+j : ℕ) : ℤ) by omega, Ring.choose_natCast]
  simp only [Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
    Int.cast_natCast]
  rw [← mul_assoc, square, one_mul, ← Nat.choose_symm_add]

private theorem choose_negative_mode (i j : ℕ) :
    ((Ring.choose (-(j : ℤ)-1) i : ℤ) : ℂ) =
      -epsilon (-(i : ℤ)-1) * chooseSign (-(i : ℤ)-1) j := by
  have sign : -epsilon (-(i : ℤ)-1) = (-1 : ℂ)^i := by
    rw [epsilon, show -(i : ℤ)-1 = -((i+1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, ← inv_pow]
    norm_num [pow_succ]
  rw [sign, weight_negative, show -(j : ℤ)-1 = -((j : ℤ)+1) by omega,
    Ring.choose_neg, show (j : ℤ)+1+i-1 = ((i+j : ℕ) : ℤ) by omega,
    Ring.choose_natCast]
  simp [Units.smul_def]

omit [Module ℂ V] in
private theorem finsum_skip (f : ℕ → V) (i : ℕ) (zero : ∀ j < i, f j = 0) :
    (∑ᶠ j : ℕ, f j) = ∑ᶠ j : ℕ, f (i+j) := by
  have subset : Function.support f ⊆ Set.range (fun j : ℕ => i+j) := by
    intro j hj
    have h : i ≤ j := by by_contra! h; exact hj (zero j h)
    exact ⟨j-i, by change i+(j-i)=j; omega⟩
  have sets : Set.range (fun j : ℕ => i+j) ∩ Function.support f =
      Set.univ ∩ Function.support f := by rw [Set.inter_eq_right.mpr subset, Set.univ_inter]
  rw [← finsum_mem_range (f := f) (g := fun j : ℕ => i+j)
    (fun _ _ h => Nat.add_left_cancel h), finsum_mem_inter_support_eq f _ _ sets,
    finsum_mem_univ]

private theorem ordinary_mode (A B : VertexOperator ℂ V) (r b : ℤ) (v : V) :
    ((R A B r) [[b]]) v =
      (∑ᶠ j : ℕ, chooseSign r j • (A [[r-j]]) ((B [[b+j]]) v)) -
        epsilon r • ∑ᶠ j : ℕ, chooseSign r j • (B [[r+b-j]]) ((A [[j]]) v) := by
  rw [ordinary_residue, ← shifted_zero_mode, distribution_apply]
  simp only [zero_add, mul_one]

/-- The two normally ordered terms of the negative-first iterate, after finite
Newton reconstruction in the second and third fields. -/
theorem normal_contraction (J A B : VertexOperator ℂ V) (K : ℕ)
    (locality : delta^[K] (signedComm 1 A B) = 0) (n b : ℤ) (v : V) :
    (∑ᶠ j : ℕ, (J [[-(j : ℤ)-1]]) (residueDistribution 1 A B n j b v)) +
      (∑ᶠ j : ℕ, residueDistribution 1 A B n (-(j : ℤ)-1) b ((J [[j]]) v)) =
      ∑ i ∈ Finset.range ((K : ℤ)-n).toNat,
        ((R J (R A B (n+i)) (-(i : ℤ)-1)) [[b]]) v := by
  let cutoff := Finset.range ((K : ℤ)-n).toNat
  let C (i : ℕ) := R A B (n+i)
  let neg (j i : ℕ) := ((Ring.choose (j : ℤ) i : ℤ) : ℂ) •
    (J [[-(j : ℤ)-1]]) (((C i) [[b+j-i]]) v)
  let pos (j i : ℕ) := ((Ring.choose (-(j : ℤ)-1) i : ℤ) : ℂ) •
    ((C i) [[b-(j : ℤ)-1-i]]) ((J [[j]]) v)
  have hn (i : ℕ) : Function.HasFiniteSupport (fun j => neg j i) := by
    have finite := forward_finite J (C i) (-1) (b-i) v
    simpa only [neg, Pi.smul_def',
      show ∀ j : ℕ, (-1 : ℤ)-j = -j-1 by intro j; omega,
      show ∀ j : ℕ, b-(i:ℤ)+j = b+j-i by intro j; omega]
      using finite.smul_right (fun j : ℕ => ((Ring.choose (j : ℤ) i : ℤ) : ℂ))
  have hp (i : ℕ) : Function.HasFiniteSupport (fun j => pos j i) := by
    have finite := reverse_finite (C i) J (b-1-i) v
    simpa only [pos, Pi.smul_def',
      show ∀ j : ℕ, b-1-(i:ℤ)-j = b-j-1-i by intro j; omega]
      using finite.smul_right (fun j : ℕ => ((Ring.choose (-(j : ℤ)-1) i : ℤ) : ℂ))
  have rowNeg (j : ℕ) : (J [[-(j : ℤ)-1]]) (residueDistribution 1 A B n j b v) =
      ∑ i ∈ cutoff, neg j i := by
    rw [residueDistribution_newton 1 A B K locality]
    simp only [cutoff, neg, C, ordinary_residue, LinearMap.sum_apply, ← Int.cast_smul_eq_zsmul ℂ,
      LinearMap.smul_apply, map_sum, map_smul, add_comm b (j : ℤ)]
  have rowPos (j : ℕ) :
      residueDistribution 1 A B n (-(j : ℤ)-1) b ((J [[j]]) v) =
        ∑ i ∈ cutoff, pos j i := by
    rw [residueDistribution_newton 1 A B K locality]
    simp only [cutoff, pos, C, ordinary_residue, LinearMap.sum_apply, ← Int.cast_smul_eq_zsmul ℂ,
      LinearMap.smul_apply,
      show -(j : ℤ)-1+b = b-j-1 by omega]
  simp_rw [rowNeg, rowPos]
  rw [finsum_sum_comm cutoff neg (fun i _ => hn i),
    finsum_sum_comm cutoff pos (fun i _ => hp i), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have splice : (∑ᶠ j : ℕ, neg j i) = ∑ᶠ j : ℕ, neg (i+j) i := by
    apply finsum_skip
    intro j hj
    simp [neg, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hj]
  rw [splice, ordinary_mode]
  have left : (∑ᶠ j : ℕ, neg (i+j) i) =
      ∑ᶠ j : ℕ, chooseSign (-(i : ℤ)-1) j •
        (J [[-(i : ℤ)-1-j]]) (((C i) [[b+j]]) v) := by
    apply finsum_congr
    intro j
    simp only [neg, weight_negative, Ring.choose_natCast, Int.cast_natCast, Nat.cast_add]
    rw [show -((i : ℤ)+j)-1 = -(i : ℤ)-1-j by omega,
      show b+((i : ℤ)+j)-i = b+j by omega]
  rw [left, sub_eq_add_neg (_ : V), ← neg_smul]
  congr 1
  have rightFinite := reverse_finite (C i) J (-(i : ℤ)-1+b) v
  have weighted : Function.HasFiniteSupport (fun j : ℕ =>
      chooseSign (-(i : ℤ)-1) j • ((C i) [[-(i : ℤ)-1+b-j]]) ((J [[j]]) v)) :=
    rightFinite.smul_right _
  rw [smul_finsum' _ weighted]
  apply finsum_congr
  intro j
  simp only [pos, choose_negative_mode, smul_smul]
  rw [show b-(j : ℤ)-1-i = -(i : ℤ)-1+b-j by omega]

private theorem ordinary_commutator_newton (J B : VertexOperator ℂ V) (L : ℕ)
    (locality : delta^[L] (signedComm 1 J B) = 0) (a b : ℤ) :
    modeComm J B a b =
      ∑ i ∈ Finset.range L, ((Ring.choose a i : ℤ) : ℂ) • ((R J B i) [[a+b-i]]) := by
  have h := residueDistribution_newton 1 J B L locality 0 a b
  rw [distribution_zero] at h
  simpa [signedComm, FieldNormalProductLocality.commutator, ← ordinary_residue,
    Algebra.smul_def] using h

private theorem weight_eq (r : ℤ) (j : ℕ) :
    chooseSign r j = LatticeHalfFockGroundRightCurrentTransport.residueWeight r j := by
  unfold chooseSign LatticeHalfFockGroundRightCurrentTransport.residueWeight
  rw [show (↑(Ring.choose r j) : ℂ) = Ring.choose (r : ℂ) j from
    Ring.map_choose (Int.castRingHom ℂ) r j]

open private residue_convolution diagonal_finite fiber_finite from
  D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

private theorem convolution (r d : ℤ) (f : ℕ → V) (h : Function.HasFiniteSupport f) :
    (∑ᶠ p : ℕ, ∑ᶠ k : ℕ, (chooseSign r p * chooseSign d k) • f (p+k)) =
      ∑ᶠ p : ℕ, chooseSign (r+d) p • f p := by
  simp_rw [weight_eq]
  have finite : Function.HasFiniteSupport (fun z : ℕ × ℕ =>
      (LatticeHalfFockGroundRightCurrentTransport.residueWeight r z.1 *
        LatticeHalfFockGroundRightCurrentTransport.residueWeight d z.2) • f (z.1+z.2)) :=
    (diagonal_finite f h).smul_right _
  rw [← finsum_curry _ finite]
  exact residue_convolution r d f h

/-- The two split commutators contract with the outer signed kernels to give
the second sum of the negative-first iterate. -/
theorem split_commutator_contraction (J A B : VertexOperator ℂ V) (L : ℕ)
    (locality : delta^[L] (signedComm 1 J B) = 0) (n b : ℤ) (v : V) :
    (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ,
      (A [[n-1-p-k]]) (modeComm J B k (b+p) v)) +
      epsilon n • (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ,
        modeComm J B (-(k : ℤ)-1) (n+b-p) ((A [[(p : ℤ)+k]]) v)) =
      ∑ i ∈ Finset.range L, ((R A (R J B i) (n-1-i)) [[b]]) v := by
  let C (i : ℕ) := R J B i
  let d (i : ℕ) : ℤ := -(i : ℤ)-1
  let f (i h : ℕ) := (A [[n+d i-h]]) (((C i) [[b+h]]) v)
  let g (i h : ℕ) := ((C i) [[n+d i+b-h]]) ((A [[h]]) v)
  let F (p k i : ℕ) := ((Ring.choose (k : ℤ) i : ℤ) : ℂ) •
    (A [[n-1-p-k]]) (((C i) [[b+(p : ℤ)+k-i]]) v)
  let G (p k i : ℕ) := ((Ring.choose (-(k : ℤ)-1) i : ℤ) : ℂ) • g i (p+k)
  have fFinite (i : ℕ) : Function.HasFiniteSupport (f i) :=
    forward_finite A (C i) (n+d i) b v
  have gFinite (i : ℕ) : Function.HasFiniteSupport (g i) :=
    reverse_finite (C i) A (n+d i+b) v
  have FFinite (p i : ℕ) : Function.HasFiniteSupport (fun k => F p k i) := by
    have h := forward_finite A (C i) (n-1-p) (b+(p : ℤ)-i) v
    simpa only [F, Pi.smul_def', sub_add_eq_add_sub]
      using h.smul_right (fun k : ℕ => ((Ring.choose (k : ℤ) i : ℤ) : ℂ))
  have GFinite (p i : ℕ) : Function.HasFiniteSupport (fun k => G p k i) :=
    ((gFinite i).comp_of_injective
      (g := fun k : ℕ => p+k) (fun _ _ h => Nat.add_left_cancel h)).smul_right _
  have forwardRow (p k : ℕ) :
      (A [[n-1-p-k]]) (modeComm J B k (b+p) v) =
        ∑ i ∈ Finset.range L, F p k i := by
    rw [ordinary_commutator_newton J B L locality]
    simp only [F, C, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      show (k : ℤ)+(b+p) = b+p+k by omega]
  have reverseRow (p k : ℕ) :
      modeComm J B (-(k : ℤ)-1) (n+b-p) ((A [[(p : ℤ)+k]]) v) =
        ∑ i ∈ Finset.range L, G p k i := by
    rw [ordinary_commutator_newton J B L locality]
    simp only [G, g, d, C, LinearMap.sum_apply, LinearMap.smul_apply, Nat.cast_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [show -(k : ℤ)-1+(n+b-p)-i = n+(-(i : ℤ)-1)+b-((p : ℤ)+k) by omega]
  have FShift (p i : ℕ) : (∑ᶠ k : ℕ, F p k i) =
      ∑ᶠ k : ℕ, chooseSign (d i) k • f i (p+k) := by
    rw [finsum_skip (fun k => F p k i) i (by
      intro k hk; simp [F, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hk])]
    apply finsum_congr
    intro k
    simp only [F, f, d, weight_negative, Ring.choose_natCast, Int.cast_natCast, Nat.cast_add]
    rw [show n-1-(p : ℤ)-((i : ℤ)+k) = n+(-(i : ℤ)-1)-(p+k) by omega,
      show b+(p : ℤ)+((i : ℤ)+k)-i = b+(p+k) by omega]
  have GWeight (p k i : ℕ) : G p k i =
      (-epsilon (d i) * chooseSign (d i) k) • g i (p+k) := by
    dsimp only [G]
    rw [choose_negative_mode]
  have forwardFinite (i : ℕ) : Function.HasFiniteSupport (fun p : ℕ =>
      chooseSign n p • ∑ᶠ k : ℕ, chooseSign (d i) k • f i (p+k)) := by
    have h : Function.HasFiniteSupport (fun z : ℕ × ℕ =>
        chooseSign (d i) z.2 • f i (z.1+z.2)) := (diagonal_finite _ (fFinite i)).smul_right _
    exact (fiber_finite h).smul_right _
  have reverseFinite (i : ℕ) : Function.HasFiniteSupport (fun p : ℕ =>
      chooseSign n p • ∑ᶠ k : ℕ, G p k i) := by
    have h : Function.HasFiniteSupport (fun z : ℕ × ℕ => G z.1 z.2 i) := by
      simp_rw [GWeight]
      exact (diagonal_finite _ (gFinite i)).smul_right _
    exact (fiber_finite h).smul_right _
  have fs (p : ℕ) := finsum_sum_comm (Finset.range L) (F p) (fun i _ => FFinite p i)
  have gs (p : ℕ) := finsum_sum_comm (Finset.range L) (G p) (fun i _ => GFinite p i)
  simp_rw [forwardRow, reverseRow, fs, gs, Finset.smul_sum, FShift]
  rw [finsum_sum_comm (Finset.range L) _ (fun i _ => forwardFinite i),
    finsum_sum_comm (Finset.range L) _ (fun i _ => reverseFinite i),
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have forward : (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ,
      chooseSign (d i) k • f i (p+k)) =
        ∑ᶠ p : ℕ, chooseSign (n+d i) p • f i p := by
    refine Eq.trans (finsum_congr (fun p => ?_)) (convolution n (d i) _ (fFinite i))
    have h : Function.HasFiniteSupport (fun k : ℕ => chooseSign (d i) k • f i (p+k)) :=
      ((fFinite i).comp_of_injective (g := fun k : ℕ => p+k)
        (fun _ _ h => Nat.add_left_cancel h)).smul_right _
    rw [smul_finsum' _ h]
    simp only [smul_smul]
  have reverse : (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ, G p k i) =
      -epsilon (d i) • ∑ᶠ p : ℕ, chooseSign (n+d i) p • g i p := by
    have h (p : ℕ) : Function.HasFiniteSupport (fun k : ℕ =>
        (chooseSign n p * chooseSign (d i) k) • g i (p+k)) :=
      ((gFinite i).comp_of_injective
        (g := fun k : ℕ => p+k) (fun _ _ h => Nat.add_left_cancel h)).smul_right _
    calc
      _ = ∑ᶠ p : ℕ, -epsilon (d i) • ∑ᶠ k : ℕ,
          (chooseSign n p * chooseSign (d i) k) • g i (p+k) := by
        apply finsum_congr
        intro p
        rw [smul_finsum' _ (GFinite p i), smul_finsum' _ (h p)]
        apply finsum_congr
        intro k
        rw [GWeight]
        simp only [smul_smul]
        congr 1
        ring
      _ = _ := by
        have finite : Function.HasFiniteSupport (fun z : ℕ × ℕ =>
            (chooseSign n z.1 * chooseSign (d i) z.2) • g i (z.1+z.2)) :=
          (diagonal_finite _ (gFinite i)).smul_right _
        rw [← smul_finsum' _ (fiber_finite finite), convolution n (d i) _ (gFinite i)]
  rw [forward, reverse, smul_smul, mul_neg, neg_smul, ← sub_eq_add_neg,
    show epsilon n * epsilon (d i) = epsilon (n+d i) by
      unfold epsilon; rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)],
    show n-1-(i : ℤ) = n+d i by dsimp [d]; omega, ordinary_mode]

open private upper high pair_finite swap_finite from
  D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

private theorem ordinary_normal_mode (J A : VertexOperator ℂ V) (b : ℤ) (v : V) :
    ((R J A (-1)) [[b]]) v =
      (∑ᶠ k : ℕ, (J [[-(k : ℤ)-1]]) ((A [[b+k]]) v)) +
        (∑ᶠ k : ℕ, (A [[b-1-k]]) ((J [[k]]) v)) := by
  rw [ordinary_mode]
  have weight (k : ℕ) : chooseSign (-1) k = 1 := by simpa using weight_negative 0 k
  simp only [weight, one_smul, epsilon, zpow_neg, zpow_one, inv_neg, inv_one,
    neg_one_smul, sub_neg_eq_add,
    show ∀ k : ℕ, (-1 : ℤ)-k = -k-1 by intro k; omega,
    show ∀ k : ℕ, (-1 : ℤ)+b-k = b-1-k by intro k; omega]

private theorem mode_tail_finite (A : VertexOperator ℂ V) (n : ℤ) (v : V) :
    Function.HasFiniteSupport (fun k : ℕ => (A [[n+k]]) v) := by
  refine (Finset.range ((upper A v : ℤ)-n).toNat).finite_toSet.subset ?_
  intro k hk
  by_contra hn
  simp only [Finset.mem_coe, Finset.mem_range] at hn
  exact hk (high A v (n+k) (by omega))

private theorem minus_one_expansion (J A B : VertexOperator ℂ V) (n b : ℤ) (v : V) :
    ((R (R J A (-1)) B n) [[b]]) v =
      ((∑ᶠ k : ℕ, (J [[-(k : ℤ)-1]]) (residueDistribution 1 A B n k b v)) +
        (∑ᶠ k : ℕ, residueDistribution 1 A B n (-(k : ℤ)-1) b ((J [[k]]) v))) +
      ((∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ,
        (A [[n-1-p-k]]) (modeComm J B k (b+p) v)) +
        epsilon n • (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ,
          modeComm J B (-(k : ℤ)-1) (n+b-p) ((A [[(p : ℤ)+k]]) v))) := by
  let x (p k : ℕ) := (J [[-(k : ℤ)-1]]) ((A [[n-p+k]]) ((B [[b+p]]) v))
  let y (p k : ℕ) := (A [[n-1-p-k]]) ((J [[k]]) ((B [[b+p]]) v))
  let z (p k : ℕ) := (B [[n+b-p]]) ((J [[-(k : ℤ)-1]]) ((A [[(p : ℤ)+k]]) v))
  let t (p k : ℕ) := (B [[n+b-p]]) ((A [[(p : ℤ)-1-k]]) ((J [[k]]) v))
  let u (p k : ℕ) := (J [[-(k : ℤ)-1]]) ((B [[n+b-p]]) ((A [[(p : ℤ)+k]]) v))
  let w (p k : ℕ) := (A [[n-1-p-k]]) ((B [[b+p]]) ((J [[k]]) v))
  have hx : Function.HasFiniteSupport (Function.uncurry x) := by
    refine pair_finite x ((upper B v : ℤ)-b).toNat ?_ ?_
    · intro p hp k
      dsimp [x]
      rw [high B v (b+p) (by omega), map_zero, map_zero]
    · intro p
      simpa only [x, show ∀ k : ℕ, (-1 : ℤ)-k = -k-1 by intro k; omega]
        using forward_finite J A (-1) (n-p) ((B [[b+p]]) v)
  have hy : Function.HasFiniteSupport (Function.uncurry y) := by
    refine pair_finite y ((upper B v : ℤ)-b).toNat ?_ ?_
    · intro p hp k
      dsimp [y]
      rw [high B v (b+p) (by omega), map_zero, map_zero]
    · intro p
      exact reverse_finite A J (n-1-p) ((B [[b+p]]) v)
  have hz : Function.HasFiniteSupport (Function.uncurry z) := by
    refine pair_finite z (upper A v) ?_ ?_
    · intro p hp k
      dsimp [z]
      rw [high A v ((p : ℤ)+k) (by omega), map_zero, map_zero]
    · intro p
      simpa only [z, show ∀ k : ℕ, (-1 : ℤ)-k = -k-1 by intro k; omega]
        using (forward_finite J A (-1) p v).fun_comp (map_zero (B [[n+b-p]]))
  have ht : Function.HasFiniteSupport (Function.uncurry t) := by
    apply swap_finite (f := Function.uncurry (fun k p => t p k))
    refine pair_finite (fun k p => t p k) (upper J v) ?_ ?_
    · intro k hk p
      dsimp [t]
      rw [high J v k (by omega), map_zero, map_zero]
    · intro k
      refine (mode_tail_finite A (-1-k) ((J [[k]]) v)).subset ?_
      intro p hp
      contrapose! hp
      rw [Function.notMem_support] at hp
      rw [Function.notMem_support]
      simp [t, show (p : ℤ)-1-k = -1-k+p by omega, hp]
  have hu : Function.HasFiniteSupport (Function.uncurry u) := by
    refine pair_finite u (upper A v) ?_ ?_
    · intro p hp k
      dsimp [u]
      rw [high A v ((p : ℤ)+k) (by omega), map_zero, map_zero]
    · intro p
      refine (mode_tail_finite A p v).subset ?_
      intro k hk
      contrapose! hk
      rw [Function.notMem_support] at hk ⊢
      simp [u, hk]
  have hw : Function.HasFiniteSupport (Function.uncurry w) := by
    apply swap_finite (f := Function.uncurry (fun k p => w p k))
    refine pair_finite (fun k p => w p k) (upper J v) ?_ ?_
    · intro k hk p
      dsimp [w]
      rw [high J v k (by omega), map_zero, map_zero]
    · intro k
      simpa only [w, show ∀ p : ℕ, n-1-(k : ℤ)-p = n-1-p-k by intro p; omega]
        using forward_finite A B (n-1-k) b ((J [[k]]) v)
  let S (f : ℕ → ℕ → V) := ∑ᶠ q : ℕ × ℕ, chooseSign n q.1 • f q.1 q.2
  have weighted (f : ℕ → ℕ → V) (hf : Function.HasFiniteSupport (Function.uncurry f)) :
      Function.HasFiniteSupport (fun q : ℕ × ℕ => chooseSign n q.1 • f q.1 q.2) :=
    hf.smul_right _
  have rows (f : ℕ → ℕ → V) (hf : Function.HasFiniteSupport (Function.uncurry f)) :
      (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ, f p k) = S f := by
    dsimp only [S]
    rw [finsum_curry _ (weighted f hf)]
    apply finsum_congr
    intro p
    have row : Function.HasFiniteSupport (f p) :=
      hf.comp_of_injective (g := Prod.mk p) (fun _ _ h => congrArg Prod.snd h)
    rw [smul_finsum' _ row]
  have columns (f : ℕ → ℕ → V) (hf : Function.HasFiniteSupport (Function.uncurry f)) :
      (∑ᶠ k : ℕ, ∑ᶠ p : ℕ, chooseSign n p • f p k) = S f := by
    rw [← finsum_curry _ (swap_finite (weighted f hf))]
    exact finsum_comp_equiv (Equiv.prodComm ℕ ℕ)
      (f := fun q : ℕ × ℕ => chooseSign n q.1 • f q.1 q.2)
  have blockAdd (f g : ℕ → ℕ → V)
      (hf : Function.HasFiniteSupport (Function.uncurry f))
      (hg : Function.HasFiniteSupport (Function.uncurry g)) :
      S (fun p k => f p k + g p k) = S f + S g := by
    simp only [S, smul_add, ← finsum_add_distrib (weighted f hf) (weighted g hg)]
  have blockSub (f g : ℕ → ℕ → V)
      (hf : Function.HasFiniteSupport (Function.uncurry f))
      (hg : Function.HasFiniteSupport (Function.uncurry g)) :
      S (fun p k => f p k - g p k) = S f - S g := by
    simp only [S, smul_sub, ← finsum_sub_distrib (weighted f hf) (weighted g hg)]
  have hfAdd {f g : ℕ → ℕ → V}
      (hf : Function.HasFiniteSupport (Function.uncurry f))
      (hg : Function.HasFiniteSupport (Function.uncurry g)) :
      Function.HasFiniteSupport (Function.uncurry fun p k => f p k + g p k) := hf.add hg
  have hfSub {f g : ℕ → ℕ → V}
      (hf : Function.HasFiniteSupport (Function.uncurry f))
      (hg : Function.HasFiniteSupport (Function.uncurry g)) :
      Function.HasFiniteSupport (Function.uncurry fun p k => f p k - g p k) := hf.sub hg
  have normalLeft :
      ((R (R J A (-1)) B n) [[b]]) v = S x + S y - epsilon n • (S z + S t) := by
    rw [ordinary_mode]
    have forward (p : ℕ) : ((R J A (-1)) [[n-p]]) ((B [[b+p]]) v) =
        ∑ᶠ k : ℕ, (x p k + y p k) := by
      rw [ordinary_normal_mode]
      have xf : Function.HasFiniteSupport (x p) :=
        hx.comp_of_injective (g := Prod.mk p) (fun _ _ h => congrArg Prod.snd h)
      have yf : Function.HasFiniteSupport (y p) :=
        hy.comp_of_injective (g := Prod.mk p) (fun _ _ h => congrArg Prod.snd h)
      simpa only [y, show ∀ k : ℕ, n-(p : ℤ)-1-k = n-1-p-k by intro k; omega]
        using (finsum_add_distrib xf yf).symm
    have reverse (p : ℕ) : (B [[n+b-p]]) (((R J A (-1)) [[p]]) v) =
        ∑ᶠ k : ℕ, (z p k + t p k) := by
      rw [ordinary_normal_mode, map_add]
      have fn : Function.HasFiniteSupport
          (fun k : ℕ => (J [[-(k : ℤ)-1]]) ((A [[(p : ℤ)+k]]) v)) := by
        simpa only [show ∀ k : ℕ, (-1 : ℤ)-k = -k-1 by intro k; omega]
          using forward_finite J A (-1) p v
      rw [map_finsum _ fn, map_finsum _ (reverse_finite A J ((p : ℤ)-1) v)]
      have zf : Function.HasFiniteSupport (z p) :=
        hz.comp_of_injective (g := Prod.mk p) (fun _ _ h => congrArg Prod.snd h)
      have tf : Function.HasFiniteSupport (t p) :=
        ht.comp_of_injective (g := Prod.mk p) (fun _ _ h => congrArg Prod.snd h)
      exact finsum_add_distrib zf tf |>.symm
    simp_rw [forward, reverse]
    rw [rows _ (hfAdd hx hy), rows _ (hfAdd hz ht), blockAdd _ _ hx hy, blockAdd _ _ hz ht]
  have commForward :
      (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ,
        (A [[n-1-p-k]]) (modeComm J B k (b+p) v)) = S y - S w := by
    simp only [FieldNormalProductLocality.commutator, LinearMap.sub_apply,
      Module.End.mul_apply, map_sub]
    change (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ, (y p k - w p k)) = _
    rw [rows _ (hfSub hy hw), blockSub _ _ hy hw]
  have commReverse :
      (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ,
        modeComm J B (-(k : ℤ)-1) (n+b-p) ((A [[(p : ℤ)+k]]) v)) = S u - S z := by
    simp only [FieldNormalProductLocality.commutator, LinearMap.sub_apply, Module.End.mul_apply]
    change (∑ᶠ p : ℕ, chooseSign n p • ∑ᶠ k : ℕ, (u p k - z p k)) = _
    rw [rows _ (hfSub hu hz), blockSub _ _ hu hz]
  have Hneg :
      (∑ᶠ k : ℕ, (J [[-(k : ℤ)-1]]) (residueDistribution 1 A B n k b v)) =
        S x - epsilon n • S u := by
    have equ (k : ℕ) : (J [[-(k : ℤ)-1]]) (residueDistribution 1 A B n k b v) =
        (∑ᶠ p : ℕ, chooseSign n p • x p k) -
          epsilon n • ∑ᶠ p : ℕ, chooseSign n p • u p k := by
      rw [distribution_apply, mul_one, map_sub, map_smul]
      have f := (forward_finite A B ((k : ℤ)+n) b v).smul_right (chooseSign n)
      have g : Function.HasFiniteSupport (fun p : ℕ =>
          chooseSign n p • (B [[n+b-p]]) ((A [[(k : ℤ)+p]]) v)) := by
        refine (mode_tail_finite A k v).subset ?_
        intro p hp
        contrapose! hp
        rw [Function.notMem_support] at hp ⊢
        simp [hp]
      simp only [Pi.smul_def'] at f
      rw [map_finsum _ f, map_finsum _ g]
      simp only [x, u, map_smul,
        show ∀ p : ℕ, (k : ℤ)+n-p = n-p+k by intro p; omega,
        show ∀ p : ℕ, (k : ℤ)+p = p+k by intro p; omega]
    have fx := fiber_finite (swap_finite (weighted x hx))
    have fu := fiber_finite (swap_finite (weighted u hu))
    have fscaled : Function.HasFiniteSupport (fun k : ℕ =>
        epsilon n • ∑ᶠ p : ℕ, chooseSign n p • u p k) := fu.smul_right _
    simp_rw [equ]
    rw [finsum_sub_distrib fx fscaled, ← smul_finsum' _ fu, columns x hx, columns u hu]
  have Hpos :
      (∑ᶠ k : ℕ, residueDistribution 1 A B n (-(k : ℤ)-1) b ((J [[k]]) v)) =
        S w - epsilon n • S t := by
    have equ (k : ℕ) :
        residueDistribution 1 A B n (-(k : ℤ)-1) b ((J [[k]]) v) =
          (∑ᶠ p : ℕ, chooseSign n p • w p k) -
            epsilon n • ∑ᶠ p : ℕ, chooseSign n p • t p k := by
      simp only [distribution_apply, mul_one, w, t,
        show ∀ p : ℕ, -(k : ℤ)-1+n-p = n-1-p-k by intro p; omega,
        show ∀ p : ℕ, -(k : ℤ)-1+p = p-1-k by intro p; omega]
    have fw := fiber_finite (swap_finite (weighted w hw))
    have ft := fiber_finite (swap_finite (weighted t ht))
    have fscaled : Function.HasFiniteSupport (fun k : ℕ =>
        epsilon n • ∑ᶠ p : ℕ, chooseSign n p • t p k) := ft.smul_right _
    simp_rw [equ]
    rw [finsum_sub_distrib fw fscaled, ← smul_finsum' _ ft, columns w hw, columns t ht]
  rw [normalLeft, commForward, commReverse, Hneg, Hpos]
  module

/-- The ordinary local-field iterate with inner exponent `-1` and arbitrary
outer exponent. Both cutoffs come from uniform locality of the indicated pair. -/
theorem residue_iterate_minus_one (J A B : VertexOperator ℂ V) (K L : ℕ)
    (localityAB : delta^[K] (signedComm 1 A B) = 0)
    (localityJB : delta^[L] (signedComm 1 J B) = 0) (n : ℤ) :
    R (R J A (-1)) B n =
      (∑ i ∈ Finset.range ((K : ℤ)-n).toNat, R J (R A B (n+i)) (-(i : ℤ)-1)) +
      (∑ i ∈ Finset.range L, R A (R J B i) (n-1-i)) := by
  apply ext_modes
  intro b
  apply LinearMap.ext
  intro v
  rw [minus_one_expansion, normal_contraction J A B K localityAB,
    split_commutator_contraction J A B L localityJB]
  simp only [map_add, map_sum, Pi.add_apply, Finset.sum_apply,
    LinearMap.add_apply, LinearMap.sum_apply]

open FieldNormalProduct (dividedDerivative)
open SignedFieldNormalProductLocality (signedDerivative_locality)
open SignedFieldResidueLocality (negativeResidue)
open LatticeHalfFockGroundRightCurrentTransport.Calculus (R_nat)
open private R_smul R_zero from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

private theorem R_smul_first (A B : VertexOperator ℂ V) (r : ℤ) (c : ℂ) :
    R (c • A) B r = c • R A B r := by
  apply ext_modes
  intro b
  apply LinearMap.ext
  intro v
  rw [ordinary_mode, show ((c • R A B r) [[b]]) v = c • ((R A B r) [[b]]) v by
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply], ordinary_mode]
  have hf : Function.HasFiniteSupport (fun j : ℕ =>
      chooseSign r j • (A [[r-j]]) ((B [[b+j]]) v)) := (forward_finite A B r b v).smul_right _
  have hg : Function.HasFiniteSupport (fun j : ℕ =>
      chooseSign r j • (B [[r+b-j]]) ((A [[j]]) v)) := (reverse_finite B A (r+b) v).smul_right _
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
  simp_rw [smul_comm (chooseSign r _) c]
  rw [← smul_finsum' c hf, ← smul_finsum' c hg, smul_sub, smul_comm (epsilon r) c]

private theorem R_negative_normal (J A : VertexOperator ℂ V) (k : ℕ) :
    R J A (-(k : ℤ)-1) = R (dividedDerivative k J) A (-1) := by
  simp only [ordinary_residue]
  have h0 : dividedDerivative 0 (dividedDerivative k J) = dividedDerivative k J := by
    apply LinearMap.ext
    intro v
    simp [dividedDerivative]
  rw [negativeResidue 1 J A k]
  rw [show (-1 : ℤ) = -(0 : ℕ)-1 by norm_num, negativeResidue, h0]

private theorem derivative_comp (J : VertexOperator ℂ V) (k i : ℕ) :
    dividedDerivative i (dividedDerivative k J) =
      ((k+i).choose k : ℂ) • dividedDerivative (k+i) J := by
  apply LinearMap.ext
  intro v
  change HahnModule.of ℂ (LaurentSeries.hasseDeriv ℂ i
    ((HahnModule.of ℂ).symm (HahnModule.of ℂ (LaurentSeries.hasseDeriv ℂ k
      ((HahnModule.of ℂ).symm (J v)))))) = _
  rw [Equiv.symm_apply_apply, LaurentSeries.hasseDeriv_comp,
    ← Nat.cast_smul_eq_nsmul ℂ, HahnModule.of_smul,
    Nat.choose_symm_add (a := i) (b := k), Nat.add_comm i k]
  rfl

private theorem derivative_nat_mode (J : VertexOperator ℂ V) (k a : ℕ) :
    ((dividedDerivative k J) [[a]]) =
      ((-1 : ℂ)^k * (a.choose k : ℂ)) • (J [[(a : ℤ)-k]]) := by
  apply LinearMap.ext
  intro v
  change Ring.choose (-(a : ℤ)-1+k) k •
      HVertexOperator.coeff J (-(a : ℤ)-1+k) v = _
  rw [VertexOperator.coeff_eq_ncoeff, ← Int.cast_smul_eq_zsmul ℂ,
    show -(-(a : ℤ)-1+k)-1 = (a : ℤ)-k by omega,
    show -(a : ℤ)-1+k = -((a : ℤ)+1-k) by omega, Ring.choose_neg,
    show (a : ℤ)+1-k+k-1 = a by omega, Ring.choose_natCast]
  simp [Units.smul_def]

private theorem derivative_positive_residue (J B : VertexOperator ℂ V) (k r : ℕ) :
    R (dividedDerivative k J) B r =
      if k ≤ r then ((-1 : ℂ)^k * (r.choose k : ℂ)) • R J B ((r-k : ℕ) : ℤ) else 0 := by
  apply ext_modes
  intro b
  apply LinearMap.ext
  intro v
  let scalar (a : ℕ) : ℂ := (-1 : ℂ)^k * (a.choose k : ℂ)
  let s (p : ℕ) : V := (((-1 : ℂ)^p * (r.choose p : ℂ)) * scalar (r-p)) •
    modeComm J B ((r : ℤ)-p-k) (b+p) v
  have sumEq : ((R (dividedDerivative k J) B r) [[b]]) v =
      ∑ p ∈ Finset.range (r+1), s p := by
    rw [R_nat, FieldDeltaBinomial.delta_binomial, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro p hp
    have hpr : p ≤ r := by simpa using Finset.mem_range.mp hp
    rw [zero_add, ← Int.natCast_sub hpr]
    simp only [FieldNormalProductLocality.commutator, derivative_nat_mode, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.mul_apply, map_smul, smul_sub, smul_smul]
    simp only [s, scalar, FieldNormalProductLocality.commutator, Int.natCast_sub hpr,
      LinearMap.sub_apply, Module.End.mul_apply, mul_assoc, smul_sub]
  rw [sumEq]
  split_ifs with h
  · have restrict : (∑ p ∈ Finset.range (r+1), s p) =
        ∑ p ∈ Finset.range (r-k+1), s p := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro p hp hp'
      have less : r-p < k := by
        have := Finset.mem_range.mp hp
        have := Finset.mem_range.not.mp hp'
        omega
      simp [s, scalar, Nat.choose_eq_zero_of_lt less]
    rw [restrict, map_smul, Pi.smul_apply, LinearMap.smul_apply, R_nat,
      FieldDeltaBinomial.delta_binomial, LinearMap.sum_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpr : p ≤ r-k := by simpa using Finset.mem_range.mp hp
    have coeff : (r.choose p : ℂ) * ((r-p).choose k : ℂ) =
        (r.choose k : ℂ) * ((r-k).choose p : ℂ) := by
      have hh := Nat.choose_mul (n := r) (k := r-p) (s := k) (by omega)
      rw [Nat.choose_symm (by omega : p ≤ r), show r-p-k = r-k-p by omega,
        Nat.choose_symm (by omega : p ≤ r-k)] at hh
      exact_mod_cast hh
    simp only [s, scalar, LinearMap.smul_apply, smul_smul, zero_add,
      Int.natCast_sub h, show (r : ℤ)-k-p = r-p-k by omega]
    congr 1
    calc
      _ = (-1 : ℂ)^k * (-1 : ℂ)^p *
          ((r.choose p : ℂ) * ((r-p).choose k : ℂ)) := by ring
      _ = _ := by rw [coeff]; ring
  · rw [map_zero, Pi.zero_apply, LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro p _
    simp [s, scalar, Nat.choose_eq_zero_of_lt (show r-p < k by omega)]

/-- The ordinary local-field iterate for inner exponent `-k-1` and every
integer outer exponent. The two finite ranges use the original locality orders. -/
theorem residue_iterate_negative (J A B : VertexOperator ℂ V) (K L k : ℕ)
    (localityAB : delta^[K] (signedComm 1 A B) = 0)
    (localityJB : delta^[L] (signedComm 1 J B) = 0) (n : ℤ) :
    R (R J A (-(k : ℤ)-1)) B n =
      (∑ i ∈ Finset.range ((K : ℤ)-n).toNat,
        chooseSign (-(k : ℤ)-1) i • R J (R A B (n+i)) (-(k : ℤ)-1-i)) +
      (∑ i ∈ Finset.range L,
        ((-1 : ℂ)^k * chooseSign (-(k : ℤ)-1) i) •
          R A (R J B i) (n-(k : ℤ)-1-i)) := by
  rw [R_negative_normal, residue_iterate_minus_one _ _ _ K (L+k) localityAB
    (signedDerivative_locality 1 J B L k localityJB)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [R_negative_normal _ _ i, derivative_comp, R_smul_first, weight_negative,
      show -(k : ℤ)-1-i = -((k+i : ℕ) : ℤ)-1 by omega]
    rw [← R_negative_normal]
  · rw [Nat.add_comm L k, Finset.sum_range_add]
    have initial :
        (∑ i ∈ Finset.range k, R A (R (dividedDerivative k J) B i) (n-1-i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : ¬ k ≤ i := Nat.not_le.mpr (Finset.mem_range.mp hi)
      rw [derivative_positive_residue, ite_eq_right hi', R_zero]
    rw [initial, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [derivative_positive_residue, ite_eq_left (by omega : k ≤ k+i),
      show k+i-k = i by omega, R_smul, weight_negative, Nat.cast_add,
      show n-1-((k : ℤ)+i) = n-k-1-i by omega]

run_cmd do
  for name in [``residueDistribution_newton, ``ordinary_residue, ``normal_contraction,
      ``split_commutator_contraction, ``residue_iterate_minus_one, ``residue_iterate_negative] do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.contains ``propext &&
        axioms.contains ``Classical.choice && axioms.contains ``Quot.sound do
      throwError "Unexpected axiom closure for {name}: {axioms}"

#print axioms residueDistribution_newton
#print axioms ordinary_residue
#print axioms normal_contraction
#print axioms split_commutator_contraction
#print axioms residue_iterate_minus_one
#print axioms residue_iterate_negative

end
end D5.S3.VertexAlgebra.OrdinaryResidueIterate
