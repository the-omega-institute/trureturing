/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeResidueProduct
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cleared residues and inverse twisting in the integral residue coordinates. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality

/-!
The cleared residue and its inverse twist in Bakalov–Kac, arXiv:math/0402315v1,
equation (3.13). The strip and restore operations use Laurent exponent residues.
-/

set_option autoImplicit false

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueProduct

open P48qNativeCurrentLocality (Field InResidue stripResidue restoreResidue coverDelta coverComm
  coverDelta_comm_eq_zero_iff nativeField_inResidue)
open P48qNativePairwiseLocality (nativeField_pairwise_locality)
open P48qAllJetWickField (NativeStates nativeField)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open NativeStandardThirdLift (standardLift)
open private ordinary_residue_mode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality

noncomputable section

/-- Finite convolution towards an exclusive upper cutoff in the product label. -/
def binomialTail {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (a : ℂ) (N : ℤ) (F : ℤ → M) (n : ℤ) : M :=
  ∑ j ∈ Finset.range (N - n).toNat, Ring.choose a j • F (n + j)

theorem binomialTail_add {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (a b : ℂ) (N : ℤ) (F : ℤ → M) (n : ℤ) :
    binomialTail a N (binomialTail b N F) n = binomialTail (a + b) N F n := by
  let L := (N - n).toNat
  let f (i k : ℕ) := (Ring.choose a i * Ring.choose b (k - i)) • F (n + k)
  unfold binomialTail
  change (∑ i ∈ Finset.range L, Ring.choose a i •
    ∑ j ∈ Finset.range (N - (n + (i : ℤ))).toNat,
      Ring.choose b j • F (n + (i : ℤ) + j)) = _
  calc
    _ = ∑ i ∈ Finset.Ico 0 L, ∑ k ∈ Finset.Ico i L, f i k := by
      rw [Nat.Ico_zero_eq_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [Finset.sum_Ico_eq_sum_range, Finset.smul_sum,
        show (N - (n + (i : ℤ))).toNat = L - i by dsimp [L] at *; omega]
      apply Finset.sum_congr rfl
      intro j _
      simp [f, smul_smul, add_assoc, add_comm i j, add_comm (i : ℤ) (j : ℤ)]
    _ = ∑ k ∈ Finset.Ico 0 L, ∑ i ∈ Finset.Ico 0 (k + 1), f i k :=
      Finset.sum_Ico_Ico_comm 0 L f
    _ = _ := by
      simp only [Nat.Ico_zero_eq_range]
      apply Finset.sum_congr rfl
      intro k _
      rw [Ring.add_choose_eq k (Commute.all a b), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_smul]

theorem binomialTail_inverse {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (a : ℂ) (N : ℤ) (F : ℤ → M) (hF : ∀ n ≥ N, F n = 0) :
    binomialTail (-a) N (binomialTail a N F) = F := by
  funext n
  rw [binomialTail_add, neg_add_cancel]
  by_cases hn : n < N
  · unfold binomialTail
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      cases j with
      | zero => contradiction
      | succ j => simp [Ring.choose_zero_succ]
    · simp [Finset.mem_range, show 0 < (N - n).toNat by omega]
  · simp [binomialTail, show (N - n).toNat = 0 by omega, hF n (by omega)]

/-- The ordinary residue after clearing the first field's fractional exponent,
with the output monomial restored in the second coordinate. -/
def clearedResidue (s t : ℤ) (A B : Field) (n : ℤ) : Field :=
  restoreResidue (s + t)
    (SignedFieldResidueLocality.residueField 1 n (stripResidue s A) (stripResidue t B)).operator

theorem clearedResidue_zero_of_locality (s t : ℤ) (A B : Field)
    (hA : InResidue s A) (hB : InResidue t B) (N : ℕ)
    (hlocal : coverDelta^[N] (coverComm A B) = 0) (n : ℤ) (hn : (N : ℤ) ≤ n) :
    clearedResidue s t A B n = 0 := by
  have hp : FieldNormalProductLocality.delta^[N]
      (FieldNormalProductLocality.commutator (stripResidue s A) (stripResidue t B)) = 0 :=
    (coverDelta_comm_eq_zero_iff s t A B hA hB N).mp hlocal
  have hq : FieldNormalProductLocality.delta^[n.toNat]
      (FieldNormalProductLocality.commutator (stripResidue s A) (stripResidue t B)) = 0 := by
    rw [show n.toNat = (n.toNat - N) + N by omega, Function.iterate_add_apply, hp]
    generalize n.toNat - N = d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [Function.iterate_succ_apply', ih]
      exact funext fun i => funext fun j => sub_self _
  apply HVertexOperator.coeff_inj
  funext k
  rw [clearedResidue, P48qNativeCurrentLocality.restoreResidue_coeff]
  split
  · rw [VertexOperator.coeff_eq_ncoeff, ← Int.toNat_of_nonneg (show 0 ≤ n by omega),
      ordinary_residue_mode, hq]
    rfl
  · rfl

/-- Inverse of BK (3.13). Each shifted integral residue is restored with the
monomial `y^(s+t-3*j)` on the cover. -/
def adjustedResidue (s t : ℤ) (A B : Field) (N : ℕ) (n : ℤ) : Field :=
  ∑ j ∈ Finset.range ((N : ℤ) - n).toNat,
    Ring.choose ((s : ℂ) / 3) j • restoreResidue (s + t - 3 * (j : ℤ))
      (SignedFieldResidueLocality.residueField 1 (n + j)
        (stripResidue s A) (stripResidue t B)).operator

/-- The shift by `3*n` keeps the coefficient index fixed under the convolution. -/
theorem adjustedResidue_coeff (s t : ℤ) (A B : Field) (N : ℕ) (n k : ℤ) :
    HVertexOperator.coeff (adjustedResidue s t A B N n) (k + 3 * n) =
      binomialTail ((s : ℂ) / 3) N
        (fun p => HVertexOperator.coeff (clearedResidue s t A B p) (k + 3 * p)) n := by
  unfold adjustedResidue binomialTail
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [clearedResidue, P48qNativeCurrentLocality.restoreResidue_coeff,
    P48qNativeCurrentLocality.restoreResidue_coeff]
  congr 1
  rw [show (k + 3 * n) % 3 = (k + 3 * (n + (j : ℤ))) % 3 by omega,
    show (s + t - 3 * (j : ℤ)) % 3 = (s + t) % 3 by omega,
    show k + 3 * n - (s + t - 3 * (j : ℤ)) =
      k + 3 * (n + (j : ℤ)) - (s + t) by ring]

/-- Any larger valid cutoff yields the same adjusted product. -/
theorem adjustedResidue_cutoff_mono (s t : ℤ) (A B : Field) (N M : ℕ) (hNM : N ≤ M)
    (hR : ∀ n ≥ (N : ℤ), clearedResidue s t A B n = 0) (n : ℤ) :
    adjustedResidue s t A B N n = adjustedResidue s t A B M n := by
  apply HVertexOperator.coeff_inj
  funext l
  have h : l = (l - 3 * n) + 3 * n := by ring
  conv_lhs => rw [h, adjustedResidue_coeff]
  conv_rhs => rw [h, adjustedResidue_coeff]
  unfold binomialTail
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  simp [hR (n + j) (by omega)]

open BinomialKernelDelta (chooseSign chooseSign_pascal finsum_split)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (epsilon)
open P48qNativeCurrentLocality (stripResidue_coeff restoreResidue_coeff)
open P48qThirdTwistedField (State)

private theorem signedPascal {V : Type*} [AddCommGroup V] [Module ℂ V]
    (r : ℤ) (f : ℕ → V)
    (hf : Function.HasFiniteSupport f) :
    (∑ᶠ j : ℕ, chooseSign (r + 1) j • f j) =
      (∑ᶠ j : ℕ, chooseSign r j • f j) - ∑ᶠ j : ℕ, chooseSign r j • f (j + 1) := by
  have ht := hf.fun_comp_of_injective (g := fun j : ℕ => j + 1)
    (fun _ _ h => Nat.add_right_cancel h)
  rw [finsum_split (fun j => chooseSign (r + 1) j • f j) (hf.smul_right (chooseSign (r + 1))),
    finsum_split (fun j => chooseSign r j • f j) (hf.smul_right (chooseSign r))]
  simp only [BinomialKernelDelta.chooseSign_zero, one_smul, chooseSign_pascal, sub_smul]
  have h₁ : Function.HasFiniteSupport (fun j => chooseSign r (j + 1) • f (j + 1)) :=
    ht.smul_right (fun j => chooseSign r (j + 1))
  have h₂ : Function.HasFiniteSupport (fun j => chooseSign r j • f (j + 1)) :=
    ht.smul_right (chooseSign r)
  rw [finsum_sub_distrib h₁ h₂]
  abel

private theorem modeSupport {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : VertexOperator ℂ V) (w : V) (p : ℤ) :
    Function.HasFiniteSupport (fun j : ℕ => (A[[p + j]]) w) := by
  refine BddAbove.finite (bddAbove_def.mpr ⟨(-((HahnModule.of ℂ).symm (A w)).order - p).toNat,
    fun j hj => le_of_not_gt (fun h => hj ?_)⟩)
  exact VertexOperator.ncoeff_eq_zero_of_lt_order A _ w (by omega)

private theorem stripMode_step (s : ℤ) (A : Field) (q : ℤ) :
    (stripResidue s A)[[q]] = (stripResidue (s + 3) A)[[q + 1]] := by
  simp only [VertexOperator.ncoeff_apply, stripResidue_coeff]
  rw [show 3 * (-(q + 1) - 1) + (s + 3) = 3 * (-q - 1) + s by omega]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- Elaborating the coefficient identities unfolds the residue constructor.
/-- Moving one integral power from the first strip into its field multiplies
the residue kernel by `z = w + (z - w)`. -/
private theorem residueLeft_mode_step {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A C D : VertexOperator ℂ V) (hmode : ∀ i, A[[i]] = C[[i + 1]]) (r q : ℤ) :
    ((residueField 1 r A D).operator)[[q]] =
      ((residueField 1 r C D).operator)[[q + 1]] +
      ((residueField 1 (r + 1) C D).operator)[[q]] := by
  apply LinearMap.ext
  intro w
  let f (j : ℕ) := (C[[r + 1 - j]]) ((D[[q + j]]) w)
  let g (j : ℕ) := (D[[r + q + 1 - j]]) ((C[[j]]) w)
  have hf : Function.HasFiniteSupport f :=
    (modeSupport D w q).subset (fun j hj hz => hj (by simp [f, hz]))
  have hg : Function.HasFiniteSupport g := by
    refine (modeSupport C w 0).subset (fun j hj hz => hj ?_)
    change (C[[0 + (j : ℤ)]]) w = 0 at hz
    simp only [zero_add] at hz
    simp [g, hz]
  rw [LinearMap.add_apply, (residueField 1 r A D).coefficient,
    (residueField 1 r C D).coefficient, (residueField 1 (r + 1) C D).coefficient]
  simp only [residueCoefficient, mul_one]
  have hl : residueLeft r q A D w =
      ∑ᶠ j : ℕ, chooseSign r j • f j := by
    unfold residueLeft
    apply finsum_congr
    intro j
    rw [hmode (r - j)]
    simp only [f, chooseSign, StateFieldResidueReconstruction.integerBinomial]
    rw [show r - (j : ℤ) + 1 = r + 1 - j by omega]
  have hl' : residueLeft r (q + 1) C D w =
      ∑ᶠ j : ℕ, chooseSign r j • f (j + 1) := by
    unfold residueLeft
    apply finsum_congr
    intro j
    simp only [f, chooseSign, StateFieldResidueReconstruction.integerBinomial, Nat.cast_add,
      Nat.cast_one]
    rw [show r + 1 - ((j : ℤ) + 1) = r - j by omega,
      show q + ((j : ℤ) + 1) = q + 1 + j by omega]
  have hr : residueRight r q A D w =
      ∑ᶠ j : ℕ, chooseSign r j • g (j + 1) := by
    unfold residueRight
    apply finsum_congr
    intro j
    rw [hmode j]
    simp only [g, chooseSign, StateFieldResidueReconstruction.integerBinomial,
      Nat.cast_add, Nat.cast_one]
    rw [show r + q + 1 - ((j : ℤ) + 1) = r + q - j by omega]
  have hr' : residueRight r (q + 1) C D w =
      ∑ᶠ j : ℕ, chooseSign r j • g j := by
    unfold residueRight
    apply finsum_congr
    intro j
    simp only [g, chooseSign, StateFieldResidueReconstruction.integerBinomial]
    rw [show r + (q + 1) = r + q + 1 by omega]
  change residueLeft r q A D w -
      epsilon r • residueRight r q A D w =
    (residueLeft r (q + 1) C D w - epsilon r • residueRight r (q + 1) C D w) +
      (residueLeft (r + 1) q C D w - epsilon (r + 1) • residueRight (r + 1) q C D w)
  have hsign : epsilon (r + 1) = -epsilon r := by
    simp [epsilon, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hg' : residueRight (r + 1) q C D w = ∑ᶠ j : ℕ, chooseSign (r + 1) j • g j := by
    simp only [residueRight, g, chooseSign, StateFieldResidueReconstruction.integerBinomial]
    rw [show r + 1 + q = r + q + 1 by omega]
  rw [hl, hl', hr, hr', hsign, hg']
  change _ = _ + ((∑ᶠ j : ℕ, chooseSign (r + 1) j • f j) -
    (-epsilon r) • (∑ᶠ j : ℕ, chooseSign (r + 1) j • g j))
  rw [signedPascal r f hf, signedPascal r g hg, neg_smul, smul_sub]
  abel

private theorem binomialTail_one {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (N : ℤ) (F : ℤ → M) (hF : ∀ n ≥ N, F n = 0) (n : ℤ) :
    binomialTail 1 N F n = F n + F (n + 1) := by
  unfold binomialTail
  rcases lt_trichotomy (n + 1) N with h | h | h
  · rw [show (N - n).toNat = 2 + ((N - n).toNat - 2) by omega, Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range ((N - n).toNat - 2),
        Ring.choose (1 : ℂ) (2 + j) • F (n + ((2 + j : ℕ) : ℤ))) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [← Nat.cast_one (R := ℂ)]
        rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : 1 < 2 + j)]
        simp
    rw [hz, add_zero]
    simp [Finset.sum_range_succ]
  · simp [show (N - n).toNat = 1 by omega, hF (n + 1) (by omega)]
  · simp [show (N - n).toNat = 0 by omega, hF n (by omega), hF (n + 1) (by omega)]

/-- The adjusted product is invariant under increasing the first strip
representative by three, with the same uniform locality cutoff. -/
theorem adjustedResidue_strip_left_add_three (s t : ℤ) (A B : Field)
    (hA : InResidue s A) (hB : InResidue t B) (N : ℕ)
    (hlocal : coverDelta^[N] (coverComm A B) = 0) (n : ℤ) :
    adjustedResidue (s + 3) t A B N n = adjustedResidue s t A B N n := by
  apply HVertexOperator.coeff_inj
  funext l
  let k := l - 3 * n
  have hk : k + 3 * n = l := by dsimp [k]; ring
  rw [← hk, adjustedResidue_coeff, adjustedResidue_coeff]
  let F (p : ℤ) := HVertexOperator.coeff (clearedResidue (s + 3) t A B p) (k + 3 * p)
  have hA' : InResidue (s + 3) A := by
    intro i hi
    exact hA i (by simpa only [show (s + 3) % 3 = s % 3 by omega] using hi)
  have hF (p : ℤ) (hp : (N : ℤ) ≤ p) : F p = 0 := by
    simp [F, clearedResidue_zero_of_locality _ _ _ _ hA' hB N hlocal p hp]
  have hstep (p : ℤ) :
      HVertexOperator.coeff (clearedResidue s t A B p) (k + 3 * p) =
        F p + F (p + 1) := by
    simp only [F, clearedResidue, restoreResidue_coeff]
    have hcond (q : ℤ) : (k + 3 * q) % 3 = k % 3 := by omega
    simp only [hcond, show (s + 3 + t) % 3 = (s + t) % 3 by omega]
    split_ifs
    · simp only [VertexOperator.coeff_eq_ncoeff]
      rw [show -((k + 3 * p - (s + 3 + t)) / 3) - 1 =
          (-((k + 3 * p - (s + t)) / 3) - 1) + 1 by omega,
        show -((k + 3 * (p + 1) - (s + 3 + t)) / 3) - 1 =
          -((k + 3 * p - (s + t)) / 3) - 1 by omega]
      exact residueLeft_mode_step _ _ _ (stripMode_step s A) p _
    · rw [add_zero]
  change binomialTail (((s + 3 : ℤ) : ℂ) / 3) N F n = _
  simp_rw [hstep, ← binomialTail_one N F hF]
  rw [binomialTail_add]
  congr 2
  push_cast
  ring

private theorem residueRight_mode_step {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : VertexOperator ℂ V) (hmode : ∀ i, B[[i]] = C[[i + 1]]) (p q : ℤ) :
    ((residueField 1 p A C).operator)[[q + 1]] = ((residueField 1 p A B).operator)[[q]] := by
  apply LinearMap.ext
  intro w
  rw [(residueField 1 p A C).coefficient, (residueField 1 p A B).coefficient]
  simp only [residueCoefficient]
  apply congrArg₂ (· - ·)
  · unfold residueLeft
    apply finsum_congr
    intro j
    rw [show q + 1 + (j : ℤ) = q + j + 1 by omega, ← hmode (q + j)]
  · congr 1
    unfold residueRight
    apply finsum_congr
    intro j
    rw [show p + (q + 1) - (j : ℤ) = p + q - j + 1 by omega, ← hmode (p + q - j)]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The second strip shift cancels directly against the restoring monomial. -/
theorem adjustedResidue_strip_right_add_three (s t : ℤ) (A B : Field) (N : ℕ) (n : ℤ) :
    adjustedResidue s (t + 3) A B N n = adjustedResidue s t A B N n := by
  have he (p : ℤ) : clearedResidue s (t + 3) A B p = clearedResidue s t A B p := by
    apply HVertexOperator.coeff_inj
    funext l
    simp only [clearedResidue, restoreResidue_coeff,
      show (s + (t + 3)) % 3 = (s + t) % 3 by omega]
    split_ifs <;> try rfl
    simp only [VertexOperator.coeff_eq_ncoeff]
    let q := -((l - (s + t)) / 3) - 1
    rw [show -((l - (s + (t + 3))) / 3) - 1 = q + 1 by dsimp [q]; omega]
    exact residueRight_mode_step _ _ _ (stripMode_step t B) p q
  apply HVertexOperator.coeff_inj
  funext l
  let k := l - 3 * n
  have hk : k + 3 * n = l := by dsimp [k]; ring
  have hs :
    (fun p => HVertexOperator.coeff (clearedResidue s (t + 3) A B p) (k + 3 * p)) =
      fun p => HVertexOperator.coeff (clearedResidue s t A B p) (k + 3 * p) := by
    funext p
    rw [he p]
  rw [← hk, adjustedResidue_coeff, adjustedResidue_coeff, hs]

/-- At every integer product label, equality with the inverse-twisted field
is equivalent to the forward BK formula on the cleared residues. -/
theorem adjustedResidue_eq_iff (s t : ℤ) (A B : Field) (N : ℕ)
    (F : ℤ → Field) (hF : ∀ n ≥ (N : ℤ), F n = 0)
    (hR : ∀ n ≥ (N : ℤ), clearedResidue s t A B n = 0) :
    (∀ n, adjustedResidue s t A B N n = F n) ↔
      ∀ n k, HVertexOperator.coeff (clearedResidue s t A B n) (k + 3 * n) =
        binomialTail (-(s : ℂ) / 3) N
          (fun p => HVertexOperator.coeff (F p) (k + 3 * p)) n := by
  have hs : -(s : ℂ) / 3 = -((s : ℂ) / 3) := neg_div _ _
  rw [hs]
  constructor
  · intro h n k
    have he : (fun p => HVertexOperator.coeff (F p) (k + 3 * p)) =
        binomialTail ((s : ℂ) / 3) N
          (fun p => HVertexOperator.coeff (clearedResidue s t A B p) (k + 3 * p)) := by
      funext p
      rw [← h p, adjustedResidue_coeff]
    rw [he, binomialTail_inverse]
    intro p hp
    simp [hR p hp]
  · intro h n
    apply HVertexOperator.coeff_inj
    funext l
    let k := l - 3 * n
    have hk : k + 3 * n = l := by dsimp [k]; ring
    rw [← hk, adjustedResidue_coeff]
    have he : (fun p => HVertexOperator.coeff (clearedResidue s t A B p) (k + 3 * p)) =
        binomialTail (-((s : ℂ) / 3)) N
          (fun p => HVertexOperator.coeff (F p) (k + 3 * p)) := funext (fun p => h p k)
    rw [he]
    have hi := binomialTail_inverse (-((s : ℂ) / 3)) N
      (fun p => HVertexOperator.coeff (F p) (k + 3 * p))
      (fun p hp => by simp [hF p hp])
    simpa only [neg_neg] using congrFun hi n

/-- Every pair of actual native eigenfields admits the same finite cutoff
for every coefficient of its cleared ordinary residue. -/
theorem native_clearedResidue_cutoff (v w : NativeStates) (s t : ℤ)
    (hv : standardLift lattice g g_cube g_isometry v =
      (ThirdTwistedChargeCocycle.zeta : ℂ) ^ s • v)
    (hw : standardLift lattice g g_cube g_isometry w =
      (ThirdTwistedChargeCocycle.zeta : ℂ) ^ t • w) :
    ∃ N : ℕ, ∀ n ≥ (N : ℤ), clearedResidue s t (nativeField v) (nativeField w) n = 0 := by
  obtain ⟨N, hN⟩ := nativeField_pairwise_locality v w
  exact ⟨N, fun n hn => clearedResidue_zero_of_locality s t _ _
    (nativeField_inResidue v s hv) (nativeField_inResidue w t hw) N hN n hn⟩

open P48qThirdTwistedField (Cartan State)
open P48qTwistedHeisenberg (currentField)
open ThirdEigenspacePairing (p48qAction)
open ThirdTwistedIterate (currentAlong)
open LatticeAllStateReconstruction (mu)
open LatticeSugawaraCurrents (vectorFrequencyBound)
open private alignedComm alignedComm_differences delta_alignedComm difference sourceModeCoeff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
open private source_zero_above from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeNegativeCurrentIterate

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem current_cleared_nonneg (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v : NativeStates)
    (t : ℤ) (hv : InResidue t (nativeField v)) (q : ℕ) (k : ℤ) :
    HVertexOperator.coeff (clearedResidue (-(r : ℤ)) t (currentField u) (nativeField v) q)
        (k + 3 * (q : ℤ)) =
      binomialTail ((r : ℂ) / 3) (vectorFrequencyBound lattice v + 1 : ℕ)
        (fun n => HVertexOperator.coeff
          (nativeField (mu lattice (currentAlong lattice u) n v)) (k + 3 * n)) q := by
  let N := vectorFrequencyBound lattice v + 1
  have hdiff :
      HVertexOperator.coeff (clearedResidue (-(r : ℤ)) t (currentField u) (nativeField v) q)
          (k + 3 * (q : ℤ)) = difference^[q] (alignedComm u r v k) 0 := by
    rw [clearedResidue, P48qNativeCurrentLocality.restoreResidue_coeff]
    split
    · rename_i hk
      rw [VertexOperator.coeff_eq_ncoeff, ordinary_residue_mode, delta_alignedComm]
      apply congrArg (fun l => difference^[q] (alignedComm u r v l) 0)
      have hd := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hk
      omega
    · rename_i hk
      have hz : alignedComm u r v k = 0 := by
        funext i
        rw [alignedComm, hv _ (by omega), LieRing.of_associative_ring_bracket]
        simp
      rw [hz]
      have hz' (m : ℕ) : difference^[m] (0 : ℤ → Module.End ℂ State) = 0 := by
        induction m with
        | zero => rfl
        | succ q ih =>
          rw [Function.iterate_succ_apply', ih]
          exact funext fun i => sub_self _
      rw [hz']
      rfl
  rw [hdiff, alignedComm_differences u r hr hu]
  simp only [Int.cast_zero, zero_add, ite_smul, zero_smul]
  rw [← Finset.sum_filter]
  have hIco : (Finset.range N).filter (q ≤ ·) = Finset.Ico q N := by
    ext j
    simp [and_comm]
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  unfold binomialTail
  rw [show ((N : ℤ) - (q : ℤ)).toNat = N - q by omega]
  apply Finset.sum_congr rfl
  intro j _
  simp [sourceModeCoeff, add_comm q j, add_comm (q : ℤ) (j : ℤ)]

/-- At every nonnegative source label the inverse residue recovers the
actual current-first iterate, with the source truncation as cutoff. -/
theorem adjustedResidue_native_current_nonneg (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v : NativeStates)
    (t : ℤ) (hv : InResidue t (nativeField v)) (q : ℕ) :
    adjustedResidue (-(r : ℤ)) t (nativeField (currentAlong lattice u)) (nativeField v)
        (vectorFrequencyBound lattice v + 1) q =
      nativeField (mu lattice (currentAlong lattice u) q v) := by
  rw [P48qNativeMonodromy.nativeField_current]
  apply HVertexOperator.coeff_inj
  funext l
  let k := l - 3 * (q : ℤ)
  let N := vectorFrequencyBound lattice v + 1
  let F (n : ℤ) :=
    HVertexOperator.coeff (nativeField (mu lattice (currentAlong lattice u) n v)) (k + 3 * n)
  have hk : k + 3 * (q : ℤ) = l := by dsimp [k]; ring
  rw [← hk, adjustedResidue_coeff, Int.cast_neg, Int.cast_natCast, neg_div]
  have hcut : ∀ n ≥ (N : ℤ), F n = 0 := by
    intro n hn
    have hn' : n = (n.toNat : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    have hm : mu lattice (currentAlong lattice u) n v = 0 := by
      rw [hn']
      exact source_zero_above u v n.toNat (by dsimp [N] at hn; omega)
    simp [F, hm]
  have hi := congrFun (binomialTail_inverse ((r : ℂ) / 3) N F hcut) (q : ℤ)
  refine Eq.trans ?_ hi
  unfold binomialTail
  apply Finset.sum_congr rfl
  intro j _
  rw [← Int.natCast_add]
  exact congrArg (Ring.choose (-((r : ℂ) / 3)) j • ·)
    (current_cleared_nonneg u r hr hu v t hv (q + j) k)

open FieldNormalProduct (dividedDerivative normalMinusOne)
open P48qNativeNegativeCurrentIterate (regularGermCoeff regularCollision signedNormalTaylor
  nativeField_current_negative_iterate)
open private regularGermCoeff_sum source_sum_cutoff sourceCoeff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeNegativeCurrentIterate
open private normalPartField signedNormalTaylor_eq from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality

private theorem ordinaryResidue_neg (A B : Field) (h : ℕ) :
    (SignedFieldResidueLocality.residueField 1 (-(h : ℤ) - 1) A B).operator =
      (normalMinusOne (dividedDerivative h A) B).val := by
  rw [SignedFieldResidueLocality.negativeResidue]
  apply HVertexOperator.coeff_inj
  funext k
  apply LinearMap.ext
  intro w
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    (SignedFieldNormalProductLocality.signedNormalMinusOne 1 (dividedDerivative h A) B).property,
    (normalMinusOne (dividedDerivative h A) B).property, one_smul]

private theorem binomialTail_regular {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (a : ℂ) (d N : ℕ) (F : ℤ → M) :
    (∑ j ∈ Finset.range N, Ring.choose (-a) (d + j) • binomialTail a (N : ℤ) F j) =
      ∑ n ∈ Finset.range N, regularGermCoeff a d n • F n := by
  let f (j n : ℕ) := (Ring.choose (-a) (d + j) * Ring.choose a (n - j)) • F n
  calc
    _ = ∑ j ∈ Finset.Ico 0 N, ∑ n ∈ Finset.Ico j N, f j n := by
      rw [Nat.Ico_zero_eq_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_Ico_eq_sum_range, binomialTail, Finset.smul_sum,
        show ((N : ℤ) - (j : ℤ)).toNat = N - j by omega]
      apply Finset.sum_congr rfl
      intro i _
      simp [f, smul_smul, add_comm j i, add_comm (j : ℤ) (i : ℤ)]
    _ = ∑ n ∈ Finset.Ico 0 N, ∑ j ∈ Finset.Ico 0 (n + 1), f j n :=
      Finset.sum_Ico_Ico_comm 0 N f
    _ = _ := by
      simp only [Nat.Ico_zero_eq_range, regularGermCoeff_sum, Finset.sum_smul]
      rfl

private theorem adjustedResidue_native_current_neg (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v : NativeStates)
    (t : ℤ) (hv : InResidue t (nativeField v)) (d : ℕ+) :
    adjustedResidue (-(r : ℤ)) t (nativeField (currentAlong lattice u)) (nativeField v)
        (vectorFrequencyBound lattice v + 1) (-((d : ℕ) : ℤ)) =
      nativeField (mu lattice (currentAlong lattice u) (-((d : ℕ) : ℤ)) v) := by
  let N := vectorFrequencyBound lattice v + 1
  let a : ℂ := (r : ℂ) / 3
  let D := (d : ℕ)
  let A := stripResidue (-(r : ℤ)) (currentField u)
  let B := stripResidue t (nativeField v)
  let R (j : ℕ) : Field := Ring.choose (-a) j • restoreResidue (t - r - 3 * (j : ℤ))
    (SignedFieldResidueLocality.residueField 1 (-(D : ℤ) + j) A B).operator
  have hsplit :
      adjustedResidue (-(r : ℤ)) t (nativeField (currentAlong lattice u)) (nativeField v)
          N (-(D : ℤ)) = (∑ j ∈ Finset.range D, R j) + ∑ j ∈ Finset.range N, R (D + j) := by
    rw [P48qNativeMonodromy.nativeField_current, adjustedResidue,
      show ((N : ℤ) - -(D : ℤ)).toNat = D + N by omega, Finset.sum_range_add]
    simp only [R, A, B, a, Int.cast_neg, Int.cast_natCast, neg_div, sub_eq_add_neg, add_comm t]
  have hnormal : (∑ j ∈ Finset.range D, R j) = normalPartField u r d v t := by
    unfold normalPartField
    rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      show (D - 1).succ = D by have := d.pos; omega]
    apply Finset.sum_congr rfl
    intro j hj
    have hl := Finset.mem_range.mp hj
    dsimp only [R]
    rw [show -(D : ℤ) + (j : ℤ) = -((D - 1 - j : ℕ) : ℤ) - 1 by omega,
      ordinaryResidue_neg]
    simp only [a, A, B, D, neg_div, Prod.swap]
  rw [hsplit, hnormal]
  apply HVertexOperator.coeff_inj
  funext l
  have hterms (j : ℕ) : HVertexOperator.coeff (R (D + j)) l =
      Ring.choose (-a) (D + j) •
        HVertexOperator.coeff
          (clearedResidue (-(r : ℤ)) t (currentField u) (nativeField v) j)
          (l + 3 * (D : ℤ) + 3 * (j : ℤ)) := by
    dsimp only [R]
    rw [map_smul, Pi.smul_apply, clearedResidue,
      P48qNativeCurrentLocality.restoreResidue_coeff,
      P48qNativeCurrentLocality.restoreResidue_coeff,
      show -(D : ℤ) + ((D + j : ℕ) : ℤ) = j by push_cast; ring]
    congr 1
    rw [show (l + 3 * (D : ℤ) + 3 * (j : ℤ)) % 3 = l % 3 by omega,
      show (t - r - 3 * ((D + j : ℕ) : ℤ)) % 3 = (-(r : ℤ) + t) % 3 by omega,
      show l - (t - r - 3 * ((D + j : ℕ) : ℤ)) =
        l + 3 * (D : ℤ) + 3 * (j : ℤ) - (-(r : ℤ) + t) by push_cast; ring]
  have hcollision :
      HVertexOperator.coeff (∑ j ∈ Finset.range N, R (D + j)) l =
        regularCollision u r d v l := by
    simp only [map_sum, Finset.sum_apply, hterms, current_cleared_nonneg u r hr hu v t hv]
    rw [binomialTail_regular, regularCollision, source_sum_cutoff]
    apply Finset.sum_congr rfl
    intro n _
    unfold sourceCoeff
    rw [show l + 3 * (D : ℤ) - 3 + 3 * ((n : ℤ) + 1) =
      l + 3 * (D : ℤ) + 3 * n by ring]
  rw [map_add, Pi.add_apply, hcollision]
  apply LinearMap.ext
  intro w
  rw [LinearMap.add_apply, nativeField_current_negative_iterate u r hr hu,
    signedNormalTaylor_eq u r hr hu d v t hv]

/-- Both product ranges identify the constructed inverse residue with the
actual native field of the current-first source product. -/
theorem adjustedResidue_native_current (u : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (v : NativeStates)
    (t : ℤ) (hv : InResidue t (nativeField v)) (n : ℤ) :
    adjustedResidue (-(r : ℤ)) t (nativeField (currentAlong lattice u)) (nativeField v)
        (vectorFrequencyBound lattice v + 1) n =
      nativeField (mu lattice (currentAlong lattice u) n v) := by
  cases n with
  | ofNat q => exact adjustedResidue_native_current_nonneg u r hr hu v t hv q
  | negSucc q =>
    exact adjustedResidue_native_current_neg u r hr hu v t hv ⟨q + 1, Nat.succ_pos q⟩

#check binomialTail_add
#check binomialTail_inverse
#check clearedResidue_zero_of_locality
#check adjustedResidue_coeff
#check adjustedResidue_cutoff_mono
#check adjustedResidue_strip_left_add_three
#check adjustedResidue_strip_right_add_three
#check adjustedResidue_eq_iff
#check native_clearedResidue_cutoff
#check adjustedResidue_native_current_nonneg
#check adjustedResidue_native_current
#print axioms binomialTail_add
#print axioms binomialTail_inverse
#print axioms clearedResidue_zero_of_locality
#print axioms adjustedResidue_coeff
#print axioms adjustedResidue_cutoff_mono
#print axioms adjustedResidue_strip_left_add_three
#print axioms adjustedResidue_strip_right_add_three
#print axioms adjustedResidue_eq_iff
#print axioms native_clearedResidue_cutoff
#print axioms adjustedResidue_native_current_nonneg
#print axioms adjustedResidue_native_current

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueProduct
