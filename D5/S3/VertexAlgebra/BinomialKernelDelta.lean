/- GID: D5/S3/VertexAlgebra/BinomialKernelDelta
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BinomialKernelDelta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite binomial expansions cancel the charged commutator at a sufficient lattice order. -/

import D5.S3.VertexAlgebra.FieldNormalProductLocality

/- Finite binomial cancellation for a genuinely bounded common kernel.
   The Option-Nat finite-sum splitting argument is adapted from the sealed
   FieldNormalProductLocality.normalMinusOne_locality residue calculation.
   Signed Pascal is the integer Ring.choose law; no field-locality premise.
   This is the algebraic (z-w) cancellation in the lattice OPE of
   Bakalov--Kac math/0402315v1, section 4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BinomialKernelDelta
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
noncomputable section

def BoundedKernel (K : ℤ → ℤ → V) : Prop :=
  ∃ a b : ℤ, ∀ k l : ℤ, k < a ∨ l < b → K k l = 0

def chooseSign (b : ℤ) (j : ℕ) : ℂ := (-1 : ℂ)^j * (Ring.choose b j : ℤ)

def expansion (K : ℤ → ℤ → V) (b : ℤ) : ℤ → ℤ → V :=
  fun k l => ∑ᶠ j : ℕ, chooseSign b j • K (k-b+j) (l-j)

def rawDelta (f : ℤ → ℤ → V) : ℤ → ℤ → V :=
  fun k l => f (k-1) l - f k (l-1)

def rawDeltaEnd : Module.End ℂ (ℤ → ℤ → V) where
  toFun := rawDelta
  map_add' f g := by funext k l; simp [rawDelta]; abel
  map_smul' c f := by funext k l; simp [rawDelta, smul_sub]

theorem rawDelta_iterate_smul (n : ℕ) (c : ℂ) (f : ℤ → ℤ → V) :
    rawDelta^[n] (c • f) = c • rawDelta^[n] f := by
  change (rawDeltaEnd : Module.End ℂ (ℤ → ℤ → V))^[n] (c • f) =
    c • (rawDeltaEnd : Module.End ℂ (ℤ → ℤ → V))^[n] f
  rw [← Module.End.pow_apply, ← Module.End.pow_apply, map_smul]

theorem rawDelta_iterate_sub (n : ℕ) (f g : ℤ → ℤ → V) :
    rawDelta^[n] (f-g) = rawDelta^[n] f - rawDelta^[n] g := by
  change (rawDeltaEnd : Module.End ℂ (ℤ → ℤ → V))^[n] (f-g) =
    (rawDeltaEnd : Module.End ℂ (ℤ → ℤ → V))^[n] f -
      (rawDeltaEnd : Module.End ℂ (ℤ → ℤ → V))^[n] g
  rw [← Module.End.pow_apply, ← Module.End.pow_apply, ← Module.End.pow_apply, map_sub]

theorem expansion_finite (K : ℤ → ℤ → V) (hK : BoundedKernel K)
    (b k l : ℤ) : Function.HasFiniteSupport
      (fun j : ℕ => chooseSign b j • K (k-b+j) (l-j)) := by
  obtain ⟨a,c,h⟩ := hK
  apply BddAbove.finite
  refine bddAbove_def.mpr ⟨(l-c).toNat, ?_⟩
  intro j hj
  by_contra hn
  exact hj (by
    change chooseSign b j • K (k-b+j) (l-j) = 0
    rw [h _ _ (Or.inr (by omega)), smul_zero])

theorem finsum_split (f : ℕ → V) (hf : Function.HasFiniteSupport f) :
    ∑ᶠ j : ℕ, f j = f 0 + ∑ᶠ j : ℕ, f (j+1) := by
  let e : Option ℕ ≃ ℕ := {
    toFun value := match value with | none => 0 | some j => j+1
    invFun value := match value with | 0 => none | j+1 => some j
    left_inv value := by cases value <;> rfl
    right_inv value := by cases value <;> rfl }
  rw [← finsum_comp_equiv e, finsum_option]
  · rfl
  · exact hf.fun_comp_of_injective (g := fun j : ℕ => j+1)
      (fun j k h => Nat.add_right_cancel h)

@[simp] theorem chooseSign_zero (b : ℤ) : chooseSign b 0 = 1 := by simp [chooseSign]

theorem chooseSign_pascal (b : ℤ) (j : ℕ) :
    chooseSign (b+1) (j+1) = chooseSign b (j+1) - chooseSign b j := by
  simp only [chooseSign, Ring.choose_succ_succ, Int.cast_add, pow_succ]
  ring

/-- Multiplying either expansion by z-w raises the integer binomial exponent. -/
theorem rawDelta_expansion (K : ℤ → ℤ → V) (hK : BoundedKernel K) (b : ℤ) :
    rawDelta (expansion K b) = expansion K (b+1) := by
  funext k l
  let F := fun j : ℕ => chooseSign b j • K (k-1-b+j) (l-j)
  let G := fun j : ℕ => chooseSign b j • K (k-b+j) (l-1-j)
  let H := fun j : ℕ => chooseSign (b+1) j • K (k-(b+1)+j) (l-j)
  have hF : Function.HasFiniteSupport F := expansion_finite K hK b (k-1) l
  have hG : Function.HasFiniteSupport G := expansion_finite K hK b k (l-1)
  have hH : Function.HasFiniteSupport H := expansion_finite K hK (b+1) k l
  have hFs : Function.HasFiniteSupport (fun j : ℕ => F (j+1)) :=
    hF.fun_comp_of_injective (g := fun j : ℕ => j+1)
      (fun j k h => Nat.add_right_cancel h)
  have hrec (j : ℕ) : F (j+1)-G j = H (j+1) := by
    dsimp [F,G,H]
    rw [chooseSign_pascal, sub_smul]
    have h1 : k-1-b+((j : ℤ)+1) = k-b+j := by omega
    have h2 : l-((j : ℤ)+1) = l-1-j := by omega
    have h3 : k-(b+1)+((j : ℤ)+1) = k-b+j := by omega
    rw [h1,h2,h3]
  have hz : F 0 = H 0 := by simp [F,H]; congr 1 <;> omega
  change (∑ᶠ j : ℕ, F j) - (∑ᶠ j : ℕ, G j) = ∑ᶠ j : ℕ, H j
  rw [finsum_split F hF, finsum_split H hH, add_sub_assoc,
    ← finsum_sub_distrib hFs hG]
  simp_rw [hrec]
  rw [hz]

theorem rawDelta_iterate_expansion (K : ℤ → ℤ → V) (hK : BoundedKernel K)
    (b : ℤ) (n : ℕ) : rawDelta^[n] (expansion K b) = expansion K (b+n) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply', hn, rawDelta_expansion K hK]
    congr 1
    omega

@[simp] theorem expansion_zero (K : ℤ → ℤ → V) : expansion K 0 = K := by
  funext k l
  unfold expansion
  rw [finsum_eq_single _ 0]
  · simp [chooseSign]
  · intro j hj
    simp [chooseSign, Ring.choose_zero_ite, hj]

/-- Negative exponents cancel exactly, with no infinite-sum convention shortcut. -/
theorem rawDelta_negative (K : ℤ → ℤ → V) (hK : BoundedKernel K) (n : ℕ) :
    rawDelta^[n] (expansion K (-(n : ℤ))) = K := by
  rw [rawDelta_iterate_expansion K hK]
  simp

theorem expansion_nat (K : ℤ → ℤ → V) (n : ℕ) (k l : ℤ) :
    expansion K n k l = ∑ j ∈ Finset.range (n+1),
      ((-1 : ℂ)^j * (n.choose j : ℂ)) • K (k-n+j) (l-j) := by
  classical
  unfold expansion
  simp only [chooseSign, Ring.choose_natCast, Int.cast_natCast]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  apply Finset.mem_range.mpr
  by_contra h
  exact hj (by simp [Nat.choose_eq_zero_of_lt (show n < j by omega)])

def flip (K : ℤ → ℤ → V) : ℤ → ℤ → V := fun k l => K l k

theorem bounded_flip (K : ℤ → ℤ → V) (hK : BoundedKernel K) : BoundedKernel (flip K) := by
  obtain ⟨a,b,h⟩ := hK
  exact ⟨b,a,fun k l hkl => h l k hkl.symm⟩

theorem expansion_nat_flip (K : ℤ → ℤ → V) (n : ℕ) :
    expansion K n = (-1 : ℂ)^n • flip (expansion (flip K) n) := by
  funext k l
  simp only [Pi.smul_apply, flip, expansion_nat, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_range_reflect (fun j =>
    (((-1 : ℂ)^n * ((-1 : ℂ)^j * (n.choose j : ℂ))) •
      K (k-j) (l-n+j))) (n+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := by simpa using Finset.mem_range.mp hj
  have hsub : n+1-1-j = n-j := by omega
  rw [hsub, Nat.choose_symm hj']
  have hsign : (-1 : ℂ)^n * ((-1 : ℂ)^(n-j)) = (-1 : ℂ)^j := by
    have hpow : (-1 : ℂ)^(n-j) * (-1 : ℂ)^(n-j) = 1 := by
      rw [← mul_pow]; norm_num
    calc
      _ = ((-1 : ℂ)^j * (-1 : ℂ)^(n-j)) * (-1 : ℂ)^(n-j) := by
        have he : (-1 : ℂ)^n = (-1 : ℂ)^j * (-1 : ℂ)^(n-j) := by
          rw [← pow_add, Nat.add_sub_of_le hj']
        exact congrArg (fun z : ℂ => z * (-1 : ℂ)^(n-j)) he
      _ = (-1 : ℂ)^j * ((-1 : ℂ)^(n-j) * (-1 : ℂ)^(n-j)) := by ring
      _ = _ := by rw [hpow,mul_one]
  rw [← mul_assoc, hsign]
  congr 2 <;> omega

theorem rawDelta_flip (f : ℤ → ℤ → V) : rawDelta (flip f) = -flip (rawDelta f) := by
  funext k l
  simp [rawDelta, flip, neg_sub]

theorem rawDelta_iterate_flip (n : ℕ) (f : ℤ → ℤ → V) :
    rawDelta^[n] (flip f) = (-1 : ℂ)^n • flip (rawDelta^[n] f) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply', hn]
    rw [show rawDelta (((-1 : ℂ)^n) • flip (rawDelta^[n] f)) =
        (-1 : ℂ)^n • rawDelta (flip (rawDelta^[n] f)) from
      (rawDeltaEnd : Module.End ℂ (ℤ → ℤ → V)).map_smul _ _]
    simp only [rawDelta_flip, pow_succ, mul_smul, neg_one_smul,
      Function.iterate_succ_apply', smul_neg]

def integerSign (b : ℤ) : ℂ := if Even b then 1 else -1

theorem integerSign_nat (n : ℕ) : integerSign (n : ℤ) = (-1 : ℂ)^n := by
  simp [integerSign, neg_one_pow_eq_ite]

theorem integerSign_neg_nat (n : ℕ) : integerSign (-(n : ℤ)) = (-1 : ℂ)^n := by
  simp [integerSign, neg_one_pow_eq_ite]

/-- A sufficient charged exponent: zero for nonnegative pairing, -b otherwise. -/
theorem binomial_commutator_killed (K : ℤ → ℤ → V) (hK : BoundedKernel K) (b : ℤ) :
    rawDelta^[(-b).toNat]
      (expansion K b - integerSign b • flip (expansion (flip K) b)) = 0 := by
  by_cases hb : 0 ≤ b
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hb
    rw [show (-(n : ℤ)).toNat = 0 by omega, Function.iterate_zero_apply,
      integerSign_nat, expansion_nat_flip K n, sub_self]
  · let n := (-b).toNat
    have he : b = -(n : ℤ) := by dsimp [n]; omega
    rw [he, show (-(-(n : ℤ))).toNat = n by omega, rawDelta_iterate_sub,
      rawDelta_iterate_smul, rawDelta_iterate_flip,
      rawDelta_negative K hK n, rawDelta_negative (flip K) (bounded_flip K hK) n,
      integerSign_neg_nat, smul_smul]
    have hs : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by rw [← mul_pow]; norm_num
    rw [hs,one_smul]
    have hf : flip (flip K) = K := rfl
    rw [hf,sub_self]

def normalized (f : ℤ → ℤ → V) : ℤ → ℤ → V := fun m n => f (-m-1) (-n-1)

theorem normalized_delta (f : ℤ → ℤ → V) :
    FieldNormalProductLocality.delta (normalized f) = normalized (rawDelta f) := by
  funext m n
  dsimp [FieldNormalProductLocality.delta, normalized, rawDelta]
  congr 2 <;> omega

theorem normalized_iterate (f : ℤ → ℤ → V) (n : ℕ) :
    FieldNormalProductLocality.delta^[n] (normalized f) = normalized (rawDelta^[n] f) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Function.iterate_succ_apply', hn, normalized_delta,
      Function.iterate_succ_apply']

theorem delta_evaluation (f : ℤ → ℤ → Module.End ℂ V) (v : V) (n : ℕ) :
    (fun m k => (FieldNormalProductLocality.delta^[n] f) m k v) =
      FieldNormalProductLocality.delta^[n] (fun m k => f m k v) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    funext m k
    simp only [FieldNormalProductLocality.delta, LinearMap.sub_apply]
    exact congrArg (fun g : ℤ → ℤ → V => g (m+1) k - g m (k+1)) hn

end
end D5.S3.VertexAlgebra.BinomialKernelDelta

/- Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the supplier repository LICENSE.
Authors: Scott Carnahan
The local binomial proof inside sealed StateFieldResidueReconstruction,
immutable bfd9ff0f15397a4fb933f36d701a60d325d84b08, is exported here unchanged
in its generic module variable. Only promotion from local to named theorem
and proof indentation are changed. No concrete-carrier transfer is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.FieldDeltaBinomial
open FieldNormalProductLocality
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
noncomputable section
theorem delta_binomial (value : ℤ → ℤ → Module.End ℂ V) (order : ℕ) (first second : ℤ) : ((deltaEnd ^ order) value) first second = ∑ offset ∈ Finset.range (order + 1), (((-1 : ℂ) ^
    offset) * (order.choose offset : ℂ)) • value (first + (order : ℤ) - offset) (second + offset) := by
  let shiftLeft : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
    toFun value := fun first second => value (first + 1) second
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let shiftRight : Module.End ℂ (ℤ → ℤ → Module.End ℂ V) := {
    toFun value := fun first second => value first (second + 1)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have commute : Commute (-shiftRight) shiftLeft := by apply LinearMap.ext; intro distribution; funext left right; simp [shiftLeft, shiftRight]
  have leftPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ V) : (shiftLeft ^ degree) distribution = fun left right => distribution (left + degree) right := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
      change distribution (left + 1 + degree) right = distribution (left + (degree + 1 : ℕ)) right; congr 1; push_cast; omega
  have rightPower (degree : ℕ) (distribution : ℤ → ℤ → Module.End ℂ V) : ((-shiftRight) ^ degree) distribution = fun left right => ((-1 : ℂ) ^ degree) • distribution left
    (right + degree) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [pow_succ', Module.End.mul_apply, inductionHypothesis]; funext left right
      change -(((-1 : ℂ) ^ degree) • distribution left (right + 1 + degree)) = ((-1 : ℂ) ^ (degree + 1)) • distribution left (right + (degree + 1 : ℕ))
      rw [pow_succ', mul_smul, neg_one_smul]
      have indices : right + 1 + (degree : ℤ) = right + (degree + 1 : ℕ) := by push_cast; omega
      rw [indices]
  have equation : (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V)) = -shiftRight + shiftLeft := by
    apply LinearMap.ext; intro distribution; funext left right; simp [deltaEnd, delta, shiftLeft, shiftRight]
    abel
  rw [equation, commute.add_pow, LinearMap.sum_apply]; simp only [Finset.sum_apply]; apply Finset.sum_congr rfl; intro offset member
  have within : offset ≤ order := by simpa using Finset.mem_range.mp member
  simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, rightPower, leftPower, Pi.smul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]; congr 2; push_cast [Int.natCast_sub within]; omega
end
end D5.S3.VertexAlgebra.FieldDeltaBinomial
