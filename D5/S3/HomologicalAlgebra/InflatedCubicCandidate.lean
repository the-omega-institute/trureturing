/- GID: D5/S3/HomologicalAlgebra/InflatedCubicCandidate
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/InflatedCubicCandidate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Involution restrictions leave two candidates for the inflated class. -/

import D5.S3.HomologicalAlgebra.BarnesWallQ8CohomologyDetector
import D5.S3.HomologicalAlgebra.ElementaryTwoThirdCohomologyDetection
import D5.S3.HomologicalAlgebra.InflatedCupCoboundary
import D5.S3.HomologicalAlgebra.CocycleDiagonalCubic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! A normalized cocycle with diagonal `q * (e + ell)` becomes the explicit
quadratic candidate plus a coboundary on the sign extension. -/

open scoped BigOperators

set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.InflatedCubicCandidate

open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient (F₂ SignExtension)

abbrev Charge (ι : Type*) := (ι × Bool) → F₂
abbrev ChargeGroup (ι : Type*) := Multiplicative (Charge ι)

def d₂ {G M : Type*} [Mul G] [AddCommGroup M]
    (B : G → G → M) (a b d : G) : M :=
  B b d - B (a * b) d + B a (b * d) - B a b

def d₃ {G M : Type*} [Mul G] [AddCommGroup M]
    (f : G → G → G → M) (a b d t : G) : M :=
  f b d t - f (a * b) d t + f a (b * d) t - f a b (d * t) + f a b d

abbrev Normalized {G M : Type*} [One G] [Zero M] (f : G → G → G → M) : Prop :=
  ∀ a b, f 1 a b = 0 ∧ f a 1 b = 0 ∧ f a b 1 = 0

variable {ι : Type*} [Fintype ι]

abbrev q (a : Charge ι) : F₂ :=
  SplitQuadraticCubic.quadratic (fun i => a (i, false)) (fun i => a (i, true))

/-- The explicit trilinear exponent with diagonal `q`. -/
def etaQ (a b d : Charge ι) : F₂ :=
  ∑ i, a (i, false) * b (i, true) * d (i, true)

private theorem etaQ_diagonal (a : Charge ι) : etaQ a a a = q a := by
  have bit : ∀ x : F₂, x * x = x := by decide +kernel
  simp only [etaQ, q, SplitQuadraticCubic.quadratic, mul_assoc, bit]

private theorem etaQ_cocycle (a b d t : Charge ι) :
    etaQ b d t - etaQ (a + b) d t + etaQ a (b + d) t -
      etaQ a b (d + t) + etaQ a b d = 0 := by
  simp only [etaQ, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : ι, (0 : F₂) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply]
      ring
    _ = 0 := Finset.sum_const_zero

/-- Inflation leaves the quadratic candidate and an explicit two-coboundary. -/
theorem inflated_eq_candidate_add_coboundary {ι M : Type} [Fintype ι] [AddCommGroup M]
    (half : ∀ m : M, ∃ k, k + k = m)
    (σ : F₂ →+ M) (c : Charge ι →+ Charge ι →+ F₂) (e : F₂) (ell : Charge ι →+ F₂)
    (hcdiag : ∀ a, c a a = q a)
    (f : ChargeGroup ι → ChargeGroup ι → ChargeGroup ι → M)
    (hf : ∀ a b d t, d₃ f a b d t = 0) (hn : Normalized f)
    (hdiag : ∀ a, f a a a = σ (q a.toAdd * (e + ell a.toAdd))) :
    ∃ B, ∀ g h k : SignExtension (Charge ι) c,
      f (Multiplicative.ofAdd g.charge) (Multiplicative.ofAdd h.charge)
        (Multiplicative.ofAdd k.charge) =
        σ (e * etaQ g.charge h.charge k.charge) + d₂ B g h k := by
  let C (a b d : ChargeGroup ι) : F₂ :=
    e * etaQ a.toAdd b.toAdd d.toAdd + c a.toAdd b.toAdd * ell d.toAdd
  let R (a b d : ChargeGroup ι) : M := f a b d - σ (C a b d)
  have hmul (a b : ChargeGroup ι) : (a * b).toAdd = a.toAdd + b.toAdd := rfl
  have hone : (1 : ChargeGroup ι).toAdd = 0 := rfl
  have htag (x : Charge ι) : (Multiplicative.ofAdd x).toAdd = x := rfl
  have hC (a b d t : ChargeGroup ι) : d₃ C a b d t = 0 := by
    have hQ := congrArg (fun x : F₂ => e * x)
      (etaQ_cocycle a.toAdd b.toAdd d.toAdd t.toAdd)
    have hL := InflatedCupCoboundary.cup_cocycle c ell a.toAdd b.toAdd d.toAdd t.toAdd
    simp only [mul_sub, mul_add, mul_zero] at hQ
    simp only [d₃, C, hmul]
    linear_combination (norm := abel) hQ + hL
  have hR (a b d t : ChargeGroup ι) : d₃ R a b d t = 0 := by
    have h := congrArg (fun x : F₂ => σ x) (hC a b d t)
    have hF := hf a b d t
    simp only [d₃, map_add, map_sub, map_zero] at h
    dsimp only [d₃] at hF
    simp only [d₃, R]
    linear_combination (norm := abel) hF - h
  have hRN : Normalized R := by
    intro a b
    rcases hn a b with ⟨h₁, h₂, h₃⟩
    refine ⟨?_, ?_, ?_⟩
    all_goals simp only [R, C, hone, etaQ, Pi.zero_apply, zero_mul,
      mul_zero, Finset.sum_const_zero, map_zero, AddMonoidHom.zero_apply, add_zero,
      h₁, h₂, h₃, sub_self]
  have hRD (a : ChargeGroup ι) : R a a a = 0 := by
    change f a a a - σ (e * etaQ a.toAdd a.toAdd a.toAdd + c a.toAdd a.toAdd * ell a.toAdd) = 0
    rw [hdiag a, etaQ_diagonal, hcdiag, mul_add, mul_comm (q a.toAdd) e, sub_self]
  obtain ⟨D, hD⟩ :=
    ElementaryTwoThirdCohomologyDetection.normalized_diagonal_zero_is_coboundary half R hR hRN hRD
  let liftD (g h : SignExtension (Charge ι) c) : M :=
    D (Multiplicative.ofAdd g.charge) (Multiplicative.ofAdd h.charge)
  let signCup (g h : SignExtension (Charge ι) c) : M := σ (g.sign * ell h.charge)
  refine ⟨fun g h => liftD g h + signCup g h, ?_⟩
  intro g h k
  have hLift : d₂ liftD g h k = R (Multiplicative.ofAdd g.charge)
      (Multiplicative.ofAdd h.charge) (Multiplicative.ofAdd k.charge) :=
    hD (Multiplicative.ofAdd g.charge) (Multiplicative.ofAdd h.charge)
      (Multiplicative.ofAdd k.charge)
  have hSign : d₂ signCup g h k = σ (c g.charge h.charge * ell k.charge) := by
    simpa only [d₂, signCup, map_add, map_sub] using congrArg (fun x : F₂ => σ x)
      (InflatedCupCoboundary.inflated_cup_is_coboundary c ell g h k)
  simp only [d₂, R, C, htag, map_add] at hLift
  simp only [d₂] at hSign ⊢
  linear_combination (norm := abel) -hLift - hSign

/-- The inflation of a normalized quotient cocycle vanishing diagonally on the
split quadratic zero cone has one of two explicit cohomology representatives. -/
theorem inflation_has_two_candidates {ι M : Type} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] [AddCommGroup M] (half : ∀ m : M, ∃ k, k + k = m)
    (σ : F₂ →+ M) (hinj : Function.Injective σ)
    (htwo : ∀ m : M, m + m = 0 → ∃ e, σ e = m)
    (c : Charge ι →+ Charge ι →+ F₂) (hcdiag : ∀ a, c a a = q a)
    (f : ChargeGroup ι → ChargeGroup ι → ChargeGroup ι → M)
    (hf : ∀ a b d t, d₃ f a b d t = 0) (hn : Normalized f)
    (hsing : ∀ x, q x = 0 →
      f (Multiplicative.ofAdd x) (Multiplicative.ofAdd x) (Multiplicative.ofAdd x) = 0) :
    ∃ e : F₂, ∃ B, ∀ g h k : SignExtension (Charge ι) c,
      f (Multiplicative.ofAdd g.charge) (Multiplicative.ofAdd h.charge)
        (Multiplicative.ofAdd k.charge) =
        σ (e * etaQ g.charge h.charge k.charge) + d₂ B g h k := by
  obtain ⟨e, ℓ, hdiag⟩ :=
    CocycleDiagonalCubic.diagonal_factor_on_split_zero_cone half σ hinj htwo f hf hn hsing
  refine ⟨e, inflated_eq_candidate_add_coboundary half σ c e ℓ hcdiag f hf hn ?_⟩
  intro a
  exact hdiag a.toAdd

/-- It suffices to know the inflated cocycle is a coboundary on the cyclic
subgroup of every nonidentity involution. The lifts of singular charges
have order at most two, so these tests force the required diagonal vanishings. -/
theorem inflation_has_two_candidates_of_involution_restrictions
    {ι M : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι] [AddCommGroup M]
    (half : ∀ m : M, ∃ k, k + k = m)
    (σ : F₂ →+ M) (hinj : Function.Injective σ)
    (htwo : ∀ m : M, m + m = 0 → ∃ e, σ e = m)
    (c : Charge ι →+ Charge ι →+ F₂) (hcdiag : ∀ a, c a a = q a)
    (f : ChargeGroup ι → ChargeGroup ι → ChargeGroup ι → M)
    (hf : ∀ a b d t, d₃ f a b d t = 0) (hn : Normalized f)
    (hcyc : ∀ z : SignExtension (Charge ι) c, z ≠ 1 → z * z = 1 →
      ∃ B : Subgroup.zpowers z → Subgroup.zpowers z → M,
        ∀ g h k : Subgroup.zpowers z,
          d₂ B g h k = f (Multiplicative.ofAdd g.val.charge)
            (Multiplicative.ofAdd h.val.charge) (Multiplicative.ofAdd k.val.charge)) :
    ∃ e : F₂, ∃ B, ∀ g h k : SignExtension (Charge ι) c,
      f (Multiplicative.ofAdd g.charge) (Multiplicative.ofAdd h.charge)
        (Multiplicative.ofAdd k.charge) =
        σ (e * etaQ g.charge h.charge k.charge) + d₂ B g h k := by
  apply inflation_has_two_candidates half σ hinj htwo c hcdiag f hf hn
  intro x hx
  let z : SignExtension (Charge ι) c := ⟨0, x⟩
  have hz : z * z = 1 := by
    have hc : c x x = 0 := (hcdiag x).trans hx
    have hxx : x + x = 0 := funext fun i => CharTwo.add_self_eq_zero (x i)
    change (⟨0 + 0 + c x x, x + x⟩ : SignExtension (Charge ι) c) = ⟨0, 0⟩
    simp [hc, hxx]
  by_cases hz₁ : z = 1
  · have hzero : x = 0 := congrArg SignExtension.charge hz₁
    subst x
    exact (hn 1 1).1
  obtain ⟨B, hB⟩ := hcyc z hz₁ hz
  let t : Subgroup.zpowers z := ⟨z, Subgroup.mem_zpowers z⟩
  have ht : t * t = 1 := Subtype.ext hz
  have h₁ := hB t t t
  have h₂ := hB t 1 t
  change d₂ B t t t = f (Multiplicative.ofAdd x) (Multiplicative.ofAdd x)
    (Multiplicative.ofAdd x) at h₁
  change d₂ B t 1 t = f (Multiplicative.ofAdd x) 1 (Multiplicative.ofAdd x) at h₂
  rw [(hn _ _).2.1] at h₂
  simp only [d₂, ht, mul_one, one_mul] at h₁ h₂
  linear_combination (norm := abel) -h₁ - h₂

open BarnesWallQ8CohomologyDetector
  (CircleCoefficients half half_add_half half_ne_zero coefficientHom coefficientHom_one)

private noncomputable def circleSign : F₂ →+ CircleCoefficients := coefficientHom half half_add_half

private theorem circleSign_one : circleSign 1 = half := coefficientHom_one half half_add_half

private theorem circleSign_injective : Function.Injective circleSign := by
  have hbit : ∀ e : F₂, e = 0 ∨ e = 1 := by decide +kernel
  intro a b h
  rcases hbit a with rfl | rfl <;> rcases hbit b with rfl | rfl
  · rfl
  · exfalso
    exact half_ne_zero (by simpa only [map_zero, circleSign_one] using h.symm)
  · exfalso
    exact half_ne_zero (by simpa only [map_zero, circleSign_one] using h)
  · rfl

private theorem circleSign_covers_two_torsion (x : CircleCoefficients) (hx : x + x = 0) :
    ∃ e : F₂, circleSign e = x := by
  have hx₂ : (2 : ℕ) • x = 0 := by simpa only [two_nsmul] using hx
  obtain ⟨n, hn, hv⟩ := (AddCircle.nsmul_eq_zero_iff (by decide : 0 < (2 : ℕ))).mp hx₂
  have hchoice : n = 0 ∨ n = 1 := by omega
  rcases hchoice with rfl | rfl
  · exact ⟨0, by simpa using hv⟩
  · exact ⟨1, by simpa [circleSign_one, half] using hv⟩

private theorem circle_doubling_surjective (x : CircleCoefficients) :
    ∃ y : CircleCoefficients, y + y = x := by
  refine QuotientAddGroup.induction_on x (fun r => ?_)
  refine ⟨((r / 2 : ℝ) : CircleCoefficients), ?_⟩
  rw [← AddCircle.coe_add, add_halves]

/-- For circle coefficients, triviality on involution subgroups leaves zero
and the explicit trilinear quadratic candidate on the sign extension. -/
theorem circle_inflation_has_two_candidates
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (c : Charge ι →+ Charge ι →+ F₂) (hcdiag : ∀ a, c a a = q a)
    (f : ChargeGroup ι → ChargeGroup ι → ChargeGroup ι → CircleCoefficients)
    (hf : ∀ a b d t, d₃ f a b d t = 0) (hn : Normalized f)
    (hcyc : ∀ z : SignExtension (Charge ι) c, z ≠ 1 → z * z = 1 →
      ∃ B : Subgroup.zpowers z → Subgroup.zpowers z → CircleCoefficients,
        ∀ g h k : Subgroup.zpowers z,
          d₂ B g h k = f (Multiplicative.ofAdd g.val.charge)
            (Multiplicative.ofAdd h.val.charge) (Multiplicative.ofAdd k.val.charge)) :
    ∃ e : F₂, ∃ B, ∀ g h k : SignExtension (Charge ι) c,
      f (Multiplicative.ofAdd g.charge) (Multiplicative.ofAdd h.charge)
        (Multiplicative.ofAdd k.charge) =
        coefficientHom half half_add_half (e * etaQ g.charge h.charge k.charge) + d₂ B g h k :=
  inflation_has_two_candidates_of_involution_restrictions circle_doubling_surjective
    circleSign circleSign_injective circleSign_covers_two_torsion c hcdiag f hf hn hcyc

#print axioms circle_inflation_has_two_candidates

end D5.S3.HomologicalAlgebra.InflatedCubicCandidate
