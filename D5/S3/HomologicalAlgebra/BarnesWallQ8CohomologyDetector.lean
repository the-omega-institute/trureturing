/- GID: D5/S3/HomologicalAlgebra/BarnesWallQ8CohomologyDetector
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/BarnesWallQ8CohomologyDetector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree]
   utility: none
   digest: A quaternion bar cycle detects the nonzero inflated Barnes–Wall anomaly candidate. -/

import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic
import OmegaBuild.Commands

/-!
The candidate anomaly for the Barnes–Wall action of Keller, Roberts and
Roberts (arXiv:2411.13646v2, Conjecture 5.2) restricts to a polynomial on
the quotient of the quaternion group by its center. A seven-term normalized
bar cycle detects the inflation, and two degenerate terms lift the cycle to
Mathlib's unnormalized complex.
-/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

namespace D5.S3.HomologicalAlgebra.BarnesWallQ8CohomologyDetector

open CategoryTheory
open Finsupp (single)
open groupCohomology (cochainsIso₂ cochainsIso₃ d₂₃ inhomogeneousCochains)
open groupHomology (d₃₂)

abbrev Q8 := QuaternionGroup 2

def i : Q8 := .a 1
def j : Q8 := .xa 0
def k : Q8 := .xa 3

theorem i_mul_j : i * j = k := by decide

private abbrev jInv : Q8 := j⁻¹
private abbrev kInv : Q8 := k⁻¹

abbrev coefficientRep (M : Type) [AddCommGroup M] := Rep.trivial ℤ Q8 M

/-- The seven terms in the normalized bar cycle, viewed as an unnormalized chain. -/
def xiSeven : (Q8 × Q8 × Q8) →₀ ℤ :=
  -single (jInv, kInv, k) 1 - single (jInv, i, jInv) 1
    + single (jInv, j, jInv) 1 - single (jInv, j, k) 1
    + single (k, kInv, k) 1 + single (k, i, jInv) 1 - single (k, i, k) 1

/-- An unnormalized lift of the normalized cycle, using two degenerate triples. -/
def Xi : (Q8 × Q8 × Q8) →₀ ℤ :=
  xiSeven + single (1, 1, jInv) 1 + single (k, 1, 1) 1

theorem d₃₂_xiSeven :
    d₃₂ (coefficientRep ℤ) xiSeven = single (k, 1) 1 - single (1, jInv) 1 := by
  have onSingle (a b c : Q8) :
      (d₃₂ (coefficientRep ℤ)).hom (single (a, b, c) 1) =
        single (b, c) 1 - single (a * b, c) 1 +
          single (a, b * c) 1 - single (a, b) 1 := by
    exact groupHomology.d₃₂_single (A := coefficientRep ℤ) (a, b, c) (1 : ℤ)
  have h₁ : jInv * kInv = i := by decide
  have h₂ : kInv * k = 1 := by decide
  have h₃ : jInv * i = k := by decide
  have h₄ : i * jInv = kInv := by decide
  have h₅ : jInv * j = 1 := by decide
  have h₆ : j * jInv = 1 := by decide
  have h₇ : j * k = i := by decide
  have h₈ : k * kInv = 1 := by decide
  have h₉ : k * i = j := by decide
  have h₁₀ : i * k = jInv := by decide
  change (d₃₂ (coefficientRep ℤ)).hom xiSeven = _
  simp only [xiSeven, map_add, map_sub, map_neg, onSingle,
    h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀]
  abel

theorem d₃₂_Xi : d₃₂ (coefficientRep ℤ) Xi = 0 := by
  have seven : (d₃₂ (coefficientRep ℤ)).hom xiSeven = _ := d₃₂_xiSeven
  have first : (d₃₂ (coefficientRep ℤ)).hom (single (1, 1, jInv) 1) =
      single (1, jInv) 1 - single (1, 1) 1 := by
    simpa only [one_mul] using
      (groupHomology.d₃₂_single_one_fst (A := coefficientRep ℤ) 1 jInv 1)
  have last : (d₃₂ (coefficientRep ℤ)).hom (single (k, 1, 1) 1) =
      single (1, 1) 1 - single (k, 1) 1 := by
    have h := groupHomology.d₃₂_single_one_thd (A := coefficientRep ℤ) k 1 (1 : ℤ)
    change (d₃₂ (coefficientRep ℤ)).hom (single (k, 1, 1) 1) =
      single (1, 1) 1 - single (k * 1, 1) 1 at h
    simpa only [mul_one] using h
  change (d₃₂ (coefficientRep ℤ)).hom Xi = _
  simp only [Xi, map_add, seven, first, last]
  abel

private def modTwo : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) (ZMod 2)

/-- The quotient coordinates `(u,v)` with `i ↦ (1,0)` and `j ↦ (0,1)`. -/
def quotientCoordinates : Q8 →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun
    | .a e => Multiplicative.ofAdd (modTwo e, 0)
    | .xa e => Multiplicative.ofAdd (modTwo e, 1)
  map_one' := by
    change Multiplicative.ofAdd (modTwo 0, (0 : ZMod 2)) =
      Multiplicative.ofAdd ((0 : ZMod 2), (0 : ZMod 2))
    rw [map_zero]
  map_mul' := by
    have h₂ : modTwo 2 = 0 := by decide
    rintro (x | x) (y | y) <;> apply Multiplicative.ofAdd.injective
    · change (modTwo (x + y), (0 : ZMod 2)) = (modTwo x + modTwo y, 0 + 0)
      simp only [map_add, zero_add]
    · change (modTwo (y - x), (1 : ZMod 2)) = (modTwo x + modTwo y, 0 + 1)
      simp only [map_sub, CharTwo.sub_eq_add, add_comm (modTwo y) (modTwo x), zero_add]
    · change (modTwo (x + y), (1 : ZMod 2)) = (modTwo x + modTwo y, 1 + 0)
      simp only [map_add, add_zero]
    · change (modTwo (2 + y - x), (0 : ZMod 2)) = (modTwo x + modTwo y, 1 + 1)
      simp only [map_sub, map_add, h₂, zero_add, CharTwo.sub_eq_add,
        add_comm (modTwo y) (modTwo x), CharTwo.add_self_eq_zero]

private theorem quotientCoordinates_mul (a b : Q8) :
    (quotientCoordinates (a * b)).toAdd =
      (quotientCoordinates a).toAdd + (quotientCoordinates b).toAdd :=
  congrArg Multiplicative.toAdd (quotientCoordinates.map_mul a b)

/-- The polynomial on the elementary abelian quotient. -/
def etaPolynomial (a b c : ZMod 2 × ZMod 2) : ZMod 2 :=
  (a.1 + a.2) * b.1 * c.1 + a.2 * b.2 * c.2

/-- The inflated exponent in `ZMod 2`. -/
def etaExponent (p : Q8 × Q8 × Q8) : ZMod 2 :=
  etaPolynomial (quotientCoordinates p.1).toAdd (quotientCoordinates p.2.1).toAdd
    (quotientCoordinates p.2.2).toAdd

variable {M : Type} [AddCommGroup M]

/-- Send the nonzero bit to the specified element of order dividing two. -/
def coefficientHom (t : M) (ht : t + t = 0) : ZMod 2 →+ M :=
  ZMod.lift 2 ⟨zmultiplesHom M t, by
    change (2 : ℤ) • t = 0
    rw [two_zsmul, ht]⟩

theorem coefficientHom_one (t : M) (ht : t + t = 0) :
    coefficientHom t ht 1 = t := by
  change ZMod.lift 2 _ ((1 : ℤ) : ZMod 2) = t
  rw [ZMod.lift_coe]
  change (1 : ℤ) • t = t
  exact one_smul ℤ t

/-- The inflated polynomial cochain with `1` in the exponent sent to `t`. -/
def eta (t : M) (ht : t + t = 0) (p : Q8 × Q8 × Q8) : M :=
  coefficientHom t ht (etaExponent p)

private theorem etaExponent_cocycle (a b c d : Q8) :
    etaExponent (b, c, d) - etaExponent (a * b, c, d)
      + etaExponent (a, b * c, d) - etaExponent (a, b, c * d)
      + etaExponent (a, b, c) = 0 := by
  simp only [etaExponent, quotientCoordinates_mul,
    etaPolynomial, Prod.fst_add, Prod.snd_add]
  ring

theorem eta_cocycle (t : M) (ht : t + t = 0) (a b c d : Q8) :
    eta t ht (b, c, d) - eta t ht (a * b, c, d)
      + eta t ht (a, b * c, d) - eta t ht (a, b, c * d)
      + eta t ht (a, b, c) = 0 := by
  simpa only [eta, map_sub, map_add, map_zero] using
    congrArg (coefficientHom t ht) (etaExponent_cocycle a b c d)

/-- Evaluation on the original seven terms. The three nonzero values have signs `+,-,+`. -/
theorem eta_xiSeven (t : M) (ht : t + t = 0) :
    Finsupp.linearCombination ℤ (eta t ht) xiSeven = t := by
  have e₁ : etaExponent (jInv, kInv, k) = 0 := by decide
  have e₂ : etaExponent (jInv, i, jInv) = 0 := by decide
  have e₃ : etaExponent (jInv, j, jInv) = 1 := by decide
  have e₄ : etaExponent (jInv, j, k) = 1 := by decide
  have e₅ : etaExponent (k, kInv, k) = 1 := by decide
  have e₆ : etaExponent (k, i, jInv) = 0 := by decide
  have e₇ : etaExponent (k, i, k) = 0 := by decide
  simp only [xiSeven, map_add, map_sub, map_neg, Finsupp.linearCombination_single,
    one_smul, eta, e₁, e₂, e₃, e₄, e₅, e₆, e₇, coefficientHom_one, map_zero]
  abel

theorem eta_Xi (t : M) (ht : t + t = 0) :
    Finsupp.linearCombination ℤ (eta t ht) Xi = t := by
  have e₈ : etaExponent (1, 1, jInv) = 0 := by decide
  have e₉ : etaExponent (k, 1, 1) = 0 := by decide
  simp only [Xi, map_add, eta_xiSeven, Finsupp.linearCombination_single, one_smul]
  simp only [eta, e₈, e₉, map_zero, add_zero]

private theorem evaluation_d₂₃ (β : Q8 × Q8 → M) :
    Finsupp.linearCombination ℤ (d₂₃ (coefficientRep M) β) =
      (Finsupp.linearCombination ℤ β).comp (d₃₂ (coefficientRep ℤ)).hom := by
  apply Finsupp.lhom_ext
  rintro ⟨a, b, c⟩ n
  change Finsupp.linearCombination ℤ (d₂₃ (coefficientRep M) β) (single (a, b, c) n) =
    Finsupp.linearCombination ℤ β (d₃₂ (coefficientRep ℤ) (single (a, b, c) n))
  rw [Finsupp.linearCombination_single, groupHomology.d₃₂_single]
  change n • (β (b, c) - β (a * b, c) + β (a, b * c) - β (a, b)) =
    Finsupp.linearCombination ℤ β
      (single (b, c) n - single (a * b, c) n + single (a, b * c) n - single (a, b) n)
  simp only [map_sub, map_add, Finsupp.linearCombination_single, smul_sub, smul_add]

/-- A coboundary evaluates to zero on `Xi`, so `eta` cannot be a coboundary. -/
theorem eta_not_coboundary (t : M) (ht : t + t = 0) (hne : t ≠ 0)
    (β : Q8 × Q8 → M) : d₂₃ (coefficientRep M) β ≠ eta t ht := by
  intro h
  have hp := LinearMap.congr_fun (evaluation_d₂₃ β) Xi
  rw [h, eta_Xi, LinearMap.comp_apply] at hp
  change t = Finsupp.linearCombination ℤ β (d₃₂ (coefficientRep ℤ) Xi) at hp
  rw [d₃₂_Xi, map_zero] at hp
  exact hne hp

/-- The same cochain in the function-on-`Fin 3` presentation. -/
def etaCochain (t : M) (ht : t + t = 0) : (Fin 3 → Q8) → M :=
  (cochainsIso₃ (coefficientRep M)).inv (eta t ht)

private theorem d_three_apply (f : (Fin 3 → Q8) → M) (a b c d : Q8) :
    inhomogeneousCochains.d (coefficientRep M) 3 f ![a, b, c, d] =
      f ![b, c, d] - f ![a * b, c, d] + f ![a, b * c, d]
        - f ![a, b, c * d] + f ![a, b, c] := by
  change f (fun i => ![a, b, c, d] i.succ) + ∑ r : Fin 4, (-1 : ℤ) ^ (r.val + 1) •
    f (Fin.contractNth r (· * ·) ![a, b, c, d]) = _
  have ht : (fun i : Fin 3 => ![a, b, c, d] i.succ) = ![b, c, d] := by
    funext i
    fin_cases i <;> rfl
  have h₀ : Fin.contractNth (0 : Fin 4) (· * ·) ![a, b, c, d] = ![a * b, c, d] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : Fin.contractNth (1 : Fin 4) (· * ·) ![a, b, c, d] = ![a, b * c, d] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : Fin.contractNth (2 : Fin 4) (· * ·) ![a, b, c, d] = ![a, b, c * d] := by
    funext i
    fin_cases i <;> rfl
  have h₃ : Fin.contractNth (3 : Fin 4) (· * ·) ![a, b, c, d] = ![a, b, c] := by
    funext i
    fin_cases i <;> rfl
  rw [Fin.sum_univ_four, ht, h₀, h₁, h₂, h₃]
  norm_num
  all_goals abel

theorem d_etaCochain (t : M) (ht : t + t = 0) :
    inhomogeneousCochains.d (coefficientRep M) 3 (etaCochain t ht) = 0 := by
  funext p
  have hp : p = ![p 0, p 1, p 2, p 3] := by
    funext r
    fin_cases r <;> rfl
  change inhomogeneousCochains.d (coefficientRep M) 3 (etaCochain t ht) p = 0
  rw [hp, d_three_apply]
  exact eta_cocycle t ht (p 0) (p 1) (p 2) (p 3)

theorem etaCochain_not_coboundary (t : M) (ht : t + t = 0) (hne : t ≠ 0)
    (β : (Fin 2 → Q8) → M) :
    inhomogeneousCochains.d (coefficientRep M) 2 β ≠ etaCochain t ht := by
  intro h
  let A := coefficientRep M
  have hc := ConcreteCategory.congr_hom (groupCohomology.comp_d₂₃_eq A) β
  change d₂₃ A ((cochainsIso₂ A).hom β) =
    (cochainsIso₃ A).hom (inhomogeneousCochains.d A 2 β) at hc
  rw [h, etaCochain, ModuleCat.hom_inv_apply] at hc
  exact eta_not_coboundary t ht hne _ hc

/-- The class represented by the inflated polynomial in Mathlib's third group cohomology. -/
def etaClass (t : M) (ht : t + t = 0) : groupCohomology (coefficientRep M) 3 :=
  groupCohomology.π (coefficientRep M) 3
    (groupCohomology.cocyclesMk (A := coefficientRep M) (etaCochain t ht) (d_etaCochain t ht))

theorem etaClass_ne_zero (t : M) (ht : t + t = 0) (hne : t ≠ 0) :
    etaClass t ht ≠ 0 := by
  intro hz
  let A := coefficientRep M
  let K := groupCohomology.inhomogeneousCochains A
  let S := K.sc 3
  let x : groupCohomology.cocycles A 3 :=
    groupCohomology.cocyclesMk (A := A) (etaCochain t ht) (d_etaCochain t ht)
  change S.homologyπ x = 0 at hz
  have hπ := ConcreteCategory.congr_hom S.homology_π_ι x
  change S.homologyι (S.homologyπ x) = S.pOpcycles (S.iCycles x) at hπ
  rw [hz, map_zero] at hπ
  obtain ⟨β, hβ⟩ := (S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles x)).mp hπ.symm
  have hi : S.iCycles x = etaCochain t ht :=
    groupCohomology.iCocycles_mk (A := A) (etaCochain t ht) (d_etaCochain t ht)
  let β' := (K.xPrevIso (i := 2) (j := 3) rfl).hom β
  have hprev : (ComplexShape.up ℕ).prev 3 = 2 :=
    (ComplexShape.up ℕ).prev_eq' (show (2 : ℕ) + 1 = 3 from rfl)
  have hd : (K.xPrevIso (i := 2) (j := 3) rfl).hom ≫ K.d 2 3 = S.f := by
    exact K.eqToHom_comp_d (by rw [hprev]; rfl) rfl
  have hdβ := ConcreteCategory.congr_hom hd β
  change inhomogeneousCochains.d A 2 β' = S.f β at hdβ
  have hβ' : S.f β = S.iCycles x := hβ
  exact etaCochain_not_coboundary t ht hne β' (hdβ.trans (hβ'.trans hi))

/-- Circle coefficients in additive notation. -/
abbrev CircleCoefficients := AddCircle (1 : ℝ)

def half : CircleCoefficients := ((1 / 2 : ℝ) : CircleCoefficients)

theorem half_add_half : half + half = 0 := by
  unfold half
  rw [← AddCircle.coe_add]
  have h : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rw [h]
  exact AddCircle.coe_period (1 : ℝ)

theorem half_ne_zero : half ≠ 0 := by
  intro h
  change ((1 / 2 : ℝ) : CircleCoefficients) = 0 at h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  have hn' : (n : ℝ) = 1 / 2 := by simpa only [zsmul_eq_mul, mul_one] using hn
  have hc : ((2 * n : ℤ) : ℝ) = 1 := by
    push_cast
    linarith
  have hi : (2 : ℤ) * n = 1 := by exact_mod_cast hc
  omega

theorem eta_xiSeven_circle :
    Finsupp.linearCombination ℤ (eta half half_add_half) xiSeven =
      ((1 / 2 : ℝ) : CircleCoefficients) :=
  eta_xiSeven half half_add_half

theorem etaClass_circle_ne_zero : etaClass half half_add_half ≠ 0 :=
  etaClass_ne_zero half half_add_half half_ne_zero

#print axioms etaClass_circle_ne_zero

end D5.S3.HomologicalAlgebra.BarnesWallQ8CohomologyDetector
