/- GID: D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual all-state outer-insertion obstruction for negative rank one.
-/

import D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.NegativeRankOneStrongGeneration

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticePositiveEnergy LatticeCoefficientEnergy
open scoped BigOperators VertexOperator

noncomputable section

/- The coefficient of the oscillator constant in a fixed charge sector. -/
def groundCoefficient (D : LatticeData) (q : Charge D) : Carrier D →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (q, 0)).comp (carrierCoeffEquiv D).toLinearMap

@[simp] theorem groundCoefficient_apply (D : LatticeData) (q : Charge D)
    (v : Carrier D) :
    groundCoefficient D q v = (v q).coeff 0 := by
  rfl

/- This is the exact projection consequence of the original all-state grading;
   it applies to arbitrary oscillator polynomials and arbitrary finite charge
   mixtures, with no positivity or global lower-bound premise. -/
theorem groundCoefficient_mode_eq_zero_of_grade_mismatch
    (D : LatticeData) (m n k : ℤ) (q : Charge D) (u v : Carrier D)
    (hu : u ∈ grade D m) (hv : v ∈ grade D n)
    (hneq : energy D (q, 0) ≠ m + n - k - 1) :
    groundCoefficient D q (((Y D u)[[k]]) v) = 0 := by
  have hout := actual_mode_grade D m n k u v hu hv
  have hz := (mem_grade_iff D (m + n - k - 1) _).mp hout (q, 0) hneq
  exact hz

/- The strict inequality which drives the positive-charge outer insertion in
   G=-2d.  The factors r,t are arbitrary oscillator degrees; no lower bound
   on the total charge energy is used. -/
theorem negative_rank_one_outer_energy_mismatch
    (d s q r t k : ℤ)
    (hd : 0 < d) (hs : 0 < s) (hsq : s < q)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hk : k < 0) :
    -d * q ^ 2 ≠ (r - d * s ^ 2) + (t - d * (q - s) ^ 2) - k - 1 := by
  intro h
  have hqs : 0 < q - s := by omega
  have hprod : 0 < 2 * d * s * (q - s) := by positivity
  nlinarith

/- A directly consumable all-state specialization: whenever the two input
   homogeneous grades have the negative rank-one values and the output charge
   is q=s+(q-s), the oscillator-constant output of every strictly negative
   mode vanishes. The grade hypotheses are intentionally explicit so this
   statement remains faithful to the actual grading API. -/
theorem negative_rank_one_outer_insertion_zero
    (d s q r t k : ℤ) (D : LatticeData)
    (u v : Carrier D) (charge : Charge D)
    (hd : 0 < d) (hs : 0 < s) (hsq : s < q)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hk : k < 0)
    (hu : u ∈ grade D (r - d * s ^ 2))
    (hv : v ∈ grade D (t - d * (q - s) ^ 2))
    (hcharge : energy D (charge, 0) = -d * q ^ 2) :
    groundCoefficient D charge (((Y D u)[[k]]) v) = 0 := by
  apply groundCoefficient_mode_eq_zero_of_grade_mismatch D
      (r - d * s ^ 2) (t - d * (q - s) ^ 2) k charge u v hu hv
  rw [hcharge]
  exact negative_rank_one_outer_energy_mismatch d s q r t k hd hs hsq hr ht hk

/-- The actual even rank-one datum; positivity of d is used only in the theorem. -/
def datum (d : ℕ) : LatticeData where
  rank := 1
  G := fun _ _ => -2 * (d : ℤ)
  symmetric := by intros; rfl
  even_diagonal := by intro i; exact ⟨-(d : ℤ), by ring⟩

def charge (d : ℕ) (s : ℤ) : Charge (datum d) := fun _ => s

@[simp] private theorem charge_add (d : ℕ) (s t : ℤ) :
    charge d s + charge d t = charge d (s + t) := rfl

@[simp] private theorem charge_zero (d : ℕ) : charge d 0 = 0 := rfl

private theorem charge_eq (d : ℕ) (a : Charge (datum d)) :
    a = charge d (a 0) := by
  funext i
  exact congrArg a (Subsingleton.elim i 0)

@[simp] private theorem charge_inj (d : ℕ) (s t : ℤ) :
    charge d s = charge d t ↔ s = t := by
  constructor
  · intro h; exact congrFun h 0
  · rintro rfl; rfl

private theorem bilinear_charge (d : ℕ) (s t : ℤ) :
    bilinear (datum d) (charge d s) (charge d t) = -2 * (d : ℤ) * s * t := by
  simp [bilinear, datum, charge, Fin.sum_univ_one]
  ring

private theorem charge_energy (d : ℕ) (s : ℤ) :
    chargeEnergy (datum d) (charge d s) = -(d : ℤ) * s ^ 2 := by
  have h := two_chargeEnergy (datum d) (charge d s)
  rw [bilinear_charge] at h
  nlinarith

private theorem basis_energy (d : ℕ) (s : ℤ) (e : Exponent (datum d)) :
    energy (datum d) (charge d s, e) =
      (oscillatorEnergy e : ℤ) - (d : ℤ) * s ^ 2 := by
  simp [energy, charge_energy]; ring

private theorem basis_grade (D : LatticeData) (a : Label D) :
    carrierBasis D a ∈ grade D (energy D a) := by
  rw [grade_eq_span]
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

private def mode (D : LatticeData) (k : ℤ) :
    Carrier D →ₗ[ℂ] Module.End ℂ (Carrier D) where
  toFun u := ((Y D u)[[k]])
  map_add' u v := by simp
  map_smul' c u := by simp

private theorem basis_outer_zero (d : ℕ) (hd : 0 < d) (s q k : ℤ)
    (hs : 0 ≤ s) (hsq : s < q) (hk : k < 0)
    (e : Exponent (datum d)) (he : 0 < s ∨ e ≠ 0)
    (a : Label (datum d)) :
    groundCoefficient (datum d) (charge d q)
      (mode (datum d) k (carrierBasis (datum d) (charge d s, e))
        (carrierBasis (datum d) a)) = 0 := by
  classical
  obtain ⟨β, f⟩ := a
  by_cases hb : β = charge d (q - s)
  · subst β
    apply groundCoefficient_mode_eq_zero_of_grade_mismatch (datum d)
      (energy (datum d) (charge d s, e))
      (energy (datum d) (charge d (q-s), f)) k (charge d q)
      _ _ (basis_grade _ _) (basis_grade _ _)
    rw [basis_energy, basis_energy, basis_energy]
    simp only [oscillatorEnergy_eq_zero_iff, Nat.cast_zero, zero_sub]
    rcases he with hp | hp
    · exact negative_rank_one_outer_energy_mismatch (d : ℤ) s q
        (oscillatorEnergy e) (oscillatorEnergy f) k (by omega) hp hsq
        (by positivity) (by positivity) hk
    · by_cases hp' : 0 < s
      · exact negative_rank_one_outer_energy_mismatch (d : ℤ) s q
          (oscillatorEnergy e) (oscillatorEnergy f) k (by omega) hp' hsq
          (by positivity) (by positivity) hk
      · have hz : s = 0 := by omega
        have hr : 0 < oscillatorEnergy e :=
          Nat.pos_of_ne_zero (fun h => hp ((oscillatorEnergy_eq_zero_iff _ _).mp h))
        subst s
        have ht : (0 : ℤ) ≤ oscillatorEnergy f := by positivity
        norm_num
        omega
  · rw [carrierBasis_apply, carrierBasis_apply]
    change groundCoefficient (datum d) (charge d q)
      (((Y (datum d) (Finsupp.single (charge d s) (MvPolynomial.monomial e 1)))[[k]])
        (Finsupp.single β (MvPolynomial.monomial f 1))) = 0
    rw [LatticeSectorIntertwiner.charge_homogeneity, groundCoefficient_apply,
      Finsupp.single_eq_of_ne]
    · simp
    · intro h
      apply hb
      ext i
      have hi := congrFun h i
      change s + β i = q at hi
      change β i = q - s
      omega

private theorem outer_positive (d : ℕ) (hd : 0 < d) (s q k : ℤ)
    (hs : 0 < s) (hsq : s < q) (hk : k < 0)
    (p : Oscillator (datum d)) (v : Carrier (datum d)) :
    groundCoefficient (datum d) (charge d q)
      (mode (datum d) k (Finsupp.single (charge d s) p) v) = 0 := by
  let L : Oscillator (datum d) →ₗ[ℂ] Carrier (datum d) →ₗ[ℂ] ℂ :=
    { toFun := fun p => (groundCoefficient (datum d) (charge d q)).comp
        (mode (datum d) k (Finsupp.single (charge d s) p))
      map_add' := by intros; ext; simp [mode]
      map_smul' := by intros; ext; simp [mode] }
  have hL : L = 0 := by
    apply (MvPolynomial.basisMonomials (Index (datum d)) ℂ).ext
    intro e
    apply (carrierBasis (datum d)).ext
    intro a
    exact basis_outer_zero d hd s q k hs.le hsq hk e (Or.inl hs) a
  exact congrArg (fun f => f p v) hL

/-- A palette letter retains an arbitrary oscillator polynomial and integer mode. -/
structure Letter (d : ℕ) where
  weight : ℤ
  polynomial : Oscillator (datum d)
  index : ℤ

private def letterState {d : ℕ} (a : Letter d) : Carrier (datum d) :=
  Finsupp.single (charge d a.weight) a.polynomial

private def wordOperator {d : ℕ} : List (Letter d) → Module.End ℂ (Carrier (datum d))
  | [] => LinearMap.id
  | a :: w => mode (datum d) a.index (letterState a) * wordOperator w

private def paletteWord {d : ℕ} (w : List (Letter d)) : Carrier (datum d) :=
  wordOperator w (vacuum (datum d))

private def Good {d : ℕ} (M : ℤ) (w : List (Letter d)) : Prop :=
  ∀ a ∈ w, -M ≤ a.weight ∧ a.weight ≤ M ∧ a.index < 0

end
end D5.S3.VertexAlgebra.Lattice.NegativeRankOneStrongGeneration

