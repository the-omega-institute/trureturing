/- GID: D5/S3/Quantum/Transport/MatrixUnitGenerator
   generality: G
   mirror-B: D5/B/S3/Quantum/Transport/MatrixUnitGenerator
   mirror-E: none(waiver:finite-differential-algebra)
   anchors: []
   digest: A computed averaged matrix-unit derivative generates the complete moving logical algebra; a real-path adapter derives every tangent hypothesis. -/

import D5.S3.Quantum.Recovery.MatrixUnitDecoder
import Mathlib

/-!
# Transport of the whole logical algebra

The matrix-unit support owner is reused. The generator is computed from F and
its velocity D; skew-adjointness and all commutator equations are conclusions.
The second theorem obtains the tangent relations from actual entrywise real
`HasDerivAt` proofs. No transport solution, unitary propagator, or Dyson-series
convergence is assumed or claimed here. The d=1 projector mechanism is the
classical Kato transport mechanism; the finite-algebra calculation below fixes
all logical matrix units simultaneously.
-/

noncomputable section
open scoped Matrix BigOperators

namespace D5.S3.Quantum.Transport.MatrixUnitGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Recovery.MatrixUnitDecoder

variable {d n : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
  [Fintype n] [DecidableEq n]

/-- The support velocity computed from the diagonal matrix-unit velocities. -/
def supportVelocity (D : d → d → Matrix n n ℂ) : Matrix n n ℂ := ∑ i, D i i

/-- The separability average over all logical matrix units. -/
def averagedVelocity (F D : d → d → Matrix n n ℂ) : Matrix n n ℂ :=
  (Fintype.card d : ℂ)⁻¹ • ∑ i, ∑ j, D i j * F j i

/-- The support-corrected generator, with no unspecified inner derivation witness. -/
def transportGenerator (F D : d → d → Matrix n n ℂ) : Matrix n n ℂ :=
  averagedVelocity F D - unitSupport F * supportVelocity D

/-- Differentiated matrix-unit and star relations force the explicit transport generator. -/
theorem matrix_unit_transport_generator (F D : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i)
    (hD : ∀ i j k l, D i j * F k l + F i j * D k l =
      if j = k then D i l else 0)
    (hDstar : ∀ i j, (D i j)ᴴ = D j i) :
    (transportGenerator F D)ᴴ = -transportGenerator F D ∧
      (∀ i j, transportGenerator F D * F i j - F i j * transportGenerator F D = D i j) ∧
      transportGenerator F D * unitSupport F - unitSupport F * transportGenerator F D =
        supportVelocity D := by
  let P := unitSupport F
  let V := supportVelocity D
  let R := ∑ i, ∑ j, D i j * F j i
  let Z := averagedVelocity F D
  have hn : (Fintype.card d : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨hPstar, hPP⟩ := unit_support_projection F hmul hstar
  have hPF (i j : d) : P * F i j = F i j := (unit_support_action F hmul i j).1
  have hFP (i j : d) : F i j * P = F i j := (unit_support_action F hmul i j).2
  have hVstar : Vᴴ = V := by simp only [V, supportVelocity, Matrix.conjTranspose_sum, hDstar]
  have hright (i j : d) : D i j * P + F i j * V = D i j := by
    calc
      _ = ∑ k, (D i j * F k k + F i j * D k k) := by
        simp only [P, V, unitSupport, supportVelocity, Matrix.mul_sum, Finset.sum_add_distrib]
      _ = ∑ k, if j = k then D i k else 0 := by simp_rw [hD]
      _ = D i j := by simp
  have hPV : V * P + P * V = V := by
    calc
      _ = ∑ i, (D i i * P + F i i * V) := by
        simp only [V, P, supportVelocity, unitSupport,
          Matrix.mul_sum, Matrix.sum_mul, Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_comm
      _ = V := by simp_rw [hright]; rfl
  have hcorner : P * V * P = 0 := by
    have hh := congrArg (fun A : Matrix n n ℂ => P * A) hPV
    have hPVV : P * (P * V) = P * V := by rw [← Matrix.mul_assoc, hPP]
    simp only [Matrix.mul_add] at hh
    rw [hPVV] at hh
    have hh' : P * V * P + P * V = P * V := by
      simpa only [Matrix.mul_add, ← Matrix.mul_assoc] using hh
    exact add_right_cancel (show P * V * P + P * V = 0 + P * V by simpa using hh')
  have hmean (A : d → Matrix n n ℂ) :
      (Fintype.card d : ℂ)⁻¹ • (∑ i, ∑ _j : d, A i) = ∑ i, A i := by
    simp only [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (R := ℂ), ← Finset.smul_sum,
      smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hRstar : R + Rᴴ = ∑ i, ∑ _j : d, D i i := by
    simp only [R, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, hstar, hDstar]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simpa using hD i j j i
  have hZstar : Z + Zᴴ = V := by
    calc
      _ = (Fintype.card d : ℂ)⁻¹ • (R + Rᴴ) := by
        simp only [Z, averagedVelocity, R, Matrix.conjTranspose_inv_natCast_smul, smul_add]
      _ = (Fintype.card d : ℂ)⁻¹ • (∑ i, ∑ _j : d, D i i) := by rw [hRstar]
      _ = V := hmean (fun i => D i i)
  have hRright (k l : d) : R * F k l = ∑ j, D k j * F j l := by
    simp [R, Matrix.sum_mul, Matrix.mul_assoc, hmul, mul_ite]
  have hderiv_left (k l i j : d) :
      F k l * D i j = (if l = i then D k j else 0) - D k l * F i j := by
    calc
      _ = (D k l * F i j + F k l * D i j) - D k l * F i j := by abel
      _ = _ := by rw [hD]
  have hRleft (k l : d) :
      F k l * R = (∑ j, D k j * F j l) - (Fintype.card d : ℂ) • (D k l * P) := by
    calc
      _ = ∑ i, ∑ j, ((if l = i then D k j else 0) - D k l * F i j) * F j i := by
        simp only [R, Matrix.mul_sum, ← Matrix.mul_assoc, hderiv_left]
      _ = (∑ i, ∑ j, (if l = i then D k j else 0) * F j i) -
          (∑ i, ∑ j, (D k l * F i j) * F j i) := by
        simp only [Matrix.sub_mul, Finset.sum_sub_distrib]
      _ = (∑ j, D k j * F j l) - (Fintype.card d : ℂ) • (D k l * P) := by
        congr 1
        · simp [ite_mul]
        · simp only [Matrix.mul_assoc, hmul, if_true,
            Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (R := ℂ)]
          simp only [P, unitSupport, Matrix.mul_sum, Finset.smul_sum]
  have hZcomm (i j : d) : Z * F i j - F i j * Z = D i j * P := by
    calc
      _ = (Fintype.card d : ℂ)⁻¹ • (R * F i j - F i j * R) := by
        simp only [Z, averagedVelocity, R, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      _ = (Fintype.card d : ℂ)⁻¹ • ((Fintype.card d : ℂ) • (D i j * P)) := by
        rw [hRright, hRleft]
        congr 1
        abel
      _ = D i j * P := by rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hnormal (i j : d) : P * V * F i j = 0 := by
    calc
      _ = (P * V * P) * F i j := by simp only [Matrix.mul_assoc, hPF]
      _ = 0 := by rw [hcorner, Matrix.zero_mul]
  have hKsum : (Z - P * V) + (Z - P * V)ᴴ = 0 := by
    have hPstar' : Pᴴ = P := hPstar
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPstar', hVstar]
    calc
      _ = (Z + Zᴴ) - (V * P + P * V) := by abel
      _ = 0 := by rw [hZstar, hPV, sub_self]
  have hKstar : (Z - P * V)ᴴ = -(Z - P * V) := by
    calc
      _ = ((Z - P * V) + (Z - P * V)ᴴ) - (Z - P * V) := by abel
      _ = _ := by rw [hKsum]; simp
  have hKcomm (i j : d) :
      (Z - P * V) * F i j - F i j * (Z - P * V) = D i j := by
    calc
      _ = (Z * F i j - F i j * Z) - (P * V * F i j - F i j * P * V) := by
        noncomm_ring
      _ = D i j * P + F i j * V := by rw [hZcomm, hnormal, hFP]; abel
      _ = D i j := hright i j
  refine ⟨hKstar, hKcomm, ?_⟩
  change (Z - P * V) * (∑ i, F i i) - (∑ i, F i i) * (Z - P * V) = ∑ i, D i i
  simp only [Matrix.mul_sum, Matrix.sum_mul, ← Finset.sum_sub_distrib, hKcomm]

/-- For an actual differentiable real path, the product and adjoint tangent hypotheses are derived by derivative uniqueness. -/
theorem generator_from_real_path (F : ℝ → d → d → Matrix n n ℂ)
    (D : d → d → Matrix n n ℂ) (t : ℝ)
    (hmul : ∀ u i j k l, F u i j * F u k l = if j = k then F u i l else 0)
    (hstar : ∀ u i j, (F u i j)ᴴ = F u j i)
    (hderiv : ∀ i j a b, HasDerivAt (fun u => F u i j a b) (D i j a b) t) :
    (transportGenerator (F t) D)ᴴ = -transportGenerator (F t) D ∧
      (∀ i j, transportGenerator (F t) D * F t i j - F t i j * transportGenerator (F t) D = D i j) ∧
      transportGenerator (F t) D * unitSupport (F t) -
        unitSupport (F t) * transportGenerator (F t) D = supportVelocity D := by
  have hD (i j k l : d) :
      D i j * F t k l + F t i j * D k l = if j = k then D i l else 0 := by
    ext a b
    have hh := HasDerivAt.fun_sum (u := Finset.univ)
      (fun c _ => (hderiv i j a c).mul (hderiv k l c b))
    have hp : HasDerivAt (fun u => (F u i j * F u k l) a b)
        ((D i j * F t k l + F t i j * D k l) a b) t := by
      simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib,
        Pi.mul_apply] using hh
    simp_rw [hmul] at hp
    by_cases h : j = k
    · simp only [if_pos h] at hp ⊢
      exact hp.unique (hderiv i l a b)
    · simp only [if_neg h, Matrix.zero_apply] at hp ⊢
      exact hp.unique (hasDerivAt_const t (0 : ℂ))
  have hDs (i j : d) : (D i j)ᴴ = D j i := by
    ext a b
    have hh := (hderiv i j b a).star
    have heq : (fun u => star (F u i j b a)) = (fun u => F u j i a b) := by
      funext u
      exact congrArg (fun M : Matrix n n ℂ => M a b) (hstar u i j)
    rw [heq] at hh
    exact hh.unique (hderiv j i a b)
  exact matrix_unit_transport_generator (F t) D (hmul t) (hstar t) hD hDs

#print axioms matrix_unit_transport_generator
#print axioms generator_from_real_path

end D5.S3.Quantum.Transport.MatrixUnitGenerator
