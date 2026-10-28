/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarRadial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorScalarRadial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual scalar lattice products share an absolutely evaluated radial fraction. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
import D5.S3.VertexAlgebra.SupportedWordRationalCollision
import D5.S3.VertexAlgebra.CollisionAnalytic.AbsoluteEvaluation

/-!
The finite numerator is extracted from the actual lattice fields. Finite
convolution identifies their supported Hahn carriers before analytic evaluation.
Mathlib's Hahn series, multivariate polynomials and vertex operators retain their
original authorship and Apache 2.0 license in the imported suppliers.

proof_shape: content
admission_basis: escape-witness
escape_witness: the natural finite polynomial embeds into the signed labelled
Laurent algebra with its exact zero-extended coefficients; finite binomial
convolution and the original canonical charge inclusions identify the two
supported actual carriers with one fixed-label fraction. Its absolutely
summable numerical coefficients are the literal original scalar modes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorScalarRadial
open LatticeGeneratingFieldLocality LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorScalarNumerator LatticeSugawaraCurrents SupportedChannelSeries
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.FiniteConvolution SupportedFieldWords.ActualFieldWordAdapter
open SupportedWordRationalCollision.ActualPolynomialBridge
open UniformGradedLocalCorrelator CollisionAbsoluteEvaluation.Labelled
open scoped BigOperators VertexOperator
noncomputable section

private def naturalExponent : (Fin 2 →₀ ℕ) →+ (Fin 2 → ℤ) where
  toFun d i := d i
  map_zero' := by ext i; simp
  map_add' d e := by ext i; simp

private theorem naturalExponent_injective : Function.Injective naturalExponent := by
  intro d e h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

private def polynomialLaurent : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] LabelledPolynomial ℂ 2 :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ naturalExponent

private theorem polynomialLaurent_coeff (R : MvPolynomial (Fin 2) ℂ) (e : Fin 2 → ℤ) :
    (polynomialLaurent R).coeff e = extend (R : MvPowerSeries (Fin 2) ℂ) (e 0) (e 1) := by
  classical
  change (Finsupp.mapDomain naturalExponent R.coeff) e = _
  by_cases he : 0 ≤ e 0 ∧ 0 ≤ e 1
  · have hd : naturalExponent (powerIndex (e 0).toNat (e 1).toNat) = e := by
      ext i
      fin_cases i <;> simp [naturalExponent, powerIndex, he.1, he.2]
    calc
      (Finsupp.mapDomain naturalExponent R.coeff) e =
          (Finsupp.mapDomain naturalExponent R.coeff)
            (naturalExponent (powerIndex (e 0).toNat (e 1).toNat)) := congrArg _ hd.symm
      _ = R.coeff (powerIndex (e 0).toNat (e 1).toNat) :=
        Finsupp.mapDomain_apply_of_injective naturalExponent_injective _ _
      _ = _ := by simp [extend, he, MvPolynomial.coeff_coe]
  · rw [extend, ite_eq_right he]
    by_contra hn
    have hs := Finsupp.mem_support_iff.mpr hn
    rw [Finsupp.mapDomain_support_of_injective naturalExponent_injective] at hs
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hs
    apply he
    rw [← hd]
    constructor <;> exact Int.natCast_nonneg _

private theorem pairs_two : labelledPairs 2 = {(0, 1)} := by decide

private theorem polynomialLaurent_eq_aeval : polynomialLaurent =
    MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i) := by
  apply MvPolynomial.algHom_ext
  intro i
  change AddMonoidAlgebra.mapDomain naturalExponent (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X]
  change AddMonoidAlgebra.mapDomain naturalExponent
    (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  ext j
  by_cases h : i = j <;> simp [naturalExponent, h]

private theorem pair_power_action (N : ℕ) (F : (Fin 2 → ℤ) → ℂ) (e : Fin 2 → ℤ) :
    distributionAction (pairPolynomial (0 : Fin 2) 1 ^ N) F e =
      clear N (fun a b => F ![a, b]) (e 0) (e 1) := by
  classical
  rw [show pairPolynomial (0 : Fin 2) 1 =
    -variablePolynomial 1 + variablePolynomial 0 by unfold pairPolynomial; abel,
    add_pow, clear]
  simp only [map_sum, LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [show -variablePolynomial (1 : Fin 2) =
    AddMonoidAlgebra.single (Pi.single 1 1) (-1 : ℂ) by simp [variablePolynomial] ]
  simp only [variablePolynomial, AddMonoidAlgebra.single_pow, one_pow,
    AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single,
    mul_one, add_zero, distributionAction_single]
  have harg : e - (k • Pi.single (1 : Fin 2) 1 + (N - k) • Pi.single 0 1) =
      ![e 0 - N + k, e 1 - k] := by
    ext i
    fin_cases i <;> simp [Nat.cast_sub hkN]
    all_goals omega
  simp only [harg]

private theorem product_coeff (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (e : Fin 2 → ℤ) :
    (scalarWordCarrier 2
      ![LatticeAllStateField.Y D (inclusion D α u), LatticeAllStateField.Y D (inclusion D β v)]
      (1 : Equiv.Perm (Fin 2)) (inclusion D γ w)
      ((readout D p).comp (projection D (α + (β + γ))))).coeff
        (orderExponents 2 1 e) = readout D p (product D α β γ u v w (e 0) (e 1)) := by
  rw [show orderExponents 2 1 e = exponents 2 (fun i => e ((1 : Equiv.Perm (Fin 2)) i)) by rfl]
  rw [scalarWordCarrier_coeff 2 _ (1 : Equiv.Perm (Fin 2)) _ _ e]
  change readout D p (projection D (α + (β + γ))
    (((LatticeAllStateField.Y D (inclusion D α u))[[-e 0 - 1]])
      (((LatticeAllStateField.Y D (inclusion D β v))[[-e 1 - 1]]) (inclusion D γ w)))) = _
  rw [← inclusion_canonical D β γ v w (-e 1 - 1),
    ← inclusion_canonical D α (β + γ) u (canonical D β γ v (-e 1 - 1) w) (-e 0 - 1)]
  change readout D p (Finsupp.single (α + (β + γ))
    (product D α β γ u v w (e 0) (e 1)) (α + (β + γ))) = _
  rw [Finsupp.single_eq_same]

private theorem reverse_coeff (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (e : Fin 2 → ℤ) :
    (scalarWordCarrier 2
      ![LatticeAllStateField.Y D (inclusion D α u), LatticeAllStateField.Y D (inclusion D β v)]
      (Equiv.swap (0 : Fin 2) 1) (inclusion D γ w)
      ((readout D p).comp (projection D (α + (β + γ))))).coeff
        (orderExponents 2 (Equiv.swap 0 1) e) =
      readout D p (reverseProduct D α β γ u v w (e 0) (e 1)) := by
  change (scalarWordCarrier 2 _ _ _ _).coeff
    (exponents 2 (fun i => e (Equiv.swap 0 1 i))) = _
  rw [scalarWordCarrier_coeff 2 _ _ _ _ e]
  change readout D p (projection D (α + (β + γ))
    (((LatticeAllStateField.Y D (inclusion D β v))[[-e 1 - 1]])
      (((LatticeAllStateField.Y D (inclusion D α u))[[-e 0 - 1]]) (inclusion D γ w)))) = _
  rw [← inclusion_canonical, ← inclusion_canonical]
  have hcharge : β + (α + γ) = α + (β + γ) := by abel
  simp [projection, inclusion, reverseProduct, hcharge]

private theorem rational_of_clear (sigma : Equiv.Perm (Fin 2))
    (S : HahnSeries (Indices 2) ℂ) (f : ℤ → ℤ → ℂ)
    (N A B : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (coeff : ∀ e, S.coeff (orderExponents 2 sigma e) = f (e 0) (e 1))
    (common : ∀ a b : ℤ, clear N f (a - A) (b - B) =
      extend (R : MvPowerSeries (Fin 2) ℂ) a b) :
    let L := AddMonoidAlgebra.single ![-(A : ℤ), -(B : ℤ)] (1 : ℂ) *
      MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i) R
    S = orderedRationalFor ℂ 2 sigma
      (algebraMap _ (CommonRational ℂ 2) L /
        algebraMap _ (CommonRational ℂ 2) (pairPolynomial (0 : Fin 2) 1 ^ N)) := by
  classical
  dsimp only
  have hmul : orderedPolynomialFor ℂ 2 sigma (pairPolynomial (0 : Fin 2) 1 ^ N) * S =
      orderedPolynomialFor ℂ 2 sigma
        (AddMonoidAlgebra.single ![-(A : ℤ), -(B : ℤ)] (1 : ℂ) * polynomialLaurent R) := by
    ext g
    obtain ⟨e, rfl⟩ := (orderExponents 2 sigma).surjective g
    rw [ordered_mul_coeff, ordered_polynomial_coeff, pair_power_action]
    simp_rw [coeff]
    rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, polynomialLaurent_coeff]
    convert common (e 0 + A) (e 1 + B) using 1 <;> simp [add_comm]
  have hQ : pairPolynomial (0 : Fin 2) 1 ^ N ≠ 0 := by
    have h := SupportedWordRationalCollision.ActualRationalReconstruction.originalQ_ne_zero 2 0 N
    simpa only [clearingPolynomial, pairs_two, Finset.prod_singleton] using h
  have hne : orderedPolynomialFor ℂ 2 sigma (pairPolynomial (0 : Fin 2) 1 ^ N) ≠ 0 := by
    simpa only [map_zero] using (orderedPolynomialFor_injective ℂ 2 sigma).ne hQ
  rw [map_div₀]
  simp only [orderedRationalFor, IsFractionRing.lift_algebraMap]
  apply (eq_div_iff hne).mpr
  rw [mul_comm, ← polynomialLaurent_eq_aeval]
  exact hmul

open private monomial_zero monomial_add monomial_unit from
  D5.S3.VertexAlgebra.CollisionAnalytic.AbsoluteEvaluation

private def valueHom (z : Fin 2 → ℂ) (hz : ∀ i, z i ≠ 0) : LabelledPolynomial ℂ 2 →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin 2 → ℤ)
    { toFun := fun e => monomial z e.toAdd
      map_one' := monomial_zero z
      map_mul' := fun e f => monomial_add z hz e.toAdd f.toAdd }

private theorem valueHom_eq (z : Fin 2 → ℂ) (hz : ∀ i, z i ≠ 0)
    (L : LabelledPolynomial ℂ 2) : valueHom z hz L = laurentValue L z := by
  simp only [valueHom, AddMonoidAlgebra.lift_apply, laurentValue, Finsupp.sum,
    smul_eq_mul, MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

private theorem laurent_numerator_value (A B : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    laurentValue (AddMonoidAlgebra.single ![-(A : ℤ), -(B : ℤ)] (1 : ℂ) *
      MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i) R) ![x, y] =
      MvPolynomial.eval ![x, y] R / (x ^ A * y ^ B) := by
  have hz : ∀ i, (![x, y] : Fin 2 → ℂ) i ≠ 0 := by
    intro i; fin_cases i <;> assumption
  rw [← valueHom_eq _ hz, map_mul]
  have hpoly : (valueHom ![x, y] hz).comp
      (MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i)) =
      MvPolynomial.aeval (![x, y] : Fin 2 → ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [valueHom, variablePolynomial, AddMonoidAlgebra.lift_single, monomial_unit]
  have heval := DFunLike.congr_fun hpoly R
  change valueHom ![x, y] hz (MvPolynomial.aeval _ R) = MvPolynomial.eval ![x, y] R at heval
  rw [heval]
  simp [valueHom, AddMonoidAlgebra.lift_single, monomial, Fin.prod_univ_two,
    zpow_neg, div_eq_mul_inv, mul_comm]

private theorem absolute_of_rational (sigma : Equiv.Perm (Fin 2))
    (S : HahnSeries (Indices 2) ℂ) (f : ℤ → ℤ → ℂ)
    (N A B : ℕ) (R : MvPolynomial (Fin 2) ℂ)
    (coeff : ∀ e, S.coeff (orderExponents 2 sigma e) = f (e 0) (e 1))
    (rational : S = orderedRationalFor ℂ 2 sigma
      (algebraMap _ (CommonRational ℂ 2)
        (AddMonoidAlgebra.single ![-(A : ℤ), -(B : ℤ)] (1 : ℂ) *
          MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i) R) /
        algebraMap _ (CommonRational ℂ 2) (pairPolynomial (0 : Fin 2) 1 ^ N)))
    (x y : ℂ) (hz : RadialChamber sigma ![x, y]) :
    Summable (fun e : Fin 2 → ℤ => ‖f (e 0) (e 1) * x ^ e 0 * y ^ e 1‖) ∧
    HasSum (fun e : Fin 2 → ℤ => f (e 0) (e 1) * x ^ e 0 * y ^ e 1)
      (MvPolynomial.eval ![x, y] R / (x ^ A * y ^ B * (x - y) ^ N)) ∧
    (∑' e : Fin 2 → ℤ, ‖f (e 0) (e 1) * x ^ e 0 * y ^ e 1‖) ≤
      laurentMajorant (AddMonoidAlgebra.single ![-(A : ℤ), -(B : ℤ)] (1 : ℂ) *
        MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i) R) ![x, y] *
          |‖x‖ - ‖y‖|⁻¹ ^ N := by
  have h := collision_absolute_evaluation sigma
    (AddMonoidAlgebra.single ![-(A : ℤ), -(B : ℤ)] (1 : ℂ) *
      MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i) R)
    (fun _ => N) ![x, y] hz
  dsimp only at h
  simp only [pairs_two, Finset.prod_singleton] at h
  rw [← rational] at h
  simp_rw [coeff] at h
  simpa [monomial, Fin.prod_univ_two, ← mul_assoc,
    laurent_numerator_value A B R x y (hz.1 0) (hz.1 1), div_div] using h.2

private theorem chamber_id (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hlt : ‖y‖ < ‖x‖) :
    RadialChamber (1 : Equiv.Perm (Fin 2)) ![x, y] := by
  constructor
  · intro i; fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem chamber_swap (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hlt : ‖x‖ < ‖y‖) :
    RadialChamber (Equiv.swap (0 : Fin 2) 1) ![x, y] := by
  constructor
  · intro i; fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

set_option maxHeartbeats 800000 in
-- The supported-carrier comparisons elaborate two native Hahn fraction embeddings.
/-- The literal two actual ordered scalar carriers expand one finite fraction,
whose original scalar mode coefficients evaluate absolutely in both chambers. -/
theorem ordinary_actual_scalar_radial_rationality
    (D : LatticeData) (J : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hJG : J * gramComplex D = 1) (hGJ : gramComplex D * J = 1)
    (α β : Charge D) (u : Sector D α) (v : Sector D β) :
    ∃ N : ℕ, ∀ (γ : Charge D) (w : Sector D γ), ∃ A B : ℕ,
      ∃ P : MvPowerSeries (Fin 2) (Oscillator D),
      ∀ p : Oscillator D, ∃ R : MvPolynomial (Fin 2) ℂ,
        (R : MvPowerSeries (Fin 2) ℂ) = mapSeries (readout D p) P ∧
        R.totalDegree ≤ (degreeBound D α β γ A B N p).toNat ∧
        let C := ![LatticeAllStateField.Y D (inclusion D α u),
          LatticeAllStateField.Y D (inclusion D β v)]
        let phi := (readout D p).comp (projection D (α + (β + γ)))
        let L := AddMonoidAlgebra.single ![-(A : ℤ), -(B : ℤ)] (1 : ℂ) *
          MvPolynomial.aeval (fun i : Fin 2 => variablePolynomial i) R
        let Q : CommonRational ℂ 2 := algebraMap _ _ L /
          algebraMap _ _ (pairPolynomial (0 : Fin 2) 1 ^ N)
        scalarWordCarrier 2 C (1 : Equiv.Perm (Fin 2)) (inclusion D γ w) phi =
          orderedRationalFor ℂ 2 1 Q ∧
        scalarWordCarrier 2 C (Equiv.swap (0 : Fin 2) 1) (inclusion D γ w) phi =
          orderedRationalFor ℂ 2 (Equiv.swap 0 1) Q ∧
        ∀ (x y : ℂ), x ≠ 0 → y ≠ 0 →
          (‖y‖ < ‖x‖ →
            Summable (fun e : Fin 2 → ℤ =>
              ‖readout D p (product D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1‖) ∧
            HasSum (fun e : Fin 2 → ℤ =>
              readout D p (product D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1)
              (MvPolynomial.eval ![x, y] R / (x ^ A * y ^ B * (x - y) ^ N)) ∧
            (∑' e : Fin 2 → ℤ,
              ‖readout D p (product D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1‖) ≤
              laurentMajorant L ![x, y] * |‖x‖ - ‖y‖|⁻¹ ^ N) ∧
          (‖x‖ < ‖y‖ →
            Summable (fun e : Fin 2 → ℤ =>
              ‖readout D p (reverseProduct D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1‖) ∧
            HasSum (fun e : Fin 2 → ℤ =>
              readout D p (reverseProduct D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1)
              (MvPolynomial.eval ![x, y] R / (x ^ A * y ^ B * (x - y) ^ N)) ∧
            (∑' e : Fin 2 → ℤ,
              ‖readout D p (reverseProduct D α β γ u v w (e 0) (e 1)) * x ^ e 0 * y ^ e 1‖) ≤
              laurentMajorant L ![x, y] * |‖x‖ - ‖y‖|⁻¹ ^ N) := by
  obtain ⟨N, _locality, _uv, rest⟩ :=
    ordinary_actual_finite_scalar_numerator D J hJG hGJ α β u v
  refine ⟨N, ?_⟩
  intro γ w
  obtain ⟨A, B, P, _uw, _vw, _common, tests⟩ := rest γ w
  refine ⟨A, B, P, ?_⟩
  intro p
  obtain ⟨R, ⟨heq, hdeg, _negative, scalar⟩, _unique⟩ := tests p
  refine ⟨R, heq, hdeg, ?_⟩
  let C : Fin 2 → VertexOperator ℂ (Carrier D) :=
    ![LatticeAllStateField.Y D (inclusion D α u), LatticeAllStateField.Y D (inclusion D β v)]
  let phi := (readout D p).comp (projection D (α + (β + γ)))
  let Sp := scalarWordCarrier 2 C (1 : Equiv.Perm (Fin 2)) (inclusion D γ w) phi
  let Sr := scalarWordCarrier 2 C (Equiv.swap (0 : Fin 2) 1) (inclusion D γ w) phi
  let fp := fun a b => readout D p (product D α β γ u v w a b)
  let fr := fun a b => readout D p (reverseProduct D α β γ u v w a b)
  have cp : ∀ e, Sp.coeff (orderExponents 2 1 e) = fp (e 0) (e 1) :=
    product_coeff D α β γ u v w p
  have cr : ∀ e, Sr.coeff (orderExponents 2 (Equiv.swap 0 1) e) = fr (e 0) (e 1) :=
    reverse_coeff D α β γ u v w p
  have hp := rational_of_clear 1 Sp fp N A B R cp (fun a b => (scalar a b).1)
  have hr := rational_of_clear (Equiv.swap 0 1) Sr fr N A B R cr
    (fun a b => (scalar a b).2.1)
  refine ⟨hp, hr, ?_⟩
  intro x y hx hy
  constructor
  · intro hlt
    exact absolute_of_rational 1 Sp fp N A B R cp hp x y (chamber_id x y hx hy hlt)
  · intro hlt
    exact absolute_of_rational (Equiv.swap 0 1) Sr fr N A B R cr hr x y
      (chamber_swap x y hx hy hlt)

end
end D5.S3.VertexAlgebra.LatticeSectorScalarRadial
