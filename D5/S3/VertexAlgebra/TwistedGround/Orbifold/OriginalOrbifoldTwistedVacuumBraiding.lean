/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumBraiding
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumBraiding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient skew reversal is the identity on the negative twisted vacuum channel. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumRigidity
import D5.S3.VertexAlgebra.StateField.SkewSymmetry

/-! The projected all-state skew law and scalar rigidity determine the exchange
of every lawful negative twisted pair with fixed-sector output. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumBraiding

noncomputable section
open scoped BigOperators VertexOperator

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (fixedTranslation)
open OriginalOrbifoldVertexAlgebra (originalVertexAlgebra)
open OriginalOrbifoldTwistedVacuumFusion
  (NegativeTwisted FixedLeech operatorSpace canonicalField canonicalIntertwiner
    canonical_mode_projected canonical_mode_nonintegral)
open VacuumFirstIntertwinerDraft (mode rationalMode_int)
open private intertwiner_eq_smul_canonical from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumRigidity
open private nonintegral_shift from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion

local notation "D" => leechData
local notation "X" => NegativeTwisted
local notation "V" => FixedLeech
private abbrev originalVOA :=
  originalVertexAlgebra D leech_spec.2.1 leech_spec.2.2.1 leech_spec.1

local notation "A" => originalVOA

private abbrev projection : OriginalOrbifoldField.Carrier D leech_spec.2.1 →ₗ[ℂ] V :=
  LinearMap.fst ℂ V X

set_option maxHeartbeats 800000 in
-- The power step compares endomorphisms on the assembled and fixed carriers.
private theorem project_translation_pow (j : ℕ)
    (w : OriginalOrbifoldField.Carrier D leech_spec.2.1) :
    projection (((A).translation ^ j) w) = (fixedTranslation D ^ j) (projection w) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply]
    change (OriginalOrbifoldTranslation.T D leech_spec.2.1 (((A).translation ^ j) w)).1 = _
    rw [OriginalOrbifoldTranslation.T_apply]
    exact congrArg (fixedTranslation D) ih

private theorem mode_smul (c : ℂ) (J : operatorSpace) (u v : X) (q : ℚ) :
    mode (c • J).val u q v = c • mode J.val u q v := by
  change mode (c • J.val) u q v = _
  simp [mode]

/-- Every lawful field vanishes at every rational mode outside the image of ℤ. -/
theorem mode_nonintegral (J : operatorSpace) (u v : X) (q : ℚ)
    (hq : ¬ ∃ n : ℤ, (n : ℚ) = q) : mode J.val u q v = 0 := by
  obtain ⟨c, rfl⟩ := intertwiner_eq_smul_canonical J
  rw [mode_smul]
  change c • mode canonicalField u q v = 0
  rw [canonical_mode_nonintegral u v q hq, smul_zero]

/-- The signed divided-translation summand at an integer mode. -/
def integerSkewTerm (J : operatorSpace) (u v : X) (n : ℤ) (j : ℕ) : V :=
  (((-1 : ℂ) ^ (n + (j : ℤ) + 1)) / (j.factorial : ℂ)) •
    (fixedTranslation D ^ j) (mode J.val v ((n + (j : ℤ) : ℤ) : ℚ) u)

private theorem canonical_integer_skew (u v : X) (n : ℤ) :
    Function.HasFiniteSupport (integerSkewTerm canonicalIntertwiner u v n) ∧
      mode canonicalIntertwiner.val u (n : ℚ) v =
        ∑ᶠ j : ℕ, integerSkewTerm canonicalIntertwiner u v n j := by
  let beforeProjection (j : ℕ) :=
    (((-1 : ℂ) ^ (n + (j : ℤ) + 1)) / (j.factorial : ℂ)) •
      ((A).translation ^ j) ((((A).stateField (0, v))[[n + j]]) (0, u))
  obtain ⟨hfinite, hskew⟩ :=
    (StateField.SkewSymmetry.skew_symmetry A (0, u) (0, v)).1 n
  have hterm : (fun j => projection (beforeProjection j)) =
      integerSkewTerm canonicalIntertwiner u v n := by
    funext j
    change projection (beforeProjection j) =
      (((-1 : ℂ) ^ (n + (j : ℤ) + 1)) / (j.factorial : ℂ)) •
        (fixedTranslation D ^ j) (mode canonicalField v ((n + (j : ℤ) : ℤ) : ℚ) u)
    simp only [beforeProjection, map_smul, project_translation_pow, canonical_mode_projected,
      rationalMode_int]
    rfl
  have hprojected : Function.HasFiniteSupport (fun j => projection (beforeProjection j)) :=
    hfinite.fun_comp (map_zero projection)
  refine ⟨hterm ▸ hprojected, ?_⟩
  change mode canonicalField u (n : ℚ) v = _
  rw [canonical_mode_projected, rationalMode_int]
  change projection ((((A).stateField (0, u))[[n]]) (0, v)) = _
  calc
    _ = projection (∑ᶠ j : ℕ, beforeProjection j) := congrArg projection hskew
    _ = ∑ᶠ j : ℕ, projection (beforeProjection j) := map_finsum projection hfinite
    _ = _ := congrArg (fun f : ℕ → V => ∑ᶠ j : ℕ, f j) hterm

/-- The literal fixed-sector integer exchange formula for every lawful field. -/
theorem integer_skew (J : operatorSpace) (u v : X) (n : ℤ) :
    Function.HasFiniteSupport (integerSkewTerm J u v n) ∧
      mode J.val u (n : ℚ) v = ∑ᶠ j : ℕ, integerSkewTerm J u v n j := by
  obtain ⟨c, rfl⟩ := intertwiner_eq_smul_canonical J
  obtain ⟨hfinite, hskew⟩ := canonical_integer_skew u v n
  have hterm : integerSkewTerm (c • canonicalIntertwiner) u v n =
      fun j => c • integerSkewTerm canonicalIntertwiner u v n j := by
    funext j
    simp only [integerSkewTerm, mode_smul, map_smul, smul_comm c]
  rw [hterm, mode_smul, hskew, smul_finsum' c hfinite]
  exact ⟨hfinite.smul_right (fun _ => c), rfl⟩

/-- The rational exchange summand for the branch with phase exp(πi(q+j+1)). -/
def skewTerm (J : operatorSpace) (u v : X) (q : ℚ) (j : ℕ) : V :=
  (Complex.exp (((q + j + 1 : ℚ) : ℂ) * (Real.pi * Complex.I)) / (j.factorial : ℂ)) •
    (fixedTranslation D ^ j) (mode J.val v (q + j) u)

private theorem skewTerm_int (J : operatorSpace) (u v : X) (n : ℤ) (j : ℕ) :
    skewTerm J u v (n : ℚ) j = integerSkewTerm J u v n j := by
  have hphase :
      Complex.exp ((((n : ℚ) + j + 1 : ℚ) : ℂ) * (Real.pi * Complex.I)) =
        (-1 : ℂ) ^ (n + (j : ℤ) + 1) := by
    rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    rfl
  simp only [skewTerm, integerSkewTerm, hphase, Int.cast_add, Int.cast_natCast]

/-- Finite rational exchange on the entire lawful space. At nonintegral
indices each shifted mode vanishes, so every summand is zero. -/
theorem rational_skew (J : operatorSpace) (u v : X) (q : ℚ) :
    Function.HasFiniteSupport (skewTerm J u v q) ∧
      mode J.val u q v = ∑ᶠ j : ℕ, skewTerm J u v q j := by
  by_cases hq : ∃ n : ℤ, (n : ℚ) = q
  · obtain ⟨n, rfl⟩ := hq
    have hterm : skewTerm J u v (n : ℚ) = integerSkewTerm J u v n :=
      funext (skewTerm_int J u v n)
    rw [hterm]
    exact integer_skew J u v n
  · have hterm : skewTerm J u v q = 0 := by
      funext j
      have hshift := nonintegral_shift hq (j : ℤ)
        (show q + (j : ℚ) = q + ((j : ℤ) : ℚ) by simp)
      simp [skewTerm, mode_nonintegral J v u _ hshift]
    rw [hterm, mode_nonintegral J u v q hq]
    simp [Function.HasFiniteSupport, Function.support]

private theorem operator_ext {J K : operatorSpace}
    (h : ∀ (u v : X) (q : ℚ), mode J.val u q v = mode K.val u q v) : J = K := by
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro v
  simpa only [mode, show -(-e - 1) - 1 = e by ring] using h u v (-e - 1)

private theorem reversal_existsUnique (J : operatorSpace) :
    ∃! K : operatorSpace, ∀ (u v : X) (q : ℚ),
      mode K.val u q v = ∑ᶠ j : ℕ, skewTerm J u v q j := by
  refine ⟨J, fun u v q => (rational_skew J u v q).2, ?_⟩
  intro K hK
  apply operator_ext
  intro u v q
  exact (hK u v q).trans (rational_skew J u v q).2.symm

private def reversed (J : operatorSpace) : operatorSpace :=
  (reversal_existsUnique J).exists.choose

private theorem reversed_eq (J : operatorSpace) : reversed J = J :=
  (reversal_existsUnique J).unique (reversal_existsUnique J).exists.choose_spec
    (fun u v q => (rational_skew J u v q).2)

/-- The lawful field uniquely determined by the exchanged rational coefficients. -/
def skewReversal : operatorSpace →ₗ[ℂ] operatorSpace where
  toFun := reversed
  map_add' J K := by simp only [reversed_eq]
  map_smul' c J := by simp only [reversed_eq, RingHom.id_apply]

/-- The swap map has the finite exchange coefficients with the actual target translation. -/
theorem skewReversal_mode (J : operatorSpace) (u v : X) (q : ℚ) :
    mode (skewReversal J).val u q v = ∑ᶠ j : ℕ, skewTerm J u v q j :=
  (reversal_existsUnique J).exists.choose_spec u v q

/-- The actual coefficient swap acts by +1 on the one-dimensional vacuum channel. -/
theorem skewReversal_eq_id :
    skewReversal = (LinearMap.id : operatorSpace →ₗ[ℂ] operatorSpace) := by
  apply LinearMap.ext
  intro J
  apply operator_ext
  intro u v q
  exact (skewReversal_mode J u v q).trans (rational_skew J u v q).2.symm

#print axioms mode_nonintegral
#print axioms integer_skew
#print axioms rational_skew
#print axioms skewReversal
#print axioms skewReversal_mode
#print axioms skewReversal_eq_id

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumBraiding
