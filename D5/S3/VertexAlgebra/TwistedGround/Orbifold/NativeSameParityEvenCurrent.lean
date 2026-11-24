/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityEvenCurrent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityEvenCurrent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Abe's diagonal obstruction kills each integral weight-one current coefficient on the Leech even twisted top. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralPower
import D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityZhuTopBalance
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityRankOneSpectrum

/-!
Abe, arXiv:math/9907120v1, Lemma 2.6 and equations (4.1)–(4.4).
The diagonal specialization comes from the eight actual terms of (4.2)
with coefficient -1/2 at L(-4).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField LatticeAllStateReconstruction LatticeSugawaraCurrents
open MvPolynomial
open ActualLeechHyperbolic (leechData leech_spec)
open Lattice.ActualZhuRankOneOdd (L abe_zhu_identity oddCurrent_parity)
open NativeOddTwistedIntertwiner (Twisted leechUnit twistedTop chargeZeroOdd OddCarrier oddMode
  oddZhuResidue fixedTopZero leechAbeOddTransport leechAbeOddTransport_grade
  leechAbeOddTransport_mode leechAbeState leechAbeState_grade leechNeutralTransport
  leechNeutralTransport_mode oddCurrent leechOscillatorSubstitution_X leechRankOneScale)
open private oddPart oddPart_on_odd oddResidue_nat neutralLift neutralLift_apply neutralTransport_lift
    neutralTransport_grade rankOne_odd_lift leechAbeOddTransport_val
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance
open private x inverseGram normalization normalization_mul sum_rank_one abeState_grade
  from D5.S3.VertexAlgebra.Lattice.ActualZhuRankOneOdd
open private rankOneOmega rankOneOmega_polynomial rankOneOmega_fixed scale_gram
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityRankOneSpectrum

open private gradeOneBasis gradeOneBasis_coe from
  D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades

noncomputable section

local notation "ℒ" => leechData
local notation "R₁" => Lattice.ActualZhuRankOneOdd.datum
local notation "b₁" => Lattice.ActualZhuRankOneOdd.oddCurrent
local notation "A₁" => Lattice.ActualZhuRankOneOdd.abeState
local notation "B[" i "]" =>
  (LinearMap.comp (Submodule.subtype (chargeZeroOdd ℒ)) (leechAbeOddTransport i))
local notation "ι" => StateFieldResidueReconstruction.epsilon

local instance : NeZero (R₁).rank := ⟨by decide⟩
local instance : Subsingleton (Fin (R₁).rank) := by change Subsingleton (Fin 1); infer_instance

local instance : AddCommGroup (twistedTop ℒ leechUnit false) :=
  @Submodule.addCommGroup ℂ (NativeOddTwistedIntertwiner.Twisted ℒ leechUnit false) _ _ _
    (twistedTop ℒ leechUnit false)

private theorem rankOneInverse :
    inverseGram * gramComplex R₁ = 1 ∧ gramComplex R₁ * inverseGram = 1 := by
  have hG (i j : Fin (R₁).rank) : (gramComplex R₁) i j = 2 := by
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    change ((2 : ℤ) : ℂ) = 2
    norm_num
  constructor <;> ext i j <;> rw [Subsingleton.elim i 0, Subsingleton.elim j 0] <;>
    simp only [Matrix.mul_apply, sum_rank_one, hG, inverseGram, Matrix.one_apply] <;> norm_num

private def neutralOddAt (w : Carrier R₁) (h : ℕ) : Prop :=
  (∃ p : Oscillator R₁, w = neutralLift R₁ p ∧
    IsWeightedHomogeneous (oscillatorWeight R₁) p h) ∧ theta R₁ w = -w

private theorem rankOne_oddCurrent_at : neutralOddAt b₁ 1 := by
  refine ⟨⟨normalization • x 0, rankOne_odd_lift, ?_⟩, oddCurrent_parity⟩
  rw [MvPolynomial.smul_eq_C_mul]
  exact (isWeightedHomogeneous_X ℂ (oscillatorWeight R₁) ((0 : Fin (R₁).rank), 0)).C_mul _

private theorem neutralAt_grade {u : Carrier R₁} {h : ℕ}
    (hu : neutralOddAt u h) : u ∈ grade R₁ (h : ℤ) := by
  obtain ⟨⟨p, rfl, hp⟩, _⟩ := hu
  simpa only [neutralLift_apply, chargeEnergy_zero, zero_add] using
    Lattice.ActualZhuCurrentRelations.single_weighted_grade R₁ 0 p h hp

private theorem rankOne_mode (r : ℤ) (u : Carrier R₁) :
    mu R₁ rankOneOmega r u = L (r-1) u := by
  simp only [mu, rankOneOmega, L, LatticeActualConformalWard.omega_ncoeff]

private theorem rankOne_mode_neutral {u : Carrier R₁}
    (hneutral : ∃ p, u = neutralLift R₁ p) (r : ℤ) :
    ∃ p, mu R₁ rankOneOmega r u = neutralLift R₁ p := by
  obtain ⟨p, rfl⟩ := hneutral
  simp only [rankOneOmega_polynomial, neutralLift_apply]
  have he := LatticeSectorIntertwiner.charge_homogeneity R₁ 0 0
    ((1 / 4 : ℂ) • (x 0 * x 0)) p r
  rw [zero_add] at he
  exact ⟨_, he⟩

private theorem rankOne_mode_odd {u : Carrier R₁} (hu : theta R₁ u = -u) (r : ℤ) :
    theta R₁ (mu R₁ rankOneOmega r u) = -mu R₁ rankOneOmega r u := by
  simp only [mu, stateField_theta, rankOneOmega_fixed, hu, map_neg]

private theorem B_mode (i : Fin (ℒ).rank) {u : Carrier R₁} {h : ℕ}
    (hu : neutralOddAt u h) (r : ℤ) :
    B[i] (mu R₁ rankOneOmega r u) = oddMode ℒ (leechRankOneOmega i) r (B[i] u) := by
  obtain ⟨⟨p, hp, _⟩, hodd⟩ := hu
  have hn : ∃ q, u = neutralLift R₁ q := ⟨p, hp⟩
  apply Subtype.ext
  change (leechAbeOddTransport i (mu R₁ rankOneOmega r u)).val.val =
    mu ℒ (leechNeutralTransport i rankOneOmega) r (leechAbeOddTransport i u).val.val
  rw [leechAbeOddTransport_val i _ (rankOne_mode_neutral hn r) (rankOne_mode_odd hodd r),
    leechAbeOddTransport_val i _ hn hodd, rankOneOmega_polynomial, hp]
  exact leechNeutralTransport_mode i _ r p

private theorem B_grade (i : Fin (ℒ).rank) {u : Carrier R₁} {h : ℕ} (hu : neutralOddAt u h) :
    (B[i] u).val ∈ grade ℒ (h : ℤ) := by
  obtain ⟨⟨p, hp, hweight⟩, hodd⟩ := hu
  change (leechAbeOddTransport i u).val.val ∈ _
  rw [leechAbeOddTransport_val i u ⟨p, hp⟩ hodd, hp]
  exact neutralTransport_grade i p h hweight

private theorem rankOne_zero_mode {u : Carrier R₁} {h : ℕ} (hu : neutralOddAt u h) :
    mu R₁ rankOneOmega 1 u = (h : ℂ) • u := by
  rw [rankOne_mode, show (1 : ℤ) - 1 = 0 by norm_num]
  exact_mod_cast (actualL0_eigen_iff_grade R₁ inverseGram rankOneInverse.1 rankOneInverse.2
    (h : ℤ) u).mpr (neutralAt_grade hu)

private theorem neutralOddAt_L_neg {u : Carrier R₁} {h : ℕ}
    (hu : neutralOddAt u h) (m : ℕ) : neutralOddAt (L (-(m : ℤ)) u) (h + m) := by
  let r : ℤ := 1 - (m : ℤ)
  have hm : mu R₁ rankOneOmega r u = L (-(m : ℤ)) u := by
    rw [rankOne_mode, show r - 1 = -(m : ℤ) by dsimp only [r]; omega]
  have hgrade := neutralAt_grade hu
  suffices hmode : neutralOddAt (mu R₁ rankOneOmega r u) (h + m) from hm ▸ hmode
  obtain ⟨⟨p, hp, _⟩, hodd⟩ := hu
  obtain ⟨q, hq⟩ := rankOne_mode_neutral ⟨p, hp⟩ r
  refine ⟨⟨q, hq, ?_⟩, rankOne_mode_odd hodd r⟩
  have hw : rankOneOmega ∈ grade R₁ 2 := by
    rw [rankOneOmega_polynomial, neutralLift_apply, MvPolynomial.smul_eq_C_mul]
    have hh := isWeightedHomogeneous_X ℂ (oscillatorWeight R₁) ((0 : Fin (R₁).rank), 0)
    simpa only [chargeEnergy_zero, zero_add, Nat.cast_ofNat, x] using
      Lattice.ActualZhuCurrentRelations.single_weighted_grade R₁ 0 _ 2 ((hh.mul hh).C_mul _)
  have hg := actual_mode_grade R₁ inverseGram rankOneInverse.1 rankOneInverse.2
    2 (h : ℤ) r rankOneOmega u hw hgrade
  change mu R₁ rankOneOmega r u ∈ _ at hg
  rw [hq, neutralLift_apply, show (2 : ℤ) + h - r - 1 = (h + m : ℕ) by dsimp [r]; omega] at hg
  -- Read the weight of the coefficient at charge zero.
  exact rankOne_single_weight hg
where
  rankOne_single_weight {q : Oscillator R₁} {n : ℕ}
      (hq : Finsupp.single (0 : Charge R₁) q ∈ grade R₁ (n : ℤ)) :
      IsWeightedHomogeneous (oscillatorWeight R₁) q n := by
    intro m hm
    by_contra hweight
    apply hm
    have he : energy R₁ ((0 : Charge R₁), m) ≠ (n : ℤ) := by
      intro he
      apply hweight
      have he' : (oscillatorEnergy m : ℤ) = (n : ℤ) := by
        simpa only [energy, chargeEnergy_zero, zero_add] using he
      exact_mod_cast he'
    simpa only [Finsupp.single_eq_same] using (mem_grade_iff R₁ (n : ℤ) _).mp hq _ he

variable (i : Fin (ℒ).rank) (F : LawfulField ℒ leechUnit false)
  (v : twistedTop ℒ leechUnit false)

private def evalRankOne : Carrier R₁ →ₗ[ℂ] twistedTop ℒ leechUnit false :=
  (zhuTopEvaluation F v).comp B[i]

/-- At equal weights the p = 1 Virasoro residue has only the right top
term for r < 0. At r = 0 the two actual omega actions cancel. -/
private theorem virasoro_step (u : Carrier R₁) (h : ℕ) (hu : neutralOddAt u h)
    (r : ℤ) (hr : r ≤ 0) :
    let Z := evalRankOne i F v
    Z (mu R₁ rankOneOmega r u) + Z (mu R₁ rankOneOmega (r+1) u) =
      (if r = 0 then 0 else -(ι r * (1/16 : ℂ))) • Z u := by
  dsimp only
  let a := leechRankOneOmega i
  let Z := zhuTopEvaluation F v
  have he := zhuTopEvaluation_residue F a (B[i] u) v 2 (h : ℤ) ((1 : ℕ) : ℤ) r
    (leechRankOneOmega_grade i) (B_grade i hu) (by norm_num) (by omega)
  rw [oddResidue_nat a (B[i] u) 1 r] at he
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, one_smul, Nat.cast_zero, add_zero] at he
  change Z (oddMode ℒ a r (B[i] u) + oddMode ℒ a (r+1) (B[i] u)) = _ at he
  rw [map_add, ← B_mode i hu r, ← B_mode i hu (r+1)] at he
  have hin : zhuTopEvaluation F (fixedTopZero false a 2 (leechRankOneOmega_grade i) v) (B[i] u) =
      (1/16 : ℂ) • Z (B[i] u) := by
    rw [leechRankOneOmega_even_zeroMode]
    apply Subtype.ext
    simp only [Z, Submodule.coe_smul, zhuTopEvaluation_homogeneous F _ (h : ℤ) _ (B_grade i hu),
      map_smul]
  have hp : (1 : ℤ) = ((2 : ℕ) : ℤ) - 1 := by norm_num
  by_cases hz : r = 0
  · subst r
    simp only [add_zero, ite_eq_left hp, hin,
      StateFieldResidueReconstruction.epsilon, zpow_zero, one_smul] at he
    dsimp only [a, Z] at he
    rw [leechRankOneOmega_even_zeroMode, sub_self] at he
    simpa only [evalRankOne, LinearMap.comp_apply, ite_true, zero_smul] using he
  · have ht : (1 : ℤ) + r ≠ ((2 : ℕ) : ℤ) - 1 := by omega
    rw [ite_eq_right ht, ite_eq_left hp, hin, smul_smul, zero_sub, ← neg_smul] at he
    simpa only [evalRankOne, LinearMap.comp_apply, ite_eq_right hz] using he

private theorem virasoro_diagonal (u : Carrier R₁) (h : ℕ) (hu : neutralOddAt u h) :
    let Z := evalRankOne i F v
    Z (L (-1) u) = (-(h : ℂ)) • Z u ∧
    Z (L (-2) u) = ((h : ℂ) + 1/16) • Z u ∧
    Z (L (-3) u) = (-(h : ℂ) - 2/16) • Z u ∧
    Z (L (-4) u) = ((h : ℂ) + 3/16) • Z u := by
  dsimp only
  have h1 := virasoro_step i F v u h hu 0 (by omega)
  have h2 := virasoro_step i F v u h hu (-1) (by omega)
  have h3 := virasoro_step i F v u h hu (-2) (by omega)
  have h4 := virasoro_step i F v u h hu (-3) (by omega)
  dsimp only at h1 h2 h3 h4
  rw [show (0 : ℤ) + 1 = 1 by norm_num, rankOne_zero_mode hu] at h1
  norm_num [rankOne_mode, StateFieldResidueReconstruction.epsilon] at h1 h2 h3 h4
  have e1 := eq_sub_of_add_eq h1
  simp only [zero_sub, ← neg_smul] at e1
  have e2 := eq_sub_of_add_eq h2
  rw [e1] at e2
  have e3 := eq_sub_of_add_eq h3
  rw [e2] at e3
  have e4 := eq_sub_of_add_eq h4
  rw [e3] at e4
  exact ⟨e1, e2.trans (by module), e3.trans (by module), e4.trans (by module)⟩

/-- The actual eight-term product in (4.2) evaluates to 2*(1/16) at the
two equal rank-one even tops. -/
theorem leech_even_abe_star_evaluation :
    evalRankOne i F v (Lattice.ActualZhuProduct.star R₁ A₁ b₁) =
      (1/8 : ℂ) • evalRankOne i F v b₁ := by
  have hadj₁ : neutralOddAt (L (-1) b₁) 2 := neutralOddAt_L_neg rankOne_oddCurrent_at 1
  have hadj₂ : neutralOddAt (L (-1) (L (-1) b₁)) 3 := neutralOddAt_L_neg hadj₁ 1
  obtain ⟨e1, _, e3, e4⟩ := virasoro_diagonal i F v b₁ 1 rankOne_oddCurrent_at
  obtain ⟨e11, e21, e31, _⟩ := virasoro_diagonal i F v _ 2 hadj₁
  obtain ⟨_, e211, _, _⟩ := virasoro_diagonal i F v _ 3 hadj₂
  rw [abe_zhu_identity]
  simp only [map_add, map_sub, map_smul]
  rw [e211, e31, e21, e11, e4, e3]
  simp only [e1]
  push_cast
  module

private theorem leech_even_abe_left_action :
    evalRankOne i F v (Lattice.ActualZhuProduct.star R₁ A₁ b₁) =
      fixedTopZero false (leechAbeState i) 4 (leechAbeState_grade i) (evalRankOne i F v b₁) := by
  let a := leechAbeState i
  let b := B[i] b₁
  have hrow : B[i] (Lattice.ActualZhuProduct.star R₁ A₁ b₁) = oddZhuResidue a b 4 (-1) := by
    change _ = oddZhuResidue a b ((4 : ℕ) : ℤ) (-1)
    rw [Lattice.ActualZhuProduct.star_homogeneous R₁ 4 A₁ b₁ abeState_grade,
      oddResidue_nat a b 4 (-1)]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro k _
    rw [show (-1 : ℤ)+(k : ℤ) = (k : ℤ)-1 by omega]
    exact congrArg (fun w : OddCarrier ℒ => (Nat.choose 4 k : ℂ) • w)
      (leechAbeOddTransport_mode i ((k : ℤ)-1))
  change zhuTopEvaluation F v (B[i] (Lattice.ActualZhuProduct.star R₁ A₁ b₁)) = _
  rw [hrow]
  exact (zhuTopEvaluation_balanced F a b v 4 1
    (leechAbeState_grade i) (leechAbeOddTransport_grade i)).1

/-- Abe (4.1) evaluated on the actual rank-one current and the actual Leech
even twisted top. The two omega actions are the native zero modes. -/
theorem leech_even_abe_evaluated_relation :
    let Z := evalRankOne i F v b₁
    fixedTopZero false (leechRankOneQuartic i) 4 (leechRankOneQuartic_grade i) Z -
      (4 : ℂ) • fixedTopZero false (leechRankOneOmega i) 2 (leechRankOneOmega_grade i)
        (fixedTopZero false (leechRankOneOmega i) 2 (leechRankOneOmega_grade i) Z) +
      fixedTopZero false (leechRankOneOmega i) 2 (leechRankOneOmega_grade i) Z = 0 := by
  dsimp only
  have h := leech_even_abe_left_action i F v
  rw [leech_even_abe_star_evaluation, leechAbeState_even_zeroMode] at h
  rw [leechRankOne_even_spectral_obstruction]
  calc
    _ = (9 : ℂ) • ((1/8 : ℂ) • evalRankOne i F v b₁ -
        (15/128 : ℂ) • evalRankOne i F v b₁) := by module
    _ = 0 := by rw [sub_eq_zero.mpr h, smul_zero]

/-- The integral physical mode 0 of the unit-length current vanishes on the
actual Leech even twisted top, for every lawful same-parity field. -/
theorem leech_even_sameParity_normalizedCurrent_zero :
    F.coeff 0 (B[i] b₁) v.val = 0 := by
  have h := leech_even_abe_evaluated_relation i F v
  dsimp only at h
  rw [leechRankOne_even_spectral_obstruction] at h
  have hz := (smul_eq_zero.mp h).resolve_left (by norm_num : (9/128 : ℂ) ≠ 0)
  have he := zhuTopEvaluation_homogeneous F v 1 (B[i] b₁) (leechAbeOddTransport_grade i)
  change (evalRankOne i F v b₁).val = F.coeff 0 (B[i] b₁) v.val at he
  simpa only [hz, Submodule.coe_zero] using he.symm

private theorem oddCurrent_polynomial (j : Fin (ℒ).rank) :
    (oddCurrent ℒ j).val = Finsupp.single 0 (X (j, 0)) := by
  change LatticeFiniteNegativeGeneration.neutralMode ℒ j (-1)
    (LatticeAllStateField.vacuum ℒ) = _
  simpa only [neutralField_ncoeff, LatticeActualConformalState.currentState] using
    LatticeActualConformalState.current_state_creation ℒ j

/-- Vanishing in the repository's unscaled weight-one current basis. -/
theorem leech_even_sameParity_current_zero :
    F.coeff 0 (oddCurrent ℒ i) v.val = 0 := by
  let k : ℂ := Complex.ofReal (leechRankOneScale i)
  have hkn : k ≠ 0 := by
    intro he
    have h := scale_gram i
    change k^2 * ((ℒ).G i i : ℂ) = 2 at h
    norm_num [he] at h
  have hnorm : normalization ≠ 0 := by
    intro he
    have h := normalization_mul
    norm_num [he] at h
  have hb : B[i] b₁ = (normalization * k) • oddCurrent ℒ i := by
    apply Subtype.ext
    change (leechAbeOddTransport i b₁).val.val = (normalization * k) • (oddCurrent ℒ i).val
    rw [leechAbeOddTransport_val i _ ⟨_, rankOne_odd_lift⟩ oddCurrent_parity,
      rankOne_odd_lift, neutralTransport_lift, neutralLift_apply, oddCurrent_polynomial]
    simp only [x, map_smul, leechOscillatorSubstitution_X, smul_smul, Finsupp.smul_single, k]
  have hz := leech_even_sameParity_normalizedCurrent_zero i F v
  rw [hb, map_smul, LinearMap.smul_apply] at hz
  exact (smul_eq_zero.mp hz).resolve_left (mul_ne_zero hnorm hkn)

/-- The vanishing extends to every element of the actual weight-one space. -/
theorem leech_even_sameParity_weightOne_zero (b : OddCarrier ℒ)
    (hb : b.val ∈ grade ℒ 1) : F.coeff 0 b v.val = 0 := by
  have hroot (a : Charge ℒ) : bilinear ℒ a a ≠ 2 := by
    by_cases ha : a = 0
    · subst a
      simp [bilinear]
    · have h := Lattice.ActualFixedC2.leech_charge_norm_ge_four a ha
      omega
  let e := gradeOneBasis ℒ leech_spec.2.2.1 hroot
  let T : grade ℒ 1 →ₗ[ℂ] Twisted ℒ leechUnit false :=
    ((LinearMap.applyₗ v.val).comp (F.coeff 0)).comp ((oddPart ℒ).comp (grade ℒ 1).subtype)
  have hT : T = 0 := by
    apply e.ext
    intro j
    change F.coeff 0 (oddPart ℒ (e j).val) v.val = 0
    have he : (e j).val = (oddCurrent ℒ j).val := by
      dsimp only [e]
      rw [gradeOneBasis_coe, oddCurrent_polynomial]
      rfl
    rw [he, oddPart_on_odd]
    exact leech_even_sameParity_current_zero j F v
  have h := LinearMap.congr_fun hT (⟨b.val, hb⟩ : grade ℒ 1)
  change F.coeff 0 (oddPart ℒ b.val) v.val = 0 at h
  rwa [oddPart_on_odd] at h

end
end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity
