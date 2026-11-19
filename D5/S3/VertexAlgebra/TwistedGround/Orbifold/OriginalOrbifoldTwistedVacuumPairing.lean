/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedVacuumPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite vacuum Ward identities for the actual negative twisted Leech pair. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumFusion
import D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose
import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation

/-! Energy and vacuum coefficient identities for arbitrary lawful fields on
the actual negative twisted Leech sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumPairing

open scoped BigOperators VertexOperator
open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (fixedMode fixedTranslation fixedVacuum fixedSpace)
open LatticePositiveEnergy (grade actualL0_eigen_iff_grade)
open LatticeAllStateField (Y vacuum stateField_creativity)
open OriginalOrbifoldConformal (conformalVector L L_fixed_apply)
open OriginalOrbifoldField (Y_fixed_ncoeff_apply)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open OriginalOrbifoldSectorModules
  (fixedParityY fixedParitySlice_borcherds fixedParitySlice_vacuum_ncoeff)
open OriginalOrbifoldTwistedVacuumFusion
open SourceBPZ.AllStateTranspose (sourcePairing_allState)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open SourceBPZ.OriginalSourceCoevaluation (gradeVacuum)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open VacuumFirstIntertwinerDraft (mode)
open private fixed_conformal_zero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumFusion
open private sum_signed_choose_zero twisted_source_derivative from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion

noncomputable section

local notation "D" => leechData
local notation "hu" => And.left (And.right leech_spec)
local notation "hD" => And.left (And.right (And.right leech_spec))
local notation "X" => NegativeTwisted
local notation "V" => FixedLeech
local notation "ω" => Prod.fst (conformalVector D hu)
local notation "ρ" => fixedParityY D hu (-1)
local notation "M" => fun (a : V) (n : ℤ) => (ρ a)[[n]]

/-- Energy on the actual negative twisted sector. -/
abbrev twistedL0 : Module.End ℂ X := M ω 1

/-- Vacuum projection on the fixed Leech carrier, normalized by the source form. -/
def vacuumFunctional : V →ₗ[ℂ] ℂ :=
  ((sourcePairing D).flip (fixedVacuum D).val).comp (fixedSpace D).subtype

/-- The projected coefficient at the vacuum index for two integer weights. -/
def vacuumAt (J : operatorSpace) (s t : ℤ) (x y : X) : ℂ :=
  vacuumFunctional (mode J.val x ((s + t - 1 : ℤ) : ℚ) y)

private theorem mode_smul_left (J : Fields) (c : ℂ) (x : X) (q : ℚ) (y : X) :
    mode J (c • x) q y = c • mode J x q y := by
  simp [mode]

private theorem sum_choose_one {U : Type*} [AddCommGroup U] [Module ℂ U]
    (g : ℕ → U) : (∑ᶠ i : ℕ, integerBinomial 1 i • g i) = g 0 + g 1 := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, integerBinomial]
  · intro i hi
    by_contra hout
    have hi' : 1 < i := by simpa using hout
    have hz : Ring.choose (1 : ℤ) i = 0 := by
      simpa only [Nat.cast_one, Nat.cast_zero] using
        (Ring.choose_natCast (R := ℤ) 1 i).trans (congrArg (Nat.cast : ℕ → ℤ)
          (Nat.choose_eq_zero_of_lt hi'))
    exact hi (by simp [integerBinomial, hz])

private theorem targetL0_val (w : V) :
    (fixedMode D ω 1 w).val = sugawaraMode D (actualInverse D) 0 w.val := by
  have h := L_fixed_apply D hu hD 0 (w, 0)
  simpa only [L, Int.zero_add, conformalVector, Y_fixed_ncoeff_apply] using h

set_option maxHeartbeats 600000 in
-- The calculation uses coefficients on both original carrier subtypes.
/-- All rational coefficients obey the conformal weight law. -/
theorem rational_mode_energy (J : operatorSpace) (s t : ℤ) (x y : X)
    (hx : twistedL0 x = (s : ℂ) • x) (hy : twistedL0 y = (t : ℂ) • y) (q : ℚ) :
    fixedMode D ω 1 (mode J.val x q y) =
      ((s : ℂ) + (t : ℂ) - (q : ℂ) - 1) • mode J.val x q y := by
  have hJ : Lawful J.val := J.property
  have h := (hJ.jacobi ω x y 1 0 q).2.2.2
  unfold leftTerm firstTerm secondTerm at h
  rw [sum_choose_one, sum_signed_choose_zero, sum_signed_choose_zero] at h
  simp only [Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one, zero_add,
    add_zero, sub_zero, add_sub_cancel_left, epsilon, zpow_zero, one_smul] at h
  change mode J.val (M ω 0 x) (1 + q) y + mode J.val (twistedL0 x) q y =
    fixedMode D ω 1 (mode J.val x q y) - mode J.val x q (twistedL0 y) at h
  rw [hJ.source, hx, hy, mode_smul_left, map_smul, add_comm (1 : ℚ) q,
    add_sub_cancel_right, Rat.cast_add, Rat.cast_one] at h
  rw [eq_sub_iff_add_eq] at h
  rw [← h, ← add_smul, ← add_smul]
  congr 1
  ring

private theorem vacuum_target_energy (w : V) :
    vacuumFunctional (fixedMode D ω 1 w) = 0 := by
  have hv : (fixedVacuum D).val ∈ grade D 0 := (gradeVacuum D).property.1
  let f := (sourcePairing D).flip (fixedVacuum D).val
  change f (fixedMode D ω 1 w).val = 0
  rw [targetL0_val]
  have he := congrArg (fun v => f (sugawaraMode D (actualInverse D) 0 v))
    (LatticePositiveEnergy.sum_gradeProjections D w.val)
  rw [← he]
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  let z := LatticePositiveEnergy.gradeProjection D k w.val
  have hz : z ∈ grade D k := LatticePositiveEnergy.gradeProjection_mem D k w.val
  change f (sugawaraMode D (actualInverse D) 0 z) = 0
  rw [(actualL0_eigen_iff_grade D (actualInverse D)
    (actualInverse_left D hu) (actualInverse_right D hu) k z).mpr hz, map_smul]
  by_cases hk : k = 0
  · simp [hk]
  · have hz' := sourcePairing_grade D k 0 hk z (fixedVacuum D).val hz hv
    change f z = 0 at hz'
    rw [hz', smul_zero]

private theorem complex_weight_ne (s t : ℤ) (q : ℚ)
    (hq : q ≠ ((s + t - 1 : ℤ) : ℚ)) :
    (s : ℂ) + (t : ℂ) - (q : ℂ) - 1 ≠ 0 := by
  intro h
  apply hq
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re,
    Complex.ratCast_re, Complex.one_re, Complex.zero_re] at hr
  have hr' : ((s : ℝ) + (t : ℝ) - (1 : ℝ)) = (q : ℝ) := by linarith
  have h' : (((s + t - 1 : ℤ) : ℚ) : ℝ) = (q : ℝ) := by push_cast; exact hr'
  exact (Rat.cast_injective h').symm

/-- Vacuum projection at a rational index has support at the sum of the weights minus one. -/
theorem vacuum_mode_eq_zero (J : operatorSpace) (s t : ℤ) (x y : X)
    (hx : twistedL0 x = (s : ℂ) • x) (hy : twistedL0 y = (t : ℂ) • y)
    (q : ℚ) (hq : q ≠ ((s + t - 1 : ℤ) : ℚ)) :
    vacuumFunctional (mode J.val x q y) = 0 := by
  have h := congrArg (fun w : V => vacuumFunctional w) (rational_mode_energy J s t x y hx hy q)
  simp only [vacuum_target_energy, map_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (complex_weight_ne s t q hq)

private theorem source_energy (a : V) (d : ℤ) (ha : a.val ∈ grade D d) :
    fixedMode D ω 1 a = (d : ℂ) • a := by
  apply Subtype.ext
  rw [targetL0_val]
  exact (actualL0_eigen_iff_grade D (actualInverse D)
    (actualInverse_left D hu) (actualInverse_right D hu) d a.val).mpr ha

set_option maxHeartbeats 600000 in
-- The calculation uses coefficients on both original carrier subtypes.
/-- Fixed-source modes shift the integer weights on the actual twisted slice. -/
theorem twisted_mode_energy (a : V) (d n s : ℤ) (x : X)
    (ha : a.val ∈ grade D d) (hx : twistedL0 x = (s : ℂ) • x) :
    twistedL0 (M a n x) = ((d + s - n - 1 : ℤ) : ℂ) • M a n x := by
  let f (i : ℕ) := M (fixedMode D ω (0+i) a) (1+n-i) x
  let g (i : ℕ) := M ω (1+0-i) (M a (n+i) x) -
    epsilon 0 • M a (n+0-i) (M ω (1+i) x)
  have h := (fixedParitySlice_borcherds D hu (-1) ω a x 1 n 0).2.2.2
  change (∑ᶠ i, integerBinomial 1 i • f i) =
    (∑ᶠ i, (((-1 : ℂ)^i)*integerBinomial 0 i) • g i) at h
  have h := (sum_choose_one f).symm.trans (h.trans (sum_signed_choose_zero g))
  dsimp only [f, g] at h
  simp only [Nat.cast_zero, Nat.cast_one, zero_add, add_zero, sub_zero,
    add_sub_cancel_left, epsilon, zpow_zero, one_smul] at h
  change M (fixedMode D ω 0 a) (1 + n) x + M (fixedMode D ω 1 a) n x =
    twistedL0 (M a n x) - M a n (twistedL0 x) at h
  have h0 : M (fixedMode D ω 0 a) (1 + n) x =
      -((1+n : ℤ) : ℂ) • M a n x := by
    calc
      _ = M (fixedTranslation D a) (1+n) x :=
        congrArg (fun b : V => M b (1+n) x) (fixed_conformal_zero a)
      _ = _ := by simpa only [add_comm (1 : ℤ) n, add_sub_cancel_right] using
        twisted_source_derivative D hu (-1) a (1+n) x
  have h1 : M (fixedMode D ω 1 a) n x = (d : ℂ) • M a n x := by
    have ht := congrArg (fun b : V => M b n x) (source_energy a d ha)
    simpa only [map_smul, Pi.smul_apply, LinearMap.smul_apply] using ht
  simp only [h0, h1, hx, map_smul] at h
  rw [eq_sub_iff_add_eq] at h
  let w := M a n x
  have hs : -((1+n : ℤ) : ℂ) + (d : ℂ) + (s : ℂ) = ((d+s-n-1 : ℤ) : ℂ) := by
    push_cast
    ring
  calc
    twistedL0 w = (-((1+n : ℤ) : ℂ) + (d : ℂ) + (s : ℂ)) • w := by
      simpa only [add_smul] using h.symm
    _ = _ := congrArg (fun c : ℂ => c • w) hs

private theorem actualInverse_eq :
    actualInverse D = (gramComplex D)⁻¹ := by
  exact (Matrix.inv_eq_left_inv (actualInverse_left D hu)).symm

/-- Quasiprimary fixed-source modes opposite to nonnegative creation modes kill
vacuum projection on every target state. -/
theorem vacuum_opposite_nonnegative (a : V) (d : ℤ) (ha : a.val ∈ grade D d)
    (hea : sugawaraMode D (gramComplex D)⁻¹ 1 a.val = 0) (w : V) (i : ℕ) :
    vacuumFunctional (fixedMode D a (2*d-2-(i : ℤ)) w) = 0 := by
  classical
  have h := sourcePairing_allState D hu d (2*d-2-(i : ℤ)) a.val ha w.val (vacuum D)
  change vacuumFunctional (fixedMode D a (2*d-2-(i : ℤ)) w) = _ at h
  rw [h]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro j _
  cases j with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.cast_zero]
    rw [show 2*d-(0 : ℤ)-(2*d-2-(i : ℤ))-2 = i by omega,
      stateField_creativity D a.val i (Int.natCast_nonneg i), map_zero, mul_zero]
  | succ j =>
    simp only [pow_succ, Module.End.mul_apply, hea, map_zero,
      Pi.zero_apply, LinearMap.zero_apply, mul_zero]

set_option maxHeartbeats 600000 in
-- The calculation uses coefficients on both original carrier subtypes.
/-- The quasiprimary vacuum Ward identity at the coefficient indices given by
the integral input weights. The two upper binomial indices are signed. -/
theorem quasiprimary_vacuum_ward (J : operatorSpace) (a : V) (d n s t : ℤ)
    (ha : a.val ∈ grade D d) (hea : sugawaraMode D (gramComplex D)⁻¹ 1 a.val = 0)
    (x y : X) :
    let m := 2*d-2-n
    let left := fun i : ℕ => integerBinomial m i •
      vacuumAt J (d+s-(n+i)-1) t (M a (n+i) x) y
    let right := fun i : ℕ => ((-1 : ℂ)^i * integerBinomial n i) •
      vacuumAt J s (d+t-(m+i)-1) x (M a (m+i) y)
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right ∧
      (∑ᶠ i, left i) = (-1 : ℂ)^(n+1) • (∑ᶠ i, right i) := by
  let m := 2*d-2-n
  let q : ℚ := ((s+t-d : ℤ) : ℚ)
  let left (i : ℕ) := integerBinomial m i •
    vacuumAt J (d+s-(n+i)-1) t (M a (n+i) x) y
  let right (i : ℕ) := ((-1 : ℂ)^i * integerBinomial n i) •
    vacuumAt J s (d+t-(m+i)-1) x (M a (m+i) y)
  change Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right ∧
    (∑ᶠ i, left i) = (-1 : ℂ)^(n+1) • (∑ᶠ i, right i)
  have hJ : Lawful J.val := J.property
  have hj := hJ.jacobi a x y m n q
  have hl := hj.1
  have hf := hj.2.1
  have hs := hj.2.2.1
  have eL (i : ℕ) : vacuumFunctional (leftTerm J.val a x y m n q i) = left i := by
    have index : (m : ℚ) + q - i = ((d+s-(n+i)-1+t-1 : ℤ) : ℚ) := by
      dsimp [m, q]
      push_cast
      ring
    simp only [leftTerm, left, map_smul, vacuumAt, index]
  have eS (i : ℕ) : vacuumFunctional (secondTerm J.val a x y m n q i) =
      epsilon n • right i := by
    have index : q + (n : ℚ) - i = ((s+(d+t-(m+i)-1)-1 : ℤ) : ℚ) := by
      dsimp [m, q]
      push_cast
      ring
    simp only [secondTerm, right, map_smul, vacuumAt, index]
    exact smul_comm _ _ _
  have eF (i : ℕ) : vacuumFunctional (firstTerm J.val a x y m n q i) = 0 := by
    rw [firstTerm, map_smul, show m+n-(i : ℤ) = 2*d-2-(i : ℤ) by dsimp [m]; ring,
      vacuum_opposite_nonnegative a d ha hea, smul_zero]
  have hL : Function.HasFiniteSupport left := by
    refine hl.subset ?_
    intro i hi
    change left i ≠ 0 at hi
    change leftTerm J.val a x y m n q i ≠ 0
    intro hz
    exact hi (by rw [← eL, hz, map_zero])
  have hR : Function.HasFiniteSupport right := by
    refine hs.subset ?_
    intro i hi
    change right i ≠ 0 at hi
    change secondTerm J.val a x y m n q i ≠ 0
    intro hz
    have hh := eS i
    rw [hz, map_zero] at hh
    exact (smul_ne_zero (zpow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)) hi) hh.symm
  refine ⟨hL, hR, ?_⟩
  have h := congrArg (fun w : V => vacuumFunctional w) hj.2.2.2
  simp only [map_sub, map_finsum vacuumFunctional hl, map_finsum vacuumFunctional hf,
    map_finsum vacuumFunctional hs, eL, eS, eF, finsum_zero, zero_sub,
    ← smul_finsum' (epsilon n) hR] at h
  rw [h, ← neg_smul, epsilon, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  rw [mul_neg_one]

#print axioms rational_mode_energy
#print axioms vacuum_mode_eq_zero
#print axioms twisted_mode_energy
#print axioms quasiprimary_vacuum_ward


open OriginalOrbifoldTwistedModeMorphisms
  (fixedParity_conformal_mode_val fixedParity_conformal_eigenweight)
open LatticeHalfFockGradedTrace
  (actualAmbientBasis actualTensorL0 actual_basis_eigenvalue oddWeight)
open LatticeHalfFockParityT (actualParity)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open private support_parity from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedModeMorphisms
open private basis_parity from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

private theorem odd_oscillator_degree (N : ℕ) (h : (-1 : ℂ) ^ N = -1) :
    ∃ k : ℕ, N = 2 * k + 1 := by
  obtain he | ho := Nat.even_or_odd N
  · rw [he.neg_one_pow] at h
    norm_num at h
  · obtain ⟨k, hk⟩ := ho
    exact ⟨k, by omega⟩

private theorem integer_eigenvectors_span :
    Submodule.span ℂ {x : X | ∃ s : ℤ, twistedL0 x = (s : ℂ) • x} = ⊤ := by
  classical
  apply top_unique
  intro x _
  let b := actualAmbientBasis D hu
  let I := (b.repr x.val).support
  let xj (j : I) : X := ⟨b j.val, by
    have hp := support_parity x j.val (Finsupp.mem_support_iff.mp j.property)
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, hp] using basis_parity D hu j.val⟩
  have decomp : ∑ j ∈ I.attach, b.repr x.val j.val • xj j = x := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change ∑ j ∈ I.attach, b.repr x.val j.val • b j.val = x.val
    rw [Finset.sum_attach I (fun j => b.repr x.val j • b j)]
    exact b.linearCombination_repr x.val
  rw [← decomp]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  change ∃ s : ℤ, twistedL0 (xj j) = (s : ℂ) • xj j
  obtain ⟨k, hk⟩ := odd_oscillator_degree (oddWeight D j.val.1)
    (support_parity x j.val (Finsupp.mem_support_iff.mp j.property))
  refine ⟨(k : ℤ) + 2, ?_⟩
  apply Subtype.ext
  rw [fixedParity_conformal_mode_val]
  change actualTensorL0 D hu (b j.val) = _ • b j.val
  have he := actual_basis_eigenvalue D hu j.val.1 j.val.2
  have hrank : (leechData.rank : ℂ) = 24 := by exact_mod_cast leech_spec.1
  simp only [Prod.mk.eta, hrank, hk] at he
  rw [he]
  congr 1
  push_cast
  ring

private def vacuumModeForm (J : operatorSpace) (q : ℚ) : LinearMap.BilinForm ℂ X :=
  LinearMap.mk₂ ℂ (fun x y => vacuumFunctional (mode J.val x q y))
    (by intros; simp [mode])
    (by intros; simp [mode])
    (by intros; simp only [map_add])
    (by intros; simp only [map_smul])

private theorem vacuum_modes_finite (J : operatorSpace) (x y : X) :
    Function.HasFiniteSupport (fun q : ℚ => vacuumModeForm J q x y) := by
  have hx : x ∈ Submodule.span ℂ {w : X | ∃ s : ℤ, twistedL0 w = (s : ℂ) • w} := by
    rw [integer_eigenvectors_span]
    exact Submodule.mem_top
  have hy : y ∈ Submodule.span ℂ {w : X | ∃ s : ℤ, twistedL0 w = (s : ℂ) • w} := by
    rw [integer_eigenvectors_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | zero => simp [Function.HasFiniteSupport, Function.support]
  | add x₁ x₂ _ _ h₁ h₂ =>
    simpa only [map_add, LinearMap.add_apply, Pi.add_apply] using
      (show Function.HasFiniteSupport (fun _ => _) from h₁.add h₂)
  | smul c x _ h =>
    simp only [map_smul, LinearMap.smul_apply]
    refine h.subset ?_
    intro q hq hz
    change vacuumModeForm J q x y = 0 at hz
    exact hq (show c • vacuumModeForm J q x y = 0 by rw [hz, smul_zero])
  | mem x hx =>
    obtain ⟨s, hs⟩ := hx
    induction hy using Submodule.span_induction with
    | zero => simp [Function.HasFiniteSupport, Function.support]
    | add y₁ y₂ _ _ h₁ h₂ =>
      simpa only [map_add, Pi.add_apply] using
        (show Function.HasFiniteSupport (fun _ => _) from h₁.add h₂)
    | smul c y _ h =>
      simp only [map_smul]
      refine h.subset ?_
      intro q hq hz
      change vacuumModeForm J q x y = 0 at hz
      exact hq (show c • vacuumModeForm J q x y = 0 by rw [hz, smul_zero])
    | mem y hy =>
      obtain ⟨t, ht⟩ := hy
      refine (Set.finite_singleton (((s+t-1 : ℤ) : ℚ))).subset ?_
      intro q hq
      by_contra hne
      exact hq (vacuum_mode_eq_zero J s t x y hs ht q hne)

/-- Sum of the vacuum readouts over all rational indices, pointwise finite. -/
def rawVacuumPairing (J : operatorSpace) : LinearMap.BilinForm ℂ X :=
  LinearMap.mk₂ ℂ (fun x y => ∑ᶠ q : ℚ, vacuumModeForm J q x y)
    (by
      intro x₁ x₂ y
      simp only [map_add, LinearMap.add_apply]
      exact finsum_add_distrib (vacuum_modes_finite J x₁ y) (vacuum_modes_finite J x₂ y))
    (by
      intro c x y
      simp only [map_smul, LinearMap.smul_apply]
      exact (smul_finsum' c (vacuum_modes_finite J x y)).symm)
    (by
      intro x y₁ y₂
      simp only [map_add]
      exact finsum_add_distrib (vacuum_modes_finite J x y₁) (vacuum_modes_finite J x y₂))
    (by
      intro c x y
      simp only [map_smul]
      exact (smul_finsum' c (vacuum_modes_finite J x y)).symm)

/-- The grade-independent bilinear readout agrees with the single vacuum
coefficient on homogeneous negative states. -/
theorem rawVacuumPairing_eq_vacuumAt (J : operatorSpace) (s t : ℤ) (x y : X)
    (hx : twistedL0 x = (s : ℂ) • x) (hy : twistedL0 y = (t : ℂ) • y) :
    rawVacuumPairing J x y = vacuumAt J s t x y := by
  change (∑ᶠ q : ℚ, vacuumModeForm J q x y) = _
  rw [finsum_eq_single _ (((s+t-1 : ℤ) : ℚ))]
  · rfl
  · exact fun q hq => vacuum_mode_eq_zero J s t x y hx hy q hq

/-- The coefficient Ward identity expressed using the same bilinear form on
each side. The integer weights in each mode shift are determined by the
negative module action. -/
theorem rawVacuumPairing_ward_homogeneous (J : operatorSpace) (a : V) (d n s t : ℤ)
    (ha : a.val ∈ grade D d) (hea : sugawaraMode D (gramComplex D)⁻¹ 1 a.val = 0)
    (x y : X) (hx : twistedL0 x = (s : ℂ) • x) (hy : twistedL0 y = (t : ℂ) • y) :
    let m := 2*d-2-n
    let left := fun i : ℕ => integerBinomial m i • rawVacuumPairing J (M a (n+i) x) y
    let right := fun i : ℕ => ((-1 : ℂ)^i * integerBinomial n i) •
      rawVacuumPairing J x (M a (m+i) y)
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right ∧
      (∑ᶠ i, left i) = (-1 : ℂ)^(n+1) • (∑ᶠ i, right i) := by
  let m := 2*d-2-n
  have hL (i : ℕ) : rawVacuumPairing J (M a (n+i) x) y =
      vacuumAt J (d+s-(n+i)-1) t (M a (n+i) x) y :=
    rawVacuumPairing_eq_vacuumAt _ _ _ _ _ (twisted_mode_energy a d _ s x ha hx) hy
  have hR (i : ℕ) : rawVacuumPairing J x (M a (m+i) y) =
      vacuumAt J s (d+t-(m+i)-1) x (M a (m+i) y) :=
    rawVacuumPairing_eq_vacuumAt _ _ _ _ _ hx (twisted_mode_energy a d _ t y ha hy)
  dsimp only
  simp only [hL, ← show m = 2*d-2-n from rfl, hR]
  exact quasiprimary_vacuum_ward J a d n s t ha hea x y

#print axioms rawVacuumPairing_eq_vacuumAt
#print axioms rawVacuumPairing_ward_homogeneous

/-- On the actual negative twisted slice, the physical conformal mode 2 is L(1). -/
abbrev twistedL1 : Module.End ℂ X := M ω 2

private theorem twisted_virasoro_apply (j : ℤ) (x : X) :
    L D hu hD j (0, x) = (0, M ω (j + 1) x) := by
  change (((OriginalOrbifoldField.Y D hu hD) (ω, 0))[[j+1]]) (0, x) = _
  calc
    _ = (fixedMode D ω (j+1) 0, M ω (j+1) x) :=
      Y_fixed_ncoeff_apply D hu hD (j+1) ω (0,x)
    _ = ((0 : V), M ω (j+1) x) := Prod.ext (map_zero (fixedMode D ω (j+1))) rfl

private theorem twistedL0_l1 (x : X) :
    twistedL0 (twistedL1 x) - twistedL1 (twistedL0 x) = -twistedL1 x := by
  have h := LinearMap.congr_fun
    (OriginalOrbifoldConformal.L_virasoro D hu hD leech_spec.1 0 1) ((0, x))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply, twisted_virasoro_apply] at h
  have hh := congrArg Prod.snd h
  simpa only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, zero_add, zero_sub,
    Int.cast_neg, Int.cast_one, neg_one_smul, one_ne_zero, ite_false, zero_smul, add_zero,
    Prod.snd_neg, show (1 : ℤ) + 1 = 2 by decide] using hh

private theorem twistedL1_pow_weight (s : ℤ) (x : X)
    (hx : twistedL0 x = (s : ℂ) • x) (i : ℕ) :
    twistedL0 ((twistedL1 ^ i) x) = ((s-(i : ℤ) : ℤ) : ℂ) • (twistedL1 ^ i) x := by
  induction i with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero] using hx
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := twistedL0_l1 ((twistedL1 ^ i) x)
    rw [ih, map_smul] at h
    push_cast at h ⊢
    linear_combination (norm := module) h

private theorem twistedL1_powers_finite (x : X) :
    Function.HasFiniteSupport (fun i : ℕ => (twistedL1 ^ i) x) := by
  have hx : x ∈ Submodule.span ℂ {w : X | ∃ s : ℤ, twistedL0 w = (s : ℂ) • w} := by
    rw [integer_eigenvectors_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | zero => simp [Function.HasFiniteSupport, Function.support]
  | add x₁ x₂ _ _ h₁ h₂ =>
    simpa only [map_add, Pi.add_apply] using
      (show Function.HasFiniteSupport (fun _ => _) from h₁.add h₂)
  | smul c x _ h =>
    simp only [map_smul]
    refine h.subset ?_
    intro i hi hz
    change (twistedL1 ^ i) x = 0 at hz
    exact hi (show c • (twistedL1 ^ i) x = 0 by rw [hz, smul_zero])
  | mem x hx =>
    obtain ⟨s, hs⟩ := hx
    refine ((Finset.range (s.toNat + 1)).finite_toSet).subset ?_
    intro i hi
    have hn : (twistedL1 ^ i) x ≠ 0 := hi
    have he := twistedL1_pow_weight s x hs i
    obtain ⟨N, hN, _⟩ := fixedParity_conformal_eigenweight (-1)
      (((s-(i : ℤ) : ℤ) : ℂ)) _ hn he
    have hr := congrArg Complex.re hN
    simp only [Complex.intCast_re, Complex.add_re, Complex.div_ofNat_re,
      Complex.natCast_re] at hr
    norm_num at hr
    have hNpos : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hpos : 0 ≤ ((s - (i : ℤ) : ℤ) : ℝ) := by
      push_cast
      linarith
    have hspos : 0 ≤ s - (i : ℤ) := by exact_mod_cast hpos
    have hle : (i : ℤ) ≤ s := by omega
    change i ∈ Finset.range (s.toNat + 1)
    apply Finset.mem_range.mpr
    omega

private theorem exponential_terms_finite (z : ℂ) (x : X) :
    Function.HasFiniteSupport (fun i : ℕ => (z^i / (i.factorial : ℂ)) • (twistedL1 ^ i) x) :=
  (twistedL1_powers_finite x).subset (by
    intro i hi hz
    change (twistedL1 ^ i) x = 0 at hz
    exact hi (show (z^i / (i.factorial : ℂ)) • (twistedL1 ^ i) x = 0 by rw [hz, smul_zero]))

/-- The finite exponential of the actual lowering mode at a complex parameter. -/
def twistedExp (z : ℂ) : Module.End ℂ X where
  toFun x := ∑ᶠ i : ℕ, (z^i / (i.factorial : ℂ)) • (twistedL1 ^ i) x
  map_add' x y := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib (exponential_terms_finite z x) (exponential_terms_finite z y)
  map_smul' c x := by
    simp only [RingHom.id_apply, map_smul, smul_comm _ c]
    exact (smul_finsum' c (exponential_terms_finite z x)).symm

private abbrev twistedGrade (s : ℤ) : Submodule ℂ X := twistedL0.eigenspace (s : ℂ)

private theorem twistedGrades_internal : DirectSum.IsInternal twistedGrade := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact twistedL0.eigenspaces_iSupIndep.comp (Int.cast_injective (α := ℂ))
  · rw [Submodule.iSup_eq_span]
    convert integer_eigenvectors_span using 2
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_ofPred_eq, Module.End.mem_eigenspace_iff,
      twistedGrade]

/-- The sign (-1)^s on the exact integral conformal weight s. -/
def twistedWeightSign : Module.End ℂ X := by
  classical
  let C := DirectSum.coeLinearMap twistedGrade
  let R := (LinearEquiv.ofBijective C twistedGrades_internal).symm.toLinearMap
  exact (DirectSum.toModule ℂ ℤ X
    (fun s => ((-1 : ℂ)^s) • (twistedGrade s).subtype)).comp R

theorem twistedWeightSign_apply (s : ℤ) (x : X) (hx : twistedL0 x = (s : ℂ) • x) :
    twistedWeightSign x = (-1 : ℂ)^s • x := by
  classical
  let v : twistedGrade s := ⟨x, Module.End.mem_eigenspace_iff.mpr hx⟩
  let C := DirectSum.coeLinearMap twistedGrade
  let e := LinearEquiv.ofBijective C twistedGrades_internal
  have hv : e.symm x = DirectSum.lof ℂ ℤ (fun s => twistedGrade s) s v := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (DirectSum.coeLinearMap_lof twistedGrade s v).symm
  change DirectSum.toModule ℂ ℤ X
    (fun s => ((-1 : ℂ)^s) • (twistedGrade s).subtype) (e.symm x) = _
  rw [hv, DirectSum.toModule_lof, LinearMap.smul_apply]
  rfl

/-- The vacuum pairing after the two finite transformations on the original negative slice. -/
def transformedPairing (J : operatorSpace) : LinearMap.BilinForm ℂ X :=
  (rawVacuumPairing J).compl₁₂ ((twistedExp 1).comp twistedWeightSign) (twistedExp (-1))

#print axioms transformedPairing


private theorem linear_ext_on_weights {U : Type*} [AddCommGroup U] [Module ℂ U]
    {f g : X →ₗ[ℂ] U}
    (h : ∀ (s : ℤ) (x : X), twistedL0 x = (s : ℂ) • x → f x = g x) :
    f = g := by
  apply LinearMap.ext_on integer_eigenvectors_span
  rintro x ⟨s, hs⟩
  exact h s x hs

private theorem shifted_modes_finite (a : V) (n : ℤ) (x : X) :
    Function.HasFiniteSupport (fun i : ℕ => M a (n+i) x) := by
  let b := HahnSeries.order ((HahnModule.of ℂ).symm ((ρ a) x))
  refine ((Finset.range ((-(n+1+b)).toNat + 1)).finite_toSet).subset ?_
  intro i hi
  by_contra h
  apply hi
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  change -(n + (i : ℤ)) - 1 < b
  have h' : (-(n+1+b)).toNat + 1 ≤ i := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using h
  omega

private theorem binomial_terms_finite (z : ℂ) (b n : ℤ) (a : V) (x : X) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (z^i * integerBinomial b i) • M a (n+i) x) :=
  (shifted_modes_finite a n x).smul_right (fun i => z^i * integerBinomial b i)

/-- The finite binomial shift of a fixed-source mode on the negative module. -/
def binomialShift (z : ℂ) (b n : ℤ) (a : V) : Module.End ℂ X where
  toFun x := ∑ᶠ i : ℕ, (z^i * integerBinomial b i) • M a (n+i) x
  map_add' x y := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib (binomial_terms_finite z b n a x) (binomial_terms_finite z b n a y)
  map_smul' c x := by
    simp only [RingHom.id_apply, map_smul, smul_comm _ c]
    exact (smul_finsum' c (binomial_terms_finite z b n a x)).symm

private theorem map_binomialShift {U : Type*} [AddCommGroup U] [Module ℂ U]
    (f : X →ₗ[ℂ] U) (z : ℂ) (b n : ℤ) (a : V) (x : X) :
    f (binomialShift z b n a x) =
      ∑ᶠ i : ℕ, (z^i * integerBinomial b i) • f (M a (n+i) x) := by
  calc
    _ = ∑ᶠ i : ℕ, f ((z^i * integerBinomial b i) • M a (n+i) x) :=
      map_finsum f (binomial_terms_finite z b n a x)
    _ = _ := by simp only [map_smul]

set_option maxHeartbeats 600000 in
-- The two pointwise finite sums are transported through the actual bilinear form.
/-- The finite Ward identity on arbitrary vectors, via the integral algebraic
energy decomposition of the negative twisted Leech module. -/
theorem rawVacuumPairing_ward (J : operatorSpace) (a : V) (d n : ℤ)
    (ha : a.val ∈ grade D d) (hea : sugawaraMode D (gramComplex D)⁻¹ 1 a.val = 0)
    (x y : X) :
    let m := 2*d-2-n
    rawVacuumPairing J (binomialShift 1 m n a x) y =
      (-1 : ℂ)^(n+1) • rawVacuumPairing J x (binomialShift (-1) n m a y) := by
  let m := 2*d-2-n
  let F := rawVacuumPairing J
  let A := binomialShift 1 m n a
  let C := binomialShift (-1) n m a
  let G : LinearMap.BilinForm ℂ X := LinearMap.comp F A
  let H := (-1 : ℂ)^(n+1) • F.compl₂ C
  change G x y = H x y
  have h : G = H := by
    apply linear_ext_on_weights
    intro s u hsu
    apply linear_ext_on_weights
    intro t v htv
    change F (A u) v = (-1 : ℂ)^(n+1) • F u (C v)
    have hL : F (A u) v = ∑ᶠ i : ℕ, integerBinomial m i • F (M a (n+i) u) v := by
      change F.flip v (binomialShift 1 m n a u) = _
      refine (map_binomialShift (F.flip v) 1 m n a u).trans ?_
      simp only [one_pow, one_mul]
      rfl
    have hR : F u (C v) = ∑ᶠ i : ℕ, ((-1 : ℂ)^i * integerBinomial n i) •
        F u (M a (m+i) v) :=
      map_binomialShift (F u) (-1) n m a v
    have hw := (rawVacuumPairing_ward_homogeneous J a d n s t ha hea u v hsu htv).2.2
    exact hL.trans (hw.trans (congrArg (fun c : ℂ => (-1 : ℂ)^(n+1) • c) hR.symm))
  exact congrArg (fun K : LinearMap.BilinForm ℂ X => K x y) h

#print axioms rawVacuumPairing_ward


open LatticeHalfFockChargedTensorCoefficients (ActualTensor)
open private A T S c dividedAd dividedAd_eq_sum homogeneous from
  D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
open private fixedParitySlice_mode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldSectorModules

private theorem twistedMode_val (a : V) (n : ℤ) (x : X) :
    (M a n x).val = (A D hu (-2*n-2) a.val) x.val :=
  fixedParitySlice_mode_val D hu (-1) a n x

private theorem twistedL1_val (x : X) :
    (twistedL1 x).val = T D hu x.val := by
  have he := OriginalOrbifoldConformal.L_twisted_apply D hu hD 1 (0,x)
  have hh := congrArg (fun p : OriginalOrbifoldField.Carrier D hu => p.2.val)
    (twisted_virasoro_apply 1 x)
  exact hh.symm.trans he

private theorem twistedL1_pow_val (i : ℕ) (x : X) :
    ((twistedL1 ^ i) x).val = (T D hu ^ i) x.val := by
  induction i with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ i ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      twistedL1_val, ih]

set_option maxHeartbeats 1000000 in
-- The all-order tensor identity is restricted along the actual parity subtype.
private theorem quasiprimary_conjugation_coefficient (a : V) (d n : ℤ)
    (ha : a.val ∈ grade D d) (hea : S D 1 a.val = 0) (x : X) (k : ℕ) :
    (∑ i ∈ Finset.range (k+1),
      ((-1 : ℂ)^(k-i) / ((i.factorial : ℂ) * ((k-i).factorial : ℂ))) •
        (twistedL1 ^ i) (M a n ((twistedL1 ^ (k-i)) x))) =
      integerBinomial (2*d-2-n) k • M a (n+k) x := by
  classical
  let e : ℤ := -2*n-2
  have ha0 : S D 0 a.val = (d : ℂ) • a.val := by
    change sugawaraMode D (gramComplex D)⁻¹ 0 a.val = _
    rw [← actualInverse_eq]
    exact (actualL0_eigen_iff_grade D (actualInverse D)
      (actualInverse_left D hu) (actualInverse_right D hu) d a.val).mpr ha
  have h := homogeneous D hu d a.val ha0 k e
  have hsum : (∑ j ∈ Finset.range (k+1), c (2*(d:ℂ)+(e:ℂ)/2-1) k j •
        A D hu (e-2*(k:ℤ)+2*(j:ℤ)) ((S D 1 ^ j) a.val)) =
      integerBinomial (2*d-2-n) k • A D hu (-2*(n+k)-2) a.val := by
    rw [Finset.sum_eq_single 0]
    · simp only [c, Nat.zero_le, ite_true, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, Nat.cast_zero, mul_zero, add_zero, pow_zero, Module.End.one_apply]
      have hi : 2*(d:ℂ)+(e:ℂ)/2-1 = ((2*d-2-n : ℤ) : ℂ) := by
        dsimp [e]
        push_cast
        ring
      have he : e-2*(k:ℤ) = -2*(n+k)-2 := by dsimp [e]; ring
      rw [hi, sub_zero, he]
      have hcast := Ring.map_choose (Int.castRingHom ℂ) (2*d-2-n) k
      exact congrArg (fun z : ℂ => z • A D hu (-2*(n+k)-2) a.val) hcast.symm
    · intro j _ hj
      have hj' : (S D 1 ^ j) a.val = 0 :=
        Module.End.pow_map_zero_of_le (Nat.pos_of_ne_zero hj) (by simpa only [pow_one] using hea)
      rw [hj', map_zero, smul_zero]
    · intro hz
      exact (hz (Finset.mem_range.mpr (Nat.zero_lt_succ k))).elim
  rw [hsum, dividedAd_eq_sum] at h
  have hx := LinearMap.congr_fun h x.val
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul,
    twistedL1_pow_val, twistedMode_val, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at hx ⊢
  exact hx

private theorem zero_of_negative_weight (s : ℤ) (x : X)
    (hx : twistedL0 x = (s : ℂ) • x) (hs : s < 0) : x = 0 := by
  by_contra hn
  obtain ⟨N, hN, _⟩ := fixedParity_conformal_eigenweight (-1) (s : ℂ) x hn hx
  have hr := congrArg Complex.re hN
  simp only [Complex.intCast_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re] at hr
  norm_num at hr
  have hN' : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hs' : (s : ℝ) < 0 := by exact_mod_cast hs
  linarith

private theorem twistedExp_range (z : ℂ) (s : ℤ) (K : ℕ) (x : X)
    (hx : twistedL0 x = (s : ℂ) • x) (hK : s < (K : ℤ)) :
    twistedExp z x = ∑ i ∈ Finset.range K,
      (z^i / (i.factorial : ℂ)) • (twistedL1 ^ i) x := by
  change (∑ᶠ i : ℕ, (z^i / (i.factorial : ℂ)) • (twistedL1 ^ i) x) = _
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra hni
  have hki : K ≤ i := Nat.le_of_not_gt (fun h => hni (Finset.mem_range.mpr h))
  have hzero := zero_of_negative_weight _ _ (twistedL1_pow_weight s x hx i) (by omega)
  apply hi
  change (z^i / (i.factorial : ℂ)) • (twistedL1 ^ i) x = 0
  rw [hzero, smul_zero]

private theorem sum_antidiagonal_range {U : Type*} [AddCommMonoid U] (K : ℕ)
    (f : ℕ × ℕ → U) (hf : ∀ i j : ℕ, K ≤ i + j → f (i,j) = 0) :
    (∑ j ∈ Finset.range K, ∑ i ∈ Finset.range K, f (i,j)) =
      ∑ k ∈ Finset.range (K+K), ∑ i ∈ Finset.range (k+1), f (i,k-i) := by
  classical
  let P := Finset.range K ×ˢ Finset.range K
  let N := Finset.range (K+K)
  let g := fun p : ℕ × ℕ => p.1 + p.2
  have hg : ∀ p ∈ P, g p ∈ N := by
    intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
    exact Finset.mem_range.mpr (Nat.add_lt_add (Finset.mem_range.mp h₁) (Finset.mem_range.mp h₂))
  calc
    _ = ∑ p ∈ P, f p := by
      dsimp only [P]
      rw [Finset.sum_product]
      exact Finset.sum_comm
    _ = ∑ k ∈ N, ∑ p ∈ P.filter (fun p => g p = k), f p :=
      (Finset.sum_fiberwise_of_maps_to hg f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk f k]
      apply Finset.sum_subset
      · intro p hp
        exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (Finset.mem_filter.mp hp).2
      · intro p hp hnot
        have hsum : p.1+p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        have hsing : K ≤ p.1 + p.2 := by
          by_contra hlt
          apply hnot
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hsum⟩
          · exact Finset.mem_range.mpr (by omega)
          · exact Finset.mem_range.mpr (by omega)
        exact hf p.1 p.2 hsing

private theorem exponential_diagonal_scalar (z : ℂ) (i j k : ℕ) (h : i + j = k) :
    (z^i / (i.factorial : ℂ)) * ((-z)^j / (j.factorial : ℂ)) =
      z^k * ((-1 : ℂ)^j / ((i.factorial : ℂ) * (j.factorial : ℂ))) := by
  rw [← h, pow_add, neg_pow]
  ring

private def conjugationTerm (z : ℂ) (a : V) (n : ℤ) (x : X) (p : ℕ × ℕ) : X :=
  ((z^p.1 / (p.1.factorial : ℂ)) * ((-z)^p.2 / (p.2.factorial : ℂ))) •
    (twistedL1 ^ p.1) (M a n ((twistedL1 ^ p.2) x))

set_option maxHeartbeats 600000 in
-- The signed divided powers on both sides are applied to the original slice.
/-- Evaluation at a fixed total lowering degree of the two finite exponentials. -/
private theorem conjugationTerm_sum (z : ℂ) (a : V) (d n : ℤ) (x : X) (k : ℕ)
    (ha : a.val ∈ grade D d) (hea : sugawaraMode D (gramComplex D)⁻¹ 1 a.val = 0) :
    (∑ i ∈ Finset.range (k+1), conjugationTerm z a n x (i,k-i)) =
      (z^k * integerBinomial (2*d-2-n) k) • M a (n+k) x := by
  let g (i : ℕ) : X :=
    ((-1 : ℂ)^(k-i) / ((i.factorial : ℂ) * ((k-i).factorial : ℂ))) •
      (twistedL1 ^ i) (M a n ((twistedL1 ^ (k-i)) x))
  have hg (i : ℕ) (hi : i ∈ Finset.range (k+1)) :
      conjugationTerm z a n x (i,k-i) = z^k • g i := by
    have he : i+(k-i)=k := by have := Finset.mem_range.mp hi; omega
    simp only [conjugationTerm, g, smul_smul,
      exponential_diagonal_scalar z i (k-i) k he]
  calc
    _ = ∑ i ∈ Finset.range (k+1), z^k • g i := Finset.sum_congr rfl hg
    _ = z^k • (∑ i ∈ Finset.range (k+1), g i) := (Finset.smul_sum ..).symm
    _ = z^k • (integerBinomial (2*d-2-n) k • M a (n+k) x) :=
      congrArg (fun w : X => z^k • w) (quasiprimary_conjugation_coefficient a d n ha hea x k)
    _ = _ := smul_smul _ _ _

set_option maxHeartbeats 1200000 in
-- The finite sum is regrouped using the total lowering degree on the actual carrier.
/-- Conjugation by the two opposite finite flows is the binomial shift of a
quasiprimary physical mode. -/
theorem quasiprimary_conjugation (z : ℂ) (a : V) (d n : ℤ)
    (ha : a.val ∈ grade D d) (hea : sugawaraMode D (gramComplex D)⁻¹ 1 a.val = 0)
    (x : X) :
    twistedExp z (M a n (twistedExp (-z) x)) = binomialShift z (2*d-2-n) n a x := by
  let Q := (twistedExp z).comp ((M a n).comp (twistedExp (-z)))
  let R := binomialShift z (2*d-2-n) n a
  change Q x = R x
  have hQR : Q = R := by
    apply linear_ext_on_weights
    intro s v hv
    change twistedExp z (M a n (twistedExp (-z) v)) = R v
    let K := (max s (d+s-n-1)).toNat + 1
    have hK : s < (K : ℤ) ∧ d+s-n-1 < (K : ℤ) := by
      dsimp [K]
      omega
    let f := conjugationTerm z a n v
    have he (j : ℕ) := twisted_mode_energy a d n (s-j) ((twistedL1 ^ j) v)
      ha (twistedL1_pow_weight s v hv j)
    have htail (i j : ℕ) (hij : K ≤ i+j) : f (i,j) = 0 := by
      have hh := twistedL1_pow_weight (d+(s-j)-n-1) _ (he j) i
      have hz := zero_of_negative_weight _ _ hh (by omega)
      simp only [f, conjugationTerm, hz, smul_zero]
    let Louter : Module.End ℂ X := (twistedExp z).comp (M a n)
    have himage : Louter (twistedExp (-z) v) =
        ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range K, f (i,j) := by
      calc
        _ = Louter (∑ j ∈ Finset.range K,
            ((-z)^j / (j.factorial : ℂ)) • (twistedL1 ^ j) v) :=
          congrArg (fun w : X => Louter w) (twistedExp_range (-z) s K v hv hK.1)
        _ = _ := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [map_smul]
          change ((-z)^j / (j.factorial : ℂ)) •
            twistedExp z (M a n ((twistedL1 ^ j) v)) = _
          rw [twistedExp_range z _ K _ (he j) (by omega), Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [f, conjugationTerm, smul_smul, mul_comm]
    let r (i : ℕ) : X := (z^i * integerBinomial (2*d-2-n) i) • M a (n+i) v
    have hR : R v = ∑ i ∈ Finset.range (K+K), r i := by
      change (∑ᶠ i, r i) = _
      apply finsum_eq_sum_of_support_subset
      intro i hi
      by_contra hni
      have hki : K+K ≤ i := Nat.le_of_not_gt (fun h => hni (Finset.mem_range.mpr h))
      have hhe := twisted_mode_energy a d (n+i) s v ha hv
      have hz := zero_of_negative_weight _ _ hhe (by omega)
      apply hi
      change r i = 0
      simp only [r, hz, smul_zero]
    have hcoeff (k : ℕ) (_ : k ∈ Finset.range (K+K)) :
        (∑ i ∈ Finset.range (k+1), f (i,k-i)) = r k :=
      conjugationTerm_sum z a d n v k ha hea
    exact himage.trans ((sum_antidiagonal_range K f htail).trans
      ((Finset.sum_congr rfl hcoeff).trans hR.symm))
  exact LinearMap.congr_fun hQR x

#print axioms quasiprimary_conjugation

private theorem sugawara_vacuum_zero (j : ℤ) (hj : -1 ≤ j) :
    sugawaraMode D (actualInverse D) j (vacuum D) = 0 := by
  rw [← LatticeActualConformalState.omega_modes]
  exact stateField_creativity D _ _ (by omega)

private theorem vacuum_quasiprimary :
    (fixedVacuum D).val ∈ grade D 0 ∧
      sugawaraMode D (gramComplex D)⁻¹ 1 (fixedVacuum D).val = 0 := by
  refine ⟨(gradeVacuum D).property.1, ?_⟩
  rw [← actualInverse_eq]
  exact sugawara_vacuum_zero 1 (by decide)

set_option maxHeartbeats 600000 in
-- The transport uses modes on the original carrier subtypes.
private theorem exp_inverse (z : ℂ) (x : X) :
    twistedExp z (twistedExp (-z) x) = x := by
  have h := quasiprimary_conjugation z (fixedVacuum D) 0 (-1)
    vacuum_quasiprimary.1 vacuum_quasiprimary.2 x
  simp only [fixedParitySlice_vacuum_ncoeff, ite_true] at h
  rw [h]
  change (∑ᶠ i : ℕ, (z^i * integerBinomial (2*(0:ℤ)-2-(-1)) i) •
    M (fixedVacuum D) (-1+i) x) = x
  rw [finsum_eq_single _ 0]
  · simp only [Nat.cast_zero, add_zero, pow_zero, integerBinomial, Ring.choose_zero_right,
      Int.cast_one, mul_one, one_smul, fixedParitySlice_vacuum_ncoeff, ite_true]
  · intro i hi
    have hn : (-1 : ℤ) + i ≠ -1 := by omega
    simp only [fixedParitySlice_vacuum_ncoeff, hn, ite_false, smul_zero]

private theorem exp_mode (z : ℂ) (a : V) (d n : ℤ)
    (ha : a.val ∈ grade D d) (hea : sugawaraMode D (gramComplex D)⁻¹ 1 a.val = 0)
    (x : X) :
    twistedExp z (M a n x) = binomialShift z (2*d-2-n) n a (twistedExp z x) := by
  have h := quasiprimary_conjugation z a d n ha hea (twistedExp z x)
  have hi := exp_inverse (-z) x
  rw [neg_neg] at hi
  exact (congrArg (fun w : X => twistedExp z (M a n w)) hi).symm.trans h

set_option maxHeartbeats 600000 in
-- The transport uses modes on the original carrier subtypes.
private theorem weightSign_mode (a : V) (d n : ℤ) (ha : a.val ∈ grade D d) (x : X) :
    twistedWeightSign (M a n x) = (-1 : ℂ)^(d-n-1) • M a n (twistedWeightSign x) := by
  let f := twistedWeightSign.comp (M a n)
  let g := (-1 : ℂ)^(d-n-1) • (M a n).comp twistedWeightSign
  have h : f = g := by
    apply linear_ext_on_weights
    intro s u hsu
    change twistedWeightSign (M a n u) = (-1 : ℂ)^(d-n-1) • M a n (twistedWeightSign u)
    have h0 := twistedWeightSign_apply (d+s-n-1) (M a n u)
      (twisted_mode_energy a d n s u ha hsu)
    have hp := congrArg (fun w : X => M a n w) (twistedWeightSign_apply s u hsu)
    simp only [map_smul] at hp
    have hi : (-1 : ℂ)^(d+s-n-1) = (-1 : ℂ)^(d-n-1) * (-1 : ℂ)^s := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      congr 1
      ring
    calc
      _ = _ := h0
      _ = ((-1 : ℂ)^(d-n-1) * (-1 : ℂ)^s) • M a n u :=
        congrArg (fun c : ℂ => c • M a n u) hi
      _ = (-1 : ℂ)^(d-n-1) • ((-1 : ℂ)^s • M a n u) := (smul_smul _ _ _).symm
      _ = _ := congrArg (fun w : X => (-1 : ℂ)^(d-n-1) • w) hp.symm
  exact LinearMap.congr_fun h x

set_option maxHeartbeats 1000000 in
-- The transport composes both finite flows with the vacuum coefficient form.
/-- Every lawful rational field yields a bilinear form with opposite-mode
covariance for every actual quasiprimary fixed-source mode. -/
theorem transformedPairing_adjoint (J : operatorSpace) (a : V) (d n : ℤ)
    (ha : a.val ∈ grade D d) (hea : sugawaraMode D (gramComplex D)⁻¹ 1 a.val = 0)
    (u v : X) :
    transformedPairing J (M a n u) v =
      (-1 : ℂ)^d • transformedPairing J u (M a (2*d-2-n) v) := by
  let m := 2*d-2-n
  let x := twistedExp 1 (twistedWeightSign u)
  let y := twistedExp (-1) v
  let F := rawVacuumPairing J
  change F (twistedExp 1 (twistedWeightSign (M a n u))) y =
    (-1 : ℂ)^d • F x (twistedExp (-1) (M a m v))
  have hm : 2*d-2-m = n := by dsimp [m]; ring
  have h := rawVacuumPairing_ward J a d n ha hea x y
  change F (binomialShift 1 m n a x) y =
    (-1 : ℂ)^(n+1) • F x (binomialShift (-1) n m a y) at h
  have hleft := congrArg (fun w : X => twistedExp 1 w) (weightSign_mode a d n ha u)
  simp only [map_smul] at hleft
  have hleftMode := exp_mode 1 a d n ha hea (twistedWeightSign u)
  have hrightMode := exp_mode (-1) a d m ha hea v
  have hright : twistedExp (-1) (M a m v) = binomialShift (-1) n m a y :=
    hrightMode.trans (congrArg (fun k : ℤ => binomialShift (-1) k m a y) hm)
  have hleft' := hleft.trans
    (congrArg (fun w : X => (-1 : ℂ)^(d-n-1) • w) hleftMode)
  have hfirst := congrArg (F.flip y) hleft'
  simp only [map_smul] at hfirst
  have hsign : (-1 : ℂ)^(d-n-1) * (-1 : ℂ)^(n+1) = (-1 : ℂ)^d := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    congr 1
    ring
  calc
    _ = (-1 : ℂ)^(d-n-1) • F (binomialShift 1 m n a x) y := hfirst
    _ = (-1 : ℂ)^(d-n-1) • ((-1 : ℂ)^(n+1) • F x (binomialShift (-1) n m a y)) :=
      congrArg (fun c : ℂ => (-1 : ℂ)^(d-n-1) • c) h
    _ = (-1 : ℂ)^d • F x (binomialShift (-1) n m a y) := by rw [smul_smul, hsign]
    _ = _ := congrArg (fun w : X => (-1 : ℂ)^d • F x w) hright.symm

set_option maxHeartbeats 600000 in
-- The transport uses modes on the original carrier subtypes.
private theorem conformal_quasiprimary :
    (ω).val ∈ grade D 2 ∧ sugawaraMode D (gramComplex D)⁻¹ 1 (ω).val = 0 := by
  let Q := sugawaraMode D (actualInverse D)
  have hω : Q (-2) (vacuum D) = (ω).val := by
    change sugawaraMode D (actualInverse D) (-2) (vacuum D) = _
    rw [← LatticeActualConformalState.omega_modes]
    exact LatticeAllStateField.stateField_creation D _
  have comm (j : ℤ) (hj : j = 0 ∨ j = 1) :
      Q j (ω).val = ((j+2 : ℤ) : ℂ) • Q (j-2) (vacuum D) := by
    have h := LinearMap.congr_fun (LatticeSugawaraVirasoro.sugawaraMode_virasoro D
      (actualInverse D) (actualInverse_left D hu) (actualInverse_right D hu) j (-2))
      (vacuum D)
    have hz : j + (-2 : ℤ) ≠ 0 := by omega
    have hzero : Q j (vacuum D) = 0 := sugawara_vacuum_zero j (by omega)
    simp only [LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, hz, ite_false, zero_smul, add_zero] at h
    change Q j (Q (-2) (vacuum D)) - Q (-2) (Q j (vacuum D)) = _ at h
    rw [hω, hzero, map_zero, sub_zero] at h
    have e : j - (-2 : ℤ) = j+2 := by omega
    have e' : j + (-2 : ℤ) = j-2 := by omega
    simpa only [e, e'] using h
  constructor
  · apply (actualL0_eigen_iff_grade D (actualInverse D) (actualInverse_left D hu)
      (actualInverse_right D hu) 2 _).mp
    simpa only [Int.zero_add, Int.zero_sub, hω, Int.cast_ofNat] using comm 0 (Or.inl rfl)
  · rw [← actualInverse_eq]
    have h := comm 1 (Or.inr rfl)
    rw [show (1 : ℤ) - 2 = -1 by decide, sugawara_vacuum_zero _ (by decide), smul_zero] at h
    exact h

/-- The transformed vacuum pairing is orthogonal across distinct conformal grades. -/
theorem transformedPairing_grade_orthogonal (J : operatorSpace) (s t : ℤ) (u v : X)
    (hsu : twistedL0 u = (s : ℂ) • u) (hv : twistedL0 v = (t : ℂ) • v) (hst : s ≠ t) :
    transformedPairing J u v = 0 := by
  have h := transformedPairing_adjoint J ω 2 1
    conformal_quasiprimary.1 conformal_quasiprimary.2 u v
  have hz : (-1 : ℂ)^(2 : ℤ) = 1 := by norm_num
  simp only [hz, one_smul, show (2 : ℤ)*2-2-1 = 1 by decide] at h
  change transformedPairing J (twistedL0 u) v = transformedPairing J u (twistedL0 v) at h
  rw [hsu, hv, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact (mul_eq_mul_right_iff.mp h).resolve_left (by exact_mod_cast hst)

#print axioms transformedPairing_adjoint
#print axioms transformedPairing_grade_orthogonal

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedVacuumPairing
