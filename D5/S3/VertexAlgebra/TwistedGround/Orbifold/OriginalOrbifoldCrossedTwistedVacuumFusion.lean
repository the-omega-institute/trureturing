/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldCrossedTwistedVacuumFusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldCrossedTwistedVacuumFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The crossed twisted Leech pair has zero full rational-mode vacuum fusion. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedVacuumDetection
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldFixedQuasiprimary

/-! Opposite twisted parities have disjoint conformal weights. The conformal
Jacobi equations lower the input grades in the vacuum coefficient, and the
fixed-mode Ward identity then detects every output mode. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldCrossedTwistedVacuumFusion

open ActualLeechHyperbolic (leechData leech_spec)
open FixedGradedDuality (fixedGradeSubmodule fixedGrades_iSup)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace
  (actualAmbientBasis actualTensorL0 actual_basis_eigenvalue oddWeight)
open LatticeInvolution (FixedCarrier fixedMode fixedVacuum)
open LatticePositiveEnergy (grade)
open OriginalOrbifoldConformal (conformalVector)
open OriginalOrbifoldFixedQuasiprimary (fixedL fixed_grade_one)
open OriginalOrbifoldSectorModules (fixedParityY)
open OriginalOrbifoldTwistedModeMorphisms
  (fixedParity_conformal_mode_val fixedParity_conformal_eigenweight)
open OriginalOrbifoldTwistedVacuumDetection (vacuumFunctional eq_zero_of_fixedMode_vacuum)
open SourceBPZ.OriginalSourceCoevaluation (gradeVacuum)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open VacuumFirstIntertwinerDraft (mode)
open private fixedL_zero_iff_grade fixedL_grade from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldFixedQuasiprimary
open private theta_projection from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
open private basis_parity from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private support_parity from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedModeMorphisms
open private lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private sum_signed_choose_zero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldVacuumFirstFusion

local notation "D" => leechData
local notation "hu" => And.left (And.right leech_spec)
local notation "V" => FixedCarrier leechData
local notation "ω" => Prod.fst (conformalVector D hu)

abbrev Twisted (s : ℂ) := paritySpace D hu s
abbrev Fields (s t : ℂ) := VacuumFirstIntertwinerDraft.Fields (Twisted s) (Twisted t) V

local notation "ρ" => fixedParityY D hu
private abbrev actionMode (s : ℂ) (a : V) (n : ℤ) : Module.End ℂ (Twisted s) :=
  (ρ s a)[[n]]

local notation "M" => actionMode

variable {s t : ℂ}

def leftTerm (J : Fields s t) (a : V) (u : Twisted s) (v : Twisted t)
    (p r : ℤ) (q : ℚ) (i : ℕ) : V :=
  integerBinomial p i • mode J (M s a (r + i) u) ((p : ℚ) + q - i) v

def firstTerm (J : Fields s t) (a : V) (u : Twisted s) (v : Twisted t)
    (p r : ℤ) (q : ℚ) (i : ℕ) : V :=
  (((-1 : ℂ) ^ i) * integerBinomial r i) •
    fixedMode D a (p + r - i) (mode J u (q + i) v)

def secondTerm (J : Fields s t) (a : V) (u : Twisted s) (v : Twisted t)
    (p r : ℤ) (q : ℚ) (i : ℕ) : V :=
  (((-1 : ℂ) ^ i) * integerBinomial r i) •
    (epsilon r • mode J u (q + (r : ℚ) - i) (M t a (p + i) v))

/-- The source derivative and all three finite mixed Jacobi sums at every rational mode.
Pointwise lower truncation is supplied by the Hahn field type. -/
structure Lawful (J : Fields s t) : Prop where
  source : ∀ (u : Twisted s) (q : ℚ) (v : Twisted t),
    mode J (M s ω 0 u) q v = -(q : ℂ) • mode J u (q - 1) v
  jacobi : ∀ (a : V) (u : Twisted s) (v : Twisted t) (p r : ℤ) (q : ℚ),
    Function.HasFiniteSupport (leftTerm J a u v p r q) ∧
    Function.HasFiniteSupport (firstTerm J a u v p r q) ∧
    Function.HasFiniteSupport (secondTerm J a u v p r q) ∧
      (∑ᶠ i, leftTerm J a u v p r q i) =
        (∑ᶠ i, firstTerm J a u v p r q i) - (∑ᶠ i, secondTerm J a u v p r q i)

/-- The two negative inputs recover the original lawful field predicate. -/
theorem lawful_negative_negative_iff (J : Fields (-1) (-1)) :
    Lawful J ↔ OriginalOrbifoldTwistedVacuumFusion.Lawful J := by
  constructor <;> intro h <;> exact ⟨h.source, h.jacobi⟩

private theorem vacuumFunctional_grade (d : ℤ) (hd : d ≠ 0)
    (w : V) (hw : w.val ∈ grade D d) : vacuumFunctional w = 0 :=
  sourcePairing_grade D d 0 hd w.val (fixedVacuum D).val hw (gradeVacuum D).property.1

private theorem linear_zero_on_fixed_grades (f : V →ₗ[ℂ] ℂ)
    (hf : ∀ (d : ℤ) (a : V), a.val ∈ grade D d → f a = 0) (w : V) : f w = 0 := by
  have hle : (⨆ d : ℤ, fixedGradeSubmodule D d) ≤ LinearMap.ker f :=
    iSup_le (fun d a ha => LinearMap.mem_ker.mpr (hf d a ha))
  rw [fixedGrades_iSup D (theta_projection D)] at hle
  exact LinearMap.mem_ker.mp (hle (show w ∈ (⊤ : Submodule ℂ V) from Submodule.mem_top))

private theorem vacuumFunctional_fixedL_on_grade (j : ℤ) (hj : j = 0 ∨ j = 1)
    (d : ℤ) (a : V) (ha : a.val ∈ grade D d) : vacuumFunctional (fixedL j a) = 0 := by
  by_cases hd : d = j
  · subst d
    rcases hj with rfl | rfl
    · have hz : fixedL 0 a = 0 := by
        simpa only [Int.cast_zero, zero_smul] using (fixedL_zero_iff_grade 0 a).mpr ha
      exact (congrArg vacuumFunctional hz).trans (map_zero vacuumFunctional)
    · have hm : a ∈ fixedGradeSubmodule D 1 := ha
      rw [fixed_grade_one] at hm
      have hz : a = 0 := by simpa only [Submodule.mem_bot] using hm
      calc
        vacuumFunctional (fixedL 1 a) = vacuumFunctional (fixedL 1 0) :=
          congrArg (fun x => vacuumFunctional (fixedL 1 x)) hz
        _ = vacuumFunctional 0 := congrArg vacuumFunctional (map_zero (fixedL 1))
        _ = 0 := map_zero vacuumFunctional
  · exact vacuumFunctional_grade (d - j) (sub_ne_zero.mpr hd) _ (fixedL_grade j d a ha)

private theorem vacuumFunctional_fixedL (j : ℤ) (hj : j = 0 ∨ j = 1) (w : V) :
    vacuumFunctional (fixedL j w) = 0 :=
  linear_zero_on_fixed_grades (vacuumFunctional.comp (fixedL j))
    (vacuumFunctional_fixedL_on_grade j hj) w

private theorem sum_choose_nat (p : ℕ) (g : ℕ → V) :
    (∑ᶠ i : ℕ, integerBinomial (p : ℤ) i • g i) =
      ∑ i ∈ Finset.range (p + 1), ((p.choose i : ℕ) : ℂ) • g i := by
  classical
  simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (p + 1))]
  intro i hi
  by_contra hout
  have hp : p < i := by simpa [Finset.mem_range] using hout
  exact hi (by simp [Nat.choose_eq_zero_of_lt hp])

private theorem sum_choose_one (g : ℕ → V) :
    (∑ᶠ i : ℕ, integerBinomial 1 i • g i) = g 0 + g 1 := by
  have h := sum_choose_nat 1 g
  simpa [Finset.sum_range_succ] using h

private theorem sum_choose_two (g : ℕ → V) :
    (∑ᶠ i : ℕ, integerBinomial 2 i • g i) = g 0 + (2 : ℂ) • g 1 + g 2 := by
  have h := sum_choose_nat 2 g
  simpa [Finset.sum_range_succ] using h

private theorem jacobi_zero {J : Fields s t} (hJ : Lawful J)
    (a : V) (u : Twisted s) (v : Twisted t) (p : ℤ) (q : ℚ) :
    (∑ᶠ i, leftTerm J a u v p 0 q i) =
      fixedMode D a p (mode J u q v) - mode J u q (M t a p v) := by
  simpa only [firstTerm, secondTerm, sum_signed_choose_zero, epsilon, zpow_zero,
    one_smul, Nat.cast_zero, Int.cast_zero, add_zero, sub_zero] using
    (hJ.jacobi a u v p 0 q).2.2.2

private def vacuumForm (J : Fields s t) (q : ℚ) : Twisted s →ₗ[ℂ] Twisted t →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun u v => vacuumFunctional (mode J u q v))
    (by intros; simp [mode])
    (by intros; simp [mode])
    (by intros; simp only [map_add])
    (by intros; simp only [map_smul])

private def twistedL0 (s : ℂ) : Module.End ℂ (Twisted s) := M s ω 1
private def twistedL1 (s : ℂ) : Module.End ℂ (Twisted s) := M s ω 2

local notation "L₀" => twistedL0
local notation "L₁" => twistedL1

private theorem mode_smul_left (J : Fields s t) (c : ℂ) (u : Twisted s) (q : ℚ)
    (v : Twisted t) : mode J (c • u) q v = c • mode J u q v := by
  simp [mode]

private theorem vacuum_weight {J : Fields s t} (hJ : Lawful J)
    (u : Twisted s) (v : Twisted t) (α β : ℂ)
    (hu₀ : L₀ s u = α • u) (hv₀ : L₀ t v = β • v) (q : ℚ) :
    (α + β - (q : ℂ) - 1) * vacuumForm J q u v = 0 := by
  have h := jacobi_zero hJ ω u v 1 q
  unfold leftTerm at h
  rw [sum_choose_one (fun i => mode J (M s ω (0 + i) u) ((1 : ℤ) + q - i) v)] at h
  simp only [Nat.cast_zero, Nat.cast_one, Int.cast_one, zero_add, sub_zero,
    add_sub_cancel_left] at h
  change mode J (M s ω 0 u) (1 + q) v + mode J (L₀ s u) q v =
    fixedL 0 (mode J u q v) - mode J u q (L₀ t v) at h
  rw [hJ.source, add_comm (1 : ℚ) q, add_sub_cancel_right, hu₀, hv₀] at h
  have hf := congrArg vacuumFunctional h
  simp only [map_add, map_sub, mode_smul_left, map_smul, vacuumFunctional_fixedL 0 (Or.inl rfl),
    Rat.cast_add, Rat.cast_one, zero_sub, smul_eq_mul] at hf
  change _ * vacuumFunctional (mode J u q v) = 0
  linear_combination hf

private theorem vacuum_lowering {J : Fields s t} (hJ : Lawful J)
    (u : Twisted s) (v : Twisted t) (α β : ℂ)
    (hu₀ : L₀ s u = α • u) (hv₀ : L₀ t v = β • v) (q : ℚ) :
    (α - β) * vacuumForm J q u v +
      vacuumForm J (q - 1) (L₁ s u) v + vacuumForm J (q - 1) u (L₁ t v) = 0 := by
  have h := jacobi_zero hJ ω u v 2 (q - 1)
  unfold leftTerm at h
  rw [sum_choose_two (fun i => mode J (M s ω (0 + i) u) ((2 : ℤ) + (q - 1) - i) v)] at h
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Int.cast_ofNat, zero_add, sub_zero] at h
  change mode J (M s ω 0 u) (2 + (q - 1)) v +
    (2 : ℂ) • mode J (L₀ s u) (2 + (q - 1) - 1) v +
    mode J (L₁ s u) (2 + (q - 1) - 2) v =
    fixedL 1 (mode J u (q - 1) v) - mode J u (q - 1) (L₁ t v) at h
  rw [hJ.source, show (2 : ℚ) + (q - 1) - 1 = q by ring,
    show (2 : ℚ) + (q - 1) - 2 = q - 1 by ring, hu₀] at h
  have hf := congrArg vacuumFunctional h
  simp only [map_add, map_sub, mode_smul_left, map_smul, vacuumFunctional_fixedL 1 (Or.inr rfl),
    Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one, zero_sub, smul_eq_mul] at hf
  have hw := vacuum_weight hJ u v α β hu₀ hv₀ q
  change _ * vacuumFunctional (mode J u q v) = 0 at hw
  change _ * vacuumFunctional (mode J u q v) +
      vacuumFunctional (mode J (L₁ s u) (q - 1) v) +
      vacuumFunctional (mode J u (q - 1) (L₁ t v)) = 0
  linear_combination hf - hw

private def weight (N : ℕ) : ℂ := 3 / 2 + (N : ℂ) / 2

private theorem oscillator_eigenvectors_span (s : ℂ) :
    Submodule.span ℂ {u : Twisted s | ∃ N : ℕ, (-1 : ℂ) ^ N = s ∧ L₀ s u = weight N • u} =
      ⊤ := by
  classical
  apply top_unique
  intro u _
  let b := actualAmbientBasis D hu
  let I := (b.repr u.val).support
  let x (j : I) : Twisted s := ⟨b j.val, by
    have hp := support_parity u j.val (Finsupp.mem_support_iff.mp j.property)
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, hp] using basis_parity D hu j.val⟩
  have hsum : ∑ j ∈ I.attach, b.repr u.val j.val • x j = u := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change ∑ j ∈ I.attach, b.repr u.val j.val • b j.val = u.val
    rw [Finset.sum_attach I (fun j => b.repr u.val j • b j)]
    exact b.linearCombination_repr u.val
  rw [← hsum]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨oddWeight D j.val.1, support_parity u j.val (Finsupp.mem_support_iff.mp j.property), ?_⟩
  apply Subtype.ext
  rw [twistedL0, fixedParity_conformal_mode_val]
  change actualTensorL0 D hu (b j.val) = weight (oddWeight D j.val.1) • b j.val
  have hrank : (leechData.rank : ℂ) / 16 = 3 / 2 := by rw [leech_spec.1]; norm_num
  simpa only [weight, hrank, Prod.mk.eta] using actual_basis_eigenvalue D hu j.val.1 j.val.2

private theorem linear_zero_on_eigenvectors (f : Twisted s →ₗ[ℂ] ℂ)
    (h : ∀ (N : ℕ) (u : Twisted s), (-1 : ℂ) ^ N = s → L₀ s u = weight N • u → f u = 0)
    (u : Twisted s) : f u = 0 := by
  have hker : (⊤ : Submodule ℂ (Twisted s)) ≤ LinearMap.ker f := by
    rw [← oscillator_eigenvectors_span s, Submodule.span_le]
    rintro x ⟨N, hN, hx⟩
    exact h N x hN hx
  exact hker (show u ∈ (⊤ : Submodule ℂ (Twisted s)) from Submodule.mem_top)

set_option maxHeartbeats 1200000 in
-- Compare the parity-subtype mode with the ambient corrected field.
private theorem twistedL1_val (u : Twisted s) :
    (L₁ s u).val = LatticeHalfFock.tensorL D
      (LatticeHalfFockChargedTensorCoefficients.ActualGround D hu) (actualInverse D) 1 u.val := by
  change (correctedField D hu (LatticeActualConformalState.omega D (actualInverse D))).coeff
    (-6) u.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega D hu _ (actualInverse_left D hu)]
  simp only [LatticeHalfFock.tensorStressField, HVertexOperator.coeff_of_coeff,
    LatticeHalfFock.stressCoeff, LatticeHalfFock.tensorL]
  rfl

private theorem lowered_eigen (N : ℕ) (u : Twisted s) (hu₀ : L₀ s u = weight N • u)
    (hne : L₁ s u ≠ 0) :
    ∃ K : ℕ, K < N ∧ (-1 : ℂ) ^ K = s ∧ L₀ s (L₁ s u) = weight K • L₁ s u := by
  have hrank : (leechData.rank : ℂ) / 16 = 3 / 2 := by rw [leech_spec.1]; norm_num
  have he : actualTensorL0 D hu u.val =
      ((leechData.rank : ℂ) / 16 + ((N : ℤ) : ℂ) / 2) • u.val := by
    rw [hrank, Int.cast_natCast]
    exact (fixedParity_conformal_mode_val s u).symm.trans (congrArg Subtype.val hu₀)
  have hscalar : (leechData.rank : ℂ) / 16 + (((N : ℤ) - 2 * 1 : ℤ) : ℂ) / 2 =
      weight N - 1 := by
    rw [hrank, weight]
    push_cast
    ring
  have hl := lowering_eigen D hu (N : ℤ) u.val he 1
  simp only [pow_one, Nat.cast_one, hscalar] at hl
  have hy := twistedL1_val (s := s) u
  have hlow : L₀ s (L₁ s u) = (weight N - 1) • L₁ s u := by
    apply Subtype.ext
    exact (fixedParity_conformal_mode_val s (L₁ s u)).trans
      ((congrArg (actualTensorL0 D hu) hy).trans
        (hl.trans (congrArg (fun x => (weight N - 1) • x) hy.symm)))
  obtain ⟨K, hK, hs⟩ :=
    fixedParity_conformal_eigenweight s (weight N - 1) (L₁ s u) hne hlow
  have hc : (N : ℂ) = ((K + 2 : ℕ) : ℂ) := by
    simp only [weight, Nat.cast_add, Nat.cast_ofNat] at hK ⊢
    linear_combination 2 * hK
  have hn : N = K + 2 := Nat.cast_injective hc
  exact ⟨K, by omega, hs, hlow.trans (congrArg (fun c : ℂ => c • L₁ s u) hK)⟩

private theorem homogeneous_vacuum_zero {J : Fields s t} (hJ : Lawful J) (hst : s ≠ t)
    (N M' : ℕ) (u : Twisted s) (v : Twisted t)
    (hN : (-1 : ℂ) ^ N = s) (hM : (-1 : ℂ) ^ M' = t)
    (hu₀ : L₀ s u = weight N • u) (hv₀ : L₀ t v = weight M' • v) (q : ℚ) :
    vacuumForm J q u v = 0 := by
  have vanish (k : ℕ) : ∀ (N M' : ℕ), N + M' = k →
      ∀ (u : Twisted s) (v : Twisted t), (-1 : ℂ) ^ N = s → (-1 : ℂ) ^ M' = t →
        L₀ s u = weight N • u → L₀ t v = weight M' • v →
        ∀ q : ℚ, vacuumForm J q u v = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n m hnm x y hs ht hx hy z
      have hleft : vacuumForm J (z - 1) (L₁ s x) y = 0 := by
        by_cases hz : L₁ s x = 0
        · rw [hz, map_zero, LinearMap.zero_apply]
        · obtain ⟨l, hln, hl, he⟩ := lowered_eigen n x hx hz
          exact ih (l + m) (by omega) l m rfl _ y hl ht he hy (z - 1)
      have hright : vacuumForm J (z - 1) x (L₁ t y) = 0 := by
        by_cases hz : L₁ t y = 0
        · rw [hz, map_zero]
        · obtain ⟨l, hlm, hl, he⟩ := lowered_eigen m y hy hz
          exact ih (n + l) (by omega) n l rfl x _ hs hl hx he (z - 1)
      have hgap : weight n - weight m ≠ 0 := by
        intro he
        have hc : (n : ℂ) = (m : ℂ) := by unfold weight at he; linear_combination 2 * he
        have hn : n = m := Nat.cast_injective hc
        exact hst (hs.symm.trans (by simpa only [hn] using ht))
      have hr := vacuum_lowering hJ x y _ _ hx hy z
      have hz : (weight n - weight m) * vacuumForm J z x y = 0 := by
        simpa only [hleft, hright, add_zero] using hr
      exact (mul_eq_zero.mp hz).resolve_left hgap
  exact vanish (N + M') N M' rfl u v hN hM hu₀ hv₀ q

private theorem all_vacuum_zero {J : Fields s t} (hJ : Lawful J) (hst : s ≠ t)
    (u : Twisted s) (q : ℚ) (v : Twisted t) : vacuumFunctional (mode J u q v) = 0 := by
  change vacuumForm J q u v = 0
  apply linear_zero_on_eigenvectors ((vacuumForm J q).flip v) _ u
  intro N x hN hx
  apply linear_zero_on_eigenvectors (vacuumForm J q x) _ v
  intro K y hK hy
  exact homogeneous_vacuum_zero hJ hst N K x y hN hK hx hy q

private theorem ward_vacuum {J : Fields s t} (hJ : Lawful J)
    (h : ∀ (u : Twisted s) (q : ℚ) (v : Twisted t), vacuumFunctional (mode J u q v) = 0)
    (a : V) (u : Twisted s) (v : Twisted t) (p : ℤ) (q : ℚ) :
    vacuumFunctional (fixedMode D a p (mode J u q v)) = 0 := by
  have hl := (hJ.jacobi a u v p 0 q).1
  have hleft : vacuumFunctional (∑ᶠ i, leftTerm J a u v p 0 q i) = 0 := by
    rw [map_finsum vacuumFunctional hl]
    have hz (i : ℕ) : vacuumFunctional (leftTerm J a u v p 0 q i) = 0 :=
      (map_smul vacuumFunctional _ _).trans (by rw [h (M s a (0 + i) u) _ v, smul_zero])
    simp only [hz, finsum_zero]
  have hj := congrArg vacuumFunctional (jacobi_zero hJ a u v p q)
  rw [hleft, map_sub, h u q (M t a p v), sub_zero] at hj
  exact hj.symm

/-- Every full rational-mode field between distinct twisted parities with fixed Leech output
is zero. In particular this applies to both orderings of the two signs. -/
theorem eq_zero_of_ne {J : Fields s t} (hst : s ≠ t) (hJ : Lawful J) : J = 0 := by
  apply LinearMap.ext
  intro u
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro v
  have hz := eq_zero_of_fixedMode_vacuum (mode J u (-e - 1) v)
    (fun a p => ward_vacuum hJ (all_vacuum_zero hJ hst) a u v p (-e - 1))
  rw [mode, show -(-e - 1) - 1 = e by ring] at hz
  simpa only [LinearMap.zero_apply, map_zero, Pi.zero_apply] using hz

/-- The full lawful predicate characterizes the zero field in either crossed direction. -/
theorem lawful_iff_eq_zero {J : Fields s t} (hst : s ≠ t) : Lawful J ↔ J = 0 := by
  refine ⟨eq_zero_of_ne hst, ?_⟩
  rintro rfl
  constructor
  · intros
    simp [mode]
  · intros
    simp [leftTerm, firstTerm, secondTerm, mode, Function.HasFiniteSupport, Function.support]

#print axioms lawful_negative_negative_iff
#print axioms eq_zero_of_ne
#print axioms lawful_iff_eq_zero

end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldCrossedTwistedVacuumFusion
