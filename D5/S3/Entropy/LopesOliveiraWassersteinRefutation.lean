/- GID: D5/S3/Entropy/LopesOliveiraWassersteinRefutation
   generality: G
   mirror-B: D5/B/S3/Entropy/LopesOliveiraWassersteinRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The all-Borel-law inequality fails at the actual classical equilibrium. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30545. -/

/-
admission_basis: open-problem-resolution (#30524; Refuted)
proof_shape: IsClassicalEquilibrium = definition; escape_witness: none
proof_shape: IsUniqueClassicalEquilibrium = definition; escape_witness: none
proof_shape: claim = definition; escape_witness: none
proof_shape: binary_classical_equilibrium = bind-only; escape_witness: none; consumer: result
proof_shape: result = bind-only; escape_witness: none; consumer: none (designated refutation result)
Direct frozen dependencies: none; all named suppliers on the live path are in the delivered Lopes–Oliveira dependency modules or pinned upstream.
-/

import D5.S3.Entropy.KolmogorovSinai.FairEquilibrium

open MeasureTheory
open D5.S3.Entropy.KolmogorovSinai
noncomputable section
namespace D5.S3.Entropy.LopesOliveiraWassersteinRefutation

open LopesOliveiraSource

/-- Classical KS variational maximization over all invariant Borel probabilities. -/
def IsClassicalEquilibrium {d : ℕ} (phi : Omega d → ℝ) (mu : Measure (Omega d)) : Prop :=
  ∃ hm : IsProbabilityMeasure mu, letI := hm
    ∃ hT : MeasurePreserving shift mu mu,
      ∀ rho : Measure (Omega d), ∀ hr : IsProbabilityMeasure rho, letI := hr
        ∀ hR : MeasurePreserving shift rho rho,
          ((∫ x, phi x ∂rho : ℝ) : EReal) + ksEntropy hR ≤
            ((∫ x, phi x ∂mu : ℝ) : EReal) + ksEntropy hT

/-- The target is the unique classical equilibrium for this same potential. -/
def IsUniqueClassicalEquilibrium {d : ℕ} (phi : Omega d → ℝ)
    (mu : Measure (Omega d)) : Prop :=
  IsClassicalEquilibrium phi mu ∧
    ∀ rho, IsClassicalEquilibrium phi rho → rho = mu

/-- The displayed source question, with classical existence and uniqueness explicit. -/
def claim : Prop :=
  ∀ d : ℤ, 2 ≤ d → ∀ phi : Omega d.toNat → ℝ, IsHolder phi →
    ∃ mu : Measure (Omega d.toNat), IsUniqueClassicalEquilibrium phi mu ∧
      ∃ c : ℝ, ∀ nu : Measure (Omega d.toNat), IsProbabilityMeasure nu →
        wassersteinOne nu mu ≤
          c * Real.sqrt (niPressure phi - niEntropy nu - ∫ x, phi x ∂nu)

/-- The source constant potential has a genuine, inhabited, unique KS equilibrium. -/
theorem binary_classical_equilibrium :
    IsUniqueClassicalEquilibrium (fun _ : Omega 2 => -Real.log 2) SourceEquilibrium.fair := by
  have hf : IsClassicalEquilibrium (fun _ : Omega 2 => -Real.log 2)
      SourceEquilibrium.fair := by
    refine ⟨inferInstance, SourceEquilibrium.fair_invariant, ?_⟩
    intro rho hr hR
    letI := hr
    simp only [integral_const, probReal_univ, one_smul]
    let hRs : MeasurePreserving LopesOliveiraFullTail.shift rho rho := hR
    change ((-Real.log 2 : ℝ) : EReal) + ksEntropy hRs ≤
      ((-Real.log 2 : ℝ) : EReal) + ksEntropy SourceEquilibrium.fair_invariant
    rw [SourceEquilibrium.fair_ks]
    exact add_le_add le_rfl (SourceEquilibrium.ks_le rho hRs)

  refine ⟨hf, ?_⟩
  intro rho heq
  rcases heq with ⟨hr, hR, hmax⟩
  letI := hr
  have h := hmax SourceEquilibrium.fair inferInstance SourceEquilibrium.fair_invariant
  have hfks : ksEntropy (show MeasurePreserving shift SourceEquilibrium.fair
      SourceEquilibrium.fair from SourceEquilibrium.fair_invariant) =
      (Real.log 2 : ℝ) := SourceEquilibrium.fair_ks
  simp only [integral_const, probReal_univ, one_smul, hfks] at h
  have hl : (Real.log 2 : ℝ) ≤ ksEntropy hR := by
    exact (EReal.addLECancellable_coe (-Real.log 2)).add_le_add_iff_left.mp h
  exact SourceEquilibrium.max_unique rho hR
    (le_antisymm (SourceEquilibrium.ks_le rho hR) hl)

/-- Literal negation of the universal source claim. -/
theorem result : ¬ claim := by
  intro hclaim
  have hholder : IsHolder (fun _ : Omega 2 => -Real.log 2) := by
    refine ⟨1, by norm_num, 0, by norm_num, ?_⟩
    intro x y
    simp
  obtain ⟨mu, hmu, c, hc⟩ := hclaim 2 (by norm_num) (fun _ => -Real.log 2) hholder
  have heq : mu = SourceEquilibrium.fair :=
    binary_classical_equilibrium.2 mu hmu.1
  subst mu
  have hobs := LopesOliveiraFullTail.full_tail_transport_obstruction
    SourceEquilibrium.fair SourceEquilibrium.fair_invariant.map_eq
  have h := hc LopesOliveiraFullTail.law inferInstance
  have hw : wassersteinOne LopesOliveiraFullTail.law SourceEquilibrium.fair =
      LopesOliveiraFullTail.wassersteinOne LopesOliveiraFullTail.law SourceEquilibrium.fair := by
    unfold wassersteinOne LopesOliveiraFullTail.wassersteinOne
    simp only [LopesOliveiraFullTail.source_distance_eq]
    rfl
  rw [hw] at h
  change LopesOliveiraFullTail.wassersteinOne _ _ ≤ c * Real.sqrt
    (LopesOliveiraFullTail.niPressure (fun _ => -Real.log 2) -
      LopesOliveiraFullTail.niEntropy LopesOliveiraFullTail.law -
        ∫ _ : Omega 2, -Real.log 2 ∂LopesOliveiraFullTail.law) at h
  rw [hobs.2.2.2.2.2.1, Real.sqrt_zero, mul_zero] at h
  linarith [hobs.2.2.2.2.2.2]

end D5.S3.Entropy.LopesOliveiraWassersteinRefutation
