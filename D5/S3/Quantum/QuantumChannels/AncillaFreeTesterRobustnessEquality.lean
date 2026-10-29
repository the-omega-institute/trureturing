/- GID: D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Ancilla-free testers with a common state have canonical POVM robustness. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

/-! The common-normalization ancilla-free equality of Sedlák, Reitzner, Chiribella and
Ziman, arXiv:1511.00976v2, Section VI.C. Partial trace and compression preserve the
feasible mixing parameters, so equality follows by taking infima. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality

open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (partialTraceRight_smul)

/-- Positive tester effects sum to the output identity tensored with a density matrix. -/
def IsTester {y x j : Type} [Fintype y] [DecidableEq y] [Fintype x] [Fintype j]
    (t : j → Matrix (y × x) (y × x) ℂ) : Prop :=
  (∀ a, (t a).PosSemidef) ∧
    ∃ σ : Matrix x x ℂ, IsDensity σ ∧ ∑ a, t a = Matrix.kronecker 1 σ

/-- Separate noise testers make the two mixtures marginals of one joint tester. -/
def TesterCompatibleAt {y x j k : Type} [Fintype y] [DecidableEq y]
    [Fintype x] [Fintype j] [Fintype k] (lam : ℝ)
    (a : j → Matrix (y × x) (y × x) ℂ) (b : k → Matrix (y × x) (y × x) ℂ) : Prop :=
  ∃ (e : j → Matrix (y × x) (y × x) ℂ) (f : k → Matrix (y × x) (y × x) ℂ)
    (c : j × k → Matrix (y × x) (y × x) ℂ),
    IsTester e ∧ IsTester f ∧ IsTester c ∧
      (∀ u, ∑ v, c (u, v) = (1 - lam) • a u + lam • e u) ∧
      (∀ v, ∑ u, c (u, v) = (1 - lam) • b v + lam • f v)

/-- Infimum of the admissible mixing parameters in the unit interval. -/
def testerRobustness {y x j k : Type} [Fintype y] [DecidableEq y]
    [Fintype x] [Fintype j] [Fintype k]
    (a : j → Matrix (y × x) (y × x) ℂ) (b : k → Matrix (y × x) (y × x) ℂ) : ℝ :=
  sInf {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ TesterCompatibleAt lam a b}

/-- Separate noise POVMs make the two mixtures marginals of one joint POVM. -/
def POVMCompatibleAt {z j k : Type} [Fintype z] [DecidableEq z]
    [Fintype j] [Fintype k] (lam : ℝ)
    (p : j → Matrix z z ℂ) (q : k → Matrix z z ℂ) : Prop :=
  ∃ (u : j → Matrix z z ℂ) (v : k → Matrix z z ℂ)
    (g : j × k → Matrix z z ℂ),
    ((∀ a, (u a).PosSemidef) ∧ ∑ a, u a = 1) ∧
    ((∀ b, (v b).PosSemidef) ∧ ∑ b, v b = 1) ∧
    ((∀ ab, (g ab).PosSemidef) ∧ ∑ ab, g ab = 1) ∧
      (∀ a, ∑ b, g (a, b) = (1 - lam) • p a + lam • u a) ∧
      (∀ b, ∑ a, g (a, b) = (1 - lam) • q b + lam • v b)

/-- Infimum of the POVM mixing parameters in the unit interval. -/
def povmRobustness {z j k : Type} [Fintype z] [DecidableEq z]
    [Fintype j] [Fintype k]
    (p : j → Matrix z z ℂ) (q : k → Matrix z z ℂ) : ℝ :=
  sInf {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ POVMCompatibleAt lam p q}

/-- The canonical POVMs act on the output and the support of the common input state. -/
def claim : Prop :=
  ∀ (y x j k : Type) [Fintype y] [DecidableEq y] [Fintype x] [DecidableEq x]
    [Fintype j] [DecidableEq j] [Fintype k] [DecidableEq k]
    (ρ : Matrix x x ℂ) (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ),
    IsDensity ρ → ((∀ a, (m a).PosSemidef) ∧ ∑ a, m a = 1) →
    ((∀ b, (n b).PosSemidef) ∧ ∑ b, n b = 1) →
      testerRobustness (fun a => Matrix.kronecker (m a) ρ)
        (fun b => Matrix.kronecker (n b) ρ) =
      povmRobustness (fun a => Matrix.kronecker (m a)
        (1 : Matrix (Fin ρ.rank) (Fin ρ.rank) ℂ))
        (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin ρ.rank) (Fin ρ.rank) ℂ))

private theorem kronecker_sum {y x j : Type} [Fintype j]
    (m : j → Matrix y y ℂ) (ρ : Matrix x x ℂ) :
    (∑ a, Matrix.kronecker (m a) ρ) = Matrix.kronecker (∑ a, m a) ρ := by
  exact (map_sum ((Matrix.kroneckerBilinear (R := ℂ)).flip ρ) m Finset.univ).symm

private theorem povm_tensor_tester {y x j : Type} [Fintype y] [DecidableEq y]
    [Fintype x] [Fintype j] (ρ : Matrix x x ℂ) (hρ : IsDensity ρ)
    (m : j → Matrix y y ℂ) (hm : (∀ a, (m a).PosSemidef) ∧ ∑ a, m a = 1) :
    IsTester (fun a => Matrix.kronecker (m a) ρ) := by
  refine ⟨fun a => (hm.1 a).kronecker hρ.1, ρ, hρ, ?_⟩
  rw [kronecker_sum, hm.2]

private theorem partialTraceRight_sum {y x j : Type} [Fintype x] [Fintype j]
    (t : j → Matrix (y × x) (y × x) ℂ) :
    partialTraceRight (∑ a, t a) = ∑ a, partialTraceRight (t a) := by
  ext a b
  rw [Matrix.sum_apply]
  change (∑ c, (∑ u, t u) (a, c) (b, c)) = ∑ u, ∑ c, t u (a, c) (b, c)
  simp only [Matrix.sum_apply]
  exact Finset.sum_comm

private theorem tester_partialTrace_povm {y x j : Type} [Fintype y] [DecidableEq y]
    [Fintype x] [Fintype j] (t : j → Matrix (y × x) (y × x) ℂ)
    (ht : IsTester t) : (∀ a, (partialTraceRight (t a)).PosSemidef) ∧
      ∑ a, partialTraceRight (t a) = 1 := by
  refine ⟨fun a => partialTraceRight_posSemidef (ht.1 a), ?_⟩
  obtain ⟨σ, hσ, hs⟩ := ht.2
  rw [← partialTraceRight_sum, hs, partialTraceRight_kronecker, hσ.2, one_smul]

private theorem povm_to_tester_compatible {y x j k : Type}
    [Fintype y] [DecidableEq y] [Fintype x] [Fintype j] [Fintype k]
    (ρ : Matrix x x ℂ) (hρ : IsDensity ρ) (lam : ℝ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ)
    (h : POVMCompatibleAt lam m n) :
    TesterCompatibleAt lam (fun a => Matrix.kronecker (m a) ρ)
      (fun b => Matrix.kronecker (n b) ρ) := by
  obtain ⟨u, v, g, hu, hv, hg, hgm, hgn⟩ := h
  refine ⟨fun a => Matrix.kronecker (u a) ρ,
    fun b => Matrix.kronecker (v b) ρ,
    fun ab => Matrix.kronecker (g ab) ρ,
    povm_tensor_tester ρ hρ u hu, povm_tensor_tester ρ hρ v hv,
    povm_tensor_tester ρ hρ g hg, ?_, ?_⟩
  · intro a
    rw [kronecker_sum, hgm a]
    change ((1 - lam) • m a + lam • u a) ⊗ₖ ρ =
      (1 - lam) • (m a ⊗ₖ ρ) + lam • (u a ⊗ₖ ρ)
    rw [Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker]
  · intro b
    rw [kronecker_sum, hgn b]
    change ((1 - lam) • n b + lam • v b) ⊗ₖ ρ =
      (1 - lam) • (n b ⊗ₖ ρ) + lam • (v b ⊗ₖ ρ)
    rw [Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker]

private theorem tester_to_povm_compatible {y x j k : Type}
    [Fintype y] [DecidableEq y] [Fintype x] [Fintype j] [Fintype k]
    (ρ : Matrix x x ℂ) (hρ : IsDensity ρ) (lam : ℝ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ)
    (h : TesterCompatibleAt lam (fun a => Matrix.kronecker (m a) ρ)
      (fun b => Matrix.kronecker (n b) ρ)) : POVMCompatibleAt lam m n := by
  obtain ⟨e, f, c, he, hf, hc, hcm, hcn⟩ := h
  refine ⟨fun a => partialTraceRight (e a), fun b => partialTraceRight (f b),
    fun ab => partialTraceRight (c ab), tester_partialTrace_povm e he,
    tester_partialTrace_povm f hf, tester_partialTrace_povm c hc, ?_, ?_⟩
  · intro a
    rw [← partialTraceRight_sum, hcm a, partialTraceRight_add,
      partialTraceRight_smul, partialTraceRight_smul,
      partialTraceRight_kronecker, hρ.2, one_smul]
  · intro b
    rw [← partialTraceRight_sum, hcn b, partialTraceRight_add,
      partialTraceRight_smul, partialTraceRight_smul,
      partialTraceRight_kronecker, hρ.2, one_smul]

private theorem povm_tensor_identity {y j : Type} [Fintype y] [DecidableEq y]
    [Fintype j] (r : ℕ) (m : j → Matrix y y ℂ) (hm : (∀ a, (m a).PosSemidef) ∧ ∑ a, m a = 1) :
    (∀ a, (Matrix.kronecker (m a) (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef) ∧
      ∑ a, Matrix.kronecker (m a) (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  refine ⟨fun a => (hm.1 a).kronecker (Matrix.PosSemidef.one), ?_⟩
  rw [kronecker_sum, hm.2]
  exact Matrix.one_kronecker_one

private theorem povm_to_ancilla_compatible {y j k : Type} [Fintype y] [DecidableEq y]
    [Fintype j] [Fintype k] (r : ℕ) (lam : ℝ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ)
    (h : POVMCompatibleAt lam m n) :
    POVMCompatibleAt lam (fun a => Matrix.kronecker (m a)
      (1 : Matrix (Fin r) (Fin r) ℂ))
      (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin r) (Fin r) ℂ)) := by
  obtain ⟨u, v, g, hu, hv, hg, hgm, hgn⟩ := h
  refine ⟨fun a => Matrix.kronecker (u a) (1 : Matrix (Fin r) (Fin r) ℂ),
    fun b => Matrix.kronecker (v b) (1 : Matrix (Fin r) (Fin r) ℂ),
    fun ab => Matrix.kronecker (g ab) (1 : Matrix (Fin r) (Fin r) ℂ),
    povm_tensor_identity r u hu, povm_tensor_identity r v hv,
    povm_tensor_identity r g hg, ?_, ?_⟩
  · intro a
    rw [kronecker_sum, hgm a]
    change ((1 - lam) • m a + lam • u a) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ) =
      (1 - lam) • (m a ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) + lam • (u a ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))
    rw [Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker]
  · intro b
    rw [kronecker_sum, hgn b]
    change ((1 - lam) • n b + lam • v b) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ) =
      (1 - lam) • (n b ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) + lam • (v b ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))
    rw [Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker]

private theorem compression_povm {y j : Type} [Fintype y] [DecidableEq y]
    [Fintype j] (r : ℕ) (hr : 0 < r)
    (m : j → Matrix (y × Fin r) (y × Fin r) ℂ) (hm : (∀ a, (m a).PosSemidef) ∧ ∑ a, m a = 1) :
    (∀ a, ((m a).submatrix (fun b => (b, ⟨0, hr⟩))
      (fun b => (b, ⟨0, hr⟩))).PosSemidef) ∧
    ∑ a, (m a).submatrix (fun b => (b, ⟨0, hr⟩)) (fun b => (b, ⟨0, hr⟩)) = 1 := by
  refine ⟨fun a => (hm.1 a).submatrix (fun b => (b, ⟨0, hr⟩)), ?_⟩
  have hs := congrArg (fun z : Matrix (y × Fin r) (y × Fin r) ℂ =>
    z.submatrix (fun b => (b, ⟨0, hr⟩)) (fun b => (b, ⟨0, hr⟩))) hm.2
  have hi : Function.Injective (fun b : y => (b, (⟨0, hr⟩ : Fin r))) :=
    fun _ _ h => congrArg Prod.fst h
  rw [Matrix.submatrix_one _ hi] at hs
  calc
    _ = (∑ a, m a).submatrix (fun b => (b, ⟨0, hr⟩))
        (fun b => (b, ⟨0, hr⟩)) := by
      ext a b
      simp only [Matrix.sum_apply, Matrix.submatrix_apply]
    _ = 1 := hs

private theorem ancilla_to_povm_compatible {y j k : Type} [Fintype y] [DecidableEq y]
    [Fintype j] [Fintype k] (r : ℕ) (hr : 0 < r) (lam : ℝ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ)
    (h : POVMCompatibleAt lam (fun a => Matrix.kronecker (m a)
      (1 : Matrix (Fin r) (Fin r) ℂ))
      (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin r) (Fin r) ℂ))) :
    POVMCompatibleAt lam m n := by
  have hk (t : Matrix y y ℂ) (b d : y) :
      Matrix.kronecker t (1 : Matrix (Fin r) (Fin r) ℂ)
        (b, ⟨0, hr⟩) (d, ⟨0, hr⟩) = t b d := by
    change t b d * (1 : Matrix (Fin r) (Fin r) ℂ) ⟨0, hr⟩ ⟨0, hr⟩ = t b d
    rw [Matrix.one_apply_eq, mul_one]
  obtain ⟨u, v, g, hu, hv, hg, hgm, hgn⟩ := h
  refine ⟨fun a => (u a).submatrix (fun b => (b, ⟨0, hr⟩))
      (fun b => (b, ⟨0, hr⟩)),
    fun a => (v a).submatrix (fun b => (b, ⟨0, hr⟩))
      (fun b => (b, ⟨0, hr⟩)),
    fun a => (g a).submatrix (fun b => (b, ⟨0, hr⟩))
      (fun b => (b, ⟨0, hr⟩)),
    compression_povm r hr u hu, compression_povm r hr v hv,
    compression_povm r hr g hg, ?_, ?_⟩
  · intro a
    ext b d
    have he := congrArg (fun z : Matrix (y × Fin r) (y × Fin r) ℂ =>
      z (b, ⟨0, hr⟩) (d, ⟨0, hr⟩)) (hgm a)
    simpa only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.add_apply,
      Matrix.smul_apply, hk] using he
  · intro a
    ext b d
    have he := congrArg (fun z : Matrix (y × Fin r) (y × Fin r) ℂ =>
      z (b, ⟨0, hr⟩) (d, ⟨0, hr⟩)) (hgn a)
    simpa only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.add_apply,
      Matrix.smul_apply, hk] using he

private theorem density_rank_pos {x : Type} [Fintype x]
    (ρ : Matrix x x ℂ) (hρ : IsDensity ρ) : 0 < ρ.rank := by
  classical
  have hn : ρ ≠ 0 := by
    intro hz
    have ht := hρ.2
    rw [hz, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  have he : ∃ a b, ρ a b ≠ 0 := by
    by_contra h
    apply hn
    ext a b
    exact Classical.not_not.mp (fun hn => h ⟨a, b, hn⟩)
  obtain ⟨a, b, hab⟩ := he
  rw [Matrix.rank_eq_finrank_span_cols]
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨ρ.col b, Submodule.subset_span ⟨b, rfl⟩⟩, ?_⟩
  intro hz
  exact hab (congrFun (congrArg Subtype.val hz) a)

private theorem tester_feasible_eq {y x j k : Type}
    [Fintype y] [DecidableEq y] [Fintype x] [Fintype j] [Fintype k]
    (ρ : Matrix x x ℂ) (hρ : IsDensity ρ)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ) :
    {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ TesterCompatibleAt lam
      (fun a => Matrix.kronecker (m a) ρ) (fun b => Matrix.kronecker (n b) ρ)} =
    {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ POVMCompatibleAt lam m n} := by
  ext lam
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨tester_to_povm_compatible ρ hρ lam m n, povm_to_tester_compatible ρ hρ lam m n⟩

private theorem ancilla_feasible_eq {y j k : Type} [Fintype y] [DecidableEq y]
    [Fintype j] [Fintype k] (r : ℕ) (hr : 0 < r)
    (m : j → Matrix y y ℂ) (n : k → Matrix y y ℂ) :
    {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ POVMCompatibleAt lam m n} =
    {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ POVMCompatibleAt lam
      (fun a => Matrix.kronecker (m a) (1 : Matrix (Fin r) (Fin r) ℂ))
      (fun b => Matrix.kronecker (n b) (1 : Matrix (Fin r) (Fin r) ℂ))} := by
  ext lam
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨povm_to_ancilla_compatible r lam m n, ancilla_to_povm_compatible r hr lam m n⟩

/-- Tester and canonical measurement robustness agree for a common ancilla-free state. -/
theorem result : claim := by
  intro y x j k _ _ _ _ _ _ _ _ ρ m n hρ _hm _hn
  change sInf _ = sInf _
  exact congrArg sInf ((tester_feasible_eq ρ hρ m n).trans
    (ancilla_feasible_eq ρ.rank (density_rank_pos ρ hρ) m n))

end D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
