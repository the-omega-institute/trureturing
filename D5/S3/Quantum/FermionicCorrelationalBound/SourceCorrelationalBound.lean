/- GID: D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound
   generality: I
   mirror-B: D5/B/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Christiansen Conjecture 3 with C=5/8 on every separable Hilbert space. -/
/-
Admission witness: D5.S3.Quantum.FermionicCorrelationalBound.SourceCorrelationalBound.result.
source_cap_result: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; consumer: SourceCorrelationalBound.result.
coefficient_positive: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.coefficient_maximum.
coefficient_maximum: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.lambdaMax, SourceCorrelationalBound.lambdaMax_greatest.
lambdaMax_greatest: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.lambdaMax_cap, SourceCorrelationalBound.lambdaMax_nonneg.
lambdaMax_nonneg: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.lambdaMax_cap.
lambdaMax_cap: proof_shape: bind-only; escape_witness: none; consumer: SourceCorrelationalBound.result.
result: proof_shape: content; escape_witness: OccupationHilbertContractions.ordered_pair_energy; purpose: settling result.
admission_basis: open-problem-resolution (#14135; Proved)
Direct frozen dependencies:
  none; same-delivery prerequisites are not baseline frozen dependencies.
Information-escape registration is paused.
-/
import D5.S3.Quantum.FermionicCorrelationalBound.PhysicalContractionRdmBridge
import D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound
noncomputable section
open scoped Classical BigOperators TensorProduct ComplexConjugate Matrix
namespace D5.S3.Quantum.FermionicCorrelationalBound.SourceCorrelationalBound
open D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound D5.S3.Quantum.FermionicCorrelationalBound.CompletedTensorSlaterGeometry D5.S3.Quantum.FermionicCorrelationalBound.OccupationHilbertContractions D5.S3.Quantum.FermionicCorrelationalBound.PhysicalContractionRdmBridge
section
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u v
/-- Physical antisymmetry is imposed on the actual tensor-factor action before taking coordinates. -/
def physicalParticle {κ : Type*} (X : HilbertObject.{u}) (b : HilbertBasis κ ℂ X.carrier)
    (label : κ ↪ ℕ) (n : ℕ) (ψ : (tensorTower X n).carrier)
    (hψ : ∀ σ : Equiv.Perm (Fin (n+1)),
      tensorPermutation X b n σ ψ=permutationPhase (n+1) σ • ψ) :
    particleExterior X b label (n+1) :=
  ⟨ψ,hψ⟩
/-- The source theorem uses physical tensor contractions and the physical Gram RDM. -/
private theorem source_cap_result : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
  ∀ (ι : Type v) (e : ι ↪ ℕ) (v : ι × Fin 2 → H) (hv : Orthonormal ℂ v)
    (c : CanonicalFamily ι) (Φ : (UniformSpace.Completion (H ⊗[ℂ] H))),
    HasSum (fun i => (c.coeff i:ℂ) • sourcePairWedge v i) Φ →
  ∀ (m : ℕ) (α : ℝ), 0 ≤ α → (∀ i,c.coeff i^2 ≤ α) → (2*(m:ℝ)+2)*α ≤ 1 →
  let d := adaptedChart e v hv
  ∀ ψ : (tensorTower (sourceHilbertObject H) (2*m+1)).carrier,
    ∀ hanti : (∀ σ : Equiv.Perm (Fin (2*m+2)),
      tensorPermutation (sourceHilbertObject H) d.basis (2*m+1) σ ψ=permutationPhase (2*m+2) σ • ψ),
    ‖ψ‖=1 →
    sourceRayleigh (sourceHilbertObject H) d.basis d.label (2*m)
      (physicalParticle (sourceHilbertObject H) d.basis d.label (2*m+1) ψ hanti) Φ ≤
      (2*(m:ℝ)+2)*(1-(m:ℝ)*(∑' i,c.coeff i^4)+(5/8:ℝ)*((2*(m:ℝ)+2)*α)^2) := by
  intro H _ _ _ _ ι e v hv c Φ hΦ m α hα hcap hsmall
  dsimp only
  intro ψ hanti hψ
  let d := adaptedChart e v hv
  let Ψ := physicalParticle (sourceHilbertObject H) d.basis d.label (2*m+1) ψ hanti
  have hΨ : ‖Ψ‖=1 := hψ
  have hcanon : Φ=sourceCanonicalFamily e v hv c := by
    rw [sourceCanonicalFamily_series,hΦ.tsum_eq]
  have hφ := sourceCanonicalFamily_coordinates e v hv c d.basis d.label d.pairs
    d.basis_pair d.label_u d.label_v
  have hnorm : ‖particleOccupation (sourceHilbertObject H) d.basis d.label (2*m+2) Ψ‖=1 := by
    rw [LinearIsometry.norm_map,hΨ]
  change sourceRayleigh (sourceHilbertObject H) d.basis d.label (2*m) Ψ Φ ≤ _
  rw [sourceRayleigh_transport,hcanon]
  erw [hφ]
  have hcap' : ∀ i,(padCanonicalSequence (familySequence e c)).coeff i^2≤α :=
    padCanonicalSequence_cap _ α (familySequence_cap e c α hα hcap)
  have hsmall' : 2*((m+1:ℕ):ℝ)*α≤1 := by
    simpa only [Nat.cast_add,Nat.cast_one,mul_add,mul_one] using hsmall
  have h := D5.S3.Quantum.FermionicCorrelationalBound.CompletedCorrelationalBound.completed_result (m+1) (by omega)
    (padCanonicalSequence (familySequence e c)) α hcap' hsmall'
  have hN : 2*(m+1)=2*m+2 := by omega
  rw [hN] at h
  have hb := h (particleOccupation (sourceHilbertObject H) d.basis d.label (2*m+2) Ψ) hnorm
  rw [padCanonicalSequence_fourth] at hb
  change completedRayleigh (2*m+2) _ _ ≤ (2*((m+1:ℕ):ℝ))*
    (1-(((m+1:ℕ):ℝ)-1)*(∑' i,(Function.extend e c.coeff (fun _ => 0)) i^4)+(5/8:ℝ)*(2*((m+1:ℕ):ℝ)*α)^2) at hb
  rw [extendedCoeff_moment e c 4 (by omega)] at hb
  simpa only [Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_sub_cancel_right] using hb
end
section
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*}
/-- Unit square mass supplies a positive canonical coefficient. -/
private theorem coefficient_positive (c : CanonicalFamily ι) : ∃ i,0<c.coeff i := by
  by_contra h
  push Not at h
  have hz : c.coeff=0 := funext fun i => le_antisymm (h i) (c.nonneg i)
  have hm := c.mass
  rw [hz] at hm
  norm_num at hm
/-- A square-summable canonical family attains its largest coefficient. -/
private theorem coefficient_maximum (c : CanonicalFamily ι) : ∃ a,IsGreatest (Set.range c.coeff) a := by
  obtain ⟨i0,hi0⟩ := coefficient_positive c
  let ε := c.coeff i0^2/2
  have hε : 0<ε := by dsimp [ε]; positivity
  let s : Set ι := {i | ε≤c.coeff i^2}
  have hs : s.Finite := by
    have he := c.summable_sq.tendsto_cofinite_zero.eventually_lt_const hε
    simpa only [s,Set.compl_setOf,not_lt] using Filter.mem_cofinite.mp he
  have hi : i0∈s := by dsimp [s,ε]; nlinarith [sq_nonneg (c.coeff i0)]
  obtain ⟨j,hj,hmax⟩ := s.exists_max_image c.coeff hs ⟨i0,hi⟩
  refine ⟨c.coeff j,⟨⟨j,rfl⟩,?_⟩⟩
  rintro a ⟨i,rfl⟩
  by_cases hmem : i∈s
  · exact hmax i hmem
  · have hsmall : c.coeff i^2<ε := lt_of_not_ge hmem
    have hlarge : ε≤c.coeff j^2 := hj
    nlinarith [c.nonneg i,c.nonneg j]
/-- The source's lambda_max, defined on the supplied canonical family. -/
def lambdaMax (c : CanonicalFamily ι) : ℝ := Classical.choose (coefficient_maximum c)
private theorem lambdaMax_greatest (c : CanonicalFamily ι) : IsGreatest (Set.range c.coeff) (lambdaMax c) :=
  Classical.choose_spec (coefficient_maximum c)
private theorem lambdaMax_nonneg (c : CanonicalFamily ι) : 0≤lambdaMax c := by
  obtain ⟨i,hi⟩ := (lambdaMax_greatest c).1
  rw [← hi]
  exact c.nonneg i
private theorem lambdaMax_cap (c : CanonicalFamily ι) (i : ι) : c.coeff i^2≤lambdaMax c^2 := by
  have h := (lambdaMax_greatest c).2 ⟨i,rfl⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (lambdaMax_nonneg c) (c.nonneg i))]
end
section
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u v
/-- Separability supplies the index injection; no coordinate encoding is assumed. -/
def canonicalIndex {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    {ι : Type v} (v : ι × Fin 2 → H) (hv : Orthonormal ℂ v) : ι ↪ ℕ := by
  letI : Countable ι := canonicalPair_countable v hv
  exact ⟨Classical.choose (exists_injective_nat ι),Classical.choose_spec (exists_injective_nat ι)⟩
/-- CHR-3 for arbitrary separable complex Hilbert spaces and given canonical form.
    N=2m+2 runs through exactly the even particle numbers at least two. -/
def claim : Prop := ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
  ∀ (ι : Type v) (v : ι × Fin 2 → H) (hv : Orthonormal ℂ v)
    (c : CanonicalFamily ι) (Φ : (UniformSpace.Completion (H ⊗[ℂ] H))),
    HasSum (fun i => (c.coeff i:ℂ) • sourcePairWedge v i) Φ →
  ∀ m : ℕ, (2*(m:ℝ)+2)*lambdaMax c^2≤1 →
  let d := adaptedChart (canonicalIndex v hv) v hv
  ∀ ψ : (tensorTower (sourceHilbertObject H) (2*m+1)).carrier,
    ∀ hanti : (∀ σ : Equiv.Perm (Fin (2*m+2)),
      tensorPermutation (sourceHilbertObject H) d.basis (2*m+1) σ ψ=permutationPhase (2*m+2) σ • ψ),
    ‖ψ‖=1 →
    sourceRayleigh (sourceHilbertObject H) d.basis d.label (2*m)
      (physicalParticle (sourceHilbertObject H) d.basis d.label (2*m+1) ψ hanti) Φ ≤
      (2*(m:ℝ)+2)*(1-(m:ℝ)*(∑' i,c.coeff i^4)+(5/8:ℝ)*((2*(m:ℝ)+2)*lambdaMax c^2)^2)
/-- The uniform source-space Christiansen bound with C=5/8. -/
theorem result : claim.{u,v} := by
  intro H _ _ _ _ ι v hv c Φ hΦ m hsmall
  exact D5.S3.Quantum.FermionicCorrelationalBound.SourceCorrelationalBound.source_cap_result H ι (canonicalIndex v hv) v hv c Φ hΦ m (lambdaMax c^2)
    (sq_nonneg _) (lambdaMax_cap c) hsmall
end
end D5.S3.Quantum.FermionicCorrelationalBound.SourceCorrelationalBound
