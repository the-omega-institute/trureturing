/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseDPS
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Bose-leaf DPS extensions, symmetry adaptation and closedness. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose
import D5.S3.Quantum.Measurement.IncoherentCone
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner

/-! Britz--Laurent (2026), equations (25)--(31), use Bose leaf support,
an unnormalized root--leaf partial trace, and leaf partial transposes.
Here cuts are initially indexed by subsets; permutation reduction to the
paper's initial-segment cuts is a separate equivalence, not an assumption.
The support implication is due to Hansenne--Xu--Kraft--Guehne.
The applications in the source note are by Haobo Ma and Wenlin Zhang. -/

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

open private leaf_conjugation_invariance allCuts_of_leafCuts allCuts_iff
  partialTranspose_empty from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose
open private edge_covariance_of_conjugation pair_support_of_column_swap all_edges_equal from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

/-- An ordinary DPS certificate with the actual Bose leaf sandwich and one
prescribed marginal. The empty leaf cut includes positivity of `E`. -/
def OrdinaryWitness (root leaf : I) (hne : root ≠ leaf)
    (ρ : Matrix (L × L) (L × L) ℂ) (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  leafProjector root * E * leafProjector root = E ∧
    edgeMarginal root leaf hne E = ρ ∧
      ∀ S : Finset I, root ∉ S → (partialTransposeOn S E).PosSemidef

/-- The adapted certificate has full Bose support on the same tensor registers. -/
def AdaptedWitness (root leaf : I) (hne : root ≠ leaf)
    (ρ : Matrix (L × L) (L × L) ℂ) (E : Matrix (I → L) (I → L) ℂ) : Prop :=
  P I L * E * P I L = E ∧ edgeMarginal root leaf hne E = ρ ∧ AllCutsPPT E

/-- The actual ordinary cone, without trace normalization. -/
def ordinaryDPS (root leaf : I) (hne : root ≠ leaf) :
    Set (Matrix (L × L) (L × L) ℂ) := {ρ | ∃ E, OrdinaryWitness root leaf hne ρ E}

/-- The actual full-Bose adapted cone, without trace normalization. -/
def adaptedDPS (root leaf : I) (hne : root ≠ leaf) :
    Set (Matrix (L × L) (L × L) ℂ) := {ρ | ∃ E, AdaptedWitness root leaf hne ρ E}

private lemma ordinary_pos (root leaf : I) (hne : root ≠ leaf)
    (ρ : Matrix (L × L) (L × L) ℂ) (E : Matrix (I → L) (I → L) ℂ)
    (h : OrdinaryWitness root leaf hne ρ E) : E.PosSemidef := by
  simpa only [partialTranspose_empty] using h.2.2 ∅ (by simp)

private lemma ordinary_star (root leaf : I) (hne : root ≠ leaf)
    (ρ : Matrix (L × L) (L × L) ℂ) (E : Matrix (I → L) (I → L) ℂ)
    (h : OrdinaryWitness root leaf hne ρ E) : StarExtension root ρ E := by
  have hp := ordinary_pos root leaf hne ρ E h
  refine ⟨hp,h.1,?_,((allCuts_iff E).mp (allCuts_of_leafCuts root E h.2.2)).2⟩
  intro i hi
  let σ : Equiv.Perm I := Equiv.swap leaf i
  have hr : σ root = root := Equiv.swap_apply_of_ne_of_ne hne hi
  have hl : σ leaf = i := Equiv.swap_apply_left leaf i
  have hm := edge_covariance_of_conjugation E σ root leaf hne
    (leaf_conjugation_invariance root E hp.isHermitian h.1 σ hr)
  have transport (a b : I) (hab : a ≠ b) (ha : a = root) (hb : b = i)
      (hh : edgeMarginal a b hab E = edgeMarginal root leaf hne E) :
      edgeMarginal root i hi E = edgeMarginal root leaf hne E := by
    subst a
    subst b
    exact hh
  exact (transport _ _ _ hr hl hm).trans h.2.1

private lemma ordinary_of_star (root leaf : I) (hne : root ≠ leaf)
    (ρ : Matrix (L × L) (L × L) ℂ) (E : Matrix (I → L) (I → L) ℂ)
    (h : StarExtension root ρ E) : OrdinaryWitness root leaf hne ρ E :=
  ⟨h.2.1,h.2.2.1 leaf hne,fun S _ => (allCuts_iff E).mpr ⟨h.1,h.2.2.2⟩ S⟩

private lemma columns_of_support (E : Matrix (I → L) (I → L) ℂ)
    (hs : P I L * E * P I L = E) :
    ∀ y, IsSymmetricVector (fun x => E x y) := by
  have hl : P I L * E = E := by
    calc
      P I L * E = P I L * (P I L * E * P I L) := by rw [hs]
      _ = (P I L * P I L) * E * P I L := by simp only [Matrix.mul_assoc]
      _ = E := by rw [P_idempotent, hs]
  intro y
  have hh := P_mulVec_symmetric (fun x => E x y)
  have he : P I L *ᵥ (fun x => E x y) = (fun x => E x y) := by
    funext x
    exact congrArg (fun M => M x y) hl
  rwa [he] at hh

private lemma marginal_bose (root leaf : I) (hne : root ≠ leaf)
    (E : Matrix (I → L) (I → L) ℂ) (hp : E.PosSemidef)
    (hs : P I L * E * P I L = E) :
    pairSymmetricProjector * edgeMarginal root leaf hne E * pairSymmetricProjector =
      edgeMarginal root leaf hne E := by
  apply pair_support_of_column_swap root leaf hne E hp
  intro x y
  exact columns_of_support E hs y (Equiv.swap root leaf) x

/-- The adapted and ordinary witnesses are the same individual matrices on a Bose input.
Complementary cuts account for every cut containing the root, including both endpoints. -/
theorem adapted_iff_ordinary (root leaf : I) (hne : root ≠ leaf)
    (ρ : Matrix (L × L) (L × L) ℂ)
    (hρ : pairSymmetricProjector * ρ * pairSymmetricProjector = ρ)
    (E : Matrix (I → L) (I → L) ℂ) :
    AdaptedWitness root leaf hne ρ E ↔ OrdinaryWitness root leaf hne ρ E := by
  constructor
  · rintro ⟨hs,hm,hp⟩
    have hc : CompleteExtension ρ E :=
      ⟨((allCuts_iff E).mp hp).1, hs, fun a b hab =>
        (all_edges_equal E ((allCuts_iff E).mp hp).1.isHermitian
          (columns_of_support E hs) root leaf a b hne hab).trans hm,
        ((allCuts_iff E).mp hp).2⟩
    exact ordinary_of_star root leaf hne ρ E ((same_matrix root ρ hρ E).mpr hc)
  · intro h
    have hc := (same_matrix root ρ hρ E).mp (ordinary_star root leaf hne ρ E h)
    exact ⟨hc.2.1,h.2.1,(allCuts_iff E).mpr ⟨hc.1,hc.2.2.2⟩⟩

/-- Britz--Laurent's Bose-input hierarchy comparison is equality. The cone on the
right is intersected with the actual PSD symmetric-support face. -/
theorem adapted_eq_inter (root leaf : I) (hne : root ≠ leaf) :
    adaptedDPS (L := L) root leaf hne = ordinaryDPS root leaf hne ∩
      {ρ | ρ.PosSemidef ∧ pairSymmetricProjector * ρ * pairSymmetricProjector = ρ} := by
  ext ρ
  constructor
  · rintro ⟨E,hE⟩
    have hp := ((allCuts_iff E).mp hE.2.2).1
    have hs : pairSymmetricProjector * ρ * pairSymmetricProjector = ρ := by
      rw [← hE.2.1]
      exact marginal_bose root leaf hne E hp hE.1
    refine ⟨⟨E,(adapted_iff_ordinary root leaf hne ρ hs E).mp hE⟩,?_,hs⟩
    rw [← hE.2.1]
    exact partialTraceRight_posSemidef (hp.submatrix (edgeSplit root leaf hne).symm)
  · rintro ⟨⟨E,hE⟩,_,hs⟩
    exact ⟨E,(adapted_iff_ordinary root leaf hne ρ hs E).mpr hE⟩

private lemma trace_edgeMarginal (root leaf : I) (hne : root ≠ leaf)
    (E : Matrix (I → L) (I → L) ℂ) :
    Matrix.trace (edgeMarginal root leaf hne E) = Matrix.trace E := by
  rw [edgeMarginal, trace_partialTraceRight]
  exact (edgeSplit root leaf hne).symm.sum_comp (fun x => E x x)

private lemma psd_closed_finite {A : Type*} [Fintype A] :
    IsClosed {E : Matrix A A ℂ | E.PosSemidef} := by
  let e := Fintype.equivFin A
  have he (E : Matrix A A ℂ) : E.PosSemidef ↔
      (E.submatrix e.symm e.symm).PosSemidef := by
    constructor
    · exact fun h => h.submatrix _
    · intro h
      simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self,
        Matrix.submatrix_id_id] using h.submatrix e
  simp_rw [he]
  exact D5.S3.Quantum.Measurement.IncoherentCone.psd_closed.preimage (by fun_prop)

private lemma psd_bound_finite {A : Type*} [Fintype A]
    (E : Matrix A A ℂ) (hp : E.PosSemidef) (R : ℝ) (hR : 0 < R)
    (ht : (Matrix.trace E).re ≤ R) (i j : A) : ‖E i j‖ ≤ R := by
  let e := Fintype.equivFin A
  have htr : Matrix.trace (E.submatrix e.symm e.symm) = Matrix.trace E :=
    e.symm.sum_comp (fun x => E x x)
  have h := D5.S3.Quantum.Measurement.IncoherentCone.psd_entry_bound_of_trace
    (hp.submatrix e.symm) R hR (by simpa only [RHLinalg.rtrace,htr] using ht) (e i) (e j)
  simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply] using h

/-- The ordinary DPS cone is closed: bounded input traces bound every actual
positive lift, so a convergent subsequence retains support, marginal and all cuts. -/
theorem ordinary_closed (root leaf : I) (hne : root ≠ leaf) :
    IsClosed (ordinaryDPS (L := L) root leaf hne) := by
  letI : NormedAddCommGroup (Matrix (I → L) (I → L) ℂ) :=
    inferInstanceAs (NormedAddCommGroup ((I → L) → (I → L) → ℂ))
  letI : NormedSpace ℝ (Matrix (I → L) (I → L) ℂ) :=
    inferInstanceAs (NormedSpace ℝ ((I → L) → (I → L) → ℂ))
  rw [← isSeqClosed_iff_isClosed]
  intro u ρ hu hlim
  choose E hE using hu
  have htcont : Continuous (fun A : Matrix (L × L) (L × L) ℂ => (Matrix.trace A).re) := by
    unfold Matrix.trace
    fun_prop
  obtain ⟨R,hR,hbound⟩ := (Metric.isBounded_range_of_tendsto _
    ((htcont.tendsto ρ).comp hlim)).exists_pos_norm_le
  have htrace (k : ℕ) : (Matrix.trace (E k)).re ≤ R := by
    rw [← trace_edgeMarginal root leaf hne, (hE k).2.1]
    exact (le_abs_self _).trans (hbound _ ⟨k,rfl⟩)
  have hnorm (k : ℕ) : ‖E k‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR.le).mpr
    intro x
    apply (pi_norm_le_iff_of_nonneg hR.le).mpr
    intro y
    exact psd_bound_finite _ (ordinary_pos root leaf hne _ _ (hE k)) R hR (htrace k) x y
  have hball (k : ℕ) : E k ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hnorm k
  obtain ⟨E₀,_,φ,hφ,hElim⟩ := (isCompact_closedBall 0 R).tendsto_subseq hball
  have hs : leafProjector root * E₀ * leafProjector root = E₀ := by
    have hc : IsClosed {F : Matrix (I → L) (I → L) ℂ |
        leafProjector root * F * leafProjector root = F} :=
      isClosed_eq (by fun_prop) continuous_id
    exact hc.mem_of_tendsto hElim (Eventually.of_forall fun k => (hE (φ k)).1)
  have hm : edgeMarginal root leaf hne E₀ = ρ := by
    have hc : Continuous (edgeMarginal (L := L) root leaf hne) := by
      unfold edgeMarginal partialTraceRight
      fun_prop
    have hh := (hc.tendsto E₀).comp hElim
    have he : (fun k => edgeMarginal root leaf hne (E (φ k))) = u ∘ φ := by
      funext k
      exact (hE (φ k)).2.1
    rw [he] at hh
    exact tendsto_nhds_unique hh (hlim.comp hφ.tendsto_atTop)
  refine ⟨E₀,hs,hm,?_⟩
  intro S hr
  have hc : Continuous (partialTransposeOn (L := L) S) := by
    unfold partialTransposeOn
    fun_prop
  exact psd_closed_finite.mem_of_tendsto ((hc.tendsto E₀).comp hElim)
    (Eventually.of_forall fun k => (hE (φ k)).2.2 S hr)

#print axioms adapted_eq_inter
#print axioms ordinary_closed

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS
