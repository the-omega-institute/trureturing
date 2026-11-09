/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Higher-body Bose marginals and their actual tensor support. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseComponentProjector
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

/-! Support lifting for genuine subsystem partial traces and hyperedge Bose support. -/

open scoped BigOperators ComplexOrder Kronecker
open Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumStates.ZeroWeightSupportFace
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHyperedgeSupport

set_option backward.isDefEq.respectTransparency false

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

attribute [local instance] Classical.propDecidable

private lemma support_from_partial_trace {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (E : Matrix (A × B) (A × B) ℂ) (hE : E.PosSemidef)
    (p : Matrix A A ℂ) (hp : p.IsHermitian) (hi : p * p = p)
    (hs : p * partialTraceRight E * p = partialTraceRight E) :
    (p ⊗ₖ (1 : Matrix B B ℂ)) * E * (p ⊗ₖ 1) = E := by
  have hr : partialTraceRight E * p = partialTraceRight E := by
    have hh := congrArg (fun M => M * p) hs
    rw [Matrix.mul_assoc (p * partialTraceRight E) p p, hi, hs] at hh
    exact hh.symm
  have hq : (1 - p) * (1 - p) = 1 - p := by
    calc
      (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
      _ = 1 - p := by rw [hi]; abel
  have hstar : ((1 - p) ⊗ₖ (1 : Matrix B B ℂ))ᴴ = (1 - p) ⊗ₖ 1 := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hp.eq]
  have hidem : ((1 - p) ⊗ₖ (1 : Matrix B B ℂ)) * ((1 - p) ⊗ₖ 1) =
      (1 - p) ⊗ₖ 1 := by
    rw [← Matrix.mul_kronecker_mul, hq, one_mul]
  have htr : Matrix.trace (E * ((1 - p) ⊗ₖ (1 : Matrix B B ℂ))) = 0 := by
    rw [Matrix.trace_mul_kron_one_right]
    change Matrix.trace (partialTraceRight E * (1 - p)) = 0
    rw [mul_sub, mul_one, hr, sub_self, Matrix.trace_zero]
  have hh := (zero_weight_support_face E ((1 - p) ⊗ₖ (1 : Matrix B B ℂ))
    hE hstar hidem htr).2
  have hc : (1 : Matrix (A × B) (A × B) ℂ) - (1 - p) ⊗ₖ (1 : Matrix B B ℂ) =
      p ⊗ₖ 1 := by
    calc
      _ = (1 : Matrix A A ℂ) ⊗ₖ (1 : Matrix B B ℂ) - (1 - p) ⊗ₖ 1 := by
        rw [Matrix.one_kronecker_one]
      _ = _ := by
        ext x y
        simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
        ring
  simpa only [hc] using hh.symm

/-- Split a tensor word into a specified subsystem and its actual complement. -/
noncomputable def subsystemSplit (S : Finset I) :
    (I → L) ≃ (S → L) × ({i : I // i ∉ S} → L) :=
  Equiv.piEquivPiSubtypeProd (fun i : I => i ∈ S) (fun _ => L)

/-- The unnormalized higher-body partial trace in the original computational basis. -/
noncomputable def subsystemMarginal (S : Finset I) (E : Matrix (I → L) (I → L) ℂ) :
    Matrix (S → L) (S → L) ℂ :=
  partialTraceRight (E.submatrix (subsystemSplit S).symm (subsystemSplit S).symm)

/-- Symmetrize the selected registers and retain the full complement identity. -/
noncomputable def subsystemProjector (S : Finset I) : Matrix (I → L) (I → L) ℂ :=
  (P S L ⊗ₖ (1 : Matrix ({i : I // i ∉ S} → L) ({i : I // i ∉ S} → L) ℂ)).submatrix
    (subsystemSplit S) (subsystemSplit S)

/-- Bose support of a subsystem marginal forces the same support on the joint operator.
The complement is unrestricted, and neither normalization nor nonsingularity is needed. -/
theorem subsystem_support (S : Finset I) (E : Matrix (I → L) (I → L) ℂ)
    (hE : E.PosSemidef)
    (hs : P S L * subsystemMarginal S E * P S L = subsystemMarginal S E) :
    subsystemProjector S * E * subsystemProjector S = E := by
  let e := subsystemSplit (L := L) S
  have hh := support_from_partial_trace (E.submatrix e.symm e.symm)
    (hE.submatrix e.symm) (P S L) (P_hermitian _ _) (P_idempotent _ _) hs
  have hc := congrArg (fun M => M.submatrix e e) hh
  rw [← Matrix.submatrix_mul_equiv _ _ e e e,
    ← Matrix.submatrix_mul_equiv _ _ e e e] at hc
  simpa only [subsystemProjector, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id] using hc

#print axioms subsystem_support

open private Local.R_local_tensor Q_one Q_mulVec Q_mul_P from
  D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open private pair_support_of_column_swap from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

private lemma subsystem_permutation_fix (S : Finset I) (τ : Equiv.Perm S) :
    Q (τ.subtypeCongr (1 : Equiv.Perm {i : I // i ∉ S})) *
      subsystemProjector (L := L) S = subsystemProjector S := by
  let e := subsystemSplit (L := L) S
  have ht := Local.R_local_tensor (L := L) S τ (1 : Equiv.Perm {i : I // i ∉ S})
  change (Q (τ.subtypeCongr (1 : Equiv.Perm {i : I // i ∉ S}))).submatrix
    e.symm e.symm = Q τ ⊗ₖ Q (1 : Equiv.Perm {i : I // i ∉ S}) at ht
  rw [Q_one] at ht
  have ht' := congrArg (fun M => M.submatrix e e) ht
  simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self,
    Matrix.submatrix_id_id] at ht'
  rw [ht']
  change (Q τ ⊗ₖ (1 : Matrix _ _ ℂ)).submatrix e e *
    (P S L ⊗ₖ (1 : Matrix _ _ ℂ)).submatrix e e = _
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Q_mul_P, one_mul]
  rfl

private lemma extend_swap (S : Finset I) {a b : I} (ha : a ∈ S) (hb : b ∈ S) :
    (Equiv.swap (⟨a,ha⟩ : S) ⟨b,hb⟩).subtypeCongr
      (1 : Equiv.Perm {i : I // i ∉ S}) = Equiv.swap a b := by
  ext k
  by_cases hk : k ∈ S
  · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hk]
    by_cases hka : k = a
    · subst k
      simp
    by_cases hkb : k = b
    · subst k
      simp
    rw [Equiv.swap_apply_of_ne_of_ne
      (by intro h; exact hka (congrArg Subtype.val h))
      (by intro h; exact hkb (congrArg Subtype.val h)),
      Equiv.swap_apply_of_ne_of_ne hka hkb]
  · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hk]
    rw [Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hk ha)
      (by rintro rfl; exact hk hb)]
    rfl

/-- Every ordered pair inside a Bose-supported higher-body marginal is Bose-supported. -/
theorem pairs_of_subsystem_support (S : Finset I)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hs : P S L * subsystemMarginal S E * P S L = subsystemMarginal S E)
    (a b : I) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    pairSymmetricProjector * edgeMarginal a b hab E * pairSymmetricProjector =
      edgeMarginal a b hab E := by
  have hsupport := subsystem_support S E hE hs
  have hf := subsystem_permutation_fix (L := L) S (Equiv.swap (⟨a,ha⟩ : S) ⟨b,hb⟩)
  rw [extend_swap S ha hb] at hf
  have he : Q (Equiv.swap a b) * E = E := by
    calc
      Q (Equiv.swap a b) * E = Q (Equiv.swap a b) *
          (subsystemProjector S * E * subsystemProjector S) := by rw [hsupport]
      _ = subsystemProjector S * E * subsystemProjector S := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hf]
      _ = E := hsupport
  apply pair_support_of_column_swap a b hab E hE
  intro x y
  have hx := congrArg (fun M => M x y) he
  exact (congrFun (Q_mulVec (Equiv.swap a b) (fun z => E z y)) x).symm.trans hx

/-- The union of the cliques on the selected higher-body subsets. -/
def hyperedgeGraph (H : Finset (Finset I)) : SimpleGraph I where
  Adj a b := a ≠ b ∧ ∃ S ∈ H, a ∈ S ∧ b ∈ S
  symm := ⟨by
    rintro a b ⟨hab,S,hS,ha,hb⟩
    exact ⟨hab.symm,S,hS,hb,ha⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- A connected union of Bose-supported higher-body subsets forces full Bose support
and equality of every ordered pair marginal on the same joint operator. -/
theorem support_of_connected_hyperedges (H : Finset (Finset I))
    (hH : (hyperedgeGraph H).Connected)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef)
    (hs : ∀ S ∈ H,
      P S L * subsystemMarginal S E * P S L = subsystemMarginal S E) :
    P I L * E * P I L = E ∧
      ∀ u v a b (huv : u ≠ v) (hab : a ≠ b),
        edgeMarginal a b hab E = edgeMarginal u v huv E := by
  apply support_of_connected_graph (hyperedgeGraph H) hH E hE
  rintro a b ⟨hab,S,hS,ha,hb⟩
  exact pairs_of_subsystem_support S E hE (hs S hS) a b ha hb hab

#print axioms pairs_of_subsystem_support
#print axioms support_of_connected_hyperedges

end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseHyperedgeSupport
