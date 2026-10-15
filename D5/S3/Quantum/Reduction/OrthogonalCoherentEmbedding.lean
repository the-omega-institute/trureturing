/- GID: D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/OrthogonalCoherentEmbedding
   mirror-E: none(waiver:finite-dimensional-argument)
   anchors: []
   utility: none
   digest: Every finite orthogonal decomposition embeds into a coherent block of maximal component dimension with complete CPTP decoders. -/

import D5.S3.Quantum.Reduction.CoherentFlagPort
import D5.S3.Quantum.Reduction.ProbeComponentRigidity

noncomputable section
open Matrix
open scoped BigOperators
namespace D5.S3.Quantum.Reduction.ProbeGraphDecomposition
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.Quantum.Reduction.ProbeComponentRigidity
variable {d J : Type*} [Fintype d] [DecidableEq d]

/-- Connected components of the original arbitrary index family. -/
def Component (v : J → d → ℂ) :=
  Quotient (Relation.EqvGen.setoid (fun i j => star (v i) ⬝ᵥ v j ≠ 0))

/-- Class of an original probe index. -/
def component (v : J → d → ℂ) (j : J) : Component v := Quotient.mk _ j

/-- The actual component span in the finite Hilbert space. -/
def hilbertComponent (v : J → d → ℂ) (c : Component v) :
    Submodule ℂ (EuclideanSpace ℂ d) :=
  Submodule.span ℂ {x | ∃ j, component v j = c ∧ WithLp.toLp 2 (v j) = x}

private theorem representatives_orthonormal (v : J → d → ℂ)
    (hv : ∀ j, star (v j) ⬝ᵥ v j = 1) :
    Orthonormal ℂ (fun c : Component v => WithLp.toLp 2 (v c.out)) := by
  classical
  rw [orthonormal_iff_ite]
  intro c e
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  split_ifs with h
  · subst e; exact hv c.out
  · by_contra hn
    have he : c = e := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq e]
      exact Quotient.sound (Relation.EqvGen.rel _ _ hn)
    exact h he

/-- Finite dimensionality proves finiteness of components, even for an
    infinite or otherwise arbitrary probe family. -/
theorem components_finite (v : J → d → ℂ)
    (hv : ∀ j, star (v j) ⬝ᵥ v j = 1) : Finite (Component v) :=
  (representatives_orthonormal v hv).linearIndependent.finite

/-- Distinct graph components span orthogonal Hilbert subspaces. -/
theorem components_orthogonal (v : J → d → ℂ) :
    Pairwise (fun c e : Component v =>
      Submodule.IsOrtho (hilbertComponent v c) (hilbertComponent v e)) := by
  intro c e hce
  rw [hilbertComponent, hilbertComponent, Submodule.isOrtho_span]
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  by_contra h
  apply hce
  exact hi.symm.trans ((Quotient.sound (Relation.EqvGen.rel _ _ h)).trans hj)

/-- The orthogonal component spans exhaust the space whenever the original
    family spans it; no finite-family replacement is assumed. -/
theorem components_span (v : J → d → ℂ)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    (⨆ c : Component v, hilbertComponent v c) = ⊤ := by
  let E := (WithLp.linearEquiv 2 ℂ (d → ℂ)).symm
  have hs : Submodule.span ℂ (Set.range (fun j => WithLp.toLp 2 (v j))) = ⊤ := by
    have h := congrArg (fun S : Submodule ℂ (d → ℂ) => S.map E.toLinearMap) hspan
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_top, LinearMap.range_eq_top.mpr E.surjective,
      E, LinearEquiv.coe_toLinearMap, WithLp.coe_symm_linearEquiv] using h
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  exact (le_iSup (fun c => hilbertComponent v c) (component v j))
    (Submodule.subset_span ⟨j, rfl, rfl⟩)

#print axioms components_finite
#print axioms components_orthogonal
#print axioms components_span
end D5.S3.Quantum.Reduction.ProbeGraphDecomposition

noncomputable section
open Matrix
open scoped BigOperators
namespace D5.S3.Quantum.Reduction.OrthogonalCoherentEmbedding
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 600000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.Quantum.Reduction.CoherentFlagPort
open D5.S3.Quantum.Reduction.ProbeComponentRigidity
variable {d F : Type*} [Fintype d] [DecidableEq d]

/-- An orthonormal coordinate frame of the actual subspace. -/
def frame (S : Submodule ℂ (EuclideanSpace ℂ d)) :
    Matrix d (Fin (Module.finrank ℂ S)) ℂ :=
  fun i k => (stdOrthonormalBasis ℂ S k : EuclideanSpace ℂ d) i

/-- The frame support projection. -/
def projection (S : Submodule ℂ (EuclideanSpace ℂ d)) : Matrix d d ℂ :=
  frame S * (frame S)ᴴ

private theorem frame_gram (S : Submodule ℂ (EuclideanSpace ℂ d)) :
    (frame S)ᴴ * frame S = 1 := by
  ext i j
  rw [← inner_matrix_col_col]
  have h := (orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ S).orthonormal) i j
  simpa only [frame, Matrix.transpose_apply, PiLp.inner_apply,
    Submodule.coe_inner, Matrix.one_apply] using h

private theorem projection_action (S : Submodule ℂ (EuclideanSpace ℂ d))
    (x : d → ℂ) : projection S *ᵥ x =
      (S.starProjection (WithLp.toLp 2 x)).ofLp := by
  rw [projection, ← mulVec_mulVec, Submodule.starProjection_apply,
    (stdOrthonormalBasis ℂ S).orthogonalProjectionOnto_apply_eq_sum]
  ext i
  simp only [frame, mulVec, dotProduct,
    conjTranspose_apply, Submodule.coe_sum, Submodule.coe_smul,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Pi.star_apply]
  ring

private theorem projection_laws (S : Submodule ℂ (EuclideanSpace ℂ d)) :
    (projection S)ᴴ = projection S ∧ projection S * projection S = projection S := by
  constructor
  · simp [projection]
  · simp only [projection, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (frame S)ᴴ, frame_gram, Matrix.one_mul]

/-- Zero padding from a smaller component coordinate space into one coherent port. -/
def padding (n q : ℕ) (h : n ≤ q) : Matrix (Fin q) (Fin n) ℂ :=
  fun i j => if i = Fin.castLE h j then 1 else 0

private theorem padding_gram (n q : ℕ) (h : n ≤ q) :
    (padding n q h)ᴴ * padding n q h = 1 := by
  ext i j
  simp [padding, mul_apply, conjTranspose_apply, Matrix.one_apply,
    eq_comm]

private theorem embedding_gram (S : Submodule ℂ (EuclideanSpace ℂ d))
    (q : ℕ) (h : Module.finrank ℂ S ≤ q) :
    (padding _ q h * (frame S)ᴴ)ᴴ * (padding _ q h * (frame S)ᴴ) =
      projection S := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (padding _ q h)ᴴ, padding_gram, Matrix.one_mul]
  rfl

private theorem projections_complete [Fintype F]
    (S : F → Submodule ℂ (EuclideanSpace ℂ d))
    (horth : Pairwise (fun i j => Submodule.IsOrtho (S i) (S j)))
    (hspan : (⨆ i, S i) = ⊤) : (∑ i, projection (S i)) = 1 := by
  apply ext_iff_mulVec.mpr
  intro x
  simp only [Matrix.sum_mulVec, projection_action, one_mulVec]
  have hf := (OrthogonalFamily.of_pairwise horth).sum_projection_of_mem_iSup
    (WithLp.toLp 2 x) (by rw [hspan]; trivial)
  simpa only [WithLp.ofLp_sum, WithLp.ofLp_toLp] using
    congrArg (fun z : EuclideanSpace ℂ d => z.ofLp) hf

/-- The construction realizes the whole orthogonal pinching map with coherent
    dimension q whenever every actual component has dimension at most q.
    Every decoder is defined and trace preserving on all of M_q. -/
theorem orthogonal_decomposition_port [Fintype F]
    (S : F → Submodule ℂ (EuclideanSpace ℂ d))
    (horth : Pairwise (fun i j => Submodule.IsOrtho (S i) (S j)))
    (hspan : (⨆ i, S i) = ⊤)
    (q : ℕ) (hdim : ∀ i, Module.finrank ℂ (S i) ≤ q)
    (w : ∀ i, S i) (hw : ∀ i, inner ℂ (w i : EuclideanSpace ℂ d) (w i : EuclideanSpace ℂ d) = 1) :
    ∃ port : FlagPort d (Fin q) F Unit (Unit ⊕ (Unit × Fin q)),
      (∀ i, port.encode i () = padding _ q (hdim i) * (frame (S i))ᴴ) ∧
      (∀ i k, port.decode i k = paddedDecoder
        (padding _ q (hdim i) * (frame (S i))ᴴ)
        (fun _ : Unit => (w i : EuclideanSpace ℂ d).ofLp) k) ∧
      (∀ i, projection (S i) * probe (w i : EuclideanSpace ℂ d).ofLp *
        projection (S i) = probe (w i : EuclideanSpace ℂ d).ofLp) ∧
      ∀ X : Matrix d d ℂ, (∑ k, port.kraus k * X * (port.kraus k)ᴴ) =
        ∑ i, projection (S i) * X * projection (S i) := by
  let J : F → Matrix (Fin q) d ℂ :=
    fun i => padding _ q (hdim i) * (frame (S i))ᴴ
  let u : F → Unit → d → ℂ := fun i _ => (w i : EuclideanSpace ℂ d).ofLp
  have hu (i) : (∑ k, star (u i k) ⬝ᵥ u i k) = 1 := by
    simp only [Fintype.sum_unique, u]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact hw i
  obtain ⟨port, henc, hdec, hport⟩ := component_pinching_port J (fun i => projection (S i))
    (fun i => embedding_gram (S i) q (hdim i))
    (fun i => (projection_laws (S i)).1) (fun i => (projection_laws (S i)).2)
    (projections_complete S horth hspan) u hu
  refine ⟨port, henc, hdec, ?_, hport⟩
  intro i
  have hv : projection (S i) *ᵥ (w i : EuclideanSpace ℂ d).ofLp =
      (w i : EuclideanSpace ℂ d).ofLp := by
    rw [projection_action]
    have hp := (S i).starProjection_eq_self_iff.mpr (w i).property
    simpa only [WithLp.toLp_ofLp] using
      congrArg (fun x : EuclideanSpace ℂ d => x.ofLp) hp
  have hl : projection (S i) * probe (w i : EuclideanSpace ℂ d).ofLp =
      probe (w i : EuclideanSpace ℂ d).ofLp := by
    rw [probe, Matrix.mul_vecMulVec, hv]
  have hr : probe (w i : EuclideanSpace ℂ d).ofLp * projection (S i) =
      probe (w i : EuclideanSpace ℂ d).ofLp := by
    have hh := congrArg Matrix.conjTranspose hl
    simpa only [Matrix.conjTranspose_mul, (projection_laws (S i)).1,
      probe, Matrix.conjTranspose_vecMulVec, star_star] using hh
  rw [hl, hr]

open D5.S3.Quantum.Reduction.ProbeGraphDecomposition
open D5.S3.Quantum.Foundation.FiniteStateChannel

private theorem component_space_transport {J : Type*} (v : J → d → ℂ) (j : J) :
    (componentSpace v j).map (WithLp.linearEquiv 2 ℂ (d → ℂ)).symm.toLinearMap =
      hilbertComponent v (component v j) := by
  rw [componentSpace, Submodule.map_span, hilbertComponent]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, (Quotient.sound hi).symm, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨v i, ⟨i, ?_, rfl⟩, rfl⟩
    exact Quotient.exact hi.symm

private theorem component_dimension_transport {J : Type*} (v : J → d → ℂ) (j : J) :
    Module.finrank ℂ (hilbertComponent v (component v j)) =
      Module.finrank ℂ (componentSpace v j) := by
  rw [← component_space_transport v j]
  exact (WithLp.linearEquiv 2 ℂ (d → ℂ)).symm.finrank_map_eq _

/-- Maximum actual graph-component dimension; finiteness is proved from unit
    probes in finite dimension rather than assumed of their index family. -/
def maxComponentDimension {J : Type*} (v : J → d → ℂ)
    (hv : ∀ j, star (v j) ⬝ᵥ v j = 1) : ℕ :=
  letI := components_finite v hv
  letI := Fintype.ofFinite (Component v)
  Finset.univ.sup (fun c => Module.finrank ℂ (hilbertComponent v c))

private theorem component_projection_probe {J : Type*} (v : J → d → ℂ)
    (c : Component v) (j : J) :
    projection (hilbertComponent v c) * probe (v j) =
      if c = component v j then probe (v j) else 0 := by
  classical
  have hm : WithLp.toLp 2 (v j) ∈ hilbertComponent v (component v j) :=
    Submodule.subset_span ⟨j, rfl, rfl⟩
  rw [probe, Matrix.mul_vecMulVec, projection_action]
  split_ifs with hc
  · subst c
    rw [Submodule.starProjection_eq_self_iff.mpr hm]
  · have ho := components_orthogonal v hc
    have hz := ho.orthogonalProjectionOnto_comp_subtypeL
    have hh := DFunLike.congr_fun hz (⟨WithLp.toLp 2 (v j), hm⟩ :
      hilbertComponent v (component v j))
    have hx : (hilbertComponent v c).starProjection (WithLp.toLp 2 (v j)) = 0 := by
      rw [Submodule.starProjection_apply]
      have ht : (hilbertComponent v c).orthogonalProjectionOnto
        (WithLp.toLp 2 (v j)) = 0 := hh
      rw [ht, Submodule.coe_zero]
    rw [hx]
    simp

private theorem pinching_probabilities {J : Type*} (v : J → d → ℂ)
    [Fintype (Component v)] (j : J) (X : Matrix d d ℂ) :
    trace (probe (v j) * (∑ c, projection (hilbertComponent v c) * X *
        projection (hilbertComponent v c))) = trace (probe (v j) * X) := by
  classical
  have hr (c : Component v) : probe (v j) * projection (hilbertComponent v c) =
      if c = component v j then probe (v j) else 0 := by
    have h := congrArg Matrix.conjTranspose (component_projection_probe v c j)
    simpa only [Matrix.conjTranspose_mul, (projection_laws _).1,
      probe, Matrix.conjTranspose_vecMulVec, star_star, apply_ite,
      Matrix.conjTranspose_zero] using h
  rw [Matrix.mul_sum, Matrix.trace_sum]
  have hterm (c : Component v) :
      trace (probe (v j) * (projection (hilbertComponent v c) * X *
        projection (hilbertComponent v c))) =
      if c = component v j then trace (probe (v j) * X) else 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hr]
    by_cases h : c = component v j
    · rw [if_pos h, if_pos h]
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, component_projection_probe, if_pos h]
    · simp [h]
  simp only [hterm]
  simp

/-- Exact coherent-port minimum for the complete arbitrary-family probe menu.
    The finite flags are the proved-finite graph components. The attainable
    port includes whole-block CPTP complement fillers; its output is pinching. -/
theorem exact_component_port_dimension {J : Type*} (v : J → d → ℂ)
    (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤) :
    letI := components_finite v hv
    letI := Fintype.ofFinite (Component v)
    (∀ (q : Type*) [Fintype q] [DecidableEq q]
      (F a b : Type*) [Fintype F] [Fintype a] [Fintype b]
      (port : FlagPort d q F a b),
      (∀ j (ρ : DensityState d),
        trace (probe (v j) * (∑ k, port.kraus k *
          CStarMatrix.ofMatrix.symm ρ.1 * (port.kraus k)ᴴ)) =
        trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) →
      maxComponentDimension v hv ≤ Fintype.card q) ∧
    ∃ port : FlagPort d (Fin (maxComponentDimension v hv)) (Component v)
        Unit (Unit ⊕ (Unit × Fin (maxComponentDimension v hv))),
      (∀ c, ∃ Jc : Matrix (Fin (maxComponentDimension v hv)) d ℂ,
        Jcᴴ * Jc = projection (hilbertComponent v c) ∧
        ∀ k, port.decode c k = paddedDecoder Jc (fun _ : Unit => v c.out) k) ∧
      (∀ c, projection (hilbertComponent v c) * probe (v c.out) *
        projection (hilbertComponent v c) = probe (v c.out)) ∧
      (∀ X : Matrix d d ℂ, (∑ k, port.kraus k * X * (port.kraus k)ᴴ) =
        ∑ c, projection (hilbertComponent v c) * X * projection (hilbertComponent v c)) ∧
      (∀ j (ρ : DensityState d),
        trace (probe (v j) * (∑ k, port.kraus k *
          CStarMatrix.ofMatrix.symm ρ.1 * (port.kraus k)ᴴ)) =
        trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) ∧
      ∃ E : QuantumChannel d (Component v × Fin (maxComponentDimension v hv)),
      ∃ D : QuantumChannel (Component v × Fin (maxComponentDimension v hv)) d,
        (∀ X : Matrix d d ℂ, ∀ c e : Component v, c ≠ e →
          ∀ i j : Fin (maxComponentDimension v hv),
            CStarMatrix.ofMatrix.symm
              (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) (c,i) (e,j) = 0) ∧
        ∀ X : Matrix d d ℂ,
          CStarMatrix.ofMatrix.symm (D.toCompletelyPositiveMap
            (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) =
          ∑ c, projection (hilbertComponent v c) * X * projection (hilbertComponent v c) := by
  classical
  letI := components_finite v hv
  letI := Fintype.ofFinite (Component v)
  constructor
  · intro q fq eq F a b ff fa fb port hp
    apply Finset.sup_le
    intro c hc
    have hd := port_component_lower_bound port v hv hp c.out
    rw [← component_dimension_transport v c.out] at hd
    have he : component v c.out = c := Quotient.out_eq c
    rw [he] at hd
    exact hd
  · let S := hilbertComponent v
    let w : ∀ c, S c := fun c =>
      ⟨WithLp.toLp 2 (v c.out), Submodule.subset_span ⟨c.out, Quotient.out_eq c, rfl⟩⟩
    have hw (c) : inner ℂ (w c : EuclideanSpace ℂ d) (w c : EuclideanSpace ℂ d) = 1 := by
      rw [ EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      exact hv c.out
    have hd (c) : Module.finrank ℂ (S c) ≤ maxComponentDimension v hv := by
      dsimp only [maxComponentDimension, S]
      exact Finset.le_sup (f := fun e : Component v => Module.finrank ℂ (hilbertComponent v e))
        (Finset.mem_univ c)
    obtain ⟨port, _, hdec, hsupp, hp⟩ := orthogonal_decomposition_port S (components_orthogonal v)
      (components_span v hspan) (maxComponentDimension v hv) hd w hw
    obtain ⟨E, D, hclass, hED⟩ := flagged_cptp_roundtrip port
    refine ⟨port, ?_, ?_, hp,
      (fun j ρ => by rw [hp]; exact pinching_probabilities v j _), E, D, hclass, ?_⟩
    · intro c
      refine ⟨padding _ _ (hd c) * (frame (S c))ᴴ,
        embedding_gram (S c) _ (hd c), ?_⟩
      intro k
      simpa only [w, WithLp.ofLp_toLp] using hdec c k
    · intro c
      simpa only [w, WithLp.ofLp_toLp] using hsupp c
    · intro X
      rw [hED, hp]

/-- The full channel formula retains cross-component coherences with their
    actual environment overlaps. Both the component scalars and their unit
    normalization are derived from probability preservation and trace preservation. -/
theorem probe_channel_block_form {s J : Type*} [Fintype s]
    (K : s → Matrix d d ℂ) (hTP : (∑ a, (K a)ᴴ * K a) = 1)
    (v : J → d → ℂ) (hv : ∀ j, star (v j) ⬝ᵥ v j = 1)
    (hspan : Submodule.span ℂ (Set.range v) = ⊤)
    (hprob : ∀ j (ρ : DensityState d),
      trace (probe (v j) * (∑ a, K a * CStarMatrix.ofMatrix.symm ρ.1 * (K a)ᴴ)) =
        trace (probe (v j) * CStarMatrix.ofMatrix.symm ρ.1)) :
    letI := components_finite v hv
    letI := Fintype.ofFinite (Component v)
    let coeff := fun (a : s) (c : Component v) => probeScalar (K a) (v c.out)
    (∀ c, (∑ a, star (coeff a c) * coeff a c) = 1) ∧
    (∀ a, K a = ∑ c, coeff a c • projection (hilbertComponent v c)) ∧
    ∀ X : Matrix d d ℂ, (∑ a, K a * X * (K a)ᴴ) =
      ∑ c, ∑ e, (∑ a, coeff a c * star (coeff a e)) •
        (projection (hilbertComponent v c) * X * projection (hilbertComponent v e)) := by
  classical
  letI := components_finite v hv
  letI := Fintype.ofFinite (Component v)
  let coeff := fun (a : s) (c : Component v) => probeScalar (K a) (v c.out)
  have hs := kraus_scalar_on_component K hTP v hv hprob
  have hn := (component_stinespring_form K hTP v hv hprob).1
  have hkp (a : s) (c : Component v) :
      K a * projection (hilbertComponent v c) =
        coeff a c • projection (hilbertComponent v c) := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
    apply hs a c.out
    have hh := Submodule.starProjection_apply_mem (hilbertComponent v c) (WithLp.toLp 2 x)
    have hc : component v c.out = c := Quotient.out_eq c
    have hm : (hilbertComponent v c).starProjection (WithLp.toLp 2 x) ∈
        (componentSpace v c.out).map (WithLp.linearEquiv 2 ℂ (d → ℂ)).symm.toLinearMap := by
      rw [component_space_transport, hc]
      exact hh
    have ht := (Submodule.mem_map_equiv (componentSpace v c.out)).mp hm
    rw [projection_action]
    exact ht
  have hk (a : s) : K a = ∑ c, coeff a c • projection (hilbertComponent v c) := by
    calc
      K a = K a * (∑ c, projection (hilbertComponent v c)) := by
        rw [projections_complete _ (components_orthogonal v) (components_span v hspan),
          Matrix.mul_one]
      _ = _ := by rw [Matrix.mul_sum]; simp only [hkp]
  refine ⟨fun c => hn c.out, hk, ?_⟩
  intro X
  have hact (a : s) : K a * X * (K a)ᴴ =
      ∑ c, ∑ e, (coeff a c * star (coeff a e)) •
        (projection (hilbertComponent v c) * X * projection (hilbertComponent v e)) := by
    calc
      _ = (∑ c, coeff a c • projection (hilbertComponent v c)) * X *
          (∑ e, coeff a e • projection (hilbertComponent v e))ᴴ := by rw [← hk a]
      _ = _ := by
        simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
          (projection_laws _).1, Matrix.sum_mul, Matrix.mul_sum,
          Matrix.smul_mul, Matrix.mul_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp only [mul_comm]
  simp only [hact]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_smul]

#print axioms orthogonal_decomposition_port
#print axioms exact_component_port_dimension
#print axioms probe_channel_block_form
end D5.S3.Quantum.Reduction.OrthogonalCoherentEmbedding
