/- GID: D5/S3/Quantum/Algebra/PBOriginalReadoutRealization
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBOriginalReadoutRealization
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional]
   utility: none
   digest: Original positive two-tables pass to coherent compressed readings without extending the response. -/

import D5.S3.Quantum.Algebra.PBActualOuterBudget
import D5.S3.QuantumStates.GNSCompatibleStateExtension
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef

/-! Coherent original-label readings of one ambient state. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ComplexOrder InnerProductSpace Matrix
open Complex

namespace D5.S3.Quantum.Algebra.PBOriginalReadoutRealization
open PBActualOuterBudget
open D5.S3.QuantumStates.GNSCompatibleStateExtension

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- One ambient state retains a specified proper central character. -/
private theorem ambient_state_extension (C : StarSubalgebra ℂ A)
    [IsClosed (C : Set A)] (χ : C →⋆ₐ[ℂ] ℂ) :
    ∃ φ : A →ₚ[ℂ] ℂ, φ 1 = 1 ∧ ∀ c : C, φ c = χ c := by
  letI : Nontrivial C := χ.toAlgHom.toRingHom.domain_nontrivial
  let f : C →L[ℂ] ℂ := χ.toAlgHom.toContinuousLinearMap
  have hn : ‖f‖ = 1 := by
    apply le_antisymm
    · exact f.opNorm_le_bound zero_le_one (fun c => by
        simpa [f] using AlgHom.norm_apply_le_self χ c)
    · simpa [f] using f.le_opNorm (1 : C)
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq C.toSubalgebra.toSubmodule f
  have hg1 : g 1 = 1 := by
    calc g 1 = f (1 : C) := hg (1 : C)
         _ = 1 := map_one χ
  let φ : A →ₚ[ℂ] ℂ := {
    toLinearMap := g.toLinearMap
    monotone' := ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mpr (by
      have hgn1 : ‖g‖ = 1 := hgn.trans hn
      simp only [hgn1, hg1, Complex.ofReal_one]) }
  exact ⟨φ, hg1, hg⟩

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The original directed Hermitian two-table, with no normalized mass. -/
def originalTable (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (p : E →ₗ[ℝ] ℝ) (a b : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(p (J a a) : ℂ), (p (J a b) : ℂ) - I * p (D a b);
     (p (J b a) : ℂ) - I * p (D b a), (p (J b b) : ℂ)]

/-- The quadratic element belongs to the same original real label space. -/
private def quadratic (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (a b : E) (z : Fin 2 → ℂ) : E :=
  normSq (z 0) • J a a + normSq (z 1) • J b b +
    (2 * (star (z 0) * z 1).re) • J a b +
    (2 * (star (z 0) * z 1).im) • D a b

private theorem table_skew (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (p : E →ₗ[ℝ] ℝ) (a b : E) (h : (originalTable J D p a b).IsHermitian) :
    p (J b a) = p (J a b) ∧ p (D b a) = -p (D a b) := by
  have he := congrFun (congrFun h 0) 1
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp [originalTable, Matrix.conjTranspose_apply] at hr hi
  exact ⟨hr, by linarith⟩

private theorem quadratic_read (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (p : E →ₗ[ℝ] ℝ) (a b : E) (z : Fin 2 → ℂ)
    (h : (originalTable J D p a b).IsHermitian) :
    p (quadratic J D a b z) =
      (star z ⬝ᵥ (originalTable J D p a b *ᵥ z)).re := by
  obtain ⟨hs, hd⟩ := table_skew J D p a b h
  simp [quadratic, originalTable, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    map_add, map_smul, hs, hd, Complex.normSq_apply]
  <;> ring

/-- Exact original cone positivity transfers the whole Hermitian two-table to
any mathematical positive functional, including the zero functional. -/
private theorem positive_read_p2 {P : Type*}
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (i : E →ₗ[ℝ] A) (p : P → E →ₗ[ℝ] ℝ)
    (hexact : ∀ a, 0 ≤ i a ↔ ∀ q, 0 ≤ p q a)
    (hraw : ∀ q a b, (originalTable J D (p q) a b).PosSemidef)
    (f : E →ₗ[ℝ] ℝ) (hf : ∀ a, 0 ≤ i a → 0 ≤ f a) (a b : E) :
    f (D a b)^2 ≤ f (J a a) * f (J b b) - f (J a b)^2 := by
  have hzero (c : E) (hc : ∀ q, p q c = 0) : f c = 0 := by
    have hp := hf c ((hexact c).mpr (fun q => (hc q).ge))
    have hm := hf (-c) ((hexact (-c)).mpr (fun q => by simp [hc q]))
    simpa using le_antisymm (by simpa using hm) hp
  have hs : f (J b a) = f (J a b) := by
    have := hzero (J b a - J a b) (fun q => by
      simpa using sub_eq_zero.mpr (table_skew J D (p q) a b (hraw q a b).1).1)
    exact sub_eq_zero.mp (by simpa only [map_sub] using this)
  have hd : f (D b a) = -f (D a b) := by
    have := hzero (D b a + D a b) (fun q => by
      simp [map_add, (table_skew J D (p q) a b (hraw q a b).1).2])
    exact eq_neg_of_add_eq_zero_left (by simpa using this)
  have herm : (originalTable J D f a b).IsHermitian := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [originalTable, Matrix.conjTranspose_apply, hs, hd, sub_eq_add_neg]
  have hmat : (originalTable J D f a b).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨herm, fun z => ?_⟩
    have hq : 0 ≤ f (quadratic J D a b z) := by
      apply hf
      apply (hexact _).mpr
      intro q
      rw [quadratic_read J D (p q) a b z (hraw q a b).1]
      exact (Complex.nonneg_iff.mp ((hraw q a b).dotProduct_mulVec_nonneg z)).1
    have hzreal : (star z ⬝ᵥ (originalTable J D f a b *ᵥ z)).im = 0 := by
      simp [originalTable, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hs, hd]
      <;> ring
    apply Complex.nonneg_iff.mpr
    exact ⟨by rwa [← quadratic_read J D f a b z herm], hzreal.symm⟩
  have hdet := (Complex.nonneg_iff.mp hmat.det_nonneg).1
  simp [originalTable, Matrix.det_fin_two, hs, hd] at hdet
  nlinarith

/-- The closed B-cyclic subspace of a single ambient GNS representation. -/
def cyclicOrbit (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) : B →ₗ[ℂ] φ.GNS where
  toFun b := φ.gnsStarAlgHom b (cyclicVector φ)
  map_add' b c := by simp
  map_smul' r b := by simp

def cyclicSpace (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) : Submodule ℂ φ.GNS :=
  (cyclicOrbit φ B).range.topologicalClosure

instance realGNS (φ : A →ₚ[ℂ] ℂ) : InnerProductSpace ℝ φ.GNS :=
  InnerProductSpace.complexToReal

private theorem cyclic_unit_mem (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) :
    cyclicVector φ ∈ cyclicSpace φ B := by
  apply Submodule.le_topologicalClosure
  exact ⟨1, by simp [cyclicOrbit]⟩

private theorem cyclic_invariant (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A)
    (b : B) (v : cyclicSpace φ B) :
    φ.gnsStarAlgHom b (v : φ.GNS) ∈ cyclicSpace φ B := by
  apply closure_minimal (s := ((cyclicOrbit φ B).range : Set φ.GNS)) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage (φ.gnsStarAlgHom b).continuous) v.2
  rintro w ⟨c, rfl⟩
  apply Submodule.le_topologicalClosure
  refine ⟨b*c, ?_⟩
  simp [cyclicOrbit, map_mul, ContinuousLinearMap.mul_apply]

private theorem orbit_inner (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) (a b : A) :
    inner ℂ (φ.gnsStarAlgHom a (cyclicVector φ))
      (φ.gnsStarAlgHom b (cyclicVector φ)) = φ (star a * b) := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  simpa [map_mul, ContinuousLinearMap.mul_apply] using (normalized_gns φ hφ).2.1 (star a*b)

private theorem central_on_cyclic (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (B C : StarSubalgebra ℂ A) (hCB : C ≤ B)
    (χ : C →⋆ₐ[ℂ] ℂ) (hretain : ∀ c : C, φ c = χ c)
    (hcentral : ∀ (c : C) (b : B), (c : A) * b = b * c)
    (c : C) (v : cyclicSpace φ B) :
    φ.gnsStarAlgHom c (v : φ.GNS) = χ c • (v : φ.GNS) := by
  let r : C := c - χ c • 1
  have hrχ : χ r = 0 := by simp [r]
  have hrφ : φ (star (r : A) * r) = 0 := by
    simpa [hrχ] using hretain (star r * r)
  have hr : φ.gnsStarAlgHom (r : A) (cyclicVector φ) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [orbit_inner φ hφ, hrφ]
  have hcξ : φ.gnsStarAlgHom (c : A) (cyclicVector φ) = χ c • cyclicVector φ := by
    simpa [r, map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, sub_eq_zero] using hr
  apply closure_minimal (s := ((cyclicOrbit φ B).range : Set φ.GNS)) ?_
    (isClosed_eq (φ.gnsStarAlgHom (c : A)).continuous (continuous_id.const_smul (χ c))) v.2
  rintro w ⟨b, rfl⟩
  change φ.gnsStarAlgHom (c : A) (φ.gnsStarAlgHom b (cyclicVector φ)) = _
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcentral, map_mul,
    ContinuousLinearMap.mul_apply, hcξ, map_smul]
  rfl

instance realCyclic (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) :
    InnerProductSpace ℝ (cyclicSpace φ B) := InnerProductSpace.complexToReal

instance cyclicComplete (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) :
    CompleteSpace (cyclicSpace φ B) := Submodule.topologicalClosure.completeSpace _

/-- Compression of one ambient representation is coherent on every original label. -/
def compressedOp (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A)
    (i : E →ₗ[ℝ] A) : E →ₗ[ℝ] (cyclicSpace φ B →ₗ[ℝ] cyclicSpace φ B) where
  toFun a := ((cyclicSpace φ B).orthogonalProjectionOnto.comp
    ((φ.gnsStarAlgHom (i a)).comp (cyclicSpace φ B).subtypeL)).toLinearMap.restrictScalars ℝ
  map_add' a b := by ext v; simp [map_add]
  map_smul' r a := by
    ext v
    simp [map_smul, show φ.gnsStarAlgHom (r • i a) = r • φ.gnsStarAlgHom (i a) from
      φ.gnsStarAlgHom.toAlgHom.map_smul_of_tower r (i a),
      ContinuousLinearMap.map_smul_of_tower]

private theorem compressed_known (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A)
    (i : E →ₗ[ℝ] A) (a : E) (ha : i a ∈ B) (v : cyclicSpace φ B) :
    (compressedOp φ B i a v : φ.GNS) = φ.gnsStarAlgHom (i a) v := by
  change ((cyclicSpace φ B).orthogonalProjectionOnto
    (φ.gnsStarAlgHom (i a) v) : φ.GNS) = _
  exact congrArg Subtype.val ((cyclicSpace φ B).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨_, cyclic_invariant φ B ⟨i a, ha⟩ v⟩)

private theorem compressed_inner (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A)
    (i : E →ₗ[ℝ] A) (a : E) (v w : cyclicSpace φ B) :
    inner ℂ v (compressedOp φ B i a w) = inner ℂ (v : φ.GNS) (φ.gnsStarAlgHom (i a) w) := by
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

/-- The known Jordan domain is exactly the inverse image of B. -/
def knownLabels (B : StarSubalgebra ℂ A) (i : E →ₗ[ℝ] A) : Submodule ℝ E :=
  B.toSubalgebra.toSubmodule.restrictScalars ℝ |>.comap i

private def compressedReadout {P : Type*}
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E) (D : E → E → E)
    (i : E →ₗ[ℝ] A) (hi : ∀ a, IsSelfAdjoint (i a)) (hu : i u = 1)
    (hJ : ∀ a b, i (J a b) = (1/2 : ℝ) • (i a * i b + i b * i a))
    (p : P → E →ₗ[ℝ] ℝ) (hexact : ∀ a, 0 ≤ i a ↔ ∀ q, 0 ≤ p q a)
    (hraw : ∀ q a b, (originalTable J D (p q) a b).PosSemidef)
    (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) :
    Readout (H := cyclicSpace φ B) J u D (knownLabels B i) := by
  refine { op := compressedOp φ B i, symmetric := ?_, unit := ?_, jordan := ?_, p2 := ?_ }
  · intro a v w
    change (inner ℂ (compressedOp φ B i a v) w).re =
      (inner ℂ v (compressedOp φ B i a w)).re
    have he : inner ℂ (compressedOp φ B i a v) w =
        inner ℂ (φ.gnsStarAlgHom (i a) v) (w : φ.GNS) := by
      rw [← inner_conj_symm, compressed_inner, inner_conj_symm]
    rw [he, compressed_inner]
    exact congrArg Complex.re ((hi a).map φ.gnsStarAlgHom |>.isSymmetric v w)
  · ext v
    rw [compressed_known φ B i u (hu ▸ B.one_mem), hu]
    simp
  · intro a ha b hb
    ext v
    have hab : i (J a b) ∈ B := by rw [hJ]; exact B.smul_mem (B.add_mem (B.mul_mem ha hb) (B.mul_mem hb ha)) _
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
      Submodule.coe_smul, Submodule.coe_add]
    rw [compressed_known φ B i (J a b) hab, hJ,
      compressed_known φ B i a ha, compressed_known φ B i b hb,
      compressed_known φ B i b hb, compressed_known φ B i a ha]
    simp [map_add, AlgHom.map_smul_of_tower, map_mul, ContinuousLinearMap.mul_apply]
  · intro v a b
    let f : E →ₗ[ℝ] ℝ := {
      toFun c := (inner ℂ (v : φ.GNS) (φ.gnsStarAlgHom (i c) v)).re
      map_add' c d := by simp [inner_add_right]
      map_smul' r c := by simp [show φ.gnsStarAlgHom (r • i c) = r • φ.gnsStarAlgHom (i c) from
        φ.gnsStarAlgHom.toAlgHom.map_smul_of_tower r (i c),
        smul_apply, inner_smul_right] }
    have hf : ∀ c, 0 ≤ i c → 0 ≤ f c := by
      intro c hc
      obtain ⟨w, hw⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hc
      change 0 ≤ (inner ℂ (v : φ.GNS) (φ.gnsStarAlgHom (i c) v)).re
      rw [hw, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
        mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
      exact inner_self_nonneg
    have h := positive_read_p2 J D i p hexact hraw f hf a b
    change (inner ℂ v (compressedOp φ B i (D a b) v)).re ^ 2 ≤
      (inner ℂ v (compressedOp φ B i (J a a) v)).re *
      (inner ℂ v (compressedOp φ B i (J b b) v)).re -
      (inner ℂ v (compressedOp φ B i (J a b) v)).re ^ 2
    simpa only [compressed_inner, f, LinearMap.coe_mk, AddHom.coe_mk] using h

end D5.S3.Quantum.Algebra.PBOriginalReadoutRealization
