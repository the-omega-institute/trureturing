/- GID: D5/S3/Quantum/Algebra/PBOriginalReadoutRealization
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBOriginalReadoutRealization
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional]
   utility: none
   digest: Original positive tables yield coherent readings without extending the response. -/

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

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/28078 -/

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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
  simp [cyclicOrbit, map_mul, mul_apply_eq_comp]

private theorem orbit_inner (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) (a b : A) :
    inner ℂ (φ.gnsStarAlgHom a (cyclicVector φ))
      (φ.gnsStarAlgHom b (cyclicVector φ)) = φ (star a * b) := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  simpa [map_mul, mul_apply_eq_comp] using (normalized_gns φ hφ).2.1 (star a*b)

private theorem central_on_cyclic (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (B C : StarSubalgebra ℂ A)
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
    simpa [r, map_sub, map_smul, sub_apply,
      smul_apply, sub_eq_zero] using hr
  apply closure_minimal (s := ((cyclicOrbit φ B).range : Set φ.GNS)) ?_
    (isClosed_eq (φ.gnsStarAlgHom (c : A)).continuous (continuous_id.const_smul (χ c))) v.2
  rintro w ⟨b, rfl⟩
  change φ.gnsStarAlgHom (c : A) (φ.gnsStarAlgHom b (cyclicVector φ)) = _
  rw [← mul_apply_eq_comp, ← map_mul, hcentral, map_mul,
    mul_apply_eq_comp, hcξ, map_smul]
  rfl

instance realCyclic (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) :
    InnerProductSpace ℝ (cyclicSpace φ B) := InnerProductSpace.complexToReal

instance cyclicComplete (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) :
    CompleteSpace (cyclicSpace φ B) := Submodule.topologicalClosure.completeSpace _

private theorem repr_smul (φ : A →ₚ[ℂ] ℂ) (r : ℝ) (a : A) :
    φ.gnsStarAlgHom (r • a) = r • φ.gnsStarAlgHom a :=
  (φ.gnsStarAlgHom.toAlgHom.restrictScalars ℝ).toLinearMap.map_smul r a

/-- Compression of one ambient representation is coherent on every original label. -/
def compressedOp (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A)
    (i : E →ₗ[ℝ] A) : E →ₗ[ℝ] (cyclicSpace φ B →ₗ[ℝ] cyclicSpace φ B) where
  toFun a := ((cyclicSpace φ B).orthogonalProjectionOnto.comp
    ((φ.gnsStarAlgHom (i a)).comp (cyclicSpace φ B).subtypeL)).toLinearMap.restrictScalars ℝ
  map_add' a b := by ext v; simp [map_add]
  map_smul' r a := by
    ext v
    change ((cyclicSpace φ B).orthogonalProjectionOnto
      (φ.gnsStarAlgHom (i (r • a)) v) : φ.GNS) =
      ((r • (cyclicSpace φ B).orthogonalProjectionOnto
        (φ.gnsStarAlgHom (i a) v) : cyclicSpace φ B) : φ.GNS)
    rw [i.map_smul, repr_smul]
    simp only [smul_apply, ContinuousLinearMap.map_smul_of_tower,
      Submodule.coe_smul_of_tower]

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

private theorem compressed_symmetric (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A)
    (i : E →ₗ[ℝ] A) (hi : ∀ a, IsSelfAdjoint (i a)) (a : E) :
    (compressedOp φ B i a).IsSymmetric := by
  intro v w
  change (inner ℂ (compressedOp φ B i a v) w).re =
    (inner ℂ v (compressedOp φ B i a w)).re
  have he : inner ℂ (compressedOp φ B i a v) w =
      inner ℂ (φ.gnsStarAlgHom (i a) v) (w : φ.GNS) := by
    rw [← inner_conj_symm, compressed_inner, inner_conj_symm]
  rw [he, compressed_inner]
  exact congrArg Complex.re ((hi a).map φ.gnsStarAlgHom |>.isSymmetric v w)

private theorem compressed_unit (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A)
    (i : E →ₗ[ℝ] A) (u : E) (hu : i u = 1) :
    compressedOp φ B i u = LinearMap.id := by
  ext v
  rw [compressed_known φ B i u (hu ▸ B.one_mem), hu]
  simp

private theorem compressed_jordan (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A)
    (i : E →ₗ[ℝ] A) (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hJ : ∀ a b, i (J a b) = (1 / 2 : ℝ) • (i a * i b + i b * i a))
    (a b : E) (ha : a ∈ knownLabels B i) (hb : b ∈ knownLabels B i) :
    compressedOp φ B i (J a b) = (1 / 2 : ℝ) •
      ((compressedOp φ B i a).comp (compressedOp φ B i b) +
       (compressedOp φ B i b).comp (compressedOp φ B i a)) := by
  ext v
  have hab : i (J a b) ∈ B := by
    rw [hJ]
    exact B.smul_mem (B.add_mem (B.mul_mem ha hb) (B.mul_mem hb ha)) _
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    Submodule.coe_smul_of_tower, Submodule.coe_add]
  rw [compressed_known φ B i (J a b) hab, hJ,
    compressed_known φ B i a ha, compressed_known φ B i b hb,
    compressed_known φ B i b hb, compressed_known φ B i a ha]
  simp only [repr_smul, map_add, map_mul, smul_apply, add_apply, mul_apply_eq_comp]

private def vectorRead (φ : A →ₚ[ℂ] ℂ) (i : E →ₗ[ℝ] A) (v : φ.GNS) : E →ₗ[ℝ] ℝ where
  toFun c := (inner ℂ v (φ.gnsStarAlgHom (i c) v)).re
  map_add' c d := by
    simp only [map_add, add_apply, inner_add_right, Complex.add_re]
  map_smul' r c := by
    simp only [map_smul, repr_smul, smul_apply, inner_smul_right_eq_smul, smul_eq_mul]
    exact RCLike.smul_re (K := ℂ) r (inner ℂ v (φ.gnsStarAlgHom (i c) v))

private theorem vectorRead_nonneg (φ : A →ₚ[ℂ] ℂ) (i : E →ₗ[ℝ] A)
    (v : φ.GNS) (c : E) (hc : 0 ≤ i c) : 0 ≤ vectorRead φ i v c := by
  obtain ⟨w, hw⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hc
  change 0 ≤ (inner ℂ v (φ.gnsStarAlgHom (i c) v)).re
  rw [hw, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := φ.gnsStarAlgHom w v)

private theorem compressed_p2 {P : Type*}
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (i : E →ₗ[ℝ] A) (p : P → E →ₗ[ℝ] ℝ)
    (hexact : ∀ a, 0 ≤ i a ↔ ∀ q, 0 ≤ p q a)
    (hraw : ∀ q a b, (originalTable J D (p q) a b).PosSemidef)
    (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) (v : cyclicSpace φ B) (a b : E) :
    inner ℝ v (compressedOp φ B i (D a b) v)^2 ≤
      inner ℝ v (compressedOp φ B i (J a a) v) *
      inner ℝ v (compressedOp φ B i (J b b) v) -
      inner ℝ v (compressedOp φ B i (J a b) v)^2 := by
  have h := positive_read_p2 J D i p hexact hraw (vectorRead φ i v)
    (vectorRead_nonneg φ i v) a b
  change (inner ℂ v (compressedOp φ B i (D a b) v)).re ^ 2 ≤
    (inner ℂ v (compressedOp φ B i (J a a) v)).re *
    (inner ℂ v (compressedOp φ B i (J b b) v)).re -
    (inner ℂ v (compressedOp φ B i (J a b) v)).re ^ 2
  simpa only [compressed_inner, vectorRead, LinearMap.coe_mk, AddHom.coe_mk] using h

private def compressedReadout {P : Type*}
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E) (D : E → E → E)
    (i : E →ₗ[ℝ] A) (hi : ∀ a, IsSelfAdjoint (i a)) (hu : i u = 1)
    (hJ : ∀ a b, i (J a b) = (1 / 2 : ℝ) • (i a * i b + i b * i a))
    (p : P → E →ₗ[ℝ] ℝ) (hexact : ∀ a, 0 ≤ i a ↔ ∀ q, 0 ≤ p q a)
    (hraw : ∀ q a b, (originalTable J D (p q) a b).PosSemidef)
    (φ : A →ₚ[ℂ] ℂ) (B : StarSubalgebra ℂ A) :
    Readout (H := cyclicSpace φ B) J u D (knownLabels B i) where
  op := compressedOp φ B i
  symmetric := compressed_symmetric φ B i hi
  unit := compressed_unit φ B i u hu
  jordan a ha b hb := compressed_jordan φ B i J hJ a b ha hb
  p2 := compressed_p2 J D i p hexact hraw φ B

/-- A faithful supplied JC carrier and the original, unnormalized preparation tables.
No completeness assumption is made on E and D is an arbitrary total function. -/
structure OriginalData (P : Type*) where
  J : E →ₗ[ℝ] E →ₗ[ℝ] E
  u : E
  D : E → E → E
  i : E →ₗ[ℝ] A
  isometry : Isometry i
  selfadjoint : ∀ a, IsSelfAdjoint (i a)
  unit : i u = 1
  jordan : ∀ a b, i (J a b) = (1 / 2 : ℝ) • (i a * i b + i b * i a)
  preparation : P → E →ₗ[ℝ] ℝ
  exact_cone : ∀ a, 0 ≤ i a ↔ ∀ q, 0 ≤ preparation q a
  raw_p2 : ∀ q a b, (originalTable J D (preparation q) a b).PosSemidef

section Original
variable {P : Type*}

/-- Actual original Jordan quantities in the specified central algebra.
Their derivation from original PB/orthogonality is a separate unpaid interface. -/
structure SectorCertificate (O : OriginalData (A := A) (E := E) P)
    (B C : StarSubalgebra ℂ A) (χ : C →⋆ₐ[ℂ] ℂ) (x y : E) (X Y δ : ℝ) where
  x_mem : O.i x ∈ B
  y_mem : O.i y ∈ B
  d_mem : O.i (O.D x y) ∈ B
  xx : C
  yy : C
  dd : C
  xy : C
  xd : C
  yd : C
  source_xx : O.i (O.J x x) = xx
  source_yy : O.i (O.J y y) = yy
  source_dd : O.i (O.J (O.D x y) (O.D x y)) = dd
  source_xy : O.i (O.J x y) = xy
  source_xd : O.i (O.J x (O.D x y)) = xd
  source_yd : O.i (O.J y (O.D x y)) = yd
  read_xx : χ xx = (X ^ 2 : ℝ)
  read_yy : χ yy = (Y ^ 2 : ℝ)
  read_dd : χ dd = (δ ^ 2 : ℝ)
  read_xy : χ xy = 0
  read_xd : χ xd = 0
  read_yd : χ yd = 0

/-- The exact conclusion of the preserved outer-budget theorem, on original labels. -/
def OuterBudgets (O : OriginalData (A := A) (E := E) P)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {L : Submodule ℝ E} (R : Readout (H := H) O.J O.u O.D L)
    (x y : E) (X Y δ : ℝ) : Prop :=
  ∀ l t : ℝ, t ≠ 0 → t ^ 2 = l ^ 2*X ^ 2+1 →
    let z := t • O.u + l • x
    let ν := O.D x y - O.J x z
    let ω := O.J x y + O.D x z
    ∃ v : H, inner ℝ v v = 1 ∧
      reading R v (O.D (y+ν) (z+ω))^2 ≤ X ^ 2/t ^ 2+δ ^ 2 ∧
      reading R v (O.D (y-ν) (z-ω))^2 ≤ X ^ 2/t ^ 2+δ ^ 2 ∧
      reading R v (O.D (y+ν) (z+ω)) - reading R v (O.D (y-ν) (z-ω)) =
        2*l*X ^ 2*Y/t ∧
      l ^ 2*X ^ 2*(X ^ 2*Y ^ 2-δ ^ 2) ≤ X ^ 2+δ ^ 2

private theorem compressed_scalar (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1 = 1)
    (B C : StarSubalgebra ℂ A) (hCB : C ≤ B)
    (χ : C →⋆ₐ[ℂ] ℂ) (hretain : ∀ c : C, φ c = χ c)
    (hcentral : ∀ (c : C) (b : B), (c : A) * b = b * c)
    (i : E →ₗ[ℝ] A) (a : E) (c : C) (r : ℝ)
    (hsource : i a = c) (hread : χ c = r) :
    compressedOp φ B i a = r • LinearMap.id := by
  ext v
  rw [compressed_known φ B i a (hsource ▸ hCB c.2), hsource,
    central_on_cyclic φ hφ B C χ hretain hcentral, hread]
  simp

private theorem jordan_square {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E} {L : Submodule ℝ E}
    (R : Readout (H := H) J u D L) (a : E) (ha : a ∈ L) (r : ℝ)
    (hs : R.op (J a a) = r • LinearMap.id) (v : H) :
    R.op a (R.op a v) = r • v := by
  have h := congrArg (fun T : H →ₗ[ℝ] H => T v) (R.jordan a ha a ha)
  rw [hs] at h
  simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.add_apply,
    LinearMap.comp_apply] at h
  calc
    _ = (1 / 2 : ℝ) • (R.op a (R.op a v) + R.op a (R.op a v)) := by module
    _ = r • v := h.symm

private theorem jordan_cross {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E} {L : Submodule ℝ E}
    (R : Readout (H := H) J u D L) (a b : E) (ha : a ∈ L) (hb : b ∈ L)
    (hs : R.op (J a b) = 0) (v : H) : R.op a (R.op b v) = -R.op b (R.op a v) := by
  have h := congrArg (fun T : H →ₗ[ℝ] H => T v) (R.jordan a ha b hb)
  rw [hs] at h
  simp only [LinearMap.zero_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.comp_apply] at h
  exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h.symm).resolve_left (by norm_num))

private def normalizedFibre {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E} {L : Submodule ℝ E}
    (R : Readout (H := H) J u D L) (x y : E) (X Y δ : ℝ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (sx : ∀ v, R.op x (R.op x v) = X ^ 2 • v)
    (sy : ∀ v, R.op y (R.op y v) = Y ^ 2 • v)
    (sd : ∀ v, R.op (D x y) (R.op (D x y) v) = δ ^ 2 • v)
    (cxy : ∀ v, R.op x (R.op y v) = -R.op y (R.op x v))
    (cxd : ∀ v, R.op x (R.op (D x y) v) = -R.op (D x y) (R.op x v))
    (cyd : ∀ v, R.op y (R.op (D x y) v) = -R.op (D x y) (R.op y v)) :
    Fibre R x y X Y δ where
  e := X⁻¹ • R.op x
  f := Y⁻¹ • R.op y
  reads_x := by simp [smul_smul, hX]
  reads_y := by simp [smul_smul, hY]
  symmetric_e := (R.symmetric x).smul (by simp)
  symmetric_f := (R.symmetric y).smul (by simp)
  square_e v := by simp [LinearMap.smul_apply, map_smul, sx, smul_smul, hX, pow_two]
  square_f v := by simp [LinearMap.smul_apply, map_smul, sy, smul_smul, hY, pow_two]
  cross v := by simp [LinearMap.smul_apply, map_smul, cxy, smul_smul, mul_comm]
  cross_d_left v := by simp [LinearMap.smul_apply, map_smul, cxd]
  cross_d_right v := by simp [LinearMap.smul_apply, map_smul, cyd]
  square_d := sd

private theorem zero_axis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H] {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E}
    {L : Submodule ℝ E} (R : Readout (H := H) J u D L) (x y : E) (X Y δ : ℝ)
    (sxx : R.op (J x x) = X ^ 2 • LinearMap.id)
    (syy : R.op (J y y) = Y ^ 2 • LinearMap.id)
    (sd : ∀ v, R.op (D x y) (R.op (D x y) v) = δ ^ 2 • v)
    (hzero : X = 0 ∨ Y = 0) : R.op (D x y) = 0 ∧ δ = 0 := by
  have hq (v : H) : inner ℝ v (R.op (D x y) v) = 0 := by
    have hp := R.p2 v x y
    rcases hzero with hX | hY
    · simp [sxx, hX] at hp
      nlinarith [sq_nonneg (inner ℝ v (R.op (J x y) v))]
    · simp [syy, hY] at hp
      nlinarith [sq_nonneg (inner ℝ v (R.op (J x y) v))]
  have hd : R.op (D x y) = 0 :=
    (R.symmetric (D x y)).inner_map_self_eq_zero.mp (fun v => by rw [real_inner_comm]; exact hq v)
  refine ⟨hd, ?_⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have he := sd v
  simp [hd] at he
  have : δ ^ 2 = 0 := (smul_eq_zero.mp he.symm).resolve_right hv
  nlinarith [sq_nonneg δ]

/-- A single ambient state and its coherent readout, with the actual PB conclusion. -/
structure Realization (O : OriginalData (A := A) (E := E) P)
    (B C : StarSubalgebra ℂ A) (χ : C →⋆ₐ[ℂ] ℂ) (x y : E) (X Y δ : ℝ) where
  state : A →ₚ[ℂ] ℂ
  state_one : state 1 = 1
  retains : ∀ c : C, state c = χ c
  R : Readout (H := cyclicSpace state B) O.J O.u O.D (knownLabels B O.i)
  coherent : R.op = compressedOp state B O.i
  unit_vector : ∃ v : cyclicSpace state B, ‖v‖ = 1
  central : ∀ (c : C) (v : cyclicSpace state B),
    state.gnsStarAlgHom c (v : state.GNS) = χ c • (v : state.GNS)
  zero_branch : X = 0 ∨ Y = 0 → R.op (O.D x y) = 0 ∧ δ = 0
  nonzero_branch : X ≠ 0 → Y ≠ 0 →
    ∃ F : Fibre R x y X Y δ, OuterBudgets O R x y X Y δ

/-- The zero carrier is trivial on the original E and D; a proper specified
character supplies the complete coherent realization in the other branch. -/
theorem original_piecewise (O : OriginalData (A := A) (E := E) P)
    (hPB : PB O.J O.D) (BI : BDerivedInterface O.J O.u O.D)
    (B C : StarSubalgebra ℂ A) [IsClosed (C : Set A)] (hCB : C ≤ B)
    (hcentral : ∀ (c : C) (b : B), (c : A) * b = b * c) :
    (Subsingleton A → (∀ a : E, a = 0) ∧ (∀ a b : E, O.D a b = 0)) ∧
    (∀ (χ : C →⋆ₐ[ℂ] ℂ) (x y : E) (X Y δ : ℝ),
      SectorCertificate O B C χ x y X Y δ → Nonempty (Realization O B C χ x y X Y δ)) := by
  refine ⟨?_, ?_⟩
  · intro hA
    letI : Subsingleton A := hA
    have hz (a : E) : a = 0 := O.isometry.injective (Subsingleton.elim _ _)
    exact ⟨hz, fun a b => hz (O.D a b)⟩
  · intro χ x y X Y δ S
    obtain ⟨φ, hφ, hretain⟩ := ambient_state_extension C χ
    let R := compressedReadout O.J O.u O.D O.i O.selfadjoint O.unit O.jordan
      O.preparation O.exact_cone O.raw_p2 φ B
    let v : cyclicSpace φ B := ⟨cyclicVector φ, cyclic_unit_mem φ B⟩
    have hv : ‖v‖ = 1 := (normalized_gns φ hφ).1
    letI : Nontrivial (cyclicSpace φ B) := nontrivial_of_ne v 0 (by
      intro h
      have hn := congrArg norm h
      simp [hv] at hn)
    have scalar (a : E) (c : C) (r : ℝ) (hs : O.i a = c) (hr : χ c = r) :
        R.op a = r • LinearMap.id :=
      compressed_scalar φ hφ B C hCB χ hretain hcentral O.i a c r hs hr
    have sxx := scalar (O.J x x) S.xx (X ^ 2) S.source_xx S.read_xx
    have syy := scalar (O.J y y) S.yy (Y ^ 2) S.source_yy S.read_yy
    have sdd := scalar (O.J (O.D x y) (O.D x y)) S.dd (δ ^ 2) S.source_dd S.read_dd
    have sxy : R.op (O.J x y) = 0 := by simpa using scalar _ S.xy 0 S.source_xy S.read_xy
    have sxd : R.op (O.J x (O.D x y)) = 0 := by simpa using scalar _ S.xd 0 S.source_xd S.read_xd
    have syd : R.op (O.J y (O.D x y)) = 0 := by simpa using scalar _ S.yd 0 S.source_yd S.read_yd
    have sx := jordan_square R x S.x_mem (X ^ 2) sxx
    have sy := jordan_square R y S.y_mem (Y ^ 2) syy
    have sd := jordan_square R (O.D x y) S.d_mem (δ ^ 2) sdd
    have cxy := jordan_cross R x y S.x_mem S.y_mem sxy
    have cxd := jordan_cross R x (O.D x y) S.x_mem S.d_mem sxd
    have cyd := jordan_cross R y (O.D x y) S.y_mem S.d_mem syd
    refine ⟨{
      state := φ
      state_one := hφ
      retains := hretain
      R := R
      coherent := rfl
      unit_vector := ⟨v, hv⟩
      central := central_on_cyclic φ hφ B C χ hretain hcentral
      zero_branch := zero_axis R x y X Y δ sxx syy sd
      nonzero_branch := ?_ }⟩
    intro hX hY
    let F := normalizedFibre R x y X Y δ hX hY sx sy sd cxy cxd cyd
    refine ⟨F, ?_⟩
    intro l t ht htsq
    apply actual_outer_budget O.J O.u O.D hPB BI (knownLabels B O.i)
      (by change O.i O.u ∈ B; rw [O.unit]; exact B.one_mem)
      (fun a ha b hb => by
        change O.i (O.J a b) ∈ B
        rw [O.jordan]
        exact B.smul_mem (B.add_mem (B.mul_mem ha hb) (B.mul_mem hb ha)) _)
      R x y S.x_mem S.y_mem S.d_mem X Y δ l t ht htsq F

#print axioms original_piecewise
end Original
end D5.S3.Quantum.Algebra.PBOriginalReadoutRealization
