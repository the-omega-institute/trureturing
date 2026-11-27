/- GID: D5/S3/Zeros/GRH/Lib/General/Measure/HaarModulus
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Measure/HaarModulus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Measure.HaarModulus. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Measure/HaarModulus.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.ColumnLattices
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of measure and integration (textbook or folklore).

General lemmas of commutative and general algebra (textbook or folklore).

This file: Haar measure push-forwards, modulus versus index, modulus of GL_n equals modulus of
determinant. -/

open MeasureTheory Measure Set Pointwise ENNReal Function AddSubgroup


variable {n R A B Z G} [Fintype n] [Group Z] [MeasurableSpace Z] [MeasurableMul Z] [Group G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [DistribMulAction G A]
  [ContinuousConstSMul G A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [PolishSpace A]

@[to_additive] lemma measure_le_of_div_mem {ζ} [IsMulRightInvariant ζ] {E K :
  Set Z} (h : ∀ y ∈ E, ∃ g,
  ∀ z ∈ E, z / g ∈ K) : ζ E ≤ ζ K := E.eq_empty_or_nonempty.elim (by aesop) (·.elim h |>.elim
  fun _ ↦ ((measurePreserving_div_right ..).measure_preimage_le _).trans' ∘ ζ.mono)

/-- For μ bi-invariant on Z, η left invariant on G, π: Z → G a measurable homomorphism, O ⊂ Z
measurable, each h having a preimage that preserves O on both sides: η(K)·π_*(μ|O) = μ(π⁻¹K ∩ O)·η⁻,
η⁻ the inverted measure, and this measure is left invariant. -/
@[to_additive] lemma map_restrict_haar_eq [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] μ [SFinite μ]
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] η [SFinite η] (π : Z →* G) {O K C}
  [η.IsMulLeftInvariant] (c : Measurable π) (o : MeasurableSet O) (s : ∀ h, ∃ g, (∀ x, (g * x ∈ O
  ↔ x ∈ O) ∧ (x * g ∈ O ↔ x ∈ O)) ∧ π g = h) (k : MeasurableSet K) (e : π ⁻¹' K ∩ O = C) :
  η K • (μ.restrict O).map π = μ C • η.inv ∧ (μ C • η.inv).IsMulLeftInvariant := by
  choose g s using s
  have := (forall_measure_preimage_mul_iff ((μ.restrict O).map π)).1 fun a A m ↦ by
    simpa [measurable_const_mul a m, inter_def, *] using measure_preimage_mul μ (g a) (π ⁻¹' A ∩ O)
  exact (fun E ↦ ⟨E, E ▸ inferInstance⟩) (ext_of_lintegral _ (by simp +contextual (disch :=
    measurability) [↓smul_eq_mul, ↓measure_mul_lintegral_eq, inv_def, lintegral_map, ← e, inter_def,
    fun b ↦ by simpa [inter_def, ← e, s] using measure_preimage_mul_right μ (g b) C]))

/-- Let G act by continuous automorphisms on a locally compact Polish abelian group A, L a
compact open subgroup, K = gL. Then [L : K ∩ L] / [K : K ∩ L] = 1/c, where g multiplies Haar
measure on A by c. -/
lemma inv_distribHaarChar_eq_relIndex_div (L : AddSubgroup A) (ho : @IsOpen A _ L) (hc : @IsCompact
  A _ L) (g : G) : (distribHaarChar A g).toReal⁻¹ = (g • L).relIndex L / L.relIndex (g • L) := by
  borelize A
  have := congr(($(relIndex_add_measure_inf (H := g • L) hc (ho.smul g) addHaar).toReal,
    $(relIndex_add_measure_inf (K := g • L) (hc.smul g) ho addHaar).toReal))
  simp_all [← distribHaarChar_mul]
  grind [toReal_pos (ho.measure_ne_zero addHaar (by simp)) hc.measure_ne_top]

variable [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [μ.IsAddHaarMeasure] [MeasurableSpace A]
  [BorelSpace A] {ν : Measure A} [ν.IsAddHaarMeasure] {O : Subring R}

/-- Let e : B → A be a topological group isomorphism, A Polish locally compact abelian, ψ
measurable, e∘φ = ψ∘e. If ψ pushes a Haar measure ν of A to c·ν, then φ pushes every Haar
measure μ of B to c·μ. -/
lemma map_haar_eq_smul_of_semiconj (e : B ≃ₜ+ A) {ψ φ} (h : ∀ x, e (φ x) = ψ (e x)) {c : ℝ≥0∞}
    (hc : ν.map ψ = c • ν) (hψ : Measurable ψ := by fun_prop) : μ.map φ = c • μ := by
  simpa (disch := fun_prop) [map_map, ← h, smul_comm, ← Measure.map_smul, comp_def,
    ← isAddLeftInvariant_eq_smul] using congr((μ.map e).addHaarScalarFactor ν • map e.symm $hc)

lemma map_smul_eq_inv_distribHaarChar_smul (a : G) : ν.map (a • ·) =
  ENNReal.ofReal (distribHaarChar A a)⁻¹ • ν := ext (by
  simp_all [coe_nnreal_eq, measurable_const_smul, preimage_smul, ← distribHaarChar_mul])

instance : ContinuousSMul (GL n R) (n → R) := ⟨by unfold_projs; fun_prop⟩

instance : ContinuousConstSMul (GL n R) (n → R) := inferInstance

/-- The multiplicative character of R sending a unit a to the inverse of its module, the factor
by which a scales additive Haar measure, and non-units to 0. -/
noncomputable def genIndex : MulChar R ℝ :=
  .ofUnitHom (NNReal.toRealHom.1.comp (distribHaarChar R)).toHomUnits⁻¹

lemma genIndex_eq_inv_distribHaarChar (a : Rˣ) : (↑(distribHaarChar R a))⁻¹ =
  genIndex a.1 := by simp [genIndex]

lemma genIndex_pos (a : Rˣ) : 0 < genIndex a.1 := by simp [genIndex, distribHaarChar_pos]

variable [PolishSpace R] (ho : @IsOpen R _ O) (hc : @IsCompact R _ O)
include ho hc

/-- Let O be a compact open subring of R and let a in O be a unit of R. Then `genIndex` of a, the
inverse module of a, equals the number of elements of the quotient ring O/aO. -/
lemma genIndex_eq_card {a} ha (u : IsUnit a) : genIndex a =
  Nat.card (O ⧸ Ideal.span {(⟨a, ha⟩ : O)}) := by
  erw [← genIndex_eq_inv_distribHaarChar u.unit,
    inv_distribHaarChar_eq_relIndex_div O.toAddSubgroup ho hc, O.relIndex_eq_one.2]
  simpa using! (congrArg index (by aesop (add simp [Ideal.mem_span_singleton', mul_comm]))).symm
  rintro _ ⟨⟩; aesop

lemma genIndex_det_eq_one {V} : V ∈ intGL n O → genIndex V.1.det = 1 := (·.choose_spec ▸ by
  erw [← RingHom.map_det, genIndex_eq_card ho hc _ (.map ..)] <;> simp [Nat.card_unique])

/-- Let R be a locally compact Polish commutative ring with a compact open subring O satisfying
`IsValuationPair`. Then g in GL_n(R) scales Haar measure on R^n by the same factor as det g
scales Haar measure on R. -/
lemma distribHaarChar_GL_eq_det (val : IsValuationPair O) (g : GL n R) :
    (↑(distribHaarChar (n → R) g))⁻¹ = genIndex g.1.det := by
  have (k) (h : k ∈ intGL n O) := by simpa [relIndex_eq_one.2, LE.le, Units.smul_def,
    mem_inv_pointwise_smul_iff, mulVec_mem_intVectors_iff h] using
    (inv_distribHaarChar_eq_relIndex_div (intVectors O n).toAddSubgroup
    isOpen_intVectors (isCompact_pi_infinite (by tauto)) k⁻¹ :)
  choose _ _ _ _ d e using val.smith_normal_form g.1
  lift d to n → Rˣ using by simpa [e] using g.det.isUnit
  borelize R
  simpa [Units.ext (v := _ * diagGL d * _) e, genIndex_det_eq_one ho,
    ← genIndex_eq_inv_distribHaarChar, addHaarMeasure_self,
    real_def, ← distribHaarChar_mul, *] using fun C ↦ congr((Measure.pi fun _ ↦ addHaarMeasure
    C).real $((image_congr' (f := (diagGL d • ·)) (funext <| Matrix.mulVec_diagonal _ ·)).trans
    (piMap_image_univ_pi (d · • ·) (@const (Set R) n C))))
