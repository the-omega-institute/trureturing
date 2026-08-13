/- GID: D5/S3/Resource/SeparableConeClosed
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The finite-dimensional separable cone is closed; witness existence remains open. -/
import Mathlib
import D5.S3.Resource.CompositeCones
import D5.S3.Resource.CompositeConeDuality
import D5.S3.Resource.EntanglementWitness
/- Provenance: Native proof over pinned mathlib. -/
/- Provenance note: witness existence is omitted because plain matrices lack the compatible real
   Hilbert-space instance required by pinned `ProperCone.hyperplane_separation'`. -/
/- Search receipt (2026-08-14): searched local D5 for `separableCone`,
   `blockPositive`, their inclusions, trace-pairing duality, and cone/convexity
   lemmas. Searched pinned mathlib for compact convex hulls, conic-hull closedness,
   Caratheodory, finite-dimensional compactness, matrix continuity, PSD rank-one
   decomposition, and proper-cone separation. Hits used below include `convexHull_eq_union`,
   `AffineIndependent.card_le_finrank_succ`, `isCompact_stdSimplex`, `isCompact_sphere`,
   `IsCompact.tendsto_subseq`, and `Matrix.posSemidef_iff_eq_sum_vecMulVec`; rechecked the
   `ConvexCone` constructor and `ProperCone` lift/separation APIs. Misses: compact-convex-hull
   for compact sets, closed conic hull, PSD-matrix closedness, and this closedness theorem.
   Loogle had no "conic hull" hit; GitHub search was unavailable because `gh`
   had no authenticated account. -/
namespace D5.S3.Resource.SeparableConeClosed
noncomputable section
set_option maxHeartbeats 0
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.CompositeConeDuality
open D5.S3.Resource.EntanglementWitness
open scoped Kronecker ComplexOrder InnerProductSpace
variable {m n : ℕ}
abbrev CompositeMatrix (m n : ℕ) := Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ
private lemma sum_extend_embedding {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid A] (e : ι ↪ κ) (f : ι → A) :
    ∑ j : κ, Function.extend e f 0 j = ∑ i : ι, f i := by
  classical
  calc
    ∑ j : κ, Function.extend e f 0 j =
        ∑ j ∈ Finset.univ.map e, Function.extend e f 0 j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hjmap
      exact Function.extend_apply' _ _ _ (by
        simpa only [Finset.mem_map, Finset.mem_univ, true_and, not_exists] using hjmap)
    _ = ∑ i : ι, f i := by
      rw [Finset.sum_map]
      simp [e.injective.extend_apply]
private def productGenerator (a : EuclideanSpace ℂ (Fin m))
    (b : EuclideanSpace ℂ (Fin n)) :
    CompositeMatrix m n :=
  Matrix.vecMulVec a.ofLp (star a.ofLp) ⊗ₖ Matrix.vecMulVec b.ofLp (star b.ofLp)
private lemma continuous_productGenerator :
    Continuous (fun p : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n) =>
      productGenerator p.1 p.2) := by
  apply continuous_matrix
  intro i j
  simp only [productGenerator, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply]
  fun_prop
private abbrev arity (m n : ℕ) := Module.finrank ℝ (CompositeMatrix m n) + 1
private def unitPairs (m n : ℕ) :
    Set (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n)) :=
  Metric.sphere 0 1 ×ˢ Metric.sphere 0 1
private def generatorSet (m n : ℕ) : Set (CompositeMatrix m n) :=
  (fun p => productGenerator p.1 p.2) '' unitPairs m n
private def normalizedParameters (m n : ℕ) :
    Set ((Fin (arity m n) → ℝ) ×
      (Fin (arity m n) → EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n))) :=
  stdSimplex ℝ (Fin (arity m n)) ×ˢ
    Set.pi Set.univ (fun _ => unitPairs m n)
private def normalizedMap (p :
    (Fin (arity m n) → ℝ) ×
      (Fin (arity m n) → EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n))) :
    CompositeMatrix m n :=
  ∑ i, p.1 i • productGenerator (p.2 i).1 (p.2 i).2
private lemma isCompact_normalizedParameters :
    IsCompact (normalizedParameters m n) := by
  apply IsCompact.prod (isCompact_stdSimplex ℝ _)
  apply isCompact_univ_pi
  intro i
  exact (isCompact_sphere (0 : EuclideanSpace ℂ (Fin m)) 1).prod
    (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1)
private lemma continuous_normalizedMap : Continuous (normalizedMap (m := m) (n := n)) := by
  unfold normalizedMap
  apply continuous_finsetSum
  intro i hi
  exact ((continuous_apply i).comp continuous_fst).smul
    (continuous_productGenerator.comp ((continuous_apply i).comp continuous_snd))
private lemma isCompact_normalizedSlice :
    IsCompact (normalizedMap '' normalizedParameters m n) :=
  isCompact_normalizedParameters.image continuous_normalizedMap
private lemma normalizedSlice_eq_convexHull [Nonempty (Fin m)] [Nonempty (Fin n)] :
    normalizedMap '' normalizedParameters m n = convexHull ℝ (generatorSet m n) := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact mem_convexHull_of_exists_fintype p.1
      (fun i => productGenerator (p.2 i).1 (p.2 i).2)
      hp.1.1 hp.1.2
      (fun i => ⟨p.2 i, hp.2 i (Set.mem_univ i), rfl⟩) rfl
  · intro S hS
    rw [convexHull_eq_union] at hS
    simp only [Set.mem_iUnion] at hS
    obtain ⟨t, ht, hind, hSt⟩ := hS
    obtain ⟨w, hw_nonneg, hw_sum, hwS⟩ := Finset.mem_convexHull'.mp hSt
    have hcard : Fintype.card t ≤ arity m n := by
      exact (hind.card_le_finrank_succ).trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    obtain ⟨e : t ↪ Fin (arity m n)⟩ :=
      Function.Embedding.nonempty_of_card_le (α := t) (β := Fin (arity m n))
        (by simpa using hcard)
    choose z hz using fun i : t => ht i.property
    let w' : Fin (arity m n) → ℝ := Function.extend e (fun i : t => w i) 0
    let z' : Fin (arity m n) →
        EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n) :=
      Function.extend e z
        (fun _ =>
          (EuclideanSpace.single (Classical.arbitrary (Fin m)) (1 : ℂ),
            EuclideanSpace.single (Classical.arbitrary (Fin n)) (1 : ℂ)))
    refine ⟨(w', z'), ?_, ?_⟩
    · constructor
      · constructor
        · intro j
          by_cases hj : ∃ i, e i = j
          · obtain ⟨i, rfl⟩ := hj
            simpa [w', e.injective.extend_apply] using hw_nonneg i i.property
          · simp [w', Function.extend_apply' _ _ _ hj]
        · change (∑ j, Function.extend e (fun i : t => w i) 0 j) = 1
          rw [sum_extend_embedding e]
          simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hw_sum
      · intro j hj
        by_cases hj' : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := hj'
          simpa [z', e.injective.extend_apply] using (hz i).1
        · simp only [z', Function.extend_apply' _ _ _ hj']
          constructor <;> simp [Metric.mem_sphere, EuclideanSpace.norm_single]
    · unfold normalizedMap
      rw [show (fun i => w' i • productGenerator (z' i).1 (z' i).2) =
          Function.extend e
            (fun i : t => w i • productGenerator (z i).1 (z i).2) 0 by
        funext j
        by_cases hj : ∃ i, e i = j
        · obtain ⟨i, rfl⟩ := hj
          simp [w', z', e.injective.extend_apply]
        · simp [w', z', Function.extend_apply' _ _ _ hj]]
      rw [sum_extend_embedding e]
      calc
        ∑ i : t, w i • productGenerator (z i).1 (z i).2 =
            ∑ i : t, w i • (i : CompositeMatrix m n) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact congrArg (fun X => w i • X) (hz i).2
        _ = ∑ y ∈ t, w y • y := by
          exact Finset.sum_attach t (fun y => w y • y)
        _ = S := hwS
private def traceReal (S : CompositeMatrix m n) : ℝ :=
  RCLike.re (Matrix.trace S)
private lemma continuous_traceReal : Continuous (traceReal : CompositeMatrix m n → ℝ) := by
  unfold traceReal Matrix.trace
  fun_prop
private lemma traceReal_productGenerator (a : EuclideanSpace ℂ (Fin m))
    (b : EuclideanSpace ℂ (Fin n)) :
    traceReal (productGenerator a b) = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  rw [traceReal, productGenerator, Matrix.trace_kronecker, Matrix.trace_vecMulVec,
    Matrix.trace_vecMulVec]
  rw [← EuclideanSpace.inner_eq_star_dotProduct a a,
    ← EuclideanSpace.inner_eq_star_dotProduct b b, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]
  norm_cast
private lemma traceReal_normalizedMap {p :
    (Fin (arity m n) → ℝ) ×
      (Fin (arity m n) → EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin n))}
    (hp : p ∈ normalizedParameters m n) : traceReal (normalizedMap p) = 1 := by
  simp only [traceReal, normalizedMap, Matrix.trace_sum, Matrix.trace_smul, map_sum,
    Complex.real_smul]
  rw [show (fun i => RCLike.re ((p.1 i : ℂ) * Matrix.trace
      (productGenerator (p.2 i).1 (p.2 i).2))) = p.1 by
    funext i
    change Complex.re ((p.1 i : ℂ) * Matrix.trace
      (productGenerator (p.2 i).1 (p.2 i).2)) = p.1 i
    rw [Complex.re_ofReal_mul]
    have hgen := traceReal_productGenerator (p.2 i).1 (p.2 i).2
    change (Matrix.trace (productGenerator (p.2 i).1 (p.2 i).2)).re =
      ‖(p.2 i).1‖ ^ 2 * ‖(p.2 i).2‖ ^ 2 at hgen
    rw [hgen]
    have ha : ‖(p.2 i).1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using (hp.2 i (Set.mem_univ i)).1
    have hb : ‖(p.2 i).2‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using (hp.2 i (Set.mem_univ i)).2
    rw [ha, hb]
    norm_num]
  exact hp.1.2
private def unitize {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  letI := Classical.decEq ι
  if ‖a‖ = 0 then EuclideanSpace.single (Classical.arbitrary ι) 1 else ‖a‖⁻¹ • a
private lemma norm_unitize {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : EuclideanSpace ℂ ι) :
    ‖unitize a‖ = 1 := by
  unfold unitize
  letI := Classical.decEq ι
  split_ifs with ha
  · rw [EuclideanSpace.norm_single]
    norm_num
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ ha]
set_option maxRecDepth 100000 in
private lemma productGenerator_eq_smul_unitize [Nonempty (Fin m)] [Nonempty (Fin n)]
    (a : Fin m → ℂ) (b : Fin n → ℂ) :
    productGenerator (WithLp.toLp 2 a) (WithLp.toLp 2 b) =
      (‖WithLp.toLp 2 a‖ ^ 2 * ‖WithLp.toLp 2 b‖ ^ 2) •
        productGenerator (unitize (WithLp.toLp 2 a)) (unitize (WithLp.toLp 2 b)) := by
  let a' : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 a
  let b' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 b
  change productGenerator a' b' =
    (‖a'‖ ^ 2 * ‖b'‖ ^ 2) • productGenerator (unitize a') (unitize b')
  by_cases ha : ‖a'‖ = 0
  · have ha0 : a' = 0 := norm_eq_zero.mp ha
    simp [ha0, productGenerator]
  by_cases hb : ‖b'‖ = 0
  · have hb0 : b' = 0 := norm_eq_zero.mp hb
    simp [hb0, productGenerator]
  ext i j
  change a'.ofLp i.1 * star (a'.ofLp j.1) *
      (b'.ofLp i.2 * star (b'.ofLp j.2)) =
    ((‖a'‖ ^ 2 * ‖b'‖ ^ 2 : ℝ) : ℂ) *
      (((unitize a').ofLp i.1 * star ((unitize a').ofLp j.1)) *
        ((unitize b').ofLp i.2 * star ((unitize b').ofLp j.2)))
  simp only [unitize, ha, hb, if_false, WithLp.ofLp_smul, Pi.smul_apply]
  norm_num
  field_simp
private def radialCone (S : CompositeMatrix m n) : Prop :=
  ∃ r : ℝ, 0 ≤ r ∧ ∃ C ∈ normalizedMap '' normalizedParameters m n, S = r • C
private lemma radialCone_zero [Nonempty (Fin m)] [Nonempty (Fin n)] :
    radialCone (0 : CompositeMatrix m n) := by
  let a : EuclideanSpace ℂ (Fin m) := unitize 0
  let b : EuclideanSpace ℂ (Fin n) := unitize 0
  have hab : productGenerator a b ∈ generatorSet m n := by
    refine ⟨(a, b), ?_, rfl⟩
    constructor
    · simpa [Metric.mem_sphere, a] using norm_unitize (0 : EuclideanSpace ℂ (Fin m))
    · simpa [Metric.mem_sphere, b] using norm_unitize (0 : EuclideanSpace ℂ (Fin n))
  have hC : productGenerator a b ∈ normalizedMap '' normalizedParameters m n := by
    rw [normalizedSlice_eq_convexHull]
    exact subset_convexHull ℝ _ hab
  exact ⟨0, le_rfl, productGenerator a b, hC, by simp⟩
private lemma radialCone_add [Nonempty (Fin m)] [Nonempty (Fin n)]
    {S T : CompositeMatrix m n} (hS : radialCone S) (hT : radialCone T) :
    radialCone (S + T) := by
  obtain ⟨r, hr, C, hC, rfl⟩ := hS
  obtain ⟨s, hs, D, hD, rfl⟩ := hT
  by_cases hrs : r + s = 0
  · have hr0 : r = 0 := le_antisymm (by linarith) hr
    have hs0 : s = 0 := le_antisymm (by linarith) hs
    simpa [hr0, hs0] using (radialCone_zero (m := m) (n := n))
  · let E := (r / (r + s)) • C + (s / (r + s)) • D
    have hrs_pos : 0 < r + s := lt_of_le_of_ne (add_nonneg hr hs) (Ne.symm hrs)
    have hE : E ∈ normalizedMap '' normalizedParameters m n := by
      rw [normalizedSlice_eq_convexHull] at hC hD ⊢
      exact (convex_convexHull ℝ (generatorSet m n)) hC hD
        (div_nonneg hr hrs_pos.le) (div_nonneg hs hrs_pos.le) (by field_simp)
    refine ⟨r + s, hrs_pos.le, E, hE, ?_⟩
    dsimp [E]
    rw [smul_add, smul_smul, smul_smul]
    congr 1 <;> field_simp
private lemma radialCone_sum [Nonempty (Fin m)] [Nonempty (Fin n)]
    {ι : Type*} [Fintype ι] (f : ι → CompositeMatrix m n)
    (hf : ∀ i, radialCone (f i)) : radialCone (∑ i, f i) := by
  classical
  exact Finset.sum_induction f (fun S => radialCone S)
    (fun _ _ hA hB => radialCone_add hA hB)
    (radialCone_zero (m := m) (n := n)) (fun i _ => hf i)
private lemma separable_productGenerator (a : EuclideanSpace ℂ (Fin m))
    (b : EuclideanSpace ℂ (Fin n)) :
    separableCone (productGenerator a b) := by
  refine ⟨1, fun _ => Matrix.vecMulVec a.ofLp (star a.ofLp),
    fun _ => Matrix.vecMulVec b.ofLp (star b.ofLp), ?_, ?_⟩
  · intro i
    exact ⟨Matrix.posSemidef_vecMulVec_self_star a.ofLp,
      Matrix.posSemidef_vecMulVec_self_star b.ofLp⟩
  · simp [productGenerator]
private lemma separable_normalizedSlice [Nonempty (Fin m)] [Nonempty (Fin n)]
    {C : CompositeMatrix m n} (hC : C ∈ normalizedMap '' normalizedParameters m n) :
    separableCone C := by
  rw [normalizedSlice_eq_convexHull] at hC
  exact (convexHull_min
    (by rintro _ ⟨p, hp, rfl⟩; exact separable_productGenerator p.1 p.2)
    convex_separableCone) hC
private lemma radialCone_separable [Nonempty (Fin m)] [Nonempty (Fin n)]
    {S : CompositeMatrix m n} (hS : radialCone S) : separableCone S := by
  obtain ⟨r, hr, C, hC, rfl⟩ := hS
  exact separableCone_smul hr (separable_normalizedSlice hC)
private lemma radialCone_productGenerator [Nonempty (Fin m)] [Nonempty (Fin n)]
    (a : Fin m → ℂ) (b : Fin n → ℂ) :
    radialCone (productGenerator (WithLp.toLp 2 a) (WithLp.toLp 2 b)) := by
  let a' : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 a
  let b' : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 b
  let C := productGenerator (unitize a') (unitize b')
  have hCgen : C ∈ generatorSet m n := by
    exact ⟨(unitize a', unitize b'),
      ⟨by simpa [Metric.mem_sphere] using norm_unitize a',
        by simpa [Metric.mem_sphere] using norm_unitize b'⟩, rfl⟩
  have hC : C ∈ normalizedMap '' normalizedParameters m n := by
    rw [normalizedSlice_eq_convexHull]
    exact subset_convexHull ℝ _ hCgen
  exact ⟨‖a'‖ ^ 2 * ‖b'‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _), C, hC,
    productGenerator_eq_smul_unitize a b⟩
private lemma radialCone_kronecker {A : Matrix (Fin m) (Fin m) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} [Nonempty (Fin m)] [Nonempty (Fin n)]
    (hA : A.PosSemidef) (hB : B.PosSemidef) : radialCone (A ⊗ₖ B) := by
  obtain ⟨ka, a, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  obtain ⟨kb, b, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  rw [show (∑ i, Matrix.vecMulVec (a i) (star (a i))) ⊗ₖ
      (∑ j, Matrix.vecMulVec (b j) (star (b j))) =
      ∑ i, ∑ j, productGenerator (WithLp.toLp 2 (a i)) (WithLp.toLp 2 (b j)) by
    ext x y
    simp [productGenerator, Matrix.sum_apply, Matrix.kroneckerMap_apply,
      Finset.sum_mul_sum]]
  exact radialCone_sum _ (fun i => radialCone_sum _
    (fun j => radialCone_productGenerator (a i) (b j)))
private lemma separable_radialCone [Nonempty (Fin m)] [Nonempty (Fin n)]
    {S : CompositeMatrix m n} (hS : separableCone S) : radialCone S := by
  obtain ⟨k, A, B, hAB, rfl⟩ := hS
  exact radialCone_sum _ (fun i => radialCone_kronecker (hAB i).1 (hAB i).2)
private lemma separableCone_iff_radialCone [Nonempty (Fin m)] [Nonempty (Fin n)]
    (S : CompositeMatrix m n) : separableCone S ↔ radialCone S :=
  ⟨separable_radialCone, radialCone_separable⟩
private lemma isClosed_radialCone [Nonempty (Fin m)] [Nonempty (Fin n)] :
    IsClosed {S : CompositeMatrix m n | radialCone S} := by
  letI : FirstCountableTopology (CompositeMatrix m n) := by
    change FirstCountableTopology
      ((Fin m × Fin n) → (Fin m × Fin n) → ℂ)
    infer_instance
  rw [← isSeqClosed_iff_isClosed]
  intro u S hu hlim
  choose r hr C hC hu_eq using fun k => hu k
  have hr_eq (k : ℕ) : r k = traceReal (u k) := by
    rw [hu_eq k]
    obtain ⟨p, hp, hpC⟩ := hC k
    rw [← hpC]
    have htrace := traceReal_normalizedMap hp
    change (Matrix.trace (normalizedMap p)).re = 1 at htrace
    change r k = (Matrix.trace (r k • normalizedMap p)).re
    rw [Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul, htrace, mul_one]
  obtain ⟨C₀, hC₀, φ, hφ, hClim⟩ :=
    isCompact_normalizedSlice.tendsto_subseq hC
  have hrlim : Filter.Tendsto (r ∘ φ) Filter.atTop (nhds (traceReal S)) := by
    have htrace := (continuous_traceReal.tendsto S).comp hlim
    have htrace_sub := htrace.comp hφ.tendsto_atTop
    have hfun : r ∘ φ = (traceReal ∘ u) ∘ φ := by
      funext k
      exact hr_eq (φ k)
    rw [hfun]
    exact htrace_sub
  have hsmul : Filter.Tendsto (fun k => r (φ k) • C (φ k)) Filter.atTop
      (nhds (traceReal S • C₀)) := hrlim.smul hClim
  have husub : Filter.Tendsto (u ∘ φ) Filter.atTop (nhds S) :=
    hlim.comp hφ.tendsto_atTop
  have hSC : S = traceReal S • C₀ := by
    apply tendsto_nhds_unique husub
    have hfun : u ∘ φ = fun k => r (φ k) • C (φ k) := by
      funext k
      exact hu_eq (φ k)
    rw [hfun]
    exact hsmul
  have hrS : 0 ≤ traceReal S := by
    exact isClosed_Ici.mem_of_tendsto hrlim (Filter.Eventually.of_forall fun k => hr (φ k))
  exact ⟨traceReal S, hrS, C₀, hC₀, hSC⟩
/-- The cone of finite sums of Kronecker products of positive semidefinite
matrices is closed in the finite-dimensional real topology. -/
theorem isClosed_separableCone :
    IsClosed {S : CompositeMatrix m n | separableCone S} := by
  cases isEmpty_or_nonempty (Fin m) with
  | inl hm =>
      have hzero (S : CompositeMatrix m n) : S = 0 := by
        ext i j
        exact isEmptyElim i.1
      rw [show {S : CompositeMatrix m n | separableCone S} = Set.univ by
        ext S
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rw [hzero S]
        exact separableCone_zero]
      exact isClosed_univ
  | inr hm =>
      cases isEmpty_or_nonempty (Fin n) with
      | inl hn =>
          have hzero (S : CompositeMatrix m n) : S = 0 := by
            ext i j
            exact isEmptyElim i.2
          rw [show {S : CompositeMatrix m n | separableCone S} = Set.univ by
            ext S
            simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
            rw [hzero S]
            exact separableCone_zero]
          exact isClosed_univ
      | inr hn =>
          simpa only [separableCone_iff_radialCone] using
            (isClosed_radialCone (m := m) (n := n))
end
end D5.S3.Resource.SeparableConeClosed
