/- GID: D5/S3/Combinatorics/Lattices/CyclotomicTraceSum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/CyclotomicTraceSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual orthogonal sums of trace ideal lattices and their normalized degrees. -/

import D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume

/-! Orthogonal sums of standard Hermitian fractional ideals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Lattices.CyclotomicTraceSum

open Module NumberField NumberField.mixedEmbedding
open CyclotomicTraceCovolume
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

/-- The orthogonal sum ambient Euclidean space. -/
abbrev SumSpace := PiLp 2 (fun _ : ι => euclidean.mixedSpace K)

/-- The actual coordinatewise direct sum lattice. -/
def sumLattice (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (SumSpace K (ι := ι)) where
  carrier := {x | ∀ i, x i ∈ traceIdealLattice K (I i)}
  zero_mem' i := (traceIdealLattice K (I i)).zero_mem
  add_mem' hx hy i := (traceIdealLattice K (I i)).add_mem (hx i) (hy i)
  smul_mem' a x hx i := (traceIdealLattice K (I i)).smul_mem a (hx i)

private def sumEquiv (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (∀ i, traceIdealLattice K (I i)) ≃ₗ[ℤ] sumLattice K I where
  toFun x := ⟨WithLp.toLp 2 (fun i => (x i : euclidean.mixedSpace K)), fun i => (x i).property⟩
  invFun x i := ⟨(x : SumSpace K) i, x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def idealBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Fin (finrank ℚ K)) ℤ (traceIdealLattice K I) :=
  (Module.finBasis ℤ (traceIdealLattice K I)).reindex
    (finCongr ((ZLattice.rank ℝ (traceIdealLattice K I)).trans (euclidean.finrank K)))

private def sumBasis (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Fin (finrank ℚ K) × ι) ℤ (sumLattice K I) :=
  ((Pi.basis (fun i => idealBasis K (I i))).map (sumEquiv K I)).reindex
    ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))

instance (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Module.Free ℤ (sumLattice K I) :=
  Module.Free.of_basis (sumBasis K I)

instance (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Module.Finite ℤ (sumLattice K I) :=
  Module.Finite.of_basis (sumBasis K I)

instance (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : DiscreteTopology (sumLattice K I) := by
  apply DiscreteTopology.of_continuous_injective (f := (sumEquiv K I).symm)
  · exact continuous_pi (fun i => Continuous.subtype_mk
      ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val) _)
  · exact (sumEquiv K I).symm.injective

private theorem sumBasis_coe (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (j : Fin (finrank ℚ K)) (i : ι) :
    (sumBasis K I (j, i) : SumSpace K) =
      PiLp.single 2 i (idealBasis K (I i) j : euclidean.mixedSpace K) := by
  have he (x : ∀ k, traceIdealLattice K (I k)) :
      ((sumEquiv K I) x : SumSpace K (ι := ι)) =
        WithLp.toLp 2 (fun k => (x k : euclidean.mixedSpace K)) := rfl
  simp only [sumBasis, Basis.reindex_apply, Basis.map_apply, he]
  simp only [Equiv.symm_trans_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply]
  ext k
  by_cases h : k = i
  · subst k
    simp
  · simp [h]

private theorem sum_gram (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Matrix.gram ℝ (fun j : Fin (finrank ℚ K) × ι =>
      (sumBasis K I j : SumSpace K (ι := ι))) =
      Matrix.blockDiagonal (fun i =>
        Matrix.gram ℝ (fun j => (idealBasis K (I i) j : euclidean.mixedSpace K))) := by
  ext ⟨j, i⟩ ⟨l, k⟩
  simp only [Matrix.gram_apply, sumBasis_coe, PiLp.inner_apply,
    PiLp.single_apply, Matrix.blockDiagonal_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = k
    · subst k
      simp
    · simp [h]
  · intro t _ hti
    simp [hti]
  · simp

private theorem sum_covolume (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    EuclideanHarderNarasimhan.covolume (sumLattice K I) =
      ∏ i, EuclideanHarderNarasimhan.covolume (traceIdealLattice K (I i)) := by
  rw [EuclideanHarderNarasimhan.covolume_eq_gram _ (sumBasis K I), sum_gram,
    Matrix.det_blockDiagonal, Real.sqrt_prod Finset.univ]
  · exact Finset.prod_congr rfl (fun i _ =>
      (EuclideanHarderNarasimhan.covolume_eq_gram _ (idealBasis K (I i))).symm)
  · intro i _
    exact (Matrix.posSemidef_gram ℝ _).det_nonneg

private theorem sum_formula (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    EuclideanHarderNarasimhan.covolume (sumLattice K I) =
      (Real.sqrt |(discr K : ℝ)|) ^ Fintype.card ι *
        Real.exp (-(∑ i, idealDegree K (I i))) := by
  rw [sum_covolume]
  simp_rw [(fun i => (trace_ideal_formula K (I i)).2.2.2)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  have hI : 0 < (FractionalIdeal.absNorm (I i).val : ℝ) := by
    have hne : FractionalIdeal.absNorm (I i).val ≠ 0 :=
      mt FractionalIdeal.absNorm_eq_zero_iff.mp (Units.ne_zero (I i))
    exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm hne)
  simp [idealDegree, Real.exp_log hI]

private theorem sum_slope (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hn : Fintype.card ι ≠ 0) :
    -Real.log (EuclideanHarderNarasimhan.covolume (sumLattice K I)) /
        (finrank ℚ K * Fintype.card ι : ℕ) =
      (∑ i, idealDegree K (I i)) / (finrank ℚ K * Fintype.card ι : ℕ) -
        discriminantShift K := by
  have hd : (finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn
  have hD : 0 < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  rw [sum_formula, Real.log_mul (pow_ne_zero _ (Real.sqrt_pos.mpr hD).ne')
    (Real.exp_ne_zero _), Real.log_pow, Real.log_sqrt hD.le, Real.log_exp]
  unfold discriminantShift
  push_cast
  field_simp [hd, hn']
  ring

/-- Orthogonal ideal sums have multiplicative covolumes and the same discriminant slope shift. -/
theorem trace_sum_formula (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    EuclideanHarderNarasimhan.covolume (sumLattice K I) =
      ∏ i, EuclideanHarderNarasimhan.covolume (traceIdealLattice K (I i)) ∧
    EuclideanHarderNarasimhan.covolume (sumLattice K I) =
      (Real.sqrt |(discr K : ℝ)|) ^ Fintype.card ι *
        Real.exp (-(∑ i, idealDegree K (I i))) ∧
    Module.finrank ℤ (sumLattice K I) = finrank ℚ K * Fintype.card ι ∧
    (Fintype.card ι ≠ 0 →
      -Real.log (EuclideanHarderNarasimhan.covolume (sumLattice K I)) /
          (finrank ℚ K * Fintype.card ι : ℕ) =
        (∑ i, idealDegree K (I i)) / (finrank ℚ K * Fintype.card ι : ℕ) -
          discriminantShift K) := by
  refine ⟨sum_covolume K I, sum_formula K I, ?_, sum_slope K I⟩
  rw [Module.finrank_eq_card_basis (sumBasis K I), Fintype.card_prod, Fintype.card_fin]

section Orthogonal

open Module NumberField NumberField.mixedEmbedding
open HarderNarasimhan EuclideanSublattices EuclideanHarderNarasimhan
open EuclideanSlopeMorphism CyclotomicTraceCovolume CyclotomicTraceSum
open EuclideanCommonLattice (bot_carrier)
open scoped Classical nonZeroDivisors

private theorem total_slope {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    (slopeData L).slope ⊥ ⊤ = -Real.log (covolume L) / finrank ℤ L := by
  have hb : ((slopeData L).rank ⊥ : ℝ) = 0 := by
    change (finrank ℤ (⊥ : Sublattice L).val : ℝ) = 0
    rw [EuclideanSublattices.integral_rank_eq L _]
    change (finrank ℝ (Submodule.span ℝ (integral L ⊥ : Set E)) : ℝ) = 0
    rw [bot_carrier]
    simp
  have ht : ((slopeData L).rank ⊤ : ℝ) = finrank ℤ L := by
    change (finrank ℤ (⊤ : Submodule ℤ L) : ℝ) = _
    simp
  unfold SlopeData.slope
  change (-Real.log (covolume (integral L ⊤)) - -Real.log (covolume (integral L ⊥))) /
    (((slopeData L).rank ⊤ : ℝ) - (slopeData L).rank ⊥) = _
  have hv : covolume (⊥ : Submodule ℤ E) = 1 := by
    rw [covolume_eq_gram _ (Module.Basis.empty _ : Module.Basis Empty ℤ _)]
    simp
  simp only [hb, ht, integral_top, bot_carrier, hv, Real.log_one, neg_zero, sub_zero]

private theorem first_nonzero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) (F : Sublattice L) (hF : ⊥ < F) :
    ∃ x ∈ integral L F, x ≠ 0 := by
  apply (integral L F).ne_bot_iff.mp
  intro h
  have hb : F = ⊥ := by
    apply Subtype.ext
    apply Submodule.map_injective_of_injective L.subtype_injective
    change integral L F = integral L ⊥
    rw [h, bot_carrier]
  exact hF.ne' hb

variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

private theorem projection_bound (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : ∀ i, (slopeData (traceIdealLattice K (I i))).Semistable ⊥ ⊤)
    (F : Sublattice (sumLattice K I)) (l : List (Sublattice (sumLattice K I)))
    (hF : (slopeData (sumLattice K I)).Filtration ⊥ ⊤ (F :: l)) :
    ∃ i, (slopeData (sumLattice K I)).slope ⊥ F ≤
      -Real.log (covolume (traceIdealLattice K (I i))) /
        finrank ℤ (traceIdealLattice K (I i)) := by
  let N := sumLattice K I
  let D := slopeData N
  have hs : D.Semistable ⊥ F := by
    generalize ha : (⊥ : Sublattice N) = a at hF ⊢
    generalize hb : (⊤ : Sublattice N) = b at hF
    cases hF with | cons hs _ _ _ => exact hs
  obtain ⟨x, hx, hx0⟩ := first_nonzero N F hs.1
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    ext i
    exact h i
  let C := traceIdealLattice K (I i)
  let p : SumSpace K (ι := ι) →L[ℝ] euclidean.mixedSpace K := PiLp.proj 2 _ i
  have hpC : ∀ y ∈ integral N F, p y ∈ C := by
    intro y hy
    exact (integral_le N F hy) i
  have hzero : Submodule.span ℝ (integral C ⊥ : Set (euclidean.mixedSpace K)) = ⊥ := by
    rw [bot_carrier]
    simp
  have hp0 : ∃ y ∈ integral N F,
      p y ∉ Submodule.span ℝ (integral C ⊥ : Set (euclidean.mixedSpace K)) := by
    refine ⟨x, hx, ?_⟩
    rw [hzero]
    exact hi
  have hp : ∀ y ∈ Submodule.span ℝ (integral N F : Set (SumSpace K)),
      ‖(Submodule.span ℝ (integral C ⊥ : Set (euclidean.mixedSpace K)))ᗮ.starProjection
        (p y)‖ ≤ Real.exp 0 * ‖y‖ := by
    intro y _
    simpa [hzero, Submodule.starProjection_top, p] using PiLp.norm_apply_le y i
  have hm := slope_morphism N C F ⊥ p 0 hpC hp0 hp
  have hsource : D.Filtration ⊥ F [F] := .cons hs le_rfl (.nil F) trivial
  have htarget : (slopeData C).Filtration ⊥ ⊤ [⊤] :=
    .cons (hI i) le_rfl (.nil ⊤) trivial
  have hmin := (filtration_extremes D ⊥ F F [] hsource).2.2.2.2.2.1
  have hmax := (filtration_extremes (slopeData C) ⊥ ⊤ ⊤ [] htarget).2.2.2.2.1
  simp only [lastLower] at hmin
  rw [hmin, hmax, add_zero, total_slope C] at hm
  exact ⟨i, hm⟩

/-- A nonempty orthogonal sum of equally sloped standard cyclotomic ideals is
semistable, with a unique single-factor HN chain and the exact
discriminant-normalized slope. -/
theorem equal_degree_sum_hn {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hcard : Fintype.card ι ≠ 0) (a : ℝ) (hdegree : ∀ i, idealDegree K (I i) = a) :
    let N := sumLattice K I
    (slopeData N).Semistable ⊥ ⊤ ∧
      (∀ l : List (Sublattice N), (slopeData N).Filtration ⊥ ⊤ l ↔ l = [⊤]) ∧
      -Real.log (covolume N) / finrank ℤ N = a / finrank ℚ K - discriminantShift K := by
  dsimp only
  let N := sumLattice K I
  have hmean : -Real.log (covolume N) / finrank ℤ N =
      a / finrank ℚ K - discriminantShift K := by
    rw [(trace_sum_formula K I).2.2.1, (trace_sum_formula K I).2.2.2 hcard]
    simp_rw [hdegree]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hcard
    have hd : (finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
    field_simp [hc, hd]
    <;> ring
  have hnontriv : (⊥ : Sublattice N) ≠ ⊤ := by
    intro h
    have he : N = ⊥ := by rw [← integral_top N, ← h, bot_carrier]
    have hr := (trace_sum_formula K I).2.2.1
    change finrank ℤ N = _ at hr
    rw [he, finrank_bot] at hr
    have hd := (Module.finrank_pos (R := ℚ) (M := K)).ne'
    exact (Nat.mul_ne_zero hd hcard) hr.symm
  obtain ⟨l, hl, _⟩ := ((euclidean_hn N ⊥ ⊤).2.1).mpr bot_le
  have hsem : (slopeData N).Semistable ⊥ ⊤ := by
    cases l with
    | nil =>
      generalize ha : (⊥ : Sublattice N) = a at hl hnontriv
      generalize hb : (⊤ : Sublattice N) = b at hl hnontriv
      cases hl
      exact (hnontriv rfl).elim
    | cons F l =>
      obtain ⟨i, hi⟩ := projection_bound K I
        (fun i => (cyclotomic_ideal_hn K (n := n) (I i)).1) F l hl
      have hid := (cyclotomic_ideal_hn K (n := n) (I i)).2.2
      rw [hdegree] at hid
      have hmax := (filtration_extremes (slopeData N) ⊥ ⊤ F l hl).2.2.1
      have hbound : (slopeData N).slope ⊥ F ≤ (slopeData N).slope ⊥ ⊤ := by
        rw [total_slope N, hmean]
        exact hi.trans_eq hid
      refine ⟨bot_lt_iff_ne_bot.mpr hnontriv.symm, fun X hX hXt => ?_⟩
      exact (hmax.2 ⟨X, hX, hXt, rfl⟩).trans hbound
  have hsingle : (slopeData N).Filtration ⊥ ⊤ [⊤] :=
    .cons hsem le_rfl (.nil ⊤) trivial
  refine ⟨hsem, fun l => ⟨fun hl => ?_, ?_⟩, hmean⟩
  · obtain ⟨_, _, hu⟩ := ((euclidean_hn N ⊥ ⊤).2.1).mpr bot_le
    exact (hu l hl).trans (hu [⊤] hsingle).symm
  · rintro rfl
    exact hsingle

end Orthogonal

end D5.S3.Combinatorics.Lattices.CyclotomicTraceSum
