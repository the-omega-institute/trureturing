/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiCurrentVacuum
   generality: I
   mirror-B: none(source-only-candidate)
   mirror-E: none(source-only-candidate)
   anchors: []
   utility: Finite Jacobi nonvanishing and one-step-image rank descent.
   status: UNCOMPILED source candidate.

The coefficient proof follows the sealed finite-coefficient paper 8cae98a5,
with the rank-descent argument attributed there to Dong--Li--Mason Lemma 3.15.
All source products are computed on the original carrier. The ambient module
has no dimension or grading premise. A(u) consists of ONE-STEP current images.
-/
import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentNilpotence
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Modules.FullJacobiCurrentVacuum
open FullJacobiCurrentTransport FullJacobiCurrentNilpotence
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section
universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The full mixed Jacobi specialization p,r=q-1,t=-p-1 is a q-term identity. -/
theorem exponential_finite_witness (J : FullJacobiLatticeModule D M)
    (α : Charge D) (q : ℕ) (hq : bilinear D α α = (q : ℤ)) (hqpos : 0 < q)
    (v : M) (p : ℤ)
    (hp : ∀ j : ℕ, mode J (exponentialState (-α)) (p + j) v = 0) :
    LatticeGeneratingFieldLocality.epsilon D (-α) α • v =
      ∑ j ∈ Finset.range q,
        ((-1 : ℂ)^j * integerBinomial ((q : ℤ) - 1) j) •
          mode J (exponentialState (-α)) (p + q - 1 - j)
            (mode J (exponentialState α) (-p - 1 + j) v) := by
  classical
  obtain ⟨hL, hF, hS, h⟩ := J.borcherds (exponentialState (-α))
    (exponentialState α) v p (-p - 1) ((q : ℤ) - 1)
  have left : (∑ᶠ j : ℕ, jacobiLeft J.stateField (exponentialState (-α))
      (exponentialState α) v p (-p - 1) ((q : ℤ) - 1) j) =
      LatticeGeneratingFieldLocality.epsilon D (-α) α • v := by
    rw [finsum_eq_single _ 0]
    · simp only [jacobiLeft, Nat.cast_zero, add_zero, sub_zero,
        ← hq, source_opposite_leading, integerBinomial, Ring.choose_zero_right,
        Int.cast_one, one_smul]
      simp [mode, J.vacuum_field, FieldNormalProduct.identityField,
        VertexOperator.ncoeff_of_coeff, show p + (-p - 1) = -1 by omega]
    · intro j hj
      simp [jacobiLeft, ← hq, source_opposite_higher α j (Nat.pos_of_ne_zero hj), mode]
  have second : ∀ j : ℕ, jacobiSecond J.stateField (exponentialState (-α))
      (exponentialState α) v p (-p - 1) ((q : ℤ) - 1) j = 0 := by
    intro j
    simp only [jacobiSecond, mode, hp, map_zero, smul_zero]
  simp_rw [smul_sub] at h
  change _ = ∑ᶠ j : ℕ,
    (jacobiFirst J.stateField (exponentialState (-α)) (exponentialState α)
      v p (-p - 1) ((q : ℤ) - 1) j -
     jacobiSecond J.stateField (exponentialState (-α)) (exponentialState α)
      v p (-p - 1) ((q : ℤ) - 1) j) at h
  rw [left, finsum_sub_distrib hF hS] at h
  simp only [second, finsum_zero, sub_zero] at h
  rw [h, finsum_eq_sum_of_support_subset _ (show Function.support
      (jacobiFirst J.stateField (exponentialState (-α)) (exponentialState α)
        v p (-p - 1) ((q : ℤ) - 1)) ⊆ Finset.range q from by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra hjq
    have hc : integerBinomial ((q : ℤ) - 1) j = 0 := by
      rw [show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega]
      simp [integerBinomial, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (show q - 1 < j by omega)]
    exact hj (by simp [jacobiFirst, hc]))]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [jacobiFirst, mode]
  rw [show p + ((q : ℤ) - 1) - j = p + q - 1 - j by omega]

/-- A nonzero vector has a nonzero charged coefficient in the specified finite interval. -/
theorem exists_exponential_mode (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (α : Charge D) (hα : α ≠ 0) (v : M) (hv : v ≠ 0) :
    ∃ p : ℤ, 0 ≤ p ∧ ∃ j ∈ Finset.range (bilinear D α α).toNat,
      mode J (exponentialState α) (-p - 1 + j) v ≠ 0 := by
  classical
  obtain ⟨P, hP⟩ := module_truncation J (exponentialState (-α)) v
  let p : ℤ := max 0 P
  have hp : ∀ j : ℕ, mode J (exponentialState (-α)) (p + j) v = 0 := by
    intro j
    apply hP
    dsimp [p]
    omega
  have hpositive := norm_positive D hD α hα
  have hq : bilinear D α α = ((bilinear D α α).toNat : ℤ) :=
    (Int.toNat_of_nonneg hpositive.le).symm
  have hqn : 0 < (bilinear D α α).toNat := by omega
  refine ⟨p, le_max_left _ _, ?_⟩
  by_contra hnone
  push_neg at hnone
  have h := exponential_finite_witness J α _ hq hqn v p hp
  have hz : LatticeGeneratingFieldLocality.epsilon D (-α) α • v = 0 := by
    rw [h]
    apply Finset.sum_eq_zero
    intro j hj
    simp [hnone j hj]
  have he : LatticeGeneratingFieldLocality.epsilon D (-α) α ≠ 0 := by
    unfold LatticeGeneratingFieldLocality.epsilon paritySign
    split_ifs <;> norm_num
  exact (smul_ne_zero he hv) hz

/-- The highest nonzero charged mode is the maximum of a finite integer interval. -/
theorem exists_highest_exponential_mode (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (α : Charge D) (hα : α ≠ 0) (v : M) (hv : v ≠ 0) :
    ∃ r : ℤ, mode J (exponentialState α) r v ≠ 0 ∧
      ∀ s : ℤ, r < s → mode J (exponentialState α) s v = 0 := by
  classical
  obtain ⟨p, hp, j, hj, hnonzero⟩ := exists_exponential_mode J hD α hα v hv
  obtain ⟨R, hR⟩ := module_truncation J (exponentialState α) v
  let a : ℤ := -p - 1 + j
  have ha : a < R := by
    by_contra h
    exact hnonzero (hR a (by omega))
  let S : Finset ℤ := (Finset.Icc a (R - 1)).filter
    (fun s => mode J (exponentialState α) s v ≠ 0)
  have haS : a ∈ S := by simp [S, ha.le, show a ≤ R - 1 by omega, hnonzero, a]
  obtain ⟨r, hr, hmax⟩ := S.exists_max_image id ⟨a, haS⟩
  have hrlo : a ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
  refine ⟨r, (Finset.mem_filter.mp hr).2, ?_⟩
  intro s hs
  by_cases hsR : R ≤ s
  · exact hR s hsR
  · by_contra hn
    have hsS : s ∈ S := by simp [S, hn, show a ≤ s by omega, show s ≤ R - 1 by omega]
    have := hmax s hsS
    dsimp only [id] at this
    omega

/-- Literal one-step positive-current image span. It has no invariance assertion. -/
def positiveImageSpan (J : FullJacobiLatticeModule D M) (v : M) : Submodule ℂ M :=
  Submodule.span ℂ (Set.range (fun x : Fin D.rank × ℕ =>
    current J x.1 ((x.2 : ℤ) + 1) v))

/-- Finite rank comes from the original field cutoffs and finite source rank. -/
theorem positive_images_finite (J : FullJacobiLatticeModule D M) (v : M) :
    (Set.range (fun x : Fin D.rank × ℕ => current J x.1 ((x.2 : ℤ) + 1) v)).Finite := by
  classical
  let f := fun x : Fin D.rank × ℕ => current J x.1 ((x.2 : ℤ) + 1) v
  let B : Finset (Fin D.rank × ℕ) := Finset.univ ×ˢ Finset.range (activeBound J v)
  apply (((B.finite_toSet).image f).insert 0).subset
  rintro y ⟨⟨i,k⟩, rfl⟩
  by_cases hk : k < activeBound J v
  · exact Set.mem_insert_of_mem _ ⟨(i,k), by simp [B, hk], rfl⟩
  · left
    apply current_vanish_above_cutoff
    exact (Finset.le_sup (f := fun h => currentCutoff J h v) (Finset.mem_univ i)).trans
      (show activeBound J v ≤ k by omega)

instance positiveImageSpan_finite (J : FullJacobiLatticeModule D M) (v : M) :
    FiniteDimensional ℂ (positiveImageSpan J v) :=
  FiniteDimensional.span_of_finite ℂ (positive_images_finite J v)

theorem positive_image_mem (J : FullJacobiLatticeModule D M)
    (v : M) (i : Fin D.rank) (n : ℤ) (hn : 0 < n) :
    current J i n v ∈ positiveImageSpan J v := by
  have he : ((n - 1).toNat : ℤ) + 1 = n := by omega
  rw [← he]
  exact Submodule.subset_span ⟨(i, (n - 1).toNat), rfl⟩

/-- Maximal active frequency is selected from the finite original-current list. -/
theorem exists_maximal_active_current (J : FullJacobiLatticeModule D M)
    (v : M) (hv : positiveImageSpan J v ≠ ⊥) :
    ∃ i : Fin D.rank, ∃ k : ℕ, 0 < k ∧ current J i k v ≠ 0 ∧
      ∀ (h : Fin D.rank) (n : ℤ), (k : ℤ) < n → current J h n v = 0 := by
  classical
  have hsome : ∃ x : Fin D.rank × ℕ, current J x.1 ((x.2 : ℤ) + 1) v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro y ⟨x, rfl⟩
    simpa using h x
  let B := (Finset.univ ×ˢ Finset.range (activeBound J v)).filter
    (fun x : Fin D.rank × ℕ => current J x.1 ((x.2 : ℤ) + 1) v ≠ 0)
  have hB : B.Nonempty := by
    obtain ⟨x, hx⟩ := hsome
    have hlt : x.2 < activeBound J v := by
      by_contra h
      exact hx (current_vanish_above_cutoff J x.1 v x.2
        ((Finset.le_sup (f := fun h => currentCutoff J h v) (Finset.mem_univ x.1)).trans
          (show activeBound J v ≤ x.2 by omega)))
    exact ⟨x, by simp [B, hlt, hx]⟩
  obtain ⟨x, hx, hmax⟩ := B.exists_max_image (fun y => y.2) hB
  refine ⟨x.1, x.2 + 1, Nat.succ_pos _, ?_, ?_⟩
  · simpa using (Finset.mem_filter.mp hx).2
  · intro h n hn
    let t := (n - 1).toNat
    have ht : (t : ℤ) + 1 = n := by dsimp [t]; omega
    by_cases htB : activeBound J v ≤ t
    · rw [← ht]
      exact current_vanish_above_cutoff J h v t
        ((Finset.le_sup (f := fun h => currentCutoff J h v) (Finset.mem_univ h)).trans htB)
    · by_contra hne
      have hm : (h,t) ∈ B := by simp [B, ht, hne, show t < activeBound J v by omega]
      have := hmax (h,t) hm
      simp only [Nat.cast_add, Nat.cast_one] at hn
      omega

private theorem minus_one_weight (j : ℕ) :
    (-1 : ℂ)^j * integerBinomial (-1) j = 1 := by
  exact LatticeActualStateFieldCalculus.minus_one_binomial j

/-- Translation and BOTH finite normal-product halves kill the specified kernel vector.
The j=0 summand is removed by the mixed commutator, just like 0<j<k. -/
theorem highest_exponential_kills_maximal_image (J : FullJacobiLatticeModule D M)
    (v : M) (i : Fin D.rank) (k : ℕ) (hk : 0 < k)
    (hlarge : ∀ (h : Fin D.rank) (n : ℤ), (k : ℤ) < n → current J h n v = 0)
    (r : ℤ) (htop : ∀ s : ℤ, r < s →
      mode J (exponentialState (unitCharge D i)) s v = 0) :
    mode J (exponentialState (unitCharge D i)) r (current J i k v) = 0 := by
  classical
  let e := exponentialState (unitCharge D i)
  let s : ℤ := r + k + 1
  obtain ⟨hF, hS, h⟩ := module_iterate J (currentState D i) e v (-1) s
  have hleft : mode J (sourceProduct D (currentState D i) (-1) e) s v = 0 := by
    rw [← source_unit_exponential_translation, module_translation_modes]
    rw [LinearMap.smul_apply, htop (s - 1) (by dsimp [s]; omega), smul_zero]
  have hfirst : ∀ j : ℕ,
      jacobiFirst J.stateField (currentState D i) e v 0 s (-1) j = 0 := by
    intro j
    simp only [jacobiFirst, zero_add, mode]
    rw [htop (s + j) (by dsimp [s]; omega), map_zero, smul_zero]
  have hsmall (j : ℕ) (hj : j < k) :
      mode J e (s - 1 - j) (current J i j v) = 0 := by
    have hc := current_exponential_apply J i (unitCharge D i) j (s - 1 - j) v
    have h1 : mode J e (s - 1 - j) v = 0 := htop _ (by dsimp [s]; omega)
    have h2 : mode J e ((j : ℤ) + (s - 1 - j)) v = 0 :=
      htop _ (by dsimp [s]; omega)
    change current J i j (mode J e (s - 1 - j) v) =
      mode J e (s - 1 - j) (current J i j v) +
        (bilinear D (unitCharge D i) (unitCharge D i) : ℂ) •
          mode J e ((j : ℤ) + (s - 1 - j)) v at hc
    simpa only [h1, h2, map_zero, smul_zero, add_zero] using hc.symm
  have hsecond : ∀ j : ℕ, j ≠ k →
      jacobiSecond J.stateField (currentState D i) e v 0 s (-1) j = 0 := by
    intro j hj
    have hkill : mode J e (s - 1 - j) (current J i j v) = 0 := by
      by_cases hj0 : j = 0
      · subst j
        exact hsmall 0 hk
      · rcases lt_or_gt_of_ne hj with hjk | hkj
        · exact hsmall j hjk
        · rw [hlarge i j (by exact_mod_cast hkj), map_zero]
    simp only [jacobiSecond, zero_add]
    rw [show s + -1 - (j : ℤ) = s - 1 - j by omega]
    change (((-1 : ℂ)^j) * integerBinomial (-1) j) •
      (StateFieldResidueReconstruction.epsilon (-1) •
        mode J e (s - 1 - j) (current J i j v)) = 0
    rw [hkill, smul_zero, smul_zero]
  have hsum : (∑ᶠ j : ℕ,
      jacobiSecond J.stateField (currentState D i) e v 0 s (-1) j) =
      -mode J e r (current J i k v) := by
    rw [finsum_eq_single _ k]
    · simp only [jacobiSecond, zero_add, mode, minus_one_weight, one_smul,
        show StateFieldResidueReconstruction.epsilon (-1) = -1 by
          norm_num [StateFieldResidueReconstruction.epsilon], neg_one_smul]
      rw [show s + -1 - (k : ℤ) = r by dsimp [s]; omega]
    · exact hsecond
  rw [hleft, hsum] at h
  simp only [hfirst, finsum_zero, zero_sub, neg_neg] at h
  exact h.symm

/-- Equality of actual one-image spans preserves all their linear relations. -/
theorem positiveImageSpan_highest_map (J : FullJacobiLatticeModule D M)
    (v : M) (α : Charge D) (r : ℤ)
    (htop : ∀ s : ℤ, r < s → mode J (exponentialState α) s v = 0) :
    positiveImageSpan J (mode J (exponentialState α) r v) =
      (positiveImageSpan J v).map (mode J (exponentialState α) r) := by
  have hf : (fun x : Fin D.rank × ℕ =>
      current J x.1 ((x.2 : ℤ) + 1) (mode J (exponentialState α) r v)) =
      (fun x : Fin D.rank × ℕ => mode J (exponentialState α) r
        (current J x.1 ((x.2 : ℤ) + 1) v)) := by
    funext x
    rw [current_exponential_apply,
      htop ((x.2 : ℤ) + 1 + r) (by omega), smul_zero, add_zero]
  rw [positiveImageSpan, hf, positiveImageSpan, Submodule.map_span]
  congr 1
  exact Set.range_comp (mode J (exponentialState α) r)
    (fun x : Fin D.rank × ℕ => current J x.1 ((x.2 : ℤ) + 1) v)

/-- The actual map has the specified nonzero current image in its kernel. -/
theorem positiveImageSpan_strict_descent (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (v : M) (hv : v ≠ 0) (hA : positiveImageSpan J v ≠ ⊥) :
    ∃ w : M, w ≠ 0 ∧
      Module.finrank ℂ (positiveImageSpan J w) <
        Module.finrank ℂ (positiveImageSpan J v) := by
  classical
  obtain ⟨i, k, hk, hnonzero, hlarge⟩ := exists_maximal_active_current J v hA
  have hi : unitCharge D i ≠ 0 := by
    intro h
    have := congrFun h i
    simpa [unitCharge] using this
  obtain ⟨r, hr, htop⟩ := exists_highest_exponential_mode J hD (unitCharge D i) hi v hv
  let E := mode J (exponentialState (unitCharge D i)) r
  let f : positiveImageSpan J v →ₗ[ℂ] M := E.domRestrict (positiveImageSpan J v)
  let z : positiveImageSpan J v :=
    ⟨current J i k v, positive_image_mem J v i k (by exact_mod_cast hk)⟩
  have hz : z ≠ 0 := by
    intro h
    exact hnonzero (congrArg Subtype.val h)
  have hzker : z ∈ LinearMap.ker f := by
    exact highest_exponential_kills_maximal_image J v i k hk hlarge r htop
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    have : z = 0 := by simpa [h] using hzker
    exact hz this
  have hkerpos : 0 < Module.finrank ℂ (LinearMap.ker f) := by
    have := (Submodule.one_le_finrank_iff).mpr hker
    omega
  have hdim := f.finrank_range_add_finrank_ker
  have hmap := positiveImageSpan_highest_map J v (unitCharge D i) r htop
  have hrange : LinearMap.range f = positiveImageSpan J (E v) := by
    dsimp only [f]
    rw [LinearMap.range_domRestrict]
    exact hmap.symm
  refine ⟨E v, hr, ?_⟩
  rw [hrange] at hdim
  omega

/-- A genuine positive-current vacuum, obtained by strong finrank induction.
This theorem applies to each nonzero vector in any original full weak module. -/
theorem exists_positive_current_vacuum (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (v : M) (hv : v ≠ 0) :
    ∃ w : M, w ≠ 0 ∧ ∀ (i : Fin D.rank) (n : ℤ),
      0 < n → current J i n w = 0 := by
  classical
  have induction : ∀ d : ℕ, ∀ u : M, u ≠ 0 →
      Module.finrank ℂ (positiveImageSpan J u) = d →
      ∃ w : M, w ≠ 0 ∧ ∀ (i : Fin D.rank) (n : ℤ),
        0 < n → current J i n w = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u hu hd
      by_cases hA : positiveImageSpan J u = ⊥
      · refine ⟨u, hu, ?_⟩
        intro i n hn
        have hm := positive_image_mem J u i n hn
        simpa [hA] using hm
      · obtain ⟨w, hw, hlt⟩ := positiveImageSpan_strict_descent J hD u hu hA
        exact ih _ (by omega) w hw rfl
  exact induction _ v hv rfl

end
end D5.S3.VertexAlgebra.Modules.FullJacobiCurrentVacuum
