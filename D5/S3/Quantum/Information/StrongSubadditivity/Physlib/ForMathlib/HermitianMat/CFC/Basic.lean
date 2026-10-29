/- GID: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/ForMathlib/HermitianMat/CFC/Basic
   generality: G
   mirror-B: none(waiver:upstream-proof-closure)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Physlib strong-subadditivity proof closure. -/

/- Adapted from leanprover-community/physlib, revision
2725b6f621901d4cd330869e9b77105045c1582e, QuantumInfo/ForMathlib/HermitianMat/CFC.lean.
Changes: D5 import paths, bounded modules, and local supplier elaboration options.
Retire this port when the receiving pinned Mathlib provides the equivalent declarations.
Apache-2.0 license text is included in the sibling ForMathlib/Misc.lean. -/
/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Inner
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.NonSingular
public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Topology.TietzeExtension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Matrix operations on HermitianMats with the CFC -/

@[expose] public section

set_option relaxedAutoImplicit true
namespace HermitianMat

noncomputable section CFC

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]
variable {X : Type*} [TopologicalSpace X]
variable (A : HermitianMat d 𝕜) (f : ℝ → ℝ) (g : ℝ → ℝ) (q r : ℝ)

/- Adding this to the `CStarAlgebra` aesop set allows `cfc_tac` to use it. -/
omit [Fintype d] [DecidableEq d] in
@[aesop safe apply (rule_sets := [CStarAlgebra])]
lemma isSelfAdjoint : IsSelfAdjoint A.mat := by
  exact A.H

/- Adding this to `fun_prop` allows `cfc_cont_tac` to use it. -/
@[fun_prop]
lemma continuousOn_finite {α β : Type*} (f : α → β) (S : Set α)
    [TopologicalSpace α] [TopologicalSpace β] [T1Space α] [Finite S] : ContinuousOn f S := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_of_discreteTopology

@[simp]
lemma conjTranspose_cfc : (cfc f A.mat).conjTranspose = cfc f A.mat := by
  exact cfc_predicate f A.mat

protected def cfc : HermitianMat d 𝕜 :=
  ⟨cfc f A.mat, cfc_predicate _ _⟩

lemma cfc_eq : A.cfc f = ⟨cfc f A.mat, cfc_predicate f A.mat⟩ := by
  rfl

@[simp]
lemma mat_cfc : (A.cfc f).mat = _root_.cfc f A.mat := by
  rfl

section congr

variable {f g A}

lemma cfc_eq_cfc_iff_eqOn (f g : ℝ → ℝ) :
    A.cfc f = A.cfc g ↔ Set.EqOn f g (spectrum ℝ A.mat) := by
  rw [HermitianMat.ext_iff, mat_cfc, mat_cfc]
  exact _root_.cfc_eq_cfc_iff_eqOn A.H

nonrec lemma cfc_congr (hfg : Set.EqOn f g (spectrum ℝ A.mat)) :
    A.cfc f = A.cfc g := by
  ext1
  exact cfc_congr hfg

/-- Version of `cfc_congr` specialized to PSD matrices. -/
nonrec theorem cfc_congr_of_nonneg (hA : 0 ≤ A) (hfg : Set.EqOn f g (Set.Ici 0)) :
    A.cfc f = A.cfc g := by
  refine cfc_congr (hfg.mono ?_)
  open MatrixOrder in
  exact spectrum_nonneg_of_nonneg (a := A.mat) hA

open ComplexOrder in
/-- Version of `cfc_congr` specialized to positive definite matrices. -/
nonrec theorem cfc_congr_of_posDef (hA : A.mat.PosDef) (hfg : Set.EqOn f g (Set.Ioi 0)) :
    A.cfc f = A.cfc g := by
  refine cfc_congr (hfg.mono ?_)
  rw [A.H.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

end congr
section commute
variable {A B : HermitianMat d 𝕜}

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
lemma _root_.Commute.cfc_left (hAB : Commute A.mat B.mat) :
    Commute (A.cfc f).mat B.mat := by
  exact hAB.cfc_real f

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
lemma _root_.Commute.cfc_right (hAB : Commute A.mat B.mat) :
    Commute A.mat (B.cfc f).mat :=
  (hAB.symm.cfc_left f).symm

lemma cfc_commute (f g : ℝ → ℝ) (hAB : Commute A.mat B.mat) :
    Commute (A.cfc f).mat (B.cfc g).mat := by
  exact (hAB.cfc_right g).cfc_left f

@[aesop safe apply (rule_sets := [Commutes])]
lemma cfc_self_commute (A : HermitianMat d 𝕜) (f g : ℝ → ℝ) :
    Commute (A.cfc f).mat (A.cfc g).mat := by
  commutes

end commute

/-- Reindexing a matrix commutes with applying the CFC. -/
@[simp]
theorem cfc_reindex (e : d ≃ d₂) : (A.reindex e).cfc f = (A.cfc f).reindex e := by
  rw [HermitianMat.ext_iff]
  simp only [mat_cfc, mat_reindex]
  exact Matrix.cfc_reindex f e

lemma spectrum_cfc_eq_image (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    spectrum ℝ (A.cfc f).mat = f '' (spectrum ℝ A.mat) := by
  exact cfc_map_spectrum f A.mat

set_option backward.isDefEq.respectTransparency false in
/--
Spectral decomposition of `A.cfc f` as a sum of scaled projections (matrix version).
-/
theorem cfc_toMat_eq_sum_smul_proj : (A.cfc f).mat =
    ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
  rw [A.mat_cfc, A.H.cfc_eq, Matrix.IsHermitian.cfc]
  have h : ( Matrix.diagonal ( RCLike.ofReal ∘ f ∘ Matrix.IsHermitian.eigenvalues A.H ) : Matrix d d 𝕜 ) = ∑ i, f ( A.H.eigenvalues i ) • Matrix.single i i 1 := by
    ext i j ; by_cases hij : i = j <;> simp [ hij ];
    · simp [ Matrix.sum_apply, Matrix.single ];
      simp [ Algebra.smul_def ];
    · rw [Finset.sum_apply, Finset.sum_apply]
      simp_all
  rw [h]
  simp [Matrix.single, Matrix.mul_assoc]
  congr! 1
  ext j k
  simp [Matrix.mul_apply,Finset.mul_sum, Finset.smul_sum, smul_ite, smul_zero]

--Ensure we get this instance:
/-- info: locallyCompact_of_proper -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency false in
#synth LocallyCompactSpace (HermitianMat d 𝕜)

lemma cfc_eigenvalues (A : HermitianMat d 𝕜) :
    ∃ (e : d ≃ d), (A.cfc f).H.eigenvalues = f ∘ A.H.eigenvalues ∘ e :=
  A.H.cfc_eigenvalues f

/-! Here we give HermitianMat versions of many cfc theorems, like `cfc_id`, `cfc_sub`, `cfc_comp`,
etc. We need these because (as above) `HermitianMat.cfc` is different from `_root_.cfc`. -/

@[simp]
nonrec lemma cfc_id : A.cfc id = A := by
  simpa [HermitianMat.ext_iff] using cfc_id ℝ A.mat

@[simp]
nonrec lemma cfc_id' : A.cfc (·) = A :=
  cfc_id A

nonrec lemma cfc_add : A.cfc (f + g) = A.cfc f + A.cfc g := by
  ext1; exact cfc_add ..

lemma cfc_add_apply : A.cfc (fun x ↦ f x + g x) = A.cfc f + A.cfc g :=
  cfc_add A f g

nonrec lemma cfc_sub : A.cfc (f - g) = A.cfc f - A.cfc g := by
  ext1; exact cfc_sub ..

lemma cfc_sub_apply : A.cfc (fun x ↦ f x - g x) = A.cfc f - A.cfc g :=
  cfc_sub A f g

nonrec lemma cfc_neg : A.cfc (-f) = -A.cfc f := by
  ext1; exact cfc_neg ..

lemma cfc_neg_apply : A.cfc (fun x ↦ -f x) = -A.cfc f :=
  cfc_neg A f

/-- We don't have a direct analog of `cfc_mul`, since we can't generally multiply
to HermitianMat's to get another one, so the theorem statement wouldn't be well-typed.
But, we can say that the matrices are always equal. See `cfc_conj` for the coe-free
analog to multiplication. -/
theorem mat_cfc_mul : (A.cfc (f * g)).mat = A.cfc f * A.cfc g := by
  simp only [mat_cfc]
  exact cfc_mul ..

lemma mat_cfc_mul_apply : (A.cfc (fun x ↦ f x * g x)).mat = A.cfc f * A.cfc g := by
  exact mat_cfc_mul ..

nonrec lemma cfc_comp : A.cfc (g ∘ f) = (A.cfc f).cfc g := by
  ext1; exact cfc_comp ..

lemma cfc_comp_apply : A.cfc (fun x ↦ g (f x)) = (A.cfc f).cfc g :=
  cfc_comp A f g

nonrec lemma cfc_conj : (A.cfc f).conj (A.cfc g) = A.cfc (f * g^2) := by
  ext1
  simp only [conj_apply, mat_cfc, mat_mk, conjTranspose_cfc]
  rw [← cfc_mul, ← cfc_mul, Pi.mul_def, Pi.pow_def]
  grind only

@[simp]
lemma cfc_diagonal (g : d → ℝ) : (diagonal 𝕜 g).cfc f = diagonal 𝕜 (f ∘ g) := by
  ext1
  exact Matrix.cfc_diagonal g f

lemma cfc_conj_unitary (U : Matrix.unitaryGroup d 𝕜) :
    (A.conj U.val).cfc f = (A.cfc f).conj U := by
  ext1
  exact Matrix.cfc_conj_unitary f U

@[simp]
nonrec lemma cfc_const : (A.cfc (fun _ ↦ r)) = r • 1 := by
  ext1
  simp only [mat_cfc, mat_smul, mat_one]
  rw [cfc_const r A.mat]
  exact Algebra.algebraMap_eq_smul_one r

@[simp]
nonrec lemma cfc_const_mul_id : A.cfc (fun x ↦ r * x) = r • A := by
  ext1
  rw [mat_cfc, mat_smul, cfc_const_mul_id r A.mat]

@[simp]
nonrec lemma cfc_const_mul : A.cfc (fun x ↦ r * f x) = r • A.cfc f := by
  rw [← cfc_const_mul_id, ← cfc_comp]
  rfl

@[simp]
nonrec lemma cfc_apply_zero : (0 : HermitianMat d 𝕜).cfc f = f 0 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
nonrec lemma cfc_apply_one : (1 : HermitianMat d 𝕜).cfc f = f 1 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

lemma cfc_pow {n : ℕ} : A.cfc (· ^ n) = A ^ n := by
  ext1
  induction n
  · simp
  · simp_rw [pow_succ, mat_pow, mat_cfc_mul_apply, pow_succ, cfc_id']
    congr

set_option backward.isDefEq.respectTransparency false in
lemma cfc_nonneg_iff : 0 ≤ A.cfc f ↔ ∀ i, 0 ≤ f (A.H.eigenvalues i) := by
  open MatrixOrder in
  rw [cfc_eq, ← Subtype.coe_le_coe, ZeroMemClass.coe_zero]
  rw [_root_.cfc_nonneg_iff f A.mat, A.H.spectrum_real_eq_range_eigenvalues]
  grind

open ComplexOrder in
lemma cfc_posDef : (A.cfc f).mat.PosDef ↔ ∀ i, 0 < f (A.H.eigenvalues i) := by
  rw [(A.cfc f).H.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues f
  rw [he]
  refine ⟨fun h i ↦ ?_, fun h i ↦ h (e i)⟩
  simpa using h (e.symm i)

variable {A f} in
/-- If a rael function preserves nonnegativity, the CFC preserves PSDness. -/
theorem cfc_nonneg_of_nonneg (hA : 0 ≤ A) (hf : ∀ i ≥ 0, 0 ≤ f i) :
    0 ≤ A.cfc f := by
  rw [cfc_nonneg_iff]
  rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg] at hA
  exact fun i ↦ hf _ (hA i)

set_option backward.isDefEq.respectTransparency false in
lemma cfc_nonSingular (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0) : NonSingular (A.cfc f) := by
  rw [nonSingular_iff_eigenvalue_ne_zero]
  obtain ⟨e, he⟩ := cfc_eigenvalues f A
  simpa [he] using fun i ↦ hf (e i)


set_option backward.isDefEq.respectTransparency false in
lemma trace_mul_cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    (A.mat * (A.cfc f).mat).trace = ∑ i, A.H.eigenvalues i * f (A.H.eigenvalues i) := by
  conv_lhs => rw [A.eq_conj_diagonal]
  rw [cfc_conj_unitary]
  simp [conj, Matrix.mul_assoc, A.H.eigenvectorUnitary.val.trace_mul_comm]
  simp [← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]

lemma norm_eq_sum_eigenvalues_sq (A : HermitianMat d 𝕜) :
    ‖A‖ ^ 2 = ∑ i, (A.H.eigenvalues i)^2 := by
  rw [← RCLike.ofReal_inj (K := 𝕜), RCLike.ofReal_pow, norm_eq_trace_sq]
  conv_lhs => change (A ^ 2).mat.trace; rw [(A ^ 2).H.trace_eq_sum_eigenvalues]
  simp only [map_sum, map_pow]
  rw [← cfc_pow]
  obtain ⟨e, he⟩ := cfc_eigenvalues (· ^ 2) A
  simp only [he, Function.comp_apply, map_pow]
  exact e.sum_comp (fun x ↦ (algebraMap ℝ 𝕜) (A.H.eigenvalues x) ^ 2)

variable {A} in
lemma lt_smul_of_norm_lt {r : ℝ} (h : ‖A‖ ≤ r) : A ≤ r • 1 := by
  rcases lt_or_ge r 0 with _ | hr
  · have := norm_nonneg A
    order
  rcases isEmpty_or_nonempty d
  · exact le_of_subsingleton
  have h' := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
  rw [norm_eq_sum_eigenvalues_sq] at h'
  nth_rw 1 [← cfc_const A, ← cfc_id A]
  rw [le_iff, ← cfc_sub]
  rw [(HermitianMat.H _).posSemidef_iff_eigenvalues_nonneg]
  intro i; rw [Pi.zero_apply]
  obtain ⟨e, he⟩ := cfc_eigenvalues ((fun x ↦ r) - id) A
  rw [he]; clear he
  dsimp only [Function.comp_apply, Pi.sub_apply, id_eq]
  rw [sub_nonneg]
  apply le_of_sq_le_sq _ hr
  refine le_trans ?_ h'
  exact Finset.single_le_sum (f := fun x ↦ (A.H.eigenvalues x)^2) (by intros; positivity) (Finset.mem_univ _)

lemma ball_subset_Icc : Metric.ball A r ⊆ Set.Icc (A - r • 1) (A + r • 1) := by
  intro x
  simp only [Metric.mem_ball, dist_eq_norm, Set.mem_Icc, tsub_le_iff_right]
  intro h
  constructor
  · rw [← norm_neg] at h
    grw [← lt_smul_of_norm_lt h.le]
    simp
  · grw [← lt_smul_of_norm_lt h.le]
    simp

lemma spectrum_subset_of_mem_Icc (A B : HermitianMat d 𝕜) :
    ∃ a b, ∀ x, A ≤ x ∧ x ≤ B → spectrum ℝ x.mat ⊆ Set.Icc a b := by
  use ⨅ i, A.H.eigenvalues i, ⨆ i, B.H.eigenvalues i
  rintro x ⟨hl, hr⟩
  exact A.H.spectrum_subset_of_mem_Icc B.H hl hr

--TODO: Generalize this to real matrices (really, RCLike) too. The theorem below
-- gives it for complex matrices only.
-- @[fun_prop]
-- protected theorem cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
--     Continuous (cfc · f : HermitianMat d 𝕜 → HermitianMat d 𝕜) := by
--   rcases isEmpty_or_nonempty d
--   · sorry
--   rw [Metric.continuous_iff] at hf ⊢
--   intro x ε hε
--   have _ : Nonempty (spectrum ℝ x.toMat) := by
--     sorry
--   replace hf b := hf b ε hε
--   choose fc hfc₀ hfc using hf
--   let δ : ℝ := ⨆ e : spectrum ℝ x.toMat, fc e
--   refine ⟨δ, ?_, ?_⟩
--   · --This whole block should just be `positivity`. TODO fix.
--     dsimp [δ]
--     --Why doesn't just `classical` make this happen automatically?
--     replace h_fin := Fintype.ofFinite (spectrum ℝ x.toMat)
--     rw [← Finset.sup'_univ_eq_ciSup, gt_iff_lt, Finset.lt_sup'_iff]
--     simp [hfc₀]
--   intro a ha
--   simp only [dist, AddSubgroupClass.subtype_apply, val_eq_coe, cfc_toMat] at ha ⊢
--   sorry

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
protected lemma cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (HermitianMat.cfc · f : HermitianMat d ℂ → HermitianMat d ℂ) := by
  unfold HermitianMat.cfc
  suffices Continuous (fun A : HermitianMat d ℂ ↦ _root_.cfc f A.mat) by
    fun_prop
  have h_compact_cover := LocallyCompactSpace.local_compact_nhds (X := HermitianMat d ℂ)
  apply continuous_of_continuousOn_iUnion_of_isOpen (ι := HermitianMat d ℂ × {x : ℝ // 0 < x})
    (s := fun ab ↦ Metric.ball ab.1 ab.2)
  · rintro ⟨A, r, hr⟩
    apply ContinuousOn.mono ?_ (ball_subset_Icc A r)
    obtain ⟨a, b, hab⟩ := spectrum_subset_of_mem_Icc (A - r • 1) (A + r • 1)
    open ComplexOrder in
    refine ContinuousOn.cfc (s := fun _ ↦ Set.Icc a b) (t := Set.Icc (A - r • 1) (A + r • 1)) (A := CStarMatrix d d ℂ) f ?_ (by fun_prop) ?_ (fun x _ ↦ x.H)
    · intro _ _
      exact isCompact_Icc
    · simp only [Set.mem_Icc]
      exact fun _ _ ↦ eventually_nhdsWithin_of_forall hab
  · simp
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    use ⟨x, 1⟩
    simp

open ComplexOrder in
lemma Matrix.PosDef.spectrum_subset_Ioi {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.PosDef) : spectrum ℝ A ⊆ Set.Ioi 0 := by
  intro x hx;
  -- Since $A$ is positive definite, all its eigenvalues are positive.
  have h_eigenvalues_pos : ∀ i : d, 0 < hA.1.eigenvalues i := by
    exact hA.eigenvalues_pos;
  have h_spectrum_eq_range : spectrum ℝ A = Set.range (hA.1.eigenvalues) := by
    exact Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hA.left;
  aesop

/--
If f is a continuous family of functions parameterized by x, then (fun x => A.cfc (f x)) is also continuous.
-/
@[fun_prop]
theorem continuous_cfc_fun {f : X → ℝ → ℝ} (hf : ∀ i, Continuous (f · i)) :
    Continuous (fun x ↦ A.cfc (f x)) := by
  apply Continuous.subtype_mk
  conv => enter [1, x]; apply A.cfc_toMat_eq_sum_smul_proj (f x)
  fun_prop

variable {f : X → ℝ → ℝ} {S : Set X}
/--
ContinuousOn variant for when all the matrices (A x) have a spectrum in a set T, and f is continuous on a set S.
-/
@[fun_prop]
theorem continuousOn_cfc_fun {T : Set ℝ}
  (hf : ∀ i ∈ T, ContinuousOn (f · i) S) (hA : spectrum ℝ A.mat ⊆ T) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  simp_rw [continuousOn_iff_continuous_domRestrict] at hf ⊢
  apply Continuous.subtype_mk
  conv => enter [1, x]; apply A.cfc_toMat_eq_sum_smul_proj (f x)
  unfold Set.domRestrict at hf
  apply continuous_finsetSum _
  rw [A.H.spectrum_real_eq_range_eigenvalues] at hA
  refine fun i _ ↦ Continuous.smul (hf _ (by grind)) (by fun_prop)

section joint_continuity

--TODO Cleanup

/--
Bound the Frobenius norm of a functional calculus application.
-/
lemma norm_cfc_le_sqrt_card_mul_bound {A : HermitianMat d ℂ} {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ spectrum ℝ A.mat, ‖f x‖ ≤ C) :
    ‖A.cfc f‖ ≤ Real.sqrt (Fintype.card d) * C := by
  rw [ ← Real.sqrt_sq ( norm_nonneg _ ) ];
  -- Recall that the Frobenius norm of a Hermitian matrix is the square root of the sum of the squares of its eigenvalues.
  have h_frobenius_eigenvalues : ∀ (M : HermitianMat d ℂ), ‖M‖ ^ 2 = ∑ i ∈ Finset.univ, (M.H.eigenvalues i) ^ 2 := by
    exact fun M => norm_eq_sum_eigenvalues_sq M;
  -- Applying the bound on the eigenvalues to the Frobenius norm.
  have h_bound : ∑ i ∈ Finset.univ, ((A.cfc f).H.eigenvalues i) ^ 2 ≤ (Fintype.card d) * C ^ 2 := by
    have h_bound : ∀ i, ((A.cfc f).H.eigenvalues i) ^ 2 ≤ C ^ 2 := by
      intro i
      have h_eigenvalue_bound : |(A.cfc f).H.eigenvalues i| ≤ C := by
        obtain ⟨ x, hx, hx' ⟩ : (A.cfc f).H.eigenvalues i ∈ f '' spectrum ℝ A.mat := by
          have h_bound := (A.cfc f).H.eigenvalues_mem_spectrum_real i
          rwa [spectrum_cfc_eq_image A f] at h_bound
        specialize hf x hx
        aesop;
      nlinarith only [ abs_le.mp h_eigenvalue_bound ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => h_bound _ ) ( by simp );
  rw [ h_frobenius_eigenvalues, Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg ( Fintype.card d : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg ( Fintype.card d ) ) ]

/-
The norm of the difference of two functional calculus applications is bounded by `sqrt(d)` times the sup norm of the difference of the functions.
-/
lemma norm_cfc_sub_cfc_le_sqrt_card {A : HermitianMat d ℂ} {f g : ℝ → ℝ} :
    ‖A.cfc f - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ⨆ x ∈ spectrum ℝ A.mat, ‖f x - g x‖ := by
  rw [ ← HermitianMat.cfc_sub ];
  refine' le_trans ( norm_cfc_le_sqrt_card_mul_bound _ _ ) _;
  exact ⨆ x ∈ spectrum ℝ A.mat, ‖f x - g x‖;
  · exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _;
  · intro x hx
    apply le_csSup;
    · -- The supremum of a finite set of real numbers is finite.
      have h_finite : Set.Finite (spectrum ℝ A.mat) := by
        exact Set.toFinite _;
      obtain ⟨ M, hM ⟩ := h_finite.exists_finset_coe;
      refine' ⟨ ∑ x ∈ M, ‖f x - g x‖, Set.forall_mem_range.2 fun x => _ ⟩;
      rw [ ← hM ];
      rw [ @ciSup_eq_ite ];
      split_ifs <;> [ exact Finset.single_le_sum ( fun x _ => norm_nonneg ( f x - g x ) ) ( by assumption ) ; exact le_trans ( by norm_num ) ( Finset.sum_nonneg fun x _ => norm_nonneg ( f x - g x ) ) ];
    · exact ⟨ x, by aesop ⟩;
  · rfl

/-
If f and g are close on T, and the spectrum of A is in T, then A.cfc f and A.cfc g are close.
-/
lemma norm_cfc_sub_le_of_sup_le {A : HermitianMat d ℂ} {f g : ℝ → ℝ} {T : Set ℝ} {ε : ℝ}
    (hT : spectrum ℝ A.mat ⊆ T) (hε : 0 ≤ ε) (h_sup : ∀ x ∈ T, ‖f x - g x‖ ≤ ε) :
    ‖A.cfc f - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ε := by
  refine' le_trans ( norm_cfc_sub_cfc_le_sqrt_card ) _;
  gcongr;
  refine' ciSup_le fun x => _;
  exact Real.iSup_le (fun i => h_sup x (hT i)) hε

/--
If $f$ is jointly continuous on $S \times T$ and $T$ is compact, then $x \mapsto f(x, \cdot)$ is continuous into the space of bounded functions on $T$ with the uniform norm.
-/
lemma dist_lt_of_continuous' {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {S : Set X} {T : Set ℝ}
    (hT : IsCompact T)
    (hf : ContinuousOn (fun (p : X × ℝ) ↦ f p.1 p.2) (S ×ˢ T))
    {x₀ : X} (hx₀ : x₀ ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds x₀, ∀ x ∈ U ∩ S, ∀ t ∈ T, ‖f x t - f x₀ t‖ < ε := by
  by_contra h_contra;
  -- For each $t \in T$, by continuity at $(x₀, t)$, there exist neighborhoods $U_t$ of $x₀$ and $V_t$ of $t$ such that for all $x \in U_t \cap S$ and $t' \in V_t \cap T$, $|f(x, t') - f(x₀, t)| < \epsilon/2$.
  have h_cont : ∀ t ∈ T, ∃ U_t ∈ nhds x₀, ∃ V_t ∈ nhds t, ∀ x ∈ U_t ∩ S, ∀ t' ∈ V_t ∩ T, ‖f x t' - f x₀ t‖ < ε / 2 := by
    intro t ht
    have h_cont_t : ∀ᶠ (p : X × ℝ) in nhds (x₀, t), p ∈ S ×ˢ T → ‖f p.1 p.2 - f x₀ t‖ < ε / 2 := by
      have := hf ( x₀, t ) ⟨ hx₀, ht ⟩;
      have := this.eventually ( Metric.ball_mem_nhds _ ( half_pos hε ) );
      rw [ eventually_nhdsWithin_iff ] at this; aesop;
    rcases mem_nhds_prod_iff.mp h_cont_t with ⟨ U, hU, V, hV, hUV ⟩;
    exact ⟨ U, hU, V, hV, fun x hx t' ht' => hUV ( Set.mk_mem_prod hx.1 ht'.1 ) ⟨ hx.2, ht'.2 ⟩ ⟩;
  choose! U hU V hV hUV using h_cont;
  -- Since $T$ is compact, cover it by finitely many $V_{t_i}$. Let $U = \bigcap U_{t_i}$.
  obtain ⟨t_fin, ht_fin⟩ : ∃ t_fin : Finset ℝ, (∀ t ∈ t_fin, t ∈ T) ∧ T ⊆ ⋃ t ∈ t_fin, V t := by
    have := hT.elim_nhds_subcover V fun t ht => hV t ht;
    tauto;
  refine h_contra ⟨⋂ t ∈ t_fin, U t, ?_, ?_⟩
  · exact Filter.biInter_mem ( Finset.finite_toSet t_fin ) |>.2 fun t ht => hU t ( ht_fin.1 t ht );
  · intro x hx t ht
    obtain ⟨t', ht'_fin, ht'_t⟩ : ∃ t' ∈ t_fin, t ∈ V t' := by
      simpa using ht_fin.2 ht;
    have := hUV t' ( ht_fin.1 t' ht'_fin ) x ⟨ Set.mem_iInter₂.1 hx.1 t' ht'_fin, hx.2 ⟩ t ⟨ ht'_t, ht ⟩;
    have := hUV t' ( ht_fin.1 t' ht'_fin ) x₀ ⟨ mem_of_mem_nhds ( hU t' ( ht_fin.1 t' ht'_fin ) ), hx₀ ⟩ t ⟨ ht'_t, ht ⟩;
    exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp ‹‖f x t - f x₀ t'‖ < ε / 2›, abs_lt.mp ‹‖f x₀ t - f x₀ t'‖ < ε / 2› ], by linarith [ abs_lt.mp ‹‖f x t - f x₀ t'‖ < ε / 2›, abs_lt.mp ‹‖f x₀ t - f x₀ t'‖ < ε / 2› ] ⟩

set_option backward.isDefEq.respectTransparency false in
/--
The functional calculus is continuous on matrices with spectrum in a compact set.
-/
lemma continuousOn_cfc_of_compact {K : Set ℝ} {g : ℝ → ℝ} (hK : IsCompact K) (hg : ContinuousOn g K) :
    ContinuousOn (fun (A : HermitianMat d ℂ) ↦ A.cfc g) {A | spectrum ℝ A.mat ⊆ K} := by
  by_contra! h_contra;
  -- By Stone-Weierstrass, there exists a sequence of polynomials `p_n` converging uniformly to `g` on `K`.
  obtain ⟨p_n, hp_n⟩ : ∃ p_n : ℕ → Polynomial ℝ, (∀ n, ∀ x ∈ K, |(p_n n).eval x - g x| ≤ 1 / (n + 1)) := by
    have h_stone_weierstrass : ∀ ε > 0, ∃ p : Polynomial ℝ, ∀ x ∈ K, |p.eval x - g x| < ε := by
      have := @exists_polynomial_near_of_continuousOn;
      obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, K ⊆ Set.Icc a b := by
        exact ⟨ hK.bddBelow.some, hK.bddAbove.some, fun x hx => ⟨ hK.bddBelow.choose_spec hx, hK.bddAbove.choose_spec hx ⟩ ⟩;
      -- Extend $g$ to a continuous function on $[a, b]$.
      obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) ∧ ∀ x ∈ K, f x = g x := by
        have := @ContinuousMap.exists_restrict_eq;
        specialize this ( show IsClosed K from hK.isClosed ) ( ContinuousMap.mk ( fun x => g x ) <| by exact continuousOn_iff_continuous_domRestrict.mp hg );
        exact ⟨ _, this.choose.continuous.continuousOn, fun x hx => by simpa using congr_arg ( fun f => f ⟨ x, hx ⟩ ) this.choose_spec ⟩;
      exact fun ε εpos => by rcases this a b f hf.1 ε εpos with ⟨ p, hp ⟩ ; exact ⟨ p, fun x hx => by simpa only [ hf.2 x hx ] using hp x ( hab hx ) ⟩ ;
    exact ⟨ fun n => Classical.choose ( h_stone_weierstrass ( 1 / ( n + 1 ) ) ( by positivity ) ), fun n x hx => le_of_lt ( Classical.choose_spec ( h_stone_weierstrass ( 1 / ( n + 1 ) ) ( by positivity ) ) x hx ) ⟩;
  -- The sequence `A ↦ A.cfc (p_n)` converges uniformly to `A ↦ A.cfc g` on `{A | spectrum A ⊆ K}`.
  have h_uniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : HermitianMat d ℂ, spectrum ℝ A.mat ⊆ K → ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ < ε := by
    -- By the properties of the functional calculus, we have `‖A.cfc p_n - A.cfc g‖ ≤ sqrt(d) * ‖p_n - g‖_{∞, K}`.
    have h_uniform_bound : ∀ n, ∀ A : HermitianMat d ℂ, spectrum ℝ A.mat ⊆ K → ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * (1 / (n + 1)) := by
      intro n A hA
      have h_uniform_bound : ‖A.cfc (fun x => (p_n n).eval x) - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ⨆ x ∈ spectrum ℝ A.mat, |(p_n n).eval x - g x| := by
        exact norm_cfc_sub_cfc_le_sqrt_card;
      refine' le_trans h_uniform_bound ( mul_le_mul_of_nonneg_left _ ( Real.sqrt_nonneg _ ) );
      refine' ciSup_le fun x => _;
      field_simp;
      by_cases hx : x ∈ spectrum ℝ A.mat <;> simp_all
      exact le_trans ( mul_le_mul_of_nonneg_right ( hp_n n x ( hA hx ) ) ( by positivity ) ) ( by nlinarith [ mul_inv_cancel₀ ( by positivity : ( n : ℝ ) + 1 ≠ 0 ) ] );
    exact fun ε εpos => ⟨ Nat.ceil ( ε⁻¹ * Real.sqrt ( Fintype.card d ) ), fun n hn A hA => lt_of_le_of_lt ( h_uniform_bound n A hA ) ( by rw [ mul_one_div, div_lt_iff₀ ] <;> nlinarith [ Nat.ceil_le.mp hn, inv_pos.mpr εpos, mul_inv_cancel₀ εpos.ne', Real.sqrt_nonneg ( Fintype.card d ), Real.sq_sqrt ( Nat.cast_nonneg ( Fintype.card d ) ) ] ) ⟩;
  -- The uniform limit of continuous functions is continuous.
  have h_cont : ContinuousOn (fun A : HermitianMat d ℂ => A.cfc g) {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K} := by
    have h_seq_cont : ∀ n, ContinuousOn (fun A : HermitianMat d ℂ => A.cfc (fun x => (p_n n).eval x)) {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K} := by
      fun_prop
    refine' Metric.continuousOn_iff.mpr _;
    intro A hA ε εpos
    obtain ⟨N, hN⟩ := h_uniform (ε / 3) (by linarith)
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ > 0, ∀ a ∈ {A : HermitianMat d ℂ | spectrum ℝ A.mat ⊆ K}, dist a A < δ → ‖a.cfc (fun x => (p_n N).eval x) - A.cfc (fun x => (p_n N).eval x)‖ < ε / 3 := by
      have := Metric.continuousOn_iff.mp ( h_seq_cont N ) A hA ( ε / 3 ) ( by linarith );
      exact ⟨ this.choose, this.choose_spec.1, fun a ha ha' => by simpa only [ dist_eq_norm ] using this.choose_spec.2 a ha ha' ⟩;
    refine' ⟨ δ, δpos, fun a ha ha' => _ ⟩;
    have := hN N le_rfl a ha;
    have := hN N le_rfl A hA;
    rw [ dist_eq_norm ];
    rw [ show a.cfc g - A.cfc g = ( a.cfc g - a.cfc ( fun x => Polynomial.eval x ( p_n N ) ) ) + ( a.cfc ( fun x => Polynomial.eval x ( p_n N ) ) - A.cfc ( fun x => Polynomial.eval x ( p_n N ) ) ) + ( A.cfc ( fun x => Polynomial.eval x ( p_n N ) ) - A.cfc g ) by abel1 ];
    exact lt_of_le_of_lt ( norm_add₃_le .. ) ( by linarith [ norm_sub_rev ( a.cfc g ) ( a.cfc fun x => Polynomial.eval x ( p_n N ) ), norm_sub_rev ( A.cfc fun x => Polynomial.eval x ( p_n N ) ) ( A.cfc g ), hδ a ha ha' ] );
  contradiction

end joint_continuity


end CFC
end HermitianMat
