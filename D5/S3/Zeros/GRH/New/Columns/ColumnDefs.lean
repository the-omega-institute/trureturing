/- GID: D5/S3/Zeros/GRH/New/Columns/ColumnDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Columns/ColumnDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Columns.ColumnDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/ColumnDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.DepthPairs
import D5.S3.Zeros.GRH.New.Exchange.LValueRatio
import D5.S3.Zeros.GRH.New.Seesaw.NamesAtSplitLevel
import D5.S3.Zeros.GRH.New.Curve.IntegralVacuum
import D5.S3.Zeros.GRH.New.Data.ChosenPlaceLevels
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: the primes of E dividing π; the levels on the spaces X_j; columns, that is, algebraic
forms on X_0 (not the columns of a Young diagram, nor `IsColumn`); branching and restriction from
X_m to Y_m. -/

noncomputable section

open Matrix Finset Subgroup Ideal Fintype

namespace Data

variable {P} (D : Data P) (j) {w}
attribute [local grind] κ keptColumns lastEntry n reducedHalfGap

@[simp] lemma π_ne_zero : D.π ≠ 0 := by grind [π, NeZero.natCast_ne]

/-- The finite set of primes w of E dividing π = `Data.π`, where ππ̄ = N (`Data.π_mul_star`). -/
def piPlaces : Finset (FinPlace D.E) :=
  (finite_factors (span_singleton_eq_bot.ne.2 D.π_ne_zero)).toFinset

lemma mem_piPlaces : w ∈ D.piPlaces ↔ D.π ∈ w.1 := by simp [piPlaces]

protected lemma isSplitLevel_piPlaces : IsSplitLevel D.piPlaces D.N := by grind [IsSplitLevel,
  mem_piPlaces, mem_star_place, v_N_eq_exp_neg_one, π, mul_comm, P.q_eq_of_modEq_one D.N_modEq_one,
  mul_mem_left, P.star_mem_iff D.N_modEq_one _ ⟨1, by simpa using D.π_mul_star⟩]

/-- The number of primes w of E dividing π equals f, the number of infinite places of E. -/
lemma card_piPlaces : #D.piPlaces = D.f := by
  simpa [and_iff_left_of_imp (D.isSplitLevel_piPlaces.natCast_mem _), ← mem_piPlaces] using
                (P.nonempty_infinitePlace_equiv_finPlace D.N_modEq_one (a :=
    D.π) ⟨1, by simp [π_mul_star]⟩).some.cardinal_eq.symm

/-- The level of stage j: elements of the principal level π̄₀π̄₁ on X_j whose last row is
congruent to (0, …, 0, 1) modulo π. -/
def columnLevel :=
  D.chosenLevel (n := D.X j) ⊓ (congruenceGL (Ô _ ∙ algebraMap _ _ D.π) Sum.inr).subgroupOf _

lemma principalLevel_le_columnLevel : principalLevel _ (D.piGBar * D.π) ≤ D.columnLevel j :=
  fun _ h ↦ ⟨D.principalLevel_le_chosenLevel (by simp) h,
  (principalLevel_le_of_dvd (dvd_mul_left ..) h).imp id (by simp)⟩

instance isLevel_columnLevel {j} : IsLevel (D.columnLevel j) := ⟨inf_le_of_left_le levelOf_le_Kf,
  isOpen_mono (principalLevel_le_columnLevel ..) (isOpen_principalLevel (by simp))⟩

/-- A chosen bijection between Y_m and the indices of X_m other than the last, which have the same
cardinality. -/
def lastIndexEquiv : D.Y D.m ≃ D.InitIndex D.m := equivOfCardEq (by simp; grind [ϱ])

/-- An integer matrix from weight κ on X_m to weight `Data.columnsY` on Y_m, chosen with the
branching properties (GL_{n+1} to GL_n) of `exists_branching_matrix`. -/
def branching := Classical.indefiniteDescription _ (exists_branching_matrix (fun _ ↦
  D.lastIndexEquiv.sumCongr (.refl _)) D.columnsY D.k (D.lastEntry D.m) (D.lastEntry D.m)
  (tsub_add_cancel_of_le (by grind [Pi.le_def] : (fun _ ↦ D.keptColumns) ≤ D.κ))
  (by bound) (by grind) (by simp (disch := grind [dvd_mul_left]) [ite_eq_right, card_congr
  D.lastIndexEquiv, keptColumns, reducedHalfGap, n, Nat.sub_right_comm _ 1, Nat.dvd_sub_iff_right]))

lemma card_X : card (D.X j) = D.n j := by simp; grind

lemma classAut_columnLevel_eq_bot : ∀ g, classAut stdRatPoints (D.columnLevel 0) g = ⊥ :=
  D.classAut_eq_bot_of_le_chosenLevel inf_le_left (by grind [card_X])

/-- The space of columns: algebraic forms on X_0 of weight (κ, 0) fixed by the level
`Data.columnLevel` of stage 0. -/
abbrev Column := levelSpace (algFormRep D.κ (D.lastEntry 0)) (D.columnLevel 0)

/-- The space of smooth algebraic forms on X_j of weight (κ, e_j), with e_j = `Data.lastEntry` j. -/
abbrev Stage := AlgForm (D.X j) D.κ (D.lastEntry j)

/-- The branching exponent n_τ: the sum over heights 1 ≤ h < 𝗇_m of κ_τ(h) − `Data.keptColumns` h,
plus the determinant exponent `Data.lastEntry` at stage m. -/
def branchExp τ :=
  diagramWeight (rankAt (D.X D.m)) (D.κ - fun _ ↦ D.keptColumns) (τ, 0) + D.lastEntry D.m τ

/-- At every infinite place τ, the exponent n_τ (`Data.branchExp`) is at least κ_τ(1) − 2b, where
κ_τ(1) is the number of columns of height one at τ. -/
lemma le_branchExp τ : D.κ τ 1 - 2 * D.b ≤ D.branchExp τ := by grw [branchExp,
  PolyRep.diagramWeight_eq_succ_add, ← D.w_le_two_mul_b .refl τ]; simp; norm_cast; grind

/-- The homomorphism g ↦ diag(g, 1) from the finite adelic unitary group of Y_m to that of X_m,
along the bijection `Data.lastIndexEquiv`. -/
def borderU := (U.block (R := 𝔸f D.E) (D.lastIndexEquiv.sumCongr (.refl Unit))).comp (.inl ..)

seal Finset.univ Finset.sum Finset.prod in
/-- The restriction of algebraic forms from X_m to Y_m: restrict to points diag(h,1), apply the
branching matrix, and multiply by ∏_τ τ(π̄)^{−n_τ}. -/
def restrictToY := (∏ τ, Φ τ (star ↑D.π) ^ (-D.branchExp τ)) •
  ((D.branching.1.map (↑)).mulVecLin.compLeft _ ∘ₗ .funLeft ℂ _ D.borderU).restrict (p :=
  AlgForm ..) (q := AlgForm ..) (id fun ψ ↦ .imp (((rightStab ψ).comap
  D.borderU).isOpen_mono (fun _ ↦ (by simp [· _])) <| ·.preimage ((U.isClosedEmbedding_mat
  isUnit_one).continuous_iff.2 (.matrix_reindex (by simp [U.sum]; fun_prop) ..))) fun k _ _ ↦ by
  simp [stdSpace_weightRep_apply]
  erw [block_embFin, k, stdSpace_weightRep_apply, mulVec_mulVec, D.branching.2.1 _ _ 1,
    Finset.prod_eq_one, one_smul] <;>
    simp [← ext_iff, PolyRep.blockScalar])
