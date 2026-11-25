/- GID: D5/S3/Quantum/Decoherence/LabelResetBandwidth
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/LabelResetBandwidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact ambient label reset with a faithful Gibbs bath and a minimum bandwidth on the record support. -/

import D5.S3.Quantum.Decoherence.LabelResetSupport
import D5.S3.Quantum.Decoherence.GibbsBathBandwidth
import D5.S3.Quantum.Decoherence.ExactQubitBathErasure

/-!
# Finite label reset with preservation of the average record

The ambient register order is X, bath, record. The reduced orbit uses bath,
record support. The columns of the input embedding carry the classical labels
and their normalized records. The output label can be any prescribed unit vector.
-/

set_option autoImplicit false

open Matrix Unitary
open scoped BigOperators ComplexOrder Kronecker Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open GibbsBathBandwidth

namespace LabelResetBandwidth

noncomputable section

variable {N I J D : Type*} [Fintype N] [Fintype I] [Fintype J] [Fintype D]
  [DecidableEq N] [DecidableEq I] [DecidableEq J] [DecidableEq D]

section PureMarginal

variable {X : Type*} [Fintype X]

/-- Embed columns in the sector with label vector w. -/
def resetEmbedding (w : X → ℂ) (K : Matrix D I ℂ) : Matrix (X × D) I ℂ :=
  fun i j => w i.1 * K i.2 j

omit [Fintype I] [DecidableEq D] [DecidableEq I] in
private theorem resetEmbedding_gram (w : X → ℂ) (hw : star w ⬝ᵥ w = 1)
    (K : Matrix D I ℂ) : (resetEmbedding w K)ᴴ * resetEmbedding w K = Kᴴ * K := by
  ext i j
  have hsum : ∑ x : X, star (w x) * w x = 1 := by simpa [dotProduct, Pi.star_apply] using hw
  simp only [Matrix.mul_apply, conjTranspose_apply, resetEmbedding, star_mul,
    Fintype.sum_prod_type]
  simp_rw [show ∀ a b c d : ℂ, a * b * (c * d) = (b * c) * (a * d) by intros; ring,
    ← Finset.mul_sum]
  rw [← Finset.sum_mul, hsum, one_mul]

omit [Fintype D] [Fintype X] [DecidableEq D] [DecidableEq I] in
private theorem pad_resetEmbedding (w : X → ℂ) (K : Matrix D I ℂ) (A : Matrix I I ℂ) :
    pad (resetEmbedding w K) A = pure w ⊗ₖ pad K A := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [pad, Matrix.mul_apply, resetEmbedding, pure, vecMulVec_apply, Pi.star_apply,
    Matrix.kronecker_apply, conjTranspose_apply, star_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end PureMarginal

section Records

variable {X E B M : Type*} [Fintype X] [Fintype E] [Fintype B] [Fintype M]
  [DecidableEq X] [DecidableEq E] [DecidableEq B] [DecidableEq M] [Nonempty X] [Nonempty B]

abbrev Total (X B E : Type*) := Matrix (X × (B × E)) (X × (B × E)) ℂ

/-- Each classical label carries its own record vector and leaves the bath index intact. -/
def recordEmbedding (v : X → E → ℂ) : Matrix (X × (B × E)) (B × X) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2.1 = j.1 then v j.2 i.2.2 else 0

omit [DecidableEq E] [Nonempty X] [Nonempty B] in
theorem recordEmbedding_isometry (v : X → E → ℂ)
    (hv : ∀ x, star (v x) ⬝ᵥ v x = 1) :
    (recordEmbedding (B := B) v)ᴴ * recordEmbedding (B := B) v = 1 := by
  ext ⟨b, x⟩ ⟨c, y⟩
  simp only [Matrix.mul_apply, conjTranspose_apply, recordEmbedding, Fintype.sum_prod_type]
  by_cases h : (b, x) = (c, y)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [apply_ite (star : ℂ → ℂ), ite_and, ite_mul, mul_ite]
    exact hv x
  · rw [Matrix.one_apply_ne h]
    apply Finset.sum_eq_zero
    intro z _
    apply Finset.sum_eq_zero
    intro d _
    apply Finset.sum_eq_zero
    intro e _
    split_ifs with h₁ h₂ h₂
    · exact (h (Prod.ext (h₁.2.symm.trans h₂.2) (h₁.1.symm.trans h₂.1))).elim
    all_goals simp

/-- The equiprobable classical input with an independent bath state. -/
def initial (v : X → E → ℂ) (τ : Matrix B B ℂ) : Total X B E :=
  pad (recordEmbedding v) (τ ⊗ₖ mixed X)

/-- The matrix with the pure records as columns. -/
def recordColumns (v : X → E → ℂ) : Matrix E X ℂ := fun i x => v x i

/-- The average of the pure record projectors. -/
def average (v : X → E → ℂ) : Matrix E E ℂ :=
  ((Fintype.card X : ℂ)⁻¹) • (recordColumns v * (recordColumns v)ᴴ)

omit [Fintype E] [DecidableEq E] [DecidableEq X] [Nonempty X] in
theorem average_apply (v : X → E → ℂ) (i j : E) :
    average v i j = ((Fintype.card X : ℂ)⁻¹) * ∑ x, v x i * star (v x j) := by
  simp [average, recordColumns, Matrix.mul_apply, conjTranspose_apply]

omit [DecidableEq E] [DecidableEq X] [Nonempty X] in
theorem average_psd (v : X → E → ℂ) : (average v).PosSemidef := by
  have h : (0 : ℂ) ≤ ((Fintype.card X : ℂ)⁻¹) := by
    have h : 0 ≤ ((Fintype.card X : ℝ)⁻¹) := by positivity
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using (Complex.zero_le_real.mpr h)
  exact (posSemidef_self_mul_conjTranspose (recordColumns v)).smul h

omit [DecidableEq E] [DecidableEq X] in
theorem average_trace (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1) :
    (average v).trace = 1 := by
  classical
  have hX : (Fintype.card X : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn (x : X) : ∑ i : E, v x i * star (v x i) = 1 := by
    simpa [dotProduct, Pi.star_apply, mul_comm] using hv x
  simp only [Matrix.trace, diag_apply, average_apply, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  change ((Fintype.card X : ℂ)⁻¹) * (∑ x : X, ∑ i : E, v x i * star (v x i)) = 1
  rw [Finset.sum_congr rfl (fun x _ => hn x)]
  simp [hX]

omit [DecidableEq E] [DecidableEq X] in
theorem average_rank (v : X → E → ℂ) : (average v).rank = (recordColumns v).rank := by
  have hX : ((Fintype.card X : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  unfold average
  rw [rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hX),
    rank_self_mul_conjTranspose]

omit [DecidableEq E] [DecidableEq X] in
theorem average_full_rank_iff (v : X → E → ℂ) :
    (average v).rank = Fintype.card X ↔ LinearIndependent ℂ v := by
  rw [average_rank, rank_eq_finrank_span_cols, linearIndependent_iff_card_eq_finrank_span]
  exact eq_comm

omit [Fintype E] [DecidableEq E] [Nonempty X] [Nonempty B] in
theorem initial_apply (v : X → E → ℂ) (τ : Matrix B B ℂ)
    (x y : X) (b c : B) (i j : E) :
    initial v τ (x, b, i) (y, c, j) =
      if x = y then ((Fintype.card X : ℂ)⁻¹) * v x i * star (v x j) * τ b c else 0 := by
  have hleft (p : B) (z : X) :
      ((recordEmbedding (B := B) v : Matrix (X × (B × E)) (B × X) ℂ) *
        (τ ⊗ₖ mixed X)) (x, b, i) (p, z) =
        v x i * (τ b p * mixed X x z) := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, recordEmbedding, Matrix.kroneckerMap_apply,
      ite_and, ite_mul]
  rw [initial, pad, Matrix.mul_apply]
  simp only [Fintype.sum_prod_type, hleft, conjTranspose_apply, recordEmbedding]
  simp [apply_ite (star : ℂ → ℂ), ite_and, mul_ite, mixed, Matrix.one_apply, Complex.real_smul]
  split <;> simp_all
  ring

/-- The physical output has the prescribed pure label and the original average record. -/
def Resets (v : X → E → ℂ) (w : X → ℂ) (A : Total X B E) : Prop :=
  partialTraceRight A = pure w ∧ partialTraceLeft (partialTraceLeft A) = average v

omit [Fintype E] [DecidableEq E] [Nonempty X] [Nonempty B] in
theorem initial_record_marginal (v : X → E → ℂ) {τ : Matrix B B ℂ} (hτ : τ.trace = 1) :
    partialTraceLeft (partialTraceLeft (initial v τ)) = average v := by
  ext i j
  simp only [partialTraceLeft, initial_apply, ite_true, average_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  change _ * τ.trace = _
  rw [hτ, mul_one, mul_assoc]

end Records


section Orbit

variable {X E B M : Type*} [Fintype X] [Fintype E] [Fintype B] [Fintype M]
  [DecidableEq X] [DecidableEq E] [DecidableEq B] [DecidableEq M] [Nonempty X] [Nonempty B]


private theorem mixed_posDef (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] :
    (mixed X).PosDef := by
  exact Matrix.PosDef.one.smul (by change 0 < (Fintype.card X : ℝ)⁻¹; positivity)

private theorem posDef_full_rank {A : Matrix N N ℂ} (hA : A.PosDef) :
    A.rank = Fintype.card N := rank_of_isUnit _ hA.isUnit

omit [Nonempty B] in
/-- Every implemented reset has exactly the input rank. -/
theorem reset_rank (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    {τ : Matrix B B ℂ} (hτ : τ.PosDef) (U : unitary (Total X B E)) :
    (conjStarAlgAut ℂ _ U (initial v τ)).rank = Fintype.card B * Fintype.card X := by
  rw [rank_unitary_conj, initial, rank_pad _ (recordEmbedding_isometry v hv),
    posDef_full_rank (hτ.kronecker (mixed_posDef X)), Fintype.card_prod]

omit [DecidableEq X] [Nonempty X] [Nonempty B] in
/-- For any orthonormal coordinates on the record support, an exact reset has
the stated support, and the compressed output has the desired marginal. -/
theorem reset_support (v : X → E → ℂ) (w : X → ℂ) (hw : star w ⬝ᵥ w = 1)
    (V : Matrix E M ℂ) (hV : Vᴴ * V = 1) {ρ : Matrix M M ℂ}
    (hρ : average v = pad V ρ) {A : Total X B E} (hA : A.PosSemidef)
    (h : Resets v w A) :
    let K := (1 : Matrix B B ℂ) ⊗ₖ V
    let Ω := Kᴴ * partialTraceLeft A * K
    Ω.PosSemidef ∧ partialTraceLeft Ω = ρ ∧
      A = pad (resetEmbedding w K) Ω := by
  dsimp only
  let K := (1 : Matrix B B ℂ) ⊗ₖ V
  let Ω := Kᴴ * partialTraceLeft A * K
  have hs : partialTraceLeft A = pad K Ω :=
    supported_of_marginal V hV (partialTraceLeft_posSemidef hA) (h.2.trans hρ)
  have hm := congrArg (partialTraceLeft (A := B)) hs
  rw [partialTrace_pad, h.2, hρ] at hm
  refine ⟨(partialTraceLeft_posSemidef hA).conjTranspose_mul_mul_same K, ?_, ?_⟩
  · simpa only [compress_pad _ hV] using
      (congrArg (fun T => Vᴴ * T * V) hm).symm
  · rw [pad_resetEmbedding, ← hs]
    exact pure_marginal_factors w hw hA h.1

set_option maxHeartbeats 800000 in
omit [Nonempty B] in
/-- Lifting a reduced admissible unitary gives an ambient unitary that acts
as the prescribed map on every branch-and-bath input column. -/
theorem lift_reduced_unitary (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) (V : Matrix E X ℂ) (hV : Vᴴ * V = 1)
    {ρ : Matrix X X ℂ} (hρ : average v = pad V ρ) (τ : Matrix B B ℂ)
    (W : unitary (Matrix (B × X) (B × X) ℂ)) (hW : Retains τ ρ W) :
    ∃ U : unitary (Total X B E),
      (U : Total X B E) * recordEmbedding v =
        resetEmbedding w ((1 : Matrix B B ℂ) ⊗ₖ V) * (W : Matrix (B × X) (B × X) ℂ) ∧
      Resets v w (conjStarAlgAut ℂ _ U (initial v τ)) := by
  let K := (1 : Matrix B B ℂ) ⊗ₖ V
  let R := resetEmbedding w K
  have hR : Rᴴ * R = 1 := (resetEmbedding_gram w hw K).trans (bathEmbedding_isometry V hV)
  have hWi : (W : Matrix (B × X) (B × X) ℂ)ᴴ * (W : Matrix (B × X) (B × X) ℂ) = 1 := coe_star_mul_self W
  obtain ⟨U, hU⟩ := exists_unitary_extension (recordEmbedding v) (R * ↑W)
    (recordEmbedding_isometry v hv) (isometry_comp R _ hR hWi)
  refine ⟨U, hU, ?_⟩
  have hout : conjStarAlgAut ℂ _ U (initial v τ) =
      pure w ⊗ₖ pad K (conjStarAlgAut ℂ _ W (τ ⊗ₖ mixed X)) := by
    rw [conj_eq_pad, initial, pad_comp, hU, ← pad_comp, ← conj_eq_pad, pad_resetEmbedding]
  have hm : partialTraceLeft (pad K (conjStarAlgAut ℂ _ W (τ ⊗ₖ mixed X))) = average v := by
    rw [partialTrace_pad, show partialTraceLeft _ = ρ from hW, hρ]
  unfold Resets
  rw [hout]
  change partialTraceRight (Matrix.kronecker (pure w) _) = pure w ∧
    partialTraceLeft (partialTraceLeft (Matrix.kronecker (pure w) _)) = average v
  rw [partialTraceRight_kronecker, partialTraceLeft_kronecker, trace_pure w hw, one_smul, hm]
  refine ⟨?_, rfl⟩
  rw [← trace_partialTraceLeft, hm, average_trace v hv, one_smul]

omit [Nonempty B] in
/-- The actual compressed output of an ambient reset is in the reduced unitary orbit. -/
theorem reduce_reset_unitary (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) (V : Matrix E X ℂ) (hV : Vᴴ * V = 1)
    {ρ : Matrix X X ℂ} (hρ : average v = pad V ρ) {τ : Matrix B B ℂ} (hτ : τ.PosDef)
    (U : unitary (Total X B E)) (hU : Resets v w (conjStarAlgAut ℂ _ U (initial v τ))) :
    let A := conjStarAlgAut ℂ _ U (initial v τ)
    let K := (1 : Matrix B B ℂ) ⊗ₖ V
    let Ω := Kᴴ * partialTraceLeft A * K
    ∃ W : unitary (Matrix (B × X) (B × X) ℂ),
      conjStarAlgAut ℂ _ W (τ ⊗ₖ mixed X) = Ω ∧
      partialTraceLeft Ω = ρ ∧ A = pad (resetEmbedding w K) Ω := by
  dsimp only
  let A := conjStarAlgAut ℂ _ U (initial v τ)
  let S := τ ⊗ₖ mixed X
  let K := (1 : Matrix B B ℂ) ⊗ₖ V
  let R := resetEmbedding w K
  let Ω := Kᴴ * partialTraceLeft A * K
  have hR : Rᴴ * R = 1 := (resetEmbedding_gram w hw K).trans (bathEmbedding_isometry V hV)
  have hS : S.PosDef := hτ.kronecker (mixed_posDef X)
  have hA : A.PosSemidef := by
    dsimp only [A]
    rw [conj_eq_pad]
    exact pad_psd _ (pad_psd _ hS.posSemidef)
  obtain ⟨hΩ, hΩm, hout⟩ := reset_support v w hw V hV hρ hA hU
  change A = pad R Ω at hout
  have hchar : A.charpoly = (initial v τ).charpoly :=
    charpoly_conj_unitary (coe_star_mul_self U)
  have h₁ := padding_charpoly (recordEmbedding (B := B) v) (recordEmbedding_isometry v hv) S
  have h₂ := padding_charpoly R hR Ω
  have hc : S.charpoly = Ω.charpoly := by
    apply mul_left_cancel₀ (pow_ne_zero (Fintype.card (X × (B × E))) Polynomial.X_ne_zero)
    have hpad :
        (pad (recordEmbedding (B := B) v) S).charpoly = (pad R Ω).charpoly :=
      hchar.symm.trans (congrArg Matrix.charpoly hout)
    rw [← h₁, hpad, h₂]
  obtain ⟨W, hW⟩ := exists_unitary_of_charpoly_eq hS.isHermitian hΩ.isHermitian hc
  exact ⟨W, hW, hΩm, hout⟩

omit [Nonempty B] in
/-- Equal-size orthonormal input and reset supports give equivalent unitary
orbit conditions at finite matrix level. -/
theorem reset_unitary_orbit_iff (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) (V : Matrix E X ℂ) (hV : Vᴴ * V = 1)
    {ρ : Matrix X X ℂ} (hρ : average v = pad V ρ) {τ : Matrix B B ℂ} (hτ : τ.PosDef) :
    (∃ U : unitary (Total X B E), Resets v w (conjStarAlgAut ℂ _ U (initial v τ))) ↔
      ∃ W : unitary (Matrix (B × X) (B × X) ℂ), Retains τ ρ W := by
  constructor
  · rintro ⟨U, hU⟩
    obtain ⟨W, hW, hm, _⟩ := reduce_reset_unitary v hv w hw V hV hρ hτ U hU
    exact ⟨W, by unfold Retains; exact (congrArg partialTraceLeft hW).trans hm⟩
  · rintro ⟨W, hW⟩
    obtain ⟨U, _, hU⟩ := lift_reduced_unitary v hv w hw V hV hρ τ W hW
    exact ⟨U, hU⟩

end Orbit

section Support

variable {X E B : Type*} [Fintype X] [Fintype E] [Fintype B]
  [DecidableEq X] [DecidableEq E] [DecidableEq B] [Nonempty X] [Nonempty B]

private def selectColumns (e : I ↪ N) : Matrix N I ℂ :=
  fun i j => if i = e j then 1 else 0

omit [Fintype N] in
private theorem select_pad_diagonal (e : I ↪ N) (p : N → ℝ)
    (hp : ∀ i, p i ≠ 0 → i ∈ Set.range e) :
    pad (selectColumns e) (diagonalReal (p ∘ e)) = diagonalReal p := by
  ext i j
  rw [pad, Matrix.mul_apply]
  simp only [diagonalReal, mul_diagonal, selectColumns, conjTranspose_apply,
    apply_ite (star : ℂ → ℂ), star_one, star_zero,
    ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Function.comp_apply]
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k, rfl⟩ := hj
    by_cases hi : i = e k <;> simp [e.injective.eq_iff, hi]
  · have h (k : I) : j ≠ e k := fun he => hj ⟨k, he.symm⟩
    have hpj : p j = 0 := by by_contra hne; exact hj (hp _ hne)
    by_cases hij : i = j
    · subst i
      simp [h, hpj]
    · simp [h, hij]

omit [Fintype I] in
private theorem selectColumns_isometry (e : I ↪ N) :
    (selectColumns e)ᴴ * selectColumns e = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp [selectColumns, conjTranspose_apply, apply_ite (star : ℂ → ℂ),
    e.injective.eq_iff, Matrix.one_apply, eq_comm]

omit [DecidableEq E] [DecidableEq X] in
/-- The record support is spanned by the records themselves, including in the
linearly dependent case. -/
theorem average_support_eq_span (v : X → E → ℂ) :
    LinearMap.range (average v).mulVecLin = Submodule.span ℂ (Set.range v) := by
  have hle : LinearMap.range (average v).mulVecLin ≤
      LinearMap.range (recordColumns v).mulVecLin := by
    unfold average
    rw [← Matrix.mul_smul, mulVecLin_mul, LinearMap.range_comp]
    exact Submodule.map_mono le_top |>.trans_eq (Submodule.map_top _)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (average_rank v)
  rw [heq, Matrix.range_mulVecLin]
  rfl

omit [DecidableEq X] [Nonempty X] in
/-- Choose positive spectral coordinates on the average record's support. -/
theorem exists_support_frame (v : X → E → ℂ) :
    ∃ (V : Matrix E (Fin (average v).rank) ℂ) (p : Fin (average v).rank → ℝ),
      Vᴴ * V = 1 ∧ (∀ i, 0 < p i) ∧ average v = pad V (diagonalReal p) ∧
      Set.range p = {a | a ∈ Set.range (average_psd v).isHermitian.eigenvalues ∧ 0 < a} := by
  classical
  let ρ := average v
  let h := (average_psd v).isHermitian
  let q := h.eigenvalues
  let S := { i : E // q i ≠ 0 }
  have hcard : Fintype.card S = ρ.rank := by
    have hr : (diagonalReal q).rank = ρ.rank := by
      rw [show ρ = conjStarAlgAut ℂ _ h.eigenvectorUnitary (diagonalReal q) from
        h.spectral_theorem, rank_unitary_conj]
    rw [← hr, diagonalReal, rank_diagonal]
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight (fun i => by simp))
  let f : Fin ρ.rank ≃ S := (Fintype.equivFinOfCardEq hcard).symm
  let e : Fin ρ.rank ↪ E := f.toEmbedding.trans (Function.Embedding.subtype _)
  let C := selectColumns e
  let U := h.eigenvectorUnitary
  let p : Fin ρ.rank → ℝ := q ∘ e
  have he (i : E) (hi : q i ≠ 0) : i ∈ Set.range e :=
    ⟨f.symm ⟨i, hi⟩, congrArg Subtype.val (f.apply_symm_apply ⟨i, hi⟩)⟩
  have hu : (U : Matrix E E ℂ)ᴴ * (U : Matrix E E ℂ) = 1 := coe_star_mul_self U
  refine ⟨(U : Matrix E E ℂ) * C, p,
    isometry_comp _ _ hu (selectColumns_isometry e), ?_, ?_, ?_⟩
  · intro i
    exact lt_of_le_of_ne ((average_psd v).eigenvalues_nonneg (e i)) (f i).2.symm
  · rw [← pad_comp, select_pad_diagonal e q he, ← conj_eq_pad]
    exact h.spectral_theorem
  · ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨e i, rfl⟩,
        lt_of_le_of_ne ((average_psd v).eigenvalues_nonneg (e i)) (f i).2.symm⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩
      obtain ⟨j, hj⟩ := he i (ne_of_gt hi)
      exact ⟨j, congrArg q hj⟩

/-- The rank obstruction applies to every independent faithful finite bath. -/
theorem reset_requires_independent (v : X → E → ℂ)
    (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) {τ : Matrix B B ℂ} (hτ : τ.PosDef)
    (U : unitary (Total X B E)) (hU : Resets v w (conjStarAlgAut ℂ _ U (initial v τ))) :
    LinearIndependent ℂ v := by
  obtain ⟨V, p, hV, _, hρ, _⟩ := exists_support_frame v
  let A := conjStarAlgAut ℂ _ U (initial v τ)
  have hA : A.PosSemidef := by
    dsimp only [A]
    rw [conj_eq_pad]
    exact pad_psd _ (pad_psd _ (hτ.kronecker (mixed_posDef X)).posSemidef)
  obtain ⟨_, _, hout⟩ := reset_support v w hw V hV hρ hA hU
  have hr := reset_rank v hv hτ U
  change A.rank = _ at hr
  rw [hout] at hr
  have hd : Fintype.card B * Fintype.card X ≤ Fintype.card B * (average v).rank := by
    calc
      _ = _ := hr.symm
      _ ≤ Fintype.card (B × Fin (average v).rank) :=
        (rank_mul_le_left _ _).trans (rank_le_card_width _)
      _ = _ := by simp
  exact (average_full_rank_iff v).mp
    (le_antisymm (by rw [average_rank]; exact rank_le_card_width _)
      (Nat.le_of_mul_le_mul_left hd Fintype.card_pos))

/-- Independent records admit a faithful compression indexed by the labels. -/
theorem exists_label_support_frame (v : X → E → ℂ) (hli : LinearIndependent ℂ v) :
    ∃ (V : Matrix E X ℂ) (p : X → ℝ),
      Vᴴ * V = 1 ∧ (∀ i, 0 < p i) ∧ average v = pad V (diagonalReal p) ∧
      Set.range p = {a | a ∈ Set.range (average_psd v).isHermitian.eigenvalues ∧ 0 < a} := by
  obtain ⟨V, p, hV, hp, hρ, hs⟩ := exists_support_frame v
  let f : X ≃ Fin (average v).rank :=
    Fintype.equivFinOfCardEq ((average_full_rank_iff v).mpr hli).symm
  refine ⟨V.submatrix id f, p ∘ f, ?_, fun x => hp (f x), ?_, ?_⟩
  · rw [conjTranspose_submatrix]
    have hg : Vᴴ.submatrix f id * V.submatrix id f = (Vᴴ * V).submatrix f f :=
      Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl E) _
    rw [hg, hV, submatrix_one_equiv]
  · apply hρ.trans
    unfold pad
    rw [conjTranspose_submatrix]
    have hd : diagonalReal (p ∘ f) = (diagonalReal p).submatrix f f := by
      simpa only [diagonalReal, Function.comp_def] using
        (Matrix.submatrix_diagonal_equiv (fun i => (p i : ℂ)) f).symm
    rw [hd, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  · rw [Set.range_comp, f.range_eq_univ, Set.image_univ, hs]

omit [Nonempty B] in
/-- The range of the actual ambient output is the full reset sector over
the record span and the bath. -/
theorem reset_output_support_eq (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) (V : Matrix E X ℂ) (hV : Vᴴ * V = 1)
    {ρ : Matrix X X ℂ} (hρ : average v = pad V ρ) {τ : Matrix B B ℂ} (hτ : τ.PosDef)
    (U : unitary (Total X B E)) (hU : Resets v w (conjStarAlgAut ℂ _ U (initial v τ))) :
    LinearMap.range (conjStarAlgAut ℂ _ U (initial v τ)).mulVecLin =
      LinearMap.range (resetEmbedding w ((1 : Matrix B B ℂ) ⊗ₖ V)).mulVecLin := by
  obtain ⟨W, hW, _, hout⟩ := reduce_reset_unitary v hv w hw V hV hρ hτ U hU
  let K := (1 : Matrix B B ℂ) ⊗ₖ V
  let R := resetEmbedding w K
  have hR : Rᴴ * R = 1 := (resetEmbedding_gram w hw K).trans (bathEmbedding_isometry V hV)
  have hpd : (conjStarAlgAut ℂ _ W (τ ⊗ₖ mixed X)).PosDef := by
    rw [conjStarAlgAut_apply]
    exact (isUnit_coe.posDef_star_right_conjugate_iff).mpr (hτ.kronecker (mixed_posDef X))
  rw [hout, ← hW]
  exact range_pad R hR hpd

/-- In an implemented reset, the frame spans the records and its tensor
embedding is exactly the range of the joint output. -/
theorem reset_has_exact_record_support (v : X → E → ℂ)
    (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) {τ : Matrix B B ℂ} (hτ : τ.PosDef)
    (U : unitary (Total X B E)) (hU : Resets v w (conjStarAlgAut ℂ _ U (initial v τ))) :
    ∃ V : Matrix E X ℂ, Vᴴ * V = 1 ∧
      LinearMap.range V.mulVecLin = Submodule.span ℂ (Set.range v) ∧
      LinearMap.range (conjStarAlgAut ℂ _ U (initial v τ)).mulVecLin =
        LinearMap.range (resetEmbedding w ((1 : Matrix B B ℂ) ⊗ₖ V)).mulVecLin := by
  have hli := reset_requires_independent v hv w hw hτ U hU
  obtain ⟨V, p, hV, hp, hρ, _⟩ := exists_label_support_frame v hli
  refine ⟨V, hV, ?_, reset_output_support_eq v hv w hw V hV hρ hτ U hU⟩
  exact (range_pad V hV (diagonalReal_posDef p hp)).symm.trans
    ((congrArg (fun A : Matrix E E ℂ => LinearMap.range A.mulVecLin) hρ).symm.trans
      (average_support_eq_span v))

end Support

section Thermal

open D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity (thermalState)

variable {X E B : Type*} [Fintype X] [Fintype E] [Fintype B]
  [DecidableEq X] [DecidableEq E] [DecidableEq B] [Nonempty X] [Nonempty B]

/-- The independent bath input from a finite Hermitian Hamiltonian. -/
def thermalBath (β : ℝ) {H : Matrix B B ℂ} (hH : H.IsHermitian) : Matrix B B ℂ :=
  CStarMatrix.ofMatrix.symm (thermalState (CStarMatrix.ofMatrix H)
    (hamiltonian_selfAdjoint hH) β).1

theorem thermalBath_posDef (β : ℝ) {H : Matrix B B ℂ} (hH : H.IsHermitian) :
    (thermalBath β hH).PosDef := by
  rw [thermalBath, thermalState_eq_gibbsBath β hH, gibbsBath, conjStarAlgAut_apply]
  exact (isUnit_coe.posDef_star_right_conjugate_iff).mpr
    (diagonalReal_posDef _ (gibbsWeight_pos β _))

/-- A genuine ambient reset with the given Hamiltonian obeys both reduced bounds. -/
theorem thermal_reset_lower_bound {β : ℝ} (hβ : 0 < β)
    (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1)
    (V : Matrix E X ℂ) (hV : Vᴴ * V = 1) {ρ : Matrix X X ℂ} (hρ : ρ.PosDef)
    (havg : average v = pad V ρ) {H : Matrix B B ℂ} (hH : H.IsHermitian)
    (U : unitary (Total X B E))
    (hU : Resets v w (conjStarAlgAut ℂ _ U (initial v (thermalBath β hH)))) :
    requiredWidth β hρ ≤ energyWidth hH.eigenvalues ∧
      (Fintype.card X : ℝ) * maxValue hρ.isHermitian.eigenvalues ≤ Fintype.card B := by
  obtain ⟨W, hW⟩ :=
    (reset_unitary_orbit_iff v hv w hw V hV havg (thermalBath_posDef β hH)).mp ⟨U, hU⟩
  exact thermal_bandwidth_lower_bound hβ hH hρ W hW

/-- The Gibbs bath and reduced swap at the optimum lift to the ambient matrices. -/
theorem thermal_reset_attained {β : ℝ} (hβ : 0 < β)
    (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1)
    (V : Matrix E X ℂ) (hV : Vᴴ * V = 1) {ρ : Matrix X X ℂ} (hρ : ρ.PosDef)
    (havg : average v = pad V ρ) :
    ∃ (H : Matrix X X ℂ) (hH : H.IsHermitian) (U : unitary (Total X X E)),
      energyWidth hH.eigenvalues = requiredWidth β hρ ∧
      (U : Total X X E) * recordEmbedding v =
        resetEmbedding w ((1 : Matrix X X ℂ) ⊗ₖ V) *
          (↑(tensorSwap (M := X)) : Matrix (X × X) (X × X) ℂ) ∧
      Resets v w (conjStarAlgAut ℂ _ U (initial v (thermalBath β hH))) := by
  have htr : ρ.trace = 1 := by rw [← trace_pad V hV, ← havg, average_trace v hv]
  obtain ⟨H, hH, hwidth, hswap⟩ := thermal_bandwidth_attained hβ hρ htr
  obtain ⟨U, hU, hreset⟩ :=
    lift_reduced_unitary v hv w hw V hV havg (thermalBath β hH) tensorSwap hswap
  exact ⟨H, hH, U, hwidth, hU, hreset⟩

/-- The minimum thermal bandwidth and the separate bath dimension bound, expressed
using exactly the positive eigenvalues of the ambient average record. -/
theorem thermal_reset_minimum {β : ℝ} (hβ : 0 < β)
    (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) (hli : LinearIndependent ℂ v) :
    ∃ p : X → ℝ,
      (∀ i, 0 < p i) ∧
      Set.range p = {a | a ∈ Set.range (average_psd v).isHermitian.eigenvalues ∧ 0 < a} ∧
      (∀ (Bath : Type*) [Fintype Bath] [DecidableEq Bath] [Nonempty Bath]
        {H : Matrix Bath Bath ℂ} (hH : H.IsHermitian) (U : unitary (Total X Bath E)),
        Resets v w (conjStarAlgAut ℂ _ U (initial v (thermalBath β hH))) →
        β⁻¹ * Real.log (maxValue p / minValue p) ≤ energyWidth hH.eigenvalues ∧
        (Fintype.card X : ℝ) * maxValue p ≤ Fintype.card Bath) ∧
      ∃ (H : Matrix X X ℂ) (hH : H.IsHermitian) (U : unitary (Total X X E)),
        energyWidth hH.eigenvalues = β⁻¹ * Real.log (maxValue p / minValue p) ∧
        Resets v w (conjStarAlgAut ℂ _ U (initial v (thermalBath β hH))) := by
  obtain ⟨V, p, hV, hp, hρ, hs⟩ := exists_label_support_frame v hli
  have hpd := diagonalReal_posDef p hp
  obtain ⟨hmin, hmax⟩ := diagonalReal_endpoints p hpd.isHermitian
  have hwidth : requiredWidth β hpd = β⁻¹ * Real.log (maxValue p / minValue p) := by
    unfold requiredWidth
    rw [hmin, hmax]
  refine ⟨p, hp, hs, ?_, ?_⟩
  · intro Bath _ _ _ H hH U hU
    simpa only [hwidth, hmax] using thermal_reset_lower_bound hβ v hv w hw V hV hpd hρ hH U hU
  · obtain ⟨H, hH, U, hW, _, hU⟩ := thermal_reset_attained hβ v hv w hw V hV hpd hρ
    exact ⟨H, hH, U, hW.trans hwidth, hU⟩

/-- Linear independence is exactly feasibility over finite Gibbs baths. A bath
indexed by the labels suffices whenever a faithful bath can implement the reset. -/
theorem independent_iff_exists_gibbs_reset {β : ℝ} (hβ : 0 < β)
    (v : X → E → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) :
    LinearIndependent ℂ v ↔
      ∃ (H : Matrix X X ℂ) (hH : H.IsHermitian) (U : unitary (Total X X E)),
        Resets v w (conjStarAlgAut ℂ _ U (initial v (thermalBath β hH))) := by
  constructor
  · intro hli
    obtain ⟨V, p, hV, hp, havg, _⟩ := exists_label_support_frame v hli
    obtain ⟨H, hH, U, _, _, hU⟩ :=
      thermal_reset_attained hβ v hv w hw V hV (diagonalReal_posDef p hp) havg
    exact ⟨H, hH, U, hU⟩
  · rintro ⟨H, hH, U, hU⟩
    exact reset_requires_independent v hv w hw (thermalBath_posDef β hH) U hU

end Thermal

section QubitCompatibility

open ExactQubitBathErasure in
/-- In the qubit development's original register order, its orbit theorem
applies directly to any admissible full output after taking the label trace. -/
theorem qubit_output_orbit_iff (v : Qubit → Qubit → ℂ) (r : ℝ)
    (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    {A : ExactQubitBathErasure.Total Qubit} (hA : A.PosSemidef) (h : Erases v A) :
    (∃ U : unitary (ExactQubitBathErasure.Total Qubit),
      conjStarAlgAut ℂ _ U (initialRecords v r) = A) ↔
      ∃ W : unitary TwoQubits,
        conjStarAlgAut ℂ _ W (supportedInput r) = partialTraceLeft A := by
  have hfac := pure_reset_factors hA h.1
  have hρ := (partialTraceLeft_posSemidef hA).isHermitian
  conv_lhs => enter [1, U]; rw [hfac]
  exact ExactQubitBathErasure.reset_unitary_orbit_iff v r hv hρ

end QubitCompatibility

end

end LabelResetBandwidth
