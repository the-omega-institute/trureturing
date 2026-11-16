/- GID: D5/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation
   generality: I
   mirror-B: D5/B/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation.claim; result=D5/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation.result; claim=D5/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation.claim
   digest: Norming commutation does not force local flatness of a commutator line. -/

/-
Larotonda and Rey, arXiv:2302.05957v1, Problem 3.13, page 26.
The polar-supremum construction here is restricted to dimension two.
admission_basis: open-problem-resolution (#26538; Refuted).
escape_witness: none.
Direct frozen dependencies: D5/S3/Quantum/Fibers/ReadoutOrthogonalEquivalence.centeredEffect
statement_id: sha256:ef79c345355d7edb0ae3f87e63505a6830869d8bcb5442c04f0247a3431ff57e.
The skew-adjoint convention is inlined in the claim; proofs use Mathlib skewAdjoint.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Per-declaration classification (all escape_witness: none):
pairing: proof_shape: bind-only; consumers: IsNorming,dualNorm,norming_bound,norming_central,norming_traceless,pairing_add,pairing_smul; Direct frozen dependencies: none.
IsAdInvariantFinsler: proof_shape: bind-only; consumers: claim; Direct frozen dependencies: none.
dualNorm: proof_shape: bind-only; consumers: IsNorming,norming_bound,norming_central,norming_traceless; Direct frozen dependencies: none.
IsNorming: proof_shape: bind-only; consumers: claim,norming_central,norming_traceless,result; Direct frozen dependencies: none.
SpectralData: proof_shape: bind-only; consumers: claim,codiagonal,result; Direct frozen dependencies: none.
codiagonal: proof_shape: bind-only; consumers: claim,result; Direct frozen dependencies: none.
claim: proof_shape: bind-only; consumers: result; Direct frozen dependencies: none.
weight: proof_shape: bind-only; consumers: bodyNorm,bodyNorm_V,bodyNorm_add,bodyNorm_conj,bodyNorm_le,bodyNorm_quadratic,bodyNorm_smul,bodyNorm_strict,bodyNorm_zero,cent_le,rest_le,weight_bdd,weight_bound,weight_le,weight_smul; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm: proof_shape: bind-only; consumers: bodyNorm_V,bodyNorm_add,bodyNorm_admissible,bodyNorm_conj,bodyNorm_eq_zero,bodyNorm_smul,bodyNorm_strict,bodyNorm_zero,cent_le,line_strict,norming_bound,norming_central,norming_traceless,rest_le,result; Direct frozen dependencies: centeredEffect (identity above).
center_formula: proof_shape: bind-only; consumers: bodyNorm_eq_zero,bodyNorm_quadratic,cent_V,cent_conj,cent_line,line_radius,norming_central,rest_V; Direct frozen dependencies: none.
denom_pos: proof_shape: bind-only; consumers: bodyNorm_V,bodyNorm_add,bodyNorm_quadratic,bodyNorm_strict,weight_bound; Direct frozen dependencies: none.
coeff_nonneg: proof_shape: bind-only; consumers: bodyNorm_add; Direct frozen dependencies: none.
weight_bound: proof_shape: bind-only; consumers: weight_bdd; Direct frozen dependencies: centeredEffect (identity above).
weight_bdd: proof_shape: bind-only; consumers: weight_le; Direct frozen dependencies: centeredEffect (identity above).
weight_le: proof_shape: bind-only; consumers: bodyNorm_add,bodyNorm_smul,bodyNorm_strict,cent_le,rest_le; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_le: proof_shape: bind-only; consumers: bodyNorm_V,bodyNorm_add,bodyNorm_quadratic,bodyNorm_smul,bodyNorm_zero; Direct frozen dependencies: centeredEffect (identity above).
cent_le: proof_shape: bind-only; consumers: bodyNorm_V,bodyNorm_admissible,bodyNorm_eq_zero,bodyNorm_zero; Direct frozen dependencies: centeredEffect (identity above).
rest_le: proof_shape: bind-only; consumers: bodyNorm_eq_zero; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_zero: proof_shape: bind-only; consumers: bodyNorm_admissible,bodyNorm_eq_zero,bodyNorm_smul; Direct frozen dependencies: centeredEffect (identity above).
cent_add: proof_shape: bind-only; consumers: bodyNorm_add,bodyNorm_quadratic,cent_line; Direct frozen dependencies: none.
rest_add: proof_shape: bind-only; consumers: bodyNorm_add,bodyNorm_quadratic; Direct frozen dependencies: centeredEffect (identity above).
cent_smul: proof_shape: bind-only; consumers: bodyNorm_quadratic,cent_line,weight_smul; Direct frozen dependencies: none.
rest_smul: proof_shape: bind-only; consumers: bodyNorm_quadratic,weight_smul; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_add: proof_shape: bind-only; consumers: bodyNorm_admissible; Direct frozen dependencies: centeredEffect (identity above).
weight_smul: proof_shape: bind-only; consumers: bodyNorm_smul; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_smul: proof_shape: bind-only; consumers: bodyNorm_admissible,norming_bound; Direct frozen dependencies: centeredEffect (identity above).
trace_conj: proof_shape: bind-only; consumers: cent_conj,rest_conj; Direct frozen dependencies: none.
cent_conj: proof_shape: bind-only; consumers: bodyNorm_conj; Direct frozen dependencies: none.
rest_conj: proof_shape: bind-only; consumers: bodyNorm_conj; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_conj: proof_shape: bind-only; consumers: bodyNorm_admissible; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_eq_zero: proof_shape: bind-only; consumers: bodyNorm_admissible; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_admissible: proof_shape: bind-only; consumers: result; Direct frozen dependencies: centeredEffect (identity above).
J: proof_shape: bind-only; consumers: V,skew_J,skew_V; Direct frozen dependencies: none.
K: proof_shape: bind-only; consumers: V,cent_V,line_radius,norm_K,norm_rest_V,norming_central,rest_V,skew_K,skew_V; Direct frozen dependencies: none.
X: proof_shape: bind-only; consumers: cent_line,line_radius,line_strict,norming_central,result,skew_X; Direct frozen dependencies: none.
T: proof_shape: bind-only; consumers: norming_central,skew_T; Direct frozen dependencies: none.
V: proof_shape: bind-only; consumers: bodyNorm_V,bodyNorm_quadratic,cent_V,cent_line,line_radius,line_strict,norm_rest_V,norming_central,norming_traceless,rest_V,result; Direct frozen dependencies: none.
skew_J: proof_shape: bind-only; consumers: skew_V; Direct frozen dependencies: none.
skew_K: proof_shape: bind-only; consumers: norming_central,skew_V; Direct frozen dependencies: none.
skew_X: proof_shape: bind-only; consumers: norming_central,result; Direct frozen dependencies: none.
skew_T: proof_shape: bind-only; consumers: norming_central; Direct frozen dependencies: none.
skew_V: proof_shape: bind-only; consumers: norming_traceless,result; Direct frozen dependencies: none.
cent_V: proof_shape: bind-only; consumers: bodyNorm_V,bodyNorm_quadratic,cent_line,rest_V; Direct frozen dependencies: none.
rest_V: proof_shape: bind-only; consumers: norm_rest_V; Direct frozen dependencies: centeredEffect (identity above).
norm_K: proof_shape: bind-only; consumers: norm_rest_V; Direct frozen dependencies: none.
norm_rest_V: proof_shape: bind-only; consumers: bodyNorm_V,bodyNorm_quadratic; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_V: proof_shape: bind-only; consumers: line_strict,norming_traceless; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_quadratic: proof_shape: bind-only; consumers: norming_traceless; Direct frozen dependencies: centeredEffect (identity above).
pairing_add: proof_shape: bind-only; consumers: norming_traceless; Direct frozen dependencies: none.
pairing_smul: proof_shape: bind-only; consumers: norming_bound,norming_traceless; Direct frozen dependencies: none.
norming_bound: proof_shape: bind-only; consumers: norming_traceless; Direct frozen dependencies: centeredEffect (identity above).
norming_traceless: proof_shape: bind-only; consumers: norming_central; Direct frozen dependencies: centeredEffect (identity above).
norming_central: proof_shape: bind-only; consumers: result; Direct frozen dependencies: centeredEffect (identity above).
bodyNorm_strict: proof_shape: bind-only; consumers: line_strict; Direct frozen dependencies: centeredEffect (identity above).
cent_line: proof_shape: bind-only; consumers: line_radius,line_strict; Direct frozen dependencies: none.
line_radius: proof_shape: bind-only; consumers: line_strict; Direct frozen dependencies: centeredEffect (identity above).
line_strict: proof_shape: bind-only; consumers: result; Direct frozen dependencies: centeredEffect (identity above).
result: proof_shape: bind-only; consumers: terminal result; Direct frozen dependencies: centeredEffect (identity above).
-/

import D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence

/-! A polar-supremum counterexample to norming commutation implying local flatness. -/

set_option autoImplicit false
set_option linter.style.longLine false
namespace D5.S3.HilbertOperators.LarotondaReyNormingFlatnessRefutation

open scoped BigOperators ComplexConjugate
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence (centeredEffect)

/-- The real trace pairing used in the source to identify the dual of u(n). -/
def pairing {n : ℕ} (N Y : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -((Matrix.trace (N * Y)).re)

/-- The four defining conditions of an Ad-invariant Finsler norm. -/
def IsAdInvariantFinsler {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop :=
  F 0 = 0 ∧
  (∀ Y, Y ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) → 0 ≤ F Y) ∧
  (∀ Y, Y ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) → (F Y = 0 ↔ Y = 0)) ∧
  (∀ Y Z, Y ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) → Z ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) → F (Y + Z) ≤ F Y + F Z) ∧
  (∀ (r : ℝ) Y, 0 ≤ r → Y ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) → F (r • Y) = r * F Y) ∧
  (∀ (U Y), U ∈ Matrix.unitaryGroup (Fin n) ℂ → Y ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) →
    F (U * Y * star U) = F Y)

/-- The dual norm from the source's trace-duality definition. -/
noncomputable def dualNorm {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ → ℝ) (N : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ Y : Matrix (Fin n) (Fin n) ℂ, Y ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) ∧ F Y ≤ 1 ∧ r = pairing N Y}

/-- A matrix representing a unit norming functional of V. -/
def IsNorming {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ → ℝ) (V N : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  N ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) ∧ dualNorm F N = 1 ∧ pairing N V = F V

/-- A finite spectral-block decomposition V = i Σ v_j P_j. -/
structure SpectralData (n : ℕ) where
  blocks : ℕ
  positiveBlocks : 0 < blocks
  value : Fin blocks → ℝ
  projection : Fin blocks → Matrix (Fin n) (Fin n) ℂ
  V : Matrix (Fin n) (Fin n) ℂ
  distinct : ∀ i j, i ≠ j → value i ≠ value j
  selfAdjointProjection : ∀ i, star (projection i) = projection i
  idempotentProjection : ∀ i, projection i * projection i = projection i
  orthogonalProjection : ∀ i j, i ≠ j → projection i * projection j = 0
  nonzeroProjection : ∀ i, projection i ≠ 0
  completeProjection : ∑ i, projection i = 1
  decomposition : V = (Complex.I : ℂ) • ∑ i, (value i : ℂ) • projection i
  skewV : V ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ)

/-- The source's codiagonal part X_C = Σ_{j ≠ k} P_j X P_k. -/
noncomputable def codiagonal {n : ℕ} (D : SpectralData n) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j, ∑ k, if D.value j ≠ D.value k then D.projection j * X * D.projection k else 0

/-- Problem 3.13: the commutation condition for every norming N implies local
flatness of the straight commutator line. The existential decomposition clause
records that the source's spectral-block object and nonempty norming set are
defined for every V. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ F : Matrix (Fin n) (Fin n) ℂ → ℝ, IsAdInvariantFinsler F →
    ∀ V : Matrix (Fin n) (Fin n) ℂ, V ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) →
      (∃ N : Matrix (Fin n) (Fin n) ℂ, IsNorming F V N) ∧
      (∃ D : SpectralData n, D.V = V) ∧
      ∀ D : SpectralData n, D.V = V →
      ∀ X : Matrix (Fin n) (Fin n) ℂ, X ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) →
        (∀ N : Matrix (Fin n) (Fin n) ℂ, IsNorming F V N →
          N * codiagonal D X = codiagonal D X * N) →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ s : ℝ, |s| < δ →
            F (V + s • (X * V - V * X)) = F V

open scoped Matrix.Norms.L2Operator
noncomputable section

private def weight (q : (Set.Icc (0 : ℝ) 1)) (Y : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ((1 - (q : ℝ)^2) * ‖(Finset.univ.expect ∘ Matrix.diag) Y‖ + 2 * (q : ℝ) * ‖centeredEffect Y‖) /
    (1 + (q : ℝ)^2 + (q : ℝ))

private def bodyNorm (Y : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := sSup (Set.range (fun q : (Set.Icc (0 : ℝ) 1) => weight q Y))

private theorem center_formula (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    (Finset.univ.expect ∘ Matrix.diag) Y = Matrix.trace Y / 2 := by
  change (𝔼 i : Fin 2, Y i i) = _
  rw [Fintype.expect_eq_sum_div_card]
  rfl

private theorem denom_pos (q : (Set.Icc (0 : ℝ) 1)) : 0 < 1 + (q : ℝ)^2 + (q : ℝ) := by
  nlinarith [q.property.1, sq_nonneg (q : ℝ)]

private theorem coeff_nonneg (q : (Set.Icc (0 : ℝ) 1)) : 0 ≤ 1 - (q : ℝ)^2 := by
  exact sub_nonneg.mpr ((sq_le_one_iff₀ q.property.1).mpr q.property.2)

private theorem weight_bound (q : (Set.Icc (0 : ℝ) 1)) (Y : Matrix (Fin 2) (Fin 2) ℂ) : weight q Y ≤ ‖(Finset.univ.expect ∘ Matrix.diag) Y‖ + 2 * ‖centeredEffect Y‖ := by
  unfold weight
  apply (div_le_iff₀ (denom_pos q)).2
  nlinarith [norm_nonneg ((Finset.univ.expect ∘ Matrix.diag) Y), norm_nonneg (centeredEffect Y), q.property.1,
    q.property.2, sq_nonneg (q : ℝ),
    mul_nonneg (sq_nonneg (q : ℝ)) (norm_nonneg ((Finset.univ.expect ∘ Matrix.diag) Y)),
    mul_nonneg (sq_nonneg (q : ℝ)) (norm_nonneg (centeredEffect Y)),
    mul_nonneg q.property.1 (norm_nonneg ((Finset.univ.expect ∘ Matrix.diag) Y))]

private theorem weight_bdd (Y : Matrix (Fin 2) (Fin 2) ℂ) : BddAbove (Set.range (fun q : (Set.Icc (0 : ℝ) 1) => weight q Y)) := by
  exact ⟨‖(Finset.univ.expect ∘ Matrix.diag) Y‖ + 2 * ‖centeredEffect Y‖, by rintro _ ⟨q,rfl⟩; exact weight_bound q Y⟩

private theorem weight_le (q : (Set.Icc (0 : ℝ) 1)) (Y : Matrix (Fin 2) (Fin 2) ℂ) : weight q Y ≤ bodyNorm Y := by
  exact le_csSup (weight_bdd Y) (Set.mem_range_self q)

private theorem bodyNorm_le (Y : Matrix (Fin 2) (Fin 2) ℂ) (b : ℝ) (h : ∀ q : (Set.Icc (0 : ℝ) 1), weight q Y ≤ b) : bodyNorm Y ≤ b := by
  exact csSup_le ⟨weight ⟨0, by norm_num⟩ Y, Set.mem_range_self _⟩ (by rintro _ ⟨q,rfl⟩; exact h q)

private theorem cent_le (Y : Matrix (Fin 2) (Fin 2) ℂ) : ‖(Finset.univ.expect ∘ Matrix.diag) Y‖ ≤ bodyNorm Y := by
  simpa [weight] using weight_le ⟨0, by norm_num⟩ Y

private theorem rest_le (Y : Matrix (Fin 2) (Fin 2) ℂ) : 2 * ‖centeredEffect Y‖ / 3 ≤ bodyNorm Y := by
  convert weight_le ⟨1, by norm_num⟩ Y using 1 <;> norm_num [weight]

private theorem bodyNorm_zero : bodyNorm 0 = 0 := by
  apply le_antisymm
  · apply bodyNorm_le; intro q; simp [weight, centeredEffect]
  · simpa [center_formula] using cent_le 0

private theorem cent_add (Y Z : Matrix (Fin 2) (Fin 2) ℂ) : (Finset.univ.expect ∘ Matrix.diag) (Y+Z) = (Finset.univ.expect ∘ Matrix.diag) Y + (Finset.univ.expect ∘ Matrix.diag) Z := by
  exact Finset.expect_add_distrib Finset.univ (fun i => Y i i) (fun i => Z i i)

private theorem rest_add (Y Z : Matrix (Fin 2) (Fin 2) ℂ) : centeredEffect (Y+Z) = centeredEffect Y + centeredEffect Z := by
  simp [centeredEffect, add_div, add_smul]; abel

private theorem cent_smul (r : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) : (Finset.univ.expect ∘ Matrix.diag) (r • Y) = r • (Finset.univ.expect ∘ Matrix.diag) Y := by
  exact (Finset.smul_expect r Finset.univ (fun i => Y i i)).symm

private theorem rest_smul (r : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) : centeredEffect (r • Y) = r • centeredEffect Y := by
  ext i j; simp [centeredEffect, Matrix.trace_smul, smul_sub, Matrix.smul_apply]; ring

private theorem bodyNorm_add (Y Z : Matrix (Fin 2) (Fin 2) ℂ) : bodyNorm (Y+Z) ≤ bodyNorm Y + bodyNorm Z := by
  apply bodyNorm_le; intro q
  calc
    weight q (Y+Z) ≤ weight q Y + weight q Z := by
      unfold weight
      rw [cent_add, rest_add, ← add_div]
      apply (div_le_div_iff_of_pos_right (denom_pos q)).2
      have h1 := mul_le_mul_of_nonneg_left (norm_add_le ((Finset.univ.expect ∘ Matrix.diag) Y) ((Finset.univ.expect ∘ Matrix.diag) Z)) (coeff_nonneg q)
      have h2 := mul_le_mul_of_nonneg_left (norm_add_le (centeredEffect Y) (centeredEffect Z)) (by nlinarith [q.property.1] : 0 ≤ 2*(q:ℝ))
      nlinarith
    _ ≤ bodyNorm Y + bodyNorm Z := add_le_add (weight_le q Y) (weight_le q Z)

private theorem weight_smul (r : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) (q : (Set.Icc (0 : ℝ) 1)) : weight q (r • Y) = |r| * weight q Y := by
  simp only [weight, cent_smul, rest_smul, norm_smul, Real.norm_eq_abs]
  ring

private theorem bodyNorm_smul (r : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) : bodyNorm (r • Y) = |r| * bodyNorm Y := by
  apply le_antisymm
  · apply bodyNorm_le; intro q
    rw [weight_smul]
    exact mul_le_mul_of_nonneg_left (weight_le q Y) (abs_nonneg r)
  · by_cases hr : r = 0
    · simp [hr, bodyNorm_zero]
    · have h := bodyNorm_le Y (bodyNorm (r • Y) / |r|) (fun q => by
        apply (le_div_iff₀ (abs_pos.mpr hr)).2
        simpa [weight_smul, mul_comm] using weight_le q (r • Y))
      simpa [mul_comm] using (le_div_iff₀ (abs_pos.mpr hr)).mp h

private theorem trace_conj (U Y : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix.trace (U * Y * star U) = Matrix.trace Y := by
  exact Matrix.trace_units_conj (Unitary.toUnits ⟨U,hU⟩) Y

private theorem cent_conj (U Y : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (Finset.univ.expect ∘ Matrix.diag) (U * Y * star U) = (Finset.univ.expect ∘ Matrix.diag) Y := by
  simp only [center_formula, trace_conj U Y hU]

private theorem rest_conj (U Y : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    centeredEffect (U * Y * star U) =
      U * centeredEffect Y * star U := by
  simp only [centeredEffect,
    trace_conj U Y hU, mul_sub, sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_one, Matrix.mem_unitaryGroup_iff.mp hU]

private theorem bodyNorm_conj (U Y : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    bodyNorm (U * Y * star U) = bodyNorm Y := by
  have hstar : star U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := Unitary.star_mem hU
  have hn : ‖centeredEffect (U * Y * star U)‖ = ‖centeredEffect Y‖ := by
    rw [rest_conj U Y hU, CStarRing.norm_mul_mem_unitary _ hstar,
      CStarRing.norm_mem_unitary_mul _ hU]
  have hw : (fun q : (Set.Icc (0 : ℝ) 1) => weight q (U * Y * star U)) = (fun q : (Set.Icc (0 : ℝ) 1) => weight q Y) := by
    funext q
    simp only [weight, cent_conj U Y hU, hn]
  unfold bodyNorm
  rw [hw]

private theorem bodyNorm_eq_zero (Y : Matrix (Fin 2) (Fin 2) ℂ) : bodyNorm Y = 0 ↔ Y = 0 := by
  constructor
  · intro h
    have hc : (Finset.univ.expect ∘ Matrix.diag) Y = 0 := norm_eq_zero.mp (le_antisymm (by simpa [h] using cent_le Y) (norm_nonneg _))
    have hr : centeredEffect Y = 0 := norm_eq_zero.mp (by have := rest_le Y; rw [h] at this; nlinarith [norm_nonneg (centeredEffect Y)])
    have hcTrace : Matrix.trace Y / 2 = 0 := by simpa only [center_formula] using hc
    simpa [centeredEffect, hcTrace] using hr
  · rintro rfl; exact bodyNorm_zero

private theorem bodyNorm_admissible : IsAdInvariantFinsler bodyNorm := by
  refine ⟨bodyNorm_zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y _; exact (norm_nonneg ((Finset.univ.expect ∘ Matrix.diag) Y)).trans (cent_le Y)
  · intro Y _; exact bodyNorm_eq_zero Y
  · intro Y Z _ _; exact bodyNorm_add Y Z
  · intro r Y hr _; simpa [abs_of_nonneg hr] using bodyNorm_smul r Y
  · intro U Y hU _; exact bodyNorm_conj U Y hU

private def J : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)
private def K : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]
private def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
private def T : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]
private def V : Matrix (Fin 2) (Fin 2) ℂ := J + (1/2 : ℝ) • K

private theorem skew_J : J ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
  change star J = -J; ext i j; fin_cases i <;> fin_cases j <;> simp [J, Matrix.star_apply]

private theorem skew_K : K ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
  change star K = -K; ext i j; fin_cases i <;> fin_cases j <;> simp [K, Matrix.star_apply]

private theorem skew_X : X ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
  change star X = -X; ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.star_apply]

private theorem skew_T : T ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
  change star T = -T; ext i j; fin_cases i <;> fin_cases j <;> simp [T, Matrix.star_apply]

private theorem skew_V : V ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
  exact (skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ)).add_mem skew_J (skewAdjoint.smul_mem (1/2 : ℝ) skew_K)

private theorem cent_V : (Finset.univ.expect ∘ Matrix.diag) V = Complex.I := by
  rw [center_formula]
  norm_num [V, J, K, Matrix.trace_fin_two]

private theorem rest_V : centeredEffect V = (1/2 : ℝ) • K := by
  change V - (Matrix.trace V / 2) • 1 = _
  rw [← center_formula V, cent_V]; simp [V, J]

private theorem norm_K : ‖K‖ = 1 := by
  have h : star K * K = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  have hh := CStarRing.norm_star_mul_self (x := K)
  rw [h, CStarRing.norm_one] at hh
  nlinarith [norm_nonneg K]

private theorem norm_rest_V : ‖centeredEffect V‖ = 1/2 := by
  rw [rest_V, norm_smul, norm_K]; norm_num

private theorem bodyNorm_V : bodyNorm V = 1 := by
  apply le_antisymm
  · apply bodyNorm_le; intro q
    unfold weight
    rw [cent_V, norm_rest_V, Complex.norm_I]
    apply (div_le_iff₀ (denom_pos q)).2
    nlinarith [sq_nonneg (q : ℝ)]
  · have h := cent_le V
    rw [cent_V, Complex.norm_I] at h
    exact h

private theorem bodyNorm_quadratic (W : Matrix (Fin 2) (Fin 2) ℂ) (hc : (Finset.univ.expect ∘ Matrix.diag) W = 0) (e : ℝ) :
    bodyNorm (V + e • W) ≤ 1 + e^2 * ‖W‖^2 := by
  have hcent : (Finset.univ.expect ∘ Matrix.diag) (V + e • W) = Complex.I := by
    rw [cent_add, cent_smul, cent_V, hc, smul_zero, add_zero]
  have hrest : ‖centeredEffect (V + e • W)‖ ≤ 1/2 + |e| * ‖W‖ := by
    rw [rest_add, rest_smul]
    have hh : centeredEffect W = W := by
      have hcTrace : Matrix.trace W / 2 = 0 := by simpa only [center_formula] using hc
      simp [centeredEffect, hcTrace]
    simpa [hh, norm_rest_V, norm_smul, Real.norm_eq_abs] using norm_add_le (centeredEffect V) (e • centeredEffect W)
  apply bodyNorm_le; intro q
  unfold weight
  rw [hcent, Complex.norm_I]
  apply (div_le_iff₀ (denom_pos q)).2
  have hmul := mul_le_mul_of_nonneg_left hrest (by nlinarith [q.property.1] : 0 ≤ 2*(q:ℝ))
  have hsq := sq_nonneg ((q:ℝ) - |e| * ‖W‖)
  have heq : (|e| * ‖W‖)^2 = e^2 * ‖W‖^2 := by rw [mul_pow, sq_abs]
  have hp1 := mul_nonneg (sq_nonneg (|e| * ‖W‖)) (sq_nonneg (q:ℝ))
  have hp2 := mul_nonneg (sq_nonneg (|e| * ‖W‖)) q.property.1
  simp only [mul_pow, sq_abs] at hp1 hp2
  nlinarith

private theorem pairing_add (N Y Z : Matrix (Fin 2) (Fin 2) ℂ) : pairing N (Y+Z) = pairing N Y + pairing N Z := by
  simp [pairing, mul_add, Matrix.trace_add]; ring

private theorem pairing_smul (N Y : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) : pairing N (r • Y) = r * pairing N Y := by
  simp [pairing, Matrix.trace_smul]

private theorem norming_bound (N Y : Matrix (Fin 2) (Fin 2) ℂ) (hN : dualNorm bodyNorm N = 1)
    (hY : Y ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) (b : ℝ) (hb : 0 < b) (hF : bodyNorm Y ≤ b) : pairing N Y ≤ b := by
  have hbounded : BddAbove {r : ℝ | ∃ Y : Matrix (Fin 2) (Fin 2) ℂ, Y ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) ∧ bodyNorm Y ≤ 1 ∧ r = pairing N Y} := by
    by_contra h
    unfold dualNorm at hN
    rw [csSup_of_not_bddAbove h] at hN
    simp at hN
  have hy : b⁻¹ • Y ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
    exact skewAdjoint.smul_mem (b⁻¹ : ℝ) hY
  have hf : bodyNorm (b⁻¹ • Y) ≤ 1 := by
    rw [bodyNorm_smul, abs_of_pos (inv_pos.mpr hb)]
    exact (inv_mul_le_iff₀ hb).2 (by simpa using hF)
  have hle := le_csSup hbounded (show pairing N (b⁻¹ • Y) ∈ {r : ℝ | ∃ Y : Matrix (Fin 2) (Fin 2) ℂ, Y ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) ∧ bodyNorm Y ≤ 1 ∧ r = pairing N Y} from ⟨_,hy,hf,rfl⟩)
  change pairing N (b⁻¹ • Y) ≤ dualNorm bodyNorm N at hle
  rw [hN, pairing_smul] at hle
  simpa using (inv_mul_le_iff₀ hb).mp hle

private theorem norming_traceless (N W : Matrix (Fin 2) (Fin 2) ℂ) (hN : IsNorming bodyNorm V N)
    (hW : W ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) (hc : (Finset.univ.expect ∘ Matrix.diag) W = 0) : pairing N W = 0 := by
  have hbase : pairing N V = 1 := hN.2.2.trans bodyNorm_V
  have hquad : ∀ e : ℝ, e * pairing N W ≤ e^2 * ‖W‖^2 := by
    intro e
    have hY : V + e • W ∈ skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := (skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ)).add_mem skew_V (skewAdjoint.smul_mem e hW)
    have h := norming_bound N (V+e•W) hN.2.1 hY (1+e^2*‖W‖^2)
      (by positivity) (bodyNorm_quadratic W hc e)
    rw [pairing_add, pairing_smul, hbase] at h
    linarith
  have hp : 0 < ‖W‖^2 + 1 := by positivity
  have h := hquad (pairing N W / (‖W‖^2 + 1))
  have hi : 0 < (‖W‖^2 + 1)^2 := sq_pos_of_pos hp
  have h' := mul_le_mul_of_nonneg_right h hi.le
  field_simp at h'
  nlinarith [sq_nonneg (pairing N W)]

private theorem norming_central (N : Matrix (Fin 2) (Fin 2) ℂ) (hN : IsNorming bodyNorm V N) :
    ∃ z : ℂ, N = z • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hk := norming_traceless N K hN skew_K (by rw [center_formula]; norm_num [K])
  have hx := norming_traceless N X hN skew_X (by rw [center_formula]; norm_num [X])
  have ht := norming_traceless N T hN skew_T (by rw [center_formula]; norm_num [T])
  simp [pairing, K, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re] at hk
  simp [pairing, X, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at hx
  simp [pairing, T, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re] at ht
  have hs : star N = -N := hN.1
  have hs00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hs
  have hs11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hs
  have hs01r := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) hs
  have hs01i := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) hs
  simp [Matrix.star_apply] at hs00 hs11 hs01r hs01i
  refine ⟨N 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Matrix.smul_apply] <;> linarith

private theorem bodyNorm_strict (Y : Matrix (Fin 2) (Fin 2) ℂ) (hc : ‖(Finset.univ.expect ∘ Matrix.diag) Y‖ = 1) (hr : 1/2 < ‖centeredEffect Y‖) :
    1 < bodyNorm Y := by
  let d : ℝ := ‖centeredEffect Y‖ - 1/2
  let b : ℝ := 2 * ‖centeredEffect Y‖ + 1
  have hd : 0 < d := by exact sub_pos.mpr hr
  have hb : 2 < b := by dsimp [b]; linarith
  have hq0 : 0 < d/b := div_pos hd (by linarith)
  have hq1 : d/b ≤ 1 := (div_le_iff₀ (by linarith : 0 < b)).2 (by dsimp [d,b]; linarith)
  have hqd : d/b < d := (div_lt_iff₀ (by linarith : 0 < b)).2 (by nlinarith)
  let q : (Set.Icc (0 : ℝ) 1) := ⟨d/b, hq0.le, hq1⟩
  have hw : 1 < weight q Y := by
    unfold weight
    rw [hc]
    apply (lt_div_iff₀ (denom_pos q)).2
    have hq : (q : ℝ) = d/b := rfl
    rw [hq]
    dsimp [d] at hqd
    nlinarith [mul_pos hq0 (sub_pos.mpr hqd)]
  exact hw.trans_le (weight_le q Y)

private theorem cent_line (s : ℝ) : (Finset.univ.expect ∘ Matrix.diag) (V + s • (X * V - V * X)) = Complex.I := by
  rw [cent_add, cent_smul, cent_V]
  have ht : (Finset.univ.expect ∘ Matrix.diag) (X * V - V * X) = 0 := by
    rw [center_formula]
    simp [Matrix.trace_sub, Matrix.trace_mul_comm X V]
  rw [ht, smul_zero, add_zero]

private theorem line_radius (s : ℝ) : ‖centeredEffect (V + s • (X * V - V * X))‖^2 = 1/4 + s^2 := by
  let A := centeredEffect (V + s • (X * V - V * X))
  have hA : A = !![Complex.I / 2, -(s : ℂ) * Complex.I;
      -(s : ℂ) * Complex.I, -Complex.I / 2] := by
    change centeredEffect (V + s • (X * V - V * X)) = _
    change (V + s • (X * V - V * X)) - (Matrix.trace (V + s • (X * V - V * X)) / 2) • 1 = _
    rw [← center_formula, cent_line]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [V, J, K, X, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        pow_two, map_ofNat, Complex.mul_re, Complex.mul_im] <;> ring
  have h : star A * A = (1/4 + s^2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hA]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.star_apply,
        pow_two, map_ofNat, Complex.mul_re, Complex.mul_im] <;> ring
  have hh := CStarRing.norm_star_mul_self (x := A)
  rw [h, norm_smul, CStarRing.norm_one, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/4+s^2), mul_one] at hh
  nlinarith [hh]

private theorem line_strict (s : ℝ) (hs : s ≠ 0) :
    bodyNorm V < bodyNorm (V + s • (X * V - V * X)) := by
  rw [bodyNorm_V]
  apply bodyNorm_strict
  · rw [cent_line, Complex.norm_I]
  · have := line_radius s
    nlinarith [sq_pos_of_ne_zero hs, norm_nonneg (centeredEffect (V+s•(X*V-V*X)))]

theorem result : ¬ D5.S3.HilbertOperators.LarotondaReyNormingFlatnessRefutation.claim := by
  intro h
  obtain ⟨_, ⟨D, hD⟩, hflat⟩ := h 2 (by norm_num) bodyNorm bodyNorm_admissible V skew_V
  have hcomm : ∀ N : Matrix (Fin 2) (Fin 2) ℂ, IsNorming bodyNorm V N →
      N * codiagonal D X = codiagonal D X * N := by
    intro N hN
    obtain ⟨z,rfl⟩ := norming_central N hN
    simp
  obtain ⟨δ,hδ,hlocal⟩ := hflat D hD X skew_X hcomm
  have he := hlocal (δ/2) (by rw [abs_of_pos (by linarith : 0 < δ/2)]; linarith)
  exact (line_strict (δ/2) (by linarith)).ne' he

end
end D5.S3.HilbertOperators.LarotondaReyNormingFlatnessRefutation
