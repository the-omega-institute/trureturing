/- GID: D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite-coordinate identities for full infinite external Gaussian sewing. -/

import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianRows
import D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum
import D5.S3.VertexAlgebra.TwistedGround.GaussianSewingLimit
import D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientContinuity

/-! Finite sewing and support-net limits identify the complete countable
Gaussian contraction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp Ring
open Filter Topology

namespace D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianSewing
open InfiniteGaussianFock GaussianExternalBlock InfiniteGaussianRows
open FactorialFockMetric (Occupation weight)
open FactorialFockQuadraticEstimate (gaussianCoefficient)
open CountableGaussianCutoff
universe u v w

/-- Native finite polynomial coefficients embedded in an arbitrary mode type.
The containing coordinate set is proved, never supplied as consistency data. -/
theorem coefficient_finite_inclusion {J : Type u} {K : Type v}
    [Fintype J] [DecidableEq J] [DecidableEq K]
    (L : K → K → ℂ) (e : J → K) (he : Function.Injective e) (d : Occupation J) :
    coefficient L (d.mapDomain e) = gaussianCoefficient (fun i j => L (e i) (e j)) d := by
  let F := Finset.univ.image e
  have hF (j : J) : e j ∈ F := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hd : (d.mapDomain e).support ⊆ F := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hk)
    exact hF j
  rw [coefficient_on_block L F _ hd]
  let e' : J → F := fun j => ⟨e j, hF j⟩
  have he' : Function.Injective e' := fun _ _ h => he (congrArg Subtype.val h)
  have hmap : restrictOccupation F (d.mapDomain e) = d.mapDomain e' := by
    apply Finsupp.mapDomain_injective (f := fun j : F => j.val) Subtype.val_injective
    rw [extend_restrict F _ hd, ← Finsupp.mapDomain_comp]
    rfl
  rw [hmap, gaussianCoefficient_enlarge _ e' he']

variable {X : Type u} {I : Type v} {Y : Type w}
variable [Fintype X] [DecidableEq X] [DecidableEq I] [Fintype Y] [DecidableEq Y]

private theorem row_finite (P : Matrix X X ℂ) (A : Data I) (R : X → ℓ²(I, ℂ))
    (d : Occupation X) (F : Finset I) (n : Occupation F) :
    row P A R d (n.mapDomain (fun i : F => i.val)) =
      gaussianCoefficient (Matrix.fromBlocks P (fun x (i : F) => R x i.val)
        (fun i : F => fun x => R x i.val) (A.block F)) (d.sumElim n) := by
  let e : X ⊕ F → X ⊕ I := Sum.map id Subtype.val
  have he : Function.Injective e :=
    Sum.map_injective.mpr ⟨Function.injective_id, Subtype.val_injective⟩
  have hd : (d.sumElim n).mapDomain e = d.sumElim (n.mapDomain Subtype.val) := by
    rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp,
      ← Finsupp.mapDomain_comp, Finsupp.sumElim_eq_add, ← Finsupp.mapDomain_comp]
    rfl
  unfold row
  rw [← hd, coefficient_finite_inclusion _ e he]
  congr 1
  ext (i | i) (j | j) <;> rfl

/-- The finite effective kernel contains all three ordered blocks. -/
def cutoffKernel (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (A B : Data I)
    (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ)) (F : Finset I) :
    Matrix (X ⊕ Y) (X ⊕ Y) ℂ :=
  FiniteGaussianSewing.effectiveKernel P Q (A.block F) (B.block F)
    (Matrix.of (fun x i => (R x i.val : ℂ)))
    (Matrix.of (fun i y => (S y i.val : ℂ)))

private theorem finite_log (A B : Data I) (F : Finset I) :
    (1 / 2 : ℂ) * (∑' k : ℕ, Matrix.trace ((A.block F * B.block F) ^ (k + 1)) /
      (k + 1 : ℂ)) = TraceClassPowerSeries.traceLog (cutoffProduct A B F) := by
  have h := FiniteSqueezedVacuum.vacuum_trace_log (A.block F) (B.block F)
    (fun i j => A.symmetric i.val j.val) (fun i j => B.symmetric i.val j.val)
    ((A.block_opNorm_le F).trans_lt A.q_lt_one)
    ((B.block_opNorm_le F).trans_lt B.q_lt_one)
  rw [TraceClassPowerSeries.traceLog, ← h.2.1.tsum_mul_left (1 / 2 : ℂ)]
  apply tsum_congr
  intro m
  rw [TraceClassPowerSeries.logTerm, cutoff_power_trace]
  have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  field_simp [hm]
  <;> ring

/-- Each support cutoff is the actual finite sewing identity. The sum still
contains every internal occupation of the finite coordinate set. -/
theorem cutoff_sewing (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Data I) (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ))
    (hP : ∀ x y, P x y = P y x) (hQ : ∀ x y, Q x y = Q y x)
    (d : Occupation X) (e : Occupation Y) (F : Finset I) :
    cutoff P Q A B R S d e F =
      Complex.exp (TraceClassPowerSeries.traceLog (cutoffProduct A B F)) *
        gaussianCoefficient (cutoffKernel P Q A B R S F) (d.sumElim e) := by
  let r : Matrix X F ℂ := fun x i => R x i.val
  let s : Matrix F Y ℂ := fun i y => S y i.val
  have hf := FiniteGaussianSewing.finite_sewing P Q (A.block F) (B.block F) r s hP hQ
    (fun i j => A.symmetric i.val j.val) (fun i j => B.symmetric i.val j.val)
    ((A.block_opNorm_le F).trans_lt A.q_lt_one)
    ((B.block_opNorm_le F).trans_lt B.q_lt_one) d e
  have hswap (n : Occupation F) :
      gaussianCoefficient (Matrix.fromBlocks (B.block F) s s.transpose Q) (n.sumElim e) =
        gaussianCoefficient (Matrix.fromBlocks Q s.transpose s (B.block F)) (e.sumElim n) := by
    have h := gaussianCoefficient_enlarge
      (Matrix.fromBlocks (B.block F) s s.transpose Q) Sum.swap
      (fun _ _ h => by simpa only [Sum.swap_swap] using congrArg Sum.swap h) (e.sumElim n)
    rw [Finsupp.mapDomain_swap_sumElim] at h
    have hmat : (fun i j : Y ⊕ F =>
        (Matrix.fromBlocks (B.block F) s s.transpose Q) (Sum.swap i) (Sum.swap j)) =
        Matrix.fromBlocks Q s.transpose s (B.block F) := by
      ext (i | i) (j | j) <;> rfl
    simpa only [hmat] using h
  rw [finite_log] at hf
  change cutoff P Q A B R S d e F =
    Complex.exp (TraceClassPowerSeries.traceLog (cutoffProduct A B F)) *
      gaussianCoefficient (FiniteGaussianSewing.effectiveKernel P Q
        (A.block F) (B.block F) r s) (d.sumElim e)
  rw [← hf.2]
  let g (n : Occupation F) := (weight n : ℂ) *
    gaussianCoefficient (Matrix.fromBlocks P r r.transpose (A.block F)) (d.sumElim n) *
    gaussianCoefficient (Matrix.fromBlocks (B.block F) s s.transpose Q) (n.sumElim e)
  change _ = ∑' n, g n
  rw [← (occupationEquiv F).tsum_eq g]
  apply tsum_congr
  intro n
  have hn := extend_restrict F n.val n.property
  have hp := row_finite P A R d F (restrictOccupation F n.val)
  have hq := row_finite Q B S e F (restrictOccupation F n.val)
  rw [hn] at hp hq
  change row P A R d n.val =
    gaussianCoefficient (Matrix.fromBlocks P r r.transpose (A.block F))
      (d.sumElim (restrictOccupation F n.val)) at hp
  change row Q B S e n.val =
    gaussianCoefficient (Matrix.fromBlocks Q s.transpose s (B.block F))
      (e.sumElim (restrictOccupation F n.val)) at hq
  change (weight n.val : ℂ) * row P A R d n.val * row Q B S e n.val =
    (weight (restrictOccupation F n.val) : ℂ) *
      gaussianCoefficient (Matrix.fromBlocks P r r.transpose (A.block F))
        (d.sumElim (restrictOccupation F n.val)) *
      gaussianCoefficient (Matrix.fromBlocks (B.block F) s s.transpose Q)
        ((restrictOccupation F n.val).sumElim e)
  rw [hp, hq, hswap, weight_restrict F n.val n.property]

open GaussianSewingLimit

/-- Ordered effective kernel. The opposite mixed block is literally the
bilinear coordinate transpose, with no Hilbert adjoint in its definition. -/
def effectiveKernel (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (A B : Data I)
    (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ)) : Matrix (X ⊕ Y) (X ⊕ Y) ℂ :=
  Matrix.fromBlocks
    (fun x x' => P x x' + bilinear (R x)
      (((1 - B.oneParticle * A.oneParticle)⁻¹ʳ * B.oneParticle) (R x')))
    (fun x y => bilinear (R x) ((1 - B.oneParticle * A.oneParticle)⁻¹ʳ (S y)))
    (fun y x => bilinear (R x) ((1 - B.oneParticle * A.oneParticle)⁻¹ʳ (S y)))
    (fun y y' => Q y y' + bilinear (S y)
      (((1 - A.oneParticle * B.oneParticle)⁻¹ʳ * A.oneParticle) (S y')))

private theorem finite_bilinear {U : Type*} {V : Type*} [Fintype U] [Fintype V]
    (F : Finset I) (R : U → ℓ²(I, ℂ)) (S : V → ℓ²(I, ℂ))
    (M : Matrix F F ℂ) (x : U) (y : V) :
    (Matrix.of (fun (x : U) (i : F) => (R x i.val : ℂ)) * M *
      Matrix.of (fun (i : F) (y : V) => (S y i.val : ℂ))) x y =
      bilinear (R x) (embedded F M (S y)) := by
  rw [bilinear_embedded]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

private theorem cutoff_mixed_transpose (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Data I) (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ))
    (F : Finset I) (x : X) (y : Y) :
    cutoffKernel P Q A B R S F (.inr y) (.inl x) =
      cutoffKernel P Q A B R S F (.inl x) (.inr y) := by
  have hA : (A.block F).transpose = A.block F := by
    ext i j; exact A.symmetric j.val i.val
  have hB : (B.block F).transpose = B.block F := by
    ext i j; exact B.symmetric j.val i.val
  have hN : ((1 - B.block F * A.block F)⁻¹ʳ).transpose =
      (1 - A.block F * B.block F)⁻¹ʳ := by
    simp only [← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hA, hB]
  have h := congrArg (fun M : Matrix Y X ℂ => M y x)
    (Matrix.transpose_mul (Matrix.of (fun (x : X) (i : F) => (R x i.val : ℂ)) *
      (1 - B.block F * A.block F)⁻¹ʳ) (Matrix.of (fun (i : F) (y : Y) => (S y i.val : ℂ))))
  simpa [cutoffKernel, FiniteGaussianSewing.effectiveKernel,
    Matrix.transpose_mul, hN, Matrix.mul_assoc] using h.symm

/-- The finite effective kernels converge entrywise to the full ordered
kernel. The mixed complement is cancelled exactly before taking limits. -/
theorem cutoffKernel_tendsto (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Data I) (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ)) :
    Tendsto (cutoffKernel P Q A B R S) atTop (𝓝 (effectiveKernel P Q A B R S)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  cases i with
  | inl x =>
    cases j with
    | inl x' =>
      have h := (tendsto_const_nhds :
        Tendsto (fun _ : Finset I => P x x') atTop (𝓝 (P x x'))).add
          (ordered_entries_tendsto A B (R x) (R x')).1
      convert h using 1
      all_goals try rfl
      funext F
      simp only [cutoffKernel, FiniteGaussianSewing.effectiveKernel,
        Matrix.fromBlocks_apply₁₁, Matrix.add_apply]
      congr 1
      change (Matrix.of (fun (a : X) (i : F) => (R a i.val : ℂ)) *
        (1 - B.block F * A.block F)⁻¹ʳ * B.block F *
        Matrix.of (fun (i : F) (a : X) => (R a i.val : ℂ))) x x' = _
      rw [Matrix.mul_assoc _ _ (B.block F),
        finite_bilinear F R R _ x x', padded_inverse_mul]
    | inr y =>
      have h := (ordered_entries_tendsto A B (R x) (S y)).2
      convert h using 1
      all_goals try rfl
      funext F
      simp only [cutoffKernel, FiniteGaussianSewing.effectiveKernel,
        Matrix.fromBlocks_apply₁₂]
      rw [finite_bilinear F R S _ x y, padded_inverse,
        ContinuousLinearMap.add_apply, map_add]
      ring
  | inr y =>
    cases j with
    | inl x =>
      have h := (ordered_entries_tendsto A B (R x) (S y)).2
      convert h using 1
      all_goals try rfl
      funext F
      rw [cutoff_mixed_transpose]
      simp only [cutoffKernel, FiniteGaussianSewing.effectiveKernel,
        Matrix.fromBlocks_apply₁₂]
      rw [finite_bilinear F R S _ x y, padded_inverse,
        ContinuousLinearMap.add_apply, map_add]
      ring
    | inr y' =>
      have h := (tendsto_const_nhds :
        Tendsto (fun _ : Finset I => Q y y') atTop (𝓝 (Q y y'))).add
          (ordered_entries_tendsto B A (S y) (S y')).1
      convert h using 1
      all_goals try rfl
      funext F
      simp only [cutoffKernel, FiniteGaussianSewing.effectiveKernel,
        Matrix.fromBlocks_apply₂₂, Matrix.add_apply]
      congr 1
      change (Matrix.of (fun (a : Y) (i : F) => (S a i.val : ℂ)) *
        (1 - A.block F * B.block F)⁻¹ʳ * A.block F *
        Matrix.of (fun (i : F) (a : Y) => (S a i.val : ℂ))) y y' = _
      rw [Matrix.mul_assoc _ _ (A.block F),
        finite_bilinear F S S _ y y', padded_inverse_mul]

/-- Full infinite/countable internal-mode Gaussian sewing, with arbitrary
finite ordinary external occupations and genuine absolute convergence.
The trace logarithm is that of the actual trace-class product AB. -/
private theorem sewing_rows (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Data I) (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ))
    (hP : ∀ x y, P x y = P y x) (hQ : ∀ x y, Q x y = Q y x)
    (d : Occupation X) (e : Occupation Y) :
    Summable (fun n : Occupation I =>
      ‖(weight n : ℂ) * row P A R d n * row Q B S e n‖) ∧
    (∑' n : Occupation I, (weight n : ℂ) * row P A R d n * row Q B S e n) =
      Complex.exp (TraceClassPowerSeries.traceLog (product A B)) *
        gaussianCoefficient (effectiveKernel P Q A B R S) (d.sumElim e) := by
  have hleft := cutoff_tendsto P Q A B R S hP hQ d e
  have hright := ((Complex.continuous_exp.tendsto _).comp
    (traceLog_cutoff_tendsto A B)).mul
      ((GaussianCoefficientContinuity.coefficient_continuous (d.sumElim e)).tendsto
        (effectiveKernel P Q A B R S) |>.comp (cutoffKernel_tendsto P Q A B R S))
  refine ⟨contraction_norm_summable P Q A B R S hP hQ d e, ?_⟩
  exact tendsto_nhds_unique hleft (by
    simpa only [Function.comp_def, ← cutoff_sewing P Q A B R S hP hQ d e] using hright)

private theorem coefficient_rename {J : Type*} {K : Type*}
    [DecidableEq J] [DecidableEq K] (L : K → K → ℂ)
    (e : J → K) (he : Function.Injective e) (d : Occupation J) :
    coefficient L (d.mapDomain e) = coefficient (fun i j => L (e i) (e j)) d := by
  let r := restrictOccupation d.support d
  have hd : r.mapDomain (fun i : d.support => i.val) = d :=
    extend_restrict _ _ (fun _ h => h)
  have hmap : r.mapDomain (fun i : d.support => e i.val) = d.mapDomain e := by
    change r.mapDomain (e ∘ Subtype.val) = _
    rw [Finsupp.mapDomain_comp, hd]
  calc
    _ = coefficient L (r.mapDomain (fun i : d.support => e i.val)) := by rw [hmap]
    _ = _ := coefficient_finite_inclusion L (fun i : d.support => e i.val)
      (he.comp Subtype.val_injective) r

/-- The second true block uses internal modes first and external modes last. -/
def rightKernel (Q : Matrix Y Y ℂ) (B : Data I) (S : Y → ℓ²(I, ℂ)) :
    (I ⊕ Y) → (I ⊕ Y) → ℂ :=
  Matrix.fromBlocks B.kernel (fun i y => S y i) (fun y i => S y i) Q

/-- The complete sourceful sewing identity. Only A and B are strict
Hilbert-Schmidt contractions. P,Q and the finite mixed l2 families are
arbitrary. Every mode type, including the empty type, remains in scope. -/
theorem sewing (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Data I) (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ))
    (hP : ∀ x y, P x y = P y x) (hQ : ∀ x y, Q x y = Q y x)
    (d : Occupation X) (e : Occupation Y) :
    Summable (fun n : Occupation I => ‖(weight n : ℂ) *
      coefficient (kernel P A R) (d.sumElim n) *
      coefficient (rightKernel Q B S) (n.sumElim e)‖) ∧
    (∑' n : Occupation I, (weight n : ℂ) *
      coefficient (kernel P A R) (d.sumElim n) *
      coefficient (rightKernel Q B S) (n.sumElim e)) =
      Complex.exp (TraceClassPowerSeries.traceLog (product A B)) *
        coefficient (effectiveKernel P Q A B R S) (d.sumElim e) := by
  have hswap (n : Occupation I) :
      coefficient (rightKernel Q B S) (n.sumElim e) = row Q B S e n := by
    have h := coefficient_rename (rightKernel Q B S) Sum.swap
      (fun _ _ h => by simpa only [Sum.swap_swap] using congrArg Sum.swap h) (e.sumElim n)
    rw [Finsupp.mapDomain_swap_sumElim] at h
    have hmat : (fun i j : Y ⊕ I =>
        rightKernel Q B S (Sum.swap i) (Sum.swap j)) = kernel Q B S := by
      ext (i | i) (j | j) <;> rfl
    simpa only [hmat, row] using h
  have hfinite : coefficient (effectiveKernel P Q A B R S) (d.sumElim e) =
      gaussianCoefficient (effectiveKernel P Q A B R S) (d.sumElim e) := by
    simpa using coefficient_finite_inclusion (effectiveKernel P Q A B R S)
      id Function.injective_id (d.sumElim e)
  rw [hfinite]
  simp_rw [hswap]
  exact sewing_rows P Q A B R S hP hQ d e

#print axioms sewing
end D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianSewing
