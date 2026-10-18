/- GID: D5/S3/Observer/PositiveMoments/PrefixPositiveRealization
   generality: G
   mirror-B: D5/B/S3/Observer/PositiveMoments/PrefixPositiveRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive realization and the least dimension of finite operator moment prefixes. -/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic

/-! Finite-dimensional real inner-product spaces, including zero-dimensional carriers. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped InnerProductSpace MatrixOrder
open LinearMap
namespace D5.S3.Observer.PositiveMoments.PrefixPositiveRealization
variable {P E F U V : Type}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem gram_rank_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : P →ₗ[ℝ] E) :
    Module.finrank ℝ (T.adjoint ∘ₗ T).range ≤ Module.finrank ℝ E := by
  rw [LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint]
  exact T.range.finrank_le

def moment (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) (k : ℕ) : U →ₗ[ℝ] U :=
  J.adjoint ∘ₗ (C ^ k) ∘ₗ J

/-- Selfadjoint powers identify a moment pairing with a Gram pairing. -/
theorem moment_pairing (C : E →ₗ[ℝ] E) (hC : C.IsSymmetric)
    (J : U →ₗ[ℝ] E) (i j : ℕ) (u v : U) :
    inner ℝ u (moment C J (i + j) v) =
      inner ℝ ((C^i) (J u)) ((C^j) (J v)) := by
  simp only [moment, LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    pow_add, Module.End.mul_apply]
  exact ((hC.pow i) (J u) ((C^j) (J v))).symm

def matchesPrefix (N : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Prop :=
  ∀ k ≤ N, moment C J k = M k

abbrev Coeff (U : Type) (q : ℕ) := PiLp 2 (fun _ : Fin q => U)

def momentBlock (M : ℕ → U →ₗ[ℝ] U) (q offset : ℕ) :
    Coeff U q →ₗ[ℝ] Coeff U q :=
  (WithLp.linearEquiv 2 ℝ (Fin q → U)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i : Fin q =>
      ∑ j : Fin q, (M (i.val + j.val + offset)).comp (LinearMap.proj j)) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin q → U)).toLinearMap

def synthesis (q : ℕ) (e : Fin q → U →ₗ[ℝ] E) : Coeff U q →ₗ[ℝ] E :=
  (∑ i, e i ∘ₗ LinearMap.proj i) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin q → U)).toLinearMap

/-- Synthesis sums the images of the coefficient vectors. -/
theorem synthesis_apply (q : ℕ) (e : Fin q → U →ₗ[ℝ] E) (v : Coeff U q) :
    synthesis q e v = ∑ i, e i (WithLp.ofLp v i) := by
  simp [synthesis, LinearMap.sum_apply]

/-- Generator pairings determine the block Hankel Gram operator. -/
theorem synthesis_gram (q : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (e : Fin q → U →ₗ[ℝ] E)
    (hgram : ∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v)) :
    (synthesis q e).adjoint ∘ₗ synthesis q e = momentBlock M q 0 := by
  classical
  apply LinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    synthesis_apply, sum_inner, inner_sum]
  simp_rw [hgram]
  simp [momentBlock, PiLp.inner_apply, LinearMap.sum_apply, Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

private theorem prefix_gram (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsSymmetric) (hM : matchesPrefix (2 * r + 1) M C J) :
    let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
    T.adjoint ∘ₗ T = momentBlock M (r + 1) 0 ∧
      T.adjoint ∘ₗ C ∘ₗ T = momentBlock M (r + 1) 1 := by
  classical
  dsimp only
  constructor
  · apply synthesis_gram
    intro i j u v
    simpa only [LinearMap.comp_apply, Nat.add_zero,
      hM (i.val + j.val) (by omega)] using (moment_pairing C hC J i.val j.val u v).symm
  · apply LinearMap.ext
    intro v
    apply ext_inner_left ℝ
    intro u
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
      synthesis_apply, map_sum, sum_inner, inner_sum]
    have hpair (i j : Fin (r + 1)) (u v : U) :
        inner ℝ ((C^i.val) (J u)) (C ((C^j.val) (J v))) =
          inner ℝ u (M (i.val + j.val + 1) v) := by
      have h := moment_pairing C hC J i.val (j.val + 1) u v
      rw [hM _ (by omega)] at h
      simpa only [pow_succ', Module.End.mul_apply, Nat.add_assoc] using h.symm
    simp_rw [hpair]
    simp [momentBlock, PiLp.inner_apply, LinearMap.sum_apply, Finset.sum_apply, inner_sum]
    exact Finset.sum_comm

private theorem prefix_necessary (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsPositive) (hM : matchesPrefix (2 * r + 1) M C J) :
    (momentBlock M (r + 1) 0).IsPositive ∧
      (momentBlock M (r + 1) 1).IsPositive ∧
      (momentBlock M (r + 1) 0).ker ≤ (momentBlock M (r + 1) 1).ker ∧
      Module.finrank ℝ (momentBlock M (r + 1) 0).range ≤ Module.finrank ℝ E := by
  let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
  obtain ⟨hg, hs⟩ := prefix_gram r M C J hC.isSymmetric hM
  change T.adjoint ∘ₗ T = _ at hg
  change T.adjoint ∘ₗ C ∘ₗ T = _ at hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hg]
    exact LinearMap.isPositive_adjoint_comp_self T
  · rw [← hs]
    exact hC.adjoint_conj T
  · rw [← hg, LinearMap.ker_adjoint_comp_self, ← hs]
    intro x hx
    change T.adjoint (C (T x)) = 0
    simp [show T x = 0 from hx]
  · rw [← hg]
    exact gram_rank_lower T

/-- Orthogonal changes of state coordinates preserve every moment. -/
theorem moment_transport (q : E ≃ₗᵢ[ℝ] V) (C : E →ₗ[ℝ] E)
    (J : U →ₗ[ℝ] E) (k : ℕ) :
    moment (q.toLinearMap ∘ₗ C ∘ₗ q.symm.toLinearMap) (q.toLinearMap ∘ₗ J) k =
      moment C J k := by
  have hp : ∀ k x, ((q.toLinearMap ∘ₗ C ∘ₗ q.symm.toLinearMap)^k) (q x) =
      q ((C^k) x) := by
    intro k x
    have hc : (q.toLinearMap ∘ₗ C ∘ₗ q.symm.toLinearMap) ∘ₗ q.toLinearMap =
        q.toLinearMap ∘ₗ C := by ext y; simp
    exact LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hc k) x
  ext v
  apply ext_inner_left ℝ
  intro u
  simp only [moment, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  change inner ℝ (q (J u)) (((q.toLinearMap ∘ₗ C ∘ₗ q.symm.toLinearMap)^k) (q (J v))) = _
  rw [hp, q.inner_map_map]

/-- A truncated shift and its two pairings determine the entire odd moment prefix. -/
theorem generators_match (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (hC : C.IsSymmetric)
    (e : Fin (r + 1) → U →ₗ[ℝ] E)
    (hg : ∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v))
    (hp : ∀ i j u v, inner ℝ (e i u) (C (e j v)) =
      inner ℝ u (M (i.val + j.val + 1) v))
    (hshift : ∀ j : Fin r, C ∘ₗ e j.castSucc = e j.succ) :
    matchesPrefix (2 * r + 1) M C (e 0) ∧
      (∀ j : Fin (r + 1), (C^j.val) ∘ₗ e 0 = e j) := by
  have he : ∀ j (hj : j ≤ r), (C^j) ∘ₗ e 0 = e ⟨j, by omega⟩ := by
    intro j
    induction j with
    | zero => intro hj; ext u; rfl
    | succ j ih =>
      intro hj
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc, ih (by omega)]
      exact hshift ⟨j, by omega⟩
  have he' (j : Fin (r + 1)) : (C^j.val) ∘ₗ e 0 = e j := he j.val (by omega)
  refine ⟨?_, he'⟩
  intro k hk
  ext v
  apply ext_inner_left ℝ
  intro u
  by_cases hkr : k ≤ 2 * r
  · let i : Fin (r + 1) := ⟨min k r, by omega⟩
    let j : Fin (r + 1) := ⟨k-i.val, by dsimp [i]; omega⟩
    have hs : k = i.val + j.val := by dsimp [i, j]; omega
    rw [hs, moment_pairing C hC]
    have hi := LinearMap.congr_fun (he' i) u
    have hj := LinearMap.congr_fun (he' j) v
    simpa only [LinearMap.comp_apply] using hi ▸ hj ▸ hg i j u v
  · have hs : k = r + (r + 1) := by omega
    rw [hs, moment_pairing C hC, pow_succ', Module.End.mul_apply]
    have hi := LinearMap.congr_fun (he' ⟨r, by omega⟩) u
    have hj := LinearMap.congr_fun (he' ⟨r, by omega⟩) v
    simp only [LinearMap.comp_apply] at hi hj
    rw [hi, hj]
    simpa only [Nat.add_assoc] using hp ⟨r, by omega⟩ ⟨r, by omega⟩ u v

abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)

def coeffInsert (q : ℕ) (i : Fin q) : U →ₗ[ℝ] Coeff U q :=
  (WithLp.linearEquiv 2 ℝ (Fin q → U)).symm.toLinearMap ∘ₗ
    LinearMap.single ℝ (fun _ : Fin q => U) i

/-- A positive operator is the Gram operator of a linear map. -/
theorem gram_factor (H : P →ₗ[ℝ] P) (hH : H.IsPositive) :
    ∃ B : P →ₗ[ℝ] P, H = B.adjoint ∘ₗ B := by
  classical
  let b := stdOrthonormalBasis ℝ P
  let φ := LinearMap.toMatrixOrthonormal b
  have hmatrix : (φ H).PosSemidef := (LinearMap.posSemidef_toMatrix_iff b).mpr hH
  obtain ⟨Z, hZ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hmatrix.nonneg
  refine ⟨φ.symm Z, ?_⟩
  have hh := congrArg φ.symm hZ
  simpa [map_mul, map_star, LinearMap.star_eq_adjoint, Module.End.mul_eq_comp] using hh

private def CompressionGoal (T : P →ₗ[ℝ] E) (S : P →ₗ[ℝ] P) : Prop :=
  ∃ C : E →ₗ[ℝ] E, C.IsPositive ∧
    ∀ v w : P, inner ℝ (T v) (C (T w)) = inner ℝ v (S w)

private theorem compression (T : P →ₗ[ℝ] E) (hT : Function.Surjective T)
    (S : P →ₗ[ℝ] P) (hS : S.IsPositive)
    (hker : T.ker ≤ S.ker) : CompressionGoal T S := by
  obtain ⟨R, hR⟩ := T.exists_rightInverse_of_surjective (range_eq_top.mpr hT)
  let B := T.liftOfSurjective hT ⟨S, hker⟩
  have hB (v : P) : B (T v) = S v := T.equivOfSurjective_apply hT hker
  have hRv (x : E) : T (R x) = x := LinearMap.congr_fun hR x
  have hSRT (v : P) : S (R (T v)) = S v := by
    rw [← hB, hRv]
    exact hB v
  refine ⟨R.adjoint ∘ₗ S ∘ₗ R, hS.adjoint_conj R, ?_⟩
  intro v w
  change inner ℝ (T v) (R.adjoint (S (R (T w)))) = inner ℝ v (S w)
  rw [LinearMap.adjoint_inner_right, hSRT, ← hS.isSymmetric, hSRT]
  exact hS.isSymmetric v w

private theorem canonical_compression (H S : P →ₗ[ℝ] P)
    (hH : H.IsPositive) (hS : S.IsPositive) (hker : H.ker ≤ S.ker) :
    ∃ B : P →ₗ[ℝ] P, H = B.adjoint ∘ₗ B ∧
      Module.finrank ℝ B.range = Module.finrank ℝ H.range ∧
      CompressionGoal B.rangeRestrict S := by
  obtain ⟨B, hB⟩ := gram_factor H hH
  refine ⟨B, hB, ?_, ?_⟩
  · rw [hB, LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint]
  · apply compression B.rangeRestrict (range_eq_top.mp B.range_rangeRestrict) S hS
    simpa only [LinearMap.ker_rangeRestrict, hB, LinearMap.ker_adjoint_comp_self] using hker

/-- Pairings against a spanning family distinguish vectors. -/
theorem generator_pairings (ι : Type*) (e : ι → U →ₗ[ℝ] E)
    (hspan : Submodule.span ℝ (⋃ i, Set.range (e i)) = ⊤)
    (a b : E) (h : ∀ i u, inner ℝ (e i u) a = inner ℝ (e i u) b) : a = b := by
  have hf : (innerₗ E).flip a = (innerₗ E).flip b :=
    LinearMap.ext_on hspan (by
      rintro x hx
      obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp hx
      exact h i u)
  apply ext_inner_left ℝ
  exact fun x => LinearMap.congr_fun hf x

private def HankelShiftGoal (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (e : Fin (r + 1) → U →ₗ[ℝ] E) (C : E →ₗ[ℝ] E) : Prop :=
  (∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v)) →
  (∀ i j u v, inner ℝ (e i u) (C (e j v)) =
    inner ℝ u (M (i.val + j.val + 1) v)) →
  Submodule.span ℝ (⋃ i, Set.range (e i)) = ⊤ →
  ∀ j : Fin r, C ∘ₗ e j.castSucc = e j.succ

private theorem hankel_shift (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (e : Fin (r + 1) → U →ₗ[ℝ] E) (C : E →ₗ[ℝ] E) :
    HankelShiftGoal r M e C := by
  intro hgram hpair hspan j
  ext v
  apply generator_pairings _ e hspan
  intro i u
  simp only [LinearMap.comp_apply, hpair, hgram]
  rfl

/-- Insertion maps read the individual entries of a block moment operator. -/
theorem block_entry (M : ℕ → U →ₗ[ℝ] U) (q offset : ℕ)
    (i j : Fin q) (u v : U) :
    inner ℝ (coeffInsert q i u) (momentBlock M q offset (coeffInsert q j v)) =
      inner ℝ u (M (i.val + j.val + offset) v) := by
  classical
  simp [coeffInsert, momentBlock, PiLp.inner_apply, LinearMap.single_apply,
    Pi.single_apply, Finset.sum_apply, inner_sum, apply_ite]
  rw [Finset.sum_eq_single i] <;> simp_all

private theorem coeff_sum (q : ℕ) (v : Coeff U q) :
    ∑ i, coeffInsert q i (WithLp.ofLp v i) = v := by
  apply (WithLp.linearEquiv 2 ℝ (Fin q → U)).injective
  simp [coeffInsert, ← map_sum, LinearMap.sum_single_apply]

/-- The coefficient insertions generate the range of a surjective synthesis map. -/
theorem full_generator_span {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (q : ℕ)
    (T : Coeff U q →ₗ[ℝ] E) (hT : Function.Surjective T) :
    Submodule.span ℝ (⋃ i, Set.range (T ∘ₗ coeffInsert q i)) = ⊤ := by
  classical
  apply top_unique
  intro x hx
  obtain ⟨v, rfl⟩ := hT x
  rw [← coeff_sum q v, map_sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨i, WithLp.ofLp v i, rfl⟩

private theorem canonical_raw (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (hH : (momentBlock M (r + 1) 0).IsPositive)
    (hS : (momentBlock M (r + 1) 1).IsPositive)
    (hker : (momentBlock M (r + 1) 0).ker ≤ (momentBlock M (r + 1) 1).ker) :
    ∃ B : Coeff U (r + 1) →ₗ[ℝ] Coeff U (r + 1),
      momentBlock M (r + 1) 0 = B.adjoint ∘ₗ B ∧
      Module.finrank ℝ B.range = Module.finrank ℝ (momentBlock M (r + 1) 0).range ∧
      ∃ C : B.range →ₗ[ℝ] B.range, C.IsPositive ∧
        let e : Fin (r + 1) → U →ₗ[ℝ] B.range :=
          fun i => B.rangeRestrict ∘ₗ coeffInsert (r + 1) i
        (∀ i j u v, inner ℝ (e i u) (e j v) = inner ℝ u (M (i.val + j.val) v)) ∧
        (∀ i j u v, inner ℝ (e i u) (C (e j v)) =
          inner ℝ u (M (i.val + j.val + 1) v)) ∧
        Submodule.span ℝ (⋃ i, Set.range (e i)) = ⊤ ∧
        (∀ j : Fin r, C ∘ₗ e j.castSucc = e j.succ) := by
  obtain ⟨B, hB, hrank, C, hC, hpair⟩ := canonical_compression
    (momentBlock M (r + 1) 0) (momentBlock M (r + 1) 1) hH hS hker
  let e : Fin (r + 1) → U →ₗ[ℝ] B.range :=
    fun i => B.rangeRestrict ∘ₗ coeffInsert (r + 1) i
  have hg : ∀ i j u v, inner ℝ (e i u) (e j v) =
      inner ℝ u (M (i.val + j.val) v) := by
    intro i j u v
    change inner ℝ (B (coeffInsert (r + 1) i u)) (B (coeffInsert (r + 1) j v)) = _
    rw [← LinearMap.adjoint_inner_right]
    change inner ℝ (coeffInsert (r + 1) i u)
      ((B.adjoint ∘ₗ B) (coeffInsert (r + 1) j v)) = _
    rw [← hB]
    simpa using block_entry M (r + 1) 0 i j u v
  have hp : ∀ i j u v, inner ℝ (e i u) (C (e j v)) =
      inner ℝ u (M (i.val + j.val + 1) v) := by
    intro i j u v
    change inner ℝ (B.rangeRestrict (coeffInsert (r + 1) i u))
      (C (B.rangeRestrict (coeffInsert (r + 1) j v))) = _
    rw [hpair]
    exact block_entry M (r + 1) 1 i j u v
  have hs : Submodule.span ℝ (⋃ i, Set.range (e i)) = ⊤ :=
    full_generator_span (r + 1) B.rangeRestrict
      (LinearMap.range_eq_top.mp B.range_rangeRestrict)
  exact ⟨B, hB, hrank, C, hC, hg, hp, hs, hankel_shift r M e C hg hp hs⟩

private theorem canonical_attainment (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (hH : (momentBlock M (r + 1) 0).IsPositive)
    (hS : (momentBlock M (r + 1) 1).IsPositive)
    (hk : (momentBlock M (r + 1) 0).ker ≤ (momentBlock M (r + 1) 1).ker) :
    ∃ (C : State (Module.finrank ℝ (momentBlock M (r + 1) 0).range) →ₗ[ℝ]
      State (Module.finrank ℝ (momentBlock M (r + 1) 0).range))
      (J : U →ₗ[ℝ] State (Module.finrank ℝ (momentBlock M (r + 1) 0).range)),
      C.IsPositive ∧ matchesPrefix (2 * r + 1) M C J := by
  obtain ⟨B, hB, hd, C, hC, hg, hp, hspan, hshift⟩ := canonical_raw r M hH hS hk
  let e : Fin (r + 1) → U →ₗ[ℝ] B.range := fun i => B.rangeRestrict ∘ₗ coeffInsert (r + 1) i
  obtain ⟨hmatch, he⟩ := generators_match r M C hC.isSymmetric e hg hp hshift
  let q := (stdOrthonormalBasis ℝ B.range).repr
  have hpos := (LinearMap.isPositive_linearIsometryEquiv_conj_iff q).mpr hC
  have hmatch' : matchesPrefix (2 * r + 1) M
      (q.toLinearMap ∘ₗ C ∘ₗ q.symm.toLinearMap) (q.toLinearMap ∘ₗ e 0) := by
    intro k hk
    rw [moment_transport]
    exact hmatch k hk
  have hout : ∃ (C' : State (Module.finrank ℝ B.range) →ₗ[ℝ] State (Module.finrank ℝ B.range))
      (J' : U →ₗ[ℝ] State (Module.finrank ℝ B.range)),
      C'.IsPositive ∧ matchesPrefix (2 * r + 1) M C' J' := ⟨_, _, hpos, hmatch'⟩
  exact hd ▸ hout

def realizable (N : ℕ) (M : ℕ → U →ₗ[ℝ] U) : Prop :=
  ∃ (n : ℕ) (C : State n →ₗ[ℝ] State n) (J : U →ₗ[ℝ] State n),
    C.IsPositive ∧ matchesPrefix N M C J

def positive_realization_iff_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) : Prop :=
  (∀ k ≤ 2 * r + 1, (M k).IsSymmetric) →
  (realizable (2 * r + 1) M ↔
    (momentBlock M (r + 1) 0).IsPositive ∧ (momentBlock M (r + 1) 1).IsPositive ∧
      (momentBlock M (r + 1) 0).ker ≤ (momentBlock M (r + 1) 1).ker)

/-- The two positive Hankel operators and kernel inclusion characterize positive realization. -/
theorem positive_realization_iff (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) :
    positive_realization_iff_statement r M := by
  intro hsym
  constructor
  · rintro ⟨n, C, J, hC, hM⟩
    obtain ⟨hH, hS, hk, hd⟩ := prefix_necessary r M C J hC hM
    exact ⟨hH, hS, hk⟩
  · rintro ⟨hH, hS, hk⟩
    obtain ⟨C, J, hC, hM⟩ := canonical_attainment r M hH hS hk
    exact ⟨_, C, J, hC, hM⟩

def minimal_dimension_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) : Prop :=
  realizable (2 * r + 1) M →
    (∃ (C : State (Module.finrank ℝ (momentBlock M (r + 1) 0).range) →ₗ[ℝ]
        State (Module.finrank ℝ (momentBlock M (r + 1) 0).range))
      (J : U →ₗ[ℝ] State (Module.finrank ℝ (momentBlock M (r + 1) 0).range)),
      C.IsPositive ∧ matchesPrefix (2 * r + 1) M C J) ∧
    (∀ (n : ℕ) (C : State n →ₗ[ℝ] State n) (J : U →ₗ[ℝ] State n),
      C.IsPositive → matchesPrefix (2 * r + 1) M C J →
      Module.finrank ℝ (momentBlock M (r + 1) 0).range ≤ n)

/-- The Hankel rank is attained and bounds every positive realization from below. -/
theorem minimal_dimension (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) :
    minimal_dimension_statement r M := by
  rintro ⟨n, C, J, hC, hM⟩
  obtain ⟨hH, hS, hk, hd⟩ := prefix_necessary r M C J hC hM
  refine ⟨canonical_attainment r M hH hS hk, ?_⟩
  intro m C' J' hC' hM'
  simpa only [finrank_euclideanSpace_fin] using
    (prefix_necessary r M C' J' hC' hM').2.2.2

def strict_realization_iff_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) : Prop :=
  realizable (2 * r + 1) M →
  ((∃ (n : ℕ) (C : State n →ₗ[ℝ] State n) (J : U →ₗ[ℝ] State n),
    C.IsPositive ∧ C.ker = ⊥ ∧ matchesPrefix (2 * r + 1) M C J) ↔
    (momentBlock M (r + 1) 1).ker = (momentBlock M (r + 1) 0).ker)

/-- A zero quadratic form vector lies in the kernel of a positive operator. -/
theorem positive_zero (A : E →ₗ[ℝ] E) (hA : A.IsPositive)
    (x : E) (hx : inner ℝ (A x) x = 0) : A x = 0 := by
  obtain ⟨B, hB⟩ := gram_factor A hA
  have hBx : B x = 0 := inner_self_eq_zero.mp (by
    simpa only [hB, LinearMap.comp_apply, LinearMap.adjoint_inner_left] using hx)
  simp [hB, LinearMap.comp_apply, hBx]

private theorem strict_kernel_necessary (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsPositive) (hM : matchesPrefix (2 * r + 1) M C J) (hk : C.ker = ⊥) :
    (momentBlock M (r + 1) 1).ker = (momentBlock M (r + 1) 0).ker := by
  let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
  obtain ⟨hg, hs⟩ := prefix_gram r M C J hC.isSymmetric hM
  refine le_antisymm ?_ (prefix_necessary r M C J hC hM).2.2.1
  intro v hv
  have hz : inner ℝ (C (T v)) (T v) = 0 := by
    have hv' : (T.adjoint ∘ₗ C ∘ₗ T) v = 0 := by rw [hs]; exact hv
    have hh := congrArg (fun z => inner ℝ z v) hv'
    simpa only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_zero_left] using hh
  have hCv := positive_zero C hC (T v) hz
  have hTv : T v = 0 := (LinearMap.ker_eq_bot'.mp hk) _ hCv
  rw [← hg]
  change T.adjoint (T v) = 0
  simp [hTv]

/-- Synthesis on a single coefficient returns the corresponding generator. -/
theorem synthesis_insert (q : ℕ) (e : Fin q → U →ₗ[ℝ] E)
    (j : Fin q) (u : U) : synthesis q e (coeffInsert q j u) = e j u := by
  classical
  simp [synthesis, coeffInsert, LinearMap.single_apply, LinearMap.sum_apply,
    Pi.single_apply, apply_ite]

/-- The synthesis range is the span of its generators. -/
theorem synthesis_range (q : ℕ) (e : Fin q → U →ₗ[ℝ] E) :
    (synthesis q e).range = Submodule.span ℝ (⋃ i, Set.range (e i)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [synthesis_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    exact Set.mem_iUnion.mpr ⟨i, WithLp.ofLp v i, rfl⟩
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨u, rfl⟩ := hi
    exact ⟨coeffInsert q i u, synthesis_insert q e i u⟩

def cyclicPrefix (r : ℕ) (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Prop :=
  Submodule.span ℝ (⋃ j : Fin (r + 1), Set.range ((C ^ j.val) ∘ₗ J)) = ⊤

private def strict_canonical_iff_statement (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) : Prop :=
  C.IsPositive → matchesPrefix (2 * r + 1) M C J → cyclicPrefix r C J →
    (C.ker = ⊥ ↔ (momentBlock M (r + 1) 1).ker = (momentBlock M (r + 1) 0).ker)

private theorem strict_canonical_iff (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E) :
    strict_canonical_iff_statement r M C J := by
  intro hC hM hcyc
  constructor
  · exact strict_kernel_necessary r M C J hC hM
  · intro hk
    let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
    have hT : Function.Surjective T :=
      LinearMap.range_eq_top.mp ((synthesis_range _ _).trans hcyc)
    obtain ⟨hg, hs⟩ := prefix_gram r M C J hC.isSymmetric hM
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨v, rfl⟩ := hT x
    have hsv : v ∈ (momentBlock M (r + 1) 1).ker := by
      rw [← hs]
      change T.adjoint (C (T v)) = 0
      simp [hx]
    rw [hk, ← hg, LinearMap.ker_adjoint_comp_self] at hsv
    exact hsv

private theorem cyclic_of_minimal_dimension (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (hC : C.IsSymmetric) (hM : matchesPrefix (2 * r + 1) M C J)
    (hd : Module.finrank ℝ E = Module.finrank ℝ (momentBlock M (r + 1) 0).range) :
    cyclicPrefix r C J := by
  let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
  have hg := (prefix_gram r M C J hC hM).1
  have hd' : Module.finrank ℝ T.range = Module.finrank ℝ E := by
    rw [← hg, LinearMap.range_adjoint_comp_self, LinearMap.finrank_range_adjoint] at hd
    exact hd.symm
  rw [cyclicPrefix, ← synthesis_range]
  exact Submodule.eq_top_of_finrank_eq hd'

/-- A positive prefix admits a positive definite realization exactly when the two kernels agree. -/
theorem strict_realization_iff (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) :
    strict_realization_iff_statement r M := by
  rintro hreal
  constructor
  · rintro ⟨n, C, J, hC, hk, hM⟩
    exact strict_kernel_necessary r M C J hC hM hk
  · intro hk
    obtain ⟨n, C, J, hC, hM⟩ := hreal
    obtain ⟨hH, hS, hker, hd⟩ := prefix_necessary r M C J hC hM
    obtain ⟨C', J', hC', hM'⟩ := canonical_attainment r M hH hS hker
    have hc := cyclic_of_minimal_dimension r M C' J' hC'.isSymmetric hM'
      (finrank_euclideanSpace_fin)
    exact ⟨_, C', J', hC',
      (strict_canonical_iff r M C' J' hC' hM' hc).mpr hk, hM'⟩

def spectral_interval_realization_iff_statement
    (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) (a b : ℝ) : Prop :=
  0 ≤ a → a ≤ b → (∀ k ≤ 2 * r + 1, (M k).IsSymmetric) →
  ((∃ (n : ℕ) (C : State n →ₗ[ℝ] State n) (J : U →ₗ[ℝ] State n),
    (C - a • LinearMap.id).IsPositive ∧ (b • LinearMap.id - C).IsPositive ∧
      matchesPrefix (2 * r + 1) M C J) ↔
    (momentBlock M (r + 1) 0).IsPositive ∧
    (momentBlock M (r + 1) 1 - a • momentBlock M (r + 1) 0).IsPositive ∧
    (b • momentBlock M (r + 1) 0 - momentBlock M (r + 1) 1).IsPositive)

/-- Positivity descends through a surjective Gram compression. -/
theorem positivity_descent (T : U →ₗ[ℝ] E) (hT : Function.Surjective T)
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) :
    (T.adjoint ∘ₗ A ∘ₗ T).IsPositive → A.IsPositive := by
  intro h
  apply (LinearMap.isPositive_iff _).mpr
  refine ⟨hA, ?_⟩
  intro x
  obtain ⟨v, rfl⟩ := hT x
  simpa only [LinearMap.comp_apply, LinearMap.adjoint_inner_left] using h.inner_nonneg_left v

/-- Two block moment inequalities characterize realization in a closed nonnegative interval. -/
theorem spectral_interval_realization_iff
    (r : ℕ) (M : ℕ → U →ₗ[ℝ] U) (a b : ℝ) :
    spectral_interval_realization_iff_statement r M a b := by
  intro ha hab hsym
  constructor
  · rintro ⟨n, C, J, hCa, hbC, hM⟩
    have hC : C.IsPositive := by
      convert hCa.add (LinearMap.isPositive_id.smul_of_nonneg ha) using 1 <;> module
    let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
    obtain ⟨hg, hs⟩ := prefix_gram r M C J hC.isSymmetric hM
    refine ⟨(prefix_necessary r M C J hC hM).1, ?_, ?_⟩
    · convert hCa.adjoint_conj T using 1
      rw [← hs, ← hg]
      ext x
      simp
      module
    · convert hbC.adjoint_conj T using 1
      rw [← hs, ← hg]
      ext x
      simp
      module
  · rintro ⟨hH, hSa, hbS⟩
    have hS : (momentBlock M (r + 1) 1).IsPositive := by
      convert hSa.add (hH.smul_of_nonneg ha) using 1 <;> module
    have hker : (momentBlock M (r + 1) 0).ker ≤ (momentBlock M (r + 1) 1).ker := by
      intro v hv
      have hv' : momentBlock M (r + 1) 0 v = 0 := hv
      have hq1 := hSa.inner_nonneg_left v
      have hq2 := hbS.inner_nonneg_left v
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, hv', smul_zero,
        sub_zero, zero_sub, inner_neg_left] at hq1 hq2
      have hz : inner ℝ (momentBlock M (r + 1) 1 v) v = 0 := by linarith
      exact positive_zero _ hS v hz
    obtain ⟨C, J, hC, hM⟩ := canonical_attainment r M hH hS hker
    have hcyc := cyclic_of_minimal_dimension r M C J hC.isSymmetric hM finrank_euclideanSpace_fin
    let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
    have hT : Function.Surjective T :=
      LinearMap.range_eq_top.mp ((synthesis_range _ _).trans hcyc)
    obtain ⟨hg, hs⟩ := prefix_gram r M C J hC.isSymmetric hM
    refine ⟨_, C, J, ?_, ?_, hM⟩
    · apply positivity_descent T hT _ (hC.isSymmetric.sub (LinearMap.isPositive_id.smul_of_nonneg ha).isSymmetric)
      convert hSa using 1
      have he : T.adjoint ∘ₗ (C - a • LinearMap.id) ∘ₗ T =
          T.adjoint ∘ₗ C ∘ₗ T - a • (T.adjoint ∘ₗ T) := by
        ext x
        simp <;> module
      rw [he, hg, hs]
    · apply positivity_descent T hT _ ((LinearMap.isPositive_id.smul_of_nonneg (ha.trans hab)).isSymmetric.sub hC.isSymmetric)
      convert hbS using 1
      have he : T.adjoint ∘ₗ (b • LinearMap.id - C) ∘ₗ T =
          b • (T.adjoint ∘ₗ T) - T.adjoint ∘ₗ C ∘ₗ T := by
        ext x
        simp <;> module
      rw [he, hg, hs]

private theorem gram_quotient_carrier {P : Type}
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (H B : P →ₗ[ℝ] P) (hB : H = B.adjoint ∘ₗ B) :
    ∃ Q : (P ⧸ H.ker) ≃ₗ[ℝ] B.range,
      (∀ v : P, (Q (H.ker.mkQ v) : P) = B v) ∧
      (∀ v w : P, inner ℝ (Q (H.ker.mkQ v)) (Q (H.ker.mkQ w)) = inner ℝ v (H w)) := by
  have hk : H.ker = B.ker := by rw [hB, LinearMap.ker_adjoint_comp_self]
  rw [hk]
  let Q := B.quotKerEquivRange
  have hQ (v : P) : (Q (B.ker.mkQ v) : P) = B v :=
    B.quotKerEquivRange_apply_mk v
  refine ⟨Q, hQ, ?_⟩
  intro v w
  change inner ℝ (Q (B.ker.mkQ v) : P) (Q (B.ker.mkQ w) : P) = _
  rw [hQ, hQ, ← LinearMap.adjoint_inner_right]
  change inner ℝ v ((B.adjoint ∘ₗ B) w) = _
  rw [← hB]

/-- The Gram quotient carries the positive realization and has the exact Hankel rank. -/
theorem quotient_attainment (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (hH : (momentBlock M (r + 1) 0).IsPositive)
    (hS : (momentBlock M (r + 1) 1).IsPositive)
    (hk : (momentBlock M (r + 1) 0).ker ≤ (momentBlock M (r + 1) 1).ker) :
    ∃ B : Coeff U (r + 1) →ₗ[ℝ] Coeff U (r + 1),
      ∃ Q : (Coeff U (r + 1) ⧸ (momentBlock M (r + 1) 0).ker) ≃ₗ[ℝ] B.range,
      ∃ (CQ : Module.End ℝ (Coeff U (r + 1) ⧸ (momentBlock M (r + 1) 0).ker))
        (JQ : U →ₗ[ℝ] (Coeff U (r + 1) ⧸ (momentBlock M (r + 1) 0).ker)),
      Module.finrank ℝ (Coeff U (r + 1) ⧸ (momentBlock M (r + 1) 0).ker) =
        Module.finrank ℝ (momentBlock M (r + 1) 0).range ∧
      (∀ v w, inner ℝ (Q ((momentBlock M (r + 1) 0).ker.mkQ v))
        (Q ((momentBlock M (r + 1) 0).ker.mkQ w)) = inner ℝ v (momentBlock M (r + 1) 0 w)) ∧
      (∀ x y, inner ℝ (Q (CQ x)) (Q y) = inner ℝ (Q x) (Q (CQ y))) ∧
      (∀ x, 0 ≤ inner ℝ (Q (CQ x)) (Q x)) ∧
      (∀ k ≤ 2 * r + 1, ∀ u v, inner ℝ (Q (JQ u)) (Q ((CQ^k) (JQ v))) = inner ℝ u (M k v)) := by
  obtain ⟨B, hB, hd, C, hC, hg, hp, hspan, hshift⟩ := canonical_raw r M hH hS hk
  obtain ⟨Q, hQ, hQgram⟩ := gram_quotient_carrier _ B hB
  let e : Fin (r + 1) → U →ₗ[ℝ] B.range := fun i => B.rangeRestrict ∘ₗ coeffInsert (r + 1) i
  have hM := (generators_match r M C hC.isSymmetric e hg hp hshift).1
  let CQ := Q.symm.toLinearMap ∘ₗ C ∘ₗ Q.toLinearMap
  let JQ := Q.symm.toLinearMap ∘ₗ e 0
  have hcq (x) : Q (CQ x) = C (Q x) := by simp [CQ]
  have hjq (u) : Q (JQ u) = e 0 u := by simp [JQ]
  have hpower : ∀ k x, Q ((CQ^k) x) = (C^k) (Q x) := by
    intro k x
    simpa only [Module.End.pow_apply] using
      (Function.Semiconj.iterate_right hcq k x)
  refine ⟨B, Q, CQ, JQ, Q.finrank_eq.trans hd, hQgram, ?_, ?_, ?_⟩
  · intro x y
    rw [hcq, hcq]
    exact hC.isSymmetric _ _
  · intro x
    rw [hcq]
    exact hC.inner_nonneg_left _
  · intro k hk u v
    rw [hjq, hpower, hjq]
    have hh := hM k hk
    have hu := LinearMap.congr_fun hh v
    have hv := congrArg (inner ℝ u) hu
    simpa only [moment, LinearMap.comp_apply, LinearMap.adjoint_inner_right] using hv

/-- Two identical Gram operators induce an isometric embedding of the generated states. -/
theorem gram_isometry (T : P →ₗ[ℝ] E) (S : P →ₗ[ℝ] V)
    (hT : Function.Surjective T) (hg : T.adjoint ∘ₗ T = S.adjoint ∘ₗ S) :
    ∃ q : E →ₗᵢ[ℝ] V, q.toLinearMap ∘ₗ T = S := by
  have hk : T.ker ≤ S.ker := by
    rw [← LinearMap.ker_adjoint_comp_self T, hg, LinearMap.ker_adjoint_comp_self]
  let B := T.liftOfSurjective hT ⟨S, hk⟩
  have hB (x : P) : B (T x) = S x := T.equivOfSurjective_apply hT hk
  have hi (x y : E) : inner ℝ (B x) (B y) = inner ℝ x y := by
    obtain ⟨v, rfl⟩ := hT x
    obtain ⟨w, rfl⟩ := hT y
    rw [hB, hB, ← LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_right]
    exact congrArg (inner ℝ v) (LinearMap.congr_fun hg.symm w)
  refine ⟨B.isometryOfInner hi, ?_⟩
  ext x
  exact hB x

/-- A common odd prefix identifies the canonical state space inside any competing realization. -/
theorem prefix_embedding (r : ℕ) (M : ℕ → U →ₗ[ℝ] U)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (C' : V →ₗ[ℝ] V) (J' : U →ₗ[ℝ] V)
    (hC : C.IsSymmetric) (hC' : C'.IsSymmetric)
    (hM : matchesPrefix (2 * r + 1) M C J) (hM' : matchesPrefix (2 * r + 1) M C' J')
    (hcyc : cyclicPrefix r C J) :
    ∃ q : E →ₗᵢ[ℝ] V,
      (∀ j ≤ r, q.toLinearMap ∘ₗ (C^j) ∘ₗ J = (C'^j) ∘ₗ J') ∧
      (∀ x y, inner ℝ (q x) (C' (q y)) = inner ℝ x (C y)) := by
  let T := synthesis (r + 1) (fun i => (C^i.val) ∘ₗ J)
  let S := synthesis (r + 1) (fun i => (C'^i.val) ∘ₗ J')
  have hT : Function.Surjective T := by
    apply LinearMap.range_eq_top.mp
    exact (synthesis_range _ _).trans hcyc
  obtain ⟨hg, hs⟩ := prefix_gram r M C J hC hM
  obtain ⟨hg', hs'⟩ := prefix_gram r M C' J' hC' hM'
  obtain ⟨q, hq⟩ := gram_isometry T S hT (hg.trans hg'.symm)
  have hq' (v : Coeff U (r + 1)) : q (T v) = S v := LinearMap.congr_fun hq v
  refine ⟨q, ?_, ?_⟩
  · intro j hj
    ext u
    have hh := hq' (coeffInsert (r + 1) ⟨j, by omega⟩ u)
    simpa only [T, S, synthesis_insert, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap] using hh
  · intro x y
    obtain ⟨v, rfl⟩ := hT x
    obtain ⟨w, rfl⟩ := hT y
    rw [hq', hq', ← LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_right]
    exact congrArg (inner ℝ v) (LinearMap.congr_fun (hs'.trans hs.symm) w)

/-- An isometric intertwining that preserves the input preserves all future moments. -/
theorem intertwining_moments (q : E →ₗᵢ[ℝ] V)
    (C : E →ₗ[ℝ] E) (J : U →ₗ[ℝ] E)
    (C' : V →ₗ[ℝ] V) (J' : U →ₗ[ℝ] V)
    (hC : q.toLinearMap ∘ₗ C = C' ∘ₗ q.toLinearMap)
    (hJ : q.toLinearMap ∘ₗ J = J') : ∀ k, moment C' J' k = moment C J k := by
  have hp : ∀ k x, (C'^k) (q x) = q ((C^k) x) := by
    intro k x
    exact LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hC.symm k) x
  intro k
  ext v
  apply ext_inner_left ℝ
  intro u
  have hJu := LinearMap.congr_fun hJ u
  have hJv := LinearMap.congr_fun hJ v
  simp only [LinearMap.comp_apply] at hJu hJv
  simp only [moment, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  rw [← hJu, ← hJv]
  change inner ℝ (q (J u)) ((C'^k) (q (J v))) = _
  rw [hp, q.inner_map_map]

end D5.S3.Observer.PositiveMoments.PrefixPositiveRealization
