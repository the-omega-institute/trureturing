/- GID: D5/S3/Arith/AbsoluteValues/Heights/NumberFieldIntegralLattice
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/NumberFieldIntegralLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral points of a subspace have unit Pluecker ideal in the primitive normalization. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.MixedLattice
public import D5.S3.Arith.AbsoluteValues.Heights.PseudoBasis
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import D5.S3.Arith.AbsoluteValues.Heights.Duality
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

public section

noncomputable section

open Module NumberField NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- The tuples of algebraic integers, as an `𝓞 K`-submodule of `ι → K`. -/
@[expose] def NumberField.integralTuples (K : Type*) [Field K] (ι : Type*) :
    Submodule (𝓞 K) (ι → K) :=
  Submodule.pi Set.univ fun _ ↦ (1 : Submodule (𝓞 K) K)

/-- The **integral points** `V ∩ (𝓞 K)ⁱ` of a subspace of `Kⁱ`. -/
@[expose] def Submodule.integerPoints (V : Submodule K (ι → K)) : Submodule (𝓞 K) (ι → K) :=
  V.restrictScalars (𝓞 K) ⊓ integralTuples K ι

section Data

open scoped nonZeroDivisors

variable [Finite ι]

variable (K ι) in
/-- Entrywise inclusion of integral tuples. -/
@[expose] def NumberField.piIntCast : (ι → 𝓞 K) →ₗ[𝓞 K] (ι → K) :=
  LinearMap.pi fun l ↦ (Algebra.linearMap (𝓞 K) K).comp (LinearMap.proj l)

/-- **The pseudo-basis of the integral points of a subspace.** -/
theorem Submodule.exists_pseudoBasis_integerPoints (V : Submodule K (ι → K)) :
    ∃ (y : Fin (finrank K V) → (ι → K)) (𝔞 : Fin (finrank K V) → FractionalIdeal (𝓞 K)⁰ K),
      LinearIndependent K y ∧ (∀ i, 𝔞 i ≠ 0) ∧ (∀ i, y i ∈ V.integerPoints) ∧
      (∀ x, x ∈ V.integerPoints ↔
        ∃ c : Fin (finrank K V) → K, (∀ i, c i ∈ 𝔞 i) ∧ x = ∑ i, c i • y i) := by
  classical
  have hPseudo (k : ℕ) (M : Submodule (𝓞 K) (ι → K)) (hM : M.FG)
      (hk : finrank K (Submodule.span K (M : Set (ι → K))) = k) :
      ∃ (y : Fin k → (ι → K)) (𝔞 : Fin k → FractionalIdeal (𝓞 K)⁰ K),
        LinearIndependent K y ∧ (∀ i, 𝔞 i ≠ 0) ∧ (∀ i, y i ∈ M) ∧
        (∀ x, x ∈ M ↔ ∃ c : Fin k → K, (∀ i, c i ∈ 𝔞 i) ∧
          x = ∑ i, c i • y i) := by
    obtain ⟨y, 𝔞, hli, h𝔞, hchar⟩ := Submodule.exists_pseudoBasis k M hM hk
    choose a ha ha0 using fun i ↦ (show ∃ a ∈ 𝔞 i, a ≠ 0 from by
      by_contra hcon
      push Not at hcon
      exact h𝔞 i (FractionalIdeal.eq_zero_iff.2 hcon))
    have hmem𝔞' : ∀ (i : Fin k) (z : K),
        z ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ (a i)⁻¹ * 𝔞 i ↔ a i * z ∈ 𝔞 i :=
      fun i z ↦ by
        rw [(fun {b : K} (hb : b ≠ 0) (I : FractionalIdeal (𝓞 K)⁰ K) (z : K) =>
          (show z ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ b * I ↔ b⁻¹ * z ∈ I from by
            constructor
            · intro h
              have h2 : b⁻¹ * z ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ b⁻¹ *
                  (FractionalIdeal.spanSingleton (𝓞 K)⁰ b * I) :=
                FractionalIdeal.mul_mem_mul
                  (FractionalIdeal.mem_spanSingleton_self _ _) h
              rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
                inv_mul_cancel₀ hb, FractionalIdeal.spanSingleton_one, one_mul] at h2
            · intro h
              have h2 := FractionalIdeal.mul_mem_mul
                (FractionalIdeal.mem_spanSingleton_self (𝓞 K)⁰ b) h
              rwa [mul_inv_cancel_left₀ hb] at h2)) (inv_ne_zero (ha0 i)), inv_inv]
    refine ⟨fun i ↦ a i • y i,
      fun i ↦ FractionalIdeal.spanSingleton (𝓞 K)⁰ (a i)⁻¹ * 𝔞 i,
      ?_, ?_, ?_, ?_⟩
    · exact hli.units_smul (fun i ↦ Units.mk0 (a i) (ha0 i))
    · intro i
      exact mul_ne_zero
        ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (inv_ne_zero (ha0 i))) (h𝔞 i)
    · intro i
      refine (hchar _).2 ⟨Pi.single i (a i), fun j ↦ ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simpa using ha j
        · simp [hj, (𝔞 j).zero_mem]
      · rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [hj]
        · simp
    · intro x
      rw [hchar x]
      constructor
      · rintro ⟨c, hc, rfl⟩
        refine ⟨fun i ↦ (a i)⁻¹ * c i, fun i ↦ ?_, ?_⟩
        · rw [hmem𝔞' i, mul_inv_cancel_left₀ (ha0 i)]
          exact hc i
        · refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [smul_smul]
          congr 1
          rw [mul_comm ((a i)⁻¹) (c i), mul_assoc, inv_mul_cancel₀ (ha0 i), mul_one]
      · rintro ⟨c, hc, rfl⟩
        refine ⟨fun i ↦ a i * c i, fun i ↦ (hmem𝔞' i _).1 (hc i), ?_⟩
        exact Finset.sum_congr rfl fun i _ ↦ by simp [smul_smul, mul_comm]
  exact hPseudo _ V.integerPoints ((fun (V : Submodule K (ι → K)) => (show V.integerPoints.FG from by
  have hle : V.integerPoints ≤ integralTuples K ι := inf_le_right
  have hN : IsNoetherian (𝓞 K) ↥(integralTuples K ι) :=
    isNoetherian_of_fg_of_noetherian _ (show (integralTuples K ι).FG from by
  rw [← (show LinearMap.range (piIntCast K ι) = integralTuples K ι from by
  ext x
  rw [LinearMap.mem_range, (show x ∈ NumberField.integralTuples K ι ↔
      ∀ l, ∃ z : 𝓞 K, (z : K) = x l from by
      simp [NumberField.integralTuples, Submodule.mem_pi, Submodule.one_eq_range])]
  constructor
  · rintro ⟨z, rfl⟩ l
    exact ⟨z l, rfl⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext fun l ↦ hz l⟩), LinearMap.range_eq_map]
  exact Submodule.FG.map _ (Module.Finite.fg_top))
  have h1 : (V.integerPoints.comap (integralTuples K ι).subtype).FG := IsNoetherian.noetherian _
  have h2 : V.integerPoints
      = Submodule.map (integralTuples K ι).subtype
          (V.integerPoints.comap (integralTuples K ι).subtype) :=
    (Submodule.map_comap_eq_self (by simpa using hle)).symm
  rw [h2]
  exact h1.map _)) V)
    (by rw [((fun (V : Submodule K (ι → K)) => (show Submodule.span K (V.integerPoints : Set (ι → K)) = V from by
  refine le_antisymm (Submodule.span_le.2 fun x hx ↦ hx.1) fun v hv ↦ ?_
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (𝓞 K)⁰ (Finset.univ : Finset ι) v
  have hdv : ((d : 𝓞 K) : K) • v ∈ V.integerPoints := by
    refine ⟨V.smul_mem _ hv, (show ∀ {x : ι → K}, x ∈ NumberField.integralTuples K ι ↔
      ∀ l, ∃ z : 𝓞 K, (z : K) = x l from by
      intro x; simp [NumberField.integralTuples, Submodule.mem_pi, Submodule.one_eq_range]).2 fun l ↦ ?_⟩
    obtain ⟨z, hz⟩ := hd l (Finset.mem_univ l)
    exact ⟨z, by simpa [Algebra.smul_def] using hz⟩
  have hdK : ((d : 𝓞 K) : K) ≠ 0 := by
    simp [IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) d.2]
  have : v = (((d : 𝓞 K) : K))⁻¹ • (((d : 𝓞 K) : K) • v) := by
    rw [inv_smul_smul₀ hdK]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hdv))) V)])

end Data

section Defs

variable [Finite ι]

open scoped Classical in
/-- The embedding of `Kⁱ` into the euclidean mixed space of `ι`-tuples. -/
@[expose] def mixedPiEmb (K : Type*) [Field K] [NumberField K] (ι : Type*) :
    (ι → K) →ₗ[ℤ] mixedPi K ι :=
  (LinearMap.restrictScalars ℤ (toMixedPi K ι).toLinearMap) ∘ₗ
    AddMonoidHom.toIntLinearMap (AddMonoidHom.pi fun l ↦
      (mixedEmbedding K).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : ι ↦ K) l))

open scoped Classical in
/-- The **real span** of a subspace of `Kⁱ` in the euclidean mixed space of tuples. -/
@[expose] def Submodule.mixedSpan (V : Submodule K (ι → K)) : Submodule ℝ (mixedPi K ι) :=
  Submodule.span ℝ (mixedPiEmb K ι '' (V : Set (ι → K)))

open scoped Classical in
/-- The Borel structure on the real span of a subspace. Declaring it once keeps instance search
off the nested `WithLp` structure of the mixed space at every use site. -/
instance instBorelSpaceMixedSpan (V : Submodule K (ι → K)) :
    BorelSpace ↥V.mixedSpan :=
  Subtype.borelSpace _

open scoped Classical in
/-- The real span of a subspace is finite-dimensional. -/
instance instFiniteDimensionalMixedSpan (V : Submodule K (ι → K)) :
    FiniteDimensional ℝ ↥V.mixedSpan :=
  inferInstance

open scoped Classical in
/-- The **lattice of integral points** of a subspace, inside its real span: the object whose
covolume the milestone computes. -/
@[expose] def Submodule.mixedLattice (V : Submodule K (ι → K)) : Submodule ℤ ↥V.mixedSpan :=
  Submodule.comap ((V.mixedSpan.subtype).restrictScalars ℤ)
    (Submodule.map (mixedPiEmb K ι) (V.integerPoints.restrictScalars ℤ))

end Defs

variable [Fintype ι]

open scoped Classical in
/-- The euclidean measure on the real span of a subspace. Declaring it once keeps instance search
off the nested `WithLp` structure of the mixed space at every use site. -/
noncomputable instance instMeasureSpaceMixedSpan (V : Submodule K (ι → K)) :
    MeasureTheory.MeasureSpace ↥V.mixedSpan :=
  measureSpaceOfInnerProductSpace

open scoped Classical in
/-- The euclidean measure on the real span of a subspace is a Haar measure. -/
instance instIsAddHaarMeasureMixedSpan (V : Submodule K (ι → K)) :
    (MeasureTheory.volume : MeasureTheory.Measure ↥V.mixedSpan).IsAddHaarMeasure :=
  inferInstance

section Product

open Matrix

open scoped Classical in
/-- **The Gram determinant of a product basis is the product of the Gram determinants.** The
euclidean space of `k`-tuples is the orthogonal sum of `k` copies of the euclidean mixed space, so
a basis whose members are supported in a single coordinate has block diagonal Gram matrix. -/
theorem NumberField.det_gram_pi {k d : ℕ} (c : Fin k → Basis (Fin d) ℝ (euclidean.mixedSpace K))
    (bE : Fin d × Fin k → mixedPi K (Fin k))
    (hbE : ∀ (j : Fin d) (i : Fin k),
      bE (j, i) = toMixedPi K (Fin k) (Pi.single i ((euclidean.toMixed K) (c i j)))) :
    (Matrix.of fun p q : Fin d × Fin k ↦ inner ℝ (bE p) (bE q)).det
      = ∏ i, (Matrix.of fun j j' : Fin d ↦ inner ℝ (c i j) (c i j')).det := by
  classical
  have hEuclidean (a b : euclidean.mixedSpace K) :
      inner ℝ a b = mixedTrace K (star (euclidean.toMixed K a) *
        (euclidean.toMixed K b)) := by
    rw [show (inner ℝ a b : ℝ) = inner ℝ a.ofLp.1 b.ofLp.1 +
        inner ℝ a.ofLp.2 b.ofLp.2 from rfl, PiLp.inner_apply, PiLp.inner_apply]
    simp only [mixedTrace, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul,
      Pi.mul_apply, Prod.fst_star, Pi.star_apply, star_trivial, Prod.snd_star, Pi.star_apply,
      Complex.star_def, RCLike.inner_apply, Complex.inner, conj_trivial]
    congr 1
    · exact Finset.sum_congr rfl fun w _ ↦ by rw [mul_comm]; rfl
    · exact Finset.sum_congr rfl fun w _ ↦ by rw [mul_comm]; rfl
  have hinner (u v : Fin k → mixedSpace K) :
      inner ℝ (toMixedPi K (Fin k) u) (toMixedPi K (Fin k) v) =
        ∑ l, mixedTrace K (star (u l) * v l) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hEuclidean]
    congr 1
  have key : (Matrix.of fun p q : Fin d × Fin k ↦ inner ℝ (bE p) (bE q))
      = Matrix.blockDiagonal
        (fun i ↦ Matrix.of fun j j' : Fin d ↦ (inner ℝ (c i j) (c i j') : ℝ)) := by
    ext ⟨j, i⟩ ⟨j', i'⟩
    simp only [Matrix.of_apply]
    rw [hbE j i, hbE j' i', hinner]
    by_cases h : i = i'
    · subst h
      rw [Matrix.blockDiagonal_apply_eq, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, Pi.single_eq_same, ← hEuclidean]
        rfl
      · intro l _ hl
        rw [Pi.single_eq_of_ne hl]
        simp
      · simp
    · rw [Matrix.blockDiagonal_apply_ne _ _ _ h]
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      rcases eq_or_ne l i with rfl | hl
      · rw [Pi.single_eq_of_ne h]
        simp
      · rw [Pi.single_eq_of_ne hl]
        simp
  rw [key, Matrix.det_blockDiagonal]

end Product

section Primitive

open exteriorPower

open scoped nonZeroDivisors

omit [Fintype ι] in
/-- If every product of elements of the `I i` lies in `J`, then the product of the `I i` does. -/
private theorem prod_le_of_forall {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    ∀ (n : ℕ) (I : Fin n → Submodule R A) (J : Submodule R A),
    (∀ a : Fin n → A, (∀ i, a i ∈ I i) → (∏ i, a i) ∈ J) → (∏ i, I i) ≤ J := by
  intro n
  induction n with
  | zero =>
    intro I J h
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    have h1 := h (fun i ↦ i.elim0) (fun i ↦ i.elim0)
    simp only [Finset.univ_eq_empty, Finset.prod_empty] at h1
    rw [Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff]
    exact h1
  | succ n ih =>
    intro I J h
    rw [Fin.prod_univ_succ]
    refine Submodule.mul_le.2 fun x hx y hy ↦ ?_
    have hy' := ih (fun i ↦ I i.succ) (Submodule.comap (LinearMap.mulLeft R x) J) ?_ hy
    · simpa using hy'
    · intro a ha
      have h2 := h (Fin.cons x a) (Fin.cases hx ha)
      rw [Fin.prod_cons] at h2
      simpa using h2

variable [LinearOrder ι]

variable (V : Submodule K (ι → K)) {k : ℕ} {y : Fin k → (ι → K)}
  {𝔞 : Fin k → FractionalIdeal (𝓞 K)⁰ K} {p : Set.powersetCard ι k → 𝓞 K}

/-- **The Plücker ideal of a saturated module is integral.** -/
theorem Submodule.prod_mul_plucker_le_one
    (hchar : ∀ x, x ∈ V.integerPoints ↔
      ∃ c : Fin k → K, (∀ i, c i ∈ 𝔞 i) ∧ x = ∑ i, c i • y i)
    (hp : ∀ s, (p s : K) = plucker k y s) :
    (∏ i, 𝔞 i) * (Ideal.span (Set.range p) : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
  have nativeSource152 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (c : Fin k → R) (v : Fin k → (ι → R))
      (s : Set.powersetCard ι k) => (show exteriorPower.plucker k (fun i ↦ c i • v i) s = (∏ i, c i) * exteriorPower.plucker k v s from by
    classical
    rw [exteriorPower.plucker, exteriorPower.plucker,
      show ((exteriorPower.ιMulti R k) fun i ↦ c i • v i) = (∏ i, c i) • (exteriorPower.ιMulti R k) v from
        MultilinearMap.map_smul_univ (exteriorPower.ιMulti R k).toMultilinearMap c v]
    simp)))
  classical
  set P : Submodule (𝓞 K) K :=
    ((Ideal.span (Set.range p) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) with hP
  set Q : Submodule (𝓞 K) K :=
    { carrier := {x | ∀ z ∈ P, x * z ∈ (1 : Submodule (𝓞 K) K)}
      add_mem' := fun hx hy z hz ↦ by
        rw [add_mul]; exact Submodule.add_mem _ (hx z hz) (hy z hz)
      zero_mem' := fun z _ ↦ by rw [zero_mul]; exact Submodule.zero_mem _
      smul_mem' := fun r x hx z hz ↦ by
        rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ (hx z hz) } with hQ
  have hgen : ∀ (a : Fin k → K), (∀ i, a i ∈ 𝔞 i) → ∀ s,
      (∏ i, a i) * ((p s : K)) ∈ (1 : Submodule (𝓞 K) K) := by
    intro a ha s
    have hint : ∀ i, a i • y i ∈ integralTuples K ι := fun i ↦ by
      have hm : a i • y i ∈ V.integerPoints := by
        refine (hchar _).2 ⟨Pi.single i (a i), fun j ↦ ?_, ?_⟩
        · rcases eq_or_ne j i with rfl | hj
          · simpa using ha j
          · simp [hj, (𝔞 j).zero_mem]
        · rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj; simp [hj]
          · simp
      exact hm.2
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 K, (z : K) = plucker k (fun i ↦ a i • y i) s := by
      have nativeSource18 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) => (show exteriorPower.plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det from by
        classical
        rw [exteriorPower.plucker, Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
        simp)))
      have nativeSource37 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {S : Type _} [CommRing S] (f : R →+* S) (k : ℕ) (v : Fin k → (ι → R))
          (s : Set.powersetCard ι k) => (show exteriorPower.plucker k (fun i ↦ f ∘ v i) s = f (exteriorPower.plucker k v s) from by
        classical
        rw [nativeSource18, nativeSource18, RingHom.map_det]
        rfl)))
      choose w hw using fun i ↦ (show ∀ {x : ι → K}, x ∈ NumberField.integralTuples K ι ↔
          ∀ l, ∃ z : 𝓞 K, (z : K) = x l from by
          intro x; simp [NumberField.integralTuples, Submodule.mem_pi, Submodule.one_eq_range]).1 (hint i)
      refine ⟨plucker k w s, ?_⟩
      have hy' : (fun i ↦ a i • y i) = fun i ↦ (algebraMap (𝓞 K) K) ∘ (w i) := by
        funext i l
        exact (hw i l).symm
      rw [hy', nativeSource37 (algebraMap (𝓞 K) K) k w s]
    refine Submodule.mem_one.2 ⟨z, ?_⟩
    rw [show (algebraMap (𝓞 K) K) z = (z : K) from rfl, hz, hp s, nativeSource152]
  have hQle : (∏ i, ((𝔞 i : Submodule (𝓞 K) K))) ≤ Q := by
    refine prod_le_of_forall k _ _ fun a ha ↦ ?_
    intro z hz
    obtain ⟨z', hz', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem x hx => obtain ⟨s, rfl⟩ := hx; exact hgen a ha s
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, mul_add]; exact Submodule.add_mem _ hu hv
    | smul r u _ hu =>
      rw [smul_eq_mul, map_mul, ← mul_assoc, mul_comm ((∏ i, a i)) _, mul_assoc]
      exact Submodule.smul_mem _ r hu
  have hCoeProd : ∀ (n : ℕ) (I : Fin n → FractionalIdeal (𝓞 K)⁰ K),
      ((∏ i, I i : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
        = ∏ i, ((I i : Submodule (𝓞 K) K)) := by
    intro n
    induction n with
    | zero => intro I; simp
    | succ n ih =>
      intro I
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ, FractionalIdeal.coe_mul, ih]
  rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, hCoeProd,
    FractionalIdeal.coe_one]
  exact Submodule.mul_le.2 fun x hx z hz ↦ hQle hx z hz

/-- **Primitivity: the Plücker ideal of the integral points of a subspace is the unit ideal.**
This is Schmidt's Lemmas 5 and 6 over a number field, and the only place the saturation of
`V ∩ (𝓞 K)ⁱ` is used. -/
theorem Submodule.prod_mul_plucker_eq_one
    (hy : LinearIndependent K y) (h𝔞 : ∀ i, 𝔞 i ≠ 0)
    (hchar : ∀ x, x ∈ V.integerPoints ↔
      ∃ c : Fin k → K, (∀ i, c i ∈ 𝔞 i) ∧ x = ∑ i, c i • y i)
    (hp : ∀ s, (p s : K) = plucker k y s) :
    (∏ i, 𝔞 i) * (Ideal.span (Set.range p) : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  have nativeSource18 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) => (show exteriorPower.plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det from by
    classical
    rw [exteriorPower.plucker, Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp)))
  have nativeSource21 := (open Module in (fun {k : ℕ} (s : Set.powersetCard (Fin k) k) => (show ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) = (id : Fin k → Fin k) from by
    classical
    have hs : (s : Finset (Fin k)) = Finset.univ := Finset.eq_univ_of_card _ (by simp)
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique _ (fun x ↦ hs ▸ Finset.mem_univ x) strictMono_id).symm)))
  have nativeSource37 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {S : Type _} [CommRing S] (f : R →+* S) (k : ℕ) (v : Fin k → (ι → R))
      (s : Set.powersetCard ι k) => (show exteriorPower.plucker k (fun i ↦ f ∘ v i) s = f (exteriorPower.plucker k v s) from by
    classical
    rw [nativeSource18, nativeSource18, RingHom.map_det]
    rfl)))
  have nativeSource152 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (c : Fin k → R) (v : Fin k → (ι → R))
      (s : Set.powersetCard ι k) => (show exteriorPower.plucker k (fun i ↦ c i • v i) s = (∏ i, c i) * exteriorPower.plucker k v s from by
    classical
    rw [exteriorPower.plucker, exteriorPower.plucker,
      show ((exteriorPower.ιMulti R k) fun i ↦ c i • v i) = (∏ i, c i) • (exteriorPower.ιMulti R k) v from
        MultilinearMap.map_smul_univ (exteriorPower.ιMulti R k).toMultilinearMap c v]
    simp)))
  classical
  have hle := Submodule.prod_mul_plucker_le_one V hchar hp
  obtain ⟨𝔠₀, h𝔠₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  suffices h : 𝔠₀ = ⊤ by rw [← h𝔠₀, h]; simp
  by_contra hne
  obtain ⟨𝔮, h𝔮max, h𝔮le⟩ := Ideal.exists_le_maximal 𝔠₀ hne
  have h𝔮inst : 𝔮.IsMaximal := h𝔮max
  have hsm : ∀ (J : FractionalIdeal (𝓞 K)⁰ K) (r : 𝓞 K) (x : K), x ∈ J → (r : K) * x ∈ J :=
    fun J r x hx ↦ by
      have h := Submodule.smul_mem ((J : Submodule (𝓞 K) K)) r hx
      rwa [Algebra.smul_def] at h
  have h𝔮bot : 𝔮 ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField h𝔮max (NumberField.RingOfIntegers.not_isField K)
  have h𝔮ne : (𝔮 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    simp [h𝔮bot]
  -- choose `a i ∈ 𝔞 i` outside `𝔮 𝔞 i`
  have hstep : ∀ i, ∃ a ∈ 𝔞 i, a ∉ (𝔮 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 i := by
    intro i
    by_contra hcon
    push Not at hcon
    have hle2 : 𝔞 i ≤ (𝔮 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 i := hcon
    have hone : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤ (𝔮 : FractionalIdeal (𝓞 K)⁰ K) := by
      calc (1 : FractionalIdeal (𝓞 K)⁰ K) = 𝔞 i * (𝔞 i)⁻¹ := (mul_inv_cancel₀ (h𝔞 i)).symm
        _ ≤ ((𝔮 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 i) * (𝔞 i)⁻¹ := by
            gcongr
        _ = (𝔮 : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [mul_assoc, mul_inv_cancel₀ (h𝔞 i), mul_one]
    rw [show (1 : FractionalIdeal (𝓞 K)⁰ K) = ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      by simp, FractionalIdeal.coeIdeal_le_coeIdeal] at hone
    exact h𝔮max.ne_top (top_le_iff.1 hone)
  choose a ha hanot using hstep
  have hint : ∀ i, a i • y i ∈ integralTuples K ι := fun i ↦ by
      have hm : a i • y i ∈ V.integerPoints := by
        refine (hchar _).2 ⟨Pi.single i (a i), fun j ↦ ?_, ?_⟩
        · rcases eq_or_ne j i with rfl | hj
          · simpa using ha j
          · simp [hj, (𝔞 j).zero_mem]
        · rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hj; simp [hj]
          · simp
      exact hm.2
  choose w hw using fun i ↦ (show ∀ {x : ι → K}, x ∈ NumberField.integralTuples K ι ↔
      ∀ l, ∃ z : 𝓞 K, (z : K) = x l from by
      intro x; simp [NumberField.integralTuples, Submodule.mem_pi, Submodule.one_eq_range]).1 (hint i)
  have hwy : (fun i ↦ (algebraMap (𝓞 K) K) ∘ (w i)) = fun i ↦ a i • y i := by
    funext i l; exact hw i l
  have hplk : ∀ s, ((plucker k w s : 𝓞 K) : K) = (∏ i, a i) * ((p s : K)) := by
    intro s
    have h1 := nativeSource37 (algebraMap (𝓞 K) K) k w s
    rw [hwy, nativeSource152, ← hp s] at h1
    exact h1.symm
  have hProdMem : ∀ (n : ℕ) (I : Fin n → FractionalIdeal (𝓞 K)⁰ K)
      (b : Fin n → K), (∀ i, b i ∈ I i) → (∏ i, b i) ∈ (∏ i, I i) := by
    intro n
    induction n with
    | zero =>
      intro I b _
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    | succ n ih =>
      intro I b hb
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      exact FractionalIdeal.mul_mem_mul (hb 0) (ih _ _ fun i ↦ hb i.succ)
  have hq𝔮 : ∀ s, plucker k w s ∈ 𝔮 := by
    intro s
    have h1 : ((plucker k w s : 𝓞 K) : K) ∈
        ((∏ i, 𝔞 i) * (Ideal.span (Set.range p) : FractionalIdeal (𝓞 K)⁰ K)) := by
      rw [hplk s]
      exact FractionalIdeal.mul_mem_mul (hProdMem k 𝔞 a ha)
        ((FractionalIdeal.mem_coeIdeal _).2 ⟨p s, Ideal.subset_span ⟨s, rfl⟩, rfl⟩)
    rw [← h𝔠₀] at h1
    obtain ⟨q', hq', hq'eq⟩ := (FractionalIdeal.mem_coeIdeal _).1 h1
    have : q' = plucker k w s := by
      exact_mod_cast hq'eq
    exact h𝔮le (this ▸ hq')
  -- the reductions of the `a i • y i` are dependent over the residue field
  have hzero : plucker k (fun i ↦ (Ideal.Quotient.mk 𝔮) ∘ (w i)) = 0 := by
    funext s
    rw [nativeSource37 (Ideal.Quotient.mk 𝔮) k w s]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hq𝔮 s)
  let _ : Field (𝓞 K ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have hdependent : ¬ LinearIndependent (𝓞 K ⧸ 𝔮)
      (fun i ↦ (Ideal.Quotient.mk 𝔮) ∘ w i) := by
    intro hv
    have hmulti : exteriorPower.ιMulti (𝓞 K ⧸ 𝔮) k
        (fun i ↦ (Ideal.Quotient.mk 𝔮) ∘ w i) ≠ 0 := by
      have h := (exteriorPower.ιMulti_family_linearIndependent_field k hv).ne_zero
        (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
      rwa [exteriorPower.ιMulti_family, nativeSource21, Function.comp_id] at h
    apply hmulti
    apply (((Pi.basisFun (𝓞 K ⧸ 𝔮) ι).exteriorPower k).equivFun).injective
    simpa only [exteriorPower.plucker, map_zero] using hzero
  obtain ⟨cq, hcqsum, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1
    hdependent
  choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (cq i)
  set u : ι → K := fun l ↦ ∑ i, ((c i : K) * a i) * (y i l) with hu
  have huV : u ∈ V.integerPoints := by
    refine (hchar u).2 ⟨fun i ↦ (c i : K) * a i, fun i ↦ ?_, ?_⟩
    · exact hsm (𝔞 i) (c i) _ (ha i)
    · funext l
      simp [hu, Finset.sum_apply]
  have huq : ∀ l, u l ∈ ((𝔮 : FractionalIdeal (𝓞 K)⁰ K)) := by
    intro l
    have h1 : (∑ i, c i * w i l : 𝓞 K) ∈ 𝔮 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      have h2 := congrFun hcqsum l
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
        Pi.zero_apply] at h2
      rw [← h2]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, hc i]
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨∑ i, c i * w i l, h1, ?_⟩
    rw [hu, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [map_mul, show (algebraMap (𝓞 K) K) (w i l) = ((w i l : 𝓞 K) : K) from rfl, hw i l]
      simp [mul_assoc]
  have hmul : ∀ t ∈ ((𝔮 : FractionalIdeal (𝓞 K)⁰ K))⁻¹, ∀ i, t * ((c i : K) * a i) ∈ 𝔞 i := by
    intro t ht
    have htu : t • u ∈ V.integerPoints := by
      refine ⟨V.smul_mem t huV.1, (show ∀ {x : ι → K}, x ∈ NumberField.integralTuples K ι ↔
      ∀ l, ∃ z : 𝓞 K, (z : K) = x l from by
      intro x; simp [NumberField.integralTuples, Submodule.mem_pi, Submodule.one_eq_range]).2 fun l ↦ ?_⟩
      have h3 : t * u l ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [← inv_mul_cancel₀ h𝔮ne]
        exact FractionalIdeal.mul_mem_mul ht (huq l)
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 h3
      exact ⟨z, by simpa using hz⟩
    obtain ⟨d, hd, hdeq⟩ := (hchar _).1 htu
    have heq : ∀ i, d i - t * ((c i : K) * a i) = 0 := by
      refine Fintype.linearIndependent_iff.1 hy _ ?_
      have h4 : ∑ i, (t * ((c i : K) * a i)) • y i = t • u := by
        rw [hu]
        funext l
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      simp only [sub_smul, Finset.sum_sub_distrib, h4, ← hdeq, sub_self]
    intro i
    rw [← sub_eq_zero.1 (heq i)]
    exact hd i
  have hcq : ∀ i, c i ∈ 𝔮 := by
    intro i
    by_contra hci
    have hsub : ((𝔮 : FractionalIdeal (𝓞 K)⁰ K))⁻¹ *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ ((c i : K) * a i) ≤ 𝔞 i := by
      refine FractionalIdeal.mul_le.2 fun t ht z hz ↦ ?_
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hz
      rw [Algebra.smul_def, ← mul_assoc, mul_comm t _, mul_assoc]
      exact hsm (𝔞 i) r _ (hmul t ht i)
    have hmem : ((c i : K) * a i) ∈ ((𝔮 : FractionalIdeal (𝓞 K)⁰ K)) * 𝔞 i := by
      have h5 : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((c i : K) * a i)
          ≤ (𝔮 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 i := by
        calc FractionalIdeal.spanSingleton (𝓞 K)⁰ ((c i : K) * a i)
            = (𝔮 : FractionalIdeal (𝓞 K)⁰ K) * (((𝔮 : FractionalIdeal (𝓞 K)⁰ K))⁻¹ *
                FractionalIdeal.spanSingleton (𝓞 K)⁰ ((c i : K) * a i)) := by
              rw [← mul_assoc, mul_inv_cancel₀ h𝔮ne, one_mul]
          _ ≤ (𝔮 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 i := by gcongr
      exact h5 (FractionalIdeal.mem_spanSingleton_self _ _)
    obtain ⟨r, m, hm, hrm⟩ := Ideal.IsMaximal.exists_inv h𝔮max hci
    refine hanot i ?_
    have hai : a i = (r : K) * ((c i : K) * a i) + (m : K) * a i := by
      have : ((r * c i + m : 𝓞 K) : K) = 1 := by rw [hrm]; simp
      push_cast at this
      calc a i = (((r : K) * (c i : K) + (m : K))) * a i := by rw [this]; ring
        _ = (r : K) * ((c i : K) * a i) + (m : K) * a i := by ring
    rw [hai]
    refine Submodule.add_mem _ ?_ ?_
    · exact hsm ((𝔮 : FractionalIdeal (𝓞 K)⁰ K) * 𝔞 i) r _ hmem
    · exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩) (ha i)
  exact hi₀ (by rw [← hc i₀, Ideal.Quotient.eq_zero_iff_mem]; exact hcq i₀)

end Primitive

end

end
