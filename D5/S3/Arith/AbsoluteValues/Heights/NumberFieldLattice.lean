/- GID: D5/S3/Arith/AbsoluteValues/Heights/NumberFieldLattice
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/NumberFieldLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The covolume of the mixed lattice is expressed through number-field data and height. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.NumberFieldIntegralLattice
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

variable [Fintype ι]

section Assembly

open exteriorPower Matrix

variable [LinearOrder ι]

open scoped Classical in
/-- **The Gram endomorphism of an independent family has positive determinant.** -/
theorem NumberField.det_mixedPiEnd_pos {k : ℕ} {y : Fin k → (ι → K)} (hy : LinearIndependent K y) :
    0 < LinearMap.det (mixedPiEnd ((Matrix.of y).map (mixedEmbedding K))) := by
  have nativeSource21 := (open Module in (fun {k : ℕ} (s : Set.powersetCard (Fin k) k) => (show ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) = (id : Fin k → Fin k) from by
    classical
    have hs : (s : Finset (Fin k)) = Finset.univ := Finset.eq_univ_of_card _ (by simp)
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique _ (fun x ↦ hs ▸ Finset.mem_univ x) strictMono_id).symm)))
  have nativeSource27 := (open Module in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v) => (show exteriorPower.plucker k v ≠ 0 from by
    classical
    have h := (exteriorPower.ιMulti_family_linearIndependent_field k hv).ne_zero
      (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
    have hι : exteriorPower.ιMulti K k v ≠ 0 := by
      rwa [exteriorPower.ιMulti_family, nativeSource21, Function.comp_id] at h
    intro hp
    rw [exteriorPower.plucker] at hp
    exact hι ((map_eq_zero_iff _ (LinearEquiv.injective _)).mp hp))))
  have hDet : LinearMap.det (mixedPiEnd ((Matrix.of y).map (mixedEmbedding K)))
      = Algebra.norm ℝ (((Matrix.of y).map (mixedEmbedding K))
          * ((Matrix.of y).map (mixedEmbedding K))ᴴ).det := by
    rw [mixedPiEnd, LinearMap.det_conj, LinearMap.det_restrictScalars,
      LinearMap.det_toLin', Matrix.det_transpose]
  rw [hDet, norm_det_gram]
  obtain ⟨s₀, hs₀⟩ : ∃ s, plucker k ((Matrix.of y).row) s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact nativeSource27 hy (funext hcon)
  refine Finset.prod_pos fun w _ ↦ pow_pos ?_ _
  refine Finset.sum_pos' (fun s _ ↦ by positivity) ⟨s₀, Finset.mem_univ s₀, ?_⟩
  exact pow_pos (w.1.pos hs₀) 2

omit [LinearOrder ι] in
open scoped Classical in
/-- **The map attached to a family with invertible Gram endomorphism is injective.** -/
theorem NumberField.mixedPiMap_injective {k : ℕ} (Y : Matrix (Fin k) ι (mixedSpace K))
    (hdet : LinearMap.det (mixedPiEnd Y) ≠ 0) : Function.Injective (mixedPiMap Y) := by
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
  have hinner :
      (∀ (u v : Fin k → mixedSpace K),
        inner ℝ (toMixedPi K (Fin k) u) (toMixedPi K (Fin k) v) =
          ∑ l, mixedTrace K (star (u l) * v l)) ∧
      (∀ (u v : ι → mixedSpace K),
        inner ℝ (toMixedPi K ι u) (toMixedPi K ι v) =
          ∑ l, mixedTrace K (star (u l) * v l)) := by
    constructor
    all_goals
      intro u v
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [hEuclidean]
      congr 1
  have hsum (u v : Fin k → mixedSpace K) :
      ∑ l, star ((Yᵀ *ᵥ u) l) * ((Yᵀ *ᵥ v) l) =
        ∑ j, star ((((Y * Yᴴ)ᵀ) *ᵥ u) j) * v j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
      star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have hgram (x y : mixedPi K (Fin k)) :
      inner ℝ (mixedPiMap Y x) (mixedPiMap Y y) = inner ℝ (mixedPiEnd Y x) y := by
    set u := (toMixedPi K (Fin k)).symm x with hu
    set v := (toMixedPi K (Fin k)).symm y with hv
    have hx : x = toMixedPi K (Fin k) u := by rw [hu]; simp
    have hy : y = toMixedPi K (Fin k) v := by rw [hv]; simp
    rw [mixedPiMap, mixedPiEnd]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.coe_restrictScalars, Matrix.toLin'_apply, ← hu, ← hv]
    rw [hinner.2, hy, hinner.1, ← map_sum, ← map_sum, hsum]
  have hA : Function.Injective (mixedPiEnd Y) := by
    have h1 : IsUnit (mixedPiEnd Y) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
    exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 h1)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine hA ?_
  rw [map_zero]
  refine ext_inner_right ℝ fun v ↦ ?_
  rw [inner_zero_left, ← hgram x v, hx, inner_zero_left]

set_option maxHeartbeats 2000000 in
open Real NumberField.InfinitePlace in
open scoped Classical nonZeroDivisors in
/-- The covolume computation, with the pseudo-basis data supplied. -/
private theorem covolume_of_data {k : ℕ} {V : Submodule K (ι → K)}
    (y : Fin k → (ι → K)) (𝔞 : Fin k → FractionalIdeal (𝓞 K)⁰ K)
    (hy : LinearIndependent K y) (h𝔞 : ∀ i, 𝔞 i ≠ 0)
    (hchar : ∀ x, x ∈ V.integerPoints ↔
      ∃ c : Fin k → K, (∀ i, c i ∈ 𝔞 i) ∧ x = ∑ i, c i • y i)
    (hyM : ∀ i, y i ∈ V.integerPoints)
    (hspanY : Submodule.span K (Set.range y) = V) :
    ∃ b : Basis (Fin (finrank ℚ K) × Fin k) ℝ ↥V.mixedSpan,
      V.mixedLattice = Submodule.span ℤ (Set.range b) ∧
      ZLattice.covolume (Submodule.span ℤ (Set.range b))
        = ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * √|NumberField.discr K|) ^ k
          * V.arakelovMulHeight := by
  have hMixedPiMapEmb {n : ℕ} (w : Fin n → (ι → K)) (c : Fin n → K) :
      mixedPiMap ((Matrix.of w).map (mixedEmbedding K))
          (toMixedPi K (Fin n) (fun i ↦ mixedEmbedding K (c i)))
        = mixedPiEmb K ι (∑ i, c i • w i) := by
    rw [mixedPiMap]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.coe_restrictScalars, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply,
      mixedPiEmb]
    congr 1
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Finset.sum_apply, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by
      simp [AddMonoidHom.coe_toIntLinearMap, Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]
  have nativeSource20 := (open Module in (fun (k : ℕ) (c : K) (v w : Fin k → (ι → K)) => (show exteriorPower.plucker k v = c • exteriorPower.plucker k w ↔ exteriorPower.ιMulti K k v = c • exteriorPower.ιMulti K k w from by
    classical
    rw [exteriorPower.plucker, exteriorPower.plucker, ← map_smul]
    exact (LinearEquiv.injective _).eq_iff)))
  have nativeSource21 := (open Module in (fun {k : ℕ} (s : Set.powersetCard (Fin k) k) => (show ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) = (id : Fin k → Fin k) from by
    classical
    have hs : (s : Finset (Fin k)) = Finset.univ := Finset.eq_univ_of_card _ (by simp)
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique _ (fun x ↦ hs ▸ Finset.mem_univ x) strictMono_id).symm)))
  have nativeSource22 := (open Module in (fun {E : Type _} [instSource2 : AddCommGroup E] [instSource3 : Module K E] {k : ℕ} {v : Fin k → E} (hv : LinearIndependent K v) => (show exteriorPower.ιMulti K k v ≠ 0 from by
    classical
    have h := (exteriorPower.ιMulti_family_linearIndependent_field k hv).ne_zero
      (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin k) k)
    rwa [exteriorPower.ιMulti_family, nativeSource21, Function.comp_id] at h)))
  have nativeSource23 := (open Module exteriorPower in (fun {k : ℕ} {V : Submodule K (ι → K)} (hV : Module.finrank K V = k) (b b' : Module.Basis (Fin k) K V) => (show ∃ c : K, exteriorPower.plucker k (fun i ↦ ((b' i : ι → K))) = c • exteriorPower.plucker k fun i ↦ ((b i : ι → K)) from by
    classical
    have h1 : Module.finrank K (⋀[K]^k V) = 1 := by rw [exteriorPower.finrank_eq, hV, Nat.choose_self]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (exteriorPower.ιMulti K k ⇑b)
      (nativeSource22 b.linearIndependent)).1 h1 (exteriorPower.ιMulti K k ⇑b')
    refine ⟨c, (nativeSource20 ..).2 ?_⟩
    have := congrArg (exteriorPower.map k V.subtype) hc
    rwa [map_smul, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, eq_comm] at this)))
  have nativeSource24 := (open Module exteriorPower in (fun {k : ℕ} {V : Submodule K (ι → K)} (hV : Module.finrank K V = k) (b : Module.Basis (Fin k) K V)
      (hb : exteriorPower.plucker k (fun i ↦ ((b i : ι → K))) ≠ 0) => (show Submodule.pluckerPoint V hV = Projectivization.mk K (exteriorPower.plucker k fun i ↦ ((b i : ι → K))) hb from by
    classical
    obtain ⟨c, hc⟩ := nativeSource23 hV b (Module.finBasisOfFinrankEq K V hV)
    refine ((Projectivization.mk_eq_mk_iff' K _ _ _ hb).2 ⟨c, hc.symm⟩))))
  have nativeSource27 := (open Module in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v) => (show exteriorPower.plucker k v ≠ 0 from by
    classical
    intro hp
    apply nativeSource22 hv
    rw [exteriorPower.plucker] at hp
    exact (map_eq_zero_iff _ (LinearEquiv.injective _)).mp hp)))
  have nativeSource28 := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v)
      (hV : Module.finrank K (Submodule.span K (Set.range v)) = k) => (show Submodule.pluckerPoint (Submodule.span K (Set.range v)) hV =
        Projectivization.mk K (exteriorPower.plucker k v) (nativeSource27 hv) from by
    classical
    have hfun : (fun i ↦ ((Module.Basis.span hv i : ι → K))) = v :=
      funext fun i ↦ congrArg Subtype.val (Module.Basis.span_apply hv i)
    rw [nativeSource24 hV (Module.Basis.span hv) (by rw [hfun]; exact nativeSource27 hv)]
    simp only [hfun])))
  have nativeSource29 := (open Module exteriorPower in (fun {k : ℕ} {v : Fin k → (ι → K)} (hv : LinearIndependent K v) => (show (Submodule.span K (Set.range v)).arakelovMulHeight = NumberField.arakelovMulHeight (exteriorPower.plucker k v) from by
    classical
    have hV : finrank K (Submodule.span K (Set.range v)) = k :=
      (finrank_span_eq_card hv).trans (Fintype.card_fin k)
    rw [(show (Submodule.span K (Set.range v)).arakelovMulHeight =
        Projectivization.projectiveArakelovMulHeight ((Submodule.span K (Set.range v)).pluckerPoint hV) from by
          exact Eq.rec (motive := fun (r : ℕ) (hr : finrank K (Submodule.span K (Set.range v)) = r) ↦
            (Submodule.span K (Set.range v)).arakelovMulHeight = Projectivization.projectiveArakelovMulHeight ((Submodule.span K (Set.range v)).pluckerPoint hr))
            rfl hV), nativeSource28 hv hV]
    rfl)))
  have nativeSource147 := (open Module MeasureTheory Matrix Real in (fun {E : Type _} [instSource1 : NormedAddCommGroup E] [instSource2 : InnerProductSpace ℝ E] [instSource3 : FiniteDimensional ℝ E] [instSource4 : MeasurableSpace E] [instSource5 : BorelSpace E] (L : Submodule ℤ E) [instSource7 : DiscreteTopology L] [instSource8 : IsZLattice ℝ L] {κ : Type _} [instSource10 : Fintype κ] [instSource11 : DecidableEq κ] (b : Module.Basis κ ℤ L) (o : OrthonormalBasis κ ℝ E) => (show ZLattice.covolume L = |(o.toBasis.toMatrix ((↑) ∘ b)).det| from by
    classical
    have hfd : (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure E).real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.MeasureSpace.volume)]
      simp [measureReal_def, o.volume_parallelepiped]
    rw [ZLattice.covolume_eq_det_mul_measureReal L MeasureTheory.MeasureSpace.volume b o.toBasis, hfd, mul_one, Module.Basis.det_apply])))
  have nativeSource148 := (open Module MeasureTheory Matrix Real in (fun {E : Type _} [instSource1 : NormedAddCommGroup E] [instSource2 : InnerProductSpace ℝ E] [instSource3 : FiniteDimensional ℝ E] [instSource4 : MeasurableSpace E] [instSource5 : BorelSpace E] (L : Submodule ℤ E) [instSource7 : DiscreteTopology L] [instSource8 : IsZLattice ℝ L] {κ : Type _} [instSource10 : Fintype κ] [instSource11 : DecidableEq κ] (b : Module.Basis κ ℤ L) => (show ZLattice.covolume L ^ 2 = (Matrix.of fun i j ↦ inner ℝ (b i : E) (b j : E)).det from by
    classical
    have hcard : Fintype.card κ = Module.finrank ℝ E :=
      (Module.finrank_eq_card_basis (b.ofZLatticeBasis ℝ L)).symm
    let o : OrthonormalBasis κ ℝ E :=
      (stdOrthonormalBasis ℝ E).reindex (Fintype.equivFinOfCardEq hcard).symm
    have hG : (Matrix.of fun i j ↦ inner ℝ (b i : E) (b j : E))
        = (o.toBasis.toMatrix ((↑) ∘ b))ᵀ * o.toBasis.toMatrix ((↑) ∘ b) := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply, Basis.toMatrix_apply, Function.comp_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, Matrix.of_apply]
      rw [← o.sum_inner_mul_inner (b i : E) (b j : E)]
      exact Finset.sum_congr rfl fun l _ ↦ by rw [real_inner_comm]
    rw [hG, nativeSource147 L b o, Matrix.det_mul, Matrix.det_transpose, ← sq,
      sq_abs])))
  have nativeSource149 := (open Module MeasureTheory Matrix Real in (fun {E : Type _} [instSource1 : NormedAddCommGroup E] [instSource2 : InnerProductSpace ℝ E] [instSource3 : FiniteDimensional ℝ E] [instSource4 : MeasurableSpace E] [instSource5 : BorelSpace E] {κ : Type _} [instSource10 : Fintype κ] [instSource11 : DecidableEq κ] {F : Type _} [instSource13 : NormedAddCommGroup F] [instSource14 : InnerProductSpace ℝ F] [instSource15 : FiniteDimensional ℝ F] (f : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E) (b : Module.Basis κ ℝ E)
      (h : ∀ x y, inner ℝ (f x) (f y) = inner ℝ (A x) y) => (show (Matrix.of fun i j ↦ inner ℝ (f (b i)) (f (b j))).det
        = A.det * (Matrix.of fun i j ↦ inner ℝ (b i) (b j)).det from by
    classical
    classical
    set M := LinearMap.toMatrix b b A with hM
    have key : (Matrix.of fun i j ↦ inner ℝ (f (b i)) (f (b j)))
        = Mᵀ * (Matrix.of fun i j ↦ inner ℝ (b i) (b j)) := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.transpose_apply]
      rw [h (b i) (b j), ← b.sum_repr (A (b i)), sum_inner]
      exact Finset.sum_congr rfl fun l _ ↦ by
        rw [real_inner_smul_left, hM, LinearMap.toMatrix_apply]
    rw [key, Matrix.det_mul, Matrix.det_transpose, hM, LinearMap.det_toMatrix])))
  have nativeSource150 := (open Module MeasureTheory Matrix Real in (fun {E : Type _} [instSource1 : NormedAddCommGroup E] [instSource2 : InnerProductSpace ℝ E] [instSource3 : FiniteDimensional ℝ E] [instSource4 : MeasurableSpace E] [instSource5 : BorelSpace E] {κ : Type _} [instSource10 : Fintype κ] [instSource11 : DecidableEq κ] {F : Type _} [instSource13 : NormedAddCommGroup F] [instSource14 : InnerProductSpace ℝ F] [instSource15 : FiniteDimensional ℝ F] [instSource16 : MeasurableSpace F] [instSource17 : BorelSpace F] {W : Submodule ℝ F} (L : Submodule ℤ ↥W)
      [DiscreteTopology L] [IsZLattice ℝ L] (c : Module.Basis κ ℤ L) (f : E →ₗ[ℝ] F) (A : E →ₗ[ℝ] E)
      (b : Module.Basis κ ℝ E) (h : ∀ x y, Inner.inner ℝ (f x) (f y) = Inner.inner ℝ (A x) y)
      (hc : ∀ i, ((c i : ↥W) : F) = f (b i)) => (show ZLattice.covolume L ^ 2 = A.det * (Matrix.of fun i j ↦ Inner.inner ℝ (b i) (b j)).det from by
    classical
    rw [nativeSource148 L c, ← nativeSource149 f A b h]
    refine congrArg Matrix.det (Matrix.ext fun i j ↦ ?_)
    simp only [Matrix.of_apply]
    rw [← hc i, ← hc j]
    exact rfl)))
  classical
  -- the integral Plücker coordinates
  have hint : ∀ i, y i ∈ integralTuples K ι := fun i ↦ (hyM i).2
  have exists_plucker_int (s : Set.powersetCard ι k) :
      ∃ z : 𝓞 K, (z : K) = plucker k y s := by
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
    have hy' : y = fun i ↦ (algebraMap (𝓞 K) K) ∘ (w i) := by
      funext i l
      exact (hw i l).symm
    rw [hy', nativeSource37 (algebraMap (𝓞 K) K) k w s]
  choose p hp using exists_plucker_int
  -- a `ℤ`-basis of each fractional ideal, read in the euclidean mixed space
  have exists_idealBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      ∃ (a : Fin (finrank ℚ K) → K) (b : Basis (Fin (finrank ℚ K)) ℝ (euclidean.mixedSpace K)),
        (∀ j, euclidean.toMixed K (b j) = mixedEmbedding K (a j)) ∧
        (∀ x : K, x ∈ Submodule.span ℤ (Set.range a) ↔ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) ∧
        ZLattice.covolume (Submodule.span ℤ (Set.range b))
          = (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ)
            * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * √|NumberField.discr K| := by
    classical
    have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ I) = finrank ℚ K := by
      rw [← Module.finrank_eq_card_chooseBasisIndex, fractionalIdeal_rank, RingOfIntegers.rank]
    set e := Fintype.equivFinOfCardEq hcard with he
    set b : Basis (Fin (finrank ℚ K)) ℝ (euclidean.mixedSpace K) :=
      ((fractionalIdealLatticeBasis K I).map (euclidean.toMixed K).symm.toLinearEquiv).reindex e
      with hb
    set φ : mixedSpace K →ₗ[ℤ] euclidean.mixedSpace K :=
      (euclidean.toMixed K).symm.toLinearMap.restrictScalars ℤ with hφ
    have hbj : ∀ j, b j = φ (fractionalIdealLatticeBasis K I (e.symm j)) := fun j ↦ by
      rw [hb]; simp [hφ]
    refine ⟨basisOfFractionalIdeal K I ∘ e.symm, b, fun j ↦ ?_, fun x ↦ ?_, ?_⟩
    · rw [hbj j]
      simp [hφ]
    · rw [show Set.range (basisOfFractionalIdeal K I ∘ e.symm)
          = Set.range (basisOfFractionalIdeal K I) by
        rw [Set.range_comp, e.symm.range_eq_univ, Set.image_univ]]
      exact mem_span_basisOfFractionalIdeal K
    · have hrange : Set.range b
          = (euclidean.toMixed K).symm '' Set.range (fractionalIdealLatticeBasis K I) := by
        rw [show (b : Fin (finrank ℚ K) → euclidean.mixedSpace K)
            = (fun x ↦ (euclidean.toMixed K).symm x) ∘ ((fractionalIdealLatticeBasis K I) ∘ e.symm)
            from funext hbj, Set.range_comp, Set.range_comp, e.symm.range_eq_univ, Set.image_univ]
      have hspan : Submodule.span ℤ (Set.range b)
          = ZLattice.comap ℝ (idealLattice K I) (euclidean.toMixed K).toLinearMap := by
        have hmap : Submodule.span ℤ (Set.range b)
            = Submodule.map φ
              (Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I))) := by
          rw [← Submodule.span_image]
          exact congrArg (Submodule.span ℤ) hrange
        rw [hmap, span_idealLatticeBasis]
        ext x
        simp only [Submodule.mem_map, hφ, LinearMap.coe_restrictScalars,
          ZLattice.comap, Submodule.mem_comap]
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
        · intro h
          exact ⟨euclidean.toMixed K x, h, by simp⟩
      rw [hspan, ZLattice.covolume_comap _ _ _ (euclidean.volumePreserving_toMixed K),
        covolume_idealLattice]
  choose a bi hab hspan_a hcov0 using fun i ↦
    exists_idealBasis (Units.mk0 (𝔞 i) (h𝔞 i))
  have hcov : ∀ i, ZLattice.covolume (Submodule.span ℤ (Set.range (bi i)))
      = (FractionalIdeal.absNorm (𝔞 i) : ℝ)
        * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * √|NumberField.discr K| := fun i ↦ by
    simpa using hcov0 i
  have ha𝔞 : ∀ i j, a i j ∈ 𝔞 i := fun i j ↦
    (hspan_a i (a i j)).1 (Submodule.subset_span ⟨j, rfl⟩)
  -- the `ℝ`-basis of the euclidean space of `k`-tuples
  set bE : Basis (Fin (finrank ℚ K) × Fin k) ℝ (mixedPi K (Fin k)) :=
    (((Pi.basis (fun i ↦ bi i)).reindex
      ((Equiv.sigmaEquivProd (Fin k) (Fin (finrank ℚ K))).trans (Equiv.prodComm _ _))).map
      (WithLp.linearEquiv 2 ℝ (∀ _ : Fin k, euclidean.mixedSpace K)).symm) with hbEdef
  have hbE : ∀ (j : Fin (finrank ℚ K)) (i : Fin k),
      bE (j, i) = toMixedPi K (Fin k) (Pi.single i ((euclidean.toMixed K) (bi i j))) := by
    intro j i
    rw [hbEdef]
    simp only [Basis.map_apply, Basis.coe_reindex, Function.comp_apply, Equiv.symm_trans_apply,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Equiv.sigmaEquivProd_symm_apply, Pi.basis_apply, toMixedPi]
    refine congrArg _ (funext fun i' ↦ ?_)
    rcases eq_or_ne i' i with rfl | hne
    · simp
    · simp [Pi.single_eq_of_ne hne]
  -- the integral points are the `ℤ`-span of the products `a i j • y i`
  have haM : ∀ (i : Fin k) (j : Fin (finrank ℚ K)), (a i j) • y i ∈ V.integerPoints :=
    fun i j ↦ by
      refine (hchar _).2 ⟨Pi.single i (a i j), fun l ↦ ?_, ?_⟩
      · rcases eq_or_ne l i with rfl | hl
        · simpa using ha𝔞 l j
        · simp [hl, (𝔞 l).zero_mem]
      · rw [Finset.sum_eq_single i]
        · simp
        · intro l _ hl; simp [hl]
        · simp
  have hZ : V.integerPoints.restrictScalars ℤ
      = Submodule.span ℤ (Set.range (fun q : Fin (finrank ℚ K) × Fin k ↦ (a q.2 q.1) • y q.2)) := by
    refine le_antisymm (fun z hz ↦ ?_) (Submodule.span_le.2 ?_)
    · obtain ⟨c, hc, rfl⟩ := (hchar z).1 hz
      have hcj : ∀ i, ∃ n : Fin (finrank ℚ K) → ℤ, ∑ j, n j • a i j = c i := fun i ↦
        (Submodule.mem_span_range_iff_exists_fun ℤ).1 ((hspan_a i (c i)).2 (hc i))
      choose n hn using hcj
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun q ↦ n q.2 q.1, ?_⟩
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← hn i, Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_assoc]
    · rintro _ ⟨q, rfl⟩
      exact haM q.2 q.1
  -- the map attached to the family, and its image
  set Ym : Matrix (Fin k) ι (mixedSpace K) := (Matrix.of y).map (mixedEmbedding K) with hYm
  have hfbE : ∀ (j : Fin (finrank ℚ K)) (i : Fin k),
      mixedPiMap Ym (bE (j, i)) = mixedPiEmb K ι ((a i j) • y i) := by
    intro j i
    have h1 : (fun i' ↦ mixedEmbedding K ((Pi.single i (a i j) : Fin k → K) i'))
        = Pi.single i (mixedEmbedding K (a i j)) := by
      funext i'
      rcases eq_or_ne i' i with rfl | hne
      · simp
      · simp [Pi.single_eq_of_ne hne]
    have h2 : ∑ i', ((Pi.single i (a i j) : Fin k → K) i') • y i' = (a i j) • y i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hne; simp [Pi.single_eq_of_ne hne]
      · simp
    rw [hbE j i, hab i j, hYm, ← h1, hMixedPiMapEmb y (Pi.single i (a i j)), h2]
  have hinj : Function.Injective (mixedPiMap Ym) :=
    NumberField.mixedPiMap_injective Ym (ne_of_gt (hYm ▸ NumberField.det_mixedPiEnd_pos hy))
  have hrange : LinearMap.range (mixedPiMap Ym) = V.mixedSpan := by
    refine le_antisymm ?_ ?_
    · rw [LinearMap.range_eq_map, ← bE.span_eq, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      obtain ⟨j, i⟩ := q
      rw [hfbE j i]
      exact Submodule.subset_span ⟨(a i j) • y i, V.smul_mem _ (hyM i).1, rfl⟩
    · rw [Submodule.mixedSpan, Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (by rw [hspanY]; exact hv)
      exact ⟨toMixedPi K (Fin k) (fun i ↦ mixedEmbedding K (c i)),
        hMixedPiMapEmb y c⟩
  set e : mixedPi K (Fin k) ≃ₗ[ℝ] ↥V.mixedSpan :=
    (LinearEquiv.ofInjective (mixedPiMap Ym) hinj).trans (LinearEquiv.ofEq _ _ hrange) with he
  have hbWcoe : ∀ q, (((bE.map e) q : ↥V.mixedSpan) : mixedPi K ι) = mixedPiMap Ym (bE q) := by
    intro q
    rw [Basis.map_apply, he]
    rfl
  have hLmap : Submodule.map ((V.mixedSpan.subtype).restrictScalars ℤ) V.mixedLattice
      = Submodule.span ℤ (Set.range (fun q ↦ (((bE.map e) q : ↥V.mixedSpan) : mixedPi K ι))) := by
    rw [Submodule.mixedLattice, Submodule.map_comap_eq_self, hZ, Submodule.map_span,
      ← Set.range_comp]
    · refine congrArg _ (congrArg Set.range (funext fun q ↦ ?_))
      obtain ⟨j, i⟩ := q
      rw [Function.comp_apply, hbWcoe (j, i), hfbE j i]
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨_, Submodule.subset_span ⟨z, hz.1, rfl⟩⟩, rfl⟩
  have hL : V.mixedLattice = Submodule.span ℤ (Set.range (bE.map e)) := by
    refine Submodule.map_injective_of_injective
      (f := (V.mixedSpan.subtype).restrictScalars ℤ) (Submodule.injective_subtype _) ?_
    rw [hLmap, Submodule.map_span, ← Set.range_comp]
    rfl
  refine ⟨bE.map e, hL, ?_⟩
  -- the squared covolume
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
  have hinner :
      (∀ (u v : Fin k → mixedSpace K),
        inner ℝ (toMixedPi K (Fin k) u) (toMixedPi K (Fin k) v) =
          ∑ l, mixedTrace K (star (u l) * v l)) ∧
      (∀ (u v : ι → mixedSpace K),
        inner ℝ (toMixedPi K ι u) (toMixedPi K ι v) =
          ∑ l, mixedTrace K (star (u l) * v l)) := by
    constructor
    all_goals
      intro u v
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [hEuclidean]
      congr 1
  have hsum (u v : Fin k → mixedSpace K) :
      ∑ l, star ((Ymᵀ *ᵥ u) l) * ((Ymᵀ *ᵥ v) l) =
        ∑ j, star ((((Ym * Ymᴴ)ᵀ) *ᵥ u) j) * v j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
      star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have hAdjoint (x y : mixedPi K (Fin k)) :
      inner ℝ (mixedPiMap Ym x) (mixedPiMap Ym y) = inner ℝ (mixedPiEnd Ym x) y := by
    set u := (toMixedPi K (Fin k)).symm x with hu
    set v := (toMixedPi K (Fin k)).symm y with hv
    have hx : x = toMixedPi K (Fin k) u := by rw [hu]; simp
    have hy : y = toMixedPi K (Fin k) v := by rw [hv]; simp
    rw [mixedPiMap, mixedPiEnd]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.coe_restrictScalars, Matrix.toLin'_apply, ← hu, ← hv]
    rw [hinner.2, hy, hinner.1, ← map_sum, ← map_sum, hsum]
  have hsq : ZLattice.covolume (Submodule.span ℤ (Set.range (bE.map e))) ^ 2
      = LinearMap.det (mixedPiEnd Ym)
        * (Matrix.of fun q q' ↦ inner ℝ (bE q) (bE q')).det :=
    nativeSource150 _ ((bE.map e).restrictScalars ℤ) (mixedPiMap Ym)
      (mixedPiEnd Ym) bE hAdjoint (fun q ↦ by
        rw [Basis.restrictScalars_apply]; exact hbWcoe q)
  -- the Gram determinant of the product basis
  have hgram : (Matrix.of fun q q' ↦ inner ℝ (bE q) (bE q')).det
      = ∏ i, ((FractionalIdeal.absNorm (𝔞 i) : ℝ)
          * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * √|NumberField.discr K|)) ^ 2 := by
    rw [NumberField.det_gram_pi bi (fun q ↦ bE q) (fun j i ↦ hbE j i)]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, ← hcov i]
    let L : Submodule ℤ (euclidean.mixedSpace K) :=
      Submodule.span ℤ (Set.range (bi i))
    let b : Module.Basis (Fin (finrank ℚ K)) ℤ L := (bi i).restrictScalars ℤ
    have hcard : Fintype.card (Fin (finrank ℚ K)) =
        Module.finrank ℝ (euclidean.mixedSpace K) :=
      (Module.finrank_eq_card_basis (b.ofZLatticeBasis ℝ L)).symm
    let o : OrthonormalBasis (Fin (finrank ℚ K)) ℝ (euclidean.mixedSpace K) :=
      (stdOrthonormalBasis ℝ (euclidean.mixedSpace K)).reindex
        (Fintype.equivFinOfCardEq hcard).symm
    have hG : (Matrix.of fun j j' ↦ inner ℝ (b j : euclidean.mixedSpace K) (b j' : euclidean.mixedSpace K))
        = (o.toBasis.toMatrix ((↑) ∘ b))ᵀ * o.toBasis.toMatrix ((↑) ∘ b) := by
      ext j j'
      rw [Matrix.mul_apply]
      simp only [Matrix.transpose_apply, Basis.toMatrix_apply, Function.comp_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
        Matrix.of_apply]
      rw [← o.sum_inner_mul_inner (b j : euclidean.mixedSpace K) (b j' : euclidean.mixedSpace K)]
      exact Finset.sum_congr rfl fun l _ ↦ by rw [real_inner_comm]
    have hfd : (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (euclidean.mixedSpace K)).real
        (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [MeasureTheory.measureReal_congr
        (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.MeasureSpace.volume)]
      simp [MeasureTheory.measureReal_def, o.volume_parallelepiped]
    have hcov : ZLattice.covolume L = |(o.toBasis.toMatrix ((↑) ∘ b)).det| := by
      rw [ZLattice.covolume_eq_det_mul_measureReal L MeasureTheory.MeasureSpace.volume
        b o.toBasis, hfd, mul_one, Module.Basis.det_apply]
    have hsq : ZLattice.covolume L ^ 2 =
        (Matrix.of fun j j' ↦ inner ℝ (b j : euclidean.mixedSpace K)
          (b j' : euclidean.mixedSpace K)).det := by
      rw [hG, hcov, Matrix.det_mul, Matrix.det_transpose, ← sq, sq_abs]
    simpa only [L, b, Basis.restrictScalars_apply] using hsq.symm
  -- the archimedean factor
  have hdet : LinearMap.det (mixedPiEnd Ym)
      = ∏ w : NumberField.InfinitePlace K,
        (∑ s : Set.powersetCard ι k, w (plucker k y s) ^ 2) ^ w.mult := by
    have hDet : LinearMap.det (mixedPiEnd Ym) = Algebra.norm ℝ (Ym * Ymᴴ).det := by
      rw [mixedPiEnd, LinearMap.det_conj, LinearMap.det_restrictScalars,
        LinearMap.det_toLin', Matrix.det_transpose]
    rw [hDet, hYm, norm_det_gram (Matrix.of y)]
    rfl
  -- the finite factor
  have hplk0 : plucker k y ≠ 0 := nativeSource27 hy
  have hpne : ∃ s, p s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hplk0 (funext fun s ↦ ?_)
    rw [← hp s, hcon s]
    simp
  have hnorm : (∏ i, (FractionalIdeal.absNorm (𝔞 i) : ℝ))
      = ((Ideal.absNorm (Ideal.span (Set.range p)) : ℝ))⁻¹ := by
    have h := congrArg FractionalIdeal.absNorm
      (Submodule.prod_mul_plucker_eq_one V hy h𝔞 hchar hp)
    rw [map_mul, map_prod, FractionalIdeal.coeIdeal_absNorm, map_one] at h
    have h2 : (∏ i, (FractionalIdeal.absNorm (𝔞 i) : ℝ))
        * ((Ideal.absNorm (Ideal.span (Set.range p)) : ℝ)) = 1 := by
      exact_mod_cast congrArg (fun q : ℚ ↦ (q : ℝ)) h
    have hne : ((Ideal.absNorm (Ideal.span (Set.range p)) : ℝ)) ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at h2
      exact zero_ne_one h2
    field_simp at h2 ⊢
    linarith [h2]
  have hH : V.arakelovMulHeight
      = (∏ w : NumberField.InfinitePlace K,
          (∑ s : Set.powersetCard ι k, w (plucker k y s) ^ 2) ^ (w.mult / 2 : ℝ))
        * ((Ideal.absNorm (Ideal.span (Set.range p)) : ℝ))⁻¹ := by
    rw [← hspanY, nativeSource29 hy,
      NumberField.arakelovMulHeight, if_neg hplk0]
    congr 1
    have hpne' : p ≠ 0 := Function.ne_iff.mpr hpne
    have hfinite := NumberField.absNorm_mul_finprod_finitePlace_eq_one (K := K) hpne'
    have hnormFinite : (∏ᶠ v : NumberField.FinitePlace K, ⨆ i, v ((p i : 𝓞 K) : K))
        = ((Ideal.absNorm (Ideal.span (Set.range p)) : ℝ))⁻¹ :=
      eq_inv_of_mul_eq_one_right (by exact_mod_cast hfinite)
    rw [← hnormFinite]
    exact finprod_congr fun v ↦ by simp only [hp]
  -- squaring the archimedean factor
  have hA2 : (∏ w : NumberField.InfinitePlace K,
        (∑ s : Set.powersetCard ι k, w (plucker k y s) ^ 2) ^ (w.mult / 2 : ℝ)) ^ 2
      = ∏ w : NumberField.InfinitePlace K,
        (∑ s : Set.powersetCard ι k, w (plucker k y s) ^ 2) ^ w.mult := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    have hx : (0 : ℝ) ≤ ∑ s : Set.powersetCard ι k, w (plucker k y s) ^ 2 :=
      Finset.sum_nonneg fun s _ ↦ sq_nonneg _
    rw [← Real.rpow_natCast ((∑ s : Set.powersetCard ι k, w (plucker k y s) ^ 2)
        ^ ((w.mult : ℝ) / 2)) 2, ← Real.rpow_mul hx, ← Real.rpow_natCast _ w.mult]
    congr 1
    push_cast
    ring
  -- the product of the ideal norms
  have hp2 : ∏ i : Fin k, ((FractionalIdeal.absNorm (𝔞 i) : ℝ)
        * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * √|NumberField.discr K|)) ^ 2
      = ((∏ i : Fin k, (FractionalIdeal.absNorm (𝔞 i) : ℝ))
          * ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * √|NumberField.discr K|) ^ k) ^ 2 := by
    rw [Finset.prod_pow]
    congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- both sides have the same square
  have hsq2 : ZLattice.covolume (Submodule.span ℤ (Set.range (bE.map e))) ^ 2
      = (((2 : ℝ)⁻¹ ^ nrComplexPlaces K * √|NumberField.discr K|) ^ k
          * V.arakelovMulHeight) ^ 2 := by
    rw [hsq, hdet, hgram, hp2, hH, hnorm, ← hA2]
    ring
  have hnn : (0 : ℝ) ≤ ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * √|NumberField.discr K|) ^ k
      * V.arakelovMulHeight := by
    have hVpos : 0 < V.arakelovMulHeight := by
      rw [← hspanY, nativeSource29 hy]
      positivity
    exact mul_nonneg
      (pow_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)) _)
      hVpos.le
  have hcovnn : 0 ≤ ZLattice.covolume (Submodule.span ℤ (Set.range (bE.map e))) :=
    (ZLattice.covolume_pos _ MeasureTheory.volume).le
  rw [← Real.sqrt_sq hcovnn, hsq2, Real.sqrt_sq hnn]

open scoped Classical in
private theorem exists_lattice_basis (V : Submodule K (ι → K)) :
    ∃ b : Basis (Fin (finrank ℚ K) × Fin (finrank K V)) ℝ ↥V.mixedSpan,
      V.mixedLattice = Submodule.span ℤ (Set.range b) ∧
      ZLattice.covolume (Submodule.span ℤ (Set.range b))
        = ((2 : ℝ)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K
            * √|NumberField.discr K|) ^ finrank K V * V.arakelovMulHeight := by
  obtain ⟨y, 𝔞, hy, h𝔞, hyM, hchar⟩ := V.exists_pseudoBasis_integerPoints
  have hle : Submodule.span K (Set.range y) ≤ V :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (hyM i).1)
  have hrk : finrank K ↥(Submodule.span K (Set.range y)) = finrank K V := by
    rw [finrank_span_eq_card hy, Fintype.card_fin]
  exact covolume_of_data y 𝔞 hy h𝔞 hchar hyM (Submodule.eq_of_le_of_finrank_eq hle hrk)

section Finiteness

omit [Fintype ι]

variable [Finite ι]

open scoped Classical in
theorem Submodule.mixedLattice_eq_span (V : Submodule K (ι → K)) :
    ∃ b : Basis (Fin (finrank ℚ K) × Fin (finrank K V)) ℝ ↥V.mixedSpan,
      V.mixedLattice = Submodule.span ℤ (Set.range b) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b, hL, -⟩ := exists_lattice_basis V
  exact ⟨b, hL⟩

open scoped Classical in
instance instDiscreteTopologyMixedLattice (V : Submodule K (ι → K)) :
    DiscreteTopology V.mixedLattice := by
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b, hL⟩ := V.mixedLattice_eq_span
  rw [hL]
  infer_instance

open scoped Classical in
instance instIsZLatticeMixedLattice (V : Submodule K (ι → K)) :
    IsZLattice ℝ V.mixedLattice := by
  constructor
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b, hL⟩ := V.mixedLattice_eq_span
  rw [hL]
  exact ZSpan.span_top b

open scoped Classical in
/-- **The real span of a subspace of `Kⁱ` has dimension `[K : ℚ] · dim V`.** -/
theorem Submodule.finrank_mixedSpan (V : Submodule K (ι → K)) :
    finrank ℝ ↥V.mixedSpan = finrank ℚ K * finrank K V := by
  obtain ⟨b, -⟩ := V.mixedLattice_eq_span
  simpa using finrank_eq_card_basis b

end Finiteness

open scoped Classical in
/-- **The covolume identity over a number field** (Layer 4.3; W. M. Schmidt, "On heights of
algebraic subspaces and diophantine approximations", *Annals of Mathematics* **85** (1967),
§3, Theorem 1). The lattice of integral points of a subspace `V ⊆ Kⁱ` has covolume the covolume
of `𝓞 K` raised to the dimension of `V`, times the Arakelov height of `V`:

```text
covol (V ∩ (𝓞 K)ⁱ) = (2^{-r₂} |discr K|^{1/2}) ^ k · H_Ar(V),
```

with `H_Ar` the height relative to `K`, so that the absolute height enters with the exponent
`[K : ℚ]`. Over `ℚ` every constant is `1` and this is `Submodule.covolume_intLattice`. -/
theorem Submodule.covolume_mixedLattice (V : Submodule K (ι → K)) :
    ZLattice.covolume V.mixedLattice
      = ((2 : ℝ)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K
          * √|NumberField.discr K|) ^ finrank K V * V.arakelovMulHeight := by
  obtain ⟨b, hL, hcov⟩ := exists_lattice_basis V
  rw [hL, hcov]

end Assembly

namespace NumberField.mixedEmbedding

open Module NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι]

end NumberField.mixedEmbedding

end

end
