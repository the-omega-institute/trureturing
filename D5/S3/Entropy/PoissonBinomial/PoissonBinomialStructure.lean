/- GID: D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure
   generality: G
   mirror-B: D5/B/S3/Entropy/PoissonBinomial/PoissonBinomialStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Poisson-binomial convolution and interior majorization chains. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone

/-! Finite Bernoulli-sum laws and majorization inside the unit cube. -/

noncomputable section
namespace D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
open scoped BigOperators
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector (IsTTransform)

/-- Mass at `k` for the sum of independent Bernoulli coordinates. -/
noncomputable def pb {M : ℕ} (c : Fin M → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ.powerset.filter (fun A => A.card = k)),
    (∏ i ∈ A, c i) * ∏ i ∈ Aᶜ, (1 - c i)

/-- Coordinate entropy minus the entropy of the Bernoulli sum. -/
noncomputable def F {M : ℕ} (c : Fin M → ℝ) : ℝ :=
  (∑ i, Real.binEntropy (c i)) -
    ∑ k ∈ Finset.range (M + 1), Real.negMulLog (pb c k)

/-- Every Poisson-binomial mass is nonnegative on the closed cube. -/
theorem pb_nonneg {M : ℕ} {c : Fin M → ℝ}
    (hc : ∀ i, c i ∈ Set.Icc 0 1) (k : ℕ) : 0 ≤ pb c k := by
  classical
  exact Finset.sum_nonneg fun A _ => mul_nonneg
    (Finset.prod_nonneg fun i _ => (hc i).1)
    (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hc i).2)

/-- The Poisson-binomial masses sum to one, including the empty vector. -/
theorem pb_sum_one {M : ℕ} (c : Fin M → ℝ) :
    ∑ k ∈ Finset.range (M + 1), pb c k = 1 := by
  classical
  unfold pb
  rw [Finset.sum_fiberwise_of_maps_to (fun A (_ : A ∈ (Finset.univ : Finset (Fin M)).powerset) =>
    show A.card ∈ Finset.range (M + 1) from Finset.mem_range.mpr
      (Nat.lt_succ_of_le (by simpa using Finset.card_le_univ A)))]
  simpa [Finset.compl_eq_univ_sdiff] using
    (Finset.prod_add c (fun i => 1 - c i) Finset.univ).symm

private def pgf {M : ℕ} (c : Fin M → ℝ) : Polynomial ℝ :=
  ∏ i, (Polynomial.C (c i) * Polynomial.X + Polynomial.C (1 - c i))

private lemma pb_eq_coeff {M : ℕ} (c : Fin M → ℝ) (k : ℕ) :
    pb c k = (pgf c).coeff k := by
  classical
  unfold pgf
  rw [Finset.prod_add]
  simp only [Polynomial.finsetSum_coeff]
  have hterm (A : Finset (Fin M)) :
      (∏ i ∈ A, (Polynomial.C (c i) * Polynomial.X)) *
        (∏ i ∈ Finset.univ \ A, Polynomial.C (1 - c i)) =
      Polynomial.monomial A.card ((∏ i ∈ A, c i) * ∏ i ∈ Aᶜ, (1 - c i)) := by
    rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod, Finset.prod_const,
      ← Polynomial.C_mul_X_pow_eq_monomial]
    simp [Finset.compl_eq_univ_sdiff, mul_assoc, mul_comm]
  simp_rw [hterm, Polynomial.coeff_monomial]
  simp only [pb, Finset.sum_filter]

/-- Permuting Bernoulli coordinates leaves each mass unchanged. -/
theorem pb_perm {M : ℕ} (c : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) (k : ℕ) :
    pb (c ∘ σ) k = pb c k := by
  simp only [pb_eq_coeff, pgf, Function.comp_apply]
  exact congrArg (fun p : Polynomial ℝ => p.coeff k)
    (Equiv.prod_comp σ (fun i => Polynomial.C (c i) * Polynomial.X + Polynomial.C (1 - c i)))

private lemma pgf_split {M : ℕ} (c : Fin M → ℝ) {i j : Fin M} (hij : i ≠ j) :
    pgf c = (Polynomial.C (c i) * Polynomial.X + Polynomial.C (1 - c i)) *
      (Polynomial.C (c j) * Polynomial.X + Polynomial.C (1 - c j)) *
      ∏ l ∈ (Finset.univ.erase i).erase j,
        (Polynomial.C (c l) * Polynomial.X + Polynomial.C (1 - c l)) := by
  classical
  unfold pgf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  ring

/-- The law of the remaining coordinates, represented by making the selected
Bernoulli variables identically zero. -/
def pbRest {M : ℕ} (c : Fin M → ℝ) (i j : Fin M) (k : ℕ) : ℝ :=
  pb (Function.update (Function.update c i 0) j 0) k

private lemma pgf_rest {M : ℕ} (c : Fin M → ℝ) {i j : Fin M} (hij : i ≠ j) :
    pgf (Function.update (Function.update c i 0) j 0) =
      ∏ l ∈ (Finset.univ.erase i).erase j,
        (Polynomial.C (c l) * Polynomial.X + Polynomial.C (1 - c l)) := by
  classical
  rw [pgf_split _ hij]
  simp only [Function.update_of_ne hij, Function.update_self, sub_zero,
    map_zero, zero_mul, zero_add, map_one, one_mul]
  apply Finset.prod_congr rfl
  intro l hl
  have hlj := (Finset.mem_erase.mp hl).1
  have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
  simp [Function.update_of_ne hlj, Function.update_of_ne hli]

section
attribute [local instance 100000] Classical.propDecidable

/-- Removing two coordinates gives a three-point convolution. The guards make
both negative-index masses zero rather than using truncated subtraction alone. -/
theorem pb_remove_two {M : ℕ} (c : Fin M → ℝ) {i j : Fin M} (hij : i ≠ j) (k : ℕ) :
    pb c k = (1 - c i) * (1 - c j) * pbRest c i j k +
      (c i * (1 - c j) + c j * (1 - c i)) *
        (if 1 ≤ k then pbRest c i j (k - 1) else 0) +
      c i * c j * (if 2 ≤ k then pbRest c i j (k - 2) else 0) := by
  classical
  let R := pgf (Function.update (Function.update c i 0) j 0)
  have hpoly : pgf c =
      Polynomial.C ((1 - c i) * (1 - c j)) * R +
      Polynomial.C (c i * (1 - c j) + c j * (1 - c i)) * (R * Polynomial.X ^ 1) +
      Polynomial.C (c i * c j) * (R * Polynomial.X ^ 2) := by
    rw [pgf_split c hij]
    rw [show R = ∏ l ∈ (Finset.univ.erase i).erase j,
      (Polynomial.C (c l) * Polynomial.X + Polynomial.C (1 - c l)) from pgf_rest c hij]
    simp only [map_mul, map_add]
    ring
  rw [pb_eq_coeff, hpoly]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
  simp only [pbRest, pb_eq_coeff]
  split_ifs <;> rfl

end

private lemma desc_mul {M : ℕ} (a : ℝ) (ha : 0 < a) (c : Fin M → ℝ) :
    desc (fun i => a * c i) = (desc c).map (fun x => a * x) := by
  simpa only [desc, List.map_ofFn, Function.comp_def] using
    (List.map_mergeSort (l := List.ofFn c)
      (r := fun x y : ℝ => decide (y ≤ x))
      (s := fun x y : ℝ => decide (y ≤ x)) (f := fun x => a * x)
      (by intro x _ y _; simp only [mul_le_mul_iff_right₀ ha])).symm

private lemma prefix_mul (xs : List ℝ) (a : ℝ) (k : ℕ) :
    prefixSum (xs.map (fun x => a * x)) k = a * prefixSum xs k := by
  simp only [prefixSum, ← List.map_take]
  simpa using List.sum_map_mul_left (xs.take k) id a

private lemma moreMixed_mul {M : ℕ} {c d : Fin M → ℝ}
    (hm : moreMixed d c) {a : ℝ} (ha : 0 < a) :
    moreMixed (fun i => a * d i) (fun i => a * c i) := by
  constructor
  · intro k hk
    simpa only [desc_mul a ha, prefix_mul] using
      mul_le_mul_of_nonneg_left (hm.1 k hk) ha.le
  · simpa only [desc_mul a ha, prefix_mul] using congrArg (a * ·) hm.2

private lemma moreMixed_sum {M : ℕ} {c d : Fin M → ℝ} (hm : moreMixed d c) :
    (∑ i, d i) = ∑ i, c i := by
  have h (x : Fin M → ℝ) : prefixSum (desc x) M = ∑ i, x i := by
    rw [prefixSum, List.take_of_length_le]
    · exact (List.mergeSort_perm _ _).sum_eq.trans (List.sum_ofFn (f := x))
    · simp [desc]
  simpa only [h] using hm.2

private lemma ttransform_mul {M : ℕ} {x y : Fin M → ℝ}
    (ht : IsTTransform x y) (a : ℝ) :
    IsTTransform (fun i => a * x i) (fun i => a * y i) := by
  obtain ⟨i,j,t,ht0,ht1,rfl⟩ := ht
  refine ⟨i,j,t,ht0,ht1,?_⟩
  ext l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  ring

private lemma ttransform_lt_one {M : ℕ} {x y : Fin M → ℝ}
    (ht : IsTTransform x y) (hx : ∀ i, x i < 1) : ∀ i, y i < 1 := by
  obtain ⟨i,j,t,ht0,ht1,rfl⟩ := ht
  intro l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  simpa only [smul_eq_mul, Set.mem_Iio] using
    (convex_Iio (𝕜 := ℝ) (1 : ℝ)) (hx l) (hx (Equiv.swap i j l))
      (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 t)

/-- A T-transform whose two endpoints belong to the open unit cube. -/
def InteriorT {M : ℕ} (x y : Fin M → ℝ) : Prop :=
  IsTTransform x y ∧ (∀ i, x i ∈ Set.Ioo 0 1) ∧ (∀ i, y i ∈ Set.Ioo 0 1)

/-- Standard majorization inside the unit cube is generated by a finite chain
of T-transforms staying inside that cube. -/
private theorem moreMixed_interior_chain {M : ℕ} (c d : Fin M → ℝ)
    (hc : ∀ i, c i ∈ Set.Ioo 0 1) (hd : ∀ i, d i ∈ Set.Ioo 0 1)
    (hm : moreMixed d c) : Relation.ReflTransGen InteriorT c d := by
  classical
  by_cases hM : M = 0
  · subst M
    have he : c = d := Subsingleton.elim c d
    rw [he]
  · have hnon : (Finset.univ : Finset (Fin M)).Nonempty := by
      exact Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hM⟩⟩
    let S : ℝ := ∑ i, c i
    have hS : 0 < S := Finset.sum_pos (fun i _ => (hc i).1) hnon
    have hsum : (∑ i, d i) = S := moreMixed_sum hm
    have hcn : (fun i => S⁻¹ * c i) ∈ simplex M := by
      refine ⟨fun i => mul_pos (inv_pos.mpr hS) (hc i).1, ?_⟩
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hS.ne'
    have hdn : (fun i => S⁻¹ * d i) ∈ simplex M := by
      refine ⟨fun i => mul_pos (inv_pos.mpr hS) (hd i).1, ?_⟩
      rw [← Finset.mul_sum, hsum, inv_mul_cancel₀ hS.ne']
    have hn := D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone.moreMixed_positive_chain
      _ _ hdn hcn (moreMixed_mul hm (inv_pos.mpr hS))
    have lift_chain : ∀ {x y : Fin M → ℝ}, Relation.ReflTransGen PositiveT x y →
        (∀ i, S * x i ∈ Set.Ioo 0 1) →
        Relation.ReflTransGen InteriorT (fun i => S * x i) (fun i => S * y i) ∧
          (∀ i, S * y i ∈ Set.Ioo 0 1) := by
      intro x y hxy hx
      induction hxy with
      | refl => exact ⟨.refl, hx⟩
      | @tail y z hxy hyz ih =>
        have ht := ttransform_mul hyz.1 S
        have hz : ∀ i, S * z i ∈ Set.Ioo 0 1 := fun i =>
          ⟨mul_pos hS (hyz.2.2.1 i), ttransform_lt_one ht (fun i => (ih.2 i).2) i⟩
        exact ⟨ih.1.tail ⟨ht, ih.2, hz⟩, hz⟩
    have hstart : ∀ i, S * (S⁻¹ * c i) ∈ Set.Ioo 0 1 := by
      simpa [← mul_assoc, hS.ne'] using hc
    simpa [← mul_assoc, hS.ne'] using (lift_chain hn hstart).1

/-- To prove monotonicity under interior majorization it suffices to treat one
interior T-transform at a time. -/
theorem le_of_interior_ttransform {M : ℕ} (G : (Fin M → ℝ) → ℝ)
    (hstep : ∀ x y, InteriorT x y → G x ≤ G y)
    (c d : Fin M → ℝ) (hc : ∀ i, c i ∈ Set.Ioo 0 1)
    (hd : ∀ i, d i ∈ Set.Ioo 0 1) (hm : moreMixed d c) : G c ≤ G d := by
  simpa only [Relation.reflTransGen_eq_self] using
    (Relation.ReflTransGen.lift G hstep c d (moreMixed_interior_chain c d hc hd hm))

end D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
