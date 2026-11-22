/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRealPolynomialZeros
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRealPolynomialZeros
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSMonicLevelGraphs]
   utility: none
   digest: Relatively prime complex equations have a real common zero set covered in codimension two. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSMonicLevelGraphs
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSProjectionResultant
import D5.S3.Quantum.Algebra.CommonPhasePolynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! Polynomial projection, using an invertible real triangular change of
coordinates, turns relative primality into a countable differentiable cover. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSRealPolynomialZeros

open Set Polynomial PeriodicMPSMonicLevelGraphs PeriodicMPSProjectionResultant
  PeriodicMPSRegularLevelGraphs OpenBoundaryMPSDensityGenericity

noncomputable section

private def triangular {n : ℕ} (d : ℕ) (a : ℝ) (x : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => if i = 0 then x 0 else x i + a * x 0 ^ ((2 + d) ^ i.val)

private theorem triangular_cancel {n : ℕ} (d : ℕ) (x : Fin (n + 1) → ℝ) :
    triangular d 1 (triangular d (-1) x) = x := by
  funext i
  by_cases h : i = 0
  · simp [triangular, h]
  · simp [triangular, h]

private theorem differentiable_triangular {n : ℕ} (d : ℕ) (a : ℝ) :
    Differentiable ℝ (triangular (n := n) d a) := by
  apply differentiable_pi.mpr
  intro i
  by_cases h : i = 0 <;> simp only [triangular, h, if_true, if_false] <;> fun_prop

private theorem triangular_eval {K : Type*} [Field K] [Algebra ℝ K] {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) K) (x : Fin (n + 1) → ℝ) :
    MvPolynomial.eval (fun i => algebraMap ℝ K (x i)) (NoetherNormalization.varChange p q) =
      MvPolynomial.eval (fun i => algebraMap ℝ K (triangular p.totalDegree 1 x i)) q := by
  change MvPolynomial.aeval (fun i => algebraMap ℝ K (x i))
    (NoetherNormalization.varChange p q) = _
  have h : (MvPolynomial.aeval (fun i => algebraMap ℝ K (x i))).comp
      (NoetherNormalization.varChange p).toAlgHom =
      MvPolynomial.aeval (fun i => algebraMap ℝ K (triangular p.totalDegree 1 x i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = 0 <;>
      simp [NoetherNormalization.varChange, triangular, hi]
  exact AlgHom.congr_fun h q

private theorem unpack_evaluation {K : Type*} [Field K] [Algebra ℝ K]
    {n : ℕ} (q : MvPolynomial (Fin (n + 1)) K) (x : Parameters (Fin n)) :
    (MvPolynomial.finSuccEquiv K n q).eval₂
      (MvPolynomial.eval (fun i => algebraMap ℝ K (x.1 i))) (algebraMap ℝ K x.2) =
      MvPolynomial.eval (fun i => algebraMap ℝ K (Fin.cons (α := fun _ => ℝ) x.2 x.1 i)) q := by
  rw [← Polynomial.eval_map, ← MvPolynomial.eval_eq_eval_mv_eval']
  have h : (Fin.cons (algebraMap ℝ K x.2) (fun i => algebraMap ℝ K (x.1 i)) :
      Fin (n + 1) → K) = fun i => algebraMap ℝ K (Fin.cons (α := fun _ => ℝ) x.2 x.1 i) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  rw [h]

private theorem differentiated_cons {n : ℕ} :
    Differentiable ℝ (fun y : Parameters (Fin n) => Fin.cons (α := fun _ => ℝ) y.2 y.1) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    fun_prop
  · simp only [Fin.cons_succ]
    fun_prop

private theorem monic_normalization {K : Type*} [Field K] {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) K} (hp : p ≠ 0) :
    ∃ c : K, c ≠ 0 ∧
      (Polynomial.C (MvPolynomial.C c) *
        MvPolynomial.finSuccEquiv K n (NoetherNormalization.varChange p p)).Monic := by
  let Q := MvPolynomial.finSuccEquiv K n (NoetherNormalization.varChange p p)
  obtain ⟨a, ha, he⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp
    (NoetherNormalization.varChange_leadingCoeff_isUnit p hp)
  refine ⟨a⁻¹, inv_ne_zero ha.ne_zero, monic_C_mul_of_mul_leadingCoeff_eq_one ?_⟩
  change MvPolynomial.C (a⁻¹) * Q.leadingCoeff = 1
  rw [show Q.leadingCoeff = MvPolynomial.C a from he, ← map_mul,
    inv_mul_cancel₀ ha.ne_zero, map_one]

private theorem cover_real_zero {n : ℕ} {p : MvPolynomial (Fin (n + 1)) ℝ} (hp : p ≠ 0) :
    ∃ (ι : Type) (_ : Countable ι) (D : ι → Set (Fin n → ℝ)) (g : ι → (Fin n → ℝ) →
      (Fin (n + 1) → ℝ)), (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧
      {x | MvPolynomial.eval x p = 0} ⊆ ⋃ i, g i '' D i := by
  obtain ⟨c, _, hc⟩ := monic_normalization hp
  let Q := Polynomial.C (MvPolynomial.C c) *
    MvPolynomial.finSuccEquiv ℝ n (NoetherNormalization.varChange p p)
  obtain ⟨ι, hι, D, g, hd, hcov⟩ := countable_cover_monic_level (p := Q) hc
  let H : Parameters (Fin n) → Fin (n + 1) → ℝ :=
    fun x => triangular p.totalDegree 1 (Fin.cons x.2 x.1)
  have hH : Differentiable ℝ H :=
    (differentiable_triangular _ _).comp differentiated_cons
  refine ⟨ι, hι, D, fun i y => H (y, g i y), ?_, ?_⟩
  · intro i
    exact hH.differentiableOn.comp (differentiableOn_id.prodMk (hd i)) (mapsTo_univ _ _)
  · intro x hx
    let y := triangular p.totalDegree (-1) x
    let z : Parameters (Fin n) := (fun i => y i.succ, y 0)
    have hy : Fin.cons z.2 z.1 = y := by
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    have hHy : H z = x := by
      unfold H
      rw [hy, triangular_cancel]
    have hz : evalFamily Q z = 0 := by
      have hu := unpack_evaluation (NoetherNormalization.varChange p p) z
      have ht := triangular_eval p p (Fin.cons z.2 z.1)
      simp only [Algebra.algebraMap_self, RingHom.id_apply] at hu ht
      change MvPolynomial.eval x p = 0 at hx
      have hv : (MvPolynomial.finSuccEquiv ℝ n (NoetherNormalization.varChange p p)).eval₂
          (MvPolynomial.eval z.1) z.2 = 0 := by
        rw [hu, ht]
        change MvPolynomial.eval (H z) p = 0
        rw [hHy]
        exact hx
      simp only [Q, evalFamily, eval₂_mul, hv, mul_zero]
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hz)
    obtain ⟨u, hu, he⟩ := hi
    exact mem_iUnion.mpr ⟨i, u, hu, (congrArg H he).trans hHy⟩

private def realFamily {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) :
    Polynomial (MvPolynomial (Fin n) ℝ) :=
  ∑ k ∈ p.support, monomial k (realCoeff (p.coeff k))

private lemma realFamily_coeff {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ)) (k : ℕ) :
    (realFamily p).coeff k = realCoeff (p.coeff k) := by
  have hzero : realCoeff (0 : MvPolynomial (Fin n) ℂ) = 0 := by
    ext m
    simp [realCoeff]
  classical
  rw [realFamily, finsetSum_coeff]
  by_cases h : k ∈ p.support
  · rw [Finset.sum_eq_single_of_mem k h]
    · simp
    · intro j _ hj
      simp [coeff_monomial, hj, Ne.symm hj]
  · have hz := notMem_support_iff.mp h
    rw [hz, hzero]
    apply Finset.sum_eq_zero
    intro j hj
    have hn : k ≠ j := fun e => h (e ▸ hj)
    simp [coeff_monomial, hn, Ne.symm hn]

private lemma realFamily_monic {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hp : p.Monic) : (realFamily p).Monic := by
  have h1 : realCoeff (1 : MvPolynomial (Fin n) ℂ) = 1 := by
    ext m
    by_cases h : (0 : Fin n →₀ ℕ) = m <;> simp [realCoeff, MvPolynomial.coeff_one, h]
  have hz : realCoeff (0 : MvPolynomial (Fin n) ℂ) = 0 := by
    ext m
    simp [realCoeff]
  have hle : (realFamily p).natDegree ≤ p.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [realFamily_coeff, coeff_eq_zero_of_natDegree_lt hk, hz]
  have h : (realFamily p).coeff p.natDegree = 1 := by
    rw [realFamily_coeff, show p.coeff p.natDegree = p.leadingCoeff from rfl, hp, h1]
  have hd : (realFamily p).natDegree = p.natDegree :=
    le_antisymm hle (le_natDegree_of_ne_zero (h.trans_ne one_ne_zero))
  show (realFamily p).coeff (realFamily p).natDegree = 1
  rwa [hd]

private lemma realFamily_eval {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℂ))
    (x : Parameters (Fin n)) :
    evalFamily (realFamily p) x =
      (p.eval₂ (MvPolynomial.eval (fun i => (x.1 i : ℂ))) (x.2 : ℂ)).re := by
  unfold realFamily evalFamily
  have hp := congrArg
    (fun q : Polynomial (MvPolynomial (Fin n) ℂ) =>
      q.eval₂ (MvPolynomial.eval (fun i => (x.1 i : ℂ))) (x.2 : ℂ)) p.as_sum_support.symm
  rw [← hp]
  simp only [← coe_eval₂RingHom, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (monomial k (realCoeff (p.coeff k))).eval₂ (MvPolynomial.eval x.1) x.2 =
    ((monomial k (p.coeff k)).eval₂ (MvPolynomial.eval (fun i => (x.1 i : ℂ))) (x.2 : ℂ)).re
  simp only [eval₂_monomial, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, (coefficient_eval _ _).1]

private lemma nonzero_component {n : ℕ} {p : MvPolynomial (Fin n) ℂ} (h : p ≠ 0) :
    ∃ r : MvPolynomial (Fin n) ℝ, r ≠ 0 ∧
      ∀ x : Fin n → ℝ, MvPolynomial.eval (fun i => (x i : ℂ)) p = 0 →
        MvPolynomial.eval x r = 0 := by
  by_cases hr : realCoeff p = 0
  · refine ⟨imagCoeff p, ?_, fun x hx => (coefficient_eval p x).2.trans (by rw [hx]; rfl)⟩
    intro hi
    apply h
    simpa [hr, hi] using (coefficient_split p).symm
  · exact ⟨realCoeff p, hr, fun x hx => (coefficient_eval p x).1.trans (by rw [hx]; rfl)⟩

set_option maxHeartbeats 1000000 in
-- The resultant and the two coordinate changes elaborate over nested polynomial rings.
/-- Two relatively prime complex polynomials, restricted to real inputs,
have a common zero set covered by countably many differentiable maps
whose domains have two fewer real coordinates. -/
theorem cover_real_common_zeros {n : ℕ} {p q : MvPolynomial (Fin (n + 2)) ℂ}
    (hp : p ≠ 0) (h : IsRelPrime p q) :
    ∃ (ι : Type) (_ : Countable ι) (D : ι → Set (Fin n → ℝ)) (g : ι → (Fin n → ℝ) →
      (Fin (n + 2) → ℝ)), (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧
      {x | MvPolynomial.eval (fun j => (x j : ℂ)) p = 0 ∧
        MvPolynomial.eval (fun j => (x j : ℂ)) q = 0} ⊆ ⋃ i, g i '' D i := by
  let e := (NoetherNormalization.varChange p).trans (MvPolynomial.finSuccEquiv ℂ (n + 1))
  have he : IsRelPrime (e p) (e q) := by
    apply IsRelPrime.of_map e.symm
    simpa only [AlgEquiv.symm_apply_apply] using h
  obtain ⟨c, hc, hP⟩ := monic_normalization hp
  let P := Polynomial.C (MvPolynomial.C c) * e p
  let Q := e q
  have hunit : IsUnit (Polynomial.C (MvPolynomial.C c : MvPolynomial (Fin (n + 1)) ℂ)) :=
    ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C).map Polynomial.C
  have hrel : IsRelPrime P Q := by
    intro a ha hb
    exact he (hunit.dvd_mul_left.mp ha) hb
  letI : NormalizedGCDMonoid (MvPolynomial (Fin (n + 1)) ℂ) := Classical.arbitrary _
  have hs := resultant_ne_zero_of_isRelPrime hP.ne_zero hrel
  obtain ⟨r, hr, hrzero⟩ := nonzero_component hs
  let A : Set (Parameters (Fin (n + 1))) := {y |
    P.eval₂ (MvPolynomial.eval (fun j => (y.1 j : ℂ))) (y.2 : ℂ) = 0 ∧
    Q.eval₂ (MvPolynomial.eval (fun j => (y.1 j : ℂ))) (y.2 : ℂ) = 0}
  obtain ⟨ι, hι, D, f, hdf, hbase⟩ := cover_real_zero hr
  obtain ⟨κ, hκ, U, g, hdg, hgraph⟩ := countable_cover_monic_level (realFamily_monic hP)
  have hba : Prod.fst '' A ⊆ ⋃ i, f i '' D i := by
    rintro _ ⟨y, hy, rfl⟩
    exact hbase (hrzero _ (map_resultant_zero_of_common_root _ hP _ hy.1 hy.2))
  have hgr : A ⊆ ⋃ j, (fun x => (x, g j x)) '' U j := by
    intro y hy
    apply hgraph
    change evalFamily (realFamily P) y = 0
    rw [realFamily_eval, hy.1]
    rfl
  obtain ⟨V, F, hF, hcover⟩ := lift_graph_cover A D f U g hdf hdg hba hgr
  let H : Parameters (Fin (n + 1)) → Fin (n + 2) → ℝ :=
    fun x => triangular p.totalDegree 1 (Fin.cons x.2 x.1)
  have hH : Differentiable ℝ H := (differentiable_triangular _ _).comp differentiated_cons
  refine ⟨ι × κ, inferInstance, V, fun i => H ∘ F i,
    fun i => hH.differentiableOn.comp (hF i) (mapsTo_univ _ _), ?_⟩
  intro x hx
  let y := triangular p.totalDegree (-1) x
  let z : Parameters (Fin (n + 1)) := (fun i => y i.succ, y 0)
  have hy : Fin.cons z.2 z.1 = y := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hHy : H z = x := by
    unfold H
    rw [hy, triangular_cancel]
  have hshift (s : MvPolynomial (Fin (n + 2)) ℂ) :
      (e s).eval₂ (MvPolynomial.eval (fun j => (z.1 j : ℂ))) (z.2 : ℂ) =
        MvPolynomial.eval (fun j => (x j : ℂ)) s := by
    have heval := unpack_evaluation (NoetherNormalization.varChange p s) z
    have ht := triangular_eval p s (Fin.cons z.2 z.1)
    have hv : MvPolynomial.eval (fun j => (H z j : ℂ)) s =
        MvPolynomial.eval (fun j => (x j : ℂ)) s :=
      congrArg (fun a : Fin (n + 2) → ℝ => MvPolynomial.eval (fun j => (a j : ℂ)) s) hHy
    exact heval.trans (ht.trans hv)
  have hz : z ∈ A := by
    refine ⟨?_, (hshift q).trans hx.2⟩
    simp [P, hshift p, hx.1]
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz)
  obtain ⟨u, hu, he'⟩ := hi
  exact mem_iUnion.mpr ⟨i, u, hu, (congrArg H he').trans hHy⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSRealPolynomialZeros
