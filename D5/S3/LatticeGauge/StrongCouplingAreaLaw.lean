/- GID: D5/S3/LatticeGauge/StrongCouplingAreaLaw
   generality: G
   mirror-B: none(waiver:covered-by-lattice-reflection-positivity4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The strong-coupling component expansion and central cancellation for rectangular loops. -/

import D5.S3.LatticeGauge.ClusterCombinatorics
import D5.S3.LatticeGauge.RectangleGeometry

/-!
Omega original.

The strong-coupling component expansion and central cancellation for rectangular loops.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Matrix Filter

namespace Omega.LatticeGauge

section StrongCoupling

variable {Ω P : Type*} [MeasurableSpace Ω] [Fintype P] [DecidableEq P]
variable (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (χ : P → Ω → ℂ) (β : ℝ)

private noncomputable def gaugeBoltzmann (S : Finset P) (x : Ω) : ℝ :=
  ∏ p ∈ S, Real.exp (β * (χ p x).re)

omit [MeasurableSpace Ω] [Fintype P] [DecidableEq P] in
private theorem gaugeBoltzmann_exp (S : Finset P) (x : Ω) :
    gaugeBoltzmann χ β S x = Real.exp (∑ p ∈ S, β * (χ p x).re) :=
  (Real.exp_sum _ _).symm

omit [MeasurableSpace Ω] [Fintype P] [DecidableEq P] in
private theorem gaugeBoltzmann_pos (S : Finset P) (x : Ω) :
    0 < gaugeBoltzmann χ β S x :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

omit [Fintype P] [DecidableEq P] in
private theorem gaugeBoltzmann_measurable (hχ : ∀ p, Measurable (χ p)) (S : Finset P) :
    Measurable (gaugeBoltzmann χ β S) :=
  Finset.measurable_prod S fun p _ => Real.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_re.comp (hχ p)))

omit [MeasurableSpace Ω] [Fintype P] [DecidableEq P] in
private theorem gaugeBoltzmann_le {d : ℝ} (hβ : 0 ≤ β) (hb : ∀ p x, ‖χ p x‖ ≤ d)
    (S : Finset P) (x : Ω) : gaugeBoltzmann χ β S x ≤ Real.exp (β * d) ^ S.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun p _ =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (hb p x)) hβ)

private theorem integrable_bounded {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V] {f : Ω → V} (hm : Measurable f) {M : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ M) : Integrable f ν :=
  (integrable_const M).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)

omit [IsProbabilityMeasure ν] in
private theorem phase_integral_zero {f : Ω → ℂ} {z : ℂ} (hz : z ≠ 1) {τ : Ω ≃ᵐ Ω}
    (hτ : MeasurePreserving τ ν ν) (h : ∀ x, f (τ x) = z * f x) :
    (∫ x, f x ∂ν) = 0 := by
  have hI := hτ.integral_comp' f
  simp_rw [h, integral_const_mul] at hI
  have hmul : (z - 1) * (∫ x, f x ∂ν) = 0 := by rw [sub_mul, one_mul, hI, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz)

private theorem gauge_partition_mono {d : ℝ} (hβ : 0 ≤ β) (hχ : ∀ p, Measurable (χ p))
    (hb : ∀ p x, ‖χ p x‖ ≤ d) (D : Finset P)
    (htwist : ∀ p ∉ D, ∃ z : ℂ, z ≠ 1 ∧ ∃ τ : Ω ≃ᵐ Ω, MeasurePreserving τ ν ν ∧
      (∀ x, χ p (τ x) = z * χ p x) ∧ ∀ q ∈ D, ∀ x, χ q (τ x) = χ q x) :
    (∫ x, gaugeBoltzmann χ β D x ∂ν) ≤ ∫ x, gaugeBoltzmann χ β Finset.univ x ∂ν := by
  let C := Finset.univ \ D
  let w := gaugeBoltzmann χ β D
  have hw : Measurable w := gaugeBoltzmann_measurable χ β hχ D
  have hw_pos : ∀ x, 0 < w x := gaugeBoltzmann_pos χ β D
  have hw_le : ∀ x, w x ≤ Real.exp (β * d) ^ D.card := gaugeBoltzmann_le χ β hβ hb D
  have hwint : Integrable w ν :=
    integrable_bounded ν hw fun x => by simpa [abs_of_pos (hw_pos x)] using hw_le x
  have hprod : ∀ p, Integrable (fun x => χ p x * (w x : ℂ)) ν := by
    intro p
    apply integrable_bounded ν ((hχ p).mul (Complex.continuous_ofReal.measurable.comp hw))
    intro x
    change ‖χ p x * (w x : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw_pos x)]
    exact mul_le_mul (hb p x) (hw_le x) (hw_pos x).le ((norm_nonneg _).trans (hb p x))
  have hvan : ∀ p ∈ C, (∫ x, (χ p x).re * w x ∂ν) = 0 := by
    intro p hp
    obtain ⟨z, hz, τ, hτ, hτp, hτD⟩ := htwist p (Finset.mem_sdiff.mp hp).2
    have hzero := phase_integral_zero ν hz hτ (f := fun x => χ p x * (w x : ℂ)) fun x => by
      have heq : w (τ x) = w x := Finset.prod_congr rfl fun q hq => by rw [hτD q hq x]
      rw [hτp, heq, mul_assoc]
    have hh := integral_re (hprod p)
    rw [hzero] at hh
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.zero_re] using hh
  have hlin : ∀ p, Integrable (fun x => β * ((χ p x).re * w x)) ν := by
    intro p
    have hr := Complex.reCLM.integrable_comp (hprod p)
    simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using hr.const_mul β
  have hsum : Integrable (fun x => ∑ p ∈ C, β * ((χ p x).re * w x)) ν :=
    integrable_finsetSum C fun p _ => hlin p
  have hid : (∫ x, w x + ∑ p ∈ C, β * ((χ p x).re * w x) ∂ν) = ∫ x, w x ∂ν := by
    rw [integral_add hwint hsum, integral_finsetSum _ (fun p _ => hlin p)]
    simp only [integral_const_mul]
    rw [add_eq_left]
    exact Finset.sum_eq_zero fun p hp => by rw [hvan p hp, mul_zero]
  rw [← hid]
  refine integral_mono (hwint.add hsum)
    (integrable_bounded ν (gaugeBoltzmann_measurable χ β hχ Finset.univ) fun x => by
      simpa [abs_of_pos (gaugeBoltzmann_pos χ β Finset.univ x)] using
        gaugeBoltzmann_le χ β hβ hb Finset.univ x) ?_
  intro x
  have hsplit : gaugeBoltzmann χ β Finset.univ x = w x * gaugeBoltzmann χ β C x := by
    change gaugeBoltzmann χ β Finset.univ x = gaugeBoltzmann χ β D x * gaugeBoltzmann χ β C x
    simp only [gaugeBoltzmann, ← Finset.prod_union Finset.disjoint_sdiff, C,
      Finset.union_sdiff_of_subset (Finset.subset_univ D)]
  rw [hsplit, gaugeBoltzmann_exp]
  calc
    w x + ∑ p ∈ C, β * ((χ p x).re * w x) = w x * (1 + ∑ p ∈ C, β * (χ p x).re) := by
      simp only [mul_add, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa only [add_comm] using Real.add_one_le_exp (∑ p ∈ C, β * (χ p x).re)) (hw_pos x).le

private noncomputable def activity (p : P) (x : Ω) : ℝ :=
  Real.exp (β * (χ p x).re) - 1

omit [MeasurableSpace Ω] [Fintype P] [DecidableEq P] in
private theorem activity_bound {d : ℝ} (hβ : 0 ≤ β) (hb : ∀ p x, ‖χ p x‖ ≤ d)
    (p : P) (x : Ω) : ‖activity χ β p x‖ ≤ Real.exp (β * d) - 1 := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum ((β * (χ p x).re : ℝ) : ℂ) 1
  have hh : ‖activity χ β p x‖ ≤ Real.exp ‖β * (χ p x).re‖ - 1 := by
    norm_num only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
    rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Complex.norm_real] at h
    exact h
  refine hh.trans (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
  rw [norm_mul, Real.norm_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hb p x)) hβ

variable (roots : Finset P) (adj : P → P → Prop) [DecidableRel adj]

private noncomputable def componentIntegrand (W : Ω → ℂ) (S : Finset P) (x : Ω) : ℂ :=
  W x * (↑(∏ p ∈ S, activity χ β p x) : ℂ) * (gaugeBoltzmann χ β (exterior roots adj S) x : ℂ)

theorem strong_coupling_finite_component_bound (W : Ω → ℂ) {d : ℝ} (hd : 0 ≤ d)
    (hβ : 0 ≤ β) (hχ : ∀ p, Measurable (χ p)) (hb : ∀ p x, ‖χ p x‖ ≤ d)
    (hmW : Measurable W) (hbW : ∀ x, ‖W x‖ ≤ 1) (keep : Finset P → Prop)
    (hlocal : ∀ S p, p ∉ exterior roots adj S →
      ∃ z : ℂ, z ≠ 1 ∧ ∃ τ : Ω ≃ᵐ Ω, MeasurePreserving τ ν ν ∧
        (∀ x, χ p (τ x) = z * χ p x) ∧ ∀ q ∈ exterior roots adj S, ∀ x, χ q (τ x) = χ q x)
    (hselection : ∀ S, rootedComponent roots adj S = S → ¬ keep S →
      ∃ z : ℂ, z ≠ 1 ∧ ∃ τ : Ω ≃ᵐ Ω, MeasurePreserving τ ν ν ∧
        (∀ x, W (τ x) = z * W x) ∧ ∀ q ∈ S ∪ exterior roots adj S, ∀ x, χ q (τ x) = χ q x) :
    ‖(∫ x, W x * (gaugeBoltzmann χ β Finset.univ x : ℂ) ∂ν) /
      ((∫ x, gaugeBoltzmann χ β Finset.univ x ∂ν : ℝ) : ℂ)‖ ≤
      ∑ S ∈ componentFamilyWhere roots adj keep, (Real.exp (β * d) - 1) ^ S.card := by
  classical
  let δ := Real.exp (β * d) - 1
  let D := exterior roots adj
  let w := gaugeBoltzmann χ β
  let f := componentIntegrand χ β roots adj W
  let Z := ∫ x, w Finset.univ x ∂ν
  have hδ : 0 ≤ δ := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hβ hd))
  have hw : ∀ S, Integrable (w S) ν := by
    intro S
    refine integrable_bounded ν (gaugeBoltzmann_measurable χ β hχ S)
      (M := Real.exp (β * d) ^ S.card) fun x => ?_
    change ‖gaugeBoltzmann χ β S x‖ ≤ _
    rw [Real.norm_of_nonneg (gaugeBoltzmann_pos χ β S x).le]
    exact gaugeBoltzmann_le χ β hβ hb S x
  have hZ : 0 < Z := by
    have heq : w Finset.univ = fun x => Real.exp (∑ p : P, β * (χ p x).re) :=
      funext (gaugeBoltzmann_exp χ β Finset.univ)
    change 0 < ∫ x, w Finset.univ x ∂ν
    rw [heq]
    exact integral_exp_pos (heq ▸ hw Finset.univ)
  have hnorm (S : Finset P) (x : Ω) : ‖f S x‖ ≤ δ ^ S.card * w (D S) x := by
    simp only [f, componentIntegrand, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (gaugeBoltzmann_pos χ β (D S) x).le, D, w]
    have hwp := (gaugeBoltzmann_pos χ β (D S) x).le
    apply mul_le_mul_of_nonneg_right _ hwp
    calc
      _ ≤ ‖∏ p ∈ S, activity χ β p x‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hbW x) (norm_nonneg _)
      _ ≤ ∏ p ∈ S, ‖activity χ β p x‖ := Finset.norm_prod_le _ _
      _ ≤ δ ^ S.card := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun p _ => activity_bound χ β hβ hb p x
  have hf (S : Finset P) : Integrable (f S) ν := by
    apply (hw (D S)).const_mul (δ ^ S.card) |>.mono'
    · apply Measurable.aestronglyMeasurable
      have ha : ∀ p, Measurable (activity χ β p) := fun p =>
        (Real.measurable_exp.comp (measurable_const.mul (Complex.measurable_re.comp (hχ p)))).sub
          measurable_const
      exact (hmW.mul (Complex.continuous_ofReal.measurable.comp
        (Finset.measurable_prod S fun p _ => ha p))).mul
          (Complex.continuous_ofReal.measurable.comp (gaugeBoltzmann_measurable χ β hχ (D S)))
    · exact Filter.Eventually.of_forall (hnorm S)
  have hzero (S : Finset P) (hS : rootedComponent roots adj S = S) (hsmall : ¬ keep S) :
      (∫ x, f S x ∂ν) = 0 := by
    obtain ⟨z, hz, τ, hτ, hW, hfix⟩ := hselection S hS hsmall
    apply phase_integral_zero ν hz hτ
    intro x
    have hp : (∏ p ∈ S, activity χ β p (τ x)) = ∏ p ∈ S, activity χ β p x :=
      Finset.prod_congr rfl fun p hp => by
        simp only [activity, hfix p (Finset.mem_union_left _ hp) x]
    have hw' : w (D S) (τ x) = w (D S) x :=
      Finset.prod_congr rfl fun p hp => by rw [hfix p (Finset.mem_union_right _ hp) x]
    simp only [f, componentIntegrand, hW, hp, ← mul_assoc]
    rw [show gaugeBoltzmann χ β (exterior roots adj S) (τ x) = _ from hw']
  let family := (Finset.univ : Finset P).powerset.filter (fun S => rootedComponent roots adj S = S)
  have hnum : (∫ x, W x * (w Finset.univ x : ℂ) ∂ν) = ∑ S ∈ family, ∫ x, f S x ∂ν := by
    rw [← integral_finsetSum _ (fun S _ => hf S)]
    apply integral_congr_ae
    filter_upwards with x
    have hn := prod_component_expansion roots adj (fun p => activity χ β p x)
    simp_rw [show ∀ p, 1 + activity χ β p x = Real.exp (β * (χ p x).re) from fun p => by
      simp [activity]] at hn
    change W x * (w Finset.univ x : ℂ) = ∑ S ∈ family, f S x
    rw [show w Finset.univ x = ∑ S ∈ family, (∏ p ∈ S, activity χ β p x) * w (D S) x from hn]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, f, componentIntegrand, mul_assoc, w, D]
  have hnum' : (∫ x, W x * (w Finset.univ x : ℂ) ∂ν) =
      ∑ S ∈ componentFamilyWhere roots adj keep, ∫ x, f S x ∂ν := by
    rw [hnum, show componentFamilyWhere roots adj keep = family.filter (keep) from by
      ext S; simp [componentFamilyWhere, family]]
    nth_rw 2 [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S hS => ?_
    split_ifs with hi
    · rfl
    · exact hzero S (Finset.mem_filter.mp hS).2 hi
  have hbound (S : Finset P) : ‖∫ x, f S x ∂ν‖ ≤ δ ^ S.card * Z := by
    calc
      _ ≤ ∫ x, ‖f S x‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ x, δ ^ S.card * w (D S) x ∂ν :=
        integral_mono (hf S).norm ((hw (D S)).const_mul _) (hnorm S)
      _ = δ ^ S.card * (∫ x, w (D S) x ∂ν) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (gauge_partition_mono ν χ β hβ hχ hb (D S) (hlocal S))
        (pow_nonneg hδ _)
  change ‖(∫ x, W x * (w Finset.univ x : ℂ) ∂ν) / (Z : ℂ)‖ ≤
    ∑ S ∈ componentFamilyWhere roots adj keep, δ ^ S.card
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ, hnum']
  apply (div_le_iff₀ hZ).mpr
  calc
    _ ≤ ∑ S ∈ componentFamilyWhere roots adj keep, ‖∫ x, f S x ∂ν‖ := norm_sum_le _ _
    _ ≤ ∑ S ∈ componentFamilyWhere roots adj keep, δ ^ S.card * Z := Finset.sum_le_sum fun S _ => hbound S
    _ = _ := (Finset.sum_mul _ _ _).symm

end StrongCoupling

variable {n : Fin 4 → ℕ} {G : Type*} [Group G] {d : ℕ}
variable [MeasurableSpace G]

section WilsonAreaLaw

variable [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

noncomputable def rectangleCharacter (D : GaugeData G d) (r : Rectangle n) (u : Link n → G) : ℂ :=
  (D.rep (pathHolonomy u r.edges)).trace / d

def plaquetteCharacter (D : GaugeData G d) (p : Plaquette n) (u : Link n → G) : ℂ :=
  (D.rep (squareHolonomy u p)).trace

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem measurable_character (D : GaugeData G d) :
    Measurable (fun a => (D.rep a).trace) :=
  Finset.measurable_sum _ fun i _ => D.measurable_entry i i

/-- The Wilson loop expectation in the open box with side lengths given by `n`. -/
noncomputable def wilsonLoop (D : GaugeData G d) (β : ℝ) (r : Rectangle n) : ℂ :=
  (∫ u, rectangleCharacter D r u * (gaugeBoltzmann (plaquetteCharacter D) β Finset.univ u : ℂ)
    ∂configMeasure μ (Link n)) /
  ((∫ u, gaugeBoltzmann (plaquetteCharacter D) β Finset.univ u ∂configMeasure μ (Link n) : ℝ) : ℂ)

private def observedLinks (marked : Link n) (S : Finset (Plaquette n)) : Finset (Link n) :=
  insert marked (S.biUnion squareLinks)

private theorem squareLinks_subset_observed (marked : Link n) {S : Finset (Plaquette n)}
    {p : Plaquette n} (hp : p ∈ S) : squareLinks p ⊆ observedLinks marked S := fun _ he =>
  Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨p, hp, he⟩)

private theorem external_links_disjoint (marked : Link n) {S : Finset (Plaquette n)}
    {p : Plaquette n} (hp : p ∈ exterior (incidentSquares marked) squareAdj S) :
    Disjoint (observedLinks marked S) (squareLinks p) := by
  classical
  have h : p ∉ incidentSquares marked ∧ p ∉ S ∧ ∀ q ∈ S, ¬ squareAdj q p := by
    simpa only [exterior, Finset.mem_filter, Finset.mem_univ, true_and] using hp
  obtain ⟨root, outside, noAdj⟩ := h
  rw [Finset.disjoint_left]
  intro e he hep
  rcases Finset.mem_insert.mp he with rfl | he
  · exact root (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hep⟩)
  · obtain ⟨q, hq, heq⟩ := Finset.mem_biUnion.mp he
    exact noAdj q hq ⟨fun h => outside (h ▸ hq), e, heq, hep⟩

private theorem internal_link (marked : Link n) {S : Finset (Plaquette n)}
    {p : Plaquette n} (hp : p ∉ exterior (incidentSquares marked) squareAdj S) :
    ∃ e ∈ observedLinks marked S, e ∈ squareLinks p := by
  classical
  simp only [exterior, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not,
    not_forall] at hp
  rcases hp with hp | hp | ⟨q, hq, -, e, heq, hep⟩
  · exact ⟨marked, Finset.mem_insert_self .., (Finset.mem_filter.mp hp).2⟩
  · have he : (⟨(p.val.1, p.val.2.1), p.property.2.1⟩ : Link n) ∈ squareLinks p := by
      obtain ⟨⟨v,i,j⟩, hij, hi, hj⟩ := p
      simp [squareLinks]
    exact ⟨_, squareLinks_subset_observed marked hp he, he⟩
  · exact ⟨e, squareLinks_subset_observed marked hq heq, hep⟩

private theorem mem_squareLinks (p : Plaquette n) (e : Link n × Bool)
    (he : e ∈ squareEdges p) : e.1 ∈ squareLinks p := by
  obtain ⟨⟨v,i,j⟩, hij, hi, hj⟩ := p
  simp only [squareEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp [squareLinks]

private theorem circulation_congr {E : Type*} (path : List (E × Bool)) {a b : E → ℤ}
    (h : ∀ e ∈ path, a e.1 = b e.1) : circulation a path = circulation b path := by
  unfold circulation
  congr 1
  exact List.map_congr_left (fun e he => by simp [signedExponent, h e he])

private theorem circulation_zero {E : Type*} (path : List (E × Bool)) :
    circulation (fun _ : E => 0) path = 0 := by
  induction path with
  | nil => rfl
  | cons e tail ih =>
    change signedExponent (fun _ : E => 0) e + circulation (fun _ : E => 0) tail = 0
    simp [signedExponent, ih]

private def clip {E : Type*} [DecidableEq E] (S : Finset E) (a : E → ℤ) (e : E) : ℤ :=
  if e ∈ S then a e else 0

private theorem clipped_circulation (p : Plaquette n) {S : Finset (Link n)} (a : Link n → ℤ)
    (hp : squareLinks p ⊆ S) :
    circulation (clip S a) (squareEdges p) = circulation a (squareEdges p) :=
  circulation_congr _ (fun e he => by simp [clip, hp (mem_squareLinks p e he)])

private theorem exterior_circulation (marked : Link n) {S : Finset (Plaquette n)}
    {p : Plaquette n} (hp : p ∈ exterior (incidentSquares marked) squareAdj S) (a : Link n → ℤ) :
    circulation (clip (observedLinks marked S) a) (squareEdges p) = 0 := by
  rw [← circulation_zero (squareEdges p)]
  exact circulation_congr _ fun e he => by
    have hn : e.1 ∉ observedLinks marked S := fun h =>
      Finset.disjoint_left.mp (external_links_disjoint marked hp) h (mem_squareLinks p e he)
    simp [clip, hn]

private def edgeCochain (e e' : Link n) : ℤ := if e' = e then 1 else 0

private theorem one_edge_circulation (p : Plaquette n) (e : Link n) (he : e ∈ squareLinks p) :
    circulation (edgeCochain e) (squareEdges p) = 1 ∨
      circulation (edgeCochain e) (squareEdges p) = -1 := by
  obtain ⟨⟨v,i,j⟩, hij, hi, hj⟩ := p
  have hi' : shift v i ≠ v := by
    intro h
    have hv := congrArg (fun w : Vertex n => (w i).val) h
    rw [shift_val_same hi] at hv
    exact Nat.succ_ne_self _ hv
  have hj' : shift v j ≠ v := by
    intro h
    have hv := congrArg (fun w : Vertex n => (w j).val) h
    rw [shift_val_same hj] at hv
    exact Nat.succ_ne_self _ hv
  simp only [squareLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp [circulation, squareEdges, edgeCochain, signedExponent, Subtype.ext_iff,
      Prod.mk.injEq, hij.ne, hij.ne.symm, hi', hi'.symm, hj', hj'.symm]

omit [MeasurableInv G] in
private theorem twist_square_of_zero (D : GaugeData G d) (z : Subgroup.center G)
    (a : Link n → ℤ) (p : Plaquette n) (u : Link n → G)
    (hp : circulation a (squareEdges p) = 0) :
    plaquetteCharacter D p (twistEquiv (z : G) a u) = plaquetteCharacter D p u := by
  change (D.rep (squareHolonomy (twist (z : G) a u) p)).trace = _
  rw [square_eq_path, twist_holonomy, hp, zpow_zero, one_mul, ← square_eq_path]
  rfl

omit [MeasurableInv G] in
private theorem trace_twist_of_sign (D : GaugeData G d) (z : Subgroup.center G) {ζ : ℂ}
    (hz : D.rep z = ζ • 1) {a : Link n → ℤ} {path : List (Link n × Bool)} (u : Link n → G) :
    (circulation a path = 1 →
      (D.rep (pathHolonomy (twistEquiv (z : G) a u) path)).trace =
        ζ * (D.rep (pathHolonomy u path)).trace) ∧
    (circulation a path = -1 →
      (D.rep (pathHolonomy (twistEquiv (z : G) a u) path)).trace =
        conj ζ * (D.rep (pathHolonomy u path)).trace) := by
  change (_ → (D.rep (pathHolonomy (twist (z : G) a u) path)).trace = _) ∧
    (_ → (D.rep (pathHolonomy (twist (z : G) a u) path)).trace = _)
  constructor
  · intro h
    rw [twist_holonomy, h, zpow_one, trace_central_mul D _ ζ hz]
  · intro h
    rw [twist_holonomy, h, zpow_neg_one, trace_central_inv_mul D _ ζ hz]

private def projectsTo (r : Rectangle n) (a : Fin r.width) (b : Fin r.height)
    (p : Plaquette n) : Prop :=
  p.val.2.1 = r.i ∧ p.val.2.2 = r.j ∧
    (p.val.1 r.i).val = (r.origin r.i).val + a ∧ (p.val.1 r.j).val = (r.origin r.j).val + b

def coversRectangle (r : Rectangle n) (S : Finset (Plaquette n)) : Prop :=
  ∀ (a : Fin r.width) (b : Fin r.height), ∃ p ∈ S, projectsTo r a b p

theorem coversRectangle_area (r : Rectangle n) (S : Finset (Plaquette n))
    (h : coversRectangle r S) : r.width * r.height ≤ S.card := by
  classical
  unfold coversRectangle at h
  choose f hfS hf using h
  let enc : Fin r.width × Fin r.height → S := fun q => ⟨f q.1 q.2, hfS q.1 q.2⟩
  have hinj : Function.Injective enc := by
    rintro ⟨a,b⟩ ⟨a',b'⟩ henc
    have heq : f a b = f a' b' := congrArg Subtype.val henc
    have h₁ := hf a b
    rw [heq] at h₁
    have h₂ := hf a' b'
    unfold projectsTo at h₁ h₂
    exact Prod.ext (Fin.ext (Nat.add_left_cancel (h₁.2.2.1.symm.trans h₂.2.2.1)))
      (Fin.ext (Nat.add_left_cancel (h₁.2.2.2.symm.trans h₂.2.2.2)))
  have hc := Fintype.card_le_of_injective enc hinj
  simp at hc
  exact hc


private theorem conjugate_ne_one {ζ : ℂ} (hζ : ζ ≠ 1) : conj ζ ≠ 1 := by
  intro h
  apply hζ
  simpa only [Complex.conj_conj, map_one] using congrArg (starRingEnd ℂ) h

omit [MeasurableInv G] in
theorem local_central_change (D : GaugeData G d) (z : Subgroup.center G)
    {ζ : ℂ} (hz : D.rep z = ζ • 1) (hζ : ζ ≠ 1) (marked : Link n)
    (S : Finset (Plaquette n)) (p : Plaquette n)
    (hp : p ∉ exterior (incidentSquares marked) squareAdj S) :
    ∃ phase : ℂ, phase ≠ 1 ∧ ∃ τ : (Link n → G) ≃ᵐ (Link n → G),
      MeasurePreserving τ (configMeasure μ (Link n)) (configMeasure μ (Link n)) ∧
      (∀ u, plaquetteCharacter D p (τ u) = phase * plaquetteCharacter D p u) ∧
      ∀ q ∈ exterior (incidentSquares marked) squareAdj S, ∀ u,
        plaquetteCharacter D q (τ u) = plaquetteCharacter D q u := by
  obtain ⟨e, he, hpe⟩ := internal_link marked hp
  let a := edgeCochain e
  have ha : clip (observedLinks marked S) a = a := by
    funext f
    by_cases hf : f = e
    · subst f
      simp [clip, he]
    · simp [clip, a, edgeCochain, hf]
  have hf q (hq : q ∈ exterior (incidentSquares marked) squareAdj S) u :
      plaquetteCharacter D q (twistEquiv (z : G) a u) = plaquetteCharacter D q u :=
    twist_square_of_zero D z a q u (ha ▸ exterior_circulation marked hq a)
  rcases one_edge_circulation p e hpe with h | h
  · refine ⟨ζ, hζ, twistEquiv (z : G) a, twist_preserving μ _ _, ?_, hf⟩
    intro u
    simpa only [plaquetteCharacter, square_eq_path] using (trace_twist_of_sign D z hz u).1 h
  · refine ⟨conj ζ, conjugate_ne_one hζ, twistEquiv (z : G) a, twist_preserving μ _ _, ?_, hf⟩
    intro u
    simpa only [plaquetteCharacter, square_eq_path] using (trace_twist_of_sign D z hz u).2 h

private theorem square_coboundary (p : Plaquette n) (f : Vertex n → ℤ) :
    circulation (fun e => f (src e) - f (dst e)) (squareEdges p) = 0 := by
  obtain ⟨⟨v,i,j⟩, hij, hi, hj⟩ := p
  simp only [circulation, squareEdges, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, signedExponent, Bool.false_eq_true, ite_false, ite_true, src, dst, shift_comm v hij.ne]
  ring

omit [MeasurableInv G] in
theorem rectangle_central_change (D : GaugeData G d) (z : Subgroup.center G)
    {ζ : ℂ} (hz : D.rep z = ζ • 1) (hζ : ζ ≠ 1) (r : Rectangle n)
    {L : ℕ} (vertices : Fin L → Vertex n) (edge : Fin L → Link n × Bool)
    (hv : Function.Injective vertices)
    (hs : ∀ k, (if (edge k).2 then src (edge k).1 else dst (edge k).1) = vertices k)
    (ht : ∀ k, (if (edge k).2 then dst (edge k).1 else src (edge k).1) = vertices (finRotate L k))
    (hedges : List.ofFn edge = r.edges) (k₀ : Fin L)
    (S : Finset (Plaquette n)) (hS : ¬ coversRectangle r S) :
    ∃ phase : ℂ, phase ≠ 1 ∧ ∃ τ : (Link n → G) ≃ᵐ (Link n → G),
      MeasurePreserving τ (configMeasure μ (Link n)) (configMeasure μ (Link n)) ∧
      (∀ u, rectangleCharacter D r (τ u) = phase * rectangleCharacter D r u) ∧
      ∀ p ∈ S ∪ exterior (incidentSquares (edge k₀).1) squareAdj S, ∀ u,
        plaquetteCharacter D p (τ u) = plaquetteCharacter D p u := by
  classical
  let V := observedLinks (edge k₀).1 S
  have observed : (edge k₀).1 ∈ V := Finset.mem_insert_self ..
  have selection :
      ∃ b : Link n → ℤ, (∀ p ∈ S, circulation b (squareEdges p) = 0) ∧
        (circulation (clip V b) r.edges = 1 ∨ circulation (clip V b) r.edges = -1) := by
    by_cases hwhole : ∀ k, (edge k).1 ∈ V
    · unfold coversRectangle at hS
      push Not at hS
      obtain ⟨x, y, hcell⟩ := hS
      let b := rayCochain (n := n) r.i r.j ((r.origin r.i).val + x) ((r.origin r.j).val + y)
      refine ⟨b, ?_, Or.inr ?_⟩
      · intro p hp
        dsimp only [b]
        simp only [projectsTo] at hcell
        rw [ray_circulation _ _ r.axes, ite_eq_right (hcell p hp)]
      · calc
          circulation (clip V b) r.edges = circulation b r.edges := by
            apply circulation_congr
            intro e he
            rw [← hedges, List.mem_ofFn] at he
            obtain ⟨k, rfl⟩ := he
            simp [clip, hwhole k]
          _ = -1 := r.cell_ray x y
    · obtain ⟨f, hf⟩ := restricted_coboundary_detects_partial_cycle src dst V vertices edge
        hv hs ht ⟨k₀, observed⟩ (not_forall.mp hwhole)
      refine ⟨fun e => f (src e) - f (dst e), fun p _ => square_coboundary p f, ?_⟩
      rw [hedges] at hf
      exact hf
  obtain ⟨b, hb, hsign⟩ := selection
  let a := clip V b
  have hfix p (hp : p ∈ S ∪ exterior (incidentSquares (edge k₀).1) squareAdj S) u :
      plaquetteCharacter D p (twistEquiv (z : G) a u) = plaquetteCharacter D p u := by
    apply twist_square_of_zero D z
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (clipped_circulation p b (squareLinks_subset_observed (edge k₀).1 hp)).trans (hb p hp)
    · exact exterior_circulation (edge k₀).1 hp b
  rcases hsign with h | h
  · refine ⟨ζ, hζ, twistEquiv (z : G) a, twist_preserving μ _ _, ?_, hfix⟩
    intro u
    unfold rectangleCharacter
    rw [(trace_twist_of_sign D z hz u).1 (show circulation a r.edges = 1 from h), mul_div_assoc]
  · refine ⟨conj ζ, conjugate_ne_one hζ, twistEquiv (z : G) a, twist_preserving μ _ _, ?_, hfix⟩
    intro u
    unfold rectangleCharacter
    rw [(trace_twist_of_sign D z hz u).2 (show circulation a r.edges = -1 from h), mul_div_assoc]


theorem rectangleCharacter_measurable (D : GaugeData G d) (r : Rectangle n) :
    Measurable (rectangleCharacter D r) :=
  ((measurable_character D).comp (measurable_path r.edges)).div_const _

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem rectangleCharacter_norm_le (D : GaugeData G d) (hd : 0 < d)
    (r : Rectangle n) (u : Link n → G) : ‖rectangleCharacter D r u‖ ≤ 1 := by
  rw [rectangleCharacter, norm_div, Complex.norm_natCast]
  exact (div_le_one (by exact_mod_cast hd)).mpr (norm_trace_le D _)

/-- Rooted connected sets of plaquettes that project onto every cell of the rectangle. -/
noncomputable def rectangleComponents (r : Rectangle n) (hw : 0 < r.width) : Finset (Finset (Plaquette n)) :=
  componentFamilyWhere (incidentSquares (r.horizontal 0 (Nat.zero_le _) ⟨0, hw⟩))
    squareAdj (coversRectangle r)

omit [μ.IsMulLeftInvariant] in
theorem wilsonLoop_norm_le_one (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < d) (r : Rectangle n) : ‖wilsonLoop μ D β r‖ ≤ 1 := by
  let ν := configMeasure μ (Link n)
  let : IsProbabilityMeasure ν := by unfold ν configMeasure; infer_instance
  let w := gaugeBoltzmann (plaquetteCharacter (n := n) D) β Finset.univ
  have wm : Measurable w := gaugeBoltzmann_measurable _ β
    (fun p => (measurable_character D).comp (measurable_square p)) _
  have wp (u : Link n → G) : 0 ≤ w u := (gaugeBoltzmann_pos _ β _ u).le
  have wi : Integrable w ν :=
    integrable_bounded ν wm (M := Real.exp (β * d) ^ (Fintype.card (Plaquette n))) fun u => by
      rw [Real.norm_of_nonneg (wp u)]
      simpa [w] using gaugeBoltzmann_le (plaquetteCharacter D) β hβ
        (fun p u => norm_trace_le D _) Finset.univ u
  have hdom (u : Link n → G) : ‖rectangleCharacter D r u * (w u : ℂ)‖ ≤ w u := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (wp u)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (rectangleCharacter_norm_le D hd r u) (wp u)
  have hi : Integrable (fun u => rectangleCharacter D r u * (w u : ℂ)) ν :=
    wi.mono' (((rectangleCharacter_measurable D r).mul
      (Complex.measurable_ofReal.comp wm)).aestronglyMeasurable) (ae_of_all _ hdom)
  have hZ : 0 < ∫ u, w u ∂ν := by
    have heq : w = fun u => Real.exp (∑ p : Plaquette n, β * (plaquetteCharacter D p u).re) :=
      funext (gaugeBoltzmann_exp _ _ Finset.univ)
    rw [heq]
    exact integral_exp_pos (heq ▸ wi)
  change ‖(∫ u, rectangleCharacter D r u * (w u : ℂ) ∂ν) / ((∫ u, w u ∂ν : ℝ) : ℂ)‖ ≤ 1
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le, div_le_one hZ]
  exact (norm_integral_le_integral_norm _).trans (integral_mono hi.norm wi hdom)

end WilsonAreaLaw

end Omega.LatticeGauge
