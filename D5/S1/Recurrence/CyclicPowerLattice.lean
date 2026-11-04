/- GID: D5/S1/Recurrence/CyclicPowerLattice
   generality: G
   mirror-B: D5/B/S1/Recurrence/CyclicPowerLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact integral relation kernel and finite indices of rational cyclic power lattices. -/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-! Rational power coordinates, the whole integral annihilator, and finite lattice growth. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Recurrence.CyclicPowerLattice
open Polynomial Matrix
open scoped BigOperators

/-- The distinguished first coordinate, including a harmless empty-dimensional definition. -/
def root (N : ℕ) : Fin N → ℚ := fun i => if i.val = 0 then 1 else 0

/-- Columns are the actual first powers of the distinguished input. -/
def powerMatrix {N : ℕ} (T : Matrix (Fin N) (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => ((T ^ j.val) *ᵥ root N) i

/-- Rational cyclic data with the whole primitive integral characteristic relation. -/
structure Data where
  N : ℕ
  positive : 0 < N
  T : Matrix (Fin N) (Fin N) ℚ
  cyclic : (powerMatrix T).det ≠ 0
  q : ℤ[X]
  primitive : q.IsPrimitive
  leading_positive : 0 < q.leadingCoeff
  relation : q.map (algebraMap ℤ ℚ) = C (q.leadingCoeff : ℚ) * T.charpoly

/-- Time in the actual power coordinates. -/
def time (d : Data) : Matrix (Fin d.N) (Fin d.N) ℚ :=
  (powerMatrix d.T)⁻¹ * d.T * powerMatrix d.T

/-- The complete power sequence in those coordinates. -/
def power (d : Data) (j : ℕ) : Fin d.N → ℚ := time d ^ j *ᵥ root d.N

/-- Evaluation on the actual input followed by the actual inverse power matrix. -/
def rationalEvaluation (d : Data) : ℚ[X] →ₗ[ℚ] (Fin d.N → ℚ) :=
  (Matrix.mulVecLin (powerMatrix d.T)⁻¹).comp
    (((Matrix.mulVecBilin ℚ ℚ).flip (root d.N)).comp (aeval d.T).toLinearMap)

/-- Integral polynomials evaluated in the same rational coordinates. -/
def evaluation (d : Data) : ℤ[X] →ₗ[ℤ] (Fin d.N → ℚ) :=
  (rationalEvaluation d).restrictScalars ℤ |>.comp
    (Polynomial.mapAlgHom (Algebra.ofId ℤ ℚ)).toLinearMap

/-- The integer span of the first L actual powers, in one fixed rational ambient group. -/
def lattice (d : Data) (L : ℕ) : Submodule ℤ (Fin d.N → ℚ) :=
  Submodule.span ℤ (Set.range fun j : Fin L => power d j.val)

/-- The coordinate integer lattice, defined as the image of all integer coordinate vectors. -/
def coordinateZ (N : ℕ) : AddSubgroup (Fin N → ℚ) :=
  (AddMonoidHom.pi fun i : Fin N =>
    (Int.castAddHom ℚ).comp (Pi.evalAddMonoidHom (fun _ : Fin N => ℤ) i)).range

private theorem inverse_mul (d : Data) : (powerMatrix d.T)⁻¹ * powerMatrix d.T = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr d.cyclic)

private theorem mul_inverse (d : Data) : powerMatrix d.T * (powerMatrix d.T)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr d.cyclic)

private theorem root_single (d : Data) : root d.N = Pi.single ⟨0, d.positive⟩ 1 := by
  ext i
  simp [root, Pi.single_apply, Fin.ext_iff]

private theorem matrix_column (d : Data) (j : Fin d.N) :
    powerMatrix d.T *ᵥ Pi.single j 1 = d.T ^ j.val *ᵥ root d.N := by
  rw [Matrix.mulVec_single_one]
  rfl

private theorem normalized_power (d : Data) (j : ℕ) :
    power d j = (powerMatrix d.T)⁻¹ *ᵥ (d.T ^ j *ᵥ root d.N) := by
  induction j with
  | zero =>
    simp only [power, pow_zero, Matrix.one_mulVec]
    have h := matrix_column d ⟨0, d.positive⟩
    simp only [pow_zero, Matrix.one_mulVec, ← root_single d] at h
    calc
      root d.N = (powerMatrix d.T)⁻¹ *ᵥ (powerMatrix d.T *ᵥ root d.N) := by
        rw [Matrix.mulVec_mulVec, inverse_mul, Matrix.one_mulVec]
      _ = _ := by rw [h]
  | succ j ih =>
    change (time d ^ (j + 1)) *ᵥ root d.N = _
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    change time d *ᵥ power d j = _
    rw [ih]
    simp only [Matrix.mulVec_mulVec]
    congr 1
    have hc : time d * (powerMatrix d.T)⁻¹ = (powerMatrix d.T)⁻¹ * d.T := by
      rw [time, Matrix.mul_assoc, mul_inverse, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, ← pow_succ']

private theorem low_power (d : Data) (j : Fin d.N) :
    power d j.val = Pi.single j 1 := by
  rw [normalized_power, ← matrix_column, Matrix.mulVec_mulVec, inverse_mul,
    Matrix.one_mulVec]

private theorem rationalEvaluation_apply (d : Data) (p : ℚ[X]) :
    rationalEvaluation d p =
      (powerMatrix d.T)⁻¹ *ᵥ (aeval d.T p *ᵥ root d.N) := rfl

private theorem rationalEvaluation_monomial (d : Data) (j : ℕ) (c : ℚ) :
    rationalEvaluation d (monomial j c) = c • power d j := by
  rw [show monomial j c = c • (X ^ j : ℚ[X]) by
    rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial], map_smul]
  congr 1
  simp [rationalEvaluation_apply, normalized_power]

private theorem evaluation_monomial (d : Data) (j : ℕ) (c : ℤ) :
    evaluation d (monomial j c) = c • power d j := by
  change rationalEvaluation d ((monomial j c).map (algebraMap ℤ ℚ)) = _
  rw [Polynomial.map_monomial, rationalEvaluation_monomial]
  exact_mod_cast (rfl : (c : ℚ) • power d j = (c : ℚ) • power d j)

private theorem rationalEvaluation_low (d : Data) (p : ℚ[X]) (hp : p.degree < d.N) :
    rationalEvaluation d p = fun i => p.coeff i.val := by
  have hs : p = ∑ j : Fin d.N, monomial j.val (p.coeff j.val) := by
    simpa using (p.sum_fin (fun j c => monomial j c) (by simp) hp).symm
  calc
    rationalEvaluation d p = ∑ j : Fin d.N, p.coeff j.val • Pi.single j 1 := by
      conv_lhs => rw [hs]
      rw [map_sum]
      simp_rw [rationalEvaluation_monomial, low_power]
    _ = _ := by ext i; simp [Finset.sum_apply, Pi.single_apply]

private theorem rational_kernel (d : Data) (p : ℚ[X]) :
    rationalEvaluation d p = 0 ↔ d.T.charpoly ∣ p := by
  constructor
  · intro h
    have hr : (p %ₘ d.T.charpoly).degree < d.N := by
      simpa [Matrix.charpoly_degree_eq_dim] using
        (degree_modByMonic_lt p d.T.charpoly_monic)
    have he : rationalEvaluation d (p %ₘ d.T.charpoly) = 0 := by
      rw [rationalEvaluation_apply, ← Matrix.aeval_eq_aeval_mod_charpoly]
      exact h
    rw [rationalEvaluation_low d _ hr] at he
    apply (modByMonic_eq_zero_iff_dvd d.T.charpoly_monic).mp
    ext j
    by_cases hj : j < d.N
    · exact congrFun he ⟨j, hj⟩
    · exact coeff_eq_zero_of_degree_lt (hr.trans_le (by exact_mod_cast Nat.le_of_not_gt hj))
  · rintro ⟨s, rfl⟩
    simp [rationalEvaluation_apply, map_mul, Matrix.aeval_self_charpoly]

private theorem whole_kernel (d : Data) (p : ℤ[X]) : evaluation d p = 0 ↔ d.q ∣ p := by
  change rationalEvaluation d (p.map (algebraMap ℤ ℚ)) = 0 ↔ _
  rw [rational_kernel]
  have hA : (d.q.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt d.leading_positive
  have he : d.q.map (algebraMap ℤ ℚ) ∣ p.map (algebraMap ℤ ℚ) ↔
      d.T.charpoly ∣ p.map (algebraMap ℤ ℚ) := by
    rw [d.relation, IsUnit.mul_left_dvd (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hA))]
  constructor
  · intro h
    exact d.primitive.dvd_of_fraction_map_dvd_fraction_map (he.mpr h)
  · intro h
    exact he.mp (Polynomial.map_dvd (algebraMap ℤ ℚ) h)

private theorem lattice_image (d : Data) (L : ℕ) :
    lattice d L = (degreeLT ℤ L).map (evaluation d) := by
  classical
  rw [lattice, degreeLT_eq_span_X_pow, Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_image, Finset.mem_range,
    Set.mem_range, exists_exists_and_eq_and]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j.val, j.isLt, ?_⟩
    simpa [← monomial_one_right_eq_X_pow] using evaluation_monomial d j.val 1
  · rintro ⟨j, hj, he⟩
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [← monomial_one_right_eq_X_pow, evaluation_monomial, one_smul] at he
    exact he

private theorem lattice_mono (d : Data) {L J : ℕ} (h : L ≤ J) :
    lattice d L ≤ lattice d J := by
  rw [lattice_image, lattice_image]
  exact Submodule.map_mono (degreeLT_mono h)

private theorem power_mem (d : Data) (l : ℕ) : power d l ∈ lattice d (l + 1) :=
  Submodule.subset_span ⟨⟨l, Nat.lt_succ_self l⟩, rfl⟩

private theorem q_degree (d : Data) : d.q.natDegree = d.N := by
  have hA : (d.q.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt d.leading_positive
  have h := congrArg Polynomial.natDegree d.relation
  rw [natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap ℤ ℚ) from Int.cast_injective),
    natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hA), Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin] at h
  exact h

private theorem leading_relation_mem (d : Data) (l : ℕ) (hl : d.N ≤ l) :
    d.q.leadingCoeff • power d l ∈ lattice d l := by
  let r : ℤ[X] := d.q * X ^ (l - d.N)
  have hq : d.q ≠ 0 := by
    intro h; simpa [h] using d.leading_positive
  have hr : r ≠ 0 := mul_ne_zero hq (pow_ne_zero _ X_ne_zero)
  have hd : r.natDegree = l := by
    dsimp [r]
    rw [natDegree_mul hq (pow_ne_zero _ X_ne_zero), q_degree, natDegree_X_pow,
      Nat.add_sub_of_le hl]
  have hc : r.leadingCoeff = d.q.leadingCoeff := by
    simp [r, leadingCoeff_mul]
  have he : evaluation d r = 0 := (whole_kernel d r).mpr ⟨X ^ (l - d.N), rfl⟩
  have hm : evaluation d r.eraseLead ∈ lattice d l := by
    rw [lattice_image]
    refine ⟨r.eraseLead, mem_degreeLT.mpr ?_, rfl⟩
    simpa [degree_eq_natDegree hr, hd] using degree_eraseLead_lt hr
  have hs := congrArg (evaluation d) r.eraseLead_add_monomial_natDegree_leadingCoeff
  rw [map_add, evaluation_monomial, he, hd, hc] at hs
  have hz : d.q.leadingCoeff • power d l = -evaluation d r.eraseLead := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hs)
  rw [hz]
  exact (lattice d l).neg_mem hm

private theorem integer_kernel (d : Data) (l : ℕ) (hl : d.N ≤ l) (n : ℤ) :
    n • power d l ∈ lattice d l ↔ d.q.leadingCoeff ∣ n := by
  constructor
  · intro hn
    by_cases hn0 : n = 0
    · simp [hn0]
    rw [lattice_image, Submodule.mem_map] at hn
    obtain ⟨p, hp, he⟩ := hn
    have hpdeg := mem_degreeLT.mp hp
    have hz : evaluation d (monomial l n - p) = 0 := by
      rw [map_sub, evaluation_monomial, he, sub_self]
    obtain ⟨s, hs⟩ := (whole_kernel d _).mp hz
    have hd : p.degree < (monomial l n).degree := by
      simpa [degree_monomial, hn0] using hpdeg
    have hc := congrArg Polynomial.leadingCoeff hs
    rw [leadingCoeff_sub_of_degree_lt hd, leadingCoeff_monomial, leadingCoeff_mul] at hc
    exact ⟨s.leadingCoeff, hc⟩
  · rintro ⟨k, rfl⟩
    rw [mul_comm, mul_smul]
    exact (lattice d l).smul_mem k (leading_relation_mem d l hl)

private theorem evaluation_low (d : Data) (p : ℤ[X]) (hp : p.degree < d.N) :
    evaluation d p = fun i => (p.coeff i.val : ℚ) := by
  change rationalEvaluation d (p.map (algebraMap ℤ ℚ)) = _
  rw [rationalEvaluation_low d _ ((degree_map_le).trans_lt hp)]
  simp

private theorem initial_lattice (d : Data) : (lattice d d.N).toAddSubgroup = coordinateZ d.N := by
  ext v
  change v ∈ lattice d d.N ↔ ∃ z : Fin d.N → ℤ, (fun i => (z i : ℚ)) = v
  rw [lattice_image, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨fun i => p.coeff i.val, ?_⟩
    exact (evaluation_low d p (mem_degreeLT.mp hp)).symm
  · rintro ⟨z, rfl⟩
    let p := (degreeLTEquiv ℤ d.N).symm z
    refine ⟨p.val, p.property, ?_⟩
    rw [evaluation_low d p.val (mem_degreeLT.mp p.property)]
    have he := (degreeLTEquiv ℤ d.N).apply_symm_apply z
    exact congrArg (fun w : Fin d.N → ℤ => fun i => (w i : ℚ)) he

/-- The next quotient uses two included lattices inside the successor lattice. -/
abbrev SuccessiveQuotient (d : Data) (l : ℕ) :=
  (lattice d (l + 1)).toAddSubgroup ⧸
    (lattice d l).toAddSubgroup.addSubgroupOf (lattice d (l + 1)).toAddSubgroup

/-- The actual new power, viewed in the successive quotient. -/
def quotientGenerator (d : Data) (l : ℕ) : SuccessiveQuotient d l :=
  QuotientAddGroup.mk (⟨power d l, power_mem d l⟩ : (lattice d (l + 1)).toAddSubgroup)

private theorem quotient_kernel (d : Data) (l : ℕ) (hl : d.N ≤ l) (n : ℤ) :
    n • quotientGenerator d l = 0 ↔ d.q.leadingCoeff ∣ n := by
  rw [quotientGenerator, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
  exact integer_kernel d l hl n

private theorem generator_order (d : Data) (l : ℕ) (hl : d.N ≤ l) :
    addOrderOf (quotientGenerator d l) = d.q.leadingCoeff.natAbs := by
  have h (n : ℕ) : n • quotientGenerator d l = 0 ↔ d.q.leadingCoeff.natAbs ∣ n := by
    rw [← Int.dvd_natCast, ← quotient_kernel d l hl]
    simp only [natCast_zsmul]
  exact Nat.dvd_antisymm
    (addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((h _).mpr dvd_rfl))
    ((h _).mp (addOrderOf_nsmul_eq_zero _))

private theorem lattice_succ (d : Data) (l : ℕ) :
    lattice d (l + 1) = (ℤ ∙ power d l) ⊔ lattice d l := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j.val < l
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨j.val, hj⟩, rfl⟩)
    · have he : j.val = l := by omega
      dsimp only
      rw [he]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (power_mem d l))
      (lattice_mono d (Nat.le_succ l))

private theorem generator_spans (d : Data) (l : ℕ) :
    AddSubgroup.zmultiples (quotientGenerator d l) = ⊤ := by
  apply (AddSubgroup.eq_top_iff' _).mpr
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    have hx : x.val ∈ (ℤ ∙ power d l) ⊔ lattice d l := by
      simpa only [Submodule.mem_toAddSubgroup, lattice_succ d l] using x.property
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
    obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hu
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨n, ?_⟩
    change n • quotientGenerator d l = QuotientAddGroup.mk x
    rw [quotientGenerator, ← QuotientAddGroup.mk_zsmul]
    apply QuotientAddGroup.eq.mpr
    change -(n • power d l) + x.val ∈ lattice d l
    rw [hn, ← huv]
    simpa only [neg_add_cancel_left] using hv

private theorem successive_finite_card (d : Data) (l : ℕ) (hl : d.N ≤ l) :
    Finite (SuccessiveQuotient d l) ∧
      Nat.card (SuccessiveQuotient d l) = d.q.leadingCoeff.natAbs := by
  have ho := generator_order d l hl
  have hpos : 0 < addOrderOf (quotientGenerator d l) := by
    rw [ho]
    exact Int.natAbs_pos.mpr (ne_of_gt d.leading_positive)
  have hf := finEquivZMultiples (addOrderOf_pos_iff.mp hpos)
  have hg := generator_spans d l
  have hfinite : Finite (AddSubgroup.zmultiples (quotientGenerator d l)) :=
    Finite.of_equiv _ hf
  have hfin : Finite (SuccessiveQuotient d l) := by
    rw [hg] at hfinite
    exact Finite.of_equiv _ AddSubgroup.topEquiv.toEquiv
  refine ⟨hfin, ?_⟩
  have hcard := Nat.card_zmultiples (quotientGenerator d l)
  rw [hg, Nat.card_congr AddSubgroup.topEquiv.toEquiv, ho] at hcard
  exact hcard

private theorem relative_index (d : Data) (L : ℕ) (hL : d.N ≤ L) :
    (coordinateZ d.N).relIndex (lattice d L).toAddSubgroup =
      d.q.leadingCoeff.natAbs ^ (L - d.N) := by
  induction L, hL using Nat.le_induction with
  | base => rw [← initial_lattice, AddSubgroup.relIndex_self]; simp
  | succ L hL ih =>
    have hbase : coordinateZ d.N ≤ (lattice d L).toAddSubgroup := by
      rw [← initial_lattice]
      exact lattice_mono d hL
    have hstep : (lattice d L).toAddSubgroup ≤ (lattice d (L + 1)).toAddSubgroup :=
      lattice_mono d (Nat.le_succ L)
    have hi : (lattice d L).toAddSubgroup.relIndex (lattice d (L + 1)).toAddSubgroup =
        d.q.leadingCoeff.natAbs := (successive_finite_card d L hL).2
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hbase hstep, ih, hi,
      Nat.succ_sub hL, pow_succ]

private theorem total_finite (d : Data) (L : ℕ) (hL : d.N ≤ L) :
    Finite ((lattice d L).toAddSubgroup ⧸
      (coordinateZ d.N).addSubgroupOf (lattice d L).toAddSubgroup) := by
  have hn : (coordinateZ d.N).relIndex (lattice d L).toAddSubgroup ≠ 0 := by
    rw [relative_index d L hL]
    exact pow_ne_zero _ (Int.natAbs_ne_zero.mpr (ne_of_gt d.leading_positive))
  let : (coordinateZ d.N).IsFiniteRelIndex (lattice d L).toAddSubgroup := ⟨hn⟩
  infer_instance

/-- Whole-polynomial relations determine successive finite quotients and the total index.
The input is arbitrary rational cyclic data; no spectral, sign or irreducibility condition is used. -/
theorem cyclic_power_lattice (d : Data) :
    (∀ j : Fin d.N, power d j.val = Pi.single j 1) ∧
    (∀ p : ℤ[X], evaluation d p = 0 ↔ d.q ∣ p) ∧
    (lattice d d.N).toAddSubgroup = coordinateZ d.N ∧
    (∀ l : ℕ, d.N ≤ l →
      (∀ n : ℤ, n • power d l ∈ lattice d l ↔ d.q.leadingCoeff ∣ n) ∧
      addOrderOf (quotientGenerator d l) = d.q.leadingCoeff.natAbs ∧
      Finite (SuccessiveQuotient d l) ∧
      Nat.card (SuccessiveQuotient d l) = d.q.leadingCoeff.natAbs) ∧
    (∀ L : ℕ, d.N ≤ L →
      Finite ((lattice d L).toAddSubgroup ⧸
        (coordinateZ d.N).addSubgroupOf (lattice d L).toAddSubgroup) ∧
      (coordinateZ d.N).relIndex (lattice d L).toAddSubgroup =
        d.q.leadingCoeff.natAbs ^ (L - d.N)) := by
  refine ⟨low_power d, whole_kernel d, initial_lattice d, ?_, ?_⟩
  · intro l hl
    exact ⟨integer_kernel d l hl, generator_order d l hl,
      (successive_finite_card d l hl).1, (successive_finite_card d l hl).2⟩
  · intro L hL
    exact ⟨total_finite d L hL, relative_index d L hL⟩

/-- info: 'D5.S1.Recurrence.CyclicPowerLattice.cyclic_power_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cyclic_power_lattice

end D5.S1.Recurrence.CyclicPowerLattice
