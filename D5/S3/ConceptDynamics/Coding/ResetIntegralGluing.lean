/- GID: D5/S3/ConceptDynamics/Coding/ResetIntegralGluing
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetIntegralGluing
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Integral compatible sign components with canonical coefficient-half reconstruction. -/
import D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open Polynomial ResetSignIntegerCyclic
open scoped BigOperators

def f (q : ℕ) : ℤ[X] := X ^ q - S q
def g (q : ℕ) : ℤ[X] := X ^ q + S q
abbrev Plus (q : ℕ) := ℤ[X] ⧸ (Ideal.span {f q} : Ideal ℤ[X])
abbrev Minus (q : ℕ) := ℤ[X] ⧸ (Ideal.span {g q} : Ideal ℤ[X])
def reduce : ℤ[X] →+* (ZMod 2)[X] := Polynomial.mapRingHom (Int.castRingHom _)
abbrev Common (q : ℕ) := (ZMod 2)[X] ⧸ (Ideal.span {reduce (g q)} : Ideal (ZMod 2)[X])

private theorem degree_S (q : ℕ) : (S q).degree < q := by
  simpa only [S, Fin.sum_univ_eq_sum_range, map_one, one_mul] using
    (degree_sum_fin_lt (fun _ : Fin q => (1 : ℤ)))

private theorem f_monic (q : ℕ) : (f q).Monic := monic_X_pow_sub (degree_S q)
private theorem g_monic (q : ℕ) : (g q).Monic := monic_X_pow_add (degree_S q)
private theorem common_monic (q : ℕ) : (reduce (g q)).Monic :=
  (g_monic q).map (Int.castRingHom (ZMod 2))

private theorem reduce_f (q : ℕ) : reduce (f q) = reduce (g q) := by
  simp only [f, g, map_sub, map_add]
  rw [sub_eq_add_neg, CharTwo.neg_eq]

private theorem product (q : ℕ) : F q = f q * g q := by
  simp only [F, f, g, show 2 * q = q * 2 by omega, pow_mul]
  ring

private theorem certificate (q : ℕ) : X * f q + (2 - X) * g q = 2 := by
  simp only [f, g]
  linear_combination 2 * geometric q

private theorem two_torsion (p : ℤ[X]) (h : (2 : ℤ) • p = 0) : p = 0 := by
  ext i
  have hi := congrArg (fun z : ℤ[X] => z.coeff i) h
  simp only [Polynomial.coeff_smul, Polynomial.coeff_zero, smul_eq_mul] at hi
  simp only [Polynomial.coeff_zero]
  omega

private theorem intersection_dvd (q : ℕ) (p : ℤ[X])
    (hf : f q ∣ p) (hg : g q ∣ p) : F q ∣ p := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have htwo : (2 : ℤ) • b = f q * (X * b + (2 - X) * a) := by
    have hc := certificate q
    have he : f q * a = g q * b := ha.symm.trans hb
    rw [Polynomial.smul_eq_C_mul]
    norm_num only [map_ofNat]
    linear_combination -b * hc - (2 - X) * he
  have hr : (2 : ℤ) • (b %ₘ f q) = 0 := by
    rw [← smul_modByMonic, htwo]
    exact (modByMonic_eq_zero_iff_dvd (f_monic q)).2 (dvd_mul_right _ _)
  obtain ⟨c, hc⟩ := (modByMonic_eq_zero_iff_dvd (f_monic q)).1 (two_torsion _ hr)
  rw [product, hb, hc]
  exact ⟨c, by ring⟩

/-- The integral sum and intersection of the two sign ideals. -/
theorem sign_ideals (q : ℕ) :
    (Ideal.span {f q} : Ideal ℤ[X]) ⊔ Ideal.span {g q} = Ideal.span {2, g q} ∧
    (Ideal.span {f q} : Ideal ℤ[X]) ⊓ Ideal.span {g q} = Ideal.span {F q} := by
  constructor
  · apply le_antisymm
    · apply sup_le
      · apply Ideal.span_le.mpr
        intro p hp
        simp only [Set.mem_singleton_iff] at hp
        subst p
        have hg : g q ∈ (Ideal.span {2, g q} : Ideal ℤ[X]) := Ideal.subset_span (by simp)
        have h2 : (2 : ℤ[X]) ∈ (Ideal.span {2, g q} : Ideal ℤ[X]) := Ideal.subset_span (by simp)
        have he : f q = g q - S q * 2 := by simp only [f, g]; ring
        rw [he]
        exact Ideal.sub_mem _ hg (Ideal.mul_mem_left _ _ h2)
      · exact Ideal.span_mono (by simp)
    · apply Ideal.span_le.mpr
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · rw [← certificate q]
        exact Ideal.add_mem _
          (Ideal.mul_mem_left _ _ (Submodule.mem_sup_left (Ideal.subset_span (by simp))))
          (Ideal.mul_mem_left _ _ (Submodule.mem_sup_right (Ideal.subset_span (by simp))))
      · exact Submodule.mem_sup_right (Ideal.subset_span (by simp))
  · ext p
    simp only [Ideal.mem_inf, Ideal.mem_span_singleton]
    constructor
    · exact fun h => intersection_dvd q p h.1 h.2
    · intro h
      rw [product] at h
      exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩

def commonPolynomial (q : ℕ) : ℤ[X] →+* Common q :=
  (AdjoinRoot.mk _).comp reduce

private theorem common_f (q : ℕ) : commonPolynomial q (f q) = 0 := by
  change AdjoinRoot.mk _ (reduce (f q)) = 0
  rw [reduce_f, AdjoinRoot.mk_self]
private theorem common_g (q : ℕ) : commonPolynomial q (g q) = 0 := AdjoinRoot.mk_self

def rplus (q : ℕ) : Plus q →+* Common q :=
  Ideal.Quotient.lift _ (commonPolynomial q) (by
    intro p hp
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, common_f, mul_zero])
def rminus (q : ℕ) : Minus q →+* Common q :=
  Ideal.Quotient.lift _ (commonPolynomial q) (by
    intro p hp
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, common_g, mul_zero])
abbrev Compatible (q : ℕ) := (rplus q).pullback (rminus q)

def plus (q : ℕ) : QF q →+* Plus q :=
  Ideal.Quotient.lift _ (AdjoinRoot.mk _) (by
    intro p hp
    apply AdjoinRoot.mk_eq_zero.mpr
    exact dvd_trans (by rw [product]; exact dvd_mul_right _ _) (Ideal.mem_span_singleton.mp hp))
def minus (q : ℕ) : QF q →+* Minus q :=
  Ideal.Quotient.lift _ (AdjoinRoot.mk _) (by
    intro p hp
    apply AdjoinRoot.mk_eq_zero.mpr
    exact dvd_trans (by rw [product]; exact dvd_mul_left _ _) (Ideal.mem_span_singleton.mp hp))

private theorem compatible_image (q : ℕ) (z : QF q) : rplus q (plus q z) = rminus q (minus q z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [plus, minus, rplus, rminus, AdjoinRoot.mk, Ideal.Quotient.lift_mk]

def toCompatible (q : ℕ) : QF q →+* Compatible q :=
  ((plus q).prod (minus q)).codRestrict _ (compatible_image q)

private theorem toCompatible_injective (q : ℕ) : Function.Injective (toCompatible q) := by
  intro z w he
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective w
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem p s).mpr
  apply Ideal.mem_span_singleton.mpr
  apply intersection_dvd
  · exact AdjoinRoot.mk_eq_mk.mp (congrArg (fun t : Compatible q => t.val.1) he)
  · exact AdjoinRoot.mk_eq_mk.mp (congrArg (fun t : Compatible q => t.val.2) he)


/-- Canonical monic representatives in the two integral components. -/
def a0 (q : ℕ) : Plus q →ₗ[ℤ] ℤ[X] := AdjoinRoot.modByMonicHom (f_monic q)
def b0 (q : ℕ) : Minus q →ₗ[ℤ] ℤ[X] := AdjoinRoot.modByMonicHom (g_monic q)

/-- Coefficientwise Euclidean division by two, including negative coefficients. -/
def half (p : ℤ[X]) : ℤ[X] :=
  ∑ i ∈ p.support, monomial i (p.coeff i / 2)

private theorem half_coeff (p : ℤ[X]) (i : ℕ) : (half p).coeff i = p.coeff i / 2 := by
  classical
  by_cases hi : i ∈ p.support
  · simp [half, Polynomial.coeff_sum, Polynomial.coeff_monomial, hi]
  · have hz : p.coeff i = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hi
    simp [half, Polynomial.coeff_sum, Polynomial.coeff_monomial, hi, hz]

private theorem reduce_a0 (q : ℕ) (a : Plus q) :
    reduce (a0 q a) = AdjoinRoot.modByMonicHom (common_monic q)
      (rplus q a) := by
  induction a using AdjoinRoot.induction_on with | ih p =>
  change reduce (p %ₘ f q) = reduce p %ₘ reduce (g q)
  rw [← reduce_f]
  exact Polynomial.map_modByMonic (Int.castRingHom (ZMod 2)) (f_monic q)

private theorem reduce_b0 (q : ℕ) (b : Minus q) :
    reduce (b0 q b) = AdjoinRoot.modByMonicHom (common_monic q)
      (rminus q b) := by
  induction b using AdjoinRoot.induction_on with | ih p =>
  exact Polynomial.map_modByMonic (Int.castRingHom (ZMod 2)) (g_monic q)

/-- Compatibility forces evenness of every coefficient of the canonical difference. -/
theorem compatible_even (q : ℕ) (z : Compatible q) :
    ∀ i : ℕ, (2 : ℤ) ∣ (a0 q z.val.1 - b0 q z.val.2).coeff i := by
  have h : reduce (a0 q z.val.1 - b0 q z.val.2) = 0 := by
    have hz : rplus q z.val.1 = rminus q z.val.2 := z.property
    rw [map_sub, reduce_a0, reduce_b0, hz, sub_self]
  intro i
  have hi := congrArg (fun p : (ZMod 2)[X] => p.coeff i) h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  simpa [reduce] using hi

private theorem difference_half (q : ℕ) (z : Compatible q) :
    a0 q z.val.1 - b0 q z.val.2 = 2 * half (a0 q z.val.1 - b0 q z.val.2) := by
  ext i
  rw [show (2 : ℤ[X]) = C 2 by norm_num, Polynomial.coeff_C_mul, half_coeff]
  have he := compatible_even q z i
  change _ = (2 : ℤ) * (_ / 2)
  omega

/-- The canonical coefficient-half reconstruction, before passage to the integral quotient. -/
def reconstruction (q : ℕ) (z : Compatible q) : ℤ[X] :=
  a0 q z.val.1 - X * f q * half (a0 q z.val.1 - b0 q z.val.2)

def fromCompatible (q : ℕ) (z : Compatible q) : QF q := fp q (reconstruction q z)

private theorem reconstruction_plus (q : ℕ) (z : Compatible q) :
    plus q (fromCompatible q z) = z.val.1 := by
  change AdjoinRoot.mk (f q) (reconstruction q z) = _
  unfold reconstruction
  rw [map_sub, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_mul, sub_zero]
  exact AdjoinRoot.mk_leftInverse (f_monic q) _

private theorem reconstruction_minus (q : ℕ) (z : Compatible q) :
    minus q (fromCompatible q z) = z.val.2 := by
  have he : reconstruction q z = b0 q z.val.2 +
      (2 - X) * g q * half (a0 q z.val.1 - b0 q z.val.2) := by
    unfold reconstruction
    linear_combination difference_half q z -
      half (a0 q z.val.1 - b0 q z.val.2) * certificate q
  change AdjoinRoot.mk (g q) (reconstruction q z) = _
  rw [he, map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_mul, add_zero]
  exact AdjoinRoot.mk_leftInverse (g_monic q) _

private theorem to_from (q : ℕ) (z : Compatible q) :
    toCompatible q (fromCompatible q z) = z := by
  apply Subtype.ext
  exact Prod.ext (reconstruction_plus q z) (reconstruction_minus q z)

private theorem from_to (q : ℕ) (z : QF q) :
    fromCompatible q (toCompatible q z) = z := by
  apply toCompatible_injective q
  exact to_from q (toCompatible q z)

/-- Literal integral sign gluing with the canonical coefficient-half inverse. -/
def gluing (q : ℕ) : QF q ≃+* Compatible q where
  toFun := toCompatible q
  invFun := fromCompatible q
  left_inv := from_to q
  right_inv := to_from q
  map_mul' := (toCompatible q).map_mul
  map_add' := (toCompatible q).map_add

private theorem representative_degrees (q : ℕ) (z : Compatible q) :
    (a0 q z.val.1).degree < q ∧ (b0 q z.val.2).degree < q := by
  have hf : (f q).degree = q := by
    exact (degree_sub_eq_left_of_degree_lt (by simpa using degree_S q)).trans (degree_X_pow q)
  have hg : (g q).degree = q := by
    exact (degree_add_eq_left_of_degree_lt (by simpa using degree_S q)).trans (degree_X_pow q)
  constructor
  · obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective z.val.1
    rw [← hp]
    change (p %ₘ f q).degree < q
    simpa only [hf] using degree_modByMonic_lt p (f_monic q)
  · obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective z.val.2
    rw [← hp]
    change (p %ₘ g q).degree < q
    simpa only [hg] using degree_modByMonic_lt p (g_monic q)

private theorem half_range (q : ℕ) (z : Compatible q) :
    half (a0 q z.val.1 - b0 q z.val.2) =
      ∑ i ∈ Finset.range q, monomial i ((a0 q z.val.1 - b0 q z.val.2).coeff i / 2) := by
  classical
  have hd : (a0 q z.val.1 - b0 q z.val.2).degree < q :=
    lt_of_le_of_lt (degree_sub_le _ _) (max_lt (representative_degrees q z).1
      (representative_degrees q z).2)
  ext i
  rw [half_coeff]
  by_cases hi : i < q
  · simp [Polynomial.coeff_sum, Polynomial.coeff_monomial, hi]
  · have hz : (a0 q z.val.1 - b0 q z.val.2).coeff i = 0 :=
      coeff_eq_zero_of_degree_lt (hd.trans_le (by exact_mod_cast Nat.le_of_not_gt hi))
    simp [Polynomial.coeff_sum, Polynomial.coeff_monomial, hi, hz]

/-- Both inverse identities, and the literal value on every polynomial class. -/
theorem integral_gluing (q : ℕ) (hq : 0 < q) :
    (∀ z : QF q, fromCompatible q (toCompatible q z) = z) ∧
    (∀ z : Compatible q, toCompatible q (fromCompatible q z) = z) ∧
    (∀ p : ℤ[X], (gluing q (fp q p)).val =
      (AdjoinRoot.mk (f q) p, AdjoinRoot.mk (g q) p)) ∧
    (∀ z : Compatible q, (gluing q).symm z =
      fp q (a0 q z.val.1 - X * f q * half (a0 q z.val.1 - b0 q z.val.2))) ∧
    (∀ z : Compatible q, (a0 q z.val.1).degree < q ∧ (b0 q z.val.2).degree < q) ∧
    (∀ z : Compatible q, half (a0 q z.val.1 - b0 q z.val.2) =
      ∑ i ∈ Finset.range q, monomial i ((a0 q z.val.1 - b0 q z.val.2).coeff i / 2)) := by
  exact ⟨from_to q, to_from q, fun _ => rfl, fun _ => rfl,
    representative_degrees q, half_range q⟩


private theorem half_cancel (p : ℤ[X]) (hp : reduce p = 0) :
    p = 2 * half p := by
  ext i
  rw [show (2 : ℤ[X]) = C 2 by norm_num, Polynomial.coeff_C_mul, half_coeff]
  have hi : (p.coeff i : ZMod 2) = 0 :=
    by simpa [reduce] using congrArg (fun r : (ZMod 2)[X] => r.coeff i) hp
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (p.coeff i) 2).mp hi
  omega

private theorem common_kernel (q : ℕ) :
    RingHom.ker (commonPolynomial q) = (Ideal.span {2, g q} : Ideal ℤ[X]) := by
  ext p
  constructor
  · intro hp
    have hz : AdjoinRoot.mk (reduce (g q)) (reduce p) = 0 := hp
    have hr : reduce (p %ₘ g q) = 0 := by
      rw [show reduce (p %ₘ g q) = reduce p %ₘ reduce (g q) from
        Polynomial.map_modByMonic (Int.castRingHom (ZMod 2)) (g_monic q)]
      exact (modByMonic_eq_zero_iff_dvd (common_monic q)).2
        (AdjoinRoot.mk_eq_zero.mp hz)
    have h2 : (2 : ℤ[X]) ∈ (Ideal.span {2, g q} : Ideal ℤ[X]) :=
      Ideal.subset_span (by simp)
    have hg : g q ∈ (Ideal.span {2, g q} : Ideal ℤ[X]) :=
      Ideal.subset_span (by simp)
    rw [← modByMonic_add_div p (g q), half_cancel _ hr]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h2) (Ideal.mul_mem_right _ _ hg)
  · intro hp
    apply (Ideal.span_le.mpr ?_ : Ideal.span {2, g q} ≤ RingHom.ker (commonPolynomial q)) hp
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · change commonPolynomial q 2 = 0
      change AdjoinRoot.mk _ (reduce 2) = 0
      have h2 : reduce 2 = 0 := by
        change Polynomial.map (Int.castRingHom (ZMod 2)) (C 2) = 0
        rw [Polynomial.map_C]
        change (C (2 : ZMod 2) : (ZMod 2)[X]) = 0
        rw [show (2 : ZMod 2) = 0 by decide, Polynomial.C_0]
      rw [h2, map_zero]
    · exact common_g q

private theorem common_surjective (q : ℕ) : Function.Surjective (commonPolynomial q) := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨p, hp⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod 2)) ZMod.intCast_surjective p
  exact ⟨p, congrArg (AdjoinRoot.mk _) hp⟩

/-- The quotient by the actual sum ideal is the literal coefficient-mod-two common ring. -/
def commonQuotientEquiv (q : ℕ) :
    (ℤ[X] ⧸ ((Ideal.span {f q} : Ideal ℤ[X]) ⊔ Ideal.span {g q})) ≃+* Common q :=
  (Ideal.quotEquivOfEq ((sign_ideals q).1.trans (common_kernel q).symm)).trans
    (RingHom.quotientKerEquivOfSurjective (common_surjective q))

private theorem W_plus (q : ℕ) : plus q (fp q (W q)) = 1 := by
  have he : W q = 1 - X * f q := by
    simp only [W, f]
    linear_combination geometric q
  change AdjoinRoot.mk (f q) (W q) = 1
  rw [he, map_sub, map_one, map_mul, AdjoinRoot.mk_self, mul_zero, sub_zero]

private theorem W_minus (q : ℕ) : minus q (fp q (W q)) = -1 := by
  have he : W q = -1 + (2 - X) * g q := by
    simp only [W, g]
    linear_combination -(geometric q)
  change AdjoinRoot.mk (g q) (W q) = -1
  rw [he, map_add, map_neg, map_one, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero]

/-- Forward time, the original sign, and every integer retain their literal orientation. -/
theorem gluing_generators (q : ℕ) :
    (gluing q (fp q X)).val =
      (AdjoinRoot.root (f q), AdjoinRoot.root (g q)) ∧
    (gluing q (fp q (W q))).val = (1, -1) ∧
    (∀ z : ℤ, (gluing q (fp q (C z))).val = ((z : Plus q), (z : Minus q))) ∧
    (∀ p : ℤ[X], commonQuotientEquiv q (Ideal.Quotient.mk _ p) = commonPolynomial q p) ∧
    reduce (g q) = ∑ k ∈ Finset.range (q + 1), (X : (ZMod 2)[X]) ^ k := by
  refine ⟨rfl, Prod.ext (W_plus q) (W_minus q), ?_, ?_, ?_⟩
  · intro z
    change (Ideal.Quotient.mk (Ideal.span {f q}) (C z),
      Ideal.Quotient.mk (Ideal.span {g q}) (C z)) = ((z : Plus q),(z : Minus q))
    rw [show C z = (z : ℤ[X]) from map_intCast C z, map_intCast, map_intCast]
  · intro p
    simp only [commonQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  · simp [reduce, g, S, Finset.sum_range_succ, Polynomial.map_sum]
    ring

end D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
