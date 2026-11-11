/- GID: D5/S3/Topology/EJAFiniteSpectral
   generality: G
   mirror-B: D5/B/S3/Topology/EJAFiniteSpectral
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Algebra.Jordan.Basic, mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: General finite real Euclidean Jordan spectral resolutions on the original carrier. -/

/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license; see docs/reports/third-party/euclidean-jordan-LICENSE.txt.
Authors: Bryan Ehrlich

Adapted from ehrlich-b/euclidean-jordan, immutable revision
 a83407e4dbf73c77c31a2291c02f20b37a5ebbaf:
 Power, PowerAssoc, FormallyReal, Subalgebra, Frame, Spectral, Class.
Only the live spectral proof dependency is retained. The polarized identity uses
pinned Mathlib directly. Retirement: when this repository's pinned Mathlib contains
an equivalent general bilinear spectral theorem, replace this port by that theorem.
-/

module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.EJAFiniteSpectral

open scoped BigOperators

section Pow

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J]

private def jpow (x : J) : ℕ → J
  | 0 => x
  | (n + 1) => x * jpow x n

omit [IsCommJordan J] in
@[simp] private theorem jpow_zero (x : J) : jpow x 0 = x := rfl

omit [IsCommJordan J] in
@[simp] private theorem jpow_succ (x : J) (n : ℕ) : jpow x (n + 1) = x * jpow x n := rfl

omit [IsCommJordan J] in
private theorem jpow_succ' (x : J) (n : ℕ) : jpow x (n + 1) = jpow x n * x := by
  rw [jpow_succ, mul_comm]

private def CommuteAt (x : J) (m : ℕ) : Prop := ∀ w : J, x * (jpow x m * w) = jpow x m * (x * w)

omit [IsCommJordan J] in

private theorem jpow_mul_jpow_of_commuteAt {x : J} {m : ℕ} (h : CommuteAt x m) (n : ℕ) :
    jpow x m * jpow x n = jpow x (m + n + 1) := by
  induction n with
  | zero => rw [jpow_zero, ← jpow_succ', Nat.add_zero]
  | succ n ih =>
      rw [jpow_succ, ← h (jpow x n), ih,
        show m + (n + 1) + 1 = (m + n + 1) + 1 from by omega]
      exact (jpow_succ x (m + n + 1)).symm

end Pow

section Albert

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]

private def cm (x : J) (i j : ℕ) (w : J) : J :=
  jpow x i * (jpow x j * w) - jpow x j * (jpow x i * w)

omit [IsCommJordan J] [Module ℝ J] in
private theorem cm_antisymm (x : J) (i j : ℕ) (w : J) : cm x i j w = - cm x j i w := by simp [cm]

omit [IsCommJordan J] [Module ℝ J] in
private theorem cm_self (x : J) (i : ℕ) (w : J) : cm x i i w = 0 := by simp [cm]

omit [IsCommJordan J] [Module ℝ J] in

private theorem commuteAt_of_cm {x : J} {i : ℕ} (h : ∀ w, cm x 0 i w = 0) : CommuteAt x i := by
  intro w
  have hw := h w
  rw [cm, jpow_zero] at hw
  exact sub_eq_zero.mp hw

private theorem cm_cyclic (x : J) (i j : ℕ) (hij : jpow x i * jpow x j = jpow x (i + j + 1)) (w : J) :
    cm x j (i + 1) w + cm x 0 (i + j + 1) w + cm x i (j + 1) w = 0 := by
  let B (b c : J) := b * (c * w) - c * (b * w)
  have h := congrArg (fun f : AddMonoid.End J => f w)
    (two_nsmul_lie_lmul_lmul_add_add_eq_zero x (jpow x i) (jpow x j))
  simp only [two_smul, Ring.lie_def] at h
  change (B x (jpow x i * jpow x j) + B (jpow x i) (jpow x j * x) +
    B (jpow x j) (x * jpow x i)) +
    (B x (jpow x i * jpow x j) + B (jpow x i) (jpow x j * x) +
    B (jpow x j) (x * jpow x i)) = 0 at h
  have hz : (2 : ℝ) • (B x (jpow x i * jpow x j) +
      B (jpow x i) (jpow x j * x) + B (jpow x j) (x * jpow x i)) = 0 := by
    simpa only [two_smul] using h
  have he := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  rw [hij, ← jpow_succ' x j, ← jpow_succ x i] at he
  simpa only [B, cm, jpow_zero, add_comm, add_left_comm, add_assoc] using he

private theorem cm_eq_zero (x : J) (N : ℕ) : ∀ i j : ℕ, i + j ≤ N → ∀ w : J, cm x i j w = 0 := by
  induction N with
  | zero =>
      intro i j hij w
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
      exact cm_self x 0 w
  | succ N ih =>
      have hA : ∀ i j : ℕ, i + j ≤ N → jpow x i * jpow x j = jpow x (i + j + 1) := fun i j hij =>
        jpow_mul_jpow_of_commuteAt (commuteAt_of_cm (fun w => ih 0 i (by omega) w)) j
      intro i j hij w
      rcases Nat.lt_or_ge (i + j) (N + 1) with hlt | hge
      · exact ih i j (by omega) w
      · have hsum : i + j = N + 1 := by omega
        set c : J := cm x 0 (N + 1) w with hc
        have key : ∀ k : ℕ, k ≤ N + 1 → ∀ l : ℕ, k + l = N + 1 → cm x k l w = (k + 1) • c := by
          intro k
          induction k with
          | zero =>
              intro _ l hl
              obtain rfl : l = N + 1 := by omega
              simp [hc]
          | succ k ihk =>
              intro hk l hl
              have hcyc := cm_cyclic x l k (hA l k (by omega)) w
              rw [show l + k + 1 = N + 1 from by omega] at hcyc
              rw [ihk (by omega) (l + 1) (by omega), cm_antisymm x l (k + 1) w, ← hc] at hcyc
              rw [(add_neg_eq_zero.mp hcyc).symm, ← succ_nsmul]
        have hlast : cm x (N + 1) 0 w = (N + 2) • c := key (N + 1) le_rfl 0 (by omega)
        have hneg : cm x (N + 1) 0 w = - c := by rw [cm_antisymm x (N + 1) 0 w, ← hc]
        have hzero : (N + 3) • c = 0 := by
          have h2 : (N + 2) • c = -c := by rw [← hlast, hneg]
          rw [show N + 3 = (N + 2) + 1 from rfl, succ_nsmul, h2]
          exact neg_add_cancel c
        rw [key i (by omega) j (by omega), nsmul_eq_zero_iff' (n := N + 3) (by omega) hzero,
          smul_zero]

private theorem commuteAt_all (x : J) (m : ℕ) : CommuteAt x m :=
  commuteAt_of_cm (fun w => cm_eq_zero x m 0 m (by omega) w)

private theorem jpow_mul_jpow (x : J) (m n : ℕ) : jpow x m * jpow x n = jpow x (m + n + 1) :=
  jpow_mul_jpow_of_commuteAt (commuteAt_all x m) n

end Albert

private class IsFormallyReal (J : Type*) [Mul J] [AddCommMonoid J] : Prop where
  
  eq_zero_of_sum_mul_self : ∀ {ι : Type} (s : Finset ι) (f : ι → J),
    ∑ i ∈ s, f i * f i = 0 → ∀ i ∈ s, f i = 0

section Basic

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsFormallyReal J]

private theorem eq_zero_of_mul_self_eq_zero {x : J} (h : x * x = 0) : x = 0 := by
  have := IsFormallyReal.eq_zero_of_sum_mul_self ({0} : Finset ℕ) (fun _ => x) (by simpa using h)
  exact this 0 (Finset.mem_singleton_self 0)

end Basic

section Nilpotent

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsFormallyReal J]

omit [IsFormallyReal J] in

private theorem jpow_eq_zero_of_le {x : J} {n : ℕ} (h : jpow x n = 0) {m : ℕ} (hm : n ≤ m) :
    jpow x m = 0 := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hlt
  · exact h
  · have hsplit : jpow x n * jpow x (m - n - 1) = jpow x m := by
      rw [jpow_mul_jpow]
      congr 1
      omega
    rw [← hsplit, h, zero_mul]

private theorem eq_zero_of_jpow_eq_zero {x : J} : ∀ (n : ℕ), jpow x n = 0 → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro h
      match n with
      | 0 => simpa using h
      | (k + 1) =>
          have hsq : jpow x k * jpow x k = 0 := by
            rw [jpow_mul_jpow]
            exact jpow_eq_zero_of_le h (by omega)
          exact ih k (by omega) (eq_zero_of_mul_self_eq_zero hsq)

end Nilpotent

section Relation
variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module ℝ J] [Module.Finite ℝ J]
private theorem exists_jpow_relation (x : J) :
    ∃ (n : ℕ) (c : Fin n → ℝ), (∃ i, c i ≠ 0) ∧ ∑ i, c i • jpow x i = 0 := by
  have hnot : ¬ LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ J + 1) => jpow x i) := by
    intro h
    have hle := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hle
    omega
  obtain ⟨c, hsum, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
  exact ⟨_, c, ⟨i, hi⟩, hsum⟩

end Relation

section Family
variable {J : Type*} [NonUnitalNonAssocCommRing J]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private structure IsOrthIdemFamily (p : ι → J) : Prop where
  
  idem : ∀ i, p i * p i = p i
  
  orth : ∀ i j, i ≠ j → p i * p j = 0

namespace IsOrthIdemFamily

variable {p : ι → J}

private theorem sum_idem (hp : IsOrthIdemFamily p) (s : Finset ι) :
    (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hne => hp.orth i j (Ne.symm hne)) (fun h => absurd hi h)]
  exact hp.idem i

end IsOrthIdemFamily
end Family

section Scalar
variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module ℝ J] [IsScalarTower ℝ J J]
private theorem mul_smul_comm' (r : ℝ) (a b : J) : a * (r • b) = r • (a * b) := by
  rw [mul_comm, smul_mul_assoc, mul_comm]
end Scalar

open Polynomial

section Eval

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

private noncomputable def jeval (x : J) : Polynomial ℝ →ₗ[ℝ] J where
  toFun p := p.sum fun n a => a • jpow x n
  map_add' p q :=
    Polynomial.sum_add_index p q _ (fun _ => zero_smul _ _) (fun _ b₁ b₂ => add_smul b₁ b₂ _)
  map_smul' r p := by
    simp only [RingHom.id_apply]
    rw [Polynomial.sum_smul_index p r (fun n a => a • jpow x n) (fun _ => zero_smul ℝ _),
      Polynomial.smul_sum]
    exact Finset.sum_congr rfl fun n _ => (mul_smul r _ _)

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
@[simp] private theorem jeval_monomial (x : J) (n : ℕ) (a : ℝ) :
    jeval x (monomial n a) = a • jpow x n :=
  Polynomial.sum_monomial_index a (fun n a => a • jpow x n) (zero_smul _ _)

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
@[simp] private theorem jeval_one (x : J) : jeval x 1 = x := by
  rw [← C_1, ← monomial_zero_left, jeval_monomial, one_smul, jpow_zero]

omit [IsCommJordan J] in

private theorem jeval_X_mul (x : J) (p : Polynomial ℝ) : jeval x (X * p) = x * jeval x p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]
  | monomial n a =>
      rw [X_mul_monomial, jeval_monomial, jeval_monomial, jpow_succ,
        mul_smul_comm']

private theorem jeval_mul (x : J) (p q : Polynomial ℝ) :
    jeval x p * jeval x q = jeval x (X * p * q) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => rw [map_add, add_mul, hp₁, hp₂, mul_add, add_mul, map_add]
  | monomial m a =>
      induction q using Polynomial.induction_on' with
      | add q₁ q₂ hq₁ hq₂ => rw [map_add, mul_add, hq₁, hq₂, mul_add, map_add]
      | monomial n b =>
          rw [jeval_monomial, jeval_monomial, smul_mul_assoc, mul_smul_comm', jpow_mul_jpow,
            smul_smul, X_mul_monomial, monomial_mul_monomial, jeval_monomial]
          congr 2
          omega

end Eval

section Annihilator

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

omit [IsCommJordan J] in
private theorem jeval_X_pow_mul {x : J} {p : Polynomial ℝ} (hp : jeval x p = 0) (k : ℕ) :
    jeval x (X ^ k * p) = 0 := by
  induction k with
  | zero => simpa using hp
  | succ k ih => rw [pow_succ', mul_assoc, jeval_X_mul, ih, mul_zero]

omit [IsCommJordan J] in
private theorem jeval_mul_eq_zero {x : J} {p : Polynomial ℝ} (hp : jeval x p = 0) (q : Polynomial ℝ) :
    jeval x (q * p) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, add_zero]
  | monomial n a =>
      have hmul : (monomial n a : Polynomial ℝ) * p = a • (X ^ n * p) := by
        rw [← C_mul_X_pow_eq_monomial, smul_eq_C_mul, mul_assoc]
      rw [hmul, map_smul, jeval_X_pow_mul hp n, smul_zero]

private noncomputable def jann (x : J) : Ideal (Polynomial ℝ) where
  carrier := {p | jeval x p = 0}
  add_mem' := fun {p q} hp hq => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, hp, hq, add_zero]
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
  smul_mem' := fun q p hp => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    exact jeval_mul_eq_zero hp q

omit [IsCommJordan J] in
private theorem mem_jann {x : J} {p : Polynomial ℝ} : p ∈ jann x ↔ jeval x p = 0 := Iff.rfl

omit [IsCommJordan J] in

private theorem exists_annihilator_generator [Module.Finite ℝ J] (x : J) :
    ∃ m : Polynomial ℝ, m ≠ 0 ∧ ∀ f, jeval x f = 0 ↔ m ∣ f := by
  obtain ⟨n, c, ⟨i₀, hi₀⟩, hsum⟩ := exists_jpow_relation x
  have hp0 : jeval x (∑ i : Fin n, monomial (i : ℕ) (c i)) = 0 := by
    rw [map_sum]
    simpa using hsum
  have hpne : (∑ i : Fin n, monomial (i : ℕ) (c i)) ≠ 0 := by
    intro h
    have hco : (∑ i : Fin n, monomial (i : ℕ) (c i)).coeff (i₀ : ℕ) = c i₀ := by
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb
        simp [Polynomial.coeff_monomial, Fin.val_ne_of_ne hb]
      · simp
    rw [h, Polynomial.coeff_zero] at hco
    exact hi₀ hco.symm
  refine ⟨Submodule.IsPrincipal.generator (jann x), ?_, fun f => ?_⟩
  · intro hgen
    have := (Submodule.IsPrincipal.mem_iff_generator_dvd (jann x)).mp (mem_jann.mpr hp0)
    rw [hgen, zero_dvd_iff] at this
    exact hpne this
  · exact (mem_jann (x := x) (p := f)).symm.trans
      (Submodule.IsPrincipal.mem_iff_generator_dvd (jann x))

private theorem jpow_jeval (x : J) (f : Polynomial ℝ) (n : ℕ) :
    jpow (jeval x f) n = jeval x (X ^ n * f ^ (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [jpow_succ, ih, jeval_mul]
      congr 1
      ring

variable [IsFormallyReal J]

private theorem isRadical_of_annihilator {x : J} {m : Polynomial ℝ}
    (hm : ∀ f, jeval x f = 0 ↔ m ∣ f) : IsRadical m := by
  intro n f hdvd
  match n with
  | 0 => exact (isUnit_of_dvd_one (by simpa using hdvd)).dvd
  | (k + 1) =>
      refine (hm f).mp ?_
      have h1 : jeval x (X ^ k * f ^ (k + 1)) = 0 :=
        jeval_X_pow_mul ((hm _).mpr hdvd) k
      rw [← jpow_jeval] at h1
      exact eq_zero_of_jpow_eq_zero k h1

private theorem coeff_zero_ne_zero_of_annihilator {x : J} {m : Polynomial ℝ}
    (hm : ∀ f, jeval x f = 0 ↔ m ∣ f) (hm0 : m ≠ 0) : m.coeff 0 ≠ 0 := by
  intro hc
  obtain ⟨m₁, hm₁⟩ := Polynomial.X_dvd_iff.mpr hc
  have hm₁0 : m₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm₁
    exact hm0 hm₁
  have hsq : jeval x m₁ * jeval x m₁ = 0 := by
    rw [jeval_mul, ← hm₁]
    exact (hm _).mpr ⟨m₁, rfl⟩
  have hdvd : m ∣ m₁ := (hm m₁).mp (eq_zero_of_mul_self_eq_zero hsq)
  have hle := Polynomial.natDegree_le_of_dvd hdvd hm₁0
  rw [hm₁, Polynomial.natDegree_mul Polynomial.X_ne_zero hm₁0, Polynomial.natDegree_X] at hle
  omega

end Annihilator

section Kill

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J] [IsFormallyReal J]

open Complex in

private theorem annihilator_aeval_ne_zero_of_im_ne_zero {x : J} {m : Polynomial ℝ}
    (hm : ∀ f, jeval x f = 0 ↔ m ∣ f) (hsq : Squarefree m) (h0 : m.coeff 0 ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0) : aeval z m ≠ 0 := by
  intro hroot
  obtain ⟨u, hu⟩ := m.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hroot hz
  set q : Polynomial ℝ := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) with hqdef
  have hqnu : ¬ IsUnit q := by
    intro h
    have h2 : q.natDegree = 2 := by rw [hqdef]; compute_degree!
    rw [Polynomial.natDegree_eq_zero_of_isUnit h] at h2
    exact absurd h2 (by norm_num)
  have hcop : IsCoprime q u := by
    rw [hu] at hsq
    exact (IsRelPrime.of_squarefree_mul hsq).isCoprime
  obtain ⟨α, β, hbez⟩ := hcop
  set c : ℝ := (β * u).coeff 0 / m.coeff 0 with hcdef
  set g : Polynomial ℝ := (β * u - C c * m).divX with hgdef
  have hXg : X * g = β * u - C c * m := by
    have hc0 : (β * u - C c * m).coeff 0 = 0 := by
      simp [hcdef, div_mul_cancel₀ _ h0]
    rw [hgdef]
    conv_rhs => rw [← Polynomial.X_mul_divX_add (β * u - C c * m)]
    rw [hc0, map_zero, add_zero]

  have h1 : m ∣ q * (X * g) := by
    rw [hXg]
    exact ⟨β - C c * q, by rw [hu]; ring⟩

  have hqsq : q = (X - C z.re) ^ 2 + C (z.im ^ 2) := by
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hqdef, hnorm]
    simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow, map_ofNat]
    ring

  set a : J := jeval x ((X - C z.re) * g) with hadef
  set b : J := z.im • jeval x g with hbdef
  have hsum : a * a + b * b = 0 := by
    have hb2 : b * b = jeval x (C (z.im ^ 2) * (X * g * g)) := by
      rw [hbdef, smul_mul_assoc, mul_smul_comm', smul_smul, jeval_mul, ← Polynomial.smul_eq_C_mul,
        map_smul]
      ring_nf
    rw [hadef, jeval_mul, hb2, ← map_add]
    refine (hm _).mpr (dvd_trans (h1.mul_right g) ?_)
    exact ⟨1, by rw [hqsq]; ring⟩
  have hb0 : b = 0 := by
    have := IsFormallyReal.eq_zero_of_sum_mul_self (Finset.univ : Finset (Fin 2)) ![a, b]
      (by simpa [Fin.sum_univ_two] using hsum)
    simpa using this 1 (Finset.mem_univ 1)
  have hg0 : jeval x g = 0 := by
    rcases smul_eq_zero.mp (hbdef ▸ hb0) with h | h
    · exact absurd h hz
    · exact h

  have hmg : m ∣ β * u := by
    have h4 : m ∣ β * u - C c * m := by
      rw [← hXg]; exact ((hm g).mp hg0).mul_left X
    simpa using dvd_add h4 (⟨C c, by ring⟩ : m ∣ C c * m)
  have hqm : q ∣ m := ⟨u, hu⟩
  exact hqnu (isUnit_of_dvd_one (hbez ▸ dvd_add (dvd_mul_left q α) (hqm.trans hmg)))

end Kill

section Split

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J] [IsFormallyReal J] [Module.Finite ℝ J]

private theorem exists_split_annihilator (x : J) :
    ∃ S : Finset ℝ, (0 : ℝ) ∉ S ∧ jeval x (∏ a ∈ S, (X - C a)) = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_annihilator_generator x
  have hsq : Squarefree m := (isRadical_of_annihilator hm).squarefree hm0
  have hc0 : m.coeff 0 ≠ 0 := coeff_zero_ne_zero_of_annihilator hm hm0
  refine ⟨m.roots.toFinset, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero] at hc0
    simpa [Polynomial.mem_roots', Polynomial.IsRoot.def] using fun _ => hc0
  · have hPm : (∏ a ∈ m.roots.toFinset, (X - C a)) ∣ m :=
      Finset.prod_dvd_of_coprime
        ((Polynomial.pairwise_coprime_X_sub_C (Function.injective_id (α := ℝ))).set_pairwise _)
        (fun a ha => Polynomial.dvd_iff_isRoot.mpr
          (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha)))
    obtain ⟨W, hW⟩ := hPm
    have hWnr : ∀ r : ℝ, W.eval r ≠ 0 := by
      intro r hr
      have hmr : m.IsRoot r := by rw [hW]; simp [Polynomial.IsRoot.def, hr]
      have hrS : r ∈ m.roots.toFinset :=
        Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hm0, hmr⟩)
      have hdd : (X - C r) * (X - C r) ∣ m := by
        rw [hW]
        exact mul_dvd_mul (Finset.dvd_prod_of_mem _ hrS) (Polynomial.dvd_iff_isRoot.mpr hr)
      have hu := hsq _ hdd
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_X_sub_C] at hu
      exact one_ne_zero hu
    have hWu : IsUnit W := by
      by_contra hWnu
      have hW0 : W ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hW
        exact hm0 hW
      have hdeg : W.degree ≠ 0 := fun h => hWnu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ W hdeg
      have him : z.im ≠ 0 := by
        intro h
        refine hWnr z.re ?_
        have hzr : z = algebraMap ℝ ℂ z.re := by
          apply Complex.ext <;> simp [h]
        rw [hzr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hz
        simpa using hz
      exact annihilator_aeval_ne_zero_of_im_ne_zero hm hsq hc0 him (by rw [hW, map_mul, hz, mul_zero])
    obtain ⟨v, hv⟩ := hWu.exists_right_inv
    refine (hm _).mpr ⟨v, ?_⟩
    calc (∏ a ∈ m.roots.toFinset, (X - C a))
        = (∏ a ∈ m.roots.toFinset, (X - C a)) * (W * v) := by rw [hv, mul_one]
      _ = m * v := by rw [← mul_assoc, ← hW]

omit [IsCommJordan J] [IsFormallyReal J] [Module.Finite ℝ J] in

private theorem jeval_eq_zero_of_eval_eq_zero {x : J} {S : Finset ℝ} (h0S : (0 : ℝ) ∉ S)
    (hA : jeval x (∏ a ∈ S, (X - C a)) = 0) {p f : Polynomial ℝ} (hpf : X * p = f)
    (hf : ∀ ν ∈ insert (0 : ℝ) S, f.eval ν = 0) : jeval x p = 0 := by
  have hnodal : (∏ ν ∈ insert (0 : ℝ) S, (X - C ν)) = X * ∏ a ∈ S, (X - C a) := by
    rw [Finset.prod_insert h0S, map_zero, sub_zero]
  have hdvd : (∏ ν ∈ insert (0 : ℝ) S, (X - C ν)) ∣ f :=
    Finset.prod_dvd_of_coprime
      ((Polynomial.pairwise_coprime_X_sub_C (Function.injective_id (α := ℝ))).set_pairwise _)
      (fun ν hν => Polynomial.dvd_iff_isRoot.mpr (hf ν hν))
  rw [hnodal] at hdvd
  obtain ⟨h, hh⟩ := hdvd
  have hp : p = (∏ a ∈ S, (X - C a)) * h := by
    apply mul_left_cancel₀ (Polynomial.X_ne_zero (R := ℝ))
    rw [hpf, hh, mul_assoc]
  rw [hp, mul_comm]
  exact jeval_mul_eq_zero hA h

private theorem exists_orthIdem_finset (x : J) :
    ∃ (S : Finset ℝ) (c : ℝ → J), (∀ a ∈ S, c a * c a = c a) ∧
      (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → c a * c a' = 0) ∧
      x = ∑ a ∈ S, a • c a := by
  classical
  obtain ⟨S, h0S, hA⟩ := exists_split_annihilator x
  set b : ℝ → Polynomial ℝ := fun a => Lagrange.basis (insert (0 : ℝ) S) id a with hbdef
  set g : ℝ → Polynomial ℝ := fun a => (b a).divX with hgdef
  have h0T : (0 : ℝ) ∈ insert (0 : ℝ) S := Finset.mem_insert_self 0 S
  have hne : ∀ a ∈ S, a ≠ 0 := fun a ha h => h0S (h ▸ ha)
  have hinj : Set.InjOn (id : ℝ → ℝ) (↑(insert (0 : ℝ) S) : Set ℝ) := fun _ _ _ _ h => h
  have heval : ∀ a ∈ S, ∀ ν ∈ insert (0 : ℝ) S, (b a).eval ν = if ν = a then 1 else 0 := by
    intro a ha ν hν
    by_cases h : ν = a
    · subst h
      simpa [hbdef] using Lagrange.eval_basis_self hinj (Finset.mem_insert_of_mem ha)
    · simpa [hbdef, h] using Lagrange.eval_basis_of_ne (v := (id : ℝ → ℝ)) (Ne.symm h) hν
  have hXg : ∀ a ∈ S, b a = X * g a := by
    intro a ha
    have h0 : (b a).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, heval a ha 0 h0T, if_neg (Ne.symm (hne a ha))]
    conv_lhs => rw [← Polynomial.X_mul_divX_add (b a)]
    rw [h0, map_zero, add_zero, hgdef]
  refine ⟨S, fun a => jeval x (g a), ?_, ?_, ?_⟩
  · intro a ha
    have key : jeval x (X * g a * g a - g a) = 0 := by
      refine jeval_eq_zero_of_eval_eq_zero h0S hA (f := b a ^ 2 - b a) ?_ ?_
      · rw [hXg a ha]; ring
      · intro ν hν
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, heval a ha ν hν]
        by_cases h : ν = a <;> simp [h]
    rw [map_sub, sub_eq_zero, ← jeval_mul] at key
    change jeval x (g a) * jeval x (g a) = jeval x (g a)
    exact key
  · intro a ha a' ha' haa'
    have key : jeval x (X * g a * g a') = 0 := by
      refine jeval_eq_zero_of_eval_eq_zero h0S hA (f := b a * b a') ?_ ?_
      · rw [hXg a ha, hXg a' ha']; ring
      · intro ν hν
        simp only [Polynomial.eval_mul, heval a ha ν hν, heval a' ha' ν hν]
        by_cases h : ν = a
        · rw [if_pos h, if_neg (by rw [h]; exact haa'), mul_zero]
        · rw [if_neg h, zero_mul]
    rw [← jeval_mul] at key
    change jeval x (g a) * jeval x (g a') = 0
    exact key
  · have key : jeval x (1 - ∑ a ∈ S, a • g a) = 0 := by
      refine jeval_eq_zero_of_eval_eq_zero h0S hA (f := X - ∑ a ∈ S, a • b a) ?_ ?_
      · rw [mul_sub, mul_one, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun a ha => by rw [mul_smul_comm, ← hXg a ha]
      · intro ν hν
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_finsetSum,
          Polynomial.eval_smul, smul_eq_mul]
        rcases Finset.mem_insert.mp hν with rfl | hνS
        · rw [Finset.sum_eq_zero fun a ha => by
            rw [heval a ha 0 hν, if_neg (Ne.symm (hne a ha)), mul_zero], sub_zero]
        · rw [Finset.sum_eq_single ν
            (fun a ha hane => by rw [heval a ha ν hν, if_neg (Ne.symm hane), mul_zero])
            (fun h => absurd hνS h),
            heval ν hνS ν hν, if_pos rfl, mul_one, sub_self]
    rw [map_sub, map_sum, jeval_one, sub_eq_zero] at key
    simpa using key

private theorem spectral_resolution (x : J) :
    ∃ (n : ℕ) (c : Fin n → J) (lam : Fin n → ℝ),
      IsOrthIdemFamily c ∧ x = ∑ i, lam i • c i := by
  classical
  obtain ⟨S, c, hidem, horth, hx⟩ := exists_orthIdem_finset x
  refine ⟨S.card, fun i => c (S.equivFin.symm i), fun i => ((S.equivFin.symm i : ℝ)),
    ⟨fun i => hidem _ (S.equivFin.symm i).2, fun i j hij => ?_⟩, ?_⟩
  · refine horth _ (S.equivFin.symm i).2 _ (S.equivFin.symm j).2 fun h => hij ?_
    exact S.equivFin.symm.injective (Subtype.ext h)
  · rw [hx, ← Finset.sum_coe_sort S (fun a => a • c a)]
    exact (Equiv.sum_comp S.equivFin.symm (fun a : {y // y ∈ S} => (a : ℝ) • c a)).symm

private theorem spectral_resolution_complete (e : J) (he : ∀ y : J, e * y = y) (x : J) :
    ∃ (n : ℕ) (c : Fin n → J) (lam : Fin n → ℝ),
      IsOrthIdemFamily c ∧ (∑ i, c i) = e ∧ x = ∑ i, lam i • c i := by
  obtain ⟨n, c, lam, hfam, hx⟩ := spectral_resolution x
  have hss : (∑ i, c i) * (∑ i, c i) = ∑ i, c i := hfam.sum_idem Finset.univ
  have hsc : ∀ k, (∑ i, c i) * c k = c k := by
    intro k
    rw [Finset.sum_mul, Finset.sum_eq_single k (fun j _ hjk => hfam.orth j k hjk)
      (fun h => absurd (Finset.mem_univ k) h)]
    exact hfam.idem k
  have hes : (∑ i, c i) * e = ∑ i, c i := by rw [mul_comm, he]
  have hlast : (e - ∑ i, c i) * (e - ∑ i, c i) = e - ∑ i, c i := by
    rw [sub_mul, mul_sub, mul_sub, he, he, hss, hes, sub_self, sub_zero]
  have horthlast : ∀ k, (e - ∑ i, c i) * c k = 0 := by
    intro k
    rw [sub_mul, he, hsc, sub_self]
  refine ⟨n + 1, Fin.snoc c (e - ∑ i, c i), Fin.snoc lam 0, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa using hlast
    | cast i => simpa using hfam.idem i
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa using horthlast j
    | cast i =>
        induction j using Fin.lastCases with
        | last => simpa [mul_comm] using horthlast i
        | cast j =>
            simpa using hfam.orth i j fun h => hij (by rw [h])
  · rw [Fin.sum_univ_castSucc]
    simp
  · rw [Fin.sum_univ_castSucc]
    simpa using hx

end Split

/-- Genuine EJA laws for the original product and the given positive definite inner product.
No JB norm, cone, frame, simplicity or representation is part of the data. -/
structure Data (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (u : X) : Prop where
  symm : ∀ x y, S x y = S y x
  unit_mul : ∀ x, S u x = x
  jordan : ∀ x y, S (S x y) (S x x) = S x (S y (S x x))
  inner_assoc : ∀ x y z, inner ℝ (S x y) z = inner ℝ y (S x z)

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}

/-- A complete finite spectral resolution on the same general real EJA carrier.
The zero algebra has an empty frame; zero eigenvalues and repeated eigenvalues are allowed.
The idempotents are not asserted primitive or nonzero. -/
theorem finite_spectral_resolution (A : Data X S u) (a : X) :
    ∃ (n : ℕ) (e : Fin n → X) (r : Fin n → ℝ),
      (∀ i, S (e i) (e i) = e i) ∧
      (∀ i j, i ≠ j → S (e i) (e j) = 0) ∧
      ∑ i, e i = u ∧ ∑ i, r i • e i = a ∧
      ∑ i, (r i ^ 2) • e i = S a a ∧ (u = 0 → n = 0) := by
  classical
  by_cases hu : u = 0
  · have allzero (x : X) : x = 0 := by
      rw [← A.unit_mul x, hu, S.map_zero, LinearMap.zero_apply]
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, fun _ => rfl⟩
    · intro i; exact Fin.elim0 i
    · simpa using hu.symm
    · simpa using (allzero a).symm
    · simpa using (allzero (S a a)).symm
  letI : NonUnitalNonAssocCommRing X :=
    { (inferInstance : AddCommGroup X) with
      mul := fun x y => S x y
      left_distrib := fun x y z => (S x).map_add y z
      right_distrib := fun x y z => congrArg (fun f : X →ₗ[ℝ] X => f z) (S.map_add x y)
      zero_mul := fun x => congrArg (fun f : X →ₗ[ℝ] X => f x) S.map_zero
      mul_zero := fun x => (S x).map_zero
      mul_comm := A.symm }
  letI : IsCommJordan X := ⟨A.jordan⟩
  letI : IsScalarTower ℝ X X := ⟨fun r x y => by
    change S (r • x) y = r • S x y
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]⟩
  have hinner (x y : X) : inner ℝ (x * y) u = inner ℝ x y := by
    change inner ℝ (S x y) u = _
    rw [A.inner_assoc, A.symm x u, A.unit_mul, real_inner_comm]
  letI : IsFormallyReal X := by
    refine ⟨fun {ι} s f hsum i hi => ?_⟩
    have hz : (∑ j ∈ s, inner ℝ (f j) (f j)) = 0 := by
      have h0 : inner ℝ (∑ j ∈ s, f j * f j) u = 0 := by rw [hsum, inner_zero_left]
      rw [sum_inner] at h0
      simpa only [hinner] using h0
    have hnn : ∀ j ∈ s, (0 : ℝ) ≤ inner ℝ (f j) (f j) := fun _ _ => real_inner_self_nonneg
    exact inner_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i hi)
  obtain ⟨n, e, r, hfam, hunit, hlin⟩ := spectral_resolution_complete u A.unit_mul a
  refine ⟨n, e, r, hfam.idem, hfam.orth, hunit, hlin.symm, ?_, fun h => (hu h).elim⟩
  change ∑ i, (r i ^ 2) • e i = a * a
  rw [hlin, Finset.sum_mul]
  symm
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · simp only [smul_mul_assoc, mul_smul_comm', hfam.idem, smul_smul, pow_two]
  · intro j _ hji
    simp only [smul_mul_assoc, mul_smul_comm', hfam.orth i j (Ne.symm hji), smul_zero]
  · simp

#print axioms finite_spectral_resolution

end D5.S3.Topology.EJAFiniteSpectral
