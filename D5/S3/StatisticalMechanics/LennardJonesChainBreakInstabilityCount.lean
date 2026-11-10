/- GID: D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The unstable-eigenvalue count of a clamped Lennard-Jones chain is k-1 or k. -/

import D5.S3.Combinatorics.Hypermatrix.PencilParameterFibers
import D5.S3.Weil.ZetaLinear.Sylvester

/-!
# Instability count for the clamped Lennard-Jones chain

Source: Rodrigues–Kevrekidis–Dobson, arXiv:1802.03477v2, abstract and equations (1)–(2).
The bond-difference factorization and the codimension-one range give the two inertia bounds.
The steady-state and endpoint hypotheses are retained from the source statement.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

def ljPotential (r : ℝ) : ℝ := r ^ (-12 : ℤ) - 2 * r ^ (-6 : ℤ)

def inflectionPoint : ℝ := (13 / 7 : ℝ) ^ ((1 : ℝ) / 6)

def bondLength {m : ℕ} (d : ℝ) (u : Fin (m + 2) → ℝ) (j : Fin (m + 1)) : ℝ :=
  d + u j.succ - u j.castSucc

def force {m : ℕ} (d : ℝ) (u : Fin (m + 2) → ℝ) (n : Fin m) : ℝ :=
  deriv ljPotential (bondLength d u n.succ) - deriv ljPotential (bondLength d u n.castSucc)

def jacobian {m : ℕ} (d : ℝ) (u : Fin (m + 2) → ℝ) : Matrix (Fin m) (Fin m) ℝ := fun n q =>
  let c : Fin (m + 1) → ℝ := fun j => deriv (deriv ljPotential) (bondLength d u j)
  if n = q then -c n.castSucc - c n.succ
  else if (n : ℕ) + 1 = (q : ℕ) then c n.succ
  else if (q : ℕ) + 1 = (n : ℕ) then c q.succ
  else 0

def claim : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (d : ℝ), 0 < d →
    ∀ (u : Fin (m + 2) → ℝ), u 0 = 0 → u (Fin.last _) = 0 →
      (∀ n, force d u n = 0) → (∀ j, 0 < bondLength d u j) →
        ∀ k : ℕ, 1 ≤ k →
          (Finset.univ.filter (fun j => inflectionPoint < bondLength d u j)).card = k →
            ∀ h : (jacobian d u).IsHermitian,
              k - 1 ≤ (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card ∧
                (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card ≤ k

private lemma curvature_formula (r : ℝ) (hr : 0 < r) :
    deriv (deriv ljPotential) r = 12 * (13 - 7 * r ^ (6 : ℕ)) / r ^ (14 : ℕ) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hfirst : ∀ x : ℝ, 0 < x →
      deriv ljPotential x = -12 * x ^ (-13 : ℤ) + 12 * x ^ (-7 : ℤ) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    change deriv ((fun y : ℝ => y ^ (-12 : ℤ)) -
      (fun y : ℝ => 2 * y ^ (-6 : ℤ))) x = _
    rw [deriv_sub]
    · rw [deriv_zpow]
      rw [deriv_const_mul (2 : ℝ)]
      · rw [deriv_zpow]
        ring_nf
      · exact DifferentiableAt.zpow differentiableAt_id (Or.inl hx0)
    · exact DifferentiableAt.zpow differentiableAt_id (Or.inl hx0)
    · exact (DifferentiableAt.zpow differentiableAt_id (Or.inl hx0)).const_mul 2
  have hev : (fun x : ℝ => deriv ljPotential x) =ᶠ[nhds r]
      (fun x : ℝ => -12 * x ^ (-13 : ℤ) + 12 * x ^ (-7 : ℤ)) := by
    filter_upwards [eventually_gt_nhds hr] with x hx
    exact hfirst x hx
  rw [hev.deriv_eq]
  change deriv ((fun x : ℝ => -12 * x ^ (-13 : ℤ)) +
      (fun x : ℝ => 12 * x ^ (-7 : ℤ))) r = _
  rw [deriv_add]
  · rw [deriv_const_mul (-12 : ℝ), deriv_const_mul (12 : ℝ)]
    · rw [deriv_zpow, deriv_zpow]
      ring_nf
      rw [_root_.zpow_neg, _root_.zpow_neg]
      field_simp
      ring
    · exact DifferentiableAt.zpow differentiableAt_id (Or.inl hr0)
    · exact DifferentiableAt.zpow differentiableAt_id (Or.inl hr0)
  · exact (DifferentiableAt.zpow differentiableAt_id (Or.inl hr0)).const_mul (-12)
  · exact (DifferentiableAt.zpow differentiableAt_id (Or.inl hr0)).const_mul 12

private lemma inflection_iff (r : ℝ) (hr : 0 < r) :
    inflectionPoint < r ↔ 13 < 7 * r ^ (6 : ℕ) := by
  change (13 / 7 : ℝ) ^ ((1 : ℝ) / 6) < r ↔ _
  simpa only [one_div, Real.rpow_ofNat,
    div_lt_iff₀ (by norm_num : (0 : ℝ) < 7), mul_comm] using
    (Real.rpow_inv_lt_iff_of_pos (by norm_num : (0 : ℝ) ≤ 13 / 7) hr.le
      (by norm_num : (0 : ℝ) < 6))

private lemma curvature_sign (r : ℝ) (hr : 0 < r) :
    deriv (deriv ljPotential) r < 0 ↔ inflectionPoint < r := by
  rw [curvature_formula r hr, div_neg_iff]
  have hden : 0 < r ^ (14 : ℕ) := pow_pos hr _
  rw [inflection_iff r hr]
  constructor
  · intro h
    rcases h with h | h
    · exfalso
      linarith
    · nlinarith [h.1]
  · intro h
    right
    constructor
    · nlinarith [h]
    · exact hden

private lemma jacobian_factorization {m : ℕ} (d : ℝ) (u : Fin (m + 2) → ℝ) :
    ∃ (b : Matrix (Fin (m + 1)) (Fin m) ℝ)
      (c : Fin (m + 1) → ℝ),
      (∀ j n, b j n = (if n.castSucc = j then 1 else 0) -
        (if n.succ = j then 1 else 0)) ∧
      (∀ j, c j = deriv (deriv ljPotential) (bondLength d u j)) ∧
      jacobian d u = -(b.transpose * Matrix.diagonal c * b) := by
  classical
  let b : Matrix (Fin (m + 1)) (Fin m) ℝ := fun j n =>
    (if n.castSucc = j then 1 else 0) - (if n.succ = j then 1 else 0)
  let c : Fin (m + 1) → ℝ := fun j => deriv (deriv ljPotential) (bondLength d u j)
  refine ⟨b, c, fun _ _ => rfl, fun _ => rfl, ?_⟩
  have he (n q : Fin m) : (b.transpose * Matrix.diagonal c * b) n q =
      c n.castSucc * b n.castSucc q - c n.succ * b n.succ q := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    have hb (j : Fin (m + 1)) : b j n =
        (if n.castSucc = j then 1 else 0) - (if n.succ = j then 1 else 0) := rfl
    simp_rw [hb, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ext n q
  change (if n = q then -c n.castSucc - c n.succ
    else if n.val + 1 = q.val then c n.succ
    else if q.val + 1 = n.val then c q.succ else 0) =
      -((b.transpose * Matrix.diagonal c * b) n q)
  rw [he]
  change _ = -(c n.castSucc *
      ((if q.castSucc = n.castSucc then 1 else 0) - (if q.succ = n.castSucc then 1 else 0)) -
    c n.succ * ((if q.castSucc = n.succ then 1 else 0) -
      (if q.succ = n.succ then 1 else 0)))
  by_cases hnq : n = q
  · subst q
    have hne : n.succ ≠ n.castSucc := Fin.castSucc_lt_succ.ne.symm
    simp only [ite_true, ite_eq_right hne, ite_eq_right hne.symm]
    ring
  · have hqn : q ≠ n := Ne.symm hnq
    have hcross : q.castSucc = n.succ ↔ n.val + 1 = q.val := by
      constructor <;> intro heq
      · have := congrArg Fin.val heq; simpa using this.symm
      · apply Fin.ext; exact heq.symm
    have hcross2 : q.succ = n.castSucc ↔ q.val + 1 = n.val := by
      constructor <;> intro heq
      · exact congrArg Fin.val heq
      · exact Fin.ext heq
    simp only [ite_eq_right hnq, Fin.castSucc_inj, Fin.succ_inj, ite_eq_right hqn, hcross, hcross2]
    split_ifs with hright hleft hleft
    · omega
    · ring
    · have heq : q.succ = n.castSucc := hcross2.mpr hleft
      rw [heq]
      ring
    · ring

open D5.S3.Combinatorics.Hypermatrix in
private lemma bond_difference_injective {m : ℕ}
    (b : Matrix (Fin (m + 1)) (Fin m) ℝ)
    (hb : ∀ j n, b j n = (if n.castSucc = j then 1 else 0) -
      (if n.succ = j then 1 else 0)) :
    Function.Injective (b.mulVec) := by
  classical
  by_cases hm : m = 0
  · subst m
    exact fun _ _ _ => Subsingleton.elim _ _
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  let f := algebraMap ℝ (AlgebraicClosure ℝ)
  have hr := (PencilParameterFibers.pencil_parameter_fibers ℝ m hmpos).2.1
    ((1, 1) : MaskedFacesDefs.Factors ℝ m) 1 (-1) (Or.inl one_ne_zero)
  have he : (1 : AlgebraicClosure ℝ) •
      (MaskedFacesDefs.factorMap ((1, 1) : MaskedFacesDefs.Factors ℝ m)).1.map f +
      (-1 : AlgebraicClosure ℝ) •
      (MaskedFacesDefs.factorMap ((1, 1) : MaskedFacesDefs.Factors ℝ m)).2.map f = b.map f := by
    change (1 : AlgebraicClosure ℝ) •
        ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * MaskedFacesDefs.E0 ℝ m *
          (1 : Matrix (Fin m) (Fin m) ℝ)).map f +
        (-1 : AlgebraicClosure ℝ) •
        ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) * MaskedFacesDefs.E1 ℝ m *
          (1 : Matrix (Fin m) (Fin m) ℝ)).map f = _
    simp only [Matrix.one_mul, Matrix.mul_one]
    ext j n
    simp [MaskedFacesDefs.E0, MaskedFacesDefs.E1,
      Matrix.map_apply, hb, eq_comm, sub_eq_add_neg]
  rw [he] at hr
  have hi : Function.Injective (b.map f).mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hd := LinearMap.finrank_range_add_finrank_ker (b.map f).mulVecLin
    change (b.map f).rank + Module.finrank (AlgebraicClosure ℝ)
      (b.map f).mulVecLin.ker = Module.finrank (AlgebraicClosure ℝ)
      (Fin m → AlgebraicClosure ℝ) at hd
    simp only [hr, Module.finrank_pi, Fintype.card_fin] at hd
    omega
  intro x y hxy
  have hmap : f ∘ x = f ∘ y := by
    apply hi
    ext j
    simpa only [Matrix.mulVecLin_apply, ← RingHom.map_mulVec] using
      congrArg f (congrFun hxy j)
  ext n
  exact f.injective (congrFun hmap n)

private lemma bond_difference_range {m : ℕ}
    (b : Matrix (Fin (m + 1)) (Fin m) ℝ)
    (hb : ∀ j n, b j n = (if n.castSucc = j then 1 else 0) -
      (if n.succ = j then 1 else 0)) :
    Module.finrank ℝ (LinearMap.range b.mulVecLin) = m := by
  have hi : Function.Injective b.mulVecLin := bond_difference_injective b hb
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using
    LinearMap.finrank_range_of_inj hi

private lemma factorization_form {m : ℕ}
    (a : Matrix (Fin m) (Fin m) ℝ)
    (b : Matrix (Fin (m + 1)) (Fin m) ℝ) (c : Fin (m + 1) → ℝ)
    (ha : a = -(b.transpose * Matrix.diagonal c * b)) (x : Fin m → ℝ) :
    RHLinalg.hermForm a x = -∑ j, c j * (b *ᵥ x) j ^ 2 := by
  rw [ha]
  have hpull := RHLinalg.hermForm_conj (Matrix.diagonal c) b x
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hpull
  have hzero : RHLinalg.hermForm (0 : Matrix (Fin m) (Fin m) ℝ) x = 0 := by
    change RCLike.re (star x ⬝ᵥ ((0 : Matrix (Fin m) (Fin m) ℝ) *ᵥ x)) = 0
    simp only [Matrix.zero_mulVec, dotProduct_zero, map_zero]
  have hneg : RHLinalg.hermForm (-(b.transpose * Matrix.diagonal c * b)) x =
      -RHLinalg.hermForm (b.transpose * Matrix.diagonal c * b) x := by
    simpa only [zero_sub, hzero]
      using RHLinalg.hermForm_sub 0 (b.transpose * Matrix.diagonal c * b) x
  rw [hneg, hpull]
  congr 1
  change (∑ j, (b *ᵥ x) j * ((Matrix.diagonal c) *ᵥ (b *ᵥ x)) j) = _
  simp only [Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma inertia_lower_bound {m : ℕ} (hm : 1 ≤ m) (d : ℝ)
    (u : Fin (m + 2) → ℝ) (hd : 0 < d)
    (hpos : ∀ j, 0 < bondLength d u j)
    (k : ℕ) (hk : 1 ≤ k)
    (hbroken : (Finset.univ.filter (fun j => inflectionPoint < bondLength d u j)).card = k)
    (h : (jacobian d u).IsHermitian) :
    k - 1 ≤ Finset.card (Finset.univ.filter (fun i => 0 < h.eigenvalues i)) := by
  classical
  obtain ⟨b, c, hb, hc, hfac⟩ := jacobian_factorization d u
  let e := Pi.spanSubset ℝ {j | inflectionPoint < bondLength d u j}
  let v := e.comap b.mulVecLin
  have hi : Function.Injective b.mulVecLin := bond_difference_injective b hb
  have he : Module.finrank ℝ e = k := by
    change Module.finrank ℝ (Pi.spanSubset ℝ _) = k
    rw [Pi.dim_spanSubset, Set.ncard_eq_toFinset_card']
    simpa only [Set.toFinset_ofPred] using hbroken
  have hv : Module.finrank ℝ v =
      Module.finrank ℝ ((LinearMap.range b.mulVecLin ⊓ e :
        Submodule ℝ (Fin (m + 1) → ℝ))) := by
    rw [← Submodule.map_comap_eq]
    exact (Submodule.equivMapOfInjective b.mulVecLin hi v).finrank_eq
  have hdim : k - 1 ≤ Module.finrank ℝ v := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range b.mulVecLin) e
    have hsup := (LinearMap.range b.mulVecLin ⊔ e).finrank_le
    rw [bond_difference_range b hb, he, ← hv] at hsum
    have hamb : Module.finrank ℝ (Fin (m + 1) → ℝ) = m + 1 := by simp
    rw [hamb] at hsup
    omega
  have hpositive : RHLinalg.PosDefOn (jacobian d u) v := by
    intro x hx hne
    rw [factorization_form _ b c hfac]
    apply neg_pos.mpr
    have hs : ∀ j, ¬inflectionPoint < bondLength d u j → (b *ᵥ x) j = 0 :=
      Pi.mem_spanSubset_iff.mp hx
    apply Finset.sum_neg'
    · intro j _
      by_cases hj : inflectionPoint < bondLength d u j
      · have hneg : c j < 0 := by rw [hc]; exact (curvature_sign _ (hpos j)).mpr hj
        exact mul_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg _)
      · rw [hs j hj]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, le_refl]
    · have hbx : b *ᵥ x ≠ 0 := by
        intro hz
        exact hne (hi (hz.trans (Matrix.mulVec_zero b).symm))
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hbx
      have hbj : inflectionPoint < bondLength d u j := by
        by_contra hn
        exact hj (hs j hn)
      refine ⟨j, Finset.mem_univ j, ?_⟩
      have hneg : c j < 0 := by rw [hc]; exact (curvature_sign _ (hpos j)).mpr hbj
      exact mul_neg_of_neg_of_pos hneg (sq_pos_of_ne_zero hj)
  exact hdim.trans (RHLinalg.finrank_le_posIndex_of_posDefOn h hpositive)

private lemma inertia_upper_bound {m : ℕ} (hm : 1 ≤ m) (d : ℝ)
    (u : Fin (m + 2) → ℝ) (hd : 0 < d)
    (hpos : ∀ j, 0 < bondLength d u j)
    (k : ℕ) (hk : 1 ≤ k)
    (hbroken : (Finset.univ.filter (fun j => inflectionPoint < bondLength d u j)).card = k)
    (h : (jacobian d u).IsHermitian) :
    Finset.card (Finset.univ.filter (fun i => 0 < h.eigenvalues i)) ≤ k := by
  classical
  obtain ⟨b, c, hb, hc, hfac⟩ := jacobian_factorization d u
  obtain ⟨w, hw, hdim⟩ := RHLinalg.posIndex_eq_max_finrank_posDefOn h
  let l : w →ₗ[ℝ] ({j // inflectionPoint < bondLength d u j} → ℝ) :=
    LinearMap.pi fun j => (LinearMap.proj j.val).comp (b.mulVecLin.comp w.subtype)
  have hi : Function.Injective l := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    apply Subtype.ext
    change (x : Fin m → ℝ) = 0
    by_contra hne
    have hp := hw x x.property hne
    have hn : RHLinalg.hermForm (jacobian d u) x ≤ 0 := by
      rw [factorization_form _ b c hfac]
      apply neg_nonpos.mpr
      apply Finset.sum_nonneg
      intro j _
      by_cases hj : inflectionPoint < bondLength d u j
      · have hz : (b *ᵥ (x : Fin m → ℝ)) j = 0 := congrFun hx ⟨j, hj⟩
        rw [hz]
        simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
      · have hnn : 0 ≤ c j := by
          rw [hc]
          exact not_lt.mp (fun hn => hj ((curvature_sign _ (hpos j)).mp hn))
        exact mul_nonneg hnn (sq_nonneg _)
    exact (not_lt.mpr hn) hp
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  have hcod : Module.finrank ℝ ({j // inflectionPoint < bondLength d u j} → ℝ) = k := by
    simpa only [Module.finrank_pi, Module.finrank_self, mul_one,
      Fintype.card_subtype] using hbroken
  rw [hdim, hcod] at hd
  exact hd

theorem result : claim := by
  intro m hm d hd u hu0 huLast hsteady hpos k hk hbroken h
  exact ⟨inertia_lower_bound hm d u hd hpos k hk hbroken h,
    inertia_upper_bound hm d u hd hpos k hk hbroken h⟩

end D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount
