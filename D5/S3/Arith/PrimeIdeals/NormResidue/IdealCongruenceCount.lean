/- GID: D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCount
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Realized norm residues yield vanishing nontrivial character averages. -/
module

public import D5.S3.Arith.PrimeIdeals.NormResidue.IdealCongruenceCountDvdDensity

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

open Ideal in
/-- **The geometry-of-numbers density transfer (Lang, *Algebraic Number Theory* GTM 110, Ch. VI §3,
Thm 3; Gun–Ramaré–Sivaraman, JNT 243 (2023), Thm 1).** The per-class norm-residue *density* is
invariant under multiplying the class by `[𝔟]` and the residue by `N(𝔟)` (for `N(𝔟)` a unit mod
`c`): `lim #{[I]=C, N(I)≤M, N(I)≡x}/M = lim #{[I]=C·[𝔟], N(I)≤M, N(I)≡x·N(𝔟)}/M`. Proved by pinning
the common `𝔟`-divisible density two ways — geometrically (`cardNormLeResidueClassDvd_div_density`,
the covolume / CRT-equidistribution route) and via the Route-A bijection
(`cardNormLeResidueClassDvd_div_density_routeA`) — whose `N(𝔟)` factors cancel. -/
private theorem tendsto_cardNormLeResidueClass_div_transfer {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) (C : ClassGroup (𝓞 K)) {κ : ℝ}
    (hκ : Filter.Tendsto (fun M : ℕ ↦ (cardNormLeResidueClass c x C M : ℝ) / (M : ℝ))
      Filter.atTop (nhds κ)) :
    Filter.Tendsto (fun M : ℕ ↦ (cardNormLeResidueClass c
        (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) (C * ClassGroup.mk0 𝔟) M : ℝ) / (M : ℝ))
      Filter.atTop (nhds κ) := by
  have cardNormLeResidueClassDvd_div_density_routeA
      (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
      (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
      (y : ZMod c) (D : ClassGroup (𝓞 K)) {κCC : ℝ}
      (hκCC : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c
          (y * (↑hu.unit⁻¹ : ZMod c)) (D * (ClassGroup.mk0 𝔟)⁻¹) N : ℝ) / (N : ℝ))
        Filter.atTop (nhds κCC)) :
      Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
        Filter.atTop (nhds (κCC / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ))) := by
    classical
    have cardNormLeResidueClassDvd_eq_div (c : ℕ)
        [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰) (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
        {xC y : ZMod c} {CC D : ClassGroup (𝓞 K)}
        (hxmul : xC * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c) = y)
        (hCmul : CC * ClassGroup.mk0 𝔟 = D) (N : ℕ) :
        cardNormLeResidueClassDvd c 𝔟 y D N
          = cardNormLeResidueClass c xC CC (N / Ideal.absNorm (𝔟 : Ideal (𝓞 K))) := by
      have cardNormLeResidueClass_eq_dvd (c : ℕ)
          [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
          (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
          (x : ZMod c) (C : ClassGroup (𝓞 K)) (N : ℕ) :
          cardNormLeResidueClass c x C N =
            cardNormLeResidueClassDvd c 𝔟 (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c))
              (C * ClassGroup.mk0 𝔟) (N * Ideal.absNorm (𝔟 : Ideal (𝓞 K))) := by
        classical
        have hNb : 0 < Ideal.absNorm (𝔟 : Ideal (𝓞 K)) := absNorm_pos_of_nonZeroDivisors 𝔟
        rw [cardNormLeResidueClass, cardNormLeResidueClassDvd]
        simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
        refine Nat.card_congr
          (((Equiv.dvd 𝔟).subtypeEquiv (fun I ↦ ?_)).trans
            (Equiv.subtypeSubtypeEquivSubtypeInter (fun J : (Ideal (𝓞 K))⁰ ↦ 𝔟 ∣ J) _))
        have hnorm : absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
            = absNorm (𝔟 : Ideal (𝓞 K)) * absNorm (I : Ideal (𝓞 K)) := by
          simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, _root_.map_mul]
        have hcls : ClassGroup.mk0 ((Equiv.dvd 𝔟) I) = ClassGroup.mk0 I * ClassGroup.mk0 𝔟 := by
          rw [Equiv.dvd_apply, map_mul, mul_comm]
        have hle : (absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≤
            N * absNorm (𝔟 : Ideal (𝓞 K))) ↔ (absNorm (I : Ideal (𝓞 K)) ≤ N) := by
          rw [hnorm, mul_comm (absNorm (𝔟 : Ideal (𝓞 K))) (absNorm (I : Ideal (𝓞 K))),
            Nat.mul_le_mul_right_iff hNb]
        have hres : (((absNorm (I : Ideal (𝓞 K)) : ZMod c)) = x) ↔
            (((absNorm (((Equiv.dvd 𝔟) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ZMod c)) =
              x * (absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) := by
          rw [hnorm, Nat.cast_mul, mul_comm ((absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c))
            ((absNorm (I : Ideal (𝓞 K)) : ZMod c)), hu.mul_left_inj]
        have hcl : (ClassGroup.mk0 I = C) ↔
            (ClassGroup.mk0 ((Equiv.dvd 𝔟) I) = C * ClassGroup.mk0 𝔟) := by
          rw [hcls, mul_left_inj]
        rw [← hle, ← hres, ← hcl]
      have hfloor : cardNormLeResidueClassDvd c 𝔟 y D N =
          cardNormLeResidueClassDvd c 𝔟 y D
            (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) * (N / Ideal.absNorm (𝔟 : Ideal (𝓞 K)))) := by
        classical
        set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
        have hNB : 0 < NB := absNorm_pos_of_nonZeroDivisors 𝔟
        have hle {a m : ℕ} (hm : 0 < m) (hd : m ∣ a) (N : ℕ) :
            a ≤ N ↔ a ≤ m * (N / m) := by
          obtain ⟨k, rfl⟩ := hd
          refine ⟨fun h ↦ ?_, fun h ↦ le_trans h (Nat.mul_div_le N m)⟩
          exact Nat.mul_le_mul_left m ((Nat.le_div_iff_mul_le hm).mpr (by rwa [mul_comm] at h))
        rw [cardNormLeResidueClassDvd, cardNormLeResidueClassDvd]
        refine Nat.card_congr (Equiv.subtypeEquivRight fun J ↦ and_congr_right fun hb ↦
          and_congr_left fun _ ↦ and_congr_left fun _ ↦
            hle hNB (map_dvd Ideal.absNorm hb) N)
      rw [hfloor,
        cardNormLeResidueClass_eq_dvd c 𝔟 hu xC CC (N / Ideal.absNorm (𝔟 : Ideal (𝓞 K))),
        hxmul, hCmul, mul_comm]
    set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
    have hNB : 0 < NB := absNorm_pos_of_nonZeroDivisors 𝔟
    have hNB0 : (NB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNB.ne'
    set u : (ZMod c)ˣ := hu.unit with hudef
    have hu_spec : (↑u : ZMod c) = (NB : ZMod c) := hu.unit_spec
    set xC : ZMod c := y * (↑u⁻¹ : ZMod c) with hxC
    set CC : ClassGroup (𝓞 K) := D * (ClassGroup.mk0 𝔟)⁻¹ with hCC
    have hxmul : xC * (NB : ZMod c) = y := by
      rw [hxC, ← hu_spec, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    have hCmul : CC * ClassGroup.mk0 𝔟 = D := by rw [hCC, inv_mul_cancel_right]
    have hcount : ∀ N : ℕ, cardNormLeResidueClassDvd c 𝔟 y D N
        = cardNormLeResidueClass c xC CC (N / NB) :=
      fun N ↦ cardNormLeResidueClassDvd_eq_div c 𝔟 hu hxmul hCmul N
    refine Filter.Tendsto.congr (fun N ↦ by rw [hcount N]) ?_
    have hgN : Filter.Tendsto (fun N : ℕ ↦ (N / NB : ℕ)) Filter.atTop Filter.atTop :=
      Nat.tendsto_div_const_atTop hNB.ne'
    have hratio : Filter.Tendsto (fun N : ℕ ↦ ((N / NB : ℕ) : ℝ) / (N : ℝ))
        Filter.atTop (nhds (1 / (NB : ℝ))) := by
      have hsub : Filter.Tendsto (fun N : ℕ ↦ ((N % NB : ℕ) : ℝ) / (N : ℝ))
          Filter.atTop (nhds 0) := by
        refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ by positivity)
          (Filter.Eventually.of_forall fun N ↦ ?_)
          (tendsto_const_div_atTop_nhds_zero_nat (NB : ℝ))
        rcases Nat.eq_zero_or_pos N with hN0 | hNpos
        · simp [hN0]
        · have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
          rw [div_le_div_iff_of_pos_right hNposR]
          exact_mod_cast (Nat.mod_lt N hNB).le
      have hkey : ∀ N : ℕ, 1 ≤ N → ((N / NB : ℕ) : ℝ) / (N : ℝ)
          = (1 - ((N % NB : ℕ) : ℝ) / (N : ℝ)) / (NB : ℝ) := by
        intro N hN
        have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hdm : ((N / NB : ℕ) : ℝ) * (NB : ℝ) + ((N % NB : ℕ) : ℝ) = (N : ℝ) := by
          exact_mod_cast Nat.div_add_mod' N NB
        field_simp
        nlinarith [hdm]
      have hlim : Filter.Tendsto (fun N : ℕ ↦ (1 - ((N % NB : ℕ) : ℝ) / (N : ℝ)) / (NB : ℝ))
          Filter.atTop (nhds ((1 - 0) / (NB : ℝ))) :=
        (tendsto_const_nhds.sub hsub).div_const (NB : ℝ)
      refine (hlim.congr' ?_).mono_right (by rw [sub_zero])
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN using (hkey N hN).symm
    have hcomp : Filter.Tendsto
        (fun N : ℕ ↦ (cardNormLeResidueClass c xC CC (N / NB) : ℝ) / ((N / NB : ℕ) : ℝ))
        Filter.atTop (nhds κCC) := hκCC.comp hgN
    have hprod := hcomp.mul hratio
    rw [show κCC * (1 / (NB : ℝ)) = κCC / (NB : ℝ) by ring] at hprod
    refine hprod.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (NB + 1)] with N hN
    have hgpos : 0 < N / NB := Nat.div_pos (le_trans (by lia) hN) hNB
    have hgR : ((N / NB : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hgpos.ne'
    have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    field_simp
  have hrate : ∀ {f : ℕ → ℝ} {κ C' : ℝ} {d : ℕ},
      0 < d →
      (∀ N : ℕ, 1 ≤ N → |f N - κ * N| ≤ C' * (N : ℝ) ^ (1 - (d : ℝ)⁻¹)) →
      Filter.Tendsto (fun N : ℕ ↦ f N / (N : ℝ)) Filter.atTop (nhds κ) := by
    intro f κ C' d hd hbound
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
    have hzero : Filter.Tendsto (fun N : ℕ ↦ |C'| * (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        by
      have h1 : Filter.Tendsto (fun x : ℝ ↦ x ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        tendsto_rpow_neg_atTop hdpos
      have h2 : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        h1.comp tendsto_natCast_atTop_atTop
      simpa using h2.const_mul |C'|
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ norm_nonneg _) ?_ hzero
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
    rw [Real.norm_eq_abs, div_sub' hNne, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos,
      mul_comm (N : ℝ) κ]
    refine (hbound N hN).trans ?_
    have hsplit : (N : ℝ) ^ (1 - (d : ℝ)⁻¹) = (N : ℝ) ^ (-(d : ℝ)⁻¹) * (N : ℝ) := by
      rw [show (1 : ℝ) - (d : ℝ)⁻¹ = -(d : ℝ)⁻¹ + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
    rw [hsplit, ← mul_assoc]
    gcongr
    exact le_abs_self C'
  classical
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := absNorm_pos_of_nonZeroDivisors 𝔟
  have hNB0 : (NB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNB.ne'
  set y : ZMod c := x * (NB : ZMod c) with hy
  set D : ClassGroup (𝓞 K) := C * ClassGroup.mk0 𝔟 with hD
  obtain ⟨κ', _, hbound⟩ :=
    exists_card_norm_le_residue_class_eq_sub_mul_rpow_le (K := K) c y D
  have hκ' : Filter.Tendsto
      (fun N : ℕ ↦ (cardNormLeResidueClass c y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ') :=
    hrate Module.finrank_pos hbound
  suffices heq : κ' = κ by rwa [heq] at hκ'
  set u : (ZMod c)ˣ := hu.unit with hudef
  have hu_spec : (↑u : ZMod c) = (NB : ZMod c) := hu.unit_spec
  have hxC : y * (↑u⁻¹ : ZMod c) = x := by
    rw [hy, ← hu_spec, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hCC : D * (ClassGroup.mk0 𝔟)⁻¹ = C := by rw [hD, mul_inv_cancel_right]
  have hL2 : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ' / (NB : ℝ))) :=
    cardNormLeResidueClassDvd_div_density c 𝔟 hu y D hκ'
  have hL3 : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ / (NB : ℝ))) := by
    refine cardNormLeResidueClassDvd_div_density_routeA c 𝔟 hu y D (κCC := κ) ?_
    rwa [hxC, hCC]
  have hdiv : κ' / (NB : ℝ) = κ / (NB : ℝ) := tendsto_nhds_unique hL2 hL3
  exact (div_left_inj' hNB0).mp hdiv

open Ideal in
/-- **Global realizer transfer.** Summing the per-class transfer over the class group (reindexing
by `Equiv.mulRight [𝔟]`): for a realizer `𝔟` with `N(𝔟) (mod c)` a unit, `κ_x = κ_{x·N(𝔟)}`, the
densities of `cardNormLeResidue` at residues `x` and `x·N(𝔟)`. -/
private theorem cardNormLeResidue_density_transfer {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (x : ZMod c) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c x N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c
        (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  have hrate : ∀ {f : ℕ → ℝ} {κ C' : ℝ} {d : ℕ},
      0 < d →
      (∀ N : ℕ, 1 ≤ N → |f N - κ * N| ≤ C' * (N : ℝ) ^ (1 - (d : ℝ)⁻¹)) →
      Filter.Tendsto (fun N : ℕ ↦ f N / (N : ℝ)) Filter.atTop (nhds κ) := by
    intro f κ C' d hd hbound
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
    have hzero : Filter.Tendsto (fun N : ℕ ↦ |C'| * (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        by
      have h1 : Filter.Tendsto (fun x : ℝ ↦ x ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        tendsto_rpow_neg_atTop hdpos
      have h2 : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        h1.comp tendsto_natCast_atTop_atTop
      simpa using h2.const_mul |C'|
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ norm_nonneg _) ?_ hzero
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
    rw [Real.norm_eq_abs, div_sub' hNne, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos,
      mul_comm (N : ℝ) κ]
    refine (hbound N hN).trans ?_
    have hsplit : (N : ℝ) ^ (1 - (d : ℝ)⁻¹) = (N : ℝ) ^ (-(d : ℝ)⁻¹) * (N : ℝ) := by
      rw [show (1 : ℝ) - (d : ℝ)⁻¹ = -(d : ℝ)⁻¹ + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
    rw [hsplit, ← mul_assoc]
    gcongr
    exact le_abs_self C'
  classical
  have hsplitDensity (y₀ : ZMod c) (κ₀ : ℝ)
      (hκ₀ : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c y₀ N : ℝ) / (N : ℝ))
        Filter.atTop (nhds κ₀)) (κf₀ : ClassGroup (𝓞 K) → ℝ)
      (hκf₀ : ∀ C, Filter.Tendsto
        (fun N : ℕ ↦ (cardNormLeResidueClass c y₀ C N : ℝ) / (N : ℝ))
        Filter.atTop (nhds (κf₀ C))) :
      κ₀ = ∑ C : ClassGroup (𝓞 K), κf₀ C := by
    have hsplit (N : ℕ) :
        Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y₀}
        = ∑ C : ClassGroup (𝓞 K),
            Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
              ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y₀) ∧ ClassGroup.mk0 I = C} := by
      have hbase : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} :=
        Ideal.finite_setOf_absNorm_le₀ N
      have hfin : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y₀} :=
        Finite.of_injective (fun I ↦ (⟨I.1, I.2.1⟩ :
          {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}))
          (fun x y h ↦ Subtype.ext (by simpa using h))
      have hfinC : ∀ C : ClassGroup (𝓞 K), Finite {I : (Ideal (𝓞 K))⁰ //
          (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y₀) ∧ ClassGroup.mk0 I = C} := fun C ↦
        Finite.of_injective (fun I ↦ (⟨I.1, I.2.1.1⟩ :
          {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}))
          (fun x y h ↦ Subtype.ext (by simpa using h))
      have hF : Fintype {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y₀} := Fintype.ofFinite _
      have hFC : ∀ C, Fintype {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y₀) ∧ ClassGroup.mk0 I = C} :=
        fun C ↦ Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card,
        Finset.sum_congr rfl (fun C _ ↦ Nat.card_eq_fintype_card (α := {I : (Ideal (𝓞 K))⁰ //
          (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y₀) ∧ ClassGroup.mk0 I = C})),
        ← Fintype.card_sigma]
      refine Fintype.card_congr ((Equiv.sigmaFiberEquiv (fun I :
        {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y₀} ↦ ClassGroup.mk0 I.1)).symm.trans ?_)
      refine Equiv.sigmaCongrRight (fun C ↦ ?_)
      exact {
        toFun := fun I ↦ ⟨I.1.1, I.1.2, I.2⟩
        invFun := fun I ↦ ⟨⟨I.1, I.2.1⟩, I.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    refine tendsto_nhds_unique hκ₀ ?_
    have hsum := tendsto_finsetSum Finset.univ fun C (_ : C ∈ Finset.univ) ↦ hκf₀ C
    refine hsum.congr fun N ↦ ?_
    rw [cardNormLeResidue, hsplit N, Nat.cast_sum, Finset.sum_div]
    rfl
  have hclassLimits (y₀ : ZMod c) : ∀ C : ClassGroup (𝓞 K), ∃ κ : ℝ,
      Filter.Tendsto
        (fun N : ℕ ↦ (cardNormLeResidueClass c y₀ C N : ℝ) / (N : ℝ))
        Filter.atTop (nhds κ) := by
    intro C
    obtain ⟨κ, _, hκ⟩ := exists_card_norm_le_residue_class_eq_sub_mul_rpow_le (K := K) c y₀ C
    exact ⟨κ, hrate Module.finrank_pos hκ⟩
  choose κf hκf using hclassLimits x
  choose κf' hκf' using hclassLimits (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c))
  have hsplit : κ = ∑ C : ClassGroup (𝓞 K), κf C :=
    hsplitDensity x κ hκ κf hκf
  have hsplit' : κ' = ∑ C : ClassGroup (𝓞 K), κf' C :=
    hsplitDensity (x * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) κ' hκ' κf' hκf'
  have htrans : ∀ C : ClassGroup (𝓞 K), κf C = κf' (C * ClassGroup.mk0 𝔟) := fun C ↦
    tendsto_nhds_unique
      (tendsto_cardNormLeResidueClass_div_transfer c 𝔟 hu x C (hκf C))
      (hκf' (C * ClassGroup.mk0 𝔟))
  rw [hsplit, hsplit', Finset.sum_congr rfl fun C _ ↦ htrans C]
  exact Equiv.sum_comp (Equiv.mulRight (ClassGroup.mk0 𝔟)) κf'

open scoped Classical in
/-- **κ-constancy over the realized-residue subgroup (Lang VI §3 Thm 3; GRS Thm 1).** If `a, a'`
lie in a subgroup `S ≤ (ℤ/c)ˣ` *all of whose elements are realized as ideal-norm residues* (`hS`),
then the per-residue ideal densities of `a` and `a'` coincide: `κ = κ'`. Both densities transfer
from the residue-`1` density via `cardNormLeResidue_density_transfer` along the realizers of `a`
and `a'`. -/
private theorem cardNormLeResidue_density_const_of_realized
    {K : Type*} [Field K] [NumberField K] {c : ℕ} [NeZero c] {S : Subgroup (ZMod c)ˣ}
    (hS : ∀ a ∈ S, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c))
    {a a' : (ZMod c)ˣ} (ha : a ∈ S) (ha' : a' ∈ S) {κ κ' : ℝ}
    (hκ : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c (a : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ))
    (hκ' : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c (a' : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ')) :
    κ = κ' := by
  have hrate : ∀ {f : ℕ → ℝ} {κ C' : ℝ} {d : ℕ},
      0 < d →
      (∀ N : ℕ, 1 ≤ N → |f N - κ * N| ≤ C' * (N : ℝ) ^ (1 - (d : ℝ)⁻¹)) →
      Filter.Tendsto (fun N : ℕ ↦ f N / (N : ℝ)) Filter.atTop (nhds κ) := by
    intro f κ C' d hd hbound
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
    have hzero : Filter.Tendsto (fun N : ℕ ↦ |C'| * (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        by
      have h1 : Filter.Tendsto (fun x : ℝ ↦ x ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        tendsto_rpow_neg_atTop hdpos
      have h2 : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        h1.comp tendsto_natCast_atTop_atTop
      simpa using h2.const_mul |C'|
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ norm_nonneg _) ?_ hzero
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
    rw [Real.norm_eq_abs, div_sub' hNne, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos,
      mul_comm (N : ℝ) κ]
    refine (hbound N hN).trans ?_
    have hsplit : (N : ℝ) ^ (1 - (d : ℝ)⁻¹) = (N : ℝ) ^ (-(d : ℝ)⁻¹) * (N : ℝ) := by
      rw [show (1 : ℝ) - (d : ℝ)⁻¹ = -(d : ℝ)⁻¹ + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
    rw [hsplit, ← mul_assoc]
    gcongr
    exact le_abs_self C'
  classical
  obtain ⟨𝔟, h𝔟⟩ := hS a ha
  obtain ⟨𝔟', h𝔟'⟩ := hS a' ha'
  have hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) := h𝔟 ▸ a.isUnit
  have hu' : IsUnit ((Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c)) := h𝔟' ▸ a'.isUnit
  obtain ⟨κ₁, _, hbound⟩ :=
    exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K c (1 : ZMod c)
  have hκ₁ : Filter.Tendsto
      (fun N : ℕ ↦ (cardNormLeResidue K c (1 : ZMod c) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ₁) :=
    hrate Module.finrank_pos hbound
  have hone_eq : (1 : ZMod c) * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c) = (a : ZMod c) := by
    rw [one_mul, h𝔟]
  have hone_eq' : (1 : ZMod c) * (Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c) = (a' : ZMod c) := by
    rw [one_mul, h𝔟']
  have hκ_a : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c
      ((1 : ZMod c) * (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ) := by rwa [hone_eq]
  have hκ_a' : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c
      ((1 : ZMod c) * (Ideal.absNorm (𝔟' : Ideal (𝓞 K)) : ZMod c)) N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κ') := by rwa [hone_eq']
  have h1 : κ₁ = κ := cardNormLeResidue_density_transfer c 𝔟 hu (1 : ZMod c) hκ₁ hκ_a
  have h2 : κ₁ = κ' := cardNormLeResidue_density_transfer c 𝔟' hu' (1 : ZMod c) hκ₁ hκ_a'
  rw [← h1, h2]

open scoped Classical in
/-- **Fourier decay from realized residues (the `hF` producer).** Let `S ≤ (ℤ/c)ˣ` be a subgroup
all of whose elements are realized as ideal-norm residues (`hS`). Then for every **nontrivial**
character `χ` of `S`, the `χ`-twisted norm-residue count average over `S` tends to `0`:

`(∑_{s ∈ S} χ(s)·#{N(I) ≤ N, N(I) ≡ s}) / N → 0`.

This is exactly the Fourier-decay hypothesis `hF` consumed by
`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform` (and by
`cardNormLeResidue_density_eq_of_mem_subgroup`): when the consumer's `S` is the full image
subgroup of ideal-norm residues, `hS` holds tautologically, so this theorem discharges its `hF`
and hands back the `κ`-uniform effective ideal count. (The avoidance of the `ℚ(i)`-trap is built
in: realization, hence decay, is asserted only over the **image subgroup** `S`, never over all of
`(ℤ/c)ˣ`.) -/
theorem tendsto_sum_char_mul_cardNormLeResidue_div_of_realized
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (S : Subgroup (ZMod c)ˣ)
    (hS : ∀ a ∈ S, ∃ 𝔟 : (Ideal (𝓞 K))⁰,
      ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c))
    (χ : S →* ℂˣ) (hχ : χ ≠ 1) :
    Filter.Tendsto (fun N : ℕ ↦ (∑ s : S, ((χ s : ℂˣ) : ℂ) *
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
        / (N : ℂ))
      Filter.atTop (nhds 0) := by
  have hrate : ∀ {f : ℕ → ℝ} {κ C' : ℝ} {d : ℕ},
      0 < d →
      (∀ N : ℕ, 1 ≤ N → |f N - κ * N| ≤ C' * (N : ℝ) ^ (1 - (d : ℝ)⁻¹)) →
      Filter.Tendsto (fun N : ℕ ↦ f N / (N : ℝ)) Filter.atTop (nhds κ) := by
    intro f κ C' d hd hbound
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
    have hzero : Filter.Tendsto (fun N : ℕ ↦ |C'| * (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        by
      have h1 : Filter.Tendsto (fun x : ℝ ↦ x ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        tendsto_rpow_neg_atTop hdpos
      have h2 : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-(d : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
        h1.comp tendsto_natCast_atTop_atTop
      simpa using h2.const_mul |C'|
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ norm_nonneg _) ?_ hzero
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
    rw [Real.norm_eq_abs, div_sub' hNne, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos,
      mul_comm (N : ℝ) κ]
    refine (hbound N hN).trans ?_
    have hsplit : (N : ℝ) ^ (1 - (d : ℝ)⁻¹) = (N : ℝ) ^ (-(d : ℝ)⁻¹) * (N : ℝ) := by
      rw [show (1 : ℝ) - (d : ℝ)⁻¹ = -(d : ℝ)⁻¹ + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
    rw [hsplit, ← mul_assoc]
    gcongr
    exact le_abs_self C'
  classical
  have hlimits : ∀ s : S, ∃ κ : ℝ,
      Filter.Tendsto
        (fun N : ℕ ↦ (cardNormLeResidue K c ((s : (ZMod c)ˣ) : ZMod c) N : ℝ) / (N : ℝ))
        Filter.atTop (nhds κ) := by
    intro s
    obtain ⟨κ, _, hκ⟩ :=
      exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K c ((s : (ZMod c)ˣ) : ZMod c)
    exact ⟨κ, hrate Module.finrank_pos hκ⟩
  choose κf hκf using hlimits
  have hconst : ∀ s : S, κf s = κf 1 := fun s ↦
    cardNormLeResidue_density_const_of_realized hS s.2 (one_mem S) (hκf s) (hκf 1)
  have hlim : Filter.Tendsto (fun N : ℕ ↦ (∑ s : S, ((χ s : ℂˣ) : ℂ) *
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
        / (N : ℂ))
      Filter.atTop (nhds (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ))) := by
    have hsum := tendsto_finsetSum Finset.univ fun s (_ : s ∈ Finset.univ) ↦
      ((Complex.continuous_ofReal.tendsto (κf s)).comp (hκf s)).const_mul ((χ s : ℂˣ) : ℂ)
    refine hsum.congr fun N ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [Function.comp_apply, cardNormLeResidue]
    push_cast
    ring
  have hval : (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ)) = 0 := by
    have hrw : (∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ))
        = (∑ s : S, ((χ s : ℂˣ) : ℂ)) * (κf 1 : ℂ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [hconst s]
    have hzero : (∑ s : S, ((χ s : ℂˣ) : ℂ)) = 0 := by
      letI : AddGroup (Additive S) := inferInstance
      letI : CommSemiring ℂ := inferInstance
      let ψ : AddChar (Additive S) ℂ :=
        AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp χ)
      have hψ : ψ ≠ 0 := by
        intro htriv
        apply hχ
        ext s
        have hs := congrArg (fun φ : AddChar (Additive S) ℂ => φ (Additive.ofMul s)) htriv
        change ((χ s : ℂˣ) : ℂ) = (1 : ℂ) at hs
        simpa only [MonoidHom.one_apply, Units.val_one] using hs
      have hsum : (∑ s : Additive S, ψ s) = 0 := by
        rw [AddChar.sum_eq_ite ψ, if_neg hψ]
      have htransport :
          (∑ s : S, ((χ s : ℂˣ) : ℂ)) = ∑ s : Additive S, ψ s :=
        Fintype.sum_equiv Additive.ofMul _ _ (fun s => rfl)
      exact htransport.trans hsum
    rw [hrw, hzero, zero_mul]
  rwa [hval] at hlim

end Chebotarev
