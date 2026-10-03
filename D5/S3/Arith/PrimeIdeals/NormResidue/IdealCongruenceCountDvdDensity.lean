/- GID: D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdDensity
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountDvdDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Given full class-residue density, the b-divisible density is divided by the norm of b. -/
module

public import D5.S3.Arith.PrimeIdeals.NormResidue.IdealCongruenceCountConeDvd

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

open Ideal NumberField NumberField.Units NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone in
/-- **The dvd-density is the full density divided by `N(𝔟)` (Lang VI §3 Thm 3; GRS Thm 1).**
For a realizer `𝔟` with `N(𝔟) (mod c)` a unit, the `𝔟`-divisible class-`D` norm-residue count has
density `κfull/N(𝔟)`, where `κfull` is the full class-`D` residue-`y` density. Proved the geometric
(covolume / CRT-equidistribution) way: principalize both counts at a coprime representative `J` of
`D⁻¹` and read off the index-`N(𝔟)` sublattice scaling from the shared cone estimate
`exists_card_idealSet_residue_real_le_dvd`. -/
theorem cardNormLeResidueClassDvd_div_density {K : Type*} [Field K] [NumberField K]
    (c : ℕ) [NeZero c] (𝔟 : (Ideal (𝓞 K))⁰)
    (hu : IsUnit ((Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ZMod c)))
    (y : ZMod c) (D : ClassGroup (𝓞 K)) {κfull : ℝ}
    (hκfull : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds κfull)) :
    Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κfull / (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℝ))) := by
  classical
  have principalize (modulus : ℕ) [NeZero modulus] (residue : ZMod modulus)
      (N : ℕ) (klass : ClassGroup (𝓞 K)) (J I : (Ideal (𝓞 K))⁰)
      (hJ : ClassGroup.mk0 J = klass⁻¹) (hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K))) :
      ((Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus)) = residue) ∧
          ClassGroup.mk0 I = klass) ↔
        (IsPrincipal (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∧
          Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≤
            N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
          ((Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :
              ZMod (modulus * Ideal.absNorm (J : Ideal (𝓞 K)))) =
            ((residue.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
              ZMod (modulus * Ideal.absNorm (J : Ideal (𝓞 K)))))) := by
    have hnorm : absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        = absNorm (I : Ideal (𝓞 K)) * absNorm (J : Ideal (𝓞 K)) := by
      simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, _root_.map_mul]; ring
    have hprin : IsPrincipal (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ↔
        ClassGroup.mk0 I = klass := by
      have hmem : (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ :=
        SetLike.coe_mem _
      rw [← ClassGroup.mk0_eq_one_iff hmem]
      have hmk : ClassGroup.mk0 (⟨(((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)), hmem⟩ :
          (Ideal (𝓞 K))⁰) = ClassGroup.mk0 ((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) := by congr 1
      rw [hmk, Equiv.dvd_apply, map_mul, hJ, inv_mul_eq_one, eq_comm]
    rw [hprin, hnorm]
    have hres : (((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus)) = residue) ↔
        (((Ideal.absNorm (I : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (modulus * Ideal.absNorm (J : Ideal (𝓞 K)))) =
          ((residue.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (modulus * Ideal.absNorm (J : Ideal (𝓞 K))))) := by
      rw [show ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus)) = residue ↔
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus)) =
            ((residue.val : ℕ) : ZMod modulus) by
        rw [ZMod.natCast_val, ZMod.cast_id]]
      rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff,
        Nat.ModEq, Nat.ModEq, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right]
      exact ⟨fun h ↦ by rw [h], fun h ↦ Nat.eq_of_mul_eq_mul_right hNJ h⟩
    have hnle : (absNorm (I : Ideal (𝓞 K)) * absNorm (J : Ideal (𝓞 K)) ≤
        N * absNorm (J : Ideal (𝓞 K))) ↔ (absNorm (I : Ideal (𝓞 K)) ≤ N) :=
      Nat.mul_le_mul_right_iff hNJ
    rw [hnle, ← hres]
    tauto
  have card_principalize_dvd (c : ℕ) [NeZero c]
      (𝔟 : (Ideal (𝓞 K))⁰) (y : ZMod c) (N : ℕ) (D : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
      (hJ : ClassGroup.mk0 J = D⁻¹) (hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K))) :
      cardNormLeResidueClassDvd c 𝔟 y D N
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (𝔟 * J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
          (IsPrincipal (I : Ideal (𝓞 K)) ∧
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
            ((y.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
              ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))))} := by
    classical
    rw [cardNormLeResidueClassDvd]
    have hdvd : ∀ I : (Ideal (𝓞 K))⁰, ((𝔟 * J : Ideal (𝓞 K)) ∣ (J * I : Ideal (𝓞 K)))
        ↔ ((𝔟 : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))) := by
      intro I
      rw [mul_comm (𝔟 : Ideal (𝓞 K)) (J : Ideal (𝓞 K)),
        mul_dvd_mul_iff_left (nonZeroDivisors.coe_ne_zero J)]
    refine Nat.card_congr
      (((Equiv.dvd J).subtypeEquiv (fun I ↦ ?_)).trans
        (Equiv.subtypeSubtypeEquivSubtype (p := fun a : (Ideal (𝓞 K))⁰ ↦ J ∣ a)
          (q := fun I' : (Ideal (𝓞 K))⁰ ↦ (𝔟 * J : Ideal (𝓞 K)) ∣ (I' : Ideal (𝓞 K)) ∧
            IsPrincipal (I' : Ideal (𝓞 K)) ∧
            Ideal.absNorm (I' : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
            ((Ideal.absNorm (I' : Ideal (𝓞 K)) : ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
              ((y.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
                ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))))
          (fun {a} hq ↦ by
            rw [nonZeroDivisors_dvd_iff_dvd_coe]
            exact dvd_trans (Dvd.intro_left _ rfl) hq.1)))
    simp only [Equiv.dvd_apply, Submonoid.coe_mul]
    rw [show ((𝔟 : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 I = D))
        ↔ (((Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 I = D) ∧
          (𝔟 : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))) by tauto,
      principalize c y N D J I hJ hNJ]
    rw [show ((𝔟 : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))) ↔
        ((𝔟 * J : Ideal (𝓞 K)) ∣ ((J : Ideal (𝓞 K)) * (I : Ideal (𝓞 K)))) from (hdvd I).symm]
    tauto
  have tendsto_count_div_of_cone_bridge
      (NJ : ℕ) (hNJ : 0 < NJ) (κ₀ C' : ℝ) (cnt : ℕ → ℕ) (coneR : ℝ → ℝ)
      (hbridge : ∀ N : ℕ, (cnt N : ℝ) * (torsionOrder K : ℝ) = coneR ((N * NJ : ℕ) : ℝ))
      (hcone : ∀ S : ℝ, 1 ≤ S → |coneR S - κ₀ * S| ≤ C' * S ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) :
      Filter.Tendsto (fun N : ℕ ↦ (cnt N : ℝ) / (N : ℝ))
        Filter.atTop (nhds (κ₀ * (NJ : ℝ) / (torsionOrder K : ℝ))) := by
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
    set d := Module.finrank ℚ K with hd
    have hdpos : 0 < d := Module.finrank_pos
    have htors : (0 : ℝ) < torsionOrder K := by
      exact_mod_cast (torsionOrder K).pos_of_ne_zero (torsionOrder_ne_zero K)
    refine hrate (C' := |C'| * (NJ : ℝ) / (torsionOrder K : ℝ))
      (d := d) hdpos (fun N hN ↦ ?_)
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNJN : (1 : ℝ) ≤ ((N * NJ : ℕ) : ℝ) := by
      rw [Nat.cast_mul]; exact one_le_mul_of_one_le_of_one_le hNR (by exact_mod_cast hNJ)
    have hkey := hcone ((N * NJ : ℕ) : ℝ) hNJN
    rw [← hbridge N, Nat.cast_mul] at hkey
    rw [show (cnt N : ℝ) - κ₀ * (NJ : ℝ) / (torsionOrder K : ℝ) * N
        = ((cnt N : ℝ) * (torsionOrder K : ℝ) - κ₀ * ((N : ℝ) * (NJ : ℝ))) / (torsionOrder K : ℝ) by
      field_simp]
    rw [abs_div, abs_of_pos htors, div_le_iff₀ htors]
    refine hkey.trans ?_
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have hNJpow : (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹) ≤ (NJ : ℝ) :=
      calc (NJ : ℝ) ^ (1 - (d : ℝ)⁻¹) ≤ (NJ : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hNJ)
              (by simp only [tsub_le_iff_right, le_add_iff_nonneg_right]; positivity)
        _ = (NJ : ℝ) := Real.rpow_one _
    have hgoalRHS : |C'| * (NJ : ℝ) / (torsionOrder K : ℝ) * (N : ℝ) ^ (1 - (d : ℝ)⁻¹) *
        (torsionOrder K : ℝ) = |C'| * ((N : ℝ) ^ (1 - (d : ℝ)⁻¹) * (NJ : ℝ)) := by
      field_simp
    rw [hgoalRHS]
    rw [mul_comm ((N : ℝ) ^ (1 - (d : ℝ)⁻¹)) ((NJ : ℝ) ^ (1 - (d : ℝ)⁻¹)),
      mul_comm ((N : ℝ) ^ (1 - (d : ℝ)⁻¹)) (NJ : ℝ), ← mul_assoc, ← mul_assoc]
    gcongr
    exact le_abs_self _
  have torsionBridge (I₀ : (Ideal (𝓞 K))⁰) (modulus residue : ℕ) (s : ℝ) :
      Nat.card {I : (Ideal (𝓞 K))⁰ // (I₀ : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal
          (I : Ideal (𝓞 K)) ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus) = (residue : ZMod modulus))} *
          torsionOrder K =
        Nat.card {u : idealSet K I₀ // mixedEmbedding.norm (u : mixedSpace K) ≤ s ∧
          ((intNorm (idealSetEquiv K I₀ u).val : ZMod modulus) =
            (residue : ZMod modulus))} := by
    obtain hs | hs := le_or_gt 0 s
    · rw [torsionOrder, ← Nat.card_prod]
      refine Nat.card_congr <| @Equiv.ofFiberEquiv _ (γ := Finset.Iic ⌊s⌋₊) _
        (fun I ↦ ⟨Ideal.absNorm I.1.val.1, Finset.mem_Iic.mpr (Nat.le_floor I.1.prop.2.2.1)⟩)
        (fun u ↦ ⟨intNorm (idealSetEquiv K I₀ u.1).1, Finset.mem_Iic.mpr
          (Nat.le_floor (by rw [intNorm_idealSetEquiv_apply]; exact u.prop.1))⟩)
        fun ⟨i, hi⟩ ↦ ?_
      simp_rw [Subtype.mk.injEq]
      have hile : (i : ℝ) ≤ s := (Nat.le_floor_iff hs).mp (Finset.mem_Iic.mp hi)
      by_cases hib : (i : ZMod modulus) = (residue : ZMod modulus)
      · calc _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // (I₀ : Ideal (𝓞 K)) ∣ I ∧
                  Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
                  (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                  ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus) =
                    (residue : ZMod modulus))} // Ideal.absNorm I.1.1 = i} × torsion K :=
              Equiv.prodSubtypeFstEquivSubtypeProd
            _ ≃ {I : (Ideal (𝓞 K))⁰ // ((I₀ : Ideal (𝓞 K)) ∣ I ∧
                  Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
                  (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                  ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus) =
                    (residue : ZMod modulus))) ∧ Ideal.absNorm I.1 = i} × torsion K :=
              Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeSubtypeEquivSubtypeInter
                (p := fun I : (Ideal (𝓞 K))⁰ ↦ (I₀ : Ideal (𝓞 K)) ∣ I ∧
                  Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
                  (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
                  ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus) =
                    (residue : ZMod modulus)))
                (q := fun I ↦ Ideal.absNorm (I : Ideal (𝓞 K)) = i)
            _ ≃ {I : (Ideal (𝓞 K))⁰ // (I₀ : Ideal (𝓞 K)) ∣ I ∧
                  Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
                  Ideal.absNorm (I : Ideal (𝓞 K)) = i} × torsion K :=
              Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeEquivRight fun I ↦ by
                constructor
                · rintro ⟨⟨h1, h2, _, _⟩, h5⟩; exact ⟨h1, h2, h5⟩
                · rintro ⟨h1, h2, h3⟩
                  exact ⟨⟨h1, h2, by rw [h3]; exact hile, by rw [h3]; exact hib⟩, h3⟩
            _ ≃ {u : idealSet K I₀ // mixedEmbedding.norm (u : mixedSpace K) = i} :=
                  (idealSetEquivNorm K I₀ i).symm
            _ ≃ {u : idealSet K I₀ // intNorm (idealSetEquiv K I₀ u).1 = i} := by
                  simp_rw [← intNorm_idealSetEquiv_apply, Nat.cast_inj]; rfl
            _ ≃ _ := (Equiv.subtypeSubtypeEquivSubtype (p := fun u : idealSet K I₀ ↦
                  mixedEmbedding.norm (u : mixedSpace K) ≤ s ∧
                    ((intNorm (idealSetEquiv K I₀ u).val : ZMod modulus) =
                      (residue : ZMod modulus)))
                  (q := fun u ↦ intNorm (idealSetEquiv K I₀ u).1 = i) fun {u} h ↦ by
                  rw [← intNorm_idealSetEquiv_apply, h]
                  exact ⟨by exact_mod_cast hile, by rw [h] at *; exact hib⟩).symm
      · have : IsEmpty {u : {u : idealSet K I₀ //
            mixedEmbedding.norm (u : mixedSpace K) ≤ s ∧
            ((intNorm (idealSetEquiv K I₀ u).val : ZMod modulus) =
              (residue : ZMod modulus))} //
            intNorm (idealSetEquiv K I₀ u.1).1 = i} :=
          ⟨fun u ↦ hib (by rw [← u.2]; exact u.1.2.2)⟩
        have : IsEmpty {u : ({I : (Ideal (𝓞 K))⁰ // (I₀ : Ideal (𝓞 K)) ∣ I ∧
            Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
            (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus) =
              (residue : ZMod modulus))} × torsion K) //
            Ideal.absNorm u.1.1.1 = i} :=
          ⟨fun u ↦ hib (by rw [← u.2]; exact u.1.1.2.2.2.2)⟩
        exact Equiv.equivOfIsEmpty _ _
    · have : IsEmpty {I : (Ideal (𝓞 K))⁰ // (I₀ : Ideal (𝓞 K)) ∣ I ∧
          Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod modulus) =
            (residue : ZMod modulus))} :=
        ⟨fun I ↦ absurd I.2.2.2.1 (not_le.mpr (lt_of_lt_of_le hs (Nat.cast_nonneg _)))⟩
      have : IsEmpty {u : idealSet K I₀ // mixedEmbedding.norm (u : mixedSpace K) ≤ s ∧
          ((intNorm (idealSetEquiv K I₀ u).val : ZMod modulus) =
            (residue : ZMod modulus))} :=
        ⟨fun u ↦ absurd u.2.1 (not_le.mpr (lt_of_lt_of_le hs (mixedEmbedding.norm_nonneg _)))⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty, zero_mul]
  have card_isPrincipal_dvd_norm_le_residue_natBound
      (I₀ : (Ideal (𝓞 K))⁰) (m b M : ℕ) :
      Nat.card {I : (Ideal (𝓞 K))⁰ // (I₀ : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ M ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m))} * torsionOrder K =
        Nat.card {a : idealSet K I₀ // mixedEmbedding.norm (a : mixedSpace K) ≤ (M : ℝ) ∧
          ((intNorm (idealSetEquiv K I₀ a).val : ZMod m) = (b : ZMod m))} := by
    rw [← torsionBridge I₀ m b (M : ℝ)]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun I ↦ by rw [Nat.cast_le])
  set NB : ℕ := Ideal.absNorm (𝔟 : Ideal (𝓞 K)) with hNBdef
  have hNB : 0 < NB := absNorm_pos_of_nonZeroDivisors 𝔟
  have hNB0 : (NB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNB.ne'
  obtain ⟨J, hJ, hJcop⟩ := exists_mk0_eq_absNorm_coprime D⁻¹ NB hNB
  set NJ : ℕ := Ideal.absNorm (J : Ideal (𝓞 K)) with hNJdef
  have hNJ : 0 < NJ := absNorm_pos_of_nonZeroDivisors J
  have hNBc : NB.Coprime c := by rw [hNBdef, ZMod.isUnit_iff_coprime] at hu; exact hu
  have hcop : NB.Coprime (c * NJ) := Nat.Coprime.mul_right hNBc (hNJdef ▸ hJcop.symm)
  haveI : NeZero (c * NJ) := ⟨Nat.mul_ne_zero (NeZero.ne c) hNJ.ne'⟩
  have hm : ((c * NJ : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (c * NJ))
  obtain ⟨κ, C', hJcone, h𝔟Jcone⟩ :=
    exists_card_idealSet_residue_real_le_dvd (c * NJ) hm (y.val * NJ) J 𝔟 hcop
  set coneJ : ℝ → ℝ := fun S ↦ (Nat.card {a : idealSet K J //
    mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
      ((intNorm (idealSetEquiv K J a).val : ZMod (c * NJ))
        = ((y.val * NJ : ℕ) : ZMod (c * NJ)))} : ℝ)
    with hconeJ
  set cone𝔟J : ℝ → ℝ := fun S ↦ (Nat.card {a : idealSet K (𝔟 * J) //
    mixedEmbedding.norm (a : mixedSpace K) ≤ S ∧
      ((intNorm (idealSetEquiv K (𝔟 * J) a).val : ZMod (c * NJ))
        = ((y.val * NJ : ℕ) : ZMod (c * NJ)))} : ℝ) with hcone𝔟J
  have hcardJ (N : ℕ) :
      cardNormLeResidueClass c y D N =
        Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
          (IsPrincipal (I : Ideal (𝓞 K)) ∧
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
            ((y.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
              ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))))} := by
    unfold cardNormLeResidueClass
    simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
    exact Nat.card_congr
      (((Equiv.dvd J).subtypeEquiv (fun I ↦ principalize c y N D J I hJ hNJ)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _))
  have hbridgeJ : ∀ N : ℕ, (cardNormLeResidueClass c y D N : ℝ) * (torsionOrder K : ℝ)
      = coneJ ((N * NJ : ℕ) : ℝ) := fun N ↦ by
    rw [hconeJ, ← Nat.cast_mul, hcardJ N,
      card_isPrincipal_dvd_norm_le_residue_natBound J (c * NJ) (y.val * NJ) (N * NJ)]
  have hbridge𝔟J : ∀ N : ℕ,
      (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) * (torsionOrder K : ℝ)
      = cone𝔟J ((N * NJ : ℕ) : ℝ) := fun N ↦ by
    rw [hcone𝔟J, ← Nat.cast_mul, card_principalize_dvd c 𝔟 y N D J hJ hNJ, ← Submonoid.coe_mul,
      card_isPrincipal_dvd_norm_le_residue_natBound (𝔟 * J) (c * NJ) (y.val * NJ) (N * NJ)]
  have hJdens : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClass c y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ * (NJ : ℝ) / (torsionOrder K : ℝ))) :=
    tendsto_count_div_of_cone_bridge NJ hNJ κ C' (cardNormLeResidueClass c y D) coneJ hbridgeJ
      (fun S hS ↦ by rw [hconeJ]; exact hJcone S hS)
  have hκfull_eq : κfull = κ * (NJ : ℝ) / (torsionOrder K : ℝ) :=
    tendsto_nhds_unique hκfull hJdens
  have h𝔟Jdens : Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidueClassDvd c 𝔟 y D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds (κ / (NB : ℝ) * (NJ : ℝ) / (torsionOrder K : ℝ))) :=
    tendsto_count_div_of_cone_bridge NJ hNJ (κ / (NB : ℝ)) C' (cardNormLeResidueClassDvd c 𝔟 y D)
      cone𝔟J hbridge𝔟J (fun S hS ↦ by rw [hcone𝔟J]; exact h𝔟Jcone S hS)
  rw [show κfull / (NB : ℝ) = κ / (NB : ℝ) * (NJ : ℝ) / (torsionOrder K : ℝ) by
    rw [hκfull_eq]; ring]
  exact h𝔟Jdens

end Chebotarev
