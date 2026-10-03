/- GID: D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A bJ-cone residue cell equals a translated sublattice cell count. -/
module

public import D5.S3.Arith.PrimeIdeals.NormResidue.IdealCongruenceCountCells

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

open Ideal NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone Units in
/-- **Per-class effective residue count.** For a fixed ideal class `C`, the number of nonzero
integral ideals of norm `≤ N`, norm residue `a (mod c)`, **and class `C`** equals
`κ_C · N + O(N^{1-1/d})`. Summed over the finite class group by
the class partition, this is the full effective count
`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`. Proof: principalize to `J`-divisible
principal ideals (with `ClassGroup.mk0 J = C⁻¹`), then invoke the geometric
cone count at modulus `c·N(J)` and residue
`a·N(J)`. -/
theorem exists_card_norm_le_residue_class_eq_sub_mul_rpow_le
    {K : Type*} [Field K] [NumberField K] (c : ℕ) [NeZero c] (a : ZMod c) (C : ClassGroup (𝓞 K)) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  have hNJ : 0 < Ideal.absNorm (J : Ideal (𝓞 K)) := absNorm_pos_of_nonZeroDivisors J
  have principalize (N : ℕ) (I : (Ideal (𝓞 K))⁰) :
      ((Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C) ↔
        (IsPrincipal (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∧
          Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≤
            N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
          ((Ideal.absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :
              ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
            ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
              ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))))) := by
    have hnorm : absNorm (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        = absNorm (I : Ideal (𝓞 K)) * absNorm (J : Ideal (𝓞 K)) := by
      simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, _root_.map_mul]; ring
    have hprin : IsPrincipal (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ↔
        ClassGroup.mk0 I = C := by
      have hmem : (((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰ :=
        SetLike.coe_mem _
      rw [← ClassGroup.mk0_eq_one_iff hmem]
      have hmk : ClassGroup.mk0 (⟨(((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)), hmem⟩ :
          (Ideal (𝓞 K))⁰) = ClassGroup.mk0 ((Equiv.dvd J) I : (Ideal (𝓞 K))⁰) := by congr 1
      rw [hmk, Equiv.dvd_apply, map_mul, hJ, _root_.inv_mul_eq_one, eq_comm]
    rw [hprin, hnorm]
    have hres : (((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ↔
        (((Ideal.absNorm (I : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
          ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
            ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))) := by
      rw [show ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a ↔
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((a.val : ℕ) : ZMod c) by
        rw [ZMod.natCast_val, ZMod.cast_id]]
      rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff,
        Nat.ModEq, Nat.ModEq, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right]
      exact ⟨fun h ↦ by rw [h], fun h ↦ Nat.eq_of_mul_eq_mul_right hNJ h⟩
    have hnle : (absNorm (I : Ideal (𝓞 K)) * absNorm (J : Ideal (𝓞 K)) ≤
        N * absNorm (J : Ideal (𝓞 K))) ↔ (absNorm (I : Ideal (𝓞 K)) ≤ N) :=
      Nat.mul_le_mul_right_iff hNJ
    rw [hnle, ← hres]
    tauto
  haveI : NeZero (c * Ideal.absNorm (J : Ideal (𝓞 K))) :=
    ⟨Nat.mul_ne_zero (NeZero.ne c) hNJ.ne'⟩
  let m : ℕ := c * Ideal.absNorm (J : Ideal (𝓞 K))
  let b : ℕ := a.val * Ideal.absNorm (J : Ideal (𝓞 K))
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
  have hbridge : ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
            (IsPrincipal (I : Ideal (𝓞 K)) ∧
            Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
    obtain ⟨κ, C', hcore⟩ := exists_card_idealSet_residue_le m b J
    have htors : (0 : ℝ) < torsionOrder K :=
      mod_cast (torsionOrder K).pos_of_ne_zero (torsionOrder_ne_zero K)
    refine ⟨κ / torsionOrder K, C' / torsionOrder K, fun N hN ↦ ?_⟩
    set cnt : ℝ := (Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
      (IsPrincipal (I : Ideal (𝓞 K)) ∧
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod m) = (b : ZMod m)))} : ℝ) with hcnt
    set cone : ℝ := (Nat.card {u : idealSet K J // mixedEmbedding.norm (u : mixedSpace K) ≤
      ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ∧
      ((intNorm (idealSetEquiv K J u).val : ZMod m) = (b : ZMod m))} : ℝ) with hcone
    have hcount : cnt * torsionOrder K = cone := by
      rw [hcnt, hcone, ← Nat.cast_mul]
      congr 1
      rw [← torsionBridge J m b
        ((N * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ)]
      congr 1
      exact Nat.card_congr (Equiv.subtypeEquivRight fun I ↦ by simp only [Nat.cast_le])
    have he : |cnt - κ / torsionOrder K * N| = |cone - κ * N| / torsionOrder K := by
      rw [eq_div_iff htors.ne', ← hcount,
        show cnt * torsionOrder K - κ * N
          = torsionOrder K * (cnt - κ / torsionOrder K * N) by field_simp,
        abs_mul, abs_of_pos htors, mul_comm]
    rw [he, div_le_iff₀ htors]
    calc |cone - κ * N| ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := hcore N hN
      _ = C' / torsionOrder K * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) *
          torsionOrder K := by field_simp
  obtain ⟨κ, C', hκ⟩ := hbridge
  have hcard (N : ℕ) :
      Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K)) ∧
          (IsPrincipal (I : Ideal (𝓞 K)) ∧
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N * Ideal.absNorm (J : Ideal (𝓞 K)) ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K)))) =
            ((a.val * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) :
              ZMod (c * Ideal.absNorm (J : Ideal (𝓞 K))))))} := by
    simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
    exact Nat.card_congr
      (((Equiv.dvd J).subtypeEquiv (fun I ↦ principalize N I)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _))
  refine ⟨κ, C', fun N hN ↦ ?_⟩
  rw [hcard N]
  exact hκ N hN


/-- **Effective ideal count by norm residue.** For a number field `K` and a modulus `c`, the
number of nonzero integral ideals of norm `≤ N` with norm residue `a (mod c)` is
`κ_a · N + O(N^{1-1/d})`, `d = [K:ℚ]`. Proof: split by ideal class (finitely many)
over the class group; sum the per-class effective counts
(`exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`) and bound the total error by the
triangle inequality over the (finite) class group. -/
theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (a : ZMod c) :
    ∃ κ C' : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  classical
  have hsplit (N : ℕ) :
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a}
      = ∑ C : ClassGroup (𝓞 K),
          Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} := by
    have hbase : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} :=
      Ideal.finite_setOf_absNorm_le₀ N
    have hfin : Finite {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} :=
      Finite.of_injective (fun I ↦ (⟨I.1, I.2.1⟩ :
        {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}))
        (fun x y h ↦ Subtype.ext (by simpa using h))
    have hfinC : ∀ C : ClassGroup (𝓞 K), Finite {I : (Ideal (𝓞 K))⁰ //
        (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} := fun C ↦
      Finite.of_injective (fun I ↦ (⟨I.1, I.2.1.1⟩ :
        {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N}))
        (fun x y h ↦ Subtype.ext (by simpa using h))
    have hF : Fintype {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} := Fintype.ofFinite _
    have hFC : ∀ C, Fintype {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C} :=
      fun C ↦ Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card,
      Finset.sum_congr rfl (fun C _ ↦ Nat.card_eq_fintype_card (α := {I : (Ideal (𝓞 K))⁰ //
        (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a) ∧ ClassGroup.mk0 I = C})),
      ← Fintype.card_sigma]
    refine Fintype.card_congr ((Equiv.sigmaFiberEquiv (fun I :
      {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
        ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a} ↦ ClassGroup.mk0 I.1)).symm.trans ?_)
    refine Equiv.sigmaCongrRight (fun C ↦ ?_)
    exact {
      toFun := fun I ↦ ⟨I.1.1, I.1.2, I.2⟩
      invFun := fun I ↦ ⟨⟨I.1, I.2.1⟩, I.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  choose κf C'f hκf using fun C : ClassGroup (𝓞 K) ↦
    exists_card_norm_le_residue_class_eq_sub_mul_rpow_le (K := K) c a C
  refine ⟨∑ C : ClassGroup (𝓞 K), κf C, ∑ C : ClassGroup (𝓞 K), |C'f C|, fun N hN ↦ ?_⟩
  rw [hsplit N, Nat.cast_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun C _ ↦ ?_
  exact (hκf C N hN).trans (by gcongr; exact le_abs_self _)

/-- **Norm-residue count, abbreviation.** `cardNormLeResidue K c a N` is the number of nonzero
integral ideals of `𝓞 K` of norm `≤ N` whose norm is `≡ a (mod c)`. The leading constant of its
effective estimate (`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`) is, by
the normalized-error limit of `cardNormLeResidue K c a N / N`. -/
def cardNormLeResidue (K : Type*) [Field K] [NumberField K] (c : ℕ) (a : ZMod c)
    (N : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = a}

open scoped Classical in
/-- **κ-uniformity over the realized-residue subgroup.** Under Fourier-decay `hF` (all nontrivial
`S`-character twists of the residue counts have vanishing density), the residue-count densities
`κ, κ'` of any `a, a' ∈ S` coincide. Proof: `hF` says every nontrivial Fourier coefficient of
`s ↦ κ_s` on `S` vanishes; finite-abelian character orthogonality then makes
`κ_·` constant on `S`. -/
theorem cardNormLeResidue_density_eq_of_mem_subgroup {K : Type*} [Field K] [NumberField K]
    {c : ℕ} [NeZero c] {S : Subgroup (ZMod c)ˣ}
    (hF : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      Filter.Tendsto (fun N : ℕ ↦ (∑ s : S, ((χ s : ℂˣ) : ℂ) *
          (cardNormLeResidue K c ((s : (ZMod c)ˣ) : ZMod c) N : ℂ)) / (N : ℂ))
        Filter.atTop (nhds 0))
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
  have hlimits : ∀ s : S, ∃ κ : ℝ,
      Filter.Tendsto
        (fun N : ℕ ↦ (cardNormLeResidue K c ((s : (ZMod c)ˣ) : ZMod c) N : ℝ) / (N : ℝ))
        Filter.atTop (nhds κ) := by
    intro s
    obtain ⟨κ, _, hκ⟩ :=
      exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K c ((s : (ZMod c)ˣ) : ZMod c)
    exact ⟨κ, hrate Module.finrank_pos hκ⟩
  choose κf hκf using hlimits
  have hκa : κ = κf ⟨a, ha⟩ := tendsto_nhds_unique hκ (hκf ⟨a, ha⟩)
  have hκa' : κ' = κf ⟨a', ha'⟩ := tendsto_nhds_unique hκ' (hκf ⟨a', ha'⟩)
  have hhat : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      ∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ) = 0 := by
    intro χ hχ
    refine tendsto_nhds_unique ?_ (hF χ hχ)
    have hsum := tendsto_finsetSum Finset.univ fun s (_ : s ∈ Finset.univ) ↦
      ((Complex.continuous_ofReal.tendsto (κf s)).comp (hκf s)).const_mul ((χ s : ℂˣ) : ℂ)
    refine hsum.congr fun N ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  letI : Fintype (S →* ℂˣ) := Fintype.ofFinite _
  have hcard0 : (Fintype.card (S →* ℂˣ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum (u : S) :
      (Fintype.card (S →* ℂˣ) : ℂ) * (κf u : ℂ) = ∑ s : S, (κf s : ℂ) := by
    have horth : ∀ s : S, (∑ χ : S →* ℂˣ, ((χ (u⁻¹ * s) : ℂˣ) : ℂ))
        = if s = u then (Fintype.card (S →* ℂˣ) : ℂ) else 0 := by
      intro s
      by_cases hs : s = u
      · subst hs; simp
      · rw [if_neg hs]
        letI : AddGroup (Additive (S →* ℂˣ)) := inferInstance
        letI : CommSemiring ℂ := inferInstance
        let ψ : AddChar (Additive (S →* ℂˣ)) ℂ := {
          toFun := fun χ => ((Additive.toMul χ (u⁻¹ * s) : ℂˣ) : ℂ)
          map_zero_eq_one' := by simp
          map_add_eq_mul' := by
            intro χ τ
            change (((Additive.toMul χ * Additive.toMul τ) (u⁻¹ * s) : ℂˣ) : ℂ) =
              ((Additive.toMul χ (u⁻¹ * s) : ℂˣ) : ℂ) *
                ((Additive.toMul τ (u⁻¹ * s) : ℂˣ) : ℂ)
            rw [MonoidHom.mul_apply, Units.val_mul] }
        have hψ : ψ ≠ 0 := by
          intro hzero
          have hg : u⁻¹ * s ≠ 1 := fun h => hs (inv_mul_eq_one.mp h).symm
          obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity S ℂ hg
          have hval := congrArg
            (fun φ : AddChar (Additive (S →* ℂˣ)) ℂ => φ (Additive.ofMul χ)) hzero
          exact hχ (Units.ext (by simpa [ψ] using hval))
        have hzero : (∑ χ : Additive (S →* ℂˣ), ψ χ) = 0 := by
          rw [AddChar.sum_eq_ite ψ, if_neg hψ]
        have htransport :
            (∑ χ : S →* ℂˣ, ((χ (u⁻¹ * s) : ℂˣ) : ℂ)) =
              ∑ χ : Additive (S →* ℂˣ), ψ χ :=
          Fintype.sum_equiv Additive.ofMul _ _ (fun χ => rfl)
        exact htransport.trans hzero
    calc
      (Fintype.card (S →* ℂˣ) : ℂ) * (κf u : ℂ)
          = ∑ s : S, (if s = u then (Fintype.card (S →* ℂˣ) : ℂ) else 0) * (κf s : ℂ) := by
              simp
      _ = ∑ s : S, (∑ χ : S →* ℂˣ, ((χ (u⁻¹ * s) : ℂˣ) : ℂ)) * (κf s : ℂ) := by
            refine Finset.sum_congr rfl fun s _ ↦ ?_; rw [horth s]
      _ = ∑ s : S, ∑ χ : S →* ℂˣ, ((χ (u⁻¹ * s) : ℂˣ) : ℂ) * (κf s : ℂ) := by
            refine Finset.sum_congr rfl fun s _ ↦ ?_; rw [Finset.sum_mul]
      _ = ∑ χ : S →* ℂˣ, ∑ s : S, ((χ (u⁻¹ * s) : ℂˣ) : ℂ) * (κf s : ℂ) := Finset.sum_comm
      _ = ∑ χ : S →* ℂˣ, ((χ u⁻¹ : ℂˣ) : ℂ) *
            ∑ s : S, ((χ s : ℂˣ) : ℂ) * (κf s : ℂ) := by
            refine Finset.sum_congr rfl fun χ _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ ↦ ?_
            rw [map_mul, Units.val_mul, mul_assoc]
      _ = ∑ s : S, (κf s : ℂ) := by
            rw [Finset.sum_eq_single_of_mem (1 : S →* ℂˣ) (Finset.mem_univ _)
              fun χ _ hχ ↦ by rw [hhat χ hχ, mul_zero]]
            simp
  have hfc : (κf ⟨a, ha⟩ : ℂ) = (κf ⟨a', ha'⟩ : ℂ) :=
    mul_left_cancel₀ hcard0 ((hsum ⟨a, ha⟩).trans (hsum ⟨a', ha'⟩).symm)
  rw [hκa, hκa']
  exact_mod_cast hfc

open scoped Classical in
/-- **Norm-residue density transfer.** Under Fourier-decay `hF` (every nontrivial `S`-character
twist of the residue counts has vanishing density), the effective estimate
`|#{N(I) ≤ N, N(I) ≡ a} − κ·N| ≤ C'·N^{1-1/d}` holds with a single pair `(κ, C')` for all `a ∈ S`
simultaneously. The per-residue leading constants are the limits of `count / N`
(from the normalized-error bound), hence constant on `S`
(`cardNormLeResidue_density_eq_of_mem_subgroup`); `κ` is that common value and `C'` the sum of the
per-residue error constants over `ZMod c`. -/
theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform
    (K : Type*) [Field K] [NumberField K] (c : ℕ) [NeZero c] (S : Subgroup (ZMod c)ˣ)
    (hF : ∀ χ : S →* ℂˣ, χ ≠ 1 →
      Filter.Tendsto (fun N : ℕ ↦ (∑ s : S, ((χ s : ℂˣ) : ℂ) *
          (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = ((s : (ZMod c)ˣ) : ZMod c)} : ℂ))
          / (N : ℂ))
        Filter.atTop (nhds 0)) :
    ∃ κ C' : ℝ, ∀ a ∈ S, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
            ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = (a : ZMod c)} : ℝ)
          - κ * N|
        ≤ C' * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
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
  choose κf C'f hκf using exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K c
  have hκlim : ∀ a : ZMod c,
      Filter.Tendsto (fun N : ℕ ↦ (cardNormLeResidue K c a N : ℝ) / (N : ℝ))
        Filter.atTop (nhds (κf a)) := fun a ↦
    hrate Module.finrank_pos (hκf a)
  refine ⟨κf ((1 : (ZMod c)ˣ) : ZMod c), ∑ b : ZMod c, |C'f b|, fun a ha N hN ↦ ?_⟩
  have hconst : κf ((a : (ZMod c)ˣ) : ZMod c) = κf ((1 : (ZMod c)ˣ) : ZMod c) :=
    cardNormLeResidue_density_eq_of_mem_subgroup hF ha (one_mem S)
      (hκlim ((a : (ZMod c)ˣ) : ZMod c)) (hκlim ((1 : (ZMod c)ˣ) : ZMod c))
  rw [← hconst]
  refine (hκf ((a : (ZMod c)ˣ) : ZMod c) N hN).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  exact (le_abs_self _).trans (Finset.single_le_sum
    (f := fun b ↦ |C'f b|) (fun b _ ↦ abs_nonneg _) (Finset.mem_univ _))

/-! ### Realizer-driven Fourier decay (the `hF` producer) -/

/-! ### Per-class densities and the realizer transfer (Lang VI §3 Thm 3)

The honest proof of κ-constancy over the realized subgroup `S` (Lang, *Algebraic Number Theory*
GTM 110, Ch. VI §3, Thm 3) is *not* the lossy multiply-by-`𝔟`-and-sandwich argument (which only
gives `κ_a ≤ N(𝔟)·κ_{a·t}`). It goes through the **per-class** densities. We isolate the single
irreducible geometric fact — the per-class realizer transfer — and assemble the global statement
around it cleanly:

* `cardNormLeResidueClass` — the per-class count; its density follows from the effective
  per-class estimate by dividing by `N`.
* The density splits over the class group, `κ_y = ∑_C κ_{C,y}`.
* `cardNormLeResidueClass_density_transfer` — **the geometric heart**: for a realizer `𝔟` of a
  unit `u = N(𝔟) mod c`, the per-class density transfers as `κ_{C,x} = κ_{C·[𝔟], x·u}`. Proof:
  the norm-multiplying bijection `I ↦ 𝔟·I` gives the exact identity
  `#{[I]=C, N(I)≡x, N(I)≤M} = #{[J]=C·[𝔟], N(J)≡x·u, 𝔟∣J, N(J)≤M·N(𝔟)}` (Route A); the
  `𝔟`-divisible class-`C·[𝔟]` density is `1/N(𝔟)` of the full class-`C·[𝔟]` density at the same
  residue (Route B, via `cardNormLeResidueClassDvd_div_density`), so the `N(𝔟)`-factors cancel.
* `cardNormLeResidue_density_const_of_realized` — the global statement: sum the transfer over the
  class group and reindex by `Equiv.mulRight [𝔟]`.
-/

open Ideal in
/-- **Per-class norm-residue count.** The number of nonzero integral ideals of `𝓞 K` of norm `≤ N`,
norm residue `y (mod c)`, and ideal class `C`. -/
def cardNormLeResidueClass {K : Type*} [Field K] [NumberField K] (c : ℕ) (y : ZMod c)
    (C : ClassGroup (𝓞 K)) (N : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
    ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 I = C}

open Ideal in
/-- **`𝔟`-divisible per-class norm-residue count.** The number of nonzero integral ideals of
`𝓞 K` divisible by `𝔟`, of norm `≤ N`, norm residue `y (mod c)`, and ideal class `D`. -/
def cardNormLeResidueClassDvd {K : Type*} [Field K] [NumberField K] (c : ℕ)
    (𝔟 : (Ideal (𝓞 K))⁰) (y : ZMod c) (D : ClassGroup (𝓞 K)) (N : ℕ) : ℕ :=
  Nat.card {J : (Ideal (𝓞 K))⁰ // (𝔟 : Ideal (𝓞 K)) ∣ (J : Ideal (𝓞 K)) ∧
    ((Ideal.absNorm (J : Ideal (𝓞 K)) ≤ N ∧
      ((Ideal.absNorm (J : Ideal (𝓞 K)) : ZMod c)) = y) ∧ ClassGroup.mk0 J = D)}

/-! ### Geometry-of-numbers core for the `𝔟`-divisible density (Lang VI §3 / GRS Thm 1)

The single irreducible geometric fact (`cardNormLeResidueClassDvd_div_density`) is the covolume /
CRT equidistribution: principalizing the class-`D` count at a coprime representative `J` of `D⁻¹`
sends the full count to the `J`-lattice cone-point count and the `𝔟`-divisible count to the
*sublattice* `Λ_{𝔟J} ⊆ Λ_J` cone-point count (index `N(𝔟)`, `gcd(N(𝔟), c·N(J)) = 1`). The leading
constants then differ by exactly `N(𝔟)` (the covolume ratio), the qualifying `m`-cosets being
matched by the norm-residue-preserving bijection `Λ_{𝔟J}/m·Λ_{𝔟J} ≅ Λ_J/m·Λ_J`. The lemmas below
assemble this. -/

open Ideal in
/-- **(L1) Coprime class representative.** Every ideal class `D` has an integral representative `J`
whose absolute norm is coprime to a prescribed positive integer `n`. (Standard avoidance: from any
representative `J₀` of `D`, multiply by a principal ideal supported away from the prime factors of
`n·N(J₀)` to clear the common factors; the class is unchanged and the resulting norm is coprime to
`n`.) This is the representative used to align the two cone-point lattices in the covolume / CRT
density transfer so that `gcd(N(𝔟), c·N(J)) = 1`. -/
theorem exists_mk0_eq_absNorm_coprime {K : Type*} [Field K] [NumberField K]
    (D : ClassGroup (𝓞 K)) (n : ℕ) (hn : 0 < n) :
    ∃ J : (Ideal (𝓞 K))⁰, ClassGroup.mk0 J = D ∧
      (Ideal.absNorm (J : Ideal (𝓞 K))).Coprime n := by
  have absNorm_coprime_of_isCoprime_span
      (J : (Ideal (𝓞 K))⁰) (n : ℕ)
      (hcop : IsCoprime (J : Ideal (𝓞 K)) (Ideal.span {(n : 𝓞 K)})) :
      (Ideal.absNorm (J : Ideal (𝓞 K))).Coprime n := by
    by_contra hnc
    obtain ⟨p, hp, hpJ, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    obtain ⟨P, hPmax, hPunder, hPdvd⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp (J : Ideal (𝓞 K)) hpJ
    have hJP : (J : Ideal (𝓞 K)) ≤ P := Ideal.le_of_dvd hPdvd
    have hpP : (p : 𝓞 K) ∈ P := by
      have hpZ : (p : ℤ) ∈ Ideal.under ℤ P := by
        rw [hPunder]
        exact Ideal.mem_span_singleton_self _
      rw [Ideal.under, Ideal.mem_comap] at hpZ
      simpa using hpZ
    have hnP : (n : 𝓞 K) ∈ P := by
      obtain ⟨k, hk⟩ := hpn
      rw [hk]
      push_cast
      exact Ideal.mul_mem_right _ _ hpP
    have hspanP : Ideal.span {(n : 𝓞 K)} ≤ P := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hnP
    have hsupP : (J : Ideal (𝓞 K)) ⊔ Ideal.span {(n : 𝓞 K)} ≤ P := sup_le hJP hspanP
    rw [Ideal.isCoprime_iff_sup_eq.mp hcop, top_le_iff] at hsupP
    exact hPmax.ne_top hsupP
  classical
  rcases eq_or_ne n 1 with rfl | hn1
  · obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective D
    exact ⟨J, hJ, Nat.coprime_one_right _⟩
  have hn2 : 2 ≤ n := by lia
  obtain ⟨J₀, hJ₀⟩ := ClassGroup.mk0_surjective D⁻¹
  have hJ₀ne : (J₀ : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J₀
  set 𝔫 : Ideal (𝓞 K) := Ideal.span {(n : 𝓞 K)} with h𝔫
  have hnZ : (n : 𝓞 K) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := 𝓞 K)).mpr hn.ne'
  have h𝔫ne : 𝔫 ≠ ⊥ := by
    rwa [h𝔫, Ne, Ideal.span_singleton_eq_bot]
  have h𝔫top : 𝔫 ≠ ⊤ := by
    rw [Ne, ← Ideal.absNorm_eq_one_iff, h𝔫, Ideal.absNorm_span_natCast]
    have : 2 ≤ n ^ Module.finrank ℤ (𝓞 K) :=
      le_trans hn2 (Nat.le_self_pow Module.finrank_pos.ne' n)
    lia
  have hle : 𝔫 * (J₀ : Ideal (𝓞 K)) ≤ (J₀ : Ideal (𝓞 K)) := Ideal.mul_le_right
  have hIne : 𝔫 * (J₀ : Ideal (𝓞 K)) ≠ 0 := mul_ne_zero h𝔫ne hJ₀ne
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hIne
  have hane : a ≠ 0 := by
    intro hbot
    rw [hbot, Ideal.span_singleton_zero, sup_bot_eq] at ha
    apply h𝔫top
    have : (J₀ : Ideal (𝓞 K)) * 𝔫 = (J₀ : Ideal (𝓞 K)) * ⊤ := by
      rwa [Ideal.mul_top, mul_comm]
    exact mul_left_cancel₀ hJ₀ne this
  have haJ₀ : Ideal.span {a} ≤ (J₀ : Ideal (𝓞 K)) := le_sup_right.trans (le_of_eq ha)
  obtain ⟨J₁, hJ₁⟩ : (J₀ : Ideal (𝓞 K)) ∣ Ideal.span {a} := Ideal.dvd_iff_le.mpr haJ₀
  have hJ₁ne : J₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ₁
    exact hane hJ₁
  have hcop : 𝔫 ⊔ J₁ = ⊤ := by
    have hkey : (J₀ : Ideal (𝓞 K)) * (𝔫 ⊔ J₁) = (J₀ : Ideal (𝓞 K)) * ⊤ := by
      calc (J₀ : Ideal (𝓞 K)) * (𝔫 ⊔ J₁)
          = (J₀ : Ideal (𝓞 K)) * 𝔫 ⊔ (J₀ : Ideal (𝓞 K)) * J₁ := Ideal.mul_sup _ _ _
        _ = 𝔫 * (J₀ : Ideal (𝓞 K)) ⊔ Ideal.span {a} := by rw [mul_comm (J₀ : Ideal (𝓞 K)) 𝔫, hJ₁]
        _ = (J₀ : Ideal (𝓞 K)) := ha
        _ = (J₀ : Ideal (𝓞 K)) * ⊤ := (Ideal.mul_top _).symm
    exact mul_left_cancel₀ hJ₀ne hkey
  have hJ₁mem : J₁ ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hJ₁ne
  have hsaZ : Ideal.span {a} ≠ 0 := by
    rwa [Submodule.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
  set J₁' : (Ideal (𝓞 K))⁰ := ⟨J₁, hJ₁mem⟩ with hJ₁'
  refine ⟨J₁', ?_, ?_⟩
  · have hsa_mem : Ideal.span {a} ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hsaZ
    have hprinc : ClassGroup.mk0 (⟨Ideal.span {a}, hsa_mem⟩ : (Ideal (𝓞 K))⁰) = 1 :=
      (ClassGroup.mk0_eq_one_iff hsa_mem).mpr ⟨a, rfl⟩
    have hfact : (⟨Ideal.span {a}, hsa_mem⟩ : (Ideal (𝓞 K))⁰) = J₀ * J₁' :=
      Subtype.ext (by simp only [Submonoid.coe_mul, hJ₁', hJ₁])
    rw [hfact, map_mul, hJ₀] at hprinc
    have hinv := mul_eq_one_iff_eq_inv.mp hprinc
    rw [← inv_inv (ClassGroup.mk0 J₁'), ← hinv, inv_inv]
  · have hcopI : IsCoprime (J₁ : Ideal (𝓞 K)) 𝔫 := by
      rwa [Ideal.isCoprime_iff_sup_eq, sup_comm]
    exact absNorm_coprime_of_isCoprime_span J₁' n (by
      simpa only [hJ₁'] using hcopI)

end Chebotarev
