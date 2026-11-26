import GRH.Lib.General.NumberTheory.FundamentalDomains
import GRH.New.RealPlace.BesselOrthonormal
import GRH.New.Filling.BoxPartition
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: size bookkeeping for the data of this proof.

This file: Explicit covolume of the level-g arithmetic unipotent group in scaled real
coordinates. -/

open Classical ENNReal Finset Fintype Function Matrix MeasureTheory NumberField Sum

attribute [-instance] Pi.instMeasurableConstSMul Pi.measurableSMul

attribute [-simp] Complex.ofReal_div Nat.cast_mul

attribute [local grind] IsFreeEntry

attribute [local simp] FI.level Filling.frameScaleSq prod_eq_zero_iff prod_pow Matrix.mul_apply
  vecMul_fromBlocks div_pow funext_iff mul_assoc mul_sub pow_mul' sub_mul tsub_add_eq_tsub_tsub_swap

/-- Under the standing hypotheses, for every class c and archimedean point y, the integral of
the cutoff β_c(uy) over u in 𝖴_∞, for the product Haar measure, equals the covolume ν, which
does not depend on c. -/
lemma Filling.lintegral_classCutoff_eq_unipCovolume {E} [Field E] [CMType E] [StablyUnram E] {𝔰}
  (S : Filling E 𝔰) c [S.IsAdmissible] (y : _ → _) :
  ∫⁻ u, S.classCutoff c fun v ↦ u v * y v ∂(.pi fun _ ↦ 𝔰.besselHaar) = .ofReal S.unipCovolume := by
  let φ := MonoidHom.mk' (fun (γ : S.classUnip c) v ↦
    (⟨_, γ.2.1.ratToInf_mem_unitriangularOn v⟩ : besselU)) (by aesop)
  have n a (j : Subtype (@IsFreeEntry 𝔰 ⟨a, ·⟩)) : inl a ≠ j.1 ∧ j.1 ≠ eStar a := by grind
  let b := (classBasis c).1
  have ⟨M, e, u⟩ : ∃ m, b = fromBlocks 1 0 0 (fromBlocks m 0 0 1) ∧
    genIndex m.det = 1 / S.N ^ numInfPlaces E := by
    use ?_, by simp [b, classBasis, toBesselH, besselLatticeBasis]; rfl
    obtain _ := congr(genIndex $(c.out.2).det), congr(genIndex $S.piBar_mul_star),
      genIndex_pos c.out.1.det, genIndex_pos S.piBar
    simp_all [genIndex_natCast, ← sq, le_of_lt]
    grind
  let m a := (b.toSquareBlockProp (IsFreeEntry ⟨a, ·⟩))ᵀ
  have d a : (m a).det =
    b.det := by simp [b.twoBlockTriangular_det (IsFreeEntry ⟨a, ·⟩) (by simp [e]; omega), m,
    (by simp [toSquareBlockProp, ← ext_iff, e] : b.toSquareBlockProp (¬IsFreeEntry ⟨a, ·⟩) = 1)]
  have B a l j : (m a *ᵥ l ∘ (↑)) j = (l ᵥ* b) j :=
    sum_of_injective _ Subtype.val_injective _ _ (by revert j; simp [e]; lia) (mul_comm _ <| l ·)
  choose F hF vF uF using fun a ↦ exists_fundamental_domain_classLattice (fun j v ↦
    S.g / S.basisScale v (inl a) * S.basisScale v j.1)
    (by simp [Pi.isUnit_iff]) (.mk'' (m a) (by simp [d, b]))
  choose F' hF' vF' uF' using fun a ↦
    exists_fundamental_domain_im_skew (S.g / S.frameScaleSq · (Fin.val a)) (by simp)
  have p := ((((measurePreserving_sigma (.symm (.subtypeProdEquivSigmaSubtype
    (@IsFreeEntry 𝔰 ⟨·, ·⟩)))).comp measurePreserving_flip).prod measurePreserving_flip).comp
    (measurePreserving_arrowProdEquivProdArrow ..)).comp
    (measurePreserving_pi _ _ fun _ : InfinitePlace E ↦ measurePreserving_freeEntries_besselHaar)
  have hB := (MeasurableSet.univ_pi hF).prod (.univ_pi hF')
  have o := existsUnique_mul_mem_box (V := (fun a ↦ .of (Subtype (IsFreeEntry ⟨a, ·⟩) →
    _)) ⊕ᵥ fun _ ↦ .of _) ((2 * ·.rev) ⊕ᵥ (2 * ·.rev + 1)) (fun u : InfinitePlace E → (𝔰.middleGram
    1).besselU ↦ Sum.rec (fun a j v ↦ (u v).1.1 (inl a) j) fun a v ↦ (freeEntries IsFreeEntry
    (u v).1.1.1).2 a) (fun _ _ e ↦ funext fun v ↦ injective_freeEntries_besselU congr((($e (inl _)
    ⟨_, ·.2⟩ v), swap ($e <| inr ·) v))) φ.range (Sum.rec _ _) (Sum.rec _ _) (Sum.rec uF uF') (by
    rintro (a | a) l ⟨x, hx⟩
    rw [← extend_comp Subtype.val_injective x 0] at hx
    have ⟨γ, H⟩ := exists_eichler_classUnip c a (@extend_val_apply' _ _ _ x 0) (fun j ↦ byCases
      (B a _ ⟨j, ·⟩ ▸ torsionClass_eq_zero.1 hx.1 _) (by revert j; simp +contextual [b, e])) 0
    swap; have ⟨γ, H⟩ := exists_eichler_classUnip c a (l := 0) (by simp) (by simp) ⟨x, hx.1⟩
    all_goals
      use ⟨_, γ, rfl⟩, by simp [← hx.2, φ, basisScale, field, *]
      rintro (b | b) k l <;> simp (disch := clear * - l k; grind) [φ, ite_eq_right, H]) (by
    rintro ⟨u, γ, G⟩ i h
    have R a j : (finAdeleMat ((S.g : E)⁻¹ • (γ.1.1.1 - 1)) (inl a) ᵥ* b) j ∈ Ô E := by
      rw [← mul_apply_eq_vecMul, show _ * _ = b * S.gIdele⁻¹ • ((S.termPosition c ..).1 - 1) by
        simp [b, coe_termPosition, Matrix.map_sub]; rfl]
      simpa [e] using (S.principalLevel_eq_unitaryLevel.le (x := termPosition ..) γ.2.2).2 _ j
    have w v x ⦃a j⦄ (d : i = inr a ∧ j = eStar a ∨ i = inl a ∧ IsFreeEntry (a, j)) :
      (x * u v).1.1 (inl a) j = (u v).1.1 (inl a) j + x.1.1 (inl a) j := by
      simp at h
      clear * - h d
      have r k l : (∀ b, k = inl b → a < b ∨ j = eStar b) → (∀ d, l ≠ eStar d) →
          (u v).1.1 k l = ite (k = l) 1 0 := by simp; grind [by simpa using mem_besselU.1 (u v).2]
      simpa [(by grind : inl a ≠ j), sub_eq_iff_eq_add'] using (sum_eq_zero fun k _ ↦
          mul_eq_zero.2 (or_not.imp (sub_eq_zero_of_eq ∘ x.2 _ k) fun n ↦ by
        have A c (_ : j = eStar c) :=
          congrFun₂ (U.coe_inv IsHermInvolution.mul_self (u v).1 ▸ (u v).1.1.mul_inv) k j
        simp +contextual -dsimp [splitGram, r] at A
        rcases j, k with ⟨_ | _ | _, _ | _ | _⟩ <;> simp at n <;> simp [r, n] at A <;> simp [*]
        grind [Complex.conj_eq_iff_im]) : ((x.1.1.1 - 1) * (_ - 1)) (inl a) j = 0)
    obtain ⟨rfl, a | a⟩ := G, i
    use ⟨_, torsionClass_eq_zero.2 (B a _ · ▸ R a _), by simp [φ, n, field]⟩,
      fun _ ↦ funext₂ fun j ↦ (w · _ (.inr ⟨rfl, j.2⟩))
    use ⟨IsIntegralClosure.mk' _ (_ * _ : E) (algebraMap_mem_Ô.1 (by
      simpa [e] using! R a (eStar a))), RingOfIntegers.ext ((Φ ofNonempty).injective (by
      simpa [φ, basisScale, Complex.ext_iff, self_eq_neg, ← two_mul] using (w ofNonempty
        (φ γ ofNonempty)⁻¹ (.inl ⟨rfl, rfl⟩)).trans congr(_ + $(U.coe_inv IsHermInvolution.mul_self
        _) _ _))), by simp [φ, basisScale, field]⟩, fun x ↦ funext (congr($(w · _ (by simp)).im)))
  have := φ.rangeRestrict_surjective.countable
  apply ((toReal_eq_toReal_iff ..).1 _).resolve_right (by simp [unipCovolume_pos])
  rw [(IsFundamentalDomain.mk' (p.1 hB).inv.nullMeasurableSet (((Equiv.inv _).existsUnique_congr fun
    _ ↦ Sum.forall).1 <| o ·⁻¹)).lintegral_eq_tsum'', ← lintegral_tsum (by fun_prop),
    lintegral_congr fun u ↦ ((φ.ofInjective fun _ ↦ by simp [φ, ← SetLike.coe_eq_coe,
    GeneralLinearGroup.ext_iff, (RingHom.injective _).eq_iff]).tsum_eq _).symm.trans (congr(∑' _,
    S.classCutoff c $(mul_assoc ..)).trans (tsum_classCutoff_eq_one ..)),
    toReal_ofReal S.unipCovolume_pos.le, unipCovolume, ← sum_range_reflect,
    sum_range, frameScaleProd, prod_comm, Fin.prod_univ_castSucc]
  simp [*, volume_pi_pi, ← measureReal_def, Fintype.card_subtype, card_filter,
    basisScale, ↓prod_sum_type, ←
    prod_subtype _ mem_filter_univ, ↓sum_sum_type, prod_filter, filter_lt_eq_Ioi, mul_pow, abs_div,
    pow_right_comm _ _ 2, pow_succ _ (_ + _), prod_pow_eq_pow_sum, ↓p.measure_preimage, prod_ite,
    (by simp; omega : ∀ k (a : Fin 𝔰.ϱ), k + 2 * (𝔰.ϱ - a) = a.rev + (k + 1 + a.rev) + 1)]
  field
