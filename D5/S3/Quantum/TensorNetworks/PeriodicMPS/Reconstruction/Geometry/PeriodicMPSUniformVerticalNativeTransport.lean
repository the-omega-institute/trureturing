/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalNativeTransport
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalNativeTransport
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Rank transport from native to paired section minors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeCriticalMatrix

open Function Matrix MvPolynomial
open scoped Matrix

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSectionRank

open PeriodicMPSUniformVerticalPrimeExclusion
open UniformNativeCriticalMatrix (criticalMatrix)

noncomputable section

private theorem det_eq_zero_of_native_frame_reindex {A E ι : Type*}
    [CommRing A] [Field E] [Fintype ι] [DecidableEq ι]
    (σ : A →+* E) (hσ : Function.Injective σ) (e : ι ≃ Fin 9)
    (M : Matrix ι ι A) (N : Matrix (Fin 10) (Fin 9) E)
    (L : Matrix ι (Fin 10) E) (C : Matrix ι ι E)
    (hframe : M.map σ = L * (N.submatrix id e) * C)
    (hrank : ∃ v : Fin 9 → E, v ≠ 0 ∧ N *ᵥ v = 0) : M.det = 0 := by
  obtain ⟨v, hv, hNv⟩ := hrank
  apply det_eq_zero_of_native_frame σ hσ M (N.submatrix id e) L C hframe
  refine ⟨v ∘ e, ?_, ?_⟩
  · intro h
    apply hv
    funext k
    obtain ⟨i, rfl⟩ := e.surjective k
    exact congrFun h i
  · funext i
    exact (e.sum_comp (fun k => N i k * v k)).trans (congrFun hNv i)

abbrev TripletIndex := Fin 6 ⊕ Fin 3
abbrev SingletIndex := Fin 6 ⊕ (Fin 2 ⊕ Fin 1)

private def tripletIndexEquiv : TripletIndex ≃ Fin 9 := finSumFinEquiv

private def singletIndexEquiv : SingletIndex ≃ Fin 9 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv


private theorem kernel_of_maximalMinors {E : Type*} [Field E] (N : Matrix (Fin 10) (Fin 9) E)
    (hminors : ∀ d : Fin 10, (N.submatrix d.succAbove id).det = 0) :
    ∃ v : Fin 9 → E, v ≠ 0 ∧ N *ᵥ v = 0 := by
  classical
  by_contra! h
  have hker : LinearMap.ker N.mulVecLin = ⊥ :=
    Matrix.ker_mulVecLin_eq_bot_iff.mpr fun v hz => by
      by_contra hn
      exact h v hn hz
  have hRank : N.rank = 9 := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker),
      Module.finrank_pi, Fintype.card_fin]
  have hSpan : Submodule.span E (Set.range N.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hRank, Module.finrank_pi, Fintype.card_fin]
  obtain ⟨rows, hrows, hdet⟩ :=
    D5.S3.Combinatorics.Matroids.LinearRado.exists_nonsingular_rows N hSpan
  have hnot : ¬ Surjective rows := by
    intro hs
    have hcard := Fintype.card_le_of_surjective rows hs
    norm_num [Fintype.card_fin] at hcard
  obtain ⟨d, hd⟩ := not_forall.mp hnot
  let g : Fin 9 → Fin 9 := fun j =>
    (finSuccAboveEquiv d).symm ⟨rows j, fun he => hd ⟨j, he⟩⟩
  have hg (j : Fin 9) : d.succAbove (g j) = rows j :=
    congrArg Subtype.val ((finSuccAboveEquiv d).apply_symm_apply _)
  have hgi : Injective g := by
    intro a b h
    apply hrows
    rw [← hg a, ← hg b, h]
  let e : Equiv.Perm (Fin 9) := Equiv.ofBijective g ⟨hgi, Finite.injective_iff_surjective.mp hgi⟩
  apply hdet
  have he : N.submatrix rows id = (N.submatrix d.succAbove id).submatrix e id := by
    ext i j
    change N (rows i) j = N (d.succAbove (g i)) j
    rw [hg]
  rw [he, Matrix.det_permute, hminors d, mul_zero]

/-- Vanishing maximal minors of the specialized native chart matrix give
the two section minor vanishing statements once the
moving frame supplies the displayed row and column matrix products. -/
theorem sectionRankImplication_of_nativeCriticalMatrix
    {m : ℕ} (hm : 3 ≤ m) {f : Roots} [IsDomain (DivisorRing f)]
    (htrace : ¬ f ∣ rootSum) (htorus : ∀ i : Fin 4, ¬ f ∣ (X i : Roots))
    {E : Type*} [Field E] [Algebra ℂ E]
    (σ : Polynomial (FractionRing (DivisorRing f)) →+* E) (hσ : Function.Injective σ)
    (hframe : ∀ j : Fin 3, ¬ f ∣ obstruction m j →
      ∃ z : Fin 5 → E,
        let x := genericSection (divisorRoots f) j
        let N := (criticalMatrix m).map (aeval z)
        (∀ d : Fin 10, (N.submatrix d.succAbove id).det = 0) ∧
        (∃ (L : Matrix SingletIndex (Fin 10) E) (C : Matrix SingletIndex SingletIndex E),
          (sectionSingletMinor (1 / 2 : ℂ) m x).map σ =
            L * (N.submatrix id singletIndexEquiv) * C) ∧
        (∃ (L : Matrix TripletIndex (Fin 10) E) (C : Matrix TripletIndex TripletIndex E),
          (sectionTripletMinor (1 / 2 : ℂ) m x).map σ =
            L * (N.submatrix id tripletIndexEquiv) * C)) :
    SectionRankImplication m f := by
  apply sectionRankImplication_of_divisorMinors hm htrace htorus
  intro j hj
  obtain ⟨z, hk, ⟨LS, CS, hS⟩, ⟨LT, CT, hT⟩⟩ := hframe j hj
  have hkernel := kernel_of_maximalMinors _ hk
  exact ⟨det_eq_zero_of_native_frame_reindex σ hσ singletIndexEquiv _ _ LS CS hS hkernel,
    det_eq_zero_of_native_frame_reindex σ hσ tripletIndexEquiv _ _ LT CT hT hkernel⟩

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSectionRank
