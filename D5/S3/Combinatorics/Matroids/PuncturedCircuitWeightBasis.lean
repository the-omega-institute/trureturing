/- GID: D5/S3/Combinatorics/Matroids/PuncturedCircuitWeightBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PuncturedCircuitWeightBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: A weight basis preserving the omitted subset and its alternating coefficient. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitBasis
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Alternating.Basic

/-! An integral change of coordinates respecting the two sides of an omitted basis. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PuncturedCircuitWeightBasis

open Finset UniformCircuitBasis
set_option autoImplicit false

variable {I : Type*}

private theorem weight_basis_on_set (A : Finset I) (hA : A.Nonempty)
    (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) :
    ∃ (basis : Module.Basis A ℤ (A → ℤ)) (z : A),
      (fun i : A => (weight i : ℤ)) = ((A.gcd weight : ℕ) : ℤ) • basis z := by
  have hcard : 0 < Fintype.card A := by simpa only [Fintype.card_coe] using card_pos.mpr hA
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  let e : A ≃ Fin (k + 1) := Fintype.equivFinOfCardEq hk
  let w := fun i => weight (e.symm i : I)
  obtain ⟨b, hb⟩ := weight_vector_in_basis k w (fun i => hweight _)
  let coords := LinearEquiv.piCongrLeft' ℤ (fun _ : Fin (k + 1) => ℤ) e.symm
  have hgcd : univ.gcd w = A.gcd weight := by
    apply Nat.dvd_antisymm
    · apply Finset.dvd_gcd
      intro i hi
      simpa [w] using (gcd_dvd (f := w) (mem_univ (e ⟨i, hi⟩)))
    · apply Finset.dvd_gcd
      intro i _
      exact gcd_dvd (e.symm i).prop
  refine ⟨(b.map coords).reindex e.symm, e.symm 0, ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply, Module.Basis.map_apply,
    ← map_zsmul, ← hgcd, ← hb]
  funext i
  change (weight i : ℤ) = (weight (e.symm (e i) : I) : ℤ)
  rw [Equiv.symm_apply_apply]

variable [DecidableEq I]

private def partition (H : Finset I) (j : I) (hj : j ∈ H) [Fintype I] :
    Unit ⊕ ((H.erase j : Finset I) ⊕ ((univ \ H : Finset I))) ≃ I where
  toFun
    | .inl _ => j
    | .inr (.inl i) => i
    | .inr (.inr i) => i
  invFun i :=
    if h : i = j then .inl ()
    else if hi : i ∈ H then .inr (.inl ⟨i, mem_erase.mpr ⟨h, hi⟩⟩)
    else .inr (.inr ⟨i, mem_sdiff.mpr ⟨mem_univ _, hi⟩⟩)
  left_inv := by
    rintro (_ | i | i)
    · simp
    · simp [(mem_erase.mp i.prop).1, (mem_erase.mp i.prop).2]
    · have hi := (mem_sdiff.mp i.prop).2
      have hij : (i : I) ≠ j := fun he => hi (he ▸ hj)
      simp [hij, hi]
  right_inv := fun i => by
    by_cases h : i = j
    · simp [h]
    · by_cases hi : i ∈ H <;> simp [h, hi]

private theorem eq_zero_iff_basis_tuple {A J M N : Type*} [Finite J]
    [AddCommGroup M] [AddCommGroup N] (e : J ≃ A)
    (basis : Module.Basis A ℤ M) (f : M [⋀^J]→ₗ[ℤ] N) :
    f = 0 ↔ f (basis ∘ e) = 0 := by
  classical
  letI := Fintype.ofFinite J
  refine ⟨fun hf => by rw [hf]; rfl, fun h => ?_⟩
  apply basis.ext_alternating
  intro v hv
  let p : Equiv.Perm J :=
    Equiv.ofBijective (e.symm ∘ v) (Finite.injective_iff_bijective.mp (e.symm.injective.comp hv))
  have htuple : (fun i => basis (v i)) = (basis ∘ e) ∘ p := by
    funext i
    change basis (v i) = basis (e (e.symm (v i)))
    rw [Equiv.apply_symm_apply]
  rw [htuple, f.map_perm, h, smul_zero]
  rfl

set_option maxHeartbeats 450000 in
/-- The inside and outside weights each lie on one integral basis vector.
The omitted coefficient vanishes in the original basis exactly when it
vanishes in the new basis. -/
theorem exists_punctured_weight_basis [Fintype I] (H : Finset I) (j : I) (hj : j ∈ H)
    (hInside : (H.erase j).Nonempty) (hOutside : (univ \ H).Nonempty)
    (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) :
    ∃ (basis : Module.Basis I ℤ (I → ℤ)) (z outside : I),
      z ∈ H.erase j ∧ outside ∉ H ∧ basis j = Pi.single j 1 ∧
      (fun i => (weight i : ℤ)) =
        (weight j : ℤ) • basis j + (((H.erase j).gcd weight : ℕ) : ℤ) • basis z +
          (((univ \ H).gcd weight : ℕ) : ℤ) • basis outside ∧
      ∀ {J N : Type*} [Finite J] [AddCommGroup N] (e : J ≃ (H.erase j : Finset I))
        (f : (I → ℤ) [⋀^J]→ₗ[ℤ] N),
        f (fun i => Pi.single (e i : I) 1) = 0 ↔ f (fun i => basis (e i : I)) = 0 := by
  classical
  let A := H.erase j
  let B := (univ \ H : Finset I)
  obtain ⟨innerBasis, z, hz⟩ := weight_basis_on_set A hInside weight hweight
  obtain ⟨outerBasis, outside, houtside⟩ := weight_basis_on_set B hOutside weight hweight
  let labels := partition H j hj
  let split :=
    (LinearEquiv.piCongrLeft' ℤ (fun _ : I => ℤ) labels.symm).trans
      (LinearEquiv.sumPiEquivProdPi ℤ Unit (A ⊕ B) (fun _ => ℤ))
  let coords := split.trans
    ((LinearEquiv.piUnique ℤ (fun _ : Unit => ℤ)).prodCongr
      (LinearEquiv.sumPiEquivProdPi ℤ A B (fun _ => ℤ)))
  let axes := (Module.Basis.singleton Unit ℤ).prod (innerBasis.prod outerBasis)
  let basis := (axes.map coords.symm).reindex labels
  have coords_apply (v : I → ℤ) :
      coords v = (v j, (fun i : A => v i, fun i : B => v i)) := rfl
  have basis_apply (x : Unit ⊕ (A ⊕ B)) : coords (basis (labels x)) = axes x := by
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply,
      LinearEquiv.apply_symm_apply]
  have hpivot : coords (basis j) = (1, 0, 0) := by
    change coords (basis (labels (Sum.inl ()))) = _
    rw [basis_apply]
    simp [axes, Function.comp_def]
    rfl
  have hinner (i : A) : coords (basis i) = (0, innerBasis i, 0) := by
    change coords (basis (labels (Sum.inr (Sum.inl i)))) = _
    rw [basis_apply]
    simp [axes, Function.comp_def]
  have houter (i : B) : coords (basis i) = (0, 0, outerBasis i) := by
    change coords (basis (labels (Sum.inr (Sum.inr i)))) = _
    rw [basis_apply]
    simp [axes, Function.comp_def]
  let insertInner : (A → ℤ) →ₗ[ℤ] (I → ℤ) :=
    coords.symm.toLinearMap.comp
      ((LinearMap.inr ℤ ℤ ((A → ℤ) × (B → ℤ))).comp (LinearMap.inl ℤ (A → ℤ) (B → ℤ)))
  have original_inner (i : A) : insertInner ((Pi.basisFun ℤ A) i) = Pi.single (i : I) 1 := by
    apply coords.injective
    change coords (coords.symm (0, (Pi.basisFun ℤ A) i, 0)) = coords (Pi.single (i : I) 1)
    rw [LinearEquiv.apply_symm_apply, coords_apply]
    ext k
    · have hji : j ≠ (i : I) := (mem_erase.mp i.prop).1.symm
      simp [hji]
    · by_cases h : k = i
      · subst k
        simp [Pi.basisFun]
      · have hv : (k : I) ≠ (i : I) := fun he => h (Subtype.ext he)
        simp [Pi.basisFun, Pi.single_apply, h, hv]
    · have hki : (k : I) ≠ (i : I) := fun he =>
        (mem_sdiff.mp k.prop).2 (he.symm ▸ mem_of_mem_erase i.prop)
      simp [hki]
  have adapted_inner (i : A) : insertInner (innerBasis i) = basis i := by
    apply coords.injective
    change coords (coords.symm (0, innerBasis i, 0)) = _
    rw [LinearEquiv.apply_symm_apply, hinner]
  refine ⟨basis, z, outside, z.prop, (mem_sdiff.mp outside.prop).2, ?_, ?_, ?_⟩
  · apply coords.injective
    rw [hpivot, coords_apply]
    ext k
    · simp
    · have hjk : j ≠ (k : I) := (mem_erase.mp k.prop).1.symm
      simp [hjk.symm]
    · have hjk : j ≠ (k : I) := fun he => (mem_sdiff.mp k.prop).2 (he ▸ hj)
      simp [hjk.symm]
  · apply coords.injective
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hpivot, hinner, houter,
      coords_apply]
    change ((weight j : ℤ), (fun i : A => (weight i : ℤ)), (fun i : B => (weight i : ℤ))) = _
    rw [hz, houtside]
    simp [A, B]
  · intro J N _ _ e f
    let restricted := f.compLinearMap insertInner
    have horiginal : restricted (Pi.basisFun ℤ A ∘ e) =
        f (fun i => Pi.single (e i : I) 1) := by
      change f (fun i => insertInner ((Pi.basisFun ℤ A) (e i))) = _
      simp only [original_inner]
    have hadapted : restricted (innerBasis ∘ e) = f (fun i => basis (e i : I)) := by
      change f (fun i => insertInner (innerBasis (e i))) = _
      simp only [adapted_inner]
    rw [← horiginal, ← hadapted, ← eq_zero_iff_basis_tuple e _ restricted,
      ← eq_zero_iff_basis_tuple e _ restricted]

end D5.S3.Combinatorics.Matroids.PuncturedCircuitWeightBasis
