/- GID: D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitPassiveCoordinates
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Weighted vector insertion preserves the subset of zero-weight indices. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms

/-! Splitting the weighted insertion equations by their passive indices. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CircuitPassiveCoordinates

open Finset
open UniformCircuitResidueForms
open Set.powersetCard (ofFinEmbEquiv)
open AlternatingMap
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

set_option autoImplicit false

variable {I M N : Type*} [LinearOrder I] [AddCommGroup M] [AddCommGroup N]
variable {d : ℕ}

/-- Keep exactly the form coefficients whose intersection with A is S. -/
noncomputable def project (b : Module.Basis I ℤ M) (A S : Finset I) :
    (M [⋀^Fin d]→ₗ[ℤ] N) →ₗ[ℤ] (M [⋀^Fin d]→ₗ[ℤ] N) :=
  let basis := basisFormEquiv (n := d) (N := N) b
  let mask : (Set.powersetCard I d → N) →ₗ[ℤ] (Set.powersetCard I d → N) :=
    { toFun f F := if F.val ∩ A = S then f F else 0
      map_add' f g := by funext F; by_cases h : F.val ∩ A = S <;> simp [h]
      map_smul' t f := by funext F; by_cases h : F.val ∩ A = S <;> simp [h] }
  basis.toLinearMap.comp (mask.comp basis.symm.toLinearMap)

private lemma project_on_basis (b : Module.Basis I ℤ M) (A S : Finset I)
    (F : Set.powersetCard I d) (f : M [⋀^Fin d]→ₗ[ℤ] N) :
    (basisFormEquiv b).symm (project b A S f) F =
      if F.val ∩ A = S then (basisFormEquiv b).symm f F else 0 := by
  simp [project]

private lemma project_coordinate (b : Module.Basis I ℤ M) (A S F : Finset I)
    (f : M [⋀^Fin d]→ₗ[ℤ] N) :
    formCoordinates b (project b A S f) F =
      if F ∩ A = S then formCoordinates b f F else 0 := by
  by_cases hd : F.card = d
  · simp [formCoordinates, hd, project]
  · simp [formCoordinates, hd]

private lemma project_project (b : Module.Basis I ℤ M) (A S T : Finset I)
    (f : M [⋀^Fin d]→ₗ[ℤ] N) :
    project b A S (project b A T f) = if S = T then project b A T f else 0 := by
  apply (basisFormEquiv b).symm.injective
  funext F
  rw [project_on_basis, project_on_basis]
  by_cases h : S = T
  · subst S
    by_cases hF : F.val ∩ A = T <;> simp [hF, project_on_basis]
  · by_cases hF : F.val ∩ A = S
    · simp [h, hF]
    · simp [h, hF]

private lemma sum_project (b : Module.Basis I ℤ M) (A : Finset I)
    (f : M [⋀^Fin d]→ₗ[ℤ] N) :
    ∑ S : A.powerset, project b A S.val f = f := by
  apply (basisFormEquiv b).symm.injective
  funext F
  let S₀ : A.powerset := ⟨F.val ∩ A, mem_powerset.mpr inter_subset_right⟩
  rw [map_sum, Finset.sum_apply, Fintype.sum_eq_single S₀]
  · simp [project_on_basis, S₀]
  · intro S hS
    rw [project_on_basis, ite_eq_right]
    exact fun h => hS (Subtype.ext h.symm)

/-- When the weights vanish on A, inserting the weighted vector commutes
with projecting to each fixed intersection with A. -/
theorem insertion_project [Fintype I] (b : Module.Basis I ℤ M) (A S : Finset I)
    (weight : I → ℕ) (hweight : ∀ i ∈ A, weight i = 0)
    (f : M [⋀^Fin (d + 1)]→ₗ[ℤ] N) :
    (project b A S f).curryLeft (∑ i, weight i • b i) =
      project b A S (f.curryLeft (∑ i, weight i • b i)) := by
  apply (basisFormEquiv b).symm.injective
  funext T
  let e := ofFinEmbEquiv.symm T
  have he : (ofFinEmbEquiv e).val = T.val := congrArg Subtype.val (ofFinEmbEquiv.apply_symm_apply T)
  have ht (g : M [⋀^Fin d]→ₗ[ℤ] N) :
      (basisFormEquiv b).symm g T = formCoordinates b g T.val := by
    rw [formCoordinates, dite_eq_left (show T.val.card = d from T.prop)]
  rw [ht, ht, project_coordinate, ← ht]
  rw [← ht, basisFormEquiv_symm_apply, basisFormEquiv_symm_apply]
  rw [curryLeft_weighted_basis b _ weight e, curryLeft_weighted_basis b f weight e, he]
  have hface (i : I) (hi : i ∉ A) : insert i T.val ∩ A = T.val ∩ A := by
    ext j
    by_cases hj : j ∈ A
    · have hne : j ≠ i := fun he => hi (he ▸ hj)
      simp [hj, hne]
    · simp [hj]
  by_cases hs : T.val ∩ A = S
  · rw [ite_eq_left hs]
    apply sum_congr rfl
    intro i _
    by_cases hi : i ∈ A
    · simp [hweight i hi]
    · rw [project_coordinate, hface i hi, ite_eq_left hs]
  · rw [ite_eq_right hs]
    apply sum_eq_zero
    intro i _
    by_cases hi : i ∈ A
    · simp [hweight i hi]
    · rw [project_coordinate, hface i hi, ite_eq_right hs, nsmul_zero, smul_zero]

/-- The part of the weighted kernel supported on one intersection with the passive set. -/
noncomputable def sector [Fintype I] (b : Module.Basis I ℤ M) (A S : Finset I)
    (weight : I → ℕ) (n : ℕ) : Submodule ℤ (M [⋀^Fin (d + 1)]→ₗ[ℤ] N) :=
  ((insertVector (∑ i, weight i • b i)).ker ⊓ Submodule.torsionBy ℤ _ (n : ℤ)) ⊓
    (project b A S - LinearMap.id).ker

/-- Weighted insertion and the scalar annihilator split independently over all
intersections with the passive indices. -/
theorem exists_split [Fintype I] (b : Module.Basis I ℤ M)
    (A : Finset I) (weight : I → ℕ) (n : ℕ) (hweight : ∀ i ∈ A, weight i = 0) :
    ∃ e : (↥((insertVector (n := d) (N := N) (∑ i, weight i • b i)).ker ⊓
      Submodule.torsionBy ℤ _ (n : ℤ))) ≃ₗ[ℤ]
      (∀ S : A.powerset, ↥(sector (d := d) (N := N) b A S.val weight n)),
      ∀ f S, (e f S).val = project b A S.val f.val := by
  let w := ∑ i, weight i • b i
  let K := (insertVector (n := d) (N := N) w).ker ⊓ Submodule.torsionBy ℤ _ (n : ℤ)
  have hsector (S : A.powerset) (f : M [⋀^Fin (d + 1)]→ₗ[ℤ] N) :
      f ∈ sector b A S.val weight n ↔ f ∈ K ∧ project b A S.val f = f := by
    change f ∈ K ∧ f ∈ (project b A S.val - LinearMap.id).ker ↔ _
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hproject (S : A.powerset) (f : K) :
      project b A S.val f.val ∈ sector b A S.val weight n := by
    apply (hsector S _).mpr
    have hf : f.val.curryLeft w = 0 ∧ (n : ℤ) • f.val = 0 := f.prop
    constructor
    · change (project b A S.val f.val).curryLeft w = 0 ∧
          (n : ℤ) • project b A S.val f.val = 0
      rw [show w = ∑ i, weight i • b i from rfl,
        insertion_project b A S.val weight hweight, hf.1, _root_.map_zero,
        ← map_smul, hf.2, _root_.map_zero]
      exact ⟨rfl, rfl⟩
    · rw [project_project, ite_eq_left rfl]
  refine ⟨{
    toFun := fun f S => ⟨project b A S.val f.val, hproject S f⟩
    invFun := fun g => ⟨∑ S, (g S).val, K.sum_mem fun S _ => ((hsector S _).mp (g S).prop).1⟩
    left_inv := fun f => Subtype.ext (sum_project b A f.val)
    right_inv := ?_
    map_add' := fun f g => funext fun S => Subtype.ext (map_add (project b A S.val) f.val g.val)
    map_smul' := fun t f => funext fun S => Subtype.ext (map_smul (project b A S.val) t f.val) },
    fun _ _ => rfl⟩
  intro g
  funext S
  apply Subtype.ext
  change project b A S.val (∑ T, (g T).val) = (g S).val
  rw [map_sum, Fintype.sum_eq_single S]
  · exact ((hsector S _).mp (g S).prop).2
  · intro T hT
    conv_lhs => rw [← ((hsector T _).mp (g T).prop).2]
    rw [project_project, ite_eq_right (fun h => hT (Subtype.ext h.symm))]

/-- A coefficient equation restricts only the factor indexed by that face's
intersection with the passive indices. -/
theorem split_with_omitted_faces [Fintype I] (b : Module.Basis I ℤ M)
    (A : Finset I) (weight : I → ℕ) (n : ℕ) (hweight : ∀ i ∈ A, weight i = 0)
    (holes : Set (Set.powersetCard I (d + 1))) :
    let K := (insertVector (n := d) (N := N) (∑ i, weight i • b i)).ker ⊓
      Submodule.torsionBy ℤ _ (n : ℤ)
    let read := fun F : Set.powersetCard I (d + 1) =>
      (LinearMap.proj F).comp (basisFormEquiv (N := N) b).symm.toLinearMap
    let P := K ⊓ ⨅ F : holes, (read F.val).ker
    let Q := fun S : A.powerset => sector b A S.val weight n ⊓
      ⨅ F : {F : holes // F.val.val ∩ A = S.val}, (read F.val.val).ker
    Nonempty (↥P ≃ₗ[ℤ] ∀ S, ↥(Q S)) := by
  dsimp only
  let K := (insertVector (n := d) (N := N) (∑ i, weight i • b i)).ker ⊓
    Submodule.torsionBy ℤ _ (n : ℤ)
  let read := fun F : Set.powersetCard I (d + 1) =>
    (LinearMap.proj F).comp (basisFormEquiv (N := N) b).symm.toLinearMap
  let P := K ⊓ ⨅ F : holes, (read F.val).ker
  let Q := fun S : A.powerset => sector b A S.val weight n ⊓
    ⨅ F : {F : holes // F.val.val ∩ A = S.val}, (read F.val.val).ker
  change Nonempty (↥P ≃ₗ[ℤ] ∀ S, ↥(Q S))
  obtain ⟨e, he⟩ := exists_split (d := d) (N := N) b A weight n hweight
  have hread (f : K) (F : Set.powersetCard I (d + 1)) (S : A.powerset)
      (hS : F.val ∩ A = S.val) : read F (e f S).val = read F f.val := by
    rw [he f S]
    change (basisFormEquiv b).symm (project b A S.val f.val) F = (basisFormEquiv b).symm f.val F
    rw [project_on_basis, ite_eq_left hS]
  have hP (f : K) : f.val ∈ P ↔ ∀ S, (e f S).val ∈ Q S := by
    simp only [P, Q, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      f.prop, (e f _).prop, true_and]
    constructor
    · intro h S F
      exact (hread f F.val.val S F.prop).trans (h F.val)
    · intro h F
      let S : A.powerset := ⟨F.val.val ∩ A, mem_powerset.mpr inter_subset_right⟩
      exact (hread f F.val S rfl).symm.trans (h S ⟨F, rfl⟩)
  let toK : P →ₗ[ℤ] K := P.inclusion inf_le_left
  let forget : (∀ S, ↥(Q S)) →ₗ[ℤ] (∀ S : A.powerset, ↥(sector b A S.val weight n)) :=
    LinearMap.pi fun S => ((Q S).inclusion inf_le_left).comp (LinearMap.proj S)
  have hInv (g : ∀ S, ↥(Q S)) : (e.symm (forget g)).val ∈ P := by
    apply (hP _).mpr
    rw [e.apply_symm_apply]
    exact fun S => (g S).prop
  refine ⟨{
    toFun := fun f S => ⟨(e (toK f) S).val, (hP (toK f)).mp f.prop S⟩
    invFun := fun g => ⟨(e.symm (forget g)).val, hInv g⟩
    left_inv := ?_
    right_inv := ?_
    map_add' := ?_
    map_smul' := ?_ }⟩
  · intro f g
    funext S
    apply Subtype.ext
    change (e (toK (f + g)) S).val = (e (toK f) S).val + (e (toK g) S).val
    rw [map_add, map_add]
    rfl
  · intro t f
    funext S
    apply Subtype.ext
    change (e (toK (t • f)) S).val = t • (e (toK f) S).val
    rw [map_smul, map_smul]
    rfl
  · intro f
    apply Subtype.ext
    change (e.symm (e (toK f))).val = f.val
    rw [e.symm_apply_apply]
    rfl
  · intro g
    funext S
    apply Subtype.ext
    change (e (e.symm (forget g)) S).val = (g S).val
    rw [e.apply_symm_apply]
    rfl

end D5.S3.Combinatorics.Matroids.CircuitPassiveCoordinates
