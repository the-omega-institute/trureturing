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

private theorem projectDecomposition (b : Module.Basis I ℤ M) (A : Finset I)
    (K : Submodule ℤ (M [⋀^Fin d]→ₗ[ℤ] N))
    (hK : ∀ (f : K) (S : A.powerset), project b A S.val f.val ∈ K) :
    ∃ e : ↥K ≃ₗ[ℤ] (∀ S : A.powerset, ↥(K ⊓ (project b A S.val - LinearMap.id).ker)),
      ∀ f S, (e f S).val = project b A S.val f.val := by
  have hsector (S : A.powerset) (f : M [⋀^Fin d]→ₗ[ℤ] N) :
      f ∈ K ⊓ (project b A S.val - LinearMap.id).ker ↔ f ∈ K ∧ project b A S.val f = f := by
    change f ∈ K ∧ f ∈ (project b A S.val - LinearMap.id).ker ↔ _
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hproject (S : A.powerset) (f : K) :
      project b A S.val f.val ∈ K ⊓ (project b A S.val - LinearMap.id).ker := by
    apply (hsector S _).mpr
    refine ⟨hK f S, ?_⟩
    rw [project_project, ite_eq_left rfl]
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

private def pairFamilies {J : Type*} (X Y : J → Type*)
    [∀ j, AddCommGroup (X j)] [∀ j, AddCommGroup (Y j)] :
    ((∀ j, X j) × (∀ j, Y j)) ≃ₗ[ℤ] (∀ j, X j × Y j) where
  toFun f j := (f.1 j, f.2 j)
  invFun f := (fun j => (f j).1, fun j => (f j).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- For restrictions acting on disjoint factors, the unrestricted product
times the doubly restricted product equals the product of the two
individually restricted modules. -/
theorem independent_restrictions_product {J : Type*} (X : J → Type*)
    [∀ j, AddCommGroup (X j)] (P Q : ∀ j, Submodule ℤ (X j))
    (hdisjoint : ∀ j, P j = ⊤ ∨ Q j = ⊤) :
    Nonempty (((∀ j, X j) × (∀ j, ↥(P j ⊓ Q j))) ≃ₗ[ℤ]
      ((∀ j, ↥(P j)) × (∀ j, ↥(Q j)))) := by
  classical
  have component (j : J) : Nonempty ((X j × ↥(P j ⊓ Q j)) ≃ₗ[ℤ] (↥(P j) × ↥(Q j))) := by
    rcases hdisjoint j with hp | hq
    · rw [hp, top_inf_eq]
      exact ⟨Submodule.topEquiv.symm.prodCongr (LinearEquiv.refl ℤ _)⟩
    · rw [hq, inf_top_eq]
      exact ⟨(LinearEquiv.prodComm ℤ _ _).trans
        ((LinearEquiv.refl ℤ _).prodCongr Submodule.topEquiv.symm)⟩
  exact ⟨(pairFamilies X (fun j => ↥(P j ⊓ Q j))).trans
    ((LinearEquiv.piCongrRight fun j => (component j).some).trans
      (pairFamilies (fun j => ↥(P j)) (fun j => ↥(Q j))).symm)⟩

private def piSubmoduleEquiv {J : Type*} {X : J → Type*} [∀ j, AddCommGroup (X j)]
    (P : ∀ j, Submodule ℤ (X j)) : ↥(Submodule.pi Set.univ P) ≃ₗ[ℤ] ∀ j, ↥(P j) where
  toFun f j := ⟨f.val j, f.prop j (Set.mem_univ j)⟩
  invFun f := ⟨fun j => (f j).val, fun j _ => (f j).prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- If two coefficients have different intersections with the zero-weight
indices, their individual and joint kernels satisfy the product identity
for restrictions on distinct factors. -/
theorem separated_coefficients_product (b : Module.Basis I ℤ M) (A : Finset I)
    (K : Submodule ℤ (M [⋀^Fin d]→ₗ[ℤ] N))
    (hK : ∀ (f : K) (S : A.powerset), project b A S.val f.val ∈ K)
    (F G : Set.powersetCard I d) (hsep : F.val ∩ A ≠ G.val ∩ A) :
    let read := fun H : Set.powersetCard I d =>
      (LinearMap.proj H).comp ((basisFormEquiv (N := N) b).symm.toLinearMap.comp K.subtype)
    Nonempty ((↥K × ↥((read F).ker ⊓ (read G).ker)) ≃ₗ[ℤ] (↥(read F).ker × ↥(read G).ker)) := by
  intro read
  let part (S : A.powerset) := K ⊓ (project b A S.val - LinearMap.id).ker
  obtain ⟨e, he⟩ := projectDecomposition b A K hK
  let X (S : A.powerset) := ↥(part S)
  let Q (H : Set.powersetCard I d) (S : A.powerset) : Submodule ℤ (X S) :=
    if H.val ∩ A = S.val then
      ((LinearMap.proj H).comp ((basisFormEquiv b).symm.toLinearMap.comp
        (part S).subtype)).ker
    else ⊤
  have hQ (H : Set.powersetCard I d) :
      (read H).ker = (Submodule.pi Set.univ (Q H)).comap e.toLinearMap := by
    ext f
    change read H f = 0 ↔ ∀ S : A.powerset, S ∈ Set.univ → e f S ∈ Q H S
    have read_at (S : A.powerset) (hs : H.val ∩ A = S.val) :
        (basisFormEquiv b).symm (e f S).val H = read H f := by
      rw [he f S, project_on_basis, ite_eq_left hs]
      rfl
    constructor
    · intro h S _
      by_cases hs : H.val ∩ A = S.val
      · simp only [Q, ite_eq_left hs, LinearMap.mem_ker]
        exact (read_at S hs).trans h
      · simp [Q, hs]
    · intro h
      let S : A.powerset := ⟨H.val ∩ A, mem_powerset.mpr inter_subset_right⟩
      have hS := h S (Set.mem_univ S)
      simp only [Q, ite_eq_left (show H.val ∩ A = S.val from rfl), LinearMap.mem_ker] at hS
      exact (read_at S rfl).symm.trans hS
  have hBoth : (read F).ker ⊓ (read G).ker =
      (Submodule.pi Set.univ (fun S => Q F S ⊓ Q G S)).comap e.toLinearMap := by
    rw [hQ F, hQ G]
    ext f
    change (∀ S : A.powerset, S ∈ Set.univ → e f S ∈ Q F S) ∧
      (∀ S : A.powerset, S ∈ Set.univ → e f S ∈ Q G S) ↔
      ∀ S : A.powerset, S ∈ Set.univ → e f S ∈ Q F S ⊓ Q G S
    simp only [Submodule.mem_inf, Set.mem_univ, true_implies, forall_and]
  have hd (S : A.powerset) : Q F S = ⊤ ∨ Q G S = ⊤ := by
    by_cases hs : F.val ∩ A = S.val
    · exact Or.inr (ite_eq_right (fun hg => hsep (hs.trans hg.symm)))
    · exact Or.inl (ite_eq_right hs)
  let one (H : Set.powersetCard I d) : ↥(read H).ker ≃ₗ[ℤ] ∀ S, ↥(Q H S) :=
    (LinearEquiv.ofEq _ _ (hQ H)).trans
      ((e.ofSubmodule' (Submodule.pi Set.univ (Q H))).trans (piSubmoduleEquiv (Q H)))
  let both : ↥((read F).ker ⊓ (read G).ker) ≃ₗ[ℤ] ∀ S, ↥(Q F S ⊓ Q G S) :=
    (LinearEquiv.ofEq _ _ hBoth).trans
      ((e.ofSubmodule' _).trans (piSubmoduleEquiv (fun S => Q F S ⊓ Q G S)))
  obtain ⟨square⟩ := independent_restrictions_product X (Q F) (Q G) hd
  exact ⟨(e.prodCongr both).trans (square.trans ((one F).symm.prodCongr (one G).symm))⟩

end D5.S3.Combinatorics.Matroids.CircuitPassiveCoordinates
