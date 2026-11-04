/- GID: D5/S3/VertexAlgebra/Lattice/NormFourTensorEmbedding
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourTensorEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Injective actual vacuum-descendant and commutant tensor intertwiner. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
import D5.S3.VertexAlgebra.Lattice.NormFourFullCommutant
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The actual minus-one product embeds the algebraic tensor product of the
norm-four cyclic vacuum space and its literal production commutant. The
norm-four construction retains the Dong-Mason-Zhu and Shimakura attribution;
the lattice and residue calculus retain the Bakalov-Kac, Carnahan and
Matsuo-Nagatomo attribution of the imported sources. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourTensorEmbedding

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualStateFieldCalculus NormFourVirasoroVector NormFourVacuumIrreducible
open NormFourVacuumVertexAlgebra
open scoped BigOperators VertexOperator TensorProduct

open private components_mem assemble eigen_in_grade eigen_shift grade_eigen grade_zero
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
open private finite_decomposition coefficient_val grade_zero_line axisState axis_modes
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

noncomputable section

private def productPair (D : LatticeData) (a : Charge D) (s : ℂ) :
    vacuumDescendants D a s →ₗ[ℂ] NormFourCommutant.space D a s →ₗ[ℂ] Carrier D where
  toFun u :=
    { toFun := fun c => mu D c.val (-1) u.val
      map_add' := by intro c d; simp [mu]
      map_smul' := by intro t c; simp [mu] }
  map_add' u v := by
    apply LinearMap.ext
    intro c
    exact map_add ((Y D c.val)[[-1]]) u.val v.val
  map_smul' t u := by
    apply LinearMap.ext
    intro c
    exact map_smul ((Y D c.val)[[-1]]) t u.val

/-- The actual c-left minus-one product on the full algebraic tensor product. -/
def tensorMap (D : LatticeData) (a : Charge D) (s : ℂ) :
    (vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) →ₗ[ℂ] Carrier D :=
  TensorProduct.lift (productPair D a s)

private theorem tensorMap_tmul (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : vacuumDescendants D a s) (c : NormFourCommutant.space D a s) :
    tensorMap D a s (u ⊗ₜ[ℂ] c) = mu D c.val (-1) u.val := rfl

private theorem product_commutes (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : vacuumDescendants D a s) (c : NormFourCommutant.space D a s)
    (p : ℤ) (v : Carrier D) :
    mu D u.val p (mu D c.val (-1) v) =
      mu D c.val (-1) (mu D u.val p v) := by
  have hc : c.val ∈ NormFourFullCommutant.fullStateCommutant D a s := by
    rw [← NormFourFullCommutant.space_eq_full_state_commutant]
    exact c.property
  have comm : ((Y D u.val)[[p]]) * ((Y D c.val)[[-1]]) -
      ((Y D c.val)[[-1]]) * ((Y D u.val)[[p]]) = 0 := by
    rw [mode_commutator]
    have vanish (j : ℕ) : commutatorTerm D u.val c.val p (-1) j = 0 := by
      simp [commutatorTerm, hc u.val u.property (j : ℤ) (by omega)]
    simp only [vanish, finsum_zero]
  exact sub_eq_zero.mp (LinearMap.congr_fun comm v)

private theorem full_intertwining (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u : vacuumDescendants D a s) (p : ℤ)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) :
    tensorMap D a s (TensorProduct.map
      (((vertexAlgebra D a ha s hs).stateField u)[[p]]) LinearMap.id z) =
      mu D u.val p (tensorMap D a s z) := by
  induction z using TensorProduct.inductionOn with
  | tmul v c =>
      rw [TensorProduct.map_tmul, tensorMap_tmul, tensorMap_tmul]
      change mu D c.val (-1)
        ((((vertexAlgebra D a ha s hs).stateField u)[[p]]) v).val = _
      have hv : ((((vertexAlgebra D a ha s hs).stateField u)[[p]]) v).val =
          ((Y D u.val)[[p]]) v.val := coefficient_val D a ha s hs u v p
      rw [hv]
      exact (product_commutes D a s u c p v.val).symm
  | add x y hx hy => simpa only [mu, map_add] using congrArg₂ (· + ·) hx hy

private def axisTensor (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (m : ℤ) :
    Module.End ℂ (vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) :=
  TensorProduct.map (restrictedMode D a ha s hs m) LinearMap.id

private theorem axis_intertwining (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (m : ℤ)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) :
    tensorMap D a s (axisTensor D a ha s hs m z) =
      mode D a s m (tensorMap D a s z) := by
  have h := full_intertwining D a ha s hs (axisState D a ha s hs) (m + 1) z
  rw [axis_modes] at h
  exact h

private def coordinates (D : LatticeData) (a : Charge D) (s : ℂ) :
    (vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) ≃ₗ[ℂ]
      (Module.Free.ChooseBasisIndex ℂ (NormFourCommutant.space D a s) →₀
        vacuumDescendants D a s) :=
  TensorProduct.equivFinsuppOfBasisRight
    (Module.Free.chooseBasis ℂ (NormFourCommutant.space D a s))

private theorem coordinates_map (D : LatticeData) (a : Charge D) (s : ℂ)
    (A : Module.End ℂ (vacuumDescendants D a s))
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s)
    (i : Module.Free.ChooseBasisIndex ℂ (NormFourCommutant.space D a s)) :
    coordinates D a s (TensorProduct.map A LinearMap.id z) i =
      A (coordinates D a s z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul u c =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, coordinates,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

private theorem coordinate_nonzero (D : LatticeData) (a : Charge D) (s : ℂ)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) (hz : z ≠ 0) :
    ∃ i, (coordinates D a s z i).val ≠ 0 := by
  by_contra! h
  apply hz
  apply (coordinates D a s).injective
  rw [map_zero]
  exact Finsupp.ext fun i => Subtype.ext (h i)

private theorem coordinate_eigen (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (h : ℂ)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s)
    (hz : axisTensor D a ha s hs 0 z = h • z)
    (i : Module.Free.ChooseBasisIndex ℂ (NormFourCommutant.space D a s)) :
    mode D a s 0 (coordinates D a s z i).val =
      h • (coordinates D a s z i).val := by
  have eq := congrArg (fun t => coordinates D a s t i) hz
  rw [axisTensor, coordinates_map, map_smul, Finsupp.smul_apply] at eq
  exact congrArg Subtype.val eq

private theorem tensor_eigen_shift (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (h : ℂ)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s)
    (hz : axisTensor D a ha s hs 0 z = h • z) (m : ℤ) :
    axisTensor D a ha s hs 0 (axisTensor D a ha s hs m z) =
      (h - (m : ℂ)) • axisTensor D a ha s hs m z := by
  apply (coordinates D a s).injective
  apply Finsupp.ext
  intro i
  simp only [axisTensor, coordinates_map, map_smul, Finsupp.smul_apply]
  apply Subtype.ext
  exact eigen_shift D a ha s hs h _ (coordinate_eigen D a ha s hs h z hz i) m

private theorem tensor_decomposition (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) :
    ∃ f : ℕ →₀ (vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s),
      (∑ n ∈ f.support, f n) = z ∧
      ∀ n, axisTensor D a ha s hs 0 (f n) = (n : ℂ) • f n := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul u c =>
      obtain ⟨f, hf, hg⟩ := finite_decomposition D a s u
      let L : vacuumDescendants D a s →ₗ[ℂ]
          (vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) :=
        (TensorProduct.mk ℂ _ _).flip c
      let g := Finsupp.mapRange.linearMap L f
      refine ⟨g, ?_, ?_⟩
      · change g.sum (fun _ t => t) = _
        change (Finsupp.mapRange L L.map_zero f).sum (fun _ t => t) = _
        rw [Finsupp.sum_mapRange_index (by intro i; rfl)]
        have eq := congrArg L hf
        change (∑ n ∈ f.support, L (f n)) = L u
        simpa only [map_sum, Finsupp.sum] using eq
      · intro n
        change restrictedMode D a ha s hs 0 (f n) ⊗ₜ[ℂ] c =
          (n : ℂ) • ((f n) ⊗ₜ[ℂ] c)
        have he : restrictedMode D a ha s hs 0 (f n) = (n : ℂ) • f n :=
          Subtype.ext (grade_eigen D a ha s hs n (f n).val (hg n))
        rw [he, TensorProduct.smul_tmul']
  | add x y hx hy =>
      obtain ⟨f, hf, hfg⟩ := hx
      obtain ⟨g, hg, hgg⟩ := hy
      refine ⟨f + g, ?_, ?_⟩
      · change (f + g).sum (fun _ t => t) = _
        rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
        exact congrArg₂ (· + ·) hf hg
      · intro n
        simp only [Finsupp.add_apply, map_add, hfg, hgg, smul_add]

-- The existing ambient finite spectral projector is applied only to F-images.
private theorem kernel_has_grade (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s)
    (hz : tensorMap D a s z = 0) (hnz : z ≠ 0) :
    ∃ n : ℕ, ∃ w : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s,
      tensorMap D a s w = 0 ∧ axisTensor D a ha s hs 0 w = (n : ℂ) • w ∧ w ≠ 0 := by
  classical
  obtain ⟨f, hf, he⟩ := tensor_decomposition D a ha s hs z
  let g := Finsupp.mapRange.linearMap (tensorMap D a s) f
  have ge : ∀ n, mode D a s 0 (g n) = (n : ℂ) • g n := by
    intro n
    change mode D a s 0 (tensorMap D a s (f n)) =
      (n : ℂ) • tensorMap D a s (f n)
    rw [← axis_intertwining D a ha s hs 0 (f n), he, map_smul]
  have gz : assemble D g = 0 := by
    have eq := congrArg (tensorMap D a s) hf
    rw [hz] at eq
    change g.sum (fun _ v => v) = 0
    change (Finsupp.mapRange (tensorMap D a s) (map_zero _) f).sum (fun _ v => v) = 0
    rw [Finsupp.sum_mapRange_index (by intro i; rfl)]
    simpa only [map_sum, Finsupp.sum] using eq
  have projected := components_mem D a s g ge (⊥ : Submodule ℂ (Carrier D))
    (by
      intro v hv
      have zero : v = 0 := by simpa using hv
      rw [zero, map_zero]
      exact Submodule.zero_mem _)
    (by rw [gz]; exact Submodule.zero_mem _)
  have some : ∃ n, f n ≠ 0 := by
    by_contra! zero
    apply hnz
    rw [← hf, show f = 0 from Finsupp.ext zero]
    simp
  obtain ⟨n, hn⟩ := some
  exact ⟨n, f n, by simpa [g] using projected n, he n, hn⟩

private theorem tensor_grade_zero (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s)
    (hz : axisTensor D a ha s hs 0 z = (0 : ℂ) • z) :
    ∃ c : NormFourCommutant.space D a s,
      z = (vertexAlgebra D a ha s hs).vacuum ⊗ₜ[ℂ] c := by
  classical
  have line (i : Module.Free.ChooseBasisIndex ℂ (NormFourCommutant.space D a s)) :
      ∃ t : ℂ, t • (vertexAlgebra D a ha s hs).vacuum = coordinates D a s z i := by
    apply Submodule.mem_span_singleton.mp
    by_cases hi : (coordinates D a s z i).val = 0
    · rw [show coordinates D a s z i = 0 from Subtype.ext hi]
      exact Submodule.zero_mem _
    · obtain ⟨n, hn, weight⟩ := eigen_in_grade D a ha s hs 0
        (coordinates D a s z i).val (coordinates D a s z i).property hi
        (coordinate_eigen D a ha s hs 0 z hz i)
      have nzero : n = 0 := by exact_mod_cast weight.symm
      subst n
      have hg : coordinates D a s z i ∈ grade D a s 0 := hn
      rw [grade_zero_line D a ha s hs] at hg
      exact hg
  choose t ht using line
  let b := Module.Free.chooseBasis ℂ (NormFourCommutant.space D a s)
  let f := coordinates D a s z
  refine ⟨∑ i ∈ f.support, t i • b i, ?_⟩
  calc
    z = (coordinates D a s).symm f := ((coordinates D a s).symm_apply_apply z).symm
    _ = ∑ i ∈ f.support, f i ⊗ₜ[ℂ] b i :=
      TensorProduct.equivFinsuppOfBasisRight_symm_apply b f
    _ = ∑ i ∈ f.support, (vertexAlgebra D a ha s hs).vacuum ⊗ₜ[ℂ] (t i • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show f i = t i • (vertexAlgebra D a ha s hs).vacuum from (ht i).symm,
        TensorProduct.smul_tmul]
    _ = _ := (TensorProduct.tmul_sum _ _ _).symm

private theorem vacuum_image (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (c : NormFourCommutant.space D a s) :
    tensorMap D a s ((vertexAlgebra D a ha s hs).vacuum ⊗ₜ[ℂ] c) = c.val := by
  rw [tensorMap_tmul]
  exact stateField_creation D c.val

private theorem tensor_injective (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    Function.Injective (tensorMap D a s) := by
  classical
  apply (injective_iff_map_eq_zero (tensorMap D a s)).mpr
  intro z hz
  by_contra hnz
  let P : ℕ → Prop := fun n =>
    ∃ w : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s,
      tensorMap D a s w = 0 ∧ axisTensor D a ha s hs 0 w = (n : ℂ) • w ∧ w ≠ 0
  have some : ∃ n, P n := kernel_has_grade D a ha s hs z hz hnz
  let n := Nat.find some
  obtain ⟨w, hw, he, hne⟩ := Nat.find_spec some
  change axisTensor D a ha s hs 0 w = (n : ℂ) • w at he
  have minimal : ∀ j, P j → n ≤ j := fun j hj => Nat.find_min' some hj
  have positive : ∀ m : ℤ, 0 < m → axisTensor D a ha s hs m w = 0 := by
    intro m hm
    by_contra image_ne
    obtain ⟨i, hi⟩ := coordinate_nonzero D a s _ image_ne
    have shifted := tensor_eigen_shift D a ha s hs (n : ℂ) w he m
    obtain ⟨j, _, weight⟩ := eigen_in_grade D a ha s hs ((n : ℂ) - (m : ℂ))
      (coordinates D a s (axisTensor D a ha s hs m w) i).val
      (coordinates D a s (axisTensor D a ha s hs m w) i).property hi
      (coordinate_eigen D a ha s hs _ _ shifted i)
    have integer_weight : (n : ℤ) - m = (j : ℤ) := by
      have hc : (((n : ℤ) - m : ℤ) : ℂ) = ((j : ℤ) : ℂ) := by
        simpa only [Int.cast_sub, Int.cast_natCast] using weight
      exact_mod_cast hc
    have lower := minimal j ⟨axisTensor D a ha s hs m w,
      by rw [axis_intertwining, hw, map_zero], by rw [← weight]; exact shifted, image_ne⟩
    omega
  obtain ⟨i, hi⟩ := coordinate_nonzero D a s w hne
  have nzero : n = 0 := by
    have roots := NormFourHighestWeight.highest_weight_values D a ha s hs (n : ℂ)
      (coordinates D a s w i).val hi (coordinate_eigen D a ha s hs _ _ he i) (by
        intro m hm
        have eq := congrArg (fun t => coordinates D a s t i) (positive m hm)
        rw [axisTensor, coordinates_map, map_zero, Finsupp.zero_apply] at eq
        exact congrArg Subtype.val eq)
    have natural_gap : (n : ℝ) = 0 ∨ 1 ≤ (n : ℝ) := by
      by_cases hn : n = 0
      · left; simp [hn]
      · right; exact_mod_cast (show 1 ≤ n by omega)
    rcases roots with zero | sixteenth | half
    · exact_mod_cast zero
    · have re := congrArg Complex.re sixteenth
      norm_num at re
      rcases natural_gap with hz | hp <;> linarith
    · have re := congrArg Complex.re half
      norm_num at re
      rcases natural_gap with hz | hp <;> linarith
  obtain ⟨c, hc⟩ := tensor_grade_zero D a ha s hs w
    (by simpa only [nzero, Nat.cast_zero] using he)
  have czero : c = 0 := Subtype.ext (by
    rw [hc, vacuum_image] at hw
    exact hw)
  apply hne
  rw [hc, czero, TensorProduct.tmul_zero]

/-- The actual algebraic tensor embedding on the literal two production
subspaces, with all S-state integer coefficients and the actual vacuum line. -/
theorem actual_tensor_embedding (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := vacuumDescendants D a s
    let C := NormFourCommutant.space D a s
    let V := vertexAlgebra D a ha s hs
    let F := tensorMap D a s
    Function.Injective F ∧
    (∀ (u : S) (c : C), F (u ⊗ₜ[ℂ] c) = mu D c.val (-1) u.val) ∧
    (∀ (u : S) (p : ℤ) (z : S ⊗[ℂ] C),
      F (TensorProduct.map ((V.stateField u)[[p]]) LinearMap.id z) =
        mu D u.val p (F z)) ∧
    ∀ c : C, F (V.vacuum ⊗ₜ[ℂ] c) = c.val :=
  ⟨tensor_injective D a ha s hs, tensorMap_tmul D a s,
    full_intertwining D a ha s hs, vacuum_image D a ha s hs⟩

end
end D5.S3.VertexAlgebra.Lattice.NormFourTensorEmbedding
