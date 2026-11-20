/- GID: D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The rank of a character kernel of pairwise inequivalent irreducible representations. -/

import Mathlib.RepresentationTheory.Character

/-!
# Rank of a character kernel

Let `ρ i : Representation k G (W i)`, for `i` in a finite type, be finite-dimensional irreducible
representations of an arbitrary group `G` over an algebraically closed field `k`, pairwise
inequivalent, and let `c i` be nonzero scalars. The functions `x ↦ ∑ i, c i * χ_i (x * y⁻¹)`,
for `y : G`, span a subspace of `G → k` of dimension `∑ i, (dim W i) ^ 2`.

The proof identifies these sections with the images of the operators `(ρ i y⁻¹)_i` under the
linear map `A ↦ (x ↦ ∑ i, c i * tr (ρ i x ∘ A i))` on `Π i, End k (W i)`. The operators
`(ρ i g)_i` span the whole product (Burnside's theorem for a family, obtained from the Jacobson
density theorem on the product module, where pairwise inequivalence and Schur's lemma make every
module endomorphism act by a scalar on each factor), and the weighted trace pairing is
nondegenerate, so this linear map is injective. For a single representation this is Burnside's
theorem read through the trace pairing; surjectivity of the group algebra onto the endomorphisms
of one irreducible representation is
`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.asAlgebraHom_surjective_of_isIrreducible`.
Algebraic closedness enters only through Schur's lemma.

Pairwise inequivalence cannot be dropped: two copies of the trivial representation with
weights `c` give the kernel `(c 0 + c 1) • 1`, of rank at most one in every characteristic and
zero in characteristic two when `c 0 = c 1 = 1`, instead of two.
-/

namespace D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank

open Module Representation
open scoped MonoidAlgebra

variable {k G : Type*} [Field k] [IsAlgClosed k] [Group G]
variable {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, AddCommGroup (W i)]
  [∀ i, Module k (W i)] [∀ i, FiniteDimensional k (W i)]

/-- An endomorphism of a finite product of pairwise inequivalent irreducible representations,
viewed as modules over the group algebra, acts on every factor by a scalar. -/
private theorem exists_scalar_of_end (ρ : ∀ i, Representation k G (W i))
    [∀ i, (ρ i).IsIrreducible] (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j)))
    (φ : Module.End k[G] (∀ i, (ρ i).asModule)) :
    ∃ a : ι → k, ∀ (m : ∀ i, (ρ i).asModule) (i : ι), φ m i = a i • m i := by
  classical
  have hdiag : ∀ i, ∃ a : k, ∀ v : (ρ i).asModule, φ (Pi.single i v) i = a • v := by
    intro i
    obtain ⟨a, ha⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
      (A := k[G]) (V := (ρ i).asModule)).2
      ((LinearMap.proj i).comp (φ.comp (LinearMap.single k[G] (fun j => (ρ j).asModule) i)))
    refine ⟨a, fun v => ?_⟩
    have := LinearMap.congr_fun ha v
    simpa only [Module.algebraMap_end_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single] using this.symm
  have hoff : ∀ i j, i ≠ j → ∀ v : (ρ j).asModule, φ (Pi.single j v) i = 0 := by
    intro i j hij v
    have := hne j i hij.symm
    have : Subsingleton ((ρ j).asModule →ₗ[k[G]] (ρ i).asModule) :=
      (IntertwiningMap.equivLinearMapAsModule (ρ j) (ρ i)).toEquiv.symm.subsingleton
    have := LinearMap.congr_fun (Subsingleton.elim
      ((LinearMap.proj i).comp (φ.comp (LinearMap.single k[G] (fun j => (ρ j).asModule) j))) 0) v
    simpa only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single,
      LinearMap.zero_apply] using this
  choose a ha using hdiag
  refine ⟨a, fun m i => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single m]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · exact ha i (m i)
  · intro j _ hji
    exact hoff i j (Ne.symm hji) (m j)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Burnside's theorem for several pairwise inequivalent irreducible representations: the
operators `(ρ i g)_i` span the whole product of the endomorphism algebras. -/
private theorem span_range_pi_eq_top (ρ : ∀ i, Representation k G (W i))
    [∀ i, (ρ i).IsIrreducible] (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j))) :
    Submodule.span k (Set.range fun g : G => (fun i => ρ i g : ∀ i, Module.End k (W i))) = ⊤ := by
  classical
  have : Module.Finite (Module.End k[G] (∀ i, (ρ i).asModule)) (∀ i, (ρ i).asModule) :=
    Module.Finite.of_restrictScalars_finite k _ _
  rw [eq_top_iff]
  rintro A -
  let A' : ∀ i, Module.End k (ρ i).asModule := fun i => (ρ i).asModuleEquiv.symm.conj (A i)
  let f : Module.End (Module.End k[G] (∀ i, (ρ i).asModule)) (∀ i, (ρ i).asModule) :=
    { toFun := fun m i => A' i (m i)
      map_add' := fun m n => by
        funext i
        exact map_add (A' i) (m i) (n i)
      map_smul' := fun φ m => by
        obtain ⟨a, ha⟩ := exists_scalar_of_end ρ hne φ
        funext i
        change A' i (φ m i) = φ (fun i => A' i (m i)) i
        rw [ha, ha]
        exact map_smul (A' i) (a i) (m i) }
  obtain ⟨r, hr⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := k[G]) f
  let T : k[G] →ₗ[k] ∀ i, Module.End k (W i) :=
    LinearMap.pi fun i => (asAlgebraHom (ρ i)).toLinearMap
  have hT : T r = A := by
    funext i
    refine LinearMap.ext fun v => ?_
    let e : ∀ j, (ρ j).asModule := Pi.single i v
    have := congr_fun (LinearMap.congr_fun hr e) i
    change (r • e) i = A' i (e i) at this
    rw [Pi.smul_apply, show e i = v from Pi.single_eq_same i v] at this
    exact this
  have hspan : ∀ s : k[G], T s ∈ Submodule.span k
      (Set.range fun g : G => (fun i => ρ i g : ∀ i, Module.End k (W i))) := by
    intro s
    induction s using MonoidAlgebra.induction_linear with
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | single g t =>
      have : T (MonoidAlgebra.single g t) = t • fun i => ρ i g := by
        funext i
        simp only [T, LinearMap.pi_apply, AlgHom.toLinearMap_apply, asAlgebraHom_single,
          Pi.smul_apply]
      rw [this]
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨g, rfl⟩)
  rw [← hT]
  exact hspan r

/-- The weighted trace pairing `(B, A) ↦ ∑ i, c i * tr (B i ∘ A i)` on a finite product of
endomorphism algebras. -/
private noncomputable def tracePairing (c : ι → k) :
    (∀ i, Module.End k (W i)) →ₗ[k] (∀ i, Module.End k (W i)) →ₗ[k] k :=
  LinearMap.mk₂ k (fun B A => ∑ i, c i * LinearMap.trace k (W i) (B i * A i))
    (fun B₁ B₂ A => by
      simp only [Pi.add_apply, add_mul, map_add, mul_add, Finset.sum_add_distrib])
    (fun t B A => by
      simp only [Pi.smul_apply, smul_mul_assoc, map_smul, smul_eq_mul, Finset.mul_sum,
        mul_left_comm])
    (fun B A₁ A₂ => by
      simp only [Pi.add_apply, mul_add, map_add, Finset.sum_add_distrib])
    (fun t B A => by
      simp only [Pi.smul_apply, mul_smul_comm, map_smul, smul_eq_mul, Finset.mul_sum,
        mul_left_comm])

omit [IsAlgClosed k] in
/-- With nonzero weights the trace pairing is nondegenerate in its second argument. -/
private theorem eq_zero_of_tracePairing (c : ι → k) (hc : ∀ i, c i ≠ 0)
    (A : ∀ i, Module.End k (W i)) (h : ∀ B, tracePairing c B A = 0) : A = 0 := by
  classical
  funext j
  by_contra hA
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hA
  obtain ⟨φ, hφ⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff k (A j v)).1 hv)
  have h1 := h (Pi.single j (φ.smulRight v))
  have h2 : LinearMap.trace k (W j) (φ.smulRight v * A j) = φ (A j v) := by
    rw [show φ.smulRight v * A j = (φ ∘ₗ A j).smulRight v from LinearMap.ext fun w => rfl,
      LinearMap.trace_smulRight]
    rfl
  rw [tracePairing, LinearMap.mk₂_apply, Finset.sum_eq_single j, Pi.single_eq_same, h2] at h1
  · exact mul_ne_zero (hc j) hφ h1
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, zero_mul, map_zero, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- For pairwise inequivalent finite-dimensional irreducible representations `ρ i` over an
algebraically closed field and nonzero weights `c i`, the kernel
`(x, y) ↦ ∑ i, c i * χ_i (x * y⁻¹)` has rank `∑ i, (dim W i) ^ 2`: its sections span a space of
that dimension. -/
theorem finrank_span_sum_character_kernel (ρ : ∀ i, Representation k G (W i))
    [∀ i, (ρ i).IsIrreducible] (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j)))
    (c : ι → k) (hc : ∀ i, c i ≠ 0) :
    Module.finrank k (Submodule.span k
      (Set.range fun y : G => fun x : G => ∑ i, c i * (ρ i).character (x * y⁻¹))) =
      ∑ i, Module.finrank k (W i) ^ 2 := by
  let Φ : (∀ i, Module.End k (W i)) →ₗ[k] G → k :=
    LinearMap.pi fun x => tracePairing c (fun i => ρ i x)
  have hsec : (fun y : G => fun x : G => ∑ i, c i * (ρ i).character (x * y⁻¹)) =
      Φ ∘ (fun g : G => (fun i => ρ i g : ∀ i, Module.End k (W i))) ∘ (·⁻¹) := by
    funext y x
    simp only [Φ, tracePairing, LinearMap.pi_apply, LinearMap.mk₂_apply, Function.comp_apply,
      Representation.character, map_mul]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro A hA
    have hext := LinearMap.ext_on_range (span_range_pi_eq_top ρ hne)
      (f := (tracePairing c).flip A) (g := 0) (fun g => congr_fun hA g)
    exact eq_zero_of_tracePairing c hc A fun B => LinearMap.congr_fun hext B
  rw [hsec, Set.range_comp, inv_surjective.range_comp, Submodule.span_image,
    span_range_pi_eq_top ρ hne, Submodule.map_top, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.finrank_linearMap, sq]

end D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
