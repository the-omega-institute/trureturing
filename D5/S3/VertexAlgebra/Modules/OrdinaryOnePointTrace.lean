/- GID: D5/S3/VertexAlgebra/Modules/OrdinaryOnePointTrace
   generality: G
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zhu top separation gives coefficientwise independence of ordinary one-point traces. -/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.Finset.Max
import OmegaBuild.Commands

/-!
The ordinary coefficient argument uses the minimum in the support of a putative
relation, following Dong–Li–Mason, [arXiv:q-alg/9703016](https://arxiv.org/abs/q-alg/9703016),
Theorem 8.7. The Zhu top action supplies the separating insertion via Jacobson density.
-/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Modules.OrdinaryOnePointTrace

/-- An algebra element acts as the identity on the chosen simple module and as
zero on all other modules of a finite family of pairwise inequivalent simples. -/
theorem exists_action_id_and_zero
    {K A I : Type*} [Field K] [Ring A] [Algebra K A] [Finite I]
    (W : I → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, Module A (W i)] [∀ i, IsScalarTower K A (W i)]
    [∀ i, FiniteDimensional K (W i)] [∀ i, IsSimpleModule A (W i)]
    (hInequiv : ∀ i j, i ≠ j → ¬ Nonempty (W i ≃ₗ[A] W j)) (k : I) :
    ∃ a : A,
      Module.toModuleEnd K (W k) a = LinearMap.id ∧
        ∀ i, i ≠ k → Module.toModuleEnd K (W i) a = 0 := by
  classical
  letI := Fintype.ofFinite I
  have : Module.Finite (Module.End A (∀ i, W i)) (∀ i, W i) :=
    Module.Finite.of_restrictScalars_finite K _ _
  have hoff (f : Module.End A (∀ i, W i)) (i j : I) (hij : i ≠ j) (v : W i) :
      f (Pi.single i v) j = 0 := by
    let entry := (LinearMap.proj j).comp (f.comp (LinearMap.single A W i))
    have he : entry = 0 :=
      entry.bijective_or_eq_zero.resolve_left fun hb =>
        hInequiv i j hij ⟨LinearEquiv.ofBijective entry hb⟩
    simpa only [entry, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, LinearMap.zero_apply] using LinearMap.congr_fun he v
  have hcoord (f : Module.End A (∀ i, W i)) (x : ∀ i, W i) (j : I) :
      f x j = f (Pi.single j (x j)) j := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, Finset.sum_apply, Fintype.sum_eq_single j]
    intro i hij
    exact hoff f i j hij (x i)
  let p : Module.End (Module.End A (∀ i, W i)) (∀ i, W i) :=
    { toFun := fun x => Pi.single k (x k)
      map_add' := fun x y => (LinearMap.single A W k).map_add (x k) (y k)
      map_smul' := fun f x => by
        change Pi.single k (f x k) = f (Pi.single k (x k))
        funext i
        by_cases hi : i = k
        · subst i
          rw [Pi.single_eq_same, hcoord f x k]
        · rw [Pi.single_eq_of_ne hi, hoff f k i (Ne.symm hi)] }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) p
  have hAct (x : ∀ i, W i) (i : I) : a • x i = Pi.single k (x k) i :=
    congrFun (LinearMap.congr_fun ha x) i
  refine ⟨a, LinearMap.ext (fun v => ?_), fun i hi => LinearMap.ext (fun v => ?_)⟩
  · change a • v = v
    simpa only [Pi.single_eq_same] using hAct (Pi.single k v) k
  · change a • v = 0
    simpa only [Pi.single_eq_same, Pi.single_eq_of_ne hi] using hAct (Pi.single i v) i

section GradedTrace

variable {I V : Type*} [AddCommGroup V] [Module ℂ V]
  {E : I → ℚ → Type*} [∀ i w, AddCommGroup (E i w)] [∀ i w, Module ℂ (E i w)]

/-- The coefficient at weight `w` is the trace of the insertion's zero mode on
that graded space. A common shift by `-c/24` reindexes these coefficients. -/
noncomputable def coefficient
    (zeroMode : ∀ i w, V →ₗ[ℂ] Module.End ℂ (E i w)) (i : I) (w : ℚ) :
    V →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ (E i w)).comp (zeroMode i w)

/-- Ordinary formal one-point traces are independent for a finite family of
finite-dimensional grades bounded below by their Zhu tops, when the top
modules are simple and pairwise inequivalent over the same Zhu algebra. -/
theorem linearIndependent_coefficient [Finite I]
    [∀ i w, FiniteDimensional ℂ (E i w)]
    {A : Type*} [Ring A] [Algebra ℂ A] (lowest : I → ℚ)
    [∀ i, Module A (E i (lowest i))] [∀ i, IsScalarTower ℂ A (E i (lowest i))]
    [∀ i, IsSimpleModule A (E i (lowest i))]
    (zhuClass : V →ₗ[ℂ] A) (hClass : Function.Surjective zhuClass)
    (zeroMode : ∀ i w, V →ₗ[ℂ] Module.End ℂ (E i w))
    (hBelow : ∀ i w, w < lowest i → Subsingleton (E i w))
    (hTop : ∀ i v, zeroMode i (lowest i) v = Module.toModuleEnd ℂ (E i (lowest i)) (zhuClass v))
    (hInequiv : ∀ i j, i ≠ j → ¬ Nonempty (E i (lowest i) ≃ₗ[A] E j (lowest j))) :
    LinearIndependent ℂ (coefficient zeroMode) := by
  classical
  letI := Fintype.ofFinite I
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hj
  let support := Finset.univ.filter (fun i => c i ≠ 0)
  have hmem (i : I) : i ∈ support ↔ c i ≠ 0 := by simp [support]
  obtain ⟨k, hk, hmin⟩ := support.exists_min_image lowest ⟨j, (hmem j).2 hj⟩
  obtain ⟨a, ha, hOther⟩ :=
    exists_action_id_and_zero (K := ℂ) (fun i => E i (lowest i)) hInequiv k
  obtain ⟨v, hv⟩ := hClass a
  have hread : ∑ i, c i * coefficient zeroMode i (lowest k) v = 0 := by
    have h := congrArg (fun f : ℚ → (V →ₗ[ℂ] ℂ) => f (lowest k) v) hc
    simpa only [Finset.sum_apply, LinearMap.sum_apply, Pi.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, Pi.zero_apply, LinearMap.zero_apply] using h
  have hvanish (i : I) (hi : i ≠ k) : c i * coefficient zeroMode i (lowest k) v = 0 := by
    by_cases hz : c i = 0
    · rw [hz, zero_mul]
    rcases lt_or_eq_of_le (hmin i ((hmem i).2 hz)) with hlt | heq
    · have := hBelow i (lowest k) hlt
      have hm : zeroMode i (lowest k) v = 0 := Subsingleton.elim _ _
      rw [coefficient, LinearMap.comp_apply, hm, map_zero, mul_zero]
    · have ht : coefficient zeroMode i (lowest i) v = 0 := by
        rw [coefficient, LinearMap.comp_apply, hTop i v, hv, hOther i hi, map_zero]
      rw [heq, ht, mul_zero]
  have hbottom : coefficient zeroMode k (lowest k) v =
      (Module.finrank ℂ (E k (lowest k)) : ℂ) := by
    rw [coefficient, LinearMap.comp_apply, hTop k v, hv, ha, LinearMap.trace_id]
  have : Nontrivial (E k (lowest k)) := IsSimpleModule.nontrivial A _
  have hdim : (Module.finrank ℂ (E k (lowest k)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  rw [Fintype.sum_eq_single k (fun i hi => hvanish i hi), hbottom] at hread
  exact (mul_ne_zero ((hmem k).1 hk) hdim) hread

end GradedTrace

#print axioms exists_action_id_and_zero
#print axioms linearIndependent_coefficient

end D5.S3.VertexAlgebra.Modules.OrdinaryOnePointTrace
