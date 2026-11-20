/- GID: D5/S3/FiniteGroups/GroupAlgebra/PositiveDefiniteClassFunction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PositiveDefiniteClassFunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive semidefinite class functions of finite rank are positive sums of characters. -/

import D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Positive semidefinite class functions of finite rank

Let `G` be an arbitrary group, with no topology, and let `φ : G → ℂ` be a class function whose
kernel `(x, y) ↦ φ (x * y⁻¹)` is positive semidefinite and whose sections
`x ↦ φ (x * y⁻¹)`, for `y : G`, span a finite-dimensional space. Then `φ` is a combination
`∑ i, c i * χ_i` with positive real weights of the characters of finitely many pairwise
inequivalent irreducible representations `ρ i` on Euclidean spaces, acting by isometries; every
matrix coefficient of every `ρ i` lies in the span of the sections, and the dimension of that
span is `∑ i, (dim ρ i) ^ 2`.

The proof runs as follows.

* The reproducing kernel Hilbert space `H` of the kernel (`RKHS.OfKernel`) is spanned by its
  kernel functions `k y`, since these span a finite-dimensional, hence closed, dense subspace;
  the evaluation map identifies `H` with the span of the sections. Right translation
  `(π g h) x = h (x * g)` maps `k y` to `k (y * g⁻¹)` and preserves inner products, because the
  kernel is right invariant. Reproducing gives `φ x = ⟪k 1, π x (k 1)⟫`.
* By strong induction on the dimension, splitting off a complement of a proper
  subrepresentation (unitary representations are semisimple,
  `UnitaryCharacterKernel.isSemisimpleRepresentation_of_norm_map`), every coefficient
  `x ↦ f (π x u)` of a finite-dimensional unitary representation is a finite sum of trace
  coefficients `x ↦ tr (ρ j x ∘ B j)` of irreducible unitary representations on Euclidean
  spaces. Grouping equivalent representations gives a pairwise inequivalent family.
* Invariance of `φ` under conjugation, Burnside's theorem for the family and nondegeneracy of
  the trace pairing (`CharacterKernelRank.span_range_pi_eq_top`,
  `CharacterKernelRank.eq_zero_of_tracePairing`) make every `B j` commute with `ρ j`, so
  `B j = c j • 1` by Schur's lemma.
* Positive semidefiniteness of the kernel makes every `c j` nonnegative
  (`UnitaryCharacterKernel.posSemidef_sum_character_kernel_iff`); the representations with
  `c j = 0` are dropped. The rank formula is `CharacterKernelRank.finrank_span_sum_character_kernel`,
  and its proof shows that the span of the sections is the span of all matrix coefficients.

No hypothesis can be dropped: on `ℤ`, `φ n = n` is a class function of finite rank whose
kernel is not positive semidefinite; a diagonal matrix coefficient of the defining
representation of `SU(2)`, as an abstract group, is positive semidefinite of rank two but not a
class function; and on `ℤ` the indicator of `0` is a positive semidefinite class function of
infinite rank.
-/

namespace D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction

open Module Representation D5.S3.FiniteGroups.GroupAlgebra.CharacterKernelRank
  D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
open scoped ComplexOrder InnerProductSpace ComplexConjugate

universe u

section Model

variable {G : Type u} [Group G]

/-- The kernel `(x, y) ↦ φ (x * y⁻¹)` with values in the operators on `ℂ`. -/
private noncomputable def opKernel (φ : G → ℂ) : Matrix G G (ℂ →L[ℂ] ℂ) :=
  Matrix.of fun x y => φ (x * y⁻¹) • (1 : ℂ →L[ℂ] ℂ)

private theorem posSemidef_opKernel {φ : G → ℂ}
    (hpsd : (Matrix.of fun x y : G => φ (x * y⁻¹)).PosSemidef) : (opKernel φ).PosSemidef := by
  have hherm : ∀ x y : G, conj (φ (y * x⁻¹)) = φ (x * y⁻¹) := fun x y => by
    have h := congr_fun (congr_fun hpsd.1 x) y
    simpa only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def] using h
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun vv => ?_⟩
  · ext x y : 1
    simp only [opKernel, Matrix.conjTranspose_apply, Matrix.of_apply, star_smul, star_one,
      RCLike.star_def, hherm]
  · have h := hpsd.2 vv
    have : (vv.sum fun x w => vv.sum fun x' w' => ⟪opKernel φ x' x w, w'⟫_ℂ) =
        vv.sum fun i xi => vv.sum fun j xj =>
          star xi * (Matrix.of fun x y : G => φ (x * y⁻¹)) i j * xj := by
      refine Finsupp.sum_congr fun x _ => Finsupp.sum_congr fun x' _ => ?_
      simp only [opKernel, Matrix.of_apply, FunLike.coe_smul, Pi.smul_apply,
        one_apply_eq_self, smul_eq_mul, RCLike.inner_apply, map_mul, RCLike.star_def, hherm]
      ring
    rw [this]
    exact (Complex.nonneg_iff.1 h).1

/-- A positive semidefinite kernel `φ (x * y⁻¹)` of finite rank is a coefficient
`x ↦ f (π x u)` of a unitary representation on a finite-dimensional inner product space. -/
private theorem exists_unitary_model (φ : G → ℂ)
    (hpsd : (Matrix.of fun x y : G => φ (x * y⁻¹)).PosSemidef)
    (hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹)))) :
    ∃ (E : Type u) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E)
      (_ : FiniteDimensional ℂ E) (π : Representation ℂ G E) (u : E) (f : E →ₗ[ℂ] ℂ),
      (∀ g v, ‖π g v‖ = ‖v‖) ∧ ∀ x, φ x = f (π x u) := by
  have : Fact (opKernel φ).PosSemidef := ⟨posSemidef_opKernel hpsd⟩
  set V := Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹)) with hV
  let H := RKHS.OfKernel (opKernel φ)
  let k : G → H := fun y => RKHS.kerFun H y 1
  have hk : ∀ y x, k y x = φ (x * y⁻¹) := by
    intro y x
    show RKHS.kerFun H y 1 x = _
    rw [RKHS.kerFun_apply, RKHS.OfKernel.kernel_ofKernel]
    simp [opKernel]
  have hrep : ∀ y (h : H), ⟪k y, h⟫_ℂ = h y := by
    intro y h
    simp [k, RKHS.kerFun_inner]
  let coe : H →ₗ[ℂ] G → ℂ := (RKHS.coeCLM ℂ : H →L[ℂ] G → ℂ)
  have hinj : Function.Injective coe := RKHS.coeCLM_injective
  have hmap : (Submodule.span ℂ (Set.range k)).map coe = V := by
    rw [Submodule.map_span, ← Set.range_comp, hV]
    exact congrArg (fun s => Submodule.span ℂ (Set.range s))
      (funext fun y => funext fun x => hk y x)
  -- The kernel functions span a finite-dimensional subspace, which is closed and dense.
  have hS0fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range k)) := by
    have e := Submodule.equivMapOfInjective coe hinj (Submodule.span ℂ (Set.range k))
    rw [hmap] at e
    exact e.symm.finiteDimensional
  have hS0 : Submodule.span ℂ (Set.range k) = ⊤ := by
    have hle : Submodule.span ℂ {f | ∃ (x : G) (v : ℂ), RKHS.kerFun H x v = f} ≤
        Submodule.span ℂ (Set.range k) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, v, rfl⟩
      have : RKHS.kerFun H x v = v • k x := by
        rw [← map_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    have h := Submodule.topologicalClosure_mono hle
    rw [RKHS.kerFun_dense,
      (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq] at h
    exact eq_top_iff.2 h
  have : FiniteDimensional ℂ H := by
    rw [hS0] at hS0fin
    exact Submodule.topEquiv.finiteDimensional
  have hrange : LinearMap.range coe = V := by rw [LinearMap.range_eq_map, ← hS0, hmap]
  let e : H ≃ₗ[ℂ] V := (LinearEquiv.ofInjective coe hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hes : ∀ v : V, ((e.symm v : H) : G → ℂ) = v := by
    intro v
    have : ((e (e.symm v) : V) : G → ℂ) = ((e.symm v : H) : G → ℂ) := rfl
    rw [← this, e.apply_symm_apply]
  -- Right translation preserves the span of the sections.
  have hinv : ∀ g, ∀ f ∈ V, LinearMap.funLeft ℂ ℂ (· * g) f ∈ V := by
    intro g
    have : V ≤ V.comap (LinearMap.funLeft ℂ ℂ (· * g)) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      have : LinearMap.funLeft ℂ ℂ (· * g) (fun x : G => φ (x * y⁻¹)) =
          fun x : G => φ (x * (y * g⁻¹)⁻¹) := by
        funext x
        simp [LinearMap.funLeft, mul_assoc]
      simp only [SetLike.mem_coe, Submodule.mem_comap, this]
      exact Submodule.subset_span ⟨_, rfl⟩
    exact fun f hf => this hf
  let R : G →* Module.End ℂ V :=
    { toFun := fun g => (LinearMap.funLeft ℂ ℂ (· * g)).restrict (hinv g)
      map_one' := by
        ext f x
        simp [LinearMap.funLeft]
      map_mul' := fun g h => by
        ext f x
        simp [LinearMap.funLeft, mul_assoc] }
  let π : Representation ℂ G H :=
    (e.symm.conjRingEquiv : Module.End ℂ V →* Module.End ℂ H).comp R
  have hπ : ∀ g (h : H) x, π g h x = h (x * g) := by
    intro g h x
    have : π g h = e.symm (R g (e h)) := rfl
    rw [this, hes]
    rfl
  have hπk : ∀ g y, π g (k y) = k (y * g⁻¹) := by
    intro g y
    refine RKHS.ext fun x => ?_
    rw [hπ, hk, hk]
    simp [mul_assoc]
  -- Right translation is unitary: check on the kernel functions, which span `H`.
  have hπinner : ∀ g a h, ⟪π g a, π g h⟫_ℂ = ⟪a, h⟫_ℂ := by
    intro g a h
    have := LinearMap.ext_on_range hS0 (f := ((innerₛₗ ℂ).flip (π g h)).comp (π g))
      (g := (innerₛₗ ℂ).flip h) fun y => by
        simp only [LinearMap.comp_apply, LinearMap.flip_apply, innerₛₗ_apply_apply, hπk, hrep,
          hπ]
        simp
    exact LinearMap.congr_fun this a
  refine ⟨H, inferInstance, inferInstance, inferInstance, π, k 1, innerₛₗ ℂ (k 1),
    fun g => (LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπinner g), fun x => ?_⟩
  rw [innerₛₗ_apply_apply, hrep, hπ, hk]
  simp

end Model

section TraceSum

variable {G : Type u} [Group G]

/-- `ψ` is a finite sum of trace coefficients `x ↦ tr (ρ j x ∘ B j)` of irreducible
representations acting by isometries on Euclidean spaces. -/
private def IsTraceSum (ψ : G → ℂ) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (n : J → ℕ)
    (ρ : ∀ j, Representation ℂ G (EuclideanSpace ℂ (Fin (n j))))
    (B : ∀ j, Module.End ℂ (EuclideanSpace ℂ (Fin (n j)))),
    (∀ j, (ρ j).IsIrreducible) ∧ (∀ j g v, ‖ρ j g v‖ = ‖v‖) ∧
      ∀ x, ψ x = ∑ j, LinearMap.trace ℂ _ (ρ j x * B j)

private theorem isTraceSum_zero : IsTraceSum (0 : G → ℂ) :=
  ⟨Empty, inferInstance, Empty.elim, fun j => j.elim, fun j => j.elim, fun j => j.elim,
    fun j => j.elim, fun x => by simp⟩

private theorem IsTraceSum.add {ψ₁ ψ₂ : G → ℂ} (h₁ : IsTraceSum ψ₁) (h₂ : IsTraceSum ψ₂) :
    IsTraceSum (ψ₁ + ψ₂) := by
  obtain ⟨J₁, _, n₁, ρ₁, B₁, hi₁, hu₁, he₁⟩ := h₁
  obtain ⟨J₂, _, n₂, ρ₂, B₂, hi₂, hu₂, he₂⟩ := h₂
  refine ⟨J₁ ⊕ J₂, inferInstance, Sum.elim n₁ n₂,
    fun j => Sum.rec (motive := fun j =>
      Representation ℂ G (EuclideanSpace ℂ (Fin (Sum.elim n₁ n₂ j)))) ρ₁ ρ₂ j,
    fun j => Sum.rec (motive := fun j =>
      Module.End ℂ (EuclideanSpace ℂ (Fin (Sum.elim n₁ n₂ j)))) B₁ B₂ j, ?_, ?_, fun x => ?_⟩
  · rintro (j | j)
    · exact hi₁ j
    · exact hi₂ j
  · rintro (j | j)
    · exact hu₁ j
    · exact hu₂ j
  · rw [Pi.add_apply, he₁, he₂, Fintype.sum_sum_type]
    rfl

/-- Irreducibility is invariant under equivalence of representations. -/
private theorem isIrreducible_of_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  let F := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let F' := IntertwiningMap.equivLinearMapAsModule σ ρ e.symm.toIntertwiningMap
  exact IsSimpleModule.congr (LinearEquiv.ofLinear F' F
    (LinearMap.ext fun v => e.symm_apply_apply v) (LinearMap.ext fun v => e.apply_symm_apply v))

/-- Trace coefficients of an irreducible unitary representation on a finite-dimensional inner
product space are trace sums: transport it to a Euclidean space along an orthonormal basis. -/
private theorem isTraceSum_of_isIrreducible {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (π : Representation ℂ G E)
    [π.IsIrreducible] (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (B : Module.End ℂ E) :
    IsTraceSum fun x => LinearMap.trace ℂ E (π x * B) := by
  let e := (stdOrthonormalBasis ℂ E).repr
  let ρ : Representation ℂ G (EuclideanSpace ℂ (Fin (finrank ℂ E))) :=
    (e.toLinearEquiv.conjRingEquiv : Module.End ℂ E →* _).comp π
  have hρ : ∀ g v, ρ g v = e (π g (e.symm v)) := fun g v => rfl
  have : ρ.IsIrreducible := isIrreducible_of_equiv (ρ := π)
    (Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => by simp [hρ])
  refine ⟨Unit, inferInstance, fun _ => finrank ℂ E, fun _ => ρ,
    fun _ => e.toLinearEquiv.conjRingEquiv B, fun _ => this, fun _ g v => ?_, fun x => ?_⟩
  · rw [hρ, LinearIsometryEquiv.norm_map, hπ, LinearIsometryEquiv.norm_map]
  · rw [Fintype.sum_unique]
    show _ = LinearMap.trace ℂ _ (e.toLinearEquiv.conjRingEquiv (π x) *
      e.toLinearEquiv.conjRingEquiv B)
    rw [← map_mul]
    exact (LinearMap.trace_conj' (π x * B) e.toLinearEquiv).symm

/-- Every coefficient `x ↦ f (π x u)` of a unitary representation on a finite-dimensional inner
product space is a trace sum. -/
private theorem isTraceSum_apply (d : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E],
      finrank ℂ E = d → ∀ (π : Representation ℂ G E), (∀ g v, ‖π g v‖ = ‖v‖) →
        ∀ (f : E →ₗ[ℂ] ℂ) (u : E), IsTraceSum fun x => f (π x u) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro E _ _ _ hd π hπ f u
  by_cases hirr : π.IsIrreducible
  · have heq : (fun x => f (π x u)) = fun x => LinearMap.trace ℂ E (π x * f.smulRight u) := by
      funext x
      rw [show π x * f.smulRight u = f.smulRight (π x u) from
        LinearMap.ext fun w => by simp, LinearMap.trace_smulRight]
    rw [heq]
    exact isTraceSum_of_isIrreducible π hπ _
  by_cases hE : Nontrivial E
  swap
  · have : Subsingleton E := not_nontrivial_iff_subsingleton.1 hE
    have : (fun x => f (π x u)) = 0 := by
      funext x
      simp [Subsingleton.elim u 0]
    rw [this]
    exact isTraceSum_zero
  -- Split off a proper subrepresentation and a complement of it.
  have : Nontrivial (Subrepresentation π) :=
    ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  obtain ⟨σ, hσb, hσt⟩ : ∃ σ : Subrepresentation π, σ ≠ ⊥ ∧ σ ≠ ⊤ := by
    by_contra hcon
    push_neg at hcon
    exact hirr { eq_bot_or_eq_top := fun σ => (em (σ = ⊥)).imp id (hcon σ) }
  obtain ⟨τ, hτ⟩ := (isSemisimpleRepresentation_of_norm_map π hπ).exists_isCompl σ
  have hτt : τ ≠ ⊤ := fun h => hσb (disjoint_top.1 (h ▸ hτ.disjoint))
  have hu : u ∈ σ.toSubmodule ⊔ τ.toSubmodule := by
    have h2 : (σ ⊔ τ).toSubmodule = ⊤ := by
      rw [codisjoint_iff.1 hτ.codisjoint]
      rfl
    rw [← Subrepresentation.toSubmodule_sup, h2]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  have hlt : ∀ ν : Subrepresentation π, ν ≠ ⊤ → finrank ℂ ν.toSubmodule < d := fun ν hν =>
    hd ▸ Submodule.finrank_lt fun h => hν (Subrepresentation.ext h)
  have h₁ := ih _ (hlt σ hσt) _ rfl σ.toRepresentation (fun g v => hπ g v)
    (f.comp σ.toSubmodule.subtype) ⟨y, hy⟩
  have h₂ := ih _ (hlt τ hτt) _ rfl τ.toRepresentation (fun g v => hπ g v)
    (f.comp τ.toSubmodule.subtype) ⟨z, hz⟩
  have heq : (fun x => f (π x (y + z))) =
      (fun x => (f.comp σ.toSubmodule.subtype) (σ.toRepresentation x ⟨y, hy⟩)) +
        fun x => (f.comp τ.toSubmodule.subtype) (τ.toRepresentation x ⟨z, hz⟩) := by
    funext x
    simp only [Pi.add_apply, map_add]
    rfl
  rw [heq]
  exact h₁.add h₂

/-- A trace sum can be rewritten over a pairwise inequivalent family. -/
private theorem exists_inequivalent_of_isTraceSum {ψ : G → ℂ} (h : IsTraceSum ψ) :
    ∃ (Q : Type) (_ : Fintype Q) (n : Q → ℕ)
      (ρ : ∀ q, Representation ℂ G (EuclideanSpace ℂ (Fin (n q))))
      (A : ∀ q, Module.End ℂ (EuclideanSpace ℂ (Fin (n q)))),
      (∀ q, (ρ q).IsIrreducible) ∧ (∀ q q', q ≠ q' → IsEmpty ((ρ q).Equiv (ρ q'))) ∧
      (∀ q g v, ‖ρ q g v‖ = ‖v‖) ∧ ∀ x, ψ x = ∑ q, LinearMap.trace ℂ _ (ρ q x * A q) := by
  classical
  obtain ⟨J, _, n, ρ, B, hirr, hunit, hψ⟩ := h
  let s : Setoid J :=
    { r := fun i j => Nonempty ((ρ i).Equiv (ρ j))
      iseqv := ⟨fun i => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩ }
  let r : Quotient s → J := Quotient.out
  -- The terms in one equivalence class are trace coefficients of its representative.
  have key : ∀ q : Quotient s, ∃ A : Module.End ℂ (EuclideanSpace ℂ (Fin (n (r q)))),
      ∀ x, ∑ j ∈ Finset.univ.filter (fun j => Quotient.mk s j = q),
        LinearMap.trace ℂ _ (ρ j x * B j) = LinearMap.trace ℂ _ (ρ (r q) x * A) := by
    intro q
    have hsum := Finset.sum_induction (s := Finset.univ.filter (fun j => Quotient.mk s j = q))
      (fun j x => LinearMap.trace ℂ _ (ρ j x * B j))
      (fun ψ : G → ℂ => ∃ A, ∀ x, ψ x = LinearMap.trace ℂ _ (ρ (r q) x * A))
      (fun a b ⟨A, hA⟩ ⟨A', hA'⟩ => ⟨A + A', fun x => by
        rw [Pi.add_apply, hA, hA', mul_add, map_add]⟩)
      ⟨0, fun x => by simp⟩
      (fun j hj => by
        have hjq : Quotient.mk s j = Quotient.mk s (r q) := by
          rw [(Finset.mem_filter.1 hj).2, Quotient.out_eq]
        obtain ⟨T⟩ := Quotient.exact hjq
        refine ⟨T.toLinearEquiv.conjRingEquiv (B j), fun x => ?_⟩
        rw [← T.conj_apply_self x]
        show _ = LinearMap.trace ℂ _ (T.toLinearEquiv.conjRingEquiv (ρ j x) *
          T.toLinearEquiv.conjRingEquiv (B j))
        rw [← map_mul]
        exact (LinearMap.trace_conj' _ T.toLinearEquiv).symm)
    obtain ⟨A, hA⟩ := hsum
    exact ⟨A, fun x => by rw [← hA x, Finset.sum_apply]⟩
  choose A hA using key
  refine ⟨Quotient s, inferInstance, fun q => n (r q), fun q => ρ (r q), A, fun q => hirr _,
    fun q q' hqq' => ⟨fun e => hqq' ?_⟩, fun q => hunit _, fun x => ?_⟩
  · rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact Quotient.sound ⟨e⟩
  · rw [hψ x, ← Finset.sum_fiberwise Finset.univ (fun j => Quotient.mk s j)]
    exact Finset.sum_congr rfl fun q _ => hA q x

/-- If a sum of trace coefficients of pairwise inequivalent irreducible representations is a
class function, every coefficient operator is a scalar. -/
private theorem exists_eq_smul_one {Q : Type} [Fintype Q] {n : Q → ℕ}
    (ρ : ∀ q, Representation ℂ G (EuclideanSpace ℂ (Fin (n q)))) [∀ q, (ρ q).IsIrreducible]
    (hne : ∀ q q', q ≠ q' → IsEmpty ((ρ q).Equiv (ρ q')))
    (A : ∀ q, Module.End ℂ (EuclideanSpace ℂ (Fin (n q))))
    (hclass : ∀ g x, ∑ q, LinearMap.trace ℂ _ (ρ q (g * x * g⁻¹) * A q) =
      ∑ q, LinearMap.trace ℂ _ (ρ q x * A q)) :
    ∃ c : Q → ℂ, ∀ q, A q = c q • 1 := by
  classical
  have hcomm : ∀ q g, ρ q g⁻¹ * A q * ρ q g = A q := by
    intro q g
    have hD : (fun q => ρ q g⁻¹ * A q * ρ q g - A q :
        ∀ q, Module.End ℂ (EuclideanSpace ℂ (Fin (n q)))) = 0 := by
      refine eq_zero_of_tracePairing (fun _ => (1 : ℂ)) (fun _ => one_ne_zero) _ fun B => ?_
      have hext := LinearMap.ext_on_range (span_range_pi_eq_top ρ hne)
        (f := (tracePairing fun _ => (1 : ℂ)).flip
          (fun q => ρ q g⁻¹ * A q * ρ q g - A q)) (g := 0) fun x => by
          simp only [LinearMap.flip_apply, tracePairing, LinearMap.mk₂_apply, one_mul,
            LinearMap.zero_apply, mul_sub, map_sub, Finset.sum_sub_distrib]
          rw [sub_eq_zero, ← hclass g x]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_mul, map_mul, LinearMap.trace_mul_comm ℂ (ρ q x), mul_assoc, mul_assoc,
            LinearMap.trace_mul_comm ℂ (ρ q g)]
          simp only [mul_assoc]
      exact LinearMap.congr_fun hext B
    exact sub_eq_zero.1 (congr_fun hD q)
  have hint : ∀ q, ∃ c : ℂ, A q = c • 1 := by
    intro q
    let T : IntertwiningMap (ρ q) (ρ q) :=
      (A q).intertwiningMap_of_isIntertwiningMap _ _ fun g v => by
        rw [← hcomm q g]
        simp only [Module.End.mul_apply, ← Module.End.mul_apply (ρ q g) (ρ q g⁻¹), ← map_mul,
          mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨c, hc⟩ :=
      (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ q)).2 T
    refine ⟨c, ?_⟩
    have := congrArg IntertwiningMap.toLinearMap hc
    simpa using this.symm
  choose c hc using hint
  exact ⟨c, hc⟩

end TraceSum

/-- A positive semidefinite class function of finite rank on an arbitrary group is a positive
combination of the characters of finitely many pairwise inequivalent irreducible
representations on Euclidean spaces, acting by isometries; the matrix coefficients of these
representations lie in the span of the sections `x ↦ φ (x * y⁻¹)`, and the dimension of that span
is the sum of the squared dimensions. -/
theorem exists_sum_character_of_finiteDimensional {G : Type*} [Group G] (φ : G → ℂ)
    (hpsd : (Matrix.of fun x y : G => φ (x * y⁻¹)).PosSemidef)
    (hclass : ∀ g x, φ (g * x * g⁻¹) = φ x)
    (hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹)))) :
    ∃ (m : ℕ) (n : Fin m → ℕ)
      (ρ : ∀ i, Representation ℂ G (EuclideanSpace ℂ (Fin (n i)))) (c : Fin m → ℝ),
      (∀ i, (ρ i).IsIrreducible) ∧ (∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j))) ∧
      (∀ i g v, ‖ρ i g v‖ = ‖v‖) ∧ (∀ i, 0 < c i) ∧
      (∀ x, φ x = ∑ i, (c i : ℂ) * (ρ i).character x) ∧
      (∀ i (v w : EuclideanSpace ℂ (Fin (n i))), (fun g => ⟪w, ρ i g v⟫_ℂ) ∈
        Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹))) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range fun y : G => fun x : G => φ (x * y⁻¹))) =
        ∑ i, n i ^ 2 := by
  sorry

end D5.S3.FiniteGroups.GroupAlgebra.PositiveDefiniteClassFunction
