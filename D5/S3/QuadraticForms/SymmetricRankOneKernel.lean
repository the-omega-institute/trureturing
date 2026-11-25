/- GID: D5/S3/QuadraticForms/SymmetricRankOneKernel
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SymmetricRankOneKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A symmetric rank-one update changes nullity and the scalar response by exact formulas. -/

module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact kernel and response transitions for a symmetric rank-one update. -/

public section

set_option autoImplicit false

noncomputable section

namespace D5.S3.QuadraticForms.SymmetricRankOneKernel

open InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {B : E →ₗ[ℝ] E} {e : E} {t S : ℝ}

/-- A kernel vector has nonzero pairing with the update direction. -/
def HasNonzeroPairing (B : E →ₗ[ℝ] E) (e : E) : Prop :=
  ∃ z : LinearMap.ker B, ⟪e, (z : E)⟫ ≠ 0

/-- The system with right-hand side `e` is solvable and all solutions have pairing `S`. -/
def ScalarResponse (B : E →ₗ[ℝ] E) (e : E) (S : ℝ) : Prop :=
  (∃ y, B y = e) ∧ ∀ y, B y = e → ⟪e, y⟫ = S

/-- The update sends `x` to `B x + (t * ⟪e, x⟫) • e`. -/
def update (B : E →ₗ[ℝ] E) (e : E) (t : ℝ) : E →ₗ[ℝ] E :=
  B + t • (rankOne ℝ e e).toLinearMap

private theorem update_apply (x : E) :
    update B e t x = B x + (t * ⟪e, x⟫) • e := by
  simp [update, toLinearMap_rankOne, smul_smul]

/-- A real rank-one update in the same direction on both sides preserves symmetry. -/
theorem update_symmetric (hB : B.IsSymmetric) : (update B e t).IsSymmetric := by
  intro x y
  simp only [update_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hB x y]
  rw [real_inner_comm x e]
  ring

private theorem pairing_zero_of_solve (hB : B.IsSymmetric) {y : E} (hy : B y = e)
    (z : LinearMap.ker B) : ⟪e, (z : E)⟫ = 0 := by
  rw [← hy, hB y z, LinearMap.mem_ker.mp z.property, inner_zero_right]

private theorem scalarResponse_of_solution (hB : B.IsSymmetric) {y : E}
    (hy : B y = e) (hS : ⟪e, y⟫ = S) : ScalarResponse B e S := by
  refine ⟨⟨y, hy⟩, fun x hx => ?_⟩
  have hz : x - y ∈ LinearMap.ker B := by simp [LinearMap.mem_ker, hx, hy]
  have hp := pairing_zero_of_solve hB hy ⟨x - y, hz⟩
  change ⟪e, x - y⟫ = 0 at hp
  exact sub_eq_zero.mp (by simpa only [inner_sub_right, hS] using hp)

/-- The right-hand side is in the range exactly when the kernel has zero pairing throughout. -/
theorem solvable_iff_no_nonzero_pairing [FiniteDimensional ℝ E] (hB : B.IsSymmetric) :
    (∃ y, B y = e) ↔ ¬ HasNonzeroPairing B e := by
  constructor
  · rintro ⟨y, hy⟩ ⟨z, hz⟩
    exact hz (pairing_zero_of_solve hB hy z)
  · intro h
    have hrange : (LinearMap.ker B)ᗮ = LinearMap.range B := by
      rw [← hB.orthogonal_range, Submodule.orthogonal_orthogonal]
    apply LinearMap.mem_range.mp
    rw [← hrange, Submodule.mem_orthogonal']
    intro z hz
    by_contra hn
    exact h ⟨⟨z, hz⟩, hn⟩

/-- The kernel flag and the unique scalar response exhaust the states of a symmetric map. -/
theorem nonzero_pairing_or_unique_scalar [FiniteDimensional ℝ E] (hB : B.IsSymmetric) :
    HasNonzeroPairing B e ∨ ∃! S, ScalarResponse B e S := by
  classical
  by_cases h : HasNonzeroPairing B e
  · exact Or.inl h
  · obtain ⟨y, hy⟩ := (solvable_iff_no_nonzero_pairing hB).mpr h
    exact Or.inr ⟨⟪e, y⟫, scalarResponse_of_solution hB hy rfl,
      fun S hS => (hS.2 y hy).symm⟩

/-- A nonzero kernel pairing removes exactly one kernel dimension and gives response `1/t`. -/
theorem update_of_nonzero_pairing [FiniteDimensional ℝ E] (hB : B.IsSymmetric) (ht : t ≠ 0)
    (h : HasNonzeroPairing B e) :
    Module.finrank ℝ (LinearMap.ker (update B e t)) + 1 =
      Module.finrank ℝ (LinearMap.ker B) ∧ ScalarResponse (update B e t) e (1 / t) := by
  obtain ⟨z, hz⟩ := h
  have hBz : B (z : E) = 0 := LinearMap.mem_ker.mp z.property
  let restriction : LinearMap.ker B →ₗ[ℝ] ℝ := (innerₗ E e).comp (LinearMap.ker B).subtype
  have hsplit (x : E) : update B e t x = 0 ↔ B x = 0 ∧ ⟪e, x⟫ = 0 := by
    constructor
    · intro hx
      have hp := congrArg (innerₗ E (z : E)) hx
      simp only [innerₗ_apply_apply, update_apply, inner_add_right, real_inner_smul_right,
        ← hB (z : E) x, hBz, inner_zero_left, zero_add, inner_zero_right] at hp
      rw [real_inner_comm e (z : E)] at hp
      have hs : ⟪e, x⟫ = 0 :=
        (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hz)).resolve_left ht
      exact ⟨by simpa [update_apply, hs] using hx, hs⟩
    · rintro ⟨hx, hs⟩
      simp [update_apply, hx, hs]
  let toRestriction : LinearMap.ker (update B e t) →ₗ[ℝ] LinearMap.ker restriction :=
    ((LinearMap.ker (update B e t)).subtype.codRestrict (LinearMap.ker B)
      fun x => (hsplit x).mp (LinearMap.mem_ker.mp x.property) |>.1).codRestrict
        (LinearMap.ker restriction)
          fun x => (hsplit x).mp (LinearMap.mem_ker.mp x.property) |>.2
  have hbij : Function.Bijective toRestriction := by
    constructor
    · intro x y hxy
      exact Subtype.ext (congrArg (fun u : LinearMap.ker restriction => (u.val : E)) hxy)
    · intro x
      refine ⟨⟨x.val.val, (hsplit x.val.val).mpr
        ⟨LinearMap.mem_ker.mp x.val.property, LinearMap.mem_ker.mp x.property⟩⟩, ?_⟩
      exact Subtype.ext (Subtype.ext rfl)
  have hsurj : Function.Surjective restriction := by
    intro a
    refine ⟨(a / ⟪e, (z : E)⟫) • z, ?_⟩
    rw [map_smul]
    change (a / ⟪e, (z : E)⟫) * ⟪e, (z : E)⟫ = a
    exact div_mul_cancel₀ a hz
  have hd := restriction.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, CommSemiring.finrank_self,
    ← (LinearEquiv.ofBijective toRestriction hbij).finrank_eq, add_comm] at hd
  refine ⟨hd, scalarResponse_of_solution (update_symmetric hB)
    (y := (1 / (t * ⟪e, (z : E)⟫)) • (z : E)) ?_ ?_⟩
  · have hc : t * (1 / (t * ⟪e, (z : E)⟫) * ⟪e, (z : E)⟫) = 1 := by
      field_simp [ht, hz]
    rw [update_apply, map_smul, hBz, smul_zero, zero_add, real_inner_smul_right, hc, one_smul]
  · rw [real_inner_smul_right]
    field_simp [ht, hz]

private theorem update_apply_solution {y : E} (hy : B y = e) (hS : ⟪e, y⟫ = S) :
    update B e t y = (1 + t * S) • e := by
  rw [update_apply, hy, hS, add_smul, one_smul]

private theorem update_kernel_remainder {y x : E} (hy : B y = e)
    (hx : x ∈ LinearMap.ker (update B e t)) :
    x + (t * ⟪e, x⟫) • y ∈ LinearMap.ker B := by
  simpa [LinearMap.mem_ker, update_apply, hy] using hx

/-- At scalar resonance the kernel gains exactly one dimension and has a nonzero pairing. -/
theorem update_of_resonance [FiniteDimensional ℝ E] (hB : B.IsSymmetric)
    (h : ScalarResponse B e S) (htS : 1 + t * S = 0) :
    Module.finrank ℝ (LinearMap.ker (update B e t)) =
      Module.finrank ℝ (LinearMap.ker B) + 1 ∧ HasNonzeroPairing (update B e t) e := by
  obtain ⟨y, hy⟩ := h.1
  have hS := h.2 y hy
  have hS₀ : S ≠ 0 := by
    intro heq
    simp [heq] at htS
  have hy' : y ∈ LinearMap.ker (update B e t) := by
    simp [LinearMap.mem_ker, update_apply_solution hy hS, htS]
  have hker (z : LinearMap.ker B) : (z : E) ∈ LinearMap.ker (update B e t) := by
    simp [LinearMap.mem_ker, update_apply, LinearMap.mem_ker.mp z.property,
      pairing_zero_of_solve hB hy z]
  let toKernel : (LinearMap.ker B × ℝ) →ₗ[ℝ] LinearMap.ker (update B e t) :=
    ((LinearMap.ker B).subtype.coprod (LinearMap.toSpanSingleton ℝ E y)).codRestrict _
      (fun z => Submodule.add_mem _ (hker z.1) (Submodule.smul_mem _ z.2 hy'))
  have hbij : Function.Bijective toKernel := by
    constructor
    · intro a b hab
      have hab' : (a.1 : E) + a.2 • y = (b.1 : E) + b.2 • y := congrArg Subtype.val hab
      have hp := congrArg (innerₗ E e) hab'
      simp only [innerₗ_apply_apply, inner_add_right, real_inner_smul_right,
        pairing_zero_of_solve hB hy, zero_add, hS] at hp
      have hsecond : a.2 = b.2 := mul_right_cancel₀ hS₀ hp
      rw [hsecond] at hab'
      exact Prod.ext (Subtype.ext (add_right_cancel hab')) hsecond
    · intro x
      refine ⟨(⟨(x : E) + (t * ⟪e, (x : E)⟫) • y, update_kernel_remainder hy x.property⟩,
        -(t * ⟪e, (x : E)⟫)), Subtype.ext ?_⟩
      change (x : E) + (t * ⟪e, (x : E)⟫) • y + (-(t * ⟪e, (x : E)⟫)) • y = x
      rw [neg_smul, add_neg_cancel_right]
  refine ⟨?_, ⟨⟨y, hy'⟩, by simpa [hS] using hS₀⟩⟩
  rw [← (LinearEquiv.ofBijective toKernel hbij).finrank_eq, Module.finrank_prod,
    CommSemiring.finrank_self]

/-- Away from resonance the kernel is unchanged and the response is `S / (1+t*S)`. -/
theorem update_of_nonresonance (hB : B.IsSymmetric) (h : ScalarResponse B e S)
    (htS : 1 + t * S ≠ 0) :
    LinearMap.ker (update B e t) = LinearMap.ker B ∧
      ScalarResponse (update B e t) e (S / (1 + t * S)) := by
  obtain ⟨y, hy⟩ := h.1
  have hS := h.2 y hy
  refine ⟨?_, scalarResponse_of_solution (update_symmetric hB)
    (y := (1 + t * S)⁻¹ • y) ?_ ?_⟩
  · ext x
    constructor
    · intro hx
      have hp := pairing_zero_of_solve hB hy ⟨_, update_kernel_remainder hy hx⟩
      change ⟪e, x + (t * ⟪e, x⟫) • y⟫ = 0 at hp
      rw [inner_add_right, real_inner_smul_right, hS] at hp
      have hf : ⟪e, x⟫ * (1 + t * S) = 0 := by
        calc
          _ = ⟪e, x⟫ + t * ⟪e, x⟫ * S := by ring
          _ = 0 := hp
      have hzero := (mul_eq_zero.mp hf).resolve_right htS
      simpa [LinearMap.mem_ker, update_apply, hzero] using hx
    · intro hx
      simp [LinearMap.mem_ker, update_apply, LinearMap.mem_ker.mp hx,
        pairing_zero_of_solve hB hy ⟨x, hx⟩]
  · rw [map_smul, update_apply_solution hy hS, smul_smul, inv_mul_cancel₀ htS, one_smul]
  · rw [real_inner_smul_right, hS, div_eq_mul_inv, mul_comm]

section Blocks

open scoped BigOperators

variable {ι : Type*}
variable {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]

/-- Apply each block on the corresponding coordinate of the Euclidean product. -/
def blockDiagonal (A : ∀ i, F i →ₗ[ℝ] F i) : PiLp 2 F →ₗ[ℝ] PiLp 2 F :=
  let coordinates := WithLp.linearEquiv 2 ℝ (∀ i, F i)
  coordinates.symm.toLinearMap ∘ₗ LinearMap.piMap A ∘ₗ coordinates.toLinearMap

private def blockKernelEquiv (A : ∀ i, F i →ₗ[ℝ] F i) :
    LinearMap.ker (blockDiagonal A) ≃ₗ[ℝ] (∀ i, LinearMap.ker (A i)) where
  toFun x i := ⟨(x : PiLp 2 F) i, LinearMap.mem_ker.mpr
    (congrArg (fun z : PiLp 2 F => z i) (LinearMap.mem_ker.mp x.property))⟩
  invFun x := ⟨WithLp.toLp 2 (fun i => (x i : F i)), LinearMap.mem_ker.mpr
    ((WithLp.ext_iff 2).mpr (funext fun i => LinearMap.mem_ker.mp (x i).property))⟩
  left_inv x := Subtype.ext ((WithLp.ext_iff 2).mpr rfl)
  right_inv x := funext fun i => Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The block sum preserves symmetry, adds nullities and scalar responses, and has a
nonzero kernel pairing exactly when at least one component does. -/
theorem blockDiagonal_states [Fintype ι] [∀ i, FiniteDimensional ℝ (F i)]
    (A : ∀ i, F i →ₗ[ℝ] F i) (hA : ∀ i, (A i).IsSymmetric) (u : PiLp 2 F) :
    (blockDiagonal A).IsSymmetric ∧
    Module.finrank ℝ (LinearMap.ker (blockDiagonal A)) =
      ∑ i, Module.finrank ℝ (LinearMap.ker (A i)) ∧
    (HasNonzeroPairing (blockDiagonal A) u ↔ ∃ i, HasNonzeroPairing (A i) (u i)) ∧
    (∀ g : ι → ℝ, (∀ i, ScalarResponse (A i) (u i) (g i)) →
      ScalarResponse (blockDiagonal A) u (∑ i, g i)) := by
  classical
  have hSymm : (blockDiagonal A).IsSymmetric := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => hA i (x i) (y i)
  refine ⟨hSymm, (blockKernelEquiv A).finrank_eq.trans (Module.finrank_pi_fintype ℝ),
    ?_, ?_⟩
  · constructor
    · rintro ⟨z, hz⟩
      by_contra h
      apply hz
      rw [PiLp.inner_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_contra hi
      exact h ⟨i, blockKernelEquiv A z i, hi⟩
    · rintro ⟨i, z, hz⟩
      let w : ∀ j, LinearMap.ker (A j) := Pi.single i z
      refine ⟨(blockKernelEquiv A).symm w, ?_⟩
      rw [PiLp.inner_apply, Finset.sum_eq_single i]
      · simpa [blockKernelEquiv, w] using hz
      · intro j _ hji
        change ⟪u j, (w j : F j)⟫ = 0
        simp [w, Pi.single_eq_of_ne hji]
      · simp
  · intro g hg
    choose y hy using fun i => (hg i).1
    let v : PiLp 2 F := WithLp.toLp 2 y
    have hv : blockDiagonal A v = u := (WithLp.ext_iff 2).mpr (funext hy)
    refine scalarResponse_of_solution hSymm hv ?_
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => (hg i).2 (y i) (hy i)

end Blocks

end D5.S3.QuadraticForms.SymmetricRankOneKernel
