/- GID: D5/S3/Quantum/Entanglement/PartialTransposeSaturation/ChainSplitting
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PartialTransposeSaturation/ChainSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Dual.Lemmas]
   utility: none
   digest: A shortest polynomial kernel chain splits by simultaneous projections. -/

/- admission_basis: escape-witness -/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting

open Submodule LinearMap

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]

/-- Coefficients of `(f - t g) u(t)`, including the two endpoint equations. -/
def boundary (f g : U →ₗ[K] V) (n : ℕ) : (Fin n → U) →ₗ[K] (Fin (n + 1) → V) where
  toFun u := Fin.snoc (f ∘ u) 0 - Fin.cons 0 (g ∘ u)
  map_add' u w := by
    cases n with
    | zero => ext i; fin_cases i; simp [Fin.snoc_zero]
    | succ n =>
        ext i
        cases i using Fin.lastCases with
        | last => simp [add_comm]
        | cast i =>
            simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, Fin.snoc_castSucc]
            cases i using Fin.cases with
            | zero => simp [Function.comp_def]
            | succ i => simp [Fin.castSucc_succ, Function.comp_def, sub_add_sub_comm]
  map_smul' a u := by
    cases n with
    | zero => ext i; fin_cases i; simp [Fin.snoc_zero]
    | succ n =>
        ext i
        cases i using Fin.lastCases with
        | last => simp
        | cast i =>
            simp only [Pi.smul_apply, Pi.sub_apply, Function.comp_apply, Fin.snoc_castSucc]
            cases i using Fin.cases with
            | zero => simp [Function.comp_def]
            | succ i => simp [Fin.castSucc_succ, Function.comp_def, smul_sub]

private theorem boundary_snoc (f g : U →ₗ[K] V) {n : ℕ} (w : Fin n → U) :
    boundary f g (n + 1) (Fin.snoc w 0) = Fin.snoc (boundary f g n w) 0 := by
  change Fin.snoc (f ∘ Fin.snoc w 0) 0 -
      (@Fin.cons _ (fun _ => V)) 0 (g ∘ Fin.snoc w 0) = _
  rw [Fin.comp_snoc, Fin.comp_snoc]
  simp only [map_zero, Fin.cons_snoc_eq_snoc_cons]
  ext i
  cases i using Fin.lastCases with
  | last => simp [boundary]
  | cast i => simp [boundary]

/-- Absence of polynomial kernel chains makes every truncated coefficient map
injective. Trailing zero coefficients are removed one at a time. -/
theorem boundary_injective_of_no_chain (f g : U →ₗ[K] V)
    (h : ∀ (r : ℕ) (u : Fin (r + 1) → U),
      boundary f g (r + 1) u = 0 → u (Fin.last r) = 0) (n : ℕ) :
    Function.Injective (boundary f g n) := by
  have hz : ∀ (n : ℕ) (u : Fin n → U), boundary f g n u = 0 → u = 0 := by
    intro n
    induction n with
    | zero => intro u _; ext i; exact Fin.elim0 i
    | succ n ih =>
        intro u hu
        have hlast := h n u hu
        have hsnoc : u = Fin.snoc (Fin.init u) 0 := by
          simpa only [hlast] using (Fin.snoc_init_self u).symm
        have hin : boundary f g n (Fin.init u) = 0 := by
          rw [hsnoc, boundary_snoc] at hu
          ext j
          have hh := congrFun hu j.castSucc
          simpa only [Fin.snoc_castSucc, Pi.zero_apply] using hh
        have hi := ih _ hin
        rw [hsnoc, hi]
        ext i
        cases i using Fin.lastCases <;> simp
  intro u v huv
  have he : boundary f g n (u - v) = 0 := by rw [map_sub, huv, sub_self]
  exact sub_eq_zero.mp (hz n _ he)

private theorem boundary_tail_of_zero (f g : U →ₗ[K] V) {n : ℕ}
    (u : Fin (n + 2) → U) (hu : boundary f g (n + 2) u = 0) :
    boundary f g (n + 1) (Fin.tail u) =
      Fin.snoc (Fin.cons (g (u 0)) (0 : Fin n → V)) 0 := by
  have he : Fin.snoc (f ∘ u) 0 = (@Fin.cons _ (fun _ => V)) 0 (g ∘ u) :=
    sub_eq_zero.mp (show Fin.snoc (f ∘ u) 0 - (@Fin.cons _ (fun _ => V)) 0 (g ∘ u) = 0
      from hu)
  ext i
  cases i using Fin.cases with
  | zero =>
      have h := congrFun he (Fin.succ (0 : Fin (n + 1))).castSucc
      rw [Fin.snoc_castSucc, Fin.castSucc_succ, Fin.cons_succ] at h
      simpa [boundary, Fin.snoc_apply_zero, Function.comp_def, Fin.tail] using h
  | succ i =>
      cases i using Fin.lastCases with
      | last =>
          have h := congrFun he (Fin.last (n + 2))
          simpa [boundary, Function.comp_def, Fin.tail] using congrArg Neg.neg h.symm
      | cast i =>
          have h := congrFun he i.succ.succ.castSucc
          rw [Fin.snoc_castSucc, Fin.castSucc_succ, Fin.cons_succ] at h
          change (@Fin.snoc (n + 1) (fun _ : Fin (n + 2) => V))
                (f ∘ Fin.tail u) 0 i.succ.castSucc -
              (@Fin.cons (n + 1) (fun _ : Fin (n + 2) => V))
                0 (g ∘ Fin.tail u) i.succ.castSucc =
            (@Fin.snoc (n + 1) (fun _ : Fin (n + 2) => V))
              ((@Fin.cons n (fun _ : Fin (n + 1) => V)) (g (u 0)) (0 : Fin n → V))
                0 i.succ.castSucc
          simp only [Fin.snoc_castSucc]
          simp only [Fin.castSucc_succ, Fin.cons_succ,
            Pi.zero_apply, Function.comp_apply, Fin.tail]
          exact sub_eq_zero.mpr h

/-- Minimality excludes a shorter preimage of the first nonzero coefficient.
This is the obstruction to a dual chain with a nonzero diagonal pairing. -/
private theorem first_coefficient_not_mem_range (f g : U →ₗ[K] V) {n : ℕ}
    (u : Fin (n + 2) → U) (hu : boundary f g (n + 2) u = 0)
    (hlast : u (Fin.last (n + 1)) ≠ 0)
    (hminimal : ∀ z : Fin (n + 1) → U,
      boundary f g (n + 1) z = 0 → z (Fin.last n) = 0) :
    Fin.cons (g (u 0)) (0 : Fin n → V) ∉ LinearMap.range (boundary f g n) := by
  rintro ⟨w, hw⟩
  let z : Fin (n + 1) → U := Fin.tail u - Fin.snoc w 0
  have hz : boundary f g (n + 1) z = 0 := by
    rw [show z = Fin.tail u - Fin.snoc w 0 from rfl, map_sub,
      boundary_tail_of_zero f g u hu, boundary_snoc, hw, sub_self]
  have hzlast := hminimal z hz
  apply hlast
  simpa [z, Fin.tail] using hzlast

/-- The shortest-chain obstruction produces a normalized separating functional
on the complete coefficient space, not merely on the chain span. Its values on
the single-coordinate inclusions are the needed dual chain. -/
private theorem shortest_chain_dual_separator (f g : U →ₗ[K] V) {n : ℕ}
    (u : Fin (n + 2) → U) (hu : boundary f g (n + 2) u = 0)
    (hlast : u (Fin.last (n + 1)) ≠ 0)
    (hminimal : ∀ z : Fin (n + 1) → U,
      boundary f g (n + 1) z = 0 → z (Fin.last n) = 0) :
    ∃ q : Module.Dual K (Fin (n + 1) → V),
      (∀ w : Fin n → U, q (boundary f g n w) = 0) ∧
      q (Fin.cons (g (u 0)) (0 : Fin n → V)) = 1 := by
  let W := LinearMap.range (boundary f g n)
  let x : Fin (n + 1) → V := Fin.cons (g (u 0)) (0 : Fin n → V)
  have hx : x ∉ W := first_coefficient_not_mem_range f g u hu hlast hminimal
  have hn : ¬ ∀ q : Module.Dual K (Fin (n + 1) → V),
      q ∈ W.dualAnnihilator → q x = 0 := by
    exact fun h => hx ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W x).mp h)
  push_neg at hn
  obtain ⟨q, hqW, hqx⟩ := hn
  refine ⟨(q x)⁻¹ • q, ?_, ?_⟩
  · intro w
    have he : q (boundary f g n w) = 0 :=
      (Submodule.mem_dualAnnihilator q).mp hqW _ ⟨w, rfl⟩
    simp [he]
  · exact inv_mul_cancel₀ hqx

private theorem boundary_single (f g : U →ₗ[K] V) {n : ℕ} (i : Fin n) (x : U) :
    boundary f g n (Pi.single i x) =
      Pi.single i.castSucc (f x) - Pi.single i.succ (g x) := by
  have hf : f ∘ Pi.single i x = Pi.single i (f x) := by
    ext j
    exact LinearMap.apply_single (fun _ : Fin n => f) i j x
  have hg : g ∘ Pi.single i x = Pi.single i (g x) := by
    ext j
    exact LinearMap.apply_single (fun _ : Fin n => g) i j x
  change Fin.snoc (f ∘ Pi.single i x) 0 -
    (@Fin.cons _ (fun _ => V)) 0 (g ∘ Pi.single i x) = _
  rw [hf, hg]
  congr 1
  · ext j
    cases j using Fin.lastCases with
    | last => simp [Pi.single_apply]
    | cast j => simp [Pi.single_apply]
  · ext j
    cases j using Fin.cases with
    | zero => simp [Pi.single_apply]
    | succ j => simp [Pi.single_apply]

/-- Every shortest nonzero kernel chain has a normalized dual intertwining
chain. Its equations hold on all of the original domain. -/
private theorem shortest_chain_dual (f g : U →ₗ[K] V) {n : ℕ}
    (u : Fin (n + 2) → U) (hu : boundary f g (n + 2) u = 0)
    (hlast : u (Fin.last (n + 1)) ≠ 0)
    (hminimal : ∀ z : Fin (n + 1) → U,
      boundary f g (n + 1) z = 0 → z (Fin.last n) = 0) :
    ∃ q : Fin (n + 1) → Module.Dual K V,
      q 0 (g (u 0)) = 1 ∧
      ∀ i : Fin n, (q i.castSucc).comp f = (q i.succ).comp g := by
  obtain ⟨Q, hQ, hQone⟩ := shortest_chain_dual_separator f g u hu hlast hminimal
  let q : Fin (n + 1) → Module.Dual K V :=
    fun i => Q.comp (LinearMap.single K (fun _ : Fin (n + 1) => V) i)
  refine ⟨q, ?_, ?_⟩
  · have he : Pi.single (0 : Fin (n + 1)) (g (u 0)) =
        (@Fin.cons _ (fun _ => V)) (g (u 0)) (0 : Fin n → V) := by
      ext i
      cases i using Fin.cases <;> simp [Pi.single_apply]
    simpa [q, he, LinearMap.single_apply] using hQone
  · intro i
    ext x
    have h := hQ (Pi.single i x)
    rw [boundary_single, map_sub, sub_eq_zero] at h
    exact h

private theorem diagonal_of_chain {n : ℕ} (a : Fin (n + 1) → Fin (n + 1) → K)
    (hshift : ∀ i j : Fin n, a i.castSucc j.castSucc = a i.succ j.succ)
    (hleft : ∀ i : Fin n, a i.succ 0 = 0)
    (hright : ∀ i : Fin n, a i.castSucc (Fin.last n) = 0)
    (hone : a 0 0 = 1) : ∀ i j, a i j = if i = j then 1 else 0 := by
  induction n with
  | zero => intro i j; fin_cases i; fin_cases j; simpa using hone
  | succ n ih =>
      let b : Fin (n + 1) → Fin (n + 1) → K := fun i j => a i.castSucc j.castSucc
      have hbshift : ∀ i j : Fin n,
          b i.castSucc j.castSucc = b i.succ j.succ := by
        intro i j
        simpa [b, Fin.castSucc_succ] using hshift i.castSucc j.castSucc
      have hbleft : ∀ i : Fin n, b i.succ 0 = 0 := by
        intro i
        simpa [b, Fin.castSucc_succ] using hleft i.castSucc
      have hbright : ∀ i : Fin n, b i.castSucc (Fin.last n) = 0 := by
        intro i
        change a i.castSucc.castSucc (Fin.last n).castSucc = 0
        rw [hshift]
        simpa [Fin.castSucc_succ] using hright i.succ
      have hb := ih b hbshift hbleft hbright (by simpa [b] using hone)
      intro i j
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases with
          | last =>
              rw [← Fin.succ_last, ← hshift]
              simpa [b] using hb (Fin.last n) (Fin.last n)
          | cast j =>
              cases j using Fin.cases with
              | zero => simpa using hleft (Fin.last n)
              | succ j =>
                  rw [Fin.castSucc_succ, ← Fin.succ_last, ← hshift]
                  have hj : (Fin.last n : Fin (n + 1)) ≠ j.castSucc := by
                    intro he
                    have he' := congrArg Fin.val he
                    have := j.isLt
                    simp only [Fin.val_last, Fin.val_castSucc] at he'
                    omega
                  have hj' : (Fin.last (n + 1) : Fin (n + 2)) ≠ j.castSucc.succ := by
                    intro he
                    have he' := congrArg Fin.val he
                    have := j.isLt
                    simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at he'
                    omega
                  simpa [b, hj, hj'] using hb (Fin.last n) j.castSucc
      | cast i =>
          cases j using Fin.lastCases with
          | last => simpa using hright i
          | cast j => simpa [b] using hb i j

/-- The normalized dual chain pairs biorthogonally with all image-chain vectors.
In particular the image chain is independent; no independence was assumed. -/
private theorem shortest_chain_biorthogonal (f g : U →ₗ[K] V) {n : ℕ}
    (u : Fin (n + 2) → U) (hu : boundary f g (n + 2) u = 0)
    (hlast : u (Fin.last (n + 1)) ≠ 0)
    (hminimal : ∀ z : Fin (n + 1) → U,
      boundary f g (n + 1) z = 0 → z (Fin.last n) = 0) :
    ∃ q : Fin (n + 1) → Module.Dual K V,
      (∀ i : Fin n, (q i.castSucc).comp f = (q i.succ).comp g) ∧
      ∀ i j : Fin (n + 1), q i (g (u j.castSucc)) = if i = j then 1 else 0 := by
  obtain ⟨q, hqone, hq⟩ := shortest_chain_dual f g u hu hlast hminimal
  have he : Fin.snoc (f ∘ u) 0 = (@Fin.cons _ (fun _ => V)) 0 (g ∘ u) :=
    sub_eq_zero.mp (show Fin.snoc (f ∘ u) 0 - (@Fin.cons _ (fun _ => V)) 0 (g ∘ u) = 0
      from hu)
  have hf₀ : f (u 0) = 0 := by
    simpa [Fin.snoc_apply_zero, Function.comp_def] using congrFun he 0
  have hglast : g (u (Fin.last (n + 1))) = 0 := by
    simpa [Function.comp_def] using (congrFun he (Fin.last (n + 2))).symm
  have hstep (j : Fin (n + 1)) : f (u j.succ) = g (u j.castSucc) := by
    have h := congrFun he j.succ.castSucc
    rw [Fin.snoc_castSucc, Fin.castSucc_succ, Fin.cons_succ] at h
    exact h
  refine ⟨q, hq, ?_⟩
  apply diagonal_of_chain (fun i j => q i (g (u j.castSucc)))
  · intro i j
    rw [← hstep, ← Fin.castSucc_succ]
    exact LinearMap.congr_fun (hq i) (u j.succ.castSucc)
  · intro i
    have h := LinearMap.congr_fun (hq i) (u 0)
    simpa [hf₀] using h.symm
  · intro i
    rw [← hstep]
    have h := LinearMap.congr_fun (hq i) (u (Fin.last (n + 1)))
    simpa [hglast] using h
  · simpa using hqone

private def coordinateProjection {ι : Type*} [Fintype ι]
    (b : ι → U) (p : ι → Module.Dual K U) : U →ₗ[K] U :=
  ∑ i, (p i).smulRight (b i)

private theorem coordinateProjection_isProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → U) (p : ι → Module.Dual K U)
    (h : ∀ i j, p i (b j) = if i = j then 1 else 0) :
    IsProj (span K (Set.range b)) (coordinateProjection b p) := by
  have hb (j : ι) : coordinateProjection b p (b j) = b j := by
    simp [coordinateProjection, LinearMap.sum_apply, h]
  constructor
  · intro x
    simp only [coordinateProjection, LinearMap.sum_apply, LinearMap.smulRight_apply]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩))
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hb j
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]

private theorem independent_of_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → U) (p : ι → Module.Dual K U)
    (h : ∀ i j, p i (b j) = if i = j then 1 else 0) : LinearIndependent K b := by
  apply LinearIndependent.of_comp (LinearMap.pi p)
  convert Pi.linearIndependent_single_one ι K using 1
  ext j i
  simp [Function.comp_def, h, Pi.single_apply, eq_comm]

/-- A degree-zero right kernel chain is a common zero column with an actual
simultaneous complementary domain. -/
theorem split_common_kernel_line (f g : U →ₗ[K] V) (u : U) (hu : u ≠ 0)
    (hf : f u = 0) (hg : g u = 0) :
    ∃ P : U →ₗ[K] U, IsProj (K ∙ u) P ∧ f.comp P = 0 ∧ g.comp P = 0 ∧
      IsCompl (K ∙ u) (ker P) := by
  obtain ⟨q, hq⟩ := Module.Projective.exists_dual_eq_one K hu
  let P := q.smulRight u
  have hP : IsProj (K ∙ u) P := by
    constructor
    · intro x
      exact Submodule.smul_mem _ _ (subset_span (by simp))
    · intro x hx
      obtain ⟨a, rfl⟩ := mem_span_singleton.mp hx
      simp [P, hq]
  refine ⟨P, hP, ?_, ?_, hP.isCompl⟩
  · ext x; simp [P, hf]
  · ext x; simp [P, hg]

/-- A shortest nonzero right kernel chain splits off as a simultaneous direct
summand. The returned projections commute with both coefficient maps and their
kernels are simultaneous complementary spaces. -/
theorem split_shortest_chain (f g : U →ₗ[K] V) {n : ℕ}
    (u : Fin (n + 2) → U) (hu : boundary f g (n + 2) u = 0)
    (hlast : u (Fin.last (n + 1)) ≠ 0)
    (hminimal : ∀ z : Fin (n + 1) → U,
      boundary f g (n + 1) z = 0 → z (Fin.last n) = 0) :
    ∃ (P : U →ₗ[K] U) (Q : V →ₗ[K] V),
      IsProj (span K (Set.range u)) P ∧
      IsProj (span K (Set.range (fun j : Fin (n + 1) => g (u j.castSucc)))) Q ∧
      Q.comp f = f.comp P ∧ Q.comp g = g.comp P ∧
      LinearIndependent K u ∧
      LinearIndependent K (fun j : Fin (n + 1) => g (u j.castSucc)) ∧
      IsCompl (span K (Set.range u)) (ker P) ∧
      IsCompl (span K (Set.range (fun j : Fin (n + 1) => g (u j.castSucc)))) (ker Q) := by
  obtain ⟨q, hq, hdual⟩ := shortest_chain_biorthogonal f g u hu hlast hminimal
  have he : Fin.snoc (f ∘ u) 0 = (@Fin.cons _ (fun _ => V)) 0 (g ∘ u) :=
    sub_eq_zero.mp (show Fin.snoc (f ∘ u) 0 - (@Fin.cons _ (fun _ => V)) 0 (g ∘ u) = 0
      from hu)
  have hf₀ : f (u 0) = 0 := by
    simpa [Fin.snoc_apply_zero, Function.comp_def] using congrFun he 0
  have hglast : g (u (Fin.last (n + 1))) = 0 := by
    simpa [Function.comp_def] using (congrFun he (Fin.last (n + 2))).symm
  have hstep (j : Fin (n + 1)) : f (u j.succ) = g (u j.castSucc) := by
    have h := congrFun he j.succ.castSucc
    rw [Fin.snoc_castSucc, Fin.castSucc_succ, Fin.cons_succ] at h
    exact h
  let p : Fin (n + 2) → Module.Dual K U :=
    Fin.cons ((q 0).comp g) (fun j => (q j).comp f)
  have hpf (j : Fin (n + 1)) : p j.succ = (q j).comp f := by simp [p]
  have hpg (j : Fin (n + 1)) : p j.castSucc = (q j).comp g := by
    cases j using Fin.cases with
    | zero => simp [p]
    | succ j => simpa [p, Fin.castSucc_succ] using hq j
  have hpdual : ∀ i j : Fin (n + 2), p i (u j) = if i = j then 1 else 0 := by
    intro i j
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.lastCases with
        | last => simp [p, hglast]
        | cast j =>
            change q 0 (g (u j.castSucc)) = if (0 : Fin (n + 2)) = j.castSucc then 1 else 0
            have hz : ((0 : Fin (n + 2)) = j.castSucc) ↔ ((0 : Fin (n + 1)) = j) := by
              simp only [Fin.ext_iff, Fin.val_zero, Fin.val_castSucc]
            simpa only [hz] using hdual 0 j
    | succ i =>
        cases j using Fin.cases with
        | zero => simp [p, hf₀]
        | succ j => simpa [p, hstep] using hdual i j
  let P := coordinateProjection u p
  let Q := coordinateProjection (fun j : Fin (n + 1) => g (u j.castSucc)) q
  have hP : IsProj (span K (Set.range u)) P := coordinateProjection_isProj u p hpdual
  have hQ : IsProj (span K (Set.range (fun j : Fin (n + 1) => g (u j.castSucc)))) Q :=
    coordinateProjection_isProj _ q hdual
  refine ⟨P, Q, hP, hQ, ?_, ?_, independent_of_coordinates u p hpdual,
    independent_of_coordinates _ q hdual, hP.isCompl, hQ.isCompl⟩
  · ext x
    simp [P, Q, coordinateProjection, LinearMap.sum_apply, map_sum,
      Fin.sum_univ_succ, hf₀, hpf, hstep, hstep 0]
    simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one'] using
      congrArg (fun v => q 0 (f x) • v) (hstep (0 : Fin (n + 1))).symm
  · ext x
    simp [P, Q, coordinateProjection, LinearMap.sum_apply, map_sum,
      Fin.sum_univ_castSucc, hglast, hpg]



end D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting

namespace D5.S3.Quantum.Entanglement.PartialTransposeSaturation

open LinearMap Submodule Module

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A simultaneous projection splits the image into complementary images.
This form does not require choosing coordinates on either summand. -/
theorem finrank_range_split (T : U →ₗ[K] V) (P : Module.End K U)
    (Q : Module.End K V) (hQ : Q.comp Q = Q) (hT : Q.comp T = T.comp P) :
    finrank K (LinearMap.range T) =
      finrank K (LinearMap.range (Q.comp T)) +
        finrank K (LinearMap.range ((LinearMap.id - Q).comp T)) := by
  let S := LinearMap.range (Q.comp T)
  let W := LinearMap.range ((LinearMap.id - Q).comp T)
  have hS : S ≤ LinearMap.range T := by
    dsimp [S]
    rw [hT]
    exact LinearMap.range_comp_le_range _ _
  have hW : W ≤ LinearMap.range T := by
    rintro _ ⟨x, rfl⟩
    refine ⟨x - P x, ?_⟩
    have ht := LinearMap.congr_fun hT x
    change Q (T x) = T (P x) at ht
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, ← ht]
  have he : S ⊔ W = LinearMap.range T := by
    apply le_antisymm (sup_le hS hW)
    rintro _ ⟨x, rfl⟩
    have hs : Q (T x) ∈ S := ⟨x, rfl⟩
    have hw : T x - Q (T x) ∈ W := ⟨x, rfl⟩
    have hsum : Q (T x) + (T x - Q (T x)) = T x := by abel
    rw [← hsum]
    exact Submodule.add_mem (S ⊔ W)
      (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hw)
  have hd : Disjoint S W := by
    apply Submodule.disjoint_def.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    have hs : Q z = z := by
      rw [← hx]
      exact LinearMap.congr_fun hQ (T x)
    have hw : Q z = 0 := by
      rw [← hy]
      change Q (T y - Q (T y)) = 0
      have hqq : Q (Q (T y)) = Q (T y) := LinearMap.congr_fun hQ (T y)
      rw [map_sub, hqq, sub_self]
    exact hs.symm.trans hw
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S W
  have hsup := congrArg (fun H : Submodule K V => finrank K H) he
  have hinf := congrArg (fun H : Submodule K V => finrank K H) hd.eq_bot
  rw [finrank_bot] at hinf
  change finrank K (LinearMap.range T) = finrank K S + finrank K W
  omega

section Tensor

variable {U' V' : Type*} [AddCommGroup U'] [Module K U']
  [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

/-- A simultaneous splitting of the first coefficient pair splits every
two-term tensor sum into complementary images. -/
theorem finrank_tensorSum_split (f₁ f₂ : U →ₗ[K] V) (g₁ g₂ : U' →ₗ[K] V')
    (P : Module.End K U) (Q : Module.End K V)
    (hQ : Q.comp Q = Q) (hf₁ : Q.comp f₁ = f₁.comp P)
    (hf₂ : Q.comp f₂ = f₂.comp P) :
    let T := TensorProduct.map f₁ g₁ + TensorProduct.map f₂ g₂
    let Q' := TensorProduct.map Q (LinearMap.id : Module.End K V')
    finrank K (LinearMap.range T) =
      finrank K (LinearMap.range (Q'.comp T)) +
        finrank K (LinearMap.range ((LinearMap.id - Q').comp T)) := by
  dsimp only
  apply finrank_range_split _
    (TensorProduct.map P (LinearMap.id : Module.End K U'))
  · rw [← TensorProduct.map_comp, hQ, LinearMap.id_comp]
  · simp only [LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
      LinearMap.id_comp, LinearMap.comp_id, hf₁, hf₂]

end Tensor

end D5.S3.Quantum.Entanglement.PartialTransposeSaturation
