/- GID: D5/S3/FiniteGroups/GroupAlgebra/EmbeddedPolynomialCancellation
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/EmbeddedPolynomialCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block, mathlib/module/Mathlib.LinearAlgebra.Determinant]
   utility: none
   digest: Cancellation of polynomial summands in the original relative stable category along arbitrary faithful finite additive embeddings. -/

import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedOriginalClassification
import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrPolynomialCancellation
import D5.S3.FiniteGroups.GroupAlgebra.PrimeCyclicRelativeTrace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Determinant

/-!
Polynomial endomorphisms preserve the top line and have constant diagonal.
The top scalar and the vanishing relative-factor trace give an invertible
block pivot, yielding cancellation over arbitrary coefficient fields without
restricting the intermediate relative-projective witnesses. This supplies the common-summand step in the
Elmer--Kadr reflection recurrence, Proof of Corollary 1.3,
DOI 10.1007/s13366-026-00855-9 / arXiv:2510.07939v1.

Source-only adaptation of ElmerKadrPolynomialCancellation. The coefficient
separation, constant diagonal and relative trace are those of the supplied
EmbeddedOriginalClassification source; no finite-field coefficient extraction
is reused. No compilation or kernel acceptance is claimed by this attempt.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.EmbeddedPolynomialCancellation

open ElmerKadrTensorCounterexample
open RectangularTensorObstruction (coefficient coefficient_cyclic coefficient_eval
  coefficient_top)
open Representation (IntertwiningMap)

universe uK uG uE

open ElmerKadrPolynomialCancellation (factors_sandwich)
open EmbeddedOriginalClassification

section PolynomialEndomorphisms

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] [Fintype E]
  (α : E →+ K) (hα : Function.Injective α)

include hα in
private theorem endomorphism_on_basis (N : ℕ)
    (hsize : N + 2 ≤ Fintype.card E)
    (h : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative))
    (i : Fin (N + 1)) :
    h (dualBasis K (N + 1) i) =
      coefficient K (N + 1) i.val (h (dualBasis K (N + 1) 0)) := by
  have hcomm : h.toLinearMap.comp (coefficient K (N + 1) i.val) =
      (coefficient K (N + 1) i.val).comp h.toLinearMap := by
    exact restricted_dual_intertwines_coefficients α hα
      (r := N + 1) (t := N + 1) (d := N + 1)
      (le_refl _) (le_refl _) (by omega) h i
  simpa only [LinearMap.comp_apply,
    Representation.IntertwiningMap.toLinearMap_apply, coefficient_cyclic]
    using LinearMap.congr_fun hcomm (dualBasis K (N + 1) 0)

include hα in
/-- The actual top line is preserved by every equivariant endomorphism. -/
private theorem endomorphism_top_line (N : ℕ)
    (hsize : N + 2 ≤ Fintype.card E)
    (h : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative)) :
    h (dualBasis K (N + 1) (Fin.last N)) =
      h (dualBasis K (N + 1) (Fin.last N))
        (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) •
          dualBasis K (N + 1) (Fin.last N) := by
  calc
    h (dualBasis K (N + 1) (Fin.last N)) =
        coefficient K (N + 1) N (h (dualBasis K (N + 1) 0)) :=
      endomorphism_on_basis α hα N hsize h (Fin.last N)
    _ = h (dualBasis K (N + 1) 0)
        (Polynomial.degreeLT.basis K (N + 1) 0) •
          dualBasis K (N + 1) (Fin.last N) := coefficient_top K N _
    _ = _ := by rw [embedded_endomorphism_constant_diagonal α hα N hsize h 0]

include hα in
private theorem endomorphism_matrix_isLowerTriangular (N : ℕ)
    (hsize : N + 2 ≤ Fintype.card E)
    (h : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative)) :
    (LinearMap.toMatrix (dualBasis K (N + 1)) (dualBasis K (N + 1))
      h.toLinearMap).IsLowerTriangular := by
  classical
  intro i j hij
  change i < j at hij
  simp only [LinearMap.toMatrix_apply, dualBasis, Module.Basis.dualBasis_repr,
    Representation.IntertwiningMap.toLinearMap_apply]
  change h (dualBasis K (N + 1) j) (Polynomial.degreeLT.basis K (N + 1) i) = 0
  rw [endomorphism_on_basis α hα N hsize h j, coefficient_eval]
  apply Finset.sum_eq_zero
  intro k _
  have hne : i.val ≠ k.val + j.val := by
    have hlt : i.val < j.val := hij
    omega
  rw [if_neg hne, mul_zero]

include hα in
/-- A nonzero top scalar gives a genuine equivariant automorphism, with
exactly the given map as its forward intertwiner. Its inverse is the actual
`Representation.Equiv.symm`; equivariance of that inverse follows by
injectivity, as in Mathlib, rather than being an additional hypothesis. -/
theorem endomorphism_equiv_of_top_ne_zero (N : ℕ)
    (hsize : N + 2 ≤ Fintype.card E)
    (h : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative))
    (htop : h (dualBasis K (N + 1) (Fin.last N))
      (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) ≠ 0) :
    ∃ e : Representation.Equiv ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative),
      e.toIntertwiningMap = h := by
  classical
  let T := LinearMap.toMatrix (dualBasis K (N + 1)) (dualBasis K (N + 1))
    h.toLinearMap
  have htri : T.IsLowerTriangular := endomorphism_matrix_isLowerTriangular α hα N hsize h
  have hdet : T.det ≠ 0 := htri.det_ne_zero_iff.mpr (by
    intro i
    have hi := embedded_endomorphism_constant_diagonal α hα N hsize h i
    have hn : h (dualBasis K (N + 1) i)
        (Polynomial.degreeLT.basis K (N + 1) i) ≠ 0 := by
      rw [hi]
      exact htop
    simpa only [T, Matrix.diag_apply, LinearMap.toMatrix_apply, dualBasis,
      Module.Basis.dualBasis_repr,
      Representation.IntertwiningMap.toLinearMap_apply] using hn)
  let e : DualPower K (N + 1) ≃ₗ[K] DualPower K (N + 1) :=
    LinearEquiv.ofIsUnitDet (f := h.toLinearMap)
      (v := dualBasis K (N + 1)) (v' := dualBasis K (N + 1))
      (isUnit_iff_ne_zero.mpr hdet)
  have he : e.toLinearMap = h.toLinearMap := by
    exact LinearEquiv.coe_ofIsUnitDet _
  refine ⟨Representation.Equiv.mk e (fun g => ?_), ?_⟩
  · change e.toLinearMap.comp ((dualAction K (N + 1)) (α.toMultiplicative g)) =
      ((dualAction K (N + 1)) (α.toMultiplicative g)).comp e.toLinearMap
    rw [he]
    exact h.isIntertwining' g
  · apply Representation.IntertwiningMap.ext
    exact he

end PolynomialEndomorphisms

section PolynomialScalar

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] [Fintype E]
  (α : E →+ K) (hα : Function.Injective α)

def topScalar (N : ℕ)
    (h : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative)) : K :=
  h (dualBasis K (N + 1) (Fin.last N))
    (Polynomial.degreeLT.basis K (N + 1) (Fin.last N))

private theorem topScalar_add (N : ℕ)
    (h k : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative)) :
    topScalar α N (h + k) = topScalar α N h + topScalar α N k := rfl

private theorem topScalar_sub (N : ℕ)
    (h k : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative)) :
    topScalar α N (h - k) = topScalar α N h - topScalar α N k := rfl

private theorem topScalar_id (N : ℕ) :
    topScalar α (K := K) N (.id ((dualAction K (N + 1)).comp α.toMultiplicative)) = 1 := by
  simp [topScalar, dualBasis]

include hα in
theorem topScalar_comp (N : ℕ) (hsize : N + 2 ≤ Fintype.card E)
    (h k : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative)) :
    topScalar α N (h.comp k) = topScalar α N h * topScalar α N k := by
  change h (k (dualBasis K (N + 1) (Fin.last N)))
      (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) =
    h (dualBasis K (N + 1) (Fin.last N))
        (Polynomial.degreeLT.basis K (N + 1) (Fin.last N)) *
      k (dualBasis K (N + 1) (Fin.last N))
        (Polynomial.degreeLT.basis K (N + 1) (Fin.last N))
  conv_lhs => rw [endomorphism_top_line α hα N hsize k]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact mul_comm _ _

include hα in
theorem topScalar_relativeFactors_zero [Nontrivial E]
    {p : ℕ} [Fact p.Prime] [CharP K p] (s N : ℕ)
    (hsize : N + 2 ≤ Fintype.card E) (hdim : ((N + 1 : ℕ) : K) ≠ 0)
    (h : Representation.IntertwiningMap
      ((dualAction K (N + 1)).comp α.toMultiplicative) ((dualAction K (N + 1)).comp α.toMultiplicative))
    (hh : RelativeFactors ((PrimeCyclicRelativeTrace.relativeAction (p := p) s).comp α.toMultiplicative) h) :
    topScalar α N h = 0 := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hz := trace_relativeFactors_for_embedding (p := p) α hα e he s _ h hh
  rw [embedded_endomorphism_trace α hα N hsize h] at hz
  exact (mul_eq_zero.mp hz).resolve_left hdim

end PolynomialScalar

section BlockCalculation

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {A B C : Type uK}
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]
  {ρ : Representation K G A} {σ : Representation K G B}
  {χ : Representation K G C}

private theorem map_pair_add (f : (ρ.prod χ).IntertwiningMap σ) (x : A) (z : C) :
    f (x, z) = f (x, 0) + f (0, z) := by
  have hp : (x, z) = (x, 0) + (0, z) := by simp
  rw [hp, map_add]

private theorem map_pair_neg (f : (ρ.prod χ).IntertwiningMap σ) (x : A) (z : C) :
    f (x, -z) = f (x, 0) - f (0, z) := by
  have hp : (x, -z) = (x, 0) - (0, z) := by simp
  rw [hp, map_sub]

end BlockCalculation

section Cancellation

variable {K : Type uK} [Field K]
  {E : Type uE} [AddGroup E] [Fintype E] [Nontrivial E]
  (α : E →+ K) (hα : Function.Injective α)
  {p : ℕ} [Fact p.Prime] [CharP K p]
  {A B : Type uK} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

include hα in
private theorem polynomial_summand_cancellation_succ (s N : ℕ)
    (hsize : N + 2 ≤ Fintype.card E) (hdim : ((N + 1 : ℕ) : K) ≠ 0)
    (ρ : Representation K (Multiplicative E) A)
    (σ : Representation K (Multiplicative E) B)
    (hstable : RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (p := p) s).comp α.toMultiplicative)
      (ρ.prod ((dualAction K (N + 1)).comp α.toMultiplicative)) (σ.prod ((dualAction K (N + 1)).comp α.toMultiplicative))) :
    RelativeStableIso ((PrimeCyclicRelativeTrace.relativeAction (p := p) s).comp α.toMultiplicative) ρ σ := by
  classical
  let χ := (dualAction K (N + 1)).comp α.toMultiplicative
  let τ := (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp α.toMultiplicative
  change RelativeStableIso τ (ρ.prod χ) (σ.prod χ) at hstable
  obtain ⟨F, G, hGF, hFG⟩ := hstable
  let pA := IntertwiningMap.fst K ρ χ
  let pB := IntertwiningMap.fst K σ χ
  let qA := IntertwiningMap.snd K ρ χ
  let qB := IntertwiningMap.snd K σ χ
  let iA := IntertwiningMap.inl K ρ χ
  let iB := IntertwiningMap.inl K σ χ
  let jA := IntertwiningMap.inr K ρ χ
  let jB := IntertwiningMap.inr K σ χ
  let b := pB.comp (F.comp jA)
  let d₀ := qB.comp (F.comp jA)
  let γ := qA.comp (G.comp iB)
  let δ := qA.comp (G.comp jB)
  let error := (qA.comp (G.comp F - .id (ρ.prod χ))).comp jA
  have hEfactor : RelativeFactors τ error := factors_sandwich τ hGF qA jA
  have hE : error = γ.comp b + δ.comp d₀ - .id χ := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change (G (F (0, z))).2 - z =
      (G (b z, 0)).2 + (G (0, d₀ z)).2 - z
    have hs : F (0, z) = (b z, 0) + (0, d₀ z) := by
      change F (0, z) = ((F (0, z)).1, 0) + (0, (F (0, z)).2)
      simp
    rw [hs, map_add] <;> rfl
  have hpivot : topScalar α N (γ.comp b) + topScalar α N δ * topScalar α N d₀ = 1 := by
    have hz := topScalar_relativeFactors_zero α hα s N hsize hdim error hEfactor
    rw [hE, topScalar_sub α, topScalar_add α, topScalar_comp α hα N hsize δ d₀,
      topScalar_id α] at hz
    exact sub_eq_zero.mp hz
  have hchoice : ∃ h : σ.IntertwiningMap χ, topScalar α N (d₀ + h.comp b) ≠ 0 := by
    by_cases hd₀ : topScalar α N d₀ = 0
    · refine ⟨γ, ?_⟩
      rw [hd₀, mul_zero, add_zero] at hpivot
      rw [topScalar_add α, hd₀, zero_add, hpivot]
      exact one_ne_zero
    · refine ⟨0, ?_⟩
      simpa only [IntertwiningMap.zero_comp, add_zero] using hd₀
  obtain ⟨h, hh⟩ := hchoice
  let D := d₀ + h.comp b
  obtain ⟨e, he⟩ := endomorphism_equiv_of_top_ne_zero α hα N hsize D hh
  let invD := e.symm.toIntertwiningMap
  have hleft (z : DualPower K (N + 1)) : invD (D z) = z := by
    change e.symm (D z) = z
    rw [← he]
    exact e.symm_apply_apply z
  have hright (z : DualPower K (N + 1)) : D (invD z) = z := by
    rw [← he]
    exact e.apply_symm_apply z

  -- q is the second row after the ACTUAL left shear (y,z) ↦ (y,z+h y).
  -- u is the first column of the ACTUAL right shear (x,z) ↦ (x,z-D⁻¹c' x).
  -- v is the inverse first shear on the B inclusion; w is the first row of
  -- the final left shear composed with the first shear. No quotient maps occur.
  let q := qB + h.comp pB
  let c' := q.comp (F.comp iA)
  let a := pB.comp (F.comp iA)
  let S := a - b.comp (invD.comp c')
  let u : ρ.IntertwiningMap (ρ.prod χ) :=
    IntertwiningMap.prod (IntertwiningMap.id ρ) (-(invD.comp c'))
  let v : σ.IntertwiningMap (σ.prod χ) :=
    IntertwiningMap.prod (IntertwiningMap.id σ) (-h)
  let w := pB - b.comp (invD.comp q)
  let T := pA.comp (G.comp v)
  have hD (z : DualPower K (N + 1)) : q (F (0, z)) = D z := by rfl
  have hFu_fst (x : A) : (F (u x)).1 = S x := by
    change (F (x, -invD (c' x))).1 = S x
    rw [map_pair_neg F] <;> rfl
  have hqFu (x : A) : q (F (u x)) = 0 := by
    change q (F (x, -invD (c' x))) = 0
    rw [map_pair_neg F, map_sub]
    change c' x - q (F (0, invD (c' x))) = 0
    rw [hD, hright, sub_self]
  have hFu (x : A) : F (u x) = v (S x) := by
    apply Prod.ext
    · exact hFu_fst x
    · have hz := hqFu x
      change (F (u x)).2 + h ((F (u x)).1) = 0 at hz
      change (F (u x)).2 = -h (S x)
      rw [hFu_fst] at hz
      have hz' := congrArg (fun z => z - h (S x)) hz
      simpa only [add_sub_cancel_right, zero_sub] using hz'
  have hwF (z : A × DualPower K (N + 1)) : w (F z) = S z.1 := by
    obtain ⟨x, z⟩ := z
    rw [map_pair_add F, map_add]
    have hx : w (F (x, 0)) = S x := by rfl
    have hz : w (F (0, z)) = 0 := by
      change b z - b (invD (q (F (0, z)))) = 0
      rw [hD, hleft, sub_self]
    rw [hx, hz, add_zero]
  have hwv (y : B) : w (v y) = y := by
    change y - b (invD (-h y + h y)) = y
    simp
  have hEA : T.comp S - .id ρ =
      (pA.comp (G.comp F - .id (ρ.prod χ))).comp u := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (G (v (S x))).1 - x = (G (F (u x))).1 - (u x).1
    rw [hFu] <;> rfl
  have hEB : S.comp T - .id σ =
      (w.comp (F.comp G - .id (σ.prod χ))).comp v := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    change S ((G (v y)).1) - y = w (F (G (v y)) - v y)
    rw [map_sub, hwF, hwv]
  refine ⟨S, T, ?_, ?_⟩
  · rw [hEA]
    exact factors_sandwich τ hGF pA u
  · rw [hEB]
    exact factors_sandwich τ hFG w v

include hα in
/-- Cancellation of the actual polynomial summand V_d for the original
relative module M_(p,s). A and B can be infinitely generated; the original
factorization witnesses P and X remain completely unrestricted. -/
theorem polynomial_summand_cancellation (s d : ℕ) (hd : 0 < d)
    (hsize : d + 1 ≤ Fintype.card E) (hdim : (d : K) ≠ 0)
    (ρ : Representation K (Multiplicative E) A)
    (σ : Representation K (Multiplicative E) B) :
    RelativeStableIso ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp α.toMultiplicative)
        (ρ.prod ((dualAction K d).comp α.toMultiplicative)) (σ.prod ((dualAction K d).comp α.toMultiplicative)) →
      RelativeStableIso ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp α.toMultiplicative)
        ρ σ := by
  cases d with
  | zero => omega
  | succ N => exact polynomial_summand_cancellation_succ α hα s N hsize hdim ρ σ

end Cancellation

end D5.S3.FiniteGroups.GroupAlgebra.EmbeddedPolynomialCancellation
