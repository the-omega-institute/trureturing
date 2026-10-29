/- GID: D5/S3/HilbertOperators/RealPositiveTrace
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/RealPositiveTrace
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Intrinsic real positive trace as a supremum over every finite orthonormal family. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Fintype.EquivFin

/-! The usual finite-orthonormal-family definition permits infinite positive trace.
Parseval and Bessel identify its value without choosing a basis in the definition.
Only this positive real operator trace, used by the boundary heat, is constructed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.HilbertOperators.RealPositiveTrace

open scoped Topology ENNReal InnerProductSpace

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Extended positive operator trace, independently of any spectrum or Hilbert basis. -/
def positiveTrace (A : E →L[ℝ] E) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (v : Fin n → E) (_ : Orthonormal ℝ v),
    ∑ j, ENNReal.ofReal (inner ℝ (v j) (A (v j)))

private theorem quadratic_hasSum (e : HilbertBasis ι ℝ E) (A : E →L[ℝ] E)
    (d : ι → ℝ) (hc : ∀ x i, e.repr (A x) i = d i * e.repr x i) (x : E) :
    HasSum (fun i => d i * (e.repr x i)^2) (inner ℝ x (A x)) := by
  convert e.hasSum_inner_mul_inner x (A x) using 1
  funext i
  rw [← e.repr_apply_apply, hc, real_inner_comm (e i) x, ← e.repr_apply_apply]
  ring

private theorem finite_family_le (e : HilbertBasis ι ℝ E) (A : E →L[ℝ] E)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hc : ∀ x i, e.repr (A x) i = d i * e.repr x i)
    (n : ℕ) (v : Fin n → E) (hv : Orthonormal ℝ v) :
    ∑ j, ENNReal.ofReal (inner ℝ (v j) (A (v j))) ≤
      ∑' i, ENNReal.ofReal (d i) := by
  classical
  have hquad (j : Fin n) :
      ENNReal.ofReal (inner ℝ (v j) (A (v j))) =
        ∑' i, ENNReal.ofReal (d i) * ENNReal.ofReal ((e.repr (v j) i)^2) := by
    rw [← (quadratic_hasSum e A d hc (v j)).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hd i) (sq_nonneg _))
        (quadratic_hasSum e A d hc (v j)).summable]
    congr 1
    funext i
    exact ENNReal.ofReal_mul (hd i)
  have hbessel (i : ι) : ∑ j : Fin n, (e.repr (v j) i)^2 ≤ 1 := by
    have h := hv.sum_inner_products_le (e i) (s := Finset.univ)
    simpa [HilbertBasis.repr_apply_apply, real_inner_comm, Real.norm_eq_abs,
      sq_abs, e.orthonormal.norm_eq_one] using h
  calc
    ∑ j, ENNReal.ofReal (inner ℝ (v j) (A (v j))) =
        ∑ j, ∑' i, ENNReal.ofReal (d i) * ENNReal.ofReal ((e.repr (v j) i)^2) := by
      simp_rw [hquad]
    _ = ∑' i, ∑ j : Fin n,
        ENNReal.ofReal (d i) * ENNReal.ofReal ((e.repr (v j) i)^2) := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comm (f := fun j : Fin n => fun i =>
          ENNReal.ofReal (d i) * ENNReal.ofReal ((e.repr (v j) i)^2)))
    _ ≤ ∑' i, ENNReal.ofReal (d i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← Finset.mul_sum]
      have hb : ∑ j : Fin n, ENNReal.ofReal ((e.repr (v j) i)^2) ≤ 1 := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
        exact (ENNReal.ofReal_le_ofReal (hbessel i)).trans_eq (by simp)
      simpa only [mul_one] using mul_le_mul le_rfl hb zero_le zero_le

private theorem diagonal_positive (e : HilbertBasis ι ℝ E) (A : E →L[ℝ] E)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hc : ∀ x i, e.repr (A x) i = d i * e.repr x i) : A.IsPositive := by
  have hb (x y : E) :
      HasSum (fun i => d i * e.repr x i * e.repr y i) (inner ℝ x (A y)) := by
    convert e.hasSum_inner_mul_inner x (A y) using 1
    funext i
    rw [← e.repr_apply_apply, hc, real_inner_comm (e i) x, ← e.repr_apply_apply]
    ring
  apply A.isPositive_iff.mpr
  constructor
  · intro x y
    change inner ℝ (A x) y = inner ℝ x (A y)
    rw [real_inner_comm y (A x), ← (hb y x).tsum_eq, ← (hb x y).tsum_eq]
    congr 1
    funext i
    ring
  · intro x
    rw [real_inner_comm x (A x), ← (quadratic_hasSum e A d hc x).tsum_eq]
    exact tsum_nonneg fun i => mul_nonneg (hd i) (sq_nonneg _)

/-- A complete positive diagonal presentation has the intrinsic trace of its eigenvalues.
Every finite orthonormal test family is included in the supremum; infinity is permitted. -/
theorem positive_trace_diagonal (e : HilbertBasis ι ℝ E) (A : E →L[ℝ] E)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hc : ∀ x i, e.repr (A x) i = d i * e.repr x i) :
    A.IsPositive ∧ positiveTrace A = ∑' i, ENNReal.ofReal (d i) := by
  classical
  refine ⟨diagonal_positive e A d hd hc, ?_⟩
  apply le_antisymm
  · exact iSup_le fun n => iSup_le fun v => iSup_le fun hv =>
      finite_family_le e A d hd hc n v hv
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    let f : Fin s.card → ι := fun j => (s.equivFin.symm j).val
    have hf : Function.Injective f := Subtype.val_injective.comp s.equivFin.symm.injective
    let v : Fin s.card → E := fun j => e (f j)
    have hv : Orthonormal ℝ v := e.orthonormal.comp f hf
    have hdi (i : ι) : inner ℝ (e i) (A (e i)) = d i := by
      have h := hc (e i) i
      simpa [HilbertBasis.repr_apply_apply, e.orthonormal.norm_eq_one] using h
    have heq : ∑ i ∈ s, ENNReal.ofReal (d i) =
        ∑ j : Fin s.card, ENNReal.ofReal (inner ℝ (v j) (A (v j))) := by
      simp only [v,hdi]
      calc
        ∑ i ∈ s, ENNReal.ofReal (d i) = ∑ i : s, ENNReal.ofReal (d i.val) := by
          exact (Finset.sum_coe_sort s (fun i => ENNReal.ofReal (d i))).symm
        _ = ∑ j : Fin s.card, ENNReal.ofReal (d (f j)) :=
          (s.equivFin.symm.sum_comp (fun i : s => ENNReal.ofReal (d i.val))).symm
    rw [heq]
    exact le_iSup_of_le s.card (le_iSup_of_le v (le_iSup_of_le hv le_rfl))

#print axioms positive_trace_diagonal
end D5.S3.HilbertOperators.RealPositiveTrace
