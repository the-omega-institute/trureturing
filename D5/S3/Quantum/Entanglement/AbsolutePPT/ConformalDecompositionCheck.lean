
import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
import Mathlib.Tactic

open Finset
open scoped BigOperators Matrix
open D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.OrderedField

universe u v
variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {E : Type v} [Fintype E] {m : ℕ}

private theorem box_improvement
    (A : Matrix (Fin m) E F) (rhs : Fin m → F) (l u x y : E → F)
    (L : (E → F) →ₗ[F] F)
    (hx : A *ᵥ x = rhs) (hy : A *ᵥ y = rhs)
    (hxl : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i)
    (hyl : ∀ i, l i ≤ y i) (hyu : ∀ i, y i ≤ u i)
    (hL : L y < L x) :
    ∃ c : E → F, c ≠ 0 ∧ A *ᵥ c = 0 ∧
      (∀ i, c i = 0 ∨ SignType.sign (c i) = SignType.sign ((y - x) i)) ∧
      (∀ w : E → F, A *ᵥ w = 0 → w ≠ 0 →
        Function.support w ⊆ Function.support c → Function.support w = Function.support c) ∧
      A *ᵥ (x + c) = rhs ∧
      (∀ i, l i ≤ (x + c) i ∧ (x + c) i ≤ u i) ∧ L (x + c) < L x := by
  classical
  have hd : A *ᵥ (y - x) = 0 := by rw [Matrix.mulVec_sub, hy, hx, sub_self]
  obtain ⟨n, c, hs, _, _, _, hc⟩ := signConformalGlobalKernelCircuitDecomposition A (y - x) hd
  have hsumL : (∑ j, L (c j)) < 0 := by
    rw [← map_sum, hs, map_sub]
    exact sub_neg.mpr hL
  have hj : ∃ j, L (c j) < 0 := by
    by_contra hn
    push_neg at hn
    exact (not_le_of_gt hsumL) (sum_nonneg fun j _ => hn j)
  obtain ⟨j, hj⟩ := hj
  refine ⟨c j, (hc j).1, (hc j).2.1, (hc j).2.2.1, (hc j).2.2.2, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_add, hx, (hc j).2.1, add_zero]
  · intro i
    have hsi : (∑ k, c k i) = y i - x i := by
      simpa only [sum_apply, Pi.sub_apply] using congrFun hs i
    by_cases hdpos : 0 ≤ y i - x i
    · have hnn (k : Fin n) : 0 ≤ c k i := by
        rcases (hc k).2.2.1 i with hk | hk
        · rw [hk]
        · have hsg : 0 ≤ SignType.sign (c k i) := by
            rw [hk]
            exact sign_nonneg_iff.mpr hdpos
          exact sign_nonneg_iff.mp hsg
      have hrest : 0 ≤ ∑ k ∈ (univ : Finset (Fin n)).erase j, c k i :=
        sum_nonneg fun k _ => hnn k
      have heq := (univ : Finset (Fin n)).sum_erase_add (fun k => c k i) (mem_univ j)
      change l i ≤ x i + c j i ∧ x i + c j i ≤ u i
      constructor <;> linarith [hnn j, hxl i, hyu i]
    · have hnp (k : Fin n) : c k i ≤ 0 := by
        rcases (hc k).2.2.1 i with hk | hk
        · rw [hk]
        · exact (sign_eq_neg_one_iff.mp
            (hk.trans (sign_neg (lt_of_not_ge hdpos)))).le
      have hrest : (∑ k ∈ (univ : Finset (Fin n)).erase j, c k i) ≤ 0 :=
        sum_nonpos fun k _ => hnp k
      have heq := (univ : Finset (Fin n)).sum_erase_add (fun k => c k i) (mem_univ j)
      change l i ≤ x i + c j i ∧ x i + c j i ≤ u i
      constructor <;> linarith [hnp j, hyl i, hxu i]
  · rw [map_add]
    exact add_lt_of_neg_right hj

private theorem box_optimality
    (A : Matrix (Fin m) E F) (rhs : Fin m → F) (l u x : E → F)
    (L : (E → F) →ₗ[F] F)
    (hx : A *ᵥ x = rhs) (hxl : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i) :
    (∀ y : E → F, A *ᵥ y = rhs → (∀ i, l i ≤ y i) → (∀ i, y i ≤ u i) → L x ≤ L y) ↔
    ¬ ∃ c : E → F, c ≠ 0 ∧ A *ᵥ c = 0 ∧
      (∀ w : E → F, A *ᵥ w = 0 → w ≠ 0 →
        Function.support w ⊆ Function.support c → Function.support w = Function.support c) ∧
      (∀ i, l i ≤ (x + c) i ∧ (x + c) i ≤ u i) ∧ L (x + c) < L x := by
  constructor
  · rintro h ⟨c, _, hcK, _, hbox, hL⟩
    have hf : A *ᵥ (x + c) = rhs := by rw [Matrix.mulVec_add, hx, hcK, add_zero]
    exact not_lt_of_ge (h (x + c) hf (fun i => (hbox i).1) (fun i => (hbox i).2)) hL
  · intro hn y hy hyl hyu
    by_contra hL
    obtain ⟨c, hc0, hcK, _, hcmin, _, hbox, hbetter⟩ :=
      box_improvement A rhs l u x y L hx hy hxl hxu hyl hyu (lt_of_not_ge hL)
    exact hn ⟨c, hc0, hcK, hcmin, hbox, hbetter⟩

private theorem affine_decomposition {d : ℕ} (q : E → (Fin d → F)) (x : E → F)
    (hxsum : ∑ i, x i = 0) (hxq : ∑ i, x i • q i = 0) :
    let A : Matrix (Fin (d + 1)) E F := fun r i => Fin.cons 1 (q i) r
    ∃ (n : ℕ) (c : Fin n → (E → F)),
      (∑ j, c j) = x ∧ LinearIndependent F c ∧
      n ≤ (support x).card ∧ n ≤ Module.finrank F (LinearMap.ker (Matrix.mulVecLin A)) ∧
      ∀ j, c j ≠ 0 ∧ (∑ i, c j i) = 0 ∧ (∑ i, c j i • q i) = 0 ∧
        (∀ i, c j i = 0 ∨ SignType.sign (c j i) = SignType.sign (x i)) ∧
        (∀ w : E → F, (∑ i, w i) = 0 → (∑ i, w i • q i) = 0 → w ≠ 0 →
          Function.support w ⊆ Function.support (c j) →
          Function.support w = Function.support (c j)) := by
  classical
  dsimp only
  let A : Matrix (Fin (d + 1)) E F := fun r i => Fin.cons 1 (q i) r
  have hker (z : E → F) :
      A *ᵥ z = 0 ↔ (∑ i, z i) = 0 ∧ (∑ i, z i • q i) = 0 := by
    constructor
    · intro h
      constructor
      · simpa [A, Matrix.mulVec, dotProduct] using congrFun h 0
      · ext r
        simpa [A, Matrix.mulVec, dotProduct, mul_comm] using congrFun h r.succ
    · rintro ⟨hs, hq⟩
      funext r
      refine Fin.cases ?_ (fun r => ?_) r
      · simpa [A, Matrix.mulVec, dotProduct] using hs
      · simpa [A, Matrix.mulVec, dotProduct, mul_comm] using congrFun hq r
  obtain ⟨n, c, hs, hli, hn, hrank, hc⟩ :=
    signConformalGlobalKernelCircuitDecomposition A x ((hker x).mpr ⟨hxsum, hxq⟩)
  refine ⟨n, c, hs, hli, hn, hrank, fun j => ?_⟩
  exact ⟨(hc j).1, ((hker (c j)).mp (hc j).2.1).1,
    ((hker (c j)).mp (hc j).2.1).2, (hc j).2.2.1,
    fun w hws hwq hwn hsub => (hc j).2.2.2 w ((hker w).mpr ⟨hws, hwq⟩) hwn hsub⟩

-- Exact rational input: a zero column and two equal columns, with both signs present.
#check (signConformalGlobalKernelCircuitDecomposition
  (F := ℚ) (E := Fin 3) (m := 1) ![![0, 1, 1]] ![2, 1, -1]
  (by ext r; fin_cases r; norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]))
-- No row equations, with arbitrary signed rational coordinates.
#check (signConformalGlobalKernelCircuitDecomposition
  (F := ℚ) (E := Fin 2) (m := 0) 0 ![1, -2] (by simp))
-- Empty original label type, retaining a positive number of rows.
#check (signConformalGlobalKernelCircuitDecomposition
  (F := ℚ) (E := Fin 0) (m := 2) 0 0 (by simp))
-- The zero vector has exactly the empty family, by the theorem's support bound.
example (A : Matrix (Fin m) E F) :
    ∃ c : Fin 0 → (E → F), (∑ j, c j) = 0 ∧ LinearIndependent F c := by
  obtain ⟨n, c, hs, hli, hn, _⟩ :=
    signConformalGlobalKernelCircuitDecomposition A 0 (by simp)
  have hn0 : n = 0 := by simpa [support] using hn
  subst n
  exact ⟨c, hs, hli⟩

set_option pp.universes true in
#check @signConformalGlobalKernelCircuitDecomposition
#print axioms box_improvement
#print axioms box_optimality
#print axioms affine_decomposition
#print axioms signConformalGlobalKernelCircuitDecomposition
