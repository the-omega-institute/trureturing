/- GID: D5/S3/Combinatorics/Graph/KyFanGap/UniformGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/UniformGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-moment compression transfers the fixed-dimensional defect gap to arbitrary finite point families. -/

import D5.S3.Combinatorics.Graph.KyFanGap.Compactness
import D5.S3.Combinatorics.Graph.KyFanGap.MomentCompression

/-! A bilinear kernel has separately quartic sign defect and quadratic row
defect. Both defects therefore survive fourth-moment compression exactly. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.KyFanGap
open MomentCompression

/-- A diagonal bilinear form on real coordinate vectors. -/
def bilinearKernel {k : ℕ} (q : Fin k → ℝ) (x y : Fin k → ℝ) : ℝ :=
  ∑ i, q i * x i * y i

private def paddedMonomial {k d : ℕ} (hd : d ≤ 4) (f : Fin d → Option (Fin k)) :
    Monomial k :=
  ⟨Finset.univ.val.map f + Multiset.replicate (4 - d) none, by simp; omega⟩

private theorem paddedMonomial_eval {k d : ℕ} (hd : d ≤ 4)
    (f : Fin d → Option (Fin k)) (x : Fin k → ℝ) :
    monomial (paddedMonomial hd f) x = ∏ i, (f i).elim 1 x := by
  simp [monomial, paddedMonomial, Multiset.map_add, Multiset.prod_add,
    Multiset.map_map, Function.comp_def, Finset.prod]

private def monomialCoefficients {k : ℕ} (m : Monomial k) (a : ℝ) : Monomial k → ℝ :=
  fun b => if b = m then a else 0

private theorem monomialCoefficients_eval {k : ℕ} (m : Monomial k) (a : ℝ)
    (x : Fin k → ℝ) : quartic (monomialCoefficients m a) x = a * monomial m x := by
  classical
  simp [quartic, monomialCoefficients]

private theorem affine_power_quartic {k d : ℕ} (hd : d ≤ 4)
    (α : Option (Fin k) → ℝ) :
    ∃ a : Monomial k → ℝ, ∀ x : Fin k → ℝ,
      quartic a x = (∑ i, α i * i.elim 1 x) ^ d := by
  classical
  let a : Monomial k → ℝ := fun m =>
    ∑ f : Fin d → Option (Fin k),
      monomialCoefficients (paddedMonomial hd f) (∏ i, α (f i)) m
  refine ⟨a, ?_⟩
  intro x
  simp only [quartic, a, Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro f _
  change quartic (monomialCoefficients (paddedMonomial hd f) (∏ i, α (f i))) x = _
  rw [monomialCoefficients_eval, paddedMonomial_eval, ← Finset.prod_mul_distrib]

private theorem kernel_power_products {k d : ℕ} (hd : d ≤ 4) (q : Fin k → ℝ) :
    ∃ f g : (Fin d → Fin k) → Monomial k → ℝ,
      ∀ x y : Fin k → ℝ,
        (∑ t, quartic (f t) x * quartic (g t) y) = bilinearKernel q x y ^ d := by
  classical
  let m (t : Fin d → Fin k) := paddedMonomial hd (fun i => some (t i))
  refine ⟨fun t => monomialCoefficients (m t) (∏ i, q (t i)),
    fun t => monomialCoefficients (m t) 1, ?_⟩
  intro x y
  simp_rw [monomialCoefficients_eval]
  simp only [m, paddedMonomial_eval, Option.elim_some, one_mul]
  rw [bilinearKernel, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro t _
  simp [Finset.prod_mul_distrib, mul_assoc]

private theorem kernel_power_average_eq {k n R d : ℕ} (hd : d ≤ 4)
    (q : Fin k → ℝ) (x : Fin n → Fin k → ℝ) (p : Fin R → ℝ)
    (y : Fin R → Fin k → ℝ)
    (h : ∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
      ∑ b, p b * monomial a (y b)) :
    (∑ r, ∑ s, bilinearKernel q (x r) (x s) ^ d) / (n : ℝ)^2 =
      ∑ a, ∑ b, p a * p b * bilinearKernel q (y a) (y b) ^ d := by
  obtain ⟨f, g, hfg⟩ := kernel_power_products hd q
  simpa only [hfg] using product_average_eq x p y h f g

private theorem coordinate_average_eq {k n R : ℕ} (x : Fin n → Fin k → ℝ)
    (p : Fin R → ℝ) (y : Fin R → Fin k → ℝ)
    (h : ∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
      ∑ b, p b * monomial a (y b)) (i : Fin k) :
    (∑ r, x r i) / n = ∑ b, p b * y b i := by
  have hm := h (paddedMonomial (d := 1) (by omega) (fun _ => some i))
  simpa [paddedMonomial_eval] using hm

private theorem kernel_mean {k R : ℕ} (q : Fin k → ℝ) (p : Fin R → ℝ)
    (y : Fin R → Fin k → ℝ) (x : Fin k → ℝ) :
    bilinearKernel q x (fun i => ∑ b, p b * y b i) =
      ∑ b, bilinearKernel q x (y b) * p b := by
  simp only [bilinearKernel, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem row_defect_average_eq {k n R : ℕ} (q : Fin k → ℝ) (c : ℝ)
    (x : Fin n → Fin k → ℝ) (p : Fin R → ℝ) (y : Fin R → Fin k → ℝ)
    (h : ∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
      ∑ b, p b * monomial a (y b)) :
    (∑ r, ((∑ s, bilinearKernel q (x r) (x s)) / n - c) ^ 2) / n =
      ∑ a, p a * ((∑ b, bilinearKernel q (y a) (y b) * p b) - c) ^ 2 := by
  classical
  let m : Fin k → ℝ := fun i => (∑ r, x r i) / n
  let α : Option (Fin k) → ℝ := fun i => i.elim (-c) (fun i => q i * m i)
  obtain ⟨a, ha⟩ := affine_power_quartic (d := 2) (by omega) α
  have hpoly (z : Fin k → ℝ) : quartic a z = (bilinearKernel q z m - c) ^ 2 := by
    rw [ha, Fintype.sum_option]
    congr 1
    simp only [α, Option.elim_none, Option.elim_some, mul_one, bilinearKernel]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hm : m = fun i => ∑ b, p b * y b i := by
    funext i
    exact coordinate_average_eq x p y h i
  have hmx (r : Fin n) : bilinearKernel q (x r) m =
      (∑ s, bilinearKernel q (x r) (x s)) / n := by
    unfold bilinearKernel m
    simp only [mul_div_assoc, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
  have he := quartic_average_eq x p y h a
  simp_rw [hpoly] at he
  rw [show (fun r => (bilinearKernel q (x r) m - c) ^ 2) =
    (fun r => ((∑ s, bilinearKernel q (x r) (x s)) / n - c) ^ 2) from
      funext (fun r => by rw [hmx])] at he
  simpa only [hm, kernel_mean] using he

private theorem sign_defect_average_eq {k n R : ℕ} (q : Fin k → ℝ)
    (x : Fin n → Fin k → ℝ) (p : Fin R → ℝ) (y : Fin R → Fin k → ℝ)
    (h : ∀ a : Monomial k, (∑ r, monomial a (x r)) / n =
      ∑ b, p b * monomial a (y b)) :
    (∑ r, ∑ s, (bilinearKernel q (x r) (x s) ^ 2 - 1) ^ 2) / (n : ℝ)^2 =
      ∑ a, ∑ b, p a * p b * (bilinearKernel q (y a) (y b) ^ 2 - 1) ^ 2 := by
  have h4 := kernel_power_average_eq (d := 4) (by omega) q x p y h
  have h2 := kernel_power_average_eq (d := 2) (by omega) q x p y h
  have h0 := kernel_power_average_eq (d := 0) (by omega) q x p y h
  have hid (t : ℝ) : (t ^ 2 - 1) ^ 2 = t ^ 4 - 2 * t ^ 2 + 1 := by ring
  have hw (u v t : ℝ) : u * v * (t ^ 2 - 1) ^ 2 =
      u * v * t ^ 4 - 2 * (u * v * t ^ 2) + u * v * 1 := by ring
  simp_rw [hid, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [add_div, sub_div, mul_div_assoc]
  rw [h4, h2]
  simp only [pow_zero] at h0
  rw [h0]
  simp_rw [← hid]
  conv_rhs =>
    arg 2
    intro a
    arg 2
    intro b
    rw [hw]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The sign and row-sum defects of an empirical bilinear kernel. -/
def empiricalDefect {k n : ℕ} (q : Fin k → ℝ) (x : Fin n → Fin k → ℝ) (c : ℝ) : ℝ :=
  (∑ r, ∑ s, (bilinearKernel q (x r) (x s) ^ 2 - 1) ^ 2) / (n : ℝ)^2 +
    (∑ r, ((∑ s, bilinearKernel q (x r) (x s)) / n - c) ^ 2) / n

private theorem exists_compressed_model {k n : ℕ} (hn : 0 < n)
    (q : Fin k → ℝ) (x : Fin n → Fin k → ℝ) (c M : ℝ)
    (hbound : ∀ r s, |bilinearKernel q (x r) (x s)| ≤ M) :
    ∃ (p : Fin (nodeCount k) → ℝ)
      (S : Matrix (Fin (nodeCount k)) (Fin (nodeCount k)) ℝ),
      (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧ S.IsSymm ∧
      (∀ a b, |S a b| ≤ M) ∧ modelDefect p S c = empiricalDefect q x c := by
  obtain ⟨p, y, hp, hsum, hy, hm⟩ := exists_moment_compression hn x
  let S : Matrix (Fin (nodeCount k)) (Fin (nodeCount k)) ℝ :=
    fun a b => bilinearKernel q (y a) (y b)
  refine ⟨p, S, hp, hsum, ?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro a b
    unfold S bilinearKernel
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro a b
    obtain ⟨r, hr⟩ := hy a
    obtain ⟨s, hs⟩ := hy b
    simpa only [S, ← hr, ← hs] using hbound r s
  · unfold modelDefect empiricalDefect S
    rw [sign_defect_average_eq q x p y hm, row_defect_average_eq q c x p y hm]

/-- A bounded bilinear kernel in a fixed nonsquare coordinate dimension has a
positive empirical defect gap, uniformly over the number of sampled points. -/
theorem bilinear_defect_gap {k : ℕ} (hk : ¬ IsSquare k) (M : ℝ) :
    ∃ η > 0, ∀ (n : ℕ), 0 < n → ∀ (q : Fin k → ℝ) (x : Fin n → Fin k → ℝ),
      (∀ r s, |bilinearKernel q (x r) (x s)| ≤ M) →
        η ≤ empiricalDefect q x (1 / Real.sqrt k) := by
  obtain ⟨η, hη, hg⟩ := exists_model_defect_gap (nodeCount k) M hk
  refine ⟨η, hη, ?_⟩
  intro n hn q x hb
  obtain ⟨p, S, hp, hs, hsym, hbound, he⟩ :=
    exists_compressed_model hn q x (1 / Real.sqrt k) M hb
  rw [← he]
  exact hg p S hp hs hsym hbound

end D5.S3.Combinatorics.Graph.KyFanGap
