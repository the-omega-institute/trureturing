import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

/-! Huang's signed flip operators bipartition the links of a cube vertex. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SignedMidpointLink

open BalancedCriticalSpectrum (Q flip flip_adj gamma gamma_apply IsSwitching switching_sq)
open BalancedCubeGirth (flip_comm gamma_anticommute)

/-- By `gamma_apply`, this is the Huang sign of `x` to `flip x i` times
the switch at `flip x i`. -/
def transportedSwitch {n : Nat} (sigma : Q n → ℝ) (x : Q n) (i : Fin n) : ℝ :=
  gamma i sigma x

/-- A selected double flip joins opposite transported signs on the link of `x`. -/
theorem transportedSwitch_eq_neg {n : Nat} {C : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching C sigma) {x : Q n} {i j : Fin n} (hij : i ≠ j)
    (hi : flip x i ∈ C) (hj : flip x j ∈ C)
    (hcorner : flip (flip x i) j ∈ C) :
    transportedSwitch sigma x i = -transportedSwitch sigma x j := by
  have hcorner' : flip (flip x j) i ∈ C := by
    simpa only [flip_comm x j i] using hcorner
  have step (y : Q n) (k : Fin n) (hy : y ∈ C) (hyk : flip y k ∈ C) :
      gamma k sigma y = sigma y := by
    rw [gamma_apply, hs.2 y hy (flip y k) hyk (flip_adj y k),
      mul_assoc, ← pow_two, switching_sq hs hyk, mul_one]
  have h := congrFun (gamma_anticommute hij sigma) x
  simp only [Pi.neg_apply, gamma_apply i (gamma j sigma) x,
    gamma_apply j (gamma i sigma) x, step (flip x i) j hi hcorner,
    step (flip x j) i hj hcorner'] at h
  simpa only [transportedSwitch, gamma_apply] using h

/-- Each selected neighbour belongs to one of the two transported sign classes. -/
theorem transportedSwitch_eq_one_or_neg_one {n : Nat} {C : Finset (Q n)}
    {sigma : Q n → ℝ} (hs : IsSwitching C sigma) {x : Q n} {i : Fin n}
    (hi : flip x i ∈ C) :
    transportedSwitch sigma x i = 1 ∨ transportedSwitch sigma x i = -1 := by
  apply eq_or_eq_neg_of_abs_eq
  rw [transportedSwitch, gamma_apply, abs_mul,
    SupportedEigenSaturation.matrix_abs_of_adj (flip_adj x i)]
  rcases hs.1 (flip x i) hi with h | h <;> simp [h]

open Classical in
/-- In a balanced cube restriction, ordered links between selected neighbours
of a midpoint number at most half the square of their number. -/
theorem double_card_links_le_square {n : Nat} {C : Finset (Q n)}
    {sigma : Q n → ℝ} (hs : IsSwitching C sigma) (x : Q n) (J : Finset (Fin n))
    (hJ : ∀ i ∈ J, flip x i ∈ C) :
    2 * ((J.product J).filter (fun p =>
      p.1 ≠ p.2 ∧ flip (flip x p.1) p.2 ∈ C)).card ≤ J.card ^ 2 := by
  let plus := J.filter (fun i => transportedSwitch sigma x i = 1)
  let minus := J.filter (fun i => transportedSwitch sigma x i ≠ 1)
  let links := (J.product J).filter (fun p =>
    p.1 ≠ p.2 ∧ flip (flip x p.1) p.2 ∈ C)
  have hpacked : links ⊆ (plus.product minus) ∪ (minus.product plus) := by
    intro p hp
    obtain ⟨hpJ, hijd, hcorner⟩ := Finset.mem_filter.mp hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hpJ
    have hsign := transportedSwitch_eq_neg hs hijd (hJ _ hi) (hJ _ hj) hcorner
    rcases transportedSwitch_eq_one_or_neg_one hs (hJ _ hi) with hpos | hneg
    · have hn : transportedSwitch sigma x p.2 ≠ 1 := by
        intro he
        rw [hpos, he] at hsign
        norm_num at hsign
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hi, hpos⟩, Finset.mem_filter.mpr ⟨hj, hn⟩⟩))
    · have hplus : transportedSwitch sigma x p.2 = 1 := by
        rw [hneg] at hsign
        linarith
      have hn : transportedSwitch sigma x p.1 ≠ 1 := by rw [hneg]; norm_num
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hi, hn⟩, Finset.mem_filter.mpr ⟨hj, hplus⟩⟩))
  have hcard : links.card ≤ plus.card * minus.card + minus.card * plus.card := by
    calc
      links.card ≤ (plus.product minus).card + (minus.product plus).card :=
        (Finset.card_le_card hpacked).trans (Finset.card_union_le _ _)
      _ = _ := congrArg₂ (· + ·) (Finset.card_product plus minus) (Finset.card_product minus plus)
  have hsum : plus.card + minus.card = J.card :=
    Finset.card_filter_add_card_filter_not _
  calc
    _ ≤ 2 * (plus.card * minus.card + minus.card * plus.card) :=
      Nat.mul_le_mul_left _ hcard
    _ = 4 * plus.card * minus.card := by ring
    _ ≤ (plus.card + minus.card) ^ 2 := four_mul_le_sq_add _ _
    _ = J.card ^ 2 := by rw [hsum]

#print axioms transportedSwitch_eq_neg
#print axioms double_card_links_le_square

end D5.S3.Combinatorics.Graph.HypercubeCritical.SignedMidpointLink
