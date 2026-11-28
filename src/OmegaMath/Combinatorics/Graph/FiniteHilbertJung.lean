import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.Dirac
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-!
Omega original.

# Finite Hilbert Jung centers and chordal reconstruction

For at most `k` points of diameter at most `D`, the center has radius at most
`sqrt ((k-1)/(2*k)) * D`. For a finite chordal graph with clique number at most
`k+1`, this yields gain reconstruction error at most `J_k/(1-J_k) * ε`.

The geometric argument maximizes weighted variance on Mathlib's compact standard
simplex. Moving toward a vertex proves the enclosing inequalities; the weighted
variance identity gives active boundary witnesses and global minimality. The
pair-distance identity and Cauchy--Schwarz give the finite cardinality bound.
No finite dimensionality or completeness of the ambient inner product space is
required. The graph extension follows the simplicial induction pattern of
`SimplicialAndIntervalPotential`, replacing its mean estimate by a geometric
center interface rather than repeating its existing Banach theorem.
-/

open scoped BigOperators InnerProductSpace

namespace FiniteHilbertJung

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type v} [Fintype ι]

noncomputable def center (p : ι → E) (w : ι → ℝ) : E := ∑ i, w i • p i

noncomputable def variance (p : ι → E) (w : ι → ℝ) : ℝ :=
  ∑ i, w i * ‖p i‖ ^ 2 - ‖center p w‖ ^ 2

lemma weighted_sq (p : ι → E) (w : ι → ℝ) (hw : ∑ i, w i = 1) (z : E) :
    ∑ i, w i * ‖p i - z‖ ^ 2 = variance p w + ‖center p w - z‖ ^ 2 := by
  simp only [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
  have hi : ∑ i, w i * (2 * ⟪p i, z⟫_ℝ) = 2 * ⟪center p w, z⟫_ℝ := by
    simp only [center, sum_inner, real_inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hi]
  unfold variance
  ring

lemma pair_sq (p : ι → E) (w : ι → ℝ) (hw : ∑ i, w i = 1) :
    ∑ i, ∑ j, w i * w j * ‖p i - p j‖ ^ 2 = 2 * variance p w := by
  have hinner : ∑ i, ∑ j, w i * w j * ⟪p i, p j⟫_ℝ = ‖center p w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [center, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [real_inner_comm (p i) (p j)]))
  simp only [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have hleft : ∑ i, ∑ j, w i * w j * ‖p i‖ ^ 2 = ∑ i, w i * ‖p i‖ ^ 2 := by
    simp_rw [show ∀ i j, w i * w j * ‖p i‖ ^ 2 = (w i * ‖p i‖ ^ 2) * w j by intros; ring,
      ← Finset.mul_sum, hw, mul_one]
  have hright : ∑ i, ∑ j, w i * w j * ‖p j‖ ^ 2 = ∑ j, w j * ‖p j‖ ^ 2 := by
    simp [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hw]
  have hmiddle : ∑ i, ∑ j, w i * w j * (2 * ⟪p i, p j⟫_ℝ) =
      2 * ‖center p w‖ ^ 2 := by
    rw [← hinner]
    simp [Finset.mul_sum, mul_left_comm, mul_assoc]
  rw [hleft, hright, hmiddle]
  unfold variance
  ring

lemma polynomial_maximum {A B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * A - t ^ 2 * B ≤ 0) : A ≤ 0 := by
  by_contra hn
  have hA : 0 < A := lt_of_not_ge hn
  let t := A / (A + B + 1)
  have hd : 0 < A + B + 1 := by positivity
  have ht : 0 < t := div_pos hA hd
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  have he : t * (A + B + 1) = A := div_mul_cancel₀ _ hd.ne'
  have hh := h t ht.le ht1
  have hAB : A ≤ t * B := by nlinarith
  nlinarith [mul_pos ht hA]

lemma variance_move [DecidableEq ι] (p : ι → E) (w : ι → ℝ)
    (i : ι) (t : ℝ) :
    variance p (fun j => (1 - t) * w j + t * (if j = i then 1 else 0)) =
      variance p w + t * (‖p i - center p w‖ ^ 2 - variance p w) -
        t ^ 2 * ‖p i - center p w‖ ^ 2 := by
  classical
  have hc : center p (fun j => (1 - t) * w j + t * (if j = i then 1 else 0)) =
      (1 - t) • center p w + t • p i := by
    simp [center, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
      Finset.sum_ite_eq']
  have hs : ∑ j, ((1 - t) * w j + t * (if j = i then 1 else 0)) * ‖p j‖ ^ 2 =
      (1 - t) * ∑ j, w j * ‖p j‖ ^ 2 + t * ‖p i‖ ^ 2 := by
    simp [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', mul_ite]
  unfold variance
  rw [hc, hs, norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, real_inner_smul_left, real_inner_smul_right,
    norm_sub_sq_real, real_inner_comm (p i) (center p w)]
  simp only [mul_pow, sq_abs]
  ring

/-- A finite family has a convex-combination center whose squared distances are
bounded by the maximum weighted variance. Positive weights are active witnesses. -/
theorem exists_variance_center [Nonempty ι] (p : ι → E) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∀ i, ‖p i - center p w‖ ^ 2 ≤ variance p w) ∧
      (∀ i, 0 < w i → ‖p i - center p w‖ ^ 2 = variance p w) := by
  classical
  have hcont : Continuous (variance p) := by
    unfold variance center
    fun_prop
  let K : Set (ι → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
  have hcompact : IsCompact K := by
    have he : K = Set.range (fun t : Convexity.StdSimplex ℝ ι => (t.weights : ι → ℝ)) := by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      ext w
      simp [K]
    rw [he]
    simpa only [Set.image_univ] using
      (isCompact_univ : IsCompact (Set.univ : Set (Convexity.StdSimplex ℝ ι))).image
        (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous
  have hne : K.Nonempty := by
    refine ⟨fun j => if j = Classical.arbitrary ι then 1 else 0, ?_, ?_⟩
    · intro j; dsimp only; split_ifs <;> positivity
    · simp
  obtain ⟨w, hw, hmax⟩ := hcompact.exists_isMaxOn hne hcont.continuousOn
  have hbound (i : ι) : ‖p i - center p w‖ ^ 2 ≤ variance p w := by
    have hpoly : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        t * (‖p i - center p w‖ ^ 2 - variance p w) -
          t ^ 2 * ‖p i - center p w‖ ^ 2 ≤ 0 := by
      intro t ht ht1
      have hv : (fun j => (1 - t) * w j + t * (if j = i then 1 else 0)) ∈
          K := by
        refine ⟨fun j => add_nonneg (mul_nonneg (by linarith) (hw.1 j))
          (mul_nonneg ht (by split_ifs <;> positivity)), ?_⟩
        simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2, mul_ite]
      have hh := hmax hv
      change variance p (fun j => (1 - t) * w j + t * (if j = i then 1 else 0)) ≤ variance p w at hh
      rw [variance_move p w i t] at hh
      linarith
    have hh := polynomial_maximum (sq_nonneg ‖p i - center p w‖) hpoly
    linarith
  refine ⟨w, hw.1, hw.2, hbound, ?_⟩
  have hsum : ∑ i, w i * (variance p w - ‖p i - center p w‖ ^ 2) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw.2, one_mul,
      weighted_sq p w hw.2 (center p w)]
    simp
  intro i hi
  have hle := Finset.single_le_sum
    (f := fun j => w j * (variance p w - ‖p j - center p w‖ ^ 2))
    (fun j _ => mul_nonneg (hw.1 j) (sub_nonneg.mpr (hbound j))) (Finset.mem_univ i)
  rw [hsum] at hle
  have := nonpos_of_mul_nonpos_right hle hi
  linarith [hbound i]

/-- A finite family in an arbitrary real inner product space has a smallest
closed enclosing ball. Its center is a convex combination of the given points,
and every positive-weight point lies on the boundary. -/
theorem exists_smallest_enclosing_ball [Nonempty ι] (p : ι → E) :
    ∃ (c : E) (r : ℝ) (w : ι → ℝ),
      0 ≤ r ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ center p w = c ∧
      (∀ i, ‖p i - c‖ ≤ r) ∧
      (∀ i, 0 < w i → ‖p i - c‖ = r) ∧
      (∀ (z : E) (R : ℝ), 0 ≤ R → (∀ i, ‖p i - z‖ ≤ R) → r ≤ R) := by
  obtain ⟨w, hw₀, hw₁, hb, hactive⟩ := exists_variance_center p
  have hV : 0 ≤ variance p w := (sq_nonneg _).trans (hb (Classical.arbitrary ι))
  have hr := Real.sq_sqrt hV
  refine ⟨center p w, Real.sqrt (variance p w), w, Real.sqrt_nonneg _, hw₀, hw₁, rfl,
    ?_, ?_, ?_⟩
  · intro i
    nlinarith [hb i, norm_nonneg (p i - center p w), Real.sqrt_nonneg (variance p w)]
  · intro i hi
    have hh := hactive i hi
    nlinarith [norm_nonneg (p i - center p w), Real.sqrt_nonneg (variance p w)]
  · intro z R hR hcover
    have hh : ∑ i, w i * ‖p i - z‖ ^ 2 ≤ R ^ 2 := by
      calc
        _ ≤ ∑ i, w i * R ^ 2 := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hcover i) 2) (hw₀ i))
        _ = _ := by rw [← Finset.sum_mul, hw₁, one_mul]
    rw [weighted_sq p w hw₁ z] at hh
    nlinarith [sq_nonneg ‖center p w - z‖, Real.sqrt_nonneg (variance p w)]

/-- Maximum weighted variance is bounded by the diameter and number of points. -/
theorem variance_le (p : ι → E) (w : ι → ℝ) (hw₀ : ∀ i, 0 ≤ w i)
    (hw₁ : ∑ i, w i = 1) (k : ℕ) (hk : 1 ≤ k) (hcard : Fintype.card ι ≤ k)
    {D : ℝ} (_hD : 0 ≤ D) (hdiam : ∀ i j, ‖p i - p j‖ ≤ D) :
    variance p w ≤ ((k : ℝ) - 1) / (2 * k) * D ^ 2 := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hsum : ∑ i, ∑ j, w i * w j * ‖p i - p j‖ ^ 2 ≤
      (1 - ∑ i, w i ^ 2) * D ^ 2 := by
    calc
      _ ≤ ∑ i, ∑ j, (w i * w j - if i = j then w i ^ 2 else 0) * D ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        by_cases hij : i = j
        · subst j
          simp [pow_two]
        · simp only [hij, ite_false, sub_zero]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hdiam i j) 2) (mul_nonneg (hw₀ i) (hw₀ j))
      _ = _ := by
        simp [sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ← Finset.mul_sum, hw₁, mul_assoc]
  rw [pair_sq p w hw₁] at hsum
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w)
  rw [hw₁, one_pow, Finset.card_univ] at hcs
  have hcs' : 1 ≤ (k : ℝ) * ∑ i, w i ^ 2 := hcs.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hrec : 1 / (k : ℝ) ≤ ∑ i, w i ^ 2 :=
    (div_le_iff₀ hkR).2 (by nlinarith)
  have he : ((k : ℝ) - 1) / (2 * k) = (1 - 1 / (k : ℝ)) / 2 := by field_simp
  rw [he]
  nlinarith [mul_nonneg (sub_nonneg.mpr hrec) (sq_nonneg D)]

/-- Finite Hilbert Jung theorem, including a convex-hull center, valid in every
real inner product space, with at most `k` points. -/
theorem exists_jung_center [Nonempty ι] (p : ι → E) (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card ι ≤ k) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ i j, ‖p i - p j‖ ≤ D) :
    ∃ c ∈ convexHull ℝ (Set.range p),
      ∀ i, ‖p i - c‖ ≤ Real.sqrt (((k : ℝ) - 1) / (2 * k)) * D := by
  obtain ⟨w, hw₀, hw₁, hb, _⟩ := exists_variance_center p
  refine ⟨center p w, mem_convexHull_of_exists_fintype w p hw₀ hw₁
    (fun i => Set.mem_range_self i) rfl, fun i => ?_⟩
  have hv := variance_le p w hw₀ hw₁ k hk hcard hD hdiam
  have hq : 0 ≤ ((k : ℝ) - 1) / (2 * k) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have hs := Real.sq_sqrt hq
  have hn := mul_nonneg (Real.sqrt_nonneg (((k : ℝ) - 1) / (2 * k))) hD
  have hb' := hb i
  nlinarith [sq_nonneg (‖p i - center p w‖ - Real.sqrt (((k : ℝ) - 1) / (2 * k)) * D)]

end FiniteHilbertJung

namespace SimpleGraph

universe u v

/-- Reverse simplicial elimination with an arbitrary finite Jung-center estimate.
This isolates the geometric input from the chordal extension argument. -/
theorem IsChordal.exists_gain_potential_of_finite_center
    {V : Type u} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hcenter : ∀ (S : Finset V) (p : V → E) (D : ℝ), 0 ≤ D → S.card ≤ k →
      (∀ x ∈ S, ∀ y ∈ S, ‖p x - p y‖ ≤ D) →
      ∃ c : E, ∀ x ∈ S, ‖p x - c‖ ≤ q * D)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ q / (1 - q) * ε := by
  classical
  let := Fintype.ofFinite V
  let C := q / (1 - q)
  have hC : 0 ≤ C := div_nonneg hq (by linarith)
  have hfix : q * (C + 1) = C := by dsimp [C]; field_simp; ring
  have hmain (S : Finset V) : ∃ φ : V → E, ∀ u ∈ S, ∀ v ∈ S, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ C * ε := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hs : S.Nonempty
      · let : Nonempty (↑S : Set V) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
        obtain ⟨z, hz⟩ := (hG.induce (S : Set V)).exists_isSimplicial
        let a : V := z.val
        have ha : a ∈ S := z.property
        obtain ⟨ψ, hψ⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        let N := S.filter fun w => G.Adj w a
        have memN {w : V} : w ∈ N ↔ w ∈ S ∧ G.Adj w a := Finset.mem_filter
        have haN : a ∉ N := fun h => (memN.mp h).2.ne rfl
        have adjN {x y : V} (hx : x ∈ N) (hy : y ∈ N) (hne : x ≠ y) : G.Adj x y :=
          hz (show (⟨x, (memN.mp hx).1⟩ : (S : Set V)) ∈ _ from (memN.mp hx).2.symm)
            (show (⟨y, (memN.mp hy).1⟩ : (S : Set V)) ∈ _ from (memN.mp hy).2.symm)
            (by simpa [Subtype.ext_iff] using hne)
        have hcl : G.IsClique (↑(insert a N) : Set V) := by
          intro x hx y hy hxy
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
          rcases hx with rfl | hx
          · exact (memN.mp (hy.resolve_left hxy.symm)).2.symm
          · rcases hy with rfl | hy
            · exact (memN.mp hx).2
            · exact adjN hx hy hxy
        have hNk := hclique (insert a N) hcl
        rw [Finset.card_insert_of_notMem haN] at hNk
        have hNk' : N.card ≤ k := by omega
        let p (w : V) := ψ w + g w a
        have hB : 0 ≤ (C + 1) * ε := mul_nonneg (by linarith) hε
        have pair (x : V) (hx : x ∈ N) (y : V) (hy : y ∈ N) :
            ‖p x - p y‖ ≤ (C + 1) * ε := by
          by_cases hxy : x = y
          · subst y; simpa using hB
          have hxa := (memN.mp hx).2
          have hya := (memN.mp hy).2
          have hx' : x ∈ S.erase a := Finset.mem_erase.mpr ⟨hxa.ne, (memN.mp hx).1⟩
          have hy' : y ∈ S.erase a := Finset.mem_erase.mpr ⟨hya.ne, (memN.mp hy).1⟩
          have hxy' := adjN hx hy hxy
          have he : p x - p y = (g x y - (ψ y - ψ x)) - (g x y + g y a - g x a) := by
            dsimp [p]; abel
          rw [he]
          exact (norm_sub_le _ _).trans (by linarith [hψ x hx' y hy' hxy', htri x y a hxy' hya hxa])
        obtain ⟨c, hc⟩ := hcenter N p ((C + 1) * ε) hB hNk' pair
        let φ (w : V) := if w = a then c else ψ w
        have new {x : V} (hx : x ∈ N) : ‖g x a - (φ a - φ x)‖ ≤ C * ε := by
          have hxa := (memN.mp hx).2
          have he : g x a - (φ a - φ x) = p x - c := by
            simp only [φ, ite_true, hxa.ne, ite_false, p]; abel
          rw [he]
          calc
            _ ≤ q * ((C + 1) * ε) := hc x hx
            _ = C * ε := by rw [← mul_assoc, hfix]
        refine ⟨φ, fun x hx y hy hxy => ?_⟩
        by_cases hxa : x = a
        · subst x
          rw [hrev y a, show -(g y a) - (φ y - φ a) = -(g y a - (φ a - φ y)) by abel, norm_neg]
          exact new (memN.mpr ⟨hy, hxy.symm⟩)
        · by_cases hya : y = a
          · subst y
            exact new (memN.mpr ⟨hx, hxy⟩)
          · simpa only [φ, hxa, hya, ite_false] using
              hψ x (Finset.mem_erase.mpr ⟨hxa, hx⟩) y (Finset.mem_erase.mpr ⟨hya, hy⟩) hxy
      · exact ⟨fun _ => 0, fun x hx => (hs ⟨x, hx⟩).elim⟩
  obtain ⟨φ, hφ⟩ := hmain Finset.univ
  exact ⟨φ, fun x y hxy => hφ x (Finset.mem_univ _) y (Finset.mem_univ _) hxy⟩

end SimpleGraph
