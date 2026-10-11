/- GID: D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Sharp half-circle sign sums and their signed rotation maximizers. -/
/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15265.
proof_shape: content: threshold_of_no_alternation, maximizing_signs_are_thresholds, sharp_norm_eq_iff.
proof_shape: bind-only: IsSign, sign_sq, flip_sum, flip_isSign, maximal_alignment, no_alternation_of_alignment, phase_between, phase, phase_exp, phase_unit, phase_strict_between, radius, threshold, phase_pow, zeta_pow_card, norm_zeta_sub_one, finite_prefix_sum, threshold_sum, threshold_norm, sharp_norm_le, finite_hull_extremes, extra_extreme_of_separation, unique_max_on_hull, exposed_hull_of_unique_max, triple_bound, triple_max_norm_first, triple_max_value, negative_unique_max.
escape_witness: threshold_of_no_alternation = own construction/computation: first sign-change cut constructed from the minimum differing coordinate; maximizing_signs_are_thresholds = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport.threshold_of_no_alternation; sharp_norm_eq_iff = D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport.threshold_of_no_alternation.
-/
import D5.S3.QuantumBounds.PeritoUnitCircleSum
import D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation
import Mathlib.Analysis.Convex.KreinMilman
noncomputable section
open scoped BigOperators ComplexConjugate RealInnerProductSpace InnerProductSpace
open Set
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport
open D5.S3.Quantum.Magic.ErewGoldsteinSICStabilizerRefutation (zeta)
variable {n : ℕ}
def IsSign (a : Fin n → ℝ) : Prop := ∀ i, a i = 1 ∨ a i = -1
private lemma sign_sq {a : ℝ} (ha : a = 1 ∨ a = -1) : a ^ 2 = 1 := sq_eq_one_iff.mpr ha
private lemma flip_sum (v : Fin n → ℂ) (a : Fin n → ℝ) (k : Fin n) : dotProduct (fun i => ((Function.update a k (-a k)) i : ℂ)) v = dotProduct (fun i => (a i : ℂ)) v - (2 * a k : ℝ) * v k := by
  classical
  simp only [dotProduct]; rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ k),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ k)]
  simp only [Function.update_self, Complex.ofReal_neg]; have ht : ∑ i ∈ Finset.univ \ {k}, (Function.update a k (-a k) i : ℂ) * v i =
      ∑ i ∈ Finset.univ \ {k}, (a i : ℂ) * v i := by
    apply Finset.sum_congr rfl; intro i hi; have hik : i ≠ k := by simpa using (Finset.mem_sdiff.mp hi).2
    rw [Function.update_of_ne hik]
  rw [ht]; push_cast; ring
private lemma flip_isSign (a : Fin n → ℝ) (ha : IsSign a) (k : Fin n) : IsSign (Function.update a k (-a k)) := by
  intro i
  by_cases h : i = k
  · subst i
    simp only [Function.update_self]
    rcases ha k with h | h <;> simp [h]
  · rw [Function.update_of_ne h]
    exact ha i
private lemma maximal_alignment (v : Fin n → ℂ) (hv : ∀ i, ‖v i‖ = 1) (a : Fin n → ℝ) (ha : IsSign a) (hm : ∀ b, IsSign b → ‖dotProduct (fun i => (b i : ℂ)) v‖ ≤ ‖dotProduct (fun i => (a i : ℂ)) v‖) (k : Fin n) : 1 ≤ a k * ((dotProduct (fun i => (a i : ℂ)) v) * conj (v k)).re := by
  have h := hm (Function.update a k (-a k)) (flip_isSign a ha k); have hs : Complex.normSq (dotProduct (fun i => ((Function.update a k (-a k)) i : ℂ)) v) ≤
      Complex.normSq (dotProduct (fun i => (a i : ℂ)) v) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (dotProduct (fun i => ((Function.update a k (-a k)) i : ℂ)) v),
      norm_nonneg (dotProduct (fun i => (a i : ℂ)) v)]
  rw [flip_sum, Complex.normSq_sub] at hs; have hvk : Complex.normSq (v k) = 1 := by rw [Complex.normSq_eq_norm_sq, hv]; norm_num
  have hquad : Complex.normSq ((2 * a k : ℝ) * v k) = 4 := by
    rw [Complex.normSq_mul, hvk, mul_one, Complex.normSq_ofReal]; nlinarith [sign_sq (ha k)]
  have hlin : (dotProduct (fun i => (a i : ℂ)) v * conj ((2 * a k : ℝ) * v k)).re =
      (2 * a k) * (dotProduct (fun i => (a i : ℂ)) v * conj (v k)).re := by
    simp only [map_mul, Complex.conj_ofReal]; rw [mul_left_comm, Complex.re_ofReal_mul]
  rw [hquad, hlin] at hs; linarith
private lemma no_alternation_of_alignment (v : Fin n → ℂ) (a : Fin n → ℝ) (ha : IsSign a) (u : ℂ) (hpos : ∀ i, 0 < a i * (u * conj (v i)).re) (hbetween : ∀ l i r : Fin n, l < i → i < r → ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ v i = (α : ℂ) * v l + (β : ℂ) * v r) (l i r : Fin n) (hli : l < i) (hir : i < r) : a i = a l ∨ a i = a r := by
  by_contra! h
  have hal : a l = -a i := by rcases ha l with hl | hl <;> rcases ha i with hi | hi <;> simp_all
  have har : a r = -a i := by rcases ha r with hr | hr <;> rcases ha i with hi | hi <;> simp_all
  obtain ⟨α, β, hα, hβ, hv⟩ := hbetween l i r hli hir
  have he : a i * (u * conj (v i)).re =
      α * (a i * (u * conj (v l)).re) + β * (a i * (u * conj (v r)).re) := by
    rw [hv]; simp only [map_add, map_mul, Complex.conj_ofReal, mul_add, Complex.add_re]; rw [mul_left_comm u (α : ℂ), mul_left_comm u (β : ℂ),
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  have hl := hpos l; have hr := hpos r; rw [hal] at hl; rw [har] at hr; have hleft : α * (a i * (u * conj (v l)).re) < 0 :=
    mul_neg_of_pos_of_neg hα (by nlinarith)
  have hright : β * (a i * (u * conj (v r)).re) < 0 :=
    mul_neg_of_pos_of_neg hβ (by nlinarith)
  linarith [hpos i]
private lemma phase_between (l i r : ℝ) (hli : l < i) (hir : i < r) (hspan : r - l < Real.pi) : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ Complex.exp ((i : ℂ) * Complex.I) = (α : ℂ) * Complex.exp ((l : ℂ) * Complex.I) + (β : ℂ) * Complex.exp ((r : ℂ) * Complex.I) := by
  have hden : 0 < Real.sin (r - l) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hspan; have hα : 0 < Real.sin (r - i) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hβ : 0 < Real.sin (i - l) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  refine ⟨Real.sin (r - i) / Real.sin (r - l), Real.sin (i - l) / Real.sin (r - l),
    div_pos hα hden, div_pos hβ hden, ?_⟩
  have hdne : Real.sin r * Real.cos l - Real.cos r * Real.sin l ≠ 0 := by
    simpa only [Real.sin_sub] using ne_of_gt hden
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      mul_zero, zero_mul, sub_zero, add_zero, Real.sin_sub] <;>
    field_simp [hdne] <;> ring
private lemma threshold_of_no_alternation (hn : 0 < n) (a : Fin n → ℝ) (ha : IsSign a) (hno : ∀ l i r : Fin n, l < i → i < r → a i = a l ∨ a i = a r) : ∃ k : ℕ, k ≤ n ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ i : Fin n, a i = if i.val < k then s else -s := by
  classical
  let o : Fin n := ⟨0, hn⟩; let T : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ a o)
  by_cases hT : T.Nonempty
  · let t : Fin n := T.min' hT
    have htT : t ∈ T := Finset.min'_mem T hT; have htdiff : a t ≠ a o := (Finset.mem_filter.mp htT).2; have hot : o < t := by
      have hotne : o ≠ t := by intro h; exact htdiff (congrArg a h.symm)
      change 0 < t.val; have htne : t.val ≠ 0 := by intro h; exact hotne (Fin.ext h.symm)
      omega
    have hpre : ∀ i : Fin n, i < t → a i = a o := by
      intro i hit
      by_contra hdiff
      have hiT : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩; have hmin := Finset.min'_le T i hiT; exact (not_le_of_gt hit) hmin
    have hpost : ∀ i : Fin n, t ≤ i → a i = -a o := by
      intro i hti; have hdiff : a i ≠ a o := by
        obtain rfl | hlt := eq_or_lt_of_le hti
        · exact htdiff
        · intro he
          rcases hno o t i hot hlt with h | h
          · exact htdiff h
          · exact htdiff (h.trans he)
      rcases ha i with hi | hi <;> rcases ha o with ho | ho <;> simp_all
    refine ⟨t.val, t.isLt.le, a o, ha o, ?_⟩
    intro i
    split_ifs with hit
    · exact hpre i hit
    · exact hpost i (by simpa using (Nat.le_of_not_gt hit))
  · refine ⟨n, le_rfl, a o, ha o, ?_⟩
    intro i; have hi : a i = a o := by
      by_contra hdiff
      exact hT ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff⟩⟩
    simp only [i.isLt, if_true]; exact hi
def phase (n : ℕ) (i : Fin n) : ℂ := zeta n ^ i.val
private lemma phase_exp (i : Fin n) : phase n i =
    Complex.exp (((Real.pi / n * i.val : ℝ) : ℂ) * Complex.I) := by
  dsimp [phase, zeta]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
private lemma phase_unit (i : Fin n) : ‖phase n i‖ = 1 := by
  rw [phase_exp]; exact Complex.norm_exp_ofReal_mul_I _
private lemma phase_strict_between (hn : 0 < n) (l i r : Fin n) (hli : l < i) (hir : i < r) : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ phase n i = (α : ℂ) * phase n l + (β : ℂ) * phase n r := by
  have hp : 0 < Real.pi / n := div_pos Real.pi_pos (by exact_mod_cast hn); simp only [phase_exp]; apply phase_between
  · exact mul_lt_mul_of_pos_left (by exact_mod_cast hli) hp
  · exact mul_lt_mul_of_pos_left (by exact_mod_cast hir) hp
  · have hrn : (r.val : ℝ) < n := by exact_mod_cast r.isLt
    have hl0 : (0 : ℝ) ≤ l.val := Nat.cast_nonneg _; have hh : Real.pi / n * (n : ℝ) = Real.pi := div_mul_cancel₀ _ (by positivity); nlinarith
private lemma maximizing_signs_are_thresholds (hn : 0 < n) (a : Fin n → ℝ) (ha : IsSign a) (hm : ∀ b, IsSign b → ‖dotProduct (fun i => (b i : ℂ)) (phase n)‖ ≤ ‖dotProduct (fun i => (a i : ℂ)) (phase n)‖) : ∃ k : ℕ, k ≤ n ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ i : Fin n, a i = if i.val < k then s else -s := by
  apply threshold_of_no_alternation hn a ha; apply no_alternation_of_alignment (phase n) a ha (dotProduct (fun i => (a i : ℂ)) (phase n))
  · intro i
    linarith [maximal_alignment (phase n) phase_unit a ha hm i]
  · exact phase_strict_between hn
def radius (n : ℕ) : ℝ := 1 / Real.sin (Real.pi / (2 * n))
def threshold (n k : ℕ) (s : ℝ) : Fin n → ℝ := fun i => if i.val < k then s else -s
lemma phase_pow (i : Fin n) : phase n i = zeta n ^ i.val := rfl
lemma zeta_pow_card (hn : 0 < n) : zeta n ^ n = -1 := by
  dsimp [zeta]; rw [← Complex.exp_nat_mul]; convert Complex.exp_pi_mul_I using 1; push_cast
  field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hn.ne']
private lemma norm_zeta_sub_one (hn : 2 ≤ n) : ‖zeta n - 1‖ = 2 * Real.sin (Real.pi / (2 * n)) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < Real.pi / (2 * n) := div_pos Real.pi_pos (by linarith); have hlt : Real.pi / (2 * n) < Real.pi := div_lt_self Real.pi_pos (by linarith); have hsin := (Real.sin_pos_of_pos_of_lt_pi hp hlt).le
  have hz : zeta n = Complex.exp (((Real.pi / n : ℝ) : ℂ) * Complex.I) := by
    unfold zeta
    congr 1
    push_cast
    ring
  rw [hz, mul_comm (_ : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]; have he : Real.pi / (n : ℝ) / 2 = Real.pi / (2 * n) := by ring
  rw [he, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hsin)]
private lemma finite_prefix_sum (f : ℕ → ℂ) (k : ℕ) (hk : k ≤ n) : ∑ i : Fin n, (if i.val < k then f i.val else 0) = ∑ i ∈ Finset.range k, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then f i else 0) n]
  calc
    (∑ i ∈ Finset.range n, if i < k then f i else 0) =
        ∑ i ∈ Finset.range k, if i < k then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk); intro i hin hik; simp only [Finset.mem_range] at hik; simp [hik]
    _ = _ := Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))
lemma threshold_sum (hn : 0 < n) (k : ℕ) (hk : k ≤ n) (s : ℝ) : dotProduct (fun i => ((threshold n k s) i : ℂ)) (phase n) = (s : ℂ) * (2 * zeta n ^ k / (zeta n - 1)) := by
  have hterm (i : Fin n) : (threshold n k s i : ℂ) * phase n i =
      (s : ℂ) * (2 * (if i.val < k then zeta n ^ i.val else 0) - zeta n ^ i.val) := by
    rw [phase_pow]; simp only [threshold]
    split_ifs <;> push_cast <;> ring
  simp only [dotProduct]; simp_rw [hterm]; rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
    finite_prefix_sum (fun i => zeta n ^ i) k hk,
    Fin.sum_univ_eq_sum_range (fun i => zeta n ^ i) n]
  have hz : zeta n ≠ 1 := by
    intro h; have hh := zeta_pow_card hn; rw [h, one_pow] at hh; norm_num at hh
  rw [geom_sum_eq hz, geom_sum_eq hz, zeta_pow_card hn]; congr 1
  field_simp
  ring
lemma threshold_norm (hn : 2 ≤ n) (k : ℕ) (hk : k ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) : ‖dotProduct (fun i => ((threshold n k s) i : ℂ)) (phase n)‖ = radius n := by
  rw [threshold_sum (by omega) k hk, norm_mul, norm_div, norm_mul, norm_pow]; have hs1 : ‖(s : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hz : zeta n = Complex.exp (((Real.pi / n : ℝ) : ℂ) * Complex.I) := by
    unfold zeta
    congr 1
    push_cast
    ring
  have hz1 : ‖zeta n‖ = 1 := by
    rw [hz]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hs1, hz1, one_pow, one_mul, norm_zeta_sub_one hn]; norm_num only [Complex.norm_ofNat, mul_one]; dsimp [radius]; have hsin : Real.sin (Real.pi / (2 * (n : ℝ))) ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply div_lt_self Real.pi_pos
      have hnR : (1 : ℝ) < n := by exact_mod_cast hn
      linarith
  field_simp
lemma sharp_norm_le (hn : 2 ≤ n) (a : Fin n → ℝ) (ha : IsSign a) : ‖dotProduct (fun i => (a i : ℂ)) (phase n)‖ ≤ radius n := by
  classical
  let z : ℂ := dotProduct (fun i => (a i : ℂ)) (phase n)
  let u : ℂ := Complex.exp ((-z.arg : ℂ) * Complex.I)
  have halign : (z * u).re = ‖z‖ := by
    dsimp [u]
    conv_lhs => arg 1; arg 1; rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [mul_assoc, ← Complex.exp_add]
    have hzero : (z.arg : ℂ) * Complex.I + (-z.arg : ℂ) * Complex.I = 0 := by ring
    rw [hzero, Complex.exp_zero, mul_one, Complex.ofReal_re]
  have hterm (i : Fin n) : ((a i : ℂ) * phase n i * u).re =
      a i * Real.cos (-z.arg + Real.pi / n * i.val) := by
    rw [phase_exp]; dsimp [u]
    rw [mul_assoc, ← Complex.exp_add]
    have he : ((Real.pi / n * i.val : ℝ) : ℂ) * Complex.I +
        (-z.arg : ℂ) * Complex.I =
        ((-z.arg + Real.pi / n * i.val : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  calc
    ‖dotProduct (fun i => (a i : ℂ)) (phase n)‖ =
        ∑ i : Fin n, a i * Real.cos (-z.arg + Real.pi / n * i.val) := by
      rw [← halign]
      dsimp [z, dotProduct]
      rw [Finset.sum_mul]
      change Complex.reAddGroupHom _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ ≤ ∑ i : Fin n, |Real.cos (-z.arg + Real.pi / n * i.val)| := by
      apply Finset.sum_le_sum
      intro i _
      rcases ha i with h | h
      · rw [h, one_mul]
        exact le_abs_self _
      · rw [h, neg_one_mul]
        exact neg_le_abs _
    _ = ∑ y ∈ Finset.range n, |Real.cos (-z.arg + Real.pi / n * y)| :=
      Fin.sum_univ_eq_sum_range (fun y : ℕ => |Real.cos (-z.arg + Real.pi / n * y)|) n
    _ ≤ radius n := D5.S3.QuantumBounds.PeritoUnitCircleSum.abs_cos_sum_le n hn (-z.arg)
lemma sharp_norm_eq_iff (hn : 2 ≤ n) (a : Fin n → ℝ) (ha : IsSign a) : ‖dotProduct (fun i => (a i : ℂ)) (phase n)‖ = radius n ↔ ∃ k : ℕ, k ≤ n ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ i : Fin n, a i = if i.val < k then s else -s := by
  constructor
  · intro he
    apply maximizing_signs_are_thresholds (by omega) a ha; intro b hb; rw [he]; exact sharp_norm_le hn b hb
  · rintro ⟨k, hk, s, hs, hform⟩
    have he : a = threshold n k s := funext hform; rw [he]; exact threshold_norm hn k hk s hs
private lemma finite_hull_extremes {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E] (T : Set E) (hT : T.Finite) : convexHull ℝ ((convexHull ℝ T).extremePoints ℝ) = convexHull ℝ T := by
  have hf : ((convexHull ℝ T).extremePoints ℝ).Finite :=
    hT.subset extremePoints_convexHull_subset
  have hc : IsCompact (convexHull ℝ T) := hT.isCompact_convexHull ℝ; have hs : IsClosed (convexHull ℝ ((convexHull ℝ T).extremePoints ℝ)) :=
    (hf.isCompact_convexHull ℝ).isClosed
  simpa [hs.closure_eq] using closure_convexHull_extremePoints hc (convex_convexHull ℝ T)
lemma extra_extreme_of_separation {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E] (T V : Set E) (hT : T.Finite) {p : E} (hp : p ∈ convexHull ℝ T) (hout : p ∉ convexHull ℝ V) : ∃ q ∈ (convexHull ℝ T).extremePoints ℝ, q ∉ V := by
  by_contra! h
  have hsub : (convexHull ℝ T).extremePoints ℝ ⊆ V := h; have hh := convexHull_mono (𝕜 := ℝ) hsub; rw [finite_hull_extremes T hT] at hh; exact hout (hh hp)
private lemma unique_max_on_hull {E : Type*} [AddCommGroup E] [Module ℝ E] (T : Set E) (l : E →ₗ[ℝ] ℝ) (c : ℝ) (v : E) (hb : ∀ x ∈ T,l x ≤ c ∧ (l x=c → x=v)) : ∀ x ∈ convexHull ℝ T,l x ≤ c ∧ (l x=c → x=v) := by
  change convexHull ℝ T ⊆ {x | l x≤c ∧ (l x=c → x=v)}; apply convexHull_min hb; intro x hx y hy a b ha hb hab; change l x≤c ∧ (l x=c → x=v) at hx; change l y≤c ∧ (l y=c → y=v) at hy
  change l (a • x + b • y)≤c ∧ (l (a • x + b • y)=c → a • x + b • y=v); rw [map_add,map_smul,map_smul]; simp only [smul_eq_mul,RingHom.id_apply]; have hxle := hx.1; have hyle := hy.1; have habc : (a+b)*c=c := by rw [hab,one_mul]
  have hleft := mul_nonneg ha (sub_nonneg.mpr hxle); have hright := mul_nonneg hb (sub_nonneg.mpr hyle); constructor
  · nlinarith
  · intro he
    by_cases haz : a=0
    · have hb1 : b=1 := by linarith
      have hey : l y=c := by simpa [haz,hb1] using he
      simp [haz,hb1,hy.2 hey]
    by_cases hbz : b=0
    · have ha1 : a=1 := by linarith
      have hex : l x=c := by simpa [hbz,ha1] using he
      simp [hbz,ha1,hx.2 hex]
    have hap : 0<a := lt_of_le_of_ne ha (Ne.symm haz); have hbp : 0<b := lt_of_le_of_ne hb (Ne.symm hbz); have hleft0 : a*(c-l x)=0 := by nlinarith
    have hright0 : b*(c-l y)=0 := by nlinarith
    have hex : l x=c := by
      have hh := (mul_eq_zero.mp hleft0).resolve_left haz; linarith
    have hey : l y=c := by
      have hh := (mul_eq_zero.mp hright0).resolve_left hbz; linarith
    rw [hx.2 hex,hy.2 hey,← add_smul,hab,one_smul]
lemma exposed_hull_of_unique_max {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (T : Set E) (l : E →L[ℝ] ℝ) (v : E) (hv : v∈T) (hb : ∀ x∈T,l x≤l v ∧ (l x=l v → x=v)) : IsExposed ℝ (convexHull ℝ T) {v} := by
  intro hn
  refine ⟨l,?_⟩
  ext x
  constructor
  · intro hx
    have h : x=v := by simpa using hx
    subst x; exact ⟨subset_convexHull ℝ T hv,fun y hy => (unique_max_on_hull T l.toLinearMap (l v) v hb y hy).1⟩
  · rintro ⟨hx,hm⟩
    have he := hm v (subset_convexHull ℝ T hv); have hh := unique_max_on_hull T l.toLinearMap (l v) v hb x hx; exact hh.2 (le_antisymm hh.1 he)
lemma triple_bound (R : ℝ) (hR : 0<R) (x y z : ℂ) (hx : ‖x‖≤R) (hy : ‖y‖≤R) (hz : ‖z‖≤R) : (x*y*z).re≤R^3 := by
  apply (Complex.re_le_norm _).trans; rw [norm_mul,norm_mul]
  calc
    ‖x‖*‖y‖*‖z‖ ≤ (R*R)*R :=
      mul_le_mul (mul_le_mul hx hy (norm_nonneg _) hR.le) hz (norm_nonneg _) (by positivity)
    _ = R^3 := by ring
private lemma triple_max_norm_first (R : ℝ) (hR : 0<R) (x y z : ℂ) (hx : ‖x‖≤R) (hy : ‖y‖≤R) (hz : ‖z‖≤R) (he : (x*y*z).re=R^3) : ‖x‖=R := by
  have hbc : ‖y‖*‖z‖≤R^2 := by
    simpa [pow_two] using mul_le_mul hy hz (norm_nonneg _) hR.le
  have hh : R*R^2≤‖x‖*R^2 := by
    calc
      R*R^2=R^3 := by ring
      _ = (x*y*z).re := he.symm
      _ ≤ ‖x*y*z‖ := Complex.re_le_norm _
      _ = ‖x‖*(‖y‖*‖z‖) := by rw [norm_mul,norm_mul]; ring
      _ ≤ ‖x‖*R^2 := mul_le_mul_of_nonneg_left hbc (norm_nonneg _)
  exact le_antisymm hx (le_of_mul_le_mul_right hh (sq_pos_of_pos hR))
lemma triple_max_value (R : ℝ) (hR : 0<R) (x y z : ℂ) (hx : ‖x‖≤R) (hy : ‖y‖≤R) (hz : ‖z‖≤R) (he : (x*y*z).re=R^3) : ‖x‖=R ∧ ‖y‖=R ∧ ‖z‖=R ∧ x*y*z=Complex.ofReal (R^3) := by
  have hxx := triple_max_norm_first R hR x y z hx hy hz he; have hyy := triple_max_norm_first R hR y x z hy hx hz (by simpa [mul_comm] using he); have hzz := triple_max_norm_first R hR z x y hz hx hy (by convert he using 1 <;> ring)
  have hnorm : ‖x*y*z‖=R^3 := by rw [norm_mul,norm_mul,hxx,hyy,hzz]; ring
  have him : (x*y*z).im=0 := Complex.abs_re_eq_norm.mp (by rw [he,hnorm,abs_of_nonneg (by positivity)])
  refine ⟨hxx,hyy,hzz,?_⟩
  apply Complex.ext
  · change (x*y*z).re=R^3
    exact he
  · change (x*y*z).im=0
    exact him
lemma negative_unique_max {E : Type*} [AddCommGroup E] [Module ℝ E] (T : Set E) (hneg : ∀ x∈T,-x∈T) (l : E →ₗ[ℝ] ℝ) (v : E) (hb : ∀ x∈T,l x≤l v ∧ (l x=l v → x=v)) : ∀ x∈T,(-l) x≤(-l) (-v) ∧ ((-l) x=(-l) (-v) → x= -v) := by
  intro x hx; have hh := hb (-x) (hneg x hx); simp only [LinearMap.neg_apply,map_neg,neg_neg] at *
  refine ⟨hh.1,?_⟩
  intro he; have heq := hh.2 he; exact neg_eq_iff_eq_neg.mp heq

end D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport
