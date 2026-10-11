/- GID: D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Sharp half-circle sign sums and their signed rotation maximizers. -/
/-
proof_shape: zeta_pow_card: bind-only; escape_witness: none.
proof_shape: freqPhase_decomposition: bind-only; escape_witness: none.
proof_shape: freqSign_sign: bind-only; escape_witness: none.
proof_shape: odd_frequency_norm_le: bind-only; escape_witness: none.
proof_shape: frequency_order: bind-only; escape_witness: none.
proof_shape: baseSigns_sum: bind-only; escape_witness: none.
proof_shape: rotation_eval: bind-only; escape_witness: none.
proof_shape: norm_maximizers_are_rotations: content; escape_witness: maximizing_signs_are_thresholds.
proof_shape: radius17_pos: bind-only; escape_witness: none.
proof_shape: extra_extreme_of_separation: bind-only; escape_witness: none.
proof_shape: not_affine_cross_of_many_extreme: bind-only; escape_witness: none.
proof_shape: exposed_hull_of_unique_max: bind-only; escape_witness: none.
proof_shape: root_reduce: bind-only; escape_witness: none.
proof_shape: root_reflect: bind-only; escape_witness: none.
proof_shape: triple_bound: bind-only; escape_witness: none.
proof_shape: triple_max_value: bind-only; escape_witness: none.
proof_shape: negative_unique_max: bind-only; escape_witness: none.
proof_shape: halfcircle_cos_sign: bind-only; escape_witness: none.
admission_basis: escape-witness
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15265.
The equality characterization constructs the first sign change of a maximizing
sign vector and excludes every later reversal; a finite rotation witness identifies it.
Private theorem/lemma classifications (all have live consumers):
proof_shape content: threshold_of_no_alternation, maximizing_signs_are_thresholds, sharp_norm_eq_iff, odd_frequency_norm_eq_iff.
proof_shape bind-only: sign_sq, flip_sum, flip_isSign, maximal_alignment, no_alternation_of_alignment, phase_between, phase_unit,
  phase_strict_between, phase_pow, norm_zeta_sub_one, finite_prefix_sum, threshold_sum, threshold_norm, sign_set_finite, sharp_norm_le,
  freqIndex_injective, reindex_signedSum, threshold_rotation, zeta_primitive, frequency_coprime, zeta17_denom, threshold9_sum, halfperiod_phase,
  rotatedSigns_neg, affine_extreme_image, finite_hull_extremes, unique_max_on_hull, triple_max_norm_first.
Private helpers carry escape_witness: none; admission is the host module basis.
-/
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Data.Real.Sign
noncomputable section
open scoped BigOperators ComplexConjugate RealInnerProductSpace InnerProductSpace
open Set
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport
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
def phase (n : ℕ) (i : Fin n) : ℂ :=
  Complex.exp (((Real.pi / n * i.val : ℝ) : ℂ) * Complex.I)
private lemma phase_unit (i : Fin n) : ‖phase n i‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _
private lemma phase_strict_between (hn : 0 < n) (l i r : Fin n) (hli : l < i) (hir : i < r) : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ phase n i = (α : ℂ) * phase n l + (β : ℂ) * phase n r := by
  have hp : 0 < Real.pi / n := div_pos Real.pi_pos (by exact_mod_cast hn); apply phase_between
  · exact mul_lt_mul_of_pos_left (by exact_mod_cast hli) hp
  · exact mul_lt_mul_of_pos_left (by exact_mod_cast hir) hp
  · have hrn : (r.val : ℝ) < n := by exact_mod_cast r.isLt
    have hl0 : (0 : ℝ) ≤ l.val := Nat.cast_nonneg _; have hh : Real.pi / n * (n : ℝ) = Real.pi := div_mul_cancel₀ _ (by positivity); nlinarith
private lemma maximizing_signs_are_thresholds (hn : 0 < n) (a : Fin n → ℝ) (ha : IsSign a) (hm : ∀ b, IsSign b → ‖dotProduct (fun i => (b i : ℂ)) (phase n)‖ ≤ ‖dotProduct (fun i => (a i : ℂ)) (phase n)‖) : ∃ k : ℕ, k ≤ n ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ i : Fin n, a i = if i.val < k then s else -s := by
  apply threshold_of_no_alternation hn a ha; apply no_alternation_of_alignment (phase n) a ha (dotProduct (fun i => (a i : ℂ)) (phase n))
  · intro i
    linarith [maximal_alignment (phase n) phase_unit a ha hm i]
  · exact phase_strict_between hn
def zeta (n : ℕ) : ℂ := Complex.exp (((Real.pi / n : ℝ) : ℂ) * Complex.I)
def radius (n : ℕ) : ℝ := 1 / Real.sin (Real.pi / (2 * n))
private def threshold (n k : ℕ) (s : ℝ) : Fin n → ℝ := fun i => if i.val < k then s else -s
private lemma phase_pow (i : Fin n) : phase n i = zeta n ^ i.val := by dsimp [phase, zeta]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
lemma zeta_pow_card (hn : 0 < n) : zeta n ^ n = -1 := by
  dsimp [zeta]; rw [← Complex.exp_nat_mul]; convert Complex.exp_pi_mul_I using 1; push_cast
  field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hn.ne']
private lemma norm_zeta_sub_one (hn : 2 ≤ n) : ‖zeta n - 1‖ = 2 * Real.sin (Real.pi / (2 * n)) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < Real.pi / (2 * n) := div_pos Real.pi_pos (by linarith); have hlt : Real.pi / (2 * n) < Real.pi := div_lt_self Real.pi_pos (by linarith); have hsin := (Real.sin_pos_of_pos_of_lt_pi hp hlt).le
  dsimp [zeta]; rw [mul_comm (_ : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]; have he : Real.pi / (n : ℝ) / 2 = Real.pi / (2 * n) := by ring
  rw [he, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hsin)]
private lemma finite_prefix_sum (f : ℕ → ℂ) (k : ℕ) (hk : k ≤ n) : ∑ i : Fin n, (if i.val < k then f i.val else 0) = ∑ i ∈ Finset.range k, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then f i else 0) n]
  calc
    (∑ i ∈ Finset.range n, if i < k then f i else 0) =
        ∑ i ∈ Finset.range k, if i < k then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk); intro i hin hik; simp only [Finset.mem_range] at hik; simp [hik]
    _ = _ := Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))
private lemma threshold_sum (hn : 0 < n) (k : ℕ) (hk : k ≤ n) (s : ℝ) : dotProduct (fun i => ((threshold n k s) i : ℂ)) (phase n) = (s : ℂ) * (2 * zeta n ^ k / (zeta n - 1)) := by
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
private lemma threshold_norm (hn : 2 ≤ n) (k : ℕ) (hk : k ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) : ‖dotProduct (fun i => ((threshold n k s) i : ℂ)) (phase n)‖ = radius n := by
  rw [threshold_sum (by omega) k hk, norm_mul, norm_div, norm_mul, norm_pow]; have hs1 : ‖(s : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hz1 : ‖zeta n‖ = 1 := Complex.norm_exp_ofReal_mul_I _; rw [hs1, hz1, one_pow, one_mul, norm_zeta_sub_one hn]; norm_num only [Complex.norm_ofNat, mul_one]; dsimp [radius]; have hsin : Real.sin (Real.pi / (2 * (n : ℝ))) ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply div_lt_self Real.pi_pos
      have hnR : (1 : ℝ) < n := by exact_mod_cast hn
      linarith
  field_simp
private lemma sign_set_finite : {a : Fin n → ℝ | IsSign a}.Finite := by
  classical
  let f : (Fin n → Bool) → (Fin n → ℝ) := fun b i => if b i then 1 else -1
  apply (Set.finite_range f).subset; intro a ha
  refine ⟨(fun i => decide (a i = 1)), ?_⟩
  funext i; dsimp [f]
  rcases ha i with h | h <;> norm_num [h]
private lemma sharp_norm_le (hn : 2 ≤ n) (a : Fin n → ℝ) (ha : IsSign a) : ‖dotProduct (fun i => (a i : ℂ)) (phase n)‖ ≤ radius n := by
  obtain ⟨b, hb, hmax⟩ := Set.exists_max_image {b | IsSign b}
    (fun b => ‖dotProduct (fun i => (b i : ℂ)) (phase n)‖) sign_set_finite ⟨a, ha⟩
  obtain ⟨k, hk, s, hs, hform⟩ := maximizing_signs_are_thresholds (by omega) b hb hmax
  have hbform : b = threshold n k s := funext hform; have he := threshold_norm hn k hk s hs; rw [← hbform] at he; exact (hmax a ha).trans_eq he
private lemma sharp_norm_eq_iff (hn : 2 ≤ n) (a : Fin n → ℝ) (ha : IsSign a) : ‖dotProduct (fun i => (a i : ℂ)) (phase n)‖ = radius n ↔ ∃ k : ℕ, k ≤ n ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ i : Fin n, a i = if i.val < k then s else -s := by
  constructor
  · intro he
    apply maximizing_signs_are_thresholds (by omega) a ha; intro b hb; rw [he]; exact sharp_norm_le hn b hb
  · rintro ⟨k, hk, s, hs, hform⟩
    have he : a = threshold n k s := funext hform; rw [he]; exact threshold_norm hn k hk s hs
def freqIndex (j : ℕ) (x : Fin 17) : Fin 17 := ⟨(j * x.val) % 17, by omega⟩
def freqSign (j : ℕ) (x : Fin 17) : ℝ := (-1) ^ (j * x.val / 17)
def freqPhase (j : ℕ) (x : Fin 17) : ℂ := zeta 17 ^ (j * x.val)
lemma freqPhase_decomposition (j : ℕ) (x : Fin 17) : freqPhase j x = (freqSign j x : ℂ) * phase 17 (freqIndex j x) := by
  have hdecomp := Nat.mod_add_div (j * x.val) 17; dsimp [freqPhase, freqSign]; rw [phase_pow]; change zeta 17 ^ (j * x.val) = ↑((-1 : ℝ) ^ (j * x.val / 17)) *
    zeta 17 ^ ((j * x.val) % 17)
  nth_rw 1 [← hdecomp]
  rw [pow_add, pow_mul, zeta_pow_card (by norm_num)]; push_cast; ring
lemma freqSign_sign (j : ℕ) (x : Fin 17) : freqSign j x = 1 ∨ freqSign j x = -1 := by dsimp [freqSign]; exact neg_one_pow_eq_or (R := ℝ) _
private lemma freqIndex_injective (j : Fin 8) : Function.Injective (freqIndex (2 * j.val + 1)) := by fin_cases j <;> decide
private lemma reindex_signedSum (j : Fin 8) (a : Fin 17 → ℝ) : ∃ b : Fin 17 → ℝ, (IsSign a → IsSign b) ∧ dotProduct (fun i => (a i : ℂ)) (freqPhase (2 * j.val + 1)) = dotProduct (fun i => (b i : ℂ)) (phase 17) ∧ ∀ x, b (freqIndex (2*j.val+1) x) = a x * freqSign (2*j.val+1) x := by
  classical
  let e : Fin 17 ≃ Fin 17 := Equiv.ofBijective (freqIndex (2 * j.val + 1))
    ⟨freqIndex_injective j, Finite.surjective_of_injective (freqIndex_injective j)⟩
  let b : Fin 17 → ℝ := fun y => a (e.symm y) * freqSign (2 * j.val + 1) (e.symm y)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro ha y
    rcases ha (e.symm y) with h | h <;>
      rcases freqSign_sign (2*j.val+1) (e.symm y) with hs | hs <;> simp [b, h, hs]
  · dsimp [dotProduct]
    rw [← Equiv.sum_comp e (fun y => (b y : ℂ) * phase 17 y)]
    apply Finset.sum_congr rfl; intro x hx; simp only [b, Equiv.symm_apply_apply]; rw [freqPhase_decomposition]; change (a x : ℂ) * ((freqSign (2*j.val+1) x : ℂ) * phase 17 (e x)) =
      ((a x * freqSign (2*j.val+1) x : ℝ) : ℂ) * phase 17 (e x)
    push_cast; ring
  · intro x
    change b (e x) = a x * freqSign (2*j.val+1) x; simp [b]
lemma odd_frequency_norm_le (j : Fin 8) (a : Fin 17 → ℝ) (ha : IsSign a) : ‖dotProduct (fun i => (a i : ℂ)) (freqPhase (2*j.val+1))‖ ≤ radius 17 := by
  obtain ⟨b, hb, he, _⟩ := reindex_signedSum j a
  rw [he]; exact sharp_norm_le (by norm_num) b (hb ha)
private lemma odd_frequency_norm_eq_iff (j : Fin 8) (a : Fin 17 → ℝ) (ha : IsSign a) : ‖dotProduct (fun i => (a i : ℂ)) (freqPhase (2*j.val+1))‖ = radius 17 ↔ ∃ k : ℕ, k ≤ 17 ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ x, a x = freqSign (2*j.val+1) x * threshold 17 k s (freqIndex (2*j.val+1) x) := by
  obtain ⟨b,hb,he,hpoint⟩ := reindex_signedSum j a
  rw [he]; constructor
  · intro h
    obtain ⟨k,hk,s,hs,hform⟩ := (sharp_norm_eq_iff (by norm_num) b (hb ha)).mp h
    refine ⟨k,hk,s,hs,?_⟩
    intro x; have hx := hpoint x; rw [hform (freqIndex (2*j.val+1) x)] at hx
    rcases freqSign_sign (2*j.val+1) x with hp | hp <;>
      rw [hp] at hx ⊢ <;> dsimp [threshold] at * <;> linarith
  · rintro ⟨k,hk,s,hs,hform⟩
    have hbform : b = threshold 17 k s := by
      funext y
      obtain ⟨x,rfl⟩ := Finite.surjective_of_injective (freqIndex_injective j) y
      rw [hpoint, hform x]
      rcases freqSign_sign (2*j.val+1) x with hp | hp <;> rw [hp] <;> ring
    rw [hbform]; exact threshold_norm (by norm_num) k hk s hs
def baseSigns (j : Fin 8) (x : Fin 17) : ℝ :=
  Real.sign (Real.cos (Real.pi * (2*j.val+1) * x.val / 17))
private def integerBaseSigns (j : Fin 8) (x : Fin 17) : ℤ :=
  (-1) ^ ((2*j.val+1)*x.val/17) *
    (if ((2*j.val+1)*x.val)%17 < 9 then 1 else -1)
private lemma baseSigns_eq_integerBaseSigns (j : Fin 8) (x : Fin 17) :
    baseSigns j x = (integerBaseSigns j x : ℝ) := by
  have hc : Real.cos (Real.pi*(2*j.val+1)*x.val/17)=
      freqSign (2*j.val+1) x*Real.cos (Real.pi/17*(freqIndex (2*j.val+1) x).val) := by
    have hh : (freqPhase (2*j.val+1) x).re =
        Real.cos (Real.pi*(2*j.val+1)*x.val/17) := by
      have he : freqPhase (2*j.val+1) x =
          Complex.exp (Complex.ofReal (Real.pi*(2*j.val+1)*x.val/17)*Complex.I) := by
        dsimp [freqPhase,zeta]
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [he,Complex.exp_ofReal_mul_I_re]
    push_cast at hh
    rw [← hh,freqPhase_decomposition,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,phase,
      Complex.exp_ofReal_mul_I_re]
    norm_num only [Nat.cast_ofNat]
  have he : (integerBaseSigns j x : ℝ)=freqSign (2*j.val+1) x*
      (if (freqIndex (2*j.val+1) x).val<9 then (1:ℝ) else -1) := by
    by_cases hlt : ((2*j.val+1)*x.val)%17<9
    · simp [integerBaseSigns,freqSign,freqIndex,hlt]
    · simp [integerBaseSigns,freqSign,freqIndex,hlt]
  rw [baseSigns, hc, he]
  have hs : ((freqIndex (2*j.val+1) x).val<9 →
      0<Real.cos (Real.pi/17*(freqIndex (2*j.val+1) x).val)) ∧
      (¬(freqIndex (2*j.val+1) x).val<9 →
      Real.cos (Real.pi/17*(freqIndex (2*j.val+1) x).val)<0) := by
    constructor
    · intro hlt
      have hxr : ((freqIndex (2*j.val+1) x).val : ℝ)≤8 := by
        exact_mod_cast (show (freqIndex (2*j.val+1) x).val≤8 by omega)
      have hx0 : (0 : ℝ)≤(freqIndex (2*j.val+1) x).val := Nat.cast_nonneg _
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos,
        mul_nonneg hx0 Real.pi_pos.le,
        mul_le_mul_of_nonneg_right hxr Real.pi_pos.le]
    · intro hlt
      have hxr : (9 : ℝ)≤(freqIndex (2*j.val+1) x).val := by
        exact_mod_cast (show 9≤(freqIndex (2*j.val+1) x).val by omega)
      have hxhi : ((freqIndex (2*j.val+1) x).val : ℝ)≤16 := by
        exact_mod_cast (show (freqIndex (2*j.val+1) x).val≤16 by omega)
      apply Real.cos_neg_of_pi_div_two_lt_of_lt <;>
        nlinarith [Real.pi_pos,
          mul_le_mul_of_nonneg_right hxr Real.pi_pos.le,
          mul_le_mul_of_nonneg_right hxhi Real.pi_pos.le]
  rcases freqSign_sign (2*j.val+1) x with hsign | hsign <;>
    rw [hsign] <;> by_cases hlt : (freqIndex (2*j.val+1) x).val<9
  · have hp := hs.1 hlt
    simp only [one_mul]
    rw [Real.sign_of_pos hp]
    simp [hlt]
  · have hn := hs.2 hlt
    simp only [one_mul]
    rw [Real.sign_of_neg hn]
    simp [hlt]
  · have hp := hs.1 hlt
    simp only [neg_one_mul]
    rw [Real.sign_of_neg (neg_lt_zero.mpr hp)]
    simp [hlt]
  · have hn := hs.2 hlt
    simp only [neg_one_mul]
    rw [Real.sign_of_pos (neg_pos.mpr hn)]
    simp [hlt]
def rotatedSigns (j : Fin 8) (t : Fin 34) (x : Fin 17) : ℝ :=
  (-1 : ℝ) ^ ((x.val+t.val)/17) * baseSigns j ⟨(x.val+t.val)%17,by omega⟩
private def integerRotatedSigns (j : Fin 8) (t : Fin 34) (x : Fin 17) : ℤ :=
  (-1) ^ ((x.val+t.val)/17) * integerBaseSigns j ⟨(x.val+t.val)%17,by omega⟩
private lemma threshold_rotation (j : Fin 8) (k : Fin 18) : ∃ t : Fin 34, ∀ x : Fin 17, (-1 : ℤ) ^ ((2*j.val+1)*x.val/17) * (if ((2*j.val+1)*x.val)%17 < k.val then 1 else -1) = integerRotatedSigns j t x := by
  let witness : Fin 8 → Fin 18 → Fin 34 := ![
    ![9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 33, 32, 31, 30, 29, 28, 27, 26],
    ![3, 14, 25, 2, 13, 24, 1, 12, 23, 0, 11, 22, 33, 10, 21, 32, 9, 20],
    ![29, 22, 15, 8, 1, 28, 21, 14, 7, 0, 27, 20, 13, 6, 33, 26, 19, 12],
    ![11, 6, 1, 30, 25, 20, 15, 10, 5, 0, 29, 24, 19, 14, 9, 4, 33, 28],
    ![1, 16, 31, 12, 27, 8, 23, 4, 19, 0, 15, 30, 11, 26, 7, 22, 3, 18],
    ![7, 10, 13, 16, 19, 22, 25, 28, 31, 0, 3, 6, 9, 12, 15, 18, 21, 24],
    ![19, 32, 11, 24, 3, 16, 29, 8, 21, 0, 13, 26, 5, 18, 31, 10, 23, 2],
    ![21, 30, 5, 14, 23, 32, 7, 16, 25, 0, 9, 18, 27, 2, 11, 20, 29, 4]]
  refine ⟨witness j k, ?_⟩
  revert j k
  decide
private lemma rotatedSigns_eq_integerRotatedSigns (j : Fin 8) (t : Fin 34) (x : Fin 17) :
    rotatedSigns j t x = (integerRotatedSigns j t x : ℝ) := by
  simp only [rotatedSigns, integerRotatedSigns, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one]
  rw [baseSigns_eq_integerBaseSigns]
private lemma zeta_primitive : IsPrimitiveRoot (zeta 17) 34 := by
  have he : zeta 17 = Complex.exp (2 * Real.pi * Complex.I / 34) := by
    congr 1; dsimp [zeta]; push_cast; ring
  rw [he]; exact Complex.isPrimitiveRoot_exp 34 (by decide)
private lemma frequency_coprime (j : Fin 8) : (2*j.val+1).Coprime 34 := by fin_cases j <;> decide
lemma frequency_order (j : Fin 8) (t : ℕ) : zeta 17 ^ ((2*j.val+1)*t) = 1 → 34 ∣ t := by intro ht; have hd := zeta_primitive.dvd_of_pow_eq_one _ ht; exact (frequency_coprime j).symm.dvd_of_dvd_mul_left hd
private lemma zeta17_denom : zeta 17 - 1 = (2 * Real.sin (Real.pi/34) : ℝ) * zeta 17 ^ 9 := by
  have hz9 : zeta 17 ^ 9 = Complex.exp (((Real.pi/2+Real.pi/34 : ℝ) : ℂ)*Complex.I) := by
    dsimp [zeta]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have ha : Real.pi/17 = 2*(Real.pi/34) := by ring
  rw [hz9]; apply Complex.ext
  · simp only [zeta,Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re]
    norm_num only [Nat.cast_ofNat]; rw [ha,Real.cos_two_mul,Real.cos_add,Real.cos_pi_div_two,Real.sin_pi_div_two]; nlinarith [Real.sin_sq_add_cos_sq (Real.pi/34)]
  · simp only [zeta,Complex.sub_im,Complex.one_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero,sub_zero,Complex.exp_ofReal_mul_I_im]
    norm_num only [Nat.cast_ofNat]; rw [ha,Real.sin_two_mul,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two]; ring
private lemma threshold9_sum : dotProduct (fun i => ((threshold 17 9 1) i : ℂ)) (phase 17) = (radius 17 : ℂ) := by
  rw [threshold_sum (by norm_num) 9 (by norm_num),zeta17_denom]; have hs : Real.sin (Real.pi/34) ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hz : zeta 17 ≠ 0 := Complex.exp_ne_zero _; dsimp [radius]; norm_num; push_cast
  field_simp
lemma baseSigns_sum (j : Fin 8) : dotProduct (fun i => ((fun x => baseSigns j x) i : ℂ)) (freqPhase (2*j.val+1)) = (radius 17 : ℂ) := by
  obtain ⟨b,_,he,hb⟩ := reindex_signedSum j (fun x => baseSigns j x)
  have hform : b = threshold 17 9 1 := by
    funext y
    obtain ⟨x,rfl⟩ := Finite.surjective_of_injective (freqIndex_injective j) y
    rw [hb, baseSigns_eq_integerBaseSigns]
    simp only [integerBaseSigns,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,
      Int.cast_ite,freqSign,threshold,freqIndex]
    by_cases hlt : ((2*j.val+1)*x.val)%17<9
    · rcases neg_one_pow_eq_or ℝ ((2*j.val+1)*x.val/17) with h | h <;> simp [hlt,h]
    · rcases neg_one_pow_eq_or ℝ ((2*j.val+1)*x.val/17) with h | h <;> simp [hlt,h]
  rw [he,hform,threshold9_sum]
private lemma halfperiod_phase (j : Fin 8) (t : ℕ) : zeta 17 ^ ((2*j.val+1)*(17*t)) = (-1 : ℂ) ^ t := by
  have hj : Odd (2*j.val+1) := ⟨j.val,by omega⟩; rw [show (2*j.val+1)*(17*t)=17*((2*j.val+1)*t) by ring,pow_mul,zeta_pow_card (by norm_num),
    pow_mul,hj.neg_one_pow]
lemma rotation_eval (j : Fin 8) (t : Fin 34) : dotProduct (fun i => ((fun x => (rotatedSigns j t x : ℝ)) i : ℂ)) (freqPhase (2*j.val+1)) * zeta 17 ^ ((2*j.val+1)*t.val) = (radius 17 : ℂ) := by
  classical
  let e : Fin 17 ≃ Fin 17 := Equiv.ofBijective
    (fun x => ⟨(x.val+t.val)%17,by omega⟩)
    ⟨by intro x y h; apply Fin.ext; have hh := congrArg Fin.val h; dsimp at hh; omega,
     by apply Finite.surjective_of_injective; intro x y h; apply Fin.ext
        have hh := congrArg Fin.val h; dsimp at hh; omega⟩
  have ht (x : Fin 17) :
      (rotatedSigns j t x : ℂ) * freqPhase (2*j.val+1) x * zeta 17 ^ ((2*j.val+1)*t.val) =
        (baseSigns j (e x) : ℂ) * freqPhase (2*j.val+1) (e x) := by
    rw [rotatedSigns_eq_integerRotatedSigns, baseSigns_eq_integerBaseSigns]
    simp only [integerRotatedSigns, Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,freqPhase]; have he : x.val+t.val = (x.val+t.val)%17 + 17*((x.val+t.val)/17) :=
      (Nat.mod_add_div _ _).symm
    have heq : e x = (⟨(x.val+t.val)%17,by omega⟩ : Fin 17) := rfl
    rw [← heq]
    have hval : (e x).val = (x.val+t.val)%17 := rfl
    simp only [hval]
    push_cast
    have hz : zeta 17 ^ ((2*j.val+1)*x.val) * zeta 17 ^ ((2*j.val+1)*t.val) =
        zeta 17 ^ ((2*j.val+1)*((x.val+t.val)%17)) * (-1 : ℂ)^((x.val+t.val)/17) := by
      rw [← pow_add,← Nat.mul_add]
      nth_rw 1 [he]
      rw [Nat.mul_add,pow_add,halfperiod_phase]
    have hs : ((-1 : ℂ)^((x.val+t.val)/17))^2=1 := by
      rcases neg_one_pow_eq_or ℂ ((x.val+t.val)/17) with h | h <;> norm_num [h]
    change ((-1 : ℂ)^((x.val+t.val)/17) * (integerBaseSigns j (e x) : ℂ)) *
      zeta 17 ^ ((2*j.val+1)*x.val) * zeta 17 ^ ((2*j.val+1)*t.val) = _
    rw [mul_assoc,mul_assoc,hz]
    calc
      _ = (integerBaseSigns j (e x) : ℂ)*zeta 17 ^ ((2*j.val+1)*((x.val+t.val)%17))*
          ((-1 : ℂ)^((x.val+t.val)/17))^2 := by ring
      _ = _ := by rw [hs,mul_one]
  simp only [dotProduct]; rw [Finset.sum_mul]; push_cast; simp_rw [ht]
  calc
    _ = ∑ x : Fin 17,(baseSigns j x : ℂ)*freqPhase (2*j.val+1) x :=
      Equiv.sum_comp e (fun x => (baseSigns j x : ℂ)*freqPhase (2*j.val+1) x)
    _ = _ := by simpa [dotProduct] using baseSigns_sum j
private lemma rotatedSigns_neg (j : Fin 8) (t : Fin 34) (x : Fin 17) : rotatedSigns j ⟨(t.val+17)%34,by omega⟩ x = -rotatedSigns j t x := by
  have hres : (x.val+(t.val+17)%34)%17=(x.val+t.val)%17 := by omega
  dsimp [rotatedSigns]; have hi : (⟨(x.val+(t.val+17)%34)%17,by omega⟩ : Fin 17)=⟨(x.val+t.val)%17,by omega⟩ := Fin.ext hres; rw [hi]
  by_cases ht : t.val<17
  · have hq : (x.val+(t.val+17)%34)/17=(x.val+t.val)/17+1 := by omega
    rw [hq,pow_succ]; ring
  · have hq : (x.val+t.val)/17=(x.val+(t.val+17)%34)/17+1 := by omega
    rw [hq,pow_succ]; ring
lemma norm_maximizers_are_rotations (j : Fin 8) (a : Fin 17 → ℝ) (ha : IsSign a) (he : ‖dotProduct (fun i => (a i : ℂ)) (freqPhase (2*j.val+1))‖=radius 17) : ∃ t : Fin 34, a=fun x => rotatedSigns j t x := by
  obtain ⟨k,hk,s,hs,hform⟩ := (odd_frequency_norm_eq_iff j a ha).mp he
  let k' : Fin 18 := ⟨k,by omega⟩
  obtain ⟨t,ht⟩ := threshold_rotation j k'
  rcases hs with rfl | rfl
  · refine ⟨t,?_⟩
    funext x
    rw [hform x]
    change (-1 : ℝ)^((2*j.val+1)*x.val/17)*(if ((2*j.val+1)*x.val)%17<k then (1:ℝ) else -1)=rotatedSigns j t x
    rw [rotatedSigns_eq_integerRotatedSigns]
    exact_mod_cast ht x
  · refine ⟨⟨(t.val+17)%34,by omega⟩,?_⟩
    funext x
    rw [hform x, rotatedSigns_neg]
    rw [rotatedSigns_eq_integerRotatedSigns, ← ht x]
    simp only [freqSign,threshold,freqIndex,Int.cast_mul,Int.cast_pow,Int.cast_ite,
      Int.cast_neg,Int.cast_one]
    change (-1 : ℝ)^((2*j.val+1)*x.val/17)*(if _<k then -1 else -(-1)) =
      -((-1 : ℝ)^((2*j.val+1)*x.val/17)*(if _<k then 1 else -1))
    split_ifs <;> ring
lemma radius17_pos : 0<radius 17 := by apply one_div_pos.mpr; apply Real.sin_pos_of_pos_of_lt_pi <;> norm_num <;> linarith [Real.pi_pos]
private lemma affine_extreme_image {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] (S : Set E) (hS : Convex ℝ S) (f : E →ᵃ[ℝ] F) (hf : Set.InjOn f S) {x : E} (hx : x ∈ S.extremePoints ℝ) : f x ∈ (f '' S).extremePoints ℝ := by
  refine ⟨Set.mem_image_of_mem f hx.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
  rw [← image_openSegment ℝ f y z] at hseg
  obtain ⟨q, hq, heq⟩ := hseg
  have hqS : q ∈ S := hS.segment_subset hy hz (openSegment_subset_segment _ _ _ hq); have hqx : q = x := hf hqS hx.1 heq; subst q; exact congrArg f (hx.2 hy hz hq)
private lemma finite_hull_extremes {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E] (T : Set E) (hT : T.Finite) : convexHull ℝ ((convexHull ℝ T).extremePoints ℝ) = convexHull ℝ T := by
  have hf : ((convexHull ℝ T).extremePoints ℝ).Finite :=
    hT.subset extremePoints_convexHull_subset
  have hc : IsCompact (convexHull ℝ T) := hT.isCompact_convexHull ℝ; have hs : IsClosed (convexHull ℝ ((convexHull ℝ T).extremePoints ℝ)) :=
    (hf.isCompact_convexHull ℝ).isClosed
  simpa [hs.closure_eq] using closure_convexHull_extremePoints hc (convex_convexHull ℝ T)
lemma extra_extreme_of_separation {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E] (T V : Set E) (hT : T.Finite) {p : E} (hp : p ∈ convexHull ℝ T) (hout : p ∉ convexHull ℝ V) : ∃ q ∈ (convexHull ℝ T).extremePoints ℝ, q ∉ V := by
  by_contra! h
  have hsub : (convexHull ℝ T).extremePoints ℝ ⊆ V := h; have hh := convexHull_mono (𝕜 := ℝ) hsub; rw [finite_hull_extremes T hT] at hh; exact hout (hh hp)
lemma not_affine_cross_of_many_extreme {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) (hS : Convex ℝ S) (g : Fin 19 → E) (hg : Function.Injective g) (hext : ∀ i, g i ∈ S.extremePoints ℝ) : ¬ ∃ f : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin 9), Set.InjOn f S ∧ f '' S = convexHull ℝ (Set.range (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ)) ∪ Set.range (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ))) := by
  rintro ⟨f, hf, him⟩
  let h : Fin 19 → EuclideanSpace ℝ (Fin 9) := fun i => f (g i)
  have hinj : Function.Injective h := by
    intro i j hij; exact hg (hf (hext i).1 (hext j).1 hij)
  let U : Set (EuclideanSpace ℝ (Fin 9)) :=
    Set.range (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ)) ∪
    Set.range (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ))
  have hU : U.Finite := (Set.finite_range _).union (Set.finite_range _); have hsub : Set.range h ⊆ U := by
    rintro _ ⟨i,rfl⟩
    have he := affine_extreme_image S hS f hf (hext i); rw [him] at he; exact extremePoints_convexHull_subset he
  have hcard : (Set.range h).ncard = 19 := by
    rw [Set.ncard_range_of_injective hinj]
    simp
  have hle := Set.ncard_le_ncard hsub hU; have hbound : U.ncard ≤ 18 := by
    calc
      U.ncard ≤ (Set.range (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ))).ncard +
        (Set.range (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ))).ncard :=
          Set.ncard_union_le _ _
      _ ≤ 9 + 9 := by
        have hinjplus : Function.Injective (fun i : Fin 9 => EuclideanSpace.single i (1 : ℝ)) := by
          intro i j hij
          by_contra hne
          have hh := congrArg (fun q : EuclideanSpace ℝ (Fin 9) => q i) hij
          simpa [PiLp.single_apply, hne] using hh
        have hinjminus : Function.Injective (fun i : Fin 9 => -EuclideanSpace.single i (1 : ℝ)) :=
          neg_injective.comp hinjplus
        rw [Set.ncard_range_of_injective hinjplus, Set.ncard_range_of_injective hinjminus]
        simp
      _ = 18 := rfl
  omega
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
lemma root_reduce (z : ℂ) (hz : z^17= -1) (t : ℕ) : z^t=(-1 : ℂ)^(t/17)*z^(t%17) := by
  nth_rw 1 [← Nat.mod_add_div t 17]
  rw [pow_add,pow_mul,hz]; ring
lemma root_reflect (z : ℂ) (hz : z^17= -1) (hn : ‖z‖=1) (r : ℕ) (hr : r≤17) : (z^(17-r)).re= -(z^r).re := by
  have hnorm : Complex.normSq (z^r)=1 := by
    rw [Complex.normSq_eq_norm_sq,norm_pow,hn]; norm_num
  have hnon : z^r≠0 := by
    intro h; rw [h,Complex.normSq_zero] at hnorm; norm_num at hnorm
  have he : z^(17-r)= -conj (z^r) := by
    apply mul_left_cancel₀ hnon; rw [← pow_add,Nat.add_sub_of_le hr,hz,mul_neg,Complex.mul_conj,hnorm]; norm_num
  rw [he,Complex.neg_re,Complex.conj_re]
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
lemma halfcircle_cos_sign (x : Fin 17) : (x.val<9 → 0<Real.cos (Real.pi/17*x.val)) ∧ (¬x.val<9 → Real.cos (Real.pi/17*x.val)<0) := by
  constructor
  · intro hx
    have hxr : (x.val : ℝ)≤8 := by exact_mod_cast (show x.val≤8 by omega)
    have hx0 : (0 : ℝ)≤x.val := Nat.cast_nonneg _; apply Real.cos_pos_of_mem_Ioo; constructor <;> nlinarith [Real.pi_pos,mul_nonneg hx0 Real.pi_pos.le,
      mul_le_mul_of_nonneg_right hxr Real.pi_pos.le]
  · intro hx
    have hxr : (9 : ℝ)≤x.val := by exact_mod_cast (show 9≤x.val by omega)
    have hxhi : (x.val : ℝ)≤16 := by exact_mod_cast (show x.val≤16 by omega)
    apply Real.cos_neg_of_pi_div_two_lt_of_lt <;>
      nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_right hxr Real.pi_pos.le,
        mul_le_mul_of_nonneg_right hxhi Real.pi_pos.le]
end D5.S3.Quantum.Entanglement.SymmetricBellPolytopeSupport
