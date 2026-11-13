/- GID: D5/S3/Quantum/Completion/InsertionMeanRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/InsertionMeanRigidity
   mirror-E: none(waiver:raw-unital-magma)
   anchors: []
   utility: none
   digest: Positive recurrent grids control all insertion means of the original arbitrary-marker raw cost. -/

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic
import D5.S3.Quantum.Completion.RawUnanchoredReplication
import D5.S3.Analytic.KarpZhangCatalanPower.Result

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
open Set

namespace D5.S3.Quantum.Completion.InsertionMeanRigidity

abbrev Grid := (ℕ × ℕ) → ℝ

def Recurrent (g : Grid) : Prop :=
  ∀ m n, 2 * g (m + 1, n + 1) + g (m + 1, n) + g (m, n + 1) = 4 * g (m, n)

private def Normalized : Set Grid :=
  {g | (∀ q, 0 ≤ g q) ∧ Recurrent g ∧ g (0, 0) = 1}

private theorem step_bounds (g : Grid) (hn : ∀ q, 0 ≤ g q) (hr : Recurrent g) (m n : ℕ) :
    g (m + 1, n) ≤ 4 * g (m, n) ∧ g (m, n + 1) ≤ 4 * g (m, n) := by
  have h := hr m n
  constructor <;> linarith [hn (m + 1, n + 1), hn (m + 1, n), hn (m, n + 1)]

private theorem grid_bound (g : Grid) (hn : ∀ q, 0 ≤ g q) (hr : Recurrent g) :
    ∀ m n, g (m, n) ≤ (4 : ℝ) ^ (m + n) * g (0, 0) := by
  intro m n
  calc
    g (m, n) ≤ (4 : ℝ) ^ m * g (0, n) :=
      le_geom (u := fun k => g (k, n)) (by norm_num) m
        (fun k _ => (step_bounds g hn hr k n).1)
    _ ≤ (4 : ℝ) ^ m * ((4 : ℝ) ^ n * g (0, 0)) :=
      mul_le_mul_of_nonneg_left
        (le_geom (u := fun k => g (0, k)) (by norm_num) n
          (fun k _ => (step_bounds g hn hr 0 k).2))
        (pow_nonneg (by norm_num) m)
    _ = (4 : ℝ) ^ (m + n) * g (0, 0) := by rw [pow_add, mul_assoc]

private theorem zero_grid (g : Grid) (hn : ∀ q, 0 ≤ g q) (hr : Recurrent g)
    (hz : g (0, 0) = 0) : g = 0 := by
  funext q
  rcases q with ⟨m, n⟩
  apply le_antisymm
  · simpa only [hz, mul_zero, Pi.zero_apply] using grid_bound g hn hr m n
  · exact hn (m, n)

private theorem normalize_mem (g : Grid) (hn : ∀ q, 0 ≤ g q) (hr : Recurrent g)
    (t : ℝ) (ht : 0 < t) (hz : g (0, 0) = t) :
    (fun q => g q / t) ∈ Normalized := by
  refine ⟨fun q => div_nonneg (hn q) (le_of_lt ht), ?_, ?_⟩
  · intro m n
    dsimp
    linear_combination (1 / t) * hr m n
  · change g (0, 0) / t = 1
    rw [hz, div_self (ne_of_gt ht)]

private theorem normalized_nonempty : Normalized.Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  refine ⟨fun _ => by norm_num, ?_, rfl⟩
  intro m n
  norm_num

private theorem normalized_closed : IsClosed Normalized := by
  have hn : IsClosed {g : Grid | ∀ q, 0 ≤ g q} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun q => isClosed_le continuous_const (continuous_apply q)
  have hr : IsClosed {g : Grid | Recurrent g} := by
    simp only [Recurrent, Set.ofPred_forall]
    exact isClosed_iInter fun m => isClosed_iInter fun n =>
      isClosed_eq (by fun_prop) (by fun_prop)
  have hz : IsClosed {g : Grid | g (0, 0) = 1} :=
    isClosed_eq (continuous_apply (0, 0)) continuous_const
  exact hn.inter (hr.inter hz)

private theorem normalized_compact : IsCompact Normalized := by
  have hb : IsCompact {g : Grid | ∀ q, g q ∈ Icc 0 ((4 : ℝ) ^ (q.1 + q.2))} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  refine hb.of_isClosed_subset normalized_closed ?_
  intro g hg q
  refine ⟨hg.1 q, ?_⟩
  simpa only [hg.2.2, mul_one] using grid_bound g hg.1 hg.2.1 q.1 q.2

private theorem extreme_minimum (l : Grid →L[ℝ] ℝ) :
    ∃ g ∈ Normalized.extremePoints ℝ, ∀ h ∈ Normalized, l g ≤ l h := by
  obtain ⟨g, hg, hmin⟩ := normalized_compact.exists_isMinOn normalized_nonempty
    l.continuous.continuousOn
  let F := (-l).toExposed Normalized
  have he : IsExposed ℝ Normalized F := ContinuousLinearMap.toExposed.isExposed
  have hf : F.Nonempty := by
    refine ⟨g, hg, ?_⟩
    intro h hh
    change -l h ≤ -l g
    exact neg_le_neg (hmin hh)
  obtain ⟨k, hk⟩ := (he.isCompact normalized_compact).extremePoints_nonempty hf
  refine ⟨k, he.isExtreme.extremePoints_subset_extremePoints hk, ?_⟩
  intro h hh
  have hm := hk.1.2 h hh
  change -l h ≤ -l k at hm
  linarith

private theorem dominated_extreme (g : Grid) (hg : g ∈ Normalized.extremePoints ℝ)
    (h : Grid) (hn : ∀ q, 0 ≤ h q) (hr : Recurrent h)
    (hd : ∀ q, h q ≤ 4 * g q) : ∀ q, h q = h (0, 0) * g q := by
  have hgn := hg.1.1
  have hgr := hg.1.2.1
  have hg0 := hg.1.2.2
  have hkn : ∀ q, 0 ≤ 4 * g q - h q := fun q => sub_nonneg.mpr (hd q)
  have hkr : Recurrent (fun q => 4 * g q - h q) := by
    intro m n
    dsimp
    linear_combination 4 * hgr m n - hr m n
  by_cases hz : h (0, 0) = 0
  · have hh := zero_grid h hn hr hz
    intro q
    rw [hh]
    simp
  by_cases hf : h (0, 0) = 4
  · have hk0 : (4 * g (0, 0) - h (0, 0)) = 0 := by rw [hg0, hf]; norm_num
    have hk := zero_grid (fun q => 4 * g q - h q) hkn hkr hk0
    intro q
    have hh := congrFun hk q
    change 4 * g q - h q = 0 at hh
    rw [hf]
    linarith
  have ht : 0 < h (0, 0) := by have := hn (0, 0); exact lt_of_le_of_ne this (Ne.symm hz)
  have hu : 0 < 4 - h (0, 0) := by
    have hb : h (0, 0) ≤ 4 := by simpa only [hg0, mul_one] using hd (0, 0)
    have hlt : h (0, 0) < 4 := lt_of_le_of_ne hb hf
    linarith
  let x : Grid := fun q => h q / h (0, 0)
  let y : Grid := fun q => (4 * g q - h q) / (4 - h (0, 0))
  have hx : x ∈ Normalized := normalize_mem h hn hr _ ht rfl
  have hy : y ∈ Normalized := normalize_mem _ hkn hkr _ hu (by rw [hg0]; ring)
  have hs : g ∈ openSegment ℝ x y := by
    refine ⟨h (0, 0) / 4, (4 - h (0, 0)) / 4, by positivity, by positivity, by ring, ?_⟩
    funext q
    change (h (0, 0) / 4) * (h q / h (0, 0)) +
      ((4 - h (0, 0)) / 4) * ((4 * g q - h q) / (4 - h (0, 0))) = g q
    field_simp [ne_of_gt ht, ne_of_gt hu]
    <;> ring
  have heq : x = g := hg.2 hx hy hs
  intro q
  have he := congrFun heq q
  change h q / h (0, 0) = g q at he
  simpa only [mul_comm] using (div_eq_iff (ne_of_gt ht)).mp he

private theorem extreme_monomial (g : Grid) (hg : g ∈ Normalized.extremePoints ℝ) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r + s + 2 * r * s = 4 ∧
      ∀ m n, g (m, n) = r ^ m * s ^ n := by
  have hn := hg.1.1
  have hr := hg.1.2.1
  have h0 := hg.1.2.2
  have hl := dominated_extreme g hg (fun q => g (q.1 + 1, q.2))
    (fun q => hn _) (fun m n => hr (m + 1) n)
    (fun q => (step_bounds g hn hr q.1 q.2).1)
  have ht := dominated_extreme g hg (fun q => g (q.1, q.2 + 1))
    (fun q => hn _) (fun m n => hr m (n + 1))
    (fun q => (step_bounds g hn hr q.1 q.2).2)
  have hL (m n : ℕ) : g (m + 1, n) = g (1, 0) * g (m, n) := hl (m, n)
  have hR (m n : ℕ) : g (m, n + 1) = g (0, 1) * g (m, n) := ht (m, n)
  have hm : ∀ m n, g (m, n) = g (1, 0) ^ m * g (0, 1) ^ n := by
    intro m
    induction m with
    | zero =>
      intro n
      induction n with
      | zero => simpa only [pow_zero, one_mul] using h0
      | succ n ih => rw [hR, ih, pow_succ]; ring
    | succ m ih =>
      intro n
      rw [hL, ih n, pow_succ]
      ring
  refine ⟨g (1, 0), g (0, 1), hn _, hn _, ?_, hm⟩
  have he := hr 0 0
  rw [hm 1 1, hm 1 0, hm 0 1, hm 0 0] at he
  norm_num at he
  nlinarith

private noncomputable def polynomialFunctional {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (v : ι → ℕ × ℕ) : Grid →L[ℝ] ℝ :=
  ∑ k ∈ t, a k • (ContinuousLinearMap.proj (v k) : Grid →L[ℝ] ℝ)

private theorem polynomialFunctional_apply {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (v : ι → ℕ × ℕ) (g : Grid) :
    polynomialFunctional t a v g = ∑ k ∈ t, a k * g (v k) := by
  simp [polynomialFunctional]

theorem finite_polynomial_positive {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (v : ι → ℕ × ℕ) (g : Grid) (hn : ∀ q, 0 ≤ g q)
    (hr : ∀ m n, 2 * g (m + 1, n + 1) + g (m + 1, n) + g (m, n + 1) = 4 * g (m, n))
    (hp : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → r + s + 2 * r * s = 4 →
      0 ≤ ∑ k ∈ t, a k * r ^ (v k).1 * s ^ (v k).2) :
    0 ≤ ∑ k ∈ t, a k * g (v k) := by
  by_cases hz : g (0, 0) = 0
  · have he := zero_grid g hn hr hz
    simp [he]
  have ht : 0 < g (0, 0) := lt_of_le_of_ne (hn _) (Ne.symm hz)
  let k : Grid := fun q => g q / g (0, 0)
  have hk : k ∈ Normalized := normalize_mem g hn hr _ ht rfl
  obtain ⟨e, he, hmin⟩ := extreme_minimum (polynomialFunctional t a v)
  obtain ⟨r, s, hr0, hs0, hc, hm⟩ := extreme_monomial e he
  have hp0 : 0 ≤ polynomialFunctional t a v e := by
    rw [polynomialFunctional_apply]
    have hm' (q : ℕ × ℕ) : e q = r ^ q.1 * s ^ q.2 := hm q.1 q.2
    simp_rw [hm']
    simpa only [mul_assoc] using hp r s hr0 hs0 hc
  have hscale : polynomialFunctional t a v k = polynomialFunctional t a v g / g (0, 0) := by
    simp only [polynomialFunctional_apply]
    dsimp [k]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hmul := mul_nonneg (hp0.trans (hmin k hk)) (le_of_lt ht)
  rw [hscale, div_mul_cancel₀ _ (ne_of_gt ht)] at hmul
  simpa only [polynomialFunctional_apply] using hmul

private theorem axis_quadratic_nonnegative (g : Grid) (hn : ∀ q, 0 ≤ g q) (hr : Recurrent g)
    (m n : ℕ) (α β : ℝ) :
    0 ≤ α ^ 2 * g (m, n) + 2 * α * β * g (m, n + 1) + β ^ 2 * g (m, n + 2) := by
  have hp : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → r + s + 2 * r * s = 4 →
      0 ≤ ∑ k : Fin 3, (![α ^ 2, 2 * α * β, β ^ 2] : Fin 3 → ℝ) k *
        r ^ (( ![(m, n), (m, n + 1), (m, n + 2)] : Fin 3 → ℕ × ℕ) k).1 *
        s ^ (( ![(m, n), (m, n + 1), (m, n + 2)] : Fin 3 → ℕ × ℕ) k).2 := by
    intro r s hr0 hs0 _
    convert mul_nonneg (mul_nonneg (pow_nonneg hr0 m) (pow_nonneg hs0 n))
      (sq_nonneg (α + β * s)) using 1 <;>
      simp [Fin.sum_univ_succ, pow_succ, show n + 2 = (n + 1) + 1 by omega] <;> ring
  have hh := finite_polynomial_positive (Finset.univ : Finset (Fin 3))
    (![α ^ 2, 2 * α * β, β ^ 2] : Fin 3 → ℝ)
    (![(m, n), (m, n + 1), (m, n + 2)] : Fin 3 → ℕ × ℕ) g hn hr hp
  simpa [Fin.sum_univ_succ, add_assoc] using hh

private theorem second_axis_logconvex (g : Grid) (hn : ∀ q, 0 ≤ g q) (hr : Recurrent g)
    (m n : ℕ) : g (m, n + 1) ^ 2 ≤ g (m, n) * g (m, n + 2) := by
  have hd := discrim_le_zero (a := g (m, n)) (b := 2 * g (m, n + 1))
    (c := g (m, n + 2)) (fun x => by
      have hh := axis_quadratic_nonnegative g hn hr m n x 1
      nlinarith)
  unfold discrim at hd
  nlinarith

private theorem first_axis_logconvex (g : Grid) (hn : ∀ q, 0 ≤ g q) (hr : Recurrent g)
    (m n : ℕ) : g (m + 1, n) ^ 2 ≤ g (m, n) * g (m + 2, n) := by
  have ht : Recurrent (fun q => g (q.2, q.1)) := by
    intro i j
    have hh := hr j i
    dsimp
    linarith
  exact second_axis_logconvex (fun q => g (q.2, q.1)) (fun q => hn _) ht n m



open D5.S3.Quantum.Completion.RawUnanchoredReplication
open D5.S3.Analytic.KarpZhangCatalanPower.Result

universe u
variable {M : Type u} [MulOneClass M]
abbrev Kernel := M → M → ℝ

def p (U : M → M) (j : ℕ) : M := U^[j] 1
def P (U : M → M) (j : ℕ) (x : M) : M := x * p U j
def S (U : M → M) (g : Kernel (M := M)) : Kernel (M := M) :=
  fun x y => (g (P U 1 x) y + g (P U 2 x) y) / 2
def T (U : M → M) (g : Kernel (M := M)) : Kernel (M := M) :=
  fun x y => (g x (P U 1 y) + g x (P U 2 y)) / 2
def F (U : M → M) (c : Kernel (M := M)) (m n : ℕ) : Kernel (M := M) :=
  (S U)^[m] ((T U)^[n] c)

private theorem commute (U : M → M) : Function.Commute (S U) (T U) := by
  intro g
  funext x y
  dsimp [S, T]
  ring

private theorem F_succ_left (U : M → M) (c : Kernel (M := M)) (m n : ℕ) :
    F U c (m + 1) n = S U (F U c m n) := by
  exact Function.iterate_succ_apply' (S U) m _

private theorem F_succ_right (U : M → M) (c : Kernel (M := M)) (m n : ℕ) :
    F U c m (n + 1) = T U (F U c m n) := by
  unfold F
  rw [Function.iterate_succ_apply']
  exact (commute U).iterate_left m ((T U)^[n] c)

private def KernelRec (U : M → M) (g : Kernel (M := M)) : Prop :=
  ∀ x y, 2 * S U (T U g) x y + S U g x y + T U g x y = 4 * g x y

private theorem rec_S (U : M → M) (g : Kernel (M := M)) (hg : KernelRec U g) :
    KernelRec U (S U g) := by
  intro x y
  have h1 := hg (P U 1 x) y
  have h2 := hg (P U 2 x) y
  dsimp [S, T] at h1 h2 ⊢
  linarith

private theorem rec_T (U : M → M) (g : Kernel (M := M)) (hg : KernelRec U g) :
    KernelRec U (T U g) := by
  intro x y
  have h1 := hg x (P U 1 y)
  have h2 := hg x (P U 2 y)
  dsimp [S, T] at h1 h2 ⊢
  linarith

private theorem F_rec (U : M → M) (c : Kernel (M := M)) (hc : KernelRec U c) :
    ∀ m n, KernelRec U (F U c m n) := by
  intro m
  induction m with
  | zero =>
    intro n
    induction n with
    | zero => exact hc
    | succ n ih =>
      rw [F_succ_right]
      exact rec_T U _ ih
  | succ m ih =>
    intro n
    rw [F_succ_left]
    exact rec_S U _ (ih n)

private theorem F_nonneg (U : M → M) (c : Kernel (M := M)) (hc : ∀ x y, 0 ≤ c x y) :
    ∀ m n x y, 0 ≤ F U c m n x y := by
  intro m
  induction m with
  | zero =>
    intro n
    induction n with
    | zero => exact hc
    | succ n ih =>
      rw [F_succ_right]
      intro x y
      exact div_nonneg (add_nonneg (ih _ _) (ih _ _)) (by norm_num)
  | succ m ih =>
    intro n
    rw [F_succ_left]
    intro x y
    exact div_nonneg (add_nonneg (ih n _ _) (ih n _ _)) (by norm_num)

private theorem raw_rec (U : M → M) (c : Kernel (M := M)) (h : RawCost U c)
    (hSym : ∀ x y, c x y = c y x)
    (hL : ∀ x y, c (P U 3 x) y = c x y)
    (hR : ∀ x y, c x (P U 3 y) = c x y)
    (hz1 : c 1 (p U 1) = 0) : KernelRec U c := by
  intro x y
  have hz1r : c (U 1) 1 = 0 := (hSym _ _).trans hz1
  have h0 := h.balance x y 1 1
  have h1 := h.balance x y (U 1) 1
  have h2 := h.balance x y 1 (U 1)
  change c 1 (U 1) = 0 at hz1
  simp only [one_mul, mul_one, h.diagonal, hz1, hz1r, mul_zero, add_zero] at h0 h1 h2
  have hl := hL x (y * U (U 1))
  have hr := hR (x * U (U 1)) y
  change c (x * U (U (U 1))) (y * U (U 1)) = c x (y * U (U 1)) at hl
  change c (x * U (U 1)) (y * U (U (U 1))) = c (x * U (U 1)) y at hr
  rw [hl] at h1
  rw [hr] at h2
  dsimp [S, T, P, p]
  linarith

private theorem bounded_axis (a : ℕ → ℝ) (hn : ∀ k, 0 ≤ a k)
    (hl : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2))
    (C : ℝ) (hb : ∀ k, a k ≤ C) : a 1 ≤ a 0 := by
  by_cases hz : a 1 = 0
  · rw [hz]
    exact hn 0
  by_contra hnot
  have hlt : a 0 < a 1 := lt_of_not_ge hnot
  have h1 : 0 < a 1 := lt_of_le_of_lt (hn 0) hlt
  have hh : IsLogConvex a := by
    refine ⟨hn, ⟨1, ne_of_gt h1⟩, ?_⟩
    intro k hk
    have he := hl (k - 1)
    rw [show k - 1 + 1 = k by omega, show k - 1 + 2 = k + 1 by omega] at he
    exact he
  have hp := positive_all hh h1
  let r : ℝ := a 1 / a 0
  have hr : 1 < r := by
    apply (lt_div_iff₀ (hp 0)).mpr
    simpa using hlt
  have hs (n : ℕ) : r * a n ≤ a (n + 1) := by
    have hh := convex_ratio hh h1 0 n
    simp only [Nat.zero_add] at hh
    exact (le_div_iff₀ (hp n)).mp hh
  have hg : ∀ n, a 0 * r ^ n ≤ a n := by
    intro n
    simpa only [mul_comm] using
      geom_le (u := a) (c := r) (by linarith) n (fun k _ => hs k)
  obtain ⟨n, _, hn⟩ := Filter.exists_lt_of_tendsto_atTop
    (tendsto_pow_atTop_atTop_of_one_lt hr) 0 (C / a 0)
  have hb' : C < r ^ n * a 0 := (div_lt_iff₀ (hp 0)).mp hn
  nlinarith [hb n, hg n]

/-- Every insertion mean of the original raw kernel is equal to the original cost. -/
theorem full_original_insertion_mean_rigidity (U : M → M) (c : Kernel (M := M))
    (h : RawCost U c) (hSym : ∀ x y, c x y = c y x)
    (hReturnL : ∀ x y, c (P U 3 x) y = c x y)
    (hReturnR : ∀ x y, c x (P U 3 y) = c x y)
    (hCost1 : c 1 (p U 1) = 0) (hCost2 : c 1 (p U 2) = 0) :
    (∀ m n x y, F U c m n x y = c x y) ∧
    S U c = c ∧ T U c = c ∧ S U (T U c) = c ∧ c - S U (T U c) = 0 := by
  have hc : KernelRec U c := raw_rec U c h hSym hReturnL hReturnR hCost1
  have hn := F_nonneg U c h.nonneg
  have hrec (x y : M) : Recurrent (fun ij => F U c ij.1 ij.2 x y) := by
    intro m n
    simp only [F_succ_left, F_succ_right]
    exact F_rec U c hc m n x y
  have hcoord (x y : M) : c x y ≤ 3 * (c x 1 + c y 1) := by
    simpa only [hSym 1 y] using unit_compare h x y
  have hprod (s t : M) : c (s * t) 1 ≤ 3 * (c s 1 + c t 1) := by
    simpa only [one_mul, mul_one] using single h s 1 t 1
  have hp1 : c (p U 1) 1 = 0 := (hSym _ _).trans hCost1
  have hp2 : c (p U 2) 1 = 0 := (hSym _ _).trans hCost2
  have hzero1 (y : M) (hy : c y 1 = 0) : c (P U 1 y) 1 = 0 := by
    apply le_antisymm
    · simpa only [P, hy, hp1, add_zero, mul_zero] using hprod y (p U 1)
    · exact h.nonneg _ _
  have hzero2 (y : M) (hy : c y 1 = 0) : c (P U 2 y) 1 = 0 := by
    apply le_antisymm
    · simpa only [P, hy, hp2, add_zero, mul_zero] using hprod y (p U 2)
    · exact h.nonneg _ _
  have hub : ∀ n x y, c y 1 = 0 → (T U)^[n] c x y ≤ 3 * c x 1 := by
    intro n
    induction n with
    | zero =>
      intro x y hy
      simpa only [Function.iterate_zero_apply, hy, add_zero] using hcoord x y
    | succ n ih =>
      intro x y hy
      rw [Function.iterate_succ_apply']
      change ((T U)^[n] c x (P U 1 y) + (T U)^[n] c x (P U 2 y)) / 2 ≤ _
      linarith [ih x (P U 1 y) (hzero1 y hy), ih x (P U 2 y) (hzero2 y hy)]
  have hunit (x : M) : (c x (p U 1) + c x (p U 2)) / 2 ≤ c x 1 := by
    have hh := bounded_axis (fun k => F U c 0 k x 1)
      (fun k => hn 0 k x 1)
      (fun k => second_axis_logconvex _ (fun ij => hn ij.1 ij.2 x 1) (hrec x 1) 0 k)
      (3 * c x 1) (fun k => hub k x 1 (h.diagonal 1))
    simpa only [F, Function.iterate_zero_apply, Function.iterate_one, T, P, one_mul] using hh
  have hreturn (z : M) : c z (p U 3) = c z 1 := by
    simpa only [P, one_mul] using hReturnR z 1
  have hphase1 (x : M) : c x (p U 1) = c (U (U x)) 1 := by
    have hs := sync_iter h 2 x (U 1)
    have hr := hreturn (U (U x))
    change c (U (U x)) (U (U (U 1))) = c x (U 1) at hs
    change c (U (U x)) (U (U (U 1))) = c (U (U x)) 1 at hr
    exact hs.symm.trans hr
  have hphase2 (x : M) : c x (p U 2) = c (U x) 1 := by
    have hs := sync_iter h 1 x (U (U 1))
    have hr := hreturn (U x)
    change c (U x) (U (U (U 1))) = c x (U (U 1)) at hs
    change c (U x) (U (U (U 1))) = c (U x) 1 at hr
    exact hs.symm.trans hr
  have hcycle (x : M) : c (U (U (U x))) 1 = c x 1 := by
    have hs := sync_iter h 3 x 1
    have hr := hreturn (U (U (U x)))
    change c (U (U (U x))) (U (U (U 1))) = c x 1 at hs
    change c (U (U (U x))) (U (U (U 1))) = c (U (U (U x))) 1 at hr
    exact hr.symm.trans hs
  have hqcycle (x : M) : c (U x) 1 = c x 1 ∧ c (U (U x)) 1 = c x 1 := by
    have h0 := hunit x
    have h1 := hunit (U x)
    have h2 := hunit (U (U x))
    simp only [hphase1, hphase2] at h0 h1 h2
    rw [hcycle x] at h1
    rw [hcycle (U x), hcycle x] at h2
    constructor <;> linarith
  have hTc (x : M) : T U c x 1 = c x 1 := by
    change (c x (1 * p U 1) + c x (1 * p U 2)) / 2 = _
    rw [one_mul, one_mul, hphase1, hphase2, (hqcycle x).1, (hqcycle x).2]
    ring
  have hqmean (x : M) : (c (P U 1 x) 1 + c (P U 2 x) 1) / 2 = c x 1 := by
    have hh := hc x 1
    change 2 * ((T U c (P U 1 x) 1 + T U c (P U 2 x) 1) / 2) +
      (c (P U 1 x) 1 + c (P U 2 x) 1) / 2 + T U c x 1 = 4 * c x 1 at hh
    rw [hTc, hTc, hTc] at hh
    linarith
  have hTb : ∀ n x y, (T U)^[n] c x y ≤ 3 * (c x 1 + c y 1) := by
    intro n
    induction n with
    | zero => exact hcoord
    | succ n ih =>
      intro x y
      rw [Function.iterate_succ_apply']
      change ((T U)^[n] c x (P U 1 y) + (T U)^[n] c x (P U 2 y)) / 2 ≤ _
      linarith [ih x (P U 1 y), ih x (P U 2 y), hqmean y]
  have hb : ∀ m n x y, F U c m n x y ≤ 3 * (c x 1 + c y 1) := by
    intro m
    induction m with
    | zero => exact hTb
    | succ m ih =>
      intro n x y
      rw [F_succ_left]
      change (F U c m n (P U 1 x) y + F U c m n (P U 2 x) y) / 2 ≤ _
      linarith [ih n (P U 1 x) y, ih n (P U 2 x) y, hqmean x]
  have hmonoS (m n : ℕ) (x y : M) : F U c (m + 1) n x y ≤ F U c m n x y := by
    have hh := bounded_axis (fun k => F U c (m + k) n x y)
      (fun k => hn (m + k) n x y)
      (fun k => by simpa only [Nat.add_assoc] using
        first_axis_logconvex _ (fun ij => hn ij.1 ij.2 x y) (hrec x y) (m + k) n)
      (3 * (c x 1 + c y 1)) (fun k => hb (m + k) n x y)
    simpa only [Nat.add_zero] using hh
  have hmonoT (m n : ℕ) (x y : M) : F U c m (n + 1) x y ≤ F U c m n x y := by
    have hh := bounded_axis (fun k => F U c m (n + k) x y)
      (fun k => hn m (n + k) x y)
      (fun k => by simpa only [Nat.add_assoc] using
        second_axis_logconvex _ (fun ij => hn ij.1 ij.2 x y) (hrec x y) m (n + k))
      (3 * (c x 1 + c y 1)) (fun k => hb m (n + k) x y)
    simpa only [Nat.add_zero] using hh
  have hstep (m n : ℕ) (x y : M) :
      F U c (m + 1) n x y = F U c m n x y ∧
      F U c m (n + 1) x y = F U c m n x y := by
    have hr := hrec x y m n
    have hdiag := (hmonoS m (n + 1) x y).trans (hmonoT m n x y)
    constructor <;> linarith [hmonoS m n x y, hmonoT m n x y]
  have hall : ∀ m n x y, F U c m n x y = c x y := by
    intro m
    induction m with
    | zero =>
      intro n
      induction n with
      | zero => intro x y; rfl
      | succ n ih =>
        intro x y
        exact (hstep 0 n x y).2.trans (ih x y)
    | succ m ih =>
      intro n x y
      exact (hstep m n x y).1.trans (ih n x y)
  have hs : S U c = c := by
    funext x y
    exact hall 1 0 x y
  have ht : T U c = c := by
    funext x y
    exact hall 0 1 x y
  have hst : S U (T U c) = c := by rw [ht, hs]
  exact ⟨hall, hs, ht, hst, by rw [hst, sub_self]⟩

end D5.S3.Quantum.Completion.InsertionMeanRigidity
