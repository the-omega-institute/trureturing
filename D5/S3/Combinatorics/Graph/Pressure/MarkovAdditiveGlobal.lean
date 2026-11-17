/- GID: D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/MarkovAdditiveGlobal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global Perron normalization, exact Doob rebasing and pressure curvature. -/
import D5.S3.Combinatorics.Graph.Pressure.MarkovAdditiveCurvature
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Global finite-state pressure and exact Doob rebasing -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix Topology
open Matrix

namespace D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]

private def tiltPerron (P : Matrix V V ℝ) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (t : ℝ) :=
  (supportNetwork P hI).perron (fun i j => -Real.log (P i j) - t * g i j) 1

private theorem tiltPerron_root (P : Matrix V V ℝ) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (t : ℝ) :
    (tiltPerron P hI g t).root = eigenvalue P g t := by
  have hr := (tiltPerron P hI g t).radius
  rw [tilt_eq_weights] at hr
  simp only [eigenvalue, hr, ENNReal.toReal_ofReal (tiltPerron P hI g t).root_pos.le]

theorem eigenvalue_pos (P : Matrix V V ℝ) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (t : ℝ) : 0 < eigenvalue P g t := by
  rw [← tiltPerron_root P hI g t]
  exact (tiltPerron P hI g t).root_pos

namespace Stationary
variable {P : Matrix V V ℝ} (π : Stationary P)

/-- A globally defined positive Perron vector, normalized by the original fixed row. -/
def perronVector (hI : P.IsIrreducible) (g : V → V → ℝ) (t : ℝ) : V → ℝ :=
  fun i => (tiltPerron P hI g t).right i /
    (∑ j, π.prob j * (tiltPerron P hI g t).right j)

theorem perronVector_spec (hI : P.IsIrreducible) (g : V → V → ℝ) (t : ℝ) :
    (∀ i, 0 < π.perronVector hI g t i) ∧
      π.prob ⬝ᵥ π.perronVector hI g t = 1 ∧
      tilt P g t *ᵥ π.perronVector hI g t =
        eigenvalue P g t • π.perronVector hI g t := by
  let R := tiltPerron P hI g t
  have hs : 0 < ∑ j, π.prob j * R.right j :=
    Finset.sum_pos (fun j _ => mul_pos (π.positive j) (R.right_pos j))
      Finset.univ_nonempty
  refine ⟨fun i => div_pos (R.right_pos i) hs, ?_, ?_⟩
  · change (∑ i, π.prob i * (R.right i / (∑ j, π.prob j * R.right j))) = 1
    calc
      _ = (∑ i, π.prob i * R.right i) / (∑ j, π.prob j * R.right j) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        exact (mul_div_assoc _ _ _).symm
      _ = 1 := div_self hs.ne'
  · have he := R.eigen
    rw [tilt_eq_weights, tiltPerron_root] at he
    ext i
    have hi := congrFun he i
    change (∑ j, tilt P g t i j * (R.right j / (∑ k, π.prob k * R.right k))) =
      eigenvalue P g t * (R.right i / (∑ k, π.prob k * R.right k))
    calc
      _ = (∑ j, tilt P g t i j * R.right j) / (∑ k, π.prob k * R.right k) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        exact (mul_div_assoc _ _ _).symm
      _ = _ := by
        rw [← mul_div_assoc]
        exact congrArg (fun a : ℝ => a / ∑ j, π.prob j * R.right j) hi

/-- The actual Doob kernel is defined for every real tilt, including periodic support. -/
def globalDoob (hI : P.IsIrreducible) (g : V → V → ℝ) (t : ℝ) : Matrix V V ℝ :=
  fun i j => tilt P g t i j * π.perronVector hI g t j /
    (eigenvalue P g t * π.perronVector hI g t i)

theorem globalDoob_stochastic (hI : P.IsIrreducible) (g : V → V → ℝ) (t : ℝ) :
    π.globalDoob hI g t ∈ Matrix.rowStochastic ℝ V ∧
      ∀ i j, 0 < π.globalDoob hI g t i j ↔ 0 < P i j := by
  obtain ⟨hr, _, he⟩ := π.perronVector_spec hI g t
  have hl := eigenvalue_pos P hI g t
  refine ⟨Matrix.mem_rowStochastic_iff_sum.mpr ⟨?_, ?_⟩, ?_⟩
  · intro i j
    exact div_nonneg (mul_nonneg
      (mul_nonneg (hI.nonneg i j) (Real.exp_pos _).le) (hr j).le) (mul_pos hl (hr i)).le
  · intro i
    change (∑ j, tilt P g t i j * π.perronVector hI g t j /
      (eigenvalue P g t * π.perronVector hI g t i)) = 1
    rw [← Finset.sum_div]
    have hi := congrFun he i
    change (∑ j, tilt P g t i j * π.perronVector hI g t j) =
      eigenvalue P g t * π.perronVector hI g t i at hi
    rw [hi, div_self (mul_pos hl (hr i)).ne']
  · intro i j
    simp only [globalDoob, tilt, div_pos_iff_of_pos_right (mul_pos hl (hr i)),
      mul_pos_iff_of_pos_right (hr j), mul_pos_iff_of_pos_right (Real.exp_pos _)]

theorem globalDoob_irreducible (hI : P.IsIrreducible) (g : V → V → ℝ) (t : ℝ) :
    (π.globalDoob hI g t).IsIrreducible := by
  have hq := π.globalDoob_stochastic hI g t
  refine ⟨fun i j => Matrix.nonneg_of_mem_rowStochastic hq.1, ?_⟩
  letI : Quiver V := Matrix.toQuiver (π.globalDoob hI g t)
  have hc : Quiver.IsStronglyConnected V := by
    intro i j
    obtain ⟨p⟩ := (@Quiver.IsSStronglyConnected.isStronglyConnected V
      (Matrix.toQuiver P) hI.connected) i j
    induction p with
    | nil => exact ⟨Quiver.Path.nil⟩
    | cons p e ih => exact ⟨ih.some.cons ⟨(hq.2 _ _).2 e.down⟩⟩
  obtain ⟨i, j, hij⟩ := Matrix.Irreducible.exists_pos_entry hI
  exact hc.isSStronglyConnected_of_hom (i₀ := i) (j₀ := j) ⟨(hq.2 i j).2 hij⟩

/-- Entry form of diagonal similarity, with the exact positive Perron scale. -/
private theorem tilt_rebase (hI : P.IsIrreducible) (g : V → V → ℝ)
    (a s : ℝ) (i j : V) :
    tilt P g (a + s) i j * π.perronVector hI g a j =
      (eigenvalue P g a * π.perronVector hI g a i) *
        tilt (π.globalDoob hI g a) g s i j := by
  have hn := (mul_pos (eigenvalue_pos P hI g a)
    ((π.perronVector_spec hI g a).1 i)).ne'
  simp only [tilt, globalDoob, add_mul, Real.exp_add]
  field_simp [(eigenvalue_pos P hI g a).ne', ((π.perronVector_spec hI g a).1 i).ne']
  <;> ring

/-- The spectral radius of each rebased tilt is exactly the quotient of Perron roots. -/
theorem eigenvalue_rebase (hI : P.IsIrreducible) (g : V → V → ℝ) (a s : ℝ) :
    eigenvalue P g (a + s) = eigenvalue P g a *
      eigenvalue (π.globalDoob hI g a) g s := by
  let Q := π.globalDoob hI g a
  let hQ := π.globalDoob_irreducible hI g a
  let R := tiltPerron Q hQ g s
  let r := π.perronVector hI g a
  have he : tilt Q g s *ᵥ R.right = eigenvalue Q g s • R.right := by
    have ht := R.eigen
    rwa [tilt_eq_weights, tiltPerron_root] at ht
  have ht : tilt P g (a + s) *ᵥ (fun i => r i * R.right i) =
      (eigenvalue P g a * eigenvalue Q g s) • (fun i => r i * R.right i) := by
    ext i
    change (∑ j, tilt P g (a + s) i j * (r j * R.right j)) = _
    calc
      _ = ∑ j, (eigenvalue P g a * r i) * (tilt Q g s i j * R.right j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_assoc, π.tilt_rebase hI g a s i j]
        ring
      _ = (eigenvalue P g a * r i) * (eigenvalue Q g s * R.right i) := by
        rw [← Finset.mul_sum]
        exact congrArg (fun x : ℝ => (eigenvalue P g a * r i) * x) (congrFun he i)
      _ = _ := by simp only [Pi.smul_apply, smul_eq_mul]; ring
  exact (positive_eigenpair_identifies_radius P hI g (a+s) _ _
    (mul_pos (eigenvalue_pos P hI g a) (eigenvalue_pos Q hQ g s))
    (fun i => mul_pos ((π.perronVector_spec hI g a).1 i) (R.right_pos i)) ht).2

theorem pressure_rebase (hI : P.IsIrreducible) (g : V → V → ℝ) (a s : ℝ) :
    pressure P g (a + s) = pressure P g a + pressure (π.globalDoob hI g a) g s := by
  unfold pressure
  rw [π.eigenvalue_rebase hI g a s, Real.log_mul
    (eigenvalue_pos P hI g a).ne'
    (eigenvalue_pos _ (π.globalDoob_irreducible hI g a) g s).ne']

include π in
/-- Local implicit branches at the actual Doob kernels give global C2 pressure. -/
theorem pressure_contDiff (hI : P.IsIrreducible) (g : V → V → ℝ) :
    ContDiff ℝ 2 (pressure P g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  let Q := π.globalDoob hI g a
  let hQ := (π.globalDoob_stochastic hI g a).1
  let hJ := π.globalDoob_irreducible hI g a
  let ρ := stationary Q hQ hJ
  have hc := ρ.pressure_contDiffAt_zero hQ hJ g
  have ht : ContDiffAt ℝ 2 (fun t : ℝ => t-a) a := by fun_prop
  have hh : (fun t => pressure P g a + pressure Q g (t-a)) = pressure P g := by
    funext t
    simpa using (π.pressure_rebase hI g a (t-a)).symm
  rw [← hh]
  have hc' : ContDiffAt ℝ 2 (pressure Q g) ((fun t : ℝ => t-a) a) := by
    simpa using hc
  exact contDiffAt_const.add (hc'.comp (f := fun t : ℝ => t-a) a ht)

theorem pressure_second_derivative (hI : P.IsIrreducible) (g : V → V → ℝ) (a : ℝ) :
    deriv (deriv (pressure P g)) a =
      (stationary (π.globalDoob hI g a) (π.globalDoob_stochastic hI g a).1
        (π.globalDoob_irreducible hI g a)).varianceRate
          (π.globalDoob_stochastic hI g a).1 (π.globalDoob_irreducible hI g a) g := by
  let Q := π.globalDoob hI g a
  let hQ := (π.globalDoob_stochastic hI g a).1
  let hJ := π.globalDoob_irreducible hI g a
  let ρ := stationary Q hQ hJ
  have hf : (fun s => pressure P g (a+s)) = (fun s => pressure P g a + pressure Q g s) :=
    funext (π.pressure_rebase hI g a)
  have hd : deriv (fun s => pressure P g (a+s)) = deriv (pressure Q g) := by
    rw [hf]
    ext s
    exact deriv_const_add _
  have ht : (fun s => deriv (pressure P g) (a+s)) = deriv (pressure Q g) := by
    ext s
    exact (deriv_comp_const_add (pressure P g) a s).symm.trans (congrFun hd s)
  have hh := congrArg (fun f : ℝ → ℝ => deriv f 0) ht
  rw [deriv_comp_const_add, add_zero] at hh
  exact hh.trans (ρ.pressure_second_derivative_zero hQ hJ g)

private theorem edgeAverage_congr_supported (hI : P.IsIrreducible)
    (f k : V → V → ℝ) (he : ∀ i j, 0 < P i j → f i j = k i j) :
    π.edgeAverage f = π.edgeAverage k := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : 0 < P i j
  · rw [he i j hij]
  · have hz : P i j = 0 := le_antisymm (le_of_not_gt hij) (hI.nonneg i j)
    simp [hz]

private theorem coboundary_mean (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (c : ℝ) (f : V → ℝ)
    (hg : ∀ i j, 0 < P i j → g i j = c + f i - f j) : π.meanReward g = c := by
  change π.edgeAverage g = c
  rw [π.edgeAverage_congr_supported hI g (fun i j => c + f i - f j) hg]
  change π.edgeAverage ((fun _ _ => c) + (fun i _ => f i) - (fun _ j => f j)) = c
  rw [map_sub, map_add, π.edgeAverage_source hP, π.edgeAverage_source hP,
    π.edgeAverage_target, π.average_const]
  ring

/-- An arbitrary supported coboundary has the canonical centered Poisson potential. -/
private theorem coboundary_corrector (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (c : ℝ) (f : V → ℝ)
    (hg : ∀ i j, 0 < P i j → g i j = c + f i - f j) :
    π.corrector hP hI g = fun i => f i - π.prob ⬝ᵥ f := by
  have hm := π.coboundary_mean hP hI g c f hg
  have hd (i : V) : π.drift g i = f i - (P *ᵥ f) i := by
    change (∑ j, P i j * (g i j - π.meanReward g)) = _
    rw [hm]
    calc
      _ = ∑ j, P i j * (f i - f j) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : 0 < P i j
        · rw [hg i j hij]; ring
        · have hz : P i j = 0 := le_antisymm (le_of_not_gt hij) (hI.nonneg i j)
          simp [hz]
      _ = _ := by
        simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          Matrix.sum_row_of_mem_rowStochastic hP, Matrix.mulVec, dotProduct]
  apply Eq.symm
  apply π.poisson_unique hP hI (π.drift g)
  · ext i
    change (f i - π.prob ⬝ᵥ f) - (∑ j, P i j * (f j - π.prob ⬝ᵥ f)) = π.drift g i
    rw [hd]
    simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Matrix.sum_row_of_mem_rowStochastic hP, Matrix.mulVec, dotProduct]
    <;> ring
  · change π.prob ⬝ᵥ (f - (fun _ => π.prob ⬝ᵥ f)) = 0
    rw [dotProduct_sub, π.average_const, sub_self]

theorem varianceRate_eq_zero_iff_coboundary (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) :
    π.varianceRate hP hI g = 0 ↔
      ∃ c : ℝ, ∃ f : V → ℝ, ∀ i j, 0 < P i j → g i j = c + f i - f j := by
  constructor
  · intro hv
    exact ⟨π.meanReward g, π.corrector hP hI g, (π.varianceRate_eq_zero_iff hP hI g).mp hv⟩
  · rintro ⟨c, f, hg⟩
    apply (π.varianceRate_eq_zero_iff hP hI g).mpr
    have hm := π.coboundary_mean hP hI g c f hg
    have hh := π.coboundary_corrector hP hI g c f hg
    intro i j hij
    rw [hm, hh, hg i j hij]
    ring

include π in
/-- Every non-coboundary reward has strictly positive curvature at every real tilt. -/
theorem pressure_strict_curvature (hI : P.IsIrreducible) (g : V → V → ℝ)
    (hg : ¬ ∃ c : ℝ, ∃ f : V → ℝ, ∀ i j, 0 < P i j → g i j = c + f i - f j)
    (a : ℝ) : 0 < deriv (deriv (pressure P g)) a := by
  let Q := π.globalDoob hI g a
  let hQ := (π.globalDoob_stochastic hI g a).1
  let hJ := π.globalDoob_irreducible hI g a
  let ρ := stationary Q hQ hJ
  rw [π.pressure_second_derivative hI g a]
  have hn : 0 ≤ ρ.varianceRate hQ hJ g :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (ρ.positive i).le (hJ.nonneg i j)) (sq_nonneg _)
  apply lt_of_le_of_ne hn
  intro hz
  obtain ⟨c, f, hc⟩ := (ρ.varianceRate_eq_zero_iff_coboundary hQ hJ g).mp hz.symm
  exact hg ⟨c, f, fun i j hij => hc i j ((π.globalDoob_stochastic hI g a).2 i j |>.mpr hij)⟩

/-- Uniqueness of the normalized actual Perron vector follows from harmonic uniqueness. -/
theorem perronVector_unique (hI : P.IsIrreducible) (g : V → V → ℝ) (t : ℝ)
    (x : V → ℝ) (he : tilt P g t *ᵥ x = eigenvalue P g t • x)
    (hx : π.prob ⬝ᵥ x = 1) : x = π.perronVector hI g t := by
  let r := π.perronVector hI g t
  let Q := π.globalDoob hI g t
  have hr := (π.perronVector_spec hI g t).1
  have hl := eigenvalue_pos P hI g t
  have hq : Q *ᵥ (fun i => x i / r i) = (fun i => x i / r i) := by
    ext i
    change (∑ j, Q i j * (x j / r j)) = x i / r i
    calc
      _ = (∑ j, tilt P g t i j * x j) / (eigenvalue P g t * r i) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [Q, globalDoob, r]
        field_simp [(hr i).ne', (hr j).ne', hl.ne']
      _ = x i / r i := by
        have hi := congrFun he i
        change (∑ j, tilt P g t i j * x j) = eigenvalue P g t * x i at hi
        rw [hi]
        field_simp
  obtain ⟨c, hc⟩ := harmonic_constant Q (π.globalDoob_stochastic hI g t).1
    (π.globalDoob_irreducible hI g t) _ hq
  have hxc : x = c • r := by
    ext i
    exact (div_eq_iff (hr i).ne').mp (congrFun hc i)
  have hc1 : c = 1 := by
    rw [hxc, dotProduct_smul, (π.perronVector_spec hI g t).2.1, smul_eq_mul, mul_one] at hx
    exact hx
  simpa [hc1, r] using hxc

/-- The globally chosen actual Perron data agree with the implicit local Doob family. -/
theorem globalDoob_eq_doob_eventually (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) :
    π.globalDoob hI g =ᶠ[nhds (0 : ℝ)] π.doob hP hI g := by
  filter_upwards [π.eigenbranch_eventually hP hI g,
    π.eigenbranch_radius_eventually hP hI g] with t he hl
  have hr : (π.eigenbranch hP hI g t).1 = π.perronVector hI g t := by
    apply π.perronVector_unique hI g t _ _ he.2
    rw [hl]
    exact he.1
  ext i j
  simp only [globalDoob, doob, hl, hr]

theorem pressure_zero (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) : pressure P g 0 = 0 := by
  have he : tilt P g 0 *ᵥ (fun _ => 1) = (1 : ℝ) • (fun _ => 1) := by
    ext i
    simpa [tilt, Matrix.mulVec, dotProduct] using Matrix.sum_row_of_mem_rowStochastic hP i
  have hl := (positive_eigenpair_identifies_radius P hI g 0 1 (fun _ => 1)
    zero_lt_one (fun _ => zero_lt_one) he).2
  simp [pressure, hl]

private theorem coboundary_tilt_entry (hI : P.IsIrreducible) (g : V → V → ℝ)
    (c : ℝ) (f : V → ℝ) (hg : ∀ i j, 0 < P i j → g i j = c + f i - f j)
    (t : ℝ) (i j : V) :
    tilt P g t i j * Real.exp (t * f j) =
      Real.exp (t*c) * Real.exp (t * f i) * P i j := by
  by_cases hij : 0 < P i j
  · simp only [tilt, hg i j hij]
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    rw [show t * (c + f i - f j) + t*f j = t*c + t*f i by ring]
    ring
  · have hz : P i j = 0 := le_antisymm (le_of_not_gt hij) (hI.nonneg i j)
    simp [tilt, hz]

/-- In the zero-variance case pressure is linear and the actual global Doob kernel is P. -/
theorem coboundary_global (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (c : ℝ) (f : V → ℝ)
    (hg : ∀ i j, 0 < P i j → g i j = c + f i - f j) (t : ℝ) :
    pressure P g t = t*c ∧ π.globalDoob hI g t = P := by
  let x := fun i => Real.exp (t*f i)
  have he : tilt P g t *ᵥ x = Real.exp (t*c) • x := by
    ext i
    change (∑ j, tilt P g t i j * Real.exp (t*f j)) = _
    simp_rw [coboundary_tilt_entry hI g c f hg]
    rw [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic hP, mul_one]
    rfl
  have hl : eigenvalue P g t = Real.exp (t*c) :=
    (positive_eigenpair_identifies_radius P hI g t _ x (Real.exp_pos _)
      (fun _ => Real.exp_pos _) he).2
  have hs : 0 < π.prob ⬝ᵥ x :=
    Finset.sum_pos (fun i _ => mul_pos (π.positive i) (Real.exp_pos _)) Finset.univ_nonempty
  have hr : π.perronVector hI g t = fun i => x i / (π.prob ⬝ᵥ x) := by
    apply Eq.symm
    apply π.perronVector_unique hI g t
    · rw [hl]
      ext i
      change (∑ j, tilt P g t i j * (x j / (π.prob ⬝ᵥ x))) =
        Real.exp (t*c) * (x i / (π.prob ⬝ᵥ x))
      simp only [← mul_div_assoc, ← Finset.sum_div]
      have hi := congrFun he i
      exact congrArg (fun z : ℝ => z / (π.prob ⬝ᵥ x)) hi
    · simp only [dotProduct, ← mul_div_assoc, ← Finset.sum_div]
      exact div_self hs.ne'
  refine ⟨by simp [pressure, hl], ?_⟩
  ext i j
  change tilt P g t i j * π.perronVector hI g t j /
    (eigenvalue P g t * π.perronVector hI g t i) = P i j
  rw [hr, hl]
  have ht := coboundary_tilt_entry hI g c f hg t i j
  change tilt P g t i j * x j = Real.exp (t*c) * x i * P i j at ht
  apply (div_eq_iff (mul_pos (Real.exp_pos _) (div_pos (Real.exp_pos _) hs)).ne').mpr
  dsimp only
  rw [← mul_div_assoc, ht]
  ring

end Stationary
end D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
