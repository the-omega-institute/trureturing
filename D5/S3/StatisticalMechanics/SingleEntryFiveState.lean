/- GID: D5/S3/StatisticalMechanics/SingleEntryFiveState
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntryFiveState
   mirror-E: none(waiver:five-state-forward-equations)
   anchors: []
   utility: none
   digest: The repressed initial condition yields strict positive two-site association. -/

import D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-! # The two-site single-entry network

States are ordered as R, 00, 10, 01, 11. The forward equations are the
independent anchor for the trajectory; association is not a trajectory premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder
open Set Matrix Filter
namespace D5.S3.StatisticalMechanics.SingleEntryFiveState

theorem constant_on_nonneg (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ t → HasDerivAt f 0 t) (t : ℝ) (ht : 0 ≤ t) : f t = f 0 := by
  have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := fun _ => 0) (C := 0)
    (fun x hx => (hf x hx.1).hasDerivWithinAt) (by simp)
    (convex_Icc (0 : ℝ) t) (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
  have he : f t - f 0 = 0 := norm_le_zero_iff.mp (by simpa using hn)
  exact sub_eq_zero.mp he

private theorem scalar_decay (f : ℝ → ℝ) (c : ℝ)
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (-c * f t) t)
    (t : ℝ) (ht : 0 ≤ t) : f t = f 0 * Real.exp (-c * t) := by
  have hfac (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (fun u => Real.exp (c * u) * f u) 0 x := by
    convert (((hasDerivAt_id x).const_mul c).exp.mul (hf x hx)) using 1 <;>
      first | rfl | (dsimp; ring)
  have hc := constant_on_nonneg _ hfac t ht
  simp only [mul_zero, Real.exp_zero, one_mul] at hc
  have he := Real.exp_ne_zero (c * t)
  rw [neg_mul, Real.exp_neg]
  field_simp
  nlinarith

theorem positive_forcing (f g : ℝ → ℝ) (c : ℝ)
    (hf0 : f 0 = 0)
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (-c * f t + g t) t)
    (hg : ∀ t, 0 < t → 0 < g t) (t : ℝ) (ht : 0 < t) : 0 < f t := by
  let H := fun u => Real.exp (c * u) * f u
  have hH (x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt H (Real.exp (c * x) * g x) x := by
    convert (((hasDerivAt_id x).const_mul c).exp.mul (hf x hx)) using 1 <;>
      first | rfl | (dsimp [H]; ring)
  have hmono : StrictMonoOn H (Icc 0 t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro x hx
      exact (hH x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hH x hx.1.le).deriv]
      exact mul_pos (Real.exp_pos _) (hg x hx.1)
  have h := hmono (left_mem_Icc.mpr ht.le) (right_mem_Icc.mpr ht.le) ht
  dsimp [H] at h
  rw [hf0, mul_zero] at h
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h

theorem symmetric_return_data {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (o : V) (ho : 0 < A o o)
    (y : ℝ → V → ℝ) (y0 : y 0 = Pi.single o 1)
    (hy : ∀ t, 0 ≤ t → ∀ i,
      HasDerivAt (fun u => y u i) (-(A *ᵥ y t) i) t) :
    ∃ lam c : V → ℝ,
      (∀ j, 0 ≤ lam j ∧ 0 ≤ c j) ∧ (∑ j, c j) = 1 ∧
      (∃ j, 0 < lam j * c j) ∧
      (∀ t, 0 ≤ t → y t o = ∑ j, c j * Real.exp (-lam j * t)) ∧
      (∀ t, 0 ≤ t → deriv (fun u => y u o) t < 0) ∧
      ∃ l : V → ℝ, (∀ i, Tendsto (fun t => y t i) atTop (nhds (l i))) ∧
        A *ᵥ l = 0 ∧
        (lam = hA.1.eigenvalues ∧
          c = fun j => (hA.1.eigenvectorUnitary : Matrix V V ℝ) o j ^ 2) ∧
        ∀ t, 0 ≤ t → ∀ i, y t i =
          ∑ j, (hA.1.eigenvectorUnitary : Matrix V V ℝ) i j *
            (hA.1.eigenvectorUnitary : Matrix V V ℝ) o j * Real.exp (-lam j * t) := by
  let U : Matrix V V ℝ := hA.1.eigenvectorUnitary
  let lam := hA.1.eigenvalues
  let c := fun t j => ∑ i, U i j * y t i
  have hsym (i k : V) : A i k = A k i := by
    have hh := congrFun (congrFun hA.1.eq k) i
    simpa using hh
  have heig (j i : V) : (∑ k, A i k * U k j) = lam j * U i j := by
    simpa [U, lam, mulVec, dotProduct] using congrFun (hA.1.mulVec_eigenvectorBasis j) i
  have hc (t : ℝ) (ht : 0 ≤ t) (j : V) :
      HasDerivAt (fun u => c u j) (-lam j * c t j) t := by
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hy t ht i).const_mul (U i j))
    convert hd using 1
    dsimp [c]
    simp only [mulVec, dotProduct, mul_neg, Finset.sum_neg_distrib, neg_mul]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    symm
    calc
      (∑ i, U i j * (A i k * y t k)) = (∑ i, A k i * U i j) * y t k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [hsym i k]
        ring
      _ = (lam j * U k j) * y t k := by rw [heig]
      _ = lam j * (U k j * y t k) := by ring
  have hc0 (j : V) : c 0 j = U o j := by simp [c, y0, Pi.single_apply, eq_comm]
  have hct (t : ℝ) (ht : 0 ≤ t) (j : V) :
      c t j = U o j * Real.exp (-lam j * t) := by
    simpa only [hc0] using scalar_decay (fun u => c u j) (lam j)
      (fun u hu => hc u hu j) t ht
  have hU : U * U.transpose = 1 := by
    simpa only [U, Unitary.coe_star, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.1.eigenvectorUnitary
  have reconstruct (t : ℝ) (i : V) : y t i = ∑ j, U i j * c t j := by
    have hh := congrFun (mulVec_mulVec (y t) U U.transpose) i
    rw [hU, one_mulVec] at hh
    exact hh.symm
  have hreturn : ∀ t, 0 ≤ t →
      y t o = ∑ j, U o j ^ 2 * Real.exp (-lam j * t) := by
    intro t ht
    rw [reconstruct t o]
    apply Finset.sum_congr rfl
    intro j _
    rw [hct t ht j]
    ring
  have hdiag : A o o = ∑ j, lam j * U o j ^ 2 := by
    have hm : A = U * diagonal lam * U.transpose := by
      simpa only [U, lam, Unitary.conjStarAlgAut_apply, Unitary.coe_star,
        star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
        Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hA.1.spectral_theorem
    rw [hm, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnonneg (j : V) : 0 ≤ lam j * U o j ^ 2 :=
    mul_nonneg (hA.eigenvalues_nonneg j) (sq_nonneg _)
  have hex : ∃ j, 0 < lam j * U o j ^ 2 := by
    have hs : 0 < ∑ j, lam j * U o j ^ 2 := by rwa [← hdiag]
    simpa using (Finset.sum_pos_iff_of_nonneg (fun j _ => hnonneg j)).mp hs
  have hdecr : ∀ t, 0 ≤ t → deriv (fun u => y u o) t < 0 := by
    intro t ht
    have hder : HasDerivAt (fun u => ∑ j, U o j ^ 2 * Real.exp (-lam j * u))
        (∑ j, -(lam j * U o j ^ 2 * Real.exp (-lam j * t))) t := by
      apply HasDerivAt.fun_sum
      intro j _
      convert (((hasDerivAt_id t).const_mul (-lam j)).exp.const_mul (U o j ^ 2)) using 1
      all_goals (first | rfl | (dsimp; ring))
    have hpos : 0 < ∑ j, lam j * U o j ^ 2 * Real.exp (-lam j * t) := by
      apply (Finset.sum_pos_iff_of_nonneg
        (fun j _ => mul_nonneg (hnonneg j) (Real.exp_pos _).le)).mpr
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, Finset.mem_univ _, mul_pos hj (Real.exp_pos _)⟩
    by_cases hzero : t = 0
    · subst t
      rw [(hy 0 le_rfl o).deriv, y0]
      simpa using neg_neg_of_pos ho
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
      have heq : (fun u => y u o) =ᶠ[nhds t]
          (fun u => ∑ j, U o j ^ 2 * Real.exp (-lam j * u)) :=
        Filter.eventually_of_mem (Ioi_mem_nhds htpos) (fun u hu => hreturn u hu.le)
      rw [heq.deriv_eq, hder.deriv, Finset.sum_neg_distrib]
      exact neg_neg_of_pos hpos
  let b : V → ℝ := fun j => if lam j = 0 then U o j else 0
  let l : V → ℝ := fun i => ∑ j, U i j * b j
  have hclim (j : V) : Tendsto (fun t => c t j) atTop (nhds (b j)) := by
    have he : (fun t => c t j) =ᶠ[atTop]
        (fun t => U o j * Real.exp (-lam j * t)) :=
      (eventually_ge_atTop 0).mono (fun t ht => hct t ht j)
    apply Tendsto.congr' he.symm
    by_cases hz : lam j = 0
    · simpa [b, hz] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => U o j) atTop (nhds (U o j)))
    · have hl : 0 < lam j := lt_of_le_of_ne (hA.eigenvalues_nonneg j) (Ne.symm hz)
      have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hl)
      simpa [b, hz, neg_mul] using hlim.const_mul (U o j)
  have hlim (i : V) : Tendsto (fun t => y t i) atTop (nhds (l i)) := by
    simp_rw [reconstruct]
    exact tendsto_finsetSum _ (fun j _ => (hclim j).const_mul (U i j))
  have hstat : A *ᵥ l = 0 := by
    ext i
    change (∑ k, A i k * (∑ j, U k j * b j)) = 0
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [show (∑ k, A i k * (U k j * b j)) =
        (∑ k, A i k * U k j) * b j by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring]
    rw [heig]
    dsimp [b]
    split_ifs with hz <;> simp [hz]
  refine ⟨lam, (fun j => U o j ^ 2),
    (fun j => ⟨hA.eigenvalues_nonneg j, sq_nonneg _⟩), ?_, hex, hreturn, hdecr,
    l, hlim, hstat, ⟨rfl, rfl⟩, ?_⟩
  · simpa [y0] using (hreturn 0 le_rfl).symm
  · intro t ht i
    rw [reconstruct]
    apply Finset.sum_congr rfl
    intro j _
    rw [hct t ht j]
    ring

/-- Six independent positive transition rates. The letters `a,b` refer to site 1
and `c,d` to site 2; `eta,theta` refer to 00 to R and R to 00. -/
structure Rates where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  eta : ℝ
  theta : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  d_pos : 0 < d
  eta_pos : 0 < eta
  theta_pos : 0 < theta

/-- Column generator in the state order R, 00, 10, 01, 11. -/
def generator (k : Rates) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-k.theta, k.eta, 0, 0, 0;
      k.theta, -(k.a + k.c + k.eta), k.b, k.d, 0;
      0, k.a, -(k.b + k.c), 0, k.d;
      0, k.c, 0, -(k.a + k.d), k.b;
      0, 0, k.c, k.a, -(k.b + k.d)]

/-- A trajectory is anchored by the generator and the repressed initial state. -/
def ForwardSolution (k : Rates) (p : ℝ → Fin 5 → ℝ) : Prop :=
  p 0 = Pi.single 0 1 ∧ ∀ t, 0 ≤ t → ∀ i,
    HasDerivAt (fun u => p u i) ((generator k *ᵥ p t) i) t

private def edgeMatrix (k : Rates) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![Real.sqrt k.theta, -Real.sqrt k.eta, 0, 0, 0;
      0, Real.sqrt k.a, -Real.sqrt k.b, 0, 0;
      0, Real.sqrt k.c, 0, -Real.sqrt k.d, 0;
      0, 0, Real.sqrt k.c, 0, -Real.sqrt k.d;
      0, 0, 0, Real.sqrt k.a, -Real.sqrt k.b]

private def gram (k : Rates) : Matrix (Fin 5) (Fin 5) ℝ :=
  (edgeMatrix k).transpose * edgeMatrix k

private def scale (k : Rates) : Fin 5 → ℝ :=
  ![Real.sqrt k.eta * Real.sqrt k.b * Real.sqrt k.d,
    Real.sqrt k.theta * Real.sqrt k.b * Real.sqrt k.d,
    Real.sqrt k.theta * Real.sqrt k.a * Real.sqrt k.d,
    Real.sqrt k.theta * Real.sqrt k.b * Real.sqrt k.c,
    Real.sqrt k.theta * Real.sqrt k.a * Real.sqrt k.c]

private theorem scale_pos (k : Rates) (i : Fin 5) : 0 < scale k i := by
  have ha := Real.sqrt_pos.mpr k.a_pos
  have hb := Real.sqrt_pos.mpr k.b_pos
  have hc := Real.sqrt_pos.mpr k.c_pos
  have hd := Real.sqrt_pos.mpr k.d_pos
  have he := Real.sqrt_pos.mpr k.eta_pos
  have ht := Real.sqrt_pos.mpr k.theta_pos
  fin_cases i
  · exact mul_pos (mul_pos he hb) hd
  · exact mul_pos (mul_pos ht hb) hd
  · exact mul_pos (mul_pos ht ha) hd
  · exact mul_pos (mul_pos ht hb) hc
  · exact mul_pos (mul_pos ht ha) hc

private theorem gram_entries (k : Rates) : gram k =
    !![k.theta, -(Real.sqrt k.theta * Real.sqrt k.eta), 0, 0, 0;
      -(Real.sqrt k.theta * Real.sqrt k.eta), k.a + k.c + k.eta,
        -(Real.sqrt k.a * Real.sqrt k.b), -(Real.sqrt k.c * Real.sqrt k.d), 0;
      0, -(Real.sqrt k.a * Real.sqrt k.b), k.b + k.c, 0,
        -(Real.sqrt k.c * Real.sqrt k.d);
      0, -(Real.sqrt k.c * Real.sqrt k.d), 0, k.a + k.d,
        -(Real.sqrt k.a * Real.sqrt k.b);
      0, 0, -(Real.sqrt k.c * Real.sqrt k.d),
        -(Real.sqrt k.a * Real.sqrt k.b), k.b + k.d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, edgeMatrix, Matrix.mul_apply, Fin.sum_univ_five, ← pow_two,
      Real.sq_sqrt k.a_pos.le, Real.sq_sqrt k.b_pos.le,
      Real.sq_sqrt k.c_pos.le, Real.sq_sqrt k.d_pos.le,
      Real.sq_sqrt k.eta_pos.le, Real.sq_sqrt k.theta_pos.le] <;> ring

private theorem similarity (k : Rates) (i j : Fin 5) :
    generator k i j * scale k j = -(scale k i * gram k i j) := by
  rw [gram_entries]
  fin_cases i <;> fin_cases j <;>
    simp [generator, scale] <;> ring_nf <;>
    simp [Real.sq_sqrt k.a_pos.le, Real.sq_sqrt k.b_pos.le,
      Real.sq_sqrt k.c_pos.le, Real.sq_sqrt k.d_pos.le,
      Real.sq_sqrt k.eta_pos.le, Real.sq_sqrt k.theta_pos.le] <;> ring

private theorem return_spectral_data (k : Rates) (p : ℝ → Fin 5 → ℝ)
    (hp : ForwardSolution k p) :
    ∃ lam c : Fin 5 → ℝ,
      (∀ j, 0 ≤ lam j ∧ 0 ≤ c j) ∧ (∑ j, c j) = 1 ∧
      (∃ j, 0 < lam j * c j) ∧
      (∀ t, 0 ≤ t → p t 0 = ∑ j, c j * Real.exp (-lam j * t)) ∧
      (∀ t, 0 ≤ t → 0 < k.theta * p t 0 - k.eta * p t 1) ∧
      ∃ l : Fin 5 → ℝ, (∀ i, Tendsto (fun t => p t i) atTop (nhds (l i))) ∧
        generator k *ᵥ l = 0 := by
  let y := fun u i => scale k 0 / scale k i * p u i
  have hscale (i : Fin 5) : scale k i ≠ 0 := ne_of_gt (scale_pos k i)
  have hA : (gram k).PosSemidef := by
    simpa [gram, star_eq_conjTranspose] using posSemidef_conjTranspose_mul_self (edgeMatrix k)
  have hy0 : y 0 = Pi.single 0 1 := by
    funext i
    dsimp [y]
    rw [hp.1]
    by_cases hi : i = 0
    · subst i
      simp [hscale]
    · simp [Pi.single_apply, hi, Ne.symm hi]
  have hy (u : ℝ) (hu : 0 ≤ u) (i : Fin 5) :
      HasDerivAt (fun x => y x i) (-(gram k *ᵥ y u) i) u := by
    have hd := (hp.2 u hu i).const_mul (scale k 0 / scale k i)
    convert hd using 1
    dsimp [y, mulVec, dotProduct]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hs := similarity k i j
    field_simp [hscale]
    nlinarith [congrArg (fun z : ℝ => z * p u j) hs]
  have hdiag : 0 < gram k 0 0 := by simpa [gram_entries] using k.theta_pos
  obtain ⟨lam, c, hn, hsum, hmode, hrep, hdecr, l, hlim, hstat, _, _⟩ :=
    symmetric_return_data (gram k) hA 0 hdiag y hy0 hy
  have hreturn : (fun u => y u 0) = (fun u => p u 0) := by
    funext u
    simp [y, hscale]
  refine ⟨lam, c, hn, hsum, hmode, ?_, ?_, ?_⟩
  · intro t ht
    change (fun u => p u 0) t = _
    rw [← hreturn]
    exact hrep t ht
  · intro t ht
    have hneg := hdecr t ht
    rw [hreturn, (hp.2 t ht 0).deriv] at hneg
    simp [generator, mulVec, dotProduct, Fin.sum_univ_five] at hneg
    linarith
  · let L : Fin 5 → ℝ := fun i => scale k i / scale k 0 * l i
    refine ⟨L, ?_, ?_⟩
    · intro i
      have he : (fun t => p t i) = (fun t => scale k i / scale k 0 * y t i) := by
        funext t
        dsimp [y]
        field_simp [hscale]
      rw [he]
      exact (hlim i).const_mul _
    · ext i
      have he := congrFun hstat i
      change (generator k *ᵥ L) i = 0
      have hid : (generator k *ᵥ L) i = -(scale k i / scale k 0 * (gram k *ᵥ l) i) := by
        dsimp [mulVec, dotProduct, L]
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have hs := similarity k i j
        field_simp [hscale]
        nlinarith [congrArg (fun z : ℝ => z * l j) hs]
      rw [hid, he]
      simp

private theorem net_input_pos (k : Rates) (p : ℝ → Fin 5 → ℝ)
    (hp : ForwardSolution k p) (t : ℝ) (ht : 0 ≤ t) :
    0 < k.theta * p t 0 - k.eta * p t 1 := by
  obtain ⟨_, _, _, _, _, _, hi⟩ := return_spectral_data k p hp
  exact hi.1 t ht

/-- Total mass outside R. -/
def activeMass (p : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ := 1 - p t 0

/-- Occupancy of the first actual site. -/
def firstOccupancy (p : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ := p t 2 + p t 4

/-- Occupancy of the second actual site. -/
def secondOccupancy (p : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ := p t 3 + p t 4

/-- Unnormalized conditional association residual. -/
def association (p : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  activeMass p t * p t 4 - firstOccupancy p t * secondOccupancy p t

/-- Width of the five-mode probability fiber at the two actual site margins. -/
def fiberWidth (p : ℝ → Fin 5 → ℝ) (t : ℝ) : ℝ :=
  min (min (firstOccupancy p t) (secondOccupancy p t))
    (min (activeMass p t - firstOccupancy p t) (activeMass p t - secondOccupancy p t))

private theorem mass_conservation (k : Rates) (p : ℝ → Fin 5 → ℝ)
    (hp : ForwardSolution k p) (t : ℝ) (ht : 0 ≤ t) : ∑ i, p t i = 1 := by
  have hd (u : ℝ) (hu : 0 ≤ u) : HasDerivAt (fun v => ∑ i, p v i) 0 u := by
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hp.2 u hu i) using 1
    simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
    ring
  have hh := constant_on_nonneg _ hd t ht
  simpa [hp.1, Pi.single_apply] using hh

/-- Every trajectory of the specified five-state forward system, starting at R,
has strictly positive fiber width and association at every positive time. The
only incomparable Boolean configurations are 10 and 01, giving strict MTP2. -/
private theorem strict_for_every_forward_solution (k : Rates) (p : ℝ → Fin 5 → ℝ)
    (hp : ForwardSolution k p) (t : ℝ) (ht : 0 < t) :
    0 < activeMass p t ∧ 0 < fiberWidth p t ∧ 0 < association p t ∧
      p t 2 * p t 3 < p t 1 * p t 4 ∧
      0 < k.theta * p t 0 - k.eta * p t 1 := by
  let f := fun u => k.theta * p u 0 - k.eta * p u 1
  let r := activeMass p
  let X := firstOccupancy p
  let Y := secondOccupancy p
  let K := fun u => p u 4
  let D := association p
  let s := k.a + k.b + k.c + k.d
  have fpos (u : ℝ) (hu : 0 ≤ u) : 0 < f u := net_input_pos k p hp u hu
  have mass (u : ℝ) (hu : 0 ≤ u) :
      p u 0 + p u 1 + p u 2 + p u 3 + p u 4 = 1 := by
    simpa [Fin.sum_univ_five, add_assoc] using mass_conservation k p hp u hu
  have r0 : r 0 = 0 := by simp [r, activeMass, hp.1, Pi.single_apply]
  have X0 : X 0 = 0 := by simp [X, firstOccupancy, hp.1, Pi.single_apply]
  have Y0 : Y 0 = 0 := by simp [Y, secondOccupancy, hp.1, Pi.single_apply]
  have K0 : K 0 = 0 := by simp [K, hp.1, Pi.single_apply]
  have D0 : D 0 = 0 := by
    change r 0 * K 0 - X 0 * Y 0 = 0
    rw [r0, X0]
    ring
  have dr (u : ℝ) (hu : 0 ≤ u) : HasDerivAt r (f u) u := by
    convert (hasDerivAt_const u (1 : ℝ)).sub (hp.2 u hu 0) using 1
    all_goals first | rfl |
      (simp [f, generator, mulVec, dotProduct, Fin.sum_univ_five] <;> ring)
  have dX (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt X (-(k.a + k.b) * X u + k.a * r u) u := by
    convert (hp.2 u hu 2).add (hp.2 u hu 4) using 1
    all_goals
      first
      | rfl
      | dsimp [X, r, firstOccupancy, activeMass]
        simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
        linear_combination -k.a * mass u hu
  have dY (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt Y (-(k.c + k.d) * Y u + k.c * r u) u := by
    convert (hp.2 u hu 3).add (hp.2 u hu 4) using 1
    all_goals
      first
      | rfl
      | dsimp [Y, r, secondOccupancy, activeMass]
        simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
        linear_combination -k.c * mass u hu
  have dK (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt K (-s * K u + (k.c * X u + k.a * Y u)) u := by
    convert hp.2 u hu 4 using 1
    dsimp [K, X, Y, firstOccupancy, secondOccupancy, s]
    simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
    ring
  have rpos (u : ℝ) (hu : 0 < u) : 0 < r u := by
    apply positive_forcing r f 0 r0 _ (fun x hx => fpos x hx.le) u hu
    intro x hx
    simpa using dr x hx
  have Xpos (u : ℝ) (hu : 0 < u) : 0 < X u :=
    positive_forcing X (fun x => k.a * r x) (k.a + k.b) X0 dX
      (fun x hx => mul_pos k.a_pos (rpos x hx)) u hu
  have Ypos (u : ℝ) (hu : 0 < u) : 0 < Y u :=
    positive_forcing Y (fun x => k.c * r x) (k.c + k.d) Y0 dY
      (fun x hx => mul_pos k.c_pos (rpos x hx)) u hu
  have rXpos (u : ℝ) (hu : 0 < u) : 0 < r u - X u := by
    apply positive_forcing (fun x => r x - X x)
      (fun x => k.b * r x + f x) (k.a + k.b) (by rw [r0, X0]; ring) _
      (fun x hx => add_pos (mul_pos k.b_pos (rpos x hx)) (fpos x hx.le)) u hu
    intro x hx
    convert (dr x hx).sub (dX x hx) using 1 <;> ring
  have rYpos (u : ℝ) (hu : 0 < u) : 0 < r u - Y u := by
    apply positive_forcing (fun x => r x - Y x)
      (fun x => k.d * r x + f x) (k.c + k.d) (by rw [r0, Y0]; ring) _
      (fun x hx => add_pos (mul_pos k.d_pos (rpos x hx)) (fpos x hx.le)) u hu
    intro x hx
    convert (dr x hx).sub (dY x hx) using 1 <;> ring
  have Kpos (u : ℝ) (hu : 0 < u) : 0 < K u :=
    positive_forcing K (fun x => k.c * X x + k.a * Y x) s K0 dK
      (fun x hx => add_pos (mul_pos k.c_pos (Xpos x hx))
        (mul_pos k.a_pos (Ypos x hx))) u hu
  have dD (u : ℝ) (hu : 0 ≤ u) : HasDerivAt D (-s * D u + f u * K u) u := by
    convert ((dr u hu).mul (dK u hu)).sub ((dX u hu).mul (dY u hu)) using 1
    all_goals
      first
      | rfl
      | dsimp [D, association, r, X, Y, K, activeMass, firstOccupancy, secondOccupancy, s]
        ring
  have Dpos : 0 < D t := positive_forcing D (fun u => f u * K u) s D0 dD
    (fun u hu => mul_pos (fpos u hu.le) (Kpos u hu)) t ht
  have hwidth : 0 < fiberWidth p t := by
    simp only [fiberWidth, lt_min_iff]
    exact ⟨⟨Xpos t ht, Ypos t ht⟩, ⟨rXpos t ht, rYpos t ht⟩⟩
  have hdet : association p t = p t 1 * p t 4 - p t 2 * p t 3 := by
    dsimp [association, activeMass, firstOccupancy, secondOccupancy]
    linear_combination -(p t 4) * mass t ht.le
  refine ⟨rpos t ht, hwidth, Dpos, ?_, fpos t ht.le⟩
  change 0 < association p t at Dpos
  rw [hdet] at Dpos
  linarith

/-- The actual matrix-exponential trajectory from the inhibited state. -/
def canonicalTrajectory (k : Rates) (t : ℝ) (i : Fin 5) : ℝ :=
  NormedSpace.exp (t • generator k) i 0

open scoped Matrix.Norms.Operator in
private def entry (i j : Fin 5) : Matrix (Fin 5) (Fin 5) ℝ →L[ℝ] ℝ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply j).comp (continuous_apply i)

private theorem canonical_forward (k : Rates) : ForwardSolution k (canonicalTrajectory k) := by
  constructor
  · funext i
    simp [canonicalTrajectory, Matrix.one_apply, Pi.single_apply, eq_comm]
  · intro t _ i
    open scoped Matrix.Norms.Operator in
      have hd := (entry i 0).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_exp_smul_const' (generator k) t)
      convert! hd using 1 <;>
        simp [canonicalTrajectory, entry, Matrix.mul_apply, mulVec, dotProduct, Function.comp_def]

private theorem exp_entry_nonneg (B : Matrix (Fin 5) (Fin 5) ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (i j : Fin 5) : 0 ≤ NormedSpace.exp B i j := by
  have hpow (n : ℕ) : ∀ i j, 0 ≤ (B ^ n) i j := by
    induction n with
    | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
    | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hB k j))
  open scoped Matrix.Norms.Operator in
    have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) B).map (entry i j)
      (entry i j).continuous
    change 0 ≤ (entry i j) (NormedSpace.exp B)
    rw [← hs.tsum_eq]
    apply tsum_nonneg
    intro n
    change 0 ≤ (n.factorial : ℝ)⁻¹ * (B ^ n) i j
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hpow n i j)

private theorem canonical_nonneg (k : Rates) (t : ℝ) (ht : 0 ≤ t) (i : Fin 5) :
    0 ≤ canonicalTrajectory k t i := by
  let C := k.a + k.b + k.c + k.d + k.eta + k.theta
  let B := generator k + C • (1 : Matrix (Fin 5) (Fin 5) ℝ)
  have hB : ∀ i j, 0 ≤ B i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [B, C, generator, Matrix.one_apply] <;>
      linarith [k.a_pos, k.b_pos, k.c_pos, k.d_pos, k.eta_pos, k.theta_pos]
  have hsplit : t • generator k = (-t * C) • (1 : Matrix (Fin 5) (Fin 5) ℝ) + t • B := by
    dsimp [B]
    rw [smul_add, smul_smul]
    module
  have hcomm : Commute ((-t * C) • (1 : Matrix (Fin 5) (Fin 5) ℝ)) (t • B) :=
    (Commute.one_left _).smul_left _
  have hscalar : NormedSpace.exp ((-t * C) • (1 : Matrix (Fin 5) (Fin 5) ℝ)) =
      Real.exp (-t * C) • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    have he : (-t * C) • (1 : Matrix (Fin 5) (Fin 5) ℝ) =
        diagonal (fun _ => -t * C) := by
      ext j l
      simp [Matrix.one_apply, Matrix.diagonal]
    rw [he, Matrix.exp_diagonal]
    ext j l
    simp [Matrix.diagonal, Matrix.one_apply, ← Real.exp_eq_exp_ℝ]
  unfold canonicalTrajectory
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, hscalar, Matrix.smul_mul, one_mul]
  exact mul_nonneg (Real.exp_pos _).le
    (exp_entry_nonneg (t • B) (fun j l => mul_nonneg ht (hB j l)) i 0)

private theorem positive_initial_forcing (f g : ℝ → ℝ) (c : ℝ)
    (hf0 : 0 < f 0)
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (-c * f t + g t) t)
    (hg : ∀ t, 0 ≤ t → 0 ≤ g t) (t : ℝ) (ht : 0 ≤ t) : 0 < f t := by
  let H := fun u => Real.exp (c * u) * f u
  have hd (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt H (Real.exp (c * u) * g u) u := by
    convert (((hasDerivAt_id u).const_mul c).exp.mul (hf u hu)) using 1 <;>
      first | rfl | (dsimp [H]; ring)
  have hm : MonotoneOn H (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro u hu
      exact (hd u hu.1).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact (hd u hu.1.le).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hd u hu.1.le).deriv]
      exact mul_nonneg (Real.exp_pos _).le (hg u hu.1.le)
  have hh := hm (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
  have h0 : H 0 = f 0 := by simp [H]
  rw [h0] at hh
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (lt_of_lt_of_le hf0 hh)

private theorem canonical_positive (k : Rates) (t : ℝ) (ht : 0 < t) :
    ∀ i, 0 < canonicalTrajectory k t i := by
  let p := canonicalTrajectory k
  have hp : ForwardSolution k p := canonical_forward k
  have hn (u : ℝ) (hu : 0 ≤ u) (i : Fin 5) : 0 ≤ p u i :=
    canonical_nonneg k u hu i
  have hR (u : ℝ) (hu : 0 ≤ u) : 0 < p u 0 := by
    apply positive_initial_forcing (fun x => p x 0) (fun x => k.eta * p x 1)
      k.theta (by simp [hp.1]) _
      (fun x hx => mul_nonneg k.eta_pos.le (hn x hx 1)) u hu
    intro x hx
    convert hp.2 x hx 0 using 1
    simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
  have hE (u : ℝ) (hu : 0 < u) : 0 < p u 1 := by
    apply positive_forcing (fun x => p x 1)
      (fun x => k.theta * p x 0 + k.b * p x 2 + k.d * p x 3)
      (k.a + k.c + k.eta) (by simp [hp.1]) _ _ u hu
    · intro x hx
      convert hp.2 x hx 1 using 1
      simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
      ring
    · intro x hx
      exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg (mul_pos k.theta_pos (hR x hx.le))
          (mul_nonneg k.b_pos.le (hn x hx.le 2)))
        (mul_nonneg k.d_pos.le (hn x hx.le 3))
  have hX (u : ℝ) (hu : 0 < u) : 0 < p u 2 := by
    apply positive_forcing (fun x => p x 2) (fun x => k.a * p x 1 + k.d * p x 4)
      (k.b + k.c) (by simp [hp.1]) _ _ u hu
    · intro x hx
      convert hp.2 x hx 2 using 1
      simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
      ring
    · intro x hx
      exact add_pos_of_pos_of_nonneg (mul_pos k.a_pos (hE x hx))
        (mul_nonneg k.d_pos.le (hn x hx.le 4))
  have hY (u : ℝ) (hu : 0 < u) : 0 < p u 3 := by
    apply positive_forcing (fun x => p x 3) (fun x => k.c * p x 1 + k.b * p x 4)
      (k.a + k.d) (by simp [hp.1]) _ _ u hu
    · intro x hx
      convert hp.2 x hx 3 using 1
      simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
      ring
    · intro x hx
      exact add_pos_of_pos_of_nonneg (mul_pos k.c_pos (hE x hx))
        (mul_nonneg k.b_pos.le (hn x hx.le 4))
  have hK (u : ℝ) (hu : 0 < u) : 0 < p u 4 := by
    apply positive_forcing (fun x => p x 4) (fun x => k.c * p x 2 + k.a * p x 3)
      (k.b + k.d) (by simp [hp.1]) _ _ u hu
    · intro x hx
      convert hp.2 x hx 4 using 1
      simp [generator, mulVec, dotProduct, Fin.sum_univ_five]
      ring
    · intro x hx
      exact add_pos (mul_pos k.c_pos (hX x hx)) (mul_pos k.a_pos (hY x hx))
  intro i
  fin_cases i
  · exact hR t ht.le
  · exact hE t ht
  · exact hX t ht
  · exact hY t ht
  · exact hK t ht

/-- The same law in the established admissible-word order 000,100,010,001,101.
The inhibited state is 010, and the joint occupancy is 101. -/
def pyramidLaw (p : ℝ → Fin 5 → ℝ) (t : ℝ) : Fin 5 → ℝ :=
  ![p t 1, p t 2, p t 0, p t 3, p t 4]

/-- Keep inhibited mass and conditionally multiply the two actual site margins. -/
def independentCompletion (p : ℝ → Fin 5 → ℝ) (t : ℝ) : Fin 5 → ℝ :=
  ![p t 0,
    (activeMass p t - firstOccupancy p t) *
      (activeMass p t - secondOccupancy p t) / activeMass p t,
    firstOccupancy p t * (activeMass p t - secondOccupancy p t) / activeMass p t,
    (activeMass p t - firstOccupancy p t) * secondOccupancy p t / activeMass p t,
    firstOccupancy p t * secondOccupancy p t / activeMass p t]

/-- Interaction of a task across the four actual Boolean configurations. -/
def taskContrast (f : Fin 5 → ℝ) : ℝ := f 4 - f 2 - f 3 + f 1

/-- Actual task expectation minus its expectation under independent completion. -/
def taskError (p : ℝ → Fin 5 → ℝ) (f : Fin 5 → ℝ) (t : ℝ) : ℝ :=
  (∑ i, f i * p t i) - ∑ i, f i * independentCompletion p t i

private theorem task_error_identity (k : Rates) (p : ℝ → Fin 5 → ℝ)
    (hp : ForwardSolution k p) (t : ℝ) (ht : 0 < t) (f : Fin 5 → ℝ) :
    taskError p f t = taskContrast f * association p t / activeMass p t := by
  have hr := (strict_for_every_forward_solution k p hp t ht).1
  have he := mass_conservation k p hp t ht.le
  simp only [Fin.sum_univ_five] at he
  have h1 : p t 1 = 1 - p t 0 - p t 2 - p t 3 - p t 4 := by linarith
  have hne : 1 - p t 0 ≠ 0 := ne_of_gt hr
  simp [taskError, taskContrast, independentCompletion, association, activeMass,
    firstOccupancy, secondOccupancy, Fin.sum_univ_five]
  rw [h1]
  field_simp [hne]
  ring

/-- The independent detailed-balance weights, normalized on the actual five
states. This defines a candidate stationary law without any stationarity premise. -/
def equilibriumLaw (k : Rates) : Fin 5 → ℝ :=
  let C := k.theta * (k.a + k.b) * (k.c + k.d) + k.eta * k.b * k.d
  ![k.eta * k.b * k.d / C, k.theta * k.b * k.d / C,
    k.theta * k.a * k.d / C, k.theta * k.b * k.c / C, k.theta * k.a * k.c / C]

private theorem stationary_unique (k : Rates) (l : Fin 5 → ℝ)
    (hs : generator k *ᵥ l = 0) (hm : ∑ i, l i = 1) : l = equilibriumLaw k := by
  have h0 := congrFun hs 0
  have h2 := congrFun hs 2
  have h3 := congrFun hs 3
  have h4 := congrFun hs 4
  simp [generator, mulVec, dotProduct, Fin.sum_univ_five] at h0 h2 h3 h4
  simp only [Fin.sum_univ_five] at hm
  let H := (k.a + k.b) * (k.c + k.d)
  let C := k.theta * H + k.eta * k.b * k.d
  have hH : 0 < H := mul_pos (add_pos k.a_pos k.b_pos) (add_pos k.c_pos k.d_pos)
  have hC : 0 < C := add_pos (mul_pos k.theta_pos hH)
    (mul_pos (mul_pos k.eta_pos k.b_pos) k.d_pos)
  have hX : (k.a + k.b) * (l 2 + l 4) = k.a * (1 - l 0) := by
    linear_combination -h2 - h4 + k.a * hm
  have hY : (k.c + k.d) * (l 3 + l 4) = k.c * (1 - l 0) := by
    linear_combination -h3 - h4 + k.c * hm
  have hK : (k.a + k.b + k.c + k.d) * l 4 =
      k.c * (l 2 + l 4) + k.a * (l 3 + l 4) := by
    linear_combination -h4
  have hKraw : (k.a + k.b + k.c + k.d) *
      (H * l 4 - k.a * k.c * (1 - l 0)) = 0 := by
    dsimp [H]
    linear_combination (k.a + k.b) * (k.c + k.d) * hK +
      k.c * (k.c + k.d) * hX + k.a * (k.a + k.b) * hY
  have hsum : 0 < k.a + k.b + k.c + k.d := by
    linarith [k.a_pos, k.b_pos, k.c_pos, k.d_pos]
  have hKprod : H * l 4 = k.a * k.c * (1 - l 0) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hKraw).resolve_left (ne_of_gt hsum))
  have hXprod : H * l 2 = k.a * k.d * (1 - l 0) := by
    dsimp [H] at *
    linear_combination (k.c + k.d) * hX - hKprod
  have hYprod : H * l 3 = k.b * k.c * (1 - l 0) := by
    dsimp [H] at *
    linear_combination (k.a + k.b) * hY - hKprod
  have hEprod : H * l 1 = k.b * k.d * (1 - l 0) := by
    dsimp [H] at *
    linear_combination (k.a + k.b) * (k.c + k.d) * hm -
      hXprod - hYprod - hKprod
  have hR : C * l 0 = k.eta * k.b * k.d := by
    dsimp [C]
    linear_combination -H * h0 + k.eta * hEprod
  have solve (z v : ℝ) (hz : H * z = v * (1 - l 0)) : z * C = k.theta * v := by
    have he : H * (z * C - k.theta * v) = 0 := by
      dsimp [C] at *
      linear_combination (k.theta * H + k.eta * k.b * k.d) * hz - v * hR
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt hH))
  have hden : k.theta * (k.a + k.b) * (k.c + k.d) + k.eta * k.b * k.d = C := by
    dsimp [C, H]
    ring
  ext i
  fin_cases i <;> simp [equilibriumLaw, hden] <;> rw [eq_div_iff (ne_of_gt hC)]
  · linear_combination hR
  · linear_combination (solve (l 1) (k.b * k.d) hEprod)
  · linear_combination (solve (l 2) (k.a * k.d) hXprod)
  · linear_combination (solve (l 3) (k.b * k.c) hYprod)
  · linear_combination (solve (l 4) (k.a * k.c) hKprod)

private theorem forward_limit (k : Rates) (p : ℝ → Fin 5 → ℝ)
    (hp : ForwardSolution k p) :
    ∀ i, Tendsto (fun t => p t i) atTop (nhds (equilibriumLaw k i)) := by
  obtain ⟨_, _, _, _, _, _, _, l, hlim, hstat⟩ := return_spectral_data k p hp
  have hmass : (∑ i, l i) = 1 := by
    have hl := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
    have he : (fun t => ∑ i, p t i) =ᶠ[atTop] (fun _ => (1 : ℝ)) :=
      (eventually_ge_atTop 0).mono (fun t ht => mass_conservation k p hp t ht)
    exact tendsto_nhds_unique hl (tendsto_const_nhds.congr' he.symm)
  rw [stationary_unique k l hstat hmass] at hlim
  exact hlim

private theorem equilibrium_properties (k : Rates) :
    (∀ i, 0 < equilibriumLaw k i) ∧ (∑ i, equilibriumLaw k i) = 1 ∧
      generator k *ᵥ equilibriumLaw k = 0 ∧
      association (fun _ => equilibriumLaw k) 0 = 0 ∧
      0 < fiberWidth (fun _ => equilibriumLaw k) 0 ∧
      activeMass (fun _ => equilibriumLaw k) 0 =
        k.theta / (k.theta + k.eta *
          (k.b / (k.a + k.b) * (k.d / (k.c + k.d)))) := by
  let C := k.theta * (k.a + k.b) * (k.c + k.d) + k.eta * k.b * k.d
  have ha := k.a_pos
  have hb := k.b_pos
  have hc := k.c_pos
  have hd := k.d_pos
  have he := k.eta_pos
  have ht := k.theta_pos
  have hs : 0 < k.a + k.b := add_pos k.a_pos k.b_pos
  have hu : 0 < k.c + k.d := add_pos k.c_pos k.d_pos
  have hC : 0 < C := add_pos (mul_pos (mul_pos k.theta_pos hs) hu)
    (mul_pos (mul_pos k.eta_pos k.b_pos) k.d_pos)
  have hp (i : Fin 5) : 0 < equilibriumLaw k i := by
    fin_cases i <;> simp only [equilibriumLaw] <;> change 0 < _ / C <;>
      apply div_pos _ hC <;> positivity
  have hm : (∑ i, equilibriumLaw k i) = 1 := by
    simp [equilibriumLaw, Fin.sum_univ_five]
    change _ / C + _ / C + _ / C + _ / C + _ / C = 1
    field_simp [ne_of_gt hC]
    dsimp [C]
    ring
  refine ⟨hp, hm, ?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [generator, equilibriumLaw, mulVec, dotProduct,
      Fin.sum_univ_five] <;> field_simp <;> ring
  · dsimp [association, activeMass, firstOccupancy, secondOccupancy]
    simp [equilibriumLaw]
    change (1 - _ / C) * (_ / C) - (_ / C + _ / C) * (_ / C + _ / C) = 0
    field_simp [ne_of_gt hC]
    dsimp [C]
    ring
  · simp only [fiberWidth, lt_min_iff]
    have h0 := hp 0
    have h1 := hp 1
    have h2 := hp 2
    have h3 := hp 3
    have h4 := hp 4
    simp only [Fin.sum_univ_five] at hm
    dsimp [firstOccupancy, secondOccupancy, activeMass]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · have hden : k.theta + k.eta *
        (k.b / (k.a + k.b) * (k.d / (k.c + k.d))) =
        C / ((k.a + k.b) * (k.c + k.d)) := by
      dsimp [C]
      field_simp [ne_of_gt hs, ne_of_gt hu]
    simp only [activeMass, equilibriumLaw, Matrix.cons_val_zero]
    change 1 - _ / C = _
    rw [hden]
    field_simp [ne_of_gt hC, ne_of_gt hs, ne_of_gt hu]
    dsimp [C]
    ring

private theorem observables_limit (k : Rates) (p : ℝ → Fin 5 → ℝ)
    (hp : ForwardSolution k p) :
    Tendsto (association p) atTop (nhds 0) ∧
    Tendsto (activeMass p) atTop (nhds
      (k.theta / (k.theta + k.eta * (k.b / (k.a + k.b) * (k.d / (k.c + k.d)))))) := by
  have h := forward_limit k p hp
  have hr : Tendsto (activeMass p) atTop
      (nhds (activeMass (fun _ => equilibriumLaw k) 0)) :=
    tendsto_const_nhds.sub (h 0)
  have hD : Tendsto (association p) atTop
      (nhds (association (fun _ => equilibriumLaw k) 0)) :=
    (hr.mul (h 4)).sub (((h 2).add (h 4)).mul ((h 3).add (h 4)))
  have he := equilibrium_properties k
  rw [he.2.2.2.1] at hD
  rw [he.2.2.2.2.2] at hr
  exact ⟨hD, hr⟩

/-- A probability-valued solution exists in the interior of the actual five-mode
pyramid at every positive time. Every solution from R has strict association;
the independent-completion task error is exact and has the interaction's sign. -/
theorem five_state_strict_association (k : Rates) :
    ((∃ p : ℝ → Fin 5 → ℝ, ForwardSolution k p ∧
      (∀ t, 0 ≤ t → (∀ i, 0 ≤ p t i) ∧ ∑ i, p t i = 1) ∧
      ∀ t, 0 < t →
        pyramidLaw p t ∈ D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.openSimplex ∧
        D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.visible (pyramidLaw p t) ∈
          D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.openPyramid) ∧
      (∀ i, 0 < equilibriumLaw k i) ∧ (∑ i, equilibriumLaw k i) = 1 ∧
      generator k *ᵥ equilibriumLaw k = 0 ∧
      association (fun _ => equilibriumLaw k) 0 = 0 ∧
      0 < fiberWidth (fun _ => equilibriumLaw k) 0 ∧
      activeMass (fun _ => equilibriumLaw k) 0 =
        k.theta / (k.theta + k.eta *
          (k.b / (k.a + k.b) * (k.d / (k.c + k.d))))) ∧
    (∀ (p : ℝ → Fin 5 → ℝ), ForwardSolution k p → ∀ t, 0 < t →
      0 < activeMass p t ∧ 0 < fiberWidth p t ∧ 0 < association p t ∧
        p t 2 * p t 3 < p t 1 * p t 4 ∧
        0 < k.theta * p t 0 - k.eta * p t 1 ∧
        (∃ lam c : Fin 5 → ℝ,
          (∀ j, 0 ≤ lam j ∧ 0 ≤ c j) ∧ (∑ j, c j) = 1 ∧
          (∃ j, 0 < lam j * c j) ∧
          ∀ u, 0 ≤ u → p u 0 = ∑ j, c j * Real.exp (-lam j * u)) ∧
        (∀ i, Tendsto (fun u => p u i) atTop (nhds (equilibriumLaw k i))) ∧
        Tendsto (association p) atTop (nhds 0) ∧
        Tendsto (activeMass p) atTop (nhds
          (k.theta / (k.theta + k.eta * (k.b / (k.a + k.b) * (k.d / (k.c + k.d)))))) ∧
        ∀ f : Fin 5 → ℝ,
          taskError p f t = taskContrast f * association p t / activeMass p t ∧
          (taskContrast f ≠ 0 → 0 < taskContrast f * taskError p f t)) := by
  constructor
  · constructor
    · refine ⟨canonicalTrajectory k, canonical_forward k, ?_, ?_⟩
      · intro t ht
        exact ⟨canonical_nonneg k t ht, mass_conservation k _ (canonical_forward k) t ht⟩
      · intro t ht
        have hs : pyramidLaw (canonicalTrajectory k) t ∈
            D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.openSimplex := by
          constructor
          · intro i
            fin_cases i <;> simp only [pyramidLaw, Matrix.cons_val_zero,
              Matrix.cons_val_succ, Matrix.cons_val_fin_one] <;> exact canonical_positive k t ht _
          · have hm := mass_conservation k _ (canonical_forward k) t ht.le
            simp [pyramidLaw, Fin.sum_univ_five] at *
            linarith
        exact ⟨hs,
          D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates.mixed_coordinates_global_chart.1
            _ hs⟩
    · exact equilibrium_properties k
  · intro p hp t ht
    obtain ⟨hr, hw, hD, hdet, hf⟩ := strict_for_every_forward_solution k p hp t ht
    obtain ⟨lam, c, hn, hsum, hmode, hrep, _⟩ := return_spectral_data k p hp
    refine ⟨hr, hw, hD, hdet, hf, ⟨lam, c, hn, hsum, hmode, hrep⟩,
      forward_limit k p hp, (observables_limit k p hp).1,
      (observables_limit k p hp).2, ?_⟩
    intro f
    have he := task_error_identity k p hp t ht f
    refine ⟨he, ?_⟩
    intro hJ
    rw [he]
    have hh : taskContrast f * (taskContrast f * association p t / activeMass p t) =
        (taskContrast f) ^ 2 * association p t / activeMass p t := by ring
    rw [hh]
    exact div_pos (mul_pos (sq_pos_of_ne_zero hJ) hD) hr

#print axioms five_state_strict_association

end D5.S3.StatisticalMechanics.SingleEntryFiveState
