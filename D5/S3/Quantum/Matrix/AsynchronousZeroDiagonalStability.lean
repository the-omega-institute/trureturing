/- GID: D5/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/AsynchronousZeroDiagonalStability
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Sharp real-history stability of the asynchronous three-block family. -/

import D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum

/-! Sharp stability of the literal asynchronous history operator. -/

noncomputable section
open Matrix Filter
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs (Vtx)
open D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
open scoped BigOperators Topology

namespace D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability

abbrev Coord := Vtx (fun _ : Fin 3 => 1)
abbrev History (K : ℕ) := Fin (K + 1) × Coord

def family (c d : ℝ) : Matrix Coord Coord ℝ :=
  fun i j => (!![0,1,1; c,0,0; -d,0,0] : Matrix (Fin 3) (Fin 3) ℝ) i.1 j.1

def fixedDelay : Fin 3 → Fin 3 → ℕ := !![0,1,2; 1,0,1; 2,1,0]

def bounded (K : ℕ) (δ : Fin 3 → Fin 3 → ℕ) : Prop :=
  (∀ i, δ i i = 0) ∧ ∀ i j, δ i j ≤ K

def remotePositive (K : ℕ) (δ : Fin 3 → Fin 3 → ℕ) : Prop :=
  bounded K δ ∧ ∀ i j, i ≠ j → 0 < δ i j

def stable (c d : ℝ) (K : ℕ) (δ : Fin 3 → Fin 3 → ℕ) : Prop :=
  ∀ y : History K → ℝ,
    Tendsto (fun t : ℕ => fun i : Coord =>
      ((asyncMatrix (family c d) δ K ^ t).mulVec y) (0, i)) atTop (𝓝 0)

private theorem weighted_power_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (q : ℝ)
    (hv : ∀ i, 0 < v i) (hq : 0 ≤ q)
    (hrow : ∀ i, ∑ j, |A i j| * v j ≤ q * v i)
    (y : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, ∀ i,
      |((A ^ t).mulVec y) i| ≤ C * q ^ t * v i := by
  let C : ℝ := ∑ j, |y j| / v j
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ =>
    div_nonneg (abs_nonneg _) (hv j).le
  have hy (i : ι) : |y i| ≤ C * v i := by
    apply (div_le_iff₀ (hv i)).mp
    exact Finset.single_le_sum
      (fun j _ => div_nonneg (abs_nonneg _) (hv j).le) (Finset.mem_univ i)
  refine ⟨C, hC, ?_⟩
  intro t
  induction t with
  | zero =>
      intro i
      simpa using hy i
  | succ t ih =>
      intro i
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      change |∑ j, A i j * ((A ^ t).mulVec y) j| ≤ _
      calc
        |∑ j, A i j * ((A ^ t).mulVec y) j|
            ≤ ∑ j, |A i j * ((A ^ t).mulVec y) j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |A i j| * |((A ^ t).mulVec y) j| := by
          simp_rw [abs_mul]
        _ ≤ ∑ j, |A i j| * (C * q ^ t * v j) := by
          exact Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _)
        _ = (C * q ^ t) * ∑ j, |A i j| * v j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ (C * q ^ t) * (q * v i) :=
          mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg hC (pow_nonneg hq _))
        _ = C * q ^ (t + 1) * v i := by rw [pow_succ]; ring

private theorem weighted_power_tendsto_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) (q : ℝ)
    (hv : ∀ i, 0 < v i) (hq : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, |A i j| * v j ≤ q * v i)
    (y : ι → ℝ) (i : ι) :
    Tendsto (fun t : ℕ => ((A ^ t).mulVec y) i) atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := weighted_power_bound A v q hv hq hrow y
  have hlim : Tendsto (fun t : ℕ => C * q ^ t * v i) atTop (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1)).mul tendsto_const_nhds :
        Tendsto (fun t : ℕ => C * q ^ t * v i) atTop (𝓝 (C * 0 * v i)))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun t => abs_nonneg _) (fun t => hbound t i) hlim


private theorem real_shift_row (M : Matrix Coord Coord ℝ)
    (δ : Fin 3 → Fin 3 → ℕ) (K : ℕ) (H : History K → ℝ)
    (r : Fin (K + 1)) (p : Coord) (hr : r.val ≠ 0) :
    ((asyncMatrix M δ K).mulVec H) (r,p) = H (⟨r.val-1, by omega⟩,p) := by
  have h := AsynchronousTwoBlockSpectrum.shift_row M δ K
    (fun s => (H s : ℂ)) r p hr
  have h' := congrArg Complex.re h
  simpa [Matrix.mulVec, dotProduct, Complex.re_sum] using h'

private theorem real_newest_row (M : Matrix Coord Coord ℝ)
    (δ : Fin 3 → Fin 3 → ℕ) (K : ℕ) (hδ : ∀ i j, δ i j ≤ K)
    (H : History K → ℝ) (p : Coord) :
    ((asyncMatrix M δ K).mulVec H) (0,p) =
      ∑ q : Coord, M p q * H (⟨δ q.1 p.1, by have := hδ q.1 p.1; omega⟩, q) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  let slot : Fin (K + 1) := ⟨δ q.1 p.1, by have := hδ q.1 p.1; omega⟩
  rw [Fintype.sum_eq_single slot]
  · simp [asyncMatrix, slot]
  · intro s hs
    have hv : s.val ≠ δ q.1 p.1 := by
      intro h
      apply hs
      exact Fin.ext h
    simp [asyncMatrix, hv]

private theorem fixedDelay_bounded {K : ℕ} (hK : 2 ≤ K) : bounded K fixedDelay := by
  constructor
  · intro i; fin_cases i <;> rfl
  · intro i j; fin_cases i <;> fin_cases j <;> simp [fixedDelay] <;> omega

private theorem fixedDelay_positive {K : ℕ} (hK : 2 ≤ K) : remotePositive K fixedDelay := by
  refine ⟨fixedDelay_bounded hK, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [fixedDelay]

private theorem exists_bad_radius (c d : ℝ) (hd : 0 ≤ d)
    (hs : 1 ≤ c + d) :
    ∃ r : ℝ, 1 ≤ r ∧ r ^ 6 = c * r ^ 2 + d ∧ (1 < c + d → 1 < r) := by
  let u : ℝ := c + d + 1
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hupper2 : c * u + d ≤ u ^ 2 := by
    have h := mul_nonneg hd (show 0 ≤ u - 1 by linarith)
    dsimp [u] at *
    nlinarith
  have hupper3 : u ^ 2 ≤ u ^ 3 := by
    have h := mul_nonneg (sq_nonneg u) (show 0 ≤ u - 1 by linarith)
    nlinarith
  let f : ℝ → ℝ := fun y => y ^ 3 - c * y - d
  have hf : ContinuousOn f (Set.Icc 1 u) := by fun_prop
  have hleft : f 1 ≤ 0 := by dsimp [f]; nlinarith
  have hright : 0 ≤ f u := by dsimp [f]; linarith
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc hu hf ⟨hleft, hright⟩
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have heq' : y ^ 3 = c * y + d := by dsimp [f] at heq; linarith
  have hsqrt := Real.sq_sqrt hy0
  have hr0 := Real.sqrt_nonneg y
  have hr1 : 1 ≤ Real.sqrt y := by nlinarith [hy.1]
  have hp : (Real.sqrt y) ^ 6 = c * (Real.sqrt y) ^ 2 + d := by
    calc
      (Real.sqrt y) ^ 6 = ((Real.sqrt y) ^ 2) ^ 3 := by ring
      _ = y ^ 3 := by rw [hsqrt]
      _ = c * y + d := heq'
      _ = c * (Real.sqrt y) ^ 2 + d := by rw [hsqrt]
  refine ⟨Real.sqrt y, hr1, hp, ?_⟩
  intro hstrict
  have hne : Real.sqrt y ≠ 1 := by
    intro he
    rw [he] at hp
    norm_num at hp
    linarith
  exact lt_of_le_of_ne hr1 (Ne.symm hne)

private def badPhase (r : ℝ) : ℂ := Complex.I * (r : ℂ)
private def badCurve (c d r : ℝ) (t : ℤ) : Fin 3 → ℝ :=
  ![(badPhase r ^ t).re,
    ((c : ℂ) * badPhase r ^ (t - 2)).re,
    (-(d : ℂ) * badPhase r ^ (t - 3)).re]

private theorem badPhase_ne_zero {r : ℝ} (hr : 1 ≤ r) : badPhase r ≠ 0 := by
  apply mul_ne_zero Complex.I_ne_zero
  exact_mod_cast (show r ≠ 0 by linarith)

private theorem badPhase_square (r : ℝ) : badPhase r ^ 2 = -((r : ℂ) ^ 2) := by
  simp [badPhase, mul_pow, Complex.I_sq]

private theorem badPhase_four (r : ℝ) : badPhase r ^ 4 = (r : ℂ) ^ 4 := by
  calc
    badPhase r ^ 4 = (badPhase r ^ 2) ^ 2 := by ring
    _ = (r : ℂ) ^ 4 := by rw [badPhase_square]; ring

private theorem badPhase_six {c d r : ℝ} (hr : r ^ 6 = c * r ^ 2 + d) :
    badPhase r ^ 6 = (c : ℂ) * badPhase r ^ 2 - (d : ℂ) := by
  have hrc : (r : ℂ) ^ 6 = (c : ℂ) * (r : ℂ) ^ 2 + (d : ℂ) := by exact_mod_cast hr
  calc
    badPhase r ^ 6 = (badPhase r ^ 2) ^ 3 := by ring
    _ = -((r : ℂ) ^ 6) := by rw [badPhase_square]; ring
    _ = (c : ℂ) * badPhase r ^ 2 - (d : ℂ) := by rw [hrc, badPhase_square]; ring

private theorem badCurve_recurrence {c d r : ℝ} (hr1 : 1 ≤ r)
    (hr : r ^ 6 = c * r ^ 2 + d) (t : ℤ) :
    badCurve c d r (t + 1) 0 = badCurve c d r (t - 1) 1 + badCurve c d r (t - 2) 2 ∧
    badCurve c d r (t + 1) 1 = c * badCurve c d r (t - 1) 0 ∧
    badCurve c d r (t + 1) 2 = -d * badCurve c d r (t - 2) 0 := by
  have hz := badPhase_ne_zero hr1
  have hexp (a b : ℤ) : badPhase r ^ (a + b) = badPhase r ^ a * badPhase r ^ b :=
    zpow_add₀ hz a b
  have hfirst : badPhase r ^ (t + 1) =
      (c : ℂ) * badPhase r ^ (t - 3) - (d : ℂ) * badPhase r ^ (t - 5) := by
    have h6 : badPhase r ^ (t + 1) = badPhase r ^ (t - 5) * badPhase r ^ (6 : ℕ) := by
      calc
        _ = badPhase r ^ ((t - 5) + (6 : ℤ)) := by congr 1; omega
        _ = _ := by rw [hexp]; simp
    have h2 : badPhase r ^ (t - 3) = badPhase r ^ (t - 5) * badPhase r ^ (2 : ℕ) := by
      calc
        _ = badPhase r ^ ((t - 5) + (2 : ℤ)) := by congr 1; omega
        _ = _ := by rw [hexp]; simp
    rw [h6, badPhase_six hr, h2]
    ring
  have hfirstRe := congrArg Complex.re hfirst
  have he1 : t - 1 - 2 = t - 3 := by omega
  have he2 : t - 2 - 3 = t - 5 := by omega
  have he3 : t + 1 - 2 = t - 1 := by omega
  have he4 : t + 1 - 3 = t - 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [badCurve, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      he1, he2]
    simpa [sub_eq_add_neg] using hfirstRe
  · simp [badCurve, he3, Complex.mul_re]
  · simp [badCurve, he4, Complex.mul_re]

private theorem badCurve_four_mul (c d r : ℝ) (m : ℕ) :
    badCurve c d r ((4 * m : ℕ) : ℤ) 0 = r ^ (4 * m) := by
  simp only [badCurve, Matrix.cons_val_zero, zpow_natCast]
  rw [pow_mul, badPhase_four, ← pow_mul]
  norm_cast

private theorem badCurve_zero (c d r : ℝ) : badCurve c d r 0 0 = 1 := by
  simp [badCurve]

private theorem badCurve_periodic (c d : ℝ) (t : ℤ) :
    badCurve c d 1 (t + 4) = badCurve c d 1 t := by
  have hz := badPhase_ne_zero (r := 1) (le_refl 1)
  have h4 : badPhase 1 ^ (4 : ℤ) = 1 := by
    simpa using badPhase_four 1
  have hp (s : ℤ) : badPhase 1 ^ (s + 4) = badPhase 1 ^ s := by
    rw [zpow_add₀ hz, h4, mul_one]
  have he2 : t + 4 - 2 = (t - 2) + 4 := by omega
  have he3 : t + 4 - 3 = (t - 3) + 4 := by omega
  funext i
  fin_cases i <;> simp [badCurve, he2, he3, hp]


private def badOrbit (c d r : ℝ) (K : ℕ) (t : ℤ) : History K → ℝ :=
  fun s => badCurve c d r (t - (s.1.val : ℤ)) s.2.1

private theorem badOrbit_step {c d r : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (hr1 : 1 ≤ r) (hr6 : r ^ 6 = c * r ^ 2 + d) (t : ℤ) :
    (asyncMatrix (family c d) fixedDelay K).mulVec (badOrbit c d r K t) =
      badOrbit c d r K (t + 1) := by
  classical
  funext s
  rcases s with ⟨slot, p⟩
  by_cases hs : slot.val = 0
  · have hslot : slot = 0 := Fin.ext hs
    subst slot
    rw [real_newest_row _ _ _ (fixedDelay_bounded hK).2]
    rcases p with ⟨i, j⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have ht := badCurve_recurrence hr1 hr6 t
    fin_cases i
    · simpa [family, fixedDelay, badOrbit, Fintype.sum_sigma,
        Fin.sum_univ_succ] using ht.1.symm
    · simpa [family, fixedDelay, badOrbit, Fintype.sum_sigma,
        Fin.sum_univ_succ] using ht.2.1.symm
    · simpa [family, fixedDelay, badOrbit, Fintype.sum_sigma,
        Fin.sum_univ_succ] using ht.2.2.symm
  · rw [real_shift_row _ _ _ _ _ _ hs]
    change badCurve c d r (t - ((slot.val - 1 : ℕ) : ℤ)) p.1 =
      badCurve c d r (t + 1 - (slot.val : ℤ)) p.1
    have ht : t - ((slot.val - 1 : ℕ) : ℤ) = t + 1 - (slot.val : ℤ) := by omega
    rw [ht]

private theorem badOrbit_power {c d r : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (hr1 : 1 ≤ r) (hr6 : r ^ 6 = c * r ^ 2 + d) (t : ℕ) :
    ((asyncMatrix (family c d) fixedDelay K) ^ t).mulVec (badOrbit c d r K 0) =
      badOrbit c d r K (t : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, badOrbit_step hK hr1 hr6]
      simp

private theorem badOrbit_periodic (c d : ℝ) (K : ℕ) (t : ℤ) :
    badOrbit c d 1 K (t + 4) = badOrbit c d 1 K t := by
  funext s
  change badCurve c d 1 (t + 4 - (s.1.val : ℤ)) s.2.1 = _
  have he : t + 4 - (s.1.val : ℤ) = (t - (s.1.val : ℤ)) + 4 := by omega
  rw [he, badCurve_periodic]
  rfl

private theorem badOrbit_initial_nonzero (c d r : ℝ) (K : ℕ) :
    badOrbit c d r K 0 (0, ⟨0,0⟩) = 1 := by
  simpa [badOrbit] using badCurve_zero c d r

private theorem badOrbit_power_four_mul {c d r : ℝ} {K : ℕ} (hK : 2 ≤ K)
    (hr1 : 1 ≤ r) (hr6 : r ^ 6 = c * r ^ 2 + d) (m : ℕ) :
    (((asyncMatrix (family c d) fixedDelay K) ^ (4 * m)).mulVec
      (badOrbit c d r K 0)) (0, ⟨0,0⟩) = r ^ (4 * m) := by
  rw [badOrbit_power hK hr1 hr6]
  simpa [badOrbit] using badCurve_four_mul c d r m

private theorem fixed_not_stable_of_bad_radius {c d r : ℝ} {K : ℕ}
    (hK : 2 ≤ K) (hr1 : 1 ≤ r) (hr6 : r ^ 6 = c * r ^ 2 + d) :
    ¬ stable c d K fixedDelay := by
  intro hstable
  have hcoord := (tendsto_pi_nhds.mp (hstable (badOrbit c d r K 0))) (⟨0,0⟩ : Coord)
  have hsub : Tendsto (fun m : ℕ => 4 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by dsimp; omega) tendsto_id
  have hlim : Tendsto (fun m : ℕ => r ^ (4 * m)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, badOrbit_power_four_mul hK hr1 hr6,
      Pi.zero_apply] using hcoord.comp hsub
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim (fun m => one_le_pow₀ hr1)
  norm_num at hbad

private theorem fixed_not_stable {c d : ℝ} {K : ℕ}
    (hd : 0 ≤ d) (hs : 1 ≤ c + d) (hK : 2 ≤ K) :
    ¬ stable c d K fixedDelay := by
  obtain ⟨r, hr1, hr6, _⟩ := exists_bad_radius c d hd hs
  exact fixed_not_stable_of_bad_radius hK hr1 hr6

private theorem choose_history_factor (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (K : ℕ) : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ q ≤ η ^ (K + 1) := by
  let N : ℝ := (K + 1 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
  let η : ℝ := 1 - (1 - q) / N
  have hfrac : 0 < (1 - q) / N := div_pos (by linarith) hN
  have hfrac1 : (1 - q) / N < 1 := (div_lt_one hN).mpr (by linarith)
  have hη : 0 < η := by dsimp [η]; linarith
  refine ⟨η, hη, by dsimp [η]; linarith, ?_⟩
  have hb := one_add_mul_sub_le_pow (show -1 ≤ η by linarith) (K + 1)
  have he : 1 + (K + 1 : ℕ) * (η - 1) = q := by
    change 1 + N * (η - 1) = q
    dsimp [η]
    field_simp [ne_of_gt hN]
    ring
  rwa [he] at hb

private theorem lift_weighted_rows {ℓ : ℕ} {n : Fin ℓ → ℕ}
    (M : Matrix (Vtx n) (Vtx n) ℝ) (δ : Fin ℓ → Fin ℓ → ℕ) (K : ℕ)
    (hδ : ∀ i j, δ i j ≤ K) (w : Vtx n → ℝ) (hw : ∀ i, 0 < w i)
    (q η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hqη : q ≤ η ^ (K + 1))
    (hrow : ∀ i, ∑ j, |M i j| * w j ≤ q * w i) :
    ∃ v : Fin (K + 1) × Vtx n → ℝ,
      (∀ rp, 0 < v rp) ∧
      ∀ rp, ∑ sq, |asyncMatrix M δ K rp sq| * v sq ≤ η * v rp := by
  classical
  let v : Fin (K + 1) × Vtx n → ℝ := fun rp => η ^ (K - rp.1.val) * w rp.2
  refine ⟨v, fun rp => mul_pos (pow_pos hη _) (hw rp.2), ?_⟩
  rintro ⟨r,i⟩
  by_cases hr : r.val = 0
  · have he : (∑ sq, |asyncMatrix M δ K (r,i) sq| * v sq) =
        ∑ j, |M i j| * (η ^ (K - δ j.1 i.1) * w j) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      let s : Fin (K + 1) := ⟨δ j.1 i.1, Nat.lt_succ_of_le (hδ _ _)⟩
      have hs (a : Fin (K + 1)) : a.val = δ j.1 i.1 ↔ a = s := by
        constructor
        · intro ha; apply Fin.ext; exact ha
        · intro ha; subst a; rfl
      simp [asyncMatrix, hr, hs, v, s, apply_ite abs, ite_mul]
    rw [he]
    calc
      (∑ j, |M i j| * (η ^ (K - δ j.1 i.1) * w j))
          ≤ ∑ j, |M i j| * w j := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact mul_le_of_le_one_left (hw j).le (pow_le_one₀ hη.le hη1)
      _ ≤ q * w i := hrow i
      _ ≤ η ^ (K + 1) * w i := mul_le_mul_of_nonneg_right hqη (hw i).le
      _ = η * v (r,i) := by simp [v, hr, pow_succ]; ring
  · let s : Fin (K + 1) := ⟨r.val - 1, by omega⟩
    have hs (a : Fin (K + 1)) : a.val + 1 = r.val ↔ a = s := by
      constructor
      · intro ha; apply Fin.ext; dsimp [s]; omega
      · intro ha; subst a; dsimp [s]; omega
    have he : (∑ sq, |asyncMatrix M δ K (r,i) sq| * v sq) = v (s,i) := by
      rw [Fintype.sum_prod_type]
      simp [asyncMatrix, hr, hs, apply_ite abs, ite_mul, ite_and]
    rw [he]
    have hexp : K - s.val = (K - r.val) + 1 := by
      dsimp [s]; have := r.isLt; omega
    change η ^ (K - s.val) * w i ≤ η * (η ^ (K - r.val) * w i)
    rw [hexp, pow_succ]
    exact le_of_eq (by ring)

private theorem family_positive_weights (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : c + d < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ w : Coord → ℝ,
      (∀ i, 0 < w i) ∧ ∀ i, ∑ j, |family c d i j| * w j ≤ q * w i := by
  let q := Real.sqrt ((1 + c + d) / 2)
  have hp : 0 < (1 + c + d) / 2 := by linarith
  have hq : 0 < q := Real.sqrt_pos.2 hp
  have hq2 : q ^ 2 = (1 + c + d) / 2 := Real.sq_sqrt hp.le
  have hq1 : q < 1 := by nlinarith
  let e := (q ^ 2 - c - d) / 4
  have he : 0 < e := by dsimp [e]; nlinarith
  let w : Coord → ℝ := fun i => (![1, (c + e) / q, (d + e) / q] : Fin 3 → ℝ) i.1
  refine ⟨q, hq, hq1, w, ?_, ?_⟩
  · rintro ⟨i,j⟩
    fin_cases i <;> dsimp [w]
    · norm_num
    · exact div_pos (by linarith) hq
    · exact div_pos (by linarith) hq
  · have hfirst : (c + e) / q + (d + e) / q ≤ q := by
      rw [← add_div, div_le_iff₀ hq]
      dsimp [e]
      nlinarith
    have hcq : q * ((c + e) / q) = c + e := by field_simp [ne_of_gt hq]
    have hdq : q * ((d + e) / q) = d + e := by field_simp [ne_of_gt hq]
    rintro ⟨i,j⟩
    fin_cases i
    · simpa [Fintype.sum_sigma, Fin.sum_univ_three, Fin.sum_univ_one,
        family, w] using hfirst
    · have h : c ≤ q * ((c + e) / q) := by rw [hcq]; linarith
      simpa [Fintype.sum_sigma, Fin.sum_univ_three, Fin.sum_univ_one,
        family, w, abs_of_nonneg hc] using h
    · have h : d ≤ q * ((d + e) / q) := by rw [hdq]; linarith
      simpa [Fintype.sum_sigma, Fin.sum_univ_three, Fin.sum_univ_one,
        family, w, abs_of_nonneg hd] using h

private theorem async_family_weights (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : c + d < 1) (K : ℕ) (δ : Fin 3 → Fin 3 → ℕ)
    (hδ : ∀ i j, δ i j ≤ K) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ v : History K → ℝ,
      (∀ rp, 0 < v rp) ∧
      ∀ rp, ∑ sq, |asyncMatrix (family c d) δ K rp sq| * v sq ≤ η * v rp := by
  obtain ⟨q,hq,hq1,w,hw,hrow⟩ := family_positive_weights c d hc hd hcd
  obtain ⟨η,hη,hη1,hqη⟩ := choose_history_factor q hq hq1 K
  exact ⟨η,hη,hη1,lift_weighted_rows (family c d) δ K hδ w hw q η hη hη1.le hqη hrow⟩

private theorem stable_of_sum_lt_one (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : c + d < 1) (K : ℕ) (δ : Fin 3 → Fin 3 → ℕ)
    (hδ : bounded K δ) : stable c d K δ := by
  obtain ⟨η,hη,hη1,v,hv,hrow⟩ := async_family_weights c d hc hd hcd K δ hδ.2
  intro y
  apply tendsto_pi_nhds.mpr
  intro i
  exact weighted_power_tendsto_zero _ v η hv hη.le hη1 hrow y (0,i)

theorem whole_theorem_three_one (lam c : ℝ) (hc : lam ^ 2 ≤ c) :
    let d := c - lam ^ 2
    let S := 2 * c - lam ^ 2
    (S < 1 ↔ ∀ K δ, bounded K δ → stable c d K δ) ∧
    (S < 1 ↔ stable c d 2 fixedDelay) ∧
    (∀ K, 2 ≤ K →
      (S < 1 ↔ ∀ δ, bounded K δ → stable c d K δ) ∧
      (S < 1 ↔ ∀ δ, remotePositive K δ → stable c d K δ)) ∧
    (S = 1 → ∀ K, 2 ≤ K → ∃ y : History K → ℝ,
      (∀ t : ℕ, (asyncMatrix (family c d) fixedDelay K ^ (t + 4)).mulVec y =
        (asyncMatrix (family c d) fixedDelay K ^ t).mulVec y) ∧
      (∀ m : ℕ, ((asyncMatrix (family c d) fixedDelay K ^ (4 * m)).mulVec y)
        (0, ⟨0, 0⟩) = 1)) ∧
    (1 < S → ∀ K, 2 ≤ K → ∃ r : ℝ, 1 < r ∧ ∃ y : History K → ℝ,
      ∀ m : ℕ, ((asyncMatrix (family c d) fixedDelay K ^ (4 * m)).mulVec y)
        (0, ⟨0, 0⟩) = r ^ (4 * m))
 := by
  dsimp only
  let d := c - lam ^ 2
  have hc0 : 0 ≤ c := le_trans (sq_nonneg lam) hc
  have hd0 : 0 ≤ d := sub_nonneg.mpr hc
  have hsum : c + d = 2 * c - lam ^ 2 := by dsimp [d]; ring
  have suff (hs : 2 * c - lam ^ 2 < 1) (K : ℕ) (δ) (hδ : bounded K δ) :
      stable c d K δ :=
    stable_of_sum_lt_one c d hc0 hd0 (by rwa [hsum]) K δ hδ
  have nec (K : ℕ) (hK : 2 ≤ K) (hs : stable c d K fixedDelay) :
      2 * c - lam ^ 2 < 1 := by
    by_contra hn
    exact fixed_not_stable hd0 (by rw [hsum]; exact le_of_not_gt hn) hK hs
  refine ⟨⟨suff, ?_⟩, ⟨?_, nec 2 le_rfl⟩, ?_, ?_, ?_⟩
  · intro h; exact nec 2 le_rfl (h 2 fixedDelay (fixedDelay_bounded le_rfl))
  · intro h; exact suff h 2 fixedDelay (fixedDelay_bounded le_rfl)
  · intro K hK
    exact ⟨⟨fun h δ hδ => suff h K δ hδ,
      fun h => nec K hK (h fixedDelay (fixedDelay_bounded hK))⟩,
      ⟨fun h δ hδ => suff h K δ hδ.1,
      fun h => nec K hK (h fixedDelay (fixedDelay_positive hK))⟩⟩
  · intro hs K hK
    have hr : (1 : ℝ) ^ 6 = c * 1 ^ 2 + d := by norm_num; linarith [hsum]
    refine ⟨badOrbit c d 1 K 0, ?_, ?_⟩
    · intro t
      rw [badOrbit_power hK (le_refl 1) hr, badOrbit_power hK (le_refl 1) hr]
      push_cast
      exact badOrbit_periodic c d K (t : ℤ)
    · intro m
      rw [badOrbit_power_four_mul hK (le_refl 1) hr]
      simp
  · intro hs K hK
    obtain ⟨r, hr1, hr6, hstrict⟩ := exists_bad_radius c d hd0
      (by rw [hsum]; exact hs.le)
    exact ⟨r, hstrict (by rwa [hsum]), badOrbit c d r K 0,
      badOrbit_power_four_mul hK hr1 hr6⟩

end D5.S3.Quantum.Matrix.AsynchronousZeroDiagonalStability
