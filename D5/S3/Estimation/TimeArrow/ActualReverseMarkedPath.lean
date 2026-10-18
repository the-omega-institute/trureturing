/- GID: D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ActualReverseMarkedPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual transpose-kernel paths have a nilpotent transfer and signed relative Poisson bounds. -/

import D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
import D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient

open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
open D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra
open D5.S3.Estimation.TimeArrow.MarkedPoissonCoefficient
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.ActualReverseMarkedPath

/-- Uniform-start history mass for the actual transpose transition kernel. -/
def reverseProbability {M q s : ℕ} (r : ℝ) (e : Experiment)
    (S : Support M q) (o : Obs M s e) : ℝ :=
  match e with
  | .pair => ∏ t : Fin s, (2 * (M : ℝ))⁻¹ * transition r S (o t).2 (o t).1
  | .path => (2 * (M : ℝ))⁻¹ *
      ∏ t : Fin s, transition r S (o t.succ) (o t.castSucc)

/-- Count generating function on the same complete reverse history. -/
def reversePGF {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) (s : ℕ) (e : Experiment) : ℂ :=
  ∑ o : Obs M s e, (reverseProbability r e S o : ℂ) *
    ∏ j, zp j ^ count e o (m j) 1 * zm j ^ count e o (m j) (-1)

/-- The reverse mean drift uses the fair one-edge parity marginals. -/
def reverseA {M k : ℕ} (zp zm : Fin k → ℂ) : ℂ := (∑ j, tiltU zp zm j) / (2 * M)
/-- The reverse parity tilt average. -/
def reverseG {M k : ℕ} (zp zm : Fin k → ℂ) : ℂ := (∑ j, tiltV zp zm j) / (2 * M)
/-- Profile-weighted symmetric tilt. -/
def reverseD {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) : ℂ :=
  (∑ j, (b r S (.inl (m j)) : ℂ) * tiltU zp zm j) / (2 * M)
/-- Profile-weighted antisymmetric tilt. -/
def reverseE {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) : ℂ :=
  (∑ j, (b r S (.inl (m j)) : ℂ) * tiltV zp zm j) / (2 * M)
/-- The row-coordinate recurrence for the transpose-kernel transfer matrix. -/
def reverseState (A G D E : ℂ) : ℕ → Fin 3 → ℂ
  | 0 => ![1, 0, 0]
  | t + 1 =>
    let x := reverseState A G D E t
    ![(1 + A) * x 0 + A * x 1 + D * x 2,
      G * x 0 + G * x 1 + E * x 2,
      (A + G) * x 0 + (1 + A + G) * x 1 + (D + E) * x 2]

/-- The three-coordinate transfer, with its length-two nilpotent block at zero drift. -/
def reverseMatrix (A G D E : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 + A, G, A + G; A, G, 1 + A + G; D, E, D + E]

private theorem reverseState_eq_matrix (A G D E : ℂ) (t : ℕ) :
    ∀ i, reverseState A G D E t i = (reverseMatrix A G D E ^ t) 0 i := by
  induction t with
  | zero => intro i; fin_cases i <;> simp [reverseState]
  | succ t ih =>
    intro i
    rw [pow_succ, Matrix.mul_apply]
    simp only [Fin.sum_univ_three, ← ih]
    fin_cases i <;> simp [reverseState, reverseMatrix] <;> ring

private theorem reverse_transfer_envelope (A G D E : ℂ) (η : ℝ) (T : ℕ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 64)
    (hA : ‖A‖ ≤ η) (hG : ‖G‖ ≤ η) (hD : ‖D‖ ≤ η) (hE : ‖E‖ ≤ η)
    (hT : (T : ℝ) * η ^ 2 ≤ 1 / 256) :
    ‖reverseState A G D E T 0 - Complex.exp ((T : ℂ) * A)‖ ≤
      80 * (T : ℝ) * η ^ 2 * Real.exp ((T : ℝ) * A.re) := by
  let h : ℂ := Complex.exp A
  have hhne : h ≠ 0 := Complex.exp_ne_zero A
  have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr hhne
  have hhlower : 63 / 64 ≤ ‖h‖ := by
    rw [show ‖h‖ = Real.exp A.re by exact Complex.norm_exp A]
    have hreal : -η ≤ A.re := by
      have hh := Complex.abs_re_le_norm A
      rw [abs_le] at hh
      linarith
    linarith [Real.add_one_le_exp A.re]
  have hdefect : ‖(1 + A) - h‖ ≤ η ^ 2 := by
    have he := Complex.norm_exp_sub_one_sub_id_le (hA.trans (by linarith))
    have hi : (1 + A) - h = -(Complex.exp A - 1 - A) := by dsimp [h]; ring
    rw [hi, norm_neg]
    exact he.trans (by nlinarith [norm_nonneg A])
  let x (t : ℕ) : ℂ := reverseState A G D E t 0 / h ^ t
  let y (t : ℕ) : ℂ := reverseState A G D E t 1 / h ^ t
  let z (t : ℕ) : ℂ := reverseState A G D E t 2 / h ^ t
  let W (t : ℕ) : ℝ := 4 * ‖y t‖ + ‖z t‖
  let θ : ℝ := 40 * η ^ 2
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hx0 : x 0 = 1 := by simp [x, reverseState]
  have hW0 : W 0 = 0 := by simp [W, y, z, reverseState]
  have hWnonneg (t : ℕ) : 0 ≤ W t := by dsimp [W]; positivity
  have hxnext (t : ℕ) :
      x (t + 1) - x t = ((1 + A - h) * x t + A * y t + D * z t) / h := by
    dsimp [x, y, z]
    simp only [reverseState, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_succ]
    field_simp [hhne]
    ring
  have hynext (t : ℕ) : y (t + 1) = (G * x t + G * y t + E * z t) / h := by
    dsimp [x, y, z]
    simp only [reverseState, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_succ]
    field_simp [hhne]
  have hznext (t : ℕ) : z (t + 1) =
      ((A + G) * x t + (1 + A + G) * y t + (D + E) * z t) / h := by
    dsimp [x, y, z]
    simp only [reverseState, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_succ]
    field_simp [hhne]
  have hsumAG : ‖A + G‖ ≤ 2 * η := (norm_add_le A G).trans (by linarith)
  have hsumDE : ‖D + E‖ ≤ 2 * η := (norm_add_le D E).trans (by linarith)
  have hsum1AG : ‖1 + A + G‖ ≤ 1 + 2 * η := by
    have h := norm_add_le (1 + A) G
    have h' := norm_add_le (1 : ℂ) A
    norm_num only [norm_one] at h'
    linarith
  have hWstep (t : ℕ) : W (t + 1) ≤ W t / 2 + 8 * η * ‖x t‖ := by
    have hy : ‖y (t + 1)‖ ≤
        (η * ‖x t‖ + η * ‖y t‖ + η * ‖z t‖) / ‖h‖ := by
      rw [hynext, norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg h)
      calc
        ‖G * x t + G * y t + E * z t‖ ≤
          ‖G‖ * ‖x t‖ + ‖G‖ * ‖y t‖ + ‖E‖ * ‖z t‖ := by
            grw [norm_add_le, norm_add_le]; simp only [norm_mul]; exact le_rfl
        _ ≤ _ := by gcongr
    have hz : ‖z (t + 1)‖ ≤
        (2 * η * ‖x t‖ + (1 + 2 * η) * ‖y t‖ + 2 * η * ‖z t‖) / ‖h‖ := by
      rw [hznext, norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg h)
      calc
        ‖(A + G) * x t + (1 + A + G) * y t + (D + E) * z t‖ ≤
          ‖A + G‖ * ‖x t‖ + ‖1 + A + G‖ * ‖y t‖ + ‖D + E‖ * ‖z t‖ := by
            grw [norm_add_le, norm_add_le]; simp only [norm_mul]; exact le_rfl
        _ ≤ _ := by gcongr
    have hc : (6 * η * ‖x t‖ + (1 + 6 * η) * ‖y t‖ + 6 * η * ‖z t‖) / ‖h‖ ≤
        W t / 2 + 8 * η * ‖x t‖ := by
      apply (div_le_iff₀ hhpos).mpr
      have h1 : 6 * η ≤ 8 * η * ‖h‖ := by
        nlinarith [mul_nonneg hη (sub_nonneg.mpr hhlower)]
      have h2 : 1 + 6 * η ≤ 2 * ‖h‖ := by linarith
      have h3 : 6 * η ≤ ‖h‖ / 2 := by linarith
      have h1' := mul_le_mul_of_nonneg_right h1 (norm_nonneg (x t))
      have h2' := mul_le_mul_of_nonneg_right h2 (norm_nonneg (y t))
      have h3' := mul_le_mul_of_nonneg_right h3 (norm_nonneg (z t))
      dsimp only [W]
      nlinarith
    calc
      W (t + 1) ≤ 4 * ((η * ‖x t‖ + η * ‖y t‖ + η * ‖z t‖) / ‖h‖) +
          (2 * η * ‖x t‖ + (1 + 2 * η) * ‖y t‖ + 2 * η * ‖z t‖) / ‖h‖ := by
        dsimp only [W]; linarith
      _ = (6 * η * ‖x t‖ + (1 + 6 * η) * ‖y t‖ + 6 * η * ‖z t‖) / ‖h‖ := by ring
      _ ≤ _ := hc
  have hincrement (t : ℕ) :
      ‖x (t + 1) - x t‖ ≤ 2 * η ^ 2 * ‖x t‖ + 2 * η * W t := by
    rw [hxnext, norm_div]
    have hn : ‖(1 + A - h) * x t + A * y t + D * z t‖ ≤
        η ^ 2 * ‖x t‖ + η * ‖y t‖ + η * ‖z t‖ := by
      calc
        _ ≤ ‖1 + A - h‖ * ‖x t‖ + ‖A‖ * ‖y t‖ + ‖D‖ * ‖z t‖ := by
          grw [norm_add_le, norm_add_le]; simp only [norm_mul]; exact le_rfl
        _ ≤ _ := by gcongr
    apply (div_le_div_of_nonneg_right hn (norm_nonneg h)).trans
    apply (div_le_iff₀ hhpos).mpr
    have h1 : η ^ 2 ≤ 2 * η ^ 2 * ‖h‖ := by
      nlinarith [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hhlower)]
    have h2 : η ≤ 2 * η * ‖h‖ := by
      nlinarith [mul_nonneg hη (sub_nonneg.mpr hhlower)]
    have h1' := mul_le_mul_of_nonneg_right h1 (norm_nonneg (x t))
    have h2' := mul_le_mul_of_nonneg_right h2 (norm_nonneg (z t))
    have h3' := mul_le_mul_of_nonneg_right h2 (norm_nonneg (y t))
    dsimp only [W]
    nlinarith [mul_nonneg hη (norm_nonneg (y t))]
  have hgrowth (t : ℕ) : ‖x t‖ ≤ (1 + θ) ^ t ∧ W t ≤ 16 * η * (1 + θ) ^ t := by
    induction t with
    | zero =>
      constructor
      · simp [hx0]
      · simp only [hW0, pow_zero, mul_one]; positivity
    | succ t ih =>
      have hpow0 : 0 ≤ (1 + θ) ^ t := by positivity
      have hw := hWstep t
      have hi := hincrement t
      have he := norm_add_le (x t) (x (t + 1) - x t)
      rw [add_sub_cancel] at he
      have hηW := mul_le_mul_of_nonneg_left ih.2 (show 0 ≤ 2 * η by positivity)
      have hηX := mul_le_mul_of_nonneg_left ih.1 (show 0 ≤ 2 * η ^ 2 by positivity)
      constructor
      · rw [pow_succ]
        dsimp only [θ] at *
        nlinarith [mul_nonneg (sq_nonneg η) hpow0]
      · rw [pow_succ]
        have hh := mul_le_mul_of_nonneg_left ih.1 (show 0 ≤ 8 * η by positivity)
        have hprod : 0 ≤ 16 * η * θ * (1 + θ) ^ t := by positivity
        nlinarith
  have hxerror (t : ℕ) : ‖x t - 1‖ ≤ (1 + θ) ^ t - 1 := by
    induction t with
    | zero => simp [hx0]
    | succ t ih =>
      have he : x (t + 1) - 1 = (x t - 1) + (x (t + 1) - x t) := by ring
      rw [he]
      have hn := norm_add_le (x t - 1) (x (t + 1) - x t)
      have hi := hincrement t
      have hX := mul_le_mul_of_nonneg_left (hgrowth t).1 (show 0 ≤ 2 * η ^ 2 by positivity)
      have hW := mul_le_mul_of_nonneg_left (hgrowth t).2 (show 0 ≤ 2 * η by positivity)
      rw [pow_succ]
      dsimp only [θ] at *
      nlinarith [mul_nonneg (sq_nonneg η) (show 0 ≤ (1 + 40 * η ^ 2) ^ t by positivity)]
  have hpow : (1 + θ) ^ T ≤ Real.exp ((T : ℝ) * θ) := by
    calc
      (1 + θ) ^ T ≤ (Real.exp θ) ^ T := by gcongr; simpa only [add_comm] using Real.add_one_le_exp θ
      _ = Real.exp ((T : ℝ) * θ) := (Real.exp_nat_mul θ T).symm
  have htime : 0 ≤ (T : ℝ) * θ ∧ (T : ℝ) * θ ≤ 1 := by
    dsimp [θ]; constructor
    · positivity
    · nlinarith
  have hexperror : Real.exp ((T : ℝ) * θ) - 1 ≤ 2 * (T : ℝ) * θ := by
    have hh := Real.abs_exp_sub_one_le
      (x := (T : ℝ) * θ) (by rw [abs_of_nonneg htime.1]; exact htime.2)
    rw [abs_of_nonneg htime.1] at hh
    simpa only [mul_assoc] using (le_abs_self _).trans hh
  have herr : ‖x T - 1‖ ≤ 80 * (T : ℝ) * η ^ 2 := by
    have hh := (hxerror T).trans ((sub_le_sub_right hpow 1).trans hexperror)
    dsimp only [θ] at hh
    nlinarith
  have hpowexp : h ^ T = Complex.exp ((T : ℂ) * A) := by
    dsimp only [h]; exact (Complex.exp_nat_mul A T).symm
  have hid : reverseState A G D E T 0 - Complex.exp ((T : ℂ) * A) =
      h ^ T * (x T - 1) := by
    dsimp only [x]
    rw [← hpowexp]
    field_simp [hhne]
  rw [hid, norm_mul, hpowexp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  exact (mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le).trans_eq (by ring)

set_option maxHeartbeats 2000000 in
/-- Exact reverse history PGF, for every natural observation length and arbitrary complex tilts. -/
theorem actual_reverse_marked_path_pgf {M q s k : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin k → Fin M) (hm : Function.Injective m) (zp zm : Fin k → ℂ) :
    reversePGF r S m zp zm s .path =
      (reverseMatrix (reverseA (M := M) zp zm) (reverseG (M := M) zp zm)
        (reverseD r S m zp zm) (reverseE r S m zp zm) ^ s) 0 0 := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hN : (2 * (M : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hMc
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  let u := tiltU zp zm
  let v := tiltV zp zm
  let A := reverseA (M := M) zp zm
  let G := reverseG (M := M) zp zm
  let D := reverseD r S m zp zm
  let E := reverseE r S m zp zm
  let N : ℂ := 2 * M
  let U := sparse m u
  let W := sparse m v
  let K (x y : Vertex M) : ℂ :=
    (transition r S y x : ℂ) * (1 + U x + W x * (chi y : ℂ))
  have hmass (n : ℕ) (o : Obs M n .path) :
      (reverseProbability r .path S o : ℂ) *
        (∏ j, zp j ^ count .path o (m j) 1 * zm j ^ count .path o (m j) (-1)) =
      N⁻¹ * ∏ t : Fin n, K (o t.castSucc) (o t.succ) := by
    rw [count_monomial .path m zp zm o]
    simp_rw [edgeTilt_eq_affine m hm zp zm]
    change (reverseProbability r .path S o : ℂ) *
      (∏ t : Fin n, (1 + U (o t.castSucc) + W (o t.castSucc) * (chi (o t.succ) : ℂ))) = _
    simp only [reverseProbability, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_prod, Complex.ofReal_natCast, Complex.ofReal_ofNat, prod_mul_distrib, K, N]
    ring
  have hsumbr : ∑ x : Vertex M, b r S x = 0 := profile_sum_zero hq hqm hr hr1 hc1 S
  have hsumb : ∑ x : Vertex M, (b r S x : ℂ) = 0 := by exact_mod_cast hsumbr
  have hsumχ : ∑ x : Vertex M, (chi x : ℂ) = 0 := by simp [Fintype.sum_sum_type, chi]
  have hχb (x : Vertex M) : (chi x : ℂ) * (b r S x : ℂ) = (b r S x : ℂ) := by
    cases x <;> simp [chi, b]
  have hχsq (x : Vertex M) : (chi x : ℂ) * (chi x : ℂ) = 1 := by
    cases x <;> norm_num [chi]
  have hχU (x : Vertex M) : (chi x : ℂ) * U x = U x := by
    cases x <;> simp [chi, U, sparse]
  have hχW (x : Vertex M) : (chi x : ℂ) * W x = W x := by
    cases x <;> simp [chi, W, sparse]
  have hsumU : ∑ x, U x = N * A := by
    calc
      ∑ x, U x = ∑ j, u j := by simpa [U] using sparse_sum m (fun _ => 1) u
      _ = N * A := by dsimp [N, A, reverseA, u]; field_simp [hMc] <;> ring
  have hsumW : ∑ x, W x = N * G := by
    calc
      ∑ x, W x = ∑ j, v j := by simpa [W] using sparse_sum m (fun _ => 1) v
      _ = N * G := by dsimp [N, G, reverseG, v]; field_simp [hMc] <;> ring
  have hsumBU : ∑ x, (b r S x : ℂ) * U x = N * D := by
    calc
      ∑ x, (b r S x : ℂ) * U x = ∑ j, (b r S (.inl (m j)) : ℂ) * u j := by simpa [U] using sparse_sum m (fun x => (b r S x : ℂ)) u
      _ = N * D := by dsimp [N, D, reverseD, u]; field_simp [hMc] <;> ring
  have hsumBW : ∑ x, (b r S x : ℂ) * W x = N * E := by
    calc
      ∑ x, (b r S x : ℂ) * W x = ∑ j, (b r S (.inl (m j)) : ℂ) * v j := by simpa [W] using sparse_sum m (fun x => (b r S x : ℂ)) v
      _ = N * E := by dsimp [N, E, reverseE, v]; field_simp [hMc] <;> ring
  let f (x : Vertex M) : ℂ := 1 + U x
  let g (x : Vertex M) : ℂ := W x
  let j (x : Vertex M) : ℂ := (chi x : ℂ) + U x + W x
  have hf : ∑ x, f x = N * (1 + A) := by
    simp only [f, sum_add_distrib, hsumU, sum_const, card_univ,
      Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [N]; push_cast; ring
  have hχf : ∑ x, (chi x : ℂ) * f x = N * A := by
    simp only [f, mul_add, mul_one, hχU, sum_add_distrib, hsumχ, hsumU, zero_add]
  have hbf : ∑ x, (b r S x : ℂ) * f x = N * D := by
    simp only [f, mul_add, mul_one, sum_add_distrib, hsumb, hsumBU, zero_add]
  have hg : ∑ x, g x = N * G := hsumW
  have hχg : ∑ x, (chi x : ℂ) * g x = N * G := by simp only [g, hχW, hsumW]
  have hbg : ∑ x, (b r S x : ℂ) * g x = N * E := hsumBW
  have hj : ∑ x, j x = N * (A + G) := by
    simp only [j, sum_add_distrib, hsumχ, hsumU, hsumW]; ring
  have hχj : ∑ x, (chi x : ℂ) * j x = N * (1 + A + G) := by
    simp only [j, mul_add, hχsq, hχU, hχW, sum_add_distrib, hsumU, hsumW,
      sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [N]; push_cast; ring
  have hbj : ∑ x, (b r S x : ℂ) * j x = N * (D + E) := by
    have hcomm (x : Vertex M) : (b r S x : ℂ) * (chi x : ℂ) = (b r S x : ℂ) := by
      rw [mul_comm]; exact hχb x
    simp only [j, mul_add, hcomm, sum_add_distrib, hsumb, hsumBU, hsumBW]; ring
  have hK (x y : Vertex M) :
      K x y = (f x + g x * (chi y : ℂ) + j x * (b r S y : ℂ)) / N := by
    cases x <;> cases y <;>
      simp [K, transition, f, g, j, chi, b, U, W, sparse, N] <;>
      push_cast <;> field_simp [hMc] <;> ring
  let p (n : ℕ) (y : Vertex M) : ℂ := endpointWeight N⁻¹ K n y
  have hp0 (y : Vertex M) : p 0 y = N⁻¹ := endpoint_zero N⁻¹ K y
  have hpnext (n : ℕ) (y : Vertex M) : p (n + 1) y = ∑ x, p n x * K x y :=
    endpoint_next N⁻¹ K n y
  let R := reverseState A G D E
  have hpend (n : ℕ) (y : Vertex M) :
      p n y = (R n 0 + (chi y : ℂ) * R n 1 + (b r S y : ℂ) * R n 2) / N := by
    induction n generalizing y with
    | zero => simp [hp0, R, reverseState, div_eq_mul_inv]
    | succ n ih =>
      rw [hpnext]
      simp_rw [ih, hK]
      have hex (x : Vertex M) :
          ((R n 0 + (chi x : ℂ) * R n 1 + (b r S x : ℂ) * R n 2) / N) *
            ((f x + g x * (chi y : ℂ) + j x * (b r S y : ℂ)) / N) =
          ((R n 0 * f x + R n 1 * ((chi x : ℂ) * f x) + R n 2 * ((b r S x : ℂ) * f x)) +
            (R n 0 * g x + R n 1 * ((chi x : ℂ) * g x) + R n 2 * ((b r S x : ℂ) * g x)) * (chi y : ℂ) +
            (R n 0 * j x + R n 1 * ((chi x : ℂ) * j x) + R n 2 * ((b r S x : ℂ) * j x)) * (b r S y : ℂ)) / N ^ 2 := by ring
      simp_rw [hex]
      rw [← sum_div]
      simp only [sum_add_distrib, ← mul_sum, ← sum_mul, hf, hχf, hbf, hg, hχg, hbg, hj, hχj, hbj]
      simp only [R, reverseState, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp [hN, hMc] <;> ring
  have htotal (n : ℕ) : reversePGF r S m zp zm n .path = R n 0 := by
    have hjoin : reversePGF r S m zp zm n .path = ∑ y, p n y := by
      calc
        reversePGF r S m zp zm n .path = N⁻¹ *
            ∑ o : Fin (n + 1) → Vertex M, ∏ t : Fin n, K (o t.castSucc) (o t.succ) := by
          dsimp only [reversePGF]
          simp_rw [hmass]
          rw [mul_sum]
          congr 1
        _ = ∑ y, p n y := (endpoint_total N⁻¹ K n).symm
    rw [hjoin]
    simp_rw [hpend]
    rw [← sum_div]
    simp only [sum_add_distrib, ← sum_mul, hsumχ, hsumb, zero_mul, add_zero,
      sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [N]; push_cast; field_simp [hMc] <;> ring
  exact (htotal s).trans (reverseState_eq_matrix A G D E s 0)

/-- Independent adjacent pairs retain the actual transpose kernel before taking products. -/
theorem actual_reverse_marked_pair_pgf {M q s k : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin k → Fin M) (hm : Function.Injective m) (zp zm : Fin k → ℂ) :
    reversePGF r S m zp zm s .pair = (1 + reverseA (M := M) zp zm) ^ s := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let N : ℂ := 2 * M
  let U := sparse m (tiltU zp zm)
  let W := sparse m (tiltV zp zm)
  let K (p : Vertex M × Vertex M) : ℂ :=
    N⁻¹ * (transition r S p.2 p.1 : ℂ) *
      (1 + U p.1 + W p.1 * (chi p.2 : ℂ))
  have hmass (o : Obs M s .pair) :
      (reverseProbability r .pair S o : ℂ) *
        (∏ j, zp j ^ count .pair o (m j) 1 * zm j ^ count .pair o (m j) (-1)) =
      ∏ t : Fin s, K (o t) := by
    rw [count_monomial .pair m zp zm o]
    simp_rw [edgeTilt_eq_affine m hm zp zm]
    change (reverseProbability r .pair S o : ℂ) *
      (∏ t : Fin s, (1 + U (o t).1 + W (o t).1 * (chi (o t).2 : ℂ))) = _
    simp only [reverseProbability, Complex.ofReal_prod, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_ofNat, prod_mul_distrib, K, N]
  have hsumb : ∑ x : Vertex M, (b r S x : ℂ) = 0 := by
    exact_mod_cast profile_sum_zero hq hqm hr hr1 hc1 S
  have hsumχ : ∑ x : Vertex M, (chi x : ℂ) = 0 := by simp [Fintype.sum_sum_type, chi]
  have hχb (x : Vertex M) : (b r S x : ℂ) * (chi x : ℂ) = (b r S x : ℂ) := by
    cases x <;> simp [chi, b]
  have hrow (x : Vertex M) : ∑ y : Vertex M, K (x, y) = (1 + U x) / N := by
    have he (y : Vertex M) : K (x, y) =
        ((1 + U x) + W x * (chi y : ℂ) +
          (chi x : ℂ) * (1 + U x) * (b r S y : ℂ) +
          (chi x : ℂ) * W x * ((b r S y : ℂ) * (chi y : ℂ))) / N ^ 2 := by
      dsimp [K, transition, N]
      push_cast
      ring
    simp_rw [he, hχb]
    rw [← sum_div]
    simp only [sum_add_distrib, ← mul_sum, hsumb, hsumχ, mul_zero, add_zero,
      sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
    dsimp only [N]
    push_cast
    field_simp [hMc]
    ring
  have htotal : ∑ p : Vertex M × Vertex M, K p = 1 + reverseA (M := M) zp zm := by
    rw [Fintype.sum_prod_type]
    simp_rw [hrow]
    rw [← sum_div, sum_add_distrib]
    have hu : ∑ x : Vertex M, U x = ∑ j, tiltU zp zm j := by
      simpa [U] using sparse_sum m (fun _ => 1) (tiltU zp zm)
    rw [hu]
    simp only [sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, mul_one]
    dsimp [N, reverseA]
    push_cast
    field_simp [hMc]
    ring
  dsimp only [reversePGF]
  simp_rw [hmass]
  change (∑ o : Fin s → Vertex M × Vertex M, ∏ t, K (o t)) = _
  rw [← Fintype.prod_sum (fun (_ : Fin s) p => K p)]
  simp_rw [htotal]
  simp

/-- A dependence-sensitive signed envelope for the actual transpose-kernel history law. -/
theorem actual_reverse_marked_poisson_envelope {M q s k : ℕ} {r η : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin k → Fin M) (hm : Function.Injective m) (zp zm : Fin k → ℂ) (e : Experiment)
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 64)
    (hA : ‖reverseA (M := M) zp zm‖ ≤ η)
    (hG : ‖reverseG (M := M) zp zm‖ ≤ η)
    (hD : ‖reverseD r S m zp zm‖ ≤ η)
    (hE : ‖reverseE r S m zp zm‖ ≤ η)
    (hT : (s : ℝ) * η ^ 2 ≤ 1 / 256) :
    ‖reversePGF r S m zp zm s e - Complex.exp ((s : ℂ) * reverseA (M := M) zp zm)‖ ≤
      80 * (s : ℝ) * η ^ 2 * Real.exp ((s : ℝ) * (reverseA (M := M) zp zm).re) := by
  cases e with
  | path =>
    rw [actual_reverse_marked_path_pgf hq hqm hr hr1 hc1 S m hm zp zm]
    rw [← reverseState_eq_matrix]
    exact reverse_transfer_envelope _ _ _ _ η s hη hη1 hA hG hD hE hT
  | pair =>
    rw [actual_reverse_marked_pair_pgf hq hqm hr hr1 hc1 S m hm zp zm]
    have hy (t : ℕ) : reverseState (reverseA (M := M) zp zm) 0 0 0 t 1 = 0 := by
      cases t <;> simp [reverseState]
    have hx (t : ℕ) : reverseState (reverseA (M := M) zp zm) 0 0 0 t 0 =
        (1 + reverseA (M := M) zp zm) ^ t := by
      induction t with
      | zero => simp [reverseState]
      | succ t ih => simp [reverseState, ih, hy, pow_succ, mul_comm]
    rw [← hx s]
    exact reverse_transfer_envelope _ 0 0 0 η s hη hη1 hA
      (by simpa using hη) (by simpa using hη) (by simpa using hη) hT

set_option maxHeartbeats 2000000 in
/-- Relative transpose-kernel count masses in both experiments at exact mean s/(4M). -/
theorem actual_reverse_marked_count_relative (C₀ : ℝ) (hC : 1 ≤ C₀) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q s k : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r < 1 → compensation M q r < 1 →
        let L := (s : ℝ) / (2 * M)
        1 ≤ L → L / M ≤ η₀ → (k = 1 ∨ k = 2) →
        ∀ (S : Support M q) (m : Fin k → Fin M), Function.Injective m →
          ∀ (np nm : Fin k → ℕ),
            (∀ j, (np j : ℝ) ≤ C₀ * L ∧ (nm j : ℝ) ≤ C₀ * L) →
            ∀ e : Experiment,
            let P := ∑ o : Obs M s e,
              if ∀ j, count e o (m j) 1 = np j ∧ count e o (m j) (-1) = nm j
              then reverseProbability r e S o else 0
            let μ := L / 2
            let Q := ∏ j, (Real.exp (-μ) * μ ^ np j / (np j).factorial) *
              (Real.exp (-μ) * μ ^ nm j / (nm j).factorial)
            |P / Q - 1| ≤ A * L ^ (k + 1) / M := by
  classical
  let R : ℝ := 2 * (C₀ + 1)
  let D : ℝ := 2 * R + 1
  let Cs : ℝ := Real.exp 2 * (Real.sqrt (2 * Real.pi) + 1)
  let A : ℝ := 160 * D ^ 2 * Cs ^ 4 * (C₀ + 1) ^ 2
  let M₀ : ℕ := max 2 ⌈64 * D⌉₊
  let η₀ : ℝ := 1 / (512 * D ^ 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A, M₀, η₀, ?_, ?_, ?_, ?_⟩
  · dsimp [A, Cs]; positivity
  · dsimp [M₀]; omega
  · dsimp [η₀]; positivity
  intro M q s k r hMM hq hqm hr hr1 hc1 L hL hLη hk S m hm np nm hn e
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hb (j : Fin k) : ‖(b r S (.inl (m j)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    dsimp only [b]
    split_ifs
    · rw [abs_of_pos hr]; exact hr1.le
    · rw [abs_neg, abs_of_nonneg hc]; exact hc1.le
  let η : ℝ := D / M
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hMbound : 64 * D ≤ (M : ℝ) := by
    have hh : ⌈64 * D⌉₊ ≤ M := (le_max_right _ _).trans hMM
    exact (Nat.le_ceil _).trans (by exact_mod_cast hh)
  have hη1 : η ≤ 1 / 64 := by
    dsimp [η]; apply (div_le_iff₀ hM).mpr; linarith
  have hTη : (s : ℝ) * η ^ 2 ≤ 1 / 256 := by
    have hid : (s : ℝ) * η ^ 2 = 2 * D ^ 2 * (L / M) := by
      dsimp [L, η]; field_simp
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hLη (show 0 ≤ 2 * D ^ 2 by positivity)
    dsimp only [η₀] at hh
    have he : 2 * D ^ 2 * (1 / (512 * D ^ 2)) = (1 : ℝ) / 256 := by
      field_simp; ring
    rwa [he] at hh
  have hmean (zp zm : Fin k → ℂ) :
      (s : ℂ) * reverseA (M := M) zp zm =
        ∑ j, (((L / 2 : ℝ) : ℂ) * (zp j - 1) + ((L / 2 : ℝ) : ℂ) * (zm j - 1)) := by
    dsimp [reverseA, tiltU, L]
    push_cast
    rw [← mul_div_assoc, mul_sum, sum_div]
    apply sum_congr rfl
    intro j _
    field_simp [hMc] <;> ring
  have henvelope (zp zm : Fin k → ℂ) (hp : ∀ j, ‖zp j‖ ≤ R) (hm' : ∀ j, ‖zm j‖ ≤ R) :
      ‖reversePGF r S m zp zm s e - Complex.exp ((s : ℂ) * reverseA (M := M) zp zm)‖ ≤
        80 * (s : ℝ) * η ^ 2 * Real.exp ((s : ℝ) * (reverseA (M := M) zp zm).re) := by
    have huv := D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.tilt_norms zp zm R hp hm'
    have hu (j : Fin k) : ‖tiltU zp zm j‖ ≤ D := by
      have hh := (huv j).1
      change ‖tiltU zp zm j‖ ≤ R + 1 at hh
      dsimp only [D]; linarith
    have hv (j : Fin k) : ‖tiltV zp zm j‖ ≤ D := by
      have hh := (huv j).2
      change ‖tiltV zp zm j‖ ≤ R at hh
      dsimp only [D]; linarith
    have hbu (j : Fin k) : ‖(b r S (.inl (m j)) : ℂ) * tiltU zp zm j‖ ≤ D := by
      rw [norm_mul]
      exact (mul_le_mul (hb j) (hu j) (norm_nonneg _) (by norm_num)).trans_eq (one_mul D)
    have hbv (j : Fin k) : ‖(b r S (.inl (m j)) : ℂ) * tiltV zp zm j‖ ≤ D := by
      rw [norm_mul]
      exact (mul_le_mul (hb j) (hv j) (norm_nonneg _) (by norm_num)).trans_eq (one_mul D)
    have hsum (a : Fin k → ℂ) (ha : ∀ j, ‖a j‖ ≤ D) : ‖(∑ j, a j) / (2 * M : ℂ)‖ ≤ η := by
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, Complex.norm_natCast]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
      have hh := D5.S3.Estimation.TimeArrow.MarkedHistoryAlgebra.marked_sum_norm hk D hD.le a ha
      have he : η * (2 * M) = 2 * D := by dsimp [η]; field_simp
      rwa [he]
    exact actual_reverse_marked_poisson_envelope hq hqm hr hr1 hc1 S m hm zp zm e hη hη1
      (hsum _ hu) (hsum _ hv) (hsum _ hbu) (hsum _ hbv) hTη
  have hμ : 0 < L / 2 ∧ 1 * L / 2 ≤ L / 2 := by constructor <;> linarith
  have hh := finite_count_poisson_relative (1 : ℝ) C₀ L (80 * (s : ℝ) * η ^ 2)
    (by norm_num) hC hL (by positivity) hk
    (fun o : Obs M s e => reverseProbability r e S o)
    (fun o j => count e o (m j) 1) (fun o j => count e o (m j) (-1))
    (fun _ => L / 2) (fun _ => L / 2) (fun _ => hμ) (fun _ => hμ) np nm hn (by
      intro zp zm hp hm'
      have he := henvelope zp zm (by simpa [R] using hp) (by simpa [R] using hm')
      have hre := congrArg Complex.re (hmean zp zm)
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.re_sum, Complex.add_re, Complex.sub_re, Complex.one_re] at hre
      simpa only [reversePGF, hmean zp zm, hre] using he)
  apply hh.trans_eq
  have hs : (s : ℝ) = 2 * (M : ℝ) * L := by dsimp [L]; field_simp
  dsimp only [A, η, Cs]
  rw [hs, pow_succ]
  field_simp [hM.ne'] <;> ring

end D5.S3.Estimation.TimeArrow.ActualReverseMarkedPath
