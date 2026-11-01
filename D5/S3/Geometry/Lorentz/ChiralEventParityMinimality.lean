/- GID: D5/S3/Geometry/Lorentz/ChiralEventParityMinimality
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/ChiralEventParityMinimality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two continuous invariant parity-odd variables vanish on a chiral event. -/

import Mathlib.LinearAlgebra.Matrix.Permutation
import D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing
import D5.S3.Topology.BorsukUlam.PlanarOddMapZero

/-! The preregistered two-variable lower bound for chiral four-particle events. -/

set_option autoImplicit false

open scoped EuclideanSpace

noncomputable section

namespace D5.S3.Geometry.Lorentz.ChiralEventParityMinimality

abbrev event := Fin 4 → Fin 4 → ℝ

def eta : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

def rotation : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 0, -1, 0; 0, -1, 0, 0; 0, 0, 0, -1]

def minkowski (x y : Fin 4 → ℝ) : ℝ :=
  x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

def forwardCone : Set (Fin 4 → ℝ) := {x |
  0 ≤ x 0 ∧ x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 ≤ x 0 ^ 2}

def properOrthochronous : Set (Matrix (Fin 4) (Fin 4) ℝ) := {lam |
  lam.transpose * eta * lam = eta ∧ Matrix.det lam = 1 ∧ 0 < lam 0 0}

def parityVector (x : Fin 4 → ℝ) : Fin 4 → ℝ := ![x 0, -x 1, -x 2, -x 3]

def parity (x : event) : event := ![parityVector (x 0), parityVector (x 1),
  parityVector (x 2), parityVector (x 3)]

def act (lam : Matrix (Fin 4) (Fin 4) ℝ) (sigma tau : Equiv.Perm (Fin 2))
    (x : event) : event :=
  ![Matrix.mulVec lam (x (Fin.castAdd 2 (sigma 0))),
    Matrix.mulVec lam (x (Fin.castAdd 2 (sigma 1))),
    Matrix.mulVec lam (x (Fin.natAdd 2 (tau 0))),
    Matrix.mulVec lam (x (Fin.natAdd 2 (tau 1)))]

def chiral (x : event) : Prop :=
  ¬ ∃ lam ∈ properOrthochronous, ∃ sigma tau,
      act lam sigma tau x = parity x

def allEvents : Set event := {x | ∀ i, x i ∈ forwardCone}

def collisionEvents : Set event := {x |
  x ∈ allEvents ∧ minkowski (x 0) (x 0) * minkowski (x 1) (x 1) <
    minkowski (x 0) (x 1) ^ 2}

def admissible (om : Set event) (f : event → ℝ) : Prop :=
  ContinuousOn f om ∧
    (∀ x ∈ om, ∀ lam ∈ properOrthochronous, ∀ sigma tau,
      f (act lam sigma tau x) = f x) ∧
    (∀ x ∈ om, f (parity x) = -f x)

def claim : Prop :=
  ∀ om ∈ ({allEvents, collisionEvents} : Set (Set event)), ∀ f₁ f₂,
    admissible om f₁ → admissible om f₂ →
      ∃ x ∈ om, chiral x ∧ f₁ x = 0 ∧ f₂ x = 0

def family (v : EuclideanSpace ℝ (Fin 3)) : event :=
  let s := v 0
  let t := v 1
  let d := v 2
  let aa := Real.sqrt (4 + t)
  let bb := Real.sqrt (4 - t)
  ![![30, 0, 0, 1], ![20, 0, 0, -1],
    ![10 + s, aa, 0, d], ![10 - s, 0, bb, -d]]

private theorem family_mem_all
    (v : EuclideanSpace ℝ (Fin 3))
    (hv : v ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    family v ∈ allEvents := by
  have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
  have hsq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    simpa [hvnorm, Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq v).symm
  have hs : -1 ≤ v 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  have hsn : v 0 ≤ 1 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  have ht : -1 ≤ v 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  have htn : v 1 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  have h4t : 0 ≤ 4 + v 1 := by linarith
  have h4tn : 0 ≤ 4 - v 1 := by linarith
  have hsa : (Real.sqrt (4 + v 1)) ^ 2 = 4 + v 1 := Real.sq_sqrt h4t
  have hsb : (Real.sqrt (4 - v 1)) ^ 2 = 4 - v 1 := Real.sq_sqrt h4tn
  intro i
  fin_cases i
  · change 0 ≤ (30 : ℝ) ∧ 0 ^ 2 + 0 ^ 2 + 1 ^ 2 ≤ 30 ^ 2
    norm_num
  · change 0 ≤ (20 : ℝ) ∧ 0 ^ 2 + 0 ^ 2 + (-1 : ℝ) ^ 2 ≤ 20 ^ 2
    norm_num
  · constructor
    · change 0 ≤ 10 + v 0
      linarith
    · change (Real.sqrt (4 + v 1)) ^ 2 + 0 ^ 2 + v 2 ^ 2 ≤ (10 + v 0) ^ 2
      rw [hsa]
      nlinarith
  · constructor
    · change 0 ≤ 10 - v 0
      linarith
    · change 0 ^ 2 + (Real.sqrt (4 - v 1)) ^ 2 + (-v 2) ^ 2 ≤ (10 - v 0) ^ 2
      rw [hsb]
      nlinarith

private theorem family_mem_collision
    (v : EuclideanSpace ℝ (Fin 3))
    (hv : v ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    family v ∈ collisionEvents := by
  constructor
  · exact family_mem_all v hv
  · norm_num [family.eq_1, minkowski.eq_1]

private theorem family_continuous :
    ContinuousOn family
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  apply Continuous.continuousOn
  change Continuous (fun v : EuclideanSpace ℝ (Fin 3) =>
    ![![30, 0, 0, 1], ![20, 0, 0, -1],
      ![10 + v 0, Real.sqrt (4 + v 1), 0, v 2],
      ![10 - v 0, 0, Real.sqrt (4 - v 1), -v 2]])
  apply continuous_pi
  intro i
  fin_cases i <;>
    apply continuous_pi <;>
    intro j <;>
    fin_cases j <;>
    fun_prop

private theorem fixed_axes (h : Matrix (Fin 4) (Fin 4) ℝ)
    (hhL : h.transpose * eta * h = eta)
    (hp : h.mulVec ![30, 0, 0, 1] = ![30, 0, 0, 1])
    (hq : h.mulVec ![20, 0, 0, -1] = ![20, 0, 0, -1]) :
    h 0 0 = 1 ∧ h 0 1 = 0 ∧ h 0 2 = 0 ∧ h 0 3 = 0 ∧
    h 1 0 = 0 ∧ h 1 3 = 0 ∧ h 2 0 = 0 ∧ h 2 3 = 0 ∧
    h 3 0 = 0 ∧ h 3 1 = 0 ∧ h 3 2 = 0 ∧ h 3 3 = 1 := by
  have hp1 := congrFun hp 0
  have hp2 := congrFun hp 1
  have hp3 := congrFun hp 2
  have hp4 := congrFun hp 3
  have hq1 := congrFun hq 0
  have hq2 := congrFun hq 1
  have hq3 := congrFun hq 2
  have hq4 := congrFun hq 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hp1 hp2 hp3 hp4 hq1 hq2 hq3 hq4
  have h00 : h 0 0 = 1 := by nlinarith [hp1, hq1]
  have h03 : h 0 3 = 0 := by nlinarith [hp1, hq1]
  have h10 : h 1 0 = 0 := by nlinarith [hp2, hq2]
  have h13 : h 1 3 = 0 := by nlinarith [hp2, hq2]
  have h20 : h 2 0 = 0 := by nlinarith [hp3, hq3]
  have h23 : h 2 3 = 0 := by nlinarith [hp3, hq3]
  have h30 : h 3 0 = 0 := by nlinarith [hp4, hq4]
  have h33 : h 3 3 = 1 := by nlinarith [hp4, hq4]
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) hhL
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) hhL
  have h31 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 3 1) hhL
  have h32 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 3 2) hhL
  simp [Matrix.mul_apply, eta.eq_1, Fin.sum_univ_four, h00, h03, h10, h13, h20, h23,
    h30, h33] at h01 h02 h31 h32
  have h01 : h 0 1 = 0 := by nlinarith [h01]
  have h02 : h 0 2 = 0 := by nlinarith [h02]
  have h31 : h 3 1 = 0 := by nlinarith [h31]
  have h32 : h 3 2 = 0 := by nlinarith [h32]
  exact ⟨h00, h01, h02, h03, h10, h13, h20, h23, h30, h31, h32, h33⟩

private theorem lorentz_norm (h : Matrix (Fin 4) (Fin 4) ℝ)
    (hhL : h.transpose * eta * h = eta) (x : Fin 4 → ℝ) :
    minkowski (h.mulVec x) (h.mulVec x) = minkowski x x := by
  have hq := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ =>
      ∑ i : Fin 4, ∑ j : Fin 4, x i * M i j * x j) hhL
  simp [Matrix.mul_apply, Matrix.mulVec, minkowski.eq_1, eta.eq_1, dotProduct,
    Fin.sum_univ_four] at hq ⊢
  nlinarith

private theorem identity_stabilizer_contra
    (s d A B : ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (hdet : h.det = -1)
    (haxes : h 0 0 = 1 ∧ h 0 1 = 0 ∧ h 0 2 = 0 ∧ h 0 3 = 0 ∧
      h 1 0 = 0 ∧ h 1 3 = 0 ∧ h 2 0 = 0 ∧ h 2 3 = 0 ∧
      h 3 0 = 0 ∧ h 3 1 = 0 ∧ h 3 2 = 0 ∧ h 3 3 = 1)
    (ha : h.mulVec ![10 + s, A, 0, d] = ![10 + s, A, 0, d])
    (hb : h.mulVec ![10 - s, 0, B, -d] = ![10 - s, 0, B, -d])
    (hA : 0 < A) (hB : 0 < B) : False := by
  rcases haxes with ⟨h00, h01, h02, h03, h10, h13, h20, h23, h30, h31, h32, h33⟩
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have ha2 := congrFun ha 2
  have ha3 := congrFun ha 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h00, h03, h10, h13, h20,
    h23, h30, h33, h01, h02, h31, h32] at ha0 ha1 ha2 ha3
  have hb0 := congrFun hb 0
  have hb1 := congrFun hb 1
  have hb2 := congrFun hb 2
  have hb3 := congrFun hb 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h00, h03, h10, h13, h20,
    h23, h30, h33, h01, h02, h31, h32] at hb0 hb1 hb2 hb3
  have h11 : h 1 1 = 1 := by nlinarith [ha1]
  have h21 : h 2 1 = 0 := Or.resolve_right ha2 (ne_of_gt hA)
  have h12 : h 1 2 = 0 := Or.resolve_right hb1 (ne_of_gt hB)
  have h22eq : h 2 2 * B = 1 * B := by simpa using hb2
  have h22 : h 2 2 = 1 := mul_right_cancel₀ (ne_of_gt hB) h22eq
  have hid : h = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, h00, h01, h02, h03, h10, h11, h12, h13,
        h20, h21, h22, h23, h30, h31, h32, h33]
  rw [hid] at hdet
  norm_num at hdet

private theorem swap_stabilizer_contra
    (s t d A B : ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ)
    (hhL : h.transpose * eta * h = eta)
    (haxes : h 0 0 = 1 ∧ h 0 1 = 0 ∧ h 0 2 = 0 ∧ h 0 3 = 0 ∧
      h 1 0 = 0 ∧ h 1 3 = 0 ∧ h 2 0 = 0 ∧ h 2 3 = 0 ∧
      h 3 0 = 0 ∧ h 3 1 = 0 ∧ h 3 2 = 0 ∧ h 3 3 = 1)
    (ha : h.mulVec ![10 + s, A, 0, d] = ![10 - s, 0, B, -d])
    (hb : h.mulVec ![10 - s, 0, B, -d] = ![10 + s, A, 0, d])
    (hA : 0 < A) (hB : 0 < B)
    (hsq : s ^ 2 + t ^ 2 + d ^ 2 = 1)
    (hA2 : A ^ 2 = 4 + t) (hB2 : B ^ 2 = 4 - t) : False := by
  rcases haxes with ⟨h00, h01, h02, h03, h10, h13, h20, h23, h30, h31, h32, h33⟩
  have ha0 := congrFun ha 0
  have ha3 := congrFun ha 3
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h00, h03, h10, h13, h20,
    h23, h30, h33, h01, h02, h31, h32] at ha0 ha3
  have hs : s = 0 := by linarith [ha0]
  have hd : d = 0 := by linarith [ha3]
  have hnorm := lorentz_norm h hhL (![10 + s, A, 0, d] : Fin 4 → ℝ)
  rw [ha] at hnorm
  simp [minkowski.eq_1] at hnorm
  have hAB : A = B := by nlinarith [hnorm, hA, hB, hs, hd]
  nlinarith [hsq, hA2, hB2, hAB]

private theorem family_chiral
    (v : EuclideanSpace ℝ (Fin 3))
    (hv : v ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    chiral (family v) := by
  intro hbad
  rcases hbad with ⟨lam, hlam, sigma, tau, hact⟩
  rcases D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing.two_forms sigma with
    hsigma | hsigma
  · subst sigma
    have hp : lam.mulVec ![30, 0, 0, 1] = parityVector ![30, 0, 0, 1] := by
      simpa [act.eq_1, parity.eq_1, family.eq_1] using congrFun hact 0
    have hq : lam.mulVec ![20, 0, 0, -1] = parityVector ![20, 0, 0, -1] := by
      simpa [act.eq_1, parity.eq_1, family.eq_1] using congrFun hact 1
    let h := eta * lam
    have heta : eta * eta = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [eta.eq_1, Matrix.mul_apply, Fin.sum_univ_four]
    have hetaT : eta.transpose = eta := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [eta.eq_1]
    have hhL : h.transpose * eta * h = eta := by
      dsimp [h]
      have heta3 : eta * eta * eta = eta := by
        rw [mul_assoc, heta, mul_one]
      calc
        (eta * lam).transpose * eta * (eta * lam) =
            lam.transpose * eta.transpose * eta * (eta * lam) := by
              rw [Matrix.transpose_mul]
        _ = lam.transpose * (eta * eta * eta) * lam := by
              rw [hetaT]
              simp only [mul_assoc]
        _ = lam.transpose * eta * lam := by rw [heta3]
        _ = eta := hlam.1
    have hp' : h.mulVec ![30, 0, 0, 1] = ![30, 0, 0, 1] := by
      dsimp [h]
      rw [← Matrix.mulVec_mulVec, hp]
      ext i
      fin_cases i <;> simp [eta.eq_1, parityVector.eq_1, Matrix.mulVec,
        dotProduct, Fin.sum_univ_four]
    have hq' : h.mulVec ![20, 0, 0, -1] = ![20, 0, 0, -1] := by
      dsimp [h]
      rw [← Matrix.mulVec_mulVec, hq]
      ext i
      fin_cases i <;> simp [eta.eq_1, parityVector.eq_1, Matrix.mulVec,
        dotProduct, Fin.sum_univ_four]
    have hdet : h.det = -1 := by
      dsimp [h]
      rw [Matrix.det_mul]
      simp [eta.eq_1, Matrix.det_diagonal, Fin.prod_univ_four, hlam.2.1]
    have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
    have hsq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
      simpa [hvnorm, Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq v).symm
    have ht : -1 ≤ v 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2), hsq]
    have htn : v 1 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2), hsq]
    have hA : 0 < Real.sqrt (4 + v 1) := Real.sqrt_pos.2 (by linarith)
    have hB : 0 < Real.sqrt (4 - v 1) := Real.sqrt_pos.2 (by linarith)
    have hpar (x y : Fin 4 → ℝ) (hx : lam.mulVec x = parityVector y) :
        h.mulVec x = y := by
      dsimp [h]
      rw [← Matrix.mulVec_mulVec, hx]
      ext i
      fin_cases i <;> simp [eta.eq_1, parityVector.eq_1, Matrix.mulVec,
        dotProduct, Fin.sum_univ_four]
    have haxes := fixed_axes h hhL hp' hq'
    rcases D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing.two_forms tau with
      htau | htau
    · subst tau
      apply identity_stabilizer_contra (v 0) (v 2) (Real.sqrt (4 + v 1))
        (Real.sqrt (4 - v 1)) h hdet haxes
      · apply hpar
        have hx := congrFun hact 2
        simpa [act.eq_1, family.eq_1, parity.eq_1, parityVector.eq_1] using hx
      · apply hpar
        have hx := congrFun hact 3
        simpa [act.eq_1, family.eq_1, parity.eq_1, parityVector.eq_1] using hx
      · exact hA
      · exact hB
    · subst tau
      apply swap_stabilizer_contra (v 0) (v 1) (v 2)
        (Real.sqrt (4 + v 1)) (Real.sqrt (4 - v 1)) h hhL haxes
      · apply hpar
        have hx := congrFun hact 3
        simpa [act.eq_1, family.eq_1, parity.eq_1, parityVector.eq_1, Equiv.swap_apply_def] using hx
      · apply hpar
        have hx := congrFun hact 2
        simpa [act.eq_1, family.eq_1, parity.eq_1, parityVector.eq_1, Equiv.swap_apply_def] using hx
      · exact hA
      · exact hB
      · exact hsq
      · exact Real.sq_sqrt (by linarith)
      · exact Real.sq_sqrt (by linarith)
  · subst sigma
    have hpq : lam.mulVec ![20, 0, 0, -1] = parityVector ![30, 0, 0, 1] := by
      simpa [act.eq_1, parity.eq_1, family.eq_1, Equiv.swap_apply_def] using congrFun hact 0
    have hn := lorentz_norm lam hlam.1 (![20, 0, 0, -1] : Fin 4 → ℝ)
    rw [hpq] at hn
    norm_num [minkowski.eq_1, parityVector.eq_1] at hn

private theorem family_neg
    (v : EuclideanSpace ℝ (Fin 3)) :
    family (-v) =
      act rotation 1 (Equiv.swap 0 1)
        (parity (family v)) := by
  funext i
  fin_cases i <;>
    funext j <;>
      fin_cases j <;>
        simp [family.eq_1, act.eq_1, parity.eq_1, parityVector.eq_1, rotation.eq_1, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three] <;> ring_nf

private theorem family_admissible_zero
    (om : Set event) (hom : collisionEvents ⊆ om) (f₁ f₂ : event → ℝ)
    (hf₁ : admissible om f₁) (hf₂ : admissible om f₂) :
    ContinuousOn (fun v => (f₁ (family v) : ℂ) + (f₂ (family v) : ℂ) * Complex.I)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hmem : ∀ v ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      family v ∈ om := by
    intro v hv
    exact hom (family_mem_collision v hv)
  have h₁ : ContinuousOn (fun v => f₁ (family v))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    hf₁.1.comp family_continuous hmem
  have h₂ : ContinuousOn (fun v => f₂ (family v))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    hf₂.1.comp family_continuous hmem
  exact (Complex.continuous_ofReal.comp_continuousOn h₁).add
    ((Complex.continuous_ofReal.comp_continuousOn h₂).mul continuousOn_const)

private theorem parity_all_iff (x : event) :
    parity x ∈ allEvents ↔ x ∈ allEvents := by
  constructor <;> intro h
  · change ∀ i, parity x i ∈ forwardCone at h
    change ∀ i, x i ∈ forwardCone
    intro i
    have hi := h i
    fin_cases i <;>
      simpa [parity.eq_1, parityVector.eq_1, forwardCone.eq_1] using hi
  · change ∀ i, x i ∈ forwardCone at h
    change ∀ i, parity x i ∈ forwardCone
    intro i
    have hi := h i
    fin_cases i <;>
      simpa [parity.eq_1, parityVector.eq_1, forwardCone.eq_1] using hi

private theorem parity_collision_iff (x : event) :
    parity x ∈ collisionEvents ↔ x ∈ collisionEvents := by
  constructor <;> intro h
  · refine ⟨(parity_all_iff x).mp h.1, ?_⟩
    simpa [parity.eq_1, parityVector.eq_1, minkowski.eq_1] using h.2
  · refine ⟨(parity_all_iff x).mpr h.1, ?_⟩
    simpa [parity.eq_1, parityVector.eq_1, minkowski.eq_1] using h.2

private theorem rotation_proper : rotation ∈ properOrthochronous := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rotation.eq_1, eta.eq_1, Matrix.mul_apply, Fin.sum_univ_four]
  · let t : Equiv.Perm (Fin 4) := Equiv.swap 1 2
    have ht : t.permMatrix ℝ * eta = rotation := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [t, rotation.eq_1, eta.eq_1, Matrix.mul_apply, Fin.sum_univ_four,
          Equiv.swap_apply_def]
    rw [← ht, Matrix.det_mul, Matrix.det_permutation]
    have hsign : Equiv.Perm.sign t = -1 := by
      dsimp [t]
      exact Equiv.Perm.sign_swap (by decide)
    norm_num [hsign, eta.eq_1, Matrix.det_diagonal, Fin.prod_univ_four]
  · norm_num [rotation.eq_1]

private theorem family_admissible_odd
    (om : Set event) (hom : collisionEvents ⊆ om) (f : event → ℝ)
    (hf : admissible om f) :
    ∀ v ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      ((f (family (-v)) : ℂ)) = -((f (family v) : ℂ)) := by
  intro v hv
  have hmem : family v ∈ om := hom (family_mem_collision v hv)
  have hpmem : parity (family v) ∈ om := hom
    ((parity_collision_iff (family v)).mpr (family_mem_collision v hv))
  have hinv := hf.2.1 (parity (family v)) hpmem rotation rotation_proper
    (1 : Equiv.Perm (Fin 2)) (Equiv.swap 0 1)
  have hpar := hf.2.2 (family v) hmem
  rw [family_neg v] at ⊢
  rw [hinv, hpar]
  norm_num

private theorem route_claim
    (hcollision : ∀ v,
      v ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        family v ∈ collisionEvents)
    (hchir : ∀ v,
      v ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) → chiral (family v))
    (hcomplex : ∀ om, collisionEvents ⊆ om → ∀ f₁ f₂,
      admissible om f₁ → admissible om f₂ →
      ContinuousOn (fun v => (f₁ (family v) : ℂ) + (f₂ (family v) : ℂ) * Complex.I)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hodd : ∀ om, collisionEvents ⊆ om → ∀ f,
      admissible om f → ∀ v ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        ((f (family (-v)) : ℂ)) = -((f (family v) : ℂ))) :
    claim := by
  intro om hom f₁ f₂ hf₁ hf₂
  rcases (Set.mem_insert_iff.mp hom) with rfl | rfl
  · have hsub : collisionEvents ⊆ allEvents := by
      intro x hx
      exact hx.1
    have hz := D5.S3.Topology.BorsukUlam.PlanarOddMapZero.planar_odd_map_zero
      (fun v => (f₁ (family v) : ℂ) + (f₂ (family v) : ℂ) * Complex.I)
      (hcomplex allEvents hsub f₁ f₂ hf₁ hf₂)
      (by
        intro v hv
        have h₁ := hodd allEvents hsub f₁ hf₁ v hv
        have h₂ := hodd allEvents hsub f₂ hf₂ v hv
        rw [h₁, h₂]
        push_cast
        ring)
    obtain ⟨v, hv, hz⟩ := hz
    have hm : family v ∈ allEvents := hsub (hcollision v hv)
    refine ⟨family v, hm, hchir v hv, ?_, ?_⟩
    · have h := congrArg Complex.re hz
      simpa using h
    · have h := congrArg Complex.im hz
      simpa using h
  · have hsub : collisionEvents ⊆ collisionEvents := by
      intro x hx
      exact hx
    have hz := D5.S3.Topology.BorsukUlam.PlanarOddMapZero.planar_odd_map_zero
      (fun v => (f₁ (family v) : ℂ) + (f₂ (family v) : ℂ) * Complex.I)
      (hcomplex collisionEvents hsub f₁ f₂ hf₁ hf₂)
      (by
        intro v hv
        have h₁ := hodd collisionEvents hsub f₁ hf₁ v hv
        have h₂ := hodd collisionEvents hsub f₂ hf₂ v hv
        rw [h₁, h₂]
        push_cast
        ring)
    obtain ⟨v, hv, hz⟩ := hz
    have hm : family v ∈ collisionEvents := hcollision v hv
    refine ⟨family v, hm, hchir v hv, ?_, ?_⟩
    · have h := congrArg Complex.re hz
      simpa using h
    · have h := congrArg Complex.im hz
      simpa using h

theorem result : claim := by
  apply route_claim family_mem_collision family_chiral
  · intro om hom f₁ f₂ hf₁ hf₂
    exact family_admissible_zero om hom f₁ f₂ hf₁ hf₂
  · intro om hom f hf v hv
    exact family_admissible_odd om hom f hf v hv

end D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
