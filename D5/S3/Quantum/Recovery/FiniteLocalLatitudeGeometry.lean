/- GID: D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual five latitude responses characterize all normalized flat products throughout the strict latitude interval. -/

import Mathlib
import D5.S3.Quantum.Information.ActualPureQubitGeometry
open Matrix
open scoped BigOperators
noncomputable section
namespace D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
set_option maxHeartbeats 2000000
set_option autoImplicit false
def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
def source (r : ℝ) : Fin 5 → Fin 2 → ℂ :=
  ![![1,0], ![0,1], ![1/(Real.sqrt (1+r^2):ℂ), (r:ℂ)/(Real.sqrt (1+r^2):ℂ)],
    ![1/(Real.sqrt (1+r^2):ℂ), (r:ℂ)*omega/(Real.sqrt (1+r^2):ℂ)],
    ![1/(Real.sqrt (1+r^2):ℂ), (r:ℂ)*omega^2/(Real.sqrt (1+r^2):ℂ)]]
def record (r : ℝ) (i : Fin 5) (p : Fin 2 × Fin 2) : ℂ :=
  source r i p.1 * source r i p.2
def symmetric (b : Fin 3 → ℂ) (p : Fin 2 × Fin 2) : ℂ :=
  (!![b 0, b 1/(Real.sqrt 2:ℂ); b 1/(Real.sqrt 2:ℂ), b 2]) p.1 p.2
def response (r : ℝ) (b : Fin 3 → ℂ) (i : Fin 5) : ℝ :=
  Complex.normSq (∑ p, star (symmetric b p) * record r i p)
def productVector (x y : Fin 2 → ℂ) (p : Fin 2 × Fin 2) : ℂ := x p.1*y p.2
def ketResponse (r : ℝ) (v : Fin 2 × Fin 2 → ℂ) (i : Fin 5) : ℝ :=
  Complex.normSq (∑ p, star (v p)*record r i p)
def productResponse (r : ℝ) (x y : Fin 2 → ℂ) (i : Fin 5) : ℝ :=
  ketResponse r (productVector x y) i
def UnitSpinor (x : Fin 2 → ℂ) : Prop := ∑ k, Complex.normSq (x k) = 1
def FlatProduct (r : ℝ) (x y : Fin 2 → ℂ) : Prop :=
  ∀ i, productResponse r x y i = productResponse r x y 0
def spinorZ (x : Fin 2 → ℂ) : ℝ := Complex.normSq (x 0)-Complex.normSq (x 1)
def antisymmetricWeight (x y : Fin 2 → ℂ) : ℝ :=
  Complex.normSq ((x 0*y 1-x 1*y 0)/(Real.sqrt 2:ℂ))
def Flat (r : ℝ) (b : Fin 3 → ℂ) : Prop := ∀ i, response r b i = response r b 0
def Normalized (b : Fin 3 → ℂ) : Prop := ∑ k, Complex.normSq (b k) = 1
def kappa (r : ℝ) : ℝ := Real.sqrt (4+2*(r^2+(r^2)⁻¹))/3
def h (r : ℝ) : ℝ := 1/(3*(1+kappa r))
def g (r : ℝ) : ℝ := kappa r/(1+kappa r)
abbrev Bloch := EuclideanSpace ℝ (Fin 3)
def rho (a : Bloch) : Matrix (Fin 2) (Fin 2) ℂ :=
  D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix 1 a
def Q (a b : Bloch) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (rho a) (rho b)
def matrixResponse (r : ℝ) (a b : Bloch) (i : Fin 5) : ℝ :=
  (star (record r i) ⬝ᵥ ((Q a b) *ᵥ record r i)).re
def K_s (r : ℝ) : Set (Bloch × Bloch) :=
  {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ ∀ i,matrixResponse r p.1 p.2 i = h r}
def defect (a b : Bloch) : ℝ := (1-inner ℝ a b)/4

/-- For every strict-interior latitude, normalized symmetric flat vectors exist and
have universal concurrence. Every unit flat product has the fixed source response,
antisymmetric weight and polar height; the actual Bloch terminal set is nonempty.
This statement concerns geometry and contains no protocol or Bellman bound. -/
theorem all_r_flat_geometry (r : ℝ) (hr : 0 < r) (hlo : 1/2 < r^2) (hhi : r^2 < 2) :
    ((∃ b : Fin 3 → ℂ, Normalized b ∧ Flat r b) ∧
    (∀ b : Fin 3 → ℂ, Normalized b → Flat r b →
      (∀ i, response r b i = 1/3) ∧
      (∀ k, Complex.normSq (b k) = 1/3) ∧
      ‖b 1^2 - 2*b 0*b 2‖ = kappa r)) ∧
    (∃ x y : Fin 2 → ℂ, UnitSpinor x ∧ UnitSpinor y ∧ ∀ i, productResponse r x y i = h r) ∧
    (∀ x y : Fin 2 → ℂ, UnitSpinor x → UnitSpinor y → FlatProduct r x y →
      (∀ i, productResponse r x y i = h r) ∧ antisymmetricWeight x y = g r ∧
      spinorZ x = -spinorZ y ∧ (spinorZ x)^2 = 1-4*h r) ∧
    (K_s r).Nonempty ∧
    (∀ a b : Bloch, (a,b) ∈ K_s r →
      a 2 = -b 2 ∧ (a 2)^2 = 1-4*h r ∧ defect a b = g r) := by
  classical
  have sym : (∃ b : Fin 3 → ℂ, Normalized b ∧ Flat r b) ∧
    (∀ b : Fin 3 → ℂ, Normalized b → Flat r b →
      (∀ i, response r b i = 1/3) ∧
      (∀ k, Complex.normSq (b k) = 1/3) ∧
      ‖b 1^2 - 2*b 0*b 2‖ = kappa r) := by
    have fourier {A B C : ℂ} {c : ℝ} :
        (∀ j : Fin 3, Complex.normSq (A + B * omega ^ j.val + C * omega ^ (2*j.val)) = c) ↔
        Complex.normSq A + Complex.normSq B + Complex.normSq C = c ∧
          B * star A + C * star B + A * star C = 0 := by
      let w := omega
      have hp : IsPrimitiveRoot w 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)
      have h3 : w ^ 3 = 1 := hp.pow_eq_one
      have hw2 : w ^ 2 = -(w + 1) := by
        have h := hp.geom_sum_eq_zero (by norm_num : 1 < 3)
        norm_num [Finset.sum_range_succ] at h
        linear_combination h
      have h4 : w ^ 4 = w := by calc
        _ = w ^ 3 * w := by ring
        _ = w := by rw [h3, one_mul]
      have h5 : w ^ 5 = w ^ 2 := by calc
        _ = w ^ 3 * w ^ 2 := by ring
        _ = w ^ 2 := by rw [h3, one_mul]
      have h6 : w ^ 6 = 1 := by calc
        _ = (w ^ 3) ^ 2 := by ring
        _ = 1 := by rw [h3]; norm_num
      have hn : w ≠ 0 := by intro hz; simp [hz] at h3
      have hw : star w = w ^ 2 := by
        apply mul_right_cancel₀ hn
        calc
          star w * w = 1 := by
            change (starRingEnd ℂ) w * w = 1
            rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
              hp.norm'_eq_one (by norm_num)]
            norm_num
          _ = w ^ 2 * w := by linear_combination -h3
      let D : ℂ := (Complex.normSq A + Complex.normSq B + Complex.normSq C : ℝ)
      let L := B * star A + C * star B + A * star C
      have p0 : (Complex.normSq (A + B + C) : ℂ) = D + L + star L := by
        simp only [D, L, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self,
          ← Complex.star_def, star_add, star_mul, star_star]
        ring
      have p1 : (Complex.normSq (A + B*w + C*w^2) : ℂ) = D + L*w + star L*w^2 := by
        simp only [D, L, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self,
          ← Complex.star_def, star_add, star_mul, star_pow, star_star, hw]
        ring_nf
        simp only [h3, h4, h5, h6, hw2]
        ring
      have p2 : (Complex.normSq (A + B*w^2 + C*w) : ℂ) = D + L*w^2 + star L*w := by
        simp only [D, L, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self,
          ← Complex.star_def, star_add, star_mul, star_pow, star_star, hw]
        ring_nf
        simp only [h3, h4, h5, h6, hw2]
        ring
      constructor
      · intro flat
        have q0 := congrArg (fun x : ℝ => (x : ℂ)) (flat 0)
        have q1 := congrArg (fun x : ℝ => (x : ℂ)) (flat 1)
        have q2 := congrArg (fun x : ℝ => (x : ℂ)) (flat 2)
        change (Complex.normSq (A+B*w^0+C*w^0) : ℂ) = c at q0
        change (Complex.normSq (A+B*w^1+C*w^2) : ℂ) = c at q1
        change (Complex.normSq (A+B*w^2+C*w^4) : ℂ) = c at q2
        simp only [pow_zero, mul_one, p0] at q0
        rw [pow_one, p1, hw2] at q1
        rw [h4, p2, hw2] at q2
        have dc : D = c := by linear_combination (q0+q1+q2)/3
        have ls : star L = -L := by linear_combination q0-dc
        have mult : L * (2*w+1) = 0 := by
          rw [ls] at q1
          linear_combination q1-dc
        have nw : 2*w+1 ≠ 0 := by
          intro hz
          have wz : w = -(1/2:ℂ) := by linear_combination hz/2
          rw [wz] at hw2
          norm_num at hw2
        exact ⟨Complex.ofReal_injective dc, (mul_eq_zero.mp mult).resolve_right nw⟩
      · rintro ⟨dc, lc⟩ j
        have dc' : D = c := congrArg (fun x : ℝ => (x : ℂ)) dc
        change L = 0 at lc
        apply Complex.ofReal_injective
        change (Complex.normSq (A+B*w^j.val+C*w^(2*j.val)) : ℂ) = c
        fin_cases j
        · simpa only [Nat.mul_zero, pow_zero, mul_one, lc, star_zero, add_zero, dc'] using p0
        · simpa only [pow_one, lc, star_zero, zero_mul, add_zero, dc'] using p1
        · simpa only [h4, lc, star_zero, zero_mul, add_zero, dc'] using p2
    have sr : (Real.sqrt 2 : ℂ)^2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have sr0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)))
    have sp : (Real.sqrt (1+r^2) : ℂ)^2 = (1+r^2:ℝ) := by
      exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 1+r^2)
    have sp0 : (Real.sqrt (1+r^2) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 1+r^2)))
    have den0 : (1+(r:ℂ)^2) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by positivity : (0:ℝ) < 1+r^2))
    push_cast at sp
    have polar (b : Fin 3 → ℂ) : response r b 0 = Complex.normSq (b 0) ∧
        response r b 1 = Complex.normSq (b 2) := by
      simp [response, record, source, symmetric, Fintype.sum_prod_type, Fin.sum_univ_two,
        Complex.star_def, Complex.normSq_conj]
    have latitude (b : Fin 3 → ℂ) (j : Fin 3) :
        response r b ⟨2+j.val, by omega⟩ =
        Complex.normSq (star (b 0) + (Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)*omega^j.val +
          (r:ℂ)^2*star (b 2)*omega^(2*j.val))/(1+r^2)^2 := by
      have amp : (∑ p, star (symmetric b p) * record r ⟨2+j.val, by omega⟩ p) =
          (star (b 0) + (Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)*omega^j.val +
          (r:ℂ)^2*star (b 2)*omega^(2*j.val))/(1+r^2:ℝ) := by
        fin_cases j <;>
          simp [record, source, symmetric, Fintype.sum_prod_type, Fin.sum_univ_two,
            star_div₀, Complex.star_def] <;>
          field_simp [sp0, sr0, den0] <;>
          ring_nf <;> simp only [sr, sp] <;> ring
      unfold response
      rw [amp, Complex.normSq_div]
      simp only [Complex.normSq_ofReal, pow_two]
    have norm_formula (b : Fin 3 → ℂ) :
        Complex.normSq (star (b 0)) +
          Complex.normSq ((Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)) +
          Complex.normSq ((r:ℂ)^2*star (b 2)) =
        Complex.normSq (b 0)+2*r^2*Complex.normSq (b 1)+r^4*Complex.normSq (b 2) := by
      simp [Complex.normSq_mul, map_pow, Complex.star_def,
        Complex.normSq_conj, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    have universal (b : Fin 3 → ℂ) (hn : Normalized b) (hf : Flat r b) :
        (∀ i, response r b i = 1/3) ∧
        (∀ k, Complex.normSq (b k) = 1/3) ∧
        ‖b 1^2 - 2*b 0*b 2‖ = kappa r := by
      have b02 : Complex.normSq (b 2) = Complex.normSq (b 0) := by
        have h := hf 1
        rw [(polar b).1, (polar b).2] at h
        exact h
      have flats : ∀ j : Fin 3,
          Complex.normSq (star (b 0)+(Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)*omega^j.val +
            (r:ℂ)^2*star (b 2)*omega^(2*j.val)) = Complex.normSq (b 0)*(1+r^2)^2 := by
        intro j
        have h := hf ⟨2+j.val, by omega⟩
        rw [latitude b j, (polar b).1] at h
        exact (div_eq_iff (by positivity : (1+r^2)^2 ≠ 0)).mp h
      obtain ⟨hnorm, hfour⟩ := fourier.mp flats
      rw [norm_formula b, b02] at hnorm
      have b10 : Complex.normSq (b 1) = Complex.normSq (b 0) := by
        nlinarith [sq_pos_of_pos hr]
      have b0 : Complex.normSq (b 0) = 1/3 := by
        unfold Normalized at hn
        simp only [Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.cons_zero,
          Fin.cons_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
          add_zero] at hn
        rw [b10, b02] at hn
        linarith
      have coords : ∀ k, Complex.normSq (b k) = 1/3 := by
        intro k
        fin_cases k
        · exact b0
        · exact b10.trans b0
        · exact b02.trans b0
      have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      have F : (Real.sqrt 2:ℂ)*(star (b 1)*b 0+(r:ℂ)^2*star (b 2)*b 1)+
          (r:ℂ)*star (b 0)*b 2 = 0 := by
        apply mul_left_cancel₀ hr0
        calc
          (r:ℂ)*_ = (Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)*star (star (b 0)) +
              (r:ℂ)^2*star (b 2)*star ((Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)) +
              star (b 0)*star ((r:ℂ)^2*star (b 2)) := by
            simp only [star_mul, star_pow, star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
            ring
          _ = 0 := hfour
          _ = (r:ℂ)*0 := (mul_zero _).symm
      have normF : 2 * Complex.normSq (star (b 1)*b 0+(r:ℂ)^2*star (b 2)*b 1) =
          r^2*Complex.normSq (b 0)*Complex.normSq (b 2) := by
        have eq : (Real.sqrt 2:ℂ)*(star (b 1)*b 0+(r:ℂ)^2*star (b 2)*b 1) =
            -(r:ℂ)*star (b 0)*b 2 := by linear_combination F
        have h := congrArg Complex.normSq eq
        simp only [map_mul, Complex.normSq_neg, Complex.normSq_ofReal, Complex.star_def,
          Complex.normSq_conj] at h
        rw [show Real.sqrt 2*Real.sqrt 2 = 2 by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]] at h
        simpa only [Complex.star_def, pow_two] using h
      have expand : Complex.normSq (star (b 1)*b 0+(r:ℂ)^2*star (b 2)*b 1) =
          Complex.normSq (b 1)*Complex.normSq (b 0) +
          r^4*Complex.normSq (b 2)*Complex.normSq (b 1) +
          2*r^2*(b 1^2*star (b 0*b 2)).re := by
        simp [Complex.normSq_apply, Complex.star_def, pow_two]
        ring
      have det : Complex.normSq (b 1^2-2*b 0*b 2) =
          Complex.normSq (b 1)^2+4*Complex.normSq (b 0)*Complex.normSq (b 2) -
          4*(b 1^2*star (b 0*b 2)).re := by
        simp [Complex.normSq_apply, Complex.star_def, pow_two]
        ring
      rw [expand, coords 0, coords 1, coords 2] at normF
      rw [coords 0, coords 1, coords 2] at det
      have norms : Complex.normSq (b 1^2-2*b 0*b 2) = (4+2*(r^2+(r^2)⁻¹))/9 := by
        have rt0 : r^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hr)
        field_simp [rt0]
        nlinarith [normF, det]
      refine ⟨fun i => (hf i).trans ((polar b).1.trans b0), coords, ?_⟩
      rw [Complex.normSq_eq_norm_sq] at norms
      have ks : (kappa r)^2 = (4+2*(r^2+(r^2)⁻¹))/9 := by
        unfold kappa
        rw [div_pow, Real.sq_sqrt (by positivity)]
        norm_num
      have kp : 0 ≤ kappa r := by unfold kappa; positivity
      nlinarith [norm_nonneg (b 1^2-2*b 0*b 2)]
    let t := r^2
    have ht : 0 < t := sq_pos_of_pos hr
    have ti : t*t⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ht)
    let c : ℝ := 1/4-(t+t⁻¹)/2
    have tsumlo : 2 ≤ t+t⁻¹ := by
      apply (mul_le_mul_iff_right₀ ht).mp
      nlinarith [sq_nonneg (t-1)]
    have tsumhi : t+t⁻¹ < 5/2 := by
      apply (mul_lt_mul_iff_right₀ ht).mp
      have mulpos : 0 < (t-1/2)*(2-t) := mul_pos (by exact sub_pos.mpr hlo)
        (by exact sub_pos.mpr hhi)
      nlinarith
    have cl : -1 < c := by dsimp [c]; linarith
    have cu : c ≤ -3/4 := by dsimp [c]; linarith
    have rad : 0 ≤ 1-c^2 := by nlinarith
    let z : ℂ := (c:ℂ)+(Real.sqrt (1-c^2):ℂ)*Complex.I
    have zs : Complex.normSq z = 1 := by
      dsimp [z]
      rw [Complex.normSq_add_mul_I, Real.sq_sqrt rad]
      ring
    have zr : z.re = c := by simp [z]
    have z0 : z ≠ 0 := by intro h; rw [h, map_zero] at zs; norm_num at zs
    have zt : Complex.normSq (1+(t:ℂ)*z) = t/2 := by
      have expand : Complex.normSq (1+(t:ℂ)*z) = 1+t^2*Complex.normSq z+2*t*z.re := by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
        ring
      rw [expand, zs, zr]
      dsimp [c]
      nlinarith
    let den : ℂ := (Real.sqrt 2:ℂ)*z*(1+(t:ℂ)*z)
    have dns : Complex.normSq den = t := by
      dsimp [den]
      rw [map_mul, map_mul, Complex.normSq_ofReal, zs, zt]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have dn0 : den ≠ 0 := by intro h; rw [h, map_zero] at dns; exact (ne_of_gt ht) dns.symm
    have rootnorm : Complex.normSq (-(r:ℂ)/den) = 1 := by
      rw [map_div₀, Complex.normSq_neg, Complex.normSq_ofReal, dns]
      change r*r/(r^2) = 1
      rw [← pow_two, div_self (ne_of_gt ht)]
    obtain ⟨u, ur⟩ := IsAlgClosed.exists_pow_nat_eq (-(r:ℂ)/den) (by norm_num : 0 < 3)
    have us : Complex.normSq u = 1 := by
      have h := congrArg Complex.normSq ur
      rw [map_pow, rootnorm] at h
      nlinarith [Complex.normSq_nonneg u, sq_nonneg (Complex.normSq u-1)]
    have u0 : u ≠ 0 := by intro h; rw [h, map_zero] at us; norm_num at us
    have ustar : u*star u = 1 := by
      rw [Complex.star_def, Complex.mul_conj, us, Complex.ofReal_one]
    have zstar : z*star z = 1 := by
      rw [Complex.star_def, Complex.mul_conj, zs, Complex.ofReal_one]
    let v := z*u^2
    have vs : Complex.normSq v = 1 := by
      dsimp [v]; rw [map_mul, map_pow, zs, us]; norm_num
    have dr : den*u^3 = -(r:ℂ) := by rw [ur]; field_simp [dn0]
    have phase : (Real.sqrt 2:ℂ)*u + (Real.sqrt 2:ℂ)*(t:ℂ)*v*star u +
        (r:ℂ)*star v = 0 := by
      have h : ((Real.sqrt 2:ℂ)*u + (Real.sqrt 2:ℂ)*(t:ℂ)*v*star u +
          (r:ℂ)*star v) * (z*u^2) = 0 := by
        calc
          _ = (Real.sqrt 2:ℂ)*z*u^3 +
              (Real.sqrt 2:ℂ)*(t:ℂ)*z^2*u^3*(u*star u) +
              (r:ℂ)*(z*star z)*(u*star u)^2 := by
            dsimp only [v]; simp only [Complex.star_def, map_mul, map_pow]; ring
          _ = den*u^3+(r:ℂ) := by rw [ustar, zstar]; dsimp [den]; ring
          _ = 0 := by rw [dr]; ring
      exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero z0 (pow_ne_zero 2 u0))
    have s30 : (Real.sqrt 3:ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3))
    have s3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
    let b : Fin 3 → ℂ := ![1/(Real.sqrt 3:ℂ), star u/(Real.sqrt 3:ℂ),
      star v/(Real.sqrt 3:ℂ)]
    have bn : ∀ k, Complex.normSq (b k) = 1/3 := by
      intro k
      fin_cases k <;>
        simp [b, Complex.normSq_div, Complex.star_def, Complex.normSq_conj, us, vs,
          Complex.normSq_ofReal, ← pow_two, s3]
    have bnormalized : Normalized b := by
      unfold Normalized
      simp_rw [bn]
      norm_num
    have fl : (Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)*star (star (b 0)) +
        (r:ℂ)^2*star (b 2)*star ((Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)) +
        star (b 0)*star ((r:ℂ)^2*star (b 2)) = 0 := by
      simp [b, star_div₀, star_mul, star_pow, Complex.star_def] at ⊢
      have eq : (Real.sqrt 2:ℂ)*u + (Real.sqrt 2:ℂ)*(r:ℂ)^2*v*star u +
          (r:ℂ)*star v = 0 := by simpa only [t, Complex.ofReal_pow] using phase
      simp only [Complex.star_def] at eq
      field_simp [s30]
      linear_combination (r:ℂ)*eq
    have latn : ∀ j : Fin 3,
        Complex.normSq (star (b 0)+(Real.sqrt 2:ℂ)*(r:ℂ)*star (b 1)*omega^j.val +
          (r:ℂ)^2*star (b 2)*omega^(2*j.val)) = (1/3:ℝ)*(1+r^2)^2 := by
      apply fourier.mpr
      refine ⟨?_, fl⟩
      rw [norm_formula b, bn 0, bn 1, bn 2]
      ring
    have resp : ∀ i, response r b i = 1/3 := by
      intro i
      fin_cases i
      · exact (polar b).1.trans (bn 0)
      · exact (polar b).2.trans (bn 2)
      · change response r b ⟨2+(0:Fin 3).val, by omega⟩ = 1/3
        rw [latitude b 0, latn 0]; field_simp
      · change response r b ⟨2+(1:Fin 3).val, by omega⟩ = 1/3
        rw [latitude b 1, latn 1]; field_simp
      · change response r b ⟨2+(2:Fin 3).val, by omega⟩ = 1/3
        rw [latitude b 2, latn 2]; field_simp
    exact ⟨⟨b, bnormalized, fun i => (resp i).trans (resp 0).symm⟩, universal⟩
  have sr0 : (Real.sqrt 2:ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))
  have sr : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have srreal : Real.sqrt 2*Real.sqrt 2 = 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have kp : 0 < kappa r := by
    unfold kappa
    apply div_pos _ (by norm_num)
    exact Real.sqrt_pos.mpr (by positivity)
  have kd : 1+kappa r ≠ 0 := by positivity
  have normsplit (a c : ℂ) :
      Complex.normSq ((a+c)/(Real.sqrt 2:ℂ)) +
      Complex.normSq ((a-c)/(Real.sqrt 2:ℂ)) = Complex.normSq a+Complex.normSq c := by
    rw [Complex.normSq_div, Complex.normSq_div, Complex.normSq_ofReal, srreal]
    simp [Complex.normSq_apply]
    ring
  have projection (v : Fin 2 × Fin 2 → ℂ) :
      let bs : Fin 3 → ℂ := ![v (0,0),(v (0,1)+v (1,0))/(Real.sqrt 2:ℂ),v (1,1)]
      ∀ i, ketResponse r v i = response r bs i := by
    intro bs i
    unfold ketResponse response
    congr 1
    simp [record, symmetric, bs, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.star_def]
    field_simp [sr0]
    ring_nf
    simp only [sr]
  have geometry (v : Fin 2 × Fin 2 → ℂ)
      (unit : ∑ p, Complex.normSq (v p) = 1)
      (det : v (0,0)*v (1,1)-v (0,1)*v (1,0) = 0)
      (flat : ∀ i, ketResponse r v i = ketResponse r v 0) :
      (∀ i, ketResponse r v i = h r) ∧
      Complex.normSq ((v (0,1)-v (1,0))/(Real.sqrt 2:ℂ)) = g r := by
    let bs : Fin 3 → ℂ := ![v (0,0),(v (0,1)+v (1,0))/(Real.sqrt 2:ℂ),v (1,1)]
    let delta := (v (0,1)-v (1,0))/(Real.sqrt 2:ℂ)
    let A := ∑ k, Complex.normSq (bs k)
    have Apos : 0 ≤ A := Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
    have total : A+Complex.normSq delta = 1 := by
      have split := normsplit (v (0,1)) (v (1,0))
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at unit
      change (Complex.normSq (v (0,0)) +
        (Complex.normSq ((v (0,1)+v (1,0))/(Real.sqrt 2:ℂ))+
          (Complex.normSq (v (1,1))+0))) +
          Complex.normSq ((v (0,1)-v (1,0))/(Real.sqrt 2:ℂ)) = 1
      linarith
    have deq : delta^2 = bs 1^2-2*bs 0*bs 2 := by
      dsimp [bs, delta]
      field_simp [sr0]
      rw [sr]
      linear_combination 4*det
    have Ap : 0 < A := by
      by_contra hA
      have Az : A = 0 := le_antisymm (le_of_not_gt hA) Apos
      have bz : ∀ k, bs k = 0 := by
        intro k
        apply Complex.normSq_eq_zero.mp
        have sumzero : ∑ k, Complex.normSq (bs k) = 0 := Az
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).mp sumzero k (Finset.mem_univ k)
      rw [bz 0, bz 1, bz 2] at deq
      have dz : delta = 0 := sq_eq_zero_iff.mp (by simpa using deq)
      rw [Az, dz, map_zero] at total
      norm_num at total
    let alpha := Real.sqrt A
    have aps : alpha^2 = A := Real.sq_sqrt Apos
    have app : 0 < alpha := Real.sqrt_pos.mpr Ap
    have ap0 : (alpha:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt app
    let b : Fin 3 → ℂ := fun k => bs k/(alpha:ℂ)
    have bn : Normalized b := by
      unfold Normalized
      simp only [b, Complex.normSq_div, Complex.normSq_ofReal]
      rw [← pow_two, aps, ← Finset.sum_div, div_self (ne_of_gt Ap)]
    have bc : ∀ k, bs k = (alpha:ℂ)*b k := by
      intro k; dsimp [b]; field_simp [ap0]
    have ampeq (i : Fin 5) :
        (∑ p, star (symmetric bs p)*record r i p) =
        (alpha:ℂ)*(∑ p, star (symmetric b p)*record r i p) := by
      simp only [symmetric, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp_rw [bc]
      simp only [star_mul, star_div₀, Complex.star_def, Complex.conj_ofReal]
      ring
    have reseq (i : Fin 5) : ketResponse r v i = A*response r b i := by
      rw [projection v i]
      unfold response
      rw [ampeq, map_mul, Complex.normSq_ofReal, ← pow_two, aps]
    have fb : Flat r b := by
      intro i
      apply mul_left_cancel₀ (ne_of_gt Ap)
      rw [← reseq i, ← reseq 0]
      exact flat i
    obtain ⟨resp, coords, detnorm⟩ := sym.2 b bn fb
    have ds : Complex.normSq delta = A*kappa r := by
      have dscaled : delta^2 = (alpha:ℂ)^2*(b 1^2-2*b 0*b 2) := by
        rw [deq, bc 0, bc 1, bc 2]; ring
      calc
        _ = ‖delta^2‖ := by rw [norm_pow, Complex.normSq_eq_norm_sq]
        _ = ‖(alpha:ℂ)^2‖*‖b 1^2-2*b 0*b 2‖ := by rw [dscaled, norm_mul]
        _ = A*kappa r := by
          rw [norm_pow, Complex.norm_of_nonneg app.le, aps, detnorm]
    have aval : A = 1/(1+kappa r) := by
      apply (eq_div_iff kd).mpr
      nlinarith [total, ds]
    constructor
    · intro i; rw [reseq i, resp i, aval]; unfold h; field_simp [kd]
    · change Complex.normSq delta = g r
      rw [ds, aval]; unfold g; ring
  have prodgeom (x y : Fin 2 → ℂ) (hx : UnitSpinor x) (hy : UnitSpinor y)
      (hf : FlatProduct r x y) :
      (∀ i, productResponse r x y i = h r) ∧ antisymmetricWeight x y = g r ∧
      spinorZ x = -spinorZ y ∧ (spinorZ x)^2 = 1-4*h r := by
    have unit : ∑ p, Complex.normSq (productVector x y p) = 1 := by
      simp only [UnitSpinor, Fin.sum_univ_two] at hx hy
      simp only [productVector, Fintype.sum_prod_type, Fin.sum_univ_two, map_mul]
      nlinarith
    have det : productVector x y (0,0)*productVector x y (1,1) -
        productVector x y (0,1)*productVector x y (1,0) = 0 := by dsimp [productVector]; ring
    obtain ⟨resp, anti⟩ := geometry (productVector x y) unit det hf
    refine ⟨resp, anti, ?_⟩
    have px : Complex.normSq (x 0)+Complex.normSq (x 1) = 1 := by
      simpa only [UnitSpinor, Fin.sum_univ_two] using hx
    have py : Complex.normSq (y 0)+Complex.normSq (y 1) = 1 := by
      simpa only [UnitSpinor, Fin.sum_univ_two] using hy
    have p0 := resp 0
    have p1 := resp 1
    simp [productResponse, ketResponse, productVector, record, source,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.star_def, Complex.normSq_conj,
      Complex.normSq_mul] at p0 p1
    have x1 : Complex.normSq (x 1) = 1-Complex.normSq (x 0) := by linarith
    have y1 : Complex.normSq (y 1) = 1-Complex.normSq (y 0) := by linarith
    rw [x1,y1] at p1
    have sum0 : Complex.normSq (x 0)+Complex.normSq (y 0) = 1 := by nlinarith [p0,p1]
    have yy : Complex.normSq (y 0) = 1-Complex.normSq (x 0) := by linarith
    rw [yy] at p0
    dsimp [spinorZ]
    rw [x1,y1,yy]
    constructor <;> nlinarith [p0]
  obtain ⟨b,bunit,bflat⟩ := sym.1
  obtain ⟨bresp,bcoords,bdnorm⟩ := sym.2 b bunit bflat
  obtain ⟨delta,dsquare⟩ := IsAlgClosed.exists_pow_nat_eq (b 1^2-2*b 0*b 2) (by norm_num : 0 < 2)
  have dnorm : Complex.normSq delta = kappa r := by
    calc
      _ = ‖delta^2‖ := by rw [Complex.normSq_eq_norm_sq,norm_pow]
      _ = kappa r := by rw [dsquare,bdnorm]
  let v0 : Fin 2 × Fin 2 → ℂ := fun p =>
    (!![b 0,(b 1+delta)/(Real.sqrt 2:ℂ);(b 1-delta)/(Real.sqrt 2:ℂ),b 2]) p.1 p.2
  have vn0 : ∑ p, Complex.normSq (v0 p) = 1+kappa r := by
    have nn : Complex.normSq (b 0)+Complex.normSq (b 1)+Complex.normSq (b 2) = 1 := by
      change Complex.normSq (b 0)+(Complex.normSq (b 1)+(Complex.normSq (b 2)+0)) = 1 at bunit
      linarith
    have split := normsplit (b 1) delta
    simp only [Fintype.sum_prod_type,Fin.sum_univ_two]
    change Complex.normSq (b 0)+Complex.normSq ((b 1+delta)/(Real.sqrt 2:ℂ))+
      (Complex.normSq ((b 1-delta)/(Real.sqrt 2:ℂ))+Complex.normSq (b 2)) = 1+kappa r
    linarith
  have vd0 : v0 (0,0)*v0 (1,1)-v0 (0,1)*v0 (1,0) = 0 := by
    dsimp [v0]
    field_simp [sr0]
    rw [sr]
    linear_combination dsquare
  have vr0 (i : Fin 5) : ketResponse r v0 i = response r b i := by
    unfold ketResponse response
    congr 1
    simp [v0,symmetric,record,Fintype.sum_prod_type,Fin.sum_univ_two,Complex.star_def]
    ring
  let scale := Real.sqrt (1+kappa r)
  have scalep : 0 < scale := Real.sqrt_pos.mpr (by positivity)
  have scale0 : (scale:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt scalep
  have scales : scale^2 = 1+kappa r := Real.sq_sqrt (by positivity)
  let v := fun p => v0 p/(scale:ℂ)
  have vn : ∑ p, Complex.normSq (v p) = 1 := by
    simp only [v,Complex.normSq_div,Complex.normSq_ofReal,← pow_two,scales]
    rw [← Finset.sum_div,vn0,div_self kd]
  have vd : v (0,0)*v (1,1)-v (0,1)*v (1,0) = 0 := by
    dsimp [v]; field_simp [scale0]; simpa only [mul_zero] using vd0
  have vr (i : Fin 5) : ketResponse r v i = h r := by
    have amp : (∑ p,star (v p)*record r i p) =
        (∑ p,star (v0 p)*record r i p)/(scale:ℂ) := by
      simp only [v,star_div₀,Complex.star_def,Complex.conj_ofReal]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _; ring
    unfold ketResponse
    rw [amp,Complex.normSq_div,Complex.normSq_ofReal,← pow_two,scales]
    change ketResponse r v0 i/(1+kappa r) = h r
    rw [vr0 i,bresp i]
    unfold h; field_simp [kd]
  have vb0 : v (0,0) ≠ 0 := by
    have bb0 : b 0 ≠ 0 := by
      intro hz
      have eq := bcoords 0
      rw [hz,map_zero] at eq
      norm_num at eq
    exact div_ne_zero bb0 scale0
  let ratio := v (1,0)/v (0,0)
  let localScale := Real.sqrt (1+Complex.normSq ratio)
  have lp : 0 < localScale := Real.sqrt_pos.mpr (by linarith [Complex.normSq_nonneg ratio])
  have l0 : (localScale:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt lp
  have ls : localScale^2 = 1+Complex.normSq ratio := Real.sq_sqrt (by linarith [Complex.normSq_nonneg ratio])
  let x : Fin 2 → ℂ := ![1/(localScale:ℂ),ratio/(localScale:ℂ)]
  let y : Fin 2 → ℂ := ![(localScale:ℂ)*v (0,0),(localScale:ℂ)*v (0,1)]
  have xv : UnitSpinor x := by
    simp only [UnitSpinor,Fin.sum_univ_two,x,Matrix.cons_val_zero,
      Matrix.cons_val_one,map_one,Complex.normSq_div,Complex.normSq_ofReal,← pow_two,ls]
    field_simp [ne_of_gt (by linarith [Complex.normSq_nonneg ratio] : 0 < 1+Complex.normSq ratio)]
  have xy : productVector x y = v := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [productVector,x,y,ratio] <;>
      field_simp [l0,vb0]
    linear_combination -vd
  have yv : UnitSpinor y := by
    have xsum := xv
    change (∑ k,Complex.normSq (x k)) = 1 at xsum
    rw [Fin.sum_univ_two] at xsum
    have total := vn
    rw [← xy] at total
    simp only [productVector,Fintype.sum_prod_type,Fin.sum_univ_two,map_mul] at total
    have ysum : Complex.normSq (y 0)+Complex.normSq (y 1) = 1 := by
      have eq : (Complex.normSq (x 0)+Complex.normSq (x 1)) *
          (Complex.normSq (y 0)+Complex.normSq (y 1)) = 1 := by nlinarith [total]
      rw [xsum,one_mul] at eq; exact eq
    simpa only [UnitSpinor,Fin.sum_univ_two] using ysum
  have prodresp : ∀ i,productResponse r x y i = h r := by
    intro i; unfold productResponse; rw [xy]; exact vr i
  have pureSpinor (a : Bloch) (ha : ‖a‖ = 1) :
      ∃ x : Fin 2 → ℂ, UnitSpinor x ∧ rho a = Matrix.vecMulVec x (star x) := by
    have an : a 0^2+a 1^2+a 2^2 = 1 := by
      have h := congrArg (fun u : ℝ => u^2) ha
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [Fin.sum_univ_succ,add_assoc] using h
    have az : -1 ≤ a 2 := by nlinarith [sq_nonneg (a 0),sq_nonneg (a 1)]
    by_cases south : a 2 = -1
    · have a00 : a 0 = 0 := by nlinarith [sq_nonneg (a 1)]
      have a10 : a 1 = 0 := by nlinarith [sq_nonneg (a 0)]
      refine ⟨![0,1],by norm_num [UnitSpinor,Fin.sum_univ_two],?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rho,D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
          Matrix.vecMulVec, a00,a10,south]
    · have azp : -1 < a 2 := lt_of_le_of_ne az (Ne.symm south)
      let z := Real.sqrt ((1+a 2)/2)
      have zp : 0 < z := Real.sqrt_pos.mpr (by linarith)
      have z0 : (z:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt zp
      have zs : z^2 = (1+a 2)/2 := Real.sq_sqrt (by linarith)
      let u : Fin 2 → ℂ := ![(z:ℂ),((a 0:ℂ)+(a 1:ℂ)*Complex.I)/(2*(z:ℂ))]
      have un : UnitSpinor u := by
        simp [UnitSpinor,u,Fin.sum_univ_two,Complex.normSq_div,
          Complex.normSq_mul,Complex.normSq_add_mul_I,Complex.normSq_ofReal]
        field_simp [ne_of_gt zp]
        nlinarith [zs,an]
      refine ⟨u,un,?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        simp [rho,D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
          u,Matrix.vecMulVec,Complex.div_re,Complex.div_im,Complex.normSq_apply] <;>
        field_simp [ne_of_gt zp] <;>
        nlinarith [zs,an]
  have spinorBloch (u : Fin 2 → ℂ) (hu : UnitSpinor u) :
      ∃ a : Bloch, ‖a‖ = 1 ∧ rho a = Matrix.vecMulVec u (star u) ∧ a 2 = spinorZ u := by
    let a : Bloch := WithLp.toLp 2 ![2*(u 0*star (u 1)).re,
      -2*(u 0*star (u 1)).im,spinorZ u]
    have un : Complex.normSq (u 0)+Complex.normSq (u 1) = 1 := by
      simpa only [UnitSpinor,Fin.sum_univ_two] using hu
    refine ⟨a,?_,?_,rfl⟩
    · have asq : ‖a‖^2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        have un2 := congrArg (fun t : ℝ => t^2) un
        simp [a,spinorZ,Fin.sum_univ_succ,Complex.star_def,Complex.normSq_apply] at ⊢ un un2
        nlinarith
      nlinarith [norm_nonneg a]
    · ext i j
      fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
        simp [rho,D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
          Matrix.vecMulVec,a,spinorZ,Complex.star_def,Complex.normSq_apply] at ⊢ un <;>
        nlinarith
  have matrixSpinors (a b : Bloch) (u v : Fin 2 → ℂ)
      (ha : rho a = Matrix.vecMulVec u (star u))
      (hb : rho b = Matrix.vecMulVec v (star v)) (i : Fin 5) :
      matrixResponse r a b i = productResponse r u v i := by
    unfold matrixResponse Q productResponse ketResponse
    rw [ha,hb]
    have full : (star (record r i) ⬝ᵥ
        ((Matrix.kronecker (Matrix.vecMulVec u (star u)) (Matrix.vecMulVec v (star v))) *ᵥ record r i)) =
        (Complex.normSq (∑ p,star (productVector u v p)*record r i p):ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [Matrix.kronecker_apply,Matrix.vecMulVec_apply,dotProduct,
        Matrix.mulVec,star_mul,star_sum,Pi.star_apply,Complex.star_def,star_star,
        Finset.mul_sum,Finset.sum_mul,productVector,map_sum,map_mul,Complex.conj_conj]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      dsimp [Matrix.kronecker,Matrix.kroneckerMap,Matrix.vecMulVec,Complex.star_def]
      ring
    exact congrArg Complex.re full
  have defectSpinors (a b : Bloch) (u v : Fin 2 → ℂ)
      (hu : UnitSpinor u) (hv : UnitSpinor v)
      (ha : rho a = Matrix.vecMulVec u (star u))
      (hb : rho b = Matrix.vecMulVec v (star v)) :
      defect a b = antisymmetricWeight u v := by
    have az : ∀ k, a k = (![2*(u 0*star (u 1)).re,-2*(u 0*star (u 1)).im,spinorZ u]) k := by
      -- Recover the fixed Bloch coordinates from the actual projector entries.
      intro k
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) ha
      have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) ha
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) ha
      have h01i := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) ha
      simp [rho,D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
        Matrix.vecMulVec,Complex.star_def,spinorZ,Complex.normSq_apply] at h00 h11 h01 h01i
      fin_cases k <;> simp [spinorZ,Complex.normSq_apply] <;> linarith
    have bz : ∀ k, b k = (![2*(v 0*star (v 1)).re,-2*(v 0*star (v 1)).im,spinorZ v]) k := by
      intro k
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hb
      have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hb
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) hb
      have h01i := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) hb
      simp [rho,D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
        Matrix.vecMulVec,Complex.star_def,spinorZ,Complex.normSq_apply] at h00 h11 h01 h01i
      fin_cases k <;> simp [spinorZ,Complex.normSq_apply] <;> linarith
    simp only [UnitSpinor,Fin.sum_univ_two] at hu hv
    have uv : (Complex.normSq (u 0)+Complex.normSq (u 1)) *
        (Complex.normSq (v 0)+Complex.normSq (v 1)) = 1 := by rw [hu,hv]; norm_num
    simp only [Complex.normSq_apply] at uv
    simp [defect,PiLp.inner_apply,RCLike.inner_apply,Fin.sum_univ_succ,
      az,bz,antisymmetricWeight,Complex.normSq_div,Complex.normSq_ofReal,srreal,
      Complex.normSq_apply,Complex.star_def,spinorZ]
    nlinarith [uv]
  obtain ⟨a,an,am,az⟩ := spinorBloch x xv
  obtain ⟨bb,bn,bm,bz⟩ := spinorBloch y yv
  refine ⟨sym,⟨x,y,xv,yv,prodresp⟩,prodgeom,⟨(a,bb),an,bn,?_⟩,?_⟩
  · intro i; rw [matrixSpinors a bb x y am bm i]; exact prodresp i
  · intro a b hab
    obtain ⟨u,hu,ha⟩ := pureSpinor a hab.1
    obtain ⟨v,hv,hb⟩ := pureSpinor b hab.2.1
    have flat : FlatProduct r u v := by
      intro i
      rw [← matrixSpinors a b u v ha hb i,← matrixSpinors a b u v ha hb 0,
        hab.2.2 i,hab.2.2 0]
    obtain ⟨resp,anti,polar,pheight⟩ := prodgeom u v hu hv flat
    have a2 : a 2 = spinorZ u := by
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re-(M 1 1).re) ha
      simp [rho,D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
        Matrix.vecMulVec,Complex.star_def,spinorZ,Complex.normSq_apply] at h00 ⊢
      linarith
    have b2 : b 2 = spinorZ v := by
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re-(M 1 1).re) hb
      simp [rho,D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix,
        Matrix.vecMulVec,Complex.star_def,spinorZ,Complex.normSq_apply] at h00 ⊢
      linarith
    exact ⟨by rw [a2,b2]; exact polar,by rw [a2]; exact pheight,
      (defectSpinors a b u v hu hv ha hb).trans anti⟩
end D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
