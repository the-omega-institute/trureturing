/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumAllocation
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The singular three-value Gram allocation and its scaling. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumCounts

/-!
# Allocation for the singular four-copy comparison

The five polynomial inequalities in the oracle's equation (12) supply
the three positive semidefinite blocks for the unnormalized four-slot kernel.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.ThreeBlockGram.ZeroSpectrum

open FourCopyGap (Gap gaps mem_gaps gapDefect)
open private monomial balanced from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open Separated (block block_scale block_psd_of_schur rawS rawU rawV rawF rawG rawW)

def eta (p : ℕ) (r y : ℝ) : ℝ := rawS (p+1) r / R y

/-- Equation (1) in the normalization of `spectralDefect`. -/
def allocation (p : ℕ) (r y : ℝ) : Fin 3 → Fin 3 → ℝ :=
  let e := eta p r y
  let m := c p * y^4 * e + D p * y^5
  let t := c p * e + D p * y^4
  ![![0, y^4 * e, e], ![m, 0, rawU (p+1) r - m], ![t, rawV (p+1) r - t, 0]]

private structure Numerators (p : ℕ) (r y : ℝ) : Prop where
  hs : w r * rawS (p+1) r = s r y
  hu : (w r)^2 * rawU (p+1) r = u p r y
  hv : (w r)^2 * rawV (p+1) r = v p r y
  hf : (w r)^3 * (rawF (p+1) r - N p * y^6) = fNum p r y
  hj : (w r)^3 * (rawG (p+1) r - N p * y^2) = jNum p r y
  hg : (w r)^3 * (rawW (p+1) r - N p * y^4) = gNum p r y

private theorem numerators (p : ℕ) (r y : ℝ) (hy : y^8 = r^p) : Numerators p r y := by
  have hpw : r^(p+1) = r * y^8 := by rw [hy, pow_succ, mul_comm]
  obtain ⟨hS,hU,hV,hF,hJ,hG⟩ := Separated.finite_sum_forms (p+1) r
  simp only [hpw, Nat.cast_add, Nat.cast_one, Separated.M] at hS hU hV hF hJ hG
  constructor
  · simpa only [w, s] using hS
  · unfold w u q
    rw [hU]
    ring
  · unfold w v q
    rw [hV]
    ring
  · unfold fNum w C q
    rw [mul_sub, hF]
    ring
  · unfold jNum w C q
    rw [mul_sub, hJ]
    ring
  · unfold gNum w q
    rw [mul_sub, hG]
    ring

private theorem rawS_pos (p : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 < rawS (p+1) r := by
  unfold rawS
  refine Finset.sum_pos' (fun i _ ↦ pow_nonneg hr i) ?_
  exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos p), by simp⟩

private theorem gramBlock_eq_block (k : Kernel) (l : Fin 3 → Fin 3 → ℝ) (i j t : Fin 3) :
    gramBlock k l i j t =
      block (f k i j) (g k i j / 2) (f k j i) (l i j) (l j i) (h k t i j) := by
  simp [gramBlock, block, Complex.ofReal_div]

private theorem incident_block (p e t H : ℝ) (hp : 0 ≤ p)
    (hH : 0 ≤ H - e^2 - D p * t^2) :
    (block 1 (c p) (C p) e (c p * e + D p * t) H).PosSemidef := by
  have hD : 0 < D p := by unfold D q; positivity
  have hCD : C p - (c p)^2 / 1 = D p := by unfold C c D q; ring
  apply block_psd_of_schur
  · norm_num
  · rwa [hCD]
  · rw [hCD, show c p * e + D p * t - c p * e / 1 = D p * t by ring]
    apply sub_nonneg.mp
    calc
      0 ≤ D p * (H - e^2 - D p * t^2) := mul_nonneg hD.le hH
      _ = _ := by ring

/-- The last pivot may be eliminated even if both diagonal signs of its
Schur complement are attained at equality. -/
private theorem block_psd_of_last (a x b y z t : ℝ) (ht : 0 < t)
    (ha : 0 ≤ a*t - y^2) (hb : 0 ≤ b*t - z^2)
    (hd : 0 ≤ (a*b-x^2)*t - b*y^2 - a*z^2 + 2*x*y*z) :
    (block a x b y z t).PosSemidef := by
  let A := a-y^2/t
  let B := b-z^2/t
  let X := x-y*z/t
  have hA : 0 ≤ A := sub_nonneg.mpr ((div_le_iff₀ ht).mpr (sub_nonneg.mp ha))
  have hB : 0 ≤ B := sub_nonneg.mpr ((div_le_iff₀ ht).mpr (sub_nonneg.mp hb))
  have hdet : t*(A*B-X^2) = (a*b-x^2)*t - b*y^2 - a*z^2 + 2*x*y*z := by
    dsimp [A, B, X]
    field_simp [ht.ne'] <;> ring
  have hX : X^2 ≤ A*B := by
    apply sub_nonneg.mp
    apply (mul_nonneg_iff_of_pos_left ht).mp
    rw [hdet]
    exact hd
  have hbase : (block t 0 A 0 X B).PosSemidef := by
    rcases eq_or_lt_of_le hA with hzero | hpos
    · have hxzero : X = 0 := (sq_nonpos_iff X).mp (by simpa only [← hzero, zero_mul] using hX)
      have heq : block t 0 A 0 X B = diagonal ![(t:ℂ), (A:ℂ), (B:ℂ)] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [block, hxzero, Matrix.diagonal_apply]
      rw [heq]
      apply posSemidef_diagonal_iff.mpr
      intro i
      fin_cases i
      · exact Complex.zero_le_real.mpr ht.le
      · exact Complex.zero_le_real.mpr hA
      · exact Complex.zero_le_real.mpr hB
    · apply block_psd_of_schur _ _ _ _ _ _ ht
      · simpa using hpos
      · simpa using hX
  let L : Matrix (Fin 3) (Fin 3) ℂ :=
    !![1, 0, 0; (↑(y/t) : ℂ), 1, 0; (↑(z/t) : ℂ), 0, 1]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hfac : L * block t 0 A 0 X B * Lᴴ = block t y a z x b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, block, A, B, X, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_three, Complex.star_def] <;>
      push_cast <;> field_simp [htC] <;> ring
  have hperm : (block t y a z x b).PosSemidef := hfac ▸ hbase.mul_mul_conjTranspose_same L
  have heq : (block t y a z x b).submatrix (![1,2,0] : Fin 3 → Fin 3) ![1,2,0] =
      block a x b y z t := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [← heq]
  exact hperm.submatrix ![1,2,0]

/-- Equation (12) implies all three PSD blocks and all three row sums. -/
theorem allocation_of_signs (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hsigns : Signs (p : ℝ) r (root p r)) :
    Allocation (spectralDefect p ![0,r,1]) (allocation p r (root p r)) := by
  let y := root p r
  let e := eta p r y
  let S := rawS (p+1) r
  let U := rawU (p+1) r
  let V := rawV (p+1) r
  let F := rawF (p+1) r - N p * y^6
  let J := rawG (p+1) r - N p * y^2
  let G := rawW (p+1) r - N p * y^4
  let L := U - (c p * y^4 * e + D p * y^5)
  let T := V - (c p * e + D p * y^4)
  have hcoeff : Coefficients p r y := coefficient_counts p hp hr.le
  have hn := numerators p r y (root_pow_eight p hr.le)
  have hS : 0 < S := rawS_pos p hr.le
  have hw : 0 < w r := sub_pos.mpr hr1
  have hR : 0 < R y := by unfold R; positivity
  have heR : e * R y = S := div_mul_cancel₀ _ hR.ne'
  have hes : w r * (e * R y) = s r y := by rw [heR]; exact hn.hs
  have hU : (w r)^2 * U = u p r y := hn.hu
  have hV : (w r)^2 * V = v p r y := hn.hv
  have hF : (w r)^3 * F = fNum p r y := hn.hf
  have hJ : (w r)^3 * J = jNum p r y := hn.hj
  have hG : (w r)^3 * G = gNum p r y := hn.hg
  have ha : 0 ≤ U - e^2 - D p * y^8 := by
    apply (mul_nonneg_iff_of_pos_left (pow_pos (mul_pos hw hR) 2)).mp
    calc
      0 ≤ Astar p r y := hsigns.aStar
      _ = _ := by unfold Astar; rw [← hU, ← hes]; ring
  have hb : 0 ≤ V - e^2 - D p * y^2 := by
    apply (mul_nonneg_iff_of_pos_left (pow_pos (mul_pos hw hR) 2)).mp
    calc
      0 ≤ Bstar p r y := hsigns.bStar
      _ = _ := by unfold Bstar; rw [← hV, ← hes]; ring
  have hL : (w r)^2 * R y * L = alpha p r y := by
    unfold L alpha
    rw [← hU, ← hes]
    ring
  have hT : (w r)^2 * R y * T = beta p r y := by
    unfold T beta
    rw [← hV, ← hes]
    ring
  have hz : z r y = w r * S * (R y)^2 := by
    unfold z S
    rw [hn.hs]
  have h₁ : 0 ≤ F*S-L^2 := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (pow_pos hw 4) (pow_pos hR 2))).mp
    calc
      0 ≤ P1 p r y := hsigns.p1
      _ = _ := by unfold P1; rw [← hF, hz, ← hL]; ring
  have h₂ : 0 ≤ J*S-T^2 := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (pow_pos hw 4) (pow_pos hR 2))).mp
    calc
      0 ≤ P2 p r y := hsigns.p2
      _ = _ := by unfold P2; rw [← hJ, hz, ← hT]; ring
  have h₃ : 0 ≤ (F*J-(G/2)^2)*S - J*L^2 - F*T^2 + 2*(G/2)*L*T := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (pow_pos hw 7) (pow_pos hR 2))).mp
    calc
      0 ≤ P3 p r y := hsigns.p3
      _ = _ := by
        unfold P3
        rw [← hF, ← hJ, ← hG, hz, ← hL, ← hT]
        ring
  have h01 := incident_block (p : ℝ) e y V (Nat.cast_nonneg p) hb
  have h01scaled := block_scale _ _ _ _ _ _ (y^4) (y^4) 1 h01
  have h02 := incident_block (p : ℝ) e (y^4) U (Nat.cast_nonneg p)
    (show 0 ≤ U - e^2 - D p * (y^4)^2 by
      rw [show (y^4)^2 = y^8 by ring]
      exact ha)
  have h12 := block_psd_of_last F (G/2) J L T S hS h₁ h₂ h₃
  change Allocation (spectralDefect p ![0,r,1]) (allocation p r y)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcoeff.h0]
    change y^4*e + e = S
    calc
      _ = e * R y := by unfold R; ring
      _ = S := heR
  · rw [hcoeff.h1]
    change c p * y^4 * e + D p * y^5 + L = U
    unfold L
    ring
  · rw [hcoeff.h2]
    change c p * e + D p * y^4 + T = V
    unfold T
    ring
  · rw [gramBlock_eq_block, hcoeff.f01, hcoeff.g01, hcoeff.f10, hcoeff.h2]
    change (block (y^8) (q p*y^8/2) (C p*y^8) (y^4*e)
      (c p*y^4*e+D p*y^5) V).PosSemidef
    have heq : block ((y^4)^2*1) (y^4*y^4*c p) ((y^4)^2*C p)
        (y^4*1*e) (y^4*1*(c p*e+D p*y)) (1^2*V) =
        block (y^8) (q p*y^8/2) (C p*y^8) (y^4*e) (c p*y^4*e+D p*y^5) V := by
      congr 1 <;> (try unfold c) <;> ring
    exact heq ▸ h01scaled
  · rw [gramBlock_eq_block, hcoeff.f02, hcoeff.g02, hcoeff.f20, hcoeff.h1]
    exact h02
  · rw [gramBlock_eq_block, hcoeff.f12, hcoeff.g12, hcoeff.f21, hcoeff.h0]
    exact h12

/-- The four-copy lower comparison for spectra contained in `{0,r,1}`.
The eigenvalue condition allows the absence of any label. -/
theorem product_bound_of_signs {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hspectrum : ∀ a, ∃ i : Fin 3, hA.isHermitian.eigenvalues a =
      (![0,r,1] : Fin 3 → ℝ) i)
    (hsigns : Signs (p : ℝ) r (root p r)) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  have hx (i : Fin 3) : 0 ≤ (![0,r,1] : Fin 3 → ℝ) i := by
    fin_cases i <;> simp [hr.le]
  exact product_bound_of_spectrum_subset p A B hA hB ![0,r,1] hx hspectrum _
    (allocation_of_signs p hp hr hr1 hsigns)

private theorem gapDefect_scale (p : ℕ) {t a b c d : ℝ} (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    gapDefect p (t*a) (t*b) (t*c) (t*d) = t^p * gapDefect p a b c d := by
  have hm (g : Gap) (hg : g ∈ gaps p) :
      monomial (t*a) (t*b) (t*c) (t*d) g = t^p * monomial a b c d g := by
    rw [← mem_gaps.mp hg]
    simp only [monomial, mul_pow, pow_add]
    ring
  have ht4 : (t ^ ((p : ℝ) / 4))^4 = t^p := by
    rw [← Real.rpow_mul_natCast ht]
    rw [show (p : ℝ) / 4 * ((4 : ℕ) : ℝ) = (p : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hb' : balanced p (t*a) (t*b) (t*c) (t*d) = t^p * balanced p a b c d := by
    rw [← ht4]
    simp only [balanced, Real.mul_rpow ht ha, Real.mul_rpow ht hb,
      Real.mul_rpow ht hc, Real.mul_rpow ht hd]
    ring
  unfold gapDefect
  rw [hb', Finset.sum_congr rfl hm, ← Finset.mul_sum]
  ring

private theorem allocation_scale {k k' : Kernel} {l : Fin 3 → Fin 3 → ℝ} {m : ℝ}
    (hm : 0 ≤ m) (hk : ∀ i j u v, k' i j u v = m * k i j u v)
    (ha : Allocation k l) :
    Allocation k' (fun i j ↦ m * l i j) := by
  have hr (i j u : Fin 3) (he : l i j + l i u = h k i j u) :
      m * l i j + m * l i u = h k' i j u := by
    rw [← mul_add, he]
    exact (hk i i j u).symm
  have hpsd (i j u : Fin 3) (hG : (gramBlock k l i j u).PosSemidef) :
      (gramBlock k' (fun i j ↦ m * l i j) i j u).PosSemidef := by
    have he : gramBlock k' (fun i j ↦ m * l i j) i j u =
        (m : ℂ) • gramBlock k l i j u := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [gramBlock, f, g, h, hk, Matrix.smul_apply, smul_eq_mul] <;>
        push_cast <;> ring
    rw [he]
    exact hG.smul (Complex.zero_le_real.mpr hm)
  obtain ⟨h0,h1,h2,h01,h02,h12⟩ := ha
  exact ⟨hr 0 1 2 h0, hr 1 0 2 h1, hr 2 0 1 h2,
    hpsd 0 1 2 h01, hpsd 0 2 1 h02, hpsd 1 2 0 h12⟩

/-- Positive rescaling gives the same bound for spectra contained in `{0,r,t}`. -/
theorem scaled_product_bound_of_signs {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp : 0 < p) {r t : ℝ} (hr : 0 < r) (hrt : r < t) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hspectrum : ∀ a, ∃ i : Fin 3, hA.isHermitian.eigenvalues a =
      (![0,r,t] : Fin 3 → ℝ) i)
    (hsigns : Signs (p : ℝ) (r/t) (root p (r/t))) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  have ht : 0 < t := hr.trans hrt
  have hratio : 0 < r/t := div_pos hr ht
  have hratio1 : r/t < 1 := (div_lt_iff₀ ht).mpr (by simpa using hrt)
  let x : Fin 3 → ℝ := ![0,r/t,1]
  have hx (i : Fin 3) : 0 ≤ x i := by
    fin_cases i <;> simp [x, hratio.le]
  have hscaled (i : Fin 3) : (![0,r,t] : Fin 3 → ℝ) i = t * x i := by
    fin_cases i <;> simp [x]
    field_simp
  let l := allocation p (r/t) (root p (r/t))
  have halloc : Allocation (spectralDefect p x) l :=
    allocation_of_signs p hp hratio hratio1 hsigns
  have hkernel (i j u v : Fin 3) :
      spectralDefect p ![0,r,t] i j u v = t^p * spectralDefect p x i j u v := by
    unfold spectralDefect
    rw [hscaled i, hscaled j, hscaled u, hscaled v]
    exact gapDefect_scale p ht.le (hx i) (hx j) (hx u) (hx v)
  have hx' (i : Fin 3) : 0 ≤ (![0,r,t] : Fin 3 → ℝ) i := by
    rw [hscaled]
    exact mul_nonneg ht.le (hx i)
  exact product_bound_of_spectrum_subset p A B hA hB ![0,r,t] hx' hspectrum _
    (allocation_scale (pow_nonneg ht.le p) hkernel halloc)

#print axioms allocation_of_signs
#print axioms product_bound_of_signs
#print axioms scaled_product_bound_of_signs

end RefinedBMV.ThreeBlockGram.ZeroSpectrum
