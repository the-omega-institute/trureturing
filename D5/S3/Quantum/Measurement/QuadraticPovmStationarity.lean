/- GID: D5/S3/Quantum/Measurement/QuadraticPovmStationarity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QuadraticPovmStationarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic positive POVM variations force first-order stationarity. -/

/-
proof_shape: quadratic_stationarity: content; normalized positive variations produce
  a local maximum and its vanishing derivative.
escape_witness: quadratic_stationarity
admission_basis: escape-witness
Direct frozen dependencies (declaration GID + statement_id):
  F1 = D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.IsPOVM
    sha256:218e2b42c4dc29468db56af33ad277eb32b8ed575533012439ed233131c5efa1
Per-declaration classification (F-labels refer to the declaration identities above):
  quadratic_stationarity: content; consumers: stationarity_constraints
    frozen dependencies: F1; escape_witness: quadratic_stationarity
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15773
The infinite dependent matrix/real telescope needs source reconstruction,
an enrolled readout and variation, sensitivity and observational-dependence proofs.
No Reg registration is delivered; the four-slot reading is DTR-Unregistered (Observe).
-/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix Filter
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
noncomputable section
namespace D5.S3.Quantum.Measurement.QuadraticPovmStationarity
set_option maxHeartbeats 2000000

theorem quadratic_stationarity {n dim : ℕ} (A M : Fin n → Matrix (Fin dim) (Fin dim) ℂ) (i : Fin n)
    (hM : IsPOVM M)
    (hopt : ∀ F, IsPOVM F → ∑ j, (trace (A j * F j)).re ≤
      ∑ j, (trace (A j * M j)).re)
    (D E : Matrix (Fin dim) (Fin dim) ℂ) (d e : Fin n → ℝ)
    (hD : ∑ j, d j • M j = D) (hE : ∑ j, e j • M j = E)
    (hcurve : ∀ t : ℝ, (M i + t • D + t^2 • E).PosSemidef) :
    (trace (A i * D)).re = ∑ j, d j * (trace (A j * M j)).re := by
  classical
  let b (t : ℝ) (j : Fin n) : ℝ := (if j = i then 1 else 0) + t * d j + t^2 * e j
  let R (t : ℝ) (j : Fin n) : Matrix (Fin dim) (Fin dim) ℂ :=
    if j = i then M i + t • D + t^2 • E else (b t i - b t j) • M j
  have hb0 (j : Fin n) : b 0 j = if j = i then 1 else 0 := by simp [b]
  have hbc (j : Fin n) : ContinuousAt (fun t => b t j) 0 := by dsimp [b]; fun_prop
  have hbi : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < b t i := by
    exact (hbc i).eventually (Ioi_mem_nhds (by simp [hb0] : (0 : ℝ) < b 0 i))
  have hbij : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, j ≠ i → 0 < b t i - b t j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall (fun _ h => (h hj).elim)
    · have hc := (hbc i).sub (hbc j)
      exact (hc.eventually (Ioi_mem_nhds (by simp [hb0,hj] : (0 : ℝ) < b 0 i - b 0 j))).mono (fun _ h _ => h)
  have hsum (t : ℝ) : ∑ j, b t j • M j = M i + t • D + t^2 • E := by
    simp only [b,add_smul,mul_smul,Finset.sum_add_distrib,← Finset.smul_sum,
      hD,hE,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hRsum (t : ℝ) : ∑ j, R t j = b t i • (1 : Matrix (Fin dim) (Fin dim) ℂ) := by
    have hR (j : Fin n) : R t j = (b t i - b t j) • M j +
        (if j = i then M i + t • D + t^2 • E else 0) := by
      by_cases hj : j = i <;> simp [R,hj]
    simp_rw [hR]
    rw [Finset.sum_add_distrib]
    simp only [sub_smul,Finset.sum_sub_distrib,← Finset.smul_sum,hM.2,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true,hsum]
    abel
  let c (j : Fin n) : ℝ := (trace (A j * M j)).re
  let l : ℝ := (trace (A i * D)).re - ∑ j, d j * c j
  let k : ℝ := (trace (A i * E)).re - ∑ j, e j * c j
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), t*l + t^2*k ≤ 0 := by
    filter_upwards [hbi,hbij] with t hi hij
    let F : Fin n → Matrix (Fin dim) (Fin dim) ℂ := fun j => (b t i)⁻¹ • R t j
    have hF : IsPOVM F := by
      constructor
      · intro j
        apply PosSemidef.smul _ (inv_nonneg.mpr hi.le)
        by_cases hj : j = i
        · simpa [R,hj] using hcurve t
        · simpa [R,hj] using (hM.1 j).smul (hij j hj).le
      · simp only [F,← Finset.smul_sum,hRsum,smul_smul,
          inv_mul_cancel₀ hi.ne',one_smul]
    have hh := hopt F hF
    have hmul := mul_le_mul_of_nonneg_left hh hi.le
    have hf : ∑ j, (trace (A j * F j)).re = (b t i)⁻¹ *
        ∑ j, (trace (A j * R t j)).re := by
      simp only [F,mul_smul_comm,trace_smul,Complex.real_smul,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Finset.mul_sum]
    rw [hf,← mul_assoc,mul_inv_cancel₀ hi.ne',one_mul] at hmul
    have hval : ∑ j, (trace (A j * R t j)).re - b t i * ∑ j, c j = t*l+t^2*k := by
      have hr (j : Fin n) : (trace (A j * R t j)).re =
          (b t i - b t j)*c j +
          (if j = i then (trace (A i * (M i+t • D+t^2 • E))).re else 0) := by
        by_cases hj : j = i
        · simp [R,hj]
        · simp only [R,if_neg hj,mul_smul_comm,trace_smul,Complex.real_smul,
            Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,c]
          simp
      simp_rw [hr]
      simp only [Finset.sum_add_distrib,sub_mul,Finset.sum_sub_distrib,
        ← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      simp only [b,add_mul,Finset.sum_add_distrib,ite_mul,one_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true,
        mul_add,mul_smul_comm,trace_add,trace_smul,Complex.add_re,Complex.real_smul,
        Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,c,l,k]
      simp only [mul_assoc,← Finset.mul_sum]
      ring
    rw [← hval]
    change _ ≤ b t i * ∑ j, c j at hmul
    linarith
  have hmax : IsLocalMax (fun t : ℝ => t*l+t^2*k) 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), t*l+t^2*k ≤ 0*l+0^2*k
    simpa only [zero_mul,zero_pow (by decide : 2 ≠ 0),add_zero] using ht
  have hd : HasDerivAt (fun t : ℝ => t*l+t^2*k) l 0 := by
    have hd1 : HasDerivAt (fun t : ℝ => t*l) l 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const l
    have hd2 : HasDerivAt (fun t : ℝ => t^2*k) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const k
    convert hd1.add hd2 using 1 <;> first | rfl | norm_num
  have hz := hmax.hasDerivAt_eq_zero hd
  dsimp [l] at hz
  exact sub_eq_zero.mp hz

end D5.S3.Quantum.Measurement.QuadraticPovmStationarity
