/- GID: D5/S3/Observer/MetricGeometry/ArithmeticHorizon
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/ArithmeticHorizon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite autonomous prediction at one phase bounds the arithmetic horizon. -/
import D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace D5.S3.Observer.MetricGeometry.ArithmeticHorizon

/-- Distance to the nearest integer, with the quotient norm's exact normalization. -/
noncomputable def torusNorm (t : ℝ) : ℝ := ‖(t : AddCircle (1 : ℝ))‖

/-- The maximum over all positive periods up to the actual state count.
The zero-budget branch is unused by a machine with an initial state. -/
noncomputable def Psi (α : ℝ) (s : ℕ) : ℝ :=
  if hs : 1 ≤ s then
    (Finset.Icc 1 s).sup' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hs⟩⟩
      (fun p => (p : ℝ) / torusNorm (p * α))
  else 0

private theorem period_norm_pos {α : ℝ} (hα : Irrational α) {p : ℕ} (hp : 0 < p) :
    0 < torusNorm (p * α) := by
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  have he : (p : ℝ) * α = (m : ℝ) := by simpa using hm.symm
  exact (hα.natCast_mul (Nat.ne_of_gt hp)).ne_int m he

private theorem arc_parameters {ε : ℝ} (hε : 0 < ε) (hεh : ε < 1 / 2) :
    0 < Real.arcsin ε / Real.pi ∧ Real.arcsin ε / Real.pi < 1 / 6 := by
  constructor
  · exact div_pos (Real.arcsin_pos.mpr hε) Real.pi_pos
  · have hi := Real.arcsin_lt_arcsin (by linarith : -1 ≤ ε) hεh
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hs : Real.arcsin (1 / 2) = Real.pi / 6 := by
      rw [← Real.sin_pi_div_six]
      exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [hs] at hi
    exact (div_lt_iff₀ Real.pi_pos).mpr (by linarith)

private theorem arc_of_chord (z : AddCircle (1 : ℝ)) {ε : ℝ}
    (hε : 0 < ε) (hεh : ε < 1 / 2)
    (hc : ‖(z.toCircle : ℂ) - 1‖ ≤ 2 * ε) :
    ‖z‖ ≤ Real.arcsin ε / Real.pi := by
  let t : ℝ := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) z : ℝ)
  have ht : -(1 / 2 : ℝ) ≤ t ∧ t < -(1 / 2 : ℝ) + 1 :=
    (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) z).property
  have htabs : |t| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have htz : (t : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
  have hn : ‖z‖ = |t| := by
    rw [← htz]
    exact (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr (by simpa using htabs)
  have hc' : ‖Complex.exp (Complex.I * (2 * Real.pi * t : ℝ)) - 1‖ ≤ 2 * ε := by
    simpa [← htz, AddCircle.toCircle_apply_mk, Circle.coe_exp, mul_comm] using hc
  rw [Complex.norm_exp_I_mul_ofReal_sub_one] at hc'
  have hhalf : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hc'
  have habs : |Real.pi * t| = Real.pi * |t| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [habs]; nlinarith [Real.pi_pos]), habs] at hc'
  have hi := (Real.le_arcsin_iff_sin_le
    (x := Real.pi * |t|) (y := ε)
    ⟨by nlinarith [abs_nonneg t, Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    ⟨by linarith, by linarith⟩).mpr (by linarith)
  rw [hn]
  exact (le_div_iff₀ Real.pi_pos).mpr (by nlinarith)

/-- Finite small-arc accuracy prevents wrapping at every sampled multiple.
This is consumed by the actual-machine bound, never assumed by its caller. -/
private theorem multiples_stay_unwrapped (z : AddCircle (1 : ℝ))
    {a : ℝ} (ha : 0 ≤ a) (hsmall : a < 1 / 6) (K : ℕ)
    (hK : ∀ k : ℕ, k ≤ K → ‖k • z‖ ≤ a) : (K : ℝ) * ‖z‖ ≤ a := by
  let t : ℝ := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) z : ℝ)
  have ht : -(1 / 2 : ℝ) ≤ t ∧ t < -(1 / 2 : ℝ) + 1 :=
    (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) z).property
  have htz : (t : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
  have hn : ‖z‖ = |t| := by
    rw [← htz]
    apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
    simpa using abs_le.mpr (show -(1 / 2 : ℝ) ≤ t ∧ t ≤ 1 / 2 from ⟨ht.1, by linarith [ht.2]⟩)
  have hmul (k : ℕ) : (((k : ℝ) * t : ℝ) : AddCircle (1 : ℝ)) = k • z := by
    rw [← nsmul_eq_mul, AddCircle.coe_nsmul, htz]
  have go : ∀ k : ℕ, k ≤ K → (k : ℝ) * ‖z‖ ≤ a := by
    intro k
    induction k with
    | zero => intro _; simpa using ha
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hz : ‖z‖ ≤ a := by simpa using hK 1 (by omega)
      have hb : |((k + 1 : ℕ) : ℝ) * t| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), ← hn, Nat.cast_add, Nat.cast_one]
        nlinarith
      have hnorm := (AddCircle.norm_coe_eq_abs_iff 1
        (x := ((k + 1 : ℕ) : ℝ) * t) (by norm_num)).mpr (by simpa using hb)
      rw [hmul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), ← hn] at hnorm
      rw [← hnorm]
      exact hK (k + 1) hk
  exact go K le_rfl

/-- Exact strict arithmetic bound for one fixed phase and arbitrary complex readout.
Only the actual orbit's accuracy through H is assumed. -/
theorem finite_predictor_horizon {S : Type*} [Fintype S]
    (G : S → S) (h : S → ℂ) (initial : S) (x : AddCircle (1 : ℝ))
    (α ε : ℝ) (hα : Irrational α) (hε : 0 < ε) (hεh : ε < 1 / 2)
    (H : ℕ)
    (accuracy : ∀ n : ℕ, n ≤ H →
      ‖h ((G^[n]) initial) - ((x + n • (α : AddCircle (1 : ℝ))).toCircle : ℂ)‖ ≤ ε) :
    (H : ℝ) < Fintype.card S + (Real.arcsin ε / Real.pi) * Psi α (Fintype.card S) := by
  classical
  let : Nonempty S := ⟨initial⟩
  let s := Fintype.card S
  let a := Real.arcsin ε / Real.pi
  have hs : 1 ≤ s := Fintype.card_pos
  have ha := (arc_parameters hε hεh).1
  have hasmall := (arc_parameters hε hεh).2
  have hmax (p : ℕ) (hp : 1 ≤ p) (hps : p ≤ s) :
      (p : ℝ) / torusNorm (p * α) ≤ Psi α s := by
    simp only [Psi, dif_pos hs]
    exact Finset.le_sup' (s := Finset.Icc 1 s)
      (fun q : ℕ => (q : ℝ) / torusNorm (q * α)) (Finset.mem_Icc.mpr ⟨hp, hps⟩)
  have hPsi : 0 ≤ Psi α s :=
    (div_nonneg (by positivity) (le_of_lt (period_norm_pos hα (by omega : 0 < (1 : ℕ))))).trans
      (hmax 1 le_rfl hs)
  by_cases hHs : H < s
  · exact lt_of_lt_of_le (by exact_mod_cast hHs)
      (le_add_of_nonneg_right (mul_nonneg ha.le hPsi))
  obtain ⟨μ, p, hp, hμp, hperiod⟩ :=
    D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound.finite_orbit_and_readout_eventually_periodic
      G h initial
  have hμH : μ ≤ H := by dsimp [s] at hHs; omega
  let K := (H - μ) / p
  have hkp : K * p ≤ H - μ := Nat.div_mul_le_self _ _
  have hnext : H - μ < (K + 1) * p := by
    simpa [K, Nat.mul_comm] using Nat.lt_mul_div_succ (H - μ) hp
  have hread (k : ℕ) : h ((G^[μ + k * p]) initial) = h ((G^[μ]) initial) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have he := (hperiod (μ + k * p) (by omega)).2
      simpa only [Nat.succ_mul, Nat.add_assoc] using he.trans ih
  have hsample (k : ℕ) (hk : k ≤ K) : ‖k • ((p : ℝ) * α : AddCircle (1 : ℝ))‖ ≤ a := by
    have hnH : μ + k * p ≤ H := by
      have := Nat.mul_le_mul_right p hk
      omega
    let u := (x + μ • (α : AddCircle (1 : ℝ))).toCircle
    let z : AddCircle (1 : ℝ) := k • ((p : ℝ) * α : AddCircle (1 : ℝ))
    have hz : (x + (μ + k * p) • (α : AddCircle (1 : ℝ))).toCircle = u * z.toCircle := by
      have hzsmul : k • (((p : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) =
          (k * p) • (α : AddCircle (1 : ℝ)) := by
        rw [← nsmul_eq_mul, AddCircle.coe_nsmul, smul_smul]
      dsimp [u, z]
      rw [hzsmul, add_nsmul, ← add_assoc, AddCircle.toCircle_add]
    have hd : ‖(u : ℂ) * (z.toCircle : ℂ) - (u : ℂ)‖ ≤ 2 * ε := by
      have h₁ := accuracy (μ + k * p) hnH
      have h₀ := accuracy μ hμH
      rw [hread k, hz] at h₁
      have hh := norm_sub_le_norm_sub_add_norm_sub
        ((u : ℂ) * (z.toCircle : ℂ)) (h ((G^[μ]) initial)) (u : ℂ)
      rw [norm_sub_rev ((u : ℂ) * (z.toCircle : ℂ)) (h ((G^[μ]) initial))] at hh
      exact hh.trans (by simpa [two_mul] using add_le_add h₁ h₀)
    have hc : ‖(z.toCircle : ℂ) - 1‖ ≤ 2 * ε := by
      have he : (u : ℂ) * (z.toCircle : ℂ) - (u : ℂ) = (u : ℂ) * ((z.toCircle : ℂ) - 1) := by ring
      simpa only [he, norm_mul, Circle.norm_coe, one_mul] using hd
    exact arc_of_chord z hε hεh hc
  have hunwrap := multiples_stay_unwrapped (((p : ℝ) * α : ℝ) : AddCircle (1 : ℝ)) ha.le hasmall K hsample
  have hδ := period_norm_pos hα hp
  have hK : (K : ℝ) ≤ a / torusNorm (p * α) := (le_div_iff₀ hδ).mpr hunwrap
  have hH : (H : ℝ) < μ + ((K : ℝ) + 1) * p := by
    have hh : H < μ + (K + 1) * p := by omega
    exact_mod_cast hh
  have hμs : (μ : ℝ) + p ≤ s := by exact_mod_cast hμp
  have hps : p ≤ s := by dsimp [s]; omega
  have hprod := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg p)
  have hpmax := mul_le_mul_of_nonneg_left (hmax p hp hps) ha.le
  have hscale : (a / torusNorm (p * α)) * (p : ℝ) =
      a * ((p : ℝ) / torusNorm (p * α)) := by ring
  rw [hscale] at hprod
  change (H : ℝ) < (s : ℝ) + a * Psi α s
  calc
    (H : ℝ) < μ + ((K : ℝ) + 1) * p := hH
    _ = ((μ : ℝ) + p) + (K : ℝ) * p := by ring
    _ ≤ s + a * ((p : ℝ) / torusNorm (p * α)) := add_le_add hμs hprod
    _ ≤ s + a * Psi α s := add_le_add (le_refl (s : ℝ)) hpmax

end D5.S3.Observer.MetricGeometry.ArithmeticHorizon
