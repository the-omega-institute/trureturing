/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequencyRows
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequencyRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-row mode-frequency reindexing for the literal external J/T kernels. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource

/-! The first mode equation is proved by a genuine tail reindexing. -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows
open OriginalGaussianExternalFrequency OriginalGaussianExternalDisplacement
open OriginalGaussianExternalGeneratedSource OriginalGaussianExternalNormal
open OriginalGaussianExternalResolvent

private lemma row_summable_at (square out out' : Bool) (q : ℕ) {R z : ℂ}
    (hsmall : ‖R‖ + ‖z‖ < 1) :
    Summable (fun p : ℕ => ‖(if square then externalT out p out' q z
      else externalJ out p out' q z) * R ^ p‖) := by
  let ρ : ℝ := (1 - ‖z‖) / 2
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg R]
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρz : ‖(ρ : ℂ)‖ + ‖z‖ < 1 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    dsimp [ρ]
    linarith
  have hh := external_kernel_mode_summable out out' hsmall hρz
  have hqJ := hh.1.prod_symm.prod_factor q
  have hqT := hh.2.prod_symm.prod_factor q
  have hρq : ‖(ρ : ℂ) ^ q‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (pow_ne_zero q (by exact_mod_cast hρ.ne'))
  let A : ℕ → ℂ := fun p => if square then externalT out p out' q z
    else externalJ out p out' q z
  have hq : Summable (fun p : ℕ => ‖R ^ p * (A p) * (ρ : ℂ) ^ q‖) := by
    cases square
    · simpa [A, Bool.false_eq_true, ite_false, Prod.swap, mul_comm, mul_left_comm, mul_assoc]
        using hqJ
    · simpa [A, ite_true, Prod.swap, mul_comm, mul_left_comm, mul_assoc] using hqT
  have hq' : Summable (fun p : ℕ => ‖(ρ : ℂ) ^ q‖ * ‖R ^ p * A p‖) := by
    apply hq.congr
    intro p
    simp only [norm_mul, norm_pow]
    ring
  have hq'' := (summable_mul_left_iff hρq).mp hq'
  apply hq''.congr
  intro p
  simp only [A, norm_mul, mul_comm]

private lemma row_derivative (square out out' : Bool) (q : ℕ) {u z : ℂ}
    (hsmall : ‖u‖ + ‖z‖ < 1) :
    HasSum (fun p : ℕ => (p : ℂ) *
      (if square then externalT out p out' q z else externalJ out p out' q z) *
        u ^ (p - 1))
      (deriv (fun w : ℂ => ∑' p : ℕ,
        (if square then externalT out p out' q z else externalJ out p out' q z) * w ^ p) u) := by
  obtain ⟨R, huR, hR⟩ := exists_between (show ‖u‖ < 1 - ‖z‖ by linarith)
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg u) huR
  have hRsmall : ‖(R : ℂ)‖ + ‖z‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0] using
      (show R + ‖z‖ < 1 by linarith)
  have hRs := row_summable_at square out out' q hRsmall
  have hd (p : ℕ) : DifferentiableOn ℂ
      (fun w : ℂ => (if square then externalT out p out' q z
        else externalJ out p out' q z) * w ^ p) (Metric.ball 0 R) := by
    intro w hw
    exact ((hasDerivAt_pow p w).const_mul _).differentiableAt.differentiableWithinAt
  have hb (p : ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      ‖(if square then externalT out p out' q z else externalJ out p out' q z) * w ^ p‖ ≤
        ‖(if square then externalT out p out' q z else externalJ out p out' q z) * R ^ p‖ := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    gcongr
    exact (show ‖w‖ < R by simpa using hw).le
  have hu : u ∈ Metric.ball (0 : ℂ) R := by simpa using huR
  have h := Complex.hasSum_deriv_of_summable_norm hRs hd Metric.isOpen_ball hb hu
  simpa only [deriv_const_mul_field, deriv_pow_field, mul_assoc, mul_left_comm,
    row_summable_at] using h

private lemma weighted_row {u : ℂ} {K : ℕ → ℂ} {d B : ℂ} (a : ℂ)
    (hK : HasSum (fun p : ℕ => K p * u ^ p) B)
    (hD : HasSum (fun p : ℕ => (p : ℂ) * K p * u ^ (p - 1)) d) :
    HasSum (fun p : ℕ => ((p : ℂ) + a) * K p * u ^ p)
      (u * d + a * B) := by
  have hd := hD.mul_left u
  have hpow (p : ℕ) : u * ((p : ℂ) * K p * u ^ (p - 1)) =
      (p : ℂ) * K p * u ^ p := by
    cases p with
    | zero => simp
    | succ p => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring
  have hh := hd.congr_fun (fun p => (hpow p).symm)
  have ha := hK.mul_left a
  exact (hh.add ha).congr_fun (fun p => by ring)

private lemma frequency_row_algebra (out : Bool) {u : ℂ} {K : ℕ → ℂ} {B d C : ℂ}
    (hK : HasSum (fun p : ℕ => K p * u ^ p) B)
    (hD : HasSum (fun p : ℕ => (p : ℂ) * K p * u ^ (p - 1)) d)
    (hC : out = false → C = K 0) :
    HasSum (fun p : ℕ => modeScale out u *
      (externalParameter out p) * (K p -
        (if out then (if p = 0 then C else K (p - 1)) else K (p + 1))) * u ^ p)
      (if out then
        u * (1 - u) * d + (1 - 3 * u) / 2 * B - (1 / 2 : ℂ) * C
      else
        u * (1 - u) * d - (u + 1) / 2 * B + (1 / 2 : ℂ) * C) := by
  cases out
  · have hm := weighted_row (-1 / 2 : ℂ) hK hD
    have htail := (hasSum_nat_add_iff' 1).mpr hm
    have hnext : HasSum (fun p : ℕ => ((p : ℂ) + 1 / 2) * K (p + 1) * u ^ (p + 1))
        (u * d - B / 2 + K 0 / 2) := by
      convert htail using 1
      · ext p
        push_cast
        ring
      · simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_zero, mul_one]
        ring
    have hhalf := weighted_row (1 / 2 : ℂ) hK hD
    have hh := hnext.sub (hhalf.mul_left u)
    convert hh using 1
    · ext p
      simp only [modeScale, Bool.false_eq_true, ite_false, externalParameter,
        pow_succ]
      ring
    · simp only [Bool.false_eq_true, ite_false]
      rw [hC rfl]
      ring
  · have hthree := weighted_row (3 / 2 : ℂ) hK hD
    have hnext : HasSum (fun p : ℕ => ((p : ℂ) + 3 / 2) * K p * u ^ (p + 1))
        (u * (u * d + 3 / 2 * B)) := by
      convert hthree.mul_left u using 1
      · ext p
        simp only [pow_succ]
        ring
    have hpre : HasSum (fun p : ℕ => ((p : ℂ) + 1 / 2) *
        (if p = 0 then C else K (p - 1)) * u ^ p)
        (C / 2 + u * (u * d + 3 / 2 * B)) := by
      apply (hasSum_nat_add_iff' 1).mp
      convert hnext using 1
      · ext p
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
          Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      · simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_zero, mul_one,
          ite_true]
        ring
    have hhalf := weighted_row (1 / 2 : ℂ) hK hD
    have hh := hhalf.sub hpre
    convert hh using 1
    · ext p
      simp only [modeScale, ite_true, one_mul, externalParameter]
      cases p with
      | zero => simp; ring
      | succ p => simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.succ_sub_one]; ring
    · simp only [ite_true]
      ring

private lemma kernel_summable (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    Summable (fun pq : ℕ × ℕ =>
      (if square then externalT out pq.1 out' pq.2 z else externalJ out pq.1 out' pq.2 z) *
        u ^ pq.1 * v ^ pq.2) := by
  have hs := external_kernel_mode_summable out out' hu hv
  cases square
  · exact (hs.1.congr (fun pq => by simp only [Bool.false_eq_true, ite_false, ite_true, norm_mul]; ring)).of_norm
  · exact (hs.2.congr (fun pq => by simp only [Bool.false_eq_true, ite_false, ite_true, norm_mul]; ring)).of_norm

private lemma column_summable (square out out' : Bool) (p : ℕ) {v z : ℂ}
    (hv : ‖v‖ + ‖z‖ < 1) :
    Summable (fun q : ℕ =>
      (if square then externalT out p out' q z else externalJ out p out' q z) * v ^ q) := by
  let ρ : ℝ := (1 - ‖z‖) / 2
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg v]
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρz : ‖(ρ : ℂ)‖ + ‖z‖ < 1 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    dsimp [ρ]
    linarith
  have hs := (kernel_summable square out out' hρz hv).prod_factor p
  have hρp : (ρ : ℂ) ^ p ≠ 0 := pow_ne_zero p (by exact_mod_cast hρ.ne')
  have hs' := hs.mul_left (((ρ : ℂ) ^ p)⁻¹)
  apply hs'.congr
  intro q
  field_simp

private lemma product_summable_of_zero_succ {f : ℕ × ℕ → ℂ}
    (h0 : Summable (fun q : ℕ => f (0, q)))
    (hs : Summable (fun pq : ℕ × ℕ => f (pq.1 + 1, pq.2))) : Summable f := by
  let a : ℕ × ℕ → ℂ := fun pq => if pq.1 = 0 then f pq else 0
  let b : ℕ × ℕ → ℂ := fun pq => if pq.1 = 0 then 0 else f pq
  have ha : Summable a := by
    have hi : Function.Injective (fun q : ℕ => (0, q)) := by
      intro q r h; exact (Prod.mk.inj h).2
    apply (hi.summable_iff (f := a) ?_).mp
    · simpa [a, Function.comp_def] using h0
    · intro pq hpq
      have hp : pq.1 ≠ 0 := by
        intro hp
        exact hpq ⟨pq.2, by ext <;> simp [hp]⟩
      simp [a, hp]
  have hb : Summable b := by
    have hi : Function.Injective (fun pq : ℕ × ℕ => (pq.1 + 1, pq.2)) := by
      intro pq rs h
      exact Prod.ext (Nat.add_right_cancel (Prod.mk.inj h).1) (Prod.mk.inj h).2
    apply (hi.summable_iff (f := b) ?_).mp
    · simpa [b, Function.comp_def] using hs
    · intro pq hpq
      have hp : pq.1 = 0 := by
        cases hp : pq.1 with
        | zero => rfl
        | succ n => exact False.elim (hpq ⟨(n, pq.2), by ext <;> simp [hp]⟩)
      simp [b, hp]
  apply (ha.add hb).congr
  intro pq
  by_cases hp : pq.1 = 0 <;> simp [a, b, hp]

private lemma frequency_product_summable (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    Summable (fun pq : ℕ × ℕ => modeScale out u *
      modeFrequency out pq.1 (fun e k =>
        if square then externalT e k out' pq.2 z else externalJ e k out' pq.2 z) *
          u ^ pq.1 * v ^ pq.2) := by
  let K : Bool → ℕ → ℕ → ℂ := fun e p q =>
    if square then externalT e p out' q z else externalJ e p out' q z
  have hK := kernel_summable square out out' hu hv
  have hD := (kernelMode_derivative square out out' hu hv).summable
  have hw (a : ℂ) : Summable (fun pq : ℕ × ℕ =>
      ((pq.1 : ℂ) + a) * K out pq.1 pq.2 * u ^ pq.1 * v ^ pq.2) := by
    have hh := (hD.mul_left u).add (hK.mul_left a)
    apply hh.congr
    intro pq
    dsimp [K]
    cases hp : pq.1 with
    | zero => cases square <;> simp [K] <;> ring
    | succ n => cases square <;> simp [K, pow_succ] <;> ring
  cases out
  · have ht := (hw (-1 / 2)).comp_injective (i := fun pq : ℕ × ℕ => (pq.1 + 1, pq.2))
      (by intro pq rs h
          exact Prod.ext (Nat.add_right_cancel (Prod.mk.inj h).1) (Prod.mk.inj h).2)
    apply (ht.sub ((hw (1 / 2)).mul_left u)).congr
    intro pq
    dsimp [modeScale, modeFrequency, externalParameter, K, predecessor]
    push_cast
    rw [pow_succ]
    ring
  · have ht : Summable (fun pq : ℕ × ℕ => ((pq.1 : ℂ) + 1 / 2) *
        (if pq.1 = 0 then K false 0 pq.2 else K true (pq.1 - 1) pq.2) *
          u ^ pq.1 * v ^ pq.2) := by
      apply product_summable_of_zero_succ
      · simpa only [K, Nat.cast_zero, zero_add, ite_true, pow_zero, mul_one, mul_assoc] using
          (column_summable square false out' 0 hv).mul_left (1 / 2 : ℂ)
      · apply ((hw (3 / 2)).mul_left u).congr
        intro pq
        simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
          Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
        ring
    apply ((hw (1 / 2)).sub ht).congr
    intro pq
    simp only [modeScale, ite_true, one_mul, modeFrequency, externalParameter]
    cases hp : pq.1 with
    | zero => cases square <;> simp [K, predecessor] <;> ring
    | succ n => cases square <;> simp [K, predecessor] <;> ring

/-- The literal external mode-frequency equation holds in each fixed second-mode row. -/
theorem external_frequency_row (square out out' : Bool) (q : ℕ) {u z : ℂ}
    (hsmall : ‖u‖ + ‖z‖ < 1) :
    let K := fun p : ℕ =>
      if square then externalT out p out' q z else externalJ out p out' q z
    let C := if square then externalT false 0 out' q z else externalJ false 0 out' q z
    HasSum (fun p : ℕ => modeScale out u * externalParameter out p *
      ((if square then externalT out p out' q z else externalJ out p out' q z) -
        (if square then externalT (predecessor out p).1 (predecessor out p).2 out' q z
          else externalJ (predecessor out p).1 (predecessor out p).2 out' q z)) * u ^ p)
      (if out then
        u * (1 - u) * deriv (fun w : ℂ => ∑' p : ℕ, K p * w ^ p) u +
          (1 - 3 * u) / 2 * (∑' p : ℕ, K p * u ^ p) - C / 2
      else
        u * (1 - u) * deriv (fun w : ℂ => ∑' p : ℕ, K p * w ^ p) u -
          (u + 1) / 2 * (∑' p : ℕ, K p * u ^ p) + C / 2) := by
  dsimp only
  let K : ℕ → ℂ := fun p : ℕ =>
    if square then externalT out p out' q z else externalJ out p out' q z
  let C : ℂ := if square then externalT false 0 out' q z else externalJ false 0 out' q z
  have hKs := row_summable_at square out out' q hsmall
  have hK : HasSum (fun p : ℕ => K p * u ^ p) (∑' p : ℕ, K p * u ^ p) := by
    exact hKs.of_norm.hasSum
  have hD := row_derivative square out out' q hsmall
  have hA := frequency_row_algebra out (K := K) hK hD (by
    intro hout
    subst out
    rfl)
  dsimp [K, C] at hA ⊢
  convert hA using 1
  · ext p
    congr 3
    cases out <;> cases p <;> rfl
  · cases square <;> ring

/-- The actual frequency difference sums to the derivative of the complete two-mode generator. -/
theorem external_frequency_generated (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    HasSum (fun pq : ℕ × ℕ => modeScale out u *
      modeFrequency out pq.1 (fun e k =>
        if square then externalT e k out' pq.2 z else externalJ e k out' pq.2 z) *
          u ^ pq.1 * v ^ pq.2)
      (if out then
        u * (1 - u) * deriv (fun w => kernelMode square out out' w v z) u +
          (1 - 3 * u) / 2 * kernelMode square out out' u v z -
          (∑' q : ℕ, (if square then externalT false 0 out' q z
            else externalJ false 0 out' q z) * v ^ q) / 2
      else
        u * (1 - u) * deriv (fun w => kernelMode square out out' w v z) u -
          (u + 1) / 2 * kernelMode square out out' u v z +
          (∑' q : ℕ, (if square then externalT false 0 out' q z
            else externalJ false 0 out' q z) * v ^ q) / 2) := by
  let K : Bool → ℕ → ℕ → ℂ := fun e p q =>
    if square then externalT e p out' q z else externalJ e p out' q z
  let A : Bool → ℕ → ℂ := fun e p => ∑' q : ℕ, K e p q * v ^ q
  have hc (e : Bool) (p : ℕ) : HasSum (fun q => K e p q * v ^ q) (A e p) :=
    (column_summable square e out' p hv).hasSum
  have hK : HasSum (fun p : ℕ => A out p * u ^ p)
      (kernelMode square out out' u v z) := by
    apply (kernel_summable square out out' hu hv).hasSum.prod_fiberwise
    intro p
    convert (hc out p).mul_right (u ^ p) using 1
    ext q
    dsimp [K]
    ring
  have hD : HasSum (fun p : ℕ => (p : ℂ) * A out p * u ^ (p - 1))
      (deriv (fun w => kernelMode square out out' w v z) u) := by
    apply (kernelMode_derivative square out out' hu hv).prod_fiberwise
    intro p
    convert (hc out p).mul_left ((p : ℂ) * u ^ (p - 1)) using 1 <;>
      (try dsimp [K]) <;> first | (ext q; ring) | ring
  have hA := frequency_row_algebra out hK hD (C := A false 0) (by
    intro h; subst out; rfl)
  have hF := (frequency_product_summable square out out' hu hv).hasSum
  have hFA : HasSum (fun p : ℕ => modeScale out u * externalParameter out p *
      (A out p - A (predecessor out p).1 (predecessor out p).2) * u ^ p)
      (∑' pq : ℕ × ℕ, modeScale out u *
        modeFrequency out pq.1 (fun e k => K e k pq.2) * u ^ pq.1 * v ^ pq.2) := by
    apply hF.prod_fiberwise
    intro p
    have hh := ((hc out p).sub (hc (predecessor out p).1
      (predecessor out p).2)).mul_left (modeScale out u * externalParameter out p * u ^ p)
    convert hh using 1 <;> (try dsimp [modeFrequency, K]) <;> first | (ext q; ring) | ring
  have heq : (fun p : ℕ => modeScale out u * externalParameter out p *
      (A out p - A (predecessor out p).1 (predecessor out p).2) * u ^ p) =
      (fun p : ℕ => modeScale out u * externalParameter out p *
        (A out p - (if out then (if p = 0 then A false 0 else A out (p - 1))
          else A out (p + 1))) * u ^ p) := by
    funext p
    cases out <;> cases p <;> rfl
  rw [heq] at hFA
  have hval := hFA.unique hA
  rw [hval] at hF
  simpa only [A, K, div_eq_mul_inv, one_mul, mul_comm] using hF

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalFrequencyRows
