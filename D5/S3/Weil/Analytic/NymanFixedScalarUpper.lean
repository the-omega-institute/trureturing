/- GID: D5/S3/Weil/Analytic/NymanFixedScalarUpper
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanFixedScalarUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square-root growth of the fixed rational scalar is equivalent to RH. -/

import D5.S3.Weil.Analytic.NymanFixedRationalScalar
import D5.S3.Weil.ZetaPntBounds.MobiusShortAverage
import OmegaBuild.Commands

/-! Square-root growth of the fixed rational scalar is equivalent to RH. -/

compile_only_with_mathlib

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction Complex
open scoped ArithmeticFunction.Moebius
open NymanFixedRationalKernel NymanFixedRationalScalar
open D5.S3.Weil.ZetaPntBounds.MobiusShortAverage

namespace NymanFixedScalarUpper

/-- Positive-exponent-slack growth of the literal finite rational kernel statistic. -/
def ScalarGrowth (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ C : ℝ,0≤C ∧ ∀ N : ℕ, 0<N → |(scalar N:ℝ)|≤C*(N:ℝ)^(θ+ε)

private def mobiusPrefix (m : ℕ) : ℝ := ∑ n∈Icc 1 m,(μ n:ℝ)

private theorem prefix_succ (m : ℕ) : mobiusPrefix (m+1)=mobiusPrefix m+(μ (m+1):ℝ) := by
  unfold mobiusPrefix
  rw [sum_Icc_succ_top (by omega)]

private theorem sum_parts {r f g : ℕ→ℝ} (L : ℕ) (h0 : r 0=0)
    (hr : ∀ k<L,r (k+1)=r k+f k) :
    (∑ k∈range L,f k*g (k+1)) =
      r L*g L+∑ k∈range L,r k*(g k-g (k+1)) := by
  calc
    _ = ∑ k ∈ range L,
        ((r (k + 1) * g (k + 1) - r k * g k) + r k * (g k - g (k + 1))) := by
      apply sum_congr rfl
      intro k hk
      rw [hr k (mem_range.mp hk)]
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_range_sub (fun k => r k * g k)]
      simp [h0]

private theorem scalar_eq_range {N : ℕ} (_hN : 0<N) :
    (scalar N:ℝ)=∑ k∈range N,(μ (N+k+1):ℝ)*b (((N+k+1:ℕ):ℝ)/(N:ℝ)) := by
  unfold scalar
  push_cast
  symm
  apply sum_bij (fun k _ => N+k+1)
  · intro k hk
    have h := mem_range.mp hk
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro k hk l hl he; omega
  · intro n hn
    have h := mem_Ioc.mp hn
    exact ⟨n-N-1,mem_range.mpr (by omega),by omega⟩
  · intro k hk
    rw [bRat_cast]
    push_cast
    rfl

private theorem scalar_parts {N : ℕ} (hN : 0<N) :
    (scalar N:ℝ)=∑ k∈range N,(mobiusPrefix (N+k)-mobiusPrefix N)*
      (b (((N+k:ℕ):ℝ)/(N:ℝ))-b (((N+k+1:ℕ):ℝ)/(N:ℝ))) := by
  rw [scalar_eq_range hN]
  let r : ℕ→ℝ := fun k => mobiusPrefix (N+k)-mobiusPrefix N
  let g : ℕ→ℝ := fun k => b (((N+k:ℕ):ℝ)/(N:ℝ))
  have h0 : r 0=0 := by simp [r]
  have hr : ∀ k<N,r (k+1)=r k+(μ (N+k+1):ℝ) := by
    intro k hk
    dsimp [r]
    rw [←Nat.add_assoc,prefix_succ]
    ring
  have he := sum_parts (r:=r) (f:=fun k => (μ (N+k+1):ℝ)) (g:=g) N h0 hr
  have hg : g N=0 := by
    unfold g
    rw [show (((N+N:ℕ):ℝ)/(N:ℝ))=2 by push_cast;field_simp;norm_num]
    exact b_zero_right A4_lt_two.le
  rw [hg,mul_zero,zero_add] at he
  exact he

/-- A uniform ordinary Möbius prefix power bound implies the same power for this
specific rational scalar. -/
theorem scalar_bound_of_prefix {β D : ℝ} (hβ : 0≤β) (hD : 0≤D)
    (hp : ∀ m : ℕ, 0<m → |mobiusPrefix m|≤D*(m:ℝ)^β) :
    ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,0<N → |(scalar N:ℝ)|≤C*(N:ℝ)^β := by
  obtain ⟨K,hK,hlip⟩ := b_lipschitz
  refine ⟨2*D*(2:ℝ)^β*K,by positivity,?_⟩
  intro N hN
  have hNr : (0:ℝ)<N := by positivity
  rw [scalar_parts hN]
  have hpoint (k : ℕ) (hk : k∈range N) :
      |(mobiusPrefix (N+k)-mobiusPrefix N)*
      (b (((N+k:ℕ):ℝ)/(N:ℝ))-b (((N+k+1:ℕ):ℝ)/(N:ℝ)))|
        ≤ (2*D*(2*(N:ℝ))^β)*(K/(N:ℝ)) := by
    have hkN : k≤N := (mem_range.mp hk).le
    have hpk : |mobiusPrefix (N+k)|≤D*(2*(N:ℝ))^β := by
      apply (hp (N+k) (by omega)).trans
      apply mul_le_mul_of_nonneg_left _ hD
      exact Real.rpow_le_rpow (by positivity) (by push_cast; exact_mod_cast (show N+k≤2*N by omega)) hβ
    have hpN : |mobiusPrefix N|≤D*(2*(N:ℝ))^β := (hp N hN).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hβ) hD)
    have hres : |mobiusPrefix (N+k)-mobiusPrefix N|≤2*D*(2*(N:ℝ))^β := by
      have h := abs_sub_le (mobiusPrefix (N+k)) 0 (mobiusPrefix N)
      simp only [sub_zero,zero_sub,abs_neg] at h
      linarith
    have hdiff := hlip (((N+k:ℕ):ℝ)/(N:ℝ)) (((N+k+1:ℕ):ℝ)/(N:ℝ))
    have he : (((N+k:ℕ):ℝ)/(N:ℝ))-(((N+k+1:ℕ):ℝ)/(N:ℝ))=-(N:ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    rw [he,abs_neg,abs_of_pos (inv_pos.mpr hNr),←div_eq_mul_inv] at hdiff
    rw [abs_mul]
    exact mul_le_mul hres hdiff (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ k∈range N,|(mobiusPrefix (N+k)-mobiusPrefix N)*
      (b (((N+k:ℕ):ℝ)/(N:ℝ))-b (((N+k+1:ℕ):ℝ)/(N:ℝ)))| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le (range N) (fun k => (mobiusPrefix (N+k)-mobiusPrefix N)*
          (b (((N+k:ℕ):ℝ)/(N:ℝ))-b (((N+k+1:ℕ):ℝ)/(N:ℝ))))
    _ ≤ ∑ _k∈range N,(2*D*(2*(N:ℝ))^β)*(K/(N:ℝ)) := sum_le_sum hpoint
    _ = (N:ℝ)*((2*D*(2*(N:ℝ))^β)*(K/(N:ℝ))) := by simp
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]
                field_simp

/-- Every actual zero-free half-plane gives the exact slack power bound for the
fixed rational scalar. -/
theorem scalar_growth_of_zero_free {θ : ℝ} (hθ : 1/2≤θ) (hθ1 : θ<1)
    (hzero : ∀ s : ℂ, θ<s.re → s≠1 → riemannZeta s≠0) :
    ScalarGrowth θ := by
  intro ε hε
  obtain ⟨D,hD,hprefix⟩ := ordinary_mobius_prefix_of_zero_free hθ hθ1 hzero hε
  exact scalar_bound_of_prefix (β:=θ+ε) (by linarith) hD.le
    (by intro m hm; exact hprefix m (by omega))

private theorem scalar_bound_of_rh (hRH : RiemannHypothesis) : ScalarSquareRoot := by
  have hzero (z : ℂ) (hz : 1/2<z.re) (hne : z≠1) : riemannZeta z≠0 := by
    intro hroot
    have htriv : ¬∃ n : ℕ,z=-2*(n+1) := by
      rintro ⟨n,rfl⟩
      simp at hz
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    exact (ne_of_gt hz) (hRH z hroot htriv hne)
  exact scalar_growth_of_zero_free (by norm_num) (by norm_num) hzero

/-- RH is equivalent to square-root growth with arbitrary positive slack of
one fully explicit finite rational scalar. -/
theorem rh_iff_scalar : RiemannHypothesis ↔ ScalarSquareRoot :=
    ⟨scalar_bound_of_rh,rh_of_scalar⟩

end NymanFixedScalarUpper
