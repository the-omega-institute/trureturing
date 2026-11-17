/- GID: D5/S3/Quantum/Foundation/EffectAdditivityStability
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/EffectAdditivityStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded binary effect defects control scalar homogeneity and signed finite-family estimates. -/

/-
Binary additive defect on the actual complex effect interval yields bounded scalar
homogeneity and a signed finite positive-family estimate. Zero coefficients are
retained, so no vanishing-at-zero premise is needed. The interval bound is proved
by a supremum contraction; the signed estimate rescales positive and negative
coefficients into the effect interval.
-/

import D5.S3.Quantum.Foundation.EffectProbabilityExtension
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder CStarAlgebra
namespace D5.S3.Quantum.Foundation.EffectAdditivityStability

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def IsEffect {d : ℕ} (E : Mat d) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

theorem effect_iff_order {d : ℕ} (E : Mat d) :
    IsEffect E ↔ 0 ≤ E ∧ E ≤ 1 := by
  exact and_congr Matrix.nonneg_iff_posSemidef.symm Matrix.le_iff.symm

theorem cstar_effect_bridge {d : ℕ} (X : CStarMatrix (Fin d) (Fin d) ℂ) :
    IsEffect (CStarMatrix.ofMatrix.symm X) ↔ 0 ≤ X ∧ X ≤ 1 := by
  rw [effect_iff_order]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv h0
    · have h := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (sub_nonneg.mpr h1)
      rw [map_sub, map_one] at h
      change 0 ≤ (1 : CStarMatrix (Fin d) (Fin d) ℂ) - X at h
      exact sub_nonneg.mp h
  · rintro ⟨h0, h1⟩
    constructor
    · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm h0
    · have h := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sub_nonneg.mpr h1)
      rw [map_sub, map_one] at h
      change (0 : Mat d) ≤ 1 - CStarMatrix.ofMatrix.symm X at h
      exact sub_nonneg.mp h

theorem bounded_interval_stability (g : ℝ → ℝ) (ε M : ℝ)
    (hε : 0 ≤ ε) (h1 : g 1 = 0)
    (hb : ∀ t, 0 ≤ t → t ≤ 1 → |g t| ≤ M)
    (ha : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ 1 →
      |g (s + t) - g s - g t| ≤ ε) :
    ∀ t, 0 ≤ t → t ≤ 1 → |g t| ≤ 2 * ε := by
  let S : Set ℝ := (fun t => |g t|) '' Set.Icc (0 : ℝ) 1
  have hne : S.Nonempty := ⟨|g 0|, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  have hbd : BddAbove S := ⟨M, by
    rintro y ⟨t, ht, rfl⟩
    exact hb t ht.1 ht.2⟩
  have hsup (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |g t| ≤ sSup S :=
    le_csSup hbd ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hstep (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      |g t| ≤ sSup S / 2 + ε := by
    by_cases ht : t ≤ 1 / 2
    · have hh := abs_le.mp (ha t t ht0 ht0 (by linarith))
      have hm := abs_le.mp (hsup (t+t) (by linarith) (by linarith))
      apply abs_le.mpr
      constructor <;> linarith
    · have hu : 0 ≤ 1-t := by linarith
      have hv : 0 ≤ 2*t-1 := by linarith
      have hfirst := ha (1-t) (2*t-1) hu hv (by linarith)
      have hsecond := ha (1-t) t hu ht0 (by linarith)
      rw [show 1-t+(2*t-1) = t by ring] at hfirst
      rw [show 1-t+t = 1 by ring, h1] at hsecond
      have hh := abs_le.mp hfirst
      have hk := abs_le.mp hsecond
      have hm := abs_le.mp (hsup (2*t-1) hv (by linarith))
      apply abs_le.mpr
      constructor <;> linarith
  have hs : sSup S ≤ sSup S / 2 + ε := by
    apply csSup_le hne
    rintro y ⟨t, ht, rfl⟩
    exact hstep t ht.1 ht.2
  intro t ht0 ht1
  have hh := hsup t ht0 ht1
  linarith

theorem probability_bounds {d : ℕ} (p : Mat d → ℝ) (ε : ℝ)
    (hpos : ∀ E, IsEffect E → 0 ≤ p E)
    (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) →
      |p (E+F) - p E - p F| ≤ ε)
    (hnorm : p 1 = 1) :
    (0 ≤ p 0 ∧ p 0 ≤ ε) ∧ ∀ E, IsEffect E → 0 ≤ p E ∧ p E ≤ 1+ε := by
  have hz : IsEffect (0 : Mat d) :=
    ⟨Matrix.PosSemidef.zero, by simpa using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef)⟩
  have hzero := hadd 0 0 Matrix.PosSemidef.zero Matrix.PosSemidef.zero (by simpa using hz)
  have hpzero := hpos 0 hz
  simp only [add_zero, sub_self, zero_sub, abs_neg] at hzero
  refine ⟨⟨hpzero, (le_abs_self _).trans hzero⟩, ?_⟩
  intro E hE
  have hcomp : IsEffect (1-E) := ⟨hE.2, by simpa using hE.1⟩
  have hsum : E + (1-E) = 1 := by abel
  have hone : IsEffect (1 : Mat d) := ⟨Matrix.PosSemidef.one, by simpa using (Matrix.PosSemidef.zero : (0 : Mat d).PosSemidef)⟩
  have ha := hadd E (1-E) hE.1 hE.2 (by rw [hsum]; exact hone)
  rw [hsum, hnorm] at ha
  have hh := abs_le.mp ha
  exact ⟨hpos E hE, by linarith [hpos (1-E) hcomp]⟩

theorem effect_homogeneity {d : ℕ} (p : Mat d → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hpos : ∀ E, IsEffect E → 0 ≤ p E)
    (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) →
      |p (E+F) - p E - p F| ≤ ε)
    (hnorm : p 1 = 1) (E : Mat d) (hE : IsEffect E) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |p (t • E) - t*p E| ≤ 2*ε := by
  have hEO := (effect_iff_order E).mp hE
  have hscaled (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : IsEffect (t • E) := by
    apply (effect_iff_order _).mpr
    refine ⟨smul_nonneg h0 hEO.1, ?_⟩
    exact (smul_le_smul_of_nonneg_right h1 hEO.1).trans (by simpa using hEO.2)
  let g : ℝ → ℝ := fun t => p (t • E) - t*p E
  have hp := (probability_bounds p ε hpos hadd hnorm).2
  apply bounded_interval_stability g ε (1+ε) hε
  · simp [g]
  · intro t ht0 ht1
    have hpt := hp _ (hscaled t ht0 ht1)
    have hpE := hp E hE
    have hprod0 := mul_nonneg ht0 hpE.1
    have hprod1 : t*p E ≤ p E := mul_le_of_le_one_left hpE.1 ht1
    dsimp [g]
    apply abs_le.mpr
    constructor <;> linarith
  · intro s t hs ht hst
    have hs1 : s ≤ 1 := by linarith
    have ht1 : t ≤ 1 := by linarith
    have hab := hadd (s • E) (t • E) (hscaled s hs hs1).1
      (hscaled t ht ht1).1 (by rw [← add_smul]; exact hscaled (s+t) (by linarith) hst)
    rw [← add_smul] at hab
    change |p ((s+t) • E) - (s+t)*p E - (p (s • E)-s*p E) -
      (p (t • E)-t*p E)| ≤ ε
    convert hab using 1
    congr 1
    ring

theorem finite_sum_error {d : ℕ} (p : Mat d → ℝ) (ε : ℝ)
    (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) →
      |p (E+F) - p E - p F| ≤ ε) :
    ∀ n : ℕ, ∀ A : Fin (n+1) → Mat d,
      (∀ i, (A i).PosSemidef) → IsEffect (∑ i, A i) →
      |p (∑ i, A i) - ∑ i, p (A i)| ≤ (n : ℝ)*ε := by
  intro n
  induction n with
  | zero => intro A _ _; simp
  | succ n ih =>
    intro A hA htotal
    let B : Fin (n+1) → Mat d := fun i => A i.succ
    have hB0 : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => (hA i.succ).nonneg
    have ht : A 0 + ∑ i, B i = ∑ i, A i := (Fin.sum_univ_succ A).symm
    have hB : IsEffect (∑ i, B i) := by
      apply (effect_iff_order _).mpr
      refine ⟨hB0, ?_⟩
      have hh : (∑ i, B i) ≤ A 0 + ∑ i, B i :=
        le_add_of_nonneg_left (hA 0).nonneg
      rw [ht] at hh
      exact hh.trans ((effect_iff_order _).mp htotal).2
    have hrec := ih B (fun i => hA i.succ) hB
    have hbin := hadd (A 0) (∑ i, B i) (hA 0)
      (Matrix.nonneg_iff_posSemidef.mp hB0) (by rw [ht]; exact htotal)
    rw [ht] at hbin
    rw [Fin.sum_univ_succ (fun i => p (A i))]
    have hr := abs_le.mp hrec
    have hb := abs_le.mp hbin
    apply abs_le.mpr
    push_cast
    constructor <;> dsimp [B] at * <;> linarith

theorem weighted_finite_sum_error {d n : ℕ} (p : Mat d → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hpos : ∀ E, IsEffect E → 0 ≤ p E)
    (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) →
      |p (E+F)-p E-p F| ≤ ε)
    (hnorm : p 1 = 1)
    (B : Fin (n+1) → Mat d) (t : Fin (n+1) → ℝ)
    (hB : ∀ i, IsEffect (B i)) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1)
    (hS : IsEffect (∑ i, t i • B i)) :
    |p (∑ i, t i • B i) - ∑ i, t i * p (B i)| ≤
      (3 * ((n : ℝ)+1)-1) * ε := by
  have hs := finite_sum_error p ε hadd n (fun i => t i • B i)
    (fun i => (hB i).1.smul (ht i).1) hS
  have hlin : |(∑ i, p (t i • B i)) - ∑ i, t i * p (B i)| ≤
      ((n : ℝ)+1) * (2*ε) := by
    calc
      _ = |∑ i, (p (t i • B i) - t i * p (B i))| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, |p (t i • B i) - t i * p (B i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (n+1), 2*ε := Finset.sum_le_sum (fun i _ =>
        effect_homogeneity p ε hε hpos hadd hnorm (B i) (hB i) (t i) (ht i).1 (ht i).2)
      _ = ((n : ℝ)+1) * (2*ε) := by simp
  calc
    _ ≤ |p (∑ i, t i • B i) - ∑ i, p (t i • B i)| +
        |(∑ i, p (t i • B i)) - ∑ i, t i * p (B i)| := abs_sub_le _ _ _
    _ ≤ (n : ℝ)*ε + ((n : ℝ)+1)*(2*ε) := add_le_add hs hlin
    _ = (3*((n : ℝ)+1)-1)*ε := by ring

theorem weighted_fintype_error {d : ℕ} {I : Type*} [Fintype I] [Nonempty I]
    (p : Mat d → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hpos : ∀ E, IsEffect E → 0 ≤ p E)
    (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) →
      |p (E+F)-p E-p F| ≤ ε)
    (hnorm : p 1 = 1) (B : I → Mat d) (t : I → ℝ)
    (hB : ∀ i, IsEffect (B i)) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1)
    (hS : IsEffect (∑ i, t i • B i)) :
    |p (∑ i, t i • B i) - ∑ i, t i * p (B i)| ≤
      (3 * (Fintype.card I : ℝ)-1) * ε := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := I))
  let e : Fin (n+1) ≃ I := ((Fintype.equivFin I).trans (finCongr hn)).symm
  have hs : (∑ j, t (e j) • B (e j)) = ∑ i, t i • B i := e.sum_comp (fun i => t i • B i)
  have hp : (∑ j, t (e j) * p (B (e j))) = ∑ i, t i * p (B i) := e.sum_comp (fun i => t i * p (B i))
  have hw := weighted_finite_sum_error p ε hε hpos hadd hnorm
    (fun j => B (e j)) (fun j => t (e j)) (fun j => hB (e j))
    (fun j => ht (e j)) (by rw [hs]; exact hS)
  rw [hs, hp] at hw
  simpa only [hn, Nat.cast_succ] using hw

theorem finite_positive_family_error {d : ℕ} {I : Type*} [Fintype I] [Nonempty I]
    (p : Mat d → ℝ) (ε K : ℝ) (hε : 0 ≤ ε) (hK : 1 ≤ K)
    (hpos : ∀ E, IsEffect E → 0 ≤ p E)
    (hadd : ∀ E F, E.PosSemidef → F.PosSemidef → IsEffect (E+F) →
      |p (E+F)-p E-p F| ≤ ε)
    (hnorm : p 1 = 1) (B : I → Mat d) (c : I → ℝ)
    (hB : ∀ i, IsEffect (B i))
    (hBsum : (∑ i, B i) ≤ K • (1 : Mat d))
    (hc : ∀ i, |c i| ≤ K) (E : Mat d) (hE : IsEffect E)
    (hrepr : E = ∑ i, c i • B i) :
    |p E - ∑ i, c i * p (B i)| ≤
      K^2 * (6 * (Fintype.card I : ℝ)+1) * ε := by
  classical
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKsq : 0 < K^2 := sq_pos_of_pos hKpos
  let s : ℝ := (K^2)⁻¹
  have hs0 : 0 ≤ s := (inv_pos.mpr hKsq).le
  have hcancel : s * K^2 = 1 := inv_mul_cancel₀ (ne_of_gt hKsq)
  have hcancel' : K^2 * s = 1 := by rw [mul_comm]; exact hcancel
  have hs1 : s ≤ 1 := by
    have hKK : 1 ≤ K^2 := by nlinarith
    exact (inv_le_one₀ hKsq).mpr hKK
  have hsK1 : s*K ≤ 1 := by
    calc
      s*K ≤ s*K^2 := mul_le_mul_of_nonneg_left (by nlinarith) hs0
      _ = 1 := hcancel
  have hfamily (w : I → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ K) :
      (∀ i, 0 ≤ s*w i ∧ s*w i ≤ 1) ∧ IsEffect (∑ i, (s*w i) • B i) := by
    have ht (i : I) : 0 ≤ s*w i ∧ s*w i ≤ s*K :=
      ⟨mul_nonneg hs0 (hw i).1, mul_le_mul_of_nonneg_left (hw i).2 hs0⟩
    refine ⟨fun i => ⟨(ht i).1, (ht i).2.trans hsK1⟩, ?_⟩
    apply (effect_iff_order _).mpr
    constructor
    · exact Finset.sum_nonneg fun i _ => smul_nonneg (ht i).1 (hB i).1.nonneg
    · calc
        (∑ i, (s*w i) • B i) ≤ ∑ i, (s*K) • B i :=
          Finset.sum_le_sum fun i _ => smul_le_smul_of_nonneg_right (ht i).2 (hB i).1.nonneg
        _ = (s*K) • ∑ i, B i := Finset.smul_sum.symm
        _ ≤ (s*K) • (K • (1 : Mat d)) :=
          smul_le_smul_of_nonneg_left hBsum (mul_nonneg hs0 hKpos.le)
        _ = 1 := by
          rw [smul_smul, show s*K*K = 1 by nlinarith [hcancel], one_smul]
  have hplus (i : I) : 0 ≤ max (c i) 0 ∧ max (c i) 0 ≤ K :=
    ⟨le_max_right _ _, max_le (abs_le.mp (hc i)).2 hKpos.le⟩
  have hminus (i : I) : 0 ≤ max (-c i) 0 ∧ max (-c i) 0 ≤ K :=
    ⟨le_max_right _ _, max_le (by linarith [(abs_le.mp (hc i)).1]) hKpos.le⟩
  have hmax (x : ℝ) : max x 0 - max (-x) 0 = x := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
      ring
  let X : Mat d := ∑ i, (s*max (c i) 0) • B i
  let Y : Mat d := ∑ i, (s*max (-c i) 0) • B i
  let P : ℝ := ∑ i, s*max (c i) 0 * p (B i)
  let Q : ℝ := ∑ i, s*max (-c i) 0 * p (B i)
  let L : ℝ := ∑ i, c i * p (B i)
  have hX := hfamily (fun i => max (c i) 0) hplus
  have hY := hfamily (fun i => max (-c i) 0) hminus
  have hXY : X - Y = s • E := by
    dsimp [X, Y]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_smul, ← mul_sub, hmax, mul_smul]
    rw [← Finset.smul_sum, ← hrepr]
  have hsum : Y + s • E = X := by
    rw [← hXY]
    abel
  have hPQ : P - Q = s*L := by
    dsimp [P, Q, L]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← sub_mul, ← mul_sub, hmax]
    ring
  have hSE : IsEffect (s • E) := by
    apply (effect_iff_order _).mpr
    refine ⟨smul_nonneg hs0 hE.1.nonneg, ?_⟩
    exact (smul_le_smul_of_nonneg_right hs1 hE.1.nonneg).trans
      (by simpa using ((effect_iff_order E).mp hE).2)
  have hx := weighted_fintype_error p ε hε hpos hadd hnorm B
    (fun i => s*max (c i) 0) hB hX.1 hX.2
  have hy := weighted_fintype_error p ε hε hpos hadd hnorm B
    (fun i => s*max (-c i) 0) hB hY.1 hY.2
  change |p X - P| ≤ (3*(Fintype.card I : ℝ)-1)*ε at hx
  change |p Y - Q| ≤ (3*(Fintype.card I : ℝ)-1)*ε at hy
  have hb := hadd Y (s • E) hY.2.1 hSE.1 (by rw [hsum]; exact hX.2)
  rw [hsum] at hb
  have hh := effect_homogeneity p ε hε hpos hadd hnorm E hE s hs0 hs1
  have hsmall : |s*(p E-L)| ≤ (6*(Fintype.card I : ℝ)+1)*ε := by
    have hxb := abs_le.mp hx
    have hyb := abs_le.mp hy
    have hbb := abs_le.mp hb
    have hhb := abs_le.mp hh
    rw [mul_sub, ← hPQ]
    apply abs_le.mpr
    constructor <;> linarith
  change |p E-L| ≤ K^2*(6*(Fintype.card I : ℝ)+1)*ε
  calc
    |p E-L| = K^2 * |s*(p E-L)| := by
      rw [abs_mul, abs_of_nonneg hs0, ← mul_assoc, hcancel', one_mul]
    _ ≤ K^2*((6*(Fintype.card I : ℝ)+1)*ε) :=
      mul_le_mul_of_nonneg_left hsmall (sq_nonneg K)
    _ = K^2*(6*(Fintype.card I : ℝ)+1)*ε := by ring

end D5.S3.Quantum.Foundation.EffectAdditivityStability
