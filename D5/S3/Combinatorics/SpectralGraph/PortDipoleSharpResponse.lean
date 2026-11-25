/- GID: D5/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PortDipoleSharpResponse
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Sharp zero-shift response for two fixed dipole moments of a weighted graph. -/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The zero-shift response of the unit dipole is half the voltage drop for unit current. -/

@[expose] public section

set_option autoImplicit false

open Matrix
open scoped Matrix

namespace D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A physical Laplacian. An off-diagonal entry of zero represents an absent edge. -/
structure IsWeightedLaplacian (L : Matrix V V ℝ) : Prop where
  symm : L.IsSymm
  row_sum : ∀ i, ∑ j, L i j = 0
  offdiag_nonpos : ∀ i j, i ≠ j → L i j ≤ 0

/-- The unnormalized current dipole. Each unit-dipole quadratic moment has a factor of one half. -/
def dipole (i j : V) : V → ℝ := Pi.single i 1 - Pi.single j 1

private lemma dipole_dot (i j : V) (x : V → ℝ) : dipole i j ⬝ᵥ x = x i - x j := by
  simp [dipole, sub_dotProduct]

private lemma diag_sum {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L) (i : V) :
    L i i = ∑ k ∈ Finset.univ.erase i, -L i k := by
  have h := Finset.sum_erase_add Finset.univ (L i) (Finset.mem_univ i)
  rw [hL.row_sum i] at h
  rw [Finset.sum_neg_distrib]
  linarith

omit [DecidableEq V] in
private lemma energy {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L) (x : V → ℝ) :
    2 * (x ⬝ᵥ (L *ᵥ x)) = ∑ i, ∑ j, -L i j * (x i - x j) ^ 2 := by
  have row (i : V) : ∑ j, L i j * (x i) ^ 2 = 0 := by
    rw [← Finset.sum_mul, hL.row_sum i, zero_mul]
  have col : (∑ i, ∑ j, L i j * (x j) ^ 2) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [fun i j => hL.symm.apply j i, row, Finset.sum_const_zero]
  calc
    _ = ∑ i, ∑ j, 2 * (x i * (L i j * x j)) := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
    _ = (∑ i, ∑ j, L i j * (x i) ^ 2) + (∑ i, ∑ j, L i j * (x j) ^ 2) +
        ∑ i, ∑ j, -L i j * (x i - x j) ^ 2 := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp [row, col]

omit [DecidableEq V] in
private lemma posSemidef {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L) : L.PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by simpa using hL.symm) fun x => ?_
  have hn : 0 ≤ ∑ i, ∑ j, -L i j * (x i - x j) ^ 2 := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    by_cases hij : i = j
    · simp [hij]
    · exact mul_nonneg (neg_nonneg.mpr (hL.offdiag_nonpos i j hij)) (sq_nonneg _)
  rw [← energy hL] at hn
  simp only [star_trivial]
  linarith

private lemma trial_energy {L : Matrix V V ℝ} (hs : L.IsSymm)
    (i j : V) (a b : ℝ) :
    let f := Pi.single i a - Pi.single j b
    f ⬝ᵥ (L *ᵥ f) = L i i * a ^ 2 + L j j * b ^ 2 - 2 * L i j * a * b := by
  intro f
  simp only [f, mulVec_sub, Matrix.mulVec_single, sub_dotProduct, dotProduct_sub,
    single_dotProduct, Matrix.col_apply, Pi.smul_apply, op_smul_eq_mul, hs.apply j i]
  ring

private lemma energy_comparison {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L)
    {i j : V} (hij : i ≠ j) {u f : V → ℝ} (hu : L *ᵥ u = dipole i j) :
    let R := u i - u j
    let d := f i - f j
    0 < R ∧ d ^ 2 ≤ R * (f ⬝ᵥ (L *ᵥ f)) ∧
      (d ^ 2 = R * (f ⬝ᵥ (L *ᵥ f)) → d • dipole i j = R • (L *ᵥ f)) := by
  intro R d
  have hpsd := posSemidef hL
  have hU : u ⬝ᵥ (L *ᵥ u) = R := by rw [hu, dotProduct_comm, dipole_dot]
  have hF : f ⬝ᵥ (L *ᵥ u) = d := by rw [hu, dotProduct_comm, dipole_dot]
  have hR₀ : 0 ≤ R := by simpa only [star_trivial, hU] using hpsd.dotProduct_mulVec_nonneg u
  have hR : 0 < R := by
    refine lt_of_le_of_ne hR₀ fun he => ?_
    have hz : star u ⬝ᵥ (L *ᵥ u) = 0 := by simpa only [star_trivial, hU] using he.symm
    have hh := congrFun ((hpsd.dotProduct_mulVec_zero_iff.mp hz).symm.trans hu) i
    simp [dipole, hij.symm] at hh
  let z := d • u - R • f
  have hz : z ⬝ᵥ (L *ᵥ z) = R * (R * (f ⬝ᵥ (L *ᵥ f)) - d ^ 2) := by
    simp only [z, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hL.symm.dotProduct_mulVec_comm (x := u) (y := f), hU, hF]
    ring
  refine ⟨hR, ?_, ?_⟩
  · have hn := hpsd.dotProduct_mulVec_nonneg z
    rw [star_trivial, hz] at hn
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hn hR)
  · intro he
    have hn : star z ⬝ᵥ (L *ᵥ z) = 0 := by rw [star_trivial, hz, ← he, sub_self, mul_zero]
    simpa only [z, mulVec_sub, mulVec_smul, hu, sub_eq_zero] using
      hpsd.dotProduct_mulVec_zero_iff.mp hn

private lemma terminal_moments {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L)
    {i j : V} (hij : i ≠ j) :
    let ki := L i i - L i j
    let kj := L j j - L j i
    let t := -L i j
    let y := L *ᵥ dipole i j
    let s := (Finset.univ.erase i).erase j
    let a := fun k => -L i k
    let b := fun k => -L j k
    0 ≤ ki - 2 * t ∧ 0 ≤ kj - 2 * t ∧
      (∑ k ∈ s, a k) = ki - 2 * t ∧ (∑ k ∈ s, b k) = kj - 2 * t ∧
      dipole i j ⬝ᵥ y = ki + kj ∧
      (∑ k, y k ^ 2) = ki ^ 2 + kj ^ 2 + ∑ k ∈ s, (a k - b k) ^ 2 ∧
      (∑ k ∈ s, (a k - b k) ^ 2) ≤
        (ki - 2 * t) ^ 2 + (kj - 2 * t) ^ 2 - 2 * (∑ k ∈ s, a k * b k) := by
  intro ki kj t y s a b
  have hy (k : V) : y k = L k i - L k j := by
    simp [y, dipole, mulVec_sub]
  have hjmem : j ∈ (Finset.univ : Finset V).erase i := by simp [hij.symm]
  have himem : i ∈ (Finset.univ : Finset V).erase j := by simp [hij]
  have hsplit (f : V → ℝ) : (∑ k, f k) = (∑ k ∈ s, f k) + f j + f i := by
    calc
      _ = (∑ k ∈ Finset.univ.erase i, f k) + f i :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm
      _ = _ := congrArg (· + f i) (Finset.sum_erase_add _ f hjmem).symm
  have hai : (∑ k ∈ s, a k) = ki - 2 * t := by
    have h := Finset.sum_erase_add _ a hjmem
    rw [← diag_sum hL] at h
    dsimp [s, a, ki, t] at *
    linarith
  have hbj : (∑ k ∈ s, b k) = kj - 2 * t := by
    have h := Finset.sum_erase_add _ b himem
    rw [Finset.erase_right_comm, ← diag_sum hL] at h
    dsimp [s, b, kj, t] at *
    linarith only [h, hL.symm.apply i j]
  have ha (k : V) (hk : k ∈ s) : 0 ≤ a k :=
    neg_nonneg.mpr (hL.offdiag_nonpos i k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1.symm)
  have hb (k : V) (hk : k ∈ s) : 0 ≤ b k :=
    neg_nonneg.mpr (hL.offdiag_nonpos j k (Finset.mem_erase.mp hk).1.symm)
  refine ⟨hai ▸ Finset.sum_nonneg ha, hbj ▸ Finset.sum_nonneg hb, hai, hbj, ?_, ?_, ?_⟩
  · rw [dipole_dot, hy, hy]
    dsimp [ki, kj]
    ring
  · rw [hsplit, hy i, hy j]
    have he : (∑ k ∈ s, y k ^ 2) = ∑ k ∈ s, (a k - b k) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hy, hL.symm.apply i k, hL.symm.apply j k]
      dsimp [a, b]
      ring
    rw [he]
    dsimp [ki, kj]
    ring
  · have ha₂ := Finset.sum_sq_le_sq_sum_of_nonneg ha
    have hb₂ := Finset.sum_sq_le_sq_sum_of_nonneg hb
    rw [hai] at ha₂
    rw [hbj] at hb₂
    simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    linarith only [ha₂, hb₂]

/-- The two-moment lower bound for a solution of the unit-current equation on any finite
physical weighted graph. The response at the unit dipole is half the voltage drop. -/
theorem response_lower_bound {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L)
    {i j : V} (hij : i ≠ j) {u : V → ℝ} (hu : L *ᵥ u = dipole i j)
    {p q : ℝ} (hp : 0 < p) (hq : q < 4 * p ^ 2)
    (hm₁ : dipole i j ⬝ᵥ (L *ᵥ dipole i j) = 2 * p)
    (hm₂ : (∑ k, ((L *ᵥ dipole i j) k) ^ 2) = 2 * q) :
    max (1 / p) (2 * p / (4 * p ^ 2 - q)) ≤ (u i - u j) / 2 ∧
      (p ^ 2 < q → max (1 / p) (2 * p / (4 * p ^ 2 - q)) < (u i - u j) / 2) := by
  let R := u i - u j
  let ki := L i i - L i j
  let kj := L j j - L j i
  let t := -L i j
  let s := (Finset.univ.erase i).erase j
  obtain ⟨hki, hkj, hai, _, hfirst, hsecond, htail⟩ := terminal_moments hL hij
  change 0 ≤ ki - 2 * t at hki
  change 0 ≤ kj - 2 * t at hkj
  have ht : 0 ≤ t := neg_nonneg.mpr (hL.offdiag_nonpos i j hij)
  have hs : ki + kj = 2 * p := hfirst.symm.trans hm₁
  have hd : 0 < 4 * p ^ 2 - q := sub_pos.mpr hq
  have hov : 0 ≤ ∑ k ∈ s, (-L i k) * (-L j k) := by
    refine Finset.sum_nonneg fun k hk => mul_nonneg ?_ ?_
    · exact neg_nonneg.mpr (hL.offdiag_nonpos i k
        (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1.symm)
    · exact neg_nonneg.mpr (hL.offdiag_nonpos j k (Finset.mem_erase.mp hk).1.symm)
  change (∑ k, ((L *ᵥ dipole i j) k) ^ 2) =
    ki ^ 2 + kj ^ 2 + ∑ k ∈ s, (-L i k - -L j k) ^ 2 at hsecond
  change _ ≤ (ki - 2 * t) ^ 2 + (kj - 2 * t) ^ 2 - 2 * (∑ k ∈ s, (-L i k) * (-L j k)) at htail
  have hq' : q ≤ ki ^ 2 + kj ^ 2 := by
    have hi₂ : (ki - 2 * t) ^ 2 ≤ ki ^ 2 := pow_le_pow_left₀ hki (by linarith) 2
    have hj₂ : (kj - 2 * t) ^ 2 ≤ kj ^ 2 := pow_le_pow_left₀ hkj (by linarith) 2
    linarith only [hm₂, hsecond, htail, hi₂, hj₂, hov]
  have hprod : 2 * ki * kj ≤ 4 * p ^ 2 - q := by
    nlinarith only [hq', congrArg (fun x : ℝ => x ^ 2) hs]
  have h1 : 1 / p ≤ R / 2 ∧ (1 / p = R / 2 → q = p ^ 2) := by
    obtain ⟨hR, hc, heq⟩ := energy_comparison hL hij (f := dipole i j) hu
    have hD : dipole i j i - dipole i j j = 2 := by norm_num [dipole, hij, hij.symm]
    change (dipole i j i - dipole i j j) ^ 2 ≤ R * (dipole i j ⬝ᵥ (L *ᵥ dipole i j)) at hc
    rw [hD, hm₁] at hc heq
    refine ⟨(div_le_iff₀ hp).2 (by nlinarith only [hc]), fun h => ?_⟩
    have hRp : R * p = 2 := by
      have h' := (div_eq_iff hp.ne').mp h
      linarith only [h']
    have hy : L *ᵥ dipole i j = p • dipole i j := by
      have he : (2:ℝ) • dipole i j = R • (L *ᵥ dipole i j) :=
        heq (by nlinarith only [hRp])
      funext k
      have e := congrFun he k
      simp only [Pi.smul_apply, smul_eq_mul] at e ⊢
      apply mul_left_cancel₀ hR.ne'
      calc
        _ = 2 * dipole i j k := e.symm
        _ = _ := by rw [← mul_assoc, hRp]
    have hnorm : (∑ k, (dipole i j k) ^ 2) = 2 := by
      calc
        _ = dipole i j ⬝ᵥ dipole i j := by simp only [dotProduct, pow_two]
        _ = _ := (dipole_dot i j _).trans hD
    have hsum : (∑ k, ((L *ᵥ dipole i j) k) ^ 2) = p ^ 2 * 2 := by
      simp only [hy, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hnorm]
    linarith only [hm₂, hsum]
  have h2 : 2 * p / (4 * p ^ 2 - q) < R / 2 := by
    let f : V → ℝ := Pi.single i kj - Pi.single j ki
    have hD : f i - f j = 2 * p := by simpa [f, hij, hij.symm, add_comm] using hs
    obtain ⟨hR, hcmp, heq⟩ := energy_comparison hL hij (f := f) hu
    change (f i - f j) ^ 2 ≤ R * (f ⬝ᵥ (L *ᵥ f)) at hcmp
    rw [hD] at hcmp heq
    have hE : f ⬝ᵥ (L *ᵥ f) = (2 * p) * (ki * kj) - t * (ki - kj) ^ 2 := by
      change (Pi.single i kj - Pi.single j ki) ⬝ᵥ
        (L *ᵥ (Pi.single i kj - Pi.single j ki)) = _
      rw [trial_energy hL.symm i j kj ki]
      have hdi : L i i = ki - t := by dsimp [ki, t]; ring
      have hdj : L j j = kj - t := by dsimp [kj, t]; linarith only [hL.symm.apply i j]
      rw [hdi, hdj, ← hs]
      dsimp [t]
      ring
    have hE' : f ⬝ᵥ (L *ᵥ f) ≤ p * (4 * p ^ 2 - q) := by
      rw [hE]
      nlinarith only [mul_nonneg ht (sq_nonneg (ki - kj)), mul_le_mul_of_nonneg_left hprod hp.le]
    have hmul := hcmp.trans (mul_le_mul_of_nonneg_left hE' hR.le)
    have hcancel : p * (4 * p) ≤ p * (R * (4 * p ^ 2 - q)) := by
      convert hmul using 1 <;> ring
    have hb := le_of_mul_le_mul_left hcancel hp
    apply (div_lt_iff₀ hd).2
    by_contra! hn
    have hRe : R * (4 * p ^ 2 - q) = 4 * p := le_antisymm (by linarith only [hn]) hb
    have hsat : (2 * p) ^ 2 = R * (p * (4 * p ^ 2 - q)) := by
      calc
        _ = p * (4 * p) := by ring
        _ = _ := by rw [← hRe]; ring
    have hcmp' : (2 * p) ^ 2 = R * (f ⬝ᵥ (L *ᵥ f)) :=
      le_antisymm hcmp ((mul_le_mul_of_nonneg_left hE' hR.le).trans hsat.ge)
    have hEqE : f ⬝ᵥ (L *ᵥ f) = p * (4 * p ^ 2 - q) :=
      mul_left_cancel₀ hR.ne' (hcmp'.symm.trans hsat)
    have hEqQ : q = ki ^ 2 + kj ^ 2 := by
      have hh : p * (4 * p ^ 2 - q) ≤ (2 * p) * (ki * kj) := by
        rw [← hEqE, hE]
        linarith only [mul_nonneg ht (sq_nonneg (ki - kj))]
      have hh' : 4 * p ^ 2 - q ≤ 2 * ki * kj := by
        apply le_of_mul_le_mul_left _ hp
        convert hh using 1; ring
      nlinarith only [hq', hh', congrArg (fun x : ℝ => x ^ 2) hs]
    have hdeg : 0 < ki ∧ 0 < kj := by
      have epos : 0 < f ⬝ᵥ (L *ᵥ f) := by rw [hEqE]; exact mul_pos hp hd
      have hprod_pos : 0 < (2 * p) * (ki * kj) := by
        rw [hE] at epos
        linarith only [epos, mul_nonneg ht (sq_nonneg (ki - kj))]
      have hxy : 0 < ki * kj := pos_of_mul_pos_right hprod_pos (by linarith only [hp])
      have hi : 0 ≤ ki := by linarith only [hki, ht]
      have hj : 0 ≤ kj := by linarith only [hkj, ht]
      exact ⟨pos_of_mul_pos_left hxy hj, pos_of_mul_pos_right hxy hi⟩
    have ht0 : t = 0 := by
      by_contra h
      have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
      have hi₂ : (ki - 2 * t) ^ 2 < ki ^ 2 :=
        pow_lt_pow_left₀ (by linarith only [htp]) hki (by decide : 2 ≠ 0)
      have hj₂ : (kj - 2 * t) ^ 2 ≤ kj ^ 2 := pow_le_pow_left₀ hkj (by linarith only [ht]) 2
      linarith only [hm₂, hsecond, htail, hi₂, hj₂, hov, hEqQ]
    have hoverlap : (∑ k ∈ s, (-L i k) * (-L j k)) = 0 := by
      rw [ht0] at htail
      simp only [mul_zero, sub_zero] at htail
      exact le_antisymm (by linarith only [hm₂, hsecond, htail, hEqQ]) hov
    have htrial : (2 * p) • dipole i j = R • (L *ᵥ f) :=
      heq hcmp'
    have hzero : ∀ k ∈ s, -L i k = 0 := by
      intro k hk
      have hki' : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      have hkj' : k ≠ j := (Finset.mem_erase.mp hk).1
      have hn (v : V) (hv : v ∈ s) : 0 ≤ (-L i v) * (-L j v) :=
        mul_nonneg (neg_nonneg.mpr (hL.offdiag_nonpos i v
          (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1.symm))
          (neg_nonneg.mpr (hL.offdiag_nonpos j v (Finset.mem_erase.mp hv).1.symm))
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hoverlap k hk
      have he := congrFun htrial k
      simp only [Pi.smul_apply, smul_eq_mul, dipole, Pi.sub_apply, Pi.single_eq_of_ne hki',
        Pi.single_eq_of_ne hkj', sub_self, mul_zero] at he
      have hf : (L *ᵥ f) k = 0 := (mul_eq_zero.mp he.symm).resolve_left hR.ne'
      simp only [f, mulVec_sub, mulVec_single, Pi.sub_apply, Pi.smul_apply, op_smul_eq_mul,
        Matrix.col_apply, hL.symm.apply i k, hL.symm.apply j k] at hf
      rcases mul_eq_zero.mp hz with hi | hj
      · exact hi
      · have hj' : L j k = 0 := neg_eq_zero.mp hj
        have hprod_zero : L i k * kj = 0 := by
          simpa [hj'] using hf
        simp [(mul_eq_zero.mp hprod_zero).resolve_right hdeg.2.ne']
    have hsum := Finset.sum_eq_zero hzero
    rw [hai] at hsum
    change ki - 2 * t = 0 at hsum
    rw [ht0, mul_zero, sub_zero] at hsum
    exact hdeg.1.ne' hsum
  refine ⟨max_le h1.1 h2.le, ?_⟩
  intro hq
  have h1' : 1 / p < R / 2 := lt_of_le_of_ne h1.1 fun h => hq.ne (h1.2 h).symm
  exact max_lt_iff.mpr ⟨h1', h2⟩

/-- The underlying graph retains exactly the strictly positive conductances. -/
def IsWeightedLaplacian.supportGraph {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L) :
    SimpleGraph V where
  Adj i j := i ≠ j ∧ L i j < 0
  symm := ⟨fun i j a => ⟨a.1.symm, by rw [hL.symm.apply i j]; exact a.2⟩⟩
  loopless := ⟨fun _ a => a.1 rfl⟩

/-- On the connected positive-weight support, a unit-current solution exists.
Every solution for the normalized dipole gives the same quadratic response,
equal to half the unit - current voltage drop. -/
theorem exists_current_solution {L : Matrix V V ℝ} (hL : IsWeightedLaplacian L)
    (hc : hL.supportGraph.Connected) (i j : V) :
    ∃ u : V → ℝ, L *ᵥ u = dipole i j ∧
      ∀ w : V → ℝ, L *ᵥ w = (Real.sqrt 2)⁻¹ • dipole i j →
        ((Real.sqrt 2)⁻¹ • dipole i j) ⬝ᵥ w = (u i - u j) / 2 := by
  have same_on_edges {x : V → ℝ} (hx : L *ᵥ x = 0) {a b : V}
      (h : hL.supportGraph.Adj a b) : x a = x b := by
    have hsum := energy hL x
    rw [hx, dotProduct_zero, mul_zero] at hsum
    have hn (a b : V) : 0 ≤ -L a b * (x a - x b) ^ 2 := by
      by_cases hab : a = b
      · simp [hab]
      · exact mul_nonneg (neg_nonneg.mpr (hL.offdiag_nonpos a b hab)) (sq_nonneg _)
    have hout := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => hn a b))).mp hsum.symm a (Finset.mem_univ _)
    have hin := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hn a b)).mp hout b (Finset.mem_univ _)
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp hin).resolve_left (neg_pos.mpr h.2).ne'))
  have same_on_walk {x : V → ℝ} (hx : L *ᵥ x = 0) {a b : V}
      (w : hL.supportGraph.Walk a b) : x a = x b := by
    induction w with
    | nil => rfl
    | cons h _ ih => exact (same_on_edges hx h).trans ih
  let A := L.toEuclideanLin
  have hA : A.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (by simpa using hL.symm)
  have hd : WithLp.toLp 2 (dipole i j) ∈ LinearMap.range A := by
    rw [← Submodule.orthogonal_orthogonal (LinearMap.range A), hA.orthogonal_range]
    apply (Submodule.mem_orthogonal _ _).2
    intro w hw
    have hker : L *ᵥ WithLp.ofLp w = 0 := by
      have hw' := LinearMap.mem_ker.mp hw
      exact WithLp.toLp_injective 2 (show WithLp.toLp 2 (L *ᵥ WithLp.ofLp w) = 0 from hw')
    obtain ⟨walk⟩ := hc i j
    rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial, dipole_dot,
      same_on_walk hker walk, sub_self]
  obtain ⟨u, hu⟩ := hd
  have hunit : L *ᵥ WithLp.ofLp u = dipole i j :=
    congrArg WithLp.ofLp hu
  refine ⟨WithLp.ofLp u, hunit, ?_⟩
  intro w hw
  let c := (Real.sqrt 2)⁻¹
  change L *ᵥ w = c • dipole i j at hw
  change (c • dipole i j) ⬝ᵥ w = _
  have hc₂ : c * c = (1:ℝ) / 2 := by
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    dsimp [c]
    rw [← pow_two, inv_pow, hs, one_div]
  calc
    _ = (L *ᵥ (c • WithLp.ofLp u)) ⬝ᵥ w := by rw [mulVec_smul, hunit]
    _ = (c • WithLp.ofLp u) ⬝ᵥ (L *ᵥ w) := by
      rw [dotProduct_comm, hL.symm.dotProduct_mulVec_comm]
    _ = _ := by
      rw [hw, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, hc₂, dotProduct_comm, dipole_dot]
      ring

private def fourLaplacian (t x M y : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![t + x, -t, -x, 0; -t, t + y, 0, -y; -x, 0, x + M, -M; 0, -y, -M, y + M]

private lemma four_physical {t x M y : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hM : 0 < M) (hy : 0 < y) :
    IsWeightedLaplacian (fourLaplacian t x M y) := by
  refine ⟨Matrix.IsSymm.ext ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;> simp [fourLaplacian, Fin.sum_univ_four]
    all_goals ring
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [fourLaplacian, hx.le, hM.le, hy.le]

private lemma four_connected {t x M y : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hM : 0 < M) (hy : 0 < y) :
    (four_physical ht hx hM hy).supportGraph.Connected := by
  let G := (four_physical ht hx hM hy).supportGraph
  have h02 : G.Adj 0 2 := ⟨by decide, neg_lt_zero.mpr hx⟩
  have h23 : G.Adj 2 3 := ⟨by decide, neg_lt_zero.mpr hM⟩
  have h31 : G.Adj 3 1 := ⟨by decide, neg_lt_zero.mpr hy⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun i => ?_⟩
  fin_cases i
  · exact SimpleGraph.Reachable.refl _
  · exact h02.reachable.trans (h23.reachable.trans h31.reachable)
  · exact h02.reachable
  · exact h02.reachable.trans h23.reachable

private lemma four_moments (t x M y : ℝ) :
    let L := fourLaplacian t x M y
    let d := dipole (0 : Fin 4) 1
    d ⬝ᵥ (L *ᵥ d) = x + y + 4 * t ∧
      (∑ k, ((L *ᵥ d) k) ^ 2) = (x + 2 * t) ^ 2 + (y + 2 * t) ^ 2 + x ^ 2 + y ^ 2 := by
  intro L d
  have hd : d = ![1, -1, 0, 0] := by
    funext i
    fin_cases i <;> norm_num [d, dipole, Pi.single_apply]
  have hv : L *ᵥ d = ![x + 2 * t, -(y + 2 * t), -x, y] := by
    rw [hd]
    funext i
    fin_cases i <;> norm_num [L, fourLaplacian, mulVec, dotProduct, Fin.sum_univ_four] <;> ring
  rw [hv, dipole_dot]
  constructor
  · simp; ring
  · simp [Fin.sum_univ_four]; ring

private lemma four_response {t x M y : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hM : 0 < M) (hy : 0 < y) :
    let S := 1 / x + 1 / M + 1 / y
    ∃ u : Fin 4 → ℝ, fourLaplacian t x M y *ᵥ u = dipole 0 1 ∧
      (u 0 - u 1) / 2 = S / (2 * (1 + t * S)) := by
  intro S
  let I := (1 + t * S)⁻¹
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hden : 0 < 1 + t * S := by positivity
  have hI : I + t * (S * I) = 1 := by
    calc
      _ = (1 + t * S) * I := by ring
      _ = 1 := mul_inv_cancel₀ hden.ne'
  have hleft : x * (S * I - (1 / M + 1 / y) * I) = I := by
    dsimp [S]
    field_simp [hx.ne', hM.ne', hy.ne']; ring
  have hmiddle : M * ((1 / M + 1 / y) * I - (1 / y) * I) = I := by
    field_simp [hM.ne', hy.ne']; ring
  have hright : y * ((1 / y) * I) = I := by
    field_simp [hy.ne']
  simp only [one_div] at hleft hmiddle hright
  let u : Fin 4 → ℝ := ![S * I, 0, (1 / M + 1 / y) * I, (1 / y) * I]
  refine ⟨u, ?_, ?_⟩
  · funext i
    fin_cases i <;>
      norm_num [u, fourLaplacian, mulVec, dotProduct, Fin.sum_univ_four, dipole, Pi.single_apply]
    · nlinarith only [hI, hleft]
    · nlinarith only [hI, hright]
    · nlinarith only [hleft, hmiddle]
    · nlinarith only [hmiddle, hright]
  · simp [u, I]
    field_simp [hden.ne']

/-- Responses of finite connected positive-weight graphs with the prescribed unit-dipole
moments. Vertices are labelled by a finite ordinal. -/
def responses (p q : ℝ) : Set ℝ :=
  {r | ∃ (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) (hL : IsWeightedLaplacian L)
      (i j : Fin n) (u : Fin n → ℝ),
    hL.supportGraph.Connected ∧ i ≠ j ∧ L *ᵥ u = dipole i j ∧
    dipole i j ⬝ᵥ (L *ᵥ dipole i j) = 2 * p ∧
    (∑ k, ((L *ᵥ dipole i j) k) ^ 2) = 2 * q ∧ r = (u i - u j) / 2}

private lemma endpoint_response_mem {p : ℝ} (hp : 0 < p) :
    1 / p ∈ responses p (p ^ 2) := by
  let L : Matrix (Fin 2) (Fin 2) ℝ := !![p / 2, -p / 2; -p / 2, p / 2]
  let u : Fin 2 → ℝ := ![2 / p, 0]
  let d := dipole (0 : Fin 2) 1
  have hd : d = ![1, -1] := by
    funext i
    fin_cases i <;> norm_num [d, dipole, Pi.single_apply]
  have hL : IsWeightedLaplacian L := by
    refine ⟨Matrix.IsSymm.ext ?_, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro i
      fin_cases i <;> simp [L, Fin.sum_univ_two] <;> ring
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [L] <;> linarith only [hp]
  have hconn : hL.supportGraph.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    have ha : hL.supportGraph.Adj 0 1 := ⟨by decide, by change -p / 2 < 0; linarith⟩
    refine ⟨0, fun i => ?_⟩
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · exact ha.reachable
  have hmul : L *ᵥ d = ![p, -p] := by
    rw [hd]
    funext i
    fin_cases i <;> norm_num [L, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  refine ⟨2, L, hL, 0, 1, u, hconn, by decide, ?_, ?_, ?_, ?_⟩
  · change L *ᵥ u = d
    rw [hd]
    funext i
    fin_cases i <;> norm_num [u, L, mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp [hp.ne']
  · change d ⬝ᵥ (L *ᵥ d) = _
    rw [hmul, dipole_dot]
    simp; ring
  · change (∑ k, ((L *ᵥ d) k) ^ 2) = _
    rw [hmul]
    simp [Fin.sum_univ_two]; ring
  · simp [u]; ring

private lemma approximation {t x y ε : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hy : 0 < y)
    (hε : 0 < ε) (hbase : ℝ) (hb : (1 / x + 1 / y) / (2 * (1 + t * (1 / x + 1 / y))) = hbase) :
    let M := ε⁻¹
    ∃ u : Fin 4 → ℝ, fourLaplacian t x M y *ᵥ u = dipole 0 1 ∧
      (u 0 - u 1) / 2 < hbase + ε := by
  intro M
  have hM : 0 < M := inv_pos.mpr hε
  obtain ⟨u, hu, hr⟩ := four_response ht hx hM hy
  let S := 1 / x + 1 / y
  have hS : 0 < S := by dsimp [S]; positivity
  have hS₁ : 1 ≤ 1 + t * S := by linarith only [mul_nonneg ht hS.le]
  have hS₂ : 1 ≤ 1 + t * (S + ε) := by linarith only [mul_nonneg ht (add_pos hS hε).le]
  have hd : 1 ≤ (1 + t * (S + ε)) * (1 + t * S) := one_le_mul_of_one_le_of_one_le hS₂ hS₁
  have he : 1 / x + 1 / M + 1 / y = S + ε := by simp [M, S, one_div]; ring
  change S / (2 * (1 + t * S)) = hbase at hb
  refine ⟨u, hu, ?_⟩
  rw [hr, he, ← hb]
  have hdiff : (S + ε) / (2 * (1 + t * (S + ε))) - S / (2 * (1 + t * S)) =
      ε / (2 * ((1 + t * (S + ε)) * (1 + t * S))) := by
    have h₁ : 1 + t * S ≠ 0 := by linarith
    have h₂ : 1 + t * (S + ε) ≠ 0 := by linarith
    field_simp [h₁, h₂]; ring
  have hsmall : ε / (2 * ((1 + t * (S + ε)) * (1 + t * S))) < ε := by
    apply (div_lt_iff₀ (by linarith only [hd])).2
    nlinarith only [mul_le_mul_of_nonneg_left hd hε.le, hε]
  linarith only [hdiff, hsmall]

private lemma four_approaches {p q ε : ℝ} (hp : 0 < p) (hlo : p ^ 2 < q)
    (hhi : q < 4 * p ^ 2) (hε : 0 < ε) :
    ∃ r ∈ responses p q, r < max (1 / p) (2 * p / (4 * p ^ 2 - q)) + ε := by
  let B := max (1 / p) (2 * p / (4 * p ^ 2 - q))
  have hden : 0 < 4 * p ^ 2 - q := by linarith
  have finish (t x y : ℝ) (ht : 0 ≤ t) (hx : 0 < x) (hy : 0 < y)
      (h₁ : x + y + 4 * t = 2 * p) (h₂ : (x + 2 * t) ^ 2 + (y + 2 * t) ^ 2 + x ^ 2 + y ^ 2 = 2 * q)
      (hb : (1 / x + 1 / y) / (2 * (1 + t * (1 / x + 1 / y))) = B) :
      ∃ r ∈ responses p q, r < B + ε := by
    have hM : 0 < ε⁻¹ := inv_pos.mpr hε
    obtain ⟨u, hu, hr⟩ := approximation ht hx hy hε B hb
    obtain ⟨hm₁, hm₂⟩ := four_moments t x ε⁻¹ y
    exact ⟨_, ⟨4, _, four_physical ht hx hM hy, 0, 1, u,
      four_connected ht hx hM hy, by decide, hu, hm₁.trans h₁, hm₂.trans h₂, rfl⟩, hr⟩
  by_cases hq : 2 * p ^ 2 ≤ q
  · let s := Real.sqrt (q / 2 - p ^ 2)
    have hs : s ^ 2 = q / 2 - p ^ 2 := Real.sq_sqrt (by linarith)
    have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
    have hsp : s < p := by
      have hc : s ^ 2 < p ^ 2 := by linarith only [hs, hhi]
      exact lt_of_pow_lt_pow_left₀ 2 hp.le hc
    have hx : 0 < p + s := by positivity
    have hy : 0 < p - s := sub_pos.mpr hsp
    have hm : 1 / p ≤ 2 * p / (4 * p ^ 2 - q) := by
      rw [div_le_div_iff₀ hp hden]
      nlinarith only [hq]
    refine finish 0 (p + s) (p - s) (by norm_num) hx hy ?_ ?_ ?_
    · ring
    · nlinarith only [hs]
    · rw [show B = 2 * p / (4 * p ^ 2 - q) from max_eq_right hm]
      have hxy : 2 * ((p + s) * (p - s)) = 4 * p ^ 2 - q := by nlinarith only [hs]
      simp only [zero_mul, add_zero, mul_one]
      rw [← hxy]
      field_simp [hx.ne', hy.ne']; ring
  · let s := Real.sqrt (q - p ^ 2)
    let t := (p - s) / 2
    have hs : s ^ 2 = q - p ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hlo.le)
    have hs₀ : 0 < s := Real.sqrt_pos.2 (sub_pos.mpr hlo)
    have hsp : s ≤ p := by
      by_contra! h
      have hc := pow_lt_pow_left₀ h hp.le (by decide : 2 ≠ 0)
      nlinarith only [hc, hs, lt_of_not_ge hq]
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hsp) (by norm_num)
    have hm : 2 * p / (4 * p ^ 2 - q) ≤ 1 / p := by
      rw [div_le_div_iff₀ hden hp]
      nlinarith only [lt_of_not_ge hq]
    refine finish t s s ht hs₀ hs₀ ?_ ?_ ?_
    · dsimp [t]; ring
    · dsimp [t]; nlinarith only [hs]
    · rw [show B = 1 / p from max_eq_left hm]
      have hd : 0 < 1 + t * (1 / s + 1 / s) := by positivity
      field_simp [hs₀.ne', hp.ne', hd.ne']
      dsimp [t]
      ring

/-- The exact infimum over all finite connected positive-weight graphs, without a
spectral cap. The lower bound holds in every dimension. Two or four vertices
suffice to approach it while preserving both moments. -/
theorem isGLB_responses {p q : ℝ} (hp : 0 < p) (hlo : p ^ 2 ≤ q) (hhi : q < 4 * p ^ 2) :
    IsGLB (responses p q) (max (1 / p) (2 * p / (4 * p ^ 2 - q))) := by
  constructor
  · rintro r ⟨n, L, hL, i, j, u, _, hij, hu, h₁, h₂, rfl⟩
    exact (response_lower_bound hL hij hu hp hhi h₁ h₂).1
  · intro y hy
    by_contra! h
    rcases hlo.eq_or_lt with he | hs
    · subst q
      have hm : 2 * p / (4 * p ^ 2 - p ^ 2) ≤ 1 / p := by
        have hd : 0 < 4 * p ^ 2 - p ^ 2 := by nlinarith only [sq_pos_of_pos hp]
        rw [div_le_div_iff₀ hd hp]
        nlinarith only [sq_nonneg p]
      exact (not_le_of_gt ((max_eq_left hm) ▸ h)) (hy (endpoint_response_mem hp))
    · obtain ⟨r, hr, hlt⟩ := four_approaches hp hs hhi (sub_pos.mpr h)
      exact (not_lt_of_ge (hy hr)) (by linarith only [hlt])

/-- The infimum is attained exactly at zero variance. -/
theorem infimum_mem_responses_iff {p q : ℝ} (hp : 0 < p) (hlo : p ^ 2 ≤ q)
    (hhi : q < 4 * p ^ 2) :
    max (1 / p) (2 * p / (4 * p ^ 2 - q)) ∈ responses p q ↔ q = p ^ 2 := by
  constructor
  · rintro ⟨n, L, hL, i, j, u, _, hij, hu, h₁, h₂, hr⟩
    by_contra! hn
    have hlt := (response_lower_bound hL hij hu hp hhi h₁ h₂).2 (lt_of_le_of_ne hlo hn.symm)
    exact (ne_of_lt hlt) hr
  · rintro rfl
    have hd : 0 < 4 * p ^ 2 - p ^ 2 := by nlinarith only [sq_pos_of_pos hp]
    have hm : 2 * p / (4 * p ^ 2 - p ^ 2) ≤ 1 / p := by
      rw [div_le_div_iff₀ hd hp]
      nlinarith only [sq_nonneg p]
    rw [max_eq_left hm]
    exact endpoint_response_mem hp

#print axioms response_lower_bound
#print axioms isGLB_responses
#print axioms infimum_mem_responses_iff
#print axioms exists_current_solution

end D5.S3.Combinatorics.SpectralGraph.PortDipoleSharpResponse
