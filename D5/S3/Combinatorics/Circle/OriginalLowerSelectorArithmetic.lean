/- GID: D5/S3/Combinatorics/Circle/OriginalLowerSelectorArithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/OriginalLowerSelectorArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Consumed supported-mask arithmetic and terminal-funded prepayment. -/
module
public import D5.S3.Combinatorics.Circle.SourcePrefixInventory
import all D5.S3.Combinatorics.Circle.SourcePrefixInventory

/-! Supported finite-mask crossing and exact prepayment arithmetic consumed by
OriginalLowerFirstSelector. Reflected charges select actual retained indices;
the arithmetic record is discharged from the original physical source there.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
@[expose] public section
namespace D5.S3.Combinatorics.Circle.OriginalLowerFirstSelector
open SourceWidth M5FullWordConsumer SourcePrefixInventory
open scoped BigOperators

/- The induction scans a fixed finite inventory. It returns a literal subset,
not an integer inferred to be attainable from a numerical interval. -/
private theorem fixed_support_crossing {α : Type*} [DecidableEq α]
    (S : Finset α) (v : α → ℤ) (M T : ℤ)
    (hv : ∀ j ∈ S, 0 < v j ∧ v j ≤ M)
    (hT : 0 < T) (hreach : T ≤ ∑ j ∈ S, v j) :
    ∃ J ⊆ S, T ≤ ∑ j ∈ J, v j ∧ (∑ j ∈ J, v j) ≤ T + M - 1 := by
  classical
  induction S using Finset.induction_on generalizing T with
  | empty => simp only [Finset.sum_empty] at hreach; omega
  | @insert j S hj ih =>
    have hjv := hv j (Finset.mem_insert_self _ _)
    have hSv : ∀ i ∈ S, 0 < v i ∧ v i ≤ M :=
      fun i hi => hv i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hj] at hreach
    by_cases hhit : T ≤ v j
    · refine ⟨{j}, by simp, by simpa using hhit, ?_⟩
      simpa only [Finset.sum_singleton] using (show v j ≤ T + M - 1 by omega)
    · obtain ⟨J, hJS, hlo, hhi⟩ := ih (T - v j) hSv (by omega) (by omega)
      have hjJ : j ∉ J := fun hh => hj (hJS hh)
      refine ⟨insert j J, Finset.insert_subset_insert j hJS, ?_, ?_⟩ <;>
        rw [Finset.sum_insert hjJ] <;> omega

/- All fields below are elementary numerical consequences of the actual
source, proved again at the source interface below. No selector field occurs. -/
private structure SelectorArithmetic where
  b : ℤ
  n : ℤ
  w : ℤ
  delta : ℤ
  Delta : ℤ
  q : ℤ
  tau : ℤ
  A : ℤ
  y : ℤ
  kappa : ℤ
  E : ℤ
  a0 : ℤ
  f0 : ℤ
  Q : ℤ
  b_pos : 0 < b
  delta_pos : 0 < delta
  delta_small : 2 * delta < b
  n_eq : n = b - delta
  delta_gap : Delta + 2 ≤ delta
  Delta_pos : 0 < Delta
  dw_pos : 0 < w - b
  tau_two : 2 ≤ tau
  q_room : 4 * tau ≤ q
  A_pos : 1 ≤ A
  A_le : A ≤ tau
  ceiling : 2 * (w - n) * (A - 1) < n + Delta + 1
  eta_pos : 0 < 2 * tau * (w - b) - b
  eta_small : 4 * (2 * tau * (w - b) - b) < b
  eta_delta : 2 * tau * (w - b) - b < 2 * tau * delta
  eta_source : 2 * q * (2 * tau * (w - b) - b) = 2 * tau * n - delta - (y - b)
  y_lower : b ≤ y
  y_upper : y ≤ 2 * b - 3
  y_odd : y % 2 = 1
  kappa_eq : 2 * kappa = delta - Delta
  kappa_nonneg : 0 ≤ kappa
  nk_small : n + kappa < b
  E_source : E = q * (y - b) + kappa
  E_front : E = q * b + n + kappa - a0
  E_nonneg : 0 ≤ E
  a0_pos : 0 < a0
  f0_one : 1 ≤ f0
  terminal : Q ≤ f0 * a0
  quarter : q * b < 2 * Q

/- The low-quotient crossing consumes only actual retained n and w indices.
It proves the real positive b budget alongside the reflected charge. -/
private theorem low_selection {ln lw : ℕ} (D : SelectorArithmetic)
    (Sn : Finset (Fin ln)) (Sw Slow : Finset (Fin lw))
    (top : Fin lw) (hSn : weight Sn = D.A)
    (hSlow : weight Slow = D.tau - D.A) (hsub : Slow ⊆ Sw)
    (htop : top ∈ Sw) (hwt : (2 : ℤ) ^ top.val = D.tau)
    (hlow : ∀ j ∈ Slow, 2 * (2 : ℤ) ^ j.val ≤ D.tau)
    (ell r : ℤ) (hell : 0 ≤ ell ∧ ell < D.tau)
    (hr : 0 ≤ r ∧ r < D.b) (hrem : (D.y - 1) / 2 < r) :
    ∃ (Nsel : Finset (Fin ln)) (Wsel : Finset (Fin lw)) (j rho : ℤ),
      Nsel ⊆ Sn ∧ Wsel ⊆ Sw ∧ 0 ≤ j ∧ j ≤ D.q - 1 ∧
      0 ≤ rho ∧ rho ≤ (D.y - 1) / 2 ∧
      ell * D.b + r - (j * D.b - weight Nsel * D.n - weight Wsel * D.w) = rho := by
  classical
  let M := (D.y - 1) / 2
  let eps := D.b - r
  let dw := D.w - D.b
  let eta := 2 * D.tau * dw - D.b
  have hM : 2 * M = D.y - 1 := by dsimp [M]; have ho := D.y_odd; omega
  have hMb : D.b - 1 ≤ 2 * M := by have hh := D.y_lower; omega
  have heps : 0 < eps ∧ eps ≤ M ∧ 2 * eps < D.b := by
    dsimp [eps, M]; have hh := D.y_lower; have hb := D.b_pos; omega
  have hdw : 0 < dw := D.dw_pos
  have hd : 0 < D.delta := D.delta_pos
  have heta : 0 < eta ∧ 4 * eta < D.b ∧ eta < 2 * D.tau * D.delta :=
    ⟨D.eta_pos, D.eta_small, D.eta_delta⟩
  have htdw : 2 * D.tau * dw = D.b + eta := by dsimp [eta]; ring
  have hcoeff : ∃ (Ns : Finset (Fin ln)) (Ws : Finset (Fin lw)),
      Ns ⊆ Sn ∧ Ws ⊆ Sw ∧ weight Ns ≤ D.A ∧ weight Ws ≤ D.tau ∧
      eps ≤ weight Ws * dw - weight Ns * D.delta ∧
      weight Ws * dw - weight Ns * D.delta ≤ eps + M := by
    by_cases hfirst : eps ≤ (D.tau - D.A) * dw
    · have hbnd (j : Fin lw) (hj : j ∈ Slow) :
          0 < (2 : ℤ) ^ j.val * dw ∧ (2 : ℤ) ^ j.val * dw ≤ M := by
        have hp : (0 : ℤ) < 2 ^ j.val := by positivity
        have hm := mul_le_mul_of_nonneg_right (hlow j hj) (le_of_lt hdw)
        constructor
        · exact mul_pos hp hdw
        · have hbm : eta ≤ D.b - 2 := by omega
          nlinarith only [hm, htdw, hMb, hbm]
      have hsum : (∑ j ∈ Slow, (2 : ℤ) ^ j.val * dw) = (D.tau - D.A) * dw := by
        rw [← Finset.sum_mul]; exact congrArg (· * dw) hSlow
      obtain ⟨Ws, hWs, hlo, hhi⟩ := fixed_support_crossing Slow
        (fun j => (2 : ℤ) ^ j.val * dw) M eps hbnd heps.1 (by rw [hsum]; exact hfirst)
      have hwle : weight Ws ≤ D.tau := by
        have hh := (weight_mono hWs).trans_eq hSlow
        have hA := D.A_pos
        omega
      refine ⟨∅, Ws, Finset.empty_subset _, hWs.trans hsub, ?_, hwle, ?_, ?_⟩
      · simpa [weight] using (show 0 ≤ D.A by have hh := D.A_pos; omega)
      · simpa only [← Finset.sum_mul, weight, Finset.sum_empty, zero_mul, sub_zero] using hlo
      · have hh : weight Ws * dw ≤ eps + M - 1 := by
          simpa only [Finset.sum_mul, weight] using hhi
        simpa [weight] using (show weight Ws * dw ≤ eps + M by omega)
    · by_cases hsecond : D.tau * dw ≤ eps + M
      · refine ⟨∅, {top}, Finset.empty_subset _, Finset.singleton_subset_iff.mpr htop,
          ?_, ?_, ?_, ?_⟩
        · simpa [weight] using (show 0 ≤ D.A by have hh := D.A_pos; omega)
        · simp [weight, hwt]
        · simp only [weight, Finset.sum_empty, Finset.sum_singleton, hwt, zero_mul, sub_zero]
          nlinarith only [htdw, heta.1, heps.2.2]
        · simpa only [weight, Finset.sum_empty, Finset.sum_singleton, hwt, zero_mul, sub_zero]
            using hsecond
      · have hAdw : M < D.A * dw := by
          have hs := mul_nonneg (show 0 ≤ D.tau - D.A by have hh := D.A_le; omega)
            (le_of_lt hdw)
          nlinarith only [hfirst, hsecond, hs]
        have hAdelta : D.A * D.delta ≤ M := by
          by_cases hA1 : D.A = 1
          · rw [hA1, one_mul]
            have hh := D.delta_small
            omega
          · have hA2 : 2 ≤ D.A := by have hh := D.A_pos; omega
            by_contra hbad
            have hK : 0 < D.w - D.n := by have hn := D.n_eq; dsimp [dw] at hdw; omega
            have hm := mul_nonneg (show 0 ≤ D.A - 2 by omega) (le_of_lt hK)
            have hid : D.A * (D.w - D.n) = D.A * dw + D.A * D.delta := by
              rw [D.n_eq]; dsimp [dw]; ring
            have hh := D.ceiling
            have hg := D.delta_gap
            have hn := D.n_eq
            nlinarith only [hbad, hAdw, hMb, hm, hid, hh, hg, hn]
        have hAdiff : D.A * (dw - D.delta) ≤ M := by
          by_cases hsign : dw ≤ D.delta
          · have hm := mul_nonpos_of_nonneg_of_nonpos
              (show 0 ≤ D.A by have hh := D.A_pos; omega) (by omega : dw - D.delta ≤ 0)
            omega
          · have hm := mul_nonneg (show 0 ≤ D.tau - D.A by have hh := D.A_le; omega)
              (show 0 ≤ dw - D.delta by omega)
            nlinarith only [hm, htdw, heta.2.2, hMb]
        let target := D.tau * dw - eps - M
        have htarget : 0 < target ∧ target ≤ D.A * D.delta := by
          dsimp [target]
          constructor
          · omega
          · nlinarith only [hfirst, hAdiff]
        have hnv (j : Fin ln) (hj : j ∈ Sn) :
            0 < (2 : ℤ) ^ j.val * D.delta ∧ (2 : ℤ) ^ j.val * D.delta ≤ M := by
          have hp : (0 : ℤ) < 2 ^ j.val := by positivity
          have hs : (2 : ℤ) ^ j.val ≤ D.A := by
            rw [← hSn]
            exact Finset.single_le_sum (fun (i : Fin ln) _ => (show (0 : ℤ) ≤ 2 ^ i.val by positivity)) hj
          exact ⟨mul_pos hp hd, (mul_le_mul_of_nonneg_right hs (le_of_lt hd)).trans hAdelta⟩
        have hsum : (∑ j ∈ Sn, (2 : ℤ) ^ j.val * D.delta) = D.A * D.delta := by
          rw [← Finset.sum_mul]; exact congrArg (· * D.delta) hSn
        obtain ⟨Ns, hNs, hlo, hhi⟩ := fixed_support_crossing Sn
          (fun j => (2 : ℤ) ^ j.val * D.delta) M target hnv htarget.1
          (by rw [hsum]; exact htarget.2)
        have hlos : target ≤ weight Ns * D.delta := by simpa [weight, Finset.sum_mul] using hlo
        have hhis : weight Ns * D.delta ≤ target + M - 1 := by simpa [weight, Finset.sum_mul] using hhi
        refine ⟨Ns, {top}, hNs, Finset.singleton_subset_iff.mpr htop,
          (weight_mono hNs).trans_eq hSn, by simp [weight, hwt], ?_, ?_⟩ <;>
          rw [show weight ({top} : Finset (Fin lw)) = D.tau by simp [weight, hwt]] <;>
          dsimp only [target] at hlos hhis <;> omega
  obtain ⟨Ns, Ws, hnsub, hwsub, hnle, hwle, hlo, hhi⟩ := hcoeff
  let j := ell + weight Ns + weight Ws + 1
  let rho := weight Ws * dw - weight Ns * D.delta - eps
  have hns0 := weight_nonneg Ns
  have hws0 := weight_nonneg Ws
  have hA := D.A_le
  have hq := D.q_room
  refine ⟨Ns, Ws, j, rho, hnsub, hwsub, by dsimp [j]; omega,
    by dsimp [j]; omega, by dsimp [rho]; omega, by dsimp [rho]; omega, ?_⟩
  rw [D.n_eq]
  dsimp [rho, j, eps, dw]
  ring

/- Exact ceiling prepayment. The terminal inequality, not a future-row
nonemptiness assumption, proves the selected coefficient is available. -/
private theorem high_prepayment (D : SelectorArithmetic) (ell r : ℤ)
    (hE : D.E = ell * D.b + r) (hell : D.tau ≤ ell)
    (hr : 0 ≤ r ∧ r < D.b) :
    ∃ p : ℕ, (p : ℤ) < D.f0 ∧
      0 ≤ D.E - (p : ℤ) * D.a0 ∧
      D.E - (p : ℤ) * D.a0 < (D.q - D.tau - 1) * D.b := by
  let B := (D.q - D.tau - 1) * D.b
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (by have hh := D.q_room; have ht := D.tau_two; omega) D.b_pos
  by_cases hearly : D.E < B
  · exact ⟨0, by have hh := D.f0_one; omega, by simpa using D.E_nonneg, by simpa using hearly⟩
  · let target := D.E - B + 1
    have htarget : 0 < target := by dsimp [target]; omega
    have hcast : ((target.toNat : ℕ) : ℤ) = target := Int.toNat_of_nonneg (by omega)
    have hex : ∃ p : ℕ, target ≤ (p : ℤ) * D.a0 := by
      refine ⟨target.toNat, ?_⟩
      rw [hcast]
      have hm := mul_nonneg (le_of_lt htarget) (show 0 ≤ D.a0 - 1 by have hh := D.a0_pos; omega)
      nlinarith only [hm]
    let p := Nat.find hex
    have hp := Nat.find_spec hex
    change target ≤ (p : ℤ) * D.a0 at hp
    have hp0 : p ≠ 0 := by intro he; simp [he] at hp; omega
    have hprev := Nat.find_min hex (show p - 1 < Nat.find hex by change p - 1 < p; omega)
    have hprev' : ((p : ℤ) - 1) * D.a0 < target := by
      have hc : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
      rw [hc] at hprev
      exact lt_of_not_ge hprev
    have hover : (p : ℤ) * D.a0 < target + D.a0 := by nlinarith only [hprev']
    have htargeteq : target + D.a0 = (D.tau + 1) * D.b + D.n + D.kappa + 1 := by
      dsimp [target, B]; rw [D.E_front]; ring
    have hsmall : (p : ℤ) * D.a0 < D.Q := by
      have hk := D.nk_small
      have hroom : 2 * ((D.tau + 2) * D.b) ≤ D.q * D.b := by
        have hm := mul_nonneg (show 0 ≤ D.q - 2 * (D.tau + 2) by
          have hh := D.q_room; have ht := D.tau_two; omega) (le_of_lt D.b_pos)
        nlinarith only [hm]
      nlinarith only [hover, htargeteq, hk, hroom, D.quarter]
    have hpf : (p : ℤ) < D.f0 := by
      by_contra hh
      have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hh) (le_of_lt D.a0_pos)
      nlinarith only [hm, hsmall, D.terminal]
    have ha0 : D.a0 < (D.tau + 2) * D.b := by
      have hf := D.E_front
      have hk := D.nk_small
      dsimp [B] at hearly
      nlinarith only [hearly, hf, hk]
    have hroom : 0 ≤ D.q - 2 * D.tau - 3 := by
      have hh := D.q_room; have ht := D.tau_two; omega
    have hroommul := mul_nonneg hroom (le_of_lt D.b_pos)
    refine ⟨p, hpf, ?_, ?_⟩
    · dsimp [target] at hover
      dsimp [B] at hover ⊢
      nlinarith only [hover, ha0, hroommul, D.b_pos]
    · dsimp [target] at hp
      dsimp only [B] at hp ⊢
      omega

private theorem numerical_selection {ln lw : ℕ} (D : SelectorArithmetic)
    (Sn : Finset (Fin ln)) (Sw Slow : Finset (Fin lw))
    (top : Fin lw) (hSn : weight Sn = D.A)
    (hSlow : weight Slow = D.tau - D.A) (hsub : Slow ⊆ Sw)
    (htop : top ∈ Sw) (hwt : (2 : ℤ) ^ top.val = D.tau)
    (hlow : ∀ j ∈ Slow, 2 * (2 : ℤ) ^ j.val ≤ D.tau)
    (ell r : ℤ) (hE : D.E = ell * D.b + r)
    (hell : 0 ≤ ell) (hr : 0 ≤ r ∧ r < D.b) (hrem : (D.y - 1) / 2 < r) :
    ∃ (Nsel : Finset (Fin ln)) (Wsel : Finset (Fin lw)) (j rho : ℤ) (pay : ℕ),
      Nsel ⊆ Sn ∧ Wsel ⊆ Sw ∧ 0 ≤ j ∧ j ≤ D.q - 1 ∧
      (pay : ℤ) < D.f0 ∧ 0 ≤ rho ∧ rho ≤ (D.y - 1) / 2 ∧
      D.E - (pay : ℤ) * D.a0 -
        (j * D.b - weight Nsel * D.n - weight Wsel * D.w) = rho := by
  classical
  by_cases hlowell : ell < D.tau
  · obtain ⟨Ns, Ws, j, rho, hn, hw, hj0, hjq, hr0, hrM, heq⟩ :=
      low_selection D Sn Sw Slow top hSn hSlow hsub htop hwt hlow ell r ⟨hell, hlowell⟩ hr hrem
    exact ⟨Ns, Ws, j, rho, 0, hn, hw, hj0, hjq, by have hh := D.f0_one; omega,
      hr0, hrM, by simpa [hE] using heq⟩
  · have hsy : 2 * D.tau * (D.w - D.b) - D.b < D.y - D.b := by
      have hprod := mul_nonneg (show 0 ≤ ell - D.tau by omega) (le_of_lt D.b_pos)
      have hmul : 2 * D.tau * D.b = 2 * D.tau * D.n + 2 * D.tau * D.delta := by
        rw [D.n_eq]; ring
      by_contra hbad
      have hm := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ 2 * D.q by have hq := D.q_room; have ht := D.tau_two; omega)
        (show D.y - D.b - (2 * D.tau * (D.w - D.b) - D.b) ≤ 0 by omega)
      have hgap : 0 < D.tau * D.delta := mul_pos (by have ht := D.tau_two; omega) D.delta_pos
      nlinarith only [hm, D.eta_source, D.E_source, hE, hprod, hr.1,
        D.kappa_eq, hmul, D.y_lower, D.Delta_pos, hgap]
    let M := (D.y - 1) / 2
    let star := (D.tau + 1) * D.b - D.tau * D.w
    have hM : 2 * M = D.y - 1 := by dsimp [M]; have hh := D.y_odd; omega
    have hstar : 0 < star ∧ star ≤ M ∧ D.b ≤ M + star := by
      have he : 2 * star = D.b - (2 * D.tau * (D.w - D.b) - D.b) := by dsimp [star]; ring
      have hs := D.eta_small
      have hp := D.eta_pos
      have hy := D.y_lower
      constructor
      · omega
      · constructor <;> omega
    obtain ⟨pay, hpay, hEp0, hEpB⟩ := high_prepayment D ell r hE (by omega) hr
    let Ep := D.E - (pay : ℤ) * D.a0
    let ellp := Ep / D.b
    let rp := Ep % D.b
    have hrp : 0 ≤ rp ∧ rp < D.b := ⟨Int.emod_nonneg _ (ne_of_gt D.b_pos), Int.emod_lt_of_pos _ D.b_pos⟩
    have hEp : Ep = ellp * D.b + rp := by
      dsimp [ellp, rp]
      nlinarith only [Int.emod_add_mul_ediv Ep D.b]
    have hellp : 0 ≤ ellp ∧ ellp ≤ D.q - D.tau - 2 := by
      have hdiv := Int.ediv_nonneg hEp0 (le_of_lt D.b_pos)
      have hprod : 0 ≤ (ellp - (D.q - D.tau - 1)) * D.b → False := by
        intro hp
        dsimp [Ep] at hEp
        nlinarith only [hp, hEpB, hEp, hrp.1]
      constructor
      · exact hdiv
      · by_contra hh
        exact hprod (mul_nonneg (by omega) (le_of_lt D.b_pos))
    by_cases hhit : rp ≤ M
    · refine ⟨∅, ∅, ellp, rp, pay, Finset.empty_subset _, Finset.empty_subset _,
        hellp.1, by have ht := D.tau_two; omega, hpay, hrp.1, hhit, ?_⟩
      simp only [weight, Finset.sum_empty, zero_mul, sub_zero]
      dsimp [Ep] at hEp
      omega
    · refine ⟨∅, {top}, ellp + D.tau + 1, rp - star, pay,
        Finset.empty_subset _, Finset.singleton_subset_iff.mpr htop,
        by have ht := D.tau_two; omega, by omega, hpay,
        by omega, by omega, ?_⟩
      simp only [weight, Finset.sum_empty, Finset.sum_singleton, hwt, zero_mul, sub_zero]
      dsimp [Ep] at hEp
      dsimp [star]
      nlinarith only [hEp]

end D5.S3.Combinatorics.Circle.OriginalLowerFirstSelector
