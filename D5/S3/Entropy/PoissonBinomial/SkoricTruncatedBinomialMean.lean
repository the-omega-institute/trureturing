/- GID: D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean
   generality: G
   mirror-B: D5/B/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Decrease of the cap-normalized truncated binomial mean. -/

/-
Škorić's Conjecture 1 (arXiv:2012.15493v2, §6.2, equation (35), journal p.966).
The integer-row, positive-cap expression is the one specified in issue #24239.

result: proof_shape: content; escape_witness: none;
admission_basis: open-problem-resolution (#24239; Proved).
Direct frozen dependencies: none (Mathlib only).

The convolution comparison for positive factorially log-concave rows proves strict
adjacent decrease before specialization to the binomial row. No distributional
extension is a separate public theorem. The source definitions are f and claim;
all other declarations are private and used by the proof of result.

Declaration classification; all direct frozen dependencies are none.
ST_succ: proof_shape: bind-only; escape_witness: none;
  consumers: TT_succ, D_identity.
TT_succ: proof_shape: bind-only; escape_witness: none;
  consumers: D_identity.
D_identity: proof_shape: bind-only; escape_witness: none;
  consumers: D_positive.
ST_pair: proof_shape: bind-only; escape_witness: none;
  consumers: D_positive.
high_pair_bij: proof_shape: bind-only; escape_witness: none;
  consumers: high_sum_dom.
ratio_chain: proof_shape: content; escape_witness: none;
  consumers: pair_step.
qratio_chain: proof_shape: content; escape_witness: none;
  consumers: endpoint_dom.
endpoint_dom: proof_shape: bind-only; escape_witness: none;
  consumers: high_pointwise.
pair_step: proof_shape: bind-only; escape_witness: none;
  consumers: inward_product.
inward_product: proof_shape: content; escape_witness: none;
  consumers: high_pointwise.
high_pointwise: proof_shape: content; escape_witness: none;
  consumers: high_sum_dom.
high_sum_dom: proof_shape: content; escape_witness: none;
  consumers: D_positive.
D_positive: proof_shape: content; escape_witness: none;
  consumers: adjacent_strict.
sum_pos: proof_shape: bind-only; escape_witness: none;
  consumers: adjacent_strict.
adjacent_strict: proof_shape: content; escape_witness: none;
  consumers: chain_nonstrict.
chain_nonstrict: proof_shape: content; escape_witness: none;
  consumers: result.
choose_fac: proof_shape: bind-only; escape_witness: none;
  consumers: result.
choose_row_pos: proof_shape: bind-only; escape_witness: none;
  consumers: result.

Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26175.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace D5.S3.Entropy.PoissonBinomial.SkoricTruncatedBinomialMean
open scoped BigOperators
noncomputable def f (x r : ℕ) : ℝ :=
  (1 / (r : ℝ)) *
    ((∑ w ∈ Finset.range (r + 1), (w : ℝ) * (Nat.choose x w : ℝ)) /
      (∑ w ∈ Finset.range (r + 1), (Nat.choose x w : ℝ)))
def claim : Prop :=
  ∀ x : ℕ, 2 ≤ x → ∀ r : ℕ, 1 ≤ r → ∀ s : ℕ, r < s → 2 * s ≤ x → f x s ≤ f x r


private theorem ST_succ (a : ℕ → ℝ) (r : ℕ) :
    (∑ skoricIndex ∈ Finset.range ((r+1)+1), a skoricIndex) = (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) + a (r+1) := by
  exact Finset.sum_range_succ a (r+1)

private theorem TT_succ (a : ℕ → ℝ) (r : ℕ) :
    (∑ skoricIndex ∈ Finset.range ((r+1)+1), (skoricIndex : ℝ) * a skoricIndex) = (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) + (r+1:ℝ) * a (r+1) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    ST_succ (fun k => (k : ℝ) * a k) r


private theorem D_identity (a : ℕ → ℝ) (r : ℕ) :
    ((r+1:ℝ) * (∑ skoricIndex ∈ Finset.range ((r+1)+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) - (r:ℝ) * (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range ((r+1)+1), (skoricIndex : ℝ) * a skoricIndex)) =
      (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) - (r+1:ℝ) * a (r+1) * (∑ j ∈ Finset.range r, (r-j:ℝ) * a j) := by
  have hsum : (∑ j ∈ Finset.range r, (r-j:ℝ) * a j) =
      (r:ℝ) * (∑ j ∈ Finset.range r, a j) - (∑ j ∈ Finset.range r, (j:ℝ) * a j) := by
    calc
      (∑ j ∈ Finset.range r, (r-j:ℝ) * a j) =
          ∑ j ∈ Finset.range r, ((r:ℝ) - (j:ℝ)) * a j := by
            apply Finset.sum_congr rfl
            intro j hj
            rfl
      _ = ∑ j ∈ Finset.range r, ((r:ℝ) * a j - (j:ℝ) * a j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [sub_mul]
      _ = (∑ j ∈ Finset.range r, (r:ℝ) * a j) -
          (∑ j ∈ Finset.range r, (j:ℝ) * a j) := by rw [Finset.sum_sub_distrib]
      _ = (r:ℝ) * (∑ j ∈ Finset.range r, a j) -
          (∑ j ∈ Finset.range r, (j:ℝ) * a j) := by rw [Finset.mul_sum]
  rw [ST_succ, TT_succ, hsum]
  simp only [Finset.sum_range_succ]
  ring


private theorem ST_pair (a : ℕ → ℝ) (r : ℕ) :
    (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) =
      ∑ i ∈ Finset.range (r+1), ∑ k ∈ Finset.range (r+1),
        (((i+k:ℕ):ℝ) / 2) * a i * a k := by
  let R := Finset.range (r+1)
  have hmul : (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) =
      ∑ i ∈ R, ∑ k ∈ R, a i * ((k:ℝ) * a k) := by
    simp only [R]
    rw [Finset.sum_mul_sum]
  have hswap :
      (∑ i ∈ R, ∑ k ∈ R, ((k:ℝ) * a i * a k)) =
      (∑ i ∈ R, ∑ k ∈ R, ((i:ℝ) * a i * a k)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hmul]
  calc
    (∑ i ∈ R, ∑ k ∈ R, a i * ((k:ℝ) * a k)) =
        ∑ i ∈ R, ∑ k ∈ R, ((k:ℝ) * a i * a k) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (1/2:ℝ) * ((∑ i ∈ R, ∑ k ∈ R, ((k:ℝ) * a i * a k)) +
          (∑ i ∈ R, ∑ k ∈ R, ((i:ℝ) * a i * a k))) := by
          rw [hswap]
          simp only [← Finset.sum_add_distrib]
          rw [Finset.mul_sum R]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum R]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = ∑ i ∈ R, ∑ k ∈ R, (((i+k:ℕ):ℝ) / 2) * a i * a k := by
          simp only [← Finset.sum_add_distrib]
          rw [Finset.mul_sum R]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum R]
          apply Finset.sum_congr rfl
          intro k hk
          push_cast
          ring


private theorem high_pair_bij (r : ℕ) (g : ℕ × ℕ → ℝ) :
    (∑ p ∈ (Finset.range (r+1) ×ˢ Finset.range (r+1)).filter
      (fun p => r+1 ≤ p.1 + p.2), g p) =
      ∑ j ∈ Finset.range r, ∑ t ∈ Finset.range (r-j),
        g (j+1+t, r-t) := by
  let D := (Finset.range r ×ˢ Finset.range r).filter (fun p => p.2 < r-p.1)
  let H := (Finset.range (r+1) ×ˢ Finset.range (r+1)).filter
      (fun p => r+1 ≤ p.1 + p.2)
  have hbij :
      (∑ p ∈ D, g (p.1 + 1 + p.2, r-p.2)) = ∑ p ∈ H, g p := by
    apply Finset.sum_bij (s := D) (t := H)
      (fun p _ => (p.1 + 1 + p.2, r-p.2))
    · intro p hp
      simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      rcases hp with ⟨⟨hp1,hp2⟩, hpt⟩
      have hp1' : p.1 < r := hp1
      have hp2' : p.2 < r := hp2
      have hp2le : p.2 ≤ r := hp2'.le
      simp only [H, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      constructor
      · constructor <;> omega
      · omega
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
      rcases hp₁ with ⟨⟨h11,h12⟩, ht1⟩
      rcases hp₂ with ⟨⟨h21,h22⟩, ht2⟩
      simp only [Prod.mk.injEq] at heq
      have hteq : p₁.2 = p₂.2 := by omega
      have hjeq : p₁.1 = p₂.1 := by omega
      exact Prod.ext hjeq hteq
    · intro p hp
      simp only [H, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      rcases hp with ⟨⟨hp1,hp2⟩, hsum⟩
      let j := p.1 + p.2 - (r+1)
      let t := r - p.2
      have hj : j < r := by dsimp [j]; omega
      have ht : t < r - j := by dsimp [j, t]; omega
      refine ⟨(j,t), ?_, ?_⟩
      · simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨hj, by omega⟩, ht⟩
      · dsimp [j, t]
        ext <;> omega
    · intro p hp
      rfl
  calc
    (∑ p ∈ H, g p) = ∑ p ∈ D, g (p.1 + 1 + p.2, r-p.2) := hbij.symm
    _ = ∑ j ∈ Finset.range r, ∑ t ∈ Finset.range (r-j),
        g (j+1+t, r-t) := by
      refine Finset.sum_finset_product' D (Finset.range r) (fun j => Finset.range (r-j))
        (f := fun j t => g (j + 1 + t, r-t)) ?_
      intro p
      simp only [D, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      constructor <;> omega


private theorem ratio_chain (a : ℕ → ℝ) (m p q : ℕ)
    (hpos : ∀ n, n ≤ m → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < m →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hpq : p ≤ q) (hqm : q + 1 ≤ m) :
    a (q+1) / a q ≤ a (p+1) / a p := by
  let R : ℕ → ℝ := fun k => a (k+1) / a k
  have hstep : ∀ k, k+1 < m → R (k+1) ≤ R k := by
    intro k hk
    have hkp : 0 < a (k+1) := hpos (k+1) (by omega)
    have hk0 : 0 < a k := hpos k (by omega)
    have hcoef : (k+1:ℝ) * (a k * a (k+2)) ≤
        (k+1:ℝ) * (a (k+1))^2 := by
      calc
        (k+1:ℝ) * (a k * a (k+2)) ≤ (k+2:ℝ) * (a k * a (k+2)) := by
          apply mul_le_mul_of_nonneg_right
          · norm_num [Nat.cast_add, Nat.cast_one]
          · exact mul_nonneg (hpos k (by omega)).le (hpos (k+2) (by omega)).le
        _ ≤ (k+1:ℝ) * (a (k+1))^2 := by
          simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc, mul_assoc, mul_left_comm, mul_comm] using
            hfac (k+1) (by omega) hk
    have hstd : a k * a (k+2) ≤ (a (k+1))^2 :=
      le_of_mul_le_mul_left hcoef (by positivity)
    dsimp [R]
    rw [div_le_div_iff₀ hkp hk0]
    simpa [Nat.add_assoc, pow_two, mul_comm, mul_left_comm, mul_assoc] using hstd
  have hchain : ∀ n, p ≤ n → n ≤ q → R n ≤ R p := by
    intro n hn
    refine Nat.le_induction (m := p) ?_ ?_ n hn
    · intro _
      exact le_rfl
    · intro k hk ih hkq
      exact (hstep k (by omega)).trans (ih (by omega))
  exact hchain q hpq (by omega)

private theorem qratio_chain (a : ℕ → ℝ) (m p q : ℕ)
    (hpos : ∀ n, n ≤ m → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < m →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hpq : p ≤ q) (hqm : q + 1 ≤ m) :
    ((q+1:ℕ):ℝ) * a (q+1) / a q ≤
      ((p+1:ℕ):ℝ) * a (p+1) / a p := by
  let Q : ℕ → ℝ := fun k => ((k+1:ℕ):ℝ) * a (k+1) / a k
  have hstep : ∀ k, k+1 < m → Q (k+1) ≤ Q k := by
    intro k hk
    have hk1 : 0 < a (k+1) := hpos (k+1) (by omega)
    have hk0 : 0 < a k := hpos k (by omega)
    dsimp [Q]
    rw [div_le_div_iff₀ hk1 hk0]
    simpa [Nat.cast_add, Nat.cast_one, pow_two, mul_assoc, mul_comm, mul_left_comm] using
      (hfac (k+1) (by omega) hk)
  have hchain : ∀ n, p ≤ n → n ≤ q → Q n ≤ Q p := by
    intro n hn
    refine Nat.le_induction (m := p) ?_ ?_ n hn
    · intro _
      exact le_rfl
    · intro k hk ih hkq
      exact (hstep k (by omega)).trans (ih (by omega))
  simpa [Q] using hchain q hpq (by omega)

private theorem endpoint_dom (a : ℕ → ℝ) (r j : ℕ)
    (hpos : ∀ n, n ≤ r+1 → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < r+1 →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hjr : j < r) :
    (r+1:ℝ) * a j * a (r+1) ≤ (j+1:ℝ) * a (j+1) * a r := by
  have h := qratio_chain a (r+1) j r hpos hfac (by omega) (by omega)
  rw [div_le_div_iff₀ (hpos r (by omega)) (hpos j (by omega))] at h
  simpa [Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm, mul_left_comm] using h

private theorem pair_step (a : ℕ → ℝ) (m p q : ℕ)
    (hpos : ∀ n, n ≤ m → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < m →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hpq : p ≤ q) (hqm : q+1 ≤ m) :
    a p * a (q+1) ≤ a (p+1) * a q := by
  have h := ratio_chain a m p q hpos hfac hpq hqm
  have hp : 0 < a p := hpos p (by omega)
  have hq : 0 < a q := hpos q (by omega)
  rw [div_le_div_iff₀ hq hp] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

private theorem inward_product (a : ℕ → ℝ) (r j i : ℕ)
    (hpos : ∀ n, n ≤ r+1 → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < r+1 →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hjr : j < r) (hji : j+1 ≤ i) (hir : i ≤ r) :
    a (j+1) * a r ≤ a i * a (r+1+j-i) := by
  have hleft : ∀ n, j+1 ≤ n → 2*n ≤ r+1+j →
      a (j+1) * a r ≤ a n * a (r+1+j-n) := by
    intro n hn
    refine Nat.le_induction (m := j+1) ?_ ?_ n hn
    · intro hbound
      have hbase : r+1+j-(j+1) = r := by omega
      rw [hbase]
    · intro k hk ih hbound
      have hkN : k+1 ≤ r+1+j := by omega
      have hstep := pair_step a (r+1) k (r+1+j-k-1) hpos hfac (by omega) (by omega)
      have hi := ih (by omega)
      calc
        a (j+1) * a r ≤ a k * a (r+1+j-k) := hi
        _ ≤ a (k+1) * a (r+1+j-k-1) := by
          have hrem : 1 ≤ r+1+j-k := Nat.le_sub_of_add_le' hkN
          have hidx : (r+1+j-k-1)+1 = r+1+j-k := Nat.sub_add_cancel hrem
          simpa only [hidx] using hstep
        _ = a (k+1) * a (r+1+j-(k+1)) := by
          rw [Nat.sub_sub]
  have hmid : 2*i ≤ r+1+j ∨ 2*(r+1+j-i) ≤ r+1+j := by omega
  rcases hmid with hmid | hmid
  · have hi := hleft i hji hmid
    exact hi
  · have hi' : j+1 ≤ r+1+j-i := by omega
    have hiu : i ≤ r+1+j := by omega
    have hi := hleft (r+1+j-i) hi' hmid
    calc
      a (j+1) * a r ≤ a (r+1+j-i) * a (r+1+j-(r+1+j-i)) := hi
      _ = a i * a (r+1+j-i) := by
        rw [Nat.sub_sub_self hiu]
        ring


private theorem high_pointwise (a : ℕ → ℝ) (r j t : ℕ)
    (hpos : ∀ n, n ≤ r+1 → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < r+1 →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hjr : j < r) (ht : t < r-j) :
    (r+1:ℝ) * a j * a (r+1) ≤
      (((r+1+j:ℕ):ℝ) / 2) * a (j+1+t) * a (r-t) := by
  have hi : j+1 ≤ j+1+t := Nat.le_add_right (j+1) t
  have hir : j+1+t ≤ r := by omega
  have hp := inward_product a r j (j+1+t) hpos hfac hjr hi hir
  have he := endpoint_dom a r j hpos hfac hjr
  have hcoef : (j+1:ℝ) ≤ ((r+1+j:ℕ):ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num)).2
    have hn : (j+1) * 2 ≤ r+1+j := by omega
    exact_mod_cast hn
  have hbase : 0 ≤ a (j+1) * a r :=
    mul_nonneg (hpos (j+1) (by omega)).le (hpos r (by omega)).le
  have hcoef' := mul_le_mul_of_nonneg_right hcoef hbase
  have hfirst : (r+1:ℝ) * a j * a (r+1) ≤
      (((r+1+j:ℕ):ℝ) / 2) * (a (j+1) * a r) := by
    exact he.trans (by simpa [mul_assoc] using hcoef')
  have hc0 : 0 ≤ ((r+1+j:ℕ):ℝ) / 2 := by positivity
  have hsecond := mul_le_mul_of_nonneg_left hp hc0
  calc
    (r+1:ℝ) * a j * a (r+1) ≤
        (((r+1+j:ℕ):ℝ) / 2) * (a (j+1) * a r) := hfirst
    _ ≤ (((r+1+j:ℕ):ℝ) / 2) * a (j+1+t) * a (r-t) := by
      have hidx : r+1+j-(j+1+t) = r-t := by omega
      simpa [hidx, mul_assoc] using hsecond

private theorem high_sum_dom (a : ℕ → ℝ) (r : ℕ)
    (hpos : ∀ n, n ≤ r+1 → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < r+1 →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    :
    (r+1:ℝ) * a (r+1) * (∑ j ∈ Finset.range r, (r-j:ℝ) * a j) ≤
      ∑ p ∈ (Finset.range (r+1) ×ˢ Finset.range (r+1)).filter
        (fun p => r+1 ≤ p.1 + p.2),
        (((p.1+p.2:ℕ):ℝ) / 2) * a p.1 * a p.2 := by
  let g : ℕ × ℕ → ℝ := fun p => (((p.1+p.2:ℕ):ℝ) / 2) * a p.1 * a p.2
  have hinner : ∀ j, j < r →
      (r-j:ℝ) * ((r+1:ℝ) * a j * a (r+1)) ≤
        ∑ t ∈ Finset.range (r-j), g (j+1+t, r-t) := by
    intro j hj
    have hs := Finset.sum_le_sum (fun t ht => by
      have hpt := high_pointwise a r j t hpos hfac hj (Finset.mem_range.mp ht)
      have htt : t < r-j := Finset.mem_range.mp ht
      have hidx : (j+1+t) + (r-t) = r+1+j := by omega
      simpa [g, hidx, mul_assoc] using hpt)
    have heq :
        (∑ t ∈ Finset.range (r-j),
          (((r+1+j:ℕ):ℝ) / 2) * a (j+1+t) * a (r-t)) =
          ∑ t ∈ Finset.range (r-j), g (j+1+t, r-t) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htt : t < r-j := Finset.mem_range.mp ht
      have hidx : (j+1+t) + (r-t) = r+1+j := by omega
      have hidxR : ((j+1+t + (r-t):ℕ):ℝ) = ((r+1+j:ℕ):ℝ) := by
        exact_mod_cast hidx
      simp only [g]
      rw [hidxR]
    calc
      (r-j:ℝ) * ((r+1:ℝ) * a j * a (r+1)) =
          ∑ t ∈ Finset.range (r-j), ((r+1:ℝ) * a j * a (r+1)) := by
            have hjle : j ≤ r := Nat.le_of_succ_le hj
            simp [Finset.sum_const, Nat.cast_sub hjle]
      _ ≤ ∑ t ∈ Finset.range (r-j),
          (((r+1+j:ℕ):ℝ) / 2) * a (j+1+t) * a (r-t) := by
            simpa [mul_assoc] using hs
      _ = ∑ t ∈ Finset.range (r-j), g (j+1+t, r-t) := heq
  have houter :
      ∑ j ∈ Finset.range r, (r-j:ℝ) * ((r+1:ℝ) * a j * a (r+1)) ≤
        ∑ j ∈ Finset.range r, ∑ t ∈ Finset.range (r-j), g (j+1+t, r-t) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hinner j (by simpa using hj)
  have hq :
      (r+1:ℝ) * a (r+1) * (∑ j ∈ Finset.range r, (r-j:ℝ) * a j) ≤
        ∑ j ∈ Finset.range r, (r-j:ℝ) * ((r+1:ℝ) * a j * a (r+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    ring_nf
    exact le_rfl
  have hbij := high_pair_bij r g
  calc
    (r+1:ℝ) * a (r+1) * (∑ j ∈ Finset.range r, (r-j:ℝ) * a j) ≤
        ∑ j ∈ Finset.range r, (r-j:ℝ) * ((r+1:ℝ) * a j * a (r+1)) := hq
    _ ≤ ∑ j ∈ Finset.range r, ∑ t ∈ Finset.range (r-j), g (j+1+t, r-t) := houter
    _ = ∑ p ∈ (Finset.range (r+1) ×ˢ Finset.range (r+1)).filter
        (fun p => r+1 ≤ p.1 + p.2), g p := hbij.symm

private theorem D_positive (a : ℕ → ℝ) (r : ℕ)
    (hpos : ∀ n, n ≤ r+1 → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < r+1 →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hr : 1 ≤ r) :
    0 < (r+1:ℝ) * (∑ skoricIndex ∈ Finset.range ((r+1)+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) - (r:ℝ) * (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range ((r+1)+1), (skoricIndex : ℝ) * a skoricIndex) := by
  let P : Finset (ℕ × ℕ) := Finset.range (r+1) ×ˢ Finset.range (r+1)
  let H : Finset (ℕ × ℕ) := P.filter (fun p => r+1 ≤ p.1 + p.2)
  let L : Finset (ℕ × ℕ) := P.filter (fun p => ¬ r+1 ≤ p.1 + p.2)
  let U : Finset (ℕ × ℕ) := {(0,1), (1,0)}
  let g : ℕ × ℕ → ℝ := fun p => (((p.1+p.2:ℕ):ℝ) / 2) * a p.1 * a p.2
  have hP : ∑ p ∈ P, g p = (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) := by
    have hp := Finset.sum_product' (Finset.range (r+1)) (Finset.range (r+1))
      (fun i k => g (i,k))
    rw [ST_pair]
    simpa [P, g] using hp
  have hhigh :
      (r+1:ℝ) * a (r+1) * (∑ j ∈ Finset.range r, (r-j:ℝ) * a j) ≤
        ∑ p ∈ H, g p := by
    simpa [H, P, g] using high_sum_dom a r hpos hfac
  have hUsub : U ⊆ L := by
    intro p hp
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [L, P] <;> omega
  have hnonneg : ∀ p ∈ L, 0 ≤ g p := by
    intro p hp
    have hpP : p ∈ P := (Finset.filter_subset _ _) hp
    simp only [P, Finset.mem_product, Finset.mem_range] at hpP
    have hpa : 0 < a p.1 := hpos p.1 (by omega)
    have hpb : 0 < a p.2 := hpos p.2 (by omega)
    dsimp [g]
    positivity
  have hlow : a 0 * a 1 ≤ ∑ p ∈ L, g p := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hUsub
      (fun p hp _ => hnonneg p hp)
    have hu : ∑ p ∈ U, g p = a 0 * a 1 := by
      simp [U, g]
      ring
    rw [← hu]
    exact hsub
  have hpart : (∑ p ∈ H, g p) + (∑ p ∈ L, g p) = ∑ p ∈ P, g p := by
    simpa [H, L] using
      (Finset.sum_filter_add_sum_filter_not P (fun p : ℕ × ℕ => r+1 ≤ p.1 + p.2) g)
  have hbound : a 0 * a 1 ≤
      (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) - (r+1:ℝ) * a (r+1) *
        (∑ j ∈ Finset.range r, (r-j:ℝ) * a j) := by
    linarith [hhigh, hlow, hpart, hP]
  have hpos01 : 0 < a 0 * a 1 := mul_pos (hpos 0 (by omega)) (hpos 1 (by omega))
  rw [D_identity]
  exact lt_of_lt_of_le hpos01 hbound

private theorem sum_pos (a : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ k, k ≤ n → 0 < a k) : 0 < (∑ skoricIndex ∈ Finset.range (n+1), a skoricIndex) := by
  apply Finset.sum_pos
  · intro k hk
    exact hpos k (by simp only [Finset.mem_range] at hk; omega)
  · exact ⟨0, by simp⟩

private theorem adjacent_strict (a : ℕ → ℝ) (r : ℕ)
    (hpos : ∀ n, n ≤ r+1 → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < r+1 →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hr : 1 ≤ r) :
    (∑ skoricIndex ∈ Finset.range ((r+1)+1), (skoricIndex : ℝ) * a skoricIndex) / ((r+1:ℝ) * (∑ skoricIndex ∈ Finset.range ((r+1)+1), a skoricIndex)) <
      (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) / ((r:ℝ) * (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex)) := by
  have hSr : 0 < (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) := sum_pos a r (fun k hk => hpos k (by omega))
  have hSr1 : 0 < (∑ skoricIndex ∈ Finset.range ((r+1)+1), a skoricIndex) := sum_pos a (r+1) hpos
  have hdenr : 0 < (r:ℝ) * (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) :=
    mul_pos (by exact_mod_cast (show 0 < r by omega)) hSr
  have hdenr1 : 0 < (r+1:ℝ) * (∑ skoricIndex ∈ Finset.range ((r+1)+1), a skoricIndex) :=
    mul_pos (by positivity) hSr1
  have hD := D_positive a r hpos hfac hr
  rw [div_lt_div_iff₀ hdenr1 hdenr]
  have hD' : (r:ℝ) * (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range ((r+1)+1), (skoricIndex : ℝ) * a skoricIndex) <
      (r+1:ℝ) * (∑ skoricIndex ∈ Finset.range ((r+1)+1), a skoricIndex) * (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) := by
    exact sub_pos.mp hD
  simpa [mul_assoc, mul_comm, mul_left_comm] using hD'

private theorem chain_nonstrict (a : ℕ → ℝ) (m r s : ℕ)
    (hpos : ∀ n, n ≤ m → 0 < a n)
    (hfac : ∀ k, 1 ≤ k → k < m →
      (k:ℝ) * (a k)^2 ≥ ((k+1:ℕ):ℝ) * a (k-1) * a (k+1))
    (hr : 1 ≤ r) (hrs : r ≤ s) (hsm : s ≤ m) :
    (∑ skoricIndex ∈ Finset.range (s+1), (skoricIndex : ℝ) * a skoricIndex) / ((s:ℝ) * (∑ skoricIndex ∈ Finset.range (s+1), a skoricIndex)) ≤ (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) / ((r:ℝ) * (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex)) := by
  have hchain : ∀ n, r ≤ n → n ≤ s →
      (∑ skoricIndex ∈ Finset.range (n+1), (skoricIndex : ℝ) * a skoricIndex) / ((n:ℝ) * (∑ skoricIndex ∈ Finset.range (n+1), a skoricIndex)) ≤ (∑ skoricIndex ∈ Finset.range (r+1), (skoricIndex : ℝ) * a skoricIndex) / ((r:ℝ) * (∑ skoricIndex ∈ Finset.range (r+1), a skoricIndex)) := by
    intro n hn
    refine Nat.le_induction (m := r) ?_ ?_ n hn
    · intro _
      exact le_rfl
    · intro k hk ih hks
      have hkpos : 1 ≤ k := Nat.le_trans hr hk
      have hk1m : k+1 ≤ m := Nat.le_trans hks hsm
      have hadj := adjacent_strict a k
        (fun n hn => hpos n (by omega))
        (fun q hq1 hqk => hfac q hq1 (by omega)) hkpos
      have hadj' : (∑ skoricIndex ∈ Finset.range ((k+1)+1), (skoricIndex : ℝ) * a skoricIndex) / (((k+1:ℕ):ℝ) * (∑ skoricIndex ∈ Finset.range ((k+1)+1), a skoricIndex)) <
          (∑ skoricIndex ∈ Finset.range (k+1), (skoricIndex : ℝ) * a skoricIndex) / ((k:ℝ) * (∑ skoricIndex ∈ Finset.range (k+1), a skoricIndex)) := by
        simpa [Nat.cast_add, Nat.cast_one] using hadj
      exact (le_of_lt hadj').trans (ih (by omega))
  exact hchain s hrs (by omega)

private theorem choose_fac (x k : ℕ) (hk1 : 1 ≤ k) (hkx : k < x) :
    (k:ℝ) * (Nat.choose x k : ℝ)^2 ≥
      ((k+1:ℕ):ℝ) * (Nat.choose x (k-1) : ℝ) * (Nat.choose x (k+1) : ℝ) := by
  have hkm : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  have h1 := Nat.choose_succ_right_eq x (k-1)
  rw [hkm] at h1
  have h1r : (Nat.choose x k : ℝ) * (k:ℝ) =
      (Nat.choose x (k-1) : ℝ) * ((x-(k-1):ℕ):ℝ) := by
    exact_mod_cast h1
  have h2 := Nat.choose_succ_right_eq x k
  have h2r : (Nat.choose x (k+1) : ℝ) * ((k+1:ℕ):ℝ) =
      (Nat.choose x k : ℝ) * ((x-k:ℕ):ℝ) := by
    exact_mod_cast h2
  have hck : 0 ≤ (Nat.choose x k : ℝ) := Nat.cast_nonneg' _
  have hcm : 0 ≤ (Nat.choose x (k-1) : ℝ) := Nat.cast_nonneg' _
  have hsub : ((x-k:ℕ):ℝ) ≤ ((x-(k-1):ℕ):ℝ) := by
    have hn : x-k + 1 = x-(k-1) := by omega
    have hnr : ((x-k:ℕ):ℝ) + 1 = ((x-(k-1):ℕ):ℝ) := by exact_mod_cast hn
    exact le_trans (le_add_of_nonneg_right zero_le_one) hnr.le
  have hmid := mul_le_mul_of_nonneg_left hsub (mul_nonneg hck hcm)
  calc
    (k:ℝ) * (Nat.choose x k : ℝ)^2 =
        (Nat.choose x k : ℝ) * ((Nat.choose x k : ℝ) * (k:ℝ)) := by ring
    _ = (Nat.choose x k : ℝ) *
        ((Nat.choose x (k-1) : ℝ) * ((x-(k-1):ℕ):ℝ)) := by rw [h1r]
    _ ≥ (Nat.choose x k : ℝ) *
        ((Nat.choose x (k-1) : ℝ) * ((x-k:ℕ):ℝ)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmid
    _ = ((k+1:ℕ):ℝ) * (Nat.choose x (k-1) : ℝ) *
        (Nat.choose x (k+1) : ℝ) := by
          calc
            (Nat.choose x k : ℝ) *
                ((Nat.choose x (k-1) : ℝ) * ((x-k:ℕ):ℝ)) =
                (Nat.choose x (k-1) : ℝ) *
                  ((Nat.choose x k : ℝ) * ((x-k:ℕ):ℝ)) := by ring
            _ = (Nat.choose x (k-1) : ℝ) *
                  ((Nat.choose x (k+1) : ℝ) * ((k+1:ℕ):ℝ)) := by
                    rw [h2r]
            _ = ((k+1:ℕ):ℝ) * (Nat.choose x (k-1) : ℝ) *
                (Nat.choose x (k+1) : ℝ) := by ring

private theorem choose_row_pos (x n : ℕ) (hn : n ≤ x) : 0 < (Nat.choose x n : ℝ) := by
  exact_mod_cast Nat.choose_pos hn

theorem result : claim := by
  intro x hx r hr s hrs h2s
  have hsm : s ≤ x := by omega
  have hpos : ∀ n, n ≤ x → 0 < (Nat.choose x n : ℝ) := by
    intro n hn
    exact choose_row_pos x n hn
  have hfac : ∀ k, 1 ≤ k → k < x →
      (k:ℝ) * (Nat.choose x k : ℝ)^2 ≥
        ((k+1:ℕ):ℝ) * (Nat.choose x (k-1) : ℝ) *
          (Nat.choose x (k+1) : ℝ) := by
    intro k hk1 hkx
    exact choose_fac x k hk1 hkx
  have hF := chain_nonstrict (fun n => (Nat.choose x n : ℝ)) x r s
    hpos hfac hr (by omega) hsm
  have hform : ∀ t, f x t =
      (∑ n ∈ Finset.range (t+1), (n:ℝ) * (Nat.choose x n : ℝ)) /
        ((t:ℝ) * ∑ n ∈ Finset.range (t+1), (Nat.choose x n : ℝ)) := by
    intro t
    unfold f
    rw [div_mul_div_comm, one_mul]
  rw [hform s, hform r]
  exact hF


end D5.S3.Entropy.PoissonBinomial.SkoricTruncatedBinomialMean
