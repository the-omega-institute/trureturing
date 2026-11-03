/- GID: D5/S1/Recurrence/MetaFibonacci/SobolewskiUlasParityPositions
   generality: I
   mirror-B: D5/B/S1/Recurrence/MetaFibonacci/SobolewskiUlasParityPositions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Both parity-position sequences of h(1,1) have finitely generated binary-kernel spans. -/

/-
result proof_shape: content (block-balance and finite-state induction after helper expansion).
escape_witness: none (the settling result supplies the module basis).
admission_basis: open-problem-resolution (#19659; Proved)
Direct frozen dependencies: D5/S1/Words/Palindromes/PeriodDoubling/SparseKernelRank.twoKernel
  statement_id: sha256:e1b044308e2015d0ff46944e48d3c2e43f3e2135242a545fe2fb3b145122b274 (definition only; no frozen theorem).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21489
The source k-kernel expression is retained for arbitrary k; binary proofs use the existing twoKernel.

Declaration classifications (the module basis applies to every row).
h: proof_shape: bind-only; escape_witness: none; consumers: r, h_step, bridge, h_eq_odd, h_eq_even, r_lt_two, r_odd, r_even, initial_g; Direct frozen dependencies: none.
r: proof_shape: bind-only; escape_witness: none; consumers: u, r_odd, r_even, r_8n2, r_8n6, rz, rz_even, rz_odd, r_period, initial_g, periodic_parity, periodic_eight, r_double16, r_double16_add, t_even, t_odd, block_table, count_in_block, block_balance, count_blocks, nth_block_selection, V, V_step, correction_representation; Direct frozen dependencies: none.
u: proof_shape: bind-only; escape_witness: none; consumers: claim, settlement_from_correction, correction_representation; Direct frozen dependencies: none.
kKernel: proof_shape: bind-only; escape_witness: none; consumers: IsKRegular, regular_of_finite_correction; Direct frozen dependencies: none.
IsKRegular: proof_shape: bind-only; escape_witness: none; consumers: claim, settlement_from_correction; Direct frozen dependencies: none.
claim: proof_shape: bind-only; escape_witness: none; consumers: result (statement); Direct frozen dependencies: none.
h_step: proof_shape: bind-only; escape_witness: none; consumers: bridge, h_eq_even; Direct frozen dependencies: none.
bridge: proof_shape: content; escape_witness: none; consumers: h_eq_odd; Direct frozen dependencies: none.
h_eq_odd: proof_shape: content; escape_witness: none; consumers: h_eq_even, r_odd; Direct frozen dependencies: none.
h_eq_even: proof_shape: content; escape_witness: none; consumers: r_even; Direct frozen dependencies: none.
r_lt_two: proof_shape: bind-only; escape_witness: none; consumers: r_8n2, r_8n6, r_period, r_double16, r_double16_add, block_balance, nth_block_selection; Direct frozen dependencies: none.
r_odd: proof_shape: content; escape_witness: none; consumers: r_8n2, r_8n6, rz_odd, initial_g, block_table; Direct frozen dependencies: none.
r_even: proof_shape: content; escape_witness: none; consumers: r_8n2, r_8n6, rz_even, initial_g, periodic_eight, r_double16, r_double16_add; Direct frozen dependencies: none.
r_8n2: proof_shape: content; escape_witness: none; consumers: block_table; Direct frozen dependencies: none.
r_8n6: proof_shape: content; escape_witness: none; consumers: periodic_eight, r_double16, r_double16_add, block_table; Direct frozen dependencies: none.
regular_of_finite_correction: proof_shape: bind-only; escape_witness: none; consumers: settlement_from_correction; Direct frozen dependencies: twoKernel, with the declaration identity above.
settlement_from_correction: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: twoKernel, with the declaration identity above.
rz: proof_shape: bind-only; escape_witness: none; consumers: rz_even, rz_odd, rz_even16, rz_odd16, rz_lower_odd_sum, rz_sum16_zero, rz_even_iter, rz_period; Direct frozen dependencies: none.
rz_even: proof_shape: content; escape_witness: none; consumers: rz_even16, rz_even_iter; Direct frozen dependencies: none.
rz_odd: proof_shape: content; escape_witness: none; consumers: rz_odd16, rz_lower_odd_sum; Direct frozen dependencies: none.
rz_even16: proof_shape: content; escape_witness: none; consumers: rz_sum16_zero; Direct frozen dependencies: none.
rz_odd16: proof_shape: content; escape_witness: none; consumers: rz_sum16_zero; Direct frozen dependencies: none.
rz_lower_odd_sum: proof_shape: content; escape_witness: none; consumers: rz_sum16_zero; Direct frozen dependencies: none.
rz_sum16_zero: proof_shape: content; escape_witness: none; consumers: rz_period; Direct frozen dependencies: none.
rz_even_iter: proof_shape: content; escape_witness: none; consumers: rz_period; Direct frozen dependencies: none.
rz_period: proof_shape: content; escape_witness: none; consumers: r_period; Direct frozen dependencies: none.
r_period: proof_shape: content; escape_witness: none; consumers: periodic_parity; Direct frozen dependencies: none.
g: proof_shape: bind-only; escape_witness: none; consumers: initial_g, periodic_parity, periodic_eight, r_double16, r_double16_add, g_even, g_odd, block_table; Direct frozen dependencies: none.
initial_g: proof_shape: bind-only; escape_witness: none; consumers: periodic_parity; Direct frozen dependencies: none.
periodic_parity: proof_shape: content; escape_witness: none; consumers: periodic_eight, r_double16, r_double16_add, block_table; Direct frozen dependencies: none.
periodic_eight: proof_shape: content; escape_witness: none; consumers: t_odd, block_table; Direct frozen dependencies: none.
r_double16: proof_shape: content; escape_witness: none; consumers: t_even; Direct frozen dependencies: none.
r_double16_add: proof_shape: content; escape_witness: none; consumers: t_odd; Direct frozen dependencies: none.
t_even: proof_shape: content; escape_witness: none; consumers: V_step; Direct frozen dependencies: none.
t_odd: proof_shape: content; escape_witness: none; consumers: V_step; Direct frozen dependencies: none.
B: proof_shape: bind-only; escape_witness: none; consumers: block_table, table_balance, table_select, count_in_block, block_balance, nth_block_selection; Direct frozen dependencies: none.
F: proof_shape: bind-only; escape_witness: none; consumers: table_select, nth_block_selection, out, correction_representation; Direct frozen dependencies: none.
g_even: proof_shape: bind-only; escape_witness: none; consumers: block_table; Direct frozen dependencies: none.
g_odd: proof_shape: bind-only; escape_witness: none; consumers: block_table; Direct frozen dependencies: none.
block_table: proof_shape: content; escape_witness: none; consumers: count_in_block, nth_block_selection; Direct frozen dependencies: none.
table_balance: proof_shape: bind-only; escape_witness: none; consumers: block_balance; Direct frozen dependencies: none.
table_select: proof_shape: bind-only; escape_witness: none; consumers: nth_block_selection; Direct frozen dependencies: none.
count_in_block: proof_shape: content; escape_witness: none; consumers: block_balance, nth_block_selection; Direct frozen dependencies: none.
block_balance: proof_shape: content; escape_witness: none; consumers: count_blocks; Direct frozen dependencies: none.
count_blocks: proof_shape: content; escape_witness: none; consumers: nth_block_selection; Direct frozen dependencies: none.
nth_block_selection: proof_shape: content; escape_witness: none; consumers: correction_representation; Direct frozen dependencies: none.
finite_kernel_of_state: proof_shape: content; escape_witness: none; consumers: finite_correction_kernel; Direct frozen dependencies: twoKernel, with the declaration identity above.
V: proof_shape: bind-only; escape_witness: none; consumers: V_step, D, finite_correction_kernel; Direct frozen dependencies: none.
vstep: proof_shape: bind-only; escape_witness: none; consumers: V_step, finite_correction_kernel; Direct frozen dependencies: none.
V_step: proof_shape: content; escape_witness: none; consumers: finite_correction_kernel; Direct frozen dependencies: none.
out: proof_shape: bind-only; escape_witness: none; consumers: D, finite_correction_kernel; Direct frozen dependencies: none.
D: proof_shape: bind-only; escape_witness: none; consumers: correction_representation, result; Direct frozen dependencies: none.
correction_representation: proof_shape: content; escape_witness: none; consumers: result; Direct frozen dependencies: none.
finite_correction_kernel: proof_shape: content; escape_witness: none; consumers: result; Direct frozen dependencies: twoKernel, with the declaration identity above.
result: proof_shape: content; escape_witness: none; consumers: terminal result; Direct frozen dependencies: twoKernel, with the declaration identity above.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SparseKernelRank

/-! Binding conventions for B. Sobolewski and M. Ulas, "Solutions of certain meta-Fibonacci recurrences",
arXiv:2204.04011v1 (Acta Arith. 209 (2023) 269–289): the sequence `h = h_{1,1}` with `h(n) = 1` for `n ≤ 1` and
`h(n) = h(n − h(n − 1)) + h(n − 2)` for `n > 1`, its parity `r(n) = h(n) (mod 2)`, the increasing enumerations `u_i` of
`{n : r(n) = i}`, `k`-kernels and `k`-regular sequences (Section 2), and Question 7.5, "Is the sequence u_i is k-regular for
some k?". -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Words.Palindromes.PeriodDoubling (twoKernel)

namespace D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

/-- `h(n)` for `n ≥ 0`: `h(0) = h(1) = 1` and `h(n) = h(n − h(n − 1)) + h(n − 2)` for `n > 1`. Arguments `≤ 1` of the
source, including negative ones, have value `1`; truncated subtraction sends a negative argument to `0`, where `h = 1`.
The `min` only guards termination and is inactive because `h ≥ 1`. -/
def h : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => h (min (n + 2 - h (n + 1)) (n + 1)) + h n
termination_by n => n
decreasing_by all_goals omega

/-- `r(n) = h(n) (mod 2)`. -/
def r (n : ℕ) : ℕ := h n % 2

/-- `u_i`: the increasing sequence of nonnegative integers `m` with `r(m) = i`, indexed from `0`. -/
noncomputable def u (i : ℕ) (n : ℕ) : ℕ := Nat.nth (fun m => r m = i) n

/-- Section 2: the `k`-kernel `K_k(a) = {(a_{k^j n + i})_{n ∈ ℕ} : j ∈ ℕ, 0 ≤ i < k^j}`. -/
def kKernel (k : ℕ) (a : ℕ → ℤ) : Set (ℕ → ℤ) :=
  {f | ∃ j i : ℕ, i < k ^ j ∧ f = fun n => a (k ^ j * n + i)}

/-- Section 2: `a` is `k`-regular if the `ℤ`-submodule generated by `K_k(a)` is finitely generated. -/
def IsKRegular (k : ℕ) (a : ℕ → ℤ) : Prop :=
  (Submodule.span ℤ (kKernel k a)).FG

/-- Question 7.5, answered affirmatively: for `i = 0, 1`, the sequence `u_i` is `k`-regular for some integer `k ≥ 2`. -/
def claim : Prop :=
  ∀ i : ℕ, i < 2 → ∃ k : ℕ, 2 ≤ k ∧ IsKRegular k (fun n => (u i n : ℤ))

end D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

namespace D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

private theorem h_step (n : ℕ) : h (n+2) = h (min (n+2 - h (n+1)) (n+1)) + h n := by
  rw [h]

private theorem bridge (n : ℕ) : h (2*n+1) = n+1 ∧ 2*n ≤ h (2*n) := by
  induction n using Nat.strong_induction_on with | h n ih =>
    rcases n with _ | n
    · simp [h]
    · have hi := ih n (by omega)
      have heven : h (2*n+2) = h (2*n) + h (n+1) := by
        rw [show 2*n+2 = (2*n)+2 by omega, h_step]
        have hm : min (2*n+2 - h (2*n+1)) (2*n+1) = n+1 := by
          rw [hi.1]
          omega
        rw [hm]
        omega
      have hsum : 2*n+2 ≤ h (2*n) + h (n+1) := by
        clear heven
        rcases Nat.even_or_odd n with hne | hno
        · obtain ⟨m, rfl⟩ := hne
          have hm := (ih (2*m) (by omega)).2
          have hm' := (ih m (by omega)).1
          by_cases hm0 : m = 0
          · subst m
            norm_num [h] at *
          · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
            have hm4 : 4*m ≤ h (4*m) := by
              have hh : 2*(2*m) = 4*m := by ring
              rw [hh] at hm
              exact hm
            have hs : 4*m+2 ≤ h (4*m) + h (2*m+1) := by
              rw [hm']
              omega
            have hh1 : 2*(m+m)+2 = 4*m+2 := by ring
            have hh2 : 2*(m+m) = 4*m := by ring
            have hh3 : m+m+1 = 2*m+1 := by ring
            simpa only [hh1, hh2, hh3] using hs
        · obtain ⟨m, rfl⟩ := hno
          have hi2 : 2 * (2*m+1) ≤ h (2 * (2*m+1)) := hi.2
          by_cases hm0 : m = 0
          · subst m
            norm_num [h]
          · have hm' : 2 * (m+1) ≤ h (2 * (m+1)) := (ih (m+1) (by omega)).2
            have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
            have hi4 : 4*m+2 ≤ h (4*m+2) := by
              have hh : 2*(2*m+1) = 4*m+2 := by ring
              rw [hh] at hi2
              exact hi2
            have hm4 : 2*m+2 ≤ h (2*m+2) := by
              have hh : 2*(m+1) = 2*m+2 := by ring
              rw [hh] at hm'
              exact hm'
            have hs : 4*m+4 ≤ h (4*m+2) + h (2*m+2) := by omega
            have hh1 : 2*(2*m+1)+2 = 4*m+4 := by ring
            have hh2 : 2*(2*m+1) = 4*m+2 := by ring
            have hh3 : 2*m+1+1 = 2*m+2 := by ring
            simpa only [hh1, hh2, hh3] using hs
      have hge : 2*n+2 ≤ h (2*n+2) := by
        simpa [heven] using hsum
      have hoddrec : h (2*n+3) =
          h (min (2*n+3 - h (2*n+2)) (2*n+2)) + h (2*n+1) := by
        have hh := h_step (2*n+1)
        convert hh using 1 <;> omega
      have hodd : h (2*n+3) = n+2 := by
        rw [hoddrec]
        have hm : min (2*n+3 - h (2*n+2)) (2*n+2) ≤ 1 := by
          omega
        have hsmall : ∀ x : ℕ, x ≤ 1 → h x = 1 := by
          intro x hx
          interval_cases x <;> simp [h]
        rw [hsmall _ hm, hi.1]
        omega
      exact ⟨hodd, hge⟩

private theorem h_eq_odd (n : ℕ) : h (2*n+1) = n+1 := by
  exact (bridge n).1
private theorem h_eq_even (n : ℕ) : h (2*n+2) = h (2*n) + h (n+1) := by
  rw [show 2*n+2 = (2*n)+2 by omega, h_step]
  have ho := h_eq_odd n
  have hm : min (2*n+2 - h (2*n+1)) (2*n+1) = n+1 := by rw [ho]; omega
  rw [hm]
  omega

private theorem r_lt_two (n : ℕ) : r n < 2 := by
  exact Nat.mod_lt _ (by omega)

private theorem r_odd (n : ℕ) : r (2*n+1) = (n+1) % 2 := by
  simp [r, h_eq_odd]

private theorem r_even (n : ℕ) : r (2*n+2) = (r (2*n) + r (n+1)) % 2 := by
  simp [r, h_eq_even, Nat.add_mod]

private theorem r_8n2 (n : ℕ) : r (8*n+2) = 1 - r (8*n) := by
  have ho : r (4*n+1) = 1 := by
    rw [show 4*n+1 = 2*(2*n)+1 by omega, r_odd]
    simp [Nat.add_mod, Nat.mul_mod]
  have he := r_even (4*n)
  have hidx : 2*(4*n) = 8*n := by ring
  rw [hidx] at he
  have hr := r_lt_two (8*n)
  have he' : r (8*n+2) = (r (8*n) + r (4*n+1)) % 2 := by
    convert he using 1 <;> ring
  rw [he', ho]
  rcases (show r (8*n) = 0 ∨ r (8*n) = 1 by
    simpa only [Nat.mod_eq_of_lt hr] using Nat.mod_two_eq_zero_or_one (r (8*n))) with hzero | hone
  · simp [hzero]
  · simp [hone]

private theorem r_8n6 (n : ℕ) : r (8*n+6) = r (8*n+4) := by
  have ho : r (4*n+3) = 0 := by
    rw [show 4*n+3 = 2*(2*n+1)+1 by omega, r_odd]
    simp [Nat.add_mod, Nat.mul_mod]
  have he := r_even (4*n+2)
  have hidx : 2*(4*n+2) = 8*n+4 := by ring
  rw [hidx] at he
  have he' : r (8*n+6) = (r (8*n+4) + r (4*n+3)) % 2 := by
    convert he using 1 <;> ring
  have hr := r_lt_two (8*n+4)
  rw [he', ho]
  simp only [Nat.add_zero]
  exact Nat.mod_eq_of_lt hr


private theorem regular_of_finite_correction (d : ℕ → ℤ) (hd : (twoKernel d).Finite) :
    IsKRegular 2 (fun n => (2 : ℤ) * n + d n) := by
  let one : ℕ → ℤ := fun _ => 1
  let linear : ℕ → ℤ := fun n => n
  let S : Set (ℕ → ℤ) := insert linear (insert one (twoKernel d))
  have hS : S.Finite := by
    dsimp [S]
    exact hd.insert _ |>.insert _
  have hfg : (Submodule.span ℤ S).FG := Submodule.fg_span hS
  apply Submodule.FG.of_le hfg
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with ⟨e, r, hr, rfl⟩
  let g : ℕ → ℤ := fun n => d (2 ^ e * n + r)
  have hg : g ∈ twoKernel d := ⟨e, r, hr, rfl⟩
  have hdecomp :
      (fun n => (2 : ℤ) * (2 ^ e * n + r) + d (2 ^ e * n + r)) =
        (2 ^ (e+1) : ℤ) • linear + (2*r : ℤ) • one + g := by
    funext n
    dsimp [linear, one, g]
    push_cast
    ring
  change (fun n => (2 : ℤ) * (2 ^ e * n + r) + d (2 ^ e * n + r)) ∈
    Submodule.span ℤ S
  rw [hdecomp]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S]))
  · exact Submodule.subset_span (by exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hg))

private theorem settlement_from_correction (i : ℕ) (D : ℕ → ℤ)
    (hrepresentation : ∀ n, (u i n : ℤ) = (2 : ℤ) * n + D n)
    (hfinite : (twoKernel D).Finite) :
    ∃ k : ℕ, 2 ≤ k ∧ IsKRegular k (fun n => (u i n : ℤ)) := by
  refine ⟨2, by omega, ?_⟩
  rw [show (fun n => (u i n : ℤ)) = (fun n => (2 : ℤ) * n + D n) by
    funext n; exact hrepresentation n]
  exact regular_of_finite_correction D hfinite

end D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions
namespace D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions
open scoped BigOperators
end D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

namespace D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions
private def rz (n : ℕ) : ZMod 2 := (r n : ZMod 2)

private theorem rz_even (n : ℕ) : rz (2*n+2) = rz (2*n) + rz (n+1) := by
  have h := congrArg (fun x : ℕ => (x : ZMod 2)) (r_even n)
  simpa [rz, Nat.cast_add, ZMod.natCast_mod] using h

private theorem rz_odd (n : ℕ) : rz (2*n+1) = ((n+1 : ℕ) : ZMod 2) := by
  have h := congrArg (fun x : ℕ => (x : ZMod 2)) (r_odd n)
  simpa [rz, ZMod.natCast_mod] using h

end D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

namespace D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

private theorem rz_even16 (n j k : ℕ) :
    rz (16*n+4*j+4+2*k) = rz (16*n+4*j+2+2*k) + rz (8*n+2*j+2+k) := by
  calc
    rz (16*n+4*j+4+2*k) = rz (2*(8*n+2*j+1+k)+2) := by congr 1 <;> ring
    _ = rz (2*(8*n+2*j+1+k)) + rz (8*n+2*j+2+k) := by
      have h := rz_even (8*n+2*j+1+k)
      convert h using 1 <;> ring
    _ = _ := by congr 1 <;> ring

private theorem rz_odd16 (n j k : ℕ) :
    rz (16*n+4*j+3+2*k) = (k : ZMod 2) := by
  calc
    rz (16*n+4*j+3+2*k) = rz (2*(8*n+2*j+1+k)+1) := by congr 1 <;> ring
    _ = ((8*n+2*j+1+k+1 : ℕ) : ZMod 2) := rz_odd _
    _ = (k : ZMod 2) := by
      apply (ZMod.natCast_eq_natCast_iff' (8*n+2*j+1+k+1) k 2).2
      omega

private theorem rz_lower_odd_sum (n j : ℕ) :
    rz (8*n+2*j+3) + rz (8*n+2*j+5) + rz (8*n+2*j+7) + rz (8*n+2*j+9) = 0 := by
  rw [show 8*n+2*j+3 = 2*(4*n+j+1)+1 by ring,
      show 8*n+2*j+5 = 2*(4*n+j+2)+1 by ring,
      show 8*n+2*j+7 = 2*(4*n+j+3)+1 by ring,
      show 8*n+2*j+9 = 2*(4*n+j+4)+1 by ring]
  rw [rz_odd, rz_odd, rz_odd, rz_odd]
  push_cast
  calc
    _ = (16 : ZMod 2) * n + 4 * j + 14 := by ring
    _ = 0 := by rw [show (16 : ZMod 2) = 0 by decide,
                       show (4 : ZMod 2) = 0 by decide,
                       show (14 : ZMod 2) = 0 by decide]; simp

private theorem rz_sum16_zero (n j : ℕ) (hj : j < 4) :
    (∑ i ∈ Finset.range 16, rz (16*n+4*j+3+i)) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have ho0 : rz (16*n+4*j+3) = (0 : ZMod 2) := by
    have hh := rz_odd16 n j 0
    have hv : ((0 : ℕ) : ZMod 2) = 0 := Nat.cast_zero
    simp only [hv] at hh
    convert hh using 1 <;> omega
  have ho1 : rz (16*n+4*j+5) = (1 : ZMod 2) := by
    have hh := rz_odd16 n j 1
    have hv : ((1 : ℕ) : ZMod 2) = 1 := by exact Nat.cast_one
    simp only [hv] at hh
    convert hh using 1 <;> omega
  have ho2 : rz (16*n+4*j+7) = (0 : ZMod 2) := by
    have hh := rz_odd16 n j 2
    have hv : ((2 : ℕ) : ZMod 2) = 0 := by exact ZMod.natCast_self 2
    simp only [hv] at hh
    convert hh using 1 <;> omega
  have ho3 : rz (16*n+4*j+9) = (1 : ZMod 2) := by
    have hh := rz_odd16 n j 3
    have hv : ((3 : ℕ) : ZMod 2) = 1 := (ZMod.natCast_eq_natCast_iff' 3 1 2).2 rfl
    simp only [hv] at hh
    convert hh using 1 <;> omega
  have ho4 : rz (16*n+4*j+11) = (0 : ZMod 2) := by
    have hh := rz_odd16 n j 4
    have hv : ((4 : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_natCast_iff' 4 0 2).2 rfl
    simp only [hv] at hh
    convert hh using 1 <;> omega
  have ho5 : rz (16*n+4*j+13) = (1 : ZMod 2) := by
    have hh := rz_odd16 n j 5
    have hv : ((5 : ℕ) : ZMod 2) = 1 := (ZMod.natCast_eq_natCast_iff' 5 1 2).2 rfl
    simp only [hv] at hh
    convert hh using 1 <;> omega
  have ho6 : rz (16*n+4*j+15) = (0 : ZMod 2) := by
    have hh := rz_odd16 n j 6
    have hv : ((6 : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_natCast_iff' 6 0 2).2 rfl
    simp only [hv] at hh
    convert hh using 1 <;> omega
  have ho7 : rz (16*n+4*j+17) = (1 : ZMod 2) := by
    have hh := rz_odd16 n j 7
    have hv : ((7 : ℕ) : ZMod 2) = 1 := (ZMod.natCast_eq_natCast_iff' 7 1 2).2 rfl
    simp only [hv] at hh
    convert hh using 1 <;> omega
  have he0 : rz (16*n+4*j+4) = rz (16*n+4*j+2) + rz (8*n+2*j+2) := by
    simpa [Nat.add_assoc] using (rz_even16 n j 0)
  have he1 : rz (16*n+4*j+6) = rz (16*n+4*j+4) + rz (8*n+2*j+3) := by
    simpa [Nat.add_assoc] using (rz_even16 n j 1)
  have he2 : rz (16*n+4*j+8) = rz (16*n+4*j+6) + rz (8*n+2*j+4) := by
    simpa [Nat.add_assoc] using (rz_even16 n j 2)
  have he3 : rz (16*n+4*j+10) = rz (16*n+4*j+8) + rz (8*n+2*j+5) := by
    simpa [Nat.add_assoc] using (rz_even16 n j 3)
  have he4 : rz (16*n+4*j+12) = rz (16*n+4*j+10) + rz (8*n+2*j+6) := by
    simpa [Nat.add_assoc] using (rz_even16 n j 4)
  have he5 : rz (16*n+4*j+14) = rz (16*n+4*j+12) + rz (8*n+2*j+7) := by
    simpa [Nat.add_assoc] using (rz_even16 n j 5)
  have he6 : rz (16*n+4*j+16) = rz (16*n+4*j+14) + rz (8*n+2*j+8) := by
    simpa [Nat.add_assoc] using (rz_even16 n j 6)
  have he7 : rz (16*n+4*j+18) = rz (16*n+4*j+16) + rz (8*n+2*j+9) := by
    simpa [Nat.add_assoc] using (rz_even16 n j 7)
  have hl := rz_lower_odd_sum n j
  simp only [ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7, he0, he1, he2, he3, he4, he5, he6, he7]
  have hz2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hz4 : (4 : ZMod 2) = 0 := by exact (ZMod.val_eq_zero _).mp rfl
  have hz6 : (6 : ZMod 2) = 0 := by exact (ZMod.val_eq_zero _).mp rfl
  have hz8 : (8 : ZMod 2) = 0 := by exact (ZMod.val_eq_zero _).mp rfl
  linear_combination (norm := ring_nf) hl
  all_goals simp only [hz2, hz4, hz6, hz8, mul_zero, zero_mul, add_zero, zero_add]
private theorem rz_even_iter (a k : ℕ) :
    rz (2*(a+k)) = rz (2*a) + (∑ i ∈ Finset.range k, rz (a+i+1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(a+(k+1)) = 2*(a+k)+2 by ring, rz_even, ih]
    simp only [Finset.sum_range_succ]
    ring

private theorem rz_period (n j : ℕ) (hj : j < 4) :
    rz (32*(n+1)+8*j+4) = rz (32*n+8*j+4) := by
  have h := rz_even_iter (16*n+4*j+2) 16
  have hs := rz_sum16_zero n j hj
  rw [show 2*((16*n+4*j+2)+16) = 32*(n+1)+8*j+4 by ring,
      show 2*(16*n+4*j+2) = 32*n+8*j+4 by ring] at h
  have hsum : (∑ i ∈ Finset.range 16, rz (16*n+4*j+2+i+1)) = 0 := by
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1 <;> omega
  rw [hsum] at h
  simpa using h

private theorem r_period (n j : ℕ) (hj : j < 4) :
    r (32*(n+1)+8*j+4) = r (32*n+8*j+4) := by
  have h := rz_period n j hj
  have h' : (r (32*(n+1)+8*j+4) : ZMod 2) = (r (32*n+8*j+4) : ZMod 2) := h
  have hm := (ZMod.natCast_eq_natCast_iff' (r (32*(n+1)+8*j+4)) (r (32*n+8*j+4)) 2).mp h'
  rw [Nat.mod_eq_of_lt (r_lt_two _), Nat.mod_eq_of_lt (r_lt_two _)] at hm
  exact hm

private def g (j : ℕ) : ℕ := if j = 1 ∨ j = 2 then 1 else 0

private theorem initial_g (j : ℕ) (hj : j < 4) : r (8*j+4) = g j := by
  have hr0 : r 0 = 1 := by norm_num [r, h]
  have hr1 : r 1 = 1 := by
    have hx := r_odd 0
    norm_num at hx
    exact hx
  have hr2 : r 2 = 0 := by
    have hx := r_even 0
    norm_num [hr0, hr1] at hx
    exact hx
  have hr3 : r 3 = 0 := by
    have hx := r_odd 1
    norm_num at hx
    exact hx
  have hr4 : r 4 = 0 := by
    have hx := r_even 1
    norm_num [hr0, hr1, hr2, hr3] at hx
    exact hx
  have hr5 : r 5 = 1 := by
    have hx := r_odd 2
    norm_num at hx
    exact hx
  have hr6 : r 6 = 0 := by
    have hx := r_even 2
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5] at hx
    exact hx
  have hr7 : r 7 = 0 := by
    have hx := r_odd 3
    norm_num at hx
    exact hx
  have hr8 : r 8 = 0 := by
    have hx := r_even 3
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7] at hx
    exact hx
  have hr9 : r 9 = 1 := by
    have hx := r_odd 4
    norm_num at hx
    exact hx
  have hr10 : r 10 = 1 := by
    have hx := r_even 4
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9] at hx
    exact hx
  have hr11 : r 11 = 0 := by
    have hx := r_odd 5
    norm_num at hx
    exact hx
  have hr12 : r 12 = 1 := by
    have hx := r_even 5
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11] at hx
    exact hx
  have hr13 : r 13 = 1 := by
    have hx := r_odd 6
    norm_num at hx
    exact hx
  have hr14 : r 14 = 1 := by
    have hx := r_even 6
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13] at hx
    exact hx
  have hr15 : r 15 = 0 := by
    have hx := r_odd 7
    norm_num at hx
    exact hx
  have hr16 : r 16 = 1 := by
    have hx := r_even 7
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15] at hx
    exact hx
  have hr17 : r 17 = 1 := by
    have hx := r_odd 8
    norm_num at hx
    exact hx
  have hr18 : r 18 = 0 := by
    have hx := r_even 8
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17] at hx
    exact hx
  have hr19 : r 19 = 0 := by
    have hx := r_odd 9
    norm_num at hx
    exact hx
  have hr20 : r 20 = 1 := by
    have hx := r_even 9
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19] at hx
    exact hx
  have hr21 : r 21 = 1 := by
    have hx := r_odd 10
    norm_num at hx
    exact hx
  have hr22 : r 22 = 1 := by
    have hx := r_even 10
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21] at hx
    exact hx
  have hr23 : r 23 = 0 := by
    have hx := r_odd 11
    norm_num at hx
    exact hx
  have hr24 : r 24 = 0 := by
    have hx := r_even 11
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22, hr23] at hx
    exact hx
  have hr25 : r 25 = 1 := by
    have hx := r_odd 12
    norm_num at hx
    exact hx
  have hr26 : r 26 = 1 := by
    have hx := r_even 12
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22, hr23, hr24, hr25] at hx
    exact hx
  have hr27 : r 27 = 0 := by
    have hx := r_odd 13
    norm_num at hx
    exact hx
  have hr28 : r 28 = 0 := by
    have hx := r_even 13
    norm_num [hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22, hr23, hr24, hr25, hr26, hr27] at hx
    exact hx
  interval_cases j <;> norm_num [g, hr4, hr12, hr20, hr28]

private theorem periodic_parity (n : ℕ) : r (8*n+4) = g (n % 4) := by
  have aux : ∀ q j : ℕ, j < 4 → r (32*q+8*j+4) = g j := by
    intro q j hj
    induction q with
    | zero =>
      simpa using initial_g j hj
    | succ q ih =>
      rw [r_period q j hj]
      exact ih
  have hx := aux (n / 4) (n % 4) (Nat.mod_lt _ (by omega))
  convert hx using 1 <;> congr 1 <;> omega

private theorem periodic_eight (n : ℕ) : r (16*n+8) = (n % 4) / 2 := by
  have hr := r_even (8*n+3)
  have ha : r (16*n+6) = g ((2*n) % 4) := by
    rw [show 16*n+6 = 8*(2*n)+6 by ring, r_8n6, periodic_parity]
  have hb := periodic_parity n
  have hc : r (16*n+8) = (r (16*n+6) + r (8*n+4)) % 2 := by
    rw [show 2*(8*n+3)+2 = 16*n+8 by ring,
        show 2*(8*n+3) = 16*n+6 by ring,
        show 8*n+3+1 = 8*n+4 by omega] at hr
    exact hr
  rw [hc, ha, hb]
  have hm : (2*n) % 4 = (2*(n%4))%4 := by simpa using (Nat.mul_mod 2 n 4)
  rw [hm]
  have hh : n % 4 < 4 := Nat.mod_lt _ (by omega)
  generalize n % 4 = j at *
  interval_cases j <;> norm_num [g]

private theorem r_double16 (n : ℕ) : r (32*n) = r (16*n) := by
  cases n with
  | zero => rfl
  | succ n =>
    have he := r_even (16*n+15)
    have hz : r (32*n+30) = 0 := by
      rw [show 32*n+30 = 8*(4*n+3)+6 by ring, r_8n6, periodic_parity]
      have hh : (4*n+3)%4 = 3 := Nat.mul_add_mod_self_left 4 n 3
      rw [hh]; decide
    have hh : r (32*(n+1)) = (r (32*n+30)+r (16*(n+1)))%2 := by
      rw [show 2*(16*n+15)+2 = 32*(n+1) by ring,
          show 2*(16*n+15) = 32*n+30 by ring,
          show 16*n+15+1 = 16*(n+1) by omega] at he
      exact he
    rw [hh, hz, Nat.zero_add, Nat.mod_eq_of_lt (r_lt_two _)]

private theorem r_double16_add (n : ℕ) : r (32*n+16) = 1 - r (16*n+8) := by
  have he := r_even (16*n+7)
  have ho : r (32*n+14) = 1 := by
    rw [show 32*n+14 = 8*(4*n+1)+6 by ring, r_8n6, periodic_parity]
    have hh : (4*n+1)%4 = 1 := Nat.mul_add_mod_self_left 4 n 1
    rw [hh]; decide
  have hh : r (32*n+16) = (r (32*n+14)+r (16*n+8))%2 := by
    rw [show 2*(16*n+7)+2 = 32*n+16 by ring,
        show 2*(16*n+7) = 32*n+14 by ring,
        show 16*n+7+1 = 16*n+8 by omega] at he
    exact he
  rw [hh, ho]
  have hb := r_lt_two (16*n+8)
  omega

private theorem t_even (n : ℕ) : (fun n : ℕ => r (16*n)) (2*n) = (fun n : ℕ => r (16*n)) n := by
  simpa [← Nat.mul_assoc] using r_double16 n

private theorem t_odd (n : ℕ) : (fun n : ℕ => r (16*n)) (2*n+1) = 1 - (n % 4)/2 := by
  simpa [Nat.mul_add, ← Nat.mul_assoc, periodic_eight] using r_double16_add n

end D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

namespace D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

private def B (a b k : ℕ) : ℕ :=
  match k with
  | 0 => a | 1 => 1 | 2 => 1-a | 3 => 0
  | 4 => b%2 | 5 => 1 | 6 => b%2 | 7 => 0
  | 8 => b/2 | 9 => 1 | 10 => 1-b/2 | 11 => 0
  | 12 => 1-b%2 | 13 => 1 | 14 => 1-b%2 | _ => 0

private def F (i a b j : ℕ) : ℕ :=
  let row : List ℕ :=
    if i = 0 then
      match b with
      | 0 => [2*a,3,4,6,7,8,11,15]
      | 1 => [2*a,3,7,8,11,12,14,15]
      | 2 => [2*a,3,4,6,7,10,11,15]
      | _ => [2*a,3,7,10,11,12,14,15]
    else
      match b with
      | 0 => [1-a,2-a,5,9,10,12,13,14]
      | 1 => [1-a,2-a,4,5,6,9,10,13]
      | 2 => [1-a,2-a,5,8,9,12,13,14]
      | _ => [1-a,2-a,4,5,6,8,9,13]
  row.getD j 0

private theorem g_even (n : ℕ) : g ((2*n)%4) = n%2 := by
  have hm : (2*n)%4 = 2*(n%2) := by simpa using (Nat.mul_mod_mul_left 2 n 2)
  rw [hm]
  have hh : n%2 < 2 := Nat.mod_lt _ (by omega)
  generalize n%2 = j at *
  interval_cases j <;> norm_num [g]

private theorem g_odd (n : ℕ) : g ((2*n+1)%4) = 1-n%2 := by
  have hm : (2*n+1)%4 = 2*(n%2)+1 := by
    rw [Nat.add_mod, show (2*n)%4 = 2*(n%2) from Nat.mul_mod_mul_left 2 n 2]
    exact Nat.mod_eq_of_lt (by have h := Nat.mod_lt n (by decide : 0 < 2); omega)
  rw [hm]
  have hh : n%2 < 2 := Nat.mod_lt _ (by omega)
  generalize n%2 = j at *
  interval_cases j <;> norm_num [g]

private theorem block_table (q k : ℕ) (hk : k < 16) :
    r (16*q+k) = B ((fun n : ℕ => r (16*n)) q) (q%4) k := by
  have ho : ∀ j : ℕ, r (16*q+2*j+1) = (j+1)%2 := by
    intro j
    rw [show 16*q+2*j+1 = 2*(8*q+j)+1 by ring, r_odd]
    simpa only [← Nat.mul_assoc, Nat.add_assoc] using (Nat.mul_add_mod_self_left 2 (4*q) (j+1))
  have hg0 : r (16*q+4) = q%2 := by
    rw [show 16*q+4 = 8*(2*q)+4 by ring, periodic_parity, g_even]
  have hg1 : r (16*q+12) = 1-q%2 := by
    rw [show 16*q+12 = 8*(2*q+1)+4 by ring, periodic_parity, g_odd]
  have hh : q%2 = (q%4)%2 := (Nat.mod_mod_of_dvd q (by decide : 2 ∣ 4)).symm
  rw [hh] at hg0 hg1
  interval_cases k
  · rfl
  · simpa [B, Nat.add_assoc] using ho 0
  · simpa [B, ← Nat.mul_assoc] using r_8n2 (2*q)
  · simpa [B, Nat.add_assoc] using ho 1
  · simpa [B, ← Nat.mul_assoc] using hg0
  · simpa [B, Nat.add_assoc] using ho 2
  · rw [show 16*q+6 = 8*(2*q)+6 by ring, r_8n6]
    simpa [B, ← Nat.mul_assoc] using hg0
  · simpa [B, Nat.add_assoc] using ho 3
  · simpa [B] using periodic_eight q
  · simpa [B, Nat.add_assoc] using ho 4
  · rw [show 16*q+10 = 8*(2*q+1)+2 by ring, r_8n2]
    have hx : 8*(2*q+1) = 16*q+8 := by ring
    rw [hx, periodic_eight]
    rfl
  · simpa [B, Nat.add_assoc] using ho 5
  · simpa [B] using hg1
  · simpa [B, Nat.add_assoc] using ho 6
  · rw [show 16*q+14 = 8*(2*q+1)+6 by ring, r_8n6]
    have hx : 8*(2*q+1)+4 = 16*q+12 := by ring
    rw [hx]
    simpa [B] using hg1
  · simpa [B, Nat.add_assoc] using ho 7

private theorem table_balance (i a b : ℕ) (hi : i < 2) (ha : a < 2) (hb : b < 4) :
    Nat.count (fun k => B a b k = i) 16 = 8 := by
  interval_cases i <;> interval_cases a <;> interval_cases b <;> decide

private theorem table_select (i a b j : ℕ) (hi : i < 2) (ha : a < 2)
    (hb : b < 4) (hj : j < 8) :
    F i a b j < 16 ∧ B a b (F i a b j) = i ∧
      Nat.count (fun k => B a b k = i) (F i a b j) = j := by
  interval_cases i <;> interval_cases a <;> interval_cases b <;> interval_cases j <;> decide

private theorem count_in_block (i q k : ℕ) (hk : k ≤ 16) :
    Nat.count (fun m => r (16*q+m) = i) k =
      Nat.count (fun m => B ((fun n : ℕ => r (16*n)) q) (q%4) m = i) k := by
  apply le_antisymm
  · apply Nat.count_mono_left
    intro m hm
    rw [block_table q m (by omega)]
    exact id
  · apply Nat.count_mono_left
    intro m hm
    rw [block_table q m (by omega)]
    exact id

private theorem block_balance (i q : ℕ) (hi : i < 2) :
    Nat.count (fun m => r (16*q+m) = i) 16 = 8 := by
  rw [count_in_block i q 16 (by omega)]
  exact table_balance i ((fun n : ℕ => r (16*n)) q) (q%4) hi (r_lt_two _) (Nat.mod_lt _ (by omega))

private theorem count_blocks (i q : ℕ) (hi : i < 2) :
    Nat.count (fun m => r m = i) (16*q) = 8*q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 16*(q+1) = 16*q+16 by ring, Nat.count_add, ih, block_balance i q hi]
    omega

private theorem nth_block_selection (i q j : ℕ) (hi : i < 2) (hj : j < 8) :
    u i (8*q+j) = 16*q + F i ((fun n : ℕ => r (16*n)) q) (q%4) j := by
  have ht := table_select i ((fun n : ℕ => r (16*n)) q) (q%4) j hi (r_lt_two _) (Nat.mod_lt _ (by omega)) hj
  have hm : r (16*q+F i ((fun n : ℕ => r (16*n)) q) (q%4) j) = i := by
    rw [block_table q _ ht.1]
    exact ht.2.1
  have hc : Nat.count (fun m => r m = i) (16*q+F i ((fun n : ℕ => r (16*n)) q) (q%4) j) = 8*q+j := by
    rw [Nat.count_add, count_blocks i q hi, count_in_block i q _ (by omega), ht.2.2]
  have he := Nat.nth_count (p := fun m => r m = i) hm
  rw [hc] at he
  exact he

end D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

namespace D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

private theorem finite_kernel_of_state {S : Type} [Finite S] (v : ℕ → S)
    (f₀ f₁ : S → S) (hv₀ : ∀ n, v (2*n) = f₀ (v n))
    (hv₁ : ∀ n, v (2*n+1) = f₁ (v n)) (out : S → ℤ) :
    (twoKernel (fun n => out (v n))).Finite := by
  have hrep : ∀ e b : ℕ, b < 2^e → ∃ F : S → S,
      ∀ n, v (2^e*n+b) = F (v n) := by
    intro e
    induction e with
    | zero =>
      intro b hb
      have hb0 : b = 0 := by simpa using hb
      subst b
      exact ⟨id, by simp⟩
    | succ e ih =>
      intro b hb
      have hbd : b / 2 < 2^e := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
        simpa [pow_succ] using hb
      obtain ⟨F, hF⟩ := ih (b/2) hbd
      by_cases hbit : b % 2 = 0
      · refine ⟨f₀ ∘ F, ?_⟩
        intro n
        have hidx : 2^(e+1)*n+b = 2*(2^e*n+b/2) := by
          rw [pow_succ]
          calc
            2^e*2*n+b = 2*(2^e*n)+b := by ring
            _ = _ := by omega
        rw [hidx, hv₀, hF]; rfl
      · have hbit1 : b % 2 = 1 := (Nat.mod_two_eq_zero_or_one b).resolve_left hbit
        refine ⟨f₁ ∘ F, ?_⟩
        intro n
        have hidx : 2^(e+1)*n+b = 2*(2^e*n+b/2)+1 := by
          rw [pow_succ]
          calc
            2^e*2*n+b = 2*(2^e*n)+b := by ring
            _ = _ := by omega
        rw [hidx, hv₁, hF]; rfl
  apply (Set.finite_range (fun F : S → S => fun n => out (F (v n)))).subset
  intro w hw
  obtain ⟨e, b, hb, rfl⟩ := hw
  obtain ⟨F, hF⟩ := hrep e b hb
  exact ⟨F, by funext n; change out (F (v n)) = out (v (2^e*n+b)); rw [hF]⟩

end D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

namespace D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions

private def V (n : ℕ) : ((Fin 2 × Fin 4) × Fin 8) :=
  ((⟨(fun n : ℕ => r (16*n)) (n/8), r_lt_two _⟩, ⟨(n/8)%4, Nat.mod_lt _ (by omega)⟩),
    ⟨n%8, Nat.mod_lt _ (by omega)⟩)

private def vstep (c : ℕ) (s : ((Fin 2 × Fin 4) × Fin 8)) : ((Fin 2 × Fin 4) × Fin 8) :=
  ((⟨if s.2.val < 4 then s.1.1.val else 1 - s.1.2.val / 2, by
      split_ifs
      · exact s.1.1.isLt
      · omega⟩,
    ⟨(2*s.1.2.val+s.2.val/4)%4, Nat.mod_lt _ (by omega)⟩),
    ⟨(2*s.2.val+c)%8, Nat.mod_lt _ (by omega)⟩)

private theorem V_step (n c : ℕ) (hc : c < 2) : V (2*n+c) = vstep c (V n) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      change (fun n : ℕ => r (16*n)) ((2*n+c)/8) = if n%8 < 4 then (fun n : ℕ => r (16*n)) (n/8) else 1-((n/8)%4)/2
      split_ifs with hh
      · have hd : (2*n+c)/8 = 2*(n/8) := by
          conv_lhs => rw [← Nat.div_add_mod n 8]
          rw [Nat.mul_add, Nat.add_assoc,
            show 2*(8*(n/8)) = 8*(2*(n/8)) by ring, Nat.mul_add_div (by decide : 0 < 8)]
          have hzero : (2*(n%8)+c)/8 = 0 := Nat.div_eq_of_lt (by omega)
          rw [hzero, Nat.add_zero]
        rw [hd, t_even]
      · have hd : (2*n+c)/8 = 2*(n/8)+1 := by
          conv_lhs => rw [← Nat.div_add_mod n 8]
          rw [Nat.mul_add, Nat.add_assoc,
            show 2*(8*(n/8)) = 8*(2*(n/8)) by ring, Nat.mul_add_div (by decide : 0 < 8)]
          have hmod := Nat.mod_lt n (by decide : 0 < 8)
          have hone : (2*(n%8)+c)/8 = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
          rw [hone]
        rw [hd, t_odd]
    · apply Fin.ext
      change ((2*n+c)/8)%4 = (2*((n/8)%4)+(n%8)/4)%4
      omega
  · apply Fin.ext
    change (2*n+c)%8 = (2*(n%8)+c)%8
    calc
      (2*n+c)%8 = ((2*n)%8+c%8)%8 := Nat.add_mod _ _ _
      _ = ((2*(n%8))%8+c%8)%8 := by rw [Nat.mul_mod_mod]
      _ = (2*(n%8)+c)%8 := (Nat.add_mod _ _ _).symm

private def out (i : ℕ) (s : ((Fin 2 × Fin 4) × Fin 8)) : ℤ :=
  (F i s.1.1.val s.1.2.val s.2.val : ℤ) - 2 * s.2.val

private def D (i n : ℕ) : ℤ := out i (V n)

private theorem correction_representation (i n : ℕ) (hi : i < 2) :
    (u i n : ℤ) = 2*(n : ℤ) + D i n := by
  have hj : n%8 < 8 := Nat.mod_lt _ (by omega)
  have hsel := nth_block_selection i (n/8) (n%8) hi hj
  have hn : 8*(n/8)+n%8 = n := Nat.div_add_mod n 8
  rw [hn] at hsel
  rw [hsel]
  dsimp [D, out, V]
  push_cast
  have hcast : (n : ℤ) = 8*(n/8 : ℕ)+(n%8 : ℕ) := by exact_mod_cast hn.symm
  omega

private theorem finite_correction_kernel (i : ℕ) : (twoKernel (D i)).Finite := by
  exact finite_kernel_of_state V (vstep 0) (vstep 1)
    (fun n => by simpa using V_step n 0 (by omega))
    (fun n => V_step n 1 (by omega)) (out i)

theorem result : claim := by
  intro i hi
  exact settlement_from_correction i (D i)
    (fun n => correction_representation i n hi) (finite_correction_kernel i)

end D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions
