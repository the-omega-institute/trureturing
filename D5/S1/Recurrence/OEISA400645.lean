/- GID: D5/S1/Recurrence/OEISA400645
   generality: I
   mirror-B: D5/B/S1/Recurrence/OEISA400645
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The signed four-lag rounded norm sequence has Bernáth's exact ratio limit. -/

/-
admission_basis: open-problem-resolution (#22857; Proved)
Each declaration below has escape_witness: none and shares this module basis.
Definition rows are marked bind-only: no separate theorem content is claimed.
Direct frozen dependencies (declaration statement_id, with same-delivery helpers expanded):
F01 = D5/S0/Tower/NonPisotFrontier/BetaThirteen.betaThirteen
  sha256:8ec5bc6200abc165ee082587a39751c49dc5710b051a0faef4f90f2f6a134aa3
F02 = D5/S0/Tower/NonPisotFrontier/BetaThirteen.betaThirteen._proof_1
  sha256:577238736e9f8a9004ed10b4d768c2812eff278aeca0bd7650721586f3de7e4b
F03 = D5/S0/Tower/NonPisotFrontier/BetaThirteen.betaThirteen._proof_2
  sha256:92735f205c84742a2e1cc10ae168f204477a75a242a7423e2e8e6c141608eefb
F04 = D5/S0/Tower/NonPisotFrontier/BetaThirteen.betaThirteen_quadratic
  sha256:c43379138c4fde8f18a1b2a3d8fa229547eda919ef4a86d71562d3c8c1c7c036
F05 = D5/S0/Tower/NonPisotFrontier/BetaThirteen.sqrt_thirteen_bounds
  sha256:5b61555d7442f375d926d61d47555ed5574ae8bef33e0526af98bef43f4c6979
F06 = D5/S0/Tower/NonPisotFrontier/BetaThirteen.sqrt_thirteen_nonneg
  sha256:f99cfc63f468545b1118a52c7b7d708b952af295cb1ce7b191aaf5e24c269586
F07 = D5/S0/Tower/NonPisotFrontier/BetaThirteen.sqrt_thirteen_sq
  sha256:7c84989ae88253e9034db2ade0cecad4af8cda5c79c0a0d578db15077e76e5b5
F08 = D5/S0/Tower/NonPisotFrontier/BetaThirteen.two_lt_betaThirteen
  sha256:282559cbf001c333119bf0f37996c29d49af2d7e1e434bc511bfe8f9810c14b7
F09 = D5/S1/Recurrence/ComplementaryGoldenRatioLimit.vanishing_affine_error
  sha256:7bb8a06de2b2ee62a417c2b4331087431026e784cdf8d928a98ff1eec0b5e4b1
F10 = D5/S1/Recurrence/OEISA400644.sourceRound
  sha256:14d9dbdd7abf39d4b4ca0cd16e46baad3d229092a6c5bfac7f78ea871c805b2a
F11 = D5/S1/Recurrence/OEISA400644.sourceRound_ge_sqrt
  sha256:76adaeec265699d987268ddb04a492d6db3d953b18a6c32698415f1683e97415
F12 = D5/S1/Recurrence/OEISA400644.sourceRound_nearest_unique (private)
  sha256:5ec7dec0e1b8d40bd3d258db419b6ca6aa6b8cbe6448e9dfdc82bb8a9e169bcc
Declaration rows; dependencies refer to the identifiers above:
radicand: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: none;
  consumers: source_fib, seq_spec, err_bound, IsSourceSequence, source_error, source_unique, source_pos.
IsSourceSequence: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: none;
  consumers: source_fib, seq_spec, err_bound, square_asymptotic, source_error, source_growth, dominant_limit, source_mono, result, source_limit, proj_lower, ratio_limit, claim, source_unique, source_pos.
squaredLimit: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: none;
  consumers: r_poly, square_asymptotic, dominant_limit, proj, algebraic_clauses, r_largest, r_bounds, proj_lower, ratio_limit, proj_step, limitingRatio, r_quad.
limitingRatio: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: none;
  consumers: algebraic_clauses, result, source_limit, ratio_limit, claim.
claim: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: none;
  consumers: result.
seq: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: F10;
  consumers: seq_spec, dominant_limit, source_mono, result, source_unique, seq_mono.
seq_mono: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F10, F11;
  consumers: seq_spec, source_mono.
seq_spec: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F12, F10, F11;
  consumers: result, source_unique.
source_unique: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F12, F10, F11;
  consumers: dominant_limit, source_mono.
source_mono: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F12, F10, F11;
  consumers: source_fib, source_error, source_growth, proj_lower, source_pos.
source_pos: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F12, F10, F11;
  consumers: source_error, source_limit, proj_lower.
source_fib: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F12, F10, F11;
  consumers: source_growth.
source_growth: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F12, F10, F11;
  consumers: err_bound.
source_error: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F12, F10, F11;
  consumers: err_bound.
r_bounds: proof_shape: bind-only; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F06;
  consumers: square_asymptotic, dominant_limit, algebraic_clauses, r_largest, proj_lower, ratio_limit, proj_step.
r_quad: proof_shape: bind-only; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F03, F05, F02, F01;
  consumers: r_poly, r_largest.
r_poly: proof_shape: bind-only; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F04, F03, F05, F02, F01;
  consumers: algebraic_clauses, proj_step.
r_largest: proof_shape: bind-only; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F08, F04, F06, F03, F05, F02, F01;
  consumers: algebraic_clauses.
algebraic_clauses: proof_shape: bind-only; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F08, F04, F06, F03, F05, F02, F01;
  consumers: result.
stable_three: proof_shape: bind-only; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F09;
  consumers: square_asymptotic.
b: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: none;
  consumers: square_asymptotic, dominant_limit, proj, err, proj_lower, ratio_limit, proj_step.
err: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: none;
  consumers: err_bound, dominant_limit, proj_step.
proj: proof_shape: bind-only; kind: def; escape_witness: none;
  Direct frozen dependencies: none;
  consumers: square_asymptotic, dominant_limit, proj_lower, proj_step.
proj_step: proof_shape: bind-only; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F04, F06, F03, F05, F02, F01;
  consumers: dominant_limit.
err_bound: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F12, F10, F11;
  consumers: dominant_limit.
proj_lower: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F12, F06, F10, F11;
  consumers: dominant_limit.
dominant_limit: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F04, F12, F06, F03, F05, F10, F02, F01, F11;
  consumers: square_asymptotic.
square_asymptotic: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F04, F12, F06, F03, F05, F10, F09, F02, F01, F11;
  consumers: ratio_limit.
ratio_limit: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F04, F12, F06, F03, F05, F10, F09, F02, F01, F11;
  consumers: source_limit.
source_limit: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F04, F12, F06, F03, F05, F10, F09, F02, F01, F11;
  consumers: result.
result: proof_shape: content; kind: theorem; escape_witness: none;
  Direct frozen dependencies: F07, F08, F04, F12, F06, F03, F05, F10, F09, F02, F01, F11;
  consumers: settling result.
The source radicand uses signed integer subtraction and positive source indices.
The proof applies OEISA400644.sourceRound through its published rounding identity.
No rounding definition or rounding proof is copied into this module.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24271.
-/

import D5.S1.Recurrence.OEISA400644
import D5.S0.Tower.NonPisotFrontier.BetaThirteen
import D5.S1.Recurrence.ComplementaryGoldenRatioLimit

namespace D5.S1.Recurrence.OEISA400645

set_option autoImplicit false

/-- The signed sum inside the source square root, for n ≥ 4. -/
def radicand (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  (a n : ℤ) ^ 2 + (a (n - 1) : ℤ) ^ 2 + (a (n - 2) : ℤ) ^ 2 -
    (a (n - 3) : ℤ) ^ 2

/-- The NAME recurrence and Mathematica initial values, with real nearest rounding.
Integer radicands cannot have a half-integer square root, so the source's
Python threshold and Mathlib rounding have the same value on this domain. -/
def IsSourceSequence (a : ℕ → ℕ) : Prop :=
  a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 1 ∧
    ∀ n : ℕ, 4 ≤ n →
      0 ≤ radicand a n ∧
        (a (n + 1) : ℤ) = round (Real.sqrt (radicand a n : ℝ))

/-- The algebraic constant identified by the source's cross-reference A289917. -/
noncomputable def squaredLimit : ℝ :=
  (1 + Real.sqrt 13 + Real.sqrt (2 * Real.sqrt 13 - 2)) / 4

/-- The conjectured limit sqrt(A289917). -/
noncomputable def limitingRatio : ℝ := Real.sqrt squaredLimit

/-- The full infinite limit assertion, with existence and a largest-real-root clause.
The eventual positivity keeps every quotient in the limiting assertion meaningful. -/
def claim : Prop :=
  (∃ a : ℕ → ℕ, IsSourceSequence a) ∧
    (∀ a : ℕ → ℕ, IsSourceSequence a →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 4 ≤ N ∧
          ∀ n : ℕ, N ≤ n →
            0 < a n ∧
              |(a (n + 1) : ℝ) / (a n : ℝ) - limitingRatio| < ε) ∧
    limitingRatio ^ 8 - limitingRatio ^ 6 - limitingRatio ^ 4 -
      limitingRatio ^ 2 + 1 = 0 ∧
    (∀ x : ℝ, x ^ 8 - x ^ 6 - x ^ 4 - x ^ 2 + 1 = 0 → x ≤ limitingRatio)


open Filter
open D5.S1.Recurrence.OEISA400644 (sourceRound sourceRound_round sourceRound_ge_sqrt)
set_option autoImplicit false
set_option maxHeartbeats 1200000

private def seq : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | n+5 => sourceRound ((seq (n+4)^2 + seq (n+3)^2 + seq (n+2)^2 : ℤ) - seq (n+1)^2).toNat

private theorem seq_mono (n : ℕ) : seq n ≤ seq (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|_|_|_|n
    · simp [seq]
    · simp [seq]
    · simp [seq]
    · simp [seq]
    · have hlo := ih (n+1) (by omega)
      have hs : (seq (n+4):ℤ)^2 ≤ (seq (n+4):ℤ)^2+(seq (n+3):ℤ)^2+
          (seq (n+2):ℤ)^2-(seq (n+1):ℤ)^2 := by
        have h1 : (seq (n+1):ℤ) ≤ seq (n+2) := by exact_mod_cast hlo
        nlinarith [sq_nonneg (seq (n+3):ℤ),sq_nonneg ((seq (n+2):ℤ)-(seq (n+1):ℤ))]
      rw [seq]
      apply le_trans _ (sourceRound_ge_sqrt _)
      apply Nat.le_sqrt.mpr
      have hc : ((seq (n+4)^2 : ℕ):ℤ) ≤
          (seq (n+4):ℤ)^2+(seq (n+3):ℤ)^2+(seq (n+2):ℤ)^2-(seq (n+1):ℤ)^2 := by
        simpa using hs
      simpa only [pow_two] using (Int.le_toNat (le_trans (by positivity) hs)).mpr hc

private theorem seq_spec : IsSourceSequence seq := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro n hn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hm := seq_mono (k+1)
  have h : 0 ≤ radicand seq (4+k) := by
    dsimp [radicand]
    simp only [show 4+k-1=k+3 by omega,show 4+k-2=k+2 by omega,
      show 4+k-3=k+1 by omega]
    have hmz : (seq (k+1):ℤ) ≤ seq (k+2) := by exact_mod_cast hm
    nlinarith [sq_nonneg (seq (4+k):ℤ),sq_nonneg (seq (k+3):ℤ),
      sq_nonneg ((seq (k+2):ℤ)-(seq (k+1):ℤ))]
  refine ⟨h,?_⟩
  rw [show 4+k+1=k+5 by omega, seq]
  have heq : (seq (k+4):ℤ)^2 + (seq (k+3):ℤ)^2 + (seq (k+2):ℤ)^2-(seq (k+1):ℤ)^2 = radicand seq (4+k) := by
    simp [radicand,show 4+k=k+4 by omega,show 4+k-1=k+3 by omega,
      show 4+k-2=k+2 by omega,show 4+k-3=k+1 by omega]
  rw [heq, ← sourceRound_round]
  congr 2
  norm_cast
  exact Int.toNat_of_nonneg h

private theorem source_unique {a : ℕ → ℕ} (ha : IsSourceSequence a) :
    ∀ n : ℕ, 1 ≤ n → a n = seq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases n with _|_|_|_|_|n
    · omega
    · exact ha.1
    · exact ha.2.1
    · exact ha.2.2.1
    · exact ha.2.2.2.1
    · have h := (ha.2.2.2.2 (n+4) (by omega)).2
      have hs := (seq_spec.2.2.2.2 (n+4) (by omega)).2
      have heq : radicand a (n+4) = radicand seq (n+4) := by
        dsimp [radicand]
        simp only [show n+4-1=n+3 by omega,show n+4-2=n+2 by omega,show n+4-3=n+1 by omega]
        rw [ih (n+4) (by omega) (by omega),ih (n+3) (by omega) (by omega),
          ih (n+2) (by omega) (by omega),ih (n+1) (by omega) (by omega)]
      rw [heq] at h
      exact_mod_cast h.trans hs.symm

private theorem source_mono {a : ℕ → ℕ} (ha : IsSourceSequence a)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : a i ≤ a j := by
  rw [source_unique ha i hi,source_unique ha j (by omega)]
  exact (monotone_nat_of_le_succ seq_mono) hij

private theorem source_pos {a : ℕ → ℕ} (ha : IsSourceSequence a)
    {n : ℕ} (hn : 4 ≤ n) : 1 ≤ a n := by
  have := source_mono ha (by omega : 1 ≤ 4) hn
  rwa [ha.2.2.2.1] at this


set_option autoImplicit false
set_option maxHeartbeats 1200000
private theorem source_fib {a : ℕ → ℕ} (ha : IsSourceSequence a)
    (n : ℕ) (hn : 4 ≤ n) : a (n+1) ≤ a n + a (n-1) := by
  have h2 := source_mono ha (by omega : 1 ≤ n-2) (by omega : n-2 ≤ n-1)
  have h1 := source_mono ha (by omega : 1 ≤ n-1) (by omega : n-1 ≤ n)
  have h2r : (a (n-2):ℝ) ≤ a (n-1) := by exact_mod_cast h2
  have h1r : (a (n-1):ℝ) ≤ a n := by exact_mod_cast h1
  have hp : 0 ≤ (a (n-2):ℝ) := by positivity
  have hm : (a (n-2):ℝ)^2 ≤ (a n:ℝ)*(a (n-1):ℝ) :=
    by
      simpa only [pow_two] using mul_le_mul (h2r.trans h1r) h2r hp (by positivity : (0:ℝ) ≤ a n)
  have hrad : (radicand a n:ℝ) ≤ ((a n:ℝ)+(a (n-1):ℝ))^2 := by
    dsimp [radicand]
    push_cast
    nlinarith [sq_nonneg (a (n-3):ℝ)]
  have hs := Real.sq_sqrt (show 0 ≤ (radicand a n:ℝ) by exact_mod_cast (ha.2.2.2.2 n hn).1)
  have hroot : Real.sqrt (radicand a n:ℝ) ≤ (a n:ℝ)+(a (n-1):ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rwa [hs]
  have hr := round_le_add_half (Real.sqrt (radicand a n:ℝ))
  rw [← (ha.2.2.2.2 n hn).2] at hr
  have hlt : (a (n+1):ℝ) < (a n:ℝ)+(a (n-1):ℝ)+1 := by norm_cast at hr; linarith
  have hnat : a (n+1) < a n+a (n-1)+1 := by exact_mod_cast hlt
  omega

private theorem source_growth {a : ℕ → ℕ} (ha : IsSourceSequence a)
    (m : ℕ) (hm : 4 ≤ m) (k : ℕ) :
    (a (m+k):ℝ) ≤ 2*(a m:ℝ)*(5/3:ℝ)^k := by
  induction k using Nat.twoStepInduction with
  | zero => simp only [Nat.add_zero,pow_zero,mul_one]; nlinarith [show (0:ℝ) ≤ a m by positivity]
  | one =>
    have hf := source_fib ha m hm
    have hmo := source_mono ha (by omega : 1 ≤ m-1) (by omega : m-1 ≤ m)
    have hf' : (a (m+1):ℝ) ≤ (a m:ℝ)+(a (m-1):ℝ) := by exact_mod_cast hf
    have hm' : (a (m-1):ℝ) ≤ a m := by exact_mod_cast hmo
    norm_num
    linarith
  | more k ih0 ih1 =>
    have hf := source_fib ha (m+k+1) (by omega)
    have hf' : (a (m+(k+2)):ℝ) ≤ (a (m+(k+1)):ℝ)+(a (m+k):ℝ) := by
      convert (show (a (m+k+1+1):ℝ) ≤ (a (m+k+1):ℝ)+(a (m+k+1-1):ℝ) by exact_mod_cast hf) using 1 <;> congr 1 <;> omega
    rw [pow_succ, pow_succ] at *
    nlinarith [show 0 ≤ (a m:ℝ)*(5/3:ℝ)^k by positivity]

private theorem source_error {a : ℕ → ℕ} (ha : IsSourceSequence a)
    (n : ℕ) (hn : 4 ≤ n) :
    |(a (n+1):ℝ)^2 - (radicand a n:ℝ)| ≤ 2*(a n:ℝ) := by
  have hrec := (ha.2.2.2.2 n hn).2
  have he := abs_sub_round (Real.sqrt (radicand a n:ℝ))
  rw [← hrec] at he
  norm_cast at he
  have hsq := Real.sq_sqrt (show 0 ≤ (radicand a n:ℝ) by exact_mod_cast (ha.2.2.2.2 n hn).1)
  have hs0 := Real.sqrt_nonneg (radicand a n:ℝ)
  have hp : (1:ℝ) ≤ a n := by exact_mod_cast source_pos ha hn
  have h1 : (a (n-1):ℝ) ≤ a n := by exact_mod_cast source_mono ha (by omega : 1 ≤ n-1) (by omega : n-1 ≤ n)
  have h2 : (a (n-2):ℝ) ≤ a n := by exact_mod_cast source_mono ha (by omega : 1 ≤ n-2) (by omega : n-2 ≤ n)
  have hsq1 := (sq_le_sq₀ (by positivity : (0:ℝ) ≤ a (n-1)) (by positivity : (0:ℝ) ≤ a n)).2 h1
  have hsq2 := (sq_le_sq₀ (by positivity : (0:ℝ) ≤ a (n-2)) (by positivity : (0:ℝ) ≤ a n)).2 h2
  have hrad : (radicand a n:ℝ) ≤ 3*(a n:ℝ)^2 := by
    dsimp [radicand]
    push_cast
    nlinarith [sq_nonneg (a (n-3):ℝ)]
  have hr : Real.sqrt (radicand a n:ℝ) ≤ 7/4*(a n:ℝ) := by
    apply (sq_le_sq₀ hs0 (by positivity)).mp
    nlinarith [sq_nonneg (a n:ℝ)]
  obtain ⟨helo,hehi⟩ := abs_le.mp he
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((a (n+1):ℝ)-Real.sqrt (radicand a n:ℝ)),
    mul_nonneg (show 0 ≤ (a (n+1):ℝ) by positivity) hs0]


open Filter
open D5.S0.Tower.NonPisotFrontier.BetaThirteen
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem r_bounds : (17 : ℝ)/10 < squaredLimit ∧ squaredLimit < 7/4 := by
  have hq := sqrt_thirteen_sq
  have hn := sqrt_thirteen_nonneg
  have hlo : (18 : ℝ)/5 < Real.sqrt 13 := by nlinarith
  have hhi : Real.sqrt 13 < (29 : ℝ)/8 := by nlinarith
  have hx : 0 ≤ 2 * Real.sqrt 13 - 2 := by linarith
  have hs := Real.sq_sqrt hx
  have hp := Real.sqrt_nonneg (2 * Real.sqrt 13 - 2)
  have hsl : (11 : ℝ)/5 < Real.sqrt (2 * Real.sqrt 13 - 2) := by nlinarith
  have hsu : Real.sqrt (2 * Real.sqrt 13 - 2) < (19 : ℝ)/8 := by nlinarith
  dsimp [squaredLimit]
  constructor <;> linarith

private theorem r_quad :
    squaredLimit ^ 2 - betaThirteen * squaredLimit + 1 = 0 := by
  have hq := sqrt_thirteen_sq
  have hn := sqrt_thirteen_bounds.1
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.sqrt 13 - 2 by linarith)
  dsimp [squaredLimit, betaThirteen]
  nlinarith

private theorem r_poly :
    squaredLimit ^ 4 - squaredLimit ^ 3 - squaredLimit ^ 2 - squaredLimit + 1 = 0 := by
  have hq := r_quad
  have ht := betaThirteen_quadratic
  linear_combination (squaredLimit^2+(betaThirteen-1)*squaredLimit+1)*hq +
    squaredLimit^2*ht

private theorem r_largest (y : ℝ)
    (hy : y^4-y^3-y^2-y+1=0) : y ≤ squaredLimit := by
  by_contra h
  have hlt : squaredLimit < y := lt_of_not_ge h
  have hr := r_bounds.1
  have ht := two_lt_betaThirteen
  have hu := sqrt_thirteen_bounds.2
  have ht3 : betaThirteen < 5/2 := by dsimp [betaThirteen]; linarith
  have hf : (y^2-betaThirteen*y+1)*(y^2+(betaThirteen-1)*y+1)=0 := by
    have heq : (y^2-betaThirteen*y+1)*(y^2+(betaThirteen-1)*y+1) =
        (y^4-y^3-y^2-y+1) - (betaThirteen^2-betaThirteen-3)*y^2 := by ring
    rw [heq, hy, show betaThirteen^2-betaThirteen-3=0 by linarith [betaThirteen_quadratic]]
    ring
  have hpos : 0 < y^2+(betaThirteen-1)*y+1 := by
    have : 0 < y := by linarith
    have : 0 < betaThirteen-1 := by linarith
    positivity
  have hz := (mul_eq_zero.mp hf).resolve_right hpos.ne'
  have hrq := r_quad
  have hfac : (y-squaredLimit)*(y+squaredLimit-betaThirteen) = 0 := by
    nlinarith [hz,hrq]
  have h1 : 0 < y-squaredLimit := sub_pos.mpr hlt
  have h2 : 0 < y+squaredLimit-betaThirteen := by linarith
  exact (mul_pos h1 h2).ne' hfac

private theorem algebraic_clauses :
    limitingRatio ^ 8 - limitingRatio ^ 6 - limitingRatio ^ 4 -
      limitingRatio ^ 2 + 1 = 0 ∧
    (∀ x : ℝ, x ^ 8 - x ^ 6 - x ^ 4 - x ^ 2 + 1 = 0 → x ≤ limitingRatio) := by
  have hr : 0 < squaredLimit := by linarith [r_bounds.1]
  have hs : limitingRatio^2 = squaredLimit := Real.sq_sqrt hr.le
  have ha : 0 ≤ limitingRatio := Real.sqrt_nonneg _
  constructor
  · rw [show limitingRatio^8=(limitingRatio^2)^4 by ring,
      show limitingRatio^6=(limitingRatio^2)^3 by ring,
      show limitingRatio^4=(limitingRatio^2)^2 by ring,hs]
    exact r_poly
  · intro x hx
    have hp : (x^2)^4-(x^2)^3-(x^2)^2-x^2+1=0 := by convert hx using 1 <;> ring
    have hl := r_largest (x^2) hp
    nlinarith


open Filter
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem stable_three {d f : ℕ → ℝ} {A B C : ℝ}
    (ha : |A| ≤ 1/2) (hb : |B| ≤ 1/5) (hc : |C| ≤ 1/8)
    (hf : Tendsto f atTop (nhds 0))
    (hrec : ∀ n, d (n+3) = f n + A*d (n+2) + B*d (n+1) + C*d n) :
    Tendsto d atTop (nhds 0) := by
  let M : ℕ → ℝ := fun n => |d (n+2)| + (2/5)*|d (n+1)| + (3/20)*|d n|
  have hp (n : ℕ) : 0 ≤ M n := by dsimp [M]; positivity
  have he (n : ℕ) : |d (n+3)| ≤ |f n| + (1/2)*|d (n+2)| +
      (1/5)*|d (n+1)| + (1/8)*|d n| := by
    rw [hrec]
    calc
      _ ≤ |f n| + |A*d (n+2)| + |B*d (n+1)| + |C*d n| := by
        linarith only [abs_add_le (f n) (A*d (n+2)),
          abs_add_le (f n+A*d (n+2)) (B*d (n+1)),
          abs_add_le (f n+A*d (n+2)+B*d (n+1)) (C*d n)]
      _ = |f n| + |A| * |d (n+2)| + |B| * |d (n+1)| + |C| * |d n| := by
        rw [abs_mul,abs_mul,abs_mul]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right ha (abs_nonneg (d (n+2))),
        mul_le_mul_of_nonneg_right hb (abs_nonneg (d (n+1))),
        mul_le_mul_of_nonneg_right hc (abs_nonneg (d n))]
  have hs (n : ℕ) : M (n+1) ≤ (9/10)*M n + |f n| := by
    dsimp [M]
    simp only [Nat.add_assoc,Nat.reduceAdd]
    nlinarith [he n,abs_nonneg (d (n+2)),abs_nonneg (d (n+1)),abs_nonneg (d n)]
  have hm := D5.S1.Recurrence.ComplementaryGoldenRatioLimit.vanishing_affine_error
    (by norm_num : (0:ℝ) ≤ 9/10) (by norm_num : (9:ℝ)/10 < 1) hp hf
    (Eventually.of_forall hs)
  have hm' := hm.const_mul (20/3:ℝ)
  have bound (n : ℕ) : ‖d n‖ ≤ (20/3)*M n := by
    rw [Real.norm_eq_abs]
    dsimp [M]
    nlinarith [abs_nonneg (d (n+2)),abs_nonneg (d (n+1))]
  exact squeeze_zero_norm bound (by simpa using hm')



open Filter
open D5.S1.Recurrence.OEISA400644 (sourceRound)
set_option autoImplicit false
set_option maxHeartbeats 1500000

private noncomputable def b (a : ℕ → ℕ) (n : ℕ) : ℝ := (a (n+23):ℝ)^2
private noncomputable def err (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  b a (n+4)-b a (n+3)-b a (n+2)-b a (n+1)+b a n
private noncomputable def proj (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  b a (n+3)+(squaredLimit-1)*b a (n+2)+
    (squaredLimit^2-squaredLimit-1)*b a (n+1)-b a n/squaredLimit

private theorem proj_step (a : ℕ → ℕ) (n : ℕ) :
    proj a (n+1)=squaredLimit*proj a n+err a n := by
  have hr : squaredLimit ≠ 0 := by linarith [r_bounds.1]
  have hp := r_poly
  dsimp [proj,err]
  simp only [Nat.add_assoc,Nat.reduceAdd]
  field_simp
  linear_combination -b a (n+1)*hp

private theorem err_bound {a : ℕ → ℕ} (ha : IsSourceSequence a) (n : ℕ) :
    |err a n| ≤ 4*(a 26:ℝ)*(5/3:ℝ)^n := by
  have he := source_error ha (n+26) (by omega)
  have hg := source_growth ha 26 (by omega) n
  have hid : err a n = (a (n+26+1):ℝ)^2-(radicand a (n+26):ℝ) := by
    dsimp [err,b,radicand]
    push_cast
    simp only [Nat.add_assoc,Nat.reduceAdd,show n+26-1=n+25 by omega,
      show n+26-2=n+24 by omega,show n+26-3=n+23 by omega]
    ring
  rw [hid]
  have hg' : (a (n+26):ℝ) ≤ 2*(a 26:ℝ)*(5/3:ℝ)^n := by simpa [Nat.add_comm] using hg
  linarith

private theorem proj_lower {a : ℕ → ℕ} (ha : IsSourceSequence a) (n : ℕ) :
    (7/17:ℝ)*b a (n+3) < proj a n := by
  have hr := r_bounds.1
  have hr0 : 0 < squaredLimit := by linarith
  have hcoef : 0 < squaredLimit^2-squaredLimit-1 := by nlinarith
  have hm := source_mono ha (by omega : 1 ≤ n+23) (by omega : n+23 ≤ n+3+23)
  have hmr : (a (n+23):ℝ) ≤ a (n+3+23) := by exact_mod_cast hm
  have hb : b a n ≤ b a (n+3) := (sq_le_sq₀ (by positivity) (by positivity)).mpr hmr
  have hb0 (k : ℕ) : 0 < b a k := by
    dsimp [b]
    have h : (1:ℝ) ≤ a (k+23) := by exact_mod_cast source_pos ha (by omega : 4 ≤ k+23)
    positivity
  have hi : 1/squaredLimit < (10/17:ℝ) := (div_lt_iff₀ hr0).2 (by linarith)
  have hd : b a n/squaredLimit ≤ b a (n+3)/squaredLimit := div_le_div_of_nonneg_right hb hr0.le
  have hm' := mul_lt_mul_of_pos_right hi (hb0 (n+3))
  have hdb : b a n/squaredLimit < (10/17:ℝ)*b a (n+3) :=
    hd.trans_lt (by simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using hm')
  dsimp [proj]
  have hc := mul_nonneg (show 0 ≤ squaredLimit-1 by linarith) (hb0 (n+2)).le
  have hc' := mul_nonneg hcoef.le (hb0 (n+1)).le
  linarith only [hdb,hc,hc']

private theorem dominant_limit {a : ℕ → ℕ} (ha : IsSourceSequence a) :
    ∃ U : ℝ, (73872:ℝ)/17 < U ∧
      Tendsto (fun n => proj a n/squaredLimit^n) atTop (nhds U) := by
  have hr := r_bounds.1
  have hr0 : 0 < squaredLimit := by linarith
  have hrne := hr0.ne'
  have hq : (5/3:ℝ)/squaredLimit < 1 := (div_lt_one hr0).2 (by linarith)
  let v : ℕ → ℝ := fun n => proj a n/squaredLimit^n
  have he (n : ℕ) : dist (v n) (v (n+1)) ≤
      (4*(a 26:ℝ)/squaredLimit)*((5/3:ℝ)/squaredLimit)^n := by
    have hid : v (n+1)-v n = err a n/squaredLimit^(n+1) := by
      dsimp [v]
      rw [proj_step,pow_succ]
      field_simp
      <;> ring
    rw [Real.dist_eq,abs_sub_comm,hid]
    simp only [abs_div,abs_of_pos (pow_pos hr0 _)]
    calc
      _ ≤ (4*(a 26:ℝ)*(5/3:ℝ)^n)/squaredLimit^(n+1) :=
        div_le_div_of_nonneg_right (err_bound ha n) (pow_pos hr0 _).le
      _ = _ := by simp only [div_pow,pow_succ]; field_simp <;> ring
  obtain ⟨U,hU⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric _ _ hq he)
  have hb := dist_le_of_le_geometric_of_tendsto₀ _ _ hq he hU
  have hden : squaredLimit-(5/3:ℝ) > 1/30 := by linarith
  have heq : (4*(a 26:ℝ)/squaredLimit)/(1-(5/3:ℝ)/squaredLimit) =
      4*(a 26:ℝ)/(squaredLimit-5/3) := by field_simp <;> ring
  rw [heq] at hb
  have hseed : a 26=324 := by
    rw [source_unique ha 26 (by omega)]
    have h1 : seq 1=0 := rfl
    have h2 : seq 2=0 := rfl
    have h3 : seq 3=0 := rfl
    have h4 : seq 4=1 := rfl
    have h5 : seq 5=1 := by
      change sourceRound ((seq 4^2+seq 3^2+seq 2^2:ℤ)-seq 1^2).toNat=1
      norm_num [h4,h3,h2,h1,sourceRound]
    have h6 : seq 6=1 := by
      change sourceRound ((seq 5^2+seq 4^2+seq 3^2:ℤ)-seq 2^2).toNat=1
      norm_num [h5,h4,h3,h2,sourceRound]
    have h7 : seq 7=2 := by
      change sourceRound ((seq 6^2+seq 5^2+seq 4^2:ℤ)-seq 3^2).toNat=2
      norm_num [h6,h5,h4,h3,sourceRound]
    have h8 : seq 8=2 := by
      change sourceRound ((seq 7^2+seq 6^2+seq 5^2:ℤ)-seq 4^2).toNat=2
      norm_num [h7,h6,h5,h4,sourceRound]
    have h9 : seq 9=3 := by
      change sourceRound ((seq 8^2+seq 7^2+seq 6^2:ℤ)-seq 5^2).toNat=3
      norm_num [h8,h7,h6,h5,sourceRound]
    have h10 : seq 10=4 := by
      change sourceRound ((seq 9^2+seq 8^2+seq 7^2:ℤ)-seq 6^2).toNat=4
      norm_num [h9,h8,h7,h6,sourceRound]
    have h11 : seq 11=5 := by
      change sourceRound ((seq 10^2+seq 9^2+seq 8^2:ℤ)-seq 7^2).toNat=5
      norm_num [h10,h9,h8,h7,sourceRound]
    have h12 : seq 12=7 := by
      change sourceRound ((seq 11^2+seq 10^2+seq 9^2:ℤ)-seq 8^2).toNat=7
      norm_num [h11,h10,h9,h8,sourceRound]
    have h13 : seq 13=9 := by
      change sourceRound ((seq 12^2+seq 11^2+seq 10^2:ℤ)-seq 9^2).toNat=9
      norm_num [h12,h11,h10,h9,sourceRound]
    have h14 : seq 14=12 := by
      change sourceRound ((seq 13^2+seq 12^2+seq 11^2:ℤ)-seq 10^2).toNat=12
      norm_num [h13,h12,h11,h10,sourceRound]
    have h15 : seq 15=16 := by
      change sourceRound ((seq 14^2+seq 13^2+seq 12^2:ℤ)-seq 11^2).toNat=16
      norm_num [h14,h13,h12,h11,sourceRound]
    have h16 : seq 16=21 := by
      change sourceRound ((seq 15^2+seq 14^2+seq 13^2:ℤ)-seq 12^2).toNat=21
      norm_num [h15,h14,h13,h12,sourceRound]
    have h17 : seq 17=28 := by
      change sourceRound ((seq 16^2+seq 15^2+seq 14^2:ℤ)-seq 13^2).toNat=28
      norm_num [h16,h15,h14,h13,sourceRound]
    have h18 : seq 18=37 := by
      change sourceRound ((seq 17^2+seq 16^2+seq 15^2:ℤ)-seq 14^2).toNat=37
      norm_num [h17,h16,h15,h14,sourceRound]
    have h19 : seq 19=48 := by
      change sourceRound ((seq 18^2+seq 17^2+seq 16^2:ℤ)-seq 15^2).toNat=48
      norm_num [h18,h17,h16,h15,sourceRound]
    have h20 : seq 20=63 := by
      change sourceRound ((seq 19^2+seq 18^2+seq 17^2:ℤ)-seq 16^2).toNat=63
      norm_num [h19,h18,h17,h16,sourceRound]
    have h21 : seq 21=83 := by
      change sourceRound ((seq 20^2+seq 19^2+seq 18^2:ℤ)-seq 17^2).toNat=83
      norm_num [h20,h19,h18,h17,sourceRound]
    have h22 : seq 22=109 := by
      change sourceRound ((seq 21^2+seq 20^2+seq 19^2:ℤ)-seq 18^2).toNat=109
      norm_num [h21,h20,h19,h18,sourceRound]
    have h23 : seq 23=143 := by
      change sourceRound ((seq 22^2+seq 21^2+seq 20^2:ℤ)-seq 19^2).toNat=143
      norm_num [h22,h21,h20,h19,sourceRound]
    have h24 : seq 24=188 := by
      change sourceRound ((seq 23^2+seq 22^2+seq 21^2:ℤ)-seq 20^2).toNat=188
      norm_num [h23,h22,h21,h20,sourceRound]
    have h25 : seq 25=247 := by
      change sourceRound ((seq 24^2+seq 23^2+seq 22^2:ℤ)-seq 21^2).toNat=247
      norm_num [h24,h23,h22,h21,sourceRound]
    have h26 : seq 26=324 := by
      change sourceRound ((seq 25^2+seq 24^2+seq 23^2:ℤ)-seq 22^2).toNat=324
      norm_num [h25,h24,h23,h22,sourceRound]
    exact h26
  have hseedr : (a 26:ℝ)=324 := by exact_mod_cast hseed
  have htail : 4*(a 26:ℝ)/(squaredLimit-5/3) < 120*(a 26:ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0 < squaredLimit-5/3)).2
    rw [hseedr]
    nlinarith
  have hlo := proj_lower ha 0
  have hstart : b a (0+3)=(a 26:ℝ)^2 := by simp [b]
  rw [hstart,hseedr] at hlo
  have hu : proj a 0-U ≤ 4*(a 26:ℝ)/(squaredLimit-5/3) := by
    have := (abs_le.mp (show |proj a 0-U| ≤ _ by simpa [v,Real.dist_eq] using hb)).2
    exact this
  refine ⟨U,?_,hU⟩
  rw [hseedr] at hu htail
  linarith


open Filter
open D5.S1.Recurrence.OEISA400644 (sourceRound)
set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem square_asymptotic {a : ℕ → ℕ} (ha : IsSourceSequence a) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (fun n => b a n/squaredLimit^n) atTop (nhds L) := by
  obtain ⟨U,hUpos,hU⟩ := dominant_limit ha
  have hr := r_bounds
  have hr0 : 0 < squaredLimit := by linarith [hr.1]
  have hrne := hr0.ne'
  let A : ℝ := (squaredLimit-1)/squaredLimit
  let B : ℝ := (squaredLimit^2-squaredLimit-1)/squaredLimit^2
  let C : ℝ := 1/squaredLimit^4
  have ha0 : 0 ≤ A := div_nonneg (by linarith [hr.1]) hr0.le
  have hb0 : 0 ≤ B := div_nonneg (by nlinarith [hr.1]) (sq_nonneg _)
  have hc0 : 0 ≤ C := by dsimp [C]; positivity
  have ha1 : A ≤ 1/2 := by
    dsimp [A]
    apply (div_le_iff₀ hr0).2
    linarith [hr.2]
  have hb1 : B ≤ 1/5 := by
    dsimp [B]
    apply (div_le_iff₀ (pow_pos hr0 2)).2
    nlinarith [sq_nonneg (squaredLimit-7/4)]
  have hc1 : C ≤ 1/8 := by
    dsimp [C]
    apply (div_le_iff₀ (pow_pos hr0 4)).2
    have hs : (289:ℝ)/100 < squaredLimit^2 := by nlinarith [hr.1]
    nlinarith [sq_nonneg (squaredLimit^2-289/100)]
  have hk : 0 < 1+A+B-C := by linarith
  let L : ℝ := (U/squaredLimit^3)/(1+A+B-C)
  let x : ℕ → ℝ := fun n => b a n/squaredLimit^n
  let d : ℕ → ℝ := fun n => x n-L
  let f : ℕ → ℝ := fun n => proj a n/squaredLimit^(n+3)-U/squaredLimit^3
  have hf : Tendsto f atTop (nhds 0) := by
    have h := (hU.div_const (squaredLimit^3)).sub_const (U/squaredLimit^3)
    simpa [f,pow_add,div_div] using h
  have hid (n : ℕ) : x (n+3) = proj a n/squaredLimit^(n+3) -
      A*x (n+2)-B*x (n+1)+C*x n := by
    dsimp [x,A,B,C,proj]
    simp only [pow_add]
    field_simp
    <;> ring
  have hcenter : (1+A+B-C)*L=U/squaredLimit^3 := by
    dsimp [L]
    exact mul_div_cancel₀ _ hk.ne'
  have hrec (n : ℕ) : d (n+3)=f n+(-A)*d (n+2)+(-B)*d (n+1)+C*d n := by
    dsimp [d,f]
    rw [hid]
    nlinarith [hcenter]
  have hd := stable_three (by simpa [abs_of_nonneg ha0] using ha1)
    (by simpa [abs_of_nonneg hb0] using hb1)
    (by simpa [abs_of_nonneg hc0] using hc1) hf hrec
  refine ⟨L,div_pos (div_pos (by linarith) (pow_pos hr0 3)) hk,?_⟩
  have h := hd.add_const L
  simpa [d,x] using h

private theorem ratio_limit {a : ℕ → ℕ} (ha : IsSourceSequence a) :
    Tendsto (fun n => (a (n+24):ℝ)/(a (n+23):ℝ)) atTop (nhds limitingRatio) := by
  obtain ⟨L,hL,hl⟩ := square_asymptotic ha
  have hr0 : 0 < squaredLimit := by linarith [r_bounds.1]
  have hs := (tendsto_add_atTop_iff_nat 1).2 hl
  have ht := ((hs.div hl hL.ne').const_mul squaredLimit)
  have hid (n : ℕ) : squaredLimit*((b a (n+1)/squaredLimit^(n+1))/(b a n/squaredLimit^n)) =
      b a (n+1)/b a n := by
    rw [pow_succ]
    field_simp
  have hb : Tendsto (fun n => b a (n+1)/b a n) atTop (nhds squaredLimit) := by
    change Tendsto (fun n => squaredLimit*((b a (n+1)/squaredLimit^(n+1))/(b a n/squaredLimit^n)))
      atTop (nhds (squaredLimit*(L/L))) at ht
    simpa only [hid,div_self hL.ne',mul_one] using ht
  have heq (n : ℕ) : (a (n+24):ℝ)/(a (n+23):ℝ) = Real.sqrt (b a (n+1)/b a n) := by
    dsimp [b]
    simp only [Nat.add_assoc,Nat.reduceAdd]
    rw [← div_pow,Real.sqrt_sq (div_nonneg (by positivity) (by positivity))]
  simp_rw [heq]
  exact Real.continuous_sqrt.continuousAt.tendsto.comp hb

private theorem source_limit {a : ℕ → ℕ} (ha : IsSourceSequence a) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      0 < a n ∧ |(a (n+1):ℝ)/(a n:ℝ)-limitingRatio| < ε := by
  intro ε he
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (ratio_limit ha) ε he
  refine ⟨N+23,by omega,?_⟩
  intro n hn
  refine ⟨lt_of_lt_of_le Nat.zero_lt_one (source_pos ha (by omega)),?_⟩
  have h := hN (n-23) (by omega)
  simpa [Real.dist_eq,show n-23+24=n+1 by omega,show n-23+23=n by omega] using h

theorem result : D5.S1.Recurrence.OEISA400645.claim := by
  exact ⟨⟨seq,seq_spec⟩,fun a ha => source_limit ha,algebraic_clauses⟩

end D5.S1.Recurrence.OEISA400645
