/- GID: D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.claim; result=D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.result; claim=D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.claim
   digest: A circulant unistochastic matrix of order ten has no circulant unitary lift. -/

/- open-problem-resolution (#16445; Refuted)

result
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#16445; Refuted)
  Direct frozen dependencies:
    D5/S3/Weil/ZetaLinear/VonNeumann.normSqMatrix
    statement_id: sha256:e52dbe98c1d31846023642a54bf054704c393626b7a8169c76de496f1c932bea
    D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsCirculant
    statement_id: sha256:50b3aebf79213311db8734fe04a47650cc34177e19c9f68dcd33808ba715a3a1
    D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.IsUnistochastic
    statement_id: sha256:c7f755de67eb34a3688f8ec2ca6ccd1f56fdc2489f30af64bfc1feec16e32a02

Every private theorem is bind-only; its consumers are:
  int_orthogonal: u_unitary.
  u_unitary: b_unistochastic.
  b_eq: b_circulant, lift_moduli.
  b_circulant, b_unistochastic: result.
  lift_moduli, support_from_moduli, sparse_rows, phase_product_zero:
    no_circulant_lift.
  no_circulant_lift: result.
After inlining local helpers, b_eq, lift_moduli and no_circulant_lift use
RHLinalg.normSqMatrix; b_circulant also uses IsCirculant, and b_unistochastic
also uses IsUnistochastic. The remaining private theorems have no direct frozen
D5 dependencies. HasCirculantLift uses normSqMatrix; claim uses all three frozen
definitions listed above. Q, W, U and b have no direct frozen D5 dependency.
No declaration asserts an escape witness.

The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).

IsCirculant and IsUnistochastic are reused from the frozen companion module.
HasCirculantLift and claim express Conjecture 19 using those source predicates.
The private integer matrix Q uses block coordinates i = 5a+r and j = 5b+s;
W = 3I+2Q and U = W/5. Its squared-norm matrix has first row
(9,4,0,0,4,0,4,0,0,4)/25. The row equations at shifts 1,4,3 force
z(9) conj(z(6)) = 0 although both factors have nonzero modulus.
-/
import D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic

noncomputable section
open Matrix Finset
open scoped ComplexConjugate
open D5.S3.Quantum.Matrix.CirculantBraceletNonUnistochastic

namespace D5.S3.Quantum.Matrix.CirculantUnitaryLiftRefutation

def HasCirculantLift {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ z : Fin d → ℂ, Matrix.circulant z ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
    B = RHLinalg.normSqMatrix (Matrix.circulant z)

def claim : Prop :=
  ∀ d : ℕ, ∀ B : Matrix (Fin d) (Fin d) ℝ,
    IsCirculant B → IsUnistochastic B → HasCirculantLift B

private def Q : Matrix (Fin 10) (Fin 10) ℤ := Matrix.of fun i j =>
  (if i.val / 5 = 0 then 1 else -1) *
    (if j.val % 5 = (i.val % 5 + 1) % 5 then 1 else 0) -
  (if j.val / 5 = 0 then 1 else -1) *
    (if i.val % 5 = (j.val % 5 + 1) % 5 then 1 else 0)

private def W : Matrix (Fin 10) (Fin 10) ℤ :=
  (3 : ℤ) • 1 + (2 : ℤ) • Q

private def U : Matrix (Fin 10) (Fin 10) ℂ := Matrix.of fun i j => (W i j : ℂ) / 5

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
-- The kernel reduces the hundred entries of the integer orthogonality certificate.
private theorem int_orthogonal : W * Wᵀ = (25 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  decide

private theorem u_unitary : U ∈ Matrix.unitaryGroup (Fin 10) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have hi := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℤ => M i j) int_orthogonal
  have hc := congrArg (fun x : ℤ => (x : ℂ)) hi
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Int.cast_sum, Int.cast_mul] at hc
  simp only [Matrix.mul_apply, Matrix.star_apply, U, Matrix.of_apply, star_div₀,
    star_intCast, star_ofNat, div_mul_div_comm]
  norm_num only
  rw [← Finset.sum_div, hc]
  by_cases hij : i = j
  · subst j
    norm_num [Matrix.one_apply]
  · simp [hij]

private def b (s : Fin 10) : ℝ :=
  if s.val = 0 then 9/25 else
    if s.val = 1 ∨ s.val = 9 ∨ s.val = 4 ∨ s.val = 6 then 4/25 else 0

set_option maxHeartbeats 2000000 in
-- There are one hundred squared-norm entries to normalize.
private theorem b_eq : (RHLinalg.normSqMatrix U) = Matrix.circulant b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [RHLinalg.normSqMatrix, U, W, Q, b, Matrix.circulant_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.ofNat_apply,
      Complex.sq_norm, Complex.normSq_apply, Matrix.of_apply, Fin.sub_def, Fin.neg_def, Fin.val_neg']

private theorem b_circulant : IsCirculant (RHLinalg.normSqMatrix U) := ⟨b, b_eq⟩
private theorem b_unistochastic : IsUnistochastic (RHLinalg.normSqMatrix U) := ⟨U, u_unitary, rfl⟩

private theorem lift_moduli (z : Fin 10 → ℂ)
    (hb : (RHLinalg.normSqMatrix U) = RHLinalg.normSqMatrix (Matrix.circulant z)) (s : Fin 10) :
    ‖z s‖ ^ 2 = b s := by
  have hs := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℝ => M s 0) hb
  rw [b_eq] at hs
  simpa [RHLinalg.normSqMatrix, Matrix.circulant_apply] using hs.symm

private theorem support_from_moduli (z : Fin 10 → ℂ)
    (hn : ∀ s, ‖z s‖ ^ 2 = b s) (s : Fin 10) :
    z s ≠ 0 ↔ s = 0 ∨ s = 1 ∨ s = 9 ∨ s = 4 ∨ s = 6 := by
  have hz0 : z s = 0 ↔ b s = 0 := by
    constructor
    · intro hh
      rw [← hn s]
      simp [hh]
    · intro hh
      have hsq : ‖z s‖ ^ 2 = 0 := (hn s).trans hh
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  rw [ne_eq, hz0]
  fin_cases s <;> norm_num [b, Fin.ext_iff]

private theorem sparse_rows (z : Fin 10 → ℂ)
    (hz : ∀ s, z s ≠ 0 ↔ s = 0 ∨ s = 1 ∨ s = 9 ∨ s = 4 ∨ s = 6)
    (hu : Matrix.circulant z ∈ Matrix.unitaryGroup (Fin 10) ℂ) :
    (z 0 * conj (z 9) + z 1 * conj (z 0) = 0) ∧
    (z 0 * conj (z 6) + z 4 * conj (z 0) = 0) ∧
    (z 4 * conj (z 1) + z 9 * conj (z 6) = 0) := by
  have hzero (s : Fin 10) (hs : ¬(s = 0 ∨ s = 1 ∨ s = 9 ∨ s = 4 ∨ s = 6)) :
      z s = 0 := by
    by_contra h
    exact hs ((hz s).mp h)
  have h2 : z 2 = 0 := hzero 2 (by decide)
  have h3 : z 3 = 0 := hzero 3 (by decide)
  have h5 : z 5 = 0 := hzero 5 (by decide)
  have h7 : z 7 = 0 := hzero 7 (by decide)
  have h8 : z 8 = 0 := hzero 8 (by decide)
  have hrow (h : Fin 10) (hh : h ≠ 0) :
      ∑ k : Fin 10, z (h - k) * conj (z (0 - k)) = 0 := by
    have hm := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℂ => M h 0)
      (Unitary.mul_star_self_of_mem hu)
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.circulant_apply, hh] using hm
  have h1 := hrow 1 (by decide)
  have h4 := hrow 4 (by decide)
  have h3' := hrow 3 (by decide)
  simp only [Fin.sum_univ_succ, Fin.sub_def, Fin.val_succ,
    Fin.coe_ofNat_eq_mod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
    Fin.reduceFinMk, h2, h3, h5, h7, h8, map_zero, mul_zero, zero_mul,
    add_zero, zero_add] at h1 h4 h3'
  exact ⟨by simpa [add_comm] using h1, by simpa [add_comm] using h4,
    by simpa [add_comm] using h3'⟩

private theorem phase_product_zero (a b c d e : ℂ) (ha : a ≠ 0)
    (h1 : a * conj c + b * conj a = 0)
    (h4 : a * conj e + d * conj a = 0)
    (h3 : d * conj b + c * conj e = 0) : c * conj e = 0 := by
  have hc1 : conj a * c + conj b * a = 0 := by
    simpa using congrArg conj h1
  have hprod : a * (c * conj e - d * conj b) = 0 := by
    linear_combination c * h4 - d * hc1
  have heq : c * conj e - d * conj b = 0 :=
    (mul_eq_zero.mp hprod).resolve_left ha
  have htwice : (2 : ℂ) * (c * conj e) = 0 := by
    linear_combination h3 + heq
  exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)

private theorem no_circulant_lift : ¬ HasCirculantLift (RHLinalg.normSqMatrix U) := by
  rintro ⟨z, hu, hb⟩
  have hs := support_from_moduli z (lift_moduli z hb)
  have hz0 : z 0 ≠ 0 := (hs 0).mpr (by simp)
  have hz9 : z 9 ≠ 0 := (hs 9).mpr (by simp)
  have hz6 : z 6 ≠ 0 := (hs 6).mpr (by simp)
  obtain ⟨h1, h4, h3⟩ := sparse_rows z hs hu
  have hp := phase_product_zero (z 0) (z 1) (z 9) (z 4) (z 6) hz0 h1 h4 h3
  rcases mul_eq_zero.mp hp with hc | he
  · exact hz9 hc
  · apply hz6
    simpa using congrArg conj he

theorem result : ¬ claim := by
  intro h
  exact no_circulant_lift (h 10 (RHLinalg.normSqMatrix U) b_circulant b_unistochastic)


end D5.S3.Quantum.Matrix.CirculantUnitaryLiftRefutation
