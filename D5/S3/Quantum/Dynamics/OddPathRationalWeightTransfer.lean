/- GID: D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/OddPathRationalWeightTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational positive weights forbid end-to-end transfer at time pi on every odd path. -/

import D5.S3.Quantum.Dynamics.PathMiddleVertexMoments
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.OddPathRationalWeightTransfer

open Matrix Polynomial Finset Complex
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open D5.S3.Quantum.Dynamics.PathMiddleVertexMoments

section Gram

/-- The powers of a reversal-invariant matrix are reversal invariant. -/
private theorem pow_rev {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hsym : ∀ x y, M x.rev y.rev = M x y) (a : ℕ) :
    ∀ x y, (M ^ a) x.rev y.rev = (M ^ a) x y := by
  induction a with
  | zero =>
    intro x y
    simp [Matrix.one_apply, Fin.rev_inj]
  | succ a ih =>
    intro x y
    rw [pow_succ, mul_apply, mul_apply]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun l => ?_
    have h1 := ih x l.rev
    have h2 := hsym l.rev y
    rw [Fin.rev_rev] at h1 h2
    rw [Fin.revPerm_apply, h1, h2]

variable {m : ℕ} (r : Fin (2 * m) → ℝ) (q : Fin (2 * m + 1) → ℝ)

/-- **Gram determinant of the middle-vertex moments.** For a reversal-invariant path Hamiltonian
`H` on `2m + 1` vertices with middle vertex `c`, and `j ≤ m`, the Hankel determinant of the
moments `(H ^ (a + b)) c c`, `a, b ≤ j`, equals `2 ^ j` times the square of the product over
`a ≤ j` of the products of the `a` edge weights following the middle vertex. -/
theorem middle_moment_gram_det
    (hsym : ∀ x y : Fin (2 * m + 1), pathHamiltonian r q x.rev y.rev = pathHamiltonian r q x y)
    (c : Fin (2 * m + 1)) (hc : (c : ℕ) = m) (j : ℕ) (hj : j ≤ m) :
    (Matrix.of fun a b : Fin (j + 1) => (pathHamiltonian r q ^ ((a : ℕ) + b)) c c).det =
      2 ^ j * (∏ a : Fin (j + 1), ∏ t : Fin a,
        (r ⟨m + t, by have := a.isLt; have := t.isLt; omega⟩ : ℂ)) ^ 2 := by
  classical
  have hcrev : c.rev = c := Fin.ext (by rw [Fin.val_rev, hc]; omega)
  have hT : ∀ (a : ℕ) (i : Fin (2 * m + 1)),
      (pathHamiltonian r q ^ a) c i = (pathHamiltonian r q ^ a) i c := by
    intro a i
    have h := congrFun (congrFun (Matrix.transpose_pow (pathHamiltonian r q) a) i) c
    rw [pathHamiltonian_transpose, transpose_apply] at h
    exact h
  have hrev : ∀ (a : ℕ) (x : Fin (2 * m + 1)),
      (pathHamiltonian r q ^ a) x.rev c = (pathHamiltonian r q ^ a) x c := by
    intro a x
    have h := pow_rev (pathHamiltonian r q) hsym a x c
    rwa [hcrev] at h
  set emb : Fin (j + 1) → Fin (2 * m + 1) := fun d => ⟨m + d, by have := d.isLt; omega⟩
    with hemb
  have hembv : ∀ d, (emb d : ℕ) = m + d := fun d => rfl
  have hinj : Function.Injective emb := fun d e h =>
    Fin.ext (by have h' := congrArg Fin.val h; rw [hembv, hembv] at h'; omega)
  set L : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ :=
    Matrix.of fun a d => (pathHamiltonian r q ^ (a : ℕ)) (emb d) c with hL
  set ε : Fin (j + 1) → ℂ := fun d => if d = 0 then 1 else 2 with hε
  have hfac : (Matrix.of fun a b : Fin (j + 1) => (pathHamiltonian r q ^ ((a : ℕ) + b)) c c) =
      L * diagonal ε * Lᵀ := by
    ext a b
    rw [of_apply, mul_apply, pow_add, mul_apply]
    simp only [mul_diagonal, transpose_apply, hL, of_apply, hT]
    set F : Fin (2 * m + 1) → ℂ := fun i =>
      (pathHamiltonian r q ^ (a : ℕ)) i c * (pathHamiltonian r q ^ (b : ℕ)) i c with hF
    have hFrev : ∀ i, F i.rev = F i := fun i => by simp only [hF, hrev]
    have hsplit : ∑ i, F i =
        ∑ i, ((if c ≤ i then F i else 0) + (if c < i then F i else 0)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
        ← Finset.sum_filter_add_sum_filter_not univ (fun i => c ≤ i) F]
      congr 1
      refine Finset.sum_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_
      · intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨mem_univ _, Fin.lt_def.mpr ?_⟩
        have := Fin.le_def.not.mp hi'
        rw [Fin.val_rev]
        omega
      · intro i hi
        have hi' := Fin.lt_def.mp (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨mem_univ _, fun h => ?_⟩
        have := Fin.le_def.mp h
        rw [Fin.val_rev] at this
        omega
      · intro i _
        exact Fin.rev_rev i
      · intro i _
        exact Fin.rev_rev i
      · intro i _
        exact (hFrev i).symm
    change ∑ i, F i = _
    rw [hsplit]
    symm
    refine Fintype.sum_of_injective emb hinj _ _ (fun i hi => ?_) (fun d => ?_)
    · by_cases hci : c ≤ i
      · have hci' := Fin.le_def.mp hci
        have hi' : m + j < (i : ℕ) := by
          by_contra hlt
          exact hi ⟨⟨(i : ℕ) - m, by omega⟩, Fin.ext (by rw [hembv]; simp only []; omega)⟩
        have h0 : F i = 0 := by
          simp only [hF]
          rw [(pathHamiltonian_pow_apply_column r q c a i).1
            (Or.inl (by have := a.isLt; omega)), zero_mul]
        simp [h0]
      · have hci' : ¬ c < i := fun h => hci h.le
        simp [hci, hci']
    · have hle : c ≤ emb d := Fin.le_def.mpr (by rw [hembv]; omega)
      rw [if_pos hle]
      by_cases hd : d = 0
      · have hlt : ¬ c < emb d := fun h => by
          have := Fin.lt_def.mp h
          rw [hembv, hd] at this
          simp at this
          omega
        rw [if_neg hlt]
        simp only [hε, hF, if_pos hd]
        ring
      · have hd' : (d : ℕ) ≠ 0 := fun h => hd (Fin.ext h)
        have hlt : c < emb d := Fin.lt_def.mpr (by rw [hembv]; omega)
        rw [if_pos hlt]
        simp only [hε, hF, if_neg hd]
        ring
  have hLtri : L.IsLowerTriangular := by
    intro a d had
    have had' : (a : ℕ) < d := Fin.lt_def.mp had
    simp only [hL, of_apply]
    exact (pathHamiltonian_pow_apply_column r q c a (emb d)).1 (Or.inl (by rw [hembv]; omega))
  have hdiag : ∀ d : Fin (j + 1), L d d = ∏ t : Fin d,
      (r ⟨m + t, by have := d.isLt; have := t.isLt; omega⟩ : ℂ) := by
    intro d
    simp only [hL, of_apply]
    rw [(pathHamiltonian_pow_apply_column r q c d (emb d)).2 (by rw [hembv]; omega),
      Finset.prod_range]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [dif_pos (by have := t.isLt; have := d.isLt; omega)]
    congr 2
    exact Fin.ext (by simp [hc])
  have hεprod : ∏ d, ε d = 2 ^ j := by
    simp [hε, Fin.prod_univ_succ, Fin.succ_ne_zero]
  rw [hfac, det_mul, det_mul, det_transpose, det_diagonal, hεprod,
    Matrix.det_of_isLowerTriangular L hLtri, Finset.prod_congr rfl fun d _ => hdiag d]
  ring

end Gram

section Parity

/-- For `q` odd and `s < 2 ^ (v + 1)`, the binomial coefficient `C(2 ^ v * q, s)` is odd exactly
when `s = 0` or `s = 2 ^ v`. -/
private theorem choose_two_pow_mul_odd (v q s : ℕ) (hq : Odd q) (hs : s < 2 ^ (v + 1)) :
    (((2 ^ v * q).choose s : ℕ) : ZMod 2) = if s = 0 ∨ s = 2 ^ v then 1 else 0 := by
  have hX : (X + 1 : (ZMod 2)[X]) ^ (2 ^ v * q) = expand (ZMod 2) (2 ^ v) ((X + 1) ^ q) := by
    rw [pow_mul, add_pow_char_pow, one_pow, map_pow, map_add, expand_X, map_one]
  have hc := congrArg (fun f => f.coeff s) hX
  simp only [coeff_X_add_one_pow, coeff_expand (pow_pos two_pos v)] at hc
  rw [hc]
  by_cases hd : 2 ^ v ∣ s
  · obtain ⟨t, rfl⟩ := hd
    have ht : t < 2 := by
      rw [pow_succ] at hs
      exact Nat.lt_of_mul_lt_mul_left hs
    rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos two_pos v)]
    interval_cases t
    · simp
    · simp [ZMod.natCast_eq_one_iff_odd.mpr hq]
  · rw [if_neg hd, if_neg]
    rintro (h | h)
    · exact hd (h ▸ dvd_zero _)
    · exact hd (h ▸ dvd_rfl)

/-- A matrix over `ZMod 2` with a column permutation of determinant one is nonsingular. -/
private theorem det_ne_zero_of_submatrix {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2))
    (σ : Equiv.Perm (Fin n)) (h : (N.submatrix id σ).det = 1) : N.det ≠ 0 := by
  intro h0
  rw [Matrix.det_permute', h0, mul_zero] at h
  exact zero_ne_one h

/-- The Hankel matrix `[C(m, a + b)]` of size `m + 1` is nonsingular modulo `2`: it is
anti-triangular with unit anti-diagonal. -/
private theorem det_choose_antitriangular (m : ℕ) :
    (Matrix.of fun a b : Fin (m + 1) => ((m.choose ((a : ℕ) + b) : ℕ) : ZMod 2)).det ≠ 0 := by
  refine det_ne_zero_of_submatrix _ Fin.revPerm ?_
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [submatrix_apply, id, of_apply, Fin.revPerm_apply, Fin.val_rev]
    rw [show (a : ℕ) + (m + 1 - (a + 1)) = m by have := a.isLt; omega, Nat.choose_self,
      Nat.cast_one]
  · intro a b hab
    have hab' : (b : ℕ) < a := Fin.lt_def.mp hab
    simp only [submatrix_apply, id, of_apply, Fin.revPerm_apply, Fin.val_rev]
    rw [Nat.choose_eq_zero_of_lt (by have := a.isLt; omega), Nat.cast_zero]

/-- For `q` odd, the Hankel matrix `[C(2 ^ v * q, a + b)]` of size `2 ^ v` is nonsingular modulo
`2`: it is the permutation matrix of `0 ↦ 0`, `a ↦ 2 ^ v - a`. -/
private theorem det_choose_two_pow (v q j : ℕ) (hq : Odd q) (hj : j + 1 = 2 ^ v) :
    (Matrix.of fun a b : Fin (j + 1) =>
      (((2 ^ v * q).choose ((a : ℕ) + b) : ℕ) : ZMod 2)).det ≠ 0 := by
  set f : Fin (j + 1) → Fin (j + 1) := fun a =>
    if h : (a : ℕ) = 0 then a else ⟨j + 1 - a, by omega⟩ with hf
  have hfv : ∀ a : Fin (j + 1), (f a : ℕ) = if (a : ℕ) = 0 then 0 else j + 1 - a := by
    intro a
    simp only [hf]
    split_ifs with h
    · exact h
    · rfl
  have hinv : Function.Involutive f := by
    intro a
    refine Fin.ext ?_
    rw [hfv, hfv]
    have := a.isLt
    split_ifs <;> omega
  refine det_ne_zero_of_submatrix _ hinv.toPerm ?_
  have hone : (Matrix.of fun a b : Fin (j + 1) =>
      (((2 ^ v * q).choose ((a : ℕ) + b) : ℕ) : ZMod 2)).submatrix id hinv.toPerm = 1 := by
    ext a b
    have ha := a.isLt
    have hb := b.isLt
    simp only [submatrix_apply, id, of_apply, Function.Involutive.coe_toPerm, one_apply]
    rw [choose_two_pow_mul_odd v q _ hq (by rw [hfv, pow_succ]; split_ifs <;> omega), hfv]
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff]
    split_ifs <;> omega
  rw [hone, det_one]

/-- For every `m ≥ 1` there is an odd `j ≤ m` such that the Hankel matrix `[C(m, a + b)]` of the
even size `j + 1` is nonsingular modulo `2`. -/
private theorem exists_odd_hankel_size (m : ℕ) (hm : 1 ≤ m) :
    ∃ j, j ≤ m ∧ Odd j ∧
      (Matrix.of fun a b : Fin (j + 1) => ((m.choose ((a : ℕ) + b) : ℕ) : ZMod 2)).det ≠ 0 := by
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨v, q, hq, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : m ≠ 0)
    have hv : v ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at he
      exact (Nat.not_even_iff_odd.mpr hq) he
    have hpos : 1 ≤ 2 ^ v := Nat.one_le_two_pow
    refine ⟨2 ^ v - 1, ?_, ?_, det_choose_two_pow v q _ hq (Nat.sub_add_cancel hpos)⟩
    · exact (Nat.sub_le _ _).trans (Nat.le_mul_of_pos_right _ hq.pos)
    · exact Nat.Even.sub_odd hpos ((Nat.even_pow' hv).mpr even_two) odd_one
  · exact ⟨m, le_rfl, ho, det_choose_antitriangular m⟩

end Parity

section Shift

variable {n : ℕ} (r : Fin n → ℝ) (q : Fin (n + 1) → ℝ)

/-- Subtracting a constant from the potentials subtracts a multiple of the identity. -/
private theorem pathHamiltonian_shift (θ : ℝ) :
    pathHamiltonian r (fun i => q i - θ) =
      pathHamiltonian r q - (θ : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  ext i j
  simp only [pathHamiltonian, of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases h : i = j
  · simp [h]
  · simp [h]

/-- Subtracting a constant `θ` from the potentials multiplies the propagator at time `π` by the
phase `exp (-i π θ)`. -/
private theorem propagator_shift (θ : ℝ) :
    hamiltonianPropagator (pathHamiltonian r (fun i => q i - θ)) (-Real.pi) =
      Complex.exp (-((Real.pi : ℂ) * I * θ)) •
        hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) := by
  have hexp : NormedSpace.exp (fun _ : Fin (n + 1) => -((Real.pi : ℂ) * I * θ)) =
      fun _ => Complex.exp (-((Real.pi : ℂ) * I * θ)) := by
    funext k
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  have hsplit : ((Real.pi : ℂ) * I) •
      (pathHamiltonian r q - (θ : ℂ) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
        ((Real.pi : ℂ) * I) • pathHamiltonian r q +
          diagonal (fun _ => -((Real.pi : ℂ) * I * θ)) := by
    rw [← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul, sub_eq_add_neg, neg_smul]
  rw [hamiltonianPropagator_neg, hamiltonianPropagator_neg, pathHamiltonian_shift, hsplit,
    Matrix.exp_add_of_commute _ _
      (by rw [← Matrix.smul_one_eq_diagonal]; exact (Commute.one_right _).smul_right _),
    Matrix.exp_diagonal, hexp, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

/-- Every complex number of modulus one is `exp (i π θ)` for a real `θ`. -/
private theorem exists_phase (γ : ℂ) (hγ : Complex.normSq γ = 1) :
    ∃ θ : ℝ, Complex.exp ((Real.pi : ℂ) * I * θ) = γ := by
  refine ⟨Complex.arg γ / Real.pi, ?_⟩
  have hn : ‖γ‖ = 1 := by
    have h2 : ‖γ‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hγ
    nlinarith [norm_nonneg γ]
  have h := Complex.norm_mul_exp_arg_mul_I γ
  rw [hn, Complex.ofReal_one, one_mul] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  calc Complex.exp ((Real.pi : ℂ) * I * ((Complex.arg γ / Real.pi : ℝ) : ℂ))
      = Complex.exp ((Complex.arg γ : ℂ) * I) := by
        congr 1
        push_cast
        field_simp
    _ = γ := h

end Shift

/-- **Rational weights rule out perfect state transfer at time `π` on every odd path.** For every
`m ≥ 1`, a path on `2m + 1` vertices with positive rational edge weights and arbitrary real
potentials has no perfect state transfer between its end vertices at time `π`. -/
def claim : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ (r : Fin (2 * m) → ℝ) (q : Fin (2 * m + 1) → ℝ),
    (∀ j, ∃ x : ℚ, r j = x) → (∀ j, 0 < r j) →
      ¬ HasPST (pathHamiltonian r q) Real.pi 0 (Fin.last (2 * m)) ∧
        ¬ HasPST (pathHamiltonian r q) Real.pi (Fin.last (2 * m)) 0

/-- On a path with `2m + 1` vertices and positive rational weights, the propagator at time `π`
does not send the first vertex to the last with phase one. -/
private theorem no_phase_one_transfer {m : ℕ} (hm : 1 ≤ m) (r : Fin (2 * m) → ℝ)
    (q : Fin (2 * m + 1) → ℝ) (hrat : ∀ j, ∃ x : ℚ, r j = x) (hpos : ∀ j, 0 < r j) :
    hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) (Fin.last (2 * m)) 0 ≠ 1 := by
  intro hU
  set c : Fin (2 * m + 1) := ⟨m, by omega⟩ with hcdef
  obtain ⟨μ, hμ, hpar⟩ := middle_vertex_moments r q hpos hU c rfl
  obtain ⟨j, hjm, hjodd, hdet⟩ := exists_odd_hankel_size m hm
  have hgram := middle_moment_gram_det r q (reversal_symmetric r q hpos hU) c rfl j hjm
  set M : Matrix (Fin (j + 1)) (Fin (j + 1)) ℤ := Matrix.of fun a b => μ ((a : ℕ) + b) with hM
  have hMC : (Matrix.of fun a b : Fin (j + 1) => (pathHamiltonian r q ^ ((a : ℕ) + b)) c c) =
      M.map (Int.castRingHom ℂ) := by
    ext a b
    simp [hM, hμ]
  have hM2 : M.map (Int.castRingHom (ZMod 2)) =
      Matrix.of fun a b : Fin (j + 1) => ((m.choose ((a : ℕ) + b) : ℕ) : ZMod 2) := by
    ext a b
    simp [hM, hpar]
  have hodd : ¬ (2 : ℤ) ∣ M.det := by
    intro h2
    apply hdet
    rw [← hM2, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (by exact_mod_cast h2)
  choose x hx using hrat
  have hx0 : ∀ t, x t ≠ 0 := fun t h0 => (hpos t).ne' (by rw [hx t, h0, Rat.cast_zero])
  set Q : ℚ := ∏ a : Fin (j + 1), ∏ t : Fin a,
    x ⟨m + t, by have := a.isLt; have := t.isLt; omega⟩ with hQ
  have hQ0 : Q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun t _ => hx0 _
  have hdetQ : ((M.det : ℤ) : ℚ) = 2 ^ j * Q ^ 2 := by
    have h : (((M.det : ℤ) : ℚ) : ℂ) = ((2 ^ j * Q ^ 2 : ℚ) : ℂ) := by
      rw [Rat.cast_intCast, ← eq_intCast (Int.castRingHom ℂ), RingHom.map_det,
        RingHom.mapMatrix_apply, ← hMC, hgram, hQ]
      push_cast
      simp only [hx, Complex.ofReal_ratCast]
    exact_mod_cast h
  have h2v : padicValRat 2 (2 : ℚ) = 1 := by
    have h := padicValRat.self (p := 2) (by norm_num)
    simpa using h
  have hv := congrArg (padicValRat 2) hdetQ
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hodd,
    padicValRat.mul (pow_ne_zero j two_ne_zero) (pow_ne_zero 2 hQ0), padicValRat.pow,
    padicValRat.pow, h2v] at hv
  obtain ⟨t, ht⟩ := hjodd
  push_cast at hv
  omega

/-- No perfect state transfer at time `π` from the last vertex to the first on a path with
`2m + 1` vertices and positive rational weights. -/
private theorem no_transfer_last_first {m : ℕ} (hm : 1 ≤ m) (r : Fin (2 * m) → ℝ)
    (q : Fin (2 * m + 1) → ℝ) (hrat : ∀ j, ∃ x : ℚ, r j = x) (hpos : ∀ j, 0 < r j) :
    ¬ HasPST (pathHamiltonian r q) Real.pi (Fin.last (2 * m)) 0 := by
  intro hpst
  obtain ⟨θ, hθ⟩ := exists_phase _ hpst
  refine no_phase_one_transfer hm r (fun i => q i - θ) hrat hpos ?_
  rw [propagator_shift, Matrix.smul_apply, smul_eq_mul, ← hθ, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero]

theorem result : claim := by
  intro m hm r q hrat hpos
  have hmain := no_transfer_last_first hm r q hrat hpos
  have hT : (hamiltonianPropagator (pathHamiltonian r q) (-Real.pi))ᵀ =
      hamiltonianPropagator (pathHamiltonian r q) (-Real.pi) := by
    rw [hamiltonianPropagator_neg, ← Matrix.exp_transpose, Matrix.transpose_smul,
      pathHamiltonian_transpose]
  refine ⟨fun h => hmain ?_, hmain⟩
  have he := congrFun (congrFun hT (Fin.last (2 * m))) 0
  rw [transpose_apply] at he
  unfold HasPST at h ⊢
  rwa [← he]

end D5.S3.Quantum.Dynamics.OddPathRationalWeightTransfer
