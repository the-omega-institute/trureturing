/- GID: D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.claim; result=D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.result; claim=D5/S3/Quantum/Entanglement/QuditSwappingProductBoundRefutation.claim
   digest: The qudit-swapping product bound fails at dimension four: 723/625 > 507/625. -/

/-
result:
  proof_shape: bind-only (instantiation and normalization of pinned Mathlib facts)
  escape_witness: none
  admission_basis: open-problem-resolution (#11499; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation

/-- The phase of the generalized Bell basis, exp(2πi/d). -/
noncomputable def omega (d : ℕ) : ℂ := Complex.exp ((2 * Real.pi / d : ℝ) * Complex.I)

/-- The unnormalized AB state obtained by the Bell outcome (p,q) on CC'.
The computational basis ket |p+k,k⟩ is represented by its delta function. -/
noncomputable def phi (d : ℕ) [NeZero d] (c b : ZMod d → ℂ) (p q : ZMod d) :
    (ZMod d × ZMod d) → ℂ :=
  fun x => (1 / (Real.sqrt d : ℂ)) * ∑ k : ZMod d,
    c (p + k) * b k * star (omega d) ^ (q.val * k.val) *
      if x = (p + k, k) then 1 else 0

/-- The Hilbert norm in the computational orthonormal basis. -/
noncomputable def stateNorm (d : ℕ) [NeZero d] (v : (ZMod d × ZMod d) → ℂ) : ℝ :=
  Real.sqrt (∑ x, ‖v x‖ ^ 2)

/-- The probability of the Bell outcome (p,q), the squared Hilbert norm of phi. -/
noncomputable def prob (d : ℕ) [NeZero d] (c b : ZMod d → ℂ) (p q : ZMod d) : ℝ :=
  stateNorm d (phi d c b p q) ^ 2

/-- The l₁ entanglement for Schmidt coefficients a in ∑k aₖ |σ(k),k⟩.
The sum is over ordered pairs of distinct indices. -/
noncomputable def El1 (d : ℕ) [NeZero d] (a : ZMod d → ℂ) : ℝ :=
  ∑ j, ∑ k, if j = k then 0 else ‖a j * a k‖

/-- The outcome-weighted entanglement of the normalized post-measurement states.
Zero-probability outcomes contribute zero. Each state has Schmidt support σ(k)=p+k. -/
noncomputable def averageEl1 (d : ℕ) [NeZero d] (c b : ZMod d → ℂ) : ℝ :=
  ∑ p, ∑ q, if prob d c b p q = 0 then 0 else
    prob d c b p q * El1 d (fun k =>
      phi d c b p q (p + k, k) / (stateNorm d (phi d c b p q) : ℂ))

/-- The improved upper-bound conjecture of Starke, Basso, Céleri and Maziero.
The paper's second coefficient vector dₖ is renamed bₖ. -/
def claim : Prop :=
  ∀ (d : ℕ) [NeZero d] (c b : ZMod d → ℂ), 2 ≤ d →
    (∑ j, ‖c j‖ ^ 2) = 1 → (∑ k, ‖b k‖ ^ 2) = 1 →
    averageEl1 d c b ≤ El1 d c * El1 d b / ((d : ℝ) - 1)

/-- Two identical normalized inputs (7/10,1/10,7/10,1/10) in dimension four
yield average entanglement 723/625, exceeding the proposed bound 507/625. -/
theorem result : ¬ claim := by
  let c : ZMod 4 → ℂ := fun k => ((if k.val % 2 = 0 then 7 / 10 else 1 / 10 : ℝ) : ℂ)
  have hc : (∑ j, ‖c j‖ ^ 2) = 1 := by
    change ∑ j : Fin 4, ‖c j‖ ^ 2 = 1
    norm_num [Fin.sum_univ_succ, c, ZMod.val, Complex.norm_real]
  have he : El1 4 c = 39 / 25 := by
    change (∑ j : Fin 4, ∑ k : Fin 4, if j = k then 0 else ‖c j * c k‖) = _
    simp only [Fin.sum_univ_succ, Fin.ext_iff]
    norm_num [c, norm_mul, ZMod.val, Complex.norm_real]
  have ha : averageEl1 4 c c = 723 / 625 := by
    have average_correlation (d : ℕ) [NeZero d] (c b : ZMod d → ℂ) :
        averageEl1 d c b = ∑ p, ∑ j, ∑ k, if j = k then 0 else
          ‖c (p + j) * c (p + k) * b j * b k‖ := by
      have hphase (d : ℕ) (q k : ZMod d) :
          ‖star (omega d) ^ (q.val * k.val)‖ = 1 := by
        have hw : ‖omega d‖ = 1 := by
          rw [omega, Complex.norm_exp]
          simp
        simp only [norm_pow, norm_star, hw, one_pow]
      have hphi (d : ℕ) [NeZero d] (c b : ZMod d → ℂ) (p q : ZMod d)
          (x : ZMod d × ZMod d) :
          phi d c b p q x = if x.1 = p + x.2 then
            (1 / (Real.sqrt d : ℂ)) * c (p + x.2) * b x.2 *
              star (omega d) ^ (q.val * x.2.val) else 0 := by
        rw [phi]
        have heq (k : ZMod d) : x = (p + k, k) ↔ x.2 = k ∧ x.1 = p + x.2 := by
          constructor
          · intro h
            subst x
            exact ⟨rfl, rfl⟩
          · rintro ⟨rfl, h⟩
            exact Prod.ext h rfl
        simp_rw [heq]
        by_cases hx : x.1 = p + x.2 <;> simp [hx, mul_assoc]
      have hnphi (d : ℕ) [NeZero d] (c b : ZMod d → ℂ) (p q k : ZMod d) :
          ‖phi d c b p q (p + k, k)‖ =
            (Real.sqrt d)⁻¹ * ‖c (p + k)‖ * ‖b k‖ := by
        rw [hphi]
        simp only [ite_true, norm_mul, norm_div, norm_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hphase, mul_one]
        rw [one_div]
      have hprob (d : ℕ) [NeZero d] (c b : ZMod d → ℂ) (p q : ZMod d) :
          prob d c b p q = ∑ k, ((Real.sqrt d)⁻¹ * ‖c (p + k)‖ * ‖b k‖) ^ 2 := by
        rw [prob, stateNorm, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
        rw [Fintype.sum_prod_type]
        simp_rw [hphi]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        have hw : ‖omega d‖ = 1 := by
          rw [omega, Complex.norm_exp]
          simp
        simp [apply_ite (fun z : ℂ => ‖z‖), hw, Complex.norm_real,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      have houtcome (d : ℕ) [NeZero d] (c b : ZMod d → ℂ) (p q : ZMod d) :
          (if prob d c b p q = 0 then 0 else
            prob d c b p q * El1 d (fun k =>
              phi d c b p q (p + k, k) / (stateNorm d (phi d c b p q) : ℂ))) =
            (1 / (d : ℝ)) * ∑ j, ∑ k, if j = k then 0 else
              ‖c (p + j) * c (p + k) * b j * b k‖ := by
        have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
        have hs : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
        have hs0 : Real.sqrt d ≠ 0 := by
          intro h
          rw [h] at hs
          exact hd (by simpa using hs.symm)
        let N := stateNorm d (phi d c b p q)
        have hN : 0 ≤ stateNorm d (phi d c b p q) := Real.sqrt_nonneg _
        by_cases hz : prob d c b p q = 0
        · rw [if_pos hz]
          have hall (k : ZMod d) : (Real.sqrt d)⁻¹ * ‖c (p + k)‖ * ‖b k‖ = 0 := by
            have ht := Finset.single_le_sum (fun (i : ZMod d) _ =>
              sq_nonneg ((Real.sqrt d)⁻¹ * ‖c (p + i)‖ * ‖b i‖))
              (Finset.mem_univ k)
            rw [← hprob, hz] at ht
            nlinarith [sq_nonneg ((Real.sqrt d)⁻¹ * ‖c (p + k)‖ * ‖b k‖)]
          have hprod (k : ZMod d) : ‖c (p + k)‖ * ‖b k‖ = 0 := by
            have := hall k
            have hi : (Real.sqrt d)⁻¹ ≠ 0 := inv_ne_zero hs0
            rw [mul_assoc, mul_eq_zero] at this
            exact this.resolve_left hi
          simp_rw [norm_mul]
          have heach (j k : ZMod d) :
              ‖c (p + j)‖ * ‖c (p + k)‖ * ‖b j‖ * ‖b k‖ = 0 := by
            calc
              _ = (‖c (p + j)‖ * ‖b j‖) * (‖c (p + k)‖ * ‖b k‖) := by ring
              _ = 0 := by rw [hprod, zero_mul]
          simp_rw [heach]
          simp
        · rw [if_neg hz, prob, El1]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          by_cases hjk : j = k
          · simp [hjk]
          · simp only [if_neg hjk, norm_mul, norm_div, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hN, hnphi]
            have hN0 : N ≠ 0 := by
              intro h
              apply hz
              change N ^ 2 = 0
              rw [h, zero_pow two_ne_zero]
            change N ^ 2 *
              (((Real.sqrt d)⁻¹ * ‖c (p + j)‖ * ‖b j‖ / N) *
              ((Real.sqrt d)⁻¹ * ‖c (p + k)‖ * ‖b k‖ / N)) = _
            conv_rhs => rw [← hs]
            field_simp
      rw [averageEl1]
      simp_rw [houtcome]
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
      simp [hd]
    rw [average_correlation]
    change (∑ p : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
      if j = k then 0 else ‖c (p + j) * c (p + k) * c j * c k‖) = _
    simp only [Fin.sum_univ_succ, Fin.ext_iff]
    norm_num [c, norm_mul, ZMod.val, Complex.norm_real, Fin.val_add]
  intro h
  have hbound := h 4 c c (by norm_num) hc hc
  rw [ha, he] at hbound
  norm_num at hbound

end D5.S3.Quantum.Entanglement.QuditSwappingProductBoundRefutation
