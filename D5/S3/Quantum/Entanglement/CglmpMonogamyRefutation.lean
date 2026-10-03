/- GID: D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/CglmpMonogamyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.claim; result=D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.result; claim=D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.claim
   digest: Two two-qutrit marginals of one three-qutrit state both violate the CGLMP inequality. -/

/-
proof_shape: dft, phase, jointProb, eventProb, cglmpI3, cglmpAt, IsCglmpValue, rhoAB, rhoBC,
  rhoAC:
  definition (the paper's measurement family, Born probabilities, Eq. (CGLMP1), Eq. (CGLMP2) and
  the three two-qutrit reduced density matrices)
proof_shape: claim: definition (published conjecture, arXiv:1704.06516, Eq. (35), read for every
  three-qutrit density matrix)
proof_shape: stateVec, rho, ang: definition (the counterexample state and the angle unit pi/6)
proof_shape: result: bind-only (as local steps: existence of the maximum of I_3 over the angles
  by continuity, 2 pi periodicity and IsCompact.exists_isMaxOn, the Born probabilities of a
  reduced pure state as sums of squared amplitudes, the twelfth roots of unity e^{-i pi k/6},
  and evaluation of the squared amplitudes)
escape_witness: none (the settlement of the external named conjecture is the new content)
admission_basis: open-problem-resolution (issue #12528; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceLeft
    sha256:68653a556c9228bbd8018884585aa56fe5fce5cd40b4a12a493f4aa319c78f5d
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Entanglement/QutritThresholdSharing.normalization
    sha256:4f9cda89db0e29177d2d790cab1e44cdc428791900fa0f21ca2ab6170dc509c3
  D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry.omega
    sha256:261e2e0ce2e1362adaaa53a143a55b36057b679a111d4a9ec19e1d9a1b0ccc26
-/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.QutritThresholdSharing
import D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.CglmpMonogamyRefutation

/-!
M. Kumari, S. Ghose and R. B. Mann, *Sufficient condition for nonexistence of symmetric
extension of qudits using Bell inequalities*, arXiv:1704.06516 (Phys. Rev. A 96 (2017) 012128),
measure a two-qutrit state with `A_k = U_FT U(φ_k)` on the first qutrit and
`B_l = U_FT^* U(φ'_l)` on the second, where `U(φ) = diag(e^{-iφ(0)}, e^{-iφ(1)}, e^{-iφ(2)})`,
followed by a computational-basis measurement, and take `B_CGLMP(ρ)` to be the maximum over the
twelve angles of the CGLMP expression `I_3` of Eq. (CGLMP1). Their Eq. (35) conjectures that for
every three-qutrit state at most one of `ρ_AB`, `ρ_BC`, `ρ_AC` has `B_CGLMP > 2`. It fails for
`v = |002⟩ + |011⟩ + 2|020⟩ + |100⟩ + 2|112⟩ - |121⟩ + 2|210⟩ + 2|222⟩` and `ρ = v v† / 20`:
with angles in units of `π/6`, `φ_1 = (0,2,7)`, `φ_2 = (0,2,1)`, `φ'_1 = (0,8,4)`,
`φ'_2 = (0,10,2)` give `I_3(ρ_AB) = 1/2 + 14√3/15`, and `φ_1 = (0,6,9)`, `φ_2 = (0,6,3)`,
`φ'_1 = (0,10,2)`, `φ'_2 = (0,0,6)` give `I_3(ρ_AC) = 1/2 + 14√3/15`, both above `2`.
-/

open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry (omega)

/-- The three-dimensional discrete Fourier transform `U_FT`, with entries `ω^{jk}/√3`. -/
noncomputable def dft : Matrix (Fin 3) (Fin 3) ℂ :=
  fun j k => omega ^ (j.val * k.val) / (Real.sqrt 3 : ℂ)

/-- The diagonal unitary `U(φ)` with entries `exp(-iφ(j))`. -/
noncomputable def phase (φ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal fun j => Complex.exp (-(Complex.I * (φ j : ℂ)))

/-- `P(A = j, B = k) = tr(Π_j ⊗ Π_k (A ⊗ B) ρ (A† ⊗ B†))`, Eq. (Probabilities). -/
noncomputable def jointProb (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (A B : Matrix (Fin 3) (Fin 3) ℂ) (j k : Fin 3) : ℝ :=
  (trace ((single j j 1 ⊗ₖ single k k 1) * (A ⊗ₖ B) * ρ * (Aᴴ ⊗ₖ Bᴴ))).re

/-- The probability of the event `E` on the outcome pair `(A, B)`. -/
noncomputable def eventProb (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (A B : Matrix (Fin 3) (Fin 3) ℂ) (E : Fin 3 → Fin 3 → Prop) [DecidableRel E] : ℝ :=
  ∑ a, ∑ b, if E a b then jointProb ρ A B a b else 0

/-- The CGLMP expression `I_3` of Eq. (CGLMP1), outcomes added modulo `3`. -/
noncomputable def cglmpI3 (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (A₁ A₂ B₁ B₂ : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  eventProb ρ A₁ B₁ (fun a b => a = b) + eventProb ρ A₂ B₁ (fun a b => b = a + 1) +
    eventProb ρ A₂ B₂ (fun a b => a = b) + eventProb ρ A₁ B₂ (fun a b => b = a) -
    eventProb ρ A₁ B₁ (fun a b => a = b - 1) - eventProb ρ A₂ B₁ (fun a b => b = a) -
    eventProb ρ A₂ B₂ (fun a b => a = b - 1) - eventProb ρ A₁ B₂ (fun a b => b = a - 1)

/-- `I_3` of the state `ρ` at the twelve angles `θ = (φ, φ')`, with `A_k = U_FT U(φ_k)` and
`B_l = U_FT^* U(φ'_l)`; `B_CGLMP(ρ)` of Eq. (CGLMP2) is its maximum over `θ`. -/
noncomputable def cglmpAt (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)
    (θ : (Fin 2 → Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ)) : ℝ :=
  cglmpI3 ρ (dft * phase (θ.1 0)) (dft * phase (θ.1 1)) (dftᴴ * phase (θ.2 0))
    (dftᴴ * phase (θ.2 1))

/-- `b` is `B_CGLMP(ρ)` of Eq. (CGLMP2): the maximum of `I_3` over the twelve angles. -/
def IsCglmpValue (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (b : ℝ) : Prop :=
  IsGreatest (Set.range (cglmpAt ρ)) b

/-- `ρ_AB = tr_C ρ` for a three-qutrit matrix indexed by `(a, b, c)`. -/
noncomputable def rhoAB (ρ : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  partialTraceRight (ρ.submatrix (fun x : (Fin 3 × Fin 3) × Fin 3 => (x.1.1, x.1.2, x.2))
    (fun x : (Fin 3 × Fin 3) × Fin 3 => (x.1.1, x.1.2, x.2)))

/-- `ρ_BC = tr_A ρ`. -/
noncomputable def rhoBC (ρ : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  partialTraceLeft ρ

/-- `ρ_AC = tr_B ρ`, indexed by `(a, c)`. -/
noncomputable def rhoAC (ρ : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  partialTraceRight (ρ.submatrix (fun x : (Fin 3 × Fin 3) × Fin 3 => (x.1.1, x.2, x.1.2))
    (fun x : (Fin 3 × Fin 3) × Fin 3 => (x.1.1, x.2, x.1.2)))

/-- Eq. (35): for every three-qutrit state, `B_CGLMP(ρ_AB) > 2` implies `B_CGLMP(ρ_BC) ≤ 2` and
`B_CGLMP(ρ_AC) ≤ 2`, for the maxima `B_CGLMP` of Eq. (CGLMP2). -/
def claim : Prop :=
  ∀ ρ : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, ρ.PosSemidef → ρ.trace = 1 →
    ∀ bAB bBC bAC : ℝ, IsCglmpValue (rhoAB ρ) bAB → IsCglmpValue (rhoBC ρ) bBC →
      IsCglmpValue (rhoAC ρ) bAC → 2 < bAB → bBC ≤ 2 ∧ bAC ≤ 2

/-- The unnormalized vector
`|002⟩ + |011⟩ + 2|020⟩ + |100⟩ + 2|112⟩ - |121⟩ + 2|210⟩ + 2|222⟩`. -/
def stateVec : Fin 3 × Fin 3 × Fin 3 → ℂ := fun x =>
  if x = (0, 0, 2) then 1 else if x = (0, 1, 1) then 1 else if x = (0, 2, 0) then 2
  else if x = (1, 0, 0) then 1 else if x = (1, 1, 2) then 2 else if x = (1, 2, 1) then -1
  else if x = (2, 1, 0) then 2 else if x = (2, 2, 2) then 2 else 0

/-- The counterexample state `ρ = v v† / 20`. -/
noncomputable def rho : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  (20 : ℂ)⁻¹ • vecMulVec stateVec (star stateVec)

/-- The angle `n π / 6`. -/
noncomputable def ang (n : ℕ) : ℝ := n * Real.pi / 6

set_option maxHeartbeats 8000000 in -- the Born-probability expansions share this declaration
/-- The conjecture fails: `ρ_AB` and `ρ_AC` of `rho` both have `B_CGLMP > 2`. -/
theorem result : ¬ claim := by
  intro h
  have hgt : 2 < 1 / 2 + 14 * Real.sqrt 3 / 15 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hmax : ∀ ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      ∃ b, IsGreatest (Set.range (cglmpAt ρ)) b := by
    have hkron : ∀ {X : Type} [TopologicalSpace X] (A B : X → Matrix (Fin 3) (Fin 3) ℂ),
        Continuous A → Continuous B → Continuous fun x => A x ⊗ₖ B x := by
      intro X _ A B hA hB
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [kroneckerMap_apply]
      exact (hA.matrix_elem i.1 j.1).mul (hB.matrix_elem i.2 j.2)
    have hph : ∀ (k : Fin 2) (s : (Fin 2 → Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ) →
        Fin 2 → Fin 3 → ℝ),
        Continuous s → Continuous fun θ => phase (s θ k) := by
      intro k s hs
      exact Continuous.matrix_diagonal (continuous_pi fun j => by fun_prop)
    intro ρ
    have hjoint : ∀ A B : (Fin 2 → Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ) →
        Matrix (Fin 3) (Fin 3) ℂ, Continuous A → Continuous B →
          ∀ j k, Continuous fun θ => jointProb ρ (A θ) (B θ) j k := by
      intro A B hA hB j k
      exact Complex.continuous_re.comp (Continuous.matrix_trace
        (((continuous_const.matrix_mul (hkron A B hA hB)).matrix_mul continuous_const).matrix_mul
          (hkron _ _ hA.matrix_conjTranspose hB.matrix_conjTranspose)))
    have hevent : ∀ A B : (Fin 2 → Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ) →
        Matrix (Fin 3) (Fin 3) ℂ, Continuous A → Continuous B →
          ∀ (E : Fin 3 → Fin 3 → Prop) [DecidableRel E],
          Continuous fun θ => eventProb ρ (A θ) (B θ) E := by
      intro A B hA hB E _
      unfold eventProb
      refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
      split_ifs
      exacts [hjoint A B hA hB a b, continuous_const]
    have hA : ∀ k, Continuous fun θ : (Fin 2 → Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
        dft * phase (θ.1 k) :=
      fun k => continuous_const.matrix_mul (hph k _ continuous_fst)
    have hB : ∀ k, Continuous fun θ : (Fin 2 → Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ) =>
        dftᴴ * phase (θ.2 k) :=
      fun k => continuous_const.matrix_mul (hph k _ continuous_snd)
    have hcont : Continuous (cglmpAt ρ) := by
      unfold cglmpAt cglmpI3
      exact (((((((hevent _ _ (hA 0) (hB 0) _).add (hevent _ _ (hA 1) (hB 0) _)).add
        (hevent _ _ (hA 1) (hB 1) _)).add (hevent _ _ (hA 0) (hB 1) _)).sub
        (hevent _ _ (hA 0) (hB 0) _)).sub (hevent _ _ (hA 1) (hB 0) _)).sub
        (hevent _ _ (hA 1) (hB 1) _)).sub (hevent _ _ (hA 0) (hB 1) _)
    set red : ℝ → ℝ := toIcoMod Real.two_pi_pos 0 with hred
    have hexp : ∀ x : ℝ, Complex.exp (-(Complex.I * ((red x : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * (x : ℂ))) := by
      intro x
      rw [hred, toIcoMod, show (x - toIcoDiv Real.two_pi_pos 0 x • (2 * Real.pi) : ℝ) =
        x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * Real.pi) by rw [zsmul_eq_mul]]
      rw [show -(Complex.I * ((x - (toIcoDiv Real.two_pi_pos 0 x : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) =
        -(Complex.I * (x : ℂ)) + (toIcoDiv Real.two_pi_pos 0 x : ℂ) * (2 * Real.pi * Complex.I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hphase : ∀ φ : Fin 3 → ℝ, phase (fun j => red (φ j)) = phase φ := by
      intro φ
      simp only [phase, hexp]
    let K : Set ((Fin 2 → Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ)) :=
      (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc 0 (2 * Real.pi)) ×ˢ
        (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc 0 (2 * Real.pi))
    have hK : IsCompact K :=
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).prod
        (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc)
    have hred_mem : ∀ x : ℝ, red x ∈ Set.Icc 0 (2 * Real.pi) := by
      intro x
      have h := toIcoMod_mem_Ico Real.two_pi_pos 0 x
      rw [zero_add] at h
      exact ⟨h.1, h.2.le⟩
    have hKmem : ∀ θ : (Fin 2 → Fin 3 → ℝ) × (Fin 2 → Fin 3 → ℝ),
        ((fun k j => red (θ.1 k j)), (fun k j => red (θ.2 k j))) ∈ K := by
      intro θ
      exact ⟨fun k _ j _ => hred_mem _, fun k _ j _ => hred_mem _⟩
    have hval : ∀ θ, cglmpAt ρ ((fun k j => red (θ.1 k j)), (fun k j => red (θ.2 k j))) =
        cglmpAt ρ θ := by
      intro θ
      simp only [cglmpAt, hphase]
    obtain ⟨θ0, -, hθ0⟩ := hK.exists_isMaxOn ⟨_, hKmem 0⟩ hcont.continuousOn
    refine ⟨cglmpAt ρ θ0, ⟨θ0, rfl⟩, ?_⟩
    rintro _ ⟨θ, rfl⟩
    rw [← hval θ]
    exact hθ0 (hKmem θ)
  set η : ℂ := Complex.exp (-(Complex.I * ((Real.pi / 6 : ℝ) : ℂ))) with hηdef
  have hpe : ∀ n : ℕ, Complex.exp (-(Complex.I * ((ang n : ℝ) : ℂ))) = η ^ n := by
    intro n
    rw [hηdef, ← Complex.exp_nat_mul]; congr 1; simp only [ang]; push_cast; ring
  have hη : η = ((Real.sqrt 3 / 2 : ℝ) : ℂ) + ((-1 / 2 : ℝ) : ℂ) * Complex.I := by
    rw [hηdef, show -(Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) =
        ((-(Real.pi / 6) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six]
    push_cast; ring
  have h12 : ∀ k : ℕ, η ^ (k + 12) = η ^ k := by
    intro k
    rw [pow_add, hηdef, ← Complex.exp_nat_mul (n := 12),
      show ((12 : ℕ) : ℂ) * -(Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) =
        ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hω : omega = η ^ 8 := by
    rw [omega, hηdef, ← Complex.exp_nat_mul,
      show ((8 : ℕ) : ℂ) * -(Complex.I * ((Real.pi / 6 : ℝ) : ℂ)) =
      2 * Real.pi * Complex.I / 3 + ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hωs : star omega = η ^ 4 := by
    rw [omega, hηdef, ← Complex.exp_nat_mul, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast; ring
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ = ((1 / 3 : ℝ) : ℂ) := by
    rw [D5.S3.Quantum.Entanglement.QutritThresholdSharing.normalization]
    push_cast
    ring
  have hamp : ∀ (p q : Fin 3 → ℕ) (j k : Fin 3) (w : Fin 3 → Fin 3 → ℂ),
      ∑ a, ∑ b, (dft * phase fun i => ang (p i)) j a * (dftᴴ * phase fun i => ang (q i)) k b *
          w a b =
        ((1 / 3 : ℝ) : ℂ) *
          ∑ a, ∑ b, η ^ (8 * (j.val * a.val) + p a + 4 * (b.val * k.val) + q b) * w a b := by
    intro p q j k w
    simp only [phase, dft, mul_diagonal, conjTranspose_apply, star_div₀, star_pow, hωs, hpe,
      Finset.mul_sum]
    simp only [hω, Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hs3, pow_add, pow_add, pow_add, pow_mul, pow_mul]
    ring
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have step : ∀ (r : ℕ) (x y x' y' : ℝ), η ^ r = (x : ℂ) + (y : ℂ) * Complex.I →
      x' = x * (Real.sqrt 3 / 2) + y / 2 → y' = y * (Real.sqrt 3 / 2) - x / 2 →
      η ^ (r + 1) = (x' : ℂ) + (y' : ℂ) * Complex.I := by
    intro r x y x' y' h hx hy
    rw [pow_succ, h, hη, hx, hy]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have t1 : η ^ 1 = ((Real.sqrt 3 / 2 : ℝ) : ℂ) + ((-1 / 2 : ℝ) : ℂ) * Complex.I := by
    rw [pow_one, hη]
  have t2 := step 1 _ _ (1 / 2) (-(Real.sqrt 3 / 2)) t1 (by linear_combination (-1 / 4) * hsq)
    (by ring)
  have t3 := step 2 _ _ 0 (-1) t2 (by ring) (by linear_combination (1 / 4) * hsq)
  have t4 := step 3 _ _ (-1 / 2) (-(Real.sqrt 3 / 2)) t3 (by ring) (by ring)
  have t5 := step 4 _ _ (-(Real.sqrt 3 / 2)) (-1 / 2) t4 (by ring)
    (by linear_combination (1 / 4) * hsq)
  have t6 := step 5 _ _ (-1) 0 t5 (by linear_combination (1 / 4) * hsq) (by ring)
  have t7 := step 6 _ _ (-(Real.sqrt 3 / 2)) (1 / 2) t6 (by ring) (by ring)
  have t8 := step 7 _ _ (-1 / 2) (Real.sqrt 3 / 2) t7 (by linear_combination (1 / 4) * hsq)
    (by ring)
  have t9 := step 8 _ _ 0 1 t8 (by ring) (by linear_combination (-1 / 4) * hsq)
  have t10 := step 9 _ _ (1 / 2) (Real.sqrt 3 / 2) t9 (by ring) (by ring)
  have t11 := step 10 _ _ (Real.sqrt 3 / 2) (1 / 2) t10 (by ring)
    (by linear_combination (-1 / 4) * hsq)
  have L2 : ∀ (u : Fin 3 × Fin 3 → Fin 3 → ℂ) (A B : Matrix (Fin 3) (Fin 3) ℂ) (j k : Fin 3),
      jointProb (Matrix.of fun x y => (20 : ℂ)⁻¹ * ∑ c, u x c * star (u y c)) A B j k =
        (20 : ℝ)⁻¹ * ∑ c, Complex.normSq (∑ a, ∑ b, A j a * B k b * u (a, b) c) := by
    intro u A B j k
    unfold jointProb
    rw [single_kronecker_single, one_mul, Matrix.mul_assoc, Matrix.mul_assoc, trace_single_mul,
      one_smul]
    simp only [Matrix.mul_apply, Matrix.of_apply, kroneckerMap_apply, conjTranspose_apply,
      Fintype.sum_prod_type,
      Fin.sum_univ_three, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.inv_re,
      Complex.inv_im]
    norm_num
    ring
  have hpsd : rho.PosSemidef :=
    (posSemidef_vecMulVec_self_star stateVec).smul (by norm_num [Complex.nonneg_iff])
  have htr : rho.trace = 1 := by
    simp (config := {decide := true}) only [rho, Matrix.trace, Matrix.diag, Matrix.smul_apply,
      vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_three, stateVec, Prod.mk.injEq, if_true,
      if_false, Pi.star_apply, star_zero, star_one, star_neg, star_ofNat, mul_zero]
    norm_num
  have hAB : rhoAB rho = Matrix.of fun x y =>
      (20 : ℂ)⁻¹ * ∑ c, stateVec (x.1, x.2, c) * star (stateVec (y.1, y.2, c)) := by
    ext x y
    simp [rhoAB, partialTraceRight, rho, vecMulVec_apply, Finset.mul_sum]
  have hAC : rhoAC rho = Matrix.of fun x y =>
      (20 : ℂ)⁻¹ * ∑ b, stateVec (x.1, b, x.2) * star (stateVec (y.1, b, y.2)) := by
    ext x y
    simp [rhoAC, partialTraceRight, rho, vecMulVec_apply, Finset.mul_sum]
  have eAB : cglmpI3 (rhoAB rho) (dft * phase fun i => ang (![0, 2, 7] i))
      (dft * phase fun i => ang (![0, 2, 1] i)) (dftᴴ * phase fun i => ang (![0, 8, 4] i))
      (dftᴴ * phase fun i => ang (![0, 10, 2] i)) = 1 / 2 + 14 * Real.sqrt 3 / 15 := by
    rw [hAB]
    simp only [cglmpI3, eventProb, L2, hamp]
    simp (config := {decide := true}) only [Fin.sum_univ_three, stateVec, Fin.val_zero, Fin.val_one,
      Fin.val_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Prod.mk.injEq, if_true, if_false, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, Nat.reduceMul, Nat.reduceAdd]
    simp only [h12, pow_zero, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
    ring_nf
    simp only [hsq]
    ring_nf
  have eAC : cglmpI3 (rhoAC rho) (dft * phase fun i => ang (![0, 6, 9] i))
      (dft * phase fun i => ang (![0, 6, 3] i)) (dftᴴ * phase fun i => ang (![0, 10, 2] i))
      (dftᴴ * phase fun i => ang (![0, 0, 6] i)) = 1 / 2 + 14 * Real.sqrt 3 / 15 := by
    rw [hAC]
    simp only [cglmpI3, eventProb, L2, hamp]
    simp (config := {decide := true}) only [Fin.sum_univ_three, stateVec, Fin.val_zero, Fin.val_one,
      Fin.val_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Prod.mk.injEq, if_true, if_false, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, Nat.reduceMul, Nat.reduceAdd]
    simp only [h12, pow_zero, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
    ring_nf
    simp only [hsq]
    ring_nf
  obtain ⟨bAB, hbAB⟩ := hmax (rhoAB rho)
  obtain ⟨bBC, hbBC⟩ := hmax (rhoBC rho)
  obtain ⟨bAC, hbAC⟩ := hmax (rhoAC rho)
  have hAB1 : cglmpI3 (rhoAB rho) (dft * phase fun i => ang (![0, 2, 7] i))
      (dft * phase fun i => ang (![0, 2, 1] i)) (dftᴴ * phase fun i => ang (![0, 8, 4] i))
      (dftᴴ * phase fun i => ang (![0, 10, 2] i)) ≤ bAB :=
    hbAB.2 ⟨(![fun i => ang (![0, 2, 7] i), fun i => ang (![0, 2, 1] i)],
      ![fun i => ang (![0, 8, 4] i), fun i => ang (![0, 10, 2] i)]), rfl⟩
  have hAC1 : cglmpI3 (rhoAC rho) (dft * phase fun i => ang (![0, 6, 9] i))
      (dft * phase fun i => ang (![0, 6, 3] i)) (dftᴴ * phase fun i => ang (![0, 10, 2] i))
      (dftᴴ * phase fun i => ang (![0, 0, 6] i)) ≤ bAC :=
    hbAC.2 ⟨(![fun i => ang (![0, 6, 9] i), fun i => ang (![0, 6, 3] i)],
      ![fun i => ang (![0, 10, 2] i), fun i => ang (![0, 0, 6] i)]), rfl⟩
  have hAC2 := (h rho hpsd htr bAB bBC bAC hbAB hbBC hbAC (by linarith)).2
  linarith

end D5.S3.Quantum.Entanglement.CglmpMonogamyRefutation
