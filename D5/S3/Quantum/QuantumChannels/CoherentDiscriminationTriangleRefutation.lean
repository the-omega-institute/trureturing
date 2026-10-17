/- GID: D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.claim; result=D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.result; claim=D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.claim
   digest: Coherent discrimination bias violates the triangle inequality on replacement channels. -/

import D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation

set_option linter.style.longLine false

namespace D5.S3.Quantum.QuantumChannels.CoherentDiscriminationTriangleRefutation

open scoped BigOperators ComplexConjugate
open _root_.Matrix
open D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
  (IsKrausChannel)

noncomputable section


/-- Canonical Kraus isometric extension, with a spectator reference system. -/
def extend {R : Type} (K : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : R × Fin 2 → ℂ) : R × Fin 2 × Fin 4 → ℂ :=
  fun x => ∑ a, K x.2.2 x.2.1 a * ψ (x.1, a)

private def amplitude {R E : Type} [Fintype R] [Fintype E] [DecidableEq E]
    (K : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : R × Fin 2 → ℂ)
    (V : Matrix (R × Fin 2 × E × Fin 2) (R × Fin 2 × E × Fin 2) ℂ)
    (e0 : E) (f : Fin 2) : R × Fin 2 × E → ℂ :=
  fun x => ∑ b, ∑ k, conj (K k b x.2.1) *
    (∑ y : R × Fin 2 × E × Fin 2,
      V (x.1, b, x.2.2, f) y *
        (if y.2.2.1 = e0 ∧ y.2.2.2 = 0 then extend K ψ (y.1, y.2.1, k) else 0))

/-- Equation (17): adjoin the zero ancillas, apply V, uncompute the Kraus extension,
and project the flag onto the channel label. The factor 1/4 is the initial 1/2
multiplied by the 1/2 from the Bell bra. The ancilla zero is specified by e0. -/
def successProbability {R E : Type} [Fintype R] [Fintype E]
    [DecidableEq R] [DecidableEq E]
    (K0 K1 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (ψ : R × Fin 2 → ℂ)
    (V : Matrix.unitaryGroup (R × Fin 2 × E × Fin 2) ℂ) (e0 : E) : ℝ :=
  (1 / 4 : ℝ) * ∑ x : R × Fin 2 × E,
    ‖amplitude K0 ψ V.val e0 0 x + amplitude K1 ψ V.val e0 1 x‖ ^ 2

/-- Equation (18), over all finite reference and pointed ancilla systems in Type. -/
def coherentValue (K0 K1 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  sSup {p : ℝ | ∃ (R E : Type) (_ : Fintype R) (_ : Fintype E)
    (_ : DecidableEq R) (_ : DecidableEq E) (e0 : E)
    (ψ : R × Fin 2 → ℂ) (V : Matrix.unitaryGroup (R × Fin 2 × E × Fin 2) ℂ),
    (∑ x, ‖ψ x‖ ^ 2) = 1 ∧ p = successProbability K0 K1 ψ V e0}

/-- Triangle inequality for coherent discrimination bias on four-Kraus qubit channels. -/
def claim : Prop :=
  ∀ K1 K2 K3 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
    IsKrausChannel K1 → IsKrausChannel K2 → IsKrausChannel K3 →
    coherentValue K1 K3 - 1/2 ≤
      (coherentValue K1 K2 - 1/2) + (coherentValue K2 K3 - 1/2)


private def replacement (t : Fin 2 → ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun k b a => if b = ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm k).1 ∧
    a = ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm k).2
    then (Real.sqrt (t b) : ℂ) else 0

private theorem replacement_normalized (t : Fin 2 → ℝ) (ht : ∀ j, 0 ≤ t j)
    (hs : t 0 + t 1 = 1) : IsKrausChannel (replacement t) := by
  rw [IsKrausChannel.eq_1]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [replacement.eq_1, Fin.sum_univ_succ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, ← Complex.ofReal_pow,
      ← pow_two, Real.sq_sqrt (ht 0), Real.sq_sqrt (ht 1), ← Complex.ofReal_add, hs]

private def block {R E : Type} [Fintype R]
    (V : Matrix (R × Fin 2 × E × Fin 2) (R × Fin 2 × E × Fin 2) ℂ)
    (e0 : E) (i j : Fin 2) (ψ : R × Fin 2 → ℂ) : R × Fin 2 × E → ℂ :=
  fun x => ∑ r, V (x.1, j, x.2.2, i) (r, j, e0, 0) * ψ (r, x.2.1)

private theorem replacement_amplitude {R E : Type} [Fintype R] [Fintype E]
    [DecidableEq E]
    (t : Fin 2 → ℝ) (ht : ∀ j, 0 ≤ t j) (ψ : R × Fin 2 → ℂ)
    (V : Matrix (R × Fin 2 × E × Fin 2) (R × Fin 2 × E × Fin 2) ℂ)
    (e0 : E) (i : Fin 2) (x : R × Fin 2 × E) :
    amplitude (replacement t) ψ V e0 i x =
      ∑ j, (t j : ℂ) * block V e0 i j ψ x := by
  have scalar (j : Fin 2) (z w : ℂ) :
      (Real.sqrt (t j) : ℂ) * z * (Real.sqrt (t j) : ℂ) * w = (t j : ℂ) * z * w := by
    calc
      _ = ((Real.sqrt (t j) : ℂ) ^ 2) * z * w := by ring
      _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt (ht j)]
  rw [amplitude.eq_1]
  simp only [Fintype.sum_prod_type]
  simp only [extend.eq_1, replacement.eq_1, block.eq_1]
  rcases x with ⟨r, a, e⟩
  fin_cases a <;>
    simp [Fin.sum_univ_succ, finProdFinEquiv, Fin.divNat, Fin.modNat, mul_ite,
      Finset.mul_sum, ← mul_assoc, scalar]

private theorem block_energy {R E : Type} [Fintype R] [Fintype E]
    [DecidableEq R] [DecidableEq E]
    (V : Matrix.unitaryGroup (R × Fin 2 × E × Fin 2) ℂ)
    (e0 : E) (j : Fin 2) (ψ : R × Fin 2 → ℂ) :
    ∑ x, (‖block V.val e0 0 j ψ x‖ ^ 2 + ‖block V.val e0 1 j ψ x‖ ^ 2) ≤
      ∑ x, ‖ψ x‖ ^ 2 := by
  have column (a : Fin 2) :
      ∑ r, ∑ e, ∑ f, ‖∑ q, V.val (r, j, e, f) (q, j, e0, 0) * ψ (q, a)‖ ^ 2 ≤
        ∑ r, ‖ψ (r, a)‖ ^ 2 := by
    let v : R × Fin 2 × E × Fin 2 → ℂ := fun y =>
      if y.2.1 = j ∧ y.2.2.1 = e0 ∧ y.2.2.2 = 0 then ψ (y.1, a) else 0
    have hnorm := ContinuousLinearMap.norm_map_of_mem_unitary
      (Unitary.map_mem (Matrix.toEuclideanCLM (n := R × Fin 2 × E × Fin 2) (𝕜 := ℂ)) V.prop) (WithLp.toLp 2 v)
    have htotal : (∑ y, ‖(V.val *ᵥ v) y‖ ^ 2) = ∑ r, ‖ψ (r, a)‖ ^ 2 := by
      have hsq := congrArg (fun z : ℝ => z ^ 2) hnorm
      rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq] at hsq
      have hv : ∑ y, ‖v y‖ ^ 2 = ∑ r, ‖ψ (r, a)‖ ^ 2 := by
        simp only [Fintype.sum_prod_type, v]
        simp only [ite_and, apply_ite, norm_zero]
        simp
      exact hsq.trans hv
    rw [← htotal]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro r hr
    have hsubset := Finset.single_le_sum
      (fun b (_ : b ∈ (Finset.univ : Finset (Fin 2))) =>
        Finset.sum_nonneg (s := Finset.univ) fun e _ =>
          Finset.sum_nonneg (s := Finset.univ) fun f _ => sq_nonneg ‖(V.val *ᵥ v) (r, b, e, f)‖) (Finset.mem_univ j)
    convert hsubset using 1
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro f hf
    simp [Matrix.mulVec, dotProduct, v, Fintype.sum_prod_type, ite_and]
  simp only [Fintype.sum_prod_type, block.eq_1]
  calc
    _ = ∑ a : Fin 2, ∑ r : R, ∑ e : E, ∑ f : Fin 2,
        ‖∑ q, V.val (r, j, e, f) (q, j, e0, 0) * ψ (q, a)‖ ^ 2 := by
      simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
    _ ≤ ∑ a : Fin 2, ∑ r : R, ‖ψ (r, a)‖ ^ 2 :=
      Finset.sum_le_sum fun a _ => column a
    _ = _ := Finset.sum_comm

end

end D5.S3.Quantum.QuantumChannels.CoherentDiscriminationTriangleRefutation
