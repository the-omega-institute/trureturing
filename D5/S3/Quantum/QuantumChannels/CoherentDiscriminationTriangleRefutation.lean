/- GID: D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.claim; result=D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.result; claim=D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation.claim
   digest: Coherent discrimination bias violates the triangle inequality on replacement channels. -/

import D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
import D5.S3.Quantum.Dynamics.PositivePauliClockOrder

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

open Classical in
private def amplitude {R E : Type} [Fintype R] [Fintype E]
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
  rw [← (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).sum_comp
    (fun k => (replacement t k)ᴴ * replacement t k)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [replacement.eq_1, Fin.sum_univ_succ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, ← Complex.ofReal_pow,
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
  simp_rw [← (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [extend.eq_1, replacement.eq_1, block.eq_1]
  rcases x with ⟨r, a, e⟩
  fin_cases a <;>
    simp [Fin.sum_univ_succ, mul_ite,
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
      (Unitary.map_mem (toEuclideanCLM (𝕜 := ℂ)) V.prop) (WithLp.toLp 2 v)
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

private theorem weighted_norm {I : Type} [Fintype I] (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (x y : EuclideanSpace ℂ I) :
    ‖(t : ℂ) • x + (u : ℂ) • y‖ ^ 2 ≤
      (t ^ 2 + u ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have htriangle := norm_add_le ((t : ℂ) • x) ((u : ℂ) • y)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht, abs_of_nonneg hu] at htriangle
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 2))
    ![t, u] ![‖x‖, ‖y‖]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hcs
  exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htriangle).trans hcs

private theorem success_upper {R E : Type} [Fintype R] [Fintype E]
    [DecidableEq R] [DecidableEq E] (t u : Fin 2 → ℝ)
    (ht : ∀ j, 0 < t j) (hu : ∀ j, 0 < u j)
    (ψ : R × Fin 2 → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1)
    (V : Matrix.unitaryGroup (R × Fin 2 × E × Fin 2) ℂ) (e0 : E) :
    successProbability (replacement t) (replacement u) ψ V e0 ≤
      (Real.sqrt (t 0 ^ 2 + u 0 ^ 2) + Real.sqrt (t 1 ^ 2 + u 1 ^ 2)) ^ 2 / 4 := by
  let X (i j : Fin 2) : EuclideanSpace ℂ (R × Fin 2 × E) :=
    WithLp.toLp 2 (block V.val e0 i j ψ)
  let W (j : Fin 2) := (t j : ℂ) • X 0 j + (u j : ℂ) • X 1 j
  have hW (j : Fin 2) : ‖W j‖ ≤ Real.sqrt (t j ^ 2 + u j ^ 2) := by
    have he : ‖X 0 j‖ ^ 2 + ‖X 1 j‖ ^ 2 ≤ 1 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      change (∑ x, ‖block V.val e0 0 j ψ x‖ ^ 2) +
        (∑ x, ‖block V.val e0 1 j ψ x‖ ^ 2) ≤ 1
      rw [← Finset.sum_add_distrib, ← hψ]
      exact block_energy V e0 j ψ
    have hw := weighted_norm (t j) (u j) (ht j).le (hu j).le (X 0 j) (X 1 j)
    have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ t j ^ 2 + u j ^ 2)
    have hs := Real.sq_sqrt (by positivity : 0 ≤ t j ^ 2 + u j ^ 2)
    dsimp only [W]
    nlinarith [norm_nonneg ((t j : ℂ) • X 0 j + (u j : ℂ) • X 1 j),
      Real.sqrt_nonneg (t j ^ 2 + u j ^ 2)]
  have hvec : (WithLp.toLp 2 (fun x =>
      amplitude (replacement t) ψ V.val e0 0 x +
      amplitude (replacement u) ψ V.val e0 1 x) : EuclideanSpace ℂ (R × Fin 2 × E)) =
        W 0 + W 1 := by
    ext x
    change amplitude (replacement t) ψ V.val e0 0 x +
      amplitude (replacement u) ψ V.val e0 1 x =
      ((t 0 : ℂ) * block V.val e0 0 0 ψ x + (u 0 : ℂ) * block V.val e0 1 0 ψ x) +
      ((t 1 : ℂ) * block V.val e0 0 1 ψ x + (u 1 : ℂ) * block V.val e0 1 1 ψ x)
    rw [replacement_amplitude t (fun j => (ht j).le),
      replacement_amplitude u (fun j => (hu j).le)]
    simp only [Fin.sum_univ_two]
    ring
  have hn := (norm_add_le (W 0) (W 1)).trans (add_le_add (hW 0) (hW 1))
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  rw [successProbability.eq_1]
  have heq := EuclideanSpace.norm_sq_eq
    (WithLp.toLp 2 (fun x => amplitude (replacement t) ψ V.val e0 0 x +
      amplitude (replacement u) ψ V.val e0 1 x) : EuclideanSpace ℂ (R × Fin 2 × E))
  change ‖(WithLp.toLp 2 (fun x => amplitude (replacement t) ψ V.val e0 0 x +
    amplitude (replacement u) ψ V.val e0 1 x) : EuclideanSpace ℂ (R × Fin 2 × E))‖ ^ 2 =
      ∑ x, ‖amplitude (replacement t) ψ V.val e0 0 x +
        amplitude (replacement u) ψ V.val e0 1 x‖ ^ 2 at heq
  rw [hvec] at heq
  change (1 / 4 : ℝ) * (∑ x, ‖amplitude (replacement t) ψ V.val e0 0 x +
    amplitude (replacement u) ψ V.val e0 1 x‖ ^ 2) ≤ _
  rw [← heq]
  linarith

private def rotation (t u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (!![t / Real.sqrt (t ^ 2 + u ^ 2), -u / Real.sqrt (t ^ 2 + u ^ 2);
    u / Real.sqrt (t ^ 2 + u ^ 2), t / Real.sqrt (t ^ 2 + u ^ 2)] :
      Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofRealHom

private theorem rotation_unitary (t u : ℝ) (ht : 0 < t) :
    rotation t u ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    !![t / Real.sqrt (t ^ 2 + u ^ 2), -u / Real.sqrt (t ^ 2 + u ^ 2);
      u / Real.sqrt (t ^ 2 + u ^ 2), t / Real.sqrt (t ^ 2 + u ^ 2)]
  have hpositive : 0 < t ^ 2 + u ^ 2 := by positivity
  have hcircle : (t / Real.sqrt (t ^ 2 + u ^ 2)) ^ 2 +
      (-u / Real.sqrt (t ^ 2 + u ^ 2)) ^ 2 = 1 := by
    rw [div_pow, div_pow, neg_sq, ← add_div, Real.sq_sqrt hpositive.le]
    exact div_self hpositive.ne'
  have hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    apply Matrix.of_mem_specialOrthogonalGroup_fin_two_iff.mpr
    exact ⟨rfl, by ring, hcircle⟩
  have horth : A * A.transpose = 1 := by simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using (Matrix.mem_unitaryGroup_iff.mp hA.1)
  rw [Matrix.mem_unitaryGroup_iff]
  change A.map Complex.ofRealHom * star (A.map Complex.ofRealHom) = 1
  have hstar : star (A.map Complex.ofRealHom) = A.transpose.map Complex.ofRealHom := by
    ext i j
    simp [Matrix.star_apply]
  rw [hstar]
  have hmap := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.map Complex.ofRealHom) horth
  simpa only [Matrix.map_mul, Matrix.map_one Complex.ofRealHom
    (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom)] using hmap

private def controlled (t u : Fin 2 → ℝ) :
    Matrix (Unit × Fin 2 × Unit × Fin 2) (Unit × Fin 2 × Unit × Fin 2) ℂ :=
  fun x y => if x.2.1 = y.2.1 then rotation (t x.2.1) (u x.2.1) x.2.2.2 y.2.2.2 else 0

private theorem controlled_unitary (t u : Fin 2 → ℝ)
    (ht : ∀ j, 0 < t j) :
    controlled t u ∈ Matrix.unitaryGroup (Unit × Fin 2 × Unit × Fin 2) ℂ := by
  let e : (Unit × Fin 2 × Unit × Fin 2) ≃ (Fin 2 × Fin 2) :=
    { toFun := fun x => (x.2.1, x.2.2.2)
      invFun := fun x => ((), x.1, (), x.2)
      left_inv := by rintro ⟨⟨⟩, b, ⟨⟩, f⟩; rfl
      right_inv := by intro x; rfl }
  let W := D5.S3.Quantum.Dynamics.PositivePauliClockOrder.controlled
    (rotation (t 0) (u 0)) (rotation (t 1) (u 1))
  have hbase := D5.S3.Quantum.Dynamics.PositivePauliClockOrder.controlled_unitary
    (rotation (t 0) (u 0)) (rotation (t 1) (u 1))
    (rotation_unitary (t 0) (u 0) (ht 0)) (rotation_unitary (t 1) (u 1) (ht 1))
  have heq : controlled t u = W.submatrix e e := by
    ext x y
    rcases x with ⟨⟨⟩, b, ⟨⟩, f⟩
    rcases y with ⟨⟨⟩, c, ⟨⟩, g⟩
    fin_cases b <;> fin_cases c <;>
      simp [controlled.eq_1, W, e,
        D5.S3.Quantum.Dynamics.PositivePauliClockOrder.controlled.eq_1,
        Matrix.blockDiagonal_apply]
  rw [Matrix.mem_unitaryGroup_iff] at hbase ⊢
  rw [heq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ e e e e.bijective, ← Matrix.star_eq_conjTranspose, hbase]
  exact Matrix.submatrix_one_equiv e

private def input0 : Unit × Fin 2 → ℂ := fun x => if x.2 = 0 then 1 else 0

private theorem attaining (t u : Fin 2 → ℝ)
    (ht : ∀ j, 0 < t j) (hu : ∀ j, 0 < u j) :
    successProbability (replacement t) (replacement u) input0
      ⟨controlled t u, controlled_unitary t u ht⟩ () =
      (Real.sqrt (t 0 ^ 2 + u 0 ^ 2) + Real.sqrt (t 1 ^ 2 + u 1 ^ 2)) ^ 2 / 4 := by
  have scalar (j : Fin 2) :
      (t j : ℂ) * ((t j / Real.sqrt (t j ^ 2 + u j ^ 2) : ℝ) : ℂ) +
      (u j : ℂ) * ((u j / Real.sqrt (t j ^ 2 + u j ^ 2) : ℝ) : ℂ) =
        (Real.sqrt (t j ^ 2 + u j ^ 2) : ℂ) := by
    have hs : 0 < Real.sqrt (t j ^ 2 + u j ^ 2) := Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos (ht j)) (sq_nonneg _))
    have heq : t j * (t j / Real.sqrt (t j ^ 2 + u j ^ 2)) +
        u j * (u j / Real.sqrt (t j ^ 2 + u j ^ 2)) = Real.sqrt (t j ^ 2 + u j ^ 2) := by
      calc
        _ = (t j ^ 2 + u j ^ 2) / Real.sqrt (t j ^ 2 + u j ^ 2) := by ring
        _ = _ := (div_eq_iff hs.ne').mpr (by rw [← pow_two, Real.sq_sqrt (by positivity)])
    exact_mod_cast heq
  have hvec (x : Unit × Fin 2 × Unit) :
      amplitude (replacement t) input0 (controlled t u) () 0 x +
      amplitude (replacement u) input0 (controlled t u) () 1 x =
      ((Real.sqrt (t 0 ^ 2 + u 0 ^ 2) + Real.sqrt (t 1 ^ 2 + u 1 ^ 2) : ℝ) : ℂ) *
        input0 ((), x.2.1) := by
    rw [replacement_amplitude t (fun j => (ht j).le),
      replacement_amplitude u (fun j => (hu j).le)]
    rcases x with ⟨⟨⟩, a, ⟨⟩⟩
    fin_cases a <;>
      simp [block.eq_1, controlled.eq_1, rotation.eq_1, input0.eq_1, Fin.sum_univ_two]
    have h0 := scalar 0
    have h1 := scalar 1
    push_cast at h0 h1
    linear_combination h0 + h1
  rw [successProbability.eq_1]
  simp only [hvec, Fintype.sum_prod_type]
  norm_num [input0.eq_1, Fin.sum_univ_two, norm_mul]
  rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

private theorem replacement_value (t u : Fin 2 → ℝ)
    (ht : ∀ j, 0 < t j) (hu : ∀ j, 0 < u j) :
    coherentValue (replacement t) (replacement u) =
      (Real.sqrt (t 0 ^ 2 + u 0 ^ 2) + Real.sqrt (t 1 ^ 2 + u 1 ^ 2)) ^ 2 / 4 := by
  let S : Set ℝ := {p : ℝ | ∃ (R E : Type) (_ : Fintype R) (_ : Fintype E)
    (_ : DecidableEq R) (_ : DecidableEq E) (e0 : E)
    (ψ : R × Fin 2 → ℂ) (V : Matrix.unitaryGroup (R × Fin 2 × E × Fin 2) ℂ),
    (∑ x, ‖ψ x‖ ^ 2) = 1 ∧ p = successProbability (replacement t) (replacement u) ψ V e0}
  let b := (Real.sqrt (t 0 ^ 2 + u 0 ^ 2) + Real.sqrt (t 1 ^ 2 + u 1 ^ 2)) ^ 2 / 4
  have hmem : b ∈ S := by
    refine ⟨Unit, Unit, inferInstance, inferInstance, inferInstance, inferInstance,
      (), input0, ⟨controlled t u, controlled_unitary t u ht⟩, ?_, ?_⟩
    · norm_num [input0.eq_1, Fintype.sum_prod_type, Fin.sum_univ_two]
    · exact (attaining t u ht hu).symm
  have hupper : ∀ p ∈ S, p ≤ b := by
    rintro p ⟨R, E, fR, fE, dR, dE, e0, ψ, V, hψ, rfl⟩
    exact @success_upper R E fR fE dR dE t u ht hu ψ hψ V e0
  have hbounded : BddAbove S := ⟨b, hupper⟩
  rw [coherentValue.eq_1]
  change sSup S = b
  exact le_antisymm (csSup_le ⟨b, hmem⟩ hupper) (le_csSup hbounded hmem)

/-- Coherent discrimination bias violates the triangle inequality on replacement channels. -/
theorem result : ¬ claim := by
  rw [claim.eq_1]
  intro h
  let a : Fin 2 → ℝ := ![3/4, 1/4]
  let b : Fin 2 → ℝ := ![1/2, 1/2]
  let c : Fin 2 → ℝ := ![1/4, 3/4]
  have ha : ∀ j, 0 < a j := by intro j; fin_cases j <;> norm_num [a]
  have hb : ∀ j, 0 < b j := by intro j; fin_cases j <;> norm_num [b]
  have hc : ∀ j, 0 < c j := by intro j; fin_cases j <;> norm_num [c]
  have hna : IsKrausChannel (replacement a) :=
    replacement_normalized a (fun j => (ha j).le) (by norm_num [a])
  have hnb : IsKrausChannel (replacement b) :=
    replacement_normalized b (fun j => (hb j).le) (by norm_num [b])
  have hnc : IsKrausChannel (replacement c) :=
    replacement_normalized c (fun j => (hc j).le) (by norm_num [c])
  have hs13 := Real.sq_sqrt (by norm_num : 0 ≤ (13 : ℝ))
  have hs5 := Real.sq_sqrt (by norm_num : 0 ≤ (5 : ℝ))
  have hcross : Real.sqrt (13 : ℝ) * Real.sqrt (5 : ℝ) = Real.sqrt 65 := by
    rw [← Real.sqrt_mul (by norm_num : 0 ≤ (13 : ℝ))]
    norm_num
  have hac : coherentValue (replacement a) (replacement c) = 5/8 := by
    rw [replacement_value a c ha hc]
    norm_num [a, c]
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (8 : ℝ))]
  have hab : coherentValue (replacement a) (replacement b) = (9 + Real.sqrt 65)/32 := by
    rw [replacement_value a b ha hb]
    norm_num [a, b]
    nlinarith [hcross]
  have hbc : coherentValue (replacement b) (replacement c) = (9 + Real.sqrt 65)/32 := by
    rw [replacement_value b c hb hc]
    norm_num [b, c]
    nlinarith [hcross]
  have htriangle := h (replacement a) (replacement b) (replacement c) hna hnb hnc
  rw [hac, hab, hbc] at htriangle
  have h65 : Real.sqrt 65 < 9 := (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  linarith

end

end D5.S3.Quantum.QuantumChannels.CoherentDiscriminationTriangleRefutation
