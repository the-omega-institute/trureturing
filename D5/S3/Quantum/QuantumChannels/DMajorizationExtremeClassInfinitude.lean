/- GID: D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.claim; result=D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.result; claim=D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.claim
   digest: Infinitely many extreme classes for a two-dimensional D-majorization set. -/

import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation

/-! The Gibbs-preserving image of a pure qubit has infinitely many extreme classes. -/

set_option autoImplicit false
set_option linter.style.longLine false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude

/-- A source quantum channel is a completely positive, trace-preserving linear map. -/
def IsQuantumChannel {n : ℕ} (t : MatrixMap (Fin n) (Fin n) ℂ) : Prop :=
  t.IsCompletelyPositive ∧ ∀ x, (t x).trace = x.trace

/-- Matrix D-majorization by a channel fixing the positive diagonal matrix. -/
def DMajorizedBy {n : ℕ} (d : Fin n → ℝ) (x a : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ t : MatrixMap (Fin n) (Fin n) ℂ, IsQuantumChannel t ∧ t a = x ∧
    t (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (d i : ℂ))

/-- The set of matrices D-majorized by the specified initial matrix. -/
def majorizationSet {n : ℕ} (d : Fin n → ℝ) (a : Matrix (Fin n) (Fin n) ℂ) :
    Set (Matrix (Fin n) (Fin n) ℂ) := {x | DMajorizedBy d x a}

/-- Finiteness of the extreme classes under unitaries commuting with D. -/
def claim : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ), (∀ i, 0 < d i) →
    ∀ a : Matrix (Fin n) (Fin n) ℂ,
      ∃ f : Finset (Matrix (Fin n) (Fin n) ℂ),
        ∀ x ∈ Set.extremePoints ℝ (majorizationSet d a),
          ∃ y ∈ f, ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ,
            u * diagonal (fun i => (d i : ℂ)) = diagonal (fun i => (d i : ℂ)) * u ∧
              x = u * y * star u

private def d : Fin 2 → ℝ := ![1 / 3, 2 / 3]
private def a : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]
private def p (m : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(m : ℂ)^2 / ((m : ℂ)^2 + 1), (m : ℂ) / ((m : ℂ)^2 + 1);
     (m : ℂ) / ((m : ℂ)^2 + 1), 1 / ((m : ℂ)^2 + 1)]

private lemma denominator_ne (m : ℕ) : (m : ℂ)^2 + 1 ≠ 0 := by
  exact_mod_cast (show m^2 + 1 ≠ 0 by omega)

private def kraus (m : ℕ) : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  let r : ℂ := (Real.sqrt ((m : ℝ)^2 + 1) : ℂ)⁻¹
  let s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  ![!![(m : ℂ) * r, 0; r, 0],
    !![0, r * s; 0, -(m : ℂ) * r * s],
    !![0, 0; 0, s]]

private lemma kraus_action (m : ℕ) (x : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus (kraus m) (kraus m) x =
      x 0 0 • p m + (x 1 1 / 2) • (1 - p m + diagonal ![0, 1]) := by
  have hr : ((Real.sqrt ((m : ℝ)^2 + 1) : ℂ)⁻¹)^2 = ((m : ℂ)^2 + 1)⁻¹ := by
    rw [inv_pow]
    congr 1
    exact_mod_cast (Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ)^2 + 1))
  have hs : ((Real.sqrt 2 : ℂ)⁻¹)^2 = (2 : ℂ)⁻¹ := by
    rw [inv_pow]
    congr 1
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  rw [MatrixMap.of_kraus]
  simp only [Fin.sum_univ_three, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  delta kraus p
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.one_apply,
      Matrix.diagonal_apply, star_mul, star_neg, star_zero, star_one, star_inv,
      star_natCast, Complex.star_def, map_mul, map_neg, map_zero, map_one,
      map_natCast, map_inv₀, Complex.conj_ofReal, zero_mul,
      mul_zero, mul_one, one_mul, add_zero, zero_add, ↓reduceIte] <;>
    ring_nf at hr hs ⊢ <;> rw [hr, hs] <;> field_simp <;> ring

private lemma pure_mem (m : ℕ) : p m ∈ majorizationSet d a := by
  refine ⟨MatrixMap.of_kraus (kraus m) (kraus m),
    ⟨MatrixMap.of_kraus_isCompletelyPositive _, ?_⟩, ?_, ?_⟩
  · intro x
    rw [kraus_action, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    have hp : (p m).trace = 1 := by
      rw [Matrix.trace_fin_two]
      delta p
      dsimp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
    rw [Matrix.trace_add, Matrix.trace_sub, hp]
    norm_num [Matrix.trace_fin_two]
  · rw [kraus_action]
    delta a
    norm_num
  · rw [kraus_action]
    ext i j
    delta d p
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.diagonal_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply] <;> ring

private lemma density (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : x ∈ majorizationSet d a) : x.PosSemidef ∧ x.trace = 1 := by
  obtain ⟨t, ht, hta, _⟩ := hx
  constructor
  · rw [← hta]
    apply ht.1.IsPositive
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp
  · rw [← hta, ht.2]
    delta a
    norm_num [Matrix.trace_fin_two]

private lemma pure_rigidity (m : ℕ) (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : x.PosSemidef) (ht : x.trace = 1)
    (hk : x *ᵥ ![1, -(m : ℂ)] = 0) : x = p m := by
  have h0 := congrFun hk 0
  have h1 := congrFun hk 1
  change x 0 ⬝ᵥ ![1, -(m : ℂ)] = 0 at h0
  change x 1 ⬝ᵥ ![1, -(m : ℂ)] = 0 at h1
  rw [Matrix.vec2_dotProduct] at h0 h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have h01 : x 0 1 = (m : ℂ) * x 1 1 := by
    have hc := congrArg star h1
    simp only [star_add, star_mul, star_neg, star_zero, star_natCast,
      hx.isHermitian.apply 0 1, hx.isHermitian.apply 1 1, mul_one] at hc
    linear_combination hc
  rw [Matrix.trace_fin_two] at ht
  have hd := denominator_ne m
  have h11 : x 1 1 * ((m : ℂ)^2 + 1) = 1 := by
    linear_combination ht - h0 - (m : ℂ) * h01
  ext i j
  delta p
  fin_cases i <;> fin_cases j <;>
    dsimp only [Fin.reduceFinMk, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    apply (eq_div_iff hd).2
  · linear_combination ((m : ℂ)^2 + 1) * h0 +
      (m : ℂ) * ((m : ℂ)^2 + 1) * h01 + (m : ℂ)^2 * h11
  · linear_combination ((m : ℂ)^2 + 1) * h01 + (m : ℂ) * h11
  · linear_combination ((m : ℂ)^2 + 1) * h1 + (m : ℂ) * h11
  · exact h11

private lemma pure_extreme (m : ℕ) :
    p m ∈ Set.extremePoints ℝ (majorizationSet d a) := by
  refine ⟨pure_mem m, ?_⟩
  intro x hx y hy hp
  obtain ⟨r, s, hr, hs, _, he⟩ := hp
  obtain ⟨hxpos, hxtr⟩ := density x hx
  obtain ⟨hypos, _⟩ := density y hy
  let v : Fin 2 → ℂ := ![1, -(m : ℂ)]
  have hpv : p m *ᵥ v = 0 := by
    ext i
    change p m i ⬝ᵥ v = 0
    rw [Matrix.vec2_dotProduct]
    delta p
    fin_cases i <;>
      dsimp only [v, Fin.reduceFinMk, Fin.isValue, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      field_simp <;> ring
  have hq : r • (star v ⬝ᵥ x *ᵥ v) + s • (star v ⬝ᵥ y *ᵥ v) = 0 := by
    rw [← dotProduct_smul, ← dotProduct_smul, ← dotProduct_add,
      ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, ← Matrix.add_mulVec, he, hpv]
    simp
  have hxq := Complex.nonneg_iff.mp (hxpos.dotProduct_mulVec_nonneg v)
  have hyq := Complex.nonneg_iff.mp (hypos.dotProduct_mulVec_nonneg v)
  have hqr := congrArg Complex.re hq
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re] at hqr
  have hxzero : star v ⬝ᵥ x *ᵥ v = 0 := by
    apply Complex.ext
    · change (star v ⬝ᵥ x *ᵥ v).re = 0
      nlinarith [mul_nonneg hs.le hyq.1]
    · exact hxq.2.symm
  exact pure_rigidity m x hxpos hxtr (hxpos.dotProduct_mulVec_zero_iff.mp hxzero)

private lemma invariant (y u : Matrix (Fin 2) (Fin 2) ℂ)
    (hunit : u ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hu : u * diagonal (fun i => (d i : ℂ)) = diagonal (fun i => (d i : ℂ)) * u) :
    (diagonal (fun i => (d i : ℂ)) * (u * y * star u)).trace =
      (diagonal (fun i => (d i : ℂ)) * y).trace := by
  have hstar : star u * u = 1 := Matrix.mem_unitaryGroup_iff'.mp hunit
  calc
    _ = (diagonal (fun i => (d i : ℂ)) * u * y * star u).trace := by
      simp only [Matrix.mul_assoc]
    _ = (u * diagonal (fun i => (d i : ℂ)) * y * star u).trace := by rw [← hu]
    _ = (star u * (u * diagonal (fun i => (d i : ℂ)) * y)).trace :=
      Matrix.trace_mul_comm _ _
    _ = _ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hstar, Matrix.one_mul]

private lemma invariant_injective :
    Function.Injective (fun m : ℕ => (diagonal (fun i => (d i : ℂ)) * p m).trace) := by
  have ht (m : ℕ) : (diagonal (fun i => (d i : ℂ)) * p m).trace =
      ((m : ℂ)^2 + 2) / (3 * ((m : ℂ)^2 + 1)) := by
    rw [Matrix.trace_fin_two]
    delta d p
    simp only [Matrix.diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
    field_simp
  intro m k he
  change (diagonal (fun i => (d i : ℂ)) * p m).trace =
    (diagonal (fun i => (d i : ℂ)) * p k).trace at he
  rw [ht, ht] at he
  have hd (j : ℕ) : (3 : ℂ) * ((j : ℂ)^2 + 1) ≠ 0 :=
    mul_ne_zero (by norm_num) (denominator_ne j)
  have hc := (div_eq_div_iff (hd m) (hd k)).mp he
  have hs : (m : ℂ)^2 = (k : ℂ)^2 := by linear_combination -hc / 3
  have hn : m^2 = k^2 := by exact_mod_cast hs
  nlinarith

/-- The two-dimensional counterexample has infinitely many extreme unitary classes. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨f, hf⟩ := hc 2 d (by intro i; delta d; fin_cases i <;> norm_num) a
  have hw (m : ℕ) := hf (p m) (pure_extreme m)
  choose y hy u hu he using hw
  have hi : Function.Injective y := by
    intro m k hmk
    apply invariant_injective
    change (diagonal (fun i => (d i : ℂ)) * p m).trace =
      (diagonal (fun i => (d i : ℂ)) * p k).trace
    rw [(he m).2, (he k).2,
      invariant (y m) (u m) (hu m) (he m).1,
      invariant (y k) (u k) (hu k) (he k).1, hmk]
  exact Set.infinite_univ.not_finite (f.finite_toSet.preimage hi.injOn |>.subset
    (by intro m _; exact hy m))

end D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude
