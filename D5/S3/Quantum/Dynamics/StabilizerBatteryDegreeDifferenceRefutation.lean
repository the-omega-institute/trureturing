/- GID: D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation.claim; result=D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation.result; claim=D5/S3/Quantum/Dynamics/StabilizerBatteryDegreeDifferenceRefutation.claim
   digest: Equal degree gaps give different stored work for fourteen-qubit stabilizer batteries. -/

import Mathlib.Algebra.Group.AddChar

import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm

/-! Circulant graph stabilizers define the initial battery state and the charging unitary.
The fourteen-site pairs with degree gap four give different work at quarter-period time. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Dynamics.StabilizerBatteryDegreeDifferenceRefutation

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (complex_sign_val tensor_smul tensor_weyl)

/-- The undirected circulant graph with neighbours at distances one through `K / 2`. -/
def adjacent (N K : ℕ) (i j : Fin N) : Prop :=
  i ≠ j ∧ ∃ d ∈ Finset.range (K / 2),
    j.val = (i.val + (d + 1)) % N ∨ i.val = (j.val + (d + 1)) % N

instance (N K : ℕ) (i j : Fin N) : Decidable (adjacent N K i j) :=
  inferInstanceAs (Decidable (_ ∧ ∃ d ∈ Finset.range (K / 2), _))

/-- One `X` at the centre and `Z` at each graph neighbour. -/
def gen (N K : ℕ) (i : Fin N) : Fin N → Pauli :=
  fun j => if j = i then .X else if adjacent N K i j then .Z else .I

/-- The battery or charger Hamiltonian, with unit stabilizer couplings. -/
def hamiltonian (N K : ℕ) : Operator N := ∑ i, wordOp (gen N K i)

/-- The largest even degree permitted by the periodic model. -/
def maxDegree (N : ℕ) : ℕ := if Even N then N - 2 else N - 1

/-- Positive interior degrees exclude both endpoint Hamiltonians. -/
def admissible (N K : ℕ) : Prop := Even K ∧ 2 ≤ K ∧ K + 2 ≤ maxDegree N

/-- A unit vector attaining the minimum energy among all unit vectors. -/
def IsGroundState {N : ℕ} (H : Operator N) (g : State N) : Prop :=
  (∑ b, ‖g b‖ ^ 2) = 1 ∧
    ∀ v : State N, (∑ b, ‖v b‖ ^ 2) = 1 →
      (star g ⬝ᵥ (H *ᵥ g)).re ≤ (star v ⬝ᵥ (H *ᵥ v)).re

/-- Stored work from the source's unitary evolution and rank-one initial density. -/
def work (N Kb Kc : ℕ) (g : State N) (t : ℝ) : ℝ :=
  let ρ₀ := vecMulVec g (star g)
  let U := NormedSpace.exp (-(Complex.I * (t : ℂ)) • hamiltonian N Kc)
  (trace ((U * ρ₀ * Uᴴ - ρ₀) * hamiltonian N Kb)).re

/-- Stored work depends only on the degree gap, away from multiples of four. -/
def claim : Prop :=
  ∀ (N : ℕ), 2 < N → ¬ 4 ∣ N →
    ∀ (Kb Kc Lb Lc : ℕ),
      admissible N Kb → admissible N Kc → admissible N Lb → admissible N Lc →
      Kb ≠ Kc → Lb ≠ Lc → Nat.dist Kc Kb = Nat.dist Lc Lb →
      ∀ (g h : State N), IsGroundState (hamiltonian N Kb) g →
        IsGroundState (hamiltonian N Lb) h →
        ∀ t : ℝ, 0 ≤ t → work N Kb Kc g t = work N Lb Lc h t

private def graphExponent (N K : ℕ) (b : Fin N → ZMod 2) : ℕ :=
  (∑ i, (b i).val) +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ adjacent N K i j),
      (b i).val * (b j).val

/-- The negative-eigenvalue graph state, including its normalization factor. -/
def graphVec (N K : ℕ) : State N :=
  fun b => ((Real.sqrt (2 ^ N : ℝ))⁻¹ : ℂ) * (-1 : ℂ) ^ graphExponent N K b

private def residualMask (N K : ℕ) (w : Fin N → Pauli) : Fin N → ZMod 2 :=
  fun j => (id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) j + ∑ i, if adjacent N K i j then (id (α := Fin N → ZMod 2) (flipBit ∘ w)) i else 0

private def wordPhase (N K : ℕ) (w : Fin N → Pauli) : GaussianInt :=
  (⟨0, 1⟩ : GaussianInt) ^ (Finset.univ.filter (fun i => w i = .Y)).card *
    (-1) ^ (graphExponent N K ((id (α := Fin N → ZMod 2) (flipBit ∘ w))) + ∑ i, ((id (α := Fin N → ZMod 2) (flipBit ∘ w)) i).val * ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i).val)

private def phaseCode : Pauli → Pauli → GaussianInt
  | .X, .Y | .Y, .Z | .Z, .X => ⟨0, 1⟩
  | .Y, .X | .Z, .Y | .X, .Z => ⟨0, -1⟩
  | _, _ => 1

private def wordFold {N : ℕ} : List (Fin N → Pauli) → GaussianInt × (Fin N → Pauli)
  | [] => (1, fun _ => .I)
  | w :: ws =>
    let v := wordFold ws
    (v.1 * ∏ i, phaseCode (w i) (v.2 i), fun i => letterProduct (w i) (v.2 i))

private def antiIndices (N Kb Kc : ℕ) (i : Fin N) : List (Fin N) :=
  (List.ofFn (fun j : Fin N => j)).filter (fun j =>
    (∏ k, sgn (gen N Kb i k) (gen N Kc j k)) = -1)

private def qData (N Kb Kc : ℕ) (i : Fin N) : GaussianInt × (Fin N → Pauli) :=
  let a := antiIndices N Kb Kc i
  let v := wordFold (gen N Kb i :: a.map (gen N Kc))
  ((⟨0, -1⟩ : GaussianInt) ^ a.length * v.1, v.2)

private def quarterFactor {N : ℕ} (S : Operator N) : Operator N :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (1 - Complex.I • S)

private lemma adjacent_comm (N K : ℕ) (i j : Fin N) :
    adjacent N K i j ↔ adjacent N K j i := by
  constructor
  · rintro ⟨h, d, hd, he | he⟩
    · exact ⟨h.symm, d, hd, Or.inr he⟩
    · exact ⟨h.symm, d, hd, Or.inl he⟩
  · rintro ⟨h, d, hd, he | he⟩
    · exact ⟨h.symm, d, hd, Or.inr he⟩
    · exact ⟨h.symm, d, hd, Or.inl he⟩

private lemma generator_sign (N Kb Kc : ℕ) (i j : Fin N) :
    (∏ k, sgn (gen N Kb i k) (gen N Kc j k)) =
      (if adjacent N Kb i j then (-1 : ℤ) else 1) *
        (if adjacent N Kc j i then (-1 : ℤ) else 1) := by
  by_cases hij : i = j
  · subst j
    simp only [adjacent, ne_eq, not_true_eq_false, false_and, if_false, one_mul]
    apply Finset.prod_eq_one
    intro k _
    by_cases hki : k = i
    · simp [gen, hki, sgn, anticomm]
    · simp only [gen, if_neg hki]
      split_ifs <;> decide
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) _
        (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    have hrest : (∏ k ∈ (Finset.univ.erase i).erase j,
        sgn (gen N Kb i k) (gen N Kc j k)) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      have hkj := (Finset.mem_erase.mp hk).1
      simp only [gen, if_neg hki, if_neg hkj]
      split_ifs <;> decide
    rw [hrest, mul_one]
    simp only [gen, if_pos rfl, if_neg hij, if_neg (Ne.symm hij)]
    split_ifs <;> decide

private lemma generators_commute (N K : ℕ) (i j : Fin N) :
    Commute (wordOp (gen N K i)) (wordOp (gen N K j)) := by
  have hs : (∏ k, sgn (gen N K i k) (gen N K j k)) = 1 := by
    rw [generator_sign]
    by_cases ha : adjacent N K i j
    · have hb := (adjacent_comm N K i j).mp ha
      simp only [if_pos ha, if_pos hb]
      norm_num
    · have hb : ¬ adjacent N K j i := fun h => ha ((adjacent_comm N K i j).mpr h)
      simp only [if_neg ha, if_neg hb, one_mul]
  unfold Commute SemiconjBy
  rw [word_comm_sign]
  have hc := congrArg (fun z : ℤ => (z : ℂ)) hs
  simp only [Int.cast_prod, Int.cast_one] at hc
  rw [hc, one_smul]

private lemma cross_commutation (N Kb Kc : ℕ) (i j : Fin N) :
    wordOp (gen N Kb i) * wordOp (gen N Kc j) =
      (if j ∈ antiIndices N Kb Kc i then (-1 : ℂ) else 1) •
        (wordOp (gen N Kc j) * wordOp (gen N Kb i)) := by
  have hm : j ∈ antiIndices N Kb Kc i ↔
      (∏ k, sgn (gen N Kb i k) (gen N Kc j k)) = -1 := by
    simp [antiIndices, List.mem_ofFn]
  rw [word_comm_sign]
  congr 1
  rw [← Int.cast_prod, generator_sign]
  by_cases ha : adjacent N Kb i j <;> by_cases hb : adjacent N Kc j i <;>
    simp [hm, generator_sign, ha, hb]

private def graphMatrix (N K : ℕ) : Matrix (Fin N) (Fin N) (ZMod 2) :=
  fun i j => if adjacent N K i j then 1 else 0

private lemma graph_binary (N K : ℕ) (b : Fin N → ZMod 2) :
    (graphExponent N K b : ZMod 2) = (∑ i, b i) + normalExponent (graphMatrix N K) b := by
  simp only [graphExponent, Nat.cast_add, Nat.cast_sum, Nat.cast_mul,
    ZMod.natCast_zmod_val, normalExponent, graphMatrix, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all

private lemma graph_polarization (N K : ℕ) (b x : Fin N → ZMod 2) :
    (graphExponent N K (b + x) : ZMod 2) + (graphExponent N K b : ZMod 2) =
      (graphExponent N K x : ZMod 2) +
        ∑ j, (∑ i, if adjacent N K i j then x i else 0) * b j := by
  have hs : (graphMatrix N K).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [graphMatrix]
    congr 1
    exact propext (adjacent_comm N K j i)
  have hd (i : Fin N) : graphMatrix N K i i = 0 := by simp [graphMatrix, adjacent]
  have hq := normal_exponent_add (graphMatrix N K) b x
  have hp := symmetric_pairing_split (graphMatrix N K) hs b x
  simp only [hd, zero_mul, Finset.sum_const_zero, zero_add] at hp
  rw [← hp] at hq
  have hb : Matrix.toBilin' (graphMatrix N K) b x =
      ∑ j, (∑ i, if adjacent N K i j then x i else 0) * b j := by
    rw [Matrix.toBilin'_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hs.apply i j]
    by_cases ha : adjacent N K i j <;> simp [graphMatrix, ha, mul_comm]
  rw [hb] at hq
  simp only [graph_binary, Pi.add_apply, Finset.sum_add_distrib]
  linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) hq

private lemma sign_nat (m : ℕ) : (-1 : ℂ) ^ m = complexSign (m : ZMod 2) := by
  rw [complex_sign_val, ZMod.val_natCast, neg_one_pow_eq_pow_mod_two]

private lemma word_action {N : ℕ} (w : Fin N → Pauli) (ψ : State N)
    (b : Fin N → ZMod 2) :
    (wordOp w *ᵥ ψ) b =
      Complex.I ^ (Finset.univ.filter (fun i => w i = .Y)).card *
        complexSign (∑ i, ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i : ZMod 2) * (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))) i) * ψ (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))) := by
  have hm (i : Fin N) : pauliMatrix (w i) =
      (if w i = .Y then Complex.I else 1) •
        (Matrix.of fun r c : Fin 2 =>
          if id (α := ZMod 2) c = id (α := ZMod 2) r + (id (α := Fin N → ZMod 2) (flipBit ∘ w)) i then
            complexSign ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i * id (α := ZMod 2) c) else 0) := by
    have hzero : id (α := ZMod 2) (0 : Fin 2) = 0 := rfl
    have hone : id (α := ZMod 2) (1 : Fin 2) = 1 := rfl
    cases hi : w i <;> ext r c <;> fin_cases r <;> fin_cases c <;>
      norm_num [flipBit, id, Function.comp_def, bellInput, hi, pauliMatrix, complexSign, Matrix.of_apply,
        Matrix.smul_apply, smul_eq_mul, hzero, hone, F₂,
        show (2 : ZMod 2) = 0 by decide,
        D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ] <;> decide
  have hw := congrFun (tensor_weyl ((id (α := Fin N → ZMod 2) (flipBit ∘ w)), (id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w))) ψ) b
  change (tensorOp (fun i => Matrix.of fun r c : Fin 2 =>
      if id (α := ZMod 2) c = id (α := ZMod 2) r + (id (α := Fin N → ZMod 2) (flipBit ∘ w)) i then
        complexSign ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i * id (α := ZMod 2) c) else 0) *ᵥ ψ) b =
    complexSign (∑ i, (id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i * (b i + (id (α := Fin N → ZMod 2) (flipBit ∘ w)) i)) * ψ (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))) at hw
  have he : (fun i => pauliMatrix (w i)) = fun i =>
      (if w i = .Y then Complex.I else 1) •
        (Matrix.of fun r c : Fin 2 =>
          if id (α := ZMod 2) c = id (α := ZMod 2) r + (id (α := Fin N → ZMod 2) (flipBit ∘ w)) i then
            complexSign ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i * id (α := ZMod 2) c) else 0) := funext hm
  rw [wordOp, he, tensor_smul, smul_mulVec]
  change (∏ i, if w i = .Y then Complex.I else 1) * _ = _
  rw [← Finset.prod_filter, Finset.prod_const, hw]
  exact (mul_assoc _ _ _).symm

private lemma graph_word_action (N K : ℕ) (w : Fin N → Pauli) (b : Fin N → ZMod 2) :
    (wordOp w *ᵥ graphVec N K) b =
      (wordPhase N K w : ℂ) *
        complexSign (∑ j, (residualMask N K w j : ZMod 2) * b j) * graphVec N K b := by
  rw [word_action]
  have hphase : (wordPhase N K w : ℂ) =
      Complex.I ^ (Finset.univ.filter (fun i => w i = .Y)).card *
        complexSign ((graphExponent N K ((id (α := Fin N → ZMod 2) (flipBit ∘ w))) : ZMod 2) +
          ∑ i, ((id (α := Fin N → ZMod 2) (flipBit ∘ w)) i : ZMod 2) * (id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i) := by
    simp only [wordPhase, map_mul, map_pow, map_neg, map_one, sign_nat,
      Nat.cast_add, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
    norm_num [GaussianInt.toComplex_def]
  have hp := graph_polarization N K b ((id (α := Fin N → ZMod 2) (flipBit ∘ w)))
  have hexp : (∑ i, ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i : ZMod 2) * (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))) i) +
        (graphExponent N K (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))) : ZMod 2) =
      ((graphExponent N K ((id (α := Fin N → ZMod 2) (flipBit ∘ w))) : ZMod 2) +
        ∑ i, ((id (α := Fin N → ZMod 2) (flipBit ∘ w)) i : ZMod 2) * (id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i) +
        (∑ j, (residualMask N K w j : ZMod 2) * b j) +
        (graphExponent N K b : ZMod 2) := by
    simp only [residualMask, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    simp only [mul_comm] at hp ⊢
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2) = 0 by decide])) hp
  rw [hphase]
  simp only [graphVec, sign_nat]
  rw [show Complex.I ^ (Finset.univ.filter (fun i => w i = .Y)).card *
        complexSign (∑ i, ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i : ZMod 2) * (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))) i) *
        (((Real.sqrt (2 ^ N : ℝ))⁻¹ : ℂ) *
          complexSign (graphExponent N K (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))))) =
      Complex.I ^ (Finset.univ.filter (fun i => w i = .Y)).card *
        ((Real.sqrt (2 ^ N : ℝ))⁻¹ : ℂ) *
          (complexSign (∑ i, ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ w)) i : ZMod 2) * (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))) i) *
            complexSign (graphExponent N K (b + (id (α := Fin N → ZMod 2) (flipBit ∘ w))))) by ring]
  rw [← complexSign_add, hexp, complexSign_add, complexSign_add]
  ring

private lemma graph_generator_eigen (N K : ℕ) (i : Fin N) :
    wordOp (gen N K i) *ᵥ graphVec N K = -graphVec N K := by
  have hx : (id (α := Fin N → ZMod 2) (flipBit ∘ gen N K i)) = Pi.single i 1 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [flipBit, id, Function.comp_def, gen]
    · simp only [flipBit, id, Function.comp_def, gen, if_neg hji, Pi.single_eq_of_ne hji]
      split_ifs <;> rfl
  have hz (j : Fin N) : (id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ gen N K i)) j =
      if adjacent N K i j then 1 else 0 := by
    by_cases hji : j = i
    · subst j
      simp [bellInput, id, Function.comp_def, gen, adjacent]
    · simp only [bellInput, id, Function.comp_def, gen, if_neg hji]
      split_ifs <;> rfl
  have hr : residualMask N K (gen N K i) = 0 := by
    funext j
    have hs : (∑ a, if adjacent N K a j then (Pi.single i (1 : ZMod 2)) a else 0) =
        if adjacent N K i j then 1 else 0 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro a _ hai
        simp [Pi.single_eq_of_ne hai]
      · simp
    rw [residualMask, hx, hz, hs]
    change ((if adjacent N K i j then 1 else 0 : ZMod 2) +
      if adjacent N K i j then 1 else 0) = 0
    split_ifs <;> decide
  have he : graphExponent N K (Pi.single i 1) = 1 := by
    have hq : (∑ a, ∑ b ∈ Finset.univ.filter (fun b => a < b ∧ adjacent N K a b),
        (show ZMod 2 from (Pi.single i (1 : ZMod 2) : Fin N → ZMod 2) a).val *
          (show ZMod 2 from (Pi.single i (1 : ZMod 2) : Fin N → ZMod 2) b).val) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b hb
      have hab := (Finset.mem_filter.mp hb).2.1
      by_cases hai : a = i
      · subst a
        simp [Pi.single_eq_of_ne (ne_of_gt hab)]
      · simp [Pi.single_eq_of_ne hai]
    rw [graphExponent, hq, add_zero, Finset.sum_eq_single i]
    · simp [ZMod.val_one]
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  have hy : Finset.univ.filter (fun j => gen N K i j = .Y) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j _
    simp only [gen]
    split_ifs <;> decide
  have hp : wordPhase N K (gen N K i) = -1 := by
    have hsum : (∑ j, ((id (α := Fin N → ZMod 2) (flipBit ∘ gen N K i)) j).val * ((id (α := Fin N → ZMod 2) (Prod.fst ∘ bellInput ∘ gen N K i)) j).val) = 0 := by
      rw [hx, Finset.sum_eq_single i]
      · simp [hz, adjacent]
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · simp
    unfold wordPhase
    rw [hy, Finset.card_empty, pow_zero, hsum, hx, he]
    norm_num
  funext b
  have ha := graph_word_action N K (gen N K i) b
  rw [hp, hr] at ha
  exact ha.trans (by simp only [map_neg, map_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_zero,
    mul_one, neg_one_mul, Pi.neg_apply])

private lemma graph_normalized (N K : ℕ) : (∑ b, ‖graphVec N K b‖ ^ 2) = 1 := by
  have hpos : 0 < (2 : ℝ) ^ N := by positivity
  simp only [graphVec, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [inv_pow, Real.sq_sqrt hpos.le, mul_inv_cancel₀ hpos.ne']

private lemma involution_energy_nonneg {N : ℕ} (S : Operator N)
    (hS : Sᴴ = S) (hSS : S * S = 1) (v : State N) :
    0 ≤ (star v ⬝ᵥ ((1 + S) *ᵥ v)).re := by
  have hgram : (1 + S)ᴴ * (1 + S) = (2 : ℂ) • (1 + S) := by
    rw [conjTranspose_add, conjTranspose_one, hS]
    simp only [two_smul]
    noncomm_ring [hSS]
  have h := (posSemidef_conjTranspose_mul_self (1 + S)).re_dotProduct_nonneg v
  rw [hgram, smul_mulVec, dotProduct_smul] at h
  norm_num [Complex.mul_re] at h
  linarith

private lemma graph_ground (N K : ℕ) :
    IsGroundState (hamiltonian N K) (graphVec N K) := by
  have hnorm (v : State N) : (star v ⬝ᵥ v).re = ∑ b, ‖v b‖ ^ 2 := by
    simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
      Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  refine ⟨graph_normalized N K, ?_⟩
  intro v hv
  have hg : (star (graphVec N K) ⬝ᵥ (hamiltonian N K *ᵥ graphVec N K)).re =
      -(N : ℝ) := by
    rw [hamiltonian, sum_mulVec, dotProduct_sum, Complex.re_sum]
    simp only [graph_generator_eigen, dotProduct_neg, Complex.neg_re, hnorm, graph_normalized,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg,
      mul_one]
  have hb (i : Fin N) : (-1 : ℝ) ≤
      (star v ⬝ᵥ (wordOp (gen N K i) *ᵥ v)).re := by
    have hi := involution_energy_nonneg (wordOp (gen N K i))
      (word_hermitian _) (wordUnit (gen N K i)).val_inv v
    rw [add_mulVec, one_mulVec, dotProduct_add, Complex.add_re, hnorm, hv] at hi
    linarith
  rw [hg]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hb i)
  simpa only [hamiltonian, sum_mulVec, dotProduct_sum, Complex.re_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg,
    mul_one] using hs

private lemma exp_involution {N : ℕ} (S : Operator N) (hSS : S * S = 1) (t : ℝ) :
    NormedSpace.exp (-(Complex.I * (t : ℂ)) • S) =
      (Real.cos t : ℂ) • 1 - (Complex.I * (Real.sin t : ℂ)) • S := by
  let Φ : (ℂ × ℂ) →ₐ[ℂ] Operator N := {
    toFun := fun z => ((z.1 + z.2) / 2) • 1 + ((z.1 - z.2) / 2) • S
    map_zero' := by simp
    map_one' := by norm_num
    map_add' := by
      rintro ⟨a, b⟩ ⟨c, d⟩
      dsimp
      module
    map_mul' := by
      rintro ⟨a, b⟩ ⟨c, d⟩
      dsimp
      simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, hSS]
      module
    commutes' := by
      intro c
      change ((c + c) / 2) • 1 + ((c - c) / 2) • S = algebraMap ℂ (Operator N) c
      rw [Algebra.algebraMap_eq_smul_one]
      module }
  have hexp := (NormedSpace.map_exp Φ Φ.toLinearMap.continuous_of_finiteDimensional
    (-(Complex.I * (t : ℂ)), Complex.I * (t : ℂ))).symm
  have himage : Φ (-(Complex.I * (t : ℂ)), Complex.I * (t : ℂ)) =
      -(Complex.I * (t : ℂ)) • S := by
    dsimp [Φ]
    module
  rw [himage] at hexp
  rw [hexp]
  change (((NormedSpace.exp (-(Complex.I * (t : ℂ)), Complex.I * (t : ℂ))).1 +
      (NormedSpace.exp (-(Complex.I * (t : ℂ)), Complex.I * (t : ℂ))).2) / 2) • 1 +
    (((NormedSpace.exp (-(Complex.I * (t : ℂ)), Complex.I * (t : ℂ))).1 -
      (NormedSpace.exp (-(Complex.I * (t : ℂ)), Complex.I * (t : ℂ))).2) / 2) • S = _
  rw [Prod.fst_exp, Prod.snd_exp, ← Complex.exp_eq_exp_ℂ]
  have hp : Complex.exp (Complex.I * (t : ℂ)) =
      (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_comm]
  have hn : Complex.exp (-(Complex.I * (t : ℂ))) =
      (Real.cos t : ℂ) - Complex.I * (Real.sin t : ℂ) := by
    rw [show -(Complex.I * (t : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hp, hn]
  module

private lemma evolution_product (N K : ℕ) (t : ℝ) :
    NormedSpace.exp (-(Complex.I * (t : ℂ)) • hamiltonian N K) =
      (List.ofFn (fun j : Fin N =>
        (Real.cos t : ℂ) • (1 : Operator N) -
          (Complex.I * (Real.sin t : ℂ)) • wordOp (gen N K j))).prod := by
  let : NormedAlgebra ℚ (Operator N) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hprod (l : List (Fin N)) :
      NormedSpace.exp (-(Complex.I * (t : ℂ)) • (l.map (fun j => wordOp (gen N K j))).sum) =
        (l.map (fun j => (Real.cos t : ℂ) • (1 : Operator N) -
          (Complex.I * (Real.sin t : ℂ)) • wordOp (gen N K j))).prod := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have hc : Commute (wordOp (gen N K a))
          (l.map (fun j => wordOp (gen N K j))).sum := by
        apply Commute.list_sum_right
        intro B hB
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hB
        exact generators_commute N K a j
      rw [List.map_cons, List.sum_cons, smul_add,
        NormedSpace.exp_add_of_commute (hc.smul_left _ |>.smul_right _),
        exp_involution (wordOp (gen N K a)) (wordUnit (gen N K a)).val_inv t, ih]
      rfl
  have h := hprod (List.ofFn (fun j : Fin N => j))
  simp only [List.map_ofFn, List.sum_ofFn] at h
  exact h

private lemma quarterFactor_adjoint {N : ℕ} (S : Operator N) (hS : Sᴴ = S) :
    (quarterFactor S)ᴴ = ((Real.sqrt 2)⁻¹ : ℂ) • (1 + Complex.I • S) := by
  simp [quarterFactor, hS]

private lemma quarter_conjugate_commuting {N : ℕ} (S B : Operator N)
    (hS : Sᴴ = S) (hSS : S * S = 1) (hSB : S * B = B * S) :
    (quarterFactor S)ᴴ * B * quarterFactor S = B := by
  have hthree : S * B * S = B := by rw [hSB, Matrix.mul_assoc, hSS, Matrix.mul_one]
  have hcore : (1 + Complex.I • S) * B * (1 - Complex.I • S) = (2 : ℂ) • B := by
    simp only [add_mul, sub_mul, mul_sub, mul_add, Matrix.mul_smul, Matrix.smul_mul,
      smul_add, smul_sub, smul_smul, one_mul, mul_one]
    simp only [← Matrix.mul_assoc, hthree, hSB, smul_neg, Complex.I_mul_I]
    simp only [neg_mul, Matrix.mul_assoc, hSS, Matrix.mul_one, smul_neg]
    module
  have hc : (((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ)) = 1 / 2 := by
    rw [← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [quarterFactor_adjoint S hS, quarterFactor]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hcore, smul_smul, hc]
  norm_num

private lemma quarter_conjugate_anticommuting {N : ℕ} (S B : Operator N)
    (hS : Sᴴ = S) (hSS : S * S = 1) (hSB : S * B = -(B * S)) :
    (quarterFactor S)ᴴ * B * quarterFactor S = B * (-Complex.I • S) := by
  have hthree : S * B * S = -B := by
    rw [hSB, neg_mul, Matrix.mul_assoc, hSS, Matrix.mul_one]
  have hcore : (1 + Complex.I • S) * B * (1 - Complex.I • S) =
      (-2 * Complex.I) • (B * S) := by
    simp only [add_mul, sub_mul, mul_sub, mul_add, Matrix.mul_smul, Matrix.smul_mul,
      smul_add, smul_sub, smul_smul, one_mul, mul_one]
    simp only [← Matrix.mul_assoc, hthree, hSB, smul_neg, Complex.I_mul_I]
    simp only [neg_mul, Matrix.mul_assoc, hSS, Matrix.mul_one, smul_neg]
    module
  have hc : (((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ)) = 1 / 2 := by
    rw [← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [quarterFactor_adjoint S hS, quarterFactor]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hcore, smul_smul, hc]
  congr 1
  ring

private lemma quarter_conjugation (N Kb Kc : ℕ) (i : Fin N) :
    let U := NormedSpace.exp
      (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • hamiltonian N Kc)
    Uᴴ * wordOp (gen N Kb i) * U =
      wordOp (gen N Kb i) *
        ((antiIndices N Kb Kc i).map (fun j => -Complex.I • wordOp (gen N Kc j))).prod := by
  have hf (j : Fin N) :
      (Real.cos (Real.pi / 4) : ℂ) • (1 : Operator N) -
        (Complex.I * (Real.sin (Real.pi / 4) : ℂ)) • wordOp (gen N Kc j) =
      quarterFactor (wordOp (gen N Kc j)) := by
    have hs : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
      field_simp
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [Real.cos_pi_div_four, Real.sin_pi_div_four, hs]
    simp only [quarterFactor, smul_sub, smul_smul, smul_eq_mul, mul_comm, Complex.ofReal_inv]
  dsimp only
  rw [evolution_product]
  simp_rw [hf]
  have hlist (l : List (Fin N)) :
      (l.map (fun j => quarterFactor (wordOp (gen N Kc j)))).prodᴴ *
        wordOp (gen N Kb i) *
        (l.map (fun j => quarterFactor (wordOp (gen N Kc j)))).prod =
      wordOp (gen N Kb i) *
        ((l.filter (fun j => j ∈ antiIndices N Kb Kc i)).map
          (fun j => -Complex.I • wordOp (gen N Kc j))).prod := by
    induction l with
    | nil => simp
    | cons a l ih =>
      let T := (l.map (fun j => quarterFactor (wordOp (gen N Kc j)))).prod
      let C := -Complex.I • wordOp (gen N Kc a)
      have hCT : Commute C T := by
        apply Commute.list_prod_right
        intro F hF
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hF
        exact ((Commute.one_right C).sub_right
          ((generators_commute N Kc a j).smul_left _ |>.smul_right _)).smul_right _
      have hCP : Commute C
          ((l.filter (fun j => j ∈ antiIndices N Kb Kc i)).map
            (fun j => -Complex.I • wordOp (gen N Kc j))).prod := by
        apply Commute.list_prod_right
        intro F hF
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hF
        exact (generators_commute N Kc a j).smul_left _ |>.smul_right _
      simp only [List.map_cons, List.prod_cons, conjTranspose_mul]
      change Tᴴ * (quarterFactor (wordOp (gen N Kc a)))ᴴ *
        wordOp (gen N Kb i) * (quarterFactor (wordOp (gen N Kc a)) * T) = _
      rw [Matrix.mul_assoc Tᴴ, ← Matrix.mul_assoc _ _ T,
        Matrix.mul_assoc Tᴴ _ (quarterFactor (wordOp (gen N Kc a)))]
      have hcross := cross_commutation N Kb Kc i a
      by_cases ha : a ∈ antiIndices N Kb Kc i
      · rw [if_pos ha, neg_one_smul] at hcross
        have hanti : wordOp (gen N Kc a) * wordOp (gen N Kb i) =
            -(wordOp (gen N Kb i) * wordOp (gen N Kc a)) := by
          rw [hcross, neg_neg]
        rw [quarter_conjugate_anticommuting _ _ (word_hermitian _)
          (wordUnit (gen N Kc a)).val_inv hanti]
        change Tᴴ * (wordOp (gen N Kb i) * C) * T = _
        rw [Matrix.mul_assoc Tᴴ, Matrix.mul_assoc _ C T, hCT.eq,
          ← Matrix.mul_assoc, ← Matrix.mul_assoc, ih]
        simp only [List.filter_cons, decide_eq_true ha, ite_true, List.map_cons, List.prod_cons]
        rw [Matrix.mul_assoc, hCP.eq, ← Matrix.mul_assoc]
      · rw [if_neg ha, one_smul] at hcross
        rw [quarter_conjugate_commuting _ _ (word_hermitian _)
          (wordUnit (gen N Kc a)).val_inv hcross.symm, ih]
        simp only [List.filter_cons, decide_eq_false ha, Bool.false_eq_true, ite_false]
  have he : (List.ofFn (fun j : Fin N => j)).filter
      (fun j => j ∈ antiIndices N Kb Kc i) = antiIndices N Kb Kc i := by
    unfold antiIndices
    apply List.filter_congr
    intro j _
    simp [List.mem_filter, List.mem_ofFn]
  have h := hlist (List.ofFn (fun j : Fin N => j))
  simpa only [List.map_ofFn, Function.comp_def, he] using h

private lemma phaseCode_cast (p q : Pauli) :
    (phaseCode p q : ℂ) = letterPhase p q := by
  cases p <;> cases q <;> norm_num [phaseCode, letterPhase, GaussianInt.toComplex_def]

private lemma wordFold_operator {N : ℕ} (ws : List (Fin N → Pauli)) :
    (ws.map wordOp).prod = ((wordFold ws).1 : ℂ) • wordOp (wordFold ws).2 := by
  induction ws with
  | nil => simp [wordFold, word_one]
  | cons w ws ih =>
    simp only [List.map_cons, List.prod_cons, wordFold, ih, Matrix.mul_smul, word_mul,
      smul_smul, map_mul, map_prod, phaseCode_cast]

private lemma qData_operator (N Kb Kc : ℕ) (i : Fin N) :
    wordOp (gen N Kb i) *
      ((antiIndices N Kb Kc i).map (fun j => -Complex.I • wordOp (gen N Kc j))).prod =
      ((qData N Kb Kc i).1 : ℂ) • wordOp (qData N Kb Kc i).2 := by
  let a := antiIndices N Kb Kc i
  have hp : (a.map (fun j => -Complex.I • wordOp (gen N Kc j))).prod =
      (-Complex.I) ^ a.length • (a.map (fun j => wordOp (gen N Kc j))).prod := by
    have h := (List.smul_prod (a.map (fun j => wordOp (gen N Kc j))) (-Complex.I)).symm
    simpa only [List.length_map, List.map_map, Function.comp_def] using h
  change wordOp (gen N Kb i) *
    (a.map (fun j => -Complex.I • wordOp (gen N Kc j))).prod = _
  rw [hp, Matrix.mul_smul]
  have hf := wordFold_operator (gen N Kb i :: a.map (gen N Kc))
  simp only [List.map_cons, List.map_map, Function.comp_def, List.prod_cons] at hf
  rw [hf, smul_smul]
  change _ = GaussianInt.toComplex
    ((⟨0, -1⟩ : GaussianInt) ^ a.length *
      (wordFold (gen N Kb i :: a.map (gen N Kc))).1) • _
  rw [map_mul, map_pow]
  have hc : GaussianInt.toComplex (⟨0, -1⟩ : GaussianInt) = -Complex.I := by
    norm_num [GaussianInt.toComplex_def]
  rw [hc]
  rfl

private lemma work_quarter (N Kb Kc : ℕ) :
    work N Kb Kc (graphVec N Kb) (Real.pi / 4) =
      ∑ i, (1 + (((qData N Kb Kc i).1 : ℂ) *
        (star (graphVec N Kb) ⬝ᵥ (wordOp (qData N Kb Kc i).2 *ᵥ
          graphVec N Kb))).re) := by
  let g := graphVec N Kb
  let ρ := vecMulVec g (star g)
  let U := NormedSpace.exp
    (-(Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • hamiltonian N Kc)
  have htr (B : Operator N) : trace (ρ * B) = star g ⬝ᵥ (B *ᵥ g) := by
    rw [trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  have hcyc (B : Operator N) : trace (U * ρ * Uᴴ * B) =
      star g ⬝ᵥ ((Uᴴ * B * U) *ᵥ g) := by
    calc
      trace (U * ρ * Uᴴ * B) = trace ((ρ * Uᴴ * B) * U) := by
        rw [Matrix.mul_assoc U ρ Uᴴ, Matrix.mul_assoc U (ρ * Uᴴ) B, trace_mul_comm]
      _ = trace (ρ * (Uᴴ * B * U)) := by simp only [Matrix.mul_assoc]
      _ = _ := htr _
  have hnorm : (star g ⬝ᵥ g).re = 1 := by
    rw [← graph_normalized N Kb]
    simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
      Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    rfl
  change (trace ((U * ρ * Uᴴ - ρ) * ∑ i, wordOp (gen N Kb i))).re = _
  rw [Matrix.mul_sum, trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.sub_mul, trace_sub, Complex.sub_re, hcyc, htr]
  have hq : Uᴴ * wordOp (gen N Kb i) * U =
      ((qData N Kb Kc i).1 : ℂ) • wordOp (qData N Kb Kc i).2 := by
    rw [show Uᴴ * wordOp (gen N Kb i) * U = _ from quarter_conjugation N Kb Kc i,
      qData_operator]
  rw [hq, smul_mulVec, dotProduct_smul, graph_generator_eigen,
    dotProduct_neg, Complex.neg_re, hnorm]
  change _ - -1 = 1 + _
  simp only [smul_eq_mul]
  ring

private lemma character_vanishes (N : ℕ) (a : Fin N → ZMod 2) (ha : a ≠ 0) :
    (∑ b : Fin N → ZMod 2,
      (-1 : ℂ) ^ (∑ j, (a j).val * (b j).val)) = 0 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  have hk1 : a k = 1 := Fin.eq_one_of_ne_zero _ hk
  let ψ : AddChar (Fin N → ZMod 2) ℂ := {
    toFun := fun b => complexSign (∑ j, a j * b j)
    map_zero_eq_one' := by
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sign_zero]
    map_add_eq_mul' := by
      intro b c
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, complexSign_add] }
  have hψ : ψ ≠ 0 := by
    intro h
    have he := congrArg (fun χ : AddChar (Fin N → ZMod 2) ℂ =>
      χ (Pi.single k 1)) h
    change complexSign (∑ j, a j * (Pi.single k (1 : ZMod 2) : Fin N → ZMod 2) j) = 1 at he
    have hs : (∑ j, a j * (Pi.single k (1 : ZMod 2) : Fin N → ZMod 2) j) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp only [Pi.single_eq_same, mul_one, hk1]
      · intro j _ hj
        simp only [Pi.single_eq_of_ne hj, mul_zero]
      · simp
    rw [hs, sign_one] at he
    norm_num at he
  have hsum : (∑ b : Fin N → ZMod 2,
      (-1 : ℂ) ^ (∑ j, (a j).val * (b j).val)) = ∑ b, ψ b := by
    apply Finset.sum_congr rfl
    intro b _
    rw [sign_nat]
    simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
    rfl
  rw [hsum]
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr hψ

private lemma graph_word_character (N K : ℕ) (w : Fin N → Pauli) :
    star (graphVec N K) ⬝ᵥ (wordOp w *ᵥ graphVec N K) =
      (wordPhase N K w : ℂ) * ((2 : ℂ) ^ N)⁻¹ *
        ∑ b : Fin N → ZMod 2,
          (-1 : ℂ) ^ (∑ j, (residualMask N K w j).val * (b j).val) := by
  have hnorm (b : Fin N → ZMod 2) :
      star (graphVec N K b) * graphVec N K b = ((2 : ℂ) ^ N)⁻¹ := by
    rw [Complex.star_def, Complex.conj_mul']
    simp only [graphVec, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  change (∑ b : Fin N → ZMod 2,
      star (graphVec N K b) * (wordOp w *ᵥ graphVec N K) b) = _
  simp_rw [graph_word_action]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [sign_nat]
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
  calc
    _ = (wordPhase N K w : ℂ) *
        (star (graphVec N K b) * graphVec N K b) *
        complexSign (∑ j, (residualMask N K w j : ZMod 2) * b j) := by ring
    _ = _ := by rw [hnorm]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private lemma pairA_finite (i : Fin 14) :
    (antiIndices 14 4 8 i).length = 4 ∧
      residualMask 14 4 (qData 14 4 8 i).2 = 0 ∧
      (qData 14 4 8 i).1 * wordPhase 14 4 (qData 14 4 8 i).2 = -1 := by
  revert i
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private lemma pairB_finite (i : Fin 14) :
    (antiIndices 14 2 6 i).length = 4 ∧
      residualMask 14 2 (qData 14 2 6 i).2 ≠ 0 := by
  revert i
  decide +kernel

private lemma pairA_expectation (i : Fin 14) :
    ((qData 14 4 8 i).1 : ℂ) *
      (star (graphVec 14 4) ⬝ᵥ (wordOp (qData 14 4 8 i).2 *ᵥ graphVec 14 4)) = -1 := by
  rw [graph_word_character, (pairA_finite i).2.1]
  simp only [Pi.zero_apply, ZMod.val_zero, zero_mul, Finset.sum_const_zero, pow_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  have hphase := congrArg (fun z : GaussianInt => (z : ℂ)) (pairA_finite i).2.2
  norm_num only [map_mul, map_neg, map_one] at hphase
  norm_num
  linear_combination hphase

private lemma pairB_expectation (i : Fin 14) :
    ((qData 14 2 6 i).1 : ℂ) *
      (star (graphVec 14 2) ⬝ᵥ (wordOp (qData 14 2 6 i).2 *ᵥ graphVec 14 2)) = 0 := by
  rw [graph_word_character, character_vanishes _ _ (pairB_finite i).2]
  simp

private lemma pairA_work : work 14 4 8 (graphVec 14 4) (Real.pi / 4) = 0 := by
  rw [work_quarter]
  simp only [pairA_expectation, Complex.neg_re, Complex.one_re, add_neg_cancel,
    Finset.sum_const_zero]

private lemma pairB_work : work 14 2 6 (graphVec 14 2) (Real.pi / 4) = 14 := by
  rw [work_quarter]
  simp only [pairB_expectation, Complex.zero_re, add_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_ofNat]

/-- The fourteen-site interior counterexample has equal degree gaps and unequal work. -/
theorem result : ¬ claim := by
  intro hc
  have h := hc 14 (by decide) (by decide) 4 8 2 6
    (by unfold admissible; decide) (by unfold admissible; decide)
    (by unfold admissible; decide) (by unfold admissible; decide)
    (by decide) (by decide) (by decide) (graphVec 14 4) (graphVec 14 2)
    (graph_ground 14 4) (graph_ground 14 2) (Real.pi / 4) (by positivity)
  rw [pairA_work, pairB_work] at h
  norm_num at h

end
end D5.S3.Quantum.Dynamics.StabilizerBatteryDegreeDifferenceRefutation
