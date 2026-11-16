/- GID: D5/S3/Quantum/Fermionic/BcGhostStateFieldLocality
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostStateFieldLocality
   mirror-E: none(waiver:algebraic-ghost-superlocality)
   anchors: []
   utility: none
   digest: Signed finite-residue cancellation for the actual ghost word fields. -/

/-
proof_shape: stateField_locality: content
escape_witness: Actual CAR, sorted occupation-word induction and homogeneous
support-sign extraction extend generic signed locality to every actual state.
admission_basis: escape-witness
-/

import D5.S3.Quantum.Fermionic.BcGhostStateField
import D5.S3.VertexAlgebra.FieldNormalProductLocality

/-! Generic signed normal-product and divided-derivative locality are specialized
to the actual occupation-word construction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostStateField
open D5.S3.VertexAlgebra.FieldNormalProduct
open D5.S3.VertexAlgebra.FieldNormalProductLocality
open private signedNormalMinusOne wordField generatingField generating_modes
  generatingMode derivative_modes Y_ket forward_finite reverse_finite from
  D5.S3.Quantum.Fermionic.BcGhostStateField

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality

private def signedComm (s : ℂ) (A B : VertexOperator ℂ Fock) :
    ℤ → ℤ → Module.End ℂ Fock :=
  D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm s A B

private theorem signedNormal_locality (x y z : ℂ) (A B C : VertexOperator ℂ Fock)
    (Na Nb Nc : ℕ) (hAC : delta^[Na] (signedComm y A C) = 0)
    (hBC : delta^[Nb] (signedComm z B C) = 0)
    (hAB : delta^[Nc] (signedComm x A B) = 0) :
    delta^[Na + Nb + Nc] (signedComm (y * z) (signedNormalMinusOne x A B).1 C) = 0 := by
  exact D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedNormal_locality
    x y z A B C Na Nb Nc hAC hBC hAB

private def Local (s : ℂ) (A B : VertexOperator ℂ Fock) : Prop :=
  ∃ N : ℕ, delta^[N] (signedComm s A B) = 0
private theorem signedDerivative_locality (s : ℂ) (first second : VertexOperator ℂ Fock) (order degree : ℕ)
    (killed : delta^[order] (signedComm s first second) = 0) :
    delta^[order + degree] (signedComm s (dividedDerivative degree first) second) = 0 := by
  exact D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedDerivative_locality
    s first second order degree killed

private theorem local_symm (s : ℂ) (hs : s * s = 1) (A B : VertexOperator ℂ Fock)
    (h : Local s A B) : Local s B A := by
  obtain ⟨N, hN⟩ := h
  have flipIterate (D : ℤ → ℤ → Module.End ℂ Fock) (k : ℕ) :
      delta^[k] (flipDistribution D) = ((-1 : ℂ) ^ k) • flipDistribution (delta^[k] D) := by
    have involution (E : ℤ → ℤ → Module.End ℂ Fock) :
        D5.S3.VertexAlgebra.BinomialKernelDelta.normalized
          (D5.S3.VertexAlgebra.BinomialKernelDelta.normalized E) = E := by
      funext m n
      dsimp [D5.S3.VertexAlgebra.BinomialKernelDelta.normalized]
      congr 1 <;> omega
    have swap : D5.S3.VertexAlgebra.BinomialKernelDelta.normalized
        (D5.S3.VertexAlgebra.BinomialKernelDelta.flip
          (D5.S3.VertexAlgebra.BinomialKernelDelta.normalized D)) =
          flipDistribution D := by
      funext m n
      dsimp [D5.S3.VertexAlgebra.BinomialKernelDelta.normalized,
        D5.S3.VertexAlgebra.BinomialKernelDelta.flip, flipDistribution]
      congr 1 <;> omega
    have original :=
      D5.S3.VertexAlgebra.BinomialKernelDelta.normalized_iterate
      (D5.S3.VertexAlgebra.BinomialKernelDelta.normalized D) k
    rw [involution] at original
    calc
      _ = D5.S3.VertexAlgebra.BinomialKernelDelta.normalized
          (D5.S3.VertexAlgebra.BinomialKernelDelta.rawDelta^[k]
            (D5.S3.VertexAlgebra.BinomialKernelDelta.flip
              (D5.S3.VertexAlgebra.BinomialKernelDelta.normalized D))) := by
        simpa only [swap] using
          D5.S3.VertexAlgebra.BinomialKernelDelta.normalized_iterate
            (D5.S3.VertexAlgebra.BinomialKernelDelta.flip
              (D5.S3.VertexAlgebra.BinomialKernelDelta.normalized D)) k
      _ = ((-1 : ℂ) ^ k) • flipDistribution
          (D5.S3.VertexAlgebra.BinomialKernelDelta.normalized
            (D5.S3.VertexAlgebra.BinomialKernelDelta.rawDelta^[k]
              (D5.S3.VertexAlgebra.BinomialKernelDelta.normalized D))) := by
        rw [D5.S3.VertexAlgebra.BinomialKernelDelta.rawDelta_iterate_flip]
        rfl
      _ = _ := by rw [← original]
  have reversed : signedComm s B A = (-s) • flipDistribution (signedComm s A B) := by
    funext l r
    simp only [signedComm,
      D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm,
      flipDistribution, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, Pi.smul_apply,
      smul_sub, smul_smul, neg_mul, hs, neg_one_smul]
    module
  refine ⟨N, ?_⟩
  rw [reversed]
  change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[N]
    ((-s) • flipDistribution (signedComm s A B)) = 0
  rw [← Module.End.pow_apply, map_smul, Module.End.pow_apply]
  change (-s) • delta^[N] (flipDistribution (signedComm s A B)) = 0
  rw [flipIterate, hN, map_zero, smul_zero, smul_zero]

private theorem identity_local (A : VertexOperator ℂ Fock) : Local 1 identityField A := by
  refine ⟨0, ?_⟩
  funext l r
  have identityModes (n : ℤ) : (identityField : VertexOperator ℂ Fock) [[n]] =
      if n = -1 then LinearMap.id else 0 := by
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    simp only [show -n - 1 = 0 ↔ n = -1 by omega]
  simp only [Function.iterate_zero_apply, signedComm,
      D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm, identityModes, one_smul]
  split_ifs <;> simp [Module.End.mul_eq_comp]

private theorem normal_local (x y z : ℂ) (A B C : VertexOperator ℂ Fock)
    (hAC : Local y A C) (hBC : Local z B C) (hAB : Local x A B) :
    Local (y * z) (signedNormalMinusOne x A B).1 C := by
  obtain ⟨Na, ha⟩ := hAC
  obtain ⟨Nb, hb⟩ := hBC
  obtain ⟨Nc, hc⟩ := hAB
  exact ⟨Na + Nb + Nc, signedNormal_locality x y z A B C Na Nb Nc ha hb hc⟩

private theorem generating_local (a b : Bool) : Local (-1) (generatingField a) (generatingField b) := by
  have mixed (l r : ℤ) : signedComm (-1) (generatingField false) (generatingField true) l r =
      if l + r + 1 = 0 then (1 : Module.End ℂ Fock) else 0 := by
    simp only [signedComm,
      D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm,
      generating_modes, generatingMode, Bool.false_eq_true, ite_false,
      ite_true, neg_one_smul, sub_neg_eq_add]
    rw [ghost_mixed_car, show (l - 1) + (r + 2) = l + r + 1 by omega]
  cases a <;> cases b
  · refine ⟨0, ?_⟩
    funext l r
    simpa only [Function.iterate_zero_apply, signedComm,
      D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm,
      generating_modes, generatingMode,
      Bool.false_eq_true, ite_false, neg_one_smul, sub_neg_eq_add, Pi.zero_apply] using
      ghost_b_car (l - 1) (r - 1)
  · refine ⟨1, ?_⟩
    funext l r
    simp only [Function.iterate_one, delta, mixed]
    rw [show l + 1 + r + 1 = l + (r + 1) + 1 by omega]
    simp
  · apply local_symm (-1) (by norm_num)
    refine ⟨1, ?_⟩
    funext l r
    simp only [Function.iterate_one, delta, mixed]
    rw [show l + 1 + r + 1 = l + (r + 1) + 1 by omega]
    simp
  · refine ⟨0, ?_⟩
    funext l r
    simpa only [Function.iterate_zero_apply, signedComm,
      D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm,
      generating_modes, generatingMode,
      ite_true, neg_one_smul, sub_neg_eq_add, Pi.zero_apply] using
      ghost_c_car (l + 2) (r + 2)

private theorem derivatives_local (a b : Bool) (k l : ℕ) :
    Local (-1) (dividedDerivative k (generatingField a)) (dividedDerivative l (generatingField b)) := by
  obtain ⟨N, hN⟩ := generating_local a b
  have hk := signedDerivative_locality (-1) (generatingField a) (generatingField b) N k hN
  have hrev := local_symm (-1) (by norm_num) _ _ ⟨N + k, hk⟩
  obtain ⟨M, hM⟩ := hrev
  have hl := signedDerivative_locality (-1) (generatingField b)
    (dividedDerivative k (generatingField a)) M l hM
  exact local_symm (-1) (by norm_num) _ _ ⟨M + l, hl⟩

private theorem word_local (w u : List ℕ) :
    Local ((-1 : ℂ) ^ (w.length * u.length)) (wordField w) (wordField u) := by
  have signSquare (p : ℕ) : ((-1 : ℂ) ^ p) * ((-1 : ℂ) ^ p) = 1 := by
    rw [← mul_pow]
    norm_num
  have generatorWord : ∀ (u : List ℕ) (j : ℕ),
      Local ((-1 : ℂ) ^ u.length)
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1))) (wordField u) := by
    intro u
    induction u with
    | nil =>
      intro j
      exact local_symm 1 (by norm_num) _ _ (identity_local _)
    | cons k tail ih =>
      intro j
      have h := normal_local ((-1 : ℂ) ^ tail.length) (-1) ((-1 : ℂ) ^ tail.length)
        (dividedDerivative (k / 2) (generatingField (k % 2 == 1))) (wordField tail)
        (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
        (derivatives_local _ _ _ _)
        (local_symm _ (signSquare tail.length) _ _ (ih j)) (ih k)
      have hout : (-1 : ℂ) * (-1 : ℂ) ^ tail.length = (-1 : ℂ) ^ (k :: tail).length := by
        simp only [List.length_cons, pow_succ']
      rw [hout] at h
      exact local_symm _ (signSquare (k :: tail).length) _ _ h
  induction w with
  | nil => simpa only [List.length_nil, zero_mul, pow_zero, wordField] using identity_local (wordField u)
  | cons j tail ih =>
    have h := normal_local ((-1 : ℂ) ^ tail.length) ((-1 : ℂ) ^ u.length)
      ((-1 : ℂ) ^ (tail.length * u.length))
      (dividedDerivative (j / 2) (generatingField (j % 2 == 1)))
      (wordField tail) (wordField u) (generatorWord u j) ih (generatorWord tail j)
    have hout : (-1 : ℂ) ^ u.length * (-1 : ℂ) ^ (tail.length * u.length) =
        (-1 : ℂ) ^ ((j :: tail).length * u.length) := by
      rw [← pow_add]
      congr 1
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    simpa only [wordField, hout] using h

/-- Every two actual occupation basis states have operator-uniform signed locality. -/
private theorem occupation_locality (S U : Finset ℕ) :
    ∃ N : ℕ, delta^[N] (fun m n =>
      ((Y (ket S)) [[m]]) * ((Y (ket U)) [[n]]) -
        ((-1 : ℂ) ^ (S.card * U.card)) •
          (((Y (ket U)) [[n]]) * ((Y (ket S)) [[m]]))) = 0 := by
  have h := word_local S.sort U.sort
  simp only [Finset.length_sort] at h
  change Local ((-1 : ℂ) ^ (S.card * U.card)) (Y (ket S)) (Y (ket U))
  rw [Y_ket, Y_ket]
  exact h

private theorem monotone (distribution : ℤ → ℤ → Module.End ℂ Fock) (small large : ℕ)
    (less : small ≤ large) (killed : delta^[small] distribution = 0) : delta^[large]
      distribution = 0 := by
  have original : (deltaEnd ^ small) distribution = 0 := by
    rw [Module.End.pow_apply]
    exact killed
  have result := Module.End.pow_map_zero_of_le less original
  rw [Module.End.pow_apply] at result
  exact result
private theorem localAdd (s : ℂ) (first second third : VertexOperator ℂ Fock)
    (firstLocal : Local s first third) (secondLocal : Local s second third) : Local s (first +
      second) third := by
  obtain ⟨firstOrder, firstKilled⟩ := firstLocal
  obtain ⟨secondOrder, secondKilled⟩ := secondLocal
  let order := max firstOrder secondOrder
  have firstBound := monotone (signedComm s first third) firstOrder
    order (le_max_left _ _) firstKilled
  have secondBound := monotone (signedComm s second third)
    secondOrder order (le_max_right _ _) secondKilled
  refine ⟨order, ?_⟩
  have split : signedComm s (first + second) third =
    signedComm s first third + signedComm s
    second third := by
    funext left right
    simp only [signedComm,
      D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm,
      map_add, Pi.add_apply, mul_add, add_mul, smul_add]
    module
  rw [split]
  change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] _ = 0
  rw [← Module.End.pow_apply, map_add]
  simp only [Module.End.pow_apply]
  change delta^[order] (signedComm s first third) +
    delta^[order] (signedComm s second third) = 0
  rw [firstBound, secondBound, add_zero]
private theorem localSmul (s : ℂ) (scalar : ℂ) (first second : VertexOperator ℂ Fock)
    (locality : Local s first second) : Local s (scalar • first) second := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  have split : signedComm s (scalar • first) second = scalar •
    signedComm s first second := by
    funext left right
    simp only [signedComm,
      D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm, map_smul, Pi.smul_apply,
      Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    module
  rw [split]
  change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ Fock))^[order] _ = 0
  rw [← Module.End.pow_apply, map_smul]
  simp only [Module.End.pow_apply]
  change scalar • delta^[order] (signedComm s first second) = 0
  rw [killed, smul_zero]
private theorem localSum (s : ℂ) {Index : Type} (indices : Finset Index) (fields : Index → VertexOperator ℂ Fock)
    (operator : VertexOperator ℂ Fock) (locality : ∀ index ∈ indices, Local s (fields index)
      operator) :
    Local s (∑ index ∈ indices, fields index) operator := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    funext left right
    simp [signedComm,
      D5.S3.VertexAlgebra.SignedFieldNormalProductLocality.signedComm]
  | @insert index indices absent inductionHypothesis =>
    rw [Finset.sum_insert absent]
    exact localAdd s _ _ _ (locality index (Finset.mem_insert_self _ _))
      (inductionHypothesis (fun other member => locality other (Finset.mem_insert_of_mem member)))
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

private theorem parity_coefficient (a : Fock) (S : Finset ℕ) :
    parity a S = (-1 : ℂ) ^ S.card * a S := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb, mul_add]
  | single U z =>
    have hu : Finsupp.single U z = z • ket U := by simp [ket]
    rw [hu, map_smul, parity_ket]
    by_cases h : U = S
    · subst U
      simp [ket, mul_comm]
    · simp [ket, h]

/-- Homogeneous signed locality on every state of the original countable carrier. -/
theorem stateField_locality (a b : Fock) (p q : ℕ)
    (ha : parity a = ((-1 : ℂ) ^ p) • a)
    (hb : parity b = ((-1 : ℂ) ^ q) • b) :
    ∃ N : ℕ, delta^[N] (fun m n =>
      ((Y a) [[m]]) * ((Y b) [[n]]) - ((-1 : ℂ) ^ (p * q)) •
        (((Y b) [[n]]) * ((Y a) [[m]]))) = 0 := by
  classical
  let s := (-1 : ℂ) ^ (p * q)
  have hs : s * s = 1 := by dsimp [s]; rw [← mul_pow]; norm_num
  have supportSign (v : Fock) (k : ℕ) (h : parity v = ((-1 : ℂ) ^ k) • v)
      (S : Finset ℕ) (hS : S ∈ v.support) : (-1 : ℂ) ^ S.card = (-1 : ℂ) ^ k := by
    have he := congrArg (fun w : Fock => w S) h
    simp only [parity_coefficient, Finsupp.smul_apply, smul_eq_mul] at he
    exact mul_right_cancel₀ (Finsupp.mem_support_iff.mp hS) he
  have expansion (v : Fock) : Y v = ∑ S ∈ v.support, (v S) • Y (ket S) := by
    calc
      Y v = ∑ S ∈ v.support, (v S) • wordField S.sort := by
        simp only [Y, Finsupp.lsum_apply, LinearMap.smulRight_apply,
          LinearMap.id_apply, Finsupp.sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Y_ket]
  change Local s (Y a) (Y b)
  rw [expansion a]
  apply localSum s
  intro S hS
  apply localSmul s
  apply local_symm s hs
  rw [expansion b]
  apply localSum s
  intro U hU
  apply localSmul s
  apply local_symm s hs
  have he : (-1 : ℂ) ^ (S.card * U.card) = s := by
    rw [pow_mul, supportSign a p ha S hS]
    rw [← pow_mul, Nat.mul_comm p U.card, pow_mul, supportSign b q hb U hU]
    rw [← pow_mul, Nat.mul_comm q p]
  have h := occupation_locality S U
  change Local ((-1 : ℂ) ^ (S.card * U.card)) (Y (ket S)) (Y (ket U)) at h
  rw [he] at h
  exact h

end D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
