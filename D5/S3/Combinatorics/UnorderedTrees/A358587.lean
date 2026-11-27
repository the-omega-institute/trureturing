/- GID: D5/S3/Combinatorics/UnorderedTrees/A358587
   generality: I
   mirror-B: D5/B/S3/Combinatorics/UnorderedTrees/A358587
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown]
   utility: none
   digest: Wu's generating function and recurrence for actual unordered rooted trees. -/

/-
admission_basis: open-problem-resolution (#34765; Proved)
result: proof_shape: content; escape_witness: actual_series;
  consumers: none (designated external open-problem settlement).
The exact result packages the actual quotient count, the integer-valued formal
series identity, the initial values and the cutoff recurrence. Its live proof
path consumes ForkDecoration.classification and ForkCount.count_by_arms.
The supporting declarations are retained only when they have live consumers.
Frozen dependencies through ParentTree (module pins):
  D5/S1/FixedPoints/TransientTrees/RootedVertexClassification
    sha256:fe0cf20f4d330be5a426aed58fdb71099864005cd6afbf79b2620c7cf3f8994a
  D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction
    sha256:f075c0c20434bf2e3cfe8d2d7ac8165cc7621f3195c96c0585c0c320e3e704db
  D5/S1/FixedPoints/RootedTransientTreeClassification
    sha256:1c160de8c440839266be52882a6259fe4fced39bb165ba7b753494b0c6302a85
Pinned Mathlib supplies the remaining algebraic and finite-cardinality facts.
Per-declaration proof shape and live consumers are recorded in the handoff.
Escape audit remains unfinished under the external open-problem-resolution route.
-/

import D5.S3.Combinatorics.UnorderedTrees.ForkCount
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Chai Wah Wu's generating function and recurrence for OEIS A358587. -/

namespace D5.S3.Combinatorics.UnorderedTrees.A358587

open ParentTree ForkCount PowerSeries
open scoped PowerSeries BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def G : ℤ⟦X⟧ := mk 1
private def U : ℤ⟦X⟧ := X * G
private def S : ℤ⟦X⟧ := G.subst U
private def H : ℤ⟦X⟧ := G.subst (X ^ 2)
private def E : ℤ⟦X⟧ := X ^ 5 * G ^ 2 * S * H
private def Q : ℤ⟦X⟧ := X ^ 6 * G ^ 4 * (G ^ 2).subst U

private theorem hasU : HasSubst U :=
  .of_constantCoeff_zero' (by simp [U])

private theorem hasX2 : HasSubst (X ^ 2 : ℤ⟦X⟧) := .X_pow (by decide)

private theorem geometric_inverse : (1 - X) * G = 1 := by
  rw [mul_comm]
  exact mk_one_mul_one_sub_eq_one ℤ

private theorem rational_identity :
    ((X - 1) ^ 2 * (X + 1) * (2 * X - 1) ^ 2) * (E + Q) =
      X ^ 5 * (X ^ 2 - X + 1) := by
  have hS : (1 - U) * S = 1 := by
    have h := congrArg (substAlgHom (R := ℤ) hasU) geometric_inverse
    simpa only [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom, S] using h
  have hH : (1 - X ^ 2) * H = 1 := by
    have h := congrArg (substAlgHom (R := ℤ) hasX2) geometric_inverse
    simpa only [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom, H] using h
  have hQ : (G ^ 2).subst U = S ^ 2 := by
    simpa only [coe_substAlgHom, S] using map_pow (substAlgHom (R := ℤ) hasU) G 2
  have hU : (1 - 2 * X) * G = 1 - U := by
    unfold U
    linear_combination geometric_inverse
  have hGS : (1 - 2 * X) * G * S = 1 := by rw [hU, hS]
  have e : ((1 - X)^2 * (1 + X) * (1 - 2 * X)) * E = X^5 := by
    calc
      _ = X^5 * ((1 - X) * G) * ((1 - 2 * X) * G * S) * ((1 - X^2) * H) := by
        unfold E
        ring
      _ = _ := by rw [geometric_inverse, hGS, hH]; simp
  have q : ((1 - X)^2 * (1 - 2 * X)^2) * Q = X^6 := by
    calc
      _ = X^6 * ((1 - X) * G)^2 * ((1 - 2 * X) * G * S)^2 := by
        rw [Q, hQ]
        ring
      _ = _ := by rw [geometric_inverse, hGS]; simp
  calc
    _ = (1 - 2*X) * (((1 - X)^2 * (1 + X) * (1 - 2*X)) * E) +
        (1 + X) * (((1 - X)^2 * (1 - 2*X)^2) * Q) := by ring
    _ = _ := by rw [e, q]; ring

private theorem coeff_trunc_subst (f z : ℤ⟦X⟧) (s j n : ℕ)
    (hs : 0 < s) (hn : j ≤ n) (h : HasSubst (X ^ s * z)) :
    coeff j (f.subst (X ^ s * z)) =
      coeff j (∑ k ∈ Finset.range (n + 1), C (coeff k f) * (X ^ s * z) ^ k) := by
  classical
  rw [coeff_subst' h]
  simp only [smul_eq_mul, map_sum, coeff_C_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra! hkn
  have hjk : ¬ s * k ≤ j := by
    have hle : k ≤ s * k := by
      simpa only [one_mul] using Nat.mul_le_mul_right k (show 1 ≤ s from hs)
    omega
  simp [Function.mem_support, mul_pow, ← pow_mul, coeff_X_pow_mul', hjk] at hk

private theorem coeff_mul_congr {f g f' g' : ℤ⟦X⟧} (n : ℕ)
    (hf : ∀ j ≤ n, coeff j f = coeff j f') (hg : ∀ j ≤ n, coeff j g = coeff j g') :
    coeff n (f * g) = coeff n (f' * g') := by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have h := Finset.mem_antidiagonal.mp hp
  rw [hf _ (by omega), hg _ (by omega)]

private theorem coeff_S_trunc (j n : ℕ) (h : j ≤ n) :
    coeff j S = coeff j (∑ b ∈ Finset.range (n + 1), U ^ b) := by
  simpa [S, U, G] using coeff_trunc_subst G G 1 j n (by decide) h
    (show HasSubst (X ^ 1 * G) by simpa [U] using hasU)

private theorem coeff_H_trunc (j n : ℕ) (h : j ≤ n) :
    coeff j H = coeff j (∑ m ∈ Finset.range (n + 1), (X ^ 2 : ℤ⟦X⟧) ^ m) := by
  simpa [H, G] using coeff_trunc_subst G 1 2 j n (by decide) h
    (show HasSubst (X ^ 2 * (1 : ℤ⟦X⟧)) by simpa using hasX2)

private theorem coeff_E_term (n b m : ℕ) :
    coeff n ((X ^ 5 * G ^ 2 * U ^ b) * (X ^ 2) ^ m) =
      if b + 5 + 2 * m ≤ n then ((n - 4 - 2*m).choose (b + 1) : ℤ) else 0 := by
  have hterm : (X ^ 5 * G ^ 2 * U ^ b) * (X ^ 2) ^ m =
      X ^ (b + 5 + 2*m) * G ^ ((b + 1) + 1) := by
    unfold U
    rw [mul_pow, ← pow_mul, pow_add, pow_add, pow_add, pow_add]
    ring
  rw [hterm, coeff_X_pow_mul']
  have hG := mk_one_pow_eq_mk_choose_add ℤ (b + 1)
  change G ^ (b + 1 + 1) = _ at hG
  rw [hG]
  by_cases h : b + 5 + 2 * m ≤ n
  · simp only [h, ite_true, coeff_mk]
    rw [show b + 1 + (n - (b + 5 + 2*m)) = n - 4 - 2*m by omega]
  · simp [h]

private theorem coeff_E (n : ℕ) :
    coeff n E = ∑ m ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - (4 + 2 * m)),
      ((n - 4 - 2*m).choose (b + 1) : ℤ) := by
  have h : coeff n E = coeff n ((X ^ 5 * G ^ 2 * (∑ b ∈ Finset.range (n + 1), U ^ b)) *
      (∑ m ∈ Finset.range (n + 1), (X ^ 2) ^ m)) := by
    unfold E
    apply coeff_mul_congr
    · intro j hj
      exact coeff_mul_congr j (fun _ _ => rfl)
        (fun k hk => coeff_S_trunc k n (hk.trans hj))
    · exact fun j hj => coeff_H_trunc j n hj
  rw [h]
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
  simp only [coeff_E_term]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_subset
    (s₁ := Finset.range (n - (4 + 2 * m))) (s₂ := Finset.range (n + 1))
    (Finset.range_mono (by omega))]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [ite_eq_left (by have h := Finset.mem_range.mp hb; omega)]
  · intro b _ hb
    rw [ite_eq_right (by have h := Finset.mem_range.not.mp hb; omega)]

private theorem coeff_G2 (v : ℕ) : coeff v (G ^ 2) = (v : ℤ) + 1 := by
  have h := mk_one_pow_eq_mk_choose_add ℤ 1
  change G ^ 2 = _ at h
  rw [h, coeff_mk, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  ring

private theorem coeff_Q_term (n v : ℕ) :
    coeff n ((X ^ 6 * G ^ 4) * (C ((v : ℤ) + 1) * U ^ v)) =
      if v + 6 ≤ n then ((v : ℤ) + 1) * ((n - 3).choose (v + 3) : ℤ) else 0 := by
  have hterm : (X ^ 6 * G ^ 4) * (C ((v : ℤ) + 1) * U ^ v) =
      C ((v : ℤ) + 1) * (X ^ (v + 6) * G ^ ((v + 3) + 1)) := by
    unfold U
    rw [mul_pow, pow_add, pow_add, pow_add]
    ring
  rw [hterm, coeff_C_mul, coeff_X_pow_mul']
  have hG := mk_one_pow_eq_mk_choose_add ℤ (v + 3)
  change G ^ (v + 3 + 1) = _ at hG
  rw [hG]
  by_cases h : v + 6 ≤ n
  · simp only [h, ite_true, coeff_mk]
    rw [show v + 3 + (n - (v + 6)) = n - 3 by omega]
  · simp [h]

private theorem coeff_Q (n : ℕ) :
    coeff n Q = ∑ v ∈ Finset.range (n - 5),
      ((v : ℤ) + 1) * ((n - 3).choose (v + 3) : ℤ) := by
  have h : coeff n Q = coeff n ((X ^ 6 * G ^ 4) *
      (∑ v ∈ Finset.range (n + 1), C ((v : ℤ) + 1) * U ^ v)) := by
    unfold Q
    apply coeff_mul_congr n (fun _ _ => rfl)
    intro j hj
    have ht := coeff_trunc_subst (G ^ 2) G 1 j n (by decide) hj
      (show HasSubst (X ^ 1 * G) by simpa [U] using hasU)
    simp only [pow_one] at ht
    change coeff j ((G ^ 2).subst (X * G)) = _
    rw [ht]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    rw [coeff_G2, U]
  rw [h, Finset.mul_sum, map_sum]
  simp only [coeff_Q_term]
  rw [← Finset.sum_subset
    (s₁ := Finset.range (n - 5)) (s₂ := Finset.range (n + 1)) (Finset.range_mono (by omega))]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [ite_eq_left (by have hv' := Finset.mem_range.mp hv; omega)]
  · intro v _ hv
    rw [ite_eq_right (by have hv' := Finset.mem_range.not.mp hv; omega)]

private theorem actual_series : mk (fun n ↦ (a n : ℤ)) = E + Q := by
  ext n
  rw [coeff_mk, map_add, coeff_E, coeff_Q, count_by_arms]
  push_cast
  rfl

private theorem actual_rational :
    ((X - 1)^2 * (X + 1) * (2*X - 1)^2) * mk (fun n ↦ (a n : ℤ)) =
      X^5 * (X^2 - X + 1) := by
  rw [actual_series, rational_identity]

private theorem initial :
    a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 0 ∧
      a 5 = 1 ∧ a 6 = 4 ∧ a 7 = 14 := by
  simp only [count_by_arms]
  decide

private theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 7 * a (n - 2) - a (n - 3) +
      8 * a (n - 4) - 4 * a (n - 5) := by
  let A : ℤ⟦X⟧ := mk (fun k ↦ (a k : ℤ))
  have he : ((X - 1)^2 * (X + 1) * (2*X - 1)^2) * A =
      A - C (5 : ℤ) * (X^1 * A) + C (7 : ℤ) * (X^2 * A) + X^3 * A -
        C (8 : ℤ) * (X^4 * A) + C (4 : ℤ) * (X^5 * A) := by
    simp only [map_ofNat]
    ring
  have hi : X^5 * (X^2 - X + 1 : ℤ⟦X⟧) = X^7 - X^6 + X^5 := by ring
  have h := congrArg (coeff n) (show _ * A = _ from actual_rational)
  rw [he, hi] at h
  simp only [map_sub, map_add, coeff_X_pow, coeff_C_mul, coeff_X_pow_mul', A, coeff_mk,
    show ¬ n = 5 by omega, show ¬ n = 6 by omega, show ¬ n = 7 by omega,
    show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, ite_true, ite_false] at h
  linear_combination h

private theorem actual_quotient :
    mk (fun n ↦ (a n : ℤ)) =
      X^5 * (X^2 - X + 1) * invOfUnit ((X - 1)^2 * (X + 1) * (2*X - 1)^2) 1 := by
  let D : ℤ⟦X⟧ := (X - 1)^2 * (X + 1) * (2*X - 1)^2
  have hD : D.constantCoeff = ↑(1 : ℤˣ) := by simp [D]
  have hI := invOfUnit_mul D (1 : ℤˣ) hD
  calc
    _ = (invOfUnit D 1 * D) * mk (fun n ↦ (a n : ℤ)) := by rw [hI, one_mul]
    _ = invOfUnit D 1 * (D * mk (fun n ↦ (a n : ℤ))) := by rw [mul_assoc]
    _ = _ := by
      rw [show D * mk (fun n ↦ (a n : ℤ)) = _ from actual_rational]
      exact mul_comm _ _

/-- Wu's entire A358587 formula block for the count of actual unordered rooted trees. -/
theorem result (n : ℕ) :
    (Set.Finite {T : TreeClass n | classHeight T = classInternalCount T} ∧
      a n = Set.ncard {T : TreeClass n | classHeight T = classInternalCount T}) ∧
    a 0 = 0 ∧
    mk (fun k ↦ (a k : ℤ)) =
      X^5 * (X^2 - X + 1) * invOfUnit ((X - 1)^2 * (X + 1) * (2*X - 1)^2) 1 ∧
    (a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 0 ∧ a 5 = 1 ∧ a 6 = 4 ∧ a 7 = 14) ∧
    (7 < n →
      (a n : ℤ) = 5 * a (n - 1) - 7 * a (n - 2) - a (n - 3) +
        8 * a (n - 4) - 4 * a (n - 5)) := by
  refine ⟨⟨Set.toFinite _, ?_⟩, initial.1, actual_quotient, initial.2, recurrence n⟩
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rfl

#print axioms result

end

end D5.S3.Combinatorics.UnorderedTrees.A358587
