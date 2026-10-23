/- GID: D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.claim; result=D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.result; claim=D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation.claim
   digest: A length-nine state in the (3,3,7) maximal class refutes the length bound. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation

noncomputable section

open scoped BigOperators

/- The four invariants are the kernel dimensions in Buniy–Feger–Kephart,
   arXiv:2210.07618v1, Appendix A, (A1)–(A6). Definition II.1 minimizes them
   simultaneously, and (2) defines coordinate length. The claim is the lower-bound
   half of Conjecture III.4 for dimensions at least three. -/

abbrev State (d1 d2 d3 : ℕ) :=
  (Fin d1 × Fin d2 × Fin d3) → ℂ

def flat1 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) :
    (Fin d1 → ℂ) →ₗ[ℂ] ((Fin d2 × Fin d3) → ℂ) :=
  LinearMap.pi fun (jk : Fin d2 × Fin d3) =>
    ∑ i : Fin d1,
      v (i, jk.1, jk.2) •
        (LinearMap.proj i : (Fin d1 → ℂ) →ₗ[ℂ] ℂ)

def flat2 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) :
    (Fin d2 → ℂ) →ₗ[ℂ] ((Fin d1 × Fin d3) → ℂ) :=
  LinearMap.pi fun (ik : Fin d1 × Fin d3) =>
    ∑ j : Fin d2,
      v (ik.1, j, ik.2) •
        (LinearMap.proj j : (Fin d2 → ℂ) →ₗ[ℂ] ℂ)

def flat3 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) :
    (Fin d3 → ℂ) →ₗ[ℂ] ((Fin d1 × Fin d2) → ℂ) :=
  LinearMap.pi fun (ij : Fin d1 × Fin d2) =>
    ∑ k : Fin d3,
      v (ij.1, ij.2, k) •
        (LinearMap.proj k : (Fin d3 → ℂ) →ₗ[ℂ] ℂ)

def block1 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) :
    State d1 d2 d3 →ₗ[ℂ] ((Fin d1 × Fin d1) → ℂ) :=
  LinearMap.pi fun (ab : Fin d1 × Fin d1) =>
    ∑ j : Fin d2, ∑ k : Fin d3,
      v (ab.1, j, k) •
        (LinearMap.proj (ab.2, j, k) :
          State d1 d2 d3 →ₗ[ℂ] ℂ)

def block2 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) :
    State d1 d2 d3 →ₗ[ℂ] ((Fin d2 × Fin d2) → ℂ) :=
  LinearMap.pi fun (ab : Fin d2 × Fin d2) =>
    ∑ i : Fin d1, ∑ k : Fin d3,
      v (i, ab.1, k) •
        (LinearMap.proj (i, ab.2, k) :
          State d1 d2 d3 →ₗ[ℂ] ℂ)

def block3 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) :
    State d1 d2 d3 →ₗ[ℂ] ((Fin d3 × Fin d3) → ℂ) :=
  LinearMap.pi fun (ab : Fin d3 × Fin d3) =>
    ∑ i : Fin d1, ∑ j : Fin d2,
      v (i, j, ab.1) •
        (LinearMap.proj (i, j, ab.2) :
          State d1 d2 d3 →ₗ[ℂ] ℂ)

def joint {d1 d2 d3 : ℕ} (v : State d1 d2 d3) :
    State d1 d2 d3 →ₗ[ℂ]
      (((Fin d1 × Fin d1) → ℂ) ×
        (((Fin d2 × Fin d2) → ℂ) ×
          ((Fin d3 × Fin d3) → ℂ))) :=
  (block1 v).prod ((block2 v).prod (block3 v))

def n1 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (flat1 v))

def n2 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (flat2 v))

def n3 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (flat3 v))

def n123 {d1 d2 d3 : ℕ} (v : State d1 d2 d3) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (joint v))

def InMEC {d1 d2 d3 : ℕ} (v : State d1 d2 d3) : Prop :=
  ∀ w : State d1 d2 d3,
    n1 v ≤ n1 w ∧
    n2 v ≤ n2 w ∧
    n3 v ≤ n3 w ∧
    n123 v ≤ n123 w

def coordSupport {d1 d2 d3 : ℕ} (v : State d1 d2 d3) :
    Finset (Fin d1 × Fin d2 × Fin d3) := by
  classical
  exact Finset.univ.filter (fun p => v p ≠ 0)

def length {d1 d2 d3 : ℕ} (v : State d1 d2 d3) : ℕ :=
  (coordSupport v).card

def claim : Prop :=
  ∀ (d1 d2 d3 : ℕ),
    3 ≤ d1 →
    3 ≤ d2 →
    3 ≤ d3 →
    ∀ v : State d1 d2 d3,
      InMEC v →
      d1 + d2 + d3 - 2 ≤ length v

variable {d1 d2 d3 : ℕ}

private theorem flat1_apply
    (v : State d1 d2 d3) (w : Fin d1 → ℂ)
    (j : Fin d2) (k : Fin d3) :
    flat1 v w (j, k) =
      ∑ i : Fin d1, v (i, j, k) * w i := by
  simp only [flat1.eq_1, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

private theorem flat2_apply
    (v : State d1 d2 d3) (w : Fin d2 → ℂ)
    (i : Fin d1) (k : Fin d3) :
    flat2 v w (i, k) =
      ∑ j : Fin d2, v (i, j, k) * w j := by
  simp only [flat2.eq_1, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

private theorem flat3_apply
    (v : State d1 d2 d3) (w : Fin d3 → ℂ)
    (i : Fin d1) (j : Fin d2) :
    flat3 v w (i, j) =
      ∑ k : Fin d3, v (i, j, k) * w k := by
  simp only [flat3.eq_1, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

private theorem block1_apply
    (v z : State d1 d2 d3) (a b : Fin d1) :
    block1 v z (a, b) =
      ∑ j : Fin d2, ∑ k : Fin d3,
        v (a, j, k) * z (b, j, k) := by
  simp only [block1.eq_1, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

private theorem block2_apply
    (v z : State d1 d2 d3) (a b : Fin d2) :
    block2 v z (a, b) =
      ∑ i : Fin d1, ∑ k : Fin d3,
        v (i, a, k) * z (i, b, k) := by
  simp only [block2.eq_1, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

private theorem block3_apply
    (v z : State d1 d2 d3) (a b : Fin d3) :
    block3 v z (a, b) =
      ∑ i : Fin d1, ∑ j : Fin d2,
        v (i, j, a) * z (i, j, b) := by
  simp only [block3.eq_1, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

/- The seven slices are the six off-diagonal matrix units and the identity. -/
private def supportU : Finset (Fin 3 × Fin 3 × Fin 7) :=
  {(0, 1, 0), (0, 2, 1),
   (1, 0, 2), (1, 2, 3),
   (2, 0, 4), (2, 1, 5),
   (0, 0, 6), (1, 1, 6), (2, 2, 6)}

private def u : State 3 3 7 :=
  fun p => if p ∈ supportU then 1 else 0

private theorem u_ne_zero_iff
    (p : Fin 3 × Fin 3 × Fin 7) :
    u p ≠ 0 ↔ p ∈ supportU := by
  by_cases hp : p ∈ supportU <;> simp [u.eq_1, hp]

private theorem support_u :
    coordSupport u = supportU := by
  classical
  ext p
  simp only [coordSupport.eq_1, Finset.mem_filter,
    Finset.mem_univ, true_and, u_ne_zero_iff]

private theorem card_supportU :
    supportU.card = 9 := by
  decide

private theorem length_u :
    length u = 9 := by
  change (coordSupport u).card = 9
  rw [support_u, card_supportU]

private theorem ker_flat1_u :
    LinearMap.ker (flat1 u) = ⊥ := by
  apply LinearMap.ker_eq_bot'.2
  intro w hw
  funext j
  have hj := congrFun hw (j, 6)
  fin_cases j <;>
    simpa [flat1_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using hj

private theorem ker_flat2_u :
    LinearMap.ker (flat2 u) = ⊥ := by
  apply LinearMap.ker_eq_bot'.2
  intro w hw
  funext i
  have hi := congrFun hw (i, 6)
  fin_cases i <;>
    simpa [flat2_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using hi

private theorem ker_flat3_u :
    LinearMap.ker (flat3 u) = ⊥ := by
  apply LinearMap.ker_eq_bot'.2
  intro w hw
  have h0 : w 0 = 0 := by
    simpa [flat3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hw (0, 1)
  have h1 : w 1 = 0 := by
    simpa [flat3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hw (0, 2)
  have h2 : w 2 = 0 := by
    simpa [flat3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hw (1, 0)
  have h3 : w 3 = 0 := by
    simpa [flat3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hw (1, 2)
  have h4 : w 4 = 0 := by
    simpa [flat3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hw (2, 0)
  have h5 : w 5 = 0 := by
    simpa [flat3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hw (2, 1)
  have h6 : w 6 = 0 := by
    simpa [flat3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hw (0, 0)
  funext k
  fin_cases k <;> assumption

private theorem ker_joint_u :
    LinearMap.ker (joint u) = ⊥ := by
  apply LinearMap.ker_eq_bot'.2
  intro z hz
  have hA : block1 u z = 0 := congrArg Prod.fst hz
  have hB : block2 u z = 0 := congrArg Prod.fst (congrArg Prod.snd hz)
  have hC : block3 u z = 0 := congrArg Prod.snd (congrArg Prod.snd hz)
  have A0 (b : Fin 3) :
      z (b, 0, 6) + z (b, 1, 0) + z (b, 2, 1) = 0 := by
    simpa [block1_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ, add_assoc]
      using congrFun hA (0, b)
  have A1 (b : Fin 3) :
      z (b, 0, 2) + z (b, 1, 6) + z (b, 2, 3) = 0 := by
    simpa [block1_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ, add_assoc]
      using congrFun hA (1, b)
  have A2 (b : Fin 3) :
      z (b, 0, 4) + z (b, 1, 5) + z (b, 2, 6) = 0 := by
    simpa [block1_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ, add_assoc]
      using congrFun hA (2, b)
  have B0 (b : Fin 3) :
      z (0, b, 6) + z (1, b, 2) + z (2, b, 4) = 0 := by
    simpa [block2_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ, add_assoc]
      using congrFun hB (0, b)
  have B1 (b : Fin 3) :
      z (0, b, 0) + z (1, b, 6) + z (2, b, 5) = 0 := by
    simpa [block2_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ, add_assoc]
      using congrFun hB (1, b)
  have B2 (b : Fin 3) :
      z (0, b, 1) + z (1, b, 3) + z (2, b, 6) = 0 := by
    simpa [block2_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ, add_assoc]
      using congrFun hB (2, b)
  have h01 (k : Fin 7) : z (0, 1, k) = 0 := by
    simpa [block3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hC (0, k)
  have h02 (k : Fin 7) : z (0, 2, k) = 0 := by
    simpa [block3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hC (1, k)
  have h10 (k : Fin 7) : z (1, 0, k) = 0 := by
    simpa [block3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hC (2, k)
  have h12 (k : Fin 7) : z (1, 2, k) = 0 := by
    simpa [block3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hC (3, k)
  have h20 (k : Fin 7) : z (2, 0, k) = 0 := by
    simpa [block3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hC (4, k)
  have h21 (k : Fin 7) : z (2, 1, k) = 0 := by
    simpa [block3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ] using congrFun hC (5, k)
  have htr (k : Fin 7) : z (0, 0, k) + z (1, 1, k) + z (2, 2, k) = 0 := by
    simpa [block3_apply, u.eq_1, supportU.eq_1, Fin.sum_univ_succ, add_assoc]
      using congrFun hC (6, k)
  -- Two diagonal coordinates in each of slices 0–5 follow from the first two blocks.
  have d110 : z (1, 1, 0) = 0 := by
    simpa only [h10, h12, zero_add, add_zero] using A0 1
  have d000 : z (0, 0, 0) = 0 := by
    simpa only [h10, h20, add_zero] using B1 0
  have d221 : z (2, 2, 1) = 0 := by
    simpa only [h20, h21, zero_add] using A0 2
  have d001 : z (0, 0, 1) = 0 := by
    simpa only [h10, h20, add_zero] using B2 0
  have d002 : z (0, 0, 2) = 0 := by
    simpa only [h01, h02, add_zero] using A1 0
  have d112 : z (1, 1, 2) = 0 := by
    simpa only [h01, h21, zero_add, add_zero] using B0 1
  have d223 : z (2, 2, 3) = 0 := by
    simpa only [h20, h21, zero_add] using A1 2
  have d113 : z (1, 1, 3) = 0 := by
    simpa only [h01, h21, zero_add, add_zero] using B2 1
  have d004 : z (0, 0, 4) = 0 := by
    simpa only [h01, h02, add_zero] using A2 0
  have d224 : z (2, 2, 4) = 0 := by
    simpa only [h02, h12, zero_add] using B0 2
  have d115 : z (1, 1, 5) = 0 := by
    simpa only [h10, h12, zero_add, add_zero] using A2 1
  have d225 : z (2, 2, 5) = 0 := by
    simpa only [h02, h12, zero_add] using B1 2
  -- The trace row supplies the third diagonal coordinate in those slices.
  have d220 : z (2, 2, 0) = 0 := by
    simpa only [d000, d110, zero_add] using htr 0
  have d111 : z (1, 1, 1) = 0 := by
    simpa only [d001, d221, zero_add, add_zero] using htr 1
  have d222 : z (2, 2, 2) = 0 := by
    simpa only [d002, d112, zero_add] using htr 2
  have d003 : z (0, 0, 3) = 0 := by
    simpa only [d113, d223, add_zero] using htr 3
  have d114 : z (1, 1, 4) = 0 := by
    simpa only [d004, d224, zero_add, add_zero] using htr 4
  have d005 : z (0, 0, 5) = 0 := by
    simpa only [d115, d225, add_zero] using htr 5
  -- The diagonal rows of the first block kill slice 6.
  have d006 : z (0, 0, 6) = 0 := by
    simpa only [h01, h02, add_zero] using A0 0
  have d116 : z (1, 1, 6) = 0 := by
    simpa only [h10, h12, zero_add, add_zero] using A1 1
  have d226 : z (2, 2, 6) = 0 := by
    simpa only [h20, h21, zero_add] using A2 2
  funext p
  rcases p with ⟨i, j, k⟩
  fin_cases i <;> fin_cases j
  · fin_cases k <;> assumption
  · exact h01 k
  · exact h02 k
  · exact h10 k
  · fin_cases k <;> assumption
  · exact h12 k
  · exact h20 k
  · exact h21 k
  · fin_cases k <;> assumption

private theorem n1_u : n1 u = 0 := by
  unfold n1
  rw [ker_flat1_u]
  exact finrank_bot ℂ (Fin 3 → ℂ)

private theorem n2_u : n2 u = 0 := by
  unfold n2
  rw [ker_flat2_u]
  exact finrank_bot ℂ (Fin 3 → ℂ)

private theorem n3_u : n3 u = 0 := by
  unfold n3
  rw [ker_flat3_u]
  exact finrank_bot ℂ (Fin 7 → ℂ)

private theorem n123_u : n123 u = 0 := by
  unfold n123
  rw [ker_joint_u]
  exact finrank_bot ℂ (State 3 3 7)

private theorem u_mem : InMEC u := by
  intro w
  rw [n1_u, n2_u, n3_u, n123_u]
  exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem result : ¬ claim := by
  intro h
  have hb := h 3 3 7 (by norm_num) (by norm_num) (by norm_num) u u_mem
  rw [length_u] at hb
  norm_num at hb

end

end D5.S3.Quantum.Entanglement.TripartiteMaximalClassLengthRefutation
