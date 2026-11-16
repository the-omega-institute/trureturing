/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Ambient eigenvectors and direction counts for balanced critical cube subgraphs. -/

import D5.S3.Combinatorics.Graph.HypercubeSubQuorum
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Batteries.Tactic.OpenPrivate

/-! The spectral bridge uses Huang's existing signing, with TRUE in its first block.
It derives ambient eigenvectors and counts actual selected edges in each cube direction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

open scoped BigOperators Classical
open D5.S3.Combinatorics.Graph.Hypercube
open private huangMatrix huangMatrix_symmetric huang_energy from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

abbrev Q (n : Nat) := Sensitivity.Q n

/-- Toggle the actual cube coordinate `i`. -/
def flip {n : Nat} (x : Q n) (i : Fin n) : Q n := Function.update x i (!x i)

@[simp] theorem flip_apply_same {n : Nat} (x : Q n) (i : Fin n) :
    flip x i i = !x i := by simp [flip]

@[simp] theorem flip_flip {n : Nat} (x : Q n) (i : Fin n) :
    flip (flip x i) i = x := by
  funext j
  by_cases h : j = i <;> simp [flip, h]

private theorem flip_head_zero {n : Nat} (x : Q (n + 1)) :
    flip x 0 0 = !x 0 := flip_apply_same x 0

private theorem flip_tail_zero {n : Nat} (x : Q (n + 1)) :
    Sensitivity.π (flip x 0) = Sensitivity.π x := by
  funext j
  simp [Sensitivity.π, flip]

private theorem flip_head_succ {n : Nat} (x : Q (n + 1)) (i : Fin n) :
    flip x i.succ 0 = x 0 := by
  exact Function.update_of_ne (Fin.succ_ne_zero i).symm _ _

private theorem flip_tail_succ {n : Nat} (x : Q (n + 1)) (i : Fin n) :
    Sensitivity.π (flip x i.succ) = flip (Sensitivity.π x) i := by
  funext j
  by_cases h : j = i <;> simp [Sensitivity.π, flip, h]

private def coeff (n : Nat) : Sensitivity.V n ≃ₗ[Real] (Q n → Real) :=
  (Sensitivity.dualBases_e_ε n).basis.equivFun

private theorem coeff_apply (n : Nat) (v : Sensitivity.V n) (x : Q n) :
    coeff n v x = Sensitivity.ε x v := by
  change (Sensitivity.dualBases_e_ε n).basis.equivFun v x = _
  rw [Module.Basis.equivFun_apply]
  exact (Sensitivity.dualBases_e_ε n).coeffs_apply v x

private theorem coeff_symm_apply (n : Nat) (z : Q n → Real) :
    (coeff n).symm z = ∑ x, z x • Sensitivity.e x := by
  simp [coeff, Module.Basis.equivFun_symm_apply, Module.DualBases.coe_basis]

private theorem matrix_coeff (n : Nat) (z : Q n → Real) :
    (huangMatrix n).mulVec z = coeff n (Sensitivity.f n ((coeff n).symm z)) := by
  ext x
  rw [coeff_apply, coeff_symm_apply]
  simp [Matrix.mulVec, dotProduct, huangMatrix, map_sum, mul_comm]

private def gammaV : (n : Nat) → Fin n → Sensitivity.V n →ₗ[Real] Sensitivity.V n
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases
      ((LinearMap.snd Real (Sensitivity.V n) (Sensitivity.V n)).prod
        (LinearMap.fst Real (Sensitivity.V n) (Sensitivity.V n)))
      (fun j => ((gammaV n j).comp (LinearMap.fst Real _ _)).prod
        ((-gammaV n j).comp (LinearMap.snd Real _ _))) i

private theorem gammaV_zero (n : Nat) (v : Sensitivity.V (n + 1)) :
    gammaV (n + 1) 0 v = (v.2, v.1) := rfl

private theorem gammaV_succ (n : Nat) (i : Fin n) (v : Sensitivity.V (n + 1)) :
    gammaV (n + 1) i.succ v = (gammaV n i v.1, -gammaV n i v.2) := rfl

private theorem anticommutatorV (n : Nat) (i : Fin n) (v : Sensitivity.V n) :
    Sensitivity.f n (gammaV n i v) + gammaV n i (Sensitivity.f n v) =
      (2 : Real) • v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          rw [gammaV_zero, Sensitivity.f_succ_apply, gammaV_zero,
            Sensitivity.f_succ_apply]
          apply Prod.ext <;> simp [two_smul] <;> abel
      | succ i =>
          have ha := ih i v.1
          have hb := ih i v.2
          rw [gammaV_succ, Sensitivity.f_succ_apply, gammaV_succ,
            Sensitivity.f_succ_apply]
          apply Prod.ext
          · simpa [map_add,
              two_smul, add_assoc, add_left_comm, add_comm] using ha
          · simpa [map_sub,
              two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hb

private theorem matrix_flip_zero {n : Nat} (x : Q (n + 1)) :
    huangMatrix (n + 1) x (flip x 0) = 1 := by
  simp only [huangMatrix, Sensitivity.e, Sensitivity.ε, Sensitivity.f_succ_apply,
    flip_head_zero, flip_tail_zero]
  cases x 0 <;> simp [Sensitivity.duality]

private theorem matrix_flip_succ {n : Nat} (x : Q (n + 1)) (i : Fin n) :
    huangMatrix (n + 1) x (flip x i.succ) =
      (if x 0 then 1 else -1) * huangMatrix n (Sensitivity.π x)
        (flip (Sensitivity.π x) i) := by
  simp only [huangMatrix, Sensitivity.e, Sensitivity.ε, Sensitivity.f_succ_apply,
    flip_head_succ, flip_tail_succ]
  cases x 0 <;> simp

private theorem epsilon_gammaV (n : Nat) (i : Fin n) (v : Sensitivity.V n) (x : Q n) :
    Sensitivity.ε x (gammaV n i v) =
      huangMatrix n x (flip x i) * Sensitivity.ε (flip x i) v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          rw [matrix_flip_zero, one_mul, gammaV_zero]
          simp only [Sensitivity.ε, flip_head_zero, flip_tail_zero]
          cases x 0 <;> simp
      | succ i =>
          rw [matrix_flip_succ, gammaV_succ]
          simp only [Sensitivity.ε, flip_head_succ, flip_tail_succ]
          cases x 0 <;> simp [ih]

/-- The signed adjacency operator in a single actual cube direction. -/
def gamma {n : Nat} (i : Fin n) : (Q n → Real) →ₗ[Real] (Q n → Real) :=
  (coeff n).toLinearMap.comp ((gammaV n i).comp (coeff n).symm.toLinearMap)

/-- The direction operator uses exactly the coefficients of the existing Huang matrix. -/
theorem gamma_apply {n : Nat} (i : Fin n) (z : Q n → Real) (x : Q n) :
    gamma i z x = huangMatrix n x (flip x i) * z (flip x i) := by
  change coeff n (gammaV n i ((coeff n).symm z)) x = _
  rw [coeff_apply, epsilon_gammaV, ← coeff_apply]
  simp

/-- The ambient Huang operator anticommutes with each direction up to twice the identity. -/
theorem anticommutator {n : Nat} (i : Fin n) (z : Q n → Real) :
    (huangMatrix n).mulVec (gamma i z) + gamma i ((huangMatrix n).mulVec z) =
      (2 : Real) • z := by
  rw [matrix_coeff, matrix_coeff]
  change coeff n (Sensitivity.f n ((coeff n).symm
      (coeff n (gammaV n i ((coeff n).symm z))))) +
      coeff n (gammaV n i ((coeff n).symm
        (coeff n (Sensitivity.f n ((coeff n).symm z))))) = _
  rw [(coeff n).symm_apply_apply, (coeff n).symm_apply_apply, ← map_add,
    anticommutatorV, map_smul, (coeff n).apply_symm_apply]

/-- Switching balance in the coefficients of Huang's fixed matrix.
TRUE selects the first recursive block, so these are the FALSE-prefix signs. -/
def IsSwitching {n : Nat} (C : Finset (Q n)) (sigma : Q n → Real) : Prop :=
  (∀ x ∈ C, sigma x = 1 ∨ sigma x = -1) ∧
    ∀ x ∈ C, ∀ y ∈ C, (hypercube n).Adj x y →
      huangMatrix n x y = sigma x * sigma y

/-- Balance asks for a switching function on the selected vertices. -/
def IsBalanced {n : Nat} (C : Finset (Q n)) : Prop :=
  ∃ sigma : Q n → Real, IsSwitching C sigma

/-- Extend the switching function by zero to the full cube. -/
def switchingVector {n : Nat} (C : Finset (Q n)) (sigma : Q n → Real) : Q n → Real :=
  fun x => if x ∈ C then sigma x else 0

private theorem switching_sq {n : Nat} {C : Finset (Q n)} {sigma : Q n → Real}
    (hs : IsSwitching C sigma) {x : Q n} (hx : x ∈ C) : sigma x ^ 2 = 1 := by
  rcases hs.1 x hx with h | h <;> rw [h] <;> norm_num

private theorem adjacent_iff {n : Nat} (x y : Q n) :
    y ∈ Sensitivity.Q.adjacent x ↔ (hypercube n).Adj x y := by
  change (∃! i, x i ≠ y i) ↔ (Finset.univ.filter (fun i => x i ≠ y i)).card = 1
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨i, hi, hunique⟩
    refine ⟨i, Finset.ext fun j => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hunique j, fun h => h ▸ hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, ?_⟩
    · have := Finset.ext_iff.mp hi i
      simpa using this.symm
    · intro j hj
      have := Finset.ext_iff.mp hi j
      simpa [hj] using this

private theorem matrix_support {n : Nat} (x y : Q n) :
    |huangMatrix n x y| = if (hypercube n).Adj x y then 1 else 0 := by
  change |Sensitivity.ε x (Sensitivity.f n (Sensitivity.e y))| = _
  rw [Sensitivity.f_matrix, adjacent_iff]

/-- Toggling one coordinate traverses an edge of the actual Hamming cube. -/
theorem flip_adj {n : Nat} (x : Q n) (i : Fin n) :
    (hypercube n).Adj x (flip x i) := by
  apply (adjacent_iff x (flip x i)).mp
  refine ⟨i, ?_, ?_⟩
  · simp [flip]
  · intro j hj
    by_contra hji
    exact hj (by simp [flip, hji])

private theorem switching_norm {n : Nat} {C : Finset (Q n)} {sigma : Q n → Real}
    (hs : IsSwitching C sigma) :
    ∑ x, (switchingVector C sigma x) ^ 2 = (C.card : Real) := by
  calc
    ∑ x, (switchingVector C sigma x) ^ 2 =
        ∑ x ∈ C, (switchingVector C sigma x) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro x _ hx
      simp [switchingVector, hx]
    _ = ∑ _x ∈ C, (1 : Real) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa [switchingVector, hx] using switching_sq hs hx
    _ = (C.card : Real) := by simp

private theorem inside_equation {n d : Nat} (C : Finset (Q n)) (sigma : Q n → Real)
    (hr : ((hypercube n).induce (C : Set (Q n))).IsRegularOfDegree d)
    (hs : IsSwitching C sigma) {x : Q n} (hx : x ∈ C) :
    (huangMatrix n).mulVec (switchingVector C sigma) x =
      (d : Real) * switchingVector C sigma x := by
  let N := (hypercube n).neighborFinset x ∩ C
  have hcard : N.card = d := by
    calc
      N.card = (((hypercube n).induce (C : Set (Q n))).neighborFinset
          ⟨x, hx⟩).card := by
        have himage : ((((hypercube n).induce (C : Set (Q n))).neighborFinset
            ⟨x, hx⟩).image (fun y => y.1)) = N := by
          ext y
          simp [N, SimpleGraph.mem_neighborFinset, and_comm]
          change (∃ (_ : y ∈ C), (hypercube n).Adj x y) ↔ _
          simp [and_comm]
        rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
      _ = d := by rw [SimpleGraph.card_neighborFinset_eq_degree, hr.degree_eq]
  have hsum : (huangMatrix n).mulVec (switchingVector C sigma) x =
      ∑ y ∈ N, huangMatrix n x y * switchingVector C sigma y := by
    rw [Matrix.mulVec, dotProduct]
    symm
    apply Finset.sum_subset (Finset.subset_univ N)
    intro y _ hy
    by_cases hyC : y ∈ C
    · have hnadj : ¬ (hypercube n).Adj x y := by
        intro hadj
        exact hy (by simp [N, SimpleGraph.mem_neighborFinset, hadj, hyC])
      have hz : huangMatrix n x y = 0 := by
        have h := matrix_support x y
        rw [ite_eq_right hnadj] at h
        exact abs_eq_zero.mp h
      simp [hz]
    · simp [switchingVector, hyC]
  rw [hsum]
  calc
    ∑ y ∈ N, huangMatrix n x y * switchingVector C sigma y =
        ∑ _y ∈ N, sigma x := by
      apply Finset.sum_congr rfl
      intro y hy
      have hy' : (hypercube n).Adj x y ∧ y ∈ C := by
        simpa [N, SimpleGraph.mem_neighborFinset] using hy
      rw [hs.2 x hx y hy'.2 hy'.1]
      simp only [switchingVector, ite_eq_left hy'.2]
      have hy2 := switching_sq hs hy'.2
      rw [mul_assoc, ← pow_two, hy2, mul_one]
    _ = (d : Real) * switchingVector C sigma x := by
      simp [hcard, switchingVector, hx]

/-- Critical regularity and switching balance force the full ambient eigen-equation.
The vanishing outside `C` follows from Huang's energy identity. -/
theorem ambient_eigenvector {d : Nat} (C : Finset (Q (d * d)))
    (sigma : Q (d * d) → Real)
    (hr : ((hypercube (d * d)).induce (C : Set (Q (d * d)))).IsRegularOfDegree d)
    (hs : IsSwitching C sigma) :
    (huangMatrix (d * d)).mulVec (switchingVector C sigma) =
      (d : Real) • switchingVector C sigma := by
  let z := switchingVector C sigma
  have hin (x : Q (d * d)) (hx : x ∈ C) :
      (huangMatrix (d * d)).mulVec z x = (d : Real) * z x :=
    inside_equation C sigma hr hs hx
  have hnorm : ∑ x, z x ^ 2 = (C.card : Real) := switching_norm hs
  have hinside : ∑ x ∈ C, ((huangMatrix (d * d)).mulVec z x) ^ 2 =
      (d : Real) ^ 2 * C.card := by
    calc
      ∑ x ∈ C, ((huangMatrix (d * d)).mulVec z x) ^ 2 =
          ∑ _x ∈ C, (d : Real) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hin x hx, mul_pow]
        have hx2 : z x ^ 2 = 1 := by
          simpa [z, switchingVector, hx] using switching_sq hs hx
        rw [hx2, mul_one]
      _ = _ := by simp [mul_comm]
  have henergy := huang_energy (d * d) z
  have hsplit : ∑ x, ((huangMatrix (d * d)).mulVec z x) ^ 2 =
      (∑ x ∈ C, ((huangMatrix (d * d)).mulVec z x) ^ 2) +
        ∑ x ∈ Finset.univ \ C, ((huangMatrix (d * d)).mulVec z x) ^ 2 := by
    simpa using (Finset.sum_sdiff (s₁ := C) (s₂ := Finset.univ)
      (Finset.subset_univ C)
      (fun x => ((huangMatrix (d * d)).mulVec z x) ^ 2)).symm
  have hout : ∑ x ∈ Finset.univ \ C,
      ((huangMatrix (d * d)).mulVec z x) ^ 2 = 0 := by
    rw [hsplit, hinside, hnorm] at henergy
    push_cast at henergy
    nlinarith
  ext x
  by_cases hx : x ∈ C
  · exact hin x hx
  · have hx2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun x (_ : x ∈ Finset.univ \ C) =>
          sq_nonneg ((huangMatrix (d * d)).mulVec z x))).mp hout x (by simp [hx])
    have hz : z x = 0 := by simp [z, switchingVector, hx]
    change (huangMatrix (d * d)).mulVec z x = (d : Real) * z x
    rw [hz, mul_zero]
    exact sq_eq_zero_iff.mp hx2

/-- Selected endpoints of edges in direction `i`, counting both endpoints. -/
def directionEndpoints {n : Nat} (C : Finset (Q n)) (i : Fin n) : Finset (Q n) :=
  C.filter (fun x => flip x i ∈ C)

/-- Selected edges in direction `i`, each counted at its FALSE endpoint. -/
def directionEdges {n : Nat} (C : Finset (Q n)) (i : Fin n) : Nat :=
  (C.filter (fun x => x i = false ∧ flip x i ∈ C)).card

private theorem switching_dot_gamma {n : Nat} {C : Finset (Q n)}
    {sigma : Q n → Real} (hs : IsSwitching C sigma) (i : Fin n) :
    switchingVector C sigma ⬝ᵥ gamma i (switchingVector C sigma) =
      ((directionEndpoints C i).card : Real) := by
  have hpoint (x : Q n) :
      switchingVector C sigma x * gamma i (switchingVector C sigma) x =
        if x ∈ directionEndpoints C i then 1 else 0 := by
    rw [gamma_apply]
    by_cases hx : x ∈ C
    · by_cases hf : flip x i ∈ C
      · simp only [switchingVector, ite_eq_left hx, ite_eq_left hf]
        rw [hs.2 x hx (flip x i) hf (flip_adj x i)]
        have hmem : x ∈ directionEndpoints C i := by simp [directionEndpoints, hx, hf]
        rw [ite_eq_left hmem]
        calc
          sigma x * (sigma x * sigma (flip x i) * sigma (flip x i)) =
              sigma x ^ 2 * sigma (flip x i) ^ 2 := by ring
          _ = 1 := by rw [switching_sq hs hx, switching_sq hs hf]; norm_num
      · simp [switchingVector, hx, hf, directionEndpoints]
    · simp [switchingVector, hx, directionEndpoints]
  simp only [dotProduct, hpoint]
  simp

private theorem endpoint_card_twice {n : Nat} (C : Finset (Q n)) (i : Fin n) :
    (directionEndpoints C i).card = 2 * directionEdges C i := by
  let F := C.filter (fun x => x i = false ∧ flip x i ∈ C)
  let T := C.filter (fun x => x i = true ∧ flip x i ∈ C)
  have hFT : F.card = T.card := by
    apply Finset.card_bij (fun x _ => flip x i)
    · intro x hx
      simp only [F, Finset.mem_filter] at hx
      simp [T, hx.1, hx.2.1, hx.2.2]
    · intro x _ y _ hxy
      have := congrArg (fun x => flip x i) hxy
      simpa using this
    · intro y hy
      simp only [T, Finset.mem_filter] at hy
      refine ⟨flip y i, ?_, by simp⟩
      simp [F, hy.1, hy.2.1, hy.2.2]
  have hunion : directionEndpoints C i = F ∪ T := by
    ext x
    cases h : x i <;> simp [directionEndpoints, F, T, h]
  have hdisj : Disjoint F T := by
    apply Finset.disjoint_left.mpr
    intro x hxF hxT
    have hf := (Finset.mem_filter.mp hxF).2.1
    have ht := (Finset.mem_filter.mp hxT).2.1
    exact Bool.false_ne_true (hf.symm.trans ht)
  rw [hunion, Finset.card_union_of_disjoint hdisj, ← hFT]
  change F.card + F.card = 2 * F.card
  omega

private theorem direction_endpoint_equation {d : Nat} (C : Finset (Q (d * d)))
    (sigma : Q (d * d) → Real)
    (hr : ((hypercube (d * d)).induce (C : Set (Q (d * d)))).IsRegularOfDegree d)
    (hs : IsSwitching C sigma) (i : Fin (d * d)) :
    (d : Real) * (directionEndpoints C i).card = (C.card : Real) := by
  let z := switchingVector C sigma
  have heigen : (huangMatrix (d * d)).mulVec z = (d : Real) • z :=
    ambient_eigenvector C sigma hr hs
  have hsym : (huangMatrix (d * d)).IsSymm :=
    Matrix.IsSymm.ext (fun x y => huangMatrix_symmetric y x)
  have hmove : z ⬝ᵥ (huangMatrix (d * d)).mulVec (gamma i z) =
      (d : Real) * (z ⬝ᵥ gamma i z) := by
    rw [hsym.dotProduct_mulVec_comm, heigen]
    simp [dotProduct_comm]
  have hanti := congrArg (fun w => z ⬝ᵥ w) (anticommutator i z)
  rw [dotProduct_add, hmove, heigen, map_smul, dotProduct_smul, dotProduct_smul] at hanti
  have hdot : z ⬝ᵥ gamma i z = ((directionEndpoints C i).card : Real) :=
    switching_dot_gamma hs i
  have hnorm : z ⬝ᵥ z = (C.card : Real) := by
    simpa only [dotProduct, ← pow_two] using switching_norm hs
  rw [hdot, hnorm] at hanti
  simp only [smul_eq_mul] at hanti
  linarith

/-- Every actual cube direction has the same number of selected edges. -/
theorem direction_edge_count {d : Nat} (C : Finset (Q (d * d)))
    (hr : ((hypercube (d * d)).induce (C : Set (Q (d * d)))).IsRegularOfDegree d)
    (hb : IsBalanced C) (i : Fin (d * d)) :
    2 * d * directionEdges C i = C.card := by
  obtain ⟨sigma, hs⟩ := hb
  have h := direction_endpoint_equation C sigma hr hs i
  rw [endpoint_card_twice] at h
  have hreal : ((2 * d * directionEdges C i : Nat) : Real) = (C.card : Real) := by
    push_cast
    push_cast at h
    nlinarith [h]
  exact_mod_cast hreal

end D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
