/- GID: D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pronko's non-cyclic Fredkin-chain eigenstates are annihilated by Sigma. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #9359)
Direct frozen dependencies: D5/S3/Quantum/FiniteDimensional.qubitZ (statement_id sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c)
-/

import D5.S3.Quantum.FiniteDimensional

open scoped BigOperators Matrix
open D5.S3.Quantum.FiniteDimensional

namespace D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation

/-- `σ^+ = [[0,1],[0,0]]` (printed page 3), on the basis `0 = |↑⟩`, `1 = |↓⟩`. -/
def sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- `σ^- = [[0,0],[1,0]]`. -/
def sigmaMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- `n↑ = ½(1 + σ^z)`. -/
noncomputable def nUp : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • (1 + qubitZ)

/-- `n↓ = ½(1 − σ^z)`. -/
noncomputable def nDown : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • (1 - qubitZ)

/-- The Kronecker product `f 0 ⊗ ⋯ ⊗ f (N−1)` on `(ℂ²)^{⊗N}`, indexed by site
configurations `Fin N → Fin 2`. -/
def tensor (N : ℕ) (f : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun y x => ∏ i, f i (y i) (x i)

/-- `A_j`: the one-site operator `A` acting in the `j`th factor, identity elsewhere. -/
def site (N : ℕ) (j : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  tensor N fun i => if i = j then A else 1

/-- `P_{j,j+1}`: the permutation operator exchanging the `j`th and `(j+1)`th copies
(sites mod `N`). -/
def P (N : ℕ) (j : Fin N) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Equiv.Perm.permMatrix ℂ
    ((Equiv.swap j (finRotate N j)).arrowCongr (Equiv.refl (Fin 2)))

/-- `Π_{j,j+1} = ½(1 − P_{j,j+1})`. -/
noncomputable def Pi (N : ℕ) (j : Fin N) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 - P N j)

/-- (2.2): `F_{j,j+1,j+2} = n↑_j Π_{j+1,j+2} + Π_{j,j+1} n↓_{j+2}`,
sites mod `N`. -/
noncomputable def F (N : ℕ) (j : Fin N) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  site N j nUp * Pi N (finRotate N j) +
    Pi N j * site N (finRotate N (finRotate N j)) nDown

/-- (2.3): `H = Σ_{j=1}^{N} F_{j,j+1,j+2}`. -/
noncomputable def H (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ := ∑ j, F N j

/-- `C = P_{1,2} ⋯ P_{N−2,N−1} P_{N−1,N}` (printed pages 3–4), the ordered
product over `j = 0, …, N−2`. -/
noncomputable def C (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  ((List.finRange N).dropLast.map (P N)).prod

/-- `σ^{r}` for `r ∈ {−1, 0, 1}` encoded as `Fin 3` by `r ↦ r + 1`:
`0 ↦ σ^-`, `1 ↦ 1`, `2 ↦ σ^+`. -/
def sigmaPow : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => sigmaMinus
  | 1 => 1
  | 2 => sigmaPlus

/-- (3.1): `Σ^{ε} = Σ_{r ∈ {−1,0,1}^N, Σ r_i = ε} σ₁^{r₁} ⋯ σ_N^{r_N}`;
`Σ^± = Sigma N (±1)`. -/
def Sigma (N : ℕ) (ε : ℤ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  ∑ r ∈ (Finset.univ : Finset (Fin N → Fin 3)).filter
      (fun r => (∑ i, (((r i : ℕ) : ℤ) - 1)) = ε),
    tensor N fun i => sigmaPow (r i)

/-- Conjecture 1 (printed page 7), fully quantified per #9359. The convention is
`0 = ↑`, `1 = ↓`, and `ψ` is a vector in `(ℂ²)^{⊗N}` indexed by configurations.
An eigenstate is nonzero, is an eigenvector of both `H` and `C`, and is non-cyclic
when its `C`-eigenvalue differs from one. -/
def claim : Prop := ∀ N : ℕ, 3 ≤ N → ∀ ψ : (Fin N → Fin 2) → ℂ, ψ ≠ 0 → ∀ E c : ℂ,
  (H N).mulVec ψ = E • ψ → (C N).mulVec ψ = c • ψ → c ≠ 1 →
    (Sigma N 1).mulVec ψ = 0 ∧ (Sigma N (-1)).mulVec ψ = 0

private def spinStep (y x : Fin 2) : Fin 3 :=
  if y = x then 1 else if y = 0 then 2 else 0

private def weight (N : ℕ) (x : Fin N → Fin 2) : ℤ :=
  ∑ i, if x i = 0 then 1 else 0

example : nUp = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nUp, qubitZ, Matrix.one_apply]

example : nDown = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nDown, qubitZ, Matrix.one_apply]

example (N : ℕ) (j : Fin N) (ψ : (Fin N → Fin 2) → ℂ) :
    (P N j).mulVec ψ =
      ψ ∘ ((Equiv.swap j (finRotate N j)).arrowCongr (Equiv.refl (Fin 2))) := by
  exact Matrix.permMatrix_mulVec
    ((Equiv.swap j (finRotate N j)).arrowCongr (Equiv.refl (Fin 2))) (v := ψ)

example (N : ℕ) (hN : 3 ≤ N) (j : Fin N) :
    j ≠ finRotate N j ∧ j ≠ finRotate N (finRotate N j) ∧
      finRotate N j ≠ finRotate N (finRotate N j) := by
  let _ : NeZero N := ⟨by omega⟩
  simp only [finRotate_apply]
  constructor
  · intro h
    have h' : j + 0 = j + 1 := by simpa using h
    have h01 : (0 : Fin N) = 1 := add_left_cancel h'
    have := congrArg Fin.val h01
    norm_num at this
    omega
  constructor
  · intro h
    have h' : j + 0 = j + (1 + 1) := by simpa [add_assoc] using h
    have h02 : (0 : Fin N) = 1 + 1 := add_left_cancel h'
    have := congrArg Fin.val h02
    norm_num [Fin.add_def, Nat.mod_eq_of_lt hN] at this
  · intro h
    have h' : j + 1 = j + (1 + 1) := by simpa [add_assoc] using h
    have h12 : (1 : Fin N) = 1 + 1 := add_left_cancel h'
    have := congrArg Fin.val h12
    norm_num [Fin.add_def, Nat.mod_eq_of_lt hN] at this
    have h1N : 1 < N := by omega
    rw [Nat.mod_eq_of_lt h1N] at this
    omega

example : C 3 = P 3 0 * P 3 1 := by
  simp [C, List.finRange]

example : C 4 = P 4 0 * P 4 1 * P 4 2 := by
  rw [show C 4 = P 4 0 * (P 4 1 * P 4 2) by simp [C, List.finRange], Matrix.mul_assoc]

example (ψ : (Fin 3 → Fin 2) → ℂ) :
    (C 3).mulVec ψ =
      ψ ∘ (((finRotate 3).arrowCongr (Equiv.refl (Fin 2))).symm) := by
  have hC : C 3 =
      Equiv.Perm.permMatrix ℂ (((finRotate 3).arrowCongr (Equiv.refl (Fin 2))).symm) := by
    rw [show C 3 = P 3 0 * P 3 1 by simp [C, List.finRange], P, P,
      ← Matrix.permMatrix_mul]
    congr 1
    ext x i
    fin_cases i <;>
      simp [Equiv.Perm.mul_apply] <;> congr 2
  rw [hC]
  exact Matrix.permMatrix_mulVec _ (v := ψ)

example (ψ : (Fin 4 → Fin 2) → ℂ) :
    (C 4).mulVec ψ =
      ψ ∘ (((finRotate 4).arrowCongr (Equiv.refl (Fin 2))).symm) := by
  have hC : C 4 =
      Equiv.Perm.permMatrix ℂ (((finRotate 4).arrowCongr (Equiv.refl (Fin 2))).symm) := by
    rw [show C 4 = P 4 0 * P 4 1 * P 4 2 by
          rw [show C 4 = P 4 0 * (P 4 1 * P 4 2) by simp [C, List.finRange], Matrix.mul_assoc],
      P, P, P, ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
    congr 1
    ext x i
    fin_cases i <;>
      simp [Equiv.Perm.mul_apply] <;> congr 2
  rw [hC]
  exact Matrix.permMatrix_mulVec _ (v := ψ)

example : ∃ (ψ : (Fin 4 → Fin 2) → ℂ) (E c : ℂ),
    ψ ≠ 0 ∧ (H 4).mulVec ψ = E • ψ ∧ (C 4).mulVec ψ = c • ψ ∧ c ≠ 1 := by
  classical
  let ψ : (Fin 4 → Fin 2) → ℂ := fun x =>
    if x = ![0, 0, 1, 1] then 1 else
    if x = ![0, 1, 0, 1] then 1 else
    if x = ![0, 1, 1, 0] then -1 else
    if x = ![1, 0, 0, 1] then -1 else
    if x = ![1, 0, 1, 0] then -1 else
    if x = ![1, 1, 0, 0] then 1 else 0
  have hFAction : ∀ (M : ℕ) (j : Fin M) (φ : (Fin M → Fin 2) → ℂ)
      (y : Fin M → Fin 2),
      (F M j).mulVec φ y =
        (if y j = 0 then (1 : ℂ) else 0) *
            ((1 / 2 : ℂ) *
              (φ y - φ (((Equiv.swap (finRotate M j) (finRotate M (finRotate M j))).arrowCongr
                (Equiv.refl (Fin 2))) y))) +
          (1 / 2 : ℂ) *
            ((if y (finRotate M (finRotate M j)) = 1 then (1 : ℂ) else 0) * φ y -
              (if (((Equiv.swap j (finRotate M j)).arrowCongr (Equiv.refl (Fin 2))) y)
                    (finRotate M (finRotate M j)) = 1 then (1 : ℂ) else 0) *
                φ (((Equiv.swap j (finRotate M j)).arrowCongr (Equiv.refl (Fin 2))) y)) := by
    intro M j φ y
    have hUp : site M j nUp =
        Matrix.diagonal (fun x => if x j = 0 then (1 : ℂ) else 0) := by
      ext a b
      simp only [site, tensor, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst b
        by_cases ha : a j = 0
        · rw [Finset.prod_eq_single j]
          · simp [ha, nUp, qubitZ]
            norm_num
          · intro i _ hij
            simp [hij]
          · simp
        · have ha1 : a j = 1 := by
            generalize hv : a j = v at ha ⊢
            fin_cases v <;> simp_all
          rw [Finset.prod_eq_single j]
          · simp [ha1, nUp, qubitZ]
          · intro i _ hij
            simp [hij]
          · simp
      · rw [if_neg hab]
        have hcoord : ∃ i, a i ≠ b i := by
          by_contra h
          push Not at h
          exact hab (funext h)
        obtain ⟨i, hi⟩ := hcoord
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        by_cases hij : i = j
        · subst i
          generalize ha : a j = u at hi ⊢
          generalize hb : b j = v at hi ⊢
          fin_cases u <;> fin_cases v
          all_goals norm_num [nUp, qubitZ, Matrix.one_apply, Fin.ext_iff] at hi
          all_goals norm_num [nUp, qubitZ, Matrix.one_apply, Fin.ext_iff]
        · simp [hij, hi]
    have hDown : site M (finRotate M (finRotate M j)) nDown =
        Matrix.diagonal (fun x =>
          if x (finRotate M (finRotate M j)) = 1 then (1 : ℂ) else 0) := by
      let k := finRotate M (finRotate M j)
      change site M k nDown = Matrix.diagonal (fun x => if x k = 1 then (1 : ℂ) else 0)
      ext a b
      simp only [site, tensor, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst b
        by_cases ha : a k = 1
        · rw [Finset.prod_eq_single k]
          · simp [ha, nDown, qubitZ]
            norm_num
          · intro i _ hik
            simp [hik]
          · simp
        · have ha0 : a k = 0 := by
            generalize hv : a k = v at ha ⊢
            fin_cases v <;> simp_all
          rw [Finset.prod_eq_single k]
          · simp [ha0, nDown, qubitZ]
          · intro i _ hik
            simp [hik]
          · simp
      · rw [if_neg hab]
        have hcoord : ∃ i, a i ≠ b i := by
          by_contra h
          push Not at h
          exact hab (funext h)
        obtain ⟨i, hi⟩ := hcoord
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        by_cases hik : i = k
        · subst i
          generalize ha : a k = u at hi ⊢
          generalize hb : b k = v at hi ⊢
          fin_cases u <;> fin_cases v
          all_goals norm_num [nDown, qubitZ, Matrix.one_apply, Fin.ext_iff] at hi
          all_goals norm_num [nDown, qubitZ, Matrix.one_apply, Fin.ext_iff]
        · simp [hik, hi]
    have hPi : ∀ (k : Fin M) (v : (Fin M → Fin 2) → ℂ),
        (Pi M k).mulVec v =
          (1 / 2 : ℂ) •
            (v - v ∘ ((Equiv.swap k (finRotate M k)).arrowCongr
              (Equiv.refl (Fin 2)))) := by
      intro k v
      rw [Pi, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, P,
        Matrix.permMatrix_mulVec]
    rw [F, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hUp, hPi, hPi, hDown]
    simp [Matrix.mulVec_diagonal]
  refine ⟨ψ, 0, -1, ?_, ?_, ?_, by norm_num⟩
  · intro hψ
    have hx := congrFun hψ ![0, 0, 1, 1]
    norm_num [ψ] at hx
  · have hF : ∀ j : Fin 4, (F 4 j).mulVec ψ = 0 := by
      intro j
      funext y
      rw [hFAction]
      have hy : y = ![y 0, y 1, y 2, y 3] := by
        funext i
        fin_cases i <;> rfl
      rw [hy]
      generalize h0 : y 0 = a
      generalize h1 : y 1 = b
      generalize h2 : y 2 = d
      generalize h3 : y 3 = e
      fin_cases j <;> fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
        simp +decide [ψ, finRotate_apply, Equiv.arrowCongr, Equiv.swap_apply_def,
          Function.comp_apply, Fin.add_def]
    have hsum : (H 4).mulVec ψ = ∑ j, (F 4 j).mulVec ψ := by
      unfold H
      simpa using Matrix.sum_mulVec (Finset.univ : Finset (Fin 4)) (F 4) ψ
    rw [hsum]
    simp [hF]
  · have hC : C 4 =
        Equiv.Perm.permMatrix ℂ (((finRotate 4).arrowCongr (Equiv.refl (Fin 2))).symm) := by
      rw [show C 4 = P 4 0 * P 4 1 * P 4 2 by
            rw [show C 4 = P 4 0 * (P 4 1 * P 4 2) by simp [C, List.finRange],
              Matrix.mul_assoc],
        P, P, P, ← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
      congr 1
      ext x i
      fin_cases i <;>
        simp [Equiv.Perm.mul_apply] <;> congr 2
    rw [hC, Matrix.permMatrix_mulVec]
    funext x
    have hx : x = ![x 0, x 1, x 2, x 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    generalize h0 : x 0 = a
    generalize h1 : x 1 = b
    generalize h2 : x 2 = d
    generalize h3 : x 3 = e
    fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
      simp +decide [ψ, finRotate_apply, Equiv.arrowCongr, Equiv.swap_apply_def,
        Function.comp_apply, Fin.add_def]

/-- Conjecture 1 holds. The proof uses no property of `H`; the hypothesis
`H ψ = E • ψ` is retained exactly as in Conjecture 1. The annihilation argument proves
the stronger current property that every `C`-eigenvector with eigenvalue different from one
is annihilated by both operators. -/
theorem result : claim := by
  classical
  rw [claim]
  intro N _ ψ _ E c _ hC hc
  have sigma_entry : ∀ (M : ℕ) (ε : ℤ) (y x : Fin M → Fin 2),
      Sigma M ε y x = if weight M y - weight M x = ε then 1 else 0 := by
    intro M ε y x
    have hpow : ∀ (q : Fin 3) (a b : Fin 2),
        sigmaPow q a b = if q = spinStep a b then 1 else 0 := by
      intro q a b
      fin_cases q <;> fin_cases a <;> fin_cases b <;>
        norm_num [sigmaPow, sigmaPlus, sigmaMinus, spinStep, Matrix.one_apply,
          Fin.ext_iff]
    have htensor : ∀ r : Fin M → Fin 3,
        tensor M (fun i => sigmaPow (r i)) y x =
          if r = fun i => spinStep (y i) (x i) then 1 else 0 := by
      intro r
      rw [tensor]
      simp_rw [hpow]
      rw [Finset.prod_ite_zero]
      simp [funext_iff]
    have hlocal : ∀ a b : Fin 2,
        (((spinStep a b : Fin 3) : ℕ) : ℤ) - 1 =
          (if a = 0 then 1 else 0) - (if b = 0 then 1 else 0) := by
      intro a b
      fin_cases a <;> fin_cases b <;> norm_num [spinStep, Fin.ext_iff]
    have hstep :
        (∑ i, ((((spinStep (y i) (x i) : Fin 3) : ℕ) : ℤ) - 1)) =
          weight M y - weight M x := by
      unfold weight
      change (Finset.univ.sum fun i : Fin M =>
          (((spinStep (y i) (x i) : Fin 3) : ℕ) : ℤ) - 1) =
        (Finset.univ.sum fun i : Fin M => if y i = 0 then (1 : ℤ) else 0) -
          Finset.univ.sum fun i : Fin M => if x i = 0 then (1 : ℤ) else 0
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact hlocal (y i) (x i)
    rw [Sigma, Matrix.sum_apply]
    simp [htensor]
    rw [← hstep]
    congr 2
    rw [Finset.sum_sub_distrib]
    simp
  have weight_perm : ∀ (M : ℕ) (x : Fin M → Fin 2) (e : Equiv.Perm (Fin M)),
      weight M (e.arrowCongr (Equiv.refl (Fin 2)) x) = weight M x := by
    intro M x e
    change (∑ i, if x (e.symm i) = 0 then (1 : ℤ) else 0) =
      ∑ i, if x i = 0 then (1 : ℤ) else 0
    simpa using Equiv.sum_comp e.symm
      (fun i : Fin M => if x i = 0 then (1 : ℤ) else 0)
  have absorption_swap : ∀ (M : ℕ) (ε : ℤ) (j : Fin M),
      Sigma M ε * P M j = Sigma M ε := by
    intro M ε j
    rw [P, PEquiv.mul_toMatrix_toPEquiv]
    ext y x
    simp only [Matrix.submatrix_apply, id_eq]
    rw [sigma_entry, sigma_entry]
    have hweight :
        weight M
            (((Equiv.swap j (finRotate M j)).arrowCongr (Equiv.refl (Fin 2))).symm x) =
          weight M x := by
      simpa using weight_perm M x (Equiv.swap j (finRotate M j)).symm
    rw [hweight]
  have absorption_list : ∀ (M : ℕ) (ε : ℤ) (js : List (Fin M)),
      Sigma M ε * (js.map (P M)).prod = Sigma M ε := by
    intro M ε js
    induction js with
    | nil => simp
    | cons j js ih =>
        simpa only [List.map_cons, List.prod_cons, ← Matrix.mul_assoc,
          absorption_swap] using ih
  have absorption : ∀ (M : ℕ) (ε : ℤ), Sigma M ε * C M = Sigma M ε := by
    intro M ε
    exact absorption_list M ε (List.finRange M).dropLast
  have annihilate : ∀ ε : ℤ, (Sigma N ε).mulVec ψ = 0 := by
    intro ε
    have hv : (Sigma N ε).mulVec ψ = c • (Sigma N ε).mulVec ψ := by
      calc
        (Sigma N ε).mulVec ψ = (Sigma N ε * C N).mulVec ψ :=
          congrArg (fun A => A.mulVec ψ) (absorption N ε).symm
        _ = (Sigma N ε).mulVec ((C N).mulVec ψ) :=
          (Matrix.mulVec_mulVec ψ (Sigma N ε) (C N)).symm
        _ = (Sigma N ε).mulVec (c • ψ) := congrArg (Sigma N ε).mulVec hC
        _ = c • (Sigma N ε).mulVec ψ := Matrix.mulVec_smul _ _ _
    have hv0 : (c - 1) • (Sigma N ε).mulVec ψ = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]
      exact hv.symm
    rcases smul_eq_zero.mp hv0 with hscalar | hzero
    · exact (hc (sub_eq_zero.mp hscalar)).elim
    · exact hzero
  exact ⟨annihilate 1, annihilate (-1)⟩

#print axioms result

end D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation
