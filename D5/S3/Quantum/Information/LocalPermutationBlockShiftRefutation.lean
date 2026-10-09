/- GID: D5/S3/Quantum/Information/LocalPermutationBlockShiftRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/LocalPermutationBlockShiftRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/LocalPermutationBlockShiftRefutation.claim; result=D5/S3/Quantum/Information/LocalPermutationBlockShiftRefutation.result; claim=D5/S3/Quantum/Information/LocalPermutationBlockShiftRefutation.claim
   digest: A three-qubit root vector refutes extended local block-shift similarity. -/

/-
proof_shape: result: content (monomial support transport and subgroup closure).
escape_witness: supports_inverse constructs the reciprocal monomial inverse;
  out_support carries its affine support invariant through subgroup closure;
  no_blockShift uses this invariant on the live path to result.
admission_basis: open-problem-resolution (#14776; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.tensorOp
    statement_id: sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
  D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  D5/S3/Quantum/Thermal/PositiveOneModeWilliamson.physicalJ2
    statement_id: sha256:a3c76f635d3fda80d5e5b8d7c1b2a552486e81143ead947af1e2bb7de3369327
Private mathematical declarations (classification and live consumers):
  supports_one: bind-only; consumers: out_support.
  supports_mul: bind-only; consumers: out_support, extended_support.
  supports_inverse: content; consumers: out_support, conjugate_support.
  affine_one: bind-only; consumers: out_support.
  affine_mul: bind-only; consumers: out_support, extended_support.
  affine_inverse: bind-only; consumers: out_support.
  factor_support: bind-only; consumers: local_support.
  local_support: bind-only; consumers: extended_support.
  pout_support: bind-only; consumers: adjacent_support.
  adjacent_support: bind-only; consumers: out_support.
  out_support: content; consumers: extended_support.
  extended_support: content; consumers: no_blockShift.
  conjugate_support: content; consumers: no_blockShift.
  delta_mem: bind-only; consumers: A_mem.
  tensor_diag: bind-only; consumers: torus_term_diagonal.
  Z_diagonal: bind-only; consumers: torus_term_diagonal.
  torus_term_diagonal: bind-only; consumers: Delta_diagonal.
  Delta_diagonal: bind-only; consumers: commutator.
  basis_injective: bind-only; consumers: A_entry.
  A_entry: bind-only; consumers: no_blockShift.
  commutator: bind-only; consumers: A_mem.
  A_mem: bind-only; consumers: result.
  blockShift_lower: bind-only; consumers: no_blockShift.
  first_bit_lt: bind-only; consumers: affine_obstruction.
  binary_perm: bind-only; consumers: affine_xor.
  affine_xor: bind-only; consumers: affine_obstruction.
  affine_obstruction: bind-only; consumers: no_blockShift.
  no_blockShift: content; consumers: result.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.Quantum.Thermal.PositiveOneModeWilliamson

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Matrix
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Thermal.PositiveOneModeWilliamson
noncomputable section
namespace D5.S3.Quantum.Information.LocalPermutationBlockShiftRefutation

def J : Matrix (Fin 2) (Fin 2) ℂ := physicalJ2.map (algebraMap ℝ ℂ)
def Pout : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,0,1,0; 0,-1,0,0; 0,0,0,1]
def PiLoc (n : ℕ) : Set (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ) :=
  {M | ∃ P, (∀ k, P k ∈ ({1, -1, J, -J} : Set _)) ∧ M = tensorOp P}

def adjacent {n : ℕ} (k : Fin (n - 1)) : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ) :=
  fun x y =>
  Pout (finProdFinEquiv (x ⟨k.val, by omega⟩, x ⟨k.val+1, by omega⟩))
    (finProdFinEquiv (y ⟨k.val, by omega⟩, y ⟨k.val+1, by omega⟩)) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≠ k.val ∧ j.val ≠ k.val+1),
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (x j) (y j)
/-- Matrix units representing the adjacent signed swaps. -/
def outGenerators (n : ℕ) : Set (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)ˣ :=
  {u | ∃ k : Fin (n-1), (u : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)) = adjacent k}
def PiOut (n : ℕ) : Subgroup (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)ˣ := Subgroup.closure (outGenerators n)
def PiEx (n : ℕ) : Set (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ) :=
  {M | ∃ p ∈ PiLoc n, ∃ q : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)ˣ, q ∈ PiOut n ∧ M = p * (q : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ))}
def tloc (n : ℕ) : Set (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ) :=
  {D | ∃ lam : Fin n → ℝ, D = ∑ k,
    tensorOp (fun j => if j = k then (Complex.I * (lam k : ℂ)) • qubitZ else 1)}
def E (n : ℕ) : Set (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ) :=
  {A | ∃ D ∈ tloc n, ∃ φ : ℝ, φ ≠ 0 ∧ D * A - A * D = (Complex.I * (φ : ℂ)) • A}
def IsBlockShift {n : ℕ} (M : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)) : Prop :=
  ∃ β : (Lex (Fin n → Fin 2)) → ℕ, Monotone β ∧ ∀ r c, M r c ≠ 0 → β r = β c + 1
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ A ∈ E n, ∃ P ∈ PiEx n, IsBlockShift (P * A * P⁻¹)


variable {n : ℕ}

private def Supports (M : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ))
    (g : Equiv.Perm (Lex (Fin n → Fin 2))) : Prop :=
  ∀ r c, M r c ≠ 0 ↔ r = g c

private def Affine (g : Equiv.Perm (Lex (Fin n → Fin 2))) : Prop :=
  ∃ pi : Equiv.Perm (Fin n), ∃ f : Fin n → Equiv.Perm (Fin 2),
    ∀ x k, g x k = f k (x (pi k))

private lemma supports_one : Supports (1 : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)) (Equiv.refl _) := by
  intro r c
  simp [Matrix.one_apply]

private lemma supports_mul {M N : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)}
    {g h : Equiv.Perm (Lex (Fin n → Fin 2))}
    (hM : Supports M g) (hN : Supports N h) : Supports (M * N) (h.trans g) := by
  intro r c
  have he : (M * N) r c = M r (h c) * N (h c) c := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single (h c)
    · intro b _ hb
      have hz : N b c = 0 := by
        by_contra hn
        exact hb ((hN b c).mp hn)
      simp [hz]
    · simp
  rw [he, mul_ne_zero_iff]
  rw [hM r (h c), hN (h c) c]
  simp

private lemma supports_inverse {M : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)}
    {g : Equiv.Perm (Lex (Fin n → Fin 2))}
    (hM : Supports M g) : Supports M⁻¹ g.symm := by
  let B : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ) := fun r c => if c = g r then (M (g r) r)⁻¹ else 0
  have hB : B * M = 1 := by
    ext r c
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (g r)]
    · by_cases h : r = c
      · subst c
        simp [B, (hM (g r) r).mpr rfl]
      · have hz : M (g r) c = 0 := by
          by_contra hn
          exact h (g.injective ((hM (g r) c).mp hn))
        simp [B, hz, h]
    · intro b _ hb
      simp [B, hb]
    · simp
  rw [Matrix.inv_eq_left_inv hB]
  intro r c
  change (if c = g r then (M (g r) r)⁻¹ else 0) ≠ 0 ↔ r = g.symm c
  by_cases h : c = g r
  · simp [h, (hM (g r) r).mpr rfl]
  · have hn : r ≠ g.symm c := by
      intro he
      exact h (by simp [he])
    simp [h, hn]

private lemma affine_one : Affine (Equiv.refl (Lex (Fin n → Fin 2))) := by
  exact ⟨Equiv.refl _, fun _ => Equiv.refl _, fun _ _ => rfl⟩

private lemma affine_mul {g h : Equiv.Perm (Lex (Fin n → Fin 2))} (hg : Affine g) (hh : Affine h) :
    Affine (h.trans g) := by
  rcases hg with ⟨p, f, hf⟩
  rcases hh with ⟨q, t, ht⟩
  refine ⟨p.trans q, fun k => (t (p k)).trans (f k), ?_⟩
  intro x k
  simp [hf, ht]

private lemma affine_inverse
    {g : Equiv.Perm (Lex (Fin n → Fin 2))} (hg : Affine g) : Affine g.symm := by
  rcases hg with ⟨p, f, hf⟩
  refine ⟨p.symm, fun k => (f (p.symm k)).symm, ?_⟩
  intro x k
  apply (f (p.symm k)).injective
  have ht := hf (g.symm x) (p.symm k)
  simpa using ht.symm

private lemma factor_support {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : P ∈ ({1, -1, J, -J} : Set _)) :
    ∃ f : Equiv.Perm (Fin 2), ∀ r c, P r c ≠ 0 ↔ r = f c := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · refine ⟨Equiv.refl _, ?_⟩
    intro r c
    simp [Matrix.one_apply]
  · refine ⟨Equiv.refl _, ?_⟩
    intro r c
    simp [Matrix.one_apply]
  · refine ⟨Equiv.swap 0 1, ?_⟩
    intro r c
    fin_cases r <;> fin_cases c <;> norm_num [J, physicalJ2, Matrix.map_apply, Equiv.swap_apply_def]
  · refine ⟨Equiv.swap 0 1, ?_⟩
    intro r c
    fin_cases r <;> fin_cases c <;> norm_num [J, physicalJ2, Matrix.map_apply, Equiv.swap_apply_def]

private lemma local_support {M : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)}
    (hM : M ∈ PiLoc n) :
    ∃ g : Equiv.Perm (Lex (Fin n → Fin 2)), Supports M g ∧ Affine g := by
  rcases hM with ⟨P, hP, rfl⟩
  choose f hf using fun k => factor_support (hP k)
  let g : Equiv.Perm (Lex (Fin n → Fin 2)) := Equiv.piCongrRight f
  refine ⟨g, ?_, Equiv.refl _, f, fun _ _ => rfl⟩
  intro r c
  simp only [tensorOp, Matrix.of_apply, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left, hf]
  exact funext_iff.symm

private lemma pout_support (a b c d : Fin 2) :
    Pout (finProdFinEquiv (a, b)) (finProdFinEquiv (c, d)) ≠ 0 ↔ a = d ∧ b = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [Pout, finProdFinEquiv]

private lemma adjacent_support (k : Fin (n-1)) :
    Supports (adjacent k) ((Equiv.arrowCongr (Equiv.swap
      (⟨k.val, by omega⟩ : Fin n) ⟨k.val+1, by omega⟩).symm (Equiv.refl (Fin 2)))) := by
  intro r c
  let a : Fin n := ⟨k.val, by omega⟩
  let b : Fin n := ⟨k.val+1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a,b] at this
  have hone (u v : Fin 2) : (1 : Matrix (Fin 2) (Fin 2) ℂ) u v ≠ 0 ↔ u = v := by
    simp [Matrix.one_apply]
  simp only [adjacent, mul_ne_zero_iff, pout_support, Finset.prod_ne_zero_iff,
    Finset.mem_filter, Finset.mem_univ, true_and, hone]
  constructor
  · rintro ⟨⟨ha,hb⟩,ht⟩
    funext j
    change r j = c ((Equiv.swap a b) j)
    by_cases hja : j = a
    · subst j; simpa [hab] using ha
    by_cases hjb : j = b
    · subst j; simpa [hab] using hb
    rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
    exact ht j ⟨by simpa [a, Fin.ext_iff] using hja,
      by simpa [b, Fin.ext_iff] using hjb⟩
  · intro h
    have ht (j : Fin n) : r j = c ((Equiv.swap a b) j) := congrFun h j
    constructor
    · constructor
      · simpa [hab] using ht a
      · simpa [hab] using ht b
    · intro j hj
      simpa [Equiv.swap_apply_of_ne_of_ne
        (show j ≠ a by simpa [a,Fin.ext_iff] using hj.1)
        (show j ≠ b by simpa [b,Fin.ext_iff] using hj.2)] using ht j

private lemma out_support {q : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)ˣ} (hq : q ∈ PiOut n) :
    ∃ g : Equiv.Perm (Lex (Fin n → Fin 2)), Supports (q : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)) g ∧ Affine g := by
  induction hq using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with ⟨k, hk⟩
    refine ⟨_, hk ▸ adjacent_support k, Equiv.swap
      (⟨k.val, by omega⟩ : Fin n) ⟨k.val+1, by omega⟩, fun _ => Equiv.refl _, ?_⟩
    intro x j
    rfl
  | one => exact ⟨_, supports_one, affine_one⟩
  | mul u v hu hv ihu ihv =>
    rcases ihu with ⟨g,hg,ag⟩
    rcases ihv with ⟨h,hh,ah⟩
    exact ⟨_, supports_mul hg hh, affine_mul ag ah⟩
  | inv u hu ihu =>
    rcases ihu with ⟨g,hg,ag⟩
    refine ⟨g.symm, ?_, affine_inverse ag⟩
    have hi : ((u : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ))⁻¹) = (↑(u⁻¹) : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)) :=
      Matrix.inv_eq_left_inv u.inv_val
    rw [← hi]
    exact supports_inverse hg

private lemma extended_support {M : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)}
    (hM : M ∈ PiEx n) :
    ∃ g : Equiv.Perm (Lex (Fin n → Fin 2)), Supports M g ∧ Affine g := by
  rcases hM with ⟨p,hp,q,hq,rfl⟩
  rcases local_support hp with ⟨g,hg,ag⟩
  rcases out_support hq with ⟨h,hh,ah⟩
  exact ⟨_,supports_mul hg hh,affine_mul ag ah⟩


private lemma conjugate_support {P A : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)}
    {g : Equiv.Perm (Lex (Fin n → Fin 2))}
    (hP : Supports P g) (r c : (Lex (Fin n → Fin 2))) :
    (P * A * P⁻¹) (g r) (g c) ≠ 0 ↔ A r c ≠ 0 := by
  have hi := supports_inverse hP
  have hl (t : (Lex (Fin n → Fin 2))) : (P * A) (g r) t = P (g r) r * A r t := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single r
    · intro b _ hb
      have hz : P (g r) b = 0 := by
        by_contra hn
        exact hb (g.injective ((hP _ _).mp hn)).symm
      simp [hz]
    · simp
  have he : (P * A * P⁻¹) (g r) (g c) =
      (P (g r) r * A r c) * P⁻¹ c (g c) := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single c, hl]
    · intro b _ hb
      have hz : P⁻¹ b (g c) = 0 := by
        by_contra hn
        exact hb (by simpa using (hi b (g c)).mp hn)
      simp [hz]
    · simp
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff]
  simp [(hP (g r) r).mpr rfl, (hi c (g c)).mpr (by simp)]

private def bar (x : (Lex (Fin n → Fin 2))) : (Lex (Fin n → Fin 2)) := fun k => (Equiv.swap 0 1) (x k)

private def A : (Matrix (Lex (Fin 3 → Fin 2)) (Lex (Fin 3 → Fin 2)) ℂ) :=
  ∑ j : Fin 3, Matrix.single (bar (Pi.single j (1 : Fin 2))) (Pi.single j (1 : Fin 2)) 1

private def Delta : (Matrix (Lex (Fin 3 → Fin 2)) (Lex (Fin 3 → Fin 2)) ℂ) := ∑ k : Fin 3,
  tensorOp (fun j => if j = k then Complex.I • qubitZ else 1)

private lemma delta_mem : Delta ∈ tloc 3 := by
  refine ⟨fun _ => 1, ?_⟩
  simp [Delta]

private lemma tensor_diag (d : Fin n → Fin 2 → ℂ) :
    tensorOp (fun k => Matrix.diagonal (d k)) =
      Matrix.diagonal (fun x : (Lex (Fin n → Fin 2)) => ∏ k, d k (x k)) := by
  ext r c
  by_cases h : r = c
  · subst c
    simp [tensorOp]
  · have hh : ∃ k, r k ≠ c k := by
      by_contra! hh
      exact h (funext hh)
    rcases hh with ⟨k,hk⟩
    have hz : (∏ j, Matrix.diagonal (d j) (r j) (c j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      simp [hk]
    change (∏ j, Matrix.diagonal (d j) (r j) (c j)) = _
    rw [hz]
    simp [h]

private lemma Z_diagonal : qubitZ = Matrix.diagonal (fun b : Fin 2 => if b = 0 then 1 else -1) := by
  exact Matrix.ext_iff_trace_mul_left.mpr (congrFun rfl)

private lemma torus_term_diagonal (k : Fin n) (v : ℂ) :
    tensorOp (fun j => if j = k then v • qubitZ else 1) =
      Matrix.diagonal (fun x : (Lex (Fin n → Fin 2)) => v * (if x k = 0 then 1 else -1)) := by
  let d : Fin n → Fin 2 → ℂ := fun j b => if j = k then v * (if b = 0 then 1 else -1) else 1
  have hf : (fun j : Fin n => if j = k then v • qubitZ else 1) =
      (fun j => Matrix.diagonal (d j)) := by
    funext j
    by_cases h : j = k
    · subst j
      simp only [ite_true, Z_diagonal]
      rw [← Matrix.diagonal_smul]
      congr 1
      funext b
      simp [d]
    · simp [h,d]
  rw [hf, tensor_diag d]
  congr 1
  funext x
  simp [d]

private lemma Delta_diagonal : Delta = Matrix.diagonal (fun x : (Lex (Fin 3 → Fin 2)) =>
    Complex.I * ((if x 0 = 0 then 1 else -1) +
      (if x 1 = 0 then 1 else -1) + (if x 2 = 0 then 1 else -1))) := by
  simp only [Delta, Fin.sum_univ_three, torus_term_diagonal]
  ext r c
  by_cases h : r = c
  · subst c
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq]
    ring
  · simp [h]

private lemma basis_injective : Function.Injective (fun j : Fin n => (Pi.single j (1 : Fin 2) : Lex (Fin n → Fin 2))) := by
  intro a b h
  by_contra hn
  have hh := congrFun h a
  simp [Pi.single,hn] at hh

private lemma A_entry (j : Fin 3) : A (bar (Pi.single j (1 : Fin 2))) (Pi.single j (1 : Fin 2)) ≠ 0 := by
  simp only [A, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have hne : (Pi.single j (1 : Fin 2) : Fin 3 → Fin 2) ≠
        (Pi.single b (1 : Fin 2) : Fin 3 → Fin 2) := fun h => hb (basis_injective h).symm
    simp [hne, eq_comm]
  · simp

private lemma commutator : Delta * A - A * Delta = (Complex.I * (-2 : ℂ)) • A := by
  rw [Delta_diagonal]
  ext r c
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul, A, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.mul_sum,Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : bar (Pi.single j (1 : Fin 2)) = r ∧ Pi.single j (1 : Fin 2) = c
  · rcases h with ⟨rfl,rfl⟩
    simp only [and_self,ite_true]
    fin_cases j <;> norm_num [bar,Pi.single_apply,Fin.ext_iff] <;> ring
  · simp [h]

private lemma A_mem : A ∈ E 3 := by
  exact ⟨Delta,delta_mem,-2,by norm_num,by simpa using commutator⟩

private lemma blockShift_lower {M : (Matrix (Lex (Fin n → Fin 2)) (Lex (Fin n → Fin 2)) ℂ)}
    (hM : IsBlockShift M) (r c : (Lex (Fin n → Fin 2)))
    (hn : M r c ≠ 0) : c < r := by
  rcases hM with ⟨b,hb,hs⟩
  have he := hs r c hn
  by_contra h
  have hh := hb (le_of_not_gt h)
  omega

private lemma first_bit_lt {x y : (Lex (Fin 3 → Fin 2))} (hx : x 0 = 0) (hy : y 0 = 1) : x < y := by
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    exact (Fin.not_lt_zero j hj).elim
  · simp [hx,hy]

private def xorBit (b a : Fin 2) : Fin 2 := if a = 0 then b else (Equiv.swap 0 1) b

private lemma binary_perm (f : Equiv.Perm (Fin 2)) (b : Fin 2) :
    f b = xorBit b (f 0) := by
  have hn : f 0 ≠ f 1 := f.injective.ne (by decide)
  by_cases h0 : f 0 = 0
  · have h1 : f 1 = 1 := Fin.eq_one_of_ne_zero _ (by
      intro h
      exact hn (h0.trans h.symm))
    fin_cases b
    · change f 0 = xorBit 0 (f 0)
      simp [xorBit,h0]
    · change f 1 = xorBit 1 (f 0)
      simp [xorBit,h0,h1]
  · have h01 := Fin.eq_one_of_ne_zero _ h0
    have h10 : f 1 = 0 := by
      apply Fin.ext
      have hl := (f 1).isLt
      have hv : (f 1).val ≠ 1 := by
        intro h
        exact hn (h01.trans (Fin.ext h).symm)
      omega
    fin_cases b
    · change f 0 = xorBit 0 (f 0)
      simp [xorBit,h01]
    · change f 1 = xorBit 1 (f 0)
      simp [xorBit,h01,h10]

private lemma affine_xor {g : Equiv.Perm (Lex (Fin n → Fin 2))} (hg : Affine g) :
    ∃ p : Equiv.Perm (Fin n), ∃ a : (Lex (Fin n → Fin 2)),
      ∀ x k, g x k = xorBit (x (p k)) (a k) := by
  rcases hg with ⟨p,f,hf⟩
  exact ⟨p,fun k => f k 0,fun x k => (hf x k).trans (binary_perm (f k) _)⟩

private lemma affine_obstruction {g : Equiv.Perm ((Lex (Fin 3 → Fin 2)))} (hg : Affine g) :
    ∃ j : Fin 3, g (bar (Pi.single j (1 : Fin 2))) < g (Pi.single j (1 : Fin 2)) := by
  rcases affine_xor hg with ⟨p,a,hf⟩
  by_cases ha : a 0 = 0
  · refine ⟨p 0,first_bit_lt ?_ ?_⟩ <;>
      rw [hf] <;> simp [bar,xorBit,ha]
  · let j : Fin 3 := if p 0 = 0 then 1 else 0
    have hj : p 0 ≠ j := by
      dsimp [j]
      by_cases hp : p 0 = 0
      · simp [hp]
      · simp [hp]
    have ha1 : a 0 = 1 := Fin.eq_one_of_ne_zero _ ha
    refine ⟨j,first_bit_lt ?_ ?_⟩ <;>
      rw [hf] <;> simp [bar,xorBit,ha1,hj]

private lemma no_blockShift {P : (Matrix (Lex (Fin 3 → Fin 2)) (Lex (Fin 3 → Fin 2)) ℂ)}
    (hP : P ∈ PiEx 3) :
    ¬ IsBlockShift (P * A * P⁻¹) := by
  rcases extended_support hP with ⟨g,hg,ag⟩
  rcases affine_obstruction ag with ⟨j,hj⟩
  intro h
  have hn := (conjugate_support hg (bar (Pi.single j (1 : Fin 2))) (Pi.single j (1 : Fin 2))).mpr (A_entry j)
  exact (lt_asymm hj (blockShift_lower h _ _ hn))

theorem result : ¬ claim := by
  intro h
  rcases h 3 (by norm_num) A A_mem with ⟨P,hP,hs⟩
  exact no_blockShift hP hs

#print axioms result
end D5.S3.Quantum.Information.LocalPermutationBlockShiftRefutation
