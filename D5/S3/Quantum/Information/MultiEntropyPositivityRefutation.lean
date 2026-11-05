/- GID: D5/S3/Quantum/Information/MultiEntropyPositivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/MultiEntropyPositivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.claim; result=D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.result; claim=D5/S3/Quantum/Information/MultiEntropyPositivityRefutation.claim
   digest: The antisymmetric three-qutrit state has negative fourth replica invariant. -/

/-
proof_shape: result: bind-only. All private theorems below are consumed bind-only helpers.
escape_witness: none
admission_basis: open-problem-resolution (#17540; Refuted)
Direct frozen dependencies (declaration statement_id at the merged dev base):
  D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.sum_fin_cons
    sha256:684738da2e682c2f5a38ed6f2c093e7bff11d8e81543b2e8a902965155b1a51d
  D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.shift
    sha256:f2abbcac1649fa4bb5059d9285404640d1c1ad864102ba749d3e3cff9c1b46d7
  D5/S3/Quantum/Information/PartialTraceMutualInformation.partialTraceRight
    sha256:8fd00cbe799f3e8a3163a296b2ad235e0a251e3e79b744b52197ba12d0343f77
  D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.unitVector
    sha256:d1a62babf629dc509728b7cc3fdd00d3c1a344bd402c4571a04d543f1d3b31a9
  D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRays.dot_star_self
    sha256:bb2b7db6682247623accfd4e25006f4d2a38c0a99a27aaf94737603b17e05ac4
IsUnitState and claim preserve the preregistered expressions; proofs reuse unitVector
through unit_norm_iff and LowRankRays.dot_star_self.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
Escape audit unfinished for the publicized sum_fin_cons and dot_star_self owners:
https://github.com/the-omega-institute/trureturing/issues/17765.
The following dependency names refer to the declaration identities above.
  Support.sum_split: proof_shape: bind-only; escape_witness: none.
    consumers: Support.sum_unshifted; direct frozen dependencies: none.
  Support.sum_unshifted: proof_shape: bind-only; escape_witness: none.
    consumers: trace_party; direct frozen dependencies: none.
  Support.trace_four: proof_shape: bind-only; escape_witness: none.
    consumers: Support.torus_transfer; direct frozen dependencies: sum_fin_cons.
  Support.torus_transfer: proof_shape: bind-only; escape_witness: none.
    consumers: Group.torus_value; direct frozen dependencies: sum_fin_cons.
  eps_square_sum: proof_shape: bind-only; escape_witness: none.
    consumers: psi_unit; direct frozen dependencies: none.
  unit_norm_iff: proof_shape: bind-only; escape_witness: none.
    consumers: psi_unit, result; direct frozen dependencies: unitVector, dot_star_self.
  psi_unit: proof_shape: bind-only; escape_witness: none.
    consumers: result; direct frozen dependencies: unitVector, dot_star_self.
  eps_gram: proof_shape: bind-only; escape_witness: none.
    consumers: rho_psi; direct frozen dependencies: none.
  shift_grid2: proof_shape: bind-only; escape_witness: none.
    consumers: trace_party; direct frozen dependencies: shift.
  trace_party: proof_shape: bind-only; escape_witness: none.
    consumers: E_torus; direct frozen dependencies: shift, partialTraceRight.
  rep_eta: proof_shape: bind-only; escape_witness: none.
    consumers: E_torus; direct frozen dependencies: none.
  shift_vec0: proof_shape: bind-only; escape_witness: none.
    consumers: E_torus; direct frozen dependencies: shift.
  shift_vec1: proof_shape: bind-only; escape_witness: none.
    consumers: E_torus; direct frozen dependencies: shift.
  E_torus: proof_shape: bind-only; escape_witness: none.
    consumers: value; direct frozen dependencies: shift, partialTraceRight.
  vertex_apply: proof_shape: bind-only; escape_witness: none.
    consumers: RowFormula.row_formula; direct frozen dependencies: none.
  rho_psi: proof_shape: bind-only; escape_witness: none.
    consumers: torus_scale; direct frozen dependencies: partialTraceRight.
  torus_scale: proof_shape: bind-only; escape_witness: none.
    consumers: value; direct frozen dependencies: partialTraceRight.
  RowFormula.row_formula: proof_shape: bind-only; escape_witness: none.
    consumers: Group.transfer_rep; direct frozen dependencies: sum_fin_cons.
  Group.perm_left: proof_shape: bind-only; escape_witness: none.
    consumers: Group.perm_right, Group.perm, Group.closed_rep; direct frozen dependencies: none.
  Group.perm_right: proof_shape: bind-only; escape_witness: none.
    consumers: Group.perm, Group.closed_rep; direct frozen dependencies: none.
  Group.perm_cmul: proof_shape: bind-only; escape_witness: none.
    consumers: Group.K_mul; direct frozen dependencies: none.
  Group.K_mul: proof_shape: bind-only; escape_witness: none.
    consumers: Group.rep_conv; direct frozen dependencies: none.
  Group.conv_apply: proof_shape: bind-only; escape_witness: none.
    consumers: Group.rep_conv, Group.conv_c, Group.conv_c2; direct frozen dependencies: none.
  Group.rep_conv: proof_shape: bind-only; escape_witness: none.
    consumers: Group.rep_four; direct frozen dependencies: none.
  Group.conv_c: proof_shape: bind-only; escape_witness: none.
    consumers: Group.rep_four; direct frozen dependencies: none.
  Group.conv_c2: proof_shape: bind-only; escape_witness: none.
    consumers: Group.rep_four; direct frozen dependencies: none.
  Group.trace_rep_c4: proof_shape: bind-only; escape_witness: none.
    consumers: Group.rep_four; direct frozen dependencies: none.
  Group.rep_four: proof_shape: bind-only; escape_witness: none.
    consumers: Group.torus_value; direct frozen dependencies: none.
  Group.closed_rep: proof_shape: bind-only; escape_witness: none.
    consumers: Group.transfer_rep; direct frozen dependencies: none.
  Group.transfer_rep: proof_shape: bind-only; escape_witness: none.
    consumers: Group.torus_value; direct frozen dependencies: sum_fin_cons.
  Group.torus_value: proof_shape: bind-only; escape_witness: none.
    consumers: value; direct frozen dependencies: sum_fin_cons.
  value: proof_shape: bind-only; escape_witness: none.
    consumers: negative; direct frozen dependencies: sum_fin_cons, shift, partialTraceRight.
  negative: proof_shape: bind-only; escape_witness: none.
    consumers: result; direct frozen dependencies: sum_fin_cons, shift, partialTraceRight.
  result: proof_shape: bind-only; escape_witness: none.
    consumers: settling result; direct frozen dependencies: sum_fin_cons, shift, partialTraceRight,
      unitVector, dot_star_self.
-/

import D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays


open scoped BigOperators
namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support

private theorem sum_split {R A B S : Type*} [Fintype R] [DecidableEq R] [Fintype A] [Fintype B]
    [AddCommMonoid S] (f : (R → A) → (R → B) → S) :
    (∑ x : R → A × B, f (fun r => (x r).1) (fun r => (x r).2)) =
      ∑ a, ∑ b, f a b := by
  classical
  calc
    _ = ∑ p : (R → A) × (R → B), f p.1 p.2 :=
      Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow R (fun _ => A) (fun _ => B))
        _ (fun p => f p.1 p.2) (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

private theorem sum_unshifted {R A C S : Type*} [Fintype R] [DecidableEq R] [Fintype A] [Fintype C]
    [CommSemiring S] (f : R → (R → A) → C → S) :
    (∑ x : R → A × C, ∏ r, f r (fun i => (x i).1) (x r).2) =
      ∑ a : R → A, ∏ r, ∑ c : C, f r a c := by
  classical
  rw [show (∑ x : R → A × C, ∏ r, f r (fun i => (x i).1) (x r).2) =
    ∑ a : R → A, ∑ c : R → C, ∏ r, f r a (c r) from sum_split (fun a c => ∏ r, f r a (c r))]
  apply Finset.sum_congr rfl
  intro a _
  exact (Fintype.prod_sum _).symm


private theorem trace_four {B S : Type*} [Fintype B] [DecidableEq B] [CommSemiring S]
    (M : Matrix B B S) :
    Matrix.trace (M ^ 4) = ∑ b : Fin 4 → B, ∏ i : Fin 4, M (b i) (b ((i + 1))) := by
  classical
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  simp only [D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection.sum_fin_cons, Fintype.sum_unique, Fin.prod_univ_four,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  change (∑ i, ∑ j, ∑ k, ∑ l, M i j * (M j k * (M k l * M l i))) =
    ∑ i, ∑ j, ∑ k, ∑ l, M i j * M j k * M k l * M l i
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  ring

private def transfer {A B S : Type*} [Fintype A] [CommSemiring S]
    (V : A → B → A → B → S) : Matrix (Fin 4 → B) (Fin 4 → B) S :=
  Matrix.of fun b c => ∑ a : Fin 4 → A, ∏ j, V (a j) (b j) (a ((j + 1))) (c j)

private def torus {A B S : Type*} [Fintype A] [Fintype B] [CommSemiring S]
    (V : A → B → A → B → S) : S :=
  ∑ a : Fin 4 → Fin 4 → A, ∑ b : Fin 4 → Fin 4 → B,
    ∏ i, ∏ j, V (a i j) (b i j) (a i ((j + 1))) (b ((i + 1)) j)

private theorem torus_transfer {A B S : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    [CommSemiring S] (V : A → B → A → B → S) :
    torus V = Matrix.trace ((transfer V) ^ 4) := by
  classical
  rw [trace_four]
  unfold torus transfer
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact (Fintype.prod_sum (fun (i : Fin 4) (a : Fin 4 → A) => ∏ j, V (a j) (b i j) (a ((j + 1))) (b ((i + 1)) j))).symm

end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support


open D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse (shift)
open D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction (unitVector)

noncomputable section

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation

/-- The replica invariant `E_n^(q)` of Gadde–Jain–Krishna–Kulkarni–Sharma (arXiv:2308.16247, Eqs. (1.10)–(1.11)):
`n^(q-1)` replicas on the torus `(ℤ/n)^(q-1)`; the index of party `a` is contracted with the replica translated
along coordinate `a` (`shift`), and the last party `q - 1` is unshifted. Local spaces are arbitrary finite types. -/
def E (n q : ℕ) [NeZero n] {L : Fin q → Type*} [∀ a, Fintype (L a)]
    (ψ : ((a : Fin q) → L a) → ℂ) : ℂ :=
  ∑ x : (Fin (q - 1) → ZMod n) → ((a : Fin q) → L a),
    ∏ r : Fin (q - 1) → ZMod n, star (ψ (x r)) * ψ (fun a => x (shift n q a r) a)

/-- A normalized pure state. -/
def IsUnitState {q : ℕ} {L : Fin q → Type*} [∀ a, Fintype (L a)] (ψ : ((a : Fin q) → L a) → ℂ) : Prop :=
  ∑ x, Complex.normSq (ψ x) = 1

/-- The positivity question of arXiv:2308.16247, Section 7: for every `q, n ≥ 2`, all finite local spaces and every
normalized pure state, `E_n^(q)` is a positive real number. -/
def claim : Prop :=
  ∀ (n q : ℕ) [NeZero n], 2 ≤ n → 2 ≤ q →
    ∀ (L : Fin q → Type) [∀ a, Fintype (L a)] (ψ : ((a : Fin q) → L a) → ℂ),
      IsUnitState ψ → 0 < (E n q ψ).re ∧ (E n q ψ).im = 0

end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
open scoped BigOperators
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

-- Determinant owner gives the alternating sign on bijections and zero on repetitions.
private def eps (x : Fin 3 → Fin 3) : ℤ :=
  Matrix.det ((1 : Matrix (Fin 3) (Fin 3) ℤ).submatrix x id)

private def psi (x : Fin 3 → Fin 3) : ℂ := (eps x : ℂ) / (Real.sqrt 6 : ℂ)



private theorem eps_square_sum : (∑ x : Fin 3 → Fin 3, eps x ^ 2) = 6 := by
  exact Eq.symm ((fun {a b} => Int.neg_inj.mp) rfl)

theorem unit_norm_iff {ι : Type*} [Fintype ι] (φ : ι → ℂ) :
    unitVector φ ↔ ∑ x, Complex.normSq (φ x) = 1 := by
  have he : star φ ⬝ᵥ φ = ((∑ x, Complex.normSq (φ x) : ℝ) : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.dot_star_self φ)
  unfold unitVector
  rw [he]
  exact_mod_cast (Iff.rfl : (∑ x, Complex.normSq (φ x) = 1) ↔ _)

private theorem psi_unit : unitVector psi := by
  classical
  apply (unit_norm_iff psi).mpr
  have hx (x : Fin 3 → Fin 3) : Complex.normSq (psi x) = (eps x : ℝ)^2 / 6 := by
    simp [psi, Complex.normSq_apply, pow_two]
  simp_rw [hx]
  rw [← Finset.sum_div]
  have h : (∑ x : Fin 3 → Fin 3, (eps x : ℝ)^2) = 6 := by
    exact_mod_cast eps_square_sum
  rw [h]
  norm_num

private theorem eps_gram (a b c d : Fin 3) :
    (∑ k : Fin 3, eps ![a,b,k] * eps ![c,d,k]) =
    (if a = c ∧ b = d then 1 else 0) - (if a = d ∧ b = c then 1 else 0) := by
  convert cross_dot_cross (Pi.single a (1 : ℤ))
    (Pi.single b (1 : ℤ)) (Pi.single c (1 : ℤ))
    (Pi.single d (1 : ℤ)) using 1
  · change (∑ k : Fin 3, eps ![a,b,k] * eps ![c,d,k]) =
      ∑ k : Fin 3, crossProduct (Pi.single a (1 : ℤ)) (Pi.single b (1 : ℤ)) k *
        crossProduct (Pi.single c (1 : ℤ)) (Pi.single d (1 : ℤ)) k
    apply Finset.sum_congr rfl
    intro k _
    apply congrArg₂ (· * ·)
    · fin_cases a <;> fin_cases b <;> fin_cases k <;> decide
    · fin_cases c <;> fin_cases d <;> fin_cases k <;> decide
  · simp [Pi.single_apply, mul_ite, ← ite_and, and_comm, eq_comm]

end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
end

open D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse (shift)
open D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction (unitVector)
namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 0


private def gridEquiv : (Fin 2 → ZMod 4) ≃ (Fin 4 × Fin 4) :=
  (finTwoArrowEquiv (ZMod 4)).trans (Equiv.prodComm _ _)

private theorem shift_grid2 (r : Fin 2 → ZMod 4) : shift 4 3 2 r = r := by
  exact List.ofFn_inj.mp rfl

private def stateEquiv : (Fin 3 → Fin 3) ≃ ((Fin 3 × Fin 3) × Fin 3) :=
  (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (finTwoArrowEquiv (Fin 3))).trans
      (Equiv.prodAssoc _ _ _).symm)

private def rho (φ : (Fin 3 → Fin 3) → ℂ) (a b c d : Fin 3) : ℂ :=
  D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight
    (Matrix.vecMulVec (fun p : (Fin 3 × Fin 3) × Fin 3 => star (φ ![p.1.1,p.1.2,p.2]))
      (fun p : (Fin 3 × Fin 3) × Fin 3 => φ ![p.1.1,p.1.2,p.2])) (a,b) (c,d)

private theorem trace_party (φ : (Fin 3 → Fin 3) → ℂ) :
    E 4 3 φ = ∑ ab : (Fin 2 → ZMod 4) → Fin 3 × Fin 3, ∏ r : (Fin 2 → ZMod 4),
      rho φ (ab r).1 (ab r).2 (ab (shift 4 3 0 r)).1 (ab (shift 4 3 1 r)).2 := by
  classical
  unfold E
  let e := Equiv.piCongrRight (fun _ : (Fin 2 → ZMod 4) => stateEquiv)
  rw [← Equiv.sum_comp e.symm]
  have h (x : (Fin 2 → ZMod 4) → (Fin 3 × Fin 3) × Fin 3) :
    (∏ r : (Fin 2 → ZMod 4), star (φ (e.symm x r)) *
      φ (fun a => e.symm x (shift 4 3 a r) a)) =
    ∏ r : (Fin 2 → ZMod 4), star (φ ![(x r).1.1,(x r).1.2,(x r).2]) *
      φ ![(x (shift 4 3 0 r)).1.1,(x (shift 4 3 1 r)).1.2,(x r).2] := by
    apply Finset.prod_congr rfl; intro r _
    congr 2
    funext a
    fin_cases a
    · rfl
    · rfl
    · change (x (shift 4 3 2 r)).2 = (x r).2
      rw [shift_grid2]
  simp_rw [h]
  exact sum_unshifted (fun (r : (Fin 2 → ZMod 4)) (ab : (Fin 2 → ZMod 4) → Fin 3 × Fin 3) (k : Fin 3) => star (φ ![(ab r).1,(ab r).2,k]) *
    φ ![(ab (shift 4 3 0 r)).1,(ab (shift 4 3 1 r)).2,k])

private theorem rep_eta (r : (Fin 2 → ZMod 4)) : ![r 0, r 1] = r := by
  exact List.ofFn_inj.mp rfl

private theorem shift_vec0 (r : (Fin 2 → ZMod 4)) : shift 4 3 0 r = ![r 0 + 1,r 1] := by
  exact List.ofFn_inj.mp rfl

private theorem shift_vec1 (r : (Fin 2 → ZMod 4)) : shift 4 3 1 r = ![r 0,r 1 + 1] := by
  exact List.ofFn_inj.mp rfl

private theorem E_torus (φ : (Fin 3 → Fin 3) → ℂ) : E 4 3 φ = torus (rho φ) := by
  classical
  rw [trace_party]
  let e : ((Fin 2 → ZMod 4) → Fin 3 × Fin 3) ≃
    ((Fin 4 → Fin 4 → Fin 3) × (Fin 4 → Fin 4 → Fin 3)) :=
    (Equiv.piCongrLeft (fun _ : (Fin 4 × Fin 4) => Fin 3 × Fin 3) gridEquiv).trans
      ((Equiv.arrowProdEquivProdArrow (Fin 4 × Fin 4) (fun _ => Fin 3) (fun _ => Fin 3)).trans
        (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.curry _ _ _)))
  unfold torus
  rw [← Fintype.sum_prod_type (fun p : (Fin 4 → Fin 4 → Fin 3) ×
    (Fin 4 → Fin 4 → Fin 3) => ∏ i, ∏ j,
      rho φ (p.1 i j) (p.2 i j) (p.1 i ((j + 1))) (p.2 ((i + 1)) j))]
  apply Fintype.sum_equiv e _ _
  intro ab
  rw [← Fintype.prod_prod_type (fun p : (Fin 4 × Fin 4) =>
    rho φ ((e ab).1 p.1 p.2) ((e ab).2 p.1 p.2)
      ((e ab).1 p.1 ((p.2 + 1))) ((e ab).2 (p.1 + 1) p.2))]
  apply Fintype.prod_equiv gridEquiv
  intro r
  change rho φ (ab r).1 (ab r).2 (ab (shift 4 3 0 r)).1 (ab (shift 4 3 1 r)).2 =
    rho φ (ab ![r 0,r 1]).1 (ab ![r 0,r 1]).2
      (ab ![r 0 + 1,r 1]).1 (ab ![r 0,r 1 + 1]).2
  rw [rep_eta, shift_vec0, shift_vec1]

end
end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
open scoped BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
private def vertex {A : Type*} [DecidableEq A] (a b c d : A) : ℤ :=
  ((1 : Matrix (A × A) (A × A) ℤ) -
    Equiv.Perm.permMatrix ℤ (Equiv.prodComm A A)) (a, b) (c, d)

private theorem vertex_apply {A : Type*} [DecidableEq A] (a b c d : A) :
    vertex a b c d =
      (1 : Matrix A A ℤ) a c * (1 : Matrix A A ℤ) b d -
        (1 : Matrix A A ℤ) a d * (1 : Matrix A A ℤ) b c := by
  simp [vertex, Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, mul_ite, ← ite_and, and_comm]

private theorem rho_psi (a b c d : Fin 3) : rho psi a b c d = (vertex a b c d : ℂ) / 6 := by
  have h6 : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have term (k : Fin 3) : star (psi ![a,b,k]) * psi ![c,d,k] =
      ((eps ![a,b,k] * eps ![c,d,k] : ℤ) : ℂ) / 6 := by
    simp only [psi, Complex.star_def, map_div₀, map_intCast, Complex.conj_ofReal]
    rw [div_mul_div_comm, ← pow_two, h6, Int.cast_mul]
  change (∑ k : Fin 3, star (psi ![a,b,k]) * psi ![c,d,k]) = _
  simp_rw [term]
  rw [← Finset.sum_div, ← Int.cast_sum, eps_gram]
  simp [vertex, Matrix.one_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, Prod.mk.injEq, and_comm]


private theorem torus_scale : D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support.torus (rho psi) =
    ((D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support.torus (vertex (A := Fin 3)) : ℤ) : ℂ) / (6 : ℂ)^16 := by
  classical
  unfold D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support.torus
  simp_rw [rho_psi, Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [← Int.cast_prod, ← Finset.sum_div, ← Int.cast_sum]
  norm_num [← pow_mul]

end
end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.RowFormula
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private def closed (b c : Fin 4 → Fin 3) : ℤ :=
    -((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 0) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 3)) +
    ((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 0) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 3)) +
    ((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 0) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 3)) +
    ((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 3) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 0)) +
    ((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 0) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 3)) +
    ((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 0) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 3) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 1)) +
    ((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 0) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 3) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 2)) +
    -((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 0) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 3)) +
    -((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 3) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 0)) +
    -((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 3) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 0)) +
    -((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 0) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 3) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 1)) +
    ((1 : Matrix (Fin 3) (Fin 3) ℤ) (b 0) (c 1) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 1) (c 2) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 2) (c 3) * (1 : Matrix (Fin 3) (Fin 3) ℤ) (b 3) (c 0))

private theorem row_formula (b c : Fin 4 → Fin 3) : transfer (vertex (A := Fin 3)) b c = closed b c := by
  unfold transfer
  simp only [Matrix.of_apply, D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection.sum_fin_cons, Fintype.sum_unique, Fin.prod_univ_four]
  change (∑ a0 : Fin 3, ∑ a1 : Fin 3, ∑ a2 : Fin 3, ∑ a3 : Fin 3,
    vertex a0 (b 0) a1 (c 0) * vertex a1 (b 1) a2 (c 1) *
    vertex a2 (b 2) a3 (c 2) * vertex a3 (b 3) a0 (c 3)) = _
  simp_rw [vertex_apply]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp [Matrix.one_apply, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq, closed]
  simp only [← ite_and, and_assoc, and_left_comm, and_comm]
  have scale (p : Prop) [Decidable p] : (if p then (3 : ℤ) else 0) =
      3 * (if p then 1 else 0) := by
    exact (mul_boole p (3 : ℤ)).symm
  simp only [scale]
  ring
end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.RowFormula

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Group
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
private def permData : Array (Fin 4 → Fin 4) := #[![0,1,2,3],![0,1,3,2],![0,2,1,3],![0,2,3,1],![0,3,1,2],![0,3,2,1],![1,0,2,3],![1,0,3,2],![1,2,0,3],![1,2,3,0],![1,3,0,2],![1,3,2,0],![2,0,1,3],![2,0,3,1],![2,1,0,3],![2,1,3,0],![2,3,0,1],![2,3,1,0],![3,0,1,2],![3,0,2,1],![3,1,0,2],![3,1,2,0],![3,2,0,1],![3,2,1,0]]
private def invData : Array (Fin 4 → Fin 4) := #[![0,1,2,3],![0,1,3,2],![0,2,1,3],![0,3,1,2],![0,2,3,1],![0,3,2,1],![1,0,2,3],![1,0,3,2],![2,0,1,3],![3,0,1,2],![2,0,3,1],![3,0,2,1],![1,2,0,3],![1,3,0,2],![2,1,0,3],![3,1,0,2],![2,3,0,1],![3,2,0,1],![1,2,3,0],![1,3,2,0],![2,1,3,0],![3,1,2,0],![2,3,1,0],![3,2,1,0]]
private def mulData : Array (Array (Fin 24)) := #[#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],#[1,0,4,5,2,3,7,6,10,11,8,9,18,19,20,21,22,23,12,13,14,15,16,17],#[2,3,0,1,5,4,12,13,14,15,16,17,6,7,8,9,10,11,19,18,22,23,20,21],#[3,2,5,4,0,1,13,12,16,17,14,15,19,18,22,23,20,21,6,7,8,9,10,11],#[4,5,1,0,3,2,18,19,20,21,22,23,7,6,10,11,8,9,13,12,16,17,14,15],#[5,4,3,2,1,0,19,18,22,23,20,21,13,12,16,17,14,15,7,6,10,11,8,9],#[6,7,8,9,10,11,0,1,2,3,4,5,14,15,12,13,17,16,20,21,18,19,23,22],#[7,6,10,11,8,9,1,0,4,5,2,3,20,21,18,19,23,22,14,15,12,13,17,16],#[8,9,6,7,11,10,14,15,12,13,17,16,0,1,2,3,4,5,21,20,23,22,18,19],#[9,8,11,10,6,7,15,14,17,16,12,13,21,20,23,22,18,19,0,1,2,3,4,5],#[10,11,7,6,9,8,20,21,18,19,23,22,1,0,4,5,2,3,15,14,17,16,12,13],#[11,10,9,8,7,6,21,20,23,22,18,19,15,14,17,16,12,13,1,0,4,5,2,3],#[12,13,14,15,16,17,2,3,0,1,5,4,8,9,6,7,11,10,22,23,19,18,21,20],#[13,12,16,17,14,15,3,2,5,4,0,1,22,23,19,18,21,20,8,9,6,7,11,10],#[14,15,12,13,17,16,8,9,6,7,11,10,2,3,0,1,5,4,23,22,21,20,19,18],#[15,14,17,16,12,13,9,8,11,10,6,7,23,22,21,20,19,18,2,3,0,1,5,4],#[16,17,13,12,15,14,22,23,19,18,21,20,3,2,5,4,0,1,9,8,11,10,6,7],#[17,16,15,14,13,12,23,22,21,20,19,18,9,8,11,10,6,7,3,2,5,4,0,1],#[18,19,20,21,22,23,4,5,1,0,3,2,10,11,7,6,9,8,16,17,13,12,15,14],#[19,18,22,23,20,21,5,4,3,2,1,0,16,17,13,12,15,14,10,11,7,6,9,8],#[20,21,18,19,23,22,10,11,7,6,9,8,4,5,1,0,3,2,17,16,15,14,13,12],#[21,20,23,22,18,19,11,10,9,8,7,6,17,16,15,14,13,12,4,5,1,0,3,2],#[22,23,19,18,21,20,16,17,13,12,15,14,5,4,3,2,1,0,11,10,9,8,7,6],#[23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]]
private theorem perm_left : ∀ (p : Fin 24) (i : Fin 4), (fun p : Fin 24 => invData[p.val]!) p ((fun p : Fin 24 => permData[p.val]!) p i) = i := by decide +kernel
private theorem perm_right : ∀ (p : Fin 24) (i : Fin 4), (fun p : Fin 24 => permData[p.val]!) p ((fun p : Fin 24 => invData[p.val]!) p i) = i := by
  intro p
  exact Function.LeftInverse.rightInverse_of_card_le (perm_left p) (le_refl _)

private def perm (p : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := (fun p : Fin 24 => permData[p.val]!) p
  invFun := (fun p : Fin 24 => invData[p.val]!) p
  left_inv := perm_left p
  right_inv := perm_right p
private theorem perm_cmul : ∀ (p q : Fin 24) (i : Fin 4), perm ((fun p q : Fin 24 => (mulData[p.val]!)[q.val]!) p q) i = perm p (perm q i) := by decide +kernel

private def rowPerm (p : Fin 24) : Equiv.Perm (Fin 4 → Fin 3) :=
  (Equiv.piCongrLeft (fun _ : Fin 4 => Fin 3) (perm p)).symm

private theorem K_mul (p q : Fin 24) : (rowPerm p).permMatrix ℤ * (rowPerm q).permMatrix ℤ = (rowPerm ((fun p q : Fin 24 => (mulData[p.val]!)[q.val]!) p q)).permMatrix ℤ := by
  rw [← Matrix.permMatrix_mul]
  congr 1
  apply Equiv.ext
  intro b
  funext i
  exact congrArg b (perm_cmul p q i).symm

noncomputable section
private def conv (a b : Fin 24 → ℤ) : Fin 24 → ℤ :=
  Finsupp.mapDomain (fun pq : Fin 24 × Fin 24 => (mulData[pq.1.val]!)[pq.2.val]!)
    (Finsupp.equivFunOnFinite.symm (fun pq : Fin 24 × Fin 24 => a pq.1 * b pq.2))

end

private theorem conv_apply (a b : Fin 24 → ℤ) (r : Fin 24) :
    conv a b r = ∑ p, ∑ q, if (mulData[p.val]!)[q.val]! = r then a p * b q else 0 := by
  unfold conv
  rw [Finsupp.mapDomain_apply]
  simp only [Finsupp.single_apply]
  rw [Finsupp.sum_fintype]
  · exact Fintype.sum_prod_type
      (fun pq : Fin 24 × Fin 24 => if (mulData[pq.1.val]!)[pq.2.val]! = r then a pq.1 * b pq.2 else 0)
  · intro pq
    simp

private theorem rep_conv (a b : Fin 24 → ℤ) : (Fintype.linearCombination ℤ (fun p : Fin 24 => (rowPerm p).permMatrix ℤ)) (conv a b) = (Fintype.linearCombination ℤ (fun p : Fin 24 => (rowPerm p).permMatrix ℤ)) a * (Fintype.linearCombination ℤ (fun p : Fin 24 => (rowPerm p).permMatrix ℤ)) b := by
  simp only [Fintype.linearCombination_apply, conv_apply]
  simp only [Finset.sum_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, K_mul]
  simp_rw [ite_smul, zero_smul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  simp
private def cData : Array ℤ := #[-1,1,1,0,-1,1,1,0,0,0,0,0,-1,0,1,0,0,0,1,-1,-1,1,0,0]
private def c2Data : Array ℤ := #[7,-6,-6,4,8,-6,-6,6,4,0,-6,4,8,-6,-6,4,7,-6,-10,8,8,-6,-6,6]
private def c4Data : Array ℤ := #[786,-824,-824,864,864,-864,-824,864,864,-860,-904,864,864,-904,-864,864,950,-904,-860,864,864,-824,-904,864]
private theorem conv_c : conv (fun p : Fin 24 => cData[p.val]!) (fun p : Fin 24 => cData[p.val]!) = (fun p : Fin 24 => c2Data[p.val]!) := by funext r; rw [conv_apply]; revert r; decide +kernel
private theorem conv_c2 : conv (fun p : Fin 24 => c2Data[p.val]!) (fun p : Fin 24 => c2Data[p.val]!) = (fun p : Fin 24 => c4Data[p.val]!) := by funext r; rw [conv_apply]; revert r; decide +kernel
end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Group

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Group
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
private theorem trace_rep_c4 : Matrix.trace ((Fintype.linearCombination ℤ (fun p : Fin 24 => (rowPerm p).permMatrix ℤ)) (fun p : Fin 24 => c4Data[p.val]!)) = -1680 := by
  simp only [Fintype.linearCombination_apply, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.trace_permutation]
  simp_rw [Set.ncard_eq_toFinset_card']
  exact (fun {a b} => Int.eq_neg_comm.mp) rfl
private theorem rep_four : Matrix.trace (((Fintype.linearCombination ℤ (fun p : Fin 24 => (rowPerm p).permMatrix ℤ)) (fun p : Fin 24 => cData[p.val]!)) ^ 4) = -1680 := by
  rw [pow_mul _ 2 2, pow_two, pow_two]
  rw [← rep_conv, conv_c, ← rep_conv, conv_c2]
  exact trace_rep_c4

private theorem closed_rep (b d : Fin 4 → Fin 3) : D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.RowFormula.closed b d = (Fintype.linearCombination ℤ (fun p : Fin 24 => (rowPerm p).permMatrix ℤ)) (fun p : Fin 24 => cData[p.val]!) b d := by
  simp [D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.RowFormula.closed, Matrix.one_apply, Fintype.linearCombination_apply, cData,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, rowPerm, perm, permData,
    Fin.sum_univ_succ, Fin.forall_fin_succ, funext_iff,
    mul_ite, ← ite_and, and_assoc, and_left_comm, and_comm]
  have ind_mul (p q : Prop) [Decidable p] [Decidable q] :
      (if p ∧ q then (1 : ℤ) else 0) =
      (if p then 1 else 0) * (if q then 1 else 0) := by
    simpa only [one_mul] using
      (ite_zero_mul_ite_zero (P := p) (Q := q) (a := (1 : ℤ)) (b := 1)).symm
  simp only [ind_mul]
  ring

private theorem transfer_rep : transfer (vertex (A := Fin 3)) = (Fintype.linearCombination ℤ (fun p : Fin 24 => (rowPerm p).permMatrix ℤ)) (fun p : Fin 24 => cData[p.val]!) := by
  ext b d
  rw [D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.RowFormula.row_formula, closed_rep]

private theorem torus_value : torus (vertex (A := Fin 3)) = (-1680 : ℤ) := by
  rw [torus_transfer, transfer_rep]
  exact rep_four
end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Group

namespace D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Support
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
private theorem value : E 4 3 psi = (-35 / 58773123072 : ℂ) := by
  rw [E_torus, torus_scale, D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.Group.torus_value]
  norm_num
private theorem negative : (E 4 3 psi).re < 0 := by
  rw [value]
  norm_num
theorem result : ¬ claim := by
  intro h
  have hp := (h 4 3 (by decide) (by decide) (fun _ => Fin 3) psi ((unit_norm_iff psi).mp psi_unit)).1
  exact (lt_asymm hp negative)
end D5.S3.Quantum.Information.MultiEntropyPositivityRefutation
