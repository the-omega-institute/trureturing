/- GID: D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.claim; result=D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.result; claim=D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation.claim
   digest: The randomized K_(3,3) graph state has larger negativity at p = 97/100 than at p = 1. -/

/-
proof_shape: Qubits, czPhase, plusState, graphState, rgState, partialTranspose, negativity:
  definition (computational basis, CZ phases, the product state |+>^n, graph states, the
  randomized graph state, partial transposition by Finset.piecewise, and the negativity with
  the frozen trace norm)
proof_shape: claim: definition (published open question, read as a universal statement over
  graphs, bipartitions and 0 <= p <= q <= 1)
proof_shape: k33, partA: definition (the complete bipartite graph K_(3,3) on Fin 6 and one of
  its parts)
proof_shape: edges9, mism, xi, enc, tab, qvals, nvals, uv, parA, sgnB, u00, u11, u01, u10:
  private definition (edge list, CZ mismatch indicator, integer numerator of the partially
  transposed state, and integer test vectors)
proof_shape: result: content (kernel evaluation, as local steps, of the edge set, of the
  orthogonality, norms and quadratic forms of the fourteen test vectors against the numerator
  at p = 97/100, of the diagonal entries, of the positive decomposition at p = 1 and of the
  norm of the subtracted vector; the closed form of the partial transpose at both values of
  p; the lower bound 2 < ||X||_1 from the unitary I - 2P built on the test vectors; and the
  upper bound ||X_1||_1 <= 2 from the positive decomposition and the triangle inequality)
escape_witness: result (form (2) of §3.2: both trace-norm bounds are produced by the
  closed-form evaluation, the explicit unitary witness and the positive decomposition; no
  existing statement gives them)
admission_basis: open-problem-resolution (issue #12382; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_eq_max_re_tr_U
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_add_le
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_neg
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm_of_posSemidef
-/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation

open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped ComplexOrder

/-- Computational-basis labels of `n` qubits. -/
abbrev Qubits (n : ℕ) := Fin n → Fin 2

/-- The diagonal entry `(-1)^{x_a x_b}` of `CZ` on the edge `e = {a, b}` at the basis state `x`. -/
def czPhase {n : ℕ} (e : Sym2 (Fin n)) (x : Qubits n) : ℂ :=
  Sym2.lift ⟨fun a b => (-1) ^ ((x a).val * (x b).val), fun a b => by
    dsimp only; rw [Nat.mul_comm]⟩ e

/-- The product state `|+⟩^{⊗n}` in the computational basis. -/
noncomputable def plusState (n : ℕ) : Qubits n → ℂ := fun _ => (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)

/-- The graph state `∏_{e ∈ F} CZ_e |+⟩^{⊗n}` of an edge set `F`; the `CZ` gates are diagonal in
the computational basis, so their product acts entrywise. -/
noncomputable def graphState {n : ℕ} (F : Finset (Sym2 (Fin n))) : Qubits n → ℂ :=
  fun x => (∏ e ∈ F, czPhase e x) * plusState n x

/-- The randomized graph state `ρ_G^p = Σ_F p^{|E_F|} (1-p)^{|E_G \ E_F|} |F⟩⟨F|`, the sum over
the spanning subgraphs `F` of `G`. -/
noncomputable def rgState {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ F ∈ G.edgeFinset.powerset,
    (((p ^ F.card * (1 - p) ^ (G.edgeFinset \ F).card : ℝ)) : ℂ) •
      vecMulVec (graphState F) (star (graphState F))

/-- The partial transposition on the qubits in `A`:
`⟨x_A x_B| M^{Γ_A} |y_A y_B⟩ = ⟨y_A x_B| M |x_A y_B⟩`, where `A.piecewise y x` takes the
coordinates in `A` from `y` and the others from `x`. -/
def partialTranspose {n : ℕ} (A : Finset (Fin n)) (M : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  fun x y => M (A.piecewise y x) (A.piecewise x y)

/-- The negativity `N(ρ) = (‖ρ^{Γ_A}‖ - 1) / 2` with the trace norm `Tr √(X† X)`. -/
noncomputable def negativity {n : ℕ} (A : Finset (Fin n)) (ρ : Matrix (Qubits n) (Qubits n) ℂ) :
    ℝ :=
  (traceNorm (partialTranspose A ρ) - 1) / 2

/-- The open question of Wu et al. (arXiv:1403.3828, Section V), read as a universal statement:
the negativity across every bipartition increases monotonically in the randomness `p`. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (p q : ℝ),
    0 ≤ p → p ≤ q → q ≤ 1 → negativity A (rgState G p) ≤ negativity A (rgState G q)

/-- `K_{3,3}` on `Fin 6`: every even vertex is adjacent to every odd vertex. -/
def k33 : SimpleGraph (Fin 6) where
  Adj a b := a.val % 2 ≠ b.val % 2
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel k33.Adj := fun a b => inferInstanceAs (Decidable (a.val % 2 ≠ b.val % 2))

/-- One part of `K_{3,3}`. -/
def partA : Finset (Fin 6) := {0, 2, 4}

private def edges9 : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(0, 3), s(0, 5), s(2, 1), s(2, 3), s(2, 5), s(4, 1), s(4, 3), s(4, 5)}


private def mism (e : Sym2 (Fin 6)) (u v : Qubits 6) : Bool :=
  Sym2.lift ⟨fun a b => decide ((u a).val * (u b).val ≠ (v a).val * (v b).val), fun a b => by
    dsimp only; rw [Nat.mul_comm (u a).val, Nat.mul_comm (v a).val]⟩ e

private def xi (a b : ℤ) (x y : Qubits 6) : ℤ :=
  ∏ e ∈ edges9, if mism e (partA.piecewise y x) (partA.piecewise x y) then a else b


/-- The binary index of a basis label. -/
private def enc (x : Qubits 6) : ℕ := ∑ k : Fin 6, (x k).val * 2 ^ (k : ℕ)

/-- The fourteen pairwise orthogonal integer vectors of the lower-bound certificate, as tables
indexed by `enc`. -/
private def tab : Fin 14 → List ℤ := ![
  [-200, 183, 183, 172, 183, -168, 172, 163, 183, 172, -168, 163, 172, 163, 163, -158, 183, -168,
    172, 163, -168, 154, 163, 154, 172, 163, 163, -158, 163, 154, -158, 153, 183, 172, -168, 163,
    172, 163, 163, -158, -168, 163, 154, 154, 163, -158, 154, 153, 172, 163, 163, -158, 163, 154,
    -158, 153, 163, -158, 154, 153, -158, 153, 153, 152],
  [0, -101, 101, 0, -101, 153, 0, -80, 101, 0, -153, 80, 0, -80, 80, 0, -101, 153, 0, -80, 153,
    -200, -80, -154, 0, -80, 80, 0, -80, -154, 0, -68, 101, 0, -153, 80, 0, -80, 80, 0, -153, 80,
    200, 154, 80, 0, 154, 68, 0, -80, 80, 0, -80, -154, 0, -68, 80, 0, 154, 68, 0, -68, 68, 0],
  [173248200, 36410922, 36410922, 13017551, 36410922, -39874478, 13017551, 2619971, 36410922,
    13017551, -39874478, 2619971, 13017551, 2619971, 2619971, 3445252, 36410922, -39874478,
    13017551, 2619971, -39874478, 32075365, 2619971, -3445764, 13017551, 2619971, 2619971,
    3445252, 2619971, -3445764, 3445252, -63225353, 36410922, 13017551, -39874478, 2619971,
    13017551, 2619971, 2619971, 3445252, -39874478, 2619971, 32075365, -3445764, 2619971, 3445252,
    -3445764, -63225353, 13017551, 2619971, 2619971, 3445252, 2619971, -3445764, 3445252,
    -63225353, 2619971, 3445252, -3445764, -63225353, 3445252, -63225353, -63225353, -112608514],
  [-20325286629000, -3873544741143, -3873544741143, -314505960998, -3873544741143,
    -3546922863955, -314505960998, 1312678673551, -3873544741143, -314505960998, -3546922863955,
    1312678673551, -314505960998, 1312678673551, 1312678673551, 5395137301109, -3873544741143,
    -3546922863955, -314505960998, 1312678673551, -3546922863955, 12085880441216, 1312678673551,
    2329827394947, -314505960998, 1312678673551, 1312678673551, 5395137301109, 1312678673551,
    2329827394947, 5395137301109, -3562749438019, -3873544741143, -314505960998, -3546922863955,
    1312678673551, -314505960998, 1312678673551, 1312678673551, 5395137301109, -3546922863955,
    1312678673551, 12085880441216, 2329827394947, 1312678673551, 5395137301109, 2329827394947,
    -3562749438019, -314505960998, 1312678673551, 1312678673551, 5395137301109, 1312678673551,
    2329827394947, 5395137301109, -3562749438019, 1312678673551, 5395137301109, 2329827394947,
    -3562749438019, 5395137301109, -3562749438019, -3562749438019, -11082038881661],
  [0, 23114709, -23114709, 0, 23114709, 1538473, 0, 2561770, -23114709, 0, -1538473, -2561770, 0,
    2561770, -2561770, 0, 23114709, 1538473, 0, 2561770, 1538473, -28318200, 2561770, -1113164, 0,
    2561770, -2561770, 0, 2561770, -1113164, 0, -9628188, -23114709, 0, -1538473, -2561770, 0,
    2561770, -2561770, 0, -1538473, -2561770, 28318200, 1113164, -2561770, 0, 1113164, 9628188, 0,
    2561770, -2561770, 0, 2561770, -1113164, 0, -9628188, -2561770, 0, 1113164, 9628188, 0,
    -9628188, 9628188, 0],
  [251354757177707544, -335706527255019767, -335706527255019767, 329497896739288314,
    -335706527255019767, -3416686958121411, 329497896739288314, 46706478892876215,
    -335706527255019767, 329497896739288314, -3416686958121411, 46706478892876215,
    329497896739288314, 46706478892876215, 46706478892876215, -34623370194362443,
    -335706527255019767, -3416686958121411, 329497896739288314, 46706478892876215,
    -3416686958121411, 367340649065602584, 46706478892876215, -549330075486266421,
    329497896739288314, 46706478892876215, 46706478892876215, -34623370194362443,
    46706478892876215, -549330075486266421, -34623370194362443, 127803327076641333,
    -335706527255019767, 329497896739288314, -3416686958121411, 46706478892876215,
    329497896739288314, 46706478892876215, 46706478892876215, -34623370194362443,
    -3416686958121411, 46706478892876215, 367340649065602584, -549330075486266421,
    46706478892876215, -34623370194362443, -549330075486266421, 127803327076641333,
    329497896739288314, 46706478892876215, 46706478892876215, -34623370194362443,
    46706478892876215, -549330075486266421, -34623370194362443, 127803327076641333,
    46706478892876215, -34623370194362443, -549330075486266421, 127803327076641333,
    -34623370194362443, 127803327076641333, 127803327076641333, -24899158894643781],
  [0, 0, 0, -200, 0, 0, 200, 0, 0, 200, 0, 0, -200, 0, 0, 0, 0, 0, 0, -194, 0, 0, 194, 0, 0, 194,
    0, 0, -194, 0, 0, 0, 0, 0, 0, -194, 0, 0, 194, 0, 0, 194, 0, 0, -194, 0, 0, 0, 0, 0, 0, 188,
    0, 0, -188, 0, 0, -188, 0, 0, 188, 0, 0, 0],
  [0, 0, 0, 200, 0, 0, -200, 0, 0, 200, 0, 388, -200, 0, -388, 0, 0, 0, 0, 194, 0, 0, -194, 0, 0,
    194, 0, -376, -194, 0, 376, 0, 0, -400, 0, -194, 400, 0, 194, 0, 0, -194, 0, 0, 194, 0, 0, 0,
    0, -388, 0, 188, 388, 0, -188, 0, 0, 188, 0, 0, -188, 0, 0, 0],
  [0, 0, 0, 200, 0, 0, 200, 388, 0, -200, 0, 0, -200, -388, 0, 0, 0, 0, -400, -194, 0, 0, -194,
    0, 400, 194, 0, 0, 194, 0, 0, 0, 0, 0, 0, 194, 0, 0, 194, -376, 0, -194, 0, 0, -194, 376, 0,
    0, 0, 0, -388, 188, 0, 0, 188, 0, 388, -188, 0, 0, -188, 0, 0, 0],
  [0, 0, 0, -200, 0, 0, -200, -388, 0, -200, 0, -388, -200, -388, -388, 752, 0, 0, 400, 194, 0,
    0, 194, 0, 400, 194, 776, -376, 194, 0, -376, 0, 0, 400, 0, 194, 400, 776, 194, -376, 0, 194,
    0, 0, 194, -376, 0, 0, -800, -388, -388, 188, -388, 0, 188, 0, -388, 188, 0, 0, 188, 0, 0, 0],
  [0, 0, 0, -78, 0, 0, -78, -138, 0, 78, 0, 0, 78, 138, 0, 0, 0, 0, -78, -138, 0, 0, -138, -194,
    78, 138, 0, 0, 138, 194, 0, 0, 0, 0, 0, -73, 0, 0, -73, 137, 0, 73, 0, 0, 73, -137, 0, 0, 0,
    0, -73, 137, 0, 0, 137, -200, 73, -137, 0, 0, -137, 200, 0, 0],
  [0, 0, 0, -78, 0, 0, -78, -138, 0, -78, 0, -146, -78, -138, -146, 274, 0, 0, -78, -138, 0, 0,
    -138, -194, -78, -138, -146, 274, -138, -194, 274, -400, 0, 156, 0, 73, 156, 276, 73, -137, 0,
    73, 0, 0, 73, -137, 0, 0, 156, 276, 73, -137, 276, 388, -137, 200, 73, -137, 0, 0, -137, 200,
    0, 0],
  [0, 0, 0, -78, 0, 0, 78, 0, 0, -78, 0, -138, 78, 0, 138, 0, 0, 0, 0, -73, 0, 0, 73, 0, 0, -73,
    0, 137, 73, 0, -137, 0, 0, -78, 0, -138, 78, 0, 138, 0, 0, -138, 0, -194, 138, 0, 194, 0, 0,
    -73, 0, 137, 73, 0, -137, 0, 0, 137, 0, -200, -137, 0, 200, 0],
  [0, 0, 0, -78, 0, 0, -78, -146, 0, -78, 0, -138, -78, -146, -138, 274, 0, 0, 156, 73, 0, 0, 73,
    0, 156, 73, 276, -137, 73, 0, -137, 0, 0, -78, 0, -138, -78, -146, -138, 274, 0, -138, 0,
    -194, -138, 274, -194, -400, 156, 73, 276, -137, 73, 0, -137, 0, 276, -137, 388, 200, -137, 0,
    200, 0]]

/-- The quadratic forms `∑ x y, u_j x * u_j y * xi (-47) 50 y x`. -/
private def qvals : Fin 14 → ℤ := ![
  -88832070306295555490648, -1289164428973156143088, -92399602549079049151527843710018,
  -1325201601769972280692381743167651182285856, -4468653857435533524187987854528,
  -2775326186667105829147346831987213026124984896608192, -226898073033312000000,
  -680694219099936000000, -680694219099936000000, -2042082657299808000000, -641294061967010566800,
  -1923882185901031700400, -641294061967010566800, -1923882185901031700400]

/-- The squared norms `∑ x, u_j x ^ 2`. -/
private def nvals : Fin 14 → ℤ := ![
  1732738, 566900, 88059055060544967, 1396177653757198461773195880, 5505555739556100,
  3945699786146756529289859529314719704, 602464, 1807392, 1807392, 5422176, 450628, 1351884,
  450628, 1351884]

/-- The `j`-th certificate vector. -/
private def uv (j : Fin 14) (x : Qubits 6) : ℤ := (tab j).getD (enc x) 0

/-- Parity of the `A` part and the sign `(-1)^{|x_B|}` of the `B` part. -/
private def parA (x : Qubits 6) : ℕ := ((x 0).val + (x 2).val + (x 4).val) % 2

private def sgnB (x : Qubits 6) : ℤ := (-1) ^ ((x 1).val + (x 3).val + (x 5).val)

/-- The products of the parity states of `A` with `|+++⟩` and `|---⟩` on `B`, unnormalized. -/
private def u00 (x : Qubits 6) : ℤ := if parA x = 0 then 1 else 0

private def u11 (x : Qubits 6) : ℤ := if parA x = 1 then sgnB x else 0

private def u01 (x : Qubits 6) : ℤ := if parA x = 0 then sgnB x else 0

private def u10 (x : Qubits 6) : ℤ := if parA x = 1 then 1 else 0

set_option maxHeartbeats 2000000 in -- the seven kernel evaluations share this declaration
/-- The negativity of the randomized `K_{3,3}` state across its two parts is larger at
`p = 97/100` than at `p = 1`, so it is not monotone in `p`. -/
theorem result : ¬ claim := by
  intro hclaim
  have edgeFinset_k33 : k33.edgeFinset = edges9 := by decide +kernel
  have uv_ortho : ∀ i j : Fin 14, i ≠ j → ∑ x : Qubits 6, uv i x * uv j x = 0 := by
    decide +kernel
  have uv_norms : ∀ j : Fin 14, ∑ x : Qubits 6, uv j x * uv j x = nvals j := by
    decide +kernel
  have uv_quads : ∀ j : Fin 14,
      ∑ x : Qubits 6, ∑ y : Qubits 6, uv j x * uv j y * xi (-47) 50 y x = qvals j := by
    decide +kernel
  have xi_diag : ∀ x : Qubits 6, xi (-47) 50 x x = 50 ^ 9 ∧ xi (-1) 1 x x = 1 := by
    decide +kernel
  have decomp_one : ∀ x y : Qubits 6,
      2 * xi (-1) 1 x y + (u01 x - u10 x) * (u01 y - u10 y) =
        2 * (u00 x * u00 y + u11 x * u11 y) + (u01 x + u10 x) * (u01 y + u10 y) := by
    decide +kernel
  have w_norm : ∑ x : Qubits 6, (u01 x - u10 x) * (u01 x - u10 x) = 64 := by
    decide +kernel
  have closed : ∀ (p : ℝ) (x y : Qubits 6), rgState k33 p x y =
      ((((2 : ℝ) ^ 6)⁻¹ : ℝ) : ℂ) *
        ∏ e ∈ k33.edgeFinset, ((p : ℂ) * (czPhase e x * czPhase e y) + ((1 - p : ℝ) : ℂ)) := by
    intro p x y
    have hstar : ∀ (e : Sym2 (Fin 6)) (z : Qubits 6), star (czPhase e z) = czPhase e z := by
      intro e z
      induction e using Sym2.ind with
      | h a b => simp [czPhase]
    have hplus : plusState 6 x * star (plusState 6 y) = ((((2 : ℝ) ^ 6)⁻¹ : ℝ) : ℂ) := by
      simp only [plusState, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      rw [← mul_pow, ← mul_inv, Real.mul_self_sqrt (by norm_num), inv_pow]
    simp only [rgState, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, graphState,
      Pi.star_apply, star_mul', star_prod, hstar, smul_eq_mul]
    have key : ∀ F ∈ k33.edgeFinset.powerset,
        (((p ^ F.card * (1 - p) ^ (k33.edgeFinset \ F).card : ℝ)) : ℂ) *
          ((∏ e ∈ F, czPhase e x) * plusState 6 x *
            ((∏ e ∈ F, czPhase e y) * star (plusState 6 y))) =
        ((((2 : ℝ) ^ 6)⁻¹ : ℝ) : ℂ) * ((∏ e ∈ F, (p : ℂ) * (czPhase e x * czPhase e y)) *
          ∏ e ∈ k33.edgeFinset \ F, ((1 - p : ℝ) : ℂ)) := by
      intro F _
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
        ← hplus]
      push_cast
      ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.prod_add]
  have hcc : ∀ (e : Sym2 (Fin 6)) (u v : Qubits 6),
      czPhase e u * czPhase e v = if mism e u v then -1 else 1 := by
    intro e u v
    induction e using Sym2.ind with
    | h a b =>
      have h2 : ∀ i : Fin 2, i.val = 0 ∨ i.val = 1 := fun i => by omega
      simp only [czPhase, mism, Sym2.lift_mk]
      rcases h2 (u a) with h1 | h1 <;> rcases h2 (u b) with h3 | h3 <;>
        rcases h2 (v a) with h4 | h4 <;> rcases h2 (v b) with h5 | h5 <;> simp [h1, h3, h4, h5]
  have hcard : edges9.card = 9 := by decide
  have hX : ∀ (p : ℝ) (a b : ℤ), (b : ℂ) ≠ 0 → ((1 - 2 * p : ℝ) : ℂ) = (a : ℂ) / b →
      ∀ x y : Qubits 6, partialTranspose partA (rgState k33 p) x y =
        ((xi a b x y : ℤ) : ℂ) / (64 * (b : ℂ) ^ 9) := by
    intro p a b hb hab x y
    simp only [partialTranspose]
    rw [closed, edgeFinset_k33]
    have hfac : ∀ e ∈ edges9,
        (p : ℂ) * (czPhase e (partA.piecewise y x) * czPhase e (partA.piecewise x y)) +
            ((1 - p : ℝ) : ℂ) =
          ((if mism e (partA.piecewise y x) (partA.piecewise x y) then a else b : ℤ) : ℂ) / b := by
      intro e _
      rw [hcc]
      split_ifs
      · push_cast at hab ⊢
        rw [← hab]
        field_simp
        ring
      · push_cast
        field_simp
        ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib, Finset.prod_const, hcard, xi]
    push_cast
    field_simp
    ring
  -- the state at `p = 97/100`
  obtain ⟨X, hXdef⟩ : ∃ X, X = partialTranspose partA (rgState k33 (97 / 100)) := ⟨_, rfl⟩
  have hXe : ∀ x y, X x y = ((xi (-47) 50 x y : ℤ) : ℂ) / (64 * ((50 : ℤ) : ℂ) ^ 9) := by
    intro x y
    rw [hXdef]
    exact hX (97 / 100) (-47) 50 (by norm_num) (by push_cast; norm_num) x y
  obtain ⟨uc, huc⟩ : ∃ uc : Fin 14 → Qubits 6 → ℂ, uc = fun j x => ((uv j x : ℤ) : ℂ) :=
    ⟨_, rfl⟩
  have hdot : ∀ i j : Fin 14, uc i ⬝ᵥ uc j = if i = j then ((nvals j : ℤ) : ℂ) else 0 := by
    intro i j
    have hcast : uc i ⬝ᵥ uc j = ((∑ x : Qubits 6, uv i x * uv j x : ℤ) : ℂ) := by
      simp only [dotProduct, huc]
      push_cast
      rfl
    rw [hcast]
    split_ifs with h
    · subst h
      rw [uv_norms]
    · rw [uv_ortho i j h]
      simp
  have hnz : ∀ j : Fin 14, ((nvals j : ℤ) : ℂ) ≠ 0 := by
    intro j
    exact_mod_cast (show nvals j ≠ 0 by revert j; decide)
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Qubits 6) (Qubits 6) ℂ,
      P = ∑ j : Fin 14, (((nvals j : ℤ) : ℂ))⁻¹ • vecMulVec (uc j) (uc j) := ⟨_, rfl⟩
  have hVV : ∀ i j : Fin 14, vecMulVec (uc i) (uc i) * vecMulVec (uc j) (uc j) =
      if i = j then ((nvals j : ℤ) : ℂ) • vecMulVec (uc j) (uc j) else 0 := by
    intro i j
    rw [vecMulVec_mul_vecMulVec, hdot]
    split_ifs with h
    · subst h
      ext x y
      simp [vecMulVec_apply]
      ring
    · ext x y
      simp [vecMulVec_apply]
  have hPP : P * P = P := by
    rw [hPdef, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [Matrix.smul_mul, Matrix.mul_smul, hVV, if_neg (Ne.symm hj), smul_zero, smul_zero])
      (by simp)]
    rw [Matrix.smul_mul, Matrix.mul_smul, hVV, if_pos rfl, smul_smul, smul_smul]
    congr 1
    field_simp [hnz i]
  have hPh : Pᴴ = P := by
    rw [hPdef]
    simp only [conjTranspose_sum, conjTranspose_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    · simp
    · ext x y
      simp [vecMulVec_apply, huc, mul_comm]
  have hU : (1 - (2 : ℂ) • P) ∈ unitaryGroup (Qubits 6) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_sub, conjTranspose_one,
      conjTranspose_smul, hPh]
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hPP, star_ofNat, smul_smul]
    module
  have hle := (traceNorm_eq_max_re_tr_U X).2 ⟨⟨1 - (2 : ℂ) • P, hU⟩, rfl⟩
  have htrX : X.trace = 1 := by
    simp only [Matrix.trace, Matrix.diag, hXe]
    simp only [(xi_diag _).1]
    push_cast
    simp [Finset.sum_const, Finset.card_univ]
    norm_num
  have htrPX : (P * X).trace =
      ((∑ j : Fin 14, (qvals j : ℝ) / ((nvals j : ℝ) * (64 * 50 ^ 9)) : ℝ) : ℂ) := by
    rw [hPdef, Finset.sum_mul, Matrix.trace_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have htr : (vecMulVec (uc j) (uc j) * X).trace =
        ((∑ x : Qubits 6, ∑ y : Qubits 6, uv j x * uv j y * xi (-47) 50 y x : ℤ) : ℂ) /
          (64 * ((50 : ℤ) : ℂ) ^ 9) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, hXe, huc]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [htr, uv_quads]
    field_simp [hnz j]
    push_cast
    ring
  have hlow : 2 < traceNorm X := by
    have hre : (((1 - (2 : ℂ) • P) * X).trace).re =
        1 - 2 * ∑ j : Fin 14, (qvals j : ℝ) / ((nvals j : ℝ) * (64 * 50 ^ 9)) := by
      rw [sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, htrX,
        htrPX, smul_eq_mul]
      rw [show (1 : ℂ) - 2 * ((∑ j : Fin 14, (qvals j : ℝ) / ((nvals j : ℝ) * (64 * 50 ^ 9)) : ℝ)
          : ℂ) =
        ((1 - 2 * ∑ j : Fin 14, (qvals j : ℝ) / ((nvals j : ℝ) * (64 * 50 ^ 9)) : ℝ) : ℂ) by
          push_cast; ring, Complex.ofReal_re]
    have hnum : 1 - 2 * ∑ j : Fin 14, (qvals j : ℝ) / ((nvals j : ℝ) * (64 * 50 ^ 9)) > 2 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, qvals, nvals, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      norm_num
    exact lt_of_lt_of_le hnum (hre ▸ hle)
  -- the state at `p = 1`
  obtain ⟨X1, hX1def⟩ : ∃ X1, X1 = partialTranspose partA (rgState k33 1) := ⟨_, rfl⟩
  have hX1e : ∀ x y, X1 x y = ((xi (-1) 1 x y : ℤ) : ℂ) / 64 := by
    intro x y
    rw [hX1def, hX 1 (-1) 1 (by norm_num) (by push_cast; norm_num) x y]
    push_cast
    ring
  obtain ⟨cv, hcv⟩ : ∃ cv : (Qubits 6 → ℤ) → Qubits 6 → ℂ, cv = fun f x => ((f x : ℤ) : ℂ) :=
    ⟨_, rfl⟩
  have hpsd : ∀ f, (vecMulVec (cv f) (cv f)).PosSemidef := by
    intro f
    have h := posSemidef_vecMulVec_self_star (cv f)
    have hs : star (cv f) = cv f := by
      ext x
      simp [hcv]
    rwa [hs] at h
  obtain ⟨N1, hN1⟩ : ∃ N1 : Matrix (Qubits 6) (Qubits 6) ℂ,
      N1 = (1 / 128 : ℂ) • vecMulVec (cv fun x => u01 x - u10 x) (cv fun x => u01 x - u10 x) :=
    ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Qubits 6) (Qubits 6) ℂ,
      M = (1 / 64 : ℂ) • (vecMulVec (cv u00) (cv u00) + vecMulVec (cv u11) (cv u11)) +
        (1 / 128 : ℂ) • vecMulVec (cv fun x => u01 x + u10 x) (cv fun x => u01 x + u10 x) :=
    ⟨_, rfl⟩
  have hc64 : (0 : ℂ) ≤ 1 / 64 := by simp
  have hc128 : (0 : ℂ) ≤ 1 / 128 := by simp
  have hN1psd : N1.PosSemidef := by
    rw [hN1]
    exact (hpsd _).smul hc128
  have hMpsd : M.PosSemidef := by
    rw [hM]
    exact (((hpsd _).add (hpsd _)).smul hc64).add ((hpsd _).smul hc128)
  have hsplit : X1 = M + -N1 := by
    ext x y
    have hc : ((2 * xi (-1) 1 x y + (u01 x - u10 x) * (u01 y - u10 y) : ℤ) : ℂ) =
        ((2 * (u00 x * u00 y + u11 x * u11 y) + (u01 x + u10 x) * (u01 y + u10 y) : ℤ) : ℂ) := by
      rw [decomp_one x y]
    push_cast at hc
    rw [hX1e, hM, hN1]
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, vecMulVec_apply, hcv,
      smul_eq_mul]
    push_cast
    linear_combination hc / 128
  have htr1 : X1.trace = 1 := by
    simp only [Matrix.trace, Matrix.diag, hX1e, (xi_diag _).2]
    simp [Finset.sum_const, Finset.card_univ]
  have htrN : N1.trace = 1 / 2 := by
    rw [hN1, Matrix.trace_smul, trace_vecMulVec]
    have h : cv (fun x => u01 x - u10 x) ⬝ᵥ cv (fun x => u01 x - u10 x) = 64 := by
      simp only [dotProduct, hcv]
      exact_mod_cast w_norm
    rw [h, smul_eq_mul]
    norm_num
  have hup : traceNorm X1 ≤ 2 := by
    have h1 := traceNorm_add_le M (-N1)
    rw [traceNorm_neg, ← hsplit] at h1
    have hMt := congrArg Complex.re (traceNorm_of_posSemidef hMpsd)
    change traceNorm M = (M.trace).re at hMt
    have hNt := congrArg Complex.re (traceNorm_of_posSemidef hN1psd)
    change traceNorm N1 = (N1.trace).re at hNt
    have hMX : M.trace = X1.trace + N1.trace := by
      rw [← Matrix.trace_add, hsplit]
      congr 1
      abel
    rw [hMX, htr1, htrN] at hMt
    rw [htrN] at hNt
    norm_num at hMt hNt
    linarith
  have h := hclaim 6 k33 partA (97 / 100) 1 (by norm_num) (by norm_num) le_rfl
  simp only [negativity] at h
  rw [← hXdef, ← hX1def] at h
  linarith

end D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation
