/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace]
   utility: none
   digest: Boundary gluing for injective periodic binary matrix product states. -/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basis
import D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation

/-! The length-two spanning hypothesis is the source's actual injectivity condition.
No individual symbol matrix is assumed invertible. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection

open scoped BigOperators Matrix

noncomputable section

abbrev Bond := Matrix (Fin 2) (Fin 2) ℂ
abbrev Word (n : ℕ) := Fin n → Fin 2

def wordMatrix (A : Fin 2 → Bond) {n : ℕ} (w : Word n) : Bond :=
  (List.ofFn fun i => A (w i)).prod

def gamma (A : Fin 2 → Bond) (n : ℕ) (X : Bond) (w : Word n) : ℂ :=
  (X * wordMatrix A w).trace

def TwoSiteSpanning (A : Fin 2 → Bond) : Prop :=
  Submodule.span ℂ (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2) = ⊤

private lemma wordMatrix_cons (A : Fin 2 → Bond) {n : ℕ} (i : Fin 2) (w : Word n) :
    wordMatrix A (Fin.cons i w) = A i * wordMatrix A w := by
  simp [wordMatrix]

private lemma wordMatrix_snoc (A : Fin 2 → Bond) {n : ℕ} (w : Word n) (i : Fin 2) :
    wordMatrix A (Fin.snoc w i) = wordMatrix A w * A i := by
  rw [wordMatrix, List.ofFn_succ']
  simp [wordMatrix]

private lemma wordMatrix_append (A : Fin 2 → Bond) {m n : ℕ}
    (u : Word m) (v : Word n) :
    wordMatrix A (Fin.append u v) = wordMatrix A u * wordMatrix A v := by
  simp [wordMatrix, List.ofFn_comp', List.ofFn_fin_append, List.prod_append]

/-- Compatible left and right virtual boundaries glue through one common matrix. -/
private theorem boundary_gluing (A : Fin 2 → Bond) (hA : TwoSiteSpanning A)
    (X Y : Fin 2 → Bond) (h : ∀ i j, X j * A i = A j * Y i) :
    ∃ Z : Bond, (∀ j, X j = A j * Z) ∧ (∀ i, Y i = Z * A i) := by
  classical
  have hI : (1 : Bond) ∈ Submodule.span ℂ
      (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2) := by
    rw [hA]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hI
  let Z : Bond := ∑ p : Fin 2 × Fin 2, c p • (Y p.1 * A p.2)
  have hX (j : Fin 2) : X j = A j * Z := by
    calc
      X j = X j * (∑ p, c p • (A p.1 * A p.2)) := by rw [hc, mul_one]
      _ = A j * Z := by
        simp only [Z, Finset.mul_sum, Matrix.mul_smul, smul_mul_assoc,
          ← Matrix.mul_assoc, h]
  refine ⟨Z, hX, ?_⟩
  intro i
  have hk (j : Fin 2) : A j * Y i = A j * (Z * A i) := by
    rw [← h i j, hX, Matrix.mul_assoc]
  calc
    Y i = (∑ p, c p • (A p.1 * A p.2)) * Y i := by rw [hc, one_mul]
    _ = (∑ p, c p • (A p.1 * A p.2)) * (Z * A i) := by
      simp only [Finset.sum_mul, smul_mul_assoc, Matrix.mul_assoc, hk]
    _ = Z * A i := by rw [hc, one_mul]

private lemma trace_separates (A : Fin 2 → Bond) (hA : TwoSiteSpanning A)
    (m : ℕ) (X Y : Bond)
    (h : ∀ w : Word (m + 2), gamma A (m + 2) X w = gamma A (m + 2) Y w) :
    X = Y := by
  classical
  induction m generalizing X Y with
  | zero =>
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro B
    have hB : B ∈ Submodule.span ℂ
        (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2) := by
      rw [hA]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hB
    have hp (p : Fin 2 × Fin 2) :
        (X * (A p.1 * A p.2)).trace = (Y * (A p.1 * A p.2)).trace := by
      simpa [gamma, wordMatrix, List.ofFn_succ, Matrix.mul_assoc] using h ![p.1, p.2]
    rw [← hc]
    simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, hp]
  | succ m ih =>
    have hx (i : Fin 2) : X * A i = Y * A i := by
      apply ih
      intro w
      simpa only [gamma, wordMatrix_cons, Matrix.mul_assoc] using h (Fin.cons i w)
    have hI : (1 : Bond) ∈ Submodule.span ℂ
        (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2) := by
      rw [hA]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hI
    calc
      X = X * (∑ p, c p • (A p.1 * A p.2)) := by rw [hc, mul_one]
      _ = Y * (∑ p, c p • (A p.1 * A p.2)) := by
        simp only [Finset.mul_sum, Matrix.mul_smul, ← Matrix.mul_assoc, hx]
      _ = Y := by rw [hc, mul_one]

/-- The exact overlap of two adjacent parent spaces, including the four-site base. -/
private theorem parent_intersection (A : Fin 2 → Bond) (hA : TwoSiteSpanning A)
    (m : ℕ) (f : Word (m + 4) → ℂ) :
    ((∃ X : Fin 2 → Bond, ∀ (w : Word (m + 3)) j,
        f (Fin.snoc w j) = gamma A (m + 3) (X j) w) ∧
      (∃ Y : Fin 2 → Bond, ∀ i (w : Word (m + 3)),
        f (Fin.cons i w) = gamma A (m + 3) (Y i) w)) ↔
      ∃ Z : Bond, f = gamma A (m + 4) Z := by
  constructor
  · rintro ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩
    have hb (i j : Fin 2) : X j * A i = A j * Y i := by
      apply trace_separates A hA m
      intro w
      have he := (hX (Fin.cons i w) j).symm.trans
        ((congrArg f (Fin.cons_snoc_eq_snoc_cons i w j)).symm.trans
          (hY i (Fin.snoc w j)))
      simpa only [gamma, wordMatrix_cons, wordMatrix_snoc, ← Matrix.mul_assoc,
        Matrix.trace_mul_cycle (Y i) (wordMatrix A w) (A j)] using he
    obtain ⟨Z, hZ, _⟩ := boundary_gluing A hA X Y hb
    refine ⟨Z, ?_⟩
    funext w
    have he := hX (Fin.init w) (w (Fin.last _))
    rw [Fin.snoc_init_self] at he
    rw [he, hZ]
    change (A (w (Fin.last _)) * Z * wordMatrix A (Fin.init w)).trace =
      (Z * wordMatrix A w).trace
    rw [Matrix.mul_assoc,
      Matrix.trace_mul_comm (A (w (Fin.last _))) (Z * wordMatrix A (Fin.init w)),
      Matrix.mul_assoc, ← wordMatrix_snoc, Fin.snoc_init_self]
  · rintro ⟨Z, rfl⟩
    constructor
    · refine ⟨fun j => A j * Z, ?_⟩
      intro w j
      simpa only [gamma, wordMatrix_snoc, ← Matrix.mul_assoc] using
        Matrix.trace_mul_cycle Z (wordMatrix A w) (A j)
    · refine ⟨fun i => Z * A i, ?_⟩
      intro i w
      simp only [gamma, wordMatrix_cons, Matrix.mul_assoc]

/-- The actual two-site amplitude flattening, with the two bits indexed as a pair. -/
def twoFlattening (A : Fin 2 → Bond) (r : ℕ) :
    Matrix (Fin 2 × Fin 2) (Word (r + 2)) ℂ :=
  fun p b => UniformMPSExpectedDimensionRefutation.traceWord 2 2 (2 + (r + 2)) A
    (Fin.append ![p.1, p.2] b)

private lemma spanning_of_rank (A : Fin 2 → Bond) (r : ℕ)
    (hr : (twoFlattening A r).rank = 4) : TwoSiteSpanning A := by
  classical
  let L : Bond →ₗ[ℂ] (Word (r + 2) → ℂ) :=
    { toFun := gamma A (r + 2)
      map_add' := by intros; ext w; simp [gamma, add_mul, Matrix.trace_add]
      map_smul' := by intros; ext w; simp [gamma, smul_mul_assoc, Matrix.trace_smul] }
  let S := Submodule.span ℂ (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2)
  have hmap : S.map L = Submodule.span ℂ (Set.range (twoFlattening A r).row) := by
    dsimp only [S]
    rw [Submodule.map_span, ← Set.range_comp]
    have he : (fun p : Fin 2 × Fin 2 => L (A p.1 * A p.2)) =
        (twoFlattening A r).row := by
      funext p b
      change ((A p.1 * A p.2) * (List.ofFn fun i => A (b i)).prod).trace =
        ((List.ofFn fun i => A (Fin.append ![p.1, p.2] b i)).prod).trace
      rw [List.ofFn_comp' (Fin.append ![p.1, p.2] b) A,
        List.ofFn_fin_append, List.map_append, List.prod_append]
      simp [List.map_ofFn, List.ofFn_succ, Matrix.mul_assoc, Function.comp_def]
    change Submodule.span ℂ (Set.range (fun p : Fin 2 × Fin 2 => L (A p.1 * A p.2))) = _
    rw [he]
  have hle : 4 ≤ Module.finrank ℂ S := by
    rw [← hr, Matrix.rank_eq_finrank_span_row, ← hmap]
    exact Submodule.finrank_map_le L S
  have hdim : Module.finrank ℂ Bond = 4 := by
    norm_num [Bond, Module.finrank_matrix]
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le S)
    (hdim.symm ▸ hle))

/-- Rank four of an actual periodic target gives the adjacent-parent intersection
at every length, with arbitrary tensors as competitors. -/
private theorem rank_locus_parent_intersection (A : Fin 2 → Bond) (r : ℕ)
    (hr : (twoFlattening A r).rank = 4) (m : ℕ) (f : Word (m + 4) → ℂ) :
    ((∃ X : Fin 2 → Bond, ∀ (w : Word (m + 3)) j,
        f (Fin.snoc w j) = gamma A (m + 3) (X j) w) ∧
      (∃ Y : Fin 2 → Bond, ∀ i (w : Word (m + 3)),
        f (Fin.cons i w) = gamma A (m + 3) (Y i) w)) ↔
      ∃ Z : Bond, f = gamma A (m + 4) Z := by
  exact parent_intersection A (spanning_of_rank A r hr) m f

/-- Four-site conditional amplitudes of an unrestricted actual periodic competitor. -/
def competitorSlice (B : Fin 2 → Bond) {r : ℕ} (b : Word r) (w : Word 4) : ℂ :=
  UniformMPSExpectedDimensionRefutation.traceWord 2 2 (4 + r) B (Fin.append w b)

/-- On every actual competitor, the two adjacent three-site parent constraints glue
into the four-site parent space, for every ring length at least four. -/
theorem actual_competitor_gluing (A B : Fin 2 → Bond) (r : ℕ)
    (hr : (twoFlattening A r).rank = 4) (b : Word r)
    (hleft : ∃ X : Fin 2 → Bond, ∀ (w : Word 3) j,
      competitorSlice B b (Fin.snoc w j) = gamma A 3 (X j) w)
    (hright : ∃ Y : Fin 2 → Bond, ∀ i (w : Word 3),
      competitorSlice B b (Fin.cons i w) = gamma A 3 (Y i) w) :
    ∃ Z : Bond, competitorSlice B b = gamma A 4 Z := by
  exact (rank_locus_parent_intersection A r hr 0 (competitorSlice B b)).mp ⟨hleft, hright⟩

/-- Native three-site amplitude columns, before forming the raw Gram matrix. -/
def threeColumns (A : Fin 2 → Bond) (r : ℕ) : Matrix (Word 3) (Word (r + 1)) ℂ :=
  fun w b => gamma A 3 (wordMatrix A b) w

/-- The unnormalized three-site reduced density matrix on a ring of length r+4. -/
def rawThree (A : Fin 2 → Bond) (r : ℕ) : Matrix (Word 3) (Word 3) ℂ :=
  threeColumns A r * (threeColumns A r).conjTranspose

private lemma gram_range {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) :
    LinearMap.range (M * M.conjTranspose).mulVecLin = LinearMap.range M.mulVecLin := by
  classical
  open scoped ComplexOrder in
    exact Submodule.eq_of_le_of_finrank_eq
      (by
        rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
        rintro _ ⟨x, _, rfl⟩
        exact ⟨x, rfl⟩)
      (Matrix.rank_self_mul_conjTranspose M)

private lemma raw_to_parent (A B : Fin 2 → Bond) (r : ℕ)
    (hraw : rawThree B r = rawThree A r) :
    ∀ b : Word (r + 1), ∃ X : Bond,
      gamma B 3 (wordMatrix B b) = gamma A 3 X := by
  classical
  let L : Bond →ₗ[ℂ] (Word 3 → ℂ) :=
    { toFun := gamma A 3
      map_add' := by intros; ext w; simp [gamma, add_mul, Matrix.trace_add]
      map_smul' := by intros; ext w; simp [gamma, smul_mul_assoc, Matrix.trace_smul] }
  have hle : LinearMap.range (threeColumns A r).mulVecLin ≤ LinearMap.range L := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact ⟨wordMatrix A b, rfl⟩
  intro b
  have hb : (threeColumns B r).col b ∈ LinearMap.range (threeColumns B r).mulVecLin := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨b, rfl⟩
  rw [← gram_range (threeColumns B r), ← rawThree, hraw, rawThree,
    gram_range (threeColumns A r)] at hb
  obtain ⟨X, hX⟩ := hle hb
  exact ⟨X, hX.symm⟩

private theorem propagate (A B : Fin 2 → Bond) (hA : TwoSiteSpanning A) (m : ℕ) :
    ∀ r : ℕ,
      (∀ b : Word (m + r), ∃ X : Bond,
        gamma B 3 (wordMatrix B b) = gamma A 3 X) →
      ∀ b : Word r, ∃ X : Bond,
        gamma B (m + 3) (wordMatrix B b) = gamma A (m + 3) X := by
  induction m with
  | zero =>
    intro r h
    rw [Nat.zero_add] at h
    exact h
  | succ m ih =>
    intro r h b
    have hp := ih (r + 1) (by
      have hn : m + 1 + r = m + (r + 1) := by omega
      rw [hn] at h
      exact h)
    apply (parent_intersection A hA m (gamma B (m + 4) (wordMatrix B b))).mp
    constructor
    · choose X hX using fun j : Fin 2 => hp (Fin.cons j b)
      refine ⟨X, ?_⟩
      intro w j
      rw [← congrFun (hX j) w]
      simp only [gamma, wordMatrix_cons, wordMatrix_snoc]
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_cycle (wordMatrix B b) (wordMatrix B w) (B j)
    · choose Y hY using fun i : Fin 2 => hp (Fin.snoc b i)
      refine ⟨Y, ?_⟩
      intro i w
      rw [← congrFun (hY i) w]
      simp only [gamma, wordMatrix_cons, wordMatrix_snoc, Matrix.mul_assoc]

private lemma scalar_of_commuting (A : Fin 2 → Bond) (hA : TwoSiteSpanning A)
    (X : Bond) (hX : ∀ i, X * A i = A i * X) : ∃ c : ℂ, X = c • (1 : Bond) := by
  classical
  have hcomm (Y : Bond) : X * Y = Y * X := by
    have hY : Y ∈ Submodule.span ℂ
        (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2) := by rw [hA]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hY
    rw [← hc]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, smul_mul_assoc]
    congr 1
    funext p
    rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, hX, ← Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
    (fun i j => (hcomm (Matrix.single i j 1)).symm)
  refine ⟨c, hc.symm.trans ?_⟩
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply, hij]

private theorem cyclic_boundary_scalar (A B : Fin 2 → Bond) (hA : TwoSiteSpanning A)
    (r : ℕ) (X : Bond)
    (he : gamma B (r + 4) 1 = gamma A (r + 4) X) :
    ∃ c : ℂ, gamma B (r + 4) 1 = c • gamma A (r + 4) 1 := by
  have hc (i : Fin 2) : X * A i = A i * X := by
    apply trace_separates A hA (r + 1)
    intro w
    have hl := congrFun he (Fin.cons i w)
    have hr := congrFun he (Fin.snoc w i)
    simp only [gamma, wordMatrix_cons, wordMatrix_snoc, one_mul] at hl hr
    change (X * A i * wordMatrix A w).trace = (A i * X * wordMatrix A w).trace
    rw [Matrix.mul_assoc, ← hl,
      Matrix.trace_mul_comm (B i) (wordMatrix B w), hr]
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_cycle X (wordMatrix A w) (A i)
  obtain ⟨c, rfl⟩ := scalar_of_commuting A hA X hc
  refine ⟨c, he.trans ?_⟩
  ext w
  simp [gamma, smul_mul_assoc, Matrix.trace_smul]

private lemma columns_of_state_eq (A B : Fin 2 → Bond) (r : ℕ) (c : ℂ)
    (he : gamma B (r + 4) 1 = c • gamma A (r + 4) 1) :
    threeColumns B r = c • threeColumns A r := by
  have he' : gamma B (3 + (r + 1)) 1 = c • gamma A (3 + (r + 1)) 1 := by
    have hn : r + 4 = 3 + (r + 1) := by omega
    rw [hn] at he
    exact he
  ext w b
  have h := congrFun he' (Fin.append w b)
  simpa only [gamma, wordMatrix_append, one_mul, Pi.smul_apply, smul_eq_mul,
    threeColumns, Matrix.smul_apply,
    Matrix.trace_mul_comm (wordMatrix B w) (wordMatrix B b),
    Matrix.trace_mul_comm (wordMatrix A w) (wordMatrix A b)] using h

private lemma raw_of_state_eq (A B : Fin 2 → Bond) (r : ℕ) (c : ℂ)
    (he : gamma B (r + 4) 1 = c • gamma A (r + 4) 1) :
    rawThree B r = (c * star c) • rawThree A r := by
  rw [rawThree, columns_of_state_eq A B r c he, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rfl

private lemma raw_ne_zero (A : Fin 2 → Bond) (r : ℕ)
    (hr : (twoFlattening A r).rank = 4) : rawThree A r ≠ 0 := by
  intro hz
  have hrange := gram_range (threeColumns A r)
  rw [← rawThree, hz, Matrix.mulVecLin_zero, LinearMap.range_zero] at hrange
  have hcolumns : threeColumns A r = 0 := by
    ext w b
    have hb : (threeColumns A r).col b ∈ LinearMap.range (threeColumns A r).mulVecLin := by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨b, rfl⟩
    rw [← hrange] at hb
    have hb' : (threeColumns A r).col b = 0 := by simpa using hb
    exact congrFun hb' w
  have hf : twoFlattening A r = 0 := by
    ext p b
    have hb := congrFun (congrFun hcolumns ![p.1, p.2, b 0]) (Fin.tail b)
    have hw : wordMatrix A b = A (b 0) * wordMatrix A (Fin.tail b) := by
      rw [← wordMatrix_cons, Fin.cons_self_tail]
    change (wordMatrix A (Fin.tail b) * wordMatrix A ![p.1, p.2, b 0]).trace = 0 at hb
    change ((List.ofFn fun i => A (Fin.append ![p.1, p.2] b i)).prod).trace = 0
    rw [List.ofFn_comp' (Fin.append ![p.1, p.2] b) A,
      List.ofFn_fin_append, List.map_append, List.prod_append]
    simp only [List.map_ofFn]
    change (wordMatrix A ![p.1, p.2] * wordMatrix A b).trace = 0
    rw [hw]
    rw [Matrix.trace_mul_comm] at hb
    simpa [wordMatrix, List.ofFn_succ, Matrix.mul_assoc] using hb
  rw [hf, Matrix.rank_zero] at hr
  norm_num at hr

private theorem phase_recovery (A B : Fin 2 → Bond) (r : ℕ)
    (hr : (twoFlattening A r).rank = 4) :
    rawThree B r = rawThree A r ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ gamma B (r + 4) 1 = c • gamma A (r + 4) 1 := by
  constructor
  · intro hraw
    have hA := spanning_of_rank A r hr
    obtain ⟨X, hX⟩ := propagate A B hA (r + 1) 0 (by
      simpa using raw_to_parent A B r hraw) (fun i => Fin.elim0 i)
    have hX' : gamma B (r + 4) 1 = gamma A (r + 4) X := by
      simpa [wordMatrix, List.ofFn_zero] using hX
    obtain ⟨c, hc⟩ := cyclic_boundary_scalar A B hA r X hX'
    have hs : (c * star c) • rawThree A r = (1 : ℂ) • rawThree A r := by
      rw [← raw_of_state_eq A B r c hc, hraw, one_smul]
    have hn : c * star c = 1 := (smul_left_injective ℂ (raw_ne_zero A r hr)) hs
    have hnorm : ‖c‖ ^ 2 = 1 := by
      have hre := congrArg Complex.re hn
      simpa [Complex.mul_conj', ← Complex.ofReal_pow] using hre
    exact ⟨c, by nlinarith [norm_nonneg c], hc⟩
  · rintro ⟨c, hc, he⟩
    rw [raw_of_state_eq A B r c he]
    have hn : c * star c = 1 := by
      change c * (starRingEnd ℂ) c = 1
      rw [Complex.mul_conj', hc]
      norm_num
    rw [hn, one_smul]

private lemma rank_of_spanning (A : Fin 2 → Bond) (hA : TwoSiteSpanning A) (r : ℕ) :
    (twoFlattening A r).rank = 4 := by
  classical
  let L : Bond →ₗ[ℂ] (Word (r + 2) → ℂ) :=
    { toFun := gamma A (r + 2)
      map_add' := by intros; ext w; simp [gamma, add_mul, Matrix.trace_add]
      map_smul' := by intros; ext w; simp [gamma, smul_mul_assoc, Matrix.trace_smul] }
  have hinj : Function.Injective L := by
    intro X Y he
    exact trace_separates A hA r X Y (congrFun he)
  have heq : LinearMap.range L = Submodule.span ℂ (Set.range (twoFlattening A r).row) := by
    calc
      LinearMap.range L = (Submodule.span ℂ
          (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2)).map L := by
        rw [hA, Submodule.map_top]
      _ = _ := by
        rw [Submodule.map_span, ← Set.range_comp]
        have he : (fun p : Fin 2 × Fin 2 => L (A p.1 * A p.2)) =
            (twoFlattening A r).row := by
          funext p b
          change ((A p.1 * A p.2) * (List.ofFn fun i => A (b i)).prod).trace =
            ((List.ofFn fun i => A (Fin.append ![p.1, p.2] b i)).prod).trace
          rw [List.ofFn_comp' (Fin.append ![p.1, p.2] b) A,
            List.ofFn_fin_append, List.map_append, List.prod_append]
          simp [List.map_ofFn, List.ofFn_succ, Matrix.mul_assoc, Function.comp_def]
        change Submodule.span ℂ (Set.range (fun p : Fin 2 × Fin 2 => L (A p.1 * A p.2))) = _
        rw [he]
  rw [Matrix.rank_eq_finrank_span_row, ← heq, LinearMap.finrank_range_of_inj hinj]
  norm_num [Bond, Module.finrank_matrix]

private def witnessPair : Fin 2 → Bond :=
  ![!![1, 0; 0, 2], !![0, 1; 1, 0]]

private lemma witness_spanning : TwoSiteSpanning witnessPair := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro M
  let S := Submodule.span ℂ
    (Set.range fun p : Fin 2 × Fin 2 => witnessPair p.1 * witnessPair p.2)
  have hp (i j : Fin 2) : witnessPair i * witnessPair j ∈ S :=
    Submodule.subset_span ⟨(i, j), rfl⟩
  have hmem := S.add_mem
    (S.add_mem
      (S.smul_mem ((M 1 1 - M 0 0) / 3) (hp 0 0))
      (S.smul_mem ((4 * M 0 0 - M 1 1) / 3) (hp 1 1)))
    (S.add_mem
      (S.smul_mem ((2 * M 1 0 - M 0 1) / 3) (hp 0 1))
      (S.smul_mem ((2 * M 0 1 - M 1 0) / 3) (hp 1 0)))
  convert hmem using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessPair, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

/-- The actual rank-four target locus is inhabited at every ring length at least
four, and its raw three-site fibres among all actual periodic competitors are
exactly phase fibres. No hypothesis is imposed on the competitor matrices. -/
theorem rank_locus_inhabited_and_phase_recovery (r : ℕ) :
    (∃ A : Fin 2 → Bond, (twoFlattening A r).rank = 4) ∧
      ∀ A B : Fin 2 → Bond, (twoFlattening A r).rank = 4 →
        (rawThree B r = rawThree A r ↔
          ∃ c : ℂ, ‖c‖ = 1 ∧ gamma B (r + 4) 1 = c • gamma A (r + 4) 1) := by
  exact ⟨⟨witnessPair, rank_of_spanning witnessPair witness_spanning r⟩,
    fun A B hr => phase_recovery A B r hr⟩

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
