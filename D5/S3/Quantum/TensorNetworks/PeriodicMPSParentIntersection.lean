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
    rw [Submodule.map_span, Set.image_range]
    have he : (fun p : Fin 2 × Fin 2 => L (A p.1 * A p.2)) =
        (twoFlattening A r).row := by
      funext p b
      simp [L, gamma, wordMatrix, twoFlattening, Matrix.row,
        UniformMPSExpectedDimensionRefutation.traceWord, List.ofFn_fin_append,
        List.ofFn_succ, List.prod_append, Matrix.mul_assoc]
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

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
