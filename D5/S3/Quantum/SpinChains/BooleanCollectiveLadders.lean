/- GID: D5/S3/Quantum/SpinChains/BooleanCollectiveLadders
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/BooleanCollectiveLadders
   mirror-E: none
   anchors: []
   utility: none
   digest: Collective Boolean ladders on the full complex configuration carrier. -/

import D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Finset.Powerset

/-! Primitive-string construction for the complete complex Boolean carrier. -/

set_option maxHeartbeats 80000

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open Matrix
open D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation
open D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion

namespace D5.S3.Quantum.SpinChains.BooleanCollectiveLadders

/-- Every Boolean configuration is retained; zero denotes membership. -/
abbrev Configuration (N : ℕ) := Fin N → Fin 2
/-- The complex Hilbert space of all Boolean configurations. -/
abbrev Space (N : ℕ) := EuclideanSpace ℂ (Configuration N)
/-- The actual, unweighted collective raising map. -/
def U (N : ℕ) : Module.End ℂ (Space N) := (totalPlus N).toEuclideanLin
/-- The actual, unweighted collective lowering map. -/
def L (N : ℕ) : Module.End ℂ (Space N) := (totalMinus N).toEuclideanLin
/-- Occupancy uses bit zero as membership, consistently with sigmaPlus. -/
def occupancy {N : ℕ} (x : Configuration N) : ℕ := ∑ i, if x i = 0 then 1 else 0
/-- The diagonal number operator on the entire carrier. -/
def numberMatrix (N : ℕ) : Matrix (Configuration N) (Configuration N) ℂ :=
  diagonal fun x => (occupancy x : ℂ)
def number (N : ℕ) : Module.End ℂ (Space N) := (numberMatrix N).toEuclideanLin
/-- Centered occupancy, whose spin-string weights run from minus j to j. -/
def Z (N : ℕ) : Module.End ℂ (Space N) := number N - (N / 2 : ℂ) • 1
/-- The actual homogeneous occupancy subspace, specified by coefficient support. -/
def rankSpace (N t : ℕ) : Submodule ℂ (Space N) where
  carrier := {v | ∀ x, occupancy x ≠ t → v x = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv x hx; simp [hu x hx, hv x hx]
  smul_mem' := by intro c v hv x hx; simp [hv x hx]
/-- All primitive vectors at a given rank, including the zero vector. -/
def primitive (N t : ℕ) : Submodule ℂ (Space N) := rankSpace N t ⊓ LinearMap.ker (L N)

private lemma tensor_mul' {N : ℕ} (A B : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    tensor N A * tensor N B = tensor N (fun i => A i * B i) := by
  exact D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensor_mul A B

private lemma site_mul {N : ℕ} (j : Fin N) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    site N j A * site N j B = site N j (A * B) := by
  rw [site, site, tensor_mul']
  congr 1
  funext i
  by_cases h : i = j <;> simp [h]

private lemma site_commute {N : ℕ} (i j : Fin N) (h : i ≠ j)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    site N i A * site N j B = site N j B * site N i A := by
  unfold site
  rw [tensor_mul', tensor_mul']
  congr 1
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

private lemma site_entry {N : ℕ} (j : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (x y : Configuration N) :
    site N j A x y = A (x j) (y j) * ∏ i ∈ Finset.univ.erase j,
      (if x i = y i then (1 : ℂ) else 0) := by
  unfold site tensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [hi.1, Matrix.one_apply]

private lemma site_sub {N : ℕ} (j : Fin N) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    site N j (A - B) = site N j A - site N j B := by
  ext x y
  simp only [site_entry, Matrix.sub_apply, sub_mul]

private lemma site_diagonal {N : ℕ} (j : Fin N) (d : Fin 2 → ℂ) :
    site N j (diagonal d) = diagonal (fun x : Configuration N => d (x j)) := by
  classical
  ext x y
  by_cases h : x = y
  · subst y
    simp [site_entry]
  · rw [diagonal_apply_ne _ h, site_entry]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc
      exact h (funext fun i => not_not.mp (not_exists.mp hc i))
    by_cases hij : i = j
    · subst i
      simp [diagonal_apply_ne _ hi]
    · have hp : (∏ k ∈ Finset.univ.erase j, if x k = y k then (1 : ℂ) else 0) = 0 :=
        Finset.prod_eq_zero (a := i) (by simp [hij]) (by simp [hi])
      rw [hp, mul_zero]

private lemma collective_commutator (N : ℕ) :
    totalMinus N * totalPlus N - totalPlus N * totalMinus N =
      (N : ℂ) • 1 - (2 : ℂ) • numberMatrix N := by
  classical
  have local_comm (i j : Fin N) :
      site N i sigmaMinus * site N j sigmaPlus -
        site N j sigmaPlus * site N i sigmaMinus =
          if i = j then site N i (diagonal ![-1, 1]) else 0 := by
    by_cases h : i = j
    · subst j
      rw [if_pos rfl, site_mul, site_mul, ← site_sub]
      congr 1
      ext a b
      fin_cases a <;> fin_cases b <;> norm_num [sigmaMinus, sigmaPlus, Matrix.mul_apply]
    · rw [if_neg h, site_commute i j h, sub_self]
  rw [totalMinus, totalPlus, Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => site N i sigmaPlus * site N j sigmaMinus)]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, local_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, site_diagonal]
  ext x y
  by_cases h : x = y
  · subst y
    simp only [Matrix.sum_apply, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, numberMatrix]
    change (∑ i : Fin N, (![-1, 1] : Fin 2 → ℂ) (x i)) =
      (N : ℂ) - 2 * (occupancy x : ℂ)
    simp only [occupancy, Nat.cast_sum]
    rw [Finset.mul_sum, ← Finset.sum_const (b := (1 : ℂ)), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    generalize x i = a
    fin_cases a <;> norm_num
  · simp [Matrix.sum_apply, diagonal_apply_ne _ h, h, numberMatrix]

private lemma number_eq_sum (N : ℕ) :
    numberMatrix N = ∑ i, site N i nUp := by
  have hn : nUp = diagonal ![1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [nUp, D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.one_apply]
  rw [hn]
  simp_rw [site_diagonal]
  ext x y
  by_cases h : x = y
  · subst y
    simp only [numberMatrix, diagonal_apply_eq, Matrix.sum_apply, occupancy, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    generalize x i = a
    fin_cases a <;> norm_num
  · simp [numberMatrix, Matrix.sum_apply, h]

private lemma sum_commutator {N : ℕ} {ι : Type*} [Fintype ι]
    (A B : ι → Matrix (Configuration N) (Configuration N) ℂ) :
    (∑ i, A i) * (∑ j, B j) - (∑ j, B j) * (∑ i, A i) =
      ∑ i, ∑ j, (A i * B j - B j * A i) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => B j * A i)]
  simp_rw [Finset.sum_sub_distrib]

private lemma number_raising (N : ℕ) :
    numberMatrix N * totalPlus N - totalPlus N * numberMatrix N = totalPlus N := by
  classical
  rw [number_eq_sum, totalPlus, sum_commutator]
  have hc (i j : Fin N) :
      site N i nUp * site N j sigmaPlus - site N j sigmaPlus * site N i nUp =
        if i = j then site N i sigmaPlus else 0 := by
    by_cases h : i = j
    · subst j
      rw [if_pos rfl, site_mul, site_mul, ← site_sub]
      congr 1
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [nUp, D5.S3.Quantum.FiniteDimensional.qubitZ, sigmaPlus, Matrix.mul_apply]
    · rw [if_neg h, site_commute i j h, sub_self]
  simp_rw [hc]
  simp

private lemma site_adjoint {N : ℕ} (i : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (site N i A)ᴴ = site N i Aᴴ := by
  ext x y
  simp only [conjTranspose_apply, site, tensor, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i <;> simp [h, conjTranspose_apply]

private lemma minus_eq_adjoint (N : ℕ) : (totalPlus N)ᴴ = totalMinus N := by
  have h : sigmaPlusᴴ = sigmaMinus := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [sigmaPlus, sigmaMinus, conjTranspose_apply]
  simp [totalPlus, totalMinus, conjTranspose_sum, site_adjoint, h]

private lemma number_adjoint (N : ℕ) : (numberMatrix N)ᴴ = numberMatrix N := by
  simp [numberMatrix]

private lemma number_lowering (N : ℕ) :
    numberMatrix N * totalMinus N - totalMinus N * numberMatrix N = -totalMinus N := by
  have h := congrArg Matrix.conjTranspose (number_raising N)
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
    minus_eq_adjoint, number_adjoint] at h
  linear_combination -h

private lemma commutator (N : ℕ) :
    L N * U N - U N * L N = (N : ℂ) • 1 - (2 : ℂ) • number N := by
  simpa only [U, L, number, Matrix.toEuclideanLin, map_sub, map_smul,
    Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using
      congrArg Matrix.toEuclideanLin (collective_commutator N)

private lemma number_U (N : ℕ) : number N * U N - U N * number N = U N := by
  simpa only [U, number, Matrix.toEuclideanLin, map_sub, Matrix.toLpLin_mul_same] using
    congrArg Matrix.toEuclideanLin (number_raising N)

private lemma number_L (N : ℕ) : number N * L N - L N * number N = -L N := by
  simpa only [L, number, Matrix.toEuclideanLin, map_sub, map_neg, Matrix.toLpLin_mul_same] using
    congrArg Matrix.toEuclideanLin (number_lowering N)

private lemma adjoint_U (N : ℕ) : (U N).adjoint = L N := by
  rw [U, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, minus_eq_adjoint]
  rfl

private lemma inner_U (N : ℕ) (v w : Space N) :
    inner ℂ (U N v) w = inner ℂ v (L N w) := by
  rw [← adjoint_U]
  exact ((U N).adjoint_inner_right v w).symm

private lemma number_apply (N : ℕ) (v : Space N) (x : Configuration N) :
    number N v x = (occupancy x : ℂ) * v x := by
  change (numberMatrix N *ᵥ v.ofLp) x = _
  simp [numberMatrix]

private lemma mem_rank_iff (N t : ℕ) (v : Space N) :
    v ∈ rankSpace N t ↔ number N v = (t : ℂ) • v := by
  constructor
  · intro hv
    ext x
    rw [number_apply]
    by_cases h : occupancy x = t
    · simp [h]
    · change ∀ x, occupancy x ≠ t → v x = 0 at hv
      simp [hv x h]
  · intro hv x hx
    have h := congrArg (fun w : Space N => w x) hv
    rw [number_apply] at h
    change (occupancy x : ℂ) * v x = (t : ℂ) * v x at h
    exact (mul_eq_mul_right_iff.mp h).resolve_left (by exact_mod_cast hx)

private lemma U_rank {N t : ℕ} {v : Space N} (hv : v ∈ rankSpace N t) :
    U N v ∈ rankSpace N (t + 1) := by
  rw [mem_rank_iff] at hv ⊢
  have hc := congrArg (fun A : Module.End ℂ (Space N) => A v) (number_U N)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, map_smul] at hc
  rw [Nat.cast_add, Nat.cast_one]
  linear_combination hc

private lemma L_rank_succ {N t : ℕ} {v : Space N} (hv : v ∈ rankSpace N (t + 1)) :
    L N v ∈ rankSpace N t := by
  rw [mem_rank_iff] at hv ⊢
  have hc := congrArg (fun A : Module.End ℂ (Space N) => A v) (number_L N)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, map_smul,
    LinearMap.neg_apply, Nat.cast_add, Nat.cast_one] at hc
  linear_combination hc

private lemma L_rank_zero {N : ℕ} {v : Space N} (hv : v ∈ rankSpace N 0) :
    L N v = 0 := by
  rw [mem_rank_iff] at hv
  have hc := congrArg (fun A : Module.End ℂ (Space N) => A v) (number_L N)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, Nat.cast_zero,
    zero_smul, map_zero, sub_zero, LinearMap.neg_apply] at hc
  ext x
  have hx := congrArg (fun w : Space N => w x) hc
  rw [number_apply] at hx
  change (occupancy x : ℂ) * L N v x = -(L N v x) at hx
  have he : ((occupancy x : ℂ) + 1) * L N v x = 0 := by linear_combination hx
  exact (mul_eq_zero.mp he).resolve_left (by
    exact_mod_cast (Nat.succ_ne_zero (occupancy x)))

/-- All actual primitive vectors and their unnormalized raising strings. -/
def primitiveStrings (N : ℕ) : Set (Space N) :=
  {w | ∃ t v, v ∈ primitive N t ∧ ∃ q : ℕ, w = (U N ^ q) v}

private lemma strings_U {N : ℕ} {v : Space N}
    (hv : v ∈ Submodule.span ℂ (primitiveStrings N)) :
    U N v ∈ Submodule.span ℂ (primitiveStrings N) := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, v, hv, q, rfl⟩ := hw
    apply Submodule.subset_span
    exact ⟨t, v, hv, q + 1, by simp [pow_succ', Module.End.mul_apply]⟩
  | zero => simpa using (Submodule.span ℂ (primitiveStrings N)).zero_mem
  | add a b ha hb ia ib => simpa using (Submodule.span ℂ (primitiveStrings N)).add_mem ia ib
  | smul c a ha ia => simpa using (Submodule.span ℂ (primitiveStrings N)).smul_mem c ia

private lemma rank_le_string_span (N t : ℕ) :
    rankSpace N t ≤ Submodule.span ℂ (primitiveStrings N) := by
  induction t with
  | zero =>
    intro v hv
    apply Submodule.subset_span
    exact ⟨0, v, ⟨hv, L_rank_zero hv⟩, 0, by simp⟩
  | succ t ih =>
    intro v hv
    let K : Submodule ℂ (Space N) := (rankSpace N t).map (U N)
    obtain ⟨a, ha, b, hb, hab⟩ := K.exists_add_mem_mem_orthogonal v
    obtain ⟨w, hw, rfl⟩ := ha
    have hbRank : b ∈ rankSpace N (t + 1) := by
      have := (rankSpace N (t + 1)).sub_mem hv (U_rank hw)
      simpa [hab] using this
    have hLb : L N b = 0 := by
      have hULb : U N (L N b) ∈ K :=
        ⟨L N b, L_rank_succ hbRank, rfl⟩
      have hz := (Submodule.mem_orthogonal K b).mp hb (U N (L N b)) hULb
      rw [inner_U] at hz
      exact inner_self_eq_zero.mp hz
    have hbSpan : b ∈ Submodule.span ℂ (primitiveStrings N) := by
      apply Submodule.subset_span
      exact ⟨t + 1, b, ⟨hbRank, hLb⟩, 0, by simp⟩
    rw [hab]
    exact Submodule.add_mem _ (strings_U (ih hw)) hbSpan

/-- Primitive raising strings exhaust the full complex Boolean carrier.
No basis, complement homogeneity, completeness or rank projection is assumed. -/
theorem primitive_strings_span (N : ℕ) :
    Submodule.span ℂ (primitiveStrings N) = ⊤ := by
  apply top_unique
  rw [← (EuclideanSpace.basisFun (Configuration N) ℂ).toBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  apply rank_le_string_span N (occupancy x)
  intro y hy
  have hxy : x ≠ y := by intro h; subst y; exact hy rfl
  simp [EuclideanSpace.basisFun_apply, hxy]

#print axioms primitive_strings_span

end D5.S3.Quantum.SpinChains.BooleanCollectiveLadders

