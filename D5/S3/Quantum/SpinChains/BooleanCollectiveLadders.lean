/- GID: D5/S3/Quantum/SpinChains/BooleanCollectiveLadders
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/BooleanCollectiveLadders
   mirror-E: none
   anchors: []
   utility: none
   digest: Collective Boolean ladders on the full complex configuration carrier. -/

import D5.S3.Quantum.Dynamics.PronkoFredkinAntiAdjointExpansion
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Powerset

/-! Primitive-string construction for the complete complex Boolean carrier.

proof_shape: result, primitive_multiplicity, native_decomposition: content.
admission_basis: escape-witness.
The actual rank split and its low-rank injectivity derive primitive dimensions.
The complete normalized-string span constructs the native-coordinate unitary;
its U/L/Z matrix identities consume that construction on the full carrier.
Auxiliary bind-only facts are consumed by these constructions. No basis,
unitary, homogeneous complement, multiplicity or completeness is assumed.
The unfinished public escape registration is tracked by issue #26983.
-/

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
private def numberMatrix (N : ℕ) : Matrix (Configuration N) (Configuration N) ℂ :=
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
        Finset.prod_eq_zero (i := i) (by simp [hij]) (by simp [hi])
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
      rw [ite_eq_left rfl, site_mul, site_mul, ← site_sub]
      congr 1
      ext a b
      fin_cases a <;> fin_cases b <;> norm_num [sigmaMinus, sigmaPlus, Matrix.mul_apply]
    · rw [ite_eq_right h, site_commute i j h, sub_self]
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
    rw [Finset.mul_sum]
    have hn : (N : ℂ) = ∑ _ : Fin N, (1 : ℂ) := by simp
    rw [hn, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    generalize x i = a
    fin_cases a <;> norm_num
  · simp [Matrix.sum_apply, h, numberMatrix]

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
      rw [ite_eq_left rfl, site_mul, site_mul, ← site_sub]
      congr 1
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [nUp, D5.S3.Quantum.FiniteDimensional.qubitZ, sigmaPlus, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
    · rw [ite_eq_right h, site_commute i j h, sub_self]
  simp_rw [hc]
  simp

private lemma site_adjoint {N : ℕ} (i : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (site N i A)ᴴ = site N i Aᴴ := by
  ext x y
  simp only [conjTranspose_apply, site, tensor, star_prod]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i <;> simp [h, conjTranspose_apply, Matrix.one_apply, eq_comm]

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
  calc
    _ = -(totalMinus N * numberMatrix N - numberMatrix N * totalMinus N) := by abel
    _ = _ := congrArg Neg.neg h

private lemma commutator (N : ℕ) :
    L N * U N - U N * L N = (N : ℂ) • 1 - (2 : ℂ) • number N := by
  simpa only [U, L, number, Matrix.toEuclideanLin, map_sub, map_smul,
    Matrix.toLpLin_mul_same, Matrix.toLpLin_one, Module.End.mul_eq_comp, Module.End.one_eq_id] using
      congrArg Matrix.toEuclideanLin (collective_commutator N)

private lemma number_U (N : ℕ) : number N * U N - U N * number N = U N := by
  simpa only [U, number, Matrix.toEuclideanLin, map_sub, Matrix.toLpLin_mul_same, Module.End.mul_eq_comp] using
    congrArg Matrix.toEuclideanLin (number_raising N)

private lemma number_L (N : ℕ) : number N * L N - L N * number N = -L N := by
  simpa only [L, number, Matrix.toEuclideanLin, map_sub, map_neg, Matrix.toLpLin_mul_same, Module.End.mul_eq_comp] using
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
  simp only [numberMatrix, Matrix.mulVec_diagonal]

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
  calc
    _ = U N v + (t : ℂ) • U N v := sub_eq_iff_eq_add.mp hc
    _ = _ := by module

private lemma L_rank_succ {N t : ℕ} {v : Space N} (hv : v ∈ rankSpace N (t + 1)) :
    L N v ∈ rankSpace N t := by
  rw [mem_rank_iff] at hv ⊢
  have hc := congrArg (fun A : Module.End ℂ (Space N) => A v) (number_L N)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, map_smul,
    LinearMap.neg_apply, Nat.cast_add, Nat.cast_one] at hc
  calc
    _ = -L N v + ((t : ℂ) + 1) • L N v := sub_eq_iff_eq_add.mp hc
    _ = _ := by module

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
private def primitiveStrings (N : ℕ) : Set (Space N) :=
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
private theorem primitive_strings_span (N : ℕ) :
    Submodule.span ℂ (primitiveStrings N) = ⊤ := by
  apply top_unique
  rw [← (EuclideanSpace.basisFun (Configuration N) ℂ).toBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  apply rank_le_string_span N (occupancy x)
  intro y hy
  have hxy : x ≠ y := by intro h; subst y; exact hy rfl
  simp [EuclideanSpace.basisFun_apply, hxy]


attribute [local instance] LieRing.ofAssociativeRing

private def H (N : ℕ) : Module.End ℂ (Space N) := (N : ℂ) • 1 - (2 : ℂ) • number N

private lemma sl2 (N : ℕ) (hN : 0 < N) : IsSl2Triple (H N) (L N) (U N) := by
  refine ⟨?_, commutator N, ?_, ?_⟩
  · intro h
    let x : Configuration N := fun _ => 1
    let v : Space N := EuclideanSpace.single x 1
    have hz := congrArg (fun A : Module.End ℂ (Space N) => A v x) h
    have hx : occupancy x = 0 := by simp [occupancy, x]
    simp [H, number_apply, v, hx] at hz
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)) hz
  · change H N * L N - L N * H N = 2 • L N
    dsimp [H]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    have h := number_L N
    calc
      _ = (-2 : ℂ) • (number N * L N - L N * number N) := by module
      _ = _ := by rw [h]; simp only [smul_neg, neg_smul, neg_neg, two_smul]
  · change H N * U N - U N * H N = -(2 • U N)
    dsimp [H]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    have h := number_U N
    calc
      _ = (-2 : ℂ) • (number N * U N - U N * number N) := by module
      _ = _ := by rw [h]; simp only [neg_smul, two_smul]

private lemma primitive_weight {N t : ℕ} {v : Space N} (hv : v ∈ primitive N t) :
    H N v = ((N : ℂ) - 2 * t) • v := by
  have ht := (mem_rank_iff N t v).mp hv.1
  simp only [H, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, ht]
  module

private lemma primitive_data {N t : ℕ} (hN : 0 < N) {v : Space N}
    (hv : v ∈ primitive N t) (hne : v ≠ 0) :
    (sl2 N hN).HasPrimitiveVectorWith v ((N : ℂ) - 2 * t) :=
  ⟨hne, primitive_weight hv, hv.2⟩

private lemma primitive_recurrence {N t : ℕ} (hN : 0 < N) {v : Space N}
    (hv : v ∈ primitive N t) (q : ℕ) :
    L N ((U N ^ (q + 1)) v) =
      (((q : ℂ) + 1) * ((N : ℂ) - 2 * t - q)) • ((U N ^ q) v) := by
  by_cases hne : v = 0
  · subst v; simp
  · exact (primitive_data hN hv hne).lie_e_pow_succ_toEnd_f q

private lemma primitive_endpoint {N t : ℕ} (hN : 0 < N) (ht : 2 * t ≤ N)
    {v : Space N} (hv : v ∈ primitive N t) :
    (U N ^ (N - 2 * t + 1)) v = 0 := by
  by_cases hne : v = 0
  · subst v; simp
  · have he : (N : ℂ) - 2 * t = ((N - 2 * t : ℕ) : ℂ) := by
      rw [Nat.cast_sub ht, Nat.cast_mul, Nat.cast_ofNat]
    exact (primitive_data hN hv hne).pow_toEnd_f_eq_zero_of_eq_nat he

private lemma primitive_degree {N t : ℕ} {v : Space N} (hv : v ∈ primitive N t)
    (hne : v ≠ 0) : 2 * t ≤ N := by
  have h := congrArg (fun A : Module.End ℂ (Space N) => A v) (commutator N)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, (show L N v = 0 from hv.2), map_zero, sub_zero,
    LinearMap.smul_apply, Module.End.one_apply, (mem_rank_iff N t v).mp hv.1] at h
  have hn : ‖U N v‖ ^ 2 = ((N : ℝ) - 2 * t) * ‖v‖ ^ 2 := by
    have hh : L N (U N v) = ((N : ℂ) - 2 * t) • v := h.trans (by module)
    have he := inner_U N v (U N v)
    rw [hh, inner_smul_right, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K] at he
    apply Complex.ofReal_injective
    push_cast
    exact he
  have hvp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have : (2 * t : ℝ) ≤ N := by nlinarith [sq_nonneg ‖U N v‖]
  exact_mod_cast this

/-- Finite primitive strings, including every starting vector and every multiplicity. -/
def finitePrimitiveStrings (S : ℕ) : Set (Space (2 * S)) :=
  {w | ∃ t, t ≤ S ∧ ∃ v, v ∈ primitive (2 * S) t ∧
    ∃ q : ℕ, q ≤ 2 * S - 2 * t ∧ w = (U (2 * S) ^ q) v}

private lemma finite_strings_span (S : ℕ) (hS : 1 ≤ S) :
    Submodule.span ℂ (finitePrimitiveStrings S) = ⊤ := by
  rw [← primitive_strings_span (2 * S)]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨t, ht, v, hv, q, hq, rfl⟩
    exact Submodule.subset_span ⟨t, v, hv, q, rfl⟩
  · apply Submodule.span_le.mpr
    rintro w ⟨t, v, hv, q, rfl⟩
    by_cases hzero : v = 0
    · simp [hzero]
    have ht : t ≤ S := by have := primitive_degree hv hzero; omega
    by_cases hq : q ≤ 2 * S - 2 * t
    · exact Submodule.subset_span ⟨t, ht, v, hv, q, hq, rfl⟩
    · have hz := primitive_endpoint (by omega : 0 < 2 * S) (by omega : 2 * t ≤ 2 * S) hv
      rw [show q = (q - (2 * S - 2 * t + 1)) + (2 * S - 2 * t + 1) by omega,
        pow_add, Module.End.mul_apply, hz, map_zero]
      exact Submodule.zero_mem _

private lemma U_pow_rank {N t : ℕ} {v : Space N} (hv : v ∈ rankSpace N t) (q : ℕ) :
    (U N ^ q) v ∈ rankSpace N (t + q) := by
  induction q with
  | zero => simpa using hv
  | succ q ih => simpa [pow_succ', Module.End.mul_apply, Nat.add_assoc] using U_rank ih

private lemma string_Z {S t : ℕ} {v : Space (2 * S)} (ht : t ≤ S)
    (hv : v ∈ primitive (2 * S) t) (q : ℕ) :
    Z (2 * S) ((U (2 * S) ^ q) v) =
      (-(S - t : ℕ) + (q : ℂ)) • ((U (2 * S) ^ q) v) := by
  have h := (mem_rank_iff _ _ _).mp (U_pow_rank hv.1 q)
  simp only [Z, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h]
  rw [Nat.cast_add, Nat.cast_sub ht, Nat.cast_mul, Nat.cast_ofNat]
  module
private lemma primitive_inner_power {N t : ℕ} (hN : 0 < N) (ht : 2 * t ≤ N)
    {v : Space N} (hv : v ∈ primitive N t) (q : ℕ) (hq : q ≤ N - 2 * t) :
    inner ℂ ((U N ^ q) v) ((U N ^ q) v) =
      ((q.factorial * (N - 2 * t).descFactorial q : ℕ) : ℂ) * inner ℂ v v := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      inner ℂ ((U N ^ (q + 1)) v) ((U N ^ (q + 1)) v) =
          inner ℂ ((U N ^ q) v) (L N ((U N ^ (q + 1)) v)) := by
        simpa only [pow_succ', Module.End.mul_apply] using
          inner_U N ((U N ^ q) v) ((U N ^ (q + 1)) v)
      _ = (((q : ℂ) + 1) * ((N : ℂ) - 2 * t - q)) *
          inner ℂ ((U N ^ q) v) ((U N ^ q) v) := by
        rw [primitive_recurrence hN hv q, inner_smul_right]
      _ = ((q.succ.factorial * (N - 2 * t).descFactorial q.succ : ℕ) : ℂ) *
          inner ℂ v v := by
        rw [ih (by omega), Nat.factorial_succ, Nat.descFactorial_succ]
        push_cast
        rw [Nat.cast_sub (by omega : q ≤ N - 2 * t), Nat.cast_sub ht]
        push_cast
        ring

private lemma primitive_orthogonal {N t t' : ℕ} {v w : Space N}
    (hv : v ∈ primitive N t) (hw : w ∈ primitive N t') (ht : t ≠ t') :
    inner ℂ v w = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : occupancy x = t
  · have he : occupancy x ≠ t' := by omega
    simp [(show ∀ x, occupancy x ≠ t' → w x = 0 from hw.1) x he]
  · simp [(show ∀ x, occupancy x ≠ t → v x = 0 from hv.1) x hx]

private lemma inner_power_unequal {N t t' : ℕ} (hN : 0 < N)
    {v w : Space N} (hv : v ∈ primitive N t) (hw : w ∈ primitive N t') :
    ∀ q r : ℕ, q ≠ r → inner ℂ ((U N ^ q) v) ((U N ^ r) w) = 0 := by
  intro q
  induction q with
  | zero =>
    intro r hr
    cases r with
    | zero => exact (hr rfl).elim
    | succ r =>
      have h := inner_U N ((U N ^ r) w) v
      rw [hv.2, inner_zero_right] at h
      simp only [pow_zero, Module.End.one_apply]
      rw [inner_eq_zero_symm]
      simpa only [pow_succ', Module.End.mul_apply] using h
  | succ q ih =>
    intro r hr
    cases r with
    | zero =>
      simpa only [pow_zero, Module.End.one_apply, pow_succ', Module.End.mul_apply,
        inner_U, (show L N w = 0 from hw.2), inner_zero_right]
    | succ r =>
      rw [pow_succ' (U N) q, Module.End.mul_apply]
      rw [inner_U, primitive_recurrence hN hw r, inner_smul_right,
        ih r (by omega), mul_zero]



private lemma inner_power_orthogonal {N t t' : ℕ} (hN : 0 < N)
    {v w : Space N} (hv : v ∈ primitive N t) (hw : w ∈ primitive N t')
    (hvw : inner ℂ v w = 0) (q r : ℕ) :
    inner ℂ ((U N ^ q) v) ((U N ^ r) w) = 0 := by
  by_cases hqr : q = r
  · subst r
    induction q with
    | zero => simpa using hvw
    | succ q ih =>
      calc
        inner ℂ ((U N ^ (q + 1)) v) ((U N ^ (q + 1)) w) =
            inner ℂ ((U N ^ q) v) (L N ((U N ^ (q + 1)) w)) := by
          simpa only [pow_succ', Module.End.mul_apply] using
            inner_U N ((U N ^ q) v) ((U N ^ (q + 1)) w)
        _ = 0 := by
          rw [primitive_recurrence hN hw q, inner_smul_right, ih, mul_zero]
  · exact inner_power_unequal hN hv hw q r hqr

/-- Exact finite primitive-string algebra on every Boolean multiplicity.
The cardinality formula, a selected orthonormal string basis, and its native-spin
unitary are separate obligations. -/
theorem result (S : ℕ) (hS : 1 ≤ S) :
    Submodule.span ℂ (finitePrimitiveStrings S) = ⊤ ∧
    (∀ (t : ℕ) (v : Space (2 * S)), v ∈ primitive (2 * S) t → v ≠ 0 → t ≤ S) ∧
    (∀ (t : ℕ), t ≤ S → ∀ (v : Space (2 * S)), v ∈ primitive (2 * S) t →
      (U (2 * S) ^ (2 * S - 2 * t + 1)) v = 0 ∧
      ∀ q : ℕ,
        L (2 * S) ((U (2 * S) ^ (q + 1)) v) =
          (((q : ℂ) + 1) * (((2 * S : ℕ) : ℂ) - 2 * (t : ℂ) - q)) • ((U (2 * S) ^ q) v) ∧
        Z (2 * S) ((U (2 * S) ^ q) v) =
          (-((S - t : ℕ) : ℂ) + q) • ((U (2 * S) ^ q) v) ∧
        (q ≤ 2 * S - 2 * t →
          inner ℂ ((U (2 * S) ^ q) v) ((U (2 * S) ^ q) v) =
            ((q.factorial * (2 * S - 2 * t).descFactorial q : ℕ) : ℂ) * inner ℂ v v)) ∧
    (∀ (t t' : ℕ) (v w : Space (2 * S)),
      v ∈ primitive (2 * S) t → w ∈ primitive (2 * S) t' →
      (t ≠ t' → inner ℂ v w = 0) ∧
      (inner ℂ v w = 0 → ∀ q r : ℕ,
        inner ℂ ((U (2 * S) ^ q) v) ((U (2 * S) ^ r) w) = 0)) := by
  have hN : 0 < 2 * S := by omega
  refine ⟨finite_strings_span S hS, ?_, ?_, ?_⟩
  · intro t v hv hne
    have := primitive_degree hv hne
    omega
  · intro t ht v hv
    refine ⟨primitive_endpoint hN (by omega) hv, fun q => ?_⟩
    exact ⟨primitive_recurrence hN hv q, string_Z ht hv q,
      fun hq => primitive_inner_power hN (by omega) hv q hq⟩
  · intro t t' v w hv hw
    exact ⟨primitive_orthogonal hv hw, fun hzero q r =>
      inner_power_orthogonal hN hv hw hzero q r⟩



private def occupiedSet {N : ℕ} (x : Configuration N) : Finset (Fin N) :=
  Finset.univ.filter fun i => x i = 0

private lemma occupiedSet_card {N : ℕ} (x : Configuration N) :
    (occupiedSet x).card = occupancy x := by
  simp only [occupiedSet, occupancy, Finset.card_filter]

private def configurationEquiv (N : ℕ) : Configuration N ≃ Finset (Fin N) where
  toFun := occupiedSet
  invFun s i := if i ∈ s then 0 else 1
  left_inv x := by
    funext i
    simp only [occupiedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    generalize x i = b
    fin_cases b <;> simp
  right_inv s := by
    ext i
    simp [occupiedSet]

private def rankConfigurationEquiv (N t : ℕ) :
    {x : Configuration N // occupancy x = t} ≃ {s : Finset (Fin N) // s.card = t} where
  toFun x := ⟨configurationEquiv N x, by simpa [configurationEquiv, occupiedSet_card] using x.property⟩
  invFun s := ⟨(configurationEquiv N).symm s, by
    rw [← occupiedSet_card]
    change ((configurationEquiv N) ((configurationEquiv N).symm s)).card = t
    simpa using s.property⟩
  left_inv x := by apply Subtype.ext; exact (configurationEquiv N).left_inv x
  right_inv s := by apply Subtype.ext; exact (configurationEquiv N).right_inv s

private def rankEquiv (N t : ℕ) :
    rankSpace N t ≃ₗ[ℂ] ({x : Configuration N // occupancy x = t} → ℂ) where
  toFun v x := v.val x.val
  invFun w := ⟨WithLp.toLp 2 (fun x => if h : occupancy x = t then w ⟨x,h⟩ else 0), by
    intro x hx
    simp [hx]⟩
  left_inv v := by
    apply Subtype.ext
    ext x
    by_cases hx : occupancy x = t
    · simp [hx]
    · simp [hx, v.property x hx]
  right_inv w := by funext x; simp [x.property]
  map_add' v w := by rfl
  map_smul' c v := by rfl

private lemma rank_finrank (N t : ℕ) :
    Module.finrank ℂ (rankSpace N t) = N.choose t := by
  rw [(rankEquiv N t).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_congr (rankConfigurationEquiv N t), Fintype.card_finset_len,
    Fintype.card_fin]

private lemma U_injective_rank {N t : ℕ} (ht : 2 * t < N) {v : Space N}
    (hv : v ∈ rankSpace N t) (hz : U N v = 0) : v = 0 := by
  have hc := congrArg (fun A : Module.End ℂ (Space N) => A v) (commutator N)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hz, map_zero, zero_sub,
    LinearMap.smul_apply, Module.End.one_apply, (mem_rank_iff N t v).mp hv] at hc
  have he := congrArg (fun w : Space N => inner ℂ w v) hc
  simp only [inner_neg_left, inner_U, inner_sub_left, inner_smul_left,
    inner_self_eq_norm_sq_to_K] at he
  have hr : -(‖L N v‖ ^ 2) = ((N : ℝ) - 2 * t) * ‖v‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    norm_num only [map_ofNat, map_natCast] at he
    convert he using 1 <;> ring
  have hp : 0 < (N : ℝ) - 2 * t := by
    have ht' : (2 : ℝ) * t < N := by exact_mod_cast ht
    linarith
  by_contra hv0
  have hpos := mul_pos hp (sq_pos_of_pos (norm_pos_iff.mpr hv0))
  linarith [sq_nonneg ‖L N v‖]

private lemma rank_split (N t : ℕ) :
    (rankSpace N t).map (U N) ⊔ primitive N (t + 1) = rankSpace N (t + 1) := by
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨v,hv,rfl⟩; exact U_rank hv
    · exact inf_le_left
  · intro v hv
    let K := (rankSpace N t).map (U N)
    obtain ⟨a,ha,b,hb,hab⟩ := K.exists_add_mem_mem_orthogonal v
    obtain ⟨w,hw,rfl⟩ := ha
    have hbRank : b ∈ rankSpace N (t+1) := by
      simpa [hab] using (rankSpace N (t+1)).sub_mem hv (U_rank hw)
    have hz := (Submodule.mem_orthogonal K b).mp hb (U N (L N b))
      ⟨L N b, L_rank_succ hbRank, rfl⟩
    rw [inner_U] at hz
    rw [hab]
    exact Submodule.add_mem_sup ⟨w,hw,rfl⟩ ⟨hbRank, inner_self_eq_zero.mp hz⟩

private lemma rank_split_disjoint (N t : ℕ) :
    Disjoint ((rankSpace N t).map (U N)) (primitive N (t+1)) := by
  rw [Submodule.disjoint_def]
  rintro v ⟨w,hw,rfl⟩ hv
  have he := inner_U N w (U N w)
  rw [show L N (U N w) = 0 from hv.2, inner_zero_right] at he
  exact inner_self_eq_zero.mp he

/-- The previous binomial coefficient is zero, rather than choose(N,0), at rank zero. -/
def previousChoose (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => N.choose t

private lemma primitive_zero_eq (N : ℕ) : primitive N 0 = rankSpace N 0 := by
  apply le_antisymm inf_le_left
  intro v hv
  exact ⟨hv, L_rank_zero hv⟩

/-- The multiplicity is derived from the actual rank split and injectivity. -/
theorem primitive_multiplicity (S t : ℕ) (ht : t ≤ S) :
    Module.finrank ℂ (primitive (2 * S) t) =
      (2 * S).choose t - previousChoose (2 * S) t := by
  cases t with
  | zero =>
    rw [primitive_zero_eq, rank_finrank]
    simp [previousChoose]
  | succ t =>
    let f : rankSpace (2*S) t →ₗ[ℂ] Space (2*S) := (U (2*S)).comp (rankSpace (2*S) t).subtype
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      apply Subtype.ext
      exact U_injective_rank (by omega) v.property hv
    have hrange : LinearMap.range f = (rankSpace (2*S) t).map (U (2*S)) := by
      ext v
      simp [f, LinearMap.mem_range, Submodule.mem_map]
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      ((rankSpace (2*S) t).map (U (2*S))) (primitive (2*S) (t+1))
    rw [rank_split, (rank_split_disjoint (2*S) t).eq_bot, Submodule.finrank_bot, add_zero,
      ← hrange, LinearMap.finrank_range_of_inj hinj, rank_finrank, rank_finrank] at hdim
    simp only [previousChoose]
    omega

/-- A basis of each actual primitive subspace; no multiplicity is assumed. -/
def primitiveBasis (N t : ℕ) := stdOrthonormalBasis ℂ (primitive N t)

/-- One label for every primitive copy and every position in its full string. -/
abbrev StringIndex (S : ℕ) :=
  (t : Fin (S + 1)) × (Fin (Module.finrank ℂ (primitive (2 * S) t)) ×
    Fin (2 * S - 2 * t + 1))

private def rawString (S : ℕ) (a : StringIndex S) : Space (2 * S) :=
  (U (2 * S) ^ a.2.2.val) (primitiveBasis (2 * S) a.1 a.2.1)

/-- Normalize each raising string in the actual complex Hilbert space. -/
def normalizedString (S : ℕ) (a : StringIndex S) : Space (2 * S) :=
  (‖rawString S a‖⁻¹ : ℂ) • rawString S a

private lemma rawString_ne_zero (S : ℕ) (hS : 1 ≤ S) (a : StringIndex S) :
    rawString S a ≠ 0 := by
  have hv := (primitiveBasis (2 * S) a.1).orthonormal.norm_eq_one a.2.1
  have hinner := primitive_inner_power (by omega : 0 < 2 * S)
    (by have := a.1.isLt; omega : 2 * a.1.val ≤ 2 * S)
    (primitiveBasis (2 * S) a.1 a.2.1).property a.2.2.val (by have := a.2.2.isLt; omega)
  have hp : 0 < a.2.2.val.factorial * (2 * S - 2 * a.1.val).descFactorial a.2.2.val :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.descFactorial_pos.mpr (by have := a.2.2.isLt; omega))
  intro hz
  change inner ℂ (rawString S a) (rawString S a) = _ at hinner
  rw [hz, inner_zero_left] at hinner
  have hnorm : inner ℂ ((primitiveBasis (2 * S) a.1 a.2.1 : primitive (2 * S) a.1) : Space (2 * S))
      (primitiveBasis (2 * S) a.1 a.2.1 : Space (2 * S)) = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    change (↑‖primitiveBasis (2 * S) a.1 a.2.1‖ : ℂ) ^ 2 = 1
    rw [hv]; norm_num
  rw [hnorm, mul_one] at hinner
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp) :
    ((a.2.2.val.factorial * (2 * S - 2 * a.1.val).descFactorial a.2.2.val : ℕ) : ℂ) ≠ 0)
    hinner.symm

private lemma rawString_orthogonal (S : ℕ) (hS : 1 ≤ S) (a b : StringIndex S)
    (hab : a ≠ b) : inner ℂ (rawString S a) (rawString S b) = 0 := by
  have hN : 0 < 2 * S := by omega
  by_cases ht : a.1 = b.1
  · rcases a with ⟨t, i, q⟩
    rcases b with ⟨t', i', q'⟩
    dsimp at ht
    subst t'
    by_cases hi : i = i'
    · subst i'
      exact inner_power_unequal hN (primitiveBasis (2 * S) t i).property
        (primitiveBasis (2 * S) t i).property q.val q'.val (by
          intro he; have : q = q' := Fin.ext he; subst q'; exact hab rfl)
    · apply inner_power_orthogonal hN (primitiveBasis (2 * S) t i).property
        (primitiveBasis (2 * S) t i').property
      exact (primitiveBasis (2 * S) t).orthonormal.inner_eq_zero hi
  · apply inner_power_orthogonal hN (primitiveBasis (2 * S) a.1 a.2.1).property
      (primitiveBasis (2 * S) b.1 b.2.1).property
    exact primitive_orthogonal (primitiveBasis (2 * S) a.1 a.2.1).property
      (primitiveBasis (2 * S) b.1 b.2.1).property (by
        intro he; exact ht (Fin.ext he))

private lemma normalizedString_orthonormal (S : ℕ) (hS : 1 ≤ S) :
    Orthonormal ℂ (normalizedString S) := by
  constructor
  · intro a
    have hn : ‖rawString S a‖ ≠ 0 := norm_ne_zero_iff.mpr (rawString_ne_zero S hS a)
    simp [normalizedString, norm_smul, norm_inv, Complex.norm_real, hn]
  · intro a b hab
    simp [normalizedString, inner_smul_left, inner_smul_right,
      rawString_orthogonal S hS a b hab]

private lemma normalizedString_span (S : ℕ) (hS : 1 ≤ S) :
    Submodule.span ℂ (Set.range (normalizedString S)) = ⊤ := by
  rw [← finite_strings_span S hS]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨a.1.val, by have := a.1.isLt; omega,
      primitiveBasis (2 * S) a.1 a.2.1,
      (primitiveBasis (2 * S) a.1 a.2.1).property, a.2.2.val,
      by have := a.2.2.isLt; omega, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, v, hv, q, hq, rfl⟩
    let t' : Fin (S + 1) := ⟨t, by omega⟩
    let q' : Fin (2 * S - 2 * t + 1) := ⟨q, by omega⟩
    let b := (primitiveBasis (2 * S) t).toBasis
    have he : v = ∑ i, b.repr ⟨v, hv⟩ i • (b i : Space (2 * S)) := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        (congrArg (fun w : primitive (2 * S) t => (w : Space (2 * S)))
          (b.sum_repr ⟨v, hv⟩)).symm
    rw [he, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    let a : StringIndex S := ⟨t', i, q'⟩
    have hn : (‖rawString S a‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (rawString_ne_zero S hS a))
    have ha : (U (2 * S) ^ q) (b i : Space (2 * S)) =
        (‖rawString S a‖ : ℂ) • normalizedString S a := by
      rw [normalizedString, smul_smul, mul_inv_cancel₀ hn, one_smul]
      rfl
    rw [ha]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)


private lemma rawString_norm_sq (S : ℕ) (hS : 1 ≤ S) (a : StringIndex S) :
    ‖rawString S a‖ ^ 2 =
      (a.2.2.val.factorial * (2*S-2*a.1.val).descFactorial a.2.2.val : ℕ) := by
  have he := primitive_inner_power (by omega : 0 < 2*S)
    (by have := a.1.isLt; omega : 2*a.1.val ≤ 2*S)
    (primitiveBasis (2*S) a.1 a.2.1).property a.2.2.val (by have := a.2.2.isLt; omega)
  have hb := (primitiveBasis (2*S) a.1).orthonormal.norm_eq_one a.2.1
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at he
  change (↑‖rawString S a‖ : ℂ) ^ 2 = _ *
    (↑‖primitiveBasis (2*S) a.1 a.2.1‖ : ℂ) ^ 2 at he
  rw [hb] at he
  norm_num only [one_pow, Complex.ofReal_one, mul_one] at he
  exact_mod_cast he

private lemma rawString_norm_succ (S : ℕ) (hS : 1 ≤ S) (t : Fin (S+1))
    (i : Fin (Module.finrank ℂ (primitive (2*S) t)))
    (q : Fin (2*S-2*t.val+1)) (hq : q.val < 2*S-2*t.val) :
    ‖rawString S ⟨t,i,⟨q.val+1,by omega⟩⟩‖ =
      Real.sqrt (((q.val:ℝ)+1) * ((2*S-2*t.val:ℕ)-q.val : ℝ)) *
        ‖rawString S ⟨t,i,q⟩‖ := by
  have hp : 0 ≤ ((q.val:ℝ)+1) * ((2*S-2*t.val:ℕ)-q.val : ℝ) := by
    have : (q.val:ℝ) ≤ (2*S-2*t.val:ℕ) := by exact_mod_cast Nat.le_of_lt hq
    positivity
  have he := rawString_norm_sq S hS ⟨t,i,⟨q.val+1,by omega⟩⟩
  have he' := rawString_norm_sq S hS ⟨t,i,q⟩
  dsimp only at he he'
  rw [Nat.factorial_succ, Nat.descFactorial_succ] at he
  push_cast at he
  rw [Nat.cast_sub (Nat.le_of_lt hq)] at he
  have hs := Real.sq_sqrt hp
  have hn : ‖rawString S ⟨t,i,⟨q.val+1,by omega⟩⟩‖ ^ 2 =
      (Real.sqrt (((q.val:ℝ)+1) * ((2*S-2*t.val:ℕ)-q.val : ℝ)) *
        ‖rawString S ⟨t,i,q⟩‖) ^ 2 := by
    rw [mul_pow, hs, he']
    rw [he, Nat.cast_mul]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hn

private lemma normalizedString_U_succ (S : ℕ) (hS : 1 ≤ S) (t : Fin (S+1))
    (i : Fin (Module.finrank ℂ (primitive (2*S) t)))
    (q : Fin (2*S-2*t.val+1)) (hq : q.val < 2*S-2*t.val) :
    U (2*S) (normalizedString S ⟨t,i,q⟩) =
      (Real.sqrt (((q.val:ℝ)+1) * ((2*S-2*t.val:ℕ)-q.val : ℝ)) : ℂ) •
        normalizedString S ⟨t,i,⟨q.val+1,by omega⟩⟩ := by
  let a : StringIndex S := ⟨t,i,q⟩
  let b : StringIndex S := ⟨t,i,⟨q.val+1,by omega⟩⟩
  have hn := rawString_norm_succ S hS t i q hq
  have ha : (‖rawString S a‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (rawString_ne_zero S hS a))
  have hb : (‖rawString S b‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (rawString_ne_zero S hS b))
  have hu : U (2*S) (rawString S a) = rawString S b := by
    simp [rawString, a, b, pow_succ', Module.End.mul_apply]
  change U (2*S) (normalizedString S a) = _ • normalizedString S b
  rw [normalizedString, normalizedString, map_smul, hu, smul_smul]
  congr 1
  rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  change ‖rawString S a‖⁻¹ = _ * ‖rawString S b‖⁻¹
  have ha' : ‖rawString S a‖ ≠ 0 := norm_ne_zero_iff.mpr (rawString_ne_zero S hS a)
  have hb' : ‖rawString S b‖ ≠ 0 := norm_ne_zero_iff.mpr (rawString_ne_zero S hS b)
  dsimp [a,b] at *
  field_simp
  simpa only [mul_comm] using hn

private lemma normalizedString_U_top (S : ℕ) (hS : 1 ≤ S) (t : Fin (S+1))
    (i : Fin (Module.finrank ℂ (primitive (2*S) t))) :
    U (2*S) (normalizedString S ⟨t,i,⟨2*S-2*t.val,by omega⟩⟩) = 0 := by
  rw [normalizedString, map_smul]
  have hz := primitive_endpoint (by omega : 0 < 2*S)
    (by have := t.isLt; omega : 2*t.val ≤ 2*S) (primitiveBasis (2*S) t i).property
  have he : U (2*S) (rawString S ⟨t,i,⟨2*S-2*t.val,by omega⟩⟩) = 0 := by
    simpa [rawString, pow_succ', Module.End.mul_apply] using hz
  rw [he, smul_zero]

private lemma normalizedString_Z (S : ℕ) (hS : 1 ≤ S) (a : StringIndex S) :
    Z (2*S) (normalizedString S a) =
      (-((S-a.1.val:ℕ):ℂ)+a.2.2.val) • normalizedString S a := by
  rw [normalizedString, map_smul, rawString,
    string_Z (by have := a.1.isLt; omega) (primitiveBasis (2*S) a.1 a.2.1).property]
  rw [smul_comm]

/-- The complete orthonormal basis constructed from every primitive string. -/
def stringBasis (S : ℕ) (hS : 1 ≤ S) :
    OrthonormalBasis (StringIndex S) ℂ (Space (2 * S)) :=
  OrthonormalBasis.mk (normalizedString_orthonormal S hS)
    (by rw [normalizedString_span S hS])

/-- The coordinate unitary is obtained from the proved full-span construction. -/
def stringUnitary (S : ℕ) (hS : 1 ≤ S) :
    Space (2 * S) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (StringIndex S) :=
  (stringBasis S hS).repr


/-- Every primitive copy, with its rank retained in the label. -/
abbrev CopyIndex (S : ℕ) :=
  (t : Fin (S+1)) × Fin (Module.finrank ℂ (primitive (2*S) t))

/-- Coordinates of the direct sum of all native spin-(S-t) spaces. -/
abbrev NativeIndex (S : ℕ) := (a : CopyIndex S) × Fin (2*S-2*a.1.val+1)

private def nativeIndexEquiv (S : ℕ) : StringIndex S ≃ NativeIndex S where
  toFun a := ⟨⟨a.1,a.2.1⟩,a.2.2.rev⟩
  invFun a := ⟨a.1.1,a.1.2,a.2.rev⟩
  left_inv a := by rcases a with ⟨t,i,q⟩; simp
  right_inv a := by rcases a with ⟨⟨t,i⟩,r⟩; simp

/-- Complete native-coordinate basis; native coordinate r is 2j-k. -/
def nativeBasis (S : ℕ) (hS : 1 ≤ S) :
    OrthonormalBasis (NativeIndex S) ℂ (Space (2*S)) :=
  (stringBasis S hS).reindex (nativeIndexEquiv S)

/-- Constructed complex unitary onto every native spin block and primitive copy. -/
def nativeUnitary (S : ℕ) (hS : 1 ≤ S) :
    Space (2*S) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (NativeIndex S) :=
  (stringUnitary S hS).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (nativeIndexEquiv S))

private lemma nativeBasis_apply (S : ℕ) (hS : 1 ≤ S) (a : NativeIndex S) :
    nativeBasis S hS a = normalizedString S ⟨a.1.1,a.1.2,a.2.rev⟩ := by
  simp [nativeBasis, OrthonormalBasis.reindex_apply, nativeIndexEquiv,
    stringBasis, OrthonormalBasis.coe_mk]

open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jz)
open D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment (raising_entry)

/-- Block diagonal of the repository's native spin matrices, on every primitive copy. -/
def nativeMatrix (S : ℕ) (A : (n : ℕ) → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    Matrix (NativeIndex S) (NativeIndex S) ℂ :=
  Matrix.blockDiagonal' fun a : CopyIndex S => A (2*S-2*a.1.val)

/-- Native raising, with no top-spin or uniform-occupancy restriction. -/
def nativeU (S : ℕ) : Module.End ℂ (EuclideanSpace ℂ (NativeIndex S)) :=
  (nativeMatrix S Jplus).toEuclideanLin
/-- Native lowering is the conjugate transpose on every spin block. -/
def nativeL (S : ℕ) : Module.End ℂ (EuclideanSpace ℂ (NativeIndex S)) :=
  (nativeMatrix S (fun n => (Jplus n)ᴴ)).toEuclideanLin
/-- Native centered weight on every spin block, including spin zero. -/
def nativeZ (S : ℕ) : Module.End ℂ (EuclideanSpace ℂ (NativeIndex S)) :=
  (nativeMatrix S Jz).toEuclideanLin

private lemma nativeBasis_U (S : ℕ) (hS : 1 ≤ S) (b : CopyIndex S)
    (r : Fin (2*S-2*b.1.val+1)) :
    U (2*S) (nativeBasis S hS ⟨b,r⟩) =
      if h : 0 < r.val then
        (Real.sqrt ((r.val:ℝ)*((2*S-2*b.1.val:ℕ)+1-r.val : ℝ)) : ℂ) •
          nativeBasis S hS ⟨b,⟨r.val-1,by omega⟩⟩ else 0 := by
  by_cases hr : 0 < r.val
  · rw [dif_pos hr, nativeBasis_apply, nativeBasis_apply]
    have hq : r.rev.val < 2*S-2*b.1.val := by rw [Fin.val_rev]; omega
    rw [normalizedString_U_succ S hS b.1 b.2 r.rev hq]
    have he : (⟨r.rev.val+1,by omega⟩ : Fin (2*S-2*b.1.val+1)) =
        (⟨r.val-1,by omega⟩ : Fin (2*S-2*b.1.val+1)).rev := by
      apply Fin.ext; simp only [Fin.val_rev]; omega
    rw [he]
    congr 2
    have hrev : (r.rev.val:ℝ) = (2*S-2*b.1.val:ℕ)-r.val := by
      rw [Fin.val_rev, Nat.cast_sub (by have := r.isLt; omega)]
      push_cast; ring
    rw [hrev]
    ring
  · rw [dif_neg hr, nativeBasis_apply]
    have he : r.rev = (⟨2*S-2*b.1.val,by omega⟩ : Fin (2*S-2*b.1.val+1)) := by
      apply Fin.ext; simp only [Fin.val_rev]; omega
    rw [he]
    exact normalizedString_U_top S hS b.1 b.2

private lemma nativeBasis_Z (S : ℕ) (hS : 1 ≤ S) (b : CopyIndex S)
    (r : Fin (2*S-2*b.1.val+1)) :
    Z (2*S) (nativeBasis S hS ⟨b,r⟩) =
      ((((2*S-2*b.1.val:ℕ):ℝ)/2-r.val : ℝ):ℂ) • nativeBasis S hS ⟨b,r⟩ := by
  rw [nativeBasis_apply, normalizedString_Z S hS]
  congr 1
  have ht : b.1.val ≤ S := by have := b.1.isLt; omega
  have hd : 2*b.1.val ≤ 2*S := by omega
  have hr : r.val ≤ 2*S-2*b.1.val := by have := r.isLt; omega
  rw [Fin.val_rev]
  push_cast
  rw [Nat.cast_sub ht, Nat.cast_sub (by omega : r.val ≤ 2*S-2*b.1.val), Nat.cast_sub hd]
  push_cast
  ring

private lemma nativeMatrix_U (S : ℕ) (hS : 1 ≤ S) :
    LinearMap.toMatrix (nativeBasis S hS).toBasis (nativeBasis S hS).toBasis (U (2*S)) =
      nativeMatrix S Jplus := by
  classical
  ext ⟨c,k⟩ ⟨b,r⟩
  rw [LinearMap.toMatrix_apply, ← OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, nativeBasis_U]
  by_cases hr : 0 < r.val
  · rw [dif_pos hr, inner_smul_right,
      orthonormal_iff_ite.mp (nativeBasis S hS).orthonormal]
    by_cases hcb : c = b
    · subst c
      rw [nativeMatrix, Matrix.blockDiagonal'_apply_eq, raising_entry]
      by_cases hk : k.val+1=r.val
      · have he : k = ⟨r.val-1,by omega⟩ := Fin.ext (by omega)
        subst k
        simp [hk]
      · have he : k ≠ (⟨r.val-1,by omega⟩ : Fin (2*S-2*b.1.val+1)) := by
          intro he; have := congrArg Fin.val he; omega
        simp [hk, he]
    · rw [nativeMatrix, Matrix.blockDiagonal'_apply_ne _ _ _ hcb]
      have he : (⟨c,k⟩ : NativeIndex S) ≠ ⟨b,⟨r.val-1,by omega⟩⟩ := by
        intro he; exact hcb (congrArg Sigma.fst he)
      simp [he]
  · rw [dif_neg hr, inner_zero_right]
    by_cases hcb : c=b
    · subst c
      rw [nativeMatrix, Matrix.blockDiagonal'_apply_eq, raising_entry, if_neg (by omega)]
    · rw [nativeMatrix, Matrix.blockDiagonal'_apply_ne _ _ _ hcb]

private lemma nativeMatrix_L (S : ℕ) (hS : 1 ≤ S) :
    LinearMap.toMatrix (nativeBasis S hS).toBasis (nativeBasis S hS).toBasis (L (2*S)) =
      nativeMatrix S (fun n => (Jplus n)ᴴ) := by
  rw [← adjoint_U, LinearMap.toMatrix_adjoint, nativeMatrix_U]
  exact Matrix.blockDiagonal'_conjTranspose _

private lemma nativeMatrix_Z (S : ℕ) (hS : 1 ≤ S) :
    LinearMap.toMatrix (nativeBasis S hS).toBasis (nativeBasis S hS).toBasis (Z (2*S)) =
      nativeMatrix S Jz := by
  classical
  ext ⟨c,k⟩ ⟨b,r⟩
  rw [LinearMap.toMatrix_apply, ← OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, nativeBasis_Z, inner_smul_right,
    orthonormal_iff_ite.mp (nativeBasis S hS).orthonormal]
  by_cases hcb : c=b
  · subst c
    rw [nativeMatrix, Matrix.blockDiagonal'_apply_eq, Jz]
    by_cases hk : k=r
    · subst k; simp
    · simp [hk, Matrix.diagonal_apply_ne _ hk]
  · rw [nativeMatrix, Matrix.blockDiagonal'_apply_ne _ _ _ hcb]
    have he : (⟨c,k⟩ : NativeIndex S) ≠ ⟨b,r⟩ := by
      intro he; exact hcb (congrArg Sigma.fst he)
    simp [he]

private lemma native_intertwiner (S : ℕ) (hS : 1 ≤ S)
    (A : Module.End ℂ (Space (2*S)))
    (M : Matrix (NativeIndex S) (NativeIndex S) ℂ)
    (hM : LinearMap.toMatrix (nativeBasis S hS).toBasis (nativeBasis S hS).toBasis A = M)
    (v : Space (2*S)) :
    nativeUnitary S hS (A v) = M.toEuclideanLin (nativeUnitary S hS v) := by
  have he := A.toMatrix_mulVec_repr (nativeBasis S hS).toBasis
    (nativeBasis S hS).toBasis v
  rw [hM] at he
  ext a
  exact (congrFun he a).symm

/-- The full Boolean decomposition, with derived multiplicities and actual native intertwiners. -/
theorem native_decomposition (S : ℕ) (hS : 1 ≤ S) :
    (∀ t : Fin (S+1), Module.finrank ℂ (primitive (2*S) t) =
      (2*S).choose t - previousChoose (2*S) t) ∧
    (∀ a : NativeIndex S, nativeBasis S hS a =
      normalizedString S ⟨a.1.1,a.1.2,a.2.rev⟩) ∧
    (∀ v : Space (2*S),
      nativeUnitary S hS (U (2*S) v) = nativeU S (nativeUnitary S hS v) ∧
      nativeUnitary S hS (L (2*S) v) = nativeL S (nativeUnitary S hS v) ∧
      nativeUnitary S hS (Z (2*S) v) = nativeZ S (nativeUnitary S hS v)) := by
  refine ⟨fun t => primitive_multiplicity S t (by have := t.isLt; omega),
    nativeBasis_apply S hS, fun v => ?_⟩
  exact ⟨native_intertwiner S hS _ _ (nativeMatrix_U S hS) v,
    native_intertwiner S hS _ _ (nativeMatrix_L S hS) v,
    native_intertwiner S hS _ _ (nativeMatrix_Z S hS) v⟩

#print axioms native_decomposition
#print axioms result
#print axioms stringUnitary

end D5.S3.Quantum.SpinChains.BooleanCollectiveLadders
