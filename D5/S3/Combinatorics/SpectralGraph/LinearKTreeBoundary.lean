/- GID: D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite propagation and uniform boundary estimates for banded matrices. -/

/-
admission_basis: escape-witness
question_answered: #22865
escape_witness: pow_prefix_eq
proof_shape: content: IsBanded.pow, cross_moment_eq_zero, pow_prefix_eq, quadratic_prefix_eq, local_moment_stabilizes, boundary_moments_stabilize.
The remaining theorem declarations are consumed bind-only helpers.
Direct frozen dependencies: D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation + D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.quadratic_row_bound + sha256:57a805a7c0194ff69096ba576900fe7e68b77d08e2f8837d3665708070ec7549.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25440
increment_limit_of_affine_correction: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
IsBanded: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.IsBanded.mul, LinearKTreeBoundary.IsBanded.pow, LinearKTreeBoundary.boundary_moments_stabilize, LinearKTreeBoundary.cross_moment_eq_zero, LinearKTreeBoundary.isBanded_one, LinearKTreeBoundary.local_moment_stabilizes, LinearKTreeBoundary.pow_prefix_eq, LinearKTreeBoundary.quadratic_prefix_eq; Direct frozen dependencies: none.
isBanded_one: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.IsBanded.pow; Direct frozen dependencies: none.
IsBanded.mul: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.IsBanded.pow; Direct frozen dependencies: none.
IsBanded.pow: proof_shape: content; escape_witness: IsBanded.pow; consumers: LinearKTreeBoundary.cross_moment_eq_zero; Direct frozen dependencies: none.
cross_moment_eq_zero: proof_shape: content; escape_witness: IsBanded.pow; consumers: LinearKTreeBoundary.boundary_moments_stabilize; Direct frozen dependencies: none.
sum_eq_prefix: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.boundary_norm_bound, LinearKTreeBoundary.boundary_sum_constant, LinearKTreeBoundary.pow_prefix_eq, LinearKTreeBoundary.quadratic_prefix_eq; Direct frozen dependencies: none.
pow_prefix_eq: proof_shape: content; escape_witness: pow_prefix_eq; consumers: LinearKTreeBoundary.quadratic_prefix_eq; Direct frozen dependencies: none.
quadratic_prefix_eq: proof_shape: content; escape_witness: pow_prefix_eq; consumers: LinearKTreeBoundary.local_moment_stabilizes; Direct frozen dependencies: none.
IsReversalInvariant: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.IsReversalInvariant.pow, LinearKTreeBoundary.bilinear_reverse, LinearKTreeBoundary.boundary_moments_stabilize; Direct frozen dependencies: none.
IsReversalInvariant.pow: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.boundary_moments_stabilize; Direct frozen dependencies: none.
bilinear_reverse: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.boundary_moments_stabilize; Direct frozen dependencies: none.
local_moment_stabilizes: proof_shape: content; escape_witness: pow_prefix_eq; consumers: LinearKTreeBoundary.boundary_moments_stabilize; Direct frozen dependencies: none.
boundary_moments_stabilize: proof_shape: content; escape_witness: pow_prefix_eq; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
symmetric_bilinear_swap: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.quadratic_defect_expansion; Direct frozen dependencies: none.
quadratic_defect_expansion: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeBoundary.inverse_defect_expansion; Direct frozen dependencies: none.
inverse_defect_expansion: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
boundary_sum_constant: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
boundary_norm_bound: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
nonnegative_row_bound: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation + D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.quadratic_row_bound + sha256:57a805a7c0194ff69096ba576900fe7e68b77d08e2f8837d3665708070ec7549.
richardson_norm_bound: proof_shape: bind-only; escape_witness: none; consumers: LinearKTreeResistance.result; Direct frozen dependencies: none.
-/
import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.Matrix.Order
import D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation

open Filter
open scoped Topology

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary

theorem increment_limit_of_affine_correction
    (R c : ℕ → ℝ) (d C : ℝ)
    (hc : Tendsto c atTop (𝓝 C))
    (hR : ∀ᶠ n in atTop, R n = (n : ℝ) * d + c n) :
    Tendsto (fun n => R (n + 1) - R n) atTop (𝓝 d) := by
  have hc' : Tendsto (fun n => c (n + 1) - c n) atTop (𝓝 0) := by
    simpa using (hc.comp (tendsto_add_atTop_nat 1)).sub hc
  have ht : Tendsto (fun n => d + (c (n + 1) - c n)) atTop (𝓝 d) := by
    simpa using tendsto_const_nhds.add hc'
  apply ht.congr'
  filter_upwards [hR, (tendsto_add_atTop_nat 1).eventually hR] with n hn hn'
  rw [hn, hn']
  push_cast
  ring

end D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary

open Matrix
open scoped BigOperators

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary

noncomputable section

variable {n : ℕ}

def IsBanded (b : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, b < Nat.dist i.val j.val → A i j = 0

private theorem isBanded_one : IsBanded 0 (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro i j hij
  apply Matrix.one_apply_ne
  intro heq
  subst j
  simp at hij

private theorem IsBanded.mul {A B : Matrix (Fin n) (Fin n) ℝ} {b c : ℕ}
    (hA : IsBanded b A) (hB : IsBanded c B) : IsBanded (b + c) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hit : b < Nat.dist i.val t.val
  · rw [hA i t hit, zero_mul]
  · have hjt : c < Nat.dist t.val j.val := by
      have htriangle := Nat.dist.triangle_inequality i.val t.val j.val
      omega
    rw [hB t j hjt, mul_zero]

private theorem IsBanded.pow {A : Matrix (Fin n) (Fin n) ℝ} {b : ℕ}
    (hA : IsBanded b A) (L : ℕ) : IsBanded (L * b) (A ^ L) := by
  induction L with
  | zero => simpa using (isBanded_one (n := n))
  | succ L ih => simpa [pow_succ, Nat.succ_mul] using ih.mul hA

private theorem cross_moment_eq_zero {A : Matrix (Fin n) (Fin n) ℝ} {b r : ℕ}
    (hA : IsBanded b A) (L : ℕ) (a z : Fin n → ℝ)
    (ha : ∀ i, r ≤ i.val → a i = 0)
    (hz : ∀ i, i.val + r < n → z i = 0)
    (hn : L * b + 2 * r < n) :
    a ⬝ᵥ (A ^ L *ᵥ z) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hai : r ≤ i.val
  · rw [ha i hai, zero_mul]
  · have hm : (A ^ L *ᵥ z) i = 0 := by
      change ∑ j, (A ^ L) i j * z j = 0
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hzj : j.val + r < n
      · rw [hz j hzj, mul_zero]
      · have hd : L * b < Nat.dist i.val j.val := by
          simp only [Nat.dist]
          omega
        rw [hA.pow L i j hd, zero_mul]
    rw [hm, mul_zero]

private theorem sum_eq_prefix {p n : ℕ} (hpn : p ≤ n) (f : Fin n → ℝ)
    (hf : ∀ i, p ≤ i.val → f i = 0) :
    ∑ i, f i = ∑ i : Fin p, f (Fin.castLE hpn i) := by
  classical
  symm
  let e : Fin p ↪ Fin n := ⟨Fin.castLE hpn, Fin.castLE_injective hpn⟩
  change (∑ i : Fin p, f (e i)) = _
  rw [← Finset.sum_map]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hf
  by_contra h
  apply hi
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩

private theorem pow_prefix_eq {p n b : ℕ} (hpn : p ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsBanded b A) (L : ℕ)
    (i j : Fin p) (hi : i.val + L * b < p) :
    (A ^ L) (Fin.castLE hpn i) (Fin.castLE hpn j) =
      ((A.submatrix (Fin.castLE hpn) (Fin.castLE hpn)) ^ L) i j := by
  induction L generalizing i with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Fin.castLE_inj]
  | succ L ih =>
    simp only [Nat.succ_mul] at hi
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    rw [sum_eq_prefix hpn (fun t => A (Fin.castLE hpn i) t *
      (A ^ L) t (Fin.castLE hpn j)) (by
        intro t ht
        have hd : b < Nat.dist i.val t.val := by
          simp only [Nat.dist]
          omega
        rw [hA _ _ hd, zero_mul])]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [Matrix.submatrix_apply]
    by_cases hit : b < Nat.dist i.val t.val
    · rw [hA _ _ hit, zero_mul, zero_mul]
    · rw [ih t (by
        have htri := Nat.dist_tri_right i.val t.val
        omega)]

private theorem quadratic_prefix_eq {p n b r : ℕ} (hpn : p ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsBanded b A) (L : ℕ)
    (a : Fin n → ℝ) (ha : ∀ i, r ≤ i.val → a i = 0)
    (hp : r + L * b ≤ p) :
    a ⬝ᵥ (A ^ L *ᵥ a) =
      (a ∘ Fin.castLE hpn) ⬝ᵥ
        ((A.submatrix (Fin.castLE hpn) (Fin.castLE hpn)) ^ L *ᵥ
          (a ∘ Fin.castLE hpn)) := by
  classical
  unfold dotProduct
  rw [sum_eq_prefix hpn _ (by
    intro i hi
    rw [ha i (by omega), zero_mul])]
  apply Finset.sum_congr rfl
  intro i hi
  change a (Fin.castLE hpn i) * _ = a (Fin.castLE hpn i) * _
  by_cases hir : r ≤ i.val
  · rw [ha _ hir, zero_mul, zero_mul]
  · congr 1
    unfold Matrix.mulVec dotProduct
    rw [sum_eq_prefix hpn _ (by
      intro j hj
      rw [ha j (by omega), mul_zero])]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [pow_prefix_eq hpn A hA L i j (by omega)]
    rfl

def IsReversalInvariant {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, A i.rev j.rev = A i j

private theorem IsReversalInvariant.pow {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : IsReversalInvariant A) (L : ℕ) : IsReversalInvariant (A ^ L) := by
  let e := Matrix.reindexRingEquiv ℝ (Fin.revPerm : Fin N ≃ Fin N)
  have he : e A = A := by
    ext i j
    exact hA i j
  have hp := e.map_pow A L
  rw [he] at hp
  intro i j
  exact congrFun (congrFun hp i) j

private theorem bilinear_reverse {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ)
    (hB : IsReversalInvariant B) (u v : Fin N → ℝ) :
    (u ∘ Fin.rev) ⬝ᵥ (B *ᵥ (v ∘ Fin.rev)) = u ⬝ᵥ (B *ᵥ v) := by
  have hvec (i : Fin N) : (B *ᵥ (v ∘ Fin.rev)) i.rev = (B *ᵥ v) i := by
    unfold Matrix.mulVec dotProduct
    calc
      _ = ∑ j : Fin N, B i.rev j.rev * (v ∘ Fin.rev) j.rev :=
        (Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N) (fun j => B i.rev j * (v ∘ Fin.rev) j)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Function.comp_apply, Fin.rev_rev]
        rw [hB i j]
  unfold dotProduct
  calc
    _ = ∑ i : Fin N, (u ∘ Fin.rev) i.rev * (B *ᵥ (v ∘ Fin.rev)) i.rev :=
      (Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N) (fun i => (u ∘ Fin.rev) i * (B *ᵥ (v ∘ Fin.rev)) i)).symm
    _ = _ := by simp only [Function.comp_apply, Fin.rev_rev, hvec]

private theorem local_moment_stabilizes
    (A : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ) (b r q : ℕ)
    (f : ℕ → ℝ) (hf : ∀ i, r ≤ i → f i = 0)
    (hband : ∀ N, IsBanded b (A N))
    (hcoeff : ∀ (N M : ℕ) (i j : Fin N) (u v : Fin M),
      i.val = u.val → j.val = v.val → i.val + q ≤ N → u.val + q ≤ M →
        A N i j = A M u v) (L : ℕ) :
    ∃ C : ℝ, ∀ᶠ N in Filter.atTop,
      (fun i : Fin N => f i.val) ⬝ᵥ
        (A N ^ L *ᵥ (fun i : Fin N => f i.val)) = C := by
  let P := r + L * b
  let T := P + q + 1
  let hPT : P ≤ T := by dsimp [T]; omega
  refine ⟨(fun i : Fin T => f i.val) ⬝ᵥ
    (A T ^ L *ᵥ (fun i : Fin T => f i.val)), ?_⟩
  apply Filter.eventually_atTop.mpr
  refine ⟨T, fun N hN => ?_⟩
  have hPN : P ≤ N := by exact Nat.le_trans hPT hN
  rw [quadratic_prefix_eq hPN (A N) (hband N) L (fun i => f i.val)
    (fun i hi => hf i.val hi) (by rfl)]
  rw [quadratic_prefix_eq hPT (A T) (hband T) L (fun i => f i.val)
    (fun i hi => hf i.val hi) (by rfl)]
  have hm : (A N).submatrix (Fin.castLE hPN) (Fin.castLE hPN) =
      (A T).submatrix (Fin.castLE hPT) (Fin.castLE hPT) := by
    ext i j
    apply hcoeff N T _ _ _ _ rfl rfl
    · have hi := i.is_lt
      dsimp [T] at hN
      change i.val + q ≤ N
      omega
    · have hi := i.is_lt
      change i.val + q ≤ T
      dsimp [T]
      omega
  rw [hm]
  rfl

theorem boundary_moments_stabilize
    (A : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ) (b r q : ℕ)
    (f : ℕ → ℝ) (hf : ∀ i, r ≤ i → f i = 0)
    (hband : ∀ N, IsBanded b (A N))
    (hrev : ∀ N, IsReversalInvariant (A N))
    (hcoeff : ∀ (N M : ℕ) (i j : Fin N) (u v : Fin M),
      i.val = u.val → j.val = v.val → i.val + q ≤ N → u.val + q ≤ M →
        A N i j = A M u v) (L : ℕ) :
    ∃ C : ℝ, ∀ᶠ N in Filter.atTop,
      (fun i : Fin N => f i.val + f i.rev.val) ⬝ᵥ
        (A N ^ L *ᵥ (fun i : Fin N => f i.val + f i.rev.val)) = C := by
  obtain ⟨C, hC⟩ := local_moment_stabilizes A b r q f hf hband hcoeff L
  refine ⟨2 * C, ?_⟩
  filter_upwards [hC, Filter.eventually_ge_atTop (L * b + 2 * r + 1)] with N hCN hN
  let a : Fin N → ℝ := fun i => f i.val
  have ha : ∀ i : Fin N, r ≤ i.val → a i = 0 := fun i hi => hf i.val hi
  have hz : ∀ i : Fin N, i.val + r < N → (a ∘ Fin.rev) i = 0 := by
    intro i hi
    apply hf
    simp only [Fin.val_rev]
    omega
  have hcross := cross_moment_eq_zero (hband N) L a (a ∘ Fin.rev) ha hz (by omega)
  have hcross' : (a ∘ Fin.rev) ⬝ᵥ (A N ^ L *ᵥ a) = 0 := by
    have hr := bilinear_reverse (A N ^ L) ((hrev N).pow L) a (a ∘ Fin.rev)
    simpa only [Function.comp_assoc, Fin.rev_rev, Function.comp_def] using hr.trans hcross
  have hsame := bilinear_reverse (A N ^ L) ((hrev N).pow L) a a
  change (a + a ∘ Fin.rev) ⬝ᵥ (A N ^ L *ᵥ (a + a ∘ Fin.rev)) = _
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [hcross, hcross', hsame]
  change a ⬝ᵥ (A N ^ L *ᵥ a) = C at hCN
  rw [hCN]
  ring

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem symmetric_bilinear_swap (B : Matrix ι ι ℝ) (hB : B.IsSymm)
    (u v : ι → ℝ) : u ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (B *ᵥ u) := by exact IsSymm.dotProduct_mulVec_comm hB

private theorem quadratic_defect_expansion (B : Matrix ι ι ℝ) (hB : B.IsSymm)
    (u c : ι → ℝ) (D : ℝ) (hD : D ≠ 0)
    (h : D • (B *ᵥ u) = u + B *ᵥ c) :
    u ⬝ᵥ (B *ᵥ u) = (u ⬝ᵥ u) / D +
      ((u ⬝ᵥ c) + c ⬝ᵥ (B *ᵥ c)) / D ^ 2 := by
  have h1 := congrArg (fun v : ι → ℝ => u ⬝ᵥ v) h
  have h2 := congrArg (fun v : ι → ℝ => c ⬝ᵥ v) h
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_add] at h1 h2
  rw [symmetric_bilinear_swap B hB u c] at h1
  rw [dotProduct_comm c u] at h2
  field_simp
  nlinarith [congrArg (fun x : ℝ => D * x) h1]

theorem inverse_defect_expansion (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm)
    (hu : IsUnit Q) (u : ι → ℝ) (D : ℝ) (hD : D ≠ 0) :
    u ⬝ᵥ (Q⁻¹ *ᵥ u) = (u ⬝ᵥ u) / D +
      ((u ⬝ᵥ (D • u - Q *ᵥ u)) +
        (D • u - Q *ᵥ u) ⬝ᵥ (Q⁻¹ *ᵥ (D • u - Q *ᵥ u))) / D ^ 2 := by
  apply quadratic_defect_expansion Q⁻¹ hQ.inv u (D • u - Q *ᵥ u) D hD
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Q.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det Q).mp hu), Matrix.one_mulVec]
  abel

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary
namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary
open Matrix Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section

theorem boundary_sum_constant (r N : ℕ) (hN : r ≤ N) (f : ℕ → ℝ)
    (hf : ∀ i, r ≤ i → f i = 0) :
    (∑ i : Fin N, (f i.val + f i.rev.val)) = 2 * ∑ i : Fin r, f i.val := by
  rw [Finset.sum_add_distrib]
  have hr : (∑ i : Fin N, f i.rev.val) = ∑ i : Fin N, f i.val :=
    Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N) (fun i => f i.val)
  rw [hr, sum_eq_prefix hN (fun i => f i.val) (fun i hi => hf i.val hi)]
  simp only [Fin.val_castLE]
  ring

theorem boundary_norm_bound (r N : ℕ) (hN : r ≤ N) (f : ℕ → ℝ)
    (hf : ∀ i, r ≤ i → f i = 0) :
    ‖WithLp.toLp 2 (fun i : Fin N => f i.val + f i.rev.val)‖ ^ 2 ≤
      4 * ∑ i : Fin r, f i.val ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin N, (f i.val + f i.rev.val) ^ 2) ≤ _
  have hr : (∑ i : Fin N, f i.rev.val ^ 2) = ∑ i : Fin N, f i.val ^ 2 :=
    Equiv.sum_comp (Fin.revPerm : Fin N ≃ Fin N) (fun i => f i.val ^ 2)
  calc
    _ ≤ ∑ i : Fin N, (2 * f i.val ^ 2 + 2 * f i.rev.val ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [sq_nonneg (f i.val - f i.rev.val)]
    _ = 4 * ∑ i : Fin N, f i.val ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr]
      ring
    _ = _ := by
      rw [sum_eq_prefix hN (fun i => f i.val ^ 2) (by
        intro i hi
        rw [hf i.val hi, zero_pow (by decide : 2 ≠ 0)])]
      rfl

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary

set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonnegative_row_bound (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hentry : ∀ i j, 0 ≤ A i j) (D : ℝ) (hrow : ∀ i, ∑ j, A i j ≤ D) :
    A ≤ D • (1 : Matrix ι ι ℝ) := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul (show IsSelfAdjoint D from rfl)).sub hA)
  intro x
  simp only [star_trivial]
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  apply sub_nonneg.mpr
  have habs : ∀ i, ∑ j, |A i j| ≤ D := by
    intro i
    simpa only [abs_of_nonneg (hentry i _)] using hrow i
  have h := D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.quadratic_row_bound
    A (fun i j => hA.isSymm.apply j i) D habs x
  have hn := (le_abs_self (∑ i, ∑ j, x i * A i j * x j)).trans h
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, pow_two,
    mul_assoc] using hn

theorem richardson_norm_bound (Q : Matrix ι ι ℝ) (D : ℝ) (hD : 1 ≤ D)
    (hlo : (1 : Matrix ι ι ℝ) ≤ Q) (hhi : Q ≤ D • (1 : Matrix ι ι ℝ)) :
    ‖(1 : Matrix ι ι ℝ) - D⁻¹ • Q‖ ≤ 1 - D⁻¹ := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hinv : 0 ≤ D⁻¹ := inv_nonneg.mpr hDp.le
  have hlo' : D⁻¹ • (1 : Matrix ι ι ℝ) ≤ D⁻¹ • Q := smul_le_smul_of_nonneg_left hlo hinv
  have hhi' : D⁻¹ • Q ≤ (1 : Matrix ι ι ℝ) := by exact (inv_smul_le_iff_of_pos hDp).mpr hhi
  have hnonneg : 0 ≤ (1 : Matrix ι ι ℝ) - D⁻¹ • Q := sub_nonneg.mpr hhi'
  have hbound : (1 : Matrix ι ι ℝ) - D⁻¹ • Q ≤
      (1 - D⁻¹) • (1 : Matrix ι ι ℝ) := by
    simpa only [sub_smul, one_smul] using sub_le_sub_left hlo' (1 : Matrix ι ι ℝ)
  have hρ : 0 ≤ 1 - D⁻¹ := by
    have := (inv_le_one₀ hDp).mpr hD
    linarith
  have hHerm := hnonneg.posSemidef.1
  have hspecLo : ∀ x ∈ spectrum ℝ ((1 : Matrix ι ι ℝ) - D⁻¹ • Q), 0 ≤ x := by
    apply (algebraMap_le_iff_le_spectrum (A := Matrix ι ι ℝ) (p := IsSelfAdjoint) hHerm).mp
    simpa only [Algebra.algebraMap_eq_smul_one, zero_smul] using hnonneg
  have hspecHi : ∀ x ∈ spectrum ℝ ((1 : Matrix ι ι ℝ) - D⁻¹ • Q), x ≤ 1 - D⁻¹ := by
    apply (le_algebraMap_iff_spectrum_le (A := Matrix ι ι ℝ) (p := IsSelfAdjoint) hHerm).mp
    simpa only [Algebra.algebraMap_eq_smul_one] using hbound
  rw [← cfc_id ℝ ((1 : Matrix ι ι ℝ) - D⁻¹ • Q) hHerm]
  apply norm_cfc_le hρ
  intro x hx
  simpa only [id_eq, Real.norm_of_nonneg (hspecLo x hx)] using hspecHi x hx

end
end D5.S3.Combinatorics.SpectralGraph.LinearKTreeBoundary
