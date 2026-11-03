/- GID: D5/S3/HomologicalAlgebra/TensorNullSummand
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/TensorNullSummand
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Singular finite-semigroup tensor powers contain a null summand. -/

/-
result
proof_shape: content
escape_witness: none
admission_basis: open-problem-resolution (#22531; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25442
The public claim retains the source expressions for null summands, indecomposable
summands, multiplicity counts and diagonal tensor actions. Proofs use Mathlib's
submodule, complement, tensor-product, dimension and convergence declarations.

Per-declaration classification (all direct frozen dependencies: none):
HasNullSummand: proof_shape: definition; escape_witness: none; consumers: claim.
IsIndecomposableSummand: proof_shape: definition; escape_witness: none; consumers: IsSummandCount, invariant_decomposition.
IsSummandCount: proof_shape: definition; escape_witness: none; consumers: claim, result.
tensorAction: proof_shape: definition; escape_witness: none; consumers: claim, tensor_rank_sum_bound, exists_null_tensor_power, tensor_counts_tendsto, result.
claim: proof_shape: definition; escape_witness: none; consumers: result.
split_common_null: proof_shape: bind-only; escape_witness: none; consumers: null_summand_of_rank_bound.
common_image_rank_le: proof_shape: bind-only; escape_witness: none; consumers: null_summand_of_rank_bound.
common_kernel_codim_le: proof_shape: bind-only; escape_witness: none; consumers: null_summand_of_rank_bound.
null_summand_of_rank_bound: proof_shape: bind-only; escape_witness: none; consumers: indecomposable_top_dim_bound, exists_null_tensor_power.
tensor_power_finrank: proof_shape: bind-only; escape_witness: none; consumers: tensor_power_range_le, exists_null_tensor_power, tensor_counts_tendsto.
tensor_power_range_le: proof_shape: bind-only; escape_witness: none; consumers: tensor_rank_sum_bound.
singular_rank_lt: proof_shape: bind-only; escape_witness: none; consumers: tensor_rank_sum_bound, exists_null_tensor_power, tensor_counts_tendsto.
normalized_counts_tendsto: proof_shape: bind-only; escape_witness: none; consumers: tensor_counts_tendsto.
independent_sum: proof_shape: bind-only; escape_witness: none; consumers: invariant_decomposition.
invariant_decomposition: proof_shape: content; escape_witness: none; consumers: exists_summand_count.
exists_summand_count: proof_shape: content; escape_witness: none; consumers: result.
summand_count_upper: proof_shape: bind-only; escape_witness: none; consumers: tensor_counts_tendsto.
independent_finrank_sum_le: proof_shape: bind-only; escape_witness: none; consumers: restricted_ranks_sum_le.
internal_finrank_sum: proof_shape: bind-only; escape_witness: none; consumers: summand_count_lower.
indecomposable_restrict: proof_shape: bind-only; escape_witness: none; consumers: summand_count_lower.
restricted_ranks_sum_le: proof_shape: bind-only; escape_witness: none; consumers: summand_count_lower.
indecomposable_top_dim_bound: proof_shape: bind-only; escape_witness: none; consumers: summand_count_lower.
summand_count_lower: proof_shape: bind-only; escape_witness: none; consumers: tensor_counts_tendsto.
exists_power_separation: proof_shape: bind-only; escape_witness: none; consumers: exists_null_tensor_power.
tensor_rank_sum_bound: proof_shape: bind-only; escape_witness: none; consumers: exists_null_tensor_power, tensor_counts_tendsto.
exists_null_tensor_power: proof_shape: bind-only; escape_witness: none; consumers: result.
tensor_counts_tendsto: proof_shape: bind-only; escape_witness: none; consumers: result.

The finite-dimensional decomposition is constructed by strong induction on dimension.
The null complement and the rank, dimension and convergence bounds use upstream
constructions and normalization. No additional algebraic-closure or identity
hypothesis is needed by those private bounds.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.Analysis.SpecificLimits.Basic


/-! Nonunital representations use multiplicative maps into endomorphisms.
Tensor powers carry the diagonal action. Indecomposable summands are counted with multiplicity.
The count sequence is required to exist, independently of its universal limit assertion.
-/

namespace D5.S3.HomologicalAlgebra.TensorNullSummand

universe u v w

section Definitions

variable {k : Type u} {S : Type v} {W : Type w}
  [Field k] [Semigroup S] [AddCommGroup W] [Module k W]

/-- A copy of the one-dimensional zero-action module is an invariant direct summand. -/
def HasNullSummand (a : S → Module.End k W) : Prop :=
  ∃ L U : Submodule k W,
    Module.finrank k L = 1 ∧ IsCompl L U ∧
      (∀ s : S, ∀ x : W, x ∈ L → a s x = 0) ∧
      (∀ s : S, U ∈ (a s).invtSubmodule)

/-- A nonzero invariant subspace that has no decomposition into two nonzero
invariant subspaces. All subspaces here are subspaces of the same ambient W. -/
def IsIndecomposableSummand (a : S → Module.End k W) (P : Submodule k W) : Prop :=
  P ≠ ⊥ ∧ (∀ s : S, P ∈ (a s).invtSubmodule) ∧
    ∀ Q R : Submodule k W, Q ≤ P → R ≤ P →
      (∀ s : S, Q ∈ (a s).invtSubmodule) →
      (∀ s : S, R ∈ (a s).invtSubmodule) →
      Disjoint Q R → Q ⊔ R = P → Q = ⊥ ∨ R = ⊥

/-- The source's number of indecomposable summands, counted with multiplicity:
an internal direct-sum decomposition indexed by Fin b. -/
def IsSummandCount (a : S → Module.End k W) (b : ℕ) : Prop :=
  ∃ P : Fin b → Submodule k W,
    DirectSum.IsInternal P ∧ ∀ i : Fin b, IsIndecomposableSummand a (P i)

/-- The diagonal action on V^{⊗n}, using Mathlib's tensor-power owner. -/
def tensorAction (ρ : S →ₙ* Module.End k W) (n : ℕ) :
    S → Module.End k (TensorPower k n W) :=
  fun s => PiTensorProduct.map (fun _ : Fin n => ρ s)

end Definitions

/-- Conjecture 4.2, including its stated asymptotic consequence.
The source assumes algebraically closed k of arbitrary characteristic and finite-dimensional
representations. Nonemptiness is part of the usual semigroup convention. Singularity of every
action on a nonempty S excludes the zero vector space, without a new nonzero hypothesis.
The source defines a(n) as an asymptotic equivalent of b(n), so a(n)=(dim V)^n means the limit below.
-/
def claim : Prop :=
  ∀ (k : Type u) (S : Type v) (V : Type w)
    [Field k] [IsAlgClosed k] [Semigroup S] [Fintype S] [Nonempty S]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : S →ₙ* Module.End k V),
    (¬ ∃ e : S, ∀ s : S, e * s = s ∧ s * e = s) →
    (∀ s : S, ¬ IsUnit (ρ s)) →
      (∃ m : ℕ, 1 ≤ m ∧ HasNullSummand (tensorAction ρ m)) ∧
      (∃ b : ℕ → ℕ, ∀ n : ℕ, IsSummandCount (tensorAction ρ n) (b n)) ∧
      ∀ b : ℕ → ℕ, (∀ n : ℕ, IsSummandCount (tensorAction ρ n) (b n)) →
        Filter.Tendsto (fun n : ℕ => (b n : ℝ) / (Module.finrank k V : ℝ) ^ n)
          Filter.atTop (nhds 1)

end D5.S3.HomologicalAlgebra.TensorNullSummand

namespace D5.S3.HomologicalAlgebra.TensorNullSummand
section Split
variable {k : Type*} {S : Type*} {W : Type*} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W]


set_option maxHeartbeats 1000000 in
private theorem split_common_null (a : S → Module.End k W) :
    ∃ L U : Submodule k W,
      L ≤ (⨅ s, LinearMap.ker (a s)) ∧ IsCompl L U ∧ (⨆ s, LinearMap.range (a s)) ≤ U ∧
      Module.finrank k L + Module.finrank k ↥((⨅ s, LinearMap.ker (a s)) ⊓ (⨆ s, LinearMap.range (a s))) =
        Module.finrank k ↥(⨅ s, LinearMap.ker (a s)) := by
  classical
  let K := (⨅ s, LinearMap.ker (a s))
  let I := (⨆ s, LinearMap.range (a s))
  obtain ⟨L, hdisj, hsup⟩ := IsModularLattice.exists_disjoint_and_sup_eq (show K ⊓ I ≤ K from inf_le_left)
  have hLK : L ≤ K := by rw [← hsup]; exact le_sup_right
  have hLI : Disjoint L I := by
    rw [disjoint_iff]
    apply le_antisymm
    · calc
        L ⊓ I ≤ K ⊓ I ⊓ L := by exact le_inf (inf_le_inf hLK le_rfl) inf_le_left
        _ = ⊥ := hdisj.eq_bot
    · exact bot_le
  obtain ⟨U, hIU, hUL⟩ := hLI.symm.exists_isCompl
  refine ⟨L, U, hLK, hUL.symm, hIU, ?_⟩
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (K ⊓ I) L
  rw [hsup, hdisj.eq_bot, finrank_bot, add_zero] at hd
  simpa only [K, I, Nat.add_comm] using hd.symm

private theorem common_image_rank_le [Fintype S] (a : S → Module.End k W) :
    Module.finrank k ↥(⨆ s, LinearMap.range (a s)) ≤ ∑ s, Module.finrank k (LinearMap.range (a s)) := by
  classical
  rw [Submodule.iSup_eq_range_dfinsupp_lsum]
  exact (DFinsupp.lsum k (fun s => (LinearMap.range (a s)).subtype)).finrank_range_le.trans_eq
    (Module.finrank_directSum k (fun s => LinearMap.range (a s)))

private theorem common_kernel_codim_le [Fintype S] (a : S → Module.End k W) :
    Module.finrank k W ≤ Module.finrank k ↥(⨅ s, LinearMap.ker (a s)) +
      ∑ s, Module.finrank k (LinearMap.range (a s)) := by
  classical
  let f : W →ₗ[k] (∀ s, LinearMap.range (a s)) := LinearMap.pi (fun s => (a s).rangeRestrict)
  have hk : LinearMap.ker f = (⨅ s, LinearMap.ker (a s)) := by
    dsimp [f]
    rw [LinearMap.ker_pi]
    exact iInf_congr (fun s => (a s).ker_rangeRestrict)
  have hr := f.finrank_range_add_finrank_ker
  have hb := (LinearMap.range f).finrank_le
  rw [Module.finrank_pi_fintype] at hb
  rw [hk] at hr
  omega

private theorem null_summand_of_rank_bound [Fintype S] (a : S → Module.End k W)
    (h : 2 * ∑ s, Module.finrank k (LinearMap.range (a s)) < Module.finrank k W) :
    HasNullSummand a := by
  classical
  obtain ⟨L, U, hLK, hLU, hIU, hd⟩ := split_common_null a
  have hdim : 0 < Module.finrank k L := by
    have hki := Submodule.finrank_mono
      (show (⨅ s, LinearMap.ker (a s)) ⊓ (⨆ s, LinearMap.range (a s)) ≤ (⨆ s, LinearMap.range (a s)) from inf_le_right)
    have hi := common_image_rank_le a
    have hk := common_kernel_codim_le a
    omega
  have hL0 : L ≠ ⊥ := by
    exact Submodule.one_le_finrank_iff.mp hdim
  obtain ⟨x, hxL, hx0⟩ := (Submodule.ne_bot_iff _).mp hL0
  let Q := Submodule.span k ({x} : Set W)
  have hQL : Q ≤ L := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxL)
  obtain ⟨U', hUU', hUQ⟩ := (hLU.disjoint.symm.mono_right hQL).exists_isCompl
  refine ⟨Q, U', finrank_span_singleton hx0, hUQ.symm, ?_, ?_⟩
  · intro s y hy
    exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp (hLK (hQL hy)) s)
  · intro s
    apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (a s)).mpr
    intro y _
    exact hUU' (hIU ((le_iSup (fun s => LinearMap.range (a s)) s) ⟨y, rfl⟩))

end Split
end D5.S3.HomologicalAlgebra.TensorNullSummand


namespace D5.S3.HomologicalAlgebra.TensorNullSummand
section TensorDimension
open Module
variable {k : Type*} {V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]

/- Adapted tensor-dimension supplier:
   CFSG.LinearAlgebra.finrank_piTensorProduct, AxiomMath/CFSG,
   revision 69cb972f587a3ecc035e092253167ff2e303c962,
   CFSG/LinearAlgebra/PiTensorFinrank.lean (Apache-2.0).
   The source and full license are identified in Library/Semigroups/he2025tensor.md.
   Replace this adaptation by an import when the pinned Mathlib supplies the
   equivalent finite tensor-dimension theorem. -/
private theorem tensor_power_finrank (n : ℕ) :
    finrank k (TensorPower k n V) = (finrank k V)^n := by
  classical
  have h : finrank k (TensorPower k n V) = ∏ _ : Fin n, finrank k V := by
    rw [Module.finrank_eq_card_basis
      (Basis.piTensorProduct (fun _ : Fin n => Module.finBasis k V)), Fintype.card_pi]
    simp
  simpa using h

private theorem tensor_power_range_le (f : Module.End k V) (n : ℕ) :
    finrank k (LinearMap.range (PiTensorProduct.map (fun _ : Fin n => f))) ≤
      (finrank k (LinearMap.range f)) ^ n := by
  classical
  let g := PiTensorProduct.map (fun _ : Fin n => f.rangeRestrict)
  let h := PiTensorProduct.map (fun _ : Fin n => (LinearMap.range f).subtype)
  have hf : PiTensorProduct.map (fun _ : Fin n => f) = h.comp g := by
    rw [← PiTensorProduct.map_comp]
    congr 1
  calc
    _ ≤ finrank k (LinearMap.range h) := by
      rw [hf]
      exact Submodule.finrank_mono (LinearMap.range_comp_le_range g h)
    _ ≤ finrank k (TensorPower k n (LinearMap.range f)) := h.finrank_range_le
    _ = _ := tensor_power_finrank n

private theorem singular_rank_lt (f : Module.End k V) (hf : ¬ IsUnit f) :
    finrank k (LinearMap.range f) < finrank k V := by
  apply Submodule.finrank_lt
  exact fun h => hf ((LinearMap.isUnit_iff_range_eq_top f).mpr h)

end TensorDimension
end D5.S3.HomologicalAlgebra.TensorNullSummand

namespace D5.S3.HomologicalAlgebra.TensorNullSummand
open Filter

private theorem normalized_counts_tendsto (d C : ℕ) (hd : 0 < d) (b : ℕ → ℕ)
    (hb : ∀ n, b n ≤ d ^ n)
    (hl : ∀ n, d ^ n ≤ b n + C * (d - 1) ^ n) :
    Tendsto (fun n : ℕ => (b n : ℝ) / (d : ℝ)^n) atTop (nhds 1) := by
  have hdR : (0 : ℝ) < d := by exact Nat.cast_pos'.mpr hd
  let q : ℝ := (d - 1 : ℕ) / (d : ℝ)
  have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) hdR.le
  have hq1 : q < 1 := (div_lt_one hdR).mpr (by exact_mod_cast (show d - 1 < d by omega))
  have ht : Tendsto (fun n : ℕ => (C : ℝ) * q^n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1))
  have hlow : Tendsto (fun n : ℕ => 1 - (C : ℝ) * q^n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro n
    have hn : 0 < (d : ℝ)^n := pow_pos hdR n
    have h := hl n
    have hr : (d : ℝ)^n ≤ (b n : ℝ) + (C : ℝ) * ((d - 1 : ℕ) : ℝ)^n := by exact_mod_cast h
    rw [le_div_iff₀ hn]
    dsimp [q]
    rw [div_pow]
    have hne := ne_of_gt hn
    field_simp
    nlinarith
  · intro n
    exact (div_le_one (pow_pos hdR n)).mpr (by exact_mod_cast hb n)

end D5.S3.HomologicalAlgebra.TensorNullSummand

namespace D5.S3.HomologicalAlgebra.TensorNullSummand
section Decomposition
variable {k : Type*} {S : Type*} {W : Type*} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W]

omit [FiniteDimensional k W] in
private theorem independent_sum {ι : Type*} {κ : Type*} (P : ι → Submodule k W)
    (Q : κ → Submodule k W) (hP : iSupIndep P) (hQ : iSupIndep Q)
    (hPQ : Disjoint (⨆ i, P i) (⨆ j, Q j)) : iSupIndep (Sum.elim P Q) := by
  intro x
  cases x with
  | inl i =>
    rw [iSup_sum]
    have hdis : Disjoint (P i ⊔ ⨆ j, ⨆ (_ : (Sum.inl j : ι ⊕ κ) ≠ Sum.inl i), P j)
        (⨆ j, ⨆ (_ : (Sum.inr j : ι ⊕ κ) ≠ Sum.inl i), Q j) :=
      hPQ.mono (sup_le (le_iSup P i) (iSup_le fun j => iSup_le fun _ => le_iSup P j))
        (iSup_le fun j => iSup_le fun _ => le_iSup Q j)
    have hpi : Disjoint (P i) (⨆ j, ⨆ (_ : (Sum.inl j : ι ⊕ κ) ≠ Sum.inl i), P j) := by
      exact iSupIndep.disjoint_biSup hP (fun h => h rfl)
    exact hpi.disjoint_sup_right_of_disjoint_sup_left hdis
  | inr i =>
    rw [iSup_sum, sup_comm]
    have hdis : Disjoint (Q i ⊔ ⨆ j, ⨆ (_ : (Sum.inr j : ι ⊕ κ) ≠ Sum.inr i), Q j)
        (⨆ j, ⨆ (_ : (Sum.inl j : ι ⊕ κ) ≠ Sum.inr i), P j) :=
      hPQ.symm.mono (sup_le (le_iSup Q i) (iSup_le fun j => iSup_le fun _ => le_iSup Q j))
        (iSup_le fun j => iSup_le fun _ => le_iSup P j)
    have hqi : Disjoint (Q i) (⨆ j, ⨆ (_ : (Sum.inr j : ι ⊕ κ) ≠ Sum.inr i), Q j) := by
      exact iSupIndep.disjoint_biSup hQ (fun h => h rfl)
    exact hqi.disjoint_sup_right_of_disjoint_sup_left hdis

private theorem invariant_decomposition (a : S → Module.End k W) (P : Submodule k W)
    (hP : ∀ s, P ∈ (a s).invtSubmodule) :
    ∃ b : ℕ, ∃ Q : Fin b → Submodule k W,
      iSupIndep Q ∧ (⨆ i, Q i) = P ∧ ∀ i, IsIndecomposableSummand a (Q i) := by
  classical
  have main : ∀ d : ℕ, ∀ P : Submodule k W, Module.finrank k P = d →
      (∀ s, P ∈ (a s).invtSubmodule) →
      ∃ b : ℕ, ∃ Q : Fin b → Submodule k W,
        iSupIndep Q ∧ (⨆ i, Q i) = P ∧ ∀ i, IsIndecomposableSummand a (Q i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro P hd hP
      by_cases hzero : P = ⊥
      · subst P
        exact ⟨0, Fin.elim0, by simp [iSupIndep], by simp, fun i => Fin.elim0 i⟩
      by_cases hind : IsIndecomposableSummand a P
      · exact ⟨1, fun _ => P, iSupIndep_subsingleton _, by simp, fun _ => hind⟩
      have hs : ∃ Q R : Submodule k W, Q ≤ P ∧ R ≤ P ∧
          (∀ s, Q ∈ (a s).invtSubmodule) ∧ (∀ s, R ∈ (a s).invtSubmodule) ∧
          Disjoint Q R ∧ Q ⊔ R = P ∧ Q ≠ ⊥ ∧ R ≠ ⊥ := by
        have hn := hind
        simp only [IsIndecomposableSummand, hP] at hn
        push Not at hn
        exact hn hzero (fun _ => trivial)
      obtain ⟨Q, R, hQP, hRP, hQ, hR, hQR, hsup, hQ0, hR0⟩ := hs
      have hQP' : Q < P := lt_of_le_of_ne hQP (by
        intro heq
        have ht : Disjoint P R := heq ▸ hQR
        exact hR0 (ht.symm.eq_bot_of_le hRP))
      have hRP' : R < P := lt_of_le_of_ne hRP (by
        intro heq
        have ht : Disjoint Q P := heq ▸ hQR
        exact hQ0 (ht.eq_bot_of_le hQP))
      obtain ⟨b, B, hBI, hBP, hBind⟩ := ih (Module.finrank k Q)
        (by simpa [hd] using Submodule.finrank_lt_finrank_of_lt hQP') Q rfl hQ
      obtain ⟨c, C, hCI, hCP, hCind⟩ := ih (Module.finrank k R)
        (by simpa [hd] using Submodule.finrank_lt_finrank_of_lt hRP') R rfl hR
      let e : Fin b ⊕ Fin c ≃ Fin (b + c) := finSumFinEquiv
      let D : Fin (b+c) → Submodule k W := fun i => Sum.elim B C (e.symm i)
      refine ⟨b+c, D, (independent_sum B C hBI hCI (by rwa [hBP, hCP])).comp e.symm.injective, ?_, ?_⟩
      · dsimp [D]
        rw [e.symm.surjective.iSup_comp, iSup_sum]
        simpa only [Sum.elim_inl, Sum.elim_inr, hBP, hCP] using hsup
      · intro i
        cases he : e.symm i with
        | inl j => simpa [D, he] using hBind j
        | inr j => simpa [D, he] using hCind j
  exact main (Module.finrank k P) P rfl hP

private theorem exists_summand_count (a : S → Module.End k W) : ∃ b, IsSummandCount a b := by
  obtain ⟨b, Q, hQI, hQtop, hind⟩ := invariant_decomposition a ⊤
    (fun s => Module.End.invtSubmodule.top_mem (a s))
  exact ⟨b, Q, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hQI hQtop, hind⟩

private theorem summand_count_upper (a : S → Module.End k W) (b : ℕ)
    (hb : IsSummandCount a b) : b ≤ Module.finrank k W := by
  classical
  obtain ⟨P, hP, hind⟩ := hb
  have hn : ∀ i, P i ≠ ⊥ := fun i => (hind i).1
  have h := hP.submodule_iSupIndep.subtype_ne_bot_le_finrank
  have he : Fintype.card {i : Fin b // P i ≠ ⊥} = b := by
    have e : {i : Fin b // P i ≠ ⊥} ≃ Fin b :=
      Equiv.subtypeUnivEquiv hn
    exact (Fintype.card_congr e).trans (Fintype.card_fin b)
  rwa [he] at h

end Decomposition
end D5.S3.HomologicalAlgebra.TensorNullSummand

namespace D5.S3.HomologicalAlgebra.TensorNullSummand
section CountBounds
variable {k : Type*} {S : Type*} {W : Type*} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W]

private theorem independent_finrank_sum_le {ι : Type*} [Fintype ι]
    (P : ι → Submodule k W) (hP : iSupIndep P) (Q : Submodule k W)
    (hQ : ∀ i, P i ≤ Q) : (∑ i, Module.finrank k (P i)) ≤ Module.finrank k Q := by
  classical
  let f := DirectSum.coeLinearMap P
  have hf : Function.Injective f := hP.dfinsupp_lsum_injective
  have hr : LinearMap.range f ≤ Q := by
    rw [DirectSum.range_coeLinearMap]
    exact iSup_le hQ
  calc
    _ = Module.finrank k (LinearMap.range f) := by
      rw [LinearMap.finrank_range_of_inj hf, Module.finrank_directSum]
    _ ≤ _ := Submodule.finrank_mono hr

private theorem internal_finrank_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Submodule k W) (hP : DirectSum.IsInternal P) :
    (∑ i, Module.finrank k (P i)) = Module.finrank k W := by
  classical
  have h := (LinearEquiv.ofBijective (DirectSum.coeLinearMap P) hP).finrank_eq
  rwa [Module.finrank_directSum] at h

omit [FiniteDimensional k W] in
private theorem indecomposable_restrict (a : S → Module.End k W)
    (P : Submodule k W) (hP : IsIndecomposableSummand a P) :
    IsIndecomposableSummand (fun s => (a s).restrict (hP.2.1 s)) (⊤ : Submodule k P) := by
  classical
  have hPinj := P.injective_subtype
  refine ⟨?_, fun s => Module.End.invtSubmodule.top_mem _, ?_⟩
  · intro ht
    apply hP.1
    have h := congrArg (Submodule.map P.subtype) ht
    simpa using h
  · intro Q R _ _ hQ hR hQR hsup
    have hQinv : ∀ s, Q.map P.subtype ∈ (a s).invtSubmodule := by
      intro s
      exact Module.End.invtSubmodule.map_subtype_mem_of_mem_invtSubmodule
        (f := a s) (p := P) (q := Q) (hP.2.1 s) (hQ s)
    have hRinv : ∀ s, R.map P.subtype ∈ (a s).invtSubmodule := by
      intro s
      exact Module.End.invtSubmodule.map_subtype_mem_of_mem_invtSubmodule
        (f := a s) (p := P) (q := R) (hP.2.1 s) (hR s)
    have hdis : Disjoint (Q.map P.subtype) (R.map P.subtype) :=
      Submodule.disjoint_map hPinj hQR
    have hsup' : Q.map P.subtype ⊔ R.map P.subtype = P := by
      rw [← Submodule.map_sup, hsup, Submodule.map_subtype_top]
    have h := hP.2.2 (Q.map P.subtype) (R.map P.subtype)
      (P.map_subtype_le Q) (P.map_subtype_le R) hQinv hRinv hdis hsup'
    rcases h with h | h
    · left
      apply Submodule.map_injective_of_injective hPinj
      simpa using h
    · right
      apply Submodule.map_injective_of_injective hPinj
      simpa using h

private theorem restricted_ranks_sum_le {ι : Type*} [Fintype ι]
    (a : S → Module.End k W) (P : ι → Submodule k W) (hP : iSupIndep P)
    (hinv : ∀ i s, P i ∈ (a s).invtSubmodule) (s : S) :
    (∑ i, Module.finrank k (LinearMap.range ((a s).restrict (hinv i s)))) ≤
      Module.finrank k (LinearMap.range (a s)) := by
  classical
  let Q : ι → Submodule k W := fun i =>
    (LinearMap.range ((a s).restrict (hinv i s))).map (P i).subtype
  have hQP : ∀ i, Q i ≤ P i := fun i => (P i).map_subtype_le _
  have hQr : ∀ i, Q i ≤ LinearMap.range (a s) := by
    intro i x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, rfl⟩ := hy
    exact ⟨(z : W), rfl⟩
  have h := independent_finrank_sum_le Q (hP.mono hQP) (LinearMap.range (a s)) hQr
  simpa only [Q, Submodule.finrank_map_subtype_eq] using h

private theorem indecomposable_top_dim_bound [Fintype S] (a : S → Module.End k W)
    (hP : IsIndecomposableSummand a (⊤ : Submodule k W)) :
    Module.finrank k W ≤ 1 + 2 * ∑ s, Module.finrank k (LinearMap.range (a s)) := by
  classical
  by_contra hn
  have hlt : 2 * ∑ s, Module.finrank k (LinearMap.range (a s)) < Module.finrank k W := by omega
  obtain ⟨L, U, hL, hc, hzero, hinv⟩ := null_summand_of_rank_bound a hlt
  have h := hP.2.2 L U le_top le_top (fun s => by
    apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (a s)).mpr
    intro x hx
    rw [hzero s x hx]
    exact L.zero_mem) hinv hc.disjoint hc.codisjoint.eq_top
  rcases h with h | h
  · have hd : Module.finrank k L = 0 := by exact Submodule.finrank_eq_zero.mpr h
    omega
  · have ht : L = ⊤ := by simpa [h] using hc.codisjoint.eq_top
    have hd : Module.finrank k W = 1 := by
      rw [ht, finrank_top] at hL
      exact hL
    omega

private theorem summand_count_lower [Fintype S] (a : S → Module.End k W) (b : ℕ)
    (hb : IsSummandCount a b) :
    Module.finrank k W ≤ b + 2 * ∑ s, Module.finrank k (LinearMap.range (a s)) := by
  classical
  obtain ⟨P, hP, hind⟩ := hb
  let ar := fun (i : Fin b) (s : S) => (a s).restrict ((hind i).2.1 s)
  have hi : ∀ i, Module.finrank k (P i) ≤
      1 + 2 * ∑ s, Module.finrank k (LinearMap.range (ar i s)) := fun i =>
    indecomposable_top_dim_bound (ar i) (indecomposable_restrict a (P i) (hind i))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hr : (∑ i, ∑ s, Module.finrank k (LinearMap.range (ar i s))) ≤
      ∑ s, Module.finrank k (LinearMap.range (a s)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun s _ => restricted_ranks_sum_le a P
      hP.submodule_iSupIndep (fun i s => (hind i).2.1 s) s)
  rw [internal_finrank_sum P hP] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one, ← Finset.mul_sum] at hsum
  omega

end CountBounds
end D5.S3.HomologicalAlgebra.TensorNullSummand

namespace D5.S3.HomologicalAlgebra.TensorNullSummand
open Module Filter
private theorem exists_power_separation (d C : ℕ) (hd : 0 < d) :
    ∃ m : ℕ, 1 ≤ m ∧ C * (d - 1)^m < d^m := by
  have hdR : (0 : ℝ) < d := by exact Nat.cast_pos'.mpr hd
  let q : ℝ := (d - 1 : ℕ) / (d : ℝ)
  have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) hdR.le
  have hq1 : q < 1 := (div_lt_one hdR).mpr (by exact_mod_cast (show d - 1 < d by omega))
  have ht : Tendsto (fun n : ℕ => (C : ℝ) * q^n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1))
  have hsmall : ∀ᶠ n : ℕ in atTop, (C : ℝ) * q^n < 1 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨m, hm, hm1⟩ := (hsmall.and (eventually_ge_atTop 1)).exists
  refine ⟨m, hm1, ?_⟩
  dsimp [q] at hm
  rw [div_pow, ← mul_div_assoc, div_lt_one (pow_pos hdR m)] at hm
  exact_mod_cast hm

section Final
variable {k : Type*} {S : Type*} {V : Type*} [Field k] [Semigroup S]
  [Fintype S] [Nonempty S] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [Nonempty S] in
private theorem tensor_rank_sum_bound (ρ : S →ₙ* Module.End k V)
    (hsing : ∀ s, ¬ IsUnit (ρ s)) (n : ℕ) :
    (∑ s, finrank k (LinearMap.range (tensorAction ρ n s))) ≤
      Fintype.card S * (finrank k V - 1)^n := by
  classical
  have hb : ∀ s, finrank k (LinearMap.range (tensorAction ρ n s)) ≤
      (finrank k V - 1)^n := by
    intro s
    have hr := singular_rank_lt (ρ s) (hsing s)
    exact (tensor_power_range_le (ρ s) n).trans (Nat.pow_le_pow_left (by omega) n)
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hb s)
  simpa using h

private theorem exists_null_tensor_power (ρ : S →ₙ* Module.End k V)
    (hsing : ∀ s, ¬ IsUnit (ρ s)) :
    ∃ m : ℕ, 1 ≤ m ∧ HasNullSummand (tensorAction ρ m) := by
  classical
  have hd : 0 < finrank k V := (Nat.zero_le _).trans_lt
    (singular_rank_lt (ρ (Classical.choice inferInstance)) (hsing _))
  obtain ⟨m, hm1, hm⟩ := exists_power_separation (finrank k V) (2 * Fintype.card S) hd
  refine ⟨m, hm1, null_summand_of_rank_bound (tensorAction ρ m) ?_⟩
  have hb := tensor_rank_sum_bound ρ hsing m
  rw [tensor_power_finrank]
  have h2 := Nat.mul_le_mul_left 2 hb
  rw [← Nat.mul_assoc] at h2
  exact h2.trans_lt hm

private theorem tensor_counts_tendsto (ρ : S →ₙ* Module.End k V)
    (hsing : ∀ s, ¬ IsUnit (ρ s)) (b : ℕ → ℕ)
    (hb : ∀ n, IsSummandCount (tensorAction ρ n) (b n)) :
    Tendsto (fun n : ℕ => (b n : ℝ) / (finrank k V : ℝ)^n) atTop (nhds 1) := by
  classical
  have hd : 0 < finrank k V := (Nat.zero_le _).trans_lt
    (singular_rank_lt (ρ (Classical.choice inferInstance)) (hsing _))
  apply normalized_counts_tendsto (finrank k V) (2 * Fintype.card S) hd b
  · intro n
    simpa only [tensor_power_finrank] using summand_count_upper (tensorAction ρ n) (b n) (hb n)
  · intro n
    have h := summand_count_lower (tensorAction ρ n) (b n) (hb n)
    have hr := tensor_rank_sum_bound ρ hsing n
    rw [tensor_power_finrank] at h
    have h2 := Nat.mul_le_mul_left 2 hr
    rw [← Nat.mul_assoc] at h2
    exact h.trans (Nat.add_le_add_left h2 (b n))
end Final

theorem result : claim := by
  classical
  intro k S V _ _ _ _ _ _ _ _ ρ _ hsing
  refine ⟨exists_null_tensor_power ρ hsing, ?_, tensor_counts_tendsto ρ hsing⟩
  have hc : ∀ n : ℕ, ∃ b, IsSummandCount (tensorAction ρ n) b := fun n =>
    exists_summand_count (tensorAction ρ n)
  exact ⟨fun n => Classical.choose (hc n), fun n => Classical.choose_spec (hc n)⟩

end D5.S3.HomologicalAlgebra.TensorNullSummand
