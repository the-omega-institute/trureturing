/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCofactor
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCofactor
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Cofactors of row minors generate every finite real nonnegative kernel. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fintype.EquivFin

/-
The classical elementary-vector argument identifies each nonnegative circuit with an
oriented cofactor vector. Deleted-column independence selects a nonsingular row minor;
CofactorKernel.kernel_cross_identity supplies proportionality over the selected support.
The original circuit equations then recover every original row equation.

admission_basis: escape-witness
liftCof: proof_shape: bind-only; escape_witness: none; consumers: cofactorCandidates,
  circuit_cofactor_complete.
cofactorCandidates: proof_shape: bind-only; escape_witness: none;
  consumers: nonnegKernel_iff_mem_hull_cofactorCandidates.
exists_row_minor_of_linearIndependent_cols: proof_shape: bind-only; escape_witness: none;
  consumers: circuit_cofactor_complete.
circuit_cofactor_complete: proof_shape: content;
  escape_witness: support-rank/minor/proportionality inference;
  consumers: nonnegKernel_iff_mem_hull_cofactorCandidates;
  admission_basis: escape-witness.
nonnegKernel_iff_mem_hull_cofactorCandidates: proof_shape: content;
  escape_witness: exact cone characterization from circuit-to-cofactor reconstruction;
  admission_basis: escape-witness.
Escape audit unfinished for circuit_cofactor_complete and
nonnegKernel_iff_mem_hull_cofactorCandidates:
https://github.com/the-omega-institute/trureturing/issues/17856.
The retained terminal Reg registration has unresolved source binding; neither theorem
has a complete validated four-slot registration.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor

open scoped BigOperators
open NonnegativeKernelCircuit

open D5.S3.Arith.Lattices.CofactorKernel (cofactor augment kernel_cross_identity)

variable {J : Type*} [Fintype J] {m : ℕ}

/-- The signed cofactors of the selected rows and columns, extended by zero to `J`. -/
noncomputable def liftCof (B : Matrix (Fin m) J ℝ) {k : ℕ}
    (ρ : Fin k ↪ Fin m) (σ : Fin (k + 1) ↪ J) : J → ℝ := by
  classical
  exact ∑ i, Pi.single (σ i) (cofactor (B.submatrix ρ σ) i)

/-- Both orientations are allowed; the filter retains all original row equations. -/
def cofactorCandidates (B : Matrix (Fin m) J ℝ) : Set (J → ℝ) :=
  {w | ∃ k : ℕ, k ≤ m ∧ ∃ (ρ : Fin k ↪ Fin m) (σ : Fin (k + 1) ↪ J) (ε : ℝ),
    (ε = 1 ∨ ε = -1) ∧ w = ε • liftCof B ρ σ ∧ InKernel B w ∧ w ≠ 0}

private theorem exists_row_minor_of_linearIndependent_cols {m k : ℕ}
    (D : Matrix (Fin m) (Fin k) ℝ) (hD : LinearIndependent ℝ D.col) :
    ∃ ρ : Fin k ↪ Fin m, (D.submatrix ρ id).det ≠ 0 := by
  classical
  have hDrank : D.rank = k := by
    have hDt : LinearIndependent ℝ D.transpose.row := hD
    simpa only [Matrix.rank_transpose, Fintype.card_fin] using hDt.rank_matrix
  obtain ⟨ι, f, hf, hspan, hlin⟩ := exists_linearIndependent' ℝ D.row
  letI : Finite ι := Finite.of_injective f hf
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = k := by
    calc
      Fintype.card ι = Module.finrank ℝ (Submodule.span ℝ (Set.range (D.row ∘ f))) :=
        (finrank_span_eq_card hlin).symm
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range D.row)) := by rw [hspan]
      _ = D.rank := (Matrix.rank_eq_finrank_span_row D).symm
      _ = k := hDrank
  let e : Fin k ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let ρ : Fin k ↪ Fin m := ⟨fun i => f (e i), hf.comp e.injective⟩
  have hminor : LinearIndependent ℝ (D.submatrix ρ id).row := by
    change LinearIndependent ℝ (fun i : Fin k => D (f (e i)))
    exact hlin.comp (fun i : Fin k => e i) e.injective
  refine ⟨ρ, ?_⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hminor)).ne_zero

/-- Every circuit is a positive multiple of an oriented, zero-extended cofactor vector.
The selected minor has size exactly one less than the circuit support, even when the
original rows are dependent. Full original kernel membership follows from proportionality. -/
theorem circuit_cofactor_complete {B : Matrix (Fin m) J ℝ} {v : J → ℝ}
    (hv : Circuit B v) :
    ∃ k : ℕ, k ≤ m ∧ ∃ (ρ : Fin k ↪ Fin m) (σ : Fin (k + 1) ↪ J) (ε a : ℝ),
      (ε = 1 ∨ ε = -1) ∧ 0 < a ∧ (nzSupport v : Set J) = Set.range σ ∧
      cofactor (B.submatrix ρ σ) 0 ≠ 0 ∧
      InKernel B (ε • liftCof B ρ σ) ∧ ε • liftCof B ρ σ ≠ 0 ∧
      v = a • (ε • liftCof B ρ σ) := by
  classical
  let S := nzSupport v
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv.2.1
  have hiS : i ∈ S := by simpa [S, nzSupport] using hi
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
  let k := S.card - 1
  have hScard : S.card = k + 1 := by omega
  let e : Fin (k + 1) ≃ S := (Finset.equivFinOfCardEq hScard).symm
  let σ : Fin (k + 1) ↪ J :=
    ⟨fun j => (e j).val, fun a b h => e.injective (Subtype.ext h)⟩
  have hσ (j : Fin (k + 1)) : σ j ∈ nzSupport v := (e j).property
  have hsupport : (nzSupport v : Set J) = Set.range σ := by
    ext j
    constructor
    · intro hj
      refine ⟨e.symm ⟨j, hj⟩, ?_⟩
      change (e (e.symm ⟨j, hj⟩)).val = j
      rw [e.apply_symm_apply]
    · rintro ⟨t, rfl⟩
      exact hσ t
  let x : Fin (k + 1) → ℝ := fun j => v (σ j)
  have hxpos (j : Fin (k + 1)) : 0 < x j := by
    have hn : v (σ j) ≠ 0 := by simpa [nzSupport] using hσ j
    exact lt_of_le_of_ne (hv.1.1 (σ j)) hn.symm
  let T : Matrix (Fin m) (Fin (k + 1)) ℝ := B.submatrix id σ
  have hsum (r : Fin m) :
      (∑ j, B r (σ j) * x j) = ∑ j, B r j * v j := by
    calc
      (∑ j, B r (σ j) * x j) = ∑ j : S, B r j * v j := by
        change (∑ j, B r (e j).val * v (e j).val) = _
        exact e.sum_comp (fun j : S => B r j * v j)
      _ = ∑ j ∈ S, B r j * v j :=
        Finset.sum_coe_sort S (fun j : J => B r j * v j)
      _ = ∑ j, B r j * v j := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro j _ hj
        have hz : v j = 0 := by simpa [S, nzSupport] using hj
        rw [hz, mul_zero]
  have hx : Matrix.mulVec T x = 0 := by
    ext r
    change (∑ j, B r (σ j) * x j) = 0
    exact (hsum r).trans (hv.1.2 r)
  let D : Matrix (Fin m) (Fin k) ℝ := T.submatrix id Fin.succ
  let τ : Fin k → ↥((nzSupport v).erase (σ 0)) := fun j =>
    ⟨σ j.succ, Finset.mem_erase.mpr
      ⟨fun h => Fin.succ_ne_zero j (σ.injective h), hσ j.succ⟩⟩
  have hτ : Function.Injective τ := by
    intro a b h
    exact Fin.succ_injective k (σ.injective (by
      simpa [τ] using congrArg Subtype.val h))
  have hD : LinearIndependent ℝ D.col := by
    exact (circuit_deleted_cols_linearIndependent hv (hσ 0)).comp τ hτ
  have hDrank : D.rank = k := by
    have hDt : LinearIndependent ℝ D.transpose.row := hD
    simpa only [Matrix.rank_transpose, Fintype.card_fin] using hDt.rank_matrix
  have hlo : k ≤ T.rank := by
    calc
      k = D.rank := hDrank.symm
      _ ≤ T.rank := by
        simpa [D] using (Matrix.rank_submatrix_le T id Fin.succ)
  have hker : LinearMap.ker T.mulVecLin ≠ ⊥ := by
    intro hz
    have hxmem : x ∈ LinearMap.ker T.mulVecLin := hx
    rw [hz, Submodule.mem_bot] at hxmem
    exact (hxpos 0).ne' (congrFun hxmem 0)
  have hnull : 1 ≤ Module.finrank ℝ (LinearMap.ker T.mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hker
  have hdim := LinearMap.finrank_range_add_finrank_ker T.mulVecLin
  change T.rank + Module.finrank ℝ (LinearMap.ker T.mulVecLin) =
    Module.finrank ℝ (Fin (k + 1) → ℝ) at hdim
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  have hrank : T.rank = k := by omega
  have hk : k ≤ m := by
    rw [← hrank]
    exact Matrix.rank_le_height T
  obtain ⟨ρ, hρ⟩ := exists_row_minor_of_linearIndependent_cols D hD
  let A : Matrix (Fin k) (Fin (k + 1)) ℝ := B.submatrix ρ σ
  let c := cofactor A
  have hminor : A.submatrix id (0 : Fin (k + 1)).succAbove = D.submatrix ρ id := by
    ext r j
    rfl
  have hc0 : c 0 ≠ 0 := by
    change (-1 : ℝ) ^ (0 : Fin (k + 1)).val *
      (A.submatrix id (0 : Fin (k + 1)).succAbove).det ≠ 0
    simpa only [Fin.val_zero, pow_zero, one_mul, hminor] using hρ
  have hAx : Matrix.mulVec A x = 0 := by
    ext r
    change (∑ j, B (ρ r) (σ j) * x j) = 0
    exact (hsum (ρ r)).trans (hv.1.2 (ρ r))
  let H : ℝ := ∑ j, x j
  let δ : ℝ := (augment A).det
  have hH : 0 < H := Finset.sum_pos (fun j _ => hxpos j) Finset.univ_nonempty
  have hcross (j : Fin (k + 1)) : δ * x j = H * c j :=
    kernel_cross_identity A x hAx j
  have hδ : δ ≠ 0 := by
    intro hz
    have he := hcross 0
    rw [hz, zero_mul] at he
    exact (mul_ne_zero hH.ne' hc0) he.symm
  have hratio (j : Fin (k + 1)) : x j = H / δ * c j := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hδ).mpr
    calc
      x j * δ = δ * x j := mul_comm _ _
      _ = H * c j := hcross j
  obtain ⟨ε, a, hε, ha, hpro⟩ :
      ∃ ε a : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < a ∧
        ∀ j, x j = a * (ε * c j) := by
    rcases lt_or_gt_of_ne hδ with hneg | hpos
    · refine ⟨-1, H / (-δ), Or.inr rfl, div_pos hH (neg_pos.mpr hneg), ?_⟩
      intro j
      simpa only [div_neg, neg_mul, one_mul, mul_neg, neg_neg] using hratio j
    · refine ⟨1, H / δ, Or.inl rfl, div_pos hH hpos, ?_⟩
      intro j
      simpa only [one_mul] using hratio j
  have hlift (j : Fin (k + 1)) : liftCof B ρ σ (σ j) = c j := by
    simp [liftCof, Finset.sum_apply, Pi.single_apply, σ.injective.eq_iff, c, A]
  have heq : v = a • (ε • liftCof B ρ σ) := by
    funext j
    by_cases hj : j ∈ Set.range σ
    · obtain ⟨t, rfl⟩ := hj
      change x t = a * (ε * liftCof B ρ σ (σ t))
      rw [hlift]
      exact hpro t
    · have hvj : v j = 0 := by
        have hjv : j ∉ nzSupport v := by
          intro h
          have hmem : j ∈ (nzSupport v : Set J) := h
          rw [hsupport] at hmem
          exact hj hmem
        simpa [nzSupport] using hjv
      have hz : liftCof B ρ σ j = 0 := by
        unfold liftCof
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro t _
        have hne : j ≠ σ t := fun h => hj ⟨t, h.symm⟩
        simp [Pi.single_apply, hne, Ne.symm hne]
      change v j = a * (ε * liftCof B ρ σ j)
      rw [hvj, hz, mul_zero, mul_zero]
  have hwK : InKernel B (ε • liftCof B ρ σ) := by
    constructor
    · intro j
      have hn := hv.1.1 j
      rw [heq] at hn
      change 0 ≤ a * (ε • liftCof B ρ σ) j at hn
      exact nonneg_of_mul_nonneg_right hn ha
    · intro r
      have he := hv.1.2 r
      rw [heq] at he
      change (∑ j, B r j * (a * (ε • liftCof B ρ σ) j)) = 0 at he
      have hf : (∑ j, B r j * (a * (ε • liftCof B ρ σ) j)) =
          a * ∑ j, B r j * (ε • liftCof B ρ σ) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hf] at he
      exact (mul_eq_zero.mp he).resolve_left ha.ne'
  have hwn : ε • liftCof B ρ σ ≠ 0 := by
    intro hz
    apply hv.2.1
    rw [heq, hz, smul_zero]
  exact ⟨k, hk, ρ, σ, ε, a, hε, ha, hsupport, hc0, hwK, hwn, heq⟩

/-- The full nonnegative kernel is exactly the cone generated by qualifying cofactor rays. -/
theorem nonnegKernel_iff_mem_hull_cofactorCandidates (B : Matrix (Fin m) J ℝ)
    (x : J → ℝ) : InKernel B x ↔ x ∈ PointedCone.hull ℝ (cofactorCandidates B) := by
  classical
  constructor
  · intro hx
    have hle : PointedCone.hull ℝ {v | Circuit B v} ≤
        PointedCone.hull ℝ (cofactorCandidates B) := by
      apply Submodule.span_le.mpr
      intro v hv
      obtain ⟨k, hk, ρ, σ, ε, a, hε, ha, _hsupport, _hc0, hwK, hwn, heq⟩ :=
        circuit_cofactor_complete hv
      have hw : ε • liftCof B ρ σ ∈ cofactorCandidates B :=
        ⟨k, hk, ρ, σ, ε, hε, rfl, hwK, hwn⟩
      rw [heq]
      exact PointedCone.smul_mem _ ha.le (PointedCone.subset_hull hw)
    exact hle (nonnegKernel_mem_hull_circuit B x hx)
  · intro hx
    let K : PointedCone ℝ (J → ℝ) := {
      carrier := {v | InKernel B v}
      zero_mem' := ⟨fun _ => le_rfl, fun r => by simp⟩
      add_mem' := by
        intro v w hv hw
        refine ⟨fun j => add_nonneg (hv.1 j) (hw.1 j), fun r => ?_⟩
        change (∑ j, B r j * (v j + w j)) = 0
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, hv.2 r, hw.2 r, add_zero]
      smul_mem' := by
        intro a v hv
        refine ⟨?_, fun r => ?_⟩
        · intro j
          change 0 ≤ (a : ℝ) * v j
          exact mul_nonneg a.property (hv.1 j)
        · change (∑ j, B r j * ((a : ℝ) * v j)) = 0
          calc
            (∑ j, B r j * ((a : ℝ) * v j)) = (a : ℝ) * ∑ j, B r j * v j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = 0 := by rw [hv.2 r, mul_zero] }
    have hle : PointedCone.hull ℝ (cofactorCandidates B) ≤ K := by
      apply Submodule.span_le.mpr
      intro w hw
      obtain ⟨_k, _hk, _ρ, _σ, _ε, _hε, _heq, hwK, _hwn⟩ := hw
      exact hwK
    exact hle hx

#print axioms circuit_cofactor_complete
#print axioms nonnegKernel_iff_mem_hull_cofactorCandidates

end D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor
