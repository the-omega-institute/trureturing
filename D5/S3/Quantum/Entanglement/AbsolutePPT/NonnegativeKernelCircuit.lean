/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Nonnegative kernels decompose into circuits with independent deleted-support columns. -/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-
The classical elementary-vector argument uses a signed kernel direction and
minimum-ratio subtraction to contradict support minimality. It gives independence
after deleting any supported column, hence the support bound by dimension.

admission_basis: escape-witness
circuit_deleted_cols_linearIndependent: proof_shape: content;
  escape_witness: dependence-to-boundary contradiction;
  consumers: circuit_support_card_le, NonnegativeKernelCofactor.circuit_cofactor_complete;
  admission_basis: escape-witness.
circuit_support_card_le: proof_shape: bind-only; escape_witness: none;
  consumers: Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Support.family.
Escape audit unfinished for circuit_deleted_cols_linearIndependent:
https://github.com/the-omega-institute/trureturing/issues/17856.
The complete deleted-support observation and source binding remain missing.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
open Finset

variable {J : Type*} [Fintype J] {m : ℕ}

/-- The nonzero coordinates, without a positivity assumption. -/
noncomputable def nzSupport (v : J → ℝ) : Finset J := by
  classical
  exact univ.filter (fun j => v j ≠ 0)

/-- Coordinatewise nonnegativity and the homogeneous row equations. -/
def InKernel (B : Fin m → J → ℝ) (v : J → ℝ) : Prop :=
  (∀ j, 0 ≤ v j) ∧ (∀ r, ∑ j, B r j * v j = 0)

/-- A nonzero nonnegative kernel vector with minimal support in its support face. -/
def Circuit (B : Fin m → J → ℝ) (v : J → ℝ) : Prop :=
  InKernel B v ∧ v ≠ 0 ∧
    ∀ w, InKernel B w → w ≠ 0 → nzSupport w ⊆ nzSupport v →
      (nzSupport v).card ≤ (nzSupport w).card

private theorem mem_support {v : J → ℝ} {j : J} : j ∈ nzSupport v ↔ v j ≠ 0 := by
  classical
  simp [nzSupport]

omit [Fintype J] in
/-- Move in a direction until the first positive-direction coordinate reaches zero. -/
private theorem subtract_to_boundary [Finite J] (v d : J → ℝ)
    (hv : ∀ j, 0 ≤ v j) (hdv : ∀ j, d j ≠ 0 → 0 < v j)
    (hd : ∃ j, 0 < d j) :
    ∃ a : ℝ, 0 < a ∧ (∀ j, 0 ≤ v j - a * d j) ∧
      ∃ k, 0 < d k ∧ v k - a * d k = 0 := by
  classical
  let := Fintype.ofFinite J
  let s := univ.filter (fun j => 0 < d j)
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := hd
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
  obtain ⟨k, hk, hmin⟩ := s.exists_min_image (fun j => v j / d j) hs
  have hdk : 0 < d k := (mem_filter.mp hk).2
  refine ⟨v k / d k, div_pos (hdv k hdk.ne') hdk, ?_, k, hdk, ?_⟩
  · intro j
    by_cases hj : 0 < d j
    · have hle := hmin j (mem_filter.mpr ⟨mem_univ _, hj⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ hj).mp hle)
    · have hmul : v k / d k * d j ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt (div_pos (hdv k hdk.ne') hdk))
          (le_of_not_gt hj)
      linarith [hv j]
  · rw [div_mul_cancel₀ _ hdk.ne', sub_self]

private theorem kernel_sub {B : Fin m → J → ℝ} {v d : J → ℝ} (hv : InKernel B v)
    (hd : ∀ r, ∑ j, B r j * d j = 0) (a : ℝ)
    (hn : ∀ j, 0 ≤ v j - a * d j) : InKernel B (fun j => v j - a * d j) := by
  refine ⟨hn, fun r => ?_⟩
  calc
    ∑ j, B r j * (v j - a * d j) =
        (∑ j, B r j * v j) - a * ∑ j, B r j * d j := by
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hv.2 r, hd r]; ring

private theorem exists_circuit {B : Fin m → J → ℝ} {x : J → ℝ}
    (hx : InKernel B x) (hne : x ≠ 0) :
    ∃ z, Circuit B z ∧ nzSupport z ⊆ nzSupport x := by
  classical
  let P : ℕ → Prop := fun n => ∃ z, InKernel B z ∧ z ≠ 0 ∧
    nzSupport z ⊆ nzSupport x ∧ (nzSupport z).card = n
  have hp : ∃ n, P n := ⟨(nzSupport x).card, x, hx, hne, subset_rfl, rfl⟩
  obtain ⟨z, hz, hzn, hzx, hcard⟩ := Nat.find_spec hp
  refine ⟨z, ⟨hz, hzn, ?_⟩, hzx⟩
  intro w hw hwn hwz
  rw [hcard]
  exact Nat.find_min' hp ⟨w, hw, hwn, hwz.trans hzx, rfl⟩

/-- Every finite nonnegative homogeneous solution is a finite conic combination of circuits. -/
theorem nonnegKernel_mem_hull_circuit (B : Fin m → J → ℝ) (x : J → ℝ)
    (hx : InKernel B x) : x ∈ PointedCone.hull ℝ {v | Circuit B v} := by
  classical
  suffices ∀ n, ∀ x : J → ℝ, (nzSupport x).card = n → InKernel B x →
      x ∈ PointedCone.hull ℝ {v | Circuit B v} from this _ x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hn hx
    by_cases hx0 : x = 0
    · subst x
      exact (PointedCone.hull ℝ {v | Circuit B v}).zero_mem
    obtain ⟨z, hz, hzx⟩ := exists_circuit hx hx0
    have hzpos : ∃ j, 0 < z j := by
      have : ∃ j, z j ≠ 0 := Function.ne_iff.mp hz.2.1
      obtain ⟨j, hj⟩ := this
      exact ⟨j, lt_of_le_of_ne (hz.1.1 j) hj.symm⟩
    have hxz : ∀ j, z j ≠ 0 → 0 < x j := by
      intro j hj
      exact lt_of_le_of_ne (hx.1 j) (mem_support.mp (hzx (mem_support.mpr hj))).symm
    obtain ⟨a, ha, hy, k, hzk, hyk⟩ := subtract_to_boundary x z hx.1 hxz hzpos
    let y : J → ℝ := fun j => x j - a * z j
    have hyK : InKernel B y := kernel_sub hx hz.1.2 a hy
    have hys : nzSupport y ⊆ (nzSupport x).erase k := by
      intro j hj
      have hjy := mem_support.mp hj
      apply mem_erase.mpr
      constructor
      · intro hjk
        subst j
        exact hjy hyk
      · apply mem_support.mpr
        intro hjx
        have hjz : z j = 0 := by
          by_contra h
          exact mem_support.mp (hzx (mem_support.mpr h)) hjx
        exact hjy (by simp [y, hjx, hjz])
    have hkx : k ∈ nzSupport x := hzx (mem_support.mpr hzk.ne')
    have hlt : (nzSupport y).card < n := by
      have := card_le_card hys
      rw [card_erase_of_mem hkx] at this
      have : 0 < (nzSupport x).card := card_pos.mpr ⟨k, hkx⟩
      omega
    have hyH := ih _ hlt y rfl hyK
    have hzH : z ∈ PointedCone.hull ℝ {v | Circuit B v} := PointedCone.subset_hull hz
    have hsum := (PointedCone.hull ℝ {v | Circuit B v}).add_mem
      (PointedCone.smul_mem _ ha.le hzH) hyH
    have he : a • z + y = x := by
      ext j
      change a * z j + (x j - a * z j) = x j
      ring
    rwa [he] at hsum

/-- Deleting any supported column of a circuit leaves linearly independent columns. -/
theorem circuit_deleted_cols_linearIndependent [DecidableEq J]
    {B : Fin m → J → ℝ} {v : J → ℝ} (hv : Circuit B v)
    {i : J} (hi : i ∈ nzSupport v) :
    LinearIndependent ℝ
      (fun j : ↥((nzSupport v).erase i) => fun r : Fin m => B r (j : J)) := by
  classical
  let s := (nzSupport v).erase i
  change LinearIndependent ℝ (fun j : s => fun r : Fin m => B r j)
  by_contra hdep
  obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let d : J → ℝ := fun k => if hk : k ∈ s then c ⟨k, hk⟩ else 0
  have hd0 : ∀ r, ∑ k, B r k * d k = 0 := by
    intro r
    have he := congrFun hc r
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
    calc
      ∑ k, B r k * d k = ∑ k ∈ s, B r k * d k := by
        apply (sum_subset (subset_univ s) ?_).symm
        intro k _ hk
        simp [d, hk]
      _ = ∑ k : s, c k * B r k := by
        rw [← sum_attach]
        simp [d, mul_comm]
      _ = 0 := he
  have hdv : ∀ k, d k ≠ 0 → 0 < v k := by
    intro k hk
    have hks : k ∈ s := by
      by_contra h
      exact hk (by simp [d, h])
    exact lt_of_le_of_ne (hv.1.1 k)
      (mem_support.mp (mem_of_mem_erase hks)).symm
  have hdi : d i = 0 := by simp [d, s]
  have hdj : d j = c j := by simp [d, j.property]
  have direction : ∃ e : J → ℝ,
      (∀ r, ∑ k, B r k * e k = 0) ∧ e i = 0 ∧
      (∀ k, e k ≠ 0 → 0 < v k) ∧ ∃ k, 0 < e k := by
    rcases lt_or_gt_of_ne hj with hjn | hjp
    · refine ⟨fun k => -d k, ?_, by simp [hdi], ?_, j, ?_⟩
      · intro r
        simp only [mul_neg, sum_neg_distrib, hd0, neg_zero]
      · intro k hk
        exact hdv k (neg_ne_zero.mp hk)
      · simpa [hdj] using neg_pos.mpr hjn
    · exact ⟨d, hd0, hdi, hdv, j, by rwa [hdj]⟩
  obtain ⟨e, he, hei, hev, hep⟩ := direction
  obtain ⟨a, _ha, hw, k, hek, hwk⟩ := subtract_to_boundary v e hv.1.1 hev hep
  let w : J → ℝ := fun j => v j - a * e j
  have hwK : InKernel B w := kernel_sub hv.1 he a hw
  have hwi : w i = v i := by simp [w, hei]
  have hwn : w ≠ 0 := by
    intro h
    have : w i = 0 := congrFun h i
    exact mem_support.mp hi (hwi.symm.trans this)
  have hws : nzSupport w ⊆ (nzSupport v).erase k := by
    intro j hjw
    have hjn := mem_support.mp hjw
    refine mem_erase.mpr ⟨?_, ?_⟩
    · intro hjk
      subst j
      exact hjn hwk
    · apply mem_support.mpr
      intro hjv
      have hje : e j = 0 := by
        by_contra h
        exact (ne_of_gt (hev j h)) hjv
      exact hjn (by simp [w, hjv, hje])
  have hkv : k ∈ nzSupport v := mem_support.mpr (hev k hek.ne').ne'
  have hmin := hv.2.2 w hwK hwn (hws.trans (erase_subset _ _))
  have hle := card_le_card hws
  rw [card_erase_of_mem hkv] at hle
  have : 0 < (nzSupport v).card := card_pos.mpr ⟨i, hi⟩
  omega

/-- A support-minimal nonzero nonnegative kernel vector uses at most one more column than rows. -/
theorem circuit_support_card_le {B : Fin m → J → ℝ} {v : J → ℝ}
    (hv : Circuit B v) : (nzSupport v).card ≤ m + 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv.2.1
  have his : i ∈ nzSupport v := mem_support.mpr hi
  have hle := (circuit_deleted_cols_linearIndependent hv his).fintype_card_le_finrank
  simp only [Fintype.card_coe, card_erase_of_mem his,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
  have hpos : 0 < (nzSupport v).card := card_pos.mpr ⟨i, his⟩
  omega

#print axioms nonnegKernel_mem_hull_circuit
#print axioms circuit_deleted_cols_linearIndependent
#print axioms circuit_support_card_le
end D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
