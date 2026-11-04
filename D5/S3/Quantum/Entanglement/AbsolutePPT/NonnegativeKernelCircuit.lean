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
import Mathlib.Basic.Sign.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

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

OrderedField.signConformalGlobalKernelCircuit: proof_shape: content;
  escape_witness: same-p nonnegative feasible strict-support erasure in compress_conic;
  live path: erasure contradiction -> independent active columns -> signed residual
    d - d e * z vanishes -> every nonzero supported kernel has equal support;
  admission_basis: escape-witness.
OrderedField.compress_conic: proof_shape: content;
  escape_witness: same-p feasible strict-support erasure;
  consumer: OrderedField.signConformalGlobalKernelCircuit.
OrderedField.subtract_to_boundary and OrderedField.mem_support: proof_shape: bind-only;
  their consumers are OrderedField.compress_conic and the global circuit proof.
The Real subtract_to_boundary retains its Finite-only telescope and delegates to
  the single ordered-field minimum-ratio proof.
OrderedField.signConformalGlobalKernelCircuitDecomposition: proof_shape: content;
  escape_witness: terminating residual-support construction with a one-sided
    nonzero pivot outside the span of the later conformal summands;
  live path: boundary erasure -> smaller-support induction -> Fin.cons independence
    -> independent family in the kernel -> nullity bound;
  admission_basis: escape-witness.
utility: not-applicable(kind=none): these are general existence and linear-algebra
  theorems, not bounded enumeration, certified instances or numerical reductions.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
open Finset
open scoped BigOperators

namespace OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {E : Type*} [Fintype E]

/-- The finite minimum-ratio boundary step over an arbitrary ordered field. -/
private theorem subtract_to_boundary (v d : E → F)
    (hv : ∀ i, 0 ≤ v i) (hdv : ∀ i, d i ≠ 0 → 0 < v i)
    (hd : ∃ i, 0 < d i) :
    ∃ a : F, 0 < a ∧ (∀ i, 0 ≤ v i - a * d i) ∧
      ∃ k, 0 < d k ∧ v k - a * d k = 0 := by
  classical
  let s := univ.filter (fun i => 0 < d i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hd
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  obtain ⟨k, hk, hmin⟩ := s.exists_min_image (fun i => v i / d i) hs
  have hdk : 0 < d k := (mem_filter.mp hk).2
  refine ⟨v k / d k, div_pos (hdv k hdk.ne') hdk, ?_, k, hdk, ?_⟩
  · intro i
    by_cases hi : 0 < d i
    · have hle := hmin i (mem_filter.mpr ⟨mem_univ _, hi⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ hi).mp hle)
    · have hmul : v k / d k * d i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (le_of_lt (div_pos (hdv k hdk.ne') hdk)) (le_of_not_gt hi)
      linarith [hv i]
  · rw [div_mul_cancel₀ _ hdk.ne', sub_self]

end OrderedField

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
  exact OrderedField.subtract_to_boundary v d hv hdv hd

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

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit

/-! The ordered-field endpoint uses the same minimum-ratio boundary step as the
Real circuit API. No Archimedean, rank or nonzero-column assumption is used. -/

namespace OrderedField

open Finset
open scoped BigOperators

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {E : Type*} [Fintype E] {m : ℕ}

noncomputable def support (v : E → F) : Finset E :=
  Finset.univ.filter (fun i => v i ≠ 0)

omit [IsStrictOrderedRing F] in
private theorem mem_support {v : E → F} {i : E} : i ∈ support v ↔ v i ≠ 0 := by
  classical
  simp [support]

-- Dependence permits strict support erasure while preserving the same p.
private theorem compress_conic
    {I : Type*} [Fintype I] (b : I → (Fin m → F)) (a : I → F) (p : Fin m → F)
    (ha : ∀ i, 0 ≤ a i) (hp : ∑ i, a i • b i = p) :
    ∃ t : I → F, (∀ i, 0 ≤ t i) ∧ (∀ i, a i = 0 → t i = 0) ∧
      (∑ i, t i • b i = p) ∧
      LinearIndependent F (fun i : ↥(support t) => b i.1) := by
  classical
  let P : ℕ → Prop := fun n => ∃ t : I → F,
    (∀ i, 0 ≤ t i) ∧ (∀ i, a i = 0 → t i = 0) ∧
      (∑ i, t i • b i = p) ∧ (support t).card = n
  have hpP : ∃ n, P n := ⟨(support a).card, a, ha,
    (fun i hi => hi), hp, rfl⟩
  obtain ⟨t, ht, hta, htp, hcard⟩ := Nat.find_spec hpP
  have hli : LinearIndependent F (fun i : ↥(support t) => b i.1) := by
    by_contra hdep
    obtain ⟨c, hc, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
    let d : I → F := fun i => if hi : i ∈ support t then c ⟨i, hi⟩ else 0
    have hd0 : ∀ r, ∑ i, b i r * d i = 0 := by
      intro r
      have he := congrFun hc r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
      calc
        ∑ i, b i r * d i = ∑ i ∈ support t, b i r * d i := by
          apply (sum_subset (subset_univ (support t)) ?_).symm
          intro i _ hi
          simp [d, hi]
        _ = ∑ i : ↥(support t), b i r * d i := by
          symm
          rw [← (support t).sum_attach]
          rfl
        _ = ∑ i : ↥(support t), c i * b i r := by
          apply sum_congr rfl
          intro i hi
          simp [d, mul_comm]
        _ = 0 := he
    have hdv : ∀ i, d i ≠ 0 → 0 < t i := by
      intro i hi
      have his : i ∈ support t := by
        by_contra hn
        exact hi (by simp [d, hn])
      exact lt_of_le_of_ne (ht i) (mem_support.mp his).symm
    have hdj : d j = c j := by
      have hjs : (j : I) ∈ support t := j.property
      simp [d, hjs]
    have direction : ∃ e : I → F,
        (∀ r, ∑ i, b i r * e i = 0) ∧
        (∀ i, e i ≠ 0 → 0 < t i) ∧ ∃ i, 0 < e i := by
      rcases lt_or_gt_of_ne hj with hjn | hjp
      · refine ⟨fun i => -d i, ?_, ?_, j, ?_⟩
        · intro r
          simp only [mul_neg, sum_neg_distrib, hd0, neg_zero]
        · intro i hi
          exact hdv i (neg_ne_zero.mp hi)
        · simpa [hdj] using neg_pos.mpr hjn
      · exact ⟨d, hd0, hdv, j, by rwa [hdj]⟩
    obtain ⟨e, he, hev, hep⟩ := direction
    obtain ⟨α, _hα, hu, k, hek, huk⟩ := subtract_to_boundary t e ht hev hep
    let u : I → F := fun i => t i - α * e i
    have husum : ∑ i, u i • b i = p := by
      calc
        ∑ i, u i • b i = (∑ i, t i • b i) - α • (∑ i, e i • b i) := by
          funext r
          simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          change (∑ i, u i * b i r) =
            (∑ i, t i * b i r) - α * ∑ i, e i * b i r
          calc
            ∑ i, u i * b i r =
                ∑ i, (t i * b i r - α * (e i * b i r)) := by
              apply sum_congr rfl
              intro i _
              simp only [u]
              ring
            _ = (∑ i, t i * b i r) - ∑ i, α * (e i * b i r) :=
              by rw [sum_sub_distrib]
            _ = (∑ i, t i * b i r) - α * ∑ i, e i * b i r := by
              rw [Finset.mul_sum]
        _ = p := by
          rw [htp]
          have he' : ∑ i, e i • b i = 0 := by
            funext r
            simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
              mul_comm] using he r
          rw [he', smul_zero, sub_zero]
    have hua : ∀ i, a i = 0 → u i = 0 := by
      intro i hai
      have hti : t i = 0 := hta i hai
      have hei : e i = 0 := by
        by_contra h
        exact (ne_of_gt (hev i h)) (hti)
      simp [u, hti, hei]
    have hus : support u ⊆ (support t).erase k := by
      intro i hi
      have hiu := mem_support.mp hi
      refine mem_erase.mpr ⟨?_, ?_⟩
      · intro hik
        subst i
        exact hiu huk
      · apply mem_support.mpr
        intro hit
        have hei : e i = 0 := by
          by_contra h
          exact (ne_of_gt (hev i h)) hit
        exact hiu (by simp [u, hit, hei])
    have htk : k ∈ support t := mem_support.mpr (hev k hek.ne').ne'
    have hlt : (support u).card < (support t).card := by
      have hle := card_le_card hus
      rw [card_erase_of_mem htk] at hle
      have hpos : 0 < (support t).card := card_pos.mpr ⟨k, htk⟩
      omega
    have hmin := Nat.find_min' hpP ⟨u, hu, hua, husum, rfl⟩
    rw [← hcard] at hmin
    exact (Nat.not_lt_of_ge hmin) hlt
  exact ⟨t, ht, hta, htp, hli⟩

end OrderedField
end D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.OrderedField

open Finset
open scoped BigOperators Matrix

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {E : Type*} [Fintype E] {m : ℕ}

set_option maxHeartbeats 1000000 in
/-- A prescribed nonzero coordinate belongs to a sign-conformal global kernel circuit.
Competitors may have arbitrary signs and need not participate at the prescribed coordinate. -/
theorem signConformalGlobalKernelCircuit
    (A : Matrix (Fin m) E F) (x : E → F) (e : E)
    (hx : A *ᵥ x = 0) (hxe : x e ≠ 0) :
    ∃ c : E → F, A *ᵥ c = 0 ∧ c e ≠ 0 ∧
      (∀ i, c i = 0 ∨ SignType.sign (c i) = SignType.sign (x i)) ∧
      (∀ w : E → F, A *ᵥ w = 0 → w ≠ 0 →
        Function.support w ⊆ Function.support c →
        Function.support w = Function.support c) := by
  classical
  let eps : E → F := fun i => if 0 ≤ x i then 1 else -1
  let y : E → F := fun i => eps i * x i
  let b : E → (Fin m → F) := fun i r => eps i * A r i
  have heps_ne (i : E) : eps i ≠ 0 := by
    by_cases hi : 0 ≤ x i <;> simp [eps, hi]
  have heps_sq (i : E) : eps i * eps i = 1 := by
    by_cases hi : 0 ≤ x i <;> simp [eps, hi]
  have hy_nonneg (i : E) : 0 ≤ y i := by
    by_cases hi : 0 ≤ x i
    · simpa [y, eps, hi] using hi
    · have hi' : x i < 0 := lt_of_not_ge hi
      simp [y, eps, hi, hi'.le]
  have hye : 0 < y e := by
    by_cases he' : 0 ≤ x e
    · simpa [y, eps, he'] using (lt_of_le_of_ne he' hxe.symm)
    · have he'' : x e < 0 := lt_of_not_ge he'
      simpa [y, eps, he'] using (neg_pos.mpr he'')
  have hsumx : ∀ r, ∑ i, A r i * x i = 0 := by
    intro r
    have hr := congrFun hx r
    simpa [Matrix.mulVec, dotProduct] using hr
  have hsumy : ∑ i, y i • b i = 0 := by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, y i * b i r) = ∑ i, (eps i * eps i) * (A r i * x i) := by
        apply sum_congr rfl
        intro i _
        simp [y, b, mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ i, A r i * x i := by simp [heps_sq]
      _ = 0 := hsumx r
  let a : E → F := fun i => if i = e then 0 else y i / y e
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    by_cases hi : i = e
    · simp [a, hi]
    · simpa [a, hi] using (div_nonneg (hy_nonneg i) hye.le)
  have hrep : ∑ i, a i • b i = - b e := by
    funext r
    simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hnorm : ∀ i, i ≠ e → a i * b i r = (y i / y e) * b i r := by
      intro i hi
      simp [a, hi]
    have hsum_erase :
        (∑ i ∈ ((univ : Finset E).erase e), y i * b i r) + y e * b e r = 0 := by
      have htot : (∑ i, y i * b i r) = 0 := by
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
          congrArg (fun z : Fin m → F => z r) hsumy
      rw [← (univ : Finset E).sum_erase_add
        (fun i => y i * b i r) (mem_univ e)] at htot
      exact htot
    have hcalc :
        (∑ i ∈ ((univ : Finset E).erase e), (y i / y e) * b i r) = -b e r := by
      have hdiv : ∀ i, i ≠ e → (y i / y e) * b i r =
          (y e)⁻¹ * (y i * b i r) := by
        intro i hi
        field_simp
      rw [show (∑ i ∈ ((univ : Finset E).erase e), (y i / y e) * b i r) =
          (y e)⁻¹ * ∑ i ∈ ((univ : Finset E).erase e), y i * b i r by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro i hi
            rw [hdiv i (by simpa using (mem_erase.mp hi).1)]
            ]
      have hye0 : y e ≠ 0 := hye.ne'
      have hS : (∑ i ∈ ((univ : Finset E).erase e), y i * b i r) =
          -(y e * b e r) := by
        linarith [hsum_erase]
      rw [hS]
      field_simp [hye0]
    calc
      ∑ i, a i * b i r = ∑ i ∈ ((univ : Finset E).erase e), (y i / y e) * b i r := by
        calc
          ∑ i, a i * b i r =
              (∑ i ∈ ((univ : Finset E).erase e), a i * b i r) + a e * b e r :=
            ((univ : Finset E).sum_erase_add (fun i => a i * b i r)
              (mem_univ e)).symm
          _ = ∑ i ∈ ((univ : Finset E).erase e), (y i / y e) * b i r := by
            rw [show a e = 0 by simp [a], zero_mul, add_zero]
            apply sum_congr rfl
            intro i hi
            exact hnorm i (by simpa using (mem_erase.mp hi).1)
      _ = -b e r := hcalc
  obtain ⟨t, ht, hta, htp, hliT⟩ :=
    compress_conic (m := m) b a (-b e) ha hrep
  have hte : t e = 0 := hta e (by simp [a])
  let z : E → F := fun i => if i = e then 1 else t i
  have hz_nonneg : ∀ i, 0 ≤ z i := by
    intro i
    by_cases hi : i = e
    · simp [z, hi]
    · simpa [z, hi] using ht i
  have hz_e : z e = 1 := by simp [z]
  have hzsum : ∑ i, z i • b i = 0 := by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have htpr := congrArg (fun q : Fin m → F => q r) htp
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at htpr
    have hzpr : ∑ i, z i * b i r = b e r + ∑ i, t i * b i r := by
      rw [show (∑ i, z i * b i r) =
          (∑ i ∈ ((univ : Finset E).erase e), t i * b i r) + b e r by
            calc
              ∑ i, z i * b i r =
                  (∑ i ∈ ((univ : Finset E).erase e), z i * b i r) + z e * b e r :=
                ((univ : Finset E).sum_erase_add (fun i => z i * b i r)
                  (mem_univ e)).symm
              _ = (∑ i ∈ ((univ : Finset E).erase e), t i * b i r) + b e r := by
                rw [hz_e, one_mul]
                congr 1
                apply sum_congr rfl
                intro i hi
                simp [z, (mem_erase.mp hi).1]]
      rw [show (∑ i ∈ ((univ : Finset E).erase e), t i * b i r) =
          ∑ i, t i * b i r by
            apply sum_subset (subset_univ _)
            intro i _ hi
            have : i = e := by simpa using hi
            subst i
            simp [hte]]
      ring
    rw [hzpr, htpr]
    simp
  have hz_support : ∀ i, z i ≠ 0 → x i ≠ 0 := by
    intro i hi
    by_cases hie : i = e
    · simpa [hie] using hxe
    · have hti : t i ≠ 0 := by simpa [z, hie] using hi
      intro hxi
      have hyi : y i = 0 := by simp [y, hxi]
      have hai : a i = 0 := by simp [a, hie, hyi]
      exact hti (hta i hai)
  have hLIz : LinearIndependent F
      (fun j : ↥((support z).erase e) => fun r => b j r) := by
    have hset : (support z).erase e = support t := by
      ext i
      constructor
      · intro hi
        have hz : z i ≠ 0 := mem_support.mp (mem_erase.mp hi).2
        have hne : i ≠ e := (mem_erase.mp hi).1
        apply mem_support.mpr
        simpa [z, hne] using hz
      · intro hi
        have ht' : t i ≠ 0 := mem_support.mp hi
        have hne : i ≠ e := by
          intro hie
          subst i
          exact (mem_support.mp hi) hte
        apply mem_erase.mpr
        refine ⟨hne, ?_⟩
        apply mem_support.mpr
        simpa [z, hne] using ht'
    rw [hset]
    exact hliT
  have hz_eq_of_kernel (d : E → F) (hd : ∑ i, d i • b i = 0)
      (hds : Function.support d ⊆ (support z : Set E)) :
      ∀ i, d i = d e * z i := by
    let r : E → F := fun i => d i - d e * z i
    have hre : r e = 0 := by simp [r, hz_e]
    have hrsum : ∑ i, r i • b i = 0 := by
      funext q
      have hdq := congrArg (fun v : Fin m → F => v q) hd
      have hzq := congrArg (fun v : Fin m → F => v q) hzsum
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hdq hzq ⊢
      calc
        ∑ i, r i * b i q =
            ∑ i, (d i * b i q - d e * (z i * b i q)) := by
          apply sum_congr rfl
          intro i _
          simp [r]
          ring
        _ = (∑ i, d i * b i q) - ∑ i, d e * (z i * b i q) := by
          rw [sum_sub_distrib]
        _ = (∑ i, d i * b i q) - d e * ∑ i, z i * b i q := by
          rw [Finset.mul_sum]
        _ = 0 := by simp [hdq, hzq]
    have hrr : ∀ j : ↥((support z).erase e), r j = 0 := by
      apply (Fintype.linearIndependent_iff.mp hLIz) (fun j => r j)
      funext q
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hsumr := congrArg (fun v : Fin m → F => v q) hrsum
      have hsumr' : (∑ i : E, r i * b i q) = 0 := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hsumr
      have hzero : ∀ i : E, i ∈ (univ : Finset E) →
          i ∉ (support z).erase e → r i * b i q = 0 := by
        intro i _ hi
        by_cases hzi : i ∈ support z
        · have hie : i = e := by
            by_contra hn
            exact hi (mem_erase.mpr ⟨hn, hzi⟩)
          subst i
          simp [hre]
        · have hdi : d i = 0 := by
            apply not_ne_iff.mp
            intro hne
            exact hzi (hds hne)
          have hzi0 : z i = 0 := by
            apply not_ne_iff.mp
            intro hne
            exact hzi (mem_support.mpr hne)
          have hri : r i = 0 := by simp [r, hdi, hzi0]
          simp [hri]
      rw [← sum_subset (subset_univ ((support z).erase e)) hzero] at hsumr'
      calc
        (∑ j : ↥((support z).erase e), r j * b j q) =
            ((support z).erase e).sum (fun i => r i * b i q) := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach ((support z).erase e)
            (fun i => r i * b i q)
        _ = 0 := by simpa [r] using hsumr'
    intro i
    by_cases hi : i = e
    · simp [hi, hz_e]
    · by_cases hzi : i ∈ support z
      · have hri := hrr (⟨i, mem_erase.mpr ⟨hi, hzi⟩⟩ : ↥((support z).erase e))
        change r i = 0 at hri
        have hri' : d i - d e * z i = 0 := by simpa [r] using hri
        exact sub_eq_zero.mp hri'
      · have hdi : d i = 0 := by
          apply not_ne_iff.mp
          intro hne
          exact hzi (hds hne)
        have hzi0 : z i = 0 := by
          apply not_ne_iff.mp
          intro hne
          exact hzi (mem_support.mpr hne)
        simp [r, hdi, hzi0]
  let c : E → F := fun i => eps i * z i
  have hc_kernel : A *ᵥ c = 0 := by
    funext r
    have hz := congrArg (fun q : Fin m → F => q r) hzsum
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hz
    change ∑ i, A r i * c i = 0
    simpa [c, b, mul_assoc, mul_left_comm, mul_comm, heps_sq] using hz
  have hc_e : c e ≠ 0 := by simp [c, hz_e, heps_ne]
  have hc_sign : ∀ i, c i = 0 ∨ SignType.sign (c i) = SignType.sign (x i) := by
    intro i
    by_cases hzi : z i = 0
    · exact Or.inl (by simp [c, hzi])
    · right
      by_cases hxi : 0 ≤ x i
      · have hcp : 0 < c i := by
          have hzpos : 0 < z i := lt_of_le_of_ne (hz_nonneg i) (Ne.symm hzi)
          simpa [c, eps, hxi] using hzpos
        have hxpos : 0 < x i := lt_of_le_of_ne hxi (by
          intro hzero
          exact hz_support i hzi hzero.symm)
        rw [sign_pos hcp, sign_pos hxpos]
      · have hxn : x i < 0 := lt_of_not_ge hxi
        have hcn : c i < 0 := by
          have hzpos : 0 < z i := lt_of_le_of_ne (hz_nonneg i) (Ne.symm hzi)
          simpa [c, eps, hxi] using (neg_lt_zero.mpr hzpos)
        rw [sign_neg hcn, sign_neg hxn]
  refine ⟨c, hc_kernel, hc_e, hc_sign, ?_⟩
  intro w hw hwn hws
  let d : E → F := fun i => eps i * w i
  have hd_kernel : ∑ i, d i • b i = 0 := by
    funext r
    have hwrow := congrFun hw r
    have hrow := congrArg (fun q : Fin m → F => q r) hw
    simp only [Matrix.mulVec, dotProduct] at hrow
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simpa [d, b, mul_assoc, mul_left_comm, mul_comm, heps_sq] using hrow
  have hd_support : Function.support d ⊆ (support z : Set E) := by
    intro i hi
    have hwi : w i ≠ 0 := by
      intro hzero
      exact hi (by simp [d, hzero])
    have hci : c i ≠ 0 := hws hwi
    have hzi : z i ≠ 0 := by
      intro hz0
      exact hci (by simp [c, hz0])
    exact mem_support.mpr hzi
  have hdz := hz_eq_of_kernel d hd_kernel hd_support
  have hde : d e ≠ 0 := by
    intro hzero
    apply hwn
    funext i
    have hi := hdz i
    have hdi : d i = 0 := by simpa [hzero] using hi
    exact (mul_eq_zero.mp (by simpa [d] using hdi)).resolve_left (heps_ne i)
  ext i
  change w i ≠ 0 ↔ c i ≠ 0
  constructor
  · intro hwi
    have hdi : d i ≠ 0 := mul_ne_zero (heps_ne i) hwi
    have hzi : z i ≠ 0 := by
      intro hz0
      apply hdi
      rw [hdz i, hz0, mul_zero]
    exact mul_ne_zero (heps_ne i) hzi
  · intro hci
    have hzi : z i ≠ 0 := by
      intro hz0
      apply hci
      simp [c, hz0]
    have hdi : d i ≠ 0 := by
      rw [hdz i]
      exact mul_ne_zero hde hzi
    intro hwi
    apply hdi
    simp [d, hwi]


-- The induction carries signed circuit minimality and the one-sided span invariant.
set_option maxHeartbeats 1000000 in
/-- Every finite signed kernel vector is an independent conformal sum of global circuits.
Positive coefficients are absorbed in the summands; the empty sum represents zero. -/
theorem signConformalGlobalKernelCircuitDecomposition
    (A : Matrix (Fin m) E F) (x : E → F) (hx : A *ᵥ x = 0) :
    ∃ (n : ℕ) (c : Fin n → (E → F)),
      (∑ j, c j) = x ∧ LinearIndependent F c ∧
      n ≤ (support x).card ∧
      n ≤ Module.finrank F (LinearMap.ker (Matrix.mulVecLin A)) ∧
      ∀ j, c j ≠ 0 ∧ A *ᵥ c j = 0 ∧
        (∀ i, c j i = 0 ∨ SignType.sign (c j i) = SignType.sign (x i)) ∧
        (∀ w : E → F, A *ᵥ w = 0 → w ≠ 0 →
          Function.support w ⊆ Function.support (c j) →
          Function.support w = Function.support (c j)) := by
  classical
  have zero_of_conformal {a b : F}
      (h : a = 0 ∨ SignType.sign a = SignType.sign b) (hb : b = 0) : a = 0 := by
    rcases h with h | h
    · exact h
    · exact sign_eq_zero_iff.mp (by simpa [hb] using h)
  have trans_conformal {a b d : F}
      (hab : a = 0 ∨ SignType.sign a = SignType.sign b)
      (hbd : b = 0 ∨ SignType.sign b = SignType.sign d) :
      a = 0 ∨ SignType.sign a = SignType.sign d := by
    rcases hab with ha | hab
    · exact Or.inl ha
    rcases hbd with hb | hbd
    · exact Or.inl (zero_of_conformal (Or.inr hab) hb)
    · exact Or.inr (hab.trans hbd)
  have main : ∀ N : ℕ, ∀ x : E → F, (support x).card = N → A *ᵥ x = 0 →
      ∃ (n : ℕ) (c : Fin n → (E → F)),
        (∑ j, c j) = x ∧ LinearIndependent F c ∧ n ≤ (support x).card ∧
        ∀ j, c j ≠ 0 ∧ A *ᵥ c j = 0 ∧
          (∀ i, c j i = 0 ∨ SignType.sign (c j i) = SignType.sign (x i)) ∧
          (∀ w : E → F, A *ᵥ w = 0 → w ≠ 0 →
            Function.support w ⊆ Function.support (c j) →
            Function.support w = Function.support (c j)) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro x hN hx
      by_cases hx0 : x = 0
      · subst x
        exact ⟨0, Fin.elim0, by simp, linearIndependent_empty_type, Nat.zero_le _, (fun j => Fin.elim0 j)⟩
      obtain ⟨e, he⟩ := Function.ne_iff.mp hx0
      obtain ⟨z, hzK, hze, hzsign, hzmin⟩ :=
        signConformalGlobalKernelCircuit A x e hx he
      have hzx (i : E) (hi : z i ≠ 0) : x i ≠ 0 := by
        intro hxi
        exact hi (zero_of_conformal (hzsign i) hxi)
      obtain ⟨a, ha, hbound, k, hzk, hboundary⟩ :=
        subtract_to_boundary (fun i => |x i|) (fun i => |z i|)
          (fun i => abs_nonneg _) (fun i hi => abs_pos.mpr (hzx i (by simpa using hi)))
          ⟨e, abs_pos.mpr hze⟩
      let b : E → F := a • z
      let y : E → F := x - b
      have hbK : A *ᵥ b = 0 := by simp [b, Matrix.mulVec_smul, hzK]
      have hyK : A *ᵥ y = 0 := by simp [y, Matrix.mulVec_sub, hx, hbK]
      have hb0 : b ≠ 0 := by
        intro h
        have := congrFun h e
        exact (mul_ne_zero ha.ne' hze) this
      have hb_support : Function.support b = Function.support z := by
        ext i
        simp [b, Function.mem_support, ha.ne']
      have hbsign (i : E) :
          b i = 0 ∨ SignType.sign (b i) = SignType.sign (x i) := by
        rcases hzsign i with hi | hi
        · exact Or.inl (by simp [b, hi])
        · exact Or.inr (by simpa [b, sign_mul, sign_pos ha] using hi)
      have hy_sign (i : E) :
          y i = 0 ∨ SignType.sign (y i) = SignType.sign (x i) := by
        by_cases hzi : z i = 0
        · right
          simp [y, b, hzi]
        have hxi := hzx i hzi
        have hsign : SignType.sign (z i) = SignType.sign (x i) :=
          (hzsign i).resolve_left hzi
        by_cases hxp : 0 < x i
        · have hzp : 0 < z i :=
            sign_eq_one_iff.mp (hsign.trans (sign_pos hxp))
          have hbi := hbound i
          rw [abs_of_pos hxp, abs_of_pos hzp] at hbi
          by_cases hyi : y i = 0
          · exact Or.inl hyi
          · right
            have hyp : 0 < y i := lt_of_le_of_ne hbi (Ne.symm hyi)
            rw [sign_pos hyp, sign_pos hxp]
        · have hxn : x i < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hxi
          have hzn : z i < 0 :=
            sign_eq_neg_one_iff.mp (hsign.trans (sign_neg hxn))
          have hbi := hbound i
          rw [abs_of_neg hxn, abs_of_neg hzn] at hbi
          by_cases hyi : y i = 0
          · exact Or.inl hyi
          · right
            have hyn : y i < 0 := by
              change x i - a * z i < 0
              have hyne : x i - a * z i ≠ 0 := hyi
              have hyle : x i - a * z i ≤ 0 := by linarith
              exact lt_of_le_of_ne hyle hyne
            rw [sign_neg hyn, sign_neg hxn]
      have hyk : y k = 0 := by
        have hzne : z k ≠ 0 := abs_pos.mp hzk
        have hxne := hzx k hzne
        have hs := (hzsign k).resolve_left hzne
        by_cases hxp : 0 < x k
        · have hzp := sign_eq_one_iff.mp (hs.trans (sign_pos hxp))
          rw [abs_of_pos hxp, abs_of_pos hzp] at hboundary
          exact hboundary
        · have hxn := lt_of_le_of_ne (le_of_not_gt hxp) hxne
          have hzn := sign_eq_neg_one_iff.mp (hs.trans (sign_neg hxn))
          rw [abs_of_neg hxn, abs_of_neg hzn] at hboundary
          change x k - a * z k = 0
          linarith
      have hys : support y ⊆ (support x).erase k := by
        intro i hi
        refine mem_erase.mpr ⟨?_, ?_⟩
        · intro hik
          subst i
          exact mem_support.mp hi hyk
        · apply mem_support.mpr
          intro hxi
          exact mem_support.mp hi (zero_of_conformal (hy_sign i) hxi)
      have hkx : k ∈ support x := mem_support.mpr (hzx k (abs_pos.mp hzk))
      have hlt : (support y).card < N := by
        have hle := card_le_card hys
        have hpos := card_pos.mpr ⟨k, hkx⟩
        rw [card_erase_of_mem hkx] at hle
        omega
      obtain ⟨n, c, hsum, hli, hn, hc⟩ := ih _ hlt y rfl hyK
      have hck (j : Fin n) : c j k = 0 :=
        zero_of_conformal ((hc j).2.2.1 k) hyk
      have hbspan : b ∉ Submodule.span F (Set.range c) := by
        intro hb
        have hzero : ∀ v ∈ Submodule.span F (Set.range c), v k = 0 := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem v hv =>
            obtain ⟨j, rfl⟩ := hv
            exact hck j
          | zero => rfl
          | add u v _ _ hu hv => simp [hu, hv]
          | smul a v _ hv => simp [hv]
        exact (mul_ne_zero ha.ne' (abs_pos.mp hzk)) (hzero b hb)
      refine ⟨n + 1, Fin.cons b c, ?_, hli.finCons hbspan, ?_, ?_⟩
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hsum]
        dsimp [y]
        abel
      · have hle := card_le_card hys
        have hpos := card_pos.mpr ⟨k, hkx⟩
        rw [card_erase_of_mem hkx] at hle
        omega
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · refine ⟨hb0, hbK, hbsign, ?_⟩
          intro w hw hwn hws
          change Function.support w ⊆ Function.support b at hws
          change Function.support w = Function.support b
          rw [hb_support] at hws ⊢
          exact hzmin w hw hwn hws
        · exact ⟨(hc j).1, (hc j).2.1,
            fun i => trans_conformal ((hc j).2.2.1 i) (hy_sign i), (hc j).2.2.2⟩
  obtain ⟨n, c, hsum, hli, hn, hc⟩ := main _ x rfl hx
  let d : Fin n → LinearMap.ker (Matrix.mulVecLin A) :=
    fun j => ⟨c j, (hc j).2.1⟩
  have hd : LinearIndependent F d :=
    LinearIndependent.of_comp (LinearMap.ker (Matrix.mulVecLin A)).subtype hli
  exact ⟨n, c, hsum, hli, hn, by simpa using hd.fintype_card_le_finrank, hc⟩

end D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.OrderedField
