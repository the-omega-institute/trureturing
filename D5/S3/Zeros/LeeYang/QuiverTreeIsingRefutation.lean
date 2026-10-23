/- GID: D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/QuiverTreeIsingRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.claim; result=D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result; claim=D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.claim
   digest: Positive joint split weights refute the tree Lee-Yang conjecture. -/
/- result
   proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#15357; Refuted)
   Direct frozen dependencies:
   D5/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport.NamedSpanningTree
     statement_id: sha256:87ce13fe28095abdbdb2e480e9e6fd6d59be3b97df0fc98de5951f50a90b4be1
   D5/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport.treeSupport
     statement_id: sha256:b21fe012d9dfc3dfbaaeae7127c25eaa22a1ecc997133b6ceb44c272808fae46
   D5/S3/Observer/AgencyHolonomy/NamedTreePhaseTransport.NamedSpanningTree.mk
     statement_id: sha256:3be4001790e62b90ec3cef59e7c38727aa6a56f59dd528eff5b19be9bc31f55d
   NamedSpanningTree src tgt Set.univ selects every edge. Its nonloop, distinct
   and isTree fields state exactly the finite-type tree convention: the all-edge
   subtype is in bijection with E, and its support equals the full edge-range graph.
   The public result is the designated refutation result (`basis=refutes`) and is exempt
   from four-slot escape registration (CLAUDE.md §3.9).
   The witness orientation is 0 -> 1 <- 2, with n = (4,4), tau = -1 and W31.
   The same polynomial arises from 0 -> 1 -> 2 with the second weight index reversed.
   The scope is arbitrary positive joint weights; the product-weight version remains open.
   The sign certificate is the negative cubic discriminant -16404.
   mass0: proof_shape: bind-only; escape_witness: none; consumers: term100, term101, term110,
     term111.
   mass1: proof_shape: bind-only; escape_witness: none; consumers: term010, term011, term110,
     term111.
   mass2: proof_shape: bind-only; escape_witness: none; consumers: term001, term011, term101,
     term111.
   term000: proof_shape: bind-only; escape_witness: none; consumers: direct.
   term001: proof_shape: bind-only; escape_witness: none; consumers: direct.
   term010: proof_shape: bind-only; escape_witness: none; consumers: direct.
   term011: proof_shape: bind-only; escape_witness: none; consumers: direct.
   term100: proof_shape: bind-only; escape_witness: none; consumers: direct.
   term101: proof_shape: bind-only; escape_witness: none; consumers: direct.
   term110: proof_shape: bind-only; escape_witness: none; consumers: direct.
   term111: proof_shape: bind-only; escape_witness: none; consumers: direct.
   direct: proof_shape: bind-only; escape_witness: none; consumers: path_poly.
   tree_ok: proof_shape: bind-only; escape_witness: none; consumers: result.
   path_poly: proof_shape: bind-only; escape_witness: none; consumers: result.
   q_discr: proof_shape: bind-only; escape_witness: none; consumers: q_not_splits.
   q_not_splits: proof_shape: bind-only; escape_witness: none; consumers: exists_nonreal_root.
   exists_nonreal_root: proof_shape: bind-only; escape_witness: none; consumers: result.
   sextic_factor: proof_shape: bind-only; escape_witness: none; consumers: lift_root.
   lift_root: proof_shape: bind-only; escape_witness: none; consumers: result.
-/

import D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.Star
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
open Finset Polynomial
namespace D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
def splits {E : Type} [Fintype E] [DecidableEq E] (n : E → ℕ) : Finset (E → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc 1 (n i - 1))
def mass {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (src tgt : E → V)
  (n : E → ℕ) (k : E → ℕ) (v : V) : ℕ := (∑ i ∈ Finset.univ.filter (fun i => src i = v), k i) +
  (∑ i ∈ Finset.univ.filter (fun i => tgt i = v), (n i - k i))
noncomputable def treePoly {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (src tgt : E → V) (n : E → ℕ) (rho : (E → ℕ) → ℝ) (tau : ℝ) : Polynomial ℝ := ∑ k ∈ splits n,
  C (rho k) * (∑ st : V → Bool, C (tau ^ (Finset.univ.filter (fun i => st (src i) ≠ st (tgt
  i))).card) * X ^ (∑ v ∈ Finset.univ.filter (fun v => st v = true), mass src tgt n k v))
def claim : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V),
    D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.NamedSpanningTree src tgt Set.univ →
    ∀ (n : E → ℕ), (∀ i, 2 ≤ n i) →
    ∀ (rho : (E → ℕ) → ℝ), (∀ k ∈ splits n, 0 < rho k) →
    ∀ tau ∈ Set.Icc (-1 : ℝ) 1, ∀ z : ℂ,
      ((treePoly src tgt n rho tau).map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1
private def rhoW (k : Fin 2 → ℕ) : ℝ := if k 0 = 2 ∧ k 1 = 2 then 10 else if k 0 = 3 ∧ k 1 = 3
  then 31 else 1
private noncomputable def p31 : Polynomial ℝ := 48 - 6*X + 8*X^2 - 62*X^3 + 24*X^4 - 62*X^5 +
  8*X^6 - 6*X^7 + 48*X^8
private theorem mass0 (k : Fin 2 → ℕ) : mass (![0,2] : Fin 2 → Fin 3) (fun _ : Fin 2 => (1 : Fin
  3)) (fun _ : Fin 2 => 4) k 0 = k 0 := by
  have hs : (Finset.univ.filter (fun i : Fin 2 => (![0,2] : Fin 2 → Fin 3) i = 0)) = {0} := by
    decide
  have ht : (Finset.univ.filter (fun i : Fin 2 => (fun _ : Fin 2 => (1 : Fin 3)) i = 0)) = (∅ :
    Finset (Fin 2)) := by decide
  unfold mass; rw [hs,ht]; simp
private theorem mass1 (k : Fin 2 → ℕ) : mass (![0,2] : Fin 2 → Fin 3) (fun _ : Fin 2 => (1 : Fin
  3)) (fun _ : Fin 2 => 4) k 1 = (4-k 0)+(4-k 1) := by
  have hs : (Finset.univ.filter (fun i : Fin 2 => (![0,2] : Fin 2 → Fin 3) i = 1)) = (∅ : Finset
    (Fin 2)) := by decide
  have ht : (Finset.univ.filter (fun i : Fin 2 => (fun _ : Fin 2 => (1 : Fin 3)) i = 1)) =
    (Finset.univ : Finset (Fin 2))
    := by decide
  unfold mass; rw [hs,ht]; simp
private theorem mass2 (k : Fin 2 → ℕ) : mass (![0,2] : Fin 2 → Fin 3) (fun _ : Fin 2 => (1 : Fin
  3)) (fun _ : Fin 2 => 4) k 2 = k 1 := by
  have hs : (Finset.univ.filter (fun i : Fin 2 => (![0,2] : Fin 2 → Fin 3) i = 2)) = {1} := by
    decide
  have ht : (Finset.univ.filter (fun i : Fin 2 => (fun _ : Fin 2 => (1 : Fin 3)) i = 2)) = (∅ :
    Finset (Fin 2)) := by decide
  unfold mass; rw [hs,ht]; simp
private noncomputable def term (st : Fin 3 → Bool) (k : Fin 2 → ℕ) : Polynomial ℝ :=
 C ((-1 : ℝ) ^ (Finset.univ.filter (fun i => st ((![0,2] : Fin 2 → Fin 3) i) ≠ st ((fun _ : Fin 2
   => (1 : Fin 3)) i))).card) *
 X ^ (∑ v ∈ Finset.univ.filter (fun v => st v = true), mass (![0,2] : Fin 2 → Fin 3) (fun _ : Fin 2
   => (1 : Fin 3)) (fun _ : Fin 2 => 4) k v)
private theorem term000 (k : Fin 2 → ℕ) : term ![false,false,false] k = 1 := by
  have he : (Finset.univ.filter (fun i : Fin 2 => (![false,false,false] ((![0,2] : Fin 2 → Fin 3)
    i) ≠
    ![false,false,false] ((fun _ : Fin 2 => (1 : Fin 3)) i)))) = (∅ : Finset (Fin 2)) := by decide
  have hv : (Finset.univ.filter (fun v : Fin 3 => ![false,false,false] v = true)) = (∅ : Finset
    (Fin 3)) := by decide
  unfold term; rw [he,hv]; simp
private theorem term001 (k : Fin 2 → ℕ) : term ![false,false,true] k = - X^(k 1) := by
  have he : (Finset.univ.filter (fun i : Fin 2 => (![false,false,true] ((![0,2] : Fin 2 → Fin 3) i)
    ≠
    ![false,false,true] ((fun _ : Fin 2 => (1 : Fin 3)) i)))) = {1} := by decide
  have hv : (Finset.univ.filter (fun v : Fin 3 => ![false,false,true] v = true)) = {2} := by
    decide
  unfold term; rw [he,hv]; simp [mass2]
private theorem term010 (k : Fin 2 → ℕ) : term ![false,true,false] k = X^((4-k 0)+(4-k 1)) := by
  have he : (Finset.univ.filter (fun i : Fin 2 => (![false,true,false] ((![0,2] : Fin 2 → Fin 3) i)
    ≠
    ![false,true,false] ((fun _ : Fin 2 => (1 : Fin 3)) i)))) = {0,1} := by decide
  have hv : (Finset.univ.filter (fun v : Fin 3 => ![false,true,false] v = true)) = {1} := by
    decide
  unfold term; rw [he,hv]; simp [mass1]
private theorem term011 (k : Fin 2 → ℕ) : term ![false,true,true] k = - X^((4-k 0)+(4-k 1)+k 1)
  := by
  have he : (Finset.univ.filter (fun i : Fin 2 => (![false,true,true] ((![0,2] : Fin 2 → Fin 3) i) ≠
    ![false,true,true] ((fun _ : Fin 2 => (1 : Fin 3)) i)))) = {0} := by decide
  have hv : (Finset.univ.filter (fun v : Fin 3 => ![false,true,true] v = true)) = {1,2} := by
    decide
  unfold term; rw [he,hv]; simp [mass1, mass2]
private theorem term100 (k : Fin 2 → ℕ) : term ![true,false,false] k = - X^(k 0) := by
  have he : (Finset.univ.filter (fun i : Fin 2 => (![true,false,false] ((![0,2] : Fin 2 → Fin 3) i)
    ≠
    ![true,false,false] ((fun _ : Fin 2 => (1 : Fin 3)) i)))) = {0} := by decide
  have hv : (Finset.univ.filter (fun v : Fin 3 => ![true,false,false] v = true)) = {0} := by
    decide
  unfold term; rw [he,hv]; simp [mass0]
private theorem term101 (k : Fin 2 → ℕ) : term ![true,false,true] k = X^(k 0+k 1) := by
  have he : (Finset.univ.filter (fun i : Fin 2 => (![true,false,true] ((![0,2] : Fin 2 → Fin 3) i) ≠
    ![true,false,true] ((fun _ : Fin 2 => (1 : Fin 3)) i)))) = {0,1} := by decide
  have hv : (Finset.univ.filter (fun v : Fin 3 => ![true,false,true] v = true)) = {0,2} := by
    decide
  unfold term; rw [he,hv]; simp [mass0, mass2]
private theorem term110 (k : Fin 2 → ℕ) : term ![true,true,false] k = - X^((4-k 0)+(4-k 1)+k 0)
  := by
  have he : (Finset.univ.filter (fun i : Fin 2 => (![true,true,false] ((![0,2] : Fin 2 → Fin 3) i) ≠
    ![true,true,false] ((fun _ : Fin 2 => (1 : Fin 3)) i)))) = {1} := by decide
  have hv : (Finset.univ.filter (fun v : Fin 3 => ![true,true,false] v = true)) = {0,1} := by
    decide
  unfold term; rw [he,hv]; simp [mass0, mass1]
  congr 1; omega
private theorem term111 (k : Fin 2 → ℕ) : term ![true,true,true] k = X^(k 0 + (4-k 0)+(4-k 1) +
  k 1) := by
  have he : (Finset.univ.filter (fun i : Fin 2 => (![true,true,true] ((![0,2] : Fin 2 → Fin 3) i) ≠
    ![true,true,true] ((fun _ : Fin 2 => (1 : Fin 3)) i)))) = (∅ : Finset (Fin 2)) := by decide
  have hv : (Finset.univ.filter (fun v : Fin 3 => ![true,true,true] v = true)) = (Finset.univ :
    Finset (Fin 3)) := by decide
  unfold term; rw [he,hv]; simp [mass0, mass1, mass2, Fin.sum_univ_three]
  congr 1; omega
private theorem direct (k : Fin 2 → ℕ) :
  (∑ st : Fin 3 → Bool, term st k) =
  1 - X^(k 1) + X^((4-k 0)+(4-k 1)) - X^((4-k 0)+(4-k 1)+k 1) - X^(k 0) + X^(k 0+k 1) - X^((4-k
    0)+(4-k 1)+k 0) + X^(k 0 + (4-k 0)+(4-k 1) + k 1) := by
  let stateEquiv : (Fin 3 → Bool) ≃ (Bool × Bool × Bool) :=
    (Fin.consEquiv (fun _ : Fin 3 => Bool)).symm.trans
      (Equiv.prodCongr (Equiv.refl Bool) (piFinTwoEquiv (fun _ : Fin 2 => Bool)))
  have h : (∑ st : Fin 3 → Bool, term st k) =
      ∑ p : Bool × Bool × Bool, term (stateEquiv.symm p) k := by
    apply Fintype.sum_equiv stateEquiv
    intro st
    simp only [Equiv.symm_apply_apply]
  rw [h]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  have h000 : stateEquiv.symm (false,false,false) = ![false,false,false] := by decide
  have h001 : stateEquiv.symm (false,false,true) = ![false,false,true] := by decide
  have h010 : stateEquiv.symm (false,true,false) = ![false,true,false] := by decide
  have h011 : stateEquiv.symm (false,true,true) = ![false,true,true] := by decide
  have h100 : stateEquiv.symm (true,false,false) = ![true,false,false] := by decide
  have h101 : stateEquiv.symm (true,false,true) = ![true,false,true] := by decide
  have h110 : stateEquiv.symm (true,true,false) = ![true,true,false] := by decide
  have h111 : stateEquiv.symm (true,true,true) = ![true,true,true] := by decide
  simp_rw [h000, h001, h010, h011, h100, h101, h110, h111]
  rw [term000, term001, term010, term011, term100, term101, term110, term111]
  ring
private theorem tree_ok :
    D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.NamedSpanningTree (![0,2] : Fin 2 → Fin
      3) (fun _ : Fin 2 => (1 : Fin 3)) Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _; fin_cases i <;> decide
  · intro i j h
    apply Subtype.ext
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    fin_cases i <;> fin_cases j <;> simp at h ⊢
  · let G : SimpleGraph (Fin 3) := SimpleGraph.fromEdgeSet (Set.range (fun i => s((![0,2] : Fin 2 →
    Fin 3) i, (fun _ : Fin 2 => (1 : Fin 3))
    i)))
    have hs :
        D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.treeSupport (![0,2] : Fin 2 → Fin 3)
          (fun _ : Fin 2 => (1 : Fin 3)) Set.univ = G := by
      unfold D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.treeSupport G
      apply congrArg SimpleGraph.fromEdgeSet
      ext e
      simp [Set.mem_range]
    rw [hs]
    have hG : G = SimpleGraph.starGraph 1 := by
      ext u v
      fin_cases u <;> fin_cases v <;> simp [G, SimpleGraph.starGraph]
    rw [hG]
    exact SimpleGraph.isTree_starGraph 1
set_option maxHeartbeats 30000000 in
-- Exact enumeration of nine splits and eight states uses kernel-reduced finite sums.
set_option maxRecDepth 30000 in
private theorem path_poly : treePoly (![0,2] : Fin 2 → Fin 3) (fun _ : Fin 2 => (1 : Fin 3)) (fun _
  : Fin 2 => 4) rhoW (-1) = p31 := by
  have hs : splits (fun _ : Fin 2 => 4) = {![1,1], ![1,2], ![1,3], ![2,1], ![2,2], ![2,3], ![3,1],
    ![3,2],
    ![3,3]} := by decide
  unfold treePoly
  change (∑ k ∈ splits (fun _ : Fin 2 => 4), C (rhoW k) * (∑ st : Fin 3 → Bool, term st k)) = p31
  rw [hs]
  simp_rw [direct]
  norm_num [rhoW,p31,Finset.sum_insert]
  simp only [Polynomial.C_ofNat]
  ring
private def Qc : Cubic ℝ := ⟨24,45,-2,-26⟩
private theorem q_discr : Qc.discr = (-16404 : ℝ) := by norm_num [Qc, Cubic.discr]
private theorem q_not_splits : ¬ Qc.toPoly.Splits := by
  intro hs
  obtain ⟨x,y,z,hxyz⟩ :=
    (Cubic.splits_iff_roots_eq_three (P := Qc) (φ := RingHom.id ℝ) (by norm_num [Qc])).mp (by
      simpa using hs)
  have hd := Cubic.discr_eq_prod_three_roots (P := Qc) (φ := RingHom.id ℝ)
      (by norm_num [Qc]) hxyz
  rw [RingHom.id_apply, q_discr] at hd
  nlinarith [sq_nonneg (Qc.a * Qc.a * (x-y) * (x-z) * (y-z))]
private theorem exists_nonreal_root : ∃ w : ℂ, (Qc.toPoly.map (algebraMap ℝ ℂ)).IsRoot w ∧ w.im ≠ 0
  := by
  let f := Qc.toPoly.map (algebraMap ℝ ℂ)
  have hs : f.Splits := IsAlgClosed.splits f
  by_contra h
  push Not at h
  have hrange : ∀ a ∈ f.roots, a ∈ (algebraMap ℝ ℂ).range := by
    intro a ha
    have him : a.im = 0 := h a (Polynomial.isRoot_of_mem_roots ha)
    refine ⟨a.re, ?_⟩
    apply Complex.ext
    · simp
    · simp [him]
  have hqsplit : Qc.toPoly.Splits :=
    Polynomial.Splits.of_splits_map_of_injective Complex.ofReal_injective hs hrange
  exact q_not_splits hqsplit
private theorem sextic_factor : p31 = 2 * (X - 1)^2 * (24*X^6 + 45*X^5 + 70*X^4 + 64*X^3 +
  70*X^2 + 45*X + 24) := by
  simp [p31]
  ring
private theorem lift_root (w : ℂ) (hw : (Qc.toPoly.map (algebraMap ℝ ℂ)).IsRoot w)
    (hwim : w.im ≠ 0) : ∃ z : ℂ,
      (p31.map (algebraMap ℝ ℂ)).IsRoot z ∧ ‖z‖ ≠ 1 := by
  let r : Polynomial ℂ := X^2 - C w * X + C 1
  have hrdeg : r.degree ≠ 0 := by
    intro hd
    have hc := Polynomial.coeff_eq_zero_of_degree_lt (p := r) (n := 2) (by rw [hd]; norm_num)
    norm_num [r, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_one] at hc
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root r hrdeg
  have hzq : z^2 - w*z + 1 = 0 := by
    simpa [Polynomial.IsRoot, r, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow] using hz
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    norm_num at hzq
  have hwz : w*z = z^2 + 1 := by
    linear_combination -hzq
  have hwrel : w = z + z⁻¹ := by
    calc
      w = (w*z) / z := by field_simp
      _ = (z^2 + 1) / z := by rw [hwz]
      _ = z + z⁻¹ := by field_simp [hz0]
  have hq : 24*w^3 + 45*w^2 - 2*w - 26 = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Qc, Cubic.toPoly, sub_eq_add_neg] using hw
  have hqsub : 24*(z+z⁻¹)^3 + 45*(z+z⁻¹)^2 - 2*(z+z⁻¹) - 26 = 0 := by
    rw [← hwrel]
    exact hq
  have hsext : 24*z^6 + 45*z^5 + 70*z^4 + 64*z^3 + 70*z^2 + 45*z + 24 = 0 := by
    have hid : z^3 * (24*(z+z⁻¹)^3 + 45*(z+z⁻¹)^2 - 2*(z+z⁻¹) - 26) =
        24*z^6 + 45*z^5 + 70*z^4 + 64*z^3 + 70*z^2 + 45*z + 24 := by
      field_simp [hz0]
      ring
    rw [← hid, hqsub]
    simp
  have hp : (p31.map (algebraMap ℝ ℂ)).IsRoot z := by
    rw [sextic_factor]
    simp only [Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_pow,
      Polynomial.map_sub, map_X, Polynomial.map_one, Polynomial.map_add, IsRoot.def,
      eval_mul, eval_ofNat, eval_pow, eval_sub, eval_X, eval_one, eval_add,
      mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or]
    rw [hsext]
    simp
  refine ⟨z, hp, ?_⟩
  intro hnorm
  have hinv : z⁻¹ = (starRingEnd ℂ) z := Complex.inv_eq_conj hnorm
  have him : (z + z⁻¹).im = 0 := by simp [hinv]
  exact hwim (by rw [hwrel, him])
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨w, hw, hwim⟩ := exists_nonreal_root
  obtain ⟨z, hz, hznorm⟩ := lift_root w hw hwim
  have htree :
      D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.NamedSpanningTree (![0,2] : Fin 2 → Fin
        3) (fun _ : Fin 2 => (1 : Fin 3)) Set.univ :=
    tree_ok
  have hn : ∀ i, 2 ≤ (fun _ : Fin 2 => 4) i := by intro i; norm_num
  have hrho : ∀ k ∈ splits (fun _ : Fin 2 => 4), 0 < rhoW k := by
    intro k hk
    unfold rhoW
    split <;> norm_num; split <;> norm_num
  have htau : (-1 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
  have hz' : ((treePoly (![0,2] : Fin 2 → Fin 3) (fun _ : Fin 2 => (1 : Fin 3)) (fun _ : Fin 2 =>
    4) rhoW (-1)).map (algebraMap ℝ ℂ)).IsRoot z := by
    rw [path_poly]
    exact hz
  have hunit := hclaim (Fin 3) (Fin 2) (![0,2] : Fin 2 → Fin 3) (fun _ : Fin 2 => (1 : Fin 3))
    htree (fun _ : Fin 2 => 4) hn rhoW hrho (-1) htau z hz'
  exact hznorm hunit
end D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
