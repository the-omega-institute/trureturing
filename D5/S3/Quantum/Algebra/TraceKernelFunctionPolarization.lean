/- GID: D5/S3/Quantum/Algebra/TraceKernelFunctionPolarization
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/TraceKernelFunctionPolarization
   mirror-E: none(waiver:partial-content)
   anchors: []
   utility: none
   digest: Mixed trace-kernel polarization for arbitrary all-parameter representatives. -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors
Modified: specialized to Fin N and inlined into the mixed polarization proof.
Released under Apache 2.0; full license: docs/reports/polarization-suppliers/tauceti-LICENSE.txt.
proof_shape: content; admission_basis: escape-witness (partial theorem only).
The local SU-circle reduction transplants the exact theorem body from Tau Ceti
`TauCeti/Analysis/Matrix/UnitaryGroup/Basic.lean`, Apache-2.0, revision
`d8fd630a6d98d0e5933f51cb0819ef09f28fa2b4`, source SHA256
`035da15c06911fd22cbb002fa12db0347ab3c108ad553b9cc0b72eebfb1e8f2f`.
The upstream pins are Lean v4.35.0-rc3 / Mathlib 1b5006ca00888f8aaafa8939b28787d423e44bba;
our pins are Lean v4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Dependency form fails this pin comparison; this is a transplant under A17.2.
Retire the local SU-circle proof when our own pinned Mathlib contains an equivalent
Matrix.exists_circle_smul_mem_specialUnitaryGroup: check its full type and compile
the direct application at Fin N on that pin, then replace this local proof.
The inspected upstream source tree has no NOTICE file; no NOTICE chain is present.
Only the needed existence proof is integrated locally; no named supplier helper
or generated simp companion is retained. Full source-witness generation remains open.
-/
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.UnitaryGroup

open scoped BigOperators Matrix
open MvPolynomial Finset
local notation "coeff" m:arg p:arg => AddMonoidAlgebra.coeff p m

namespace D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization
set_option maxHeartbeats 1500000 in
set_option maxRecDepth 5000 in
-- Polynomial induction and nested coefficient substitutions require this elaboration budget.
theorem trace_kernel_function_polarization (m n N : ℕ) (hN : 1 ≤ N)
    (f : {Z : Matrix (Fin N) (Fin N) ℂ // Matrix.trace Z = 0} → {W : Matrix (Fin N) (Fin N) ℂ // Matrix.trace W = 0} → ℂ)
    (hSU : ∀ (U : Matrix (Fin N) (Fin N) ℂ), U ∈ Matrix.specialUnitaryGroup (Fin N) ℂ →
      ∀ Z W : {Z : Matrix (Fin N) (Fin N) ℂ // Matrix.trace Z = 0},
      ∀ hZ : Matrix.trace (U * Z.val * Uᴴ) = 0,
      ∀ hW : Matrix.trace (U * W.val * Uᴴ) = 0, f ⟨U * Z.val * Uᴴ, hZ⟩ ⟨U * W.val * Uᴴ, hW⟩ = f Z W)
    (P : MvPolynomial (Bool × (Fin N × Fin N)) ℂ)
    (hP : ∀ Z W, eval (fun e : Bool × (Fin N × Fin N) => if e.1 then W.val e.2.1 e.2.2 else Z.val e.2.1 e.2.2) P = f Z W)
    (hdegree : ∀ (a b : ℂ) Z W, f ⟨a • Z.val, by simp [Matrix.trace_smul, Z.property]⟩ ⟨b • W.val, by simp [Matrix.trace_smul, W.property]⟩ =
        a ^ m * b ^ n * f Z W) :
    ∃ F : MultilinearMap ℂ (fun _ : Fin m ⊕ Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ,
      (∀ x, F x = ((m.factorial : ℂ) * (n.factorial : ℂ))⁻¹ * coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin m ⊕ Fin n => 1))
          (eval₂ C (fun v : Bool × (Fin N × Fin N) => if v.1 then ∑ j : Fin n, C (x (Sum.inr j) v.2.1 v.2.2) * X (Sum.inr j)
            else ∑ i : Fin m, C (x (Sum.inl i) v.2.1 v.2.2) * X (Sum.inl i))
              (MvPolynomial.eval₂Hom MvPolynomial.C (fun e : Bool × (Fin N × Fin N) => MvPolynomial.X e - if e.2.1 = e.2.2 then MvPolynomial.C ((N : ℂ)⁻¹) * ∑ k : Fin N, MvPolynomial.X (e.1, k, k) else 0) P))) ∧
      (∀ Z W, F (Sum.elim (fun _ => Z.val) (fun _ => W.val)) = f Z W) ∧
      (∀ T : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ,
        (∀ Z W : Matrix (Fin N) (Fin N) ℂ, eval (fun e : Bool × (Fin N × Fin N) => if e.1 then (T W) e.2.1 e.2.2 else (T Z) e.2.1 e.2.2) (MvPolynomial.eval₂Hom MvPolynomial.C (fun e : Bool × (Fin N × Fin N) => MvPolynomial.X e - if e.2.1 = e.2.2 then MvPolynomial.C ((N : ℂ)⁻¹) * ∑ k : Fin N, MvPolynomial.X (e.1, k, k) else 0) P) =
          eval (fun e : Bool × (Fin N × Fin N) => if e.1 then W e.2.1 e.2.2 else Z e.2.1 e.2.2) (MvPolynomial.eval₂Hom MvPolynomial.C (fun e : Bool × (Fin N × Fin N) => MvPolynomial.X e - if e.2.1 = e.2.2 then MvPolynomial.C ((N : ℂ)⁻¹) * ∑ k : Fin N, MvPolynomial.X (e.1, k, k) else 0) P)) →
        ∀ x, F (fun j => T (x j)) = F x) ∧
      (∀ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ x, F (fun j => (U : Matrix (Fin N) (Fin N) ℂ) * x j * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ) = F x) := by
  classical
  let q : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ := fun Z => Z - (Matrix.trace Z / (N : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)
  let entries (Z W : Matrix (Fin N) (Fin N) ℂ) : (Bool × (Fin N × Fin N)) → ℂ := fun e => if e.1 then W e.2.1 e.2.2 else Z e.2.1 e.2.2
  let projectedVariable (e : Bool × (Fin N × Fin N)) : MvPolynomial (Bool × (Fin N × Fin N)) ℂ :=
    MvPolynomial.X e - if e.2.1 = e.2.2 then MvPolynomial.C ((N : ℂ)⁻¹) * ∑ k : Fin N, MvPolynomial.X (e.1, k, k) else 0
  let Q : MvPolynomial (Bool × (Fin N × Fin N)) ℂ →+* MvPolynomial (Bool × (Fin N × Fin N)) ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C projectedVariable
  have trace_q (Z : Matrix (Fin N) (Fin N) ℂ) : Matrix.trace (q Z) = 0 := by
    have h : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simp [q, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, div_mul_cancel₀ _ h]
  have q_of_trace_zero (Z : Matrix (Fin N) (Fin N) ℂ) (hZ : Matrix.trace Z = 0) : q Z = Z := by
    simp [q, hZ]
  have eval_Q (P : MvPolynomial (Bool × (Fin N × Fin N)) ℂ) (Z W : Matrix (Fin N) (Fin N) ℂ) :
      MvPolynomial.eval (entries Z W) (Q P) = MvPolynomial.eval (entries (q Z) (q W)) P := by
    change MvPolynomial.eval _ (MvPolynomial.eval₂Hom _ _ P) = _; change MvPolynomial.eval _ (MvPolynomial.eval₂ MvPolynomial.C projectedVariable P) = _
    rw [MvPolynomial.eval_eval₂]
    simp only [show ∀ e, MvPolynomial.eval (entries Z W) (projectedVariable e) = entries (q Z) (q W) e by
      intro e; rcases e with ⟨c,i,j⟩; cases c <;> by_cases hij : i = j <;>
        simp [projectedVariable, entries, q, Matrix.trace, div_eq_mul_inv, mul_comm, hij]]
    have hc : (MvPolynomial.eval (entries Z W)).comp MvPolynomial.C = RingHom.id ℂ := by
      ext c; simp
    rw [hc, MvPolynomial.eval₂_id]
  have hP' : ∀ Z W : Matrix (Fin N) (Fin N) ℂ, MvPolynomial.eval (entries Z W) (Q P) = f ⟨q Z, trace_q Z⟩ ⟨q W, trace_q W⟩ := by
    intro Z W; rw [eval_Q]; simpa [entries] using hP ⟨q Z, trace_q Z⟩ ⟨q W, trace_q W⟩
  let V := Fin N × Fin N
  let flat : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] (V → ℂ) := { toFun := fun Z v => Z v.1 v.2, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  have hq (a : ℂ) (Z : Matrix (Fin N) (Fin N) ℂ) : q (a • Z) = a • q Z := by
    unfold q; rw [Matrix.trace_smul, smul_sub, smul_smul]; simp only [smul_eq_mul, mul_div_assoc]
  have hfull (a b : ℂ) (Z W : V → ℂ) : eval (fun v : Bool × V => if v.1 then b * W v.2 else a * Z v.2) (Q P) =
        a ^ m * b ^ n * eval (fun v => if v.1 then W v.2 else Z v.2) (Q P) := by
    let ZZ : Matrix (Fin N) (Fin N) ℂ := fun i j => Z (i,j)
    let WW : Matrix (Fin N) (Fin N) ℂ := fun i j => W (i,j)
    change eval (entries (a • ZZ) (b • WW)) (Q P) = a ^ m * b ^ n * eval (entries ZZ WW) (Q P)
    rw [eval_Q, eval_Q]
    have hp1 : eval (entries (q ZZ) (q WW)) P = f ⟨q ZZ, trace_q ZZ⟩ ⟨q WW, trace_q WW⟩ := by
      rw [← eval_Q]; exact hP' ZZ WW
    have hp2 : eval (entries (a • q ZZ) (b • q WW)) P = f ⟨a • q ZZ, by simp [Matrix.trace_smul, trace_q]⟩
          ⟨b • q WW, by simp [Matrix.trace_smul, trace_q]⟩ := by
      have hh := hP' (a • ZZ) (b • WW)
      rw [eval_Q] at hh; simpa only [hq] using hh
    rw [hq a ZZ, hq b WW, hp2, hp1]; exact hdegree a b ⟨q ZZ, trace_q ZZ⟩ ⟨q WW, trace_q WW⟩
  have hcore {σ : Type} [Fintype σ] (m n : ℕ) (P : MvPolynomial (Bool × σ) ℂ)
      (hdegree : ∀ (a b : ℂ) (Z W : σ → ℂ), eval (fun v => if v.1 then b * W v.2 else a * Z v.2) P =
          a ^ m * b ^ n * eval (fun v => if v.1 then W v.2 else Z v.2) P) :
      ∃ F : MultilinearMap ℂ (fun _ : Fin m ⊕ Fin n => σ → ℂ) ℂ, (∀ x, F x = ((m.factorial : ℂ) * (n.factorial : ℂ))⁻¹ *
          coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin m ⊕ Fin n => 1))
            (eval₂ C (fun v => if v.1 then ∑ j : Fin n, C (x (Sum.inr j) v.2) * X (Sum.inr j)
              else ∑ i : Fin m, C (x (Sum.inl i) v.2) * X (Sum.inl i)) P)) ∧
        (∀ Z W : σ → ℂ, F (Sum.elim (fun _ => Z) (fun _ => W)) = eval (fun v => if v.1 then W v.2 else Z v.2) P) ∧
        (∀ T : (σ → ℂ) →ₗ[ℂ] (σ → ℂ), (∀ Z W : σ → ℂ, eval (fun v => if v.1 then T W v.2 else T Z v.2) P =
              eval (fun v => if v.1 then W v.2 else Z v.2) P) →
          ∀ x, F (fun j => T (x j)) = F x) := by
    classical
    let J := Fin m ⊕ Fin n
    let color : J → Bool := Sum.elim (fun _ => false) (fun _ => true)
    let L (j : J) : (σ → ℂ) →ₗ[ℂ] (Bool × σ → ℂ) :=
      { toFun := fun z v => if v.1 = color j then z v.2 else 0
        map_add' := by
          intros; funext v; by_cases h : v.1 = color j <;> simp [h]
        map_smul' := by
          intros; funext v; by_cases h : v.1 = color j <;> simp [h] }
    have hgeneral {σ J : Type} [Fintype σ] [Fintype J] (P : MvPolynomial σ ℂ) : ∃ F : MultilinearMap ℂ (fun _ : J => σ → ℂ) ℂ, ∀ x : J → σ → ℂ,
            F x = coeff (Finsupp.equivFunOnFinite.symm (fun _ : J => 1)) (eval₂ C (fun v => ∑ j : J, C (x j v) * X j) P) := by
      classical
      let S (x : J → σ → ℂ) (v : σ) : MvPolynomial J ℂ := ∑ j : J, C (x j v) * X j
      let ones : J →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
      let f (x : J → σ → ℂ) : ℂ := coeff ones (eval₂ C (S x) P)
      have slot_formula (x : J → σ → ℂ) (i : J) : f x = ∑ v : σ, x i v * coeff (Finsupp.equivFunOnFinite.symm (fun _ : {j : J // j ≠ i} => 1))
              (eval₂ C (fun v => ∑ j : {j : J // j ≠ i}, C (x j v) * X j) (pderiv v P)) := by
        let T := {j : J // j ≠ i}
        let e : T →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
        let d : J →₀ ℕ := e.mapDomain Subtype.val
        let K : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial T ℂ := killCompl Subtype.val_injective
        have hd : d i = 0 := by
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨j, hj⟩
          exact j.property hj
        have hone : d + Finsupp.single i 1 = ones := by
          ext j
          by_cases h : j = i
          · subst j
            simp [hd, ones]
          · have hv := Finsupp.mapDomain_apply_of_injective Subtype.val_injective e (⟨j, h⟩ : T)
            simpa [d, e, ones, h] using hv
        have hKX (j : J) : K (X j) = if h : j ≠ i then X (⟨j, h⟩ : T) else 0 := by
          by_cases h : j ≠ i
          · rw [dif_pos h]
            have hx : (X j : MvPolynomial J ℂ) = rename Subtype.val (X (⟨j, h⟩ : T) : MvPolynomial T ℂ) := by
              rw [rename_X]
            dsimp only [K]; rw [hx, killCompl_rename_app]
          · simp only [K, killCompl, aeval_X]
            have hr : j ∉ Set.range (Subtype.val : T → J) := by
              rintro ⟨t, rfl⟩
              exact h t.property
            simp [hr, h]
        have hKS (v : σ) : K (S x v) = ∑ j : T, C (x j v) * X j := by
          simp only [S, map_sum, map_mul, algHom_C, hKX, MvPolynomial.algebraMap_eq]
          let g (j : J) : MvPolynomial T ℂ := C (x j v) * if h : j ≠ i then X (⟨j, h⟩ : T) else 0
          change (∑ j : J, g j) = _
          calc
            _ = ∑ j ∈ Finset.univ.erase i, g j := by
              apply (Finset.sum_subset (Finset.erase_subset i Finset.univ) ?_).symm
              intro j hj hn
              have hji : j = i := by
                by_contra h
                exact hn (Finset.mem_erase.mpr ⟨h, hj⟩)
              subst j
              simp [g]
            _ = ∑ j : T, g j := Finset.sum_subtype _ (by simp) g
            _ = _ := by
              apply Finset.sum_congr rfl
              intro j hj; simp [g, j.property]
        have hchain (Q : MvPolynomial σ ℂ) : pderiv i (eval₂ C (S x) Q) = ∑ v : σ, C (x i v) * eval₂ C (S x) (pderiv v Q) := by
          induction Q using MvPolynomial.induction_on with
          | C a => simp
          | add A B hA hB => simp [hA, hB, mul_add, Finset.sum_add_distrib]
          | mul_X A v hA =>
            have hSi : pderiv i (S x v) = C (x i v) := by
              simp [S, Pi.single_apply]
            have hpi (w : σ) : eval₂ C (S x) (Pi.single (M := fun _ : σ => MvPolynomial σ ℂ) w 1 v) = if v = w then 1 else 0 := by
              by_cases h : v = w <;> simp [h]
            simp only [eval₂_mul, eval₂_X, pderiv_mul, hSi, hA, pderiv_X, eval₂_add, eval₂_mul, eval₂_X, hpi]
            simp only [
              mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
              Finset.sum_ite_eq]
            rw [Finset.sum_mul]
            have hs : (∑ w : σ, C (x i w) * eval₂ C (S x) (pderiv w A) * S x v) = ∑ w : σ, C (x i w) * (eval₂ C (S x) (pderiv w A) * S x v) := by
              apply Finset.sum_congr rfl
              intro w hw; ring
            rw [hs]; congr 1; simpa only [if_pos (Finset.mem_univ v)] using
              mul_comm (eval₂ C (S x) A) (C (x i v))
        have hKeval (Q : MvPolynomial σ ℂ) : K (eval₂ C (S x) Q) = eval₂ C (fun v => ∑ j : T, C (x j v) * X j) Q := by
          change K.toRingHom (eval₂ C (S x) Q) = _; rw [hom_eval₂]; change eval₂ (K.toRingHom.comp C) (fun v => K (S x v)) Q = _; simp only [hKS]
          have hc : K.toRingHom.comp (C : ℂ →+* MvPolynomial J ℂ) = C := by
            ext a; simp [MvPolynomial.algebraMap_eq]
          rw [hc]
        change coeff ones (eval₂ C (S x) P) = _
        have hder := coeff_pderiv (i := i) (eval₂ C (S x) P) d
        simp only [hd, Nat.cast_zero, zero_add, mul_one, hone] at hder; rw [← hder]
        have hk := coeff_killCompl (p := pderiv i (eval₂ C (S x) P)) (s := e) Subtype.val_injective
        rw [← hk]; change coeff e (K (pderiv i (eval₂ C (S x) P))) = _; rw [hchain]
        simp only [map_sum, map_mul, algHom_C, MvPolynomial.algebraMap_eq, hKeval, coeff_sum, coeff_C_mul]
        rfl
      refine ⟨{ toFun := f, map_update_add' := ?_, map_update_smul' := ?_ }, fun x => rfl⟩
      · intro _ x i a b
        rw [slot_formula _ i, slot_formula _ i, slot_formula _ i]; simp only [Function.update_self, Pi.add_apply]
        have hup (z : σ → ℂ) (j : {j : J // j ≠ i}) : Function.update x i z j = x j := Function.update_of_ne j.property _ _
        simp only [hup, add_mul, Finset.sum_add_distrib]
      · intro _ x i c a
        rw [slot_formula _ i, slot_formula _ i]; simp only [Function.update_self, Pi.smul_apply, smul_eq_mul]
        have hup (z : σ → ℂ) (j : {j : J // j ≠ i}) : Function.update x i z j = x j := Function.update_of_ne j.property _ _
        simp only [hup, mul_assoc, Finset.mul_sum]
    obtain ⟨G, hG⟩ := hgeneral (J := J) P
    let k : ℂ := ((m.factorial : ℂ) * (n.factorial : ℂ))⁻¹
    let F := k • G.compLinearMap L
    have hF (x : J → σ → ℂ) : F x = k * coeff (Finsupp.equivFunOnFinite.symm (fun _ : J => 1))
          (eval₂ C (fun v => if v.1 then ∑ j : Fin n, C (x (Sum.inr j) v.2) * X (Sum.inr j)
            else ∑ i : Fin m, C (x (Sum.inl i) v.2) * X (Sum.inl i)) P) := by
      simp only [F, smul_apply, MultilinearMap.compLinearMap_apply, smul_eq_mul, hG]
      have hs : (fun v : Bool × σ => ∑ j : J, C (L j (x j) v) * X j) =
          (fun v => if v.1 then ∑ j : Fin n, C (x (Sum.inr j) v.2) * X (Sum.inr j)
            else ∑ i : Fin m, C (x (Sum.inl i) v.2) * X (Sum.inl i)) := by
        funext v; rcases v with ⟨b, v⟩
        cases b <;> simp [J, L, color, Fintype.sum_sum_type]
      rw [hs]
    refine ⟨F, hF, ?_, ?_⟩
    · intro Z W
      rw [hF]
      let A : MvPolynomial J ℂ := ∑ i : Fin m, X (Sum.inl i)
      let B : MvPolynomial J ℂ := ∑ j : Fin n, X (Sum.inr j)
      let p : ℂ := eval (fun v => if v.1 then W v.2 else Z v.2) P
      have heq : eval₂ C (fun v : Bool × σ => if v.1 then ∑ j : Fin n, C (W v.2) * X (Sum.inr j) else ∑ i : Fin m, C (Z v.2) * X (Sum.inl i)) P =
          C p * A ^ m * B ^ n := by
        apply MvPolynomial.funext
        intro t; rw [eval_eval₂]
        have hc : (eval t).comp (C : ℂ →+* MvPolynomial J ℂ) = RingHom.id ℂ := by
          ext c; simp
        rw [hc, eval₂_id]; simp only [map_mul, map_pow, eval_C, A, B, map_sum, eval_X]
        have hin : (fun v : Bool × σ => eval t (if v.1 then ∑ j : Fin n, C (W v.2) * X (Sum.inr j) else ∑ i : Fin m, C (Z v.2) * X (Sum.inl i))) =
            (fun v => if v.1 then (∑ j : Fin n, t (Sum.inr j)) * W v.2
              else (∑ i : Fin m, t (Sum.inl i)) * Z v.2) := by
          funext v; cases v.1 <;> simp [Finset.mul_sum, mul_comm]
        rw [hin]; simpa [p, mul_assoc, mul_comm, mul_left_comm] using
          hdegree (∑ i : Fin m, t (Sum.inl i)) (∑ j : Fin n, t (Sum.inr j)) Z W
      simp only [Sum.elim_inl, Sum.elim_inr]; rw [heq]
      let a : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
      let b : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
      have hsplit (Q : MvPolynomial J ℂ) : coeff (Finsupp.equivFunOnFinite.symm (fun _ : J => 1)) Q =
            coeff b (coeff a (sumAlgEquiv ℂ (Fin m) (Fin n) Q)) := by
        let e := Finsupp.sumFinsuppAddEquivProdFinsupp (M := ℕ) (α := Fin m) (β := Fin n)
        change coeff _ Q = AddMonoidAlgebra.coeff
          (AddMonoidAlgebra.domCongr ℂ ℂ e Q) (a, b)
        rw [AddMonoidAlgebra.coeff_domCongr]; congr 1; ext j; cases j <;> rfl
      have hfac (r : ℕ) : coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin r => 1))
          ((∑ i : Fin r, X i : MvPolynomial (Fin r) ℂ) ^ r) = (r.factorial : ℂ) := by
        rw [coeff_sum_X_pow_of_fintype]
        simp [Finsupp.sum_of_support_subset _ (Finset.subset_univ _),
          Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial]
      rw [hsplit]
      let A' : MvPolynomial (Fin m) (MvPolynomial (Fin n) ℂ) := ∑ i : Fin m, X i
      let B' : MvPolynomial (Fin n) ℂ := ∑ j : Fin n, X j
      have hA : sumAlgEquiv ℂ (Fin m) (Fin n) A = A' := by
        dsimp only [A, A']; rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj; exact sumAlgEquiv_X_inl ℂ (Fin m) (Fin n) j
      have hB : sumAlgEquiv ℂ (Fin m) (Fin n) B = C B' := by
        dsimp only [B, B']; rw [map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro j hj; exact sumAlgEquiv_X_inr ℂ (Fin m) (Fin n) j
      have hmap : sumAlgEquiv ℂ (Fin m) (Fin n) (C p * A ^ m * B ^ n) = C (C p) * A' ^ m * C (B' ^ n) := by
        rw [map_mul, map_mul, map_pow, map_pow, hA, hB, sumAlgEquiv_C_inl, map_pow]
      rw [hmap]
      have hfac' : coeff a ((∑ i : Fin m, X i : MvPolynomial (Fin m) (MvPolynomial (Fin n) ℂ)) ^ m) = C (m.factorial : ℂ) := by
        rw [coeff_sum_X_pow_of_fintype]
        simp [a, Finsupp.sum_of_support_subset _ (Finset.subset_univ _),
          Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial]
      change k * coeff b (coeff a (C (C p) * A' ^ m * C (B' ^ n))) = p
      rw [show C (C p) * A' ^ m * C (B' ^ n) = C (C p * B' ^ n) * A' ^ m by
        rw [map_mul]; ring]
      rw [coeff_C_mul, hfac']
      rw [show (C p * B' ^ n) * C (m.factorial : ℂ) = C (p * (m.factorial : ℂ)) * B' ^ n by
        rw [map_mul]; ring]
      rw [coeff_C_mul]
      change k * ((p * (m.factorial : ℂ)) * coeff
        (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => 1)) (B' ^ n)) = p
      rw [hfac]
      have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      dsimp [k]
      rw [show p * (m.factorial : ℂ) * (n.factorial : ℂ) =
      ((m.factorial : ℂ) * (n.factorial : ℂ)) * p by ring,
      inv_mul_cancel_left₀ (mul_ne_zero hm hn)]

    · intro T hT x
      rw [hF, hF]
      apply congrArg (fun Q : MvPolynomial J ℂ => k * coeff (Finsupp.equivFunOnFinite.symm (fun _ : J => 1)) Q)
      apply MvPolynomial.funext
      intro t; rw [eval_eval₂, eval_eval₂]
      have hc : (eval t).comp (C : ℂ →+* MvPolynomial J ℂ) = RingHom.id ℂ := by
        ext c; simp
      rw [hc, eval₂_id, eval₂_id]
      let Z : σ → ℂ := ∑ i : Fin m, t (Sum.inl i) • x (Sum.inl i)
      let W : σ → ℂ := ∑ j : Fin n, t (Sum.inr j) • x (Sum.inr j)
      have htx : (fun v : Bool × σ => eval t (if v.1 then ∑ j : Fin n, C (T (x (Sum.inr j)) v.2) * X (Sum.inr j)
           else ∑ i : Fin m, C (T (x (Sum.inl i)) v.2) * X (Sum.inl i))) =
          (fun v => if v.1 then T W v.2 else T Z v.2) := by
        funext v; cases v.1 <;> simp [Z, W, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, mul_comm]
      have hx : (fun v : Bool × σ => eval t (if v.1 then ∑ j : Fin n, C (x (Sum.inr j) v.2) * X (Sum.inr j)
           else ∑ i : Fin m, C (x (Sum.inl i) v.2) * X (Sum.inl i))) =
          (fun v => if v.1 then W v.2 else Z v.2) := by
        funext v; cases v.1 <;> simp [Z, W, map_sum, Finset.sum_apply, Pi.smul_apply, mul_comm]
      rw [htx, hx]; exact hT Z W
  obtain ⟨G, hG, hdiag, hInv⟩ := hcore m n (Q P) hfull
  refine ⟨G.compLinearMap (fun _ => flat), ?_, ?_, ?_, ?_⟩
  · intro x
    have hflat (Z : Matrix (Fin N) (Fin N) ℂ) (v : V) : flat Z v = Z v.1 v.2 := rfl
    rw [MultilinearMap.compLinearMap_apply, hG]; simp only [hflat]; rfl
  · intro Z W
    have hx : (fun j : Fin m ⊕ Fin n => flat (Sum.elim (fun _ => Z.val) (fun _ => W.val) j)) =
        Sum.elim (fun _ => flat Z.val) (fun _ => flat W.val) := by
      funext j; cases j <;> rfl
    rw [MultilinearMap.compLinearMap_apply, hx, hdiag]; change eval (entries Z.val W.val) (Q P) = _
    rw [eval_Q, q_of_trace_zero Z.val Z.property, q_of_trace_zero W.val W.property]; exact hP Z W
  · intro T hT x
    let unflat : (V → ℂ) →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ := { toFun := fun z i j => z (i,j), map_add' := by intros; rfl, map_smul' := by intros; rfl }
    let TT := flat.comp (T.comp unflat)
    have hTT (Z W : V → ℂ) : eval (fun v : Bool × V => if v.1 then TT W v.2 else TT Z v.2) (Q P) =
          eval (fun v => if v.1 then W v.2 else Z v.2) (Q P) := by
      exact hT (unflat Z) (unflat W)
    have huf (Z : Matrix (Fin N) (Fin N) ℂ) : unflat (flat Z) = Z := rfl
    change G (fun j => flat (T (x j))) = G (fun j => flat (x j))
    have hi := hInv TT hTT (fun j => flat (x j))
    change G (fun j => flat (T (unflat (flat (x j))))) = G (fun j => flat (x j)) at hi; simpa only [huf] using hi

  · intro U x
    have htr (A : Matrix.unitaryGroup (Fin N) ℂ) (Z : Matrix (Fin N) (Fin N) ℂ) :
        Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ) * Z * (A : Matrix (Fin N) (Fin N) ℂ)ᴴ) = Matrix.trace Z := by
      rw [Matrix.trace_mul_cycle]; rw [show (A : Matrix (Fin N) (Fin N) ℂ)ᴴ * (A : Matrix (Fin N) (Fin N) ℂ) = 1 from A.property.1]
      simp
    have hUU : (U : Matrix (Fin N) (Fin N) ℂ) * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ = 1 := U.property.2
    have hqc (Z : Matrix (Fin N) (Fin N) ℂ) : q ((U : Matrix (Fin N) (Fin N) ℂ) * Z * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ) =
        (U : Matrix (Fin N) (Fin N) ℂ) * q Z * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
      simp [q, htr, Matrix.mul_sub, Matrix.sub_mul, hUU]
    have hSUcircle (A : Matrix.unitaryGroup (Fin N) ℂ) :
        ∃ c : Circle, ((c : ℂ) • (A : Matrix (Fin N) (Fin N) ℂ)) ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
      have hunit : ∀ c : Circle, ((c : ℂ) • (A : Matrix (Fin N) (Fin N) ℂ)) ∈ Matrix.unitaryGroup (Fin N) ℂ := fun c => by
        apply Unitary.smul_mem_of_mem
        · apply Unitary.mem_iff_star_mul_self.mpr
          rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]
        · exact A.2
      rcases isEmpty_or_nonempty (Fin N) with hn | hn
      · exact ⟨1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hunit 1, Matrix.det_isEmpty⟩⟩
      · have hcard : (Fintype.card (Fin N) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        have hnorm : ‖(A : Matrix (Fin N) (Fin N) ℂ).det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary A.2)
        obtain ⟨θ, hθ⟩ := Circle.exp_surjective
          (⟨(A : Matrix (Fin N) (Fin N) ℂ).det, mem_sphere_zero_iff_norm.mpr hnorm⟩ : Circle)
        have hdetA : (A : Matrix (Fin N) (Fin N) ℂ).det = Complex.exp ((θ : ℂ) * Complex.I) := by
          have := congrArg (fun z : Circle => (z : ℂ)) hθ
          rw [Circle.coe_exp] at this; exact this.symm
        refine ⟨Circle.exp (-(θ / Fintype.card (Fin N))), Matrix.mem_specialUnitaryGroup_iff.mpr
          ⟨hunit _, ?_⟩⟩
        rw [Matrix.det_smul, Circle.coe_exp, hdetA, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_zero]
        congr 1; push_cast; field_simp; ring
    obtain ⟨c, hc⟩ := hSUcircle U
    have hc1 : star (c : ℂ) * (c : ℂ) = 1 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]
    have hcc (Z : Matrix (Fin N) (Fin N) ℂ) : ((c : ℂ) • (U : Matrix (Fin N) (Fin N) ℂ)) * Z *
        ((c : ℂ) • (U : Matrix (Fin N) (Fin N) ℂ))ᴴ = (U : Matrix (Fin N) (Fin N) ℂ) * Z * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc1, one_smul]
    have hfU (Z W : {Z : Matrix (Fin N) (Fin N) ℂ // Matrix.trace Z = 0}) :
        f ⟨(U : Matrix (Fin N) (Fin N) ℂ) * Z.val * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ, by rw [htr, Z.property]⟩
          ⟨(U : Matrix (Fin N) (Fin N) ℂ) * W.val * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ, by rw [htr, W.property]⟩ = f Z W := by
      have hz : Matrix.trace (((c : ℂ) • (U : Matrix (Fin N) (Fin N) ℂ)) * Z.val *
          ((c : ℂ) • (U : Matrix (Fin N) (Fin N) ℂ))ᴴ) = 0 := by rw [hcc, htr, Z.property]
      have hw : Matrix.trace (((c : ℂ) • (U : Matrix (Fin N) (Fin N) ℂ)) * W.val *
          ((c : ℂ) • (U : Matrix (Fin N) (Fin N) ℂ))ᴴ) = 0 := by rw [hcc, htr, W.property]
      simpa only [hcc] using hSU ((c : ℂ) • (U : Matrix (Fin N) (Fin N) ℂ)) hc Z W hz hw
    let T : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
      { toFun := fun Z => (U : Matrix (Fin N) (Fin N) ℂ) * Z * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ
        map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
        map_smul' := by intros; simp }
    have hT (Z W : Matrix (Fin N) (Fin N) ℂ) : eval (entries (T Z) (T W)) (Q P) = eval (entries Z W) (Q P) := by
      rw [eval_Q, eval_Q]
      change eval (entries (q ((U : Matrix (Fin N) (Fin N) ℂ) * Z * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ))
        (q ((U : Matrix (Fin N) (Fin N) ℂ) * W * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ))) P = _
      rw [hqc, hqc]
      rw [hP ⟨(U : Matrix (Fin N) (Fin N) ℂ) * q Z * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ, by rw [htr, trace_q]⟩
          ⟨(U : Matrix (Fin N) (Fin N) ℂ) * q W * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ, by rw [htr, trace_q]⟩,
        hP ⟨q Z, trace_q Z⟩ ⟨q W, trace_q W⟩]
      exact hfU ⟨q Z, trace_q Z⟩ ⟨q W, trace_q W⟩
    let unflat : (V → ℂ) →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ := { toFun := fun z i j => z (i,j), map_add' := by intros; rfl, map_smul' := by intros; rfl }
    let TT := flat.comp (T.comp unflat)
    have hTT (Z W : V → ℂ) : eval (fun v : Bool × V => if v.1 then TT W v.2 else TT Z v.2) (Q P) =
          eval (fun v => if v.1 then W v.2 else Z v.2) (Q P) := by
      exact hT (unflat Z) (unflat W)
    have huf (Z : Matrix (Fin N) (Fin N) ℂ) : unflat (flat Z) = Z := rfl
    change G (fun j => flat (T (x j))) = G (fun j => flat (x j))
    have hi := hInv TT hTT (fun j => flat (x j))
    change G (fun j => flat (T (unflat (flat (x j))))) = G (fun j => flat (x j)) at hi; simpa only [huf] using hi
#print axioms trace_kernel_function_polarization
end D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization
