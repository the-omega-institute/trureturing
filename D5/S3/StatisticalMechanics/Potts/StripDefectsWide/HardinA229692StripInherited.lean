/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripInherited
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692StripInherited
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/HardinA229692Strip.finite_certificate
   digest: Exact two-defect width-six HA transfer. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229692Strip.result)
oldForward: proof_shape=bind-only; consumers=old_prefix, leading_table, old_relation
old_prefix: proof_shape=bind-only; consumers=leading_table
leading_table: proof_shape=bind-only; consumers=leading_step, inherited_polynomial
leading_mul: proof_shape=bind-only; consumers=leading_step
leading_step: proof_shape=bind-only; consumers=inherited_step
copy_columns: proof_shape=bind-only; consumers=inherited_step
copy_table: proof_shape=bind-only; consumers=inherited_step, inherited_polynomial
old_relation: proof_shape=bind-only; consumers=inherited_polynomial
inherited_step: proof_shape=bind-only; consumers=step
step: proof_shape=bind-only; consumers=HardinA229692StripForward.step0 through HardinA229692StripForward.step10
inherited_polynomial: proof_shape=bind-only; consumers=polynomial
polynomial: proof_shape=bind-only; consumers=HardinA229692StripForward.forward_certificate
-/

import Mathlib.Data.Matrix.Block
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584Strip
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripInherited
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229692StripData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private def oldForward (n : ℕ) : Fin 32 → ℤ :=
  DefectTransfer.forward HardinA229584StripData.T HardinA229584StripData.initial n

private theorem old_prefix (i : Fin 8) : oldForward i.val = HardinA229584StripData.W i := by
  exact HardinA229584Strip.powers_table i

private theorem leading_table (i : Fin 12) :
    (fun j : Fin 32 => W i (j.castAdd 36)) = oldForward i.val := by
  induction i using Fin.addCases (m := 8) (n := 4) with
  | left i =>
    simpa only [W, Fin.append_left, Fin.val_castAdd] using (old_prefix i).symm
  | right i =>
    simp only [W, Fin.append_right, Fin.append_left, Fin.val_natAdd]
    rw [← show oldForward 7 = HardinA229584StripData.W 7 from old_prefix ⟨7, by omega⟩]
    simp only [oldForward, DefectTransfer.forward, ← Function.iterate_add_apply]
    simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private theorem leading_mul (v : Fin 68 → ℤ) (j : Fin 32) :
    Matrix.vecMul v T (j.castAdd 36) =
      Matrix.vecMul (fun k : Fin 32 => v (k.castAdd 36)) HardinA229584StripData.T j := by
  have block_leading (A : Matrix (Fin 32) (Fin 32) ℤ)
      (B : Matrix (Fin 32) (Fin 36) ℤ) (D : Matrix (Fin 36) (Fin 36) ℤ) :
      Matrix.vecMul v (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A B (0 : Matrix (Fin 36) (Fin 32) ℤ) D)) (j.castAdd 36) =
        Matrix.vecMul (fun k : Fin 32 => v (k.castAdd 36)) A j := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_vecMul_equiv, Matrix.vecMul_fromBlocks]
    simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd,
      Sum.elim_inl, Matrix.vecMul_zero, add_zero, Equiv.symm_symm]
    rfl
  exact block_leading _ _ _

private theorem leading_step (i : Fin 11) (j : Fin 32) :
    W i.succ (j.castAdd 36) = Matrix.vecMul (W i.castSucc) T (j.castAdd 36) := by
  rw [leading_mul]
  have h : (fun j : Fin 32 => W i.succ (j.castAdd 36)) =
      Matrix.vecMul (fun j : Fin 32 => W i.castSucc (j.castAdd 36))
        HardinA229584StripData.T := by
    rw [leading_table, leading_table]
    simp only [oldForward, DefectTransfer.forward, Fin.val_succ, Fin.val_castSucc,
      Function.iterate_succ_apply']
  exact congrFun h j

private theorem copy_columns : ∀ (r : Fin 68) (k : Fin 10),
    T r (![39, 43, 48, 52, 58, 61, 62, 63, 66, 67] k) =
      T r ((![14, 17, 25, 27, 8, 10, 12, 20, 22, 30] k : Fin 32).castAdd 36) := by
  decide +kernel

private theorem copy_table (i : Fin 12) (k : Fin 10) :
    W i (![39, 43, 48, 52, 58, 61, 62, 63, 66, 67] k) =
      W i ((![14, 17, 25, 27, 8, 10, 12, 20, 22, 30] k : Fin 32).castAdd 36) := by
  fin_cases i <;> fin_cases k <;> rfl

/-- The leading block and its repeated columns advance by the frozen owner. -/
private theorem inherited_step (i : Fin 11) (j : Fin 68)
    (hj : j.val < 32 ∨ j.val = 39 ∨ j.val = 43 ∨ j.val = 48 ∨ j.val = 52 ∨
      j.val = 58 ∨ j.val = 61 ∨ j.val = 62 ∨ j.val = 63 ∨ j.val = 66 ∨ j.val = 67) :
    W i.succ j = Matrix.vecMul (W i.castSucc) T j := by
  rcases hj with hj | hj
  · exact leading_step i ⟨j.val, hj⟩
  · have hcopy (k : Fin 10) :
        W i.succ (![39, 43, 48, 52, 58, 61, 62, 63, 66, 67] k) =
          Matrix.vecMul (W i.castSucc) T (![39, 43, 48, 52, 58, 61, 62, 63, 66, 67] k) := by
      rw [copy_table]
      rw [leading_step]
      unfold Matrix.vecMul dotProduct
      simp_rw [copy_columns]
    rcases hj with h | h | h | h | h | h | h | h | h | h
    · have he : j = 39 := Fin.ext h
      subst j
      exact hcopy 0
    · have he : j = 43 := Fin.ext h
      subst j
      exact hcopy 1
    · have he : j = 48 := Fin.ext h
      subst j
      exact hcopy 2
    · have he : j = 52 := Fin.ext h
      subst j
      exact hcopy 3
    · have he : j = 58 := Fin.ext h
      subst j
      exact hcopy 4
    · have he : j = 61 := Fin.ext h
      subst j
      exact hcopy 5
    · have he : j = 62 := Fin.ext h
      subst j
      exact hcopy 6
    · have he : j = 63 := Fin.ext h
      subst j
      exact hcopy 7
    · have he : j = 66 := Fin.ext h
      subst j
      exact hcopy 8
    · have he : j = 67 := Fin.ext h
      subst j
      exact hcopy 9

private theorem old_relation (n : ℕ) : oldForward (n + 7) =
    ∑ j : Fin 6, (![-6561, 14580, -12150, 4662, -805, 50] j : ℤ) •
      oldForward (n + 1 + j.val) := by
  have hh := congrArg (fun v => Matrix.vecMul v (HardinA229584StripData.T ^ n))
    HardinA229584Strip.polynomial_relation
  simp only [oldForward, DefectTransfer.forward_eq, Matrix.sum_vecMul,
    Matrix.smul_vecMul, Matrix.vecMul_vecMul, ← pow_add] at hh
  simpa only [oldForward, DefectTransfer.forward_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh

/-- The inherited polynomial is the frozen degree-six relation times the cubic factor. -/
private theorem inherited_polynomial (j : Fin 68)
    (hj : j.val < 32 ∨ j.val = 39 ∨ j.val = 43 ∨ j.val = 48 ∨ j.val = 52 ∨
      j.val = 58 ∨ j.val = 61 ∨ j.val = 62 ∨ j.val = 63 ∨ j.val = 66 ∨ j.val = 67) :
    W 11 j = (∑ k : Fin 9,
      (![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] k : ℤ) •
        W ⟨2 + k.val, by omega⟩) j := by
  have leading (j : Fin 32) : W 11 (j.castAdd 36) = (∑ k : Fin 9,
      (![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] k : ℤ) •
        W ⟨2 + k.val, by omega⟩) (j.castAdd 36) := by
    have table (i : Fin 12) : W i (j.castAdd 36) = oldForward i.val j :=
      congrFun (leading_table i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, table]
    have h1 := congrFun (old_relation 1) j
    have h2 := congrFun (old_relation 2) j
    have h3 := congrFun (old_relation 3) j
    have h4 := congrFun (old_relation 4) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ,
      Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.val_one, Fin.val_ofNat, Nat.reduceAdd, mul_zero, add_zero] at h1 h2 h3 h4 ⊢
    change oldForward 11 j = _
    linarith only [h1, h2, h3, h4]
  rcases hj with hj | hj
  · exact leading ⟨j.val, hj⟩
  · have hcopy (k : Fin 10) : W 11 (![39, 43, 48, 52, 58, 61, 62, 63, 66, 67] k) =
        (∑ l : Fin 9,
          (![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] l : ℤ) •
            W ⟨2 + l.val, by omega⟩) (![39, 43, 48, 52, 58, 61, 62, 63, 66, 67] k) := by
      simpa only [Finset.sum_apply, Pi.smul_apply, copy_table] using
        leading (![14, 17, 25, 27, 8, 10, 12, 20, 22, 30] k)
    rcases hj with h | h | h | h | h | h | h | h | h | h
    · have he : j = 39 := Fin.ext h
      subst j
      exact hcopy 0
    · have he : j = 43 := Fin.ext h
      subst j
      exact hcopy 1
    · have he : j = 48 := Fin.ext h
      subst j
      exact hcopy 2
    · have he : j = 52 := Fin.ext h
      subst j
      exact hcopy 3
    · have he : j = 58 := Fin.ext h
      subst j
      exact hcopy 4
    · have he : j = 61 := Fin.ext h
      subst j
      exact hcopy 5
    · have he : j = 62 := Fin.ext h
      subst j
      exact hcopy 6
    · have he : j = 63 := Fin.ext h
      subst j
      exact hcopy 7
    · have he : j = 66 := Fin.ext h
      subst j
      exact hcopy 8
    · have he : j = 67 := Fin.ext h
      subst j
      exact hcopy 9

/-- Assemble an old-owner step with the restricted new-coordinate certificate. -/
theorem step (i : Fin 11)
    (new_coordinates : ∀ j : Fin 36, ¬ (j.val = 7 ∨ j.val = 11 ∨ j.val = 16 ∨ j.val = 20 ∨ j.val = 26 ∨ j.val = 29 ∨ j.val = 30 ∨ j.val = 31 ∨ j.val = 34 ∨ j.val = 35) →
      W i.succ (j.natAdd 32) = Matrix.vecMul (W i.castSucc) T (j.natAdd 32)) :
    W i.succ = Matrix.vecMul (W i.castSucc) T := by
  funext j
  fin_cases j
  · exact inherited_step i 0 (by omega)
  · exact inherited_step i 1 (by omega)
  · exact inherited_step i 2 (by omega)
  · exact inherited_step i 3 (by omega)
  · exact inherited_step i 4 (by omega)
  · exact inherited_step i 5 (by omega)
  · exact inherited_step i 6 (by omega)
  · exact inherited_step i 7 (by omega)
  · exact inherited_step i 8 (by omega)
  · exact inherited_step i 9 (by omega)
  · exact inherited_step i 10 (by omega)
  · exact inherited_step i 11 (by omega)
  · exact inherited_step i 12 (by omega)
  · exact inherited_step i 13 (by omega)
  · exact inherited_step i 14 (by omega)
  · exact inherited_step i 15 (by omega)
  · exact inherited_step i 16 (by omega)
  · exact inherited_step i 17 (by omega)
  · exact inherited_step i 18 (by omega)
  · exact inherited_step i 19 (by omega)
  · exact inherited_step i 20 (by omega)
  · exact inherited_step i 21 (by omega)
  · exact inherited_step i 22 (by omega)
  · exact inherited_step i 23 (by omega)
  · exact inherited_step i 24 (by omega)
  · exact inherited_step i 25 (by omega)
  · exact inherited_step i 26 (by omega)
  · exact inherited_step i 27 (by omega)
  · exact inherited_step i 28 (by omega)
  · exact inherited_step i 29 (by omega)
  · exact inherited_step i 30 (by omega)
  · exact inherited_step i 31 (by omega)
  · exact new_coordinates 0 (by decide +kernel)
  · exact new_coordinates 1 (by decide +kernel)
  · exact new_coordinates 2 (by decide +kernel)
  · exact new_coordinates 3 (by decide +kernel)
  · exact new_coordinates 4 (by decide +kernel)
  · exact new_coordinates 5 (by decide +kernel)
  · exact new_coordinates 6 (by decide +kernel)
  · exact inherited_step i 39 (by omega)
  · exact new_coordinates 8 (by decide +kernel)
  · exact new_coordinates 9 (by decide +kernel)
  · exact new_coordinates 10 (by decide +kernel)
  · exact inherited_step i 43 (by omega)
  · exact new_coordinates 12 (by decide +kernel)
  · exact new_coordinates 13 (by decide +kernel)
  · exact new_coordinates 14 (by decide +kernel)
  · exact new_coordinates 15 (by decide +kernel)
  · exact inherited_step i 48 (by omega)
  · exact new_coordinates 17 (by decide +kernel)
  · exact new_coordinates 18 (by decide +kernel)
  · exact new_coordinates 19 (by decide +kernel)
  · exact inherited_step i 52 (by omega)
  · exact new_coordinates 21 (by decide +kernel)
  · exact new_coordinates 22 (by decide +kernel)
  · exact new_coordinates 23 (by decide +kernel)
  · exact new_coordinates 24 (by decide +kernel)
  · exact new_coordinates 25 (by decide +kernel)
  · exact inherited_step i 58 (by omega)
  · exact new_coordinates 27 (by decide +kernel)
  · exact new_coordinates 28 (by decide +kernel)
  · exact inherited_step i 61 (by omega)
  · exact inherited_step i 62 (by omega)
  · exact inherited_step i 63 (by omega)
  · exact new_coordinates 32 (by decide +kernel)
  · exact new_coordinates 33 (by decide +kernel)
  · exact inherited_step i 66 (by omega)
  · exact inherited_step i 67 (by omega)

/-- Assemble the transported polynomial with its new-coordinate certificate. -/
theorem polynomial
    (new_coordinates : ∀ j : Fin 36, ¬ (j.val = 7 ∨ j.val = 11 ∨ j.val = 16 ∨ j.val = 20 ∨ j.val = 26 ∨ j.val = 29 ∨ j.val = 30 ∨ j.val = 31 ∨ j.val = 34 ∨ j.val = 35) →
      W 11 (j.natAdd 32) = (∑ k : Fin 9,
        (![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] k : ℤ) •
          W ⟨2 + k.val, by omega⟩) (j.natAdd 32)) :
    W 11 = ∑ k : Fin 9,
      (![531441, -1771470, 2460375, -1842183, 803115, -205200, 29368, -2145, 75] k : ℤ) •
        W ⟨2 + k.val, by omega⟩ := by
  funext j
  fin_cases j
  · exact inherited_polynomial 0 (by omega)
  · exact inherited_polynomial 1 (by omega)
  · exact inherited_polynomial 2 (by omega)
  · exact inherited_polynomial 3 (by omega)
  · exact inherited_polynomial 4 (by omega)
  · exact inherited_polynomial 5 (by omega)
  · exact inherited_polynomial 6 (by omega)
  · exact inherited_polynomial 7 (by omega)
  · exact inherited_polynomial 8 (by omega)
  · exact inherited_polynomial 9 (by omega)
  · exact inherited_polynomial 10 (by omega)
  · exact inherited_polynomial 11 (by omega)
  · exact inherited_polynomial 12 (by omega)
  · exact inherited_polynomial 13 (by omega)
  · exact inherited_polynomial 14 (by omega)
  · exact inherited_polynomial 15 (by omega)
  · exact inherited_polynomial 16 (by omega)
  · exact inherited_polynomial 17 (by omega)
  · exact inherited_polynomial 18 (by omega)
  · exact inherited_polynomial 19 (by omega)
  · exact inherited_polynomial 20 (by omega)
  · exact inherited_polynomial 21 (by omega)
  · exact inherited_polynomial 22 (by omega)
  · exact inherited_polynomial 23 (by omega)
  · exact inherited_polynomial 24 (by omega)
  · exact inherited_polynomial 25 (by omega)
  · exact inherited_polynomial 26 (by omega)
  · exact inherited_polynomial 27 (by omega)
  · exact inherited_polynomial 28 (by omega)
  · exact inherited_polynomial 29 (by omega)
  · exact inherited_polynomial 30 (by omega)
  · exact inherited_polynomial 31 (by omega)
  · exact new_coordinates 0 (by decide +kernel)
  · exact new_coordinates 1 (by decide +kernel)
  · exact new_coordinates 2 (by decide +kernel)
  · exact new_coordinates 3 (by decide +kernel)
  · exact new_coordinates 4 (by decide +kernel)
  · exact new_coordinates 5 (by decide +kernel)
  · exact new_coordinates 6 (by decide +kernel)
  · exact inherited_polynomial 39 (by omega)
  · exact new_coordinates 8 (by decide +kernel)
  · exact new_coordinates 9 (by decide +kernel)
  · exact new_coordinates 10 (by decide +kernel)
  · exact inherited_polynomial 43 (by omega)
  · exact new_coordinates 12 (by decide +kernel)
  · exact new_coordinates 13 (by decide +kernel)
  · exact new_coordinates 14 (by decide +kernel)
  · exact new_coordinates 15 (by decide +kernel)
  · exact inherited_polynomial 48 (by omega)
  · exact new_coordinates 17 (by decide +kernel)
  · exact new_coordinates 18 (by decide +kernel)
  · exact new_coordinates 19 (by decide +kernel)
  · exact inherited_polynomial 52 (by omega)
  · exact new_coordinates 21 (by decide +kernel)
  · exact new_coordinates 22 (by decide +kernel)
  · exact new_coordinates 23 (by decide +kernel)
  · exact new_coordinates 24 (by decide +kernel)
  · exact new_coordinates 25 (by decide +kernel)
  · exact inherited_polynomial 58 (by omega)
  · exact new_coordinates 27 (by decide +kernel)
  · exact new_coordinates 28 (by decide +kernel)
  · exact inherited_polynomial 61 (by omega)
  · exact inherited_polynomial 62 (by omega)
  · exact inherited_polynomial 63 (by omega)
  · exact new_coordinates 32 (by decide +kernel)
  · exact new_coordinates 33 (by decide +kernel)
  · exact inherited_polynomial 66 (by omega)
  · exact inherited_polynomial 67 (by omega)

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.HardinA229692StripInherited
