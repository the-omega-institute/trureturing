/- SOURCE ONLY. Arbitrary cache, arbitrary query; no fixed cache validity.
   A query checks only the recursive dependency cone of its requested minor.
   Its success premise is paid at a current-spectrum inequality use. -/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SixRowNumericRecurrence
open scoped BigOperators

inductive Table (α : Type) where
  | leaf (key : α) (value : ℤ)
  | node (pivot : ℕ) (left right : Table α)

def code {k : ℕ} (e : Fin k → Fin 22) : ℕ :=
  ∑ i, (e i).val * 22 ^ i.val

def lookup {k : ℕ} (t : Table (Fin k → Fin 22))
    (e : Fin k → Fin 22) : Option ℤ :=
  match t with
  | .leaf a v => if e = a then some v else none
  | .node p l r => if code e < p then lookup l e else lookup r e

abbrev Cache := (k : Fin 7) → Table (Fin k.val → Fin 22)

noncomputable def minorDet (B : Matrix (Fin 6) (Fin 22) ℤ)
    (k : ℕ) (hk : k ≤ 6) (e : Fin k → Fin 22) : ℤ :=
  (B.submatrix (fun i : Fin k => ⟨6-k+i.val, by omega⟩) e).det

theorem minorDet_zero (B : Matrix (Fin 6) (Fin 22) ℤ)
    (e : Fin 0 → Fin 22) : minorDet B 0 (by omega) e = 1 := by
  simp [minorDet]

theorem minorDet_succ (B : Matrix (Fin 6) (Fin 22) ℤ)
    (k : ℕ) (hk : k+1 ≤ 6) (e : Fin (k+1) → Fin 22) :
    minorDet B (k+1) hk e =
      ∑ j : Fin (k+1), (-1 : ℤ)^j.val *
        B ⟨6-(k+1), by omega⟩ (e j) *
        minorDet B k (by omega) (fun q => e (j.succAbove q)) := by
  classical
  unfold minorDet
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hm :
      (B.submatrix (fun i : Fin (k+1) => ⟨6-(k+1)+i.val, by omega⟩) e).submatrix
        Fin.succ j.succAbove =
      B.submatrix (fun i : Fin k => ⟨6-k+i.val, by omega⟩)
        (fun q => e (j.succAbove q)) := by
    funext i q
    change B ⟨6-(k+1)+(i.val+1), by omega⟩ (e (j.succAbove q)) =
      B ⟨6-k+i.val, by omega⟩ (e (j.succAbove q))
    congr 1
    apply Fin.ext
    have hi : i.val < k := i.isLt
    have hk' : k < 6 := by omega
    change 6 - (k + 1) + (i.val + 1) = 6 - k + i.val
    omega
  rw [hm]
  simp only [Matrix.submatrix_apply, Fin.val_zero, Nat.zero_add, Nat.add_zero]

/- Values and routing are untrusted. Neither a correct table nor a positive
   all-table check is a premise or a conclusion of the query theorem. -/
def query (B : Matrix (Fin 6) (Fin 22) ℤ) (cache : Cache) :
    (k : ℕ) → (hk : k ≤ 6) → (Fin k → Fin 22) → Option ℤ
  | 0, _, e => if lookup (cache 0) e = some 1 then some 1 else none
  | k+1, hk, e =>
      let children := fun j : Fin (k+1) =>
        query B cache k (by omega) (fun q => e (j.succAbove q))
      let value := (lookup (cache ⟨k+1, by omega⟩) e).getD 0
      if (lookup (cache ⟨k+1, by omega⟩) e).isSome = true ∧
          (∀ j, (children j).isSome = true) ∧
          value = ∑ j : Fin (k+1), (-1 : ℤ)^j.val *
            B ⟨6-(k+1), by omega⟩ (e j) * (children j).getD 0
      then some value else none

theorem some_getD (o : Option ℤ) (h : o.isSome = true) :
    o = some (o.getD 0) := by
  cases o <;> simp_all

theorem query_sound (B : Matrix (Fin 6) (Fin 22) ℤ) (cache : Cache)
    (k : ℕ) (hk : k ≤ 6) (e : Fin k → Fin 22) (v : ℤ)
    (hq : query B cache k hk e = some v) : minorDet B k hk e = v := by
  revert hk e v
  induction k with
  | zero =>
      intro hk e v hq
      dsimp only [query] at hq
      split_ifs at hq with h
      · cases Option.some.inj hq
        exact minorDet_zero B e
  | succ k ih =>
      intro hk e v hq
      dsimp only [query] at hq
      split_ifs at hq with h
      · have hv := Option.some.inj hq
        rw [minorDet_succ]
        calc
          _ = ∑ j : Fin (k+1), (-1 : ℤ)^j.val *
              B ⟨6-(k+1), by omega⟩ (e j) *
              (query B cache k (by omega)
                (fun q => e (j.succAbove q))).getD 0 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [ih (by omega) _ _ (some_getD _ (h.2.1 j))]
          _ = (lookup (cache ⟨k+1, by omega⟩) e).getD 0 := h.2.2.symm
          _ = v := hv

end D5.S3.Quantum.Entanglement.AbsolutePPT.SixRowNumericRecurrence
