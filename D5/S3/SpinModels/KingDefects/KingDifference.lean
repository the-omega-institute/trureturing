/- GID: D5/S3/SpinModels/KingDefects/KingDifference
   generality: G
   mirror-B: D5/B/S3/SpinModels/KingDefects/KingDifference
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Klein-valued discrete integration and rainbow-block rigidity on rectangles. -/
/-
admission_basis: escape-witness
escape_witness: integrate_v (propagation of a cocycle along an arbitrary row),
  integrationEquiv (root and difference field reconstruct a unique colouring).
The finite Klein identities support uniform structural theorems; no bounded
colouring enumeration or numerical instance is asserted.
-/
import D5.S3.SpinModels.KingDefects.KingGrid
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace D5.S3.SpinModels.KingDefects.KingDifference

open KingGrid

abbrev K := ZMod 2 × ZMod 2

noncomputable def colourEquiv : Fin 4 ≃ K :=
  Fintype.equivOfCardEq (by simp [K])

private theorem neg_self (a : K) : -a = a := by
  ext <;> exact ZMod.neg_eq_self_mod_two _

@[simp] private theorem self_add (a : K) : a + a = 0 := by
  rw [← neg_self a, neg_add_cancel]

@[simp] private theorem add_add_cancel (a b : K) : a + (a + b) = b := by
  rw [← add_assoc, self_add, zero_add]

@[simp] private theorem add_eq_zero (a b : K) : a + b = 0 ↔ a = b := by
  rw [← neg_self b, add_neg_eq_zero]

structure DiffField (N M : ℕ) where
  h : Fin (N+1) → Fin M → K
  v : Fin N → Fin (M+1) → K

/-- The two paths across every elementary square have equal differences. -/
def Cocycle {N M : ℕ} (s : DiffField N M) : Prop :=
  ∀ i j, s.h i.castSucc j + s.v i j.succ =
    s.v i j.castSucc + s.h i.succ j

def differentiate {N M : ℕ} (f : Cell (N+1) (M+1) → K) : DiffField N M where
  h i j := f (i,j.castSucc) + f (i,j.succ)
  v i j := f (i.castSucc,j) + f (i.succ,j)

theorem differentiate_cocycle {N M : ℕ} (f : Cell (N+1) (M+1) → K) :
    Cocycle (differentiate f) := by
  intro i j
  dsimp [differentiate]
  have reorder (a b c d : K) : (a+b)+(b+d) = (a+c)+(c+d) := by
    simp [add_assoc, ← add_assoc b b, ← add_assoc c c]
  exact reorder _ _ _ _

def integrate {N M : ℕ} (t : K) (s : DiffField N M) : Cell (N+1) (M+1) → K :=
  fun p => t + Fin.partialSum (fun i => s.v i 0) p.1 + Fin.partialSum (s.h p.1) p.2

theorem integrate_root {N M : ℕ} (t : K) (s : DiffField N M) :
    integrate t s (0,0) = t := by simp [integrate]

theorem integrate_h {N M : ℕ} (t : K) (s : DiffField N M)
    (i : Fin (N+1)) (j : Fin M) :
    (differentiate (integrate t s)).h i j = s.h i j := by
  dsimp [differentiate, integrate]
  rw [Fin.partialSum_succ]
  simp [add_assoc, ← add_assoc (t + Fin.partialSum (fun i => s.v i 0) i)
    (t + Fin.partialSum (fun i => s.v i 0) i)]

theorem integrate_v {N M : ℕ} (t : K) (s : DiffField N M) (hs : Cocycle s)
    (i : Fin N) (j : Fin (M+1)) :
    (differentiate (integrate t s)).v i j = s.v i j := by
  induction j using Fin.inductionOn with
  | zero =>
    dsimp [differentiate, integrate]
    rw [Fin.partialSum_succ]
    simp [add_assoc, add_left_comm, add_comm]
  | succ j ih =>
    have hc := hs i j
    have hd : (differentiate (integrate t s)).v i j.succ =
        (differentiate (integrate t s)).v i j.castSucc +
          (s.h i.castSucc j + s.h i.succ j) := by
      dsimp [differentiate, integrate]
      rw [Fin.partialSum_succ, Fin.partialSum_succ]
      abel
    rw [hd, ih]
    have hc' := congrArg (fun z => s.h i.castSucc j + z) hc
    simpa [add_assoc, add_left_comm, add_comm] using hc'.symm

theorem differentiate_integrate {N M : ℕ} (t : K) (s : DiffField N M)
    (hs : Cocycle s) : differentiate (integrate t s) = s := by
  apply DiffField.ext
  · funext i j
    exact integrate_h t s i j
  · funext i j
    exact integrate_v t s hs i j

theorem integrate_differentiate {N M : ℕ} (f : Cell (N+1) (M+1) → K) :
    integrate (f (0,0)) (differentiate f) = f := by
  funext p
  obtain ⟨i,j⟩ := p
  induction i using Fin.inductionOn with
  | zero =>
    induction j using Fin.inductionOn with
    | zero => simp [integrate]
    | succ j ih =>
      dsimp [integrate, differentiate] at ih ⊢
      rw [Fin.partialSum_succ]
      simpa [add_assoc] using congrArg (fun z => z +
        (f (0,j.castSucc) + f (0,j.succ))) ih
  | succ i ih =>
    have hbase : integrate (f (0,0)) (differentiate f) (i.succ,0) = f (i.succ,0) := by
      have hprev := congrFun (funext (fun j => ih j)) (0 : Fin (M+1))
      dsimp [integrate, differentiate] at hprev ⊢
      rw [Fin.partialSum_succ]
      simpa [add_assoc] using congrArg (fun z => z +
        (f (i.castSucc,0) + f (i.succ,0))) hprev
    induction j using Fin.inductionOn with
    | zero => exact hbase
    | succ j ihj =>
      dsimp [integrate, differentiate] at ihj ⊢
      rw [Fin.partialSum_succ]
      simpa [add_assoc] using congrArg (fun z => z +
        (f (i.succ,j.castSucc) + f (i.succ,j.succ))) ihj

/-- No defect restriction is needed for discrete integration. -/
def integrationEquiv (N M : ℕ) :
    (Cell (N+1) (M+1) → K) ≃ K × {s : DiffField N M // Cocycle s} where
  toFun f := (f (0,0), ⟨differentiate f, differentiate_cocycle f⟩)
  invFun q := integrate q.1 q.2.val
  left_inv := integrate_differentiate
  right_inv q := by
    apply Prod.ext (integrate_root _ _)
    exact Subtype.ext (differentiate_integrate _ _ q.2.property)

end D5.S3.SpinModels.KingDefects.KingDifference
