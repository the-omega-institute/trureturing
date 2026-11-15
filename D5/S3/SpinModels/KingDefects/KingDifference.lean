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
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Algebra.BigOperators.Fin

/-! Discrete derivatives, exact integration and local rainbow rigidity. -/
namespace D5.S3.SpinModels.KingDefects.KingDifference

open KingGrid

abbrev K := ZMod 2 × ZMod 2

noncomputable def colourEquiv : Fin 4 ≃ K :=
  Fintype.equivOfCardEq (by simp [K])

private theorem neg_self (a : K) : -a = a := by
  exact IsAddKleinFour.neg_eq_self a

@[simp] private theorem self_add (a : K) : a + a = 0 := by
  exact IsAddKleinFour.add_self a

@[simp] private theorem add_add_cancel (a b : K) : a + (a + b) = b := by
  rw [← add_assoc, self_add, zero_add]

@[simp] private theorem add_eq_zero (a b : K) : a + b = 0 ↔ a = b := by
  simpa only [neg_self] using (add_eq_zero_iff_eq_neg (a := a) (b := b))

@[ext] structure DiffField (N M : ℕ) where
  h : Fin (N+1) → Fin M → K
  v : Fin N → Fin (M+1) → K
  deriving DecidableEq, Fintype

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
  simpa only [add_assoc] using add_add_cancel
    (t + Fin.partialSum (fun i => s.v i 0) i + Fin.partialSum (s.h i) j.castSucc) (s.h i j)

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
      simp only [Fin.partialSum_succ]
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

theorem difference_unique {N M : ℕ} (f g : Cell (N+1) (M+1) → K)
    (hr : f (0,0) = g (0,0)) (hd : differentiate f = differentiate g) : f = g := by
  have base (i : Fin (N+1)) : f (i,0) = g (i,0) := by
    induction i using Fin.inductionOn with
    | zero => exact hr
    | succ i ih =>
      have hv := congrFun (congrFun (congrArg DiffField.v hd) i) 0
      change f (i.castSucc,0) + f (i.succ,0) = g (i.castSucc,0) + g (i.succ,0) at hv
      rw [ih] at hv
      exact add_left_cancel hv
  funext p
  obtain ⟨i,j⟩ := p
  induction j using Fin.inductionOn with
  | zero => exact base i
  | succ j ih =>
    have hh := congrFun (congrFun (congrArg DiffField.h hd) i) j
    change f (i,j.castSucc) + f (i,j.succ) = g (i,j.castSucc) + g (i,j.succ) at hh
    rw [ih] at hh
    exact add_left_cancel hh

theorem integrate_differentiate {N M : ℕ} (f : Cell (N+1) (M+1) → K) :
    integrate (f (0,0)) (differentiate f) = f :=
  difference_unique _ _ (integrate_root _ _)
    (differentiate_integrate _ _ (differentiate_cocycle f))

/-- No defect restriction is needed for discrete integration. -/
def integrationEquiv (N M : ℕ) :
    (Cell (N+1) (M+1) → K) ≃ K × {s : DiffField N M // Cocycle s} where
  toFun f := (f (0,0), ⟨differentiate f, differentiate_cocycle f⟩)
  invFun q := integrate q.1 q.2.val
  left_inv := integrate_differentiate
  right_inv q := by
    apply Prod.ext (integrate_root _ _)
    exact Subtype.ext (differentiate_integrate _ _ q.2.property)


def edgeValue {N M : ℕ} (s : DiffField N M) : Edge (N+1) (M+1) → K
  | .H i j => s.h i j
  | .V i j => s.v i j
  | .D i j => s.h i.castSucc j + s.v i j.succ
  | .A i j => s.h i.castSucc j + s.v i j.castSucc

def RawAdmissible {N M : ℕ} (e : Edge (N+1) (M+1)) (s : DiffField N M) : Prop :=
  Cocycle s ∧ ∀ d, edgeValue s d = 0 ↔ d = e

theorem differentiate_edgeValue {N M : ℕ} (f : Cell (N+1) (M+1) → K)
    (e : Edge (N+1) (M+1)) :
    edgeValue (differentiate f) e = f (end0 e) + f (end1 e) := by
  cases e with
  | H i j => rfl
  | V i j => rfl
  | D i j =>
    change (f (i.castSucc,j.castSucc) + f (i.castSucc,j.succ)) +
      (f (i.castSucc,j.succ) + f (i.succ,j.succ)) = _
    simp [add_assoc]
    rfl
  | A i j =>
    change (f (i.castSucc,j.castSucc) + f (i.castSucc,j.succ)) +
      (f (i.castSucc,j.castSucc) + f (i.succ,j.castSucc)) = _
    simp [add_assoc, add_left_comm, add_comm]
    rfl

theorem raw_differentiate_iff {N M : ℕ} (f : Cell (N+1) (M+1) → K)
    (e : Edge (N+1) (M+1)) :
    RawAdmissible e (differentiate f) ↔ DefectAt e f := by
  simp only [RawAdmissible, differentiate_cocycle, true_and,
    differentiate_edgeValue, add_eq_zero, DefectAt, mono]

def defectIntegrationEquiv {N M : ℕ} (e : Edge (N+1) (M+1)) :
    {f : Cell (N+1) (M+1) → K // DefectAt e f} ≃
      K × {s : DiffField N M // RawAdmissible e s} where
  toFun f := (f.val (0,0), ⟨differentiate f.val,
    (raw_differentiate_iff f.val e).mpr f.property⟩)
  invFun q := ⟨integrate q.1 q.2.val, by
    apply (raw_differentiate_iff _ e).mp
    rw [differentiate_integrate _ _ q.2.property.1]
    exact q.2.property⟩
  left_inv f := Subtype.ext (integrate_differentiate f.val)
  right_inv q := by
    apply Prod.ext (integrate_root _ _)
    exact Subtype.ext (differentiate_integrate _ _ q.2.property.1)

/-- The field alone parametrizes colourings whose root colour is zero. -/
def rootZeroEquiv {N M : ℕ} (e : Edge (N+1) (M+1)) :
    {f : Cell (N+1) (M+1) → K // DefectAt e f ∧ f (0,0) = 0} ≃
      {s : DiffField N M // RawAdmissible e s} where
  toFun f := ⟨differentiate f.val, (raw_differentiate_iff f.val e).mpr f.property.1⟩
  invFun s := ⟨integrate 0 s.val,
    (defectIntegrationEquiv e).symm (0,s) |>.property, integrate_root _ _⟩
  left_inv f := by
    apply Subtype.ext
    simpa only [f.property.2] using integrate_differentiate f.val
  right_inv s := Subtype.ext (differentiate_integrate _ _ s.property.1)

noncomputable def N_e {N M : ℕ} (e : Edge (N+1) (M+1)) : ℕ :=
  Nat.card {s : DiffField N M // RawAdmissible e s}

private noncomputable def relabelDefectEquiv {n k : ℕ} (e : Edge n k) :
    {f : Cell n k → Fin 4 // DefectAt e f} ≃
      {f : Cell n k → K // DefectAt e f} where
  toFun f := ⟨colourEquiv ∘ f.val, by
    intro d
    simpa only [mono, Function.comp_apply, colourEquiv.injective.eq_iff] using f.property d⟩
  invFun f := ⟨colourEquiv.symm ∘ f.val, by
    intro d
    simpa only [mono, Function.comp_apply, colourEquiv.symm.injective.eq_iff] using f.property d⟩
  left_inv f := by apply Subtype.ext; funext p; exact colourEquiv.symm_apply_apply _
  right_inv f := by apply Subtype.ext; funext p; exact colourEquiv.apply_symm_apply _

theorem count_fixed_edge {N M : ℕ} (e : Edge (N+1) (M+1)) :
    Nat.card {f : Cell (N+1) (M+1) → Fin 4 // DefectAt e f} = 4 * N_e e := by
  rw [Nat.card_congr (relabelDefectEquiv e),
    Nat.card_congr (defectIntegrationEquiv e), Nat.card_prod]
  simp [K, N_e, Nat.card_eq_fintype_card]

theorem count_from_fields (N M : ℕ) :
    L (N+1) (M+1) = 4 * ∑ e : Edge (N+1) (M+1), N_e e := by
  rw [count_by_edge]
  simp_rw [count_fixed_edge]
  exact (Finset.mul_sum ..).symm

/-- The six pairs of the four vertices of a square. -/
def Rainbow (a b c d : K) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

private theorem rainbow_algebra (a b c d : K) :
    Rainbow a b c d ↔
      a+b = c+d ∧ a+c = b+d ∧ a+b ≠ 0 ∧ a+c ≠ 0 ∧ a+b ≠ a+c := by
  unfold Rainbow
  revert a b c d
  decide +kernel

/-- Rainbow squares have constant opposite slots and distinct nonzero directions. -/
theorem rainbow_block {N M : ℕ} (f : Cell (N+1) (M+1) → K)
    (i : Fin N) (j : Fin M) :
    Rainbow (f (i.castSucc,j.castSucc)) (f (i.castSucc,j.succ))
      (f (i.succ,j.castSucc)) (f (i.succ,j.succ)) ↔
      (differentiate f).h i.castSucc j = (differentiate f).h i.succ j ∧
      (differentiate f).v i j.castSucc = (differentiate f).v i j.succ ∧
      (differentiate f).h i.castSucc j ≠ 0 ∧
      (differentiate f).v i j.castSucc ≠ 0 ∧
      (differentiate f).h i.castSucc j ≠ (differentiate f).v i j.castSucc := by
  exact rainbow_algebra _ _ _ _

#print axioms defectIntegrationEquiv
#print axioms count_from_fields
#print axioms rainbow_block

end D5.S3.SpinModels.KingDefects.KingDifference

