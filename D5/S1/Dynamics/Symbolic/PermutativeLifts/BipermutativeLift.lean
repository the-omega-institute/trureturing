/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-sourcePrefix fibres of two-sided bipermutative block codes. -/

import Mathlib.Algebra.Group.End
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast

/-! Actual finite-prefix permutations, two-sided reconstruction and full-lift conjugacy. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift

open Function
open SymbolicDynamics.FullShift

variable {A : Type*} {k : ℕ}

/-- The literal length-`k+1` sourcePrefix, rather than the group of its permutations. -/
abbrev Prefix (A : Type*) (k : ℕ) := Fin (k + 1) → A

/-- A block code of length `k+2` is bijective in either end letter. -/
structure Bipermutative (h : (Fin (k + 2) → A) → A) : Prop where
  right : ∀ u : Prefix A k, Bijective (fun b : A => h (Fin.snoc u b))
  left : ∀ v : Prefix A k, Bijective (fun a : A => h (Fin.cons a v))

variable {h : (Fin (k + 2) → A) → A}

noncomputable def rightEquiv (bh : Bipermutative h) (u : Prefix A k) : A ≃ A :=
  Equiv.ofBijective (fun b => h (Fin.snoc u b)) (bh.right u)

/-- The uniquely reconstructed right endpoint for the prescribed output letter. -/
noncomputable def rightLetter (bh : Bipermutative h) (a : A) (u : Prefix A k) : A :=
  (rightEquiv bh u).symm a

private theorem right_letter_spec (bh : Bipermutative h) (a : A) (u : Prefix A k) :
    h (Fin.snoc u (rightLetter bh a u)) = a :=
  (rightEquiv bh u).apply_symm_apply a

/-- Moving a sourcePrefix one step to the right in the actual fibre. -/
noncomputable def prefixStep (bh : Bipermutative h) (a : A) (u : Prefix A k) :
    Prefix A k :=
  Fin.snoc (Fin.tail u) (rightLetter bh a u)

private theorem cons_prefix_step (bh : Bipermutative h) (a : A) (u : Prefix A k) :
    Fin.cons (α := fun _ => A) (u 0) (prefixStep bh a u) =
      Fin.snoc (α := fun _ => A) u (rightLetter bh a u) := by
  simp only [prefixStep, Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]

private theorem code_prefix_step (bh : Bipermutative h) (a : A) (u : Prefix A k) :
    h (Fin.cons (u 0) (prefixStep bh a u)) = a := by
  rw [cons_prefix_step bh a u, right_letter_spec bh a u]

private theorem prefix_step_injective (bh : Bipermutative h) (a : A) :
    Injective (prefixStep bh a) := by
  intro u v huv
  have hzero : u 0 = v 0 := by
    apply (bh.left (prefixStep bh a v)).injective
    have hu : h (Fin.cons (u 0) (prefixStep bh a v)) = a := by
      simpa only [huv] using code_prefix_step bh a u
    exact hu.trans (code_prefix_step bh a v).symm
  have htail : Fin.tail u = Fin.tail v := by
    have hi := congrArg Fin.init huv
    simpa only [prefixStep, Fin.init_snoc] using hi
  rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v, hzero, htail]

/-- Every output letter acts by a permutation on `A^(k+1)` itself. -/
noncomputable def prefixPerm [Finite A] (bh : Bipermutative h) (a : A) :
    Equiv.Perm (Prefix A k) :=
  Equiv.ofBijective (prefixStep bh a)
    ⟨prefix_step_injective bh a, Finite.surjective_of_injective (prefix_step_injective bh a)⟩

private theorem prefix_perm_apply [Finite A] (bh : Bipermutative h) (a : A)
    (u : Prefix A k) : prefixPerm bh a u = prefixStep bh a u := rfl

private theorem prefix_perm_overlap [Finite A] (bh : Bipermutative h) (a : A)
    (u : Prefix A k) (j : Fin k) :
    prefixPerm bh a u j.castSucc = u j.succ := by
  simp only [prefix_perm_apply, prefixStep, Fin.snoc_castSucc, Fin.tail]

/-- A length-`k+2` physical window at an integer position. -/
def window (x : ℤ → A) (i : ℤ) : Fin (k + 2) → A :=
  fun j => x (i + (j : ℕ))

/-- The actual sliding block code on the two-sided full shift. -/
def code (h : (Fin (k + 2) → A) → A) (x : ℤ → A) : ℤ → A :=
  fun i => h (window x i)

def sourcePrefix (x : ℤ → A) : Prefix A k := fun j => x (j : ℕ)

private theorem window_eq_snoc (x : ℤ → A) (i : ℤ) :
    window (k := k) x i =
      Fin.snoc (fun j : Fin (k + 1) => x (i + (j : ℕ))) (x (i + (k + 1 : ℕ))) := by
  ext j
  cases j using Fin.lastCases <;> simp [window]

theorem code_shift (x : ℤ → A) (i : ℤ) :
    code h (shift i x) = shift i (code h x) := by
  ext j
  change h (window (shift i x) j) = h (window x (i + j))
  apply congrArg h
  funext t
  simp only [window, shift_apply, add_assoc]

private theorem prefix_step_code (bh : Bipermutative h) (x : ℤ → A) :
    prefixStep bh (code h x 0) (sourcePrefix x) = sourcePrefix (shift 1 x) := by
  have hlast : rightLetter bh (code h x 0) (sourcePrefix x) = x (k + 1 : ℕ) := by
    unfold rightLetter
    apply (rightEquiv bh (sourcePrefix x)).symm_apply_eq.mpr
    change code h x 0 = h (Fin.snoc (sourcePrefix x) (x (k + 1 : ℕ)))
    simp only [code, window_eq_snoc, zero_add]
    rfl
  ext j
  cases j using Fin.lastCases with
  | last => simp [prefixStep, hlast, sourcePrefix, shift, Nat.cast_add, add_comm]
  | cast j => simp [prefixStep, sourcePrefix, shift, Fin.tail, Nat.cast_add, add_comm]

/-- The whole finite extension; its fibre is the sourcePrefix set. -/
noncomputable def skewPerm [Finite A] (bh : Bipermutative h) :
    Equiv.Perm ((ℤ → A) × Prefix A k) where
  toFun z := (shift 1 z.1, prefixPerm bh (z.1 0) z.2)
  invFun z := (shift (-1) z.1, (prefixPerm bh (z.1 (-1))).symm z.2)
  left_inv z := by
    apply Prod.ext
    · ext i
      simp [shift]
    · simp [shift]
  right_inv z := by
    apply Prod.ext
    · ext i
      simp [shift]
    · simp [shift]

def coordinates (h : (Fin (k + 2) → A) → A) (x : ℤ → A) :
    (ℤ → A) × Prefix A k := (code h x, sourcePrefix x)

private theorem coordinates_shift [Finite A] (bh : Bipermutative h) (x : ℤ → A) :
    coordinates h (shift 1 x) = skewPerm bh (coordinates h x) := by
  apply Prod.ext
  · exact code_shift (h := h) x 1
  · exact (prefix_step_code bh x).symm

section Reconstruction

variable [Finite A] (bh : Bipermutative h)

/-- Integer iterates provide both future and past reconstruction, using only
the actual sourcePrefix permutation. -/
noncomputable def orbit (z : (ℤ → A) × Prefix A k) (i : ℤ) :
    (ℤ → A) × Prefix A k := (skewPerm bh ^ i) z

@[simp] private theorem orbit_zero (z : (ℤ → A) × Prefix A k) : orbit bh z 0 = z := by
  simp [orbit]

private theorem orbit_succ (z : (ℤ → A) × Prefix A k) (i : ℤ) :
    orbit bh z (i + 1) = skewPerm bh (orbit bh z i) := by
  rw [orbit, show i + 1 = 1 + i by omega, zpow_one_add, Equiv.Perm.mul_apply]
  rfl

private theorem orbit_pred (z : (ℤ → A) × Prefix A k) (i : ℤ) :
    orbit bh z (i - 1) = (skewPerm bh).symm (orbit bh z i) := by
  apply (skewPerm bh).injective
  simpa using (orbit_succ bh z (i - 1)).symm

private theorem orbit_base (z : (ℤ → A) × Prefix A k) (i : ℤ) :
    (orbit bh z i).1 = shift i z.1 := by
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [orbit_succ]
    change shift 1 (orbit bh z (n : ℤ)).1 = _
    rw [ih]
    ext j
    simp only [shift_apply, sub_eq_add_neg, add_left_comm, add_comm]
  | pred n ih =>
    rw [orbit_pred]
    change shift (-1) (orbit bh z (-(n : ℤ))).1 = _
    rw [ih]
    ext j
    simp only [shift_apply, sub_eq_add_neg, add_left_comm, add_comm]

private theorem orbit_overlap (z : (ℤ → A) × Prefix A k) (i : ℤ) (j : Fin k) :
    (orbit bh z (i + 1)).2 j.castSucc = (orbit bh z i).2 j.succ := by
  rw [orbit_succ]
  exact prefix_perm_overlap bh _ _ j

/-- Reading the first symbol of every reconstructed sourcePrefix gives a physical
two-sided source sequence. -/
noncomputable def reconstruct (z : (ℤ → A) × Prefix A k) : ℤ → A :=
  fun i => (orbit bh z i).2 0

private theorem orbit_coordinate (z : (ℤ → A) × Prefix A k) (j : ℕ)
    (hj : j < k + 1) (i : ℤ) :
    (orbit bh z i).2 ⟨j, hj⟩ = reconstruct bh z (i + (j : ℤ)) := by
  induction j generalizing i with
  | zero => simp [reconstruct]
  | succ j ih =>
    have hjk : j < k := by omega
    have hlow : j < k + 1 := by omega
    calc
      (orbit bh z i).2 ⟨j + 1, hj⟩ =
          (orbit bh z (i + 1)).2 ⟨j, hlow⟩ :=
        (orbit_overlap bh z i ⟨j, hjk⟩).symm
      _ = reconstruct bh z ((i + 1) + (j : ℤ)) := ih hlow (i + 1)
      _ = reconstruct bh z (i + ((j + 1 : ℕ) : ℤ)) := by
        congr 1
        push_cast
        omega

private theorem reconstruct_prefix_at (z : (ℤ → A) × Prefix A k) (i : ℤ) :
    (fun j : Fin (k + 1) => reconstruct bh z (i + (j : ℕ))) =
      (orbit bh z i).2 := by
  ext j
  exact (orbit_coordinate bh z (j : ℕ) j.isLt i).symm

private theorem reconstruct_window (z : (ℤ → A) × Prefix A k) (i : ℤ) :
    window (reconstruct bh z) i =
      Fin.cons ((orbit bh z i).2 0) (orbit bh z (i + 1)).2 := by
  ext j
  cases j using Fin.cases with
  | zero => simp [window, reconstruct]
  | succ j =>
    simp only [window, Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    rw [orbit_coordinate bh z (j : ℕ) j.isLt (i + 1)]
    congr 1
    omega

private theorem code_reconstruct (z : (ℤ → A) × Prefix A k) :
    code h (reconstruct bh z) = z.1 := by
  ext i
  change h (window (reconstruct bh z) i) = z.1 i
  rw [reconstruct_window, orbit_succ]
  change h (Fin.cons ((orbit bh z i).2 0)
    (prefixStep bh ((orbit bh z i).1 0) (orbit bh z i).2)) = _
  rw [code_prefix_step bh ((orbit bh z i).1 0) (orbit bh z i).2]
  simpa only [shift_apply, add_zero] using congrFun (orbit_base bh z i) 0

private theorem source_prefix_reconstruct (z : (ℤ → A) × Prefix A k) :
    sourcePrefix (reconstruct bh z) = z.2 := by
  change (fun j : Fin (k + 1) => reconstruct bh z (j : ℕ)) = z.2
  simpa only [zero_add, orbit_zero] using reconstruct_prefix_at bh z 0

private theorem coordinates_reconstruct (z : (ℤ → A) × Prefix A k) :
    coordinates h (reconstruct bh z) = z := by
  apply Prod.ext
  · exact code_reconstruct bh z
  · change sourcePrefix (reconstruct bh z) = z.2
    exact source_prefix_reconstruct bh z

private theorem coordinates_shift_back (x : ℤ → A) :
    coordinates h (shift (-1) x) = (skewPerm bh).symm (coordinates h x) := by
  apply (skewPerm bh).injective
  rw [Equiv.apply_symm_apply, ← coordinates_shift]
  congr 1
  ext i
  simp [shift]

private theorem orbit_coordinates (x : ℤ → A) (i : ℤ) :
    orbit bh (coordinates h x) i = coordinates h (shift i x) := by
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [orbit_succ, ih, ← coordinates_shift]
    congr 1
    ext j
    simp only [shift_apply, sub_eq_add_neg, add_left_comm, add_comm]
  | pred n ih =>
    rw [orbit_pred, ih, ← coordinates_shift_back]
    congr 1
    ext j
    simp only [shift_apply, sub_eq_add_neg, add_left_comm, add_comm]

private theorem reconstruct_coordinates (x : ℤ → A) :
    reconstruct bh (coordinates h x) = x := by
  ext i
  change (orbit bh (coordinates h x) i).2 0 = x i
  rw [orbit_coordinates]
  change x (i + 0) = x i
  exact congrArg x (add_zero i)

/-- Every output configuration and every literal sourcePrefix have exactly one
two-sided source. Both endpoint permutations are used in this equivalence. -/
noncomputable def fullShiftEquiv : (ℤ → A) ≃ ((ℤ → A) × Prefix A k) where
  toFun := coordinates h
  invFun := reconstruct bh
  left_inv := reconstruct_coordinates bh
  right_inv := coordinates_reconstruct bh

end Reconstruction

section Topology

variable [Finite A] [TopologicalSpace A] [DiscreteTopology A]

private theorem continuous_code (h : (Fin (k + 2) → A) → A) : Continuous (code h) := by
  apply continuous_pi
  intro i
  exact (continuous_of_discreteTopology : Continuous h).comp
    (continuous_pi fun j => continuous_apply (i + (j : ℕ)))

private theorem continuous_prefix : Continuous (sourcePrefix (A := A) (k := k)) := by
  apply continuous_pi
  intro j
  change Continuous (fun x : ℤ → A => x ((j : ℕ) : ℤ))
  exact continuous_apply ((j : ℕ) : ℤ)

private theorem continuous_coordinates (h : (Fin (k + 2) → A) → A) :
    Continuous (coordinates h) :=
  (continuous_code h).prodMk continuous_prefix

/-- A genuine homeomorphism on the entire full shift and its full sourcePrefix fibre. -/
noncomputable def fullShiftHomeomorph (bh : Bipermutative h) :
    (ℤ → A) ≃ₜ ((ℤ → A) × Prefix A k) :=
  Continuous.homeoOfEquivCompactToT2 (f := fullShiftEquiv bh) (continuous_coordinates h)

/-- The entire inverse image, with no choice of component. -/
abbrev LiftPoint (h : (Fin (k + 2) → A) → A) (Y : Subshift A ℤ) :=
  {x : ℤ → A // code h x ∈ Y.carrier}

noncomputable def fullLiftEquiv (bh : Bipermutative h) (Y : Subshift A ℤ) :
    LiftPoint h Y ≃ (Y.carrier × Prefix A k) where
  toFun x := (⟨code h x.1, x.2⟩, sourcePrefix x.1)
  invFun z := ⟨reconstruct bh (z.1.1, z.2), by
    rw [code_reconstruct]
    exact z.1.2⟩
  left_inv x := Subtype.ext (reconstruct_coordinates bh x.1)
  right_inv z := by
    apply Prod.ext
    · exact Subtype.ext (code_reconstruct bh (z.1.1, z.2))
    · change sourcePrefix (reconstruct bh (z.1.1, z.2)) = z.2
      exact source_prefix_reconstruct bh (z.1.1, z.2)

noncomputable def fullLiftHomeomorph (bh : Bipermutative h) (Y : Subshift A ℤ) :
    LiftPoint h Y ≃ₜ (Y.carrier × Prefix A k) where
  toEquiv := fullLiftEquiv bh Y
  continuous_toFun :=
    (((continuous_code h).comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_prefix.comp continuous_subtype_val)
  continuous_invFun :=
    by
      have hc : Continuous (reconstruct bh) := (fullShiftHomeomorph bh).symm.continuous
      exact (hc.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

def baseShift (Y : Subshift A ℤ) (y : Y.carrier) : Y.carrier :=
  ⟨shift 1 y.1, Y.mapsTo 1 y.2⟩

/-- The entire inverse image is invariant under every integer shift. -/
def integerShift (Y : Subshift A ℤ) (g : ℤ) (x : LiftPoint h Y) : LiftPoint h Y :=
  ⟨shift g x.1, by
    rw [code_shift (h := h) x.1 g]
    exact Y.mapsTo g x.2⟩

theorem integerShift_add (Y : Subshift A ℤ) (g j : ℤ) (x : LiftPoint h Y) :
    integerShift Y (g + j) x = integerShift Y g (integerShift Y j x) := by
  apply Subtype.ext
  funext i
  simp [integerShift, shift, add_assoc, add_comm g j]

instance integerShiftAction (h : (Fin (k + 2) → A) → A) (Y : Subshift A ℤ) :
    AddAction ℤ (LiftPoint h Y) where
  vadd := integerShift Y
  zero_vadd x := by
    apply Subtype.ext
    funext i
    change x.1 (0 + i) = x.1 i
    rw [zero_add]
  add_vadd := integerShift_add Y

def liftShift (Y : Subshift A ℤ) (x : LiftPoint h Y) : LiftPoint h Y :=
  integerShift Y 1 x

noncomputable def skewStep (bh : Bipermutative h) (Y : Subshift A ℤ)
    (z : Y.carrier × Prefix A k) : Y.carrier × Prefix A k :=
  (baseShift Y z.1, prefixPerm bh (z.1.1 0) z.2)

/-- Kang--Jaeger full-lift conjugacy on the literal `A^(k+1)` fibre,
derived from both endpoint permutations and two-sided reconstruction. -/
theorem full_lift_conjugacy (bh : Bipermutative h) (Y : Subshift A ℤ)
    (x : LiftPoint h Y) :
    fullLiftHomeomorph bh Y (liftShift Y x) =
      skewStep bh Y (fullLiftHomeomorph bh Y x) := by
  apply Prod.ext
  · exact Subtype.ext (code_shift (h := h) x.1 1)
  · exact (prefix_step_code bh x.1).symm

end Topology

end D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativeLift
