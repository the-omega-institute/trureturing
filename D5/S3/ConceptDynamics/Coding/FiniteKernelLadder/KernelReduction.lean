/- GID: D5/S3/ConceptDynamics/Coding/FiniteKernelLadder/KernelReduction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FiniteKernelLadder/KernelReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual kernel quotients, lag stabilization and original-power kernel invariants. -/

import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import D5.S3.ConceptDynamics.Coding.UnitWordGyration
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FreeModule.PID
import D5.S3.ConceptDynamics.Coding.CountedLocalizedGyrationResidue
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LinearMap.End

/- Cohosted KernelRSSquare support. -/
/-
Wagoner, Proc. AMS 109 (1990), pp. 529–531, (2.2),(2.5),(2.7).
The OCR diagram is NOT a premise: all arrows below are constructed.
Mathlib pin db584cd6d46c92f209a44c0f1c829460d327499d.

This module uses COLUMN linear maps. Its companion takes their actual
matrix transposes before consuming the existing ROW cochain.
No freeness, nonzero dimension or injectivity hypothesis is used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SourceOnly.KernelRSSquare

universe u v w
variable {L : Type u} [CommRing L]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]

abbrev KQuot (f : V →ₗ[L] W) := V ⧸ LinearMap.ker f

def project (f : V →ₗ[L] W) : V →ₗ[L] KQuot f :=
  (LinearMap.ker f).mkQ

/-- The actual map induced by f, with codomain the original module. -/
def factor (f : V →ₗ[L] W) : KQuot f →ₗ[L] W :=
  (LinearMap.ker f).liftQ f le_rfl

@[simp] theorem factor_project (f : V →ₗ[L] W) :
    (factor f).comp (project f) = f := by
  ext x
  rfl

/-- The elementary SSE (project f,factor f) has endpoints f and its
actual induced endomorphism. This does not discard a nilpotent summand. -/
def reduced (f : Module.End L V) : Module.End L (KQuot f) :=
  (project f).comp (factor f)

variable (r : V →ₗ[L] W) (s : W →ₗ[L] V)

abbrev P : Module.End L V := s.comp r
abbrev Q : Module.End L W := r.comp s

/-- The extra center in the RS square is V/ker r, not V/ker P. -/
def centerToLeft : KQuot r →ₗ[L] KQuot (P r s) :=
  (LinearMap.ker r).liftQ (project (P r s)) (by
    intro x hx
    change project (P r s) x = 0
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.ker (P r s))).mpr
    change s (r x) = 0
    change r x = 0 at hx
    rw [hx, map_zero])

def centerReturn : KQuot (Q r s) →ₗ[L] KQuot r :=
  (LinearMap.ker (Q r s)).liftQ ((project r).comp s) (by
    intro y hy
    change project r (s y) = 0
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.ker r)).mpr
    exact hy)

/-- The forward and backward arrows on BOTH kernel quotients. -/
def bottomForward : KQuot (P r s) →ₗ[L] KQuot (Q r s) :=
  (LinearMap.ker (P r s)).liftQ ((project (Q r s)).comp r) (by
    intro x hx
    change project (Q r s) (r x) = 0
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.ker (Q r s))).mpr
    change r (s (r x)) = 0
    change s (r x) = 0 at hx
    rw [hx, map_zero])

def bottomBackward : KQuot (Q r s) →ₗ[L] KQuot (P r s) :=
  (LinearMap.ker (Q r s)).liftQ ((project (P r s)).comp s) (by
    intro y hy
    change project (P r s) (s y) = 0
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.ker (P r s))).mpr
    change s (r (s y)) = 0
    change r (s y) = 0 at hy
    rw [hy, map_zero])

/- The following equalities are precisely the factor equations of four
actual RS triangles. They are stronger than the SE commutative square. -/

@[simp] theorem centerToLeft_project :
    (centerToLeft r s).comp (project r) = project (P r s) := by
  ext x
  rfl

theorem left_factorization :
    (factor (P r s)).comp (centerToLeft r s) = s.comp (factor r) := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.ker r).mkQ_surjective z
  rfl

@[simp] theorem centerReturn_project :
    (centerReturn r s).comp (project (Q r s)) = (project r).comp s := by
  ext y
  rfl

theorem right_factorization :
    (factor r).comp (centerReturn r s) = factor (Q r s) := by
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := (LinearMap.ker (Q r s)).mkQ_surjective z
  rfl

theorem lower_left_factorization :
    (centerReturn r s).comp (bottomForward r s) =
      (project r).comp (factor (P r s)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.ker (P r s)).mkQ_surjective z
  rfl

theorem lower_right_factorization :
    (centerToLeft r s).comp (centerReturn r s) = bottomBackward r s := by
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := (LinearMap.ker (Q r s)).mkQ_surjective z
  rfl

theorem diagonal_factorization :
    (bottomForward r s).comp (centerToLeft r s) =
      (project (Q r s)).comp (factor r) := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.ker r).mkQ_surjective z
  rfl

/-- Freeness is proved, not postulated: V/ker f is the range of f, a
submodule of a based finite free module over the PID. Fin 0 is allowed.
The input basis of V is deliberately unnecessary for this construction. -/
def quotientBasis [IsDomain L] [IsPrincipalIdealRing L]
    {n : ℕ} (bW : Module.Basis (Fin n) L W) (f : V →ₗ[L] W) :
    Σ m : ℕ, Module.Basis (Fin m) L (KQuot f) := by
  let br := Submodule.basisOfPid bW (LinearMap.range f)
  exact ⟨br.1, br.2.map f.quotKerEquivRange.symm⟩

end SourceOnly.KernelRSSquare

end -- close this source block's anonymous noncomputable section

/- Cohosted KernelRSSquareGyration support. -/
/- This consumes the same dyadicGyration
from the completed rectangular supplier, not a cochain defined from gamma.
The four RS triangles use one fixed basis per vertex of the square.
No conjugacy-invariance or zero basis-change value is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SourceOnly.KernelRSSquareGyration

open D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open SourceOnly.KernelRSSquare

universe u v w z
variable {L : Type u} [CommRing L]
variable {U : Type z} {V : Type v} {W : Type w}
variable [AddCommGroup U] [Module L U]
variable [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]

/-- Explicit COLUMN-to-ROW conversion, for arbitrary rectangular sizes. -/
def rows {n m : ℕ} (bV : Module.Basis (Fin n) L V)
    (bW : Module.Basis (Fin m) L W) (f : V →ₗ[L] W) :
    Matrix (Fin n) (Fin m) L := (LinearMap.toMatrix bV bW f).transpose

theorem rows_comp {n m p : ℕ}
    (bU : Module.Basis (Fin n) L U) (bV : Module.Basis (Fin m) L V)
    (bW : Module.Basis (Fin p) L W) (f : U →ₗ[L] V) (g : V →ₗ[L] W) :
    rows bU bW (g.comp f) = rows bU bV f * rows bV bW g := by
  unfold rows
  rw [LinearMap.toMatrix_comp bU bV bW, Matrix.transpose_mul]

section Dyadic
variable {X : Type*} {Y : Type*} {Z : Type*}
variable [AddCommGroup X] [Module GyrationDyadic X]
variable [AddCommGroup Y] [Module GyrationDyadic Y]
variable [AddCommGroup Z] [Module GyrationDyadic Z]
variable {d : ℕ} [NeZero d]

def value {n m : ℕ} (bX : Module.Basis (Fin n) GyrationDyadic X)
    (bY : Module.Basis (Fin m) GyrationDyadic Y)
    (r : X →ₗ[GyrationDyadic] Y) (s : Y →ₗ[GyrationDyadic] X) : ZMod 3 :=
  dyadicGyration d (rows bX bY r) (rows bY bX s)

/-- Actual finite-free quotient coordinates over Z[1/2]. The PID proof
extends each ideal from its contraction to Z. This avoids an unproved
typeclass assumption at the dyadic application. The input f may be zero. -/
def dyadicQuotientBasis {m : ℕ}
    (bY : Module.Basis (Fin m) GyrationDyadic Y)
    (f : X →ₗ[GyrationDyadic] Y) :
    Σ n : ℕ, Module.Basis (Fin n) GyrationDyadic (KQuot f) := by
  letI : IsDomain GyrationDyadic :=
    Localization.Away.isDomain (by decide : (2 : ℤ) ≠ 0)
  letI : IsPrincipalIdealRing GyrationDyadic := {
    principal := fun J => by
      exact (IsLocalization.map_under (Submonoid.powers (2 : ℤ)) GyrationDyadic J) ▸
        (inferInstance : (Ideal.map (algebraMap ℤ GyrationDyadic) (J.under ℤ)).IsPrincipal) }
  exact quotientBasis bY f

set_option maxHeartbeats 1000000 in
theorem value_triangle (hd : 3 ∣ d) {n m p : ℕ}
    (bX : Module.Basis (Fin n) GyrationDyadic X)
    (bY : Module.Basis (Fin m) GyrationDyadic Y)
    (bZ : Module.Basis (Fin p) GyrationDyadic Z)
    (r : X →ₗ[GyrationDyadic] Y) (u : Y →ₗ[GyrationDyadic] Z)
    (v : Z →ₗ[GyrationDyadic] X) :
    value (d := d) bX bY r (v.comp u) +
      value (d := d) bY bZ u (r.comp v) =
      value (d := d) bX bZ (u.comp r) v := by
  let e : ℕ := padicValInt 3 (((2 * d).factorial : ℕ) : ℤ)
  unfold value
  rw [rows_comp, rows_comp, rows_comp]
  exact canonicalLocalizedGyration_triangle hd e le_rfl (gyrationDyadicReduction d)
      (rows bX bY r) (rows bY bZ u) (rows bZ bX v)

/-- Full cochain conservation across Wagoner's kernel square. The two
vertical terms remain explicit. The source and target may both be singular.
Any chosen finite bases work provided each square vertex uses its same
basis in every incident triangle. All dimensions, including zero, occur. -/
theorem kernel_square (hd : 3 ∣ d)
    {n m c a b : ℕ} (r : X →ₗ[GyrationDyadic] Y)
    (s : Y →ₗ[GyrationDyadic] X)
    (bX : Module.Basis (Fin n) GyrationDyadic X)
    (bY : Module.Basis (Fin m) GyrationDyadic Y)
    (bC : Module.Basis (Fin c) GyrationDyadic (KQuot r))
    (bA : Module.Basis (Fin a) GyrationDyadic (KQuot (P r s)))
    (bB : Module.Basis (Fin b) GyrationDyadic (KQuot (Q r s))) :
    value (d := d) bX bY r s +
      value (d := d) bY bB (project (Q r s)) (factor (Q r s)) =
    value (d := d) bX bA (project (P r s)) (factor (P r s)) +
      value (d := d) bA bB (bottomForward r s) (bottomBackward r s) := by
  have h₁ := value_triangle (d := d) hd bX bC bY
    (project r) (factor r) s
  rw [factor_project] at h₁
  have h₂ := value_triangle (d := d) hd bX bC bA
    (project r) (centerToLeft r s) (factor (P r s))
  rw [left_factorization, centerToLeft_project] at h₂
  have h₃ := value_triangle (d := d) hd bC bY bB
    (factor r) (project (Q r s)) (centerReturn r s)
  rw [centerReturn_project, right_factorization] at h₃
  have h₄ := value_triangle (d := d) hd bC bA bB
    (centerToLeft r s) (bottomForward r s) (centerReturn r s)
  rw [lower_left_factorization, lower_right_factorization,
    diagonal_factorization] at h₄
  rw [← h₁, add_assoc, h₃, ← h₄, ← add_assoc, h₂]

end Dyadic
end SourceOnly.KernelRSSquareGyration

end -- close this source block's anonymous noncomputable section

/- Cohosted UnitLagReduction support. -/
/- Algebraic unit-endpoint simplification.
All powers and lag equations concern the ACTUAL maps. No inverse of the
possibly singular B is used in the kernel statements. No finite-rank,
PID, field-of-fractions or nonzero-dimension assumption occurs here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SourceOnly.UnitLagReduction

universe u v w
variable {L : Type u} [CommRing L]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]

theorem unit_apply_inv (a : (Module.End L V)ˣ) (x : V) :
    (a : Module.End L V) ((↑a⁻¹ : Module.End L V) x) = x :=
  congrArg (fun z : Module.End L V => z x) (Units.mul_inv a)

theorem unit_inv_apply (a : (Module.End L V)ˣ) (x : V) :
    (↑a⁻¹ : Module.End L V) ((a : Module.End L V) x) = x :=
  congrArg (fun z : Module.End L V => z x) (Units.inv_mul a)

theorem unit_injective (a : (Module.End L V)ˣ) :
    Function.Injective (a : Module.End L V) := by
  intro x y h
  have h' := congrArg (↑a⁻¹ : Module.End L V) h
  simpa only [unit_inv_apply] using h'

theorem intertwine_pow (A : Module.End L V) (B : Module.End L W)
    (g : W →ₗ[L] V) (h : g.comp B = A.comp g) (n : ℕ) (x : W) :
    g ((B ^ n) x) = (A ^ n) (g x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        g ((B ^ (n+1)) x) = g (B ((B^n) x)) := by
          rw [pow_succ', Module.End.mul_apply]
        _ = A (g ((B^n) x)) :=
          congrArg (fun z : W →ₗ[L] V => z ((B^n) x)) h
        _ = A ((A^n) (g x)) := by rw [ih]
        _ = (A^(n+1)) (g x) := by rw [pow_succ', Module.End.mul_apply]

/-- The left lag identity makes f injective without any assumption on B. -/
theorem lag_forward_injective (a : (Module.End L V)ˣ)
    (f : V →ₗ[L] W) (g : W →ₗ[L] V) (k : ℕ)
    (hgf : g.comp f = (a : Module.End L V)^k) : Function.Injective f := by
  intro x y hxy
  apply unit_injective (a^k)
  change ((a : Module.End L V)^k) x = ((a : Module.End L V)^k) y
  rw [← hgf]
  exact congrArg g hxy

/-- g is surjective by an explicit preimage f(a^(-k)x). -/
theorem lag_return_surjective (a : (Module.End L V)ˣ)
    (f : V →ₗ[L] W) (g : W →ₗ[L] V) (k : ℕ)
    (hgf : g.comp f = (a : Module.End L V)^k) : Function.Surjective g := by
  intro x
  refine ⟨f ((↑((a^k)⁻¹) : Module.End L V) x), ?_⟩
  calc
    g (f ((↑((a^k)⁻¹) : Module.End L V) x)) =
        ((a : Module.End L V)^k) ((↑((a^k)⁻¹) : Module.End L V) x) :=
      congrArg (fun z : V →ₗ[L] V => z ((↑((a^k)⁻¹) : Module.End L V) x)) hgf
    _ = x := unit_apply_inv (a^k) x

/-- Exact eventual kernel: the nilpotent part is ker g, not assumed zero.
The proof uses both lag products; singular B is fully retained. -/
theorem lag_kernel (a : (Module.End L V)ˣ) (B : Module.End L W)
    (f : V →ₗ[L] W) (g : W →ₗ[L] V) (k : ℕ)
    (hgf : g.comp f = (a : Module.End L V)^k)
    (hfg : f.comp g = B^k) : LinearMap.ker (B^k) = LinearMap.ker g := by
  ext x
  change (B^k) x = 0 ↔ g x = 0
  rw [← hfg]
  change f (g x) = 0 ↔ g x = 0
  constructor
  · intro hx
    exact lag_forward_injective a f g k hgf (hx.trans (map_zero f).symm)
  · intro hx
    rw [hx, map_zero]

/-- A finite explicit bound replaces an appeal to eventual stabilization.
Once n=k+q, every kernel is exactly the lag kernel. -/
theorem lag_kernel_after (a : (Module.End L V)ˣ) (B : Module.End L W)
    (f : V →ₗ[L] W) (g : W →ₗ[L] V) (k q : ℕ)
    (hgf : g.comp f = (a : Module.End L V)^k)
    (hfg : f.comp g = B^k)
    (hgB : g.comp B = (a : Module.End L V).comp g) :
    LinearMap.ker (B^(k+q)) = LinearMap.ker (B^k) := by
  rw [lag_kernel a B f g k hgf hfg]
  ext x
  change (B^(k+q)) x = 0 ↔ g x = 0
  constructor
  · intro hx
    apply unit_injective (a^(k+q))
    change ((a : Module.End L V)^(k+q)) (g x) =
      ((a : Module.End L V)^(k+q)) 0
    rw [← intertwine_pow (a : Module.End L V) B g hgB, hx, map_zero, map_zero]
  · intro hx
    have hk : (B^k) x = 0 := by
      rw [← hfg]
      change f (g x) = 0
      rw [hx, map_zero]
    rw [Nat.add_comm k q, pow_add, Module.End.mul_apply, hk, map_zero]

/-- The actual endomorphism on W/ker(B^k), not the original B with its
nilpotent part silently omitted. -/
def powerQuotientEnd (B : Module.End L W) (k : ℕ) :
    Module.End L (W ⧸ LinearMap.ker (B^k)) :=
  (LinearMap.ker (B^k)).mapQ (LinearMap.ker (B^k)) B (by
    intro x hx
    change (B^k) (B x) = 0
    have hc : (B^k) (B x) = B ((B^k) x) :=
      congrArg (fun z : Module.End L W => z x) (Commute.self_pow B k).eq.symm
    rw [hc]
    change (B^k) x = 0 at hx
    rw [hx, map_zero])

/-- The lag bound proves injectivity of the quotient dynamics. This is
the exact algebraic termination condition needed by a finite kernel ladder. -/
theorem powerQuotientEnd_injective
    (a : (Module.End L V)ˣ) (B : Module.End L W)
    (f : V →ₗ[L] W) (g : W →ₗ[L] V) (k : ℕ)
    (hgf : g.comp f = (a : Module.End L V)^k)
    (hfg : f.comp g = B^k)
    (hgB : g.comp B = (a : Module.End L V).comp g) :
    Function.Injective (powerQuotientEnd B k) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := (LinearMap.ker (B^k)).mkQ_surjective z
    change (LinearMap.ker (B^k)).mkQ (B x) = 0 at hz
    have hx : (B^k) (B x) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.ker (B^k))).mp hz
    have hx' : x ∈ LinearMap.ker (B^(k+1)) := by
      change (B^(k+1)) x = 0
      rw [pow_succ, Module.End.mul_apply]
      exact hx
    rw [lag_kernel_after a B f g k 1 hgf hfg hgB] at hx'
    change (LinearMap.ker (B^k)).mkQ x = 0
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.ker (B^k))).mpr hx'
  · exact bot_le

/-- If B has already been made injective by the kernel construction,
the actual lag equations force it to be a unit. Injective over a PID alone
would NOT imply this conclusion (multiplication by 2 is a counterexample).
Only gB=ag is needed in addition to the two lag products. -/
def unitFromLag (a : (Module.End L V)ˣ) (B : Module.End L W)
    (f : V →ₗ[L] W) (g : W →ₗ[L] V) (k : ℕ)
    (hgf : g.comp f = (a : Module.End L V)^k)
    (hfg : f.comp g = B^k)
    (hgB : g.comp B = (a : Module.End L V).comp g)
    (hB : Function.Injective B) : (Module.End L W)ˣ := by
  have hp : ∀ j : ℕ, Function.Injective (B^j) := by
    intro j
    induction j with
    | zero => exact Function.injective_id
    | succ j ih =>
        rw [pow_succ', Module.End.mul_eq_comp]
        exact hB.comp ih
  have hg : Function.Injective g := by
    intro x y hxy
    apply hp k
    rw [← hfg]
    exact congrArg f hxy
  let e : W ≃ₗ[L] V := LinearEquiv.ofBijective g
    ⟨hg, lag_return_surjective a f g k hgf⟩
  have hb (x : W) : g (B x) = (a : Module.End L V) (g x) :=
    congrArg (fun z : W →ₗ[L] V => z x) hgB
  refine {
    val := B
    inv := e.symm.toLinearMap.comp ((↑a⁻¹ : Module.End L V).comp e.toLinearMap)
    val_inv := ?_
    inv_val := ?_ }
  · ext x
    apply e.injective
    change g (B (e.symm ((↑a⁻¹ : Module.End L V) (e x)))) = g x
    rw [hb]
    change (a : Module.End L V)
      (e (e.symm ((↑a⁻¹ : Module.End L V) (e x)))) = e x
    rw [e.apply_symm_apply]
    exact unit_apply_inv a (e x)
  · ext x
    apply e.injective
    change e (e.symm ((↑a⁻¹ : Module.End L V) (e (B x)))) = e x
    rw [e.apply_symm_apply]
    change (↑a⁻¹ : Module.End L V) (g (B x)) = g x
    rw [hb]
    exact unit_inv_apply a (g x)

end SourceOnly.UnitLagReduction

end -- close this source block's anonymous noncomputable section

/- Cohosted FiniteKernelLadder support. -/
/-
Finite simultaneous ordinary kernel quotients of an ACTUAL elementary word.
The input allows singular and zero dimensional intermediate modules.

COLUMN maps are primary. `rows` is the literal transpose of `toMatrix`.
The ROW forward product is chronological; no original map is inverted.
Only dynamics proved to be units by actual lag identities are inverted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SourceOnly.FiniteKernelLadder

open D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open SourceOnly.KernelRSSquare
open SourceOnly.KernelRSSquareGyration
open SourceOnly.UnitLagReduction

universe u
abbrev D := GyrationDyadic
abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) D

/-- A genuinely based finite free module with its actual COLUMN dynamics.
No unit, nonzero-rank or injectivity field occurs. -/
structure Based where
  V : Type u
  [add : AddCommGroup V]
  [moduleD : Module D V]
  dim : ℕ
  basis : Module.Basis (Fin dim) D V
  time : Module.End D V

attribute [instance] Based.add Based.moduleD

section Coordinates
variable {V W : Type u} [AddCommGroup V] [Module D V]
  [AddCommGroup W] [Module D W]

/-- Consumed coordinate helper: the row operation is faithful, including Fin 0. -/
theorem rows_injective {n m : ℕ} (bV : Module.Basis (Fin n) D V)
    (bW : Module.Basis (Fin m) D W) : Function.Injective (rows bV bW) := by
  intro f g h
  apply (LinearMap.toMatrix bV bW).injective
  simpa only [rows, Matrix.transpose_transpose] using congrArg Matrix.transpose h

@[simp] theorem rows_id {n : ℕ} (b : Module.Basis (Fin n) D V) :
    rows b b LinearMap.id = 1 := by
  simp only [rows, LinearMap.toMatrix_id, Matrix.transpose_one]

@[simp] theorem rows_one {n : ℕ} (b : Module.Basis (Fin n) D V) :
    rows b b (1 : Module.End D V) = 1 := rows_id b

/-- Powers of one COLUMN dynamics have the same exponent in row coordinates.
Composition of distinct forward maps, in contrast, reverses at transpose. -/
theorem rows_pow {n : ℕ} (b : Module.Basis (Fin n) D V)
    (T : Module.End D V) (k : ℕ) : rows b b (T^k) = (rows b b T)^k := by
  induction k with
  | zero => exact rows_one b
  | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, rows_comp, ih, pow_succ]

/-- In the basis transported by the actual isomorphism, its matrix is I. -/
theorem rows_equiv {n : ℕ} (b : Module.Basis (Fin n) D V)
    (e : V ≃ₗ[D] W) : rows b (b.map e) e.toLinearMap = 1 := by
  unfold rows
  rw [LinearMap.toMatrix_map_right]
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    ext x
    exact e.symm_apply_apply x
  rw [he, LinearMap.toMatrix_id, Matrix.transpose_one]

/-- Exact change-of-coordinates calculation. This is a matrix statement,
not an assumption that the cochain is conjugacy invariant. -/
theorem rows_transport {X Y : Type u} [AddCommGroup X] [Module D X]
    [AddCommGroup Y] [Module D Y] {n m : ℕ}
    (bV : Module.Basis (Fin n) D V) (bW : Module.Basis (Fin m) D W)
    (eV : V ≃ₗ[D] X) (eW : W ≃ₗ[D] Y)
    (f : V →ₗ[D] W) (g : X →ₗ[D] Y)
    (h : g.comp eV.toLinearMap = eW.toLinearMap.comp f) :
    rows (bV.map eV) (bW.map eW) g = rows bV bW f := by
  unfold rows
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  apply congrArg Matrix.transpose
  apply congrArg (LinearMap.toMatrix bV bW)
  ext x
  change eW.symm (g (eV x)) = f x
  rw [show g (eV x) = eW (f x) from congrArg (fun z => z x) h]
  exact eW.symm_apply_apply (f x)

/-- Units in row coordinates reverse multiplication. Both inverse laws are
proved explicitly, so this does not silently invert the original time. -/
def rowUnit {n : ℕ} (b : Module.Basis (Fin n) D V)
    (a : (Module.End D V)ˣ) : (Mat n n)ˣ where
  val := rows b b (a : Module.End D V)
  inv := rows b b (↑a⁻¹ : Module.End D V)
  val_inv := by
    rw [← rows_comp]
    change rows b b ((↑a⁻¹ : Module.End D V) * (a : Module.End D V)) = 1
    rw [Units.inv_mul, rows_one]
  inv_val := by
    rw [← rows_comp]
    change rows b b ((a : Module.End D V) * (↑a⁻¹ : Module.End D V)) = 1
    rw [Units.mul_inv, rows_one]

end Coordinates

namespace Based

def matrix (X : Based.{u}) : Mat X.dim X.dim := rows X.basis X.basis X.time

/-- The quotient projection is an isomorphism precisely when its actual
kernel vanishes. Surjectivity is the actual quotient API, not a premise. -/
def projectEquiv (X : Based.{u}) (h : Function.Injective X.time) :
    X.V ≃ₗ[D] KQuot X.time :=
  LinearEquiv.ofBijective (project X.time) ⟨by
    apply LinearMap.ker_eq_bot.mp
    simpa only [project, Submodule.ker_mkQ] using LinearMap.ker_eq_bot.mpr h,
    (LinearMap.ker X.time).mkQ_surjective⟩

/-- One choice per vertex. If time is injective use the ACTUAL transported
basis. Otherwise use the proved dyadic PID/range construction. This test
makes no injectivity assumption on a singular intermediate. -/
def quotientCoordinates (X : Based.{u}) :
    Σ n : ℕ, Module.Basis (Fin n) D (KQuot X.time) := by
  classical
  exact if h : Function.Injective X.time then
    ⟨X.dim, X.basis.map (X.projectEquiv h)⟩
  else dyadicQuotientBasis X.basis X.time

/-- The j+1 stage is quotient by the KERNEL OF THE j-STAGE MAP.
It is not the original module equipped with the (j+1)st power. -/
def reduce (X : Based.{u}) : Based.{u} where
  V := KQuot X.time
  dim := X.quotientCoordinates.1
  basis := X.quotientCoordinates.2
  time := reduced X.time

@[simp] theorem project_zero_iff (X : Based.{u}) (x : X.V) :
    project X.time x = 0 ↔ X.time x = 0 :=
  Submodule.Quotient.mk_eq_zero (LinearMap.ker X.time)

@[simp] theorem reduced_project (X : Based.{u}) (x : X.V) :
    X.reduce.time (project X.time x) = project X.time (X.time x) := rfl

/-- Actual vertical intertwining. -/
theorem project_intertwines (X : Based.{u}) :
    X.reduce.time.comp (project X.time) = (project X.time).comp X.time := by
  ext x
  rfl

/-- Factor injectivity comes from the first isomorphism theorem; it does
not require injectivity of time on the original module. -/
theorem factor_injective (X : Based.{u}) : Function.Injective (factor X.time) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

/-- Endpoint injectivity passes to the quotient by its actual kernel. -/
theorem reduced_injective (X : Based.{u}) (h : Function.Injective X.time) :
    Function.Injective X.reduce.time :=
  (X.projectEquiv h).injective.comp X.factor_injective

/-- Actual lag-one proof of the new unit. Injectivity alone is not used
as a surjectivity criterion over the dyadic PID. -/
theorem reduced_isUnit (X : Based.{u}) (h : IsUnit X.time) :
    IsUnit X.reduce.time := by
  let a := h.unit
  have hi : Function.Injective X.time := unit_injective a
  let a' := unitFromLag a X.reduce.time (project X.time) (factor X.time) 1
    (by
      change (factor X.time).comp (project X.time) = X.time
      exact factor_project X.time)
    (by simp only [pow_one]; rfl)
    (by
      ext z
      obtain ⟨x, rfl⟩ := (LinearMap.ker X.time).mkQ_surjective z
      rfl)
    (X.reduced_injective hi)
  exact ⟨a', rfl⟩

def stage (X : Based.{u}) : ℕ → Based.{u}
  | 0 => X
  | j+1 => (X.stage j).reduce

/-- q^j is the composite of all j actual quotient projections. -/
def q (X : Based.{u}) : (j : ℕ) → X.V →ₗ[D] (X.stage j).V
  | 0 => LinearMap.id
  | j+1 => (project (X.stage j).time).comp (X.q j)

theorem q_surjective (X : Based.{u}) (j : ℕ) : Function.Surjective (X.q j) := by
  induction j with
  | zero => exact Function.surjective_id
  | succ j ih => exact (LinearMap.ker (X.stage j).time).mkQ_surjective.comp ih

theorem q_intertwines (X : Based.{u}) (j : ℕ) :
    (X.stage j).time.comp (X.q j) = (X.q j).comp X.time := by
  induction j with
  | zero => rfl
  | succ j ih =>
      ext x
      change (X.stage j).reduce.time (project (X.stage j).time (X.q j x)) =
        project (X.stage j).time (X.q j (X.time x))
      exact (congrArg (fun f => f (X.q j x))
        (X.stage j).project_intertwines).trans
          (congrArg (project (X.stage j).time) (congrArg (fun f => f x) ih))

/-- The key exact induction: iterating kernels of reduced maps removes
exactly ker(T^j) of the ORIGINAL dynamics T. -/
theorem q_zero_iff (X : Based.{u}) (j : ℕ) (x : X.V) :
    X.q j x = 0 ↔ (X.time^j) x = 0 := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      change project (X.stage j).time (X.q j x) = 0 ↔ (X.time^(j+1)) x = 0
      rw [(X.stage j).project_zero_iff]
      have hc := congrArg (fun f => f x) (X.q_intertwines j)
      change (X.stage j).time (X.q j x) = X.q j (X.time x) at hc
      rw [hc, ih, pow_succ, Module.End.mul_apply]

/-- Exact submodule equality; this is not an eventual-kernel premise. -/
theorem kernel_formula (X : Based.{u}) (j : ℕ) :
    LinearMap.ker (X.q j) = LinearMap.ker (X.time^j) := by
  ext x
  exact X.q_zero_iff j x

theorem stage_isUnit (X : Based.{u}) (h : IsUnit X.time) (j : ℕ) :
    IsUnit (X.stage j).time := by
  induction j with
  | zero => exact h
  | succ j ih => exact (X.stage j).reduced_isUnit ih

/-- Endpoint q is its actual bijective quotient composite. -/
def qEquiv (X : Based.{u}) (h : IsUnit X.time) (j : ℕ) :
    X.V ≃ₗ[D] (X.stage j).V :=
  LinearEquiv.ofBijective (X.q j) ⟨by
    apply LinearMap.ker_eq_bot.mp
    rw [X.kernel_formula]
    exact LinearMap.ker_eq_bot.mpr (unit_injective (h.unit^j)), X.q_surjective j⟩

/-- Exact one-step endpoint coordinates. The Sigma equality fixes both
rank and basis, rather than postulating a hidden quotient basis. -/
theorem endpoint_coordinates (X : Based.{u}) (h : IsUnit X.time) :
    X.quotientCoordinates =
      ⟨X.dim, X.basis.map (X.projectEquiv (unit_injective h.unit))⟩ := by
  unfold quotientCoordinates
  split
  · rfl
  · rename_i hn
    exact (hn (unit_injective h.unit)).elim

def vertical {d : ℕ} [NeZero d] (X : Based.{u}) : ZMod 3 :=
  value (d := d) X.basis X.reduce.basis (project X.time) (factor X.time)

/-- Both vertical boundaries of a closed strip vanish by the EXISTING
identity_weight, after computing q=I and factor=A in the transported bases. -/
theorem endpoint_vertical {d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (X : Based.{u}) (h : IsUnit X.time) : X.vertical (d := d) = 0 := by
  have hi : Function.Injective X.time := unit_injective h.unit
  change dyadicGyration d (rows X.basis X.quotientCoordinates.2 (project X.time))
    (rows X.quotientCoordinates.2 X.basis (factor X.time)) = 0
  rw [X.endpoint_coordinates h]
  have hp : rows X.basis (X.basis.map (X.projectEquiv hi)) (project X.time) = 1 :=
    rows_equiv X.basis (X.projectEquiv hi)
  have hf : rows (X.basis.map (X.projectEquiv hi)) X.basis (factor X.time) =
      X.matrix := by
    have hc := congrArg (rows X.basis X.basis) (factor_project X.time)
    rw [rows_comp X.basis (X.basis.map (X.projectEquiv hi)) X.basis,
      hp, Matrix.one_mul] at hc
    exact hc
  rw [hp, hf]
  exact SourceOnly.UnitWordGyration.Edge.identity_weight hd
    ⟨X.dim, rowUnit X.basis h.unit⟩

/-- Finite termination uses the actual prefix lag k≤K. We apply the
supplier's injectivity theorem on the ACTUAL power quotient at k, and
lag_kernel_after to transfer its kernel to K. No inverse of B occurs. -/
theorem final_injective (X : Based.{u})
    {V : Type u} [AddCommGroup V] [Module D V]
    (a : (Module.End D V)ˣ) (f : V →ₗ[D] X.V) (g : X.V →ₗ[D] V)
    (k K : ℕ) (hk : k ≤ K)
    (hgf : g.comp f = (a : Module.End D V)^k)
    (hfg : f.comp g = X.time^k)
    (hgB : g.comp X.time = (a : Module.End D V).comp g) :
    Function.Injective (X.stage K).time := by
  have hstab : LinearMap.ker (X.time^K) = LinearMap.ker (X.time^k) := by
    simpa only [Nat.add_sub_of_le hk] using
      lag_kernel_after a X.time f g k (K-k) hgf hfg hgB
  have hp := powerQuotientEnd_injective a X.time f g k hgf hfg hgB
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := X.q_surjective K z
    have hx : X.q K (X.time x) = 0 := by
      rw [← show (X.stage K).time (X.q K x) = X.q K (X.time x) from
        congrArg (fun t => t x) (X.q_intertwines K)]
      exact hz
    have hK : X.time x ∈ LinearMap.ker (X.time^K) := (X.q_zero_iff K _).mp hx
    rw [hstab] at hK
    have hbar : powerQuotientEnd X.time k ((LinearMap.ker (X.time^k)).mkQ x) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.ker (X.time^k))).mpr hK
    have hxbar : (LinearMap.ker (X.time^k)).mkQ x = 0 :=
      hp (hbar.trans (map_zero _).symm)
    have hxk : x ∈ LinearMap.ker (X.time^k) :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.ker (X.time^k))).mp hxbar
    rw [← hstab] at hxk
    exact (X.q_zero_iff K x).mpr hxk
  · exact bot_le

end Based

end SourceOnly.FiniteKernelLadder

end -- close this source block's anonymous noncomputable section
