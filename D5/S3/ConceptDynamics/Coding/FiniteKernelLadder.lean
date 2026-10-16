/- GID: D5/S3/ConceptDynamics/Coding/FiniteKernelLadder
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FiniteKernelLadder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite kernel towers, original-length termination, cochain strips and stored endpoint coordinates. -/

import D5.S3.ConceptDynamics.Coding.FiniteWordLag
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

/-- An actual COLUMN elementary SSE. Its two equations are part of the
input word, not a shift-equivalence surrogate. -/
structure Edge (X Y : Based.{u}) where
  r : X.V →ₗ[D] Y.V
  s : Y.V →ₗ[D] X.V
  sr : s.comp r = X.time
  rs : r.comp s = Y.time

namespace Edge
variable {X Y : Based.{u}}

/-- The actual induced forward arrow on the simultaneous vertex quotients. -/
def reduceR (e : Edge X Y) : X.reduce.V →ₗ[D] Y.reduce.V :=
  (LinearMap.ker X.time).liftQ ((project Y.time).comp e.r) (by
    intro x hx
    apply (Y.project_zero_iff _).mpr
    have hc : Y.time (e.r x) = e.r (X.time x) := by
      rw [← e.rs, ← e.sr]
      rfl
    rw [hc]
    change X.time x = 0 at hx
    rw [hx, map_zero])

def reduceS (e : Edge X Y) : Y.reduce.V →ₗ[D] X.reduce.V :=
  (LinearMap.ker Y.time).liftQ ((project X.time).comp e.s) (by
    intro y hy
    apply (X.project_zero_iff _).mpr
    have hc : X.time (e.s y) = e.s (Y.time y) := by
      rw [← e.rs, ← e.sr]
      rfl
    rw [hc]
    change Y.time y = 0 at hy
    rw [hy, map_zero])

@[simp] theorem reduceR_project (e : Edge X Y) (x : X.V) :
    e.reduceR (project X.time x) = project Y.time (e.r x) := rfl

@[simp] theorem reduceS_project (e : Edge X Y) (y : Y.V) :
    e.reduceS (project Y.time y) = project X.time (e.s y) := rfl

/-- This pair IS the supplier's bottomForward/bottomBackward after the
two actual endpoint equations identify P,Q with the vertex dynamics. -/
def reduce (e : Edge X Y) : Edge X.reduce Y.reduce where
  r := e.reduceR
  s := e.reduceS
  sr := by
    ext z
    obtain ⟨x, rfl⟩ := (LinearMap.ker X.time).mkQ_surjective z
    change e.reduceS (e.reduceR (project X.time x)) =
      X.reduce.time (project X.time x)
    rw [reduceR_project, reduceS_project, Based.reduced_project]
    exact congrArg (project X.time) (congrArg (fun t => t x) e.sr)
  rs := by
    ext z
    obtain ⟨y, rfl⟩ := (LinearMap.ker Y.time).mkQ_surjective z
    change e.reduceR (e.reduceS (project Y.time y)) =
      Y.reduce.time (project Y.time y)
    rw [reduceS_project, reduceR_project, Based.reduced_project]
    exact congrArg (project Y.time) (congrArg (fun t => t y) e.rs)

def weight (d : ℕ) [NeZero d] (e : Edge X Y) : ZMod 3 :=
  value (d := d) X.basis Y.basis e.r e.s

/-- Four ACTUAL RS triangles, not just naturality of the quotient square.
The center basis is chosen once for this cell; vertex quotient bases are
those of Based.reduce and are reused by both adjacent cells. No coordinate
reset is inserted. Both vertical values are retained literally. -/
theorem cell {d : ℕ} [NeZero d] (hd : 3 ∣ d) (e : Edge X Y) :
    e.weight d + Y.vertical (d := d) =
      X.vertical (d := d) + e.reduce.weight d := by
  cases X with
  | @mk VX ax mx nx bx tx =>
    cases Y with
    | @mk VY ay my ny by_ ty =>
      letI := ax
      letI := mx
      letI := ay
      letI := my
      rcases e with ⟨r, s, hsr, hrs⟩
      change VX →ₗ[D] VY at r
      change VY →ₗ[D] VX at s
      change s.comp r = tx at hsr
      change r.comp s = ty at hrs
      cases hsr
      cases hrs
      let bc := dyadicQuotientBasis by_ r
      let X' : Based.{u} := { V := VX, dim := nx, basis := bx, time := s.comp r }
      let Y' : Based.{u} := { V := VY, dim := ny, basis := by_, time := r.comp s }
      exact kernel_square hd r s bx by_ bc.2 X'.quotientCoordinates.2
        Y'.quotientCoordinates.2

end Edge

/-- A finite arbitrary elementary word. Length zero is an actual constructor. -/
inductive Path : Based.{u} → Based.{u} → ℕ → Type (u+1)
  | nil (X : Based.{u}) : Path X X 0
  | cons {X Y Z : Based.{u}} {n : ℕ} (e : Edge X Y) (tail : Path Y Z n) :
      Path X Z (n+1)

namespace Path
variable {X Y Z : Based.{u}} {n m : ℕ}

def forward : {X Y : Based.{u}} → {n : ℕ} → Path X Y n → X.V →ₗ[D] Y.V
  | _, _, _, .nil _ => LinearMap.id
  | _, _, _, .cons e tail => tail.forward.comp e.r

def forwardRows (w : Path X Y n) : Mat X.dim Y.dim :=
  rows X.basis Y.basis w.forward

/-- The recursive sum of exactly the existing B_d on the actual letters. -/
def weight (d : ℕ) [NeZero d] :
    {X Y : Based.{u}} → {n : ℕ} → Path X Y n → ZMod 3
  | _, _, _, .nil _ => 0
  | _, _, _, .cons e tail => e.weight d + tail.weight d

@[simp] theorem forwardRows_nil (X : Based.{u}) : (nil X).forwardRows = 1 := rows_id _

/-- Explicit chronological order R_0 R_1 ... R_(n-1) in ROW coordinates. -/
theorem forwardRows_cons (e : Edge X Y) (tail : Path Y Z n) :
    (cons e tail).forwardRows = rows X.basis Y.basis e.r * tail.forwardRows :=
  rows_comp _ _ _ _ _


def reduce : {X Y : Based.{u}} → {n : ℕ} → Path X Y n → Path X.reduce Y.reduce n
  | _, _, _, .nil X => .nil X.reduce
  | _, _, _, .cons e tail => .cons e.reduce tail.reduce

/-- Naturality of the actual chronological COLUMN composite. This theorem
is used for products only; the cochain proof instead consumes Edge.cell. -/
theorem reduce_forward (w : Path X Y n) :
    w.reduce.forward.comp (project X.time) = (project Y.time).comp w.forward := by
  induction w with
  | nil X => rfl
  | cons e tail ih =>
      ext x
      change tail.reduce.forward (e.reduceR (project _ x)) =
        project _ (tail.forward (e.r x))
      rw [Edge.reduceR_project]
      exact congrArg (fun t => t (e.r x)) ih

/-- Sum the strip, with BOTH endpoint vertical terms still visible.
Every interior vertical term cancels because its module AND basis are
literally the same on the two incident cells. -/
theorem strip {d : ℕ} [NeZero d] (hd : 3 ∣ d) (w : Path X Y n) :
    w.weight d + Y.vertical (d := d) =
      X.vertical (d := d) + w.reduce.weight d := by
  induction w with
  | nil X => simp only [weight, reduce, zero_add, add_zero]
  | @cons X Z Y n e tail ih =>
      change (e.weight d + tail.weight d) + _ = _ + (e.reduce.weight d + _)
      calc
        (e.weight d + tail.weight d) + Y.vertical (d := d) =
            e.weight d + (tail.weight d + Y.vertical (d := d)) := add_assoc _ _ _
        _ = e.weight d + (_ + tail.reduce.weight d) := by rw [ih]
        _ = (e.weight d + _) + tail.reduce.weight d := (add_assoc _ _ _).symm
        _ = (X.vertical (d := d) + e.reduce.weight d) + tail.reduce.weight d := by
          rw [e.cell hd]
        _ = X.vertical (d := d) + (e.reduce.weight d + tail.reduce.weight d) :=
          add_assoc _ _ _

/-- One complete row of cells preserves the same cochain for unit endpoints. -/
theorem reduce_weight {d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (w : Path X Y n) (hX : IsUnit X.time) (hY : IsUnit Y.time) :
    w.reduce.weight d = w.weight d := by
  have h := w.strip hd
  rw [X.endpoint_vertical hd hX, Y.endpoint_vertical hd hY, add_zero, zero_add] at h
  exact h.symm

/-- Actual endpoint quotient bases give equality of chronological products,
not just conjugacy of their induced actions. HEq accounts for the rank
identity proved by the endpoint basis Sigma equality. -/
theorem reduce_forwardRows (w : Path X Y n)
    (hX : IsUnit X.time) (hY : IsUnit Y.time) :
    HEq w.reduce.forwardRows w.forwardRows := by
  have hn := w.reduce_forward
  change HEq (rows X.quotientCoordinates.2 Y.quotientCoordinates.2 w.reduce.forward)
    (rows X.basis Y.basis w.forward)
  rw [X.endpoint_coordinates hX, Y.endpoint_coordinates hY]
  exact heq_of_eq (rows_transport X.basis Y.basis
    (X.projectEquiv (unit_injective hX.unit))
    (Y.projectEquiv (unit_injective hY.unit)) w.forward w.reduce.forward hn)

def stage (w : Path X Y n) : (j : ℕ) → Path (X.stage j) (Y.stage j) n
  | 0 => w
  | j+1 => (w.stage j).reduce

theorem stage_weight {d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (w : Path X Y n) (hX : IsUnit X.time) (hY : IsUnit Y.time) (j : ℕ) :
    (w.stage j).weight d = w.weight d := by
  induction j with
  | zero => rfl
  | succ j ih =>
      exact ((w.stage j).reduce_weight hd (X.stage_isUnit hX j)
        (Y.stage_isUnit hY j)).trans ih

theorem stage_forwardRows (w : Path X Y n)
    (hX : IsUnit X.time) (hY : IsUnit Y.time) (j : ℕ) :
    HEq (w.stage j).forwardRows w.forwardRows := by
  induction j with
  | zero => rfl
  | succ j ih =>
      exact HEq.trans ((w.stage j).reduce_forwardRows
        (X.stage_isUnit hX j) (Y.stage_isUnit hY j)) ih

/-- Membership of ALL vertices, including the last one. -/
def All (p : Based.{u} → Prop) : {X Y : Based.{u}} → {n : ℕ} → Path X Y n → Prop
  | X, _, _, .nil _ => p X
  | X, _, _, .cons _ tail => p X ∧ tail.All p

theorem all_head {p : Based.{u} → Prop} (w : Path X Y n) (h : w.All p) : p X := by
  cases w with
  | nil X => exact h
  | cons e tail => exact h.1

theorem all_last {p : Based.{u} → Prop} (w : Path X Y n) (h : w.All p) : p Y := by
  revert h
  induction w with
  | nil X => exact fun h => h
  | cons e tail ih => exact fun h => ih h.2

theorem all_mono {p q : Based.{u} → Prop} (w : Path X Y n)
    (hpq : ∀ V, p V → q V) (h : w.All p) : w.All q := by
  revert h
  induction w with
  | nil X => exact fun h => hpq X h
  | cons e tail ih => exact fun h => ⟨hpq _ h.1, ih h.2⟩

theorem all_reduce {p : Based.{u} → Prop} (w : Path X Y n)
    (h : w.All (fun V => p V.reduce)) : w.reduce.All p := by
  revert h
  induction w with
  | nil X => exact fun h => h
  | cons e tail ih => exact fun h => ⟨h.1, ih h.2⟩

theorem all_stage {p : Based.{u} → Prop} (w : Path X Y n) (j : ℕ)
    (h : w.All (fun V => p (V.stage j))) : (w.stage j).All p := by
  revert h
  induction j generalizing p with
  | zero => exact fun h => h
  | succ j ih => exact fun h => (w.stage j).all_reduce (ih h)

/-- Ordinary concatenation, used to expose actual prefixes rather than
postulating lag data at each vertex. -/
def append : {X Y Z : Based.{u}} → {n m : ℕ} →
    Path X Y n → Path Y Z m → Path X Z (n+m)
  | _, _, _, _, _, .nil _, v => by simpa only [Nat.zero_add] using v
  | _, _, _, _, _, .cons e tail, v => by
      simpa only [Nat.add_right_comm] using cons e (append tail v)

/-- Every vertex is reached by an actual prefix of length at most n.
This retains arbitrary singular intermediates and the empty prefix. -/
theorem all_from_prefix {A B C : Based.{u}} {k l : ℕ}
    (v : Path A B k) (w : Path B C l) :
    w.All (fun T => ∃ i : ℕ, i ≤ k+l ∧ Nonempty (Path A T i)) := by
  induction w generalizing A k with
  | nil B => exact ⟨k, by omega, ⟨v⟩⟩
  | @cons B C E l e tail ih =>
      constructor
      · exact ⟨k, by omega, ⟨v⟩⟩
      · have ht := ih (v.append (.cons e (.nil C)))
        simpa only [Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 l] using ht

theorem all_prefix (w : Path X Y n) :
    w.All (fun T => ∃ k : ℕ, k ≤ n ∧ Nonempty (Path X T k)) := by
  simpa only [Nat.zero_add] using all_from_prefix (.nil X) w

/-- The exact immutable ExchangeChain; no new abstract lag premise. -/
theorem exchangeChain (w : Path X Y n) :
    D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain
      D X.matrix Y.matrix n := by
  induction w with
  | nil X => exact .nil X.matrix
  | @cons X Z Y n e tail ih =>
      have hsr : rows X.basis Z.basis e.r * rows Z.basis X.basis e.s = X.matrix := by
        rw [← rows_comp, e.sr]
        rfl
      have hrs : rows Z.basis X.basis e.s * rows X.basis Z.basis e.r = Z.matrix := by
        rw [← rows_comp, e.rs]
        rfl
      rw [← hrs] at ih
      have hc := D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier.ExchangeChain.cons
        (rows X.basis Z.basis e.r) (rows Z.basis X.basis e.s) ih
      rw [hsr] at hc
      exact hc

/-- FiniteWordLag.chain_lag gives actual maps in COLUMN coordinates after
transposing back. All three consumed lag equations are proved here. -/
theorem lag (w : Path X Y n) :
    ∃ f : X.V →ₗ[D] Y.V, ∃ g : Y.V →ₗ[D] X.V,
      g.comp f = X.time^n ∧ f.comp g = Y.time^n ∧
      g.comp Y.time = X.time.comp g := by
  obtain ⟨F, G, _hAF, hBG, hFG, hGF⟩ :=
    SourceOnly.FiniteWordLag.chain_lag w.exchangeChain
  let f := Matrix.toLin X.basis Y.basis F.transpose
  let g := Matrix.toLin Y.basis X.basis G.transpose
  have hf : rows X.basis Y.basis f = F := by
    simp only [rows, f, LinearMap.toMatrix_toLin, Matrix.transpose_transpose]
  have hg : rows Y.basis X.basis g = G := by
    simp only [rows, g, LinearMap.toMatrix_toLin, Matrix.transpose_transpose]
  refine ⟨f, g, ?_, ?_, ?_⟩
  · apply rows_injective X.basis X.basis
    rw [rows_comp, hf, hg, rows_pow]
    exact hFG
  · apply rows_injective Y.basis Y.basis
    rw [rows_comp, hf, hg, rows_pow]
    exact hGF
  · apply rows_injective Y.basis X.basis
    rw [rows_comp, rows_comp, hg]
    exact hBG

/-- All final maps are injective at K=n, from each actual prefix lag k≤n. -/
theorem final_all_injective (w : Path X Y n) (hX : IsUnit X.time) :
    (w.stage n).All (fun V => Function.Injective V.time) := by
  apply w.all_stage n
  apply w.all_mono _ w.all_prefix
  intro T hT
  obtain ⟨k, hk, ⟨pre⟩⟩ := hT
  obtain ⟨f, g, hgf, hfg, hgB⟩ := pre.lag
  exact T.final_injective hX.unit f g k n hk hgf hfg hgB

/-- Consumed logical helper for the vertex induction. -/
theorem all_mp {p q : Based.{u} → Prop} (w : Path X Y n) :
    w.All p → w.All (fun T => p T → q T) → w.All q := by
  induction w with
  | nil X => exact fun hi hp => hp hi
  | cons e tail ih => exact fun hi hp => ⟨hp.1 hi.1, ih hi.2 hp.2⟩

/-- Actual injective final vertices become units ONLY through their actual
finite prefix lag identities and unitFromLag. -/
theorem all_isUnit_of_all_injective (w : Path X Y n) (hX : IsUnit X.time)
    (hi : w.All (fun V => Function.Injective V.time)) :
    w.All (fun V => IsUnit V.time) := by
  have hp : w.All (fun T =>
      Function.Injective T.time → IsUnit T.time) := by
    apply w.all_mono _ w.all_prefix
    intro T hT hTinj
    obtain ⟨k, _hk, ⟨pre⟩⟩ := hT
    obtain ⟨f, g, hgf, hfg, hgB⟩ := pre.lag
    exact ⟨unitFromLag hX.unit T.time f g k hgf hfg hgB hTinj, rfl⟩
  exact w.all_mp hi hp

/-- This is the constructed final word's unit assertion, with no singular
intermediate of the original word ever being inverted. -/
theorem final_all_isUnit (w : Path X Y n) (hX : IsUnit X.time) :
    (w.stage n).All (fun V => IsUnit V.time) :=
  (w.stage n).all_isUnit_of_all_injective (X.stage_isUnit hX n)
    (w.final_all_injective hX)

end Path

namespace Based

/-- A Sigma packages a finite basis without losing its index equality. -/
def coordinates (X : Based.{u}) : Σ n : ℕ, Module.Basis (Fin n) D X.V :=
  ⟨X.dim, X.basis⟩

/-- FULL cumulative endpoint basis identity, not merely recursive pairwise
basis choices. It proves that the stored stage basis is the image of the
ORIGINAL basis under the ACTUAL q^j isomorphism. -/
theorem endpoint_basis_transport (X : Based.{u}) (h : IsUnit X.time) (j : ℕ) :
    (X.stage j).coordinates = ⟨X.dim, X.basis.map (X.qEquiv h j)⟩ := by
  induction j with
  | zero =>
      change (⟨X.dim, X.basis⟩ : Σ n, Module.Basis (Fin n) D X.V) = _
      congr 1
      ext i
      rfl
  | succ j ih =>
      let e := (X.stage j).projectEquiv (unit_injective (X.stage_isUnit h j).unit)
      let mapCoordinates :
          (Σ n, Module.Basis (Fin n) D (X.stage j).V) →
          (Σ n, Module.Basis (Fin n) D (X.stage (j+1)).V) :=
        fun c => ⟨c.1, c.2.map e⟩
      calc
        (X.stage (j+1)).coordinates = mapCoordinates (X.stage j).coordinates :=
          (X.stage j).endpoint_coordinates (X.stage_isUnit h j)
        _ = mapCoordinates ⟨X.dim, X.basis.map (X.qEquiv h j)⟩ := congrArg _ ih
        _ = ⟨X.dim, X.basis.map (X.qEquiv h (j+1))⟩ := by
          change (⟨X.dim, (X.basis.map (X.qEquiv h j)).map e⟩ :
            Σ n, Module.Basis (Fin n) D (X.stage (j+1)).V) = _
          congr 1
          ext i
          rfl

/-- The final time matrix is the literal original A, in that same basis. -/
theorem endpoint_matrix (X : Based.{u}) (h : IsUnit X.time) (j : ℕ) :
    HEq (X.stage j).matrix X.matrix := by
  change HEq (rows (X.stage j).coordinates.2 (X.stage j).coordinates.2
    (X.stage j).time) _
  rw [X.endpoint_basis_transport h j]
  exact heq_of_eq (rows_transport X.basis X.basis (X.qEquiv h j) (X.qEquiv h j)
    X.time (X.stage j).time (X.q_intertwines j))

abbrev unitVertex (X : Based.{u}) (h : IsUnit X.time) : SourceOnly.UnitWordGyration.Vertex where
  dim := X.dim
  time := rowUnit X.basis h.unit

end Based

/-- Consumed dependent-coordinate helper. HEq is used only to transport the
proved rank equality; the resulting vertices are literally equal. -/
theorem unitVertex_ext {A B : SourceOnly.UnitWordGyration.Vertex}
    (hdim : A.dim = B.dim)
    (hval : HEq (A.time : Mat A.dim A.dim) (B.time : Mat B.dim B.dim)) : A = B := by
  rcases A with ⟨na, a⟩
  rcases B with ⟨nb, b⟩
  dsimp only at hdim hval
  subst nb
  have hab : a = b := Units.ext (eq_of_heq hval)
  cases hab
  rfl

namespace Based

/-- This equality is at the exact UnitWordGyration vertex, not a new
cochain or a conjugate endpoint supplied as a premise. -/
theorem endpoint_unitVertex (X : Based.{u}) (h : IsUnit X.time) (j : ℕ) :
    (X.stage j).unitVertex (X.stage_isUnit h j) = X.unitVertex h := by
  apply unitVertex_ext
  · exact congrArg Sigma.fst (X.endpoint_basis_transport h j)
  · exact X.endpoint_matrix h j

end Based

namespace Edge
variable {X Y : Based.{u}}

/-- Reconstruct an existing ROW unit edge only after BOTH time units have
been proved. R and S are the same actual reduced linear maps in their
stored stage bases. -/
def unitEdge (e : Edge X Y) (hX : IsUnit X.time) (hY : IsUnit Y.time) :
    SourceOnly.UnitWordGyration.Edge (X.unitVertex hX) (Y.unitVertex hY) where
  R := rows X.basis Y.basis e.r
  S := rows Y.basis X.basis e.s
  rs := by
    change rows X.basis Y.basis e.r * rows Y.basis X.basis e.s = X.matrix
    rw [← rows_comp, e.sr]
    rfl
  sr := by
    change rows Y.basis X.basis e.s * rows X.basis Y.basis e.r = Y.matrix
    rw [← rows_comp, e.rs]
    rfl

end Edge

namespace Path
variable {X Y : Based.{u}} {n : ℕ}

/-- Reconstruct the existing finite Word, with an actual unit at every
vertex. The hypotheses here are discharged by final_all_isUnit below. -/
def unitWord : {X Y : Based.{u}} → {n : ℕ} → (w : Path X Y n) →
    (h : w.All (fun V => IsUnit V.time)) →
    SourceOnly.UnitWordGyration.Word
      (X.unitVertex (w.all_head h)) (Y.unitVertex (w.all_last h))
  | _, _, _, .nil X, h => .nil (X.unitVertex h)
  | _, _, _, .cons e tail, h =>
      .cons (e.unitEdge h.1 (tail.all_head h.2)) (tail.unitWord h.2)

theorem unitWord_weight {d : ℕ} [NeZero d] (w : Path X Y n)
    (h : w.All (fun V => IsUnit V.time)) :
    (w.unitWord h).weight d = w.weight d := by
  revert h
  induction w with
  | nil X => exact fun _ => rfl
  | cons e tail ih =>
      intro h
      change e.weight d + (tail.unitWord h.2).weight d = e.weight d + tail.weight d
      rw [ih h.2]

/-- Literal chronological forward product, retained by reconstruction. -/
theorem unitWord_forward (w : Path X Y n)
    (h : w.All (fun V => IsUnit V.time)) :
    (w.unitWord h).forward = w.forwardRows := by
  revert h
  induction w with
  | nil X => exact fun _ => (forwardRows_nil X).symm
  | cons e tail ih =>
      intro h
      change rows _ _ e.r * (tail.unitWord h.2).forward = _
      rw [ih h.2, forwardRows_cons]

end Path

/-- Transport along the proved endpoint-vertex equality. This changes no
letter, basis, cochain value or forward matrix entry. -/
def transportLoop {A B : SourceOnly.UnitWordGyration.Vertex} (h : A = B)
    (w : SourceOnly.UnitWordGyration.Word A A) : SourceOnly.UnitWordGyration.Word B B :=
  h ▸ w

theorem transportLoop_weight {A B : SourceOnly.UnitWordGyration.Vertex}
    {d : ℕ} [NeZero d] (h : A = B) (w : SourceOnly.UnitWordGyration.Word A A) :
    (transportLoop h w).weight d = w.weight d := by
  cases h
  rfl

theorem transportLoop_forward {A B : SourceOnly.UnitWordGyration.Vertex}
    (h : A = B) (w : SourceOnly.UnitWordGyration.Word A A) :
    HEq (transportLoop h w).forward w.forward := by
  cases h
  rfl

/-- CLOSED arbitrary finite elementary loop-to-one-edge construction.
It returns the existing unit Word on the literal original row vertex, the
unit whose value is the actual chronological forward product, preservation
of the SAME B_d sum, and the existing loop_one_edge comparison.

No ladder, cochain conservation, quotient basis or intermediate unit is an
input. Length zero and rank zero are retained. The independent original-h
periodic/beam application is outside this finite algebraic statement. -/
theorem arbitrary_loop_one_edge {X : Based.{u}} {n : ℕ}
    (w : Path X X n) (hX : IsUnit X.time) :
    ∃ v : SourceOnly.UnitWordGyration.Word (X.unitVertex hX) (X.unitVertex hX),
    ∃ U : (Mat X.dim X.dim)ˣ,
      v.forward = w.forwardRows ∧
      (U : Mat X.dim X.dim) = w.forwardRows ∧
      Commute (U : Mat X.dim X.dim) X.matrix ∧
      ∀ (d : ℕ) [NeZero d], 3 ∣ d →
        v.weight d = w.weight d ∧
        w.weight d = dyadicGyration d w.forwardRows
          ((↑U⁻¹ : Mat X.dim X.dim) * X.matrix) := by
  have hu : (w.stage n).All (fun V => IsUnit V.time) := w.final_all_isUnit hX
  let v₀ := (w.stage n).unitWord hu
  have hv : (X.stage n).unitVertex ((w.stage n).all_head hu) = X.unitVertex hX :=
    X.endpoint_unitVertex hX n
  let v := transportLoop hv v₀
  have hforward : v.forward = w.forwardRows := by
    apply eq_of_heq
    exact HEq.trans (transportLoop_forward hv v₀)
      (HEq.trans (heq_of_eq ((w.stage n).unitWord_forward hu))
        (w.stage_forwardRows hX hX n))
  refine ⟨v, v.loopUnit, hforward, v.collapse_forward.trans hforward,
    v.loopUnit_commutes, ?_⟩
  intro d _ hd
  have hweight : v.weight d = w.weight d := by
    calc
      v.weight d = v₀.weight d := transportLoop_weight hv v₀
      _ = (w.stage n).weight d := (w.stage n).unitWord_weight hu
      _ = w.weight d := w.stage_weight hd hX hX n
  refine ⟨hweight, ?_⟩
  calc
    w.weight d = v.weight d := hweight.symm
    _ = dyadicGyration d v.forward
        ((v.loopUnit⁻¹).val * X.matrix) := v.loop_one_edge hd
    _ = _ := by rw [hforward]

end SourceOnly.FiniteKernelLadder

end -- close this source block's anonymous noncomputable section

