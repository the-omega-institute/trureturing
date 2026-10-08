/- GID: D5/S3/HomologicalAlgebra/StationaryColimitAction
   generality: G
   utility: finite-stage detection of identity actions on stationary module colimits
   digest: A finite commuting family acts identically on a finite-rank stationary colimit exactly when one common stage kills every action difference.
-/
import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open Module

namespace D5.S3.HomologicalAlgebra.StationaryColimitAction

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The actual stationary system, with the original forward transition T. -/
def transition (T : Module.End R M) (i j : ℕ) (_ : i ≤ j) : Module.End R M :=
  T ^ (j-i)

instance stationarySystem (T : Module.End R M) :
    DirectedSystem (fun _ : ℕ => M) (fun i j h => transition T i j h) where
  map_self x := by simp [transition]
  map_map := by
    intro k j i hij hjk x
    change (T^(k-j)) ((T^(j-i)) x) = (T^(k-i)) x
    rw [← Module.End.mul_apply, ← pow_add]
    congr 2
    omega

abbrev StationaryModule (T : Module.End R M) :=
  Module.DirectLimit (fun _ : ℕ => M) (transition T)

/-- A commuting endomorphism acts on the actual direct limit. -/
def induced (T P : Module.End R M) (hPT : Commute P T) :
    Module.End R (StationaryModule T) :=
  Module.DirectLimit.map (fun _ : ℕ => P) (by
    intro i j hij
    change P * T^(j-i) = T^(j-i) * P
    exact (hPT.pow_right (j-i)).eq)

private theorem propagate (T P : Module.End R M) {a k : ℕ} (hak : a ≤ k)
    (h : T^a * P = T^a) : T^k * P = T^k := by
  have h' := congrArg (fun Q : Module.End R M => T^(k-a) * Q) h
  simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hak] using h'

/-- Identity on a stationary direct limit is detected at one finite stage
uniformly on a finite basis. No desired matrix-power equality is assumed. -/
private theorem induced_eq_id_iff {I : Type*} [Fintype I]
    (b : Basis I R M) (T P : Module.End R M) (hPT : Commute P T) :
    induced T P hPT = LinearMap.id ↔ ∃ N : ℕ, T^N * P = T^N := by
  classical
  constructor
  · intro h
    have each (i : I) : ∃ N : ℕ, (T^N) (P (b i)) = (T^N) (b i) := by
      have hi := LinearMap.congr_fun h
        (Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (transition T) 0 (b i))
      simp only [induced, Module.DirectLimit.map_apply_of, LinearMap.id_apply] at hi
      obtain ⟨N, h0N, hN⟩ := Module.DirectLimit.exists_eq_of_of_eq hi
      exact ⟨N, by simpa only [transition, Nat.sub_zero] using hN⟩
    choose stage stage_eq using each
    let N : ℕ := Finset.univ.sup stage
    refine ⟨N, b.ext (fun i => ?_)⟩
    have hi : stage i ≤ N := Finset.le_sup (f := stage) (Finset.mem_univ i)
    have heq := congrArg (fun x : M => (T^(N-stage i)) x) (stage_eq i)
    change (T^N) (P (b i)) = (T^N) (b i)
    simpa only [← Module.End.mul_apply, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi] using heq
  · rintro ⟨N, hN⟩
    apply Module.DirectLimit.hom_ext
    intro i
    apply LinearMap.ext
    intro x
    change induced T P hPT
        (Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (transition T) i x) =
      Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (transition T) i x
    rw [induced, Module.DirectLimit.map_apply_of]
    have lift_stage (v : M) :
        Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (transition T) (i+N)
          ((T^N) v) =
        Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (transition T) i v := by
      simpa only [transition, Nat.add_sub_cancel_left] using
        (Module.DirectLimit.of_f (R := R) (ι := ℕ) (G := fun _ : ℕ => M)
          (f := transition T) (i := i) (j := i+N) (hij := Nat.le_add_right i N) (x := v))
    calc
      _ = Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (transition T) (i+N)
            ((T^N) (P x)) := (lift_stage (P x)).symm
      _ = Module.DirectLimit.of R ℕ (fun _ : ℕ => M) (transition T) (i+N)
            ((T^N) x) := by
        exact congrArg (Module.DirectLimit.of R ℕ (fun _ : ℕ => M)
          (transition T) (i+N)) (LinearMap.congr_fun hN x)
      _ = _ := lift_stage x

/-- A finite family acting identically on the dimension group has one common
annihilation stage; conversely one common stage proves identity on every level.
For original18.1, R=Z, I=Fin n x H, and P is the original left H action. -/
theorem finite_family_inert_iff_eventual {I Γ : Type*} [Fintype I] [Fintype Γ]
    (b : Basis I R M) (T : Module.End R M) (P : Γ → Module.End R M)
    (hPT : ∀ g, Commute (P g) T) :
    (∀ g, induced T (P g) (hPT g) = LinearMap.id) ↔
      ∃ N : ℕ, ∀ g, T^N * P g = T^N := by
  classical
  constructor
  · intro h
    have each : ∀ g, ∃ N : ℕ, T^N * P g = T^N :=
      fun g => (induced_eq_id_iff b T (P g) (hPT g)).mp (h g)
    choose stage hstage using each
    refine ⟨Finset.univ.sup stage, fun g => ?_⟩
    exact propagate T (P g) (Finset.le_sup (f := stage) (Finset.mem_univ g)) (hstage g)
  · rintro ⟨N, hN⟩ g
    exact (induced_eq_id_iff b T (P g) (hPT g)).mpr ⟨N, hN g⟩

end D5.S3.HomologicalAlgebra.StationaryColimitAction
