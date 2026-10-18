/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/Source
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/Source
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer-clock XOR sources retain separators and the actual hidden endpoint. -/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

abbrev Spins := ℤ → Bool

inductive Hidden where
  | a (spin : Bool)
  | b (spin : Bool)
  deriving DecidableEq, Fintype

/-- Both phases use the original integer read clock. -/
def visible (φ : Bool) (S : Spins) (t : ℤ) : Bool :=
  if (t - φ.toInt) % 2 = 0 then
    Bool.xor (S ((t - φ.toInt) / 2)) (S ((t - φ.toInt) / 2 + 1))
  else false

def hidden (φ : Bool) (S : Spins) (t : ℤ) : Hidden :=
  if (t - φ.toInt) % 2 = 0 then .a (S ((t - φ.toInt) / 2))
  else .b (S ((t - φ.toInt) / 2 + 1))

/-- The target spin index at endpoint zero or one, in either phase. -/
def targetIndex (j φ : Bool) : ℤ := if φ then 0 else j.toInt

def targetClass (j φ : Bool) (s : Bool) : Hidden :=
  if j = φ then .a s else .b s

theorem active_visible (φ : Bool) (S : Spins) (e : ℤ) :
    visible φ S (2 * e + φ.toInt) = Bool.xor (S e) (S (e + 1)) := by
  have hd : (2 * e + φ.toInt - φ.toInt) / 2 = e := by omega
  have hm : (2 * e + φ.toInt - φ.toInt) % 2 = 0 := by omega
  simp [visible, hm, hd]

theorem separator_visible (φ : Bool) (S : Spins) (e : ℤ) :
    visible φ S (2 * e + φ.toInt + 1) = false := by
  have hm : (2 * e + φ.toInt + 1 - φ.toInt) % 2 ≠ 0 := by omega
  simp [visible, hm]

theorem active_hidden (φ : Bool) (S : Spins) (e : ℤ) :
    hidden φ S (2 * e + φ.toInt) = .a (S e) := by
  have hd : (2 * e + φ.toInt - φ.toInt) / 2 = e := by omega
  have hm : (2 * e + φ.toInt - φ.toInt) % 2 = 0 := by omega
  simp [hidden, hm, hd]

theorem separator_hidden (φ : Bool) (S : Spins) (e : ℤ) :
    hidden φ S (2 * e + φ.toInt + 1) = .b (S (e + 1)) := by
  have hd : (2 * e + φ.toInt + 1 - φ.toInt) / 2 = e := by omega
  have hm : (2 * e + φ.toInt + 1 - φ.toInt) % 2 ≠ 0 := by omega
  simp [hidden, hm, hd]

theorem negative_seam (S : Spins) : hidden true S 0 = .b (S 0) := by
  simpa using separator_hidden true S (-1)

theorem actual_endpoint (j φ : Bool) (S : Spins) :
    hidden φ S j.toInt = targetClass j φ (S (targetIndex j φ)) := by
  cases j <;> cases φ
  · simpa [targetClass, targetIndex] using active_hidden false S 0
  · simpa [targetClass, targetIndex] using negative_seam S
  · simpa [targetClass, targetIndex] using separator_hidden false S 0
  · simpa [targetClass, targetIndex] using active_hidden true S 0

theorem opposite_phase_visible (φ : Bool) (S : Spins) (t : ℤ)
    (h : (t - φ.toInt) % 2 = 0) : visible (!φ) S t = false := by
  have ht : 2 * ((t - (!φ).toInt - 1) / 2) + (!φ).toInt + 1 = t := by
    cases φ <;> simp only [Bool.not_false, Bool.not_true, Bool.toInt_false,
      Bool.toInt_true] at * <;> omega
  simpa only [ht] using separator_visible (!φ) S ((t - (!φ).toInt - 1) / 2)

theorem constant_visible (φ s : Bool) (t : ℤ) : visible φ (fun _ => s) t = false := by
  simp [visible]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
