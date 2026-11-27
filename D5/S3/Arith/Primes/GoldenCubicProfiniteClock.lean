/- GID: D5/S3/Arith/Primes/GoldenCubicProfiniteClock
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicProfiniteClock
   mirror-E: none(waiver:exact-cofinal-clock)
   anchors: []
   utility: none
   digest: The eventual cubic Lucas residue families form the full compatible absolute-time clock. -/

import D5.S3.Arith.Primes.ProfiniteObservationClock
import D5.S3.Arith.Primes.GoldenCubicClockCofinality

set_option autoImplicit false

/-! The native cubic Lucas observations instantiate the cofinal adding machine. -/

namespace D5.S3.Arith.Primes.GoldenCubicProfiniteClock

open WSSProfiniteClock
open GoldenCubicBlockSignedRankClock GoldenCubicBlockThreeAdic
open GoldenCubicClockCofinality

noncomputable def period (m : Positive) : ℕ := (nativeModulusRule m.val).period

def refinement (m n : Positive) : Prop := m.val ∣ n.val

private theorem exact_kernel (m : Positive) (n k : ℕ)
    (hn : (nativeModulusRule m.val).transient ≤ n)
    (hk : (nativeModulusRule m.val).transient ≤ k) :
    cubicBlock n % (m.val:ℤ) = cubicBlock k % (m.val:ℤ) ↔ n ≡ k [MOD period m] := by
  change (cubicBlock n ≡ cubicBlock k [ZMOD (m.val:ℤ)]) ↔ n ≡ k [MOD period m]
  rcases lt_trichotomy k n with h | h | h
  · rw [native_modulus_collision _ _ _ m.prop h, and_iff_right hk, Nat.ModEq.comm,
      Nat.modEq_iff_dvd' h.le]
    rfl
  · subst k
    exact ⟨fun _ => Nat.ModEq.refl _, fun _ => Int.ModEq.refl _⟩
  · have hs : (cubicBlock n ≡ cubicBlock k [ZMOD (m.val:ℤ)]) ↔
          (cubicBlock k ≡ cubicBlock n [ZMOD (m.val:ℤ)]) :=
        ⟨Int.ModEq.symm, Int.ModEq.symm⟩
    rw [hs, native_modulus_collision _ _ _ m.prop h, and_iff_right hn,
      Nat.modEq_iff_dvd' h.le]
    rfl

/-- Observation at modulus (m) is the literal integer remainder;
no change to the native cubic-block orbit is made. -/
noncomputable def nativeSystem : ObservationSystem period refinement where
  State _ := ℤ
  observe m n := cubicBlock n % (m.val:ℤ)
  threshold m := (nativeModulusRule m.val).transient
  positive m := (native_modulus_rule_spec m.val m.prop).2.1
  kernel := exact_kernel
  reduce {i _j} _h z := z % (i.val:ℤ)
  reduce_observe h n := Int.emod_emod_of_dvd (cubicBlock n) (Int.natCast_dvd_natCast.mpr h)

private theorem native_directed (i j : Positive) : ∃ k, refinement i k ∧ refinement j k :=
  ⟨⟨i.val*j.val, Nat.mul_pos i.prop j.prop⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩

private theorem native_cofinal (m : Positive) : ∃ i, m.val ∣ period i := by
  obtain ⟨M, hM, hdiv⟩ := native_period_cofinal m.val m.prop
  exact ⟨⟨M,hM⟩,hdiv⟩

/-- Every compatible late native residue family has one and only one
compatible absolute-time label across all positive time moduli. -/
noncomputable def nativeClock : EveryClock ≃ nativeSystem.Family :=
  nativeSystem.allClockEquiv native_directed native_cofinal

/-- At each finite modulus, the adding-machine step acts by the native
cubic polynomial followed by reduction. -/
def nativeUpdate (m : Positive) (z : ℤ) : ℤ := (3+(z-3)*z^2) % (m.val:ℤ)

theorem native_observe_next (m : Positive) (n : ℕ) :
    nativeSystem.observe m (n+1) = nativeUpdate m (nativeSystem.observe m n) := by
  change cubicBlock (n+1) % (m.val:ℤ) =
    (3+(cubicBlock n % (m.val:ℤ)-3)*(cubicBlock n % (m.val:ℤ))^2) % (m.val:ℤ)
  have he : cubicBlock (n+1) = 3+(cubicBlock n-3)*(cubicBlock n)^2 := by
    nlinarith only [cubicBlock_three_fixed_point_step n]
  rw [he]
  have h := Int.mod_modEq (cubicBlock n) (m.val:ℤ)
  exact (((h.sub_right 3).mul (h.pow 2)).add_left 3).symm

theorem nativeClock_next (x : EveryClock) (m : Positive) :
    ((nativeClock (EveryClock.next x)).state m).val =
      nativeUpdate m ((nativeClock x).state m).val := by
  change ((nativeSystem.allClockEquiv native_directed native_cofinal (EveryClock.next x)).state m).val = _
  rw [nativeSystem.allClock_next native_directed native_cofinal x]
  exact nativeSystem.next_is_native nativeUpdate native_observe_next _ m

/-- At any single observation precision and all its divisors, a
compatible late-clock reading is realized by arbitrarily late blocks. -/
theorem nativeClock_late_cone (x : EveryClock) (m : Positive) (B : ℕ) :
    ∃ n, B ≤ n ∧ cubicBlock n % (m.val:ℤ) = ((nativeClock x).state m).val ∧
      ∀ k : Positive, k.val ∣ m.val →
        cubicBlock n % (k.val:ℤ) = ((nativeClock x).state k).val :=
  nativeSystem.late_cone (nativeClock x) m B

/-- No finite native block is an eventual family. Its own isolating
three-adic coordinate cannot be realized arbitrarily late. -/
theorem finite_block_not_eventual (i : ℕ) (x : nativeSystem.Family) :
    ∃ m : Positive, (x.state m).val ≠ cubicBlock i % (m.val:ℤ) := by
  let m : Positive := ⟨3^(i+2), by positivity⟩
  refine ⟨m,?_⟩
  intro he
  obtain ⟨n, hn, hobs, _⟩ := nativeSystem.late_cone x m (i+1)
  have hcol : cubicBlock n ≡ cubicBlock i [ZMOD (3:ℤ)^(i+2)] := by
    have hh := hobs.trans he
    change cubicBlock n % (m.val:ℤ) = cubicBlock i % (m.val:ℤ) at hh
    change cubicBlock n % (3:ℤ)^(i+2) = cubicBlock i % (3:ℤ)^(i+2)
    simpa only [m, Nat.cast_pow, Nat.cast_ofNat] using hh
  have hn' := (native_block_isolated_at_three i n).mp hcol
  omega

end D5.S3.Arith.Primes.GoldenCubicProfiniteClock
