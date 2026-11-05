/- GID: D5/S3/Combinatorics/Circle/NarrowDoublingOrbit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/NarrowDoublingOrbit
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Dynamics.PeriodicPts.Defs, mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: Actual arbitrary-seed narrow doubling orbits have Mersenne reduced modulus and exact diameter. -/
import D5.S1.Words.AssociatedMersenne.CircularWords
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! # Narrow doubling orbits at arbitrary odd modulus

For odd X >= 3 and 0 < Q < X, the actual least period r, gcd g and standard
orbit diameter W satisfy r >= 2, r = orderOf (2 : ZMod (X/g)) and, when
2*W < X, X/g = 2^r-1 and 2*W = X-g. The proof derives the sorted rotation,
its single actual temporal cycle, the adjacent-gap recurrence and gcd
cancellation. Nonunit seeds remain in scope.

The fixed-Q consumers use one consecutive block of the actual period.
The converse chooses Q existentially. Full physical Circle J remains OPEN:
no physical realization, nested masks, joint-strip sufficiency or prescribed-Q
sufficiency is asserted.

Attribution: elementary finite cyclic order, least-period and gcd arguments.
Caller-supplied Pro reasoning and independent ordinary checking were fallible
inputs; the successful native scoped Lean build establishes the formal proof.
No literature novelty or official acceptance is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace D5.S3.Combinatorics.Circle.NarrowDoublingOrbit

open D5.S1.Words.AssociatedMersenne.CircularWords

/-- Standard representatives, including nonunit seeds. -/
def residue (X Q n : ℕ) : ℕ := (2 ^ n * Q) % X

/-- Actual least dynamical period; no proposed period is substituted. -/
noncomputable def period (X Q : ℕ) : ℕ :=
  Function.minimalPeriod (fun z : ZMod X => 2 * z) (Q : ZMod X)

def denominator (X Q : ℕ) : ℕ := X / Nat.gcd X Q

/-- One actual least-period block, with repeated ambient labels removed. -/
noncomputable def orbit (X Q : ℕ) : Finset ℕ :=
  (Finset.range (period X Q)).image (residue X Q)

/-- The ordinary diameter of the finite standard-residue orbit. -/
noncomputable def diameter (X Q : ℕ) : ℕ :=
  if h : (orbit X Q).Nonempty then
    (orbit X Q).max' h - (orbit X Q).min' h
  else 0

/-- Exponent of the directed gap at sorted index `i`. Subtraction takes
place in `ZMod r`, including at `i + 1 = r`. -/
def gapExponent (r u i : ℕ) : ℕ :=
  ((u : ZMod r) * ((i : ZMod r) + 1) - 1).val

/-- The prescribed maximum for the unit shift `s` with inverse `u` modulo `r`.
No orbit or narrowness predicate is used in this arithmetic definition. -/
def explicitNumerator (r s u : ℕ) : ℕ :=
  2 ^ (r - 1) + ∑ i ∈ Finset.range (s - 1), 2 ^ gapExponent r u i

/-- Strict positively oriented circular order, cut at zero. -/
private def CyclicBetween (a b c : ℤ) : Prop :=
  (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)

private theorem iterate_double (X Q n : ℕ) :
    (fun z : ZMod X => 2 * z)^[n] (Q : ZMod X) =
      (2 : ZMod X) ^ n * (Q : ZMod X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    ring

private theorem residue_eq_val (X Q n : ℕ) :
    residue X Q n = ((2 : ZMod X) ^ n * (Q : ZMod X)).val := by
  have hc : ((2 ^ n * Q : ℕ) : ZMod X) =
      (2 : ZMod X) ^ n * (Q : ZMod X) := by push_cast; rfl
  rw [residue, ← hc, ZMod.val_natCast]

private theorem residue_cast (X Q n : ℕ) :
    (residue X Q n : ℤ) = ((2 : ℤ) ^ n * (Q : ℤ)) % (X : ℤ) := by
  simp only [residue, Int.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

private theorem periodic_iff_modEq (X Q n : ℕ) :
    Function.IsPeriodicPt (fun z : ZMod X => 2 * z) n (Q : ZMod X) ↔
      Nat.ModEq X (2 ^ n * Q) Q := by
  change (fun z : ZMod X => 2 * z)^[n] (Q : ZMod X) = (Q : ZMod X) ↔ _
  rw [iterate_double]
  have hc : ((2 ^ n * Q : ℕ) : ZMod X) =
      (2 : ZMod X) ^ n * (Q : ZMod X) := by push_cast; rfl
  rw [← hc, ZMod.natCast_eq_natCast_iff]

/-- Cancel exactly the gcd, rather than assuming that Q is a unit. -/
private theorem periodic_iff_reduced {X : ℕ} (hX : 0 < X) (Q n : ℕ) :
    Function.IsPeriodicPt (fun z : ZMod X => 2 * z) n (Q : ZMod X) ↔
      (2 : ZMod (denominator X Q)) ^ n = 1 := by
  have hz : ((2 : ZMod (denominator X Q)) ^ n = 1) ↔
      Nat.ModEq (denominator X Q) (2 ^ n) 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (2 ^ n) 1 (denominator X Q))
  rw [periodic_iff_modEq, hz]
  constructor
  · intro h
    have h' : Nat.ModEq X (2 ^ n * Q) (1 * Q) := by simpa using h
    exact h'.cancel_right_div_gcd hX
  · intro h
    have h' := (h.mul_right (Q / Nat.gcd X Q)).mul_right' (Nat.gcd X Q)
    simpa only [denominator, Nat.mul_assoc,
      Nat.div_mul_cancel (Nat.gcd_dvd_left X Q),
      Nat.div_mul_cancel (Nat.gcd_dvd_right X Q), one_mul] using h'

private theorem period_eq_order {X : ℕ} (hX : 0 < X) (Q : ℕ) :
    period X Q = orderOf (2 : ZMod (denominator X Q)) := by
  unfold period orderOf
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  rw [periodic_iff_reduced hX, isPeriodicPt_mul_iff_pow_eq_one]

private theorem period_pos {X : ℕ} (hX : 0 < X) (hodd : Odd X) (Q : ℕ) :
    0 < period X Q := by
  let : NeZero X := ⟨Nat.ne_of_gt hX⟩
  have hu : IsUnit (2 : ZMod X) :=
    (ZMod.isUnit_iff_coprime 2 X).mpr (Nat.coprime_two_left.mpr hodd)
  exact Function.minimalPeriod_pos_of_mem_periodicPts
    (hu.mul_right_injective.mem_periodicPts (Q : ZMod X))

private theorem denominator_gt_one {X Q : ℕ} (hQ : 0 < Q) (hQX : Q < X) :
    1 < denominator X Q := by
  have hgQ : Nat.gcd X Q ≤ Q := Nat.le_of_dvd hQ (Nat.gcd_dvd_right X Q)
  have hg : 0 < Nat.gcd X Q := Nat.gcd_pos_of_pos_left Q (by omega)
  have he : denominator X Q * Nat.gcd X Q = X :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left X Q)
  by_contra h
  have hd : denominator X Q ≤ 1 := by omega
  have hm := Nat.mul_le_mul_right (Nat.gcd X Q) hd
  omega

private theorem period_ge_two {X Q : ℕ} (hX : 0 < X) (hodd : Odd X)
    (hQ : 0 < Q) (hQX : Q < X) : 2 ≤ period X Q := by
  have hr := period_pos hX hodd Q
  have hD := denominator_gt_one hQ hQX
  by_contra h
  have he : period X Q = 1 := by omega
  have hp := Function.isPeriodicPt_minimalPeriod
    (fun z : ZMod X => 2 * z) (Q : ZMod X)
  change Function.IsPeriodicPt (fun z : ZMod X => 2 * z) (period X Q)
    (Q : ZMod X) at hp
  rw [he, periodic_iff_reduced hX] at hp
  have hc : Nat.ModEq (denominator X Q) 1 2 := by
    have hc' := (ZMod.natCast_eq_natCast_iff 2 1 (denominator X Q)).mp
      (by simpa using hp)
    exact hc'.symm
  have hd : denominator X Q ∣ 1 := by
    simpa using (Nat.modEq_iff_dvd' (by omega : 1 ≤ 2)).mp hc
  have := Nat.le_of_dvd (by omega : 0 < 1) hd
  omega

private theorem residue_mod_period (X Q n : ℕ) :
    residue X Q (n % period X Q) = residue X Q n := by
  rw [residue_eq_val, residue_eq_val, ← iterate_double, ← iterate_double]
  exact congrArg ZMod.val
    (Function.iterate_mod_minimalPeriod_eq
      (f := fun z : ZMod X => 2 * z) (x := (Q : ZMod X)) (n := n))

private theorem residue_zero {X Q : ℕ} (hQX : Q < X) : residue X Q 0 = Q := by
  simp [residue, Nat.mod_eq_of_lt hQX]

private theorem residue_return {X Q : ℕ} (hQX : Q < X) :
    residue X Q (period X Q) = Q := by
  have h := residue_mod_period X Q (period X Q)
  simpa [residue_zero hQX] using h.symm

private theorem residue_injective (X Q : ℕ) :
    Set.InjOn (residue X Q) (Set.Iio (period X Q)) := by
  intro i hi j hj hij
  apply Function.iterate_injOn_Iio_minimalPeriod
    (f := fun z : ZMod X => 2 * z) (x := (Q : ZMod X)) hi hj
  change (fun z : ZMod X => 2 * z)^[i] (Q : ZMod X) =
    (fun z : ZMod X => 2 * z)^[j] (Q : ZMod X)
  rw [iterate_double, iterate_double]
  have h : Nat.ModEq X (2 ^ i * Q) (2 ^ j * Q) := hij
  have h' := (ZMod.natCast_eq_natCast_iff _ _ X).mpr h
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h'

private theorem orbit_nonempty {X : ℕ} (hX : 0 < X) (hodd : Odd X) (Q : ℕ) :
    (orbit X Q).Nonempty := by
  exact ⟨residue X Q 0, Finset.mem_image.mpr
    ⟨0, Finset.mem_range.mpr (period_pos hX hodd Q), rfl⟩⟩

private theorem orbit_card (X Q : ℕ) : (orbit X Q).card = period X Q := by
  unfold orbit
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range _
  · intro i hi j hj hij
    exact residue_injective X Q (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

/-- Actual sorted point; this preserves the original cut at zero. -/
private noncomputable def sortedPoint (X Q : ℕ) : Fin (period X Q) ↪o ℕ :=
  (orbit X Q).orderEmbOfFin (orbit_card X Q)

/-- Positive circular adjacent gap, with X added only at the last index. -/
private noncomputable def directedGap (X Q : ℕ) (i : Fin (period X Q)) : ℤ :=
  (sortedPoint X Q (cycAdd i 1) : ℤ) - sortedPoint X Q i +
    if i.val + 1 < period X Q then 0 else (X : ℤ)

private theorem residue_mem_orbit {X : ℕ} (hX : 0 < X) (hodd : Odd X)
    (Q n : ℕ) : residue X Q n ∈ orbit X Q := by
  apply Finset.mem_image.mpr
  exact ⟨n % period X Q,
    Finset.mem_range.mpr (Nat.mod_lt _ (period_pos hX hodd Q)),
    residue_mod_period X Q n⟩

/-- A consecutive block of the actual period covers every phase.
The finite-index arithmetic is reused from AssociatedMersenne.CircularWords. -/
private theorem phase_block_covers {X : ℕ} (hX : 0 < X) (hodd : Odd X)
    (Q phase n : ℕ) : ∃ j < period X Q,
      residue X Q (phase + j) = residue X Q n := by
  have hr := period_pos hX hodd Q
  let p : Fin (period X Q) := ⟨phase % period X Q, Nat.mod_lt _ hr⟩
  obtain ⟨j, hj⟩ := (cycAdd_bijective p).2
    ⟨n % period X Q, Nat.mod_lt _ hr⟩
  have he : (phase + j.val) % period X Q = n % period X Q := by
    have hv := congrArg Fin.val hj
    change (phase % period X Q + j.val) % period X Q = n % period X Q at hv
    simpa only [Nat.mod_add_mod] using hv
  refine ⟨j.val, j.isLt, ?_⟩
  rw [← residue_mod_period X Q (phase + j.val), he, residue_mod_period]

private theorem diameter_le_of_interval {X Q L U : ℕ}
    (hne : (orbit X Q).Nonempty)
    (hb : ∀ z ∈ orbit X Q, L ≤ z ∧ z ≤ U) :
    diameter X Q ≤ U - L := by
  have hmax := (hb _ ((orbit X Q).max'_mem hne)).2
  have hmin := (hb _ ((orbit X Q).min'_mem hne)).1
  unfold diameter
  rw [dite_eq_left hne]
  omega

/-- On any interval of span less than X/2, doubling followed by reduction
preserves strict circular order. The two branches are derived from bounds. -/
private theorem narrow_cyclic_order {X L U a b c : ℤ}
    (_hX : 0 < X) (hL : 0 ≤ L) (hU : U < X) (hW : 2 * (U - L) < X)
    (ha : L ≤ a ∧ a ≤ U) (hb : L ≤ b ∧ b ≤ U) (hc : L ≤ c ∧ c ≤ U) :
    CyclicBetween ((2 * a) % X) ((2 * b) % X) ((2 * c) % X) ↔
      CyclicBetween a b c := by
  have branch (z : ℤ) (hz : L ≤ z ∧ z ≤ U) :
      (2 * z) % X = if 2 * z < X then 2 * z else 2 * z - X := by
    split_ifs with hzX
    · exact Int.emod_eq_of_lt (by omega) hzX
    · have he : (2 * z) % X = (2 * z - X) % X := by
        simp only [Int.sub_emod_right]
      rw [he]
      exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [branch a ha, branch b hb, branch c hc]
  unfold CyclicBetween
  split_ifs <;> omega

/-- Exact algebraic old-height hypotheses on one consecutive layer block.
This is an interface for necessary conditions, not physical realizability. -/
def HeightBlock (X Q k m₀ r : ℕ) (H : ℕ → ℤ) : Prop :=
  ∀ j < r, 0 ≤ H (m₀ + j) ∧
    2 * H (m₀ + j) ≤ (X : ℤ) - 1 ∧
    Int.ModEq (X : ℤ) (H (m₀ + j))
      ((Q : ℤ) - (2 : ℤ) ^ (k + (m₀ + j)) * (Q : ℤ))

private theorem height_identifies_residue {X Q k m₀ j : ℕ} {H : ℕ → ℤ}
    (hQ : (X : ℤ) + 1 ≤ 2 * (Q : ℤ)) (hQX : Q < X)
    (hh : 0 ≤ H (m₀ + j) ∧ 2 * H (m₀ + j) ≤ (X : ℤ) - 1 ∧
      Int.ModEq (X : ℤ) (H (m₀ + j))
        ((Q : ℤ) - (2 : ℤ) ^ (k + (m₀ + j)) * (Q : ℤ))) :
    (residue X Q (k + (m₀ + j)) : ℤ) = (Q : ℤ) - H (m₀ + j) := by
  have hb : 0 ≤ (Q : ℤ) - H (m₀ + j) ∧ (Q : ℤ) - H (m₀ + j) < X := by
    have : (Q : ℤ) < X := by exact_mod_cast hQX
    omega
  have he := hh.2.2.sub_left (Q : ℤ)
  have he' : Int.ModEq (X : ℤ) ((Q : ℤ) - H (m₀ + j))
      ((2 : ℤ) ^ (k + (m₀ + j)) * (Q : ℤ)) := by
    have hcancel : (Q : ℤ) - ((Q : ℤ) -
        (2 : ℤ) ^ (k + (m₀ + j)) * (Q : ℤ)) =
        (2 : ℤ) ^ (k + (m₀ + j)) * (Q : ℤ) := by ring
    rw [hcancel] at he
    exact he
  rw [residue_cast]
  change ((Q : ℤ) - H (m₀ + j)) % X =
    ((2 : ℤ) ^ (k + (m₀ + j)) * (Q : ℤ)) % X at he'
  exact he'.symm.trans (Int.emod_eq_of_lt hb.1 hb.2)

/-- A fixed nonterminal Q on ONE consecutive actual-period block forces the
whole standard orbit into [Q-(X-1)/2,Q], with Q its maximum and narrow diameter.
This is the finite-horizon reduction consumed by the later classification
consumer, with no physical-realization assertion. -/
private theorem block_narrow_data {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : (X : ℤ) + 1 ≤ 2 * (Q : ℤ)) (hQX : Q < X)
    (k m₀ : ℕ) (H : ℕ → ℤ)
    (hblock : HeightBlock X Q k m₀ (period X Q) H) :
    2 ≤ period X Q ∧
    period X Q = orderOf (2 : ZMod (denominator X Q)) ∧
    (∀ n : ℕ, 1 ≤ residue X Q n ∧
      Q - (X - 1) / 2 ≤ residue X Q n ∧ residue X Q n ≤ Q) ∧
    (∀ z ∈ orbit X Q, z ≤ Q) ∧ Q ∈ orbit X Q ∧
    2 * diameter X Q < X := by
  have hXp : 0 < X := by omega
  have hQp : 0 < Q := by
    have : (0 : ℤ) < Q := by omega
    exact_mod_cast this
  have hne := orbit_nonempty hXp hodd Q
  have hall (n : ℕ) : 1 ≤ residue X Q n ∧
      Q - (X - 1) / 2 ≤ residue X Q n ∧ residue X Q n ≤ Q := by
    obtain ⟨j, hj, he⟩ := phase_block_covers hXp hodd Q (k + m₀) n
    have hh := hblock j hj
    have hid := height_identifies_residue hQ hQX hh
    have hexp : k + (m₀ + j) = k + m₀ + j := by omega
    rw [hexp, he] at hid
    have hdiv := Nat.mod_add_div (X - 1) 2
    have hmod := Nat.mod_lt (X - 1) (by omega : 0 < 2)
    have hcast : ((X - 1 : ℕ) : ℤ) = (X : ℤ) - 1 := by omega
    have hfloor : H (m₀ + j) ≤ ((X - 1) / 2 : ℕ) := by
      have hdiv' : ((X - 1 : ℕ) : ℤ) =
          ((X - 1) % 2 : ℕ) + 2 * (((X - 1) / 2 : ℕ) : ℤ) := by
        exact_mod_cast hdiv.symm
      omega
    omega
  have hinterval : ∀ z ∈ orbit X Q,
      Q - (X - 1) / 2 ≤ z ∧ z ≤ Q := by
    intro z hz
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
    exact (hall n).2
  have hdiam := diameter_le_of_interval hne hinterval
  have hU : 2 * ((X - 1) / 2) < X := by omega
  have hQmem : Q ∈ orbit X Q := by
    simpa only [residue_zero hQX] using residue_mem_orbit hXp hodd Q 0
  exact ⟨period_ge_two hXp hodd hQp hQX, period_eq_order hXp Q, hall,
    fun z hz => (hinterval z hz).2, hQmem, by omega⟩

/-- The geometric circular-order part is derived from narrowness for the
actual arbitrary-modulus orbit. The later sorted-shift and gap proofs consume
this geometric argument. -/
private theorem narrow_orbit_preserves_cyclic_order {X Q : ℕ}
    (hX : 3 ≤ X) (hodd : Odd X) (hnarrow : 2 * diameter X Q < X)
    {a b c : ℕ} (ha : a ∈ orbit X Q) (hb : b ∈ orbit X Q)
    (hc : c ∈ orbit X Q) :
    CyclicBetween ((2 * (a : ℤ)) % X) ((2 * (b : ℤ)) % X)
      ((2 * (c : ℤ)) % X) ↔ CyclicBetween a b c := by
  have hXp : 0 < X := by omega
  have hne := orbit_nonempty hXp hodd Q
  let L := (orbit X Q).min' hne
  let U := (orbit X Q).max' hne
  have hbds (z : ℕ) (hz : z ∈ orbit X Q) : L ≤ z ∧ z ≤ U :=
    ⟨(orbit X Q).min'_le z hz, (orbit X Q).le_max' z hz⟩
  have hLU : L ≤ U := (orbit X Q).min'_le_max' hne
  have hUX : U < X := by
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp ((orbit X Q).max'_mem hne)
    change (orbit X Q).max' hne < X
    rw [← hn]
    exact Nat.mod_lt _ hXp
  have hW : 2 * ((U : ℤ) - L) < X := by
    have hd : diameter X Q = U - L := by
      simp only [diameter, dite_eq_left hne, U, L]
    rw [hd] at hnarrow
    omega
  exact narrow_cyclic_order (by exact_mod_cast hXp) (by positivity)
    (by exact_mod_cast hUX) hW
    (by exact_mod_cast hbds a ha) (by exact_mod_cast hbds b hb)
    (by exact_mod_cast hbds c hc)

private theorem circular_successor_iff {r : ℕ} (hr : 2 ≤ r) (i j : Fin r) :
    (i ≠ j ∧ ∀ k : Fin r, ¬ CyclicBetween i.val k.val j.val) ↔
      j = cycAdd i 1 := by
  have hn : (cycAdd i 1).val = if i.val + 1 < r then i.val + 1 else 0 := by
    rw [cycAdd_val]
    split_ifs with hi
    · exact Nat.mod_eq_of_lt hi
    · have he : i.val + 1 = r := by omega
      rw [he, Nat.mod_self]
  constructor
  · rintro ⟨hne, hnone⟩
    apply Fin.ext
    rw [hn]
    have hne' : i.val ≠ j.val := fun he => hne (Fin.ext he)
    split_ifs with hi
    · let k : Fin r := ⟨i.val + 1, hi⟩
      have hnot := hnone k
      have hk : k.val = i.val + 1 := rfl
      unfold CyclicBetween at hnot
      omega
    · let k : Fin r := ⟨0, by omega⟩
      have hnot := hnone k
      have hk : k.val = 0 := rfl
      unfold CyclicBetween at hnot
      omega
  · rintro rfl
    constructor
    · intro he
      have hv := congrArg Fin.val he
      rw [hn] at hv
      split_ifs at hv <;> omega
    · intro k hk
      unfold CyclicBetween at hk
      split_ifs at hn <;> omega

/-- An order-preserving circular permutation is a rotation. This proves the
index-shift step, using the existing cycAdd arithmetic throughout. -/
private theorem cyclic_perm_is_shift {r : ℕ} (hr : 2 ≤ r)
    (p : Equiv.Perm (Fin r))
    (horder : ∀ i j k : Fin r,
      CyclicBetween (p i).val (p j).val (p k).val ↔ CyclicBetween i.val j.val k.val) :
    ∃ s : Fin r, ∀ i : Fin r, p i = cycAdd s i.val := by
  have hcomm (i : Fin r) : p (cycAdd i 1) = cycAdd (p i) 1 := by
    have hi := (circular_successor_iff hr i (cycAdd i 1)).mpr rfl
    apply (circular_successor_iff hr (p i) (p (cycAdd i 1))).mp
    refine ⟨fun he => hi.1 (p.injective he), ?_⟩
    intro k hk
    have hpre : CyclicBetween i.val (p.symm k).val (cycAdd i 1).val := by
      apply (horder i (p.symm k) (cycAdd i 1)).mp
      simpa only [p.apply_symm_apply] using hk
    exact hi.2 _ hpre
  let z : Fin r := ⟨0, by omega⟩
  have hall (n : ℕ) : ∀ hn : n < r, p ⟨n, hn⟩ = cycAdd (p z) n := by
    induction n with
    | zero =>
      intro hn
      rw [cycAdd_zero]
    | succ n ih =>
      intro hn
      let i : Fin r := ⟨n, by omega⟩
      have hnext : cycAdd i 1 = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        rw [cycAdd_val]
        exact Nat.mod_eq_of_lt hn
      calc
        p ⟨n + 1, hn⟩ = p (cycAdd i 1) := congrArg p hnext.symm
        _ = cycAdd (p i) 1 := hcomm i
        _ = cycAdd (cycAdd (p z) n) 1 := by rw [ih i.isLt]
        _ = cycAdd (p z) (n + 1) := cycAdd_assoc (p z) n 1
  exact ⟨p z, fun i => hall i.val i.isLt⟩

private theorem residue_succ (X Q n : ℕ) :
    residue X Q (n + 1) = (2 * residue X Q n) % X := by
  have he : 2 ^ (n + 1) * Q = 2 * (2 ^ n * Q) := by rw [pow_succ]; ring
  simp only [residue, he, Nat.mul_mod, Nat.mod_mod]

private theorem orbit_lt {X : ℕ} (hX : 0 < X) (Q z : ℕ)
    (hz : z ∈ orbit X Q) : z < X := by
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
  exact Nat.mod_lt _ hX

private theorem double_mem_orbit {X : ℕ} (hX : 0 < X) (hodd : Odd X)
    (Q z : ℕ) (hz : z ∈ orbit X Q) : (2 * z) % X ∈ orbit X Q := by
  obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
  rw [← residue_succ]
  exact residue_mem_orbit hX hodd Q (n + 1)

/-- Sorting the actual orbit turns doubling into one cyclic index shift.
The shift is derived from narrowness, with no unit-seed assumption.
The subsequent source transfers the actual temporal cycle to these indices
and connects it to the directed gap recurrence. -/
private theorem narrow_doubling_sorted_shift {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : 0 < Q) (hQX : Q < X) (hnarrow : 2 * diameter X Q < X) :
    ∃ s : Fin (period X Q), ∀ i : Fin (period X Q),
      (orbit X Q).orderEmbOfFin (orbit_card X Q) (cycAdd s i.val) =
        (2 * (orbit X Q).orderEmbOfFin (orbit_card X Q) i) % X := by
  classical
  have hXp : 0 < X := by omega
  let S := orbit X Q
  let e : Fin (period X Q) ≃o S := S.orderIsoOfFin (orbit_card X Q)
  let a : Fin (period X Q) ↪o ℕ := S.orderEmbOfFin (orbit_card X Q)
  let T : S → S := fun z =>
    ⟨(2 * z.val) % X, double_mem_orbit hXp hodd Q z.val z.property⟩
  have hT : Function.Injective T := by
    intro z w he
    apply Subtype.ext
    have hmod : Nat.ModEq X (2 * z.val) (2 * w.val) :=
      congrArg Subtype.val he
    have he' := hmod.cancel_left_of_coprime
      (Nat.coprime_two_right.mpr hodd).gcd_eq_one
    exact he'.eq_of_lt_of_lt (orbit_lt hXp Q z.val z.property)
      (orbit_lt hXp Q w.val w.property)
  let t : Equiv.Perm S := Equiv.ofBijective T ⟨hT, Finite.surjective_of_injective hT⟩
  let p : Equiv.Perm (Fin (period X Q)) :=
    e.toEquiv.trans (t.trans e.toEquiv.symm)
  have hp (i : Fin (period X Q)) : a (p i) = (2 * a i) % X := by
    change (e (e.symm (T (e i)))).val = (2 * (e i).val) % X
    rw [e.apply_symm_apply]
  have hpi (i : Fin (period X Q)) : (a (p i) : ℤ) = (2 * (a i : ℤ)) % X := by
    simpa only [Int.natCast_mod, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun z : ℕ => (z : ℤ)) (hp i)
  have hlt (i j : Fin (period X Q)) :
      ((a i : ℕ) : ℤ) < a j ↔ (i.val : ℤ) < j.val := by
    have hn : a i < a j ↔ i.val < j.val := a.lt_iff_lt
    exact_mod_cast hn
  have hcirc (i j k : Fin (period X Q)) :
      CyclicBetween (a i) (a j) (a k) ↔ CyclicBetween i.val j.val k.val := by
    simp only [CyclicBetween, hlt]
  have horder (i j k : Fin (period X Q)) :
      CyclicBetween (p i).val (p j).val (p k).val ↔ CyclicBetween i.val j.val k.val := by
    rw [← hcirc, hpi, hpi, hpi]
    exact (narrow_orbit_preserves_cyclic_order hX hodd hnarrow
      (S.orderEmbOfFin_mem (orbit_card X Q) i)
      (S.orderEmbOfFin_mem (orbit_card X Q) j)
      (S.orderEmbOfFin_mem (orbit_card X Q) k)).trans (hcirc i j k)
  obtain ⟨s, hs⟩ := cyclic_perm_is_shift (period_ge_two hXp hodd hQ hQX) p horder
  refine ⟨s, ?_⟩
  intro i
  change a (cycAdd s i.val) = (2 * a i) % X
  rw [← hs i]
  exact hp i

/-- Transfer the actual temporal orbit to any sorted-index doubling map.
The cycle, its return, and the absence of an earlier return are derived;
none of these is an additional hypothesis about the sorted shift.
 -/
private theorem sorted_doubling_actual_cycle {X Q : ℕ}
    (hX : 0 < X) (hodd : Odd X)
    (p : Fin (period X Q) → Fin (period X Q))
    (hstep : ∀ i : Fin (period X Q),
      (orbit X Q).orderEmbOfFin (orbit_card X Q) (p i) =
        (2 * (orbit X Q).orderEmbOfFin (orbit_card X Q) i) % X) :
    (∀ i j, ∃ n < period X Q, p^[n] i = j) ∧
    (∀ i, p^[period X Q] i = i) ∧
    (∀ i n, 0 < n → n < period X Q → p^[n] i ≠ i) := by
  let a := (orbit X Q).orderEmbOfFin (orbit_card X Q)
  have hr := period_pos hX hodd Q
  have hphase (i : Fin (period X Q)) :
      ∃ m < period X Q, a i = residue X Q m := by
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp
      ((orbit X Q).orderEmbOfFin_mem (orbit_card X Q) i)
    exact ⟨m, Finset.mem_range.mp hm, he.symm⟩
  have hiter (i : Fin (period X Q)) (m : ℕ)
      (hmi : a i = residue X Q m) (n : ℕ) :
      a (p^[n] i) = residue X Q (m + n) := by
    induction n with
    | zero => simpa only [Function.iterate_zero_apply, Nat.add_zero] using hmi
    | succ n ih =>
      rw [Function.iterate_succ_apply', hstep, ih, ← residue_succ]
      congr 1
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨m, _, hmi⟩ := hphase i
    obtain ⟨l, _, hlj⟩ := hphase j
    obtain ⟨n, hn, he⟩ := phase_block_covers hX hodd Q m l
    refine ⟨n, hn, a.injective ?_⟩
    exact (hiter i m hmi n).trans (he.trans hlj.symm)
  · intro i
    obtain ⟨m, _, hmi⟩ := hphase i
    apply a.injective
    calc
      a (p^[period X Q] i) = residue X Q (m + period X Q) :=
        hiter i m hmi (period X Q)
      _ = residue X Q m := by
        rw [← residue_mod_period X Q (m + period X Q)]
        simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
        exact residue_mod_period X Q m
      _ = a i := hmi.symm
  · intro i n hn hnr he
    obtain ⟨m, hm, hmi⟩ := hphase i
    have hv : residue X Q (m + n) = residue X Q m :=
      (hiter i m hmi n).symm.trans ((congrArg a he).trans hmi)
    have hmod : (m + n) % period X Q = m :=
      residue_injective X Q (Nat.mod_lt _ hr) hm
        ((residue_mod_period X Q (m + n)).trans hv)
    have hc : Nat.ModEq (period X Q) (m + n) (m + 0) := by
      change (m + n) % period X Q = (m + 0) % period X Q
      simpa only [Nat.add_zero, Nat.mod_eq_of_lt hm] using hmod
    have hn0 : Nat.ModEq (period X Q) n 0 := hc.add_left_cancel' m
    have hnz := hn0.eq_of_lt_of_lt hnr hr
    omega

/-- The derived sorted shift acts transitively on directed adjacent gaps:
the gap is indexed by its initial point, so the same index map acts on it.
This records the actual r-cycle before any numerical gap recurrence is used.
 -/
private theorem narrow_doubling_sorted_cycle {X Q : ℕ}
    (hX : 3 ≤ X) (hodd : Odd X) (hQ : 0 < Q) (hQX : Q < X)
    (hnarrow : 2 * diameter X Q < X) :
    ∃ s : Fin (period X Q),
      (∀ i : Fin (period X Q),
        (orbit X Q).orderEmbOfFin (orbit_card X Q) (cycAdd s i.val) =
          (2 * (orbit X Q).orderEmbOfFin (orbit_card X Q) i) % X) ∧
      (∀ i j : Fin (period X Q), ∃ n < period X Q,
        (fun v : Fin (period X Q) => cycAdd s v.val)^[n] i = j) ∧
      (∀ i : Fin (period X Q),
        (fun v : Fin (period X Q) => cycAdd s v.val)^[period X Q] i = i) ∧
      (∀ (i : Fin (period X Q)) (n : ℕ), 0 < n → n < period X Q →
        (fun v : Fin (period X Q) => cycAdd s v.val)^[n] i ≠ i) := by
  obtain ⟨s, hs⟩ := narrow_doubling_sorted_shift hX hodd hQ hQX hnarrow
  exact ⟨s, hs, sorted_doubling_actual_cycle (by omega) hodd
    (fun v => cycAdd s v.val) hs⟩

/-- Arithmetic of the already derived sorted shift. -/
private theorem shift_iterate_cast {r : ℕ} (hr : 0 < r) (s i : Fin r) (n : ℕ) :
    (((fun v : Fin r => cycAdd s v.val)^[n] i).val : ZMod r) =
      (i.val : ZMod r) + (n : ZMod r) * s.val := by
  letI : NeZero r := ⟨hr.ne'⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (((s.val + ((fun v : Fin r => cycAdd s v.val)^[n] i).val) % r : ℕ) :
      ZMod r) = _
    rw [ZMod.natCast_mod, Nat.cast_add, ih]
    push_cast
    ring

/-- Transitivity supplies a genuine modular inverse, rather than assuming one. -/
private theorem transitive_shift_inverse {r : ℕ} (hr : 2 ≤ r) (s : Fin r)
    (htrans : ∀ i j : Fin r, ∃ n < r,
      (fun v : Fin r => cycAdd s v.val)^[n] i = j) :
    0 < s.val ∧ Nat.Coprime s.val r ∧
      ∃ u < r, (s.val : ZMod r) * (u : ZMod r) = 1 := by
  letI : NeZero r := ⟨by omega⟩
  let z : Fin r := ⟨0, by omega⟩
  let o : Fin r := ⟨1, by omega⟩
  obtain ⟨u, hu, he⟩ := htrans z o
  have hc := shift_iterate_cast (by omega : 0 < r) s z u
  rw [he] at hc
  have hunit : (s.val : ZMod r) * (u : ZMod r) = 1 := by
    simpa [z, o, mul_comm] using hc.symm
  have hmod : Nat.ModEq r (s.val * u) 1 := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_mul, Nat.cast_one] using hunit
  have hs : 0 < s.val := by
    by_contra hn
    have hz : s.val = 0 := by omega
    have hc' := hmod.eq_of_lt_of_lt
      (by simp [hz]; omega) (by omega : 1 < r)
    simp [hz] at hc'
  exact ⟨hs, Nat.coprime_of_mul_modEq_one u hmod, u, hu, hunit⟩

/-- Inverting the actual shift identifies the exponent at each sorted gap.
The last gap corresponds to exponent r-1, without a natural-subtraction seam. -/
private theorem shift_gap_location {r u : ℕ} (hr : 0 < r) (s i : Fin r)
    (hu : (s.val : ZMod r) * (u : ZMod r) = 1) (hw : r - 1 < r) :
    (fun v : Fin r => cycAdd s v.val)^[gapExponent r u i.val + 1]
      ⟨r - 1, hw⟩ = i := by
  letI : NeZero r := ⟨hr.ne'⟩
  have hwcast : ((r - 1 : ℕ) : ZMod r) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), ZMod.natCast_self, Nat.cast_one]
    ring
  have he : (gapExponent r u i.val : ZMod r) =
      (u : ZMod r) * ((i.val : ZMod r) + 1) - 1 :=
    ZMod.natCast_zmod_val _
  have hcast := shift_iterate_cast hr s (⟨r - 1, hw⟩ : Fin r)
    (gapExponent r u i.val + 1)
  rw [hwcast, Nat.cast_add, Nat.cast_one, he] at hcast
  have heq : (((fun v : Fin r => cycAdd s v.val)^[gapExponent r u i.val + 1]
      ⟨r - 1, hw⟩).val : ZMod r) = (i.val : ZMod r) := by
    rw [hcast]
    calc
      -1 + ((u : ZMod r) * ((i.val : ZMod r) + 1) - 1 + 1) * s.val =
          ((s.val : ZMod r) * u) * ((i.val : ZMod r) + 1) - 1 := by ring
      _ = (i.val : ZMod r) := by rw [hu]; ring
  apply Fin.ext
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp heq).eq_of_lt_of_lt
    (Fin.isLt _) i.isLt

private theorem shift_commutes_successor {r : ℕ} (s i : Fin r) :
    cycAdd s (cycAdd i 1).val = cycAdd (cycAdd s i.val) 1 := by
  apply Fin.ext
  simp only [cycAdd_val, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

/-- Algebra along a genuine cycle, applied below to the derived actual gap
action. This is not a replacement hypothesis in the classification. -/
private theorem gap_cycle_growth {α : Type*} [DecidableEq α]
    (r : ℕ) (hr : 2 ≤ r) (p : α → α) (w : α) (G : α → ℤ) (X : ℤ)
    (hreturn : p^[r] w = w)
    (hearly : ∀ n, 0 < n → n < r → p^[n] w ≠ w)
    (hrec : ∀ i, G (p i) = if i = w then 2 * G i - X else 2 * G i) :
    X = ((2 ^ r - 1 : ℕ) : ℤ) * G (p w) ∧
      G w = (2 : ℤ) ^ (r - 1) * G (p w) ∧
      (∀ n < r, G (p^[n + 1] w) = (2 : ℤ) ^ n * G (p w)) := by
  have hwalk (n : ℕ) : n < r →
      G (p^[n + 1] w) = (2 : ℤ) ^ n * G (p w) := by
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Function.iterate_succ_apply', hrec,
        ite_eq_right (hearly (n + 1) (by omega) (by omega)), ih (by omega), pow_succ]
      ring
  have hlast := hwalk (r - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r), hreturn] at hlast
  have hfirst : G (p w) = 2 * G w - X := by simpa using hrec w
  have hpow : (2 : ℤ) ^ r = 2 * (2 : ℤ) ^ (r - 1) := by
    calc
      (2 : ℤ) ^ r = 2 ^ (r - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (r - 1) := by rw [pow_succ]; ring
  have hM : ((2 ^ r - 1 : ℕ) : ℤ) = (2 : ℤ) ^ r - 1 := by
    have hp : 0 < (2 : ℕ) ^ r := pow_pos (by omega) r
    rw [Nat.cast_sub (by omega : 1 ≤ (2 : ℕ) ^ r)]
    push_cast; rfl
  refine ⟨?_, hlast, hwalk⟩
  rw [hM, hpow]
  nlinarith [hlast, hfirst]

/-- Numerical gap data for the actual arbitrary-seed orbit. All geometric
and cycle hypotheses used in gap_cycle_growth are proved here from the
original narrowness hypothesis. -/
private theorem narrow_gap_arithmetic {X Q : ℕ}
    (hX : 3 ≤ X) (hodd : Odd X) (hQ : 0 < Q) (hQX : Q < X)
    (hnarrow : 2 * diameter X Q < X) :
    ∃ d : ℤ, 0 < d ∧ (Nat.gcd X Q : ℤ) ∣ d ∧
      (X : ℤ) = ((2 ^ period X Q - 1 : ℕ) : ℤ) * d ∧
      2 * (diameter X Q : ℤ) = (X : ℤ) - d ∧
      ∃ s : Fin (period X Q),
        (∀ i, sortedPoint X Q (cycAdd s i.val) = (2 * sortedPoint X Q i) % X) ∧
        (∀ i j, ∃ n < period X Q,
          (fun v : Fin (period X Q) => cycAdd s v.val)^[n] i = j) ∧
        (∀ n < period X Q, ∀ hw : period X Q - 1 < period X Q,
          directedGap X Q
            ((fun v : Fin (period X Q) => cycAdd s v.val)^[n + 1]
              ⟨period X Q - 1, hw⟩) = (2 : ℤ) ^ n * d) := by
  classical
  have hXp : 0 < X := by omega
  have hr := period_ge_two hXp hodd hQ hQX
  have hrp := period_pos hXp hodd Q
  have hne := orbit_nonempty hXp hodd Q
  obtain ⟨s, hs, htrans, hreturn, hearly⟩ :=
    narrow_doubling_sorted_cycle hX hodd hQ hQX hnarrow
  let r := period X Q
  let a : Fin r ↪o ℕ := (orbit X Q).orderEmbOfFin (orbit_card X Q)
  let p : Fin r → Fin r := fun i => cycAdd s i.val
  let next : Fin r → Fin r := fun i => cycAdd i 1
  let z : Fin r := ⟨0, hrp⟩
  let w : Fin r := ⟨r - 1, by dsimp [r]; omega⟩
  let G : Fin r → ℤ := fun i =>
    (a (next i) : ℤ) - a i + if i.val + 1 < r then 0 else (X : ℤ)
  have hz : a z = (orbit X Q).min' hne :=
    Finset.orderEmbOfFin_zero (orbit_card X Q) hrp
  have hw : a w = (orbit X Q).max' hne :=
    Finset.orderEmbOfFin_last (orbit_card X Q) hrp
  have hW : (diameter X Q : ℤ) = (a w : ℤ) - a z := by
    have hle : a z ≤ a w := a.monotone (by change 0 ≤ r - 1; omega)
    unfold diameter
    rw [dite_eq_left hne, ← hw, ← hz]
    omega
  have hWpos : 0 < (diameter X Q : ℤ) := by
    have hzw : z < w := by change 0 < r - 1; dsimp [r]; omega
    have hlt := a.strictMono hzw
    omega
  have hWnarrow : 2 * (diameter X Q : ℤ) < X := by exact_mod_cast hnarrow
  have hnextw : next w = z := by
    apply Fin.ext
    change (r - 1 + 1) % r = 0
    rw [Nat.sub_add_cancel (by dsimp [r]; omega : 1 ≤ r), Nat.mod_self]
  have hGwrap : G w = (X : ℤ) - diameter X Q := by
    change (a (next w) : ℤ) - a w +
      (if w.val + 1 < r then 0 else (X : ℤ)) = _
    rw [hnextw, ite_eq_right (by dsimp [w]; omega)]
    omega
  have hordinary (i : Fin r) (hi : i ≠ w) : 0 < G i ∧ 2 * G i < X := by
    have hi' : i.val + 1 < r := by
      have hv : i.val ≠ r - 1 := fun he => hi (Fin.ext he)
      have := i.isLt
      omega
    have hnv : (next i).val = i.val + 1 := Nat.mod_eq_of_lt hi'
    have hinc : a i < a (next i) :=
      a.strictMono (by change i.val < (next i).val; rw [hnv]; omega)
    have hlo : a z ≤ a i := a.monotone (by change 0 ≤ i.val; omega)
    have hhi : a (next i) ≤ a w := a.monotone (by
      change (next i).val ≤ r - 1
      have := (next i).isLt
      omega)
    have hGi : G i = (a (next i) : ℤ) - a i := by
      change (a (next i) : ℤ) - a i + (if i.val + 1 < r then 0 else (X : ℤ)) = _
      rw [ite_eq_left hi', add_zero]
    rw [hGi]
    omega
  have hbounds (i : Fin r) : 0 ≤ G i ∧ G i < X := by
    by_cases hi : i = w
    · rw [hi, hGwrap]
      omega
    · have ho := hordinary i hi
      omega
  have hcomm (i : Fin r) : p (next i) = next (p i) :=
    shift_commutes_successor s i
  have hpoint (i : Fin r) :
      Int.ModEq (X : ℤ) (a (p i)) (2 * (a i : ℤ)) := by
    have he : (a (p i) : ℤ) = (2 * (a i : ℤ)) % X := by
      simpa only [Int.natCast_mod, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun n : ℕ => (n : ℤ)) (hs i)
    change (a (p i) : ℤ) % X = (2 * (a i : ℤ)) % X
    rw [he, Int.emod_emod]
  have hgap (i : Fin r) :
      Int.ModEq (X : ℤ) (G i) ((a (next i) : ℤ) - a i) := by
    change ((a (next i) : ℤ) - a i +
      (if i.val + 1 < r then 0 else (X : ℤ))) % X = _
    split_ifs <;> simp only [add_zero, Int.add_emod, Int.emod_self, Int.emod_emod]
  have hdouble (i : Fin r) : Int.ModEq (X : ℤ) (G (p i)) (2 * G i) := by
    have he := (hpoint (next i)).sub (hpoint i)
    rw [hcomm i] at he
    have halg : 2 * (a (next i) : ℤ) - 2 * (a i : ℤ) =
        2 * ((a (next i) : ℤ) - a i) := by ring
    rw [halg] at he
    exact (hgap (p i)).trans (he.trans ((hgap i).mul_left 2).symm)
  have hrec (i : Fin r) :
      G (p i) = if i = w then 2 * G i - (X : ℤ) else 2 * G i := by
    have he := hdouble i
    change G (p i) % X = (2 * G i) % X at he
    rw [Int.emod_eq_of_lt (hbounds (p i)).1 (hbounds (p i)).2] at he
    by_cases hi : i = w
    · subst i
      rw [ite_eq_left rfl]
      calc
        G (p w) = (2 * G w) % X := he
        _ = (2 * G w - (X : ℤ)) % X := by simp only [Int.sub_emod_right]
        _ = 2 * G w - (X : ℤ) :=
          Int.emod_eq_of_lt (by rw [hGwrap]; omega) (by rw [hGwrap]; omega)
    · rw [ite_eq_right hi]
      exact he.trans (Int.emod_eq_of_lt (by have := hbounds i; omega)
        (hordinary i hi).2)
  have hprod := gap_cycle_growth r hr p w G X (hreturn w)
    (fun n hn hnr => hearly w n hn hnr) hrec
  have hd : G (p w) = (X : ℤ) - 2 * diameter X Q := by
    have he := hrec w
    rw [ite_eq_left rfl, hGwrap] at he
    omega
  have hgpoint (i : Fin r) : (Nat.gcd X Q : ℤ) ∣ (a i : ℤ) := by
    obtain ⟨n, _, he⟩ := Finset.mem_image.mp
      ((orbit X Q).orderEmbOfFin_mem (orbit_card X Q) i)
    have hg : Nat.gcd X Q ∣ residue X Q n :=
      (Nat.dvd_mod_iff (Nat.gcd_dvd_left X Q)).mpr
        (dvd_mul_of_dvd_right (Nat.gcd_dvd_right X Q) (2 ^ n))
    rw [he] at hg
    exact Int.natCast_dvd_natCast.mpr hg
  have hggap (i : Fin r) : (Nat.gcd X Q : ℤ) ∣ G i := by
    have hgX : (Nat.gcd X Q : ℤ) ∣ (X : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left X Q)
    change (Nat.gcd X Q : ℤ) ∣ (a (next i) : ℤ) - a i +
      (if i.val + 1 < r then 0 else (X : ℤ))
    apply dvd_add ((hgpoint (next i)).sub (hgpoint i))
    split_ifs
    · exact dvd_zero _
    · exact hgX
  refine ⟨G (p w), by omega, hggap (p w), hprod.1, by omega, s, hs, htrans, ?_⟩
  intro n hn hw
  exact hprod.2.2 n hn

/-- All-odd-modulus classification, including nonunit seeds.
Its source proof uses the actual sorted gap cycle; no transitivity,
recurrence, reduced-modulus classification, or unit-seed premise is added.
No physical or official acceptance is asserted. -/
theorem narrow_classification {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : 0 < Q) (hQX : Q < X) (hnarrow : 2 * diameter X Q < X) :
    2 ≤ period X Q ∧
    period X Q = orderOf (2 : ZMod (denominator X Q)) ∧
    denominator X Q = 2 ^ period X Q - 1 ∧
    2 * diameter X Q = X - Nat.gcd X Q := by
  have hXp : 0 < X := by omega
  have hr := period_ge_two hXp hodd hQ hQX
  have hg : 0 < Nat.gcd X Q := Nat.gcd_pos_of_pos_left Q hXp
  have hM : 0 < 2 ^ period X Q - 1 := by
    have hp : 1 < (2 : ℕ) ^ period X Q :=
      one_lt_pow' (by omega) (by omega)
    omega
  have hreturn := Function.isPeriodicPt_minimalPeriod
    (fun z : ZMod X => 2 * z) (Q : ZMod X)
  change Function.IsPeriodicPt (fun z : ZMod X => 2 * z) (period X Q)
    (Q : ZMod X) at hreturn
  have hpow := (periodic_iff_reduced hXp Q (period X Q)).mp hreturn
  have hcong : Nat.ModEq (denominator X Q) 1 (2 ^ period X Q) := by
    apply Nat.ModEq.symm
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hpow
  have hDM : denominator X Q ∣ 2 ^ period X Q - 1 :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ (2 : ℕ) ^ period X Q)).mp hcong
  obtain ⟨d, hdpos, hgdiv, hprod, hdiam, _⟩ :=
    narrow_gap_arithmetic hX hodd hQ hQX hnarrow
  obtain ⟨u, hu⟩ := hgdiv
  have hXD : Nat.gcd X Q * denominator X Q = X := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left X Q)
  have hXDZ : (Nat.gcd X Q : ℤ) * denominator X Q = (X : ℤ) := by
    exact_mod_cast hXD
  have hscale : (Nat.gcd X Q : ℤ) * denominator X Q =
      (Nat.gcd X Q : ℤ) * (((2 ^ period X Q - 1 : ℕ) : ℤ) * u) := by
    calc
      _ = (X : ℤ) := hXDZ
      _ = ((2 ^ period X Q - 1 : ℕ) : ℤ) * d := hprod
      _ = _ := by rw [hu]; ring
  have hD : (denominator X Q : ℤ) = ((2 ^ period X Q - 1 : ℕ) : ℤ) * u :=
    mul_left_cancel₀ (by exact_mod_cast hg.ne') hscale
  have hMD : 2 ^ period X Q - 1 ∣ denominator X Q :=
    Int.natCast_dvd_natCast.mp ⟨u, hD⟩
  have hDeq := Nat.dvd_antisymm hDM hMD
  have hcancel : ((2 ^ period X Q - 1 : ℕ) : ℤ) * d =
      ((2 ^ period X Q - 1 : ℕ) : ℤ) * Nat.gcd X Q := by
    rw [← hprod, ← hXDZ, hDeq]
    ring
  have hdg : d = (Nat.gcd X Q : ℤ) :=
    mul_left_cancel₀ (by exact_mod_cast hM.ne') hcancel
  rw [hdg] at hdiam
  exact ⟨hr, period_eq_order hXp Q, hDeq, by omega⟩

/-- Finite-horizon reduction: one consecutive block of
the actual period forces the entire fixed-Q orbit to be narrow and doubling
to be a transitive cyclic shift of its sorted points, with no early return.
The classification consumer is stated separately below. -/
theorem fixedQ_block_forces_narrow {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : (X : ℤ) + 1 ≤ 2 * (Q : ℤ)) (hQX : Q < X)
    (k m₀ : ℕ) (H : ℕ → ℤ)
    (hblock : HeightBlock X Q k m₀ (period X Q) H) :
    2 ≤ period X Q ∧
    period X Q = orderOf (2 : ZMod (denominator X Q)) ∧
    (∀ n : ℕ, 1 ≤ residue X Q n ∧
      Q - (X - 1) / 2 ≤ residue X Q n ∧ residue X Q n ≤ Q) ∧
    (∀ z ∈ orbit X Q, z ≤ Q) ∧ Q ∈ orbit X Q ∧
    2 * diameter X Q < X ∧
    ∃ s : Fin (period X Q),
      (∀ i : Fin (period X Q),
        (orbit X Q).orderEmbOfFin (orbit_card X Q) (cycAdd s i.val) =
          (2 * (orbit X Q).orderEmbOfFin (orbit_card X Q) i) % X) ∧
      (∀ i j : Fin (period X Q), ∃ n < period X Q,
        (fun v : Fin (period X Q) => cycAdd s v.val)^[n] i = j) ∧
      (∀ i : Fin (period X Q),
        (fun v : Fin (period X Q) => cycAdd s v.val)^[period X Q] i = i) ∧
      (∀ (i : Fin (period X Q)) (n : ℕ), 0 < n → n < period X Q →
        (fun v : Fin (period X Q) => cycAdd s v.val)^[n] i ≠ i) := by
  obtain ⟨hr, hord, hall, hmax, hmem, hnarrow⟩ :=
    block_narrow_data hX hodd hQ hQX k m₀ H hblock
  have hQp : 0 < Q := by
    have : (0 : ℤ) < Q := by omega
    exact_mod_cast this
  exact ⟨hr, hord, hall, hmax, hmem, hnarrow,
    narrow_doubling_sorted_cycle hX hodd hQp hQX hnarrow⟩

/-- A nontrivial Mersenne divisor produces SOME abstract narrow orbit of
exactly the specified least period. Q is chosen here; the assertion is not
a sufficient criterion for a prescribed Q, and has no physical conclusion. -/
theorem exists_narrow_of_mersenne_dvd {X t : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (ht : 2 ≤ t) (hdiv : 2 ^ t - 1 ∣ X) :
    ∃ Q : ℕ, 0 < Q ∧ Q < X ∧ period X Q = t ∧
      (orbit X Q).card = t ∧ 2 * diameter X Q = X - Q ∧
      2 * diameter X Q < X := by
  let M : ℕ := 2 ^ t - 1
  let g : ℕ := X / M
  have hpow : 4 ≤ 2 ^ t := by
    simpa using pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) ht
  have hM : 3 ≤ M := by dsimp [M]; omega
  have hMg : M * g = X := Nat.mul_div_cancel' hdiv
  have hg : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have he := hMg
    rw [hzero, mul_zero] at he
    omega
  have hgX : g < X := by
    calc
      g = 1 * g := by omega
      _ < M * g := Nat.mul_lt_mul_of_pos_right (by omega : 1 < M) hg
      _ = X := hMg
  have hpred : 2 ≤ 2 ^ (t - 1) := by
    simpa using pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ))
      (show 1 ≤ t - 1 by omega)
  have hpowstep : 2 ^ t = 2 ^ (t - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hpredM : 2 ^ (t - 1) < M := by dsimp [M]; omega
  have hshort (n : ℕ) (hn : n < t) : residue X g n = g * 2 ^ n := by
    have hp := pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ))
      (show n ≤ t - 1 by omega)
    have hlt : g * 2 ^ n < X := by
      calc
        g * 2 ^ n ≤ g * 2 ^ (t - 1) := Nat.mul_le_mul_left g hp
        _ < g * M := Nat.mul_lt_mul_of_pos_left hpredM hg
        _ = X := by simpa only [Nat.mul_comm] using hMg
    unfold residue
    rw [Nat.mul_comm (2 ^ n), Nat.mod_eq_of_lt hlt]
  have hreturn : residue X g t = g := by
    have hprod : 2 ^ t * g = X + g := by
      have he : 2 ^ t = M + 1 := by dsimp [M]; omega
      calc
        2 ^ t * g = (M + 1) * g := congrArg (fun z : ℕ => z * g) he
        _ = M * g + g := by ring
        _ = X + g := by rw [hMg]
    simp only [residue, hprod, Nat.add_mod, Nat.mod_self, zero_add,
      Nat.mod_eq_of_lt hgX]
  have hrp := period_pos (by omega : 0 < X) hodd g
  have hret : Function.IsPeriodicPt (fun z : ZMod X => 2 * z) t (g : ZMod X) := by
    apply (periodic_iff_modEq X g t).mpr
    change residue X g t = g % X
    rw [hreturn, Nat.mod_eq_of_lt hgX]
  have hrle : period X g ≤ t := hret.minimalPeriod_le (by omega)
  have hr : period X g = t := by
    by_contra hne
    have hlt : period X g < t := by omega
    have he := residue_return hgX
    rw [hshort _ hlt] at he
    have hp : 1 < 2 ^ period X g :=
      one_lt_pow' (by omega : 1 < (2 : ℕ)) (Nat.ne_of_gt hrp)
    have hgt : g < g * 2 ^ period X g := by
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp hg
    omega
  have hne := orbit_nonempty (by omega : 0 < X) hodd g
  have hall (z : ℕ) (hz : z ∈ orbit X g) :
      g ≤ z ∧ z ≤ g * 2 ^ (t - 1) := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    have hnt : n < t := by simpa only [hr] using Finset.mem_range.mp hn
    rw [hshort n hnt]
    have hp : 0 < 2 ^ n := pow_pos (by omega : 0 < (2 : ℕ)) n
    have hp' := pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ))
      (show n ≤ t - 1 by omega)
    constructor
    · simpa only [mul_one] using
        Nat.mul_le_mul_left g (show 1 ≤ 2 ^ n by omega)
    · exact Nat.mul_le_mul_left g hp'
  have hminmem : g ∈ orbit X g := by
    simpa only [residue_zero hgX] using
      residue_mem_orbit (by omega : 0 < X) hodd g 0
  have hmaxmem : g * 2 ^ (t - 1) ∈ orbit X g := by
    rw [← hshort (t - 1) (by omega)]
    exact residue_mem_orbit (by omega : 0 < X) hodd g (t - 1)
  have hmin : (orbit X g).min' hne = g := by
    apply le_antisymm
    · exact (orbit X g).min'_le g hminmem
    · exact (hall _ ((orbit X g).min'_mem hne)).1
  have hmax : (orbit X g).max' hne = g * 2 ^ (t - 1) := by
    apply le_antisymm
    · exact (hall _ ((orbit X g).max'_mem hne)).2
    · exact (orbit X g).le_max' _ hmaxmem
  have hdiam : 2 * diameter X g = X - g := by
    unfold diameter
    rw [dite_eq_left hne, hmax, hmin]
    have hgp : g ≤ g * 2 ^ (t - 1) := by
      simpa only [mul_one] using
        Nat.mul_le_mul_left g (show 1 ≤ 2 ^ (t - 1) by omega)
    have hsub : g * 2 ^ (t - 1) - g + g = g * 2 ^ (t - 1) :=
      Nat.sub_add_cancel hgp
    have hsubX : X - g + g = X := Nat.sub_add_cancel (by omega)
    have hMstep : M + 1 = 2 * 2 ^ (t - 1) := by dsimp [M]; omega
    have hscaled : 2 * (g * 2 ^ (t - 1)) = X + g := by
      calc
        2 * (g * 2 ^ (t - 1)) = g * (M + 1) := by rw [hMstep]; ring
        _ = M * g + g := by ring
        _ = X + g := by rw [hMg]
    omega
  exact ⟨g, hg, hgX, hr, (orbit_card X g).trans hr, hdiam, by omega⟩

/-- Exactly one consecutive block of the actual period, with one fixed
nonterminal Q and an arbitrary starting layer. Necessary arithmetic only;
there is no physical-realization or prescribed-Q sufficiency claim. -/
theorem fixedQ_block_classification {X Q : ℕ} (hX : 3 ≤ X) (hodd : Odd X)
    (hQ : (X : ℤ) + 1 ≤ 2 * (Q : ℤ)) (hQX : Q < X)
    (k m₀ : ℕ) (H : ℕ → ℤ)
    (hblock : HeightBlock X Q k m₀ (period X Q) H) :
    denominator X Q = 2 ^ period X Q - 1 ∧
      2 * diameter X Q = X - Nat.gcd X Q := by
  obtain ⟨_, _, _, _, _, hnarrow, _⟩ :=
    fixedQ_block_forces_narrow hX hodd hQ hQX k m₀ H hblock
  have hQp : 0 < Q := by
    have : (0 : ℤ) < Q := by omega
    exact_mod_cast this
  obtain ⟨_, _, hD, hdiam⟩ := narrow_classification hX hodd hQp hQX hnarrow
  exact ⟨hD, hdiam⟩

/-- Abstract existence, with Q existentially chosen. This does not assert
that a prescribed Q works, or that an abstract orbit is physically realized. -/
theorem exists_narrow_period_iff_mersenne_dvd {X t : ℕ}
    (hX : 3 ≤ X) (hodd : Odd X) (ht : 2 ≤ t) :
    (∃ Q : ℕ, 0 < Q ∧ Q < X ∧ period X Q = t ∧ 2 * diameter X Q < X) ↔
      2 ^ t - 1 ∣ X := by
  constructor
  · rintro ⟨Q, hQ, hQX, hr, hnarrow⟩
    obtain ⟨_, _, hD, _⟩ := narrow_classification hX hodd hQ hQX hnarrow
    rw [← hr, ← hD]
    exact ⟨Nat.gcd X Q, (Nat.div_mul_cancel (Nat.gcd_dvd_left X Q)).symm⟩
  · intro hdiv
    obtain ⟨Q, hQ, hQX, hr, _, _, hnarrow⟩ :=
      exists_narrow_of_mersenne_dvd hX hodd ht hdiv
    exact ⟨Q, hQ, hQX, hr, hnarrow⟩

/-- Existential version when the period is not prescribed. -/
theorem exists_narrow_iff_mersenne_dvd {X : ℕ} (hX : 3 ≤ X) (hodd : Odd X) :
    (∃ Q : ℕ, 0 < Q ∧ Q < X ∧ 2 * diameter X Q < X) ↔
      ∃ t : ℕ, 2 ≤ t ∧ 2 ^ t - 1 ∣ X := by
  constructor
  · rintro ⟨Q, hQ, hQX, hnarrow⟩
    obtain ⟨hr, _, hD, _⟩ := narrow_classification hX hodd hQ hQX hnarrow
    refine ⟨period X Q, hr, ?_⟩
    rw [← hD]
    exact ⟨Nat.gcd X Q, (Nat.div_mul_cancel (Nat.gcd_dvd_left X Q)).symm⟩
  · rintro ⟨t, ht, hdiv⟩
    obtain ⟨Q, hQ, hQX, _, _, _, hnarrow⟩ :=
      exists_narrow_of_mersenne_dvd hX hodd ht hdiv
    exact ⟨Q, hQ, hQX, hnarrow⟩

end D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
