/-
Directed integer logarithm bounds; see current scoped verification receipts.
Intended canonical owner: D5/S3/Arith/GoldenResource/DirectedLogarithmBounds.
This implements the integer recurrence of exact_pressure_certificate.py,
SHA256 f99780ee4fdc76814f65e2dc7012e950420bddee552751fda807ee4d5e121f76.
The original successful-Option soundness statements are retained. Private
natural arithmetic proves success of THIS loop for every fuel >= 33 on
0<zd, 3*zn<=zd, including zero. Total accessors at fuel 100 consume that
proof and the original soundness statements. Analytic correctness still
has STRICT parameter domain z<1/3. No packet admission or finite-pressure
result is asserted. The additional integer width proof follows the first
actual return by step 33, then is transported through the total accessors.
Kernel and axiom status must be read from current scoped verification receipts.
-/
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.DirectedLogarithmBounds

open scoped BigOperators
open RobinRationalBasis

def scale : ℕ := 10 ^ 30

/-- Exact nonnegative-integer ceiling division, including the Python `-1`. -/
def ceilDiv (n d : ℕ) : ℕ := (n + d - 1) / d

private theorem scale_pos : (0 : ℝ) < scale := by norm_num [scale]

private theorem ceil_mul_bounds (n d : ℕ) (hd : 0 < d) :
    n ≤ ceilDiv n d * d ∧ ceilDiv n d * d < n + d := by
  have hmod := Nat.mod_lt (n + d - 1) hd
  have heq : (n + d - 1) / d * d + (n + d - 1) % d = n + d - 1 := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod (n + d - 1) d
  have hfloor := Nat.div_mul_le_self (n + d - 1) d
  unfold ceilDiv
  omega

private theorem ceil_le_iff (n d m : ℕ) (hd : 0 < d) :
    ceilDiv n d ≤ m ↔ n ≤ d * m := by
  have hc := ceil_mul_bounds n d hd
  constructor
  · intro h
    have hm := Nat.mul_le_mul_right d h
    nlinarith only [hc.1, hm]
  · intro h
    by_contra hn
    have hm : m + 1 ≤ ceilDiv n d := by omega
    have hp := Nat.mul_le_mul_right d hm
    nlinarith only [hc.2, hp, h]

private theorem ceil_mono {n m d : ℕ} (hd : 0 < d) (h : n ≤ m) :
    ceilDiv n d ≤ ceilDiv m d := by
  apply (ceil_le_iff n d (ceilDiv m d) hd).2
  have hm := (ceil_mul_bounds m d hd).1
  nlinarith only [h, hm]

private theorem floor_mul_bounds (n d : ℕ) (hd : 0 < d) :
    n / d * d ≤ n ∧ n < (n / d + 1) * d := by
  have heq : n / d * d + n % d = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n d
  have hmod := Nat.mod_lt n hd
  exact ⟨Nat.div_mul_le_self n d, by nlinarith only [heq, hmod]⟩

private theorem floor_le_of_le_mul (n d m : ℕ) (hd : 0 < d)
    (h : n ≤ d * m) : n / d ≤ m := by
  have hf := (floor_mul_bounds n d hd).1
  by_contra hn
  have hq : m + 1 ≤ n / d := by omega
  have hm := Nat.mul_le_mul_right d hq
  nlinarith only [hf, hm, h, hd]

private theorem floor_le_ceil {n m d : ℕ} (hd : 0 < d) (h : n ≤ m) :
    n / d ≤ ceilDiv m d := by
  apply floor_le_of_le_mul n d (ceilDiv m d) hd
  have hc := (ceil_mul_bounds m d hd).1
  nlinarith only [h, hc]

private theorem floor_ceil_gap (n d : ℕ) (hd : 0 < d) :
    n / d ≤ ceilDiv n d ∧ ceilDiv n d ≤ n / d + 1 := by
  refine ⟨floor_le_ceil hd le_rfl, ?_⟩
  apply (ceil_le_iff n d (n / d + 1) hd).2
  have hf := (floor_mul_bounds n d hd).2
  nlinarith only [hf]

/-- Positive-divisor ceiling composition, also at numerator zero. -/
private theorem ceil_comp (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ceilDiv (ceilDiv n a) b = ceilDiv n (a * b) := by
  have hab := Nat.mul_pos ha hb
  apply Nat.le_antisymm
  · apply (ceil_le_iff (ceilDiv n a) b (ceilDiv n (a * b)) hb).2
    apply (ceil_le_iff n a (b * ceilDiv n (a * b)) ha).2
    have h := (ceil_mul_bounds n (a * b) hab).1
    nlinarith only [h]
  · apply (ceil_le_iff n (a * b) (ceilDiv (ceilDiv n a) b) hab).2
    have h1 := (ceil_mul_bounds n a ha).1
    have h2 := (ceil_mul_bounds (ceilDiv n a) b hb).1
    have h3 := Nat.mul_le_mul_left a h2
    nlinarith only [h1, h3]

private theorem ceil_real_bounds (n d : ℕ) (hd : 0 < d) :
    (n : ℝ) / d ≤ ceilDiv n d ∧
      (ceilDiv n d : ℝ) < (n : ℝ) / d + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := ceil_mul_bounds n d hd
  constructor
  · apply (div_le_iff₀ hdR).2
    exact_mod_cast h.1
  · calc
      (ceilDiv n d : ℝ) < ((n : ℝ) + d) / d :=
        (lt_div_iff₀ hdR).2 (by exact_mod_cast h.2)
      _ = (n : ℝ) / d + 1 := by field_simp [hdR.ne']

/-- The same scale and initial directed square coefficients as the generator. -/
structure Coefficients where
  a : ℕ
  b : ℕ

def zlo (zn zd : ℕ) : ℕ := scale * zn / zd
def zhi (zn zd : ℕ) : ℕ := ceilDiv (scale * zn) zd

def coefficients (zn zd : ℕ) : Coefficients :=
  ⟨zlo zn zd * zlo zn zd / scale, ceilDiv (zhi zn zd * zhi zn zd) scale⟩

structure State where
  k : ℕ
  pl : ℕ
  ph : ℕ
  lo : ℕ
  hi : ℕ

def initial (zn zd : ℕ) : State := ⟨0, zlo zn zd, zhi zn zd, 0, 0⟩

/-- All RHSs use the OLD state, as in the Python assignment order. -/
def step (c : Coefficients) (s : State) : State :=
  { k := s.k + 1
    pl := s.pl * c.a / scale
    ph := ceilDiv (s.ph * c.b) scale
    lo := s.lo + 2 * s.pl / (2 * s.k + 1)
    hi := s.hi + ceilDiv (2 * s.ph) (2 * s.k + 1) }

/-- Called on the NEW state, so its odd denominator is 2*(old k+1)+1. -/
def tail (c : Coefficients) (s : State) : ℕ :=
  ceilDiv (2 * s.ph * scale) ((2 * s.k + 1) * (scale - c.b))

/-- One unit of fuel permits one complete step and one stopping test.
After a failed test at step 100 the generator asserts; this version returns
`none`. A fuel failure has no enclosure interpretation. -/
def loop (c : Coefficients) : ℕ → State → Option (ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, s =>
    let t := step c s
    if tail c t ≤ 1 then some (t.lo, t.hi + tail c t)
    else loop c fuel t

def bounds (zn zd fuel : ℕ) : Option (ℕ × ℕ) :=
  if zn = 0 then some (0, 0)
  else loop (coefficients zn zd) fuel (initial zn zd)

private def uniformZ : ℕ := 333333333333333333333333333334
private def uniformB : ℕ := 111111111111111111111111111112

private theorem uniform_constants :
    ceilDiv scale 3 = uniformZ ∧
    ceilDiv (uniformZ * uniformZ) scale = uniformB ∧
    8 * uniformB ≤ scale ∧ uniformB < scale ∧
    uniformZ < 8 ^ 33 ∧ 2 * scale ≤ 67 * (scale - uniformB) := by
  norm_num [ceilDiv, scale, uniformZ, uniformB]

private theorem initial_upper_bound {zn zd : ℕ}
    (hd : 0 < zd) (hz : 3 * zn ≤ zd) : zhi zn zd ≤ uniformZ := by
  apply (ceil_le_iff (scale * zn) zd uniformZ hd).2
  have hS : scale ≤ 3 * uniformZ := by
    have h := (ceil_mul_bounds scale 3 (by omega)).1
    rw [uniform_constants.1] at h
    simpa only [Nat.mul_comm] using h
  have h1 := Nat.mul_le_mul_right zn hS
  have h2 := Nat.mul_le_mul_left uniformZ hz
  nlinarith only [h1, h2]

private theorem coefficient_upper_bound {zn zd : ℕ}
    (hd : 0 < zd) (hz : 3 * zn ≤ zd) : (coefficients zn zd).b ≤ uniformB := by
  have hzh := initial_upper_bound hd hz
  have hsq := Nat.mul_le_mul hzh hzh
  change ceilDiv (zhi zn zd * zhi zn zd) scale ≤ uniformB
  rw [← uniform_constants.2.1]
  exact ceil_mono (by norm_num [scale]) hsq

/-- A single ACTUAL rounded ph update contracts by the ceiling of /8. -/
private theorem upper_step_bound (c : Coefficients) (s : State)
    (hb : c.b ≤ uniformB) : (step c s).ph ≤ ceilDiv s.ph 8 := by
  have h8 : 8 * c.b ≤ scale := by
    have h := Nat.mul_le_mul_left 8 hb
    exact h.trans uniform_constants.2.2.1
  have hp := (ceil_mul_bounds s.ph 8 (by omega)).1
  apply (ceil_le_iff (s.ph * c.b) scale (ceilDiv s.ph 8)
    (by norm_num [scale])).2
  have h1 := Nat.mul_le_mul_right c.b hp
  have h2 := Nat.mul_le_mul_left (ceilDiv s.ph 8) h8
  nlinarith only [h1, h2]

private theorem upper_step_decay (c : Coefficients) (s : State)
    (hb : c.b ≤ uniformB) (hp : s.ph ≤ ceilDiv uniformZ (8 ^ s.k)) :
    (step c s).ph ≤ ceilDiv uniformZ (8 ^ (step c s).k) := by
  calc
    (step c s).ph ≤ ceilDiv s.ph 8 := upper_step_bound c s hb
    _ ≤ ceilDiv (ceilDiv uniformZ (8 ^ s.k)) 8 := ceil_mono (by omega) hp
    _ = ceilDiv uniformZ (8 ^ s.k * 8) :=
      ceil_comp uniformZ (8 ^ s.k) 8 (by positivity) (by omega)
    _ = ceilDiv uniformZ (8 ^ (step c s).k) := by
      rw [show (step c s).k = s.k + 1 from rfl, pow_succ]

private theorem tail_at_33 (c : Coefficients) (s : State)
    (hb : c.b ≤ uniformB) (hk : s.k = 33) (hp : s.ph ≤ 1) :
    tail c s ≤ 1 := by
  have hbS : c.b < scale := hb.trans_lt uniform_constants.2.2.2.1
  have hdiff : scale - uniformB ≤ scale - c.b := by omega
  have hden : 2 * scale ≤ (2 * s.k + 1) * (scale - c.b) := by
    rw [hk]
    have h := Nat.mul_le_mul_left 67 hdiff
    exact uniform_constants.2.2.2.2.2.trans (by simpa using h)
  have hd : 0 < (2 * s.k + 1) * (scale - c.b) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt hbS)
  apply (ceil_le_iff _ _ 1 hd).2
  have hn := Nat.mul_le_mul_right (2 * scale) hp
  nlinarith only [hn, hden]

/-- A failed ACTUAL next-state test cannot pass index 33. Both the
totality and width inductions consume this same fact. -/
private theorem next_index_lt_33 (c : Coefficients) (s : State)
    (hb : c.b ≤ uniformB) (hk : s.k < 33)
    (hp : s.ph ≤ ceilDiv uniformZ (8 ^ s.k))
    (hstop : ¬ tail c (step c s) ≤ 1) : (step c s).k < 33 := by
  have ht := upper_step_decay c s hb hp
  have hle : (step c s).k ≤ 33 := by dsimp only [step]; omega
  by_contra hn
  have heq : (step c s).k = 33 := by omega
  have hph : (step c s).ph ≤ 1 := by
    apply ht.trans
    rw [heq]
    apply (ceil_le_iff uniformZ (8 ^ 33) 1 (by positivity)).2
    simpa using uniform_constants.2.2.2.2.1.le
  exact hstop (tail_at_33 c (step c s) hb heq hph)

/-- Induction follows loop itself. A prior stop keeps its exact pair; if
there was no prior stop, the post-step state k=33 forces the stop branch.
No separate iterator, fuel validator or altered early-exit rule occurs. -/
private theorem loop_success (c : Coefficients) (hb : c.b ≤ uniformB)
    (fuel : ℕ) (s : State) (hk : s.k < 33)
    (hp : s.ph ≤ ceilDiv uniformZ (8 ^ s.k)) (hf : 33 ≤ s.k + fuel) :
    ∃ p, loop c fuel s = some p := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    let t := step c s
    have ht : t.ph ≤ ceilDiv uniformZ (8 ^ t.k) := upper_step_decay c s hb hp
    by_cases hstop : tail c t ≤ 1
    · refine ⟨(t.lo, t.hi + tail c t), ?_⟩
      change (if tail c t ≤ 1 then some (t.lo, t.hi + tail c t)
        else loop c fuel t) = _
      rw [if_pos hstop]
    · have htk : t.k < 33 := next_index_lt_33 c s hb hk hp hstop
      obtain ⟨p, hrun⟩ := ih t htk ht (by dsimp [t, step]; omega)
      refine ⟨p, ?_⟩
      change (if tail c t ≤ 1 then some (t.lo, t.hi + tail c t)
        else loop c fuel t) = some p
      rw [if_neg hstop]
      exact hrun

/-- Uniform success has the CLOSED integer domain. This is not an
analytic endpoint soundness claim. The zero branch uses no fuel. -/
private theorem bounds_success (zn zd fuel : ℕ) (hd : 0 < zd)
    (hz : 3 * zn ≤ zd) (hf : 33 ≤ fuel) :
    ∃ p, bounds zn zd fuel = some p := by
  by_cases hn : zn = 0
  · exact ⟨(0, 0), by simp [bounds, hn]⟩
  · have h := loop_success (coefficients zn zd) (coefficient_upper_bound hd hz)
      fuel (initial zn zd) (by simp [initial])
      (by simpa [initial, ceilDiv] using initial_upper_bound hd hz)
      (by simpa [initial] using hf)
    simpa only [bounds, if_neg hn] using h

private theorem getD_run (o : Option (ℕ × ℕ)) (h : ∃ p, o = some p) :
    o = some (o.getD (0, 0)) := by
  obtain ⟨p, rfl⟩ := h
  rfl

/-- The actual fuel-100 result. Its default is proved unreachable on the
stated domain by the same loop's 33-step success proof. -/
def totalBounds (zn zd : ℕ) : ℕ × ℕ := (bounds zn zd 100).getD (0, 0)

/-- All differences are first proved as ADDITIVE natural inequalities.
In particular, neither a coefficient nor a power subtraction is assumed
to be nonnegative. The endpoint 3*zn=zd is allowed in this arithmetic. -/
private theorem initial_integer_bounds {zn zd : ℕ}
    (hd : 0 < zd) (hz : 3 * zn ≤ zd) :
    3 * zlo zn zd ≤ scale ∧ zlo zn zd ≤ zhi zn zd ∧
      zhi zn zd ≤ zlo zn zd + 1 := by
  have hf := Nat.div_mul_le_self (scale * zn) zd
  have h1 := Nat.mul_le_mul_left 3 hf
  have h2 := Nat.mul_le_mul_left scale hz
  have hsmall : 3 * zlo zn zd ≤ scale := by
    change 3 * (scale * zn / zd) ≤ scale
    by_contra hn
    have hq : scale + 1 ≤ 3 * (scale * zn / zd) := by omega
    have hqmul := Nat.mul_le_mul_right zd hq
    nlinarith only [h1, h2, hqmul, hd]
  exact ⟨hsmall, floor_ceil_gap (scale * zn) zd hd⟩

private theorem coefficient_integer_bounds {zn zd : ℕ}
    (hd : 0 < zd) (hz : 3 * zn ≤ zd) :
    (coefficients zn zd).a ≤ (coefficients zn zd).b ∧
      (coefficients zn zd).b ≤ (coefficients zn zd).a + 2 ∧
      8 * (coefficients zn zd).b ≤ scale := by
  have hS : 0 < scale := by norm_num [scale]
  obtain ⟨hsmall, horder, hgap⟩ := initial_integer_bounds hd hz
  have hsq := Nat.mul_le_mul horder horder
  have hsqgap : zhi zn zd * zhi zn zd < zlo zn zd * zlo zn zd + scale := by
    have hsq' := Nat.mul_le_mul hgap hgap
    have hlarge : 3 < scale := by norm_num [scale]
    have hlin : 2 * zlo zn zd + 1 < scale := by omega
    nlinarith only [hsq', hlin]
  have hf := (floor_mul_bounds (zlo zn zd * zlo zn zd) scale hS).2
  refine ⟨floor_le_ceil hS hsq, ?_, ?_⟩
  · change ceilDiv (zhi zn zd * zhi zn zd) scale ≤
      zlo zn zd * zlo zn zd / scale + 2
    apply (ceil_le_iff _ _ _ hS).2
    nlinarith only [hsqgap, hf]
  · exact (Nat.mul_le_mul_left 8 (coefficient_upper_bound hd hz)).trans
      uniform_constants.2.2.1

/-- Concrete invariants of this State, including the exceptional OLD k=0
increment. This is not an input validator or an assumed output width. -/
private structure WidthInvariant (s : State) : Prop where
  powerSmall : 3 * s.pl ≤ scale
  powerOrder : s.pl ≤ s.ph
  powerGap : s.ph ≤ s.pl + 3
  firstGap : s.k = 0 → s.ph ≤ s.pl + 1
  sumOrder : s.lo ≤ s.hi
  sumGap : s.hi ≤ s.lo + 3 * s.k

private theorem initial_width_invariant {zn zd : ℕ}
    (hd : 0 < zd) (hz : 3 * zn ≤ zd) : WidthInvariant (initial zn zd) := by
  obtain ⟨hsmall, horder, hgap⟩ := initial_integer_bounds hd hz
  refine ⟨hsmall, horder, ?_, fun _ => hgap, by simp [initial], by simp [initial]⟩
  change zhi zn zd ≤ zlo zn zd + 3
  omega

/-- The two actual power roundings lose strictly less than 2 units.
24*(next.ph-next.pl)<73 is written after multiplication by S, so no
Nat subtraction or field division is needed. 73/24=3/8+2/3+2<4. -/
private theorem power_step_gap (c : Coefficients) (s : State)
    (hab : c.a ≤ c.b) (hgap : c.b ≤ c.a + 2) (hb : 8 * c.b ≤ scale)
    (hs : WidthInvariant s) :
    (step c s).pl ≤ (step c s).ph ∧
      (step c s).ph ≤ (step c s).pl + 3 := by
  have hS : 0 < scale := by norm_num [scale]
  have hn := Nat.mul_le_mul hs.powerOrder hab
  have hord : (step c s).pl ≤ (step c s).ph := floor_le_ceil hS hn
  have hu := Nat.mul_le_mul_right c.b hs.powerGap
  have hl := Nat.mul_le_mul_left s.pl hgap
  have hnum : s.ph * c.b ≤ s.pl * c.a + 3 * c.b + 2 * s.pl := by
    nlinarith only [hu, hl]
  have hf := (floor_mul_bounds (s.pl * c.a) scale hS).2
  have hc := (ceil_mul_bounds (s.ph * c.b) scale hS).2
  have hstrict : 24 * ((step c s).ph * scale) <
      24 * ((step c s).pl * scale) + 73 * scale := by
    change 24 * (ceilDiv (s.ph * c.b) scale * scale) <
      24 * (s.pl * c.a / scale * scale) + 73 * scale
    nlinarith only [hnum, hf, hc, hb, hs.powerSmall]
  refine ⟨hord, ?_⟩
  by_contra hn
  have hfour : (step c s).pl + 4 ≤ (step c s).ph := by omega
  have hm := Nat.mul_le_mul_right scale hfour
  nlinarith only [hstrict, hm, hS]

private theorem sum_increment_gap (s : State) (hs : WidthInvariant s) :
    2 * s.pl / (2 * s.k + 1) ≤ ceilDiv (2 * s.ph) (2 * s.k + 1) ∧
      ceilDiv (2 * s.ph) (2 * s.k + 1) ≤ 2 * s.pl / (2 * s.k + 1) + 3 := by
  have hd : 0 < 2 * s.k + 1 := by omega
  refine ⟨floor_le_ceil hd (by have h := hs.powerOrder; omega), ?_⟩
  by_cases hk : s.k = 0
  · have hfirst := hs.firstGap hk
    have h : 2 * s.ph ≤ 2 * s.pl + 3 := by omega
    simpa [hk, ceilDiv] using h
  · have hodd : 3 ≤ 2 * s.k + 1 := by omega
    apply (ceil_le_iff _ _ _ hd).2
    have hf := (floor_mul_bounds (2 * s.pl) (2 * s.k + 1) hd).2
    have hp := hs.powerGap
    nlinarith only [hf, hp, hodd]

private theorem step_width_invariant (c : Coefficients) (s : State)
    (hab : c.a ≤ c.b) (hgap : c.b ≤ c.a + 2) (hb : 8 * c.b ≤ scale)
    (hs : WidthInvariant s) : WidthInvariant (step c s) := by
  have hS : 0 < scale := by norm_num [scale]
  have ha : c.a ≤ scale := by omega
  have hnum : s.pl * c.a ≤ scale * s.pl := by
    have h := Nat.mul_le_mul_left s.pl ha
    nlinarith only [h]
  have hdec : (step c s).pl ≤ s.pl := floor_le_of_le_mul _ _ _ hS hnum
  have hp := power_step_gap c s hab hgap hb hs
  have hi := sum_increment_gap s hs
  constructor
  · have h := Nat.mul_le_mul_left 3 hdec
    exact h.trans hs.powerSmall
  · exact hp.1
  · exact hp.2
  · intro hk
    have hk' : (step c s).k = s.k + 1 := rfl
    omega
  · change s.lo + 2 * s.pl / (2 * s.k + 1) ≤
      s.hi + ceilDiv (2 * s.ph) (2 * s.k + 1)
    have ho := hs.sumOrder
    omega
  · change s.hi + ceilDiv (2 * s.ph) (2 * s.k + 1) ≤
      s.lo + 2 * s.pl / (2 * s.k + 1) + 3 * (s.k + 1)
    have hsum := hs.sumGap
    omega

/-- The witness j is the index of the FIRST actual stop: induction takes
the current returned pair immediately in the true branch and follows only
the false branch otherwise. In particular success at fuel 100 alone is
not used as a substitute for the bound j<=33. -/
private theorem loop_width (c : Coefficients) (hab : c.a ≤ c.b)
    (hgap : c.b ≤ c.a + 2) (hb : c.b ≤ uniformB)
    (fuel : ℕ) (s : State) (hk : s.k < 33)
    (hp : s.ph ≤ ceilDiv uniformZ (8 ^ s.k)) (hs : WidthInvariant s)
    (p : ℕ × ℕ) (hrun : loop c fuel s = some p) :
    ∃ j : ℕ, s.k < j ∧ j ≤ 33 ∧ p.1 ≤ p.2 ∧ p.2 ≤ p.1 + 3 * j + 1 := by
  induction fuel generalizing s with
  | zero => simp only [loop, reduceCtorEq] at hrun
  | succ fuel ih =>
    let t := step c s
    have h8 := (Nat.mul_le_mul_left 8 hb).trans uniform_constants.2.2.1
    have ht : WidthInvariant t := step_width_invariant c s hab hgap h8 hs
    have htp : t.ph ≤ ceilDiv uniformZ (8 ^ t.k) := upper_step_decay c s hb hp
    change (if tail c t ≤ 1 then some (t.lo, t.hi + tail c t)
      else loop c fuel t) = some p at hrun
    by_cases hstop : tail c t ≤ 1
    · rw [if_pos hstop] at hrun
      have heq := Option.some.inj hrun
      subst p
      refine ⟨t.k, ?_, ?_, ?_, ?_⟩
      · dsimp [t, step]; omega
      · dsimp [t, step]; omega
      · have ho := ht.sumOrder
        simp only [Prod.fst, Prod.snd]
        omega
      · have hg := ht.sumGap
        simp only [Prod.fst, Prod.snd]
        omega
    · rw [if_neg hstop] at hrun
      have htk : t.k < 33 := next_index_lt_33 c s hb hk hp hstop
      obtain ⟨j, hj, hj33, ho, hg⟩ := ih t htk htp ht hrun
      refine ⟨j, ?_, hj33, ho, hg⟩
      have htk' : t.k = s.k + 1 := rfl
      omega

private theorem bounds_span (zn zd fuel : ℕ) (hd : 0 < zd)
    (hz : 3 * zn ≤ zd) (p : ℕ × ℕ) (hrun : bounds zn zd fuel = some p) :
    p.1 ≤ p.2 ∧ p.2 ≤ p.1 + 100 := by
  by_cases hn : zn = 0
  · have heq : (0, 0) = p := by simpa [bounds, hn] using hrun
    subst p
    norm_num
  · have hc := coefficient_integer_bounds hd hz
    obtain ⟨j, _, hj, ho, hg⟩ := loop_width (coefficients zn zd) hc.1 hc.2.1
      (coefficient_upper_bound hd hz) fuel (initial zn zd) (by simp [initial])
      (by simpa [initial, ceilDiv] using initial_upper_bound hd hz)
      (initial_width_invariant hd hz) p (by simpa [bounds, hn] using hrun)
    exact ⟨ho, by omega⟩

/-- CLOSED-domain integer width of the actual total accessor. Ordering is
proved before its Nat subtraction; the zero branch has width zero. -/
theorem totalBounds_width (zn zd : ℕ) (hd : 0 < zd) (hz : 3 * zn ≤ zd) :
    (totalBounds zn zd).1 ≤ (totalBounds zn zd).2 ∧
      (totalBounds zn zd).2 - (totalBounds zn zd).1 ≤ 100 := by
  have hrun : bounds zn zd 100 = some (totalBounds zn zd) :=
    getD_run _ (bounds_success zn zd 100 hd hz (by omega))
  have h := bounds_span zn zd 100 hd hz _ hrun
  omega

/-- Scaled enclosure. Scaling is kept integral until the final transport. -/
def Encloses (p : ℕ × ℕ) (x : ℝ) : Prop :=
  (p.1 : ℝ) ≤ scale * x ∧ scale * x ≤ (p.2 : ℝ)

def lower (p : ℕ × ℕ) : ℚ := (p.1 : ℚ) / scale
def upper (p : ℕ × ℕ) : ℚ := (p.2 : ℚ) / scale

theorem encloses_iff_rat (p : ℕ × ℕ) (x : ℝ) :
    Encloses p x ↔ (lower p : ℝ) ≤ x ∧ x ≤ (upper p : ℝ) := by
  simp only [Encloses, lower, upper, Rat.cast_div, Rat.cast_natCast]
  constructor
  · intro h
    exact ⟨(div_le_iff₀ scale_pos).2 (by nlinarith [h.1]),
      (le_div_iff₀ scale_pos).2 (by nlinarith [h.2])⟩
  · intro h
    exact ⟨by nlinarith [(div_le_iff₀ scale_pos).1 h.1],
      by nlinarith [(le_div_iff₀ scale_pos).1 h.2]⟩

private structure CoefficientInvariant (c : Coefficients) (z : ℝ) : Prop where
  lower : (c.a : ℝ) ≤ scale * z ^ 2
  upper : scale * z ^ 2 ≤ (c.b : ℝ)
  strict : c.b < scale

private structure Invariant (z : ℝ) (s : State) : Prop where
  powerLo : (s.pl : ℝ) ≤ scale * z ^ (2 * s.k + 1)
  powerHi : scale * z ^ (2 * s.k + 1) ≤ (s.ph : ℝ)
  sumLo : (s.lo : ℝ) ≤ scale * atanhPartial z s.k
  sumHi : scale * atanhPartial z s.k ≤ (s.hi : ℝ)

private theorem initial_parameter {zn zd : ℕ} (hd : 0 < zd) :
    (zlo zn zd : ℝ) ≤ scale * ((zn : ℝ) / zd) ∧
    scale * ((zn : ℝ) / zd) ≤ (zhi zn zd : ℝ) ∧
    (zhi zn zd : ℝ) < scale * ((zn : ℝ) / zd) + 1 := by
  have hf : ((scale * zn / zd : ℕ) : ℝ) ≤ (scale * zn : ℕ) / (zd : ℝ) :=
    Nat.cast_div_le
  have hc := ceil_real_bounds (scale * zn) zd hd
  push_cast at hf hc
  simpa only [zlo, zhi, mul_div_assoc] using And.intro hf hc

private theorem initial_coefficient_invariant {zn zd : ℕ}
    (hd : 0 < zd) (hz : 3 * zn < zd) :
    CoefficientInvariant (coefficients zn zd) ((zn : ℝ) / zd) := by
  let z : ℝ := (zn : ℝ) / zd
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hp := initial_parameter (zn := zn) hd
  change (zlo zn zd : ℝ) ≤ scale * z ∧
    scale * z ≤ (zhi zn zd : ℝ) ∧ (zhi zn zd : ℝ) < scale * z + 1 at hp
  have hzl0 : (0 : ℝ) ≤ zlo zn zd := Nat.cast_nonneg _
  have hzh0 : (0 : ℝ) ≤ zhi zn zd := Nat.cast_nonneg _
  have hsqlo := mul_le_mul hp.1 hp.1 hzl0 (mul_nonneg scale_pos.le hz0)
  have hsqhi := mul_le_mul hp.2.1 hp.2.1 (mul_nonneg scale_pos.le hz0) hzh0
  have ha := (Nat.cast_div_le (m := zlo zn zd * zlo zn zd)
    (n := scale) : ((zlo zn zd * zlo zn zd / scale : ℕ) : ℝ) ≤
      (zlo zn zd * zlo zn zd : ℕ) / (scale : ℝ))
  have hb := ceil_real_bounds (zhi zn zd * zhi zn zd) scale
    (by norm_num [scale])
  push_cast at ha hb
  have hal : ((coefficients zn zd).a : ℝ) ≤ scale * z ^ 2 := by
    change ((zlo zn zd * zlo zn zd / scale : ℕ) : ℝ) ≤ _
    apply ha.trans
    apply (div_le_iff₀ scale_pos).2
    nlinarith only [hsqlo]
  have hbu : scale * z ^ 2 ≤ ((coefficients zn zd).b : ℝ) := by
    change _ ≤ (ceilDiv (zhi zn zd * zhi zn zd) scale : ℝ)
    apply le_trans _ hb.1
    apply (le_div_iff₀ scale_pos).2
    nlinarith only [hsqhi]
  exact ⟨hal, hbu, (coefficient_upper_bound hd hz.le).trans_lt
    uniform_constants.2.2.2.1⟩

private theorem initial_invariant {zn zd : ℕ} (hd : 0 < zd) :
    Invariant ((zn : ℝ) / zd) (initial zn zd) := by
  have h := initial_parameter (zn := zn) hd
  constructor
  · simpa [initial] using h.1
  · simpa [initial] using h.2.1
  · simp [initial, atanhPartial]
  · simp [initial, atanhPartial]

private theorem partial_succ (z : ℝ) (k : ℕ) :
    atanhPartial z (k + 1) = atanhPartial z k +
      2 * z ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
  simp only [atanhPartial, Finset.sum_range_succ]
  push_cast
  ring

/-- BOTH power roundings and BOTH sum roundings are propagated at each step. -/
private theorem step_invariant {c : Coefficients} {z : ℝ} {s : State}
    (hz : 0 ≤ z) (hc : CoefficientInvariant c z) (hs : Invariant z s) :
    Invariant z (step c s) := by
  have hp0 : 0 ≤ scale * z ^ (2 * s.k + 1) := by positivity
  have ha0 : (0 : ℝ) ≤ c.a := Nat.cast_nonneg _
  have hph0 : (0 : ℝ) ≤ s.ph := Nat.cast_nonneg _
  have hoddN : 0 < 2 * s.k + 1 := by omega
  have hodd : (0 : ℝ) < (2 * s.k + 1 : ℕ) := by exact_mod_cast hoddN
  have hpl := mul_le_mul hs.powerLo hc.lower ha0 hp0
  have hph := mul_le_mul hs.powerHi hc.upper (by positivity) hph0
  have hpId : z ^ (2 * (s.k + 1) + 1) = z ^ (2 * s.k + 1) * z ^ 2 := by
    rw [show 2 * (s.k + 1) + 1 = (2 * s.k + 1) + 2 by omega, pow_add]
  have hlPow := (Nat.cast_div_le (m := s.pl * c.a) (n := scale) :
    ((s.pl * c.a / scale : ℕ) : ℝ) ≤ (s.pl * c.a : ℕ) / (scale : ℝ))
  have hhPow := (ceil_real_bounds (s.ph * c.b) scale (by norm_num [scale])).1
  have hlSum := (Nat.cast_div_le (m := 2 * s.pl) (n := 2 * s.k + 1) :
    ((2 * s.pl / (2 * s.k + 1) : ℕ) : ℝ) ≤
      (2 * s.pl : ℕ) / (2 * s.k + 1 : ℕ))
  have hhSum := (ceil_real_bounds (2 * s.ph) (2 * s.k + 1) hoddN).1
  push_cast at hlPow hhPow hlSum hhSum
  constructor
  · change ((s.pl * c.a / scale : ℕ) : ℝ) ≤ _
    rw [show (step c s).k = s.k + 1 from rfl, hpId]
    apply hlPow.trans
    apply (div_le_iff₀ scale_pos).2
    nlinarith only [hpl]
  · change _ ≤ (ceilDiv (s.ph * c.b) scale : ℝ)
    rw [show (step c s).k = s.k + 1 from rfl, hpId]
    apply le_trans _ hhPow
    apply (le_div_iff₀ scale_pos).2
    nlinarith only [hph]
  · change ((s.lo + 2 * s.pl / (2 * s.k + 1) : ℕ) : ℝ) ≤
      scale * atanhPartial z (s.k + 1)
    rw [Nat.cast_add, partial_succ]
    have hterm : (2 : ℝ) * s.pl / (2 * s.k + 1 : ℕ) ≤
        scale * (2 * z ^ (2 * s.k + 1) / (2 * s.k + 1 : ℕ)) := by
      calc
        _ ≤ (2 * ((scale : ℝ) * z ^ (2 * s.k + 1))) / (2 * s.k + 1 : ℕ) :=
          div_le_div_of_nonneg_right (by nlinarith only [hs.powerLo]) hodd.le
        _ = _ := by ring
    push_cast at hterm ⊢
    nlinarith only [hs.sumLo, hlSum, hterm]
  · change scale * atanhPartial z (s.k + 1) ≤
      ((s.hi + ceilDiv (2 * s.ph) (2 * s.k + 1) : ℕ) : ℝ)
    rw [Nat.cast_add, partial_succ]
    have hterm : scale * (2 * z ^ (2 * s.k + 1) / (2 * s.k + 1 : ℕ)) ≤
        (2 : ℝ) * s.ph / (2 * s.k + 1 : ℕ) := by
      calc
        _ = (2 * ((scale : ℝ) * z ^ (2 * s.k + 1))) / (2 * s.k + 1 : ℕ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hs.powerHi]) hodd.le
    push_cast at hterm ⊢
    nlinarith only [hs.sumHi, hhSum, hterm]

private theorem power_ratios {z : ℝ} {s : State} (hs : Invariant z s) :
    (s.pl : ℝ) / scale ≤ z ^ (2 * s.k + 1) ∧
      z ^ (2 * s.k + 1) ≤ (s.ph : ℝ) / scale := by
  exact ⟨(div_le_iff₀ scale_pos).2 (by nlinarith [hs.powerLo]),
    (le_div_iff₀ scale_pos).2 (by nlinarith [hs.powerHi])⟩

private theorem coefficient_ratios {c : Coefficients} {z : ℝ}
    (hc : CoefficientInvariant c z) :
    (c.a : ℝ) / scale ≤ z ^ 2 ∧ z ^ 2 ≤ (c.b : ℝ) / scale ∧
      (c.b : ℝ) / scale < 1 := by
  refine ⟨(div_le_iff₀ scale_pos).2 (by nlinarith [hc.lower]),
    (le_div_iff₀ scale_pos).2 (by nlinarith [hc.upper]), ?_⟩
  apply (div_lt_one scale_pos).2
  exact_mod_cast hc.strict

/-- Transport ONLY the existing PUBLIC sharp remainder at y=(1+z)/(1-z).
The endpoint z=1/3 is deliberately absent: it would give y=2. -/
private theorem public_remainder {z : ℝ} (hz0 : 0 ≤ z) (hz3 : z < 1 / 3) (k : ℕ) :
    0 ≤ Real.log ((1 + z) / (1 - z)) - atanhPartial z k ∧
    Real.log ((1 + z) / (1 - z)) - atanhPartial z k ≤
      2 * z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) * (1 - z ^ 2)) := by
  have hz1 : 0 < 1 - z := by linarith
  have hy1 : 1 ≤ (1 + z) / (1 - z) := (le_div_iff₀ hz1).2 (by linarith)
  have hy2 : (1 + z) / (1 - z) < 2 := (div_lt_iff₀ hz1).2 (by linarith)
  have hid : atanhParameter ((1 + z) / (1 - z)) = z := by
    unfold atanhParameter
    field_simp [hz1.ne']
    ring
  have h := log_expansion_remainder_bound hy1 hy2 k
  simpa only [logRemainder, hid, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one] using h

private theorem state_enclosure {c : Coefficients} {z : ℝ} {s : State}
    (hz0 : 0 ≤ z) (hz3 : z < 1 / 3) (hc : CoefficientInvariant c z)
    (hs : Invariant z s) :
    Encloses (s.lo, s.hi + tail c s) (Real.log ((1 + z) / (1 - z))) := by
  have hS : (0 : ℝ) < scale := scale_pos
  have hbR : (c.b : ℝ) < scale := by exact_mod_cast hc.strict
  have hdiff : (0 : ℝ) < (scale : ℝ) - c.b := sub_pos.mpr hbR
  have hodN : 0 < 2 * s.k + 1 := by omega
  have hod : (0 : ℝ) < (2 * s.k + 1 : ℕ) := by exact_mod_cast hodN
  have hdenN : 0 < (2 * s.k + 1) * (scale - c.b) :=
    Nat.mul_pos hodN (Nat.sub_pos_of_lt hc.strict)
  have hcoeff := coefficient_ratios hc
  have hsmall : ((scale : ℝ) - c.b) / scale ≤ 1 - z ^ 2 := by
    apply (div_le_iff₀ hS).2
    nlinarith only [(le_div_iff₀ hS).1 hcoeff.2.1]
  have hsmall0 : 0 < ((scale : ℝ) - c.b) / scale := div_pos hdiff hS
  have hzsq : 0 < 1 - z ^ 2 := hsmall0.trans_le hsmall
  have hrat := power_ratios hs
  have hn : 0 ≤ 2 * ((s.ph : ℝ) / scale) := by positivity
  have hrem : 2 * z ^ (2 * s.k + 1) /
        ((2 * s.k + 1 : ℕ) * (1 - z ^ 2)) ≤
      (2 * ((s.ph : ℝ) / scale)) /
        ((2 * s.k + 1 : ℕ) * (((scale : ℝ) - c.b) / scale)) := by
    calc
      _ ≤ (2 * ((s.ph : ℝ) / scale)) /
          ((2 * s.k + 1 : ℕ) * (1 - z ^ 2)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrat.2 (by norm_num))
          (mul_pos hod hzsq).le
      _ ≤ _ := div_le_div_of_nonneg_left hn (mul_pos hod hsmall0)
        (mul_le_mul_of_nonneg_left hsmall hod.le)
  have hceil := (ceil_real_bounds (2 * s.ph * scale)
    ((2 * s.k + 1) * (scale - c.b)) hdenN).1
  simp only [Nat.cast_mul, Nat.cast_sub hc.strict.le, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one] at hceil
  have htail : (scale : ℝ) *
      (2 * z ^ (2 * s.k + 1) / ((2 * s.k + 1 : ℕ) * (1 - z ^ 2))) ≤ tail c s := by
    apply (mul_le_mul_of_nonneg_left hrem hS.le).trans
    convert hceil using 1 <;> simp only [tail] <;>
      field_simp [hS.ne', hdiff.ne', (show (2 : ℝ) * s.k + 1 ≠ 0 by positivity)] <;> ring
  have hlog := public_remainder hz0 hz3 s.k
  have hl := mul_le_mul_of_nonneg_left hlog.1 hS.le
  have hh := mul_le_mul_of_nonneg_left hlog.2 hS.le
  unfold Encloses
  simp only [Prod.fst, Prod.snd, Nat.cast_add]
  constructor <;> nlinarith only [hs.sumLo, hs.sumHi, hl, hh, htail]

private theorem loop_sound {c : Coefficients} {z : ℝ}
    (hz0 : 0 ≤ z) (hz3 : z < 1 / 3) (hc : CoefficientInvariant c z)
    (fuel : ℕ) (s : State) (hs : Invariant z s) (p : ℕ × ℕ)
    (hrun : loop c fuel s = some p) :
    Encloses p (Real.log ((1 + z) / (1 - z))) := by
  induction fuel generalizing s with
  | zero => simp only [loop, reduceCtorEq] at hrun
  | succ fuel ih =>
    let t := step c s
    have ht : Invariant z t := step_invariant hz0 hc hs
    change (if tail c t ≤ 1 then some (t.lo, t.hi + tail c t)
      else loop c fuel t) = some p at hrun
    split_ifs at hrun with hstop
    · have heq := Option.some.inj hrun
      subst p
      exact state_enclosure hz0 hz3 hc ht
    · exact ih t ht hrun

/-- Literal soundness domain: natural zn,zd,fuel; 0<zd and 3*zn<zd.
The zero branch works even at fuel=0. No bound follows from `none`. -/
theorem bounds_sound (zn zd fuel : ℕ) (hd : 0 < zd) (hz : 3 * zn < zd)
    (p : ℕ × ℕ) (hrun : bounds zn zd fuel = some p) :
    Encloses p (Real.log ((1 + (zn : ℝ) / zd) / (1 - (zn : ℝ) / zd))) := by
  by_cases hn : zn = 0
  · subst zn
    have heq : (0, 0) = p := by simpa [bounds] using hrun
    subst p
    norm_num [Encloses]
  · have hz0 : (0 : ℝ) ≤ (zn : ℝ) / zd := by positivity
    have hz3 : (zn : ℝ) / zd < (1 / 3 : ℝ) := by
      apply (div_lt_iff₀ (show (0 : ℝ) < zd by exact_mod_cast hd)).2
      have h : (3 : ℝ) * zn < zd := by exact_mod_cast hz
      linarith
    exact loop_sound hz0 hz3 (initial_coefficient_invariant hd hz) fuel
      (initial zn zd) (initial_invariant hd) p (by simpa [bounds, hn] using hrun)

/-- Total algorithm correctness for EVERY fuel >=33 in the strict analytic
domain; the witness is an output of bounds itself, with its exact early exit. -/
theorem bounds_total_correct (zn zd fuel : ℕ) (hd : 0 < zd)
    (hz : 3 * zn < zd) (hf : 33 ≤ fuel) :
    ∃ p, bounds zn zd fuel = some p ∧
      Encloses p (Real.log ((1 + (zn : ℝ) / zd) / (1 - (zn : ℝ) / zd))) := by
  obtain ⟨p, hrun⟩ := bounds_success zn zd fuel hd hz.le hf
  exact ⟨p, hrun, bounds_sound zn zd fuel hd hz p hrun⟩

theorem totalBounds_correct (zn zd : ℕ) (hd : 0 < zd) (hz : 3 * zn < zd) :
    bounds zn zd 100 = some (totalBounds zn zd) ∧
      Encloses (totalBounds zn zd)
        (Real.log ((1 + (zn : ℝ) / zd) / (1 - (zn : ℝ) / zd))) := by
  obtain ⟨p, hp, he⟩ := bounds_total_correct zn zd 100 hd hz (by omega)
  have hrun : bounds zn zd 100 = some (totalBounds zn zd) := getD_run _ ⟨p, hp⟩
  have heq : p = totalBounds zn zd := Option.some.inj (hp.symm.trans hrun)
  exact ⟨hrun, heq ▸ he⟩

/-- No decimal approximation to log 2 occurs anywhere in this computation. -/
def logTwo (fuel : ℕ) : Option (ℕ × ℕ) :=
  match bounds 1 7 fuel, bounds 1 5 fuel with
  | some a, some b => some (a.1 + b.1, a.2 + b.2)
  | _, _ => none

private theorem logTwo_sound (fuel : ℕ) (p : ℕ × ℕ)
    (hrun : logTwo fuel = some p) : Encloses p (Real.log 2) := by
  cases ha : bounds 1 7 fuel with
  | none => simp [logTwo, ha] at hrun
  | some a =>
    cases hb : bounds 1 5 fuel with
    | none => simp [logTwo, ha, hb] at hrun
    | some b =>
      have heq : (a.1 + b.1, a.2 + b.2) = p := by
        simpa [logTwo, ha, hb] using hrun
      subst p
      have h1 := bounds_sound 1 7 fuel (by norm_num) (by norm_num) a ha
      have h2 := bounds_sound 1 5 fuel (by norm_num) (by norm_num) b hb
      have hid : Real.log 2 =
          Real.log ((1 + (1 : ℝ) / 7) / (1 - (1 : ℝ) / 7)) +
          Real.log ((1 + (1 : ℝ) / 5) / (1 - (1 : ℝ) / 5)) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        congr 1
        norm_num
      unfold Encloses at h1 h2 ⊢
      rw [hid]
      push_cast
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

def totalLogTwo : ℕ × ℕ := (logTwo 100).getD (0, 0)

theorem totalLogTwo_correct :
    logTwo 100 = some totalLogTwo ∧ Encloses totalLogTwo (Real.log 2) := by
  have ha := (totalBounds_correct 1 7 (by omega) (by omega)).1
  have hb := (totalBounds_correct 1 5 (by omega) (by omega)).1
  have hpair : logTwo 100 = some
      ((totalBounds 1 7).1 + (totalBounds 1 5).1,
        (totalBounds 1 7).2 + (totalBounds 1 5).2) := by
    simp only [logTwo, ha, hb]
  have hrun : logTwo 100 = some totalLogTwo := getD_run _ ⟨_, hpair⟩
  exact ⟨hrun, logTwo_sound 100 _ hrun⟩

/-- The bit_length choice is replaced by an explicit integer witness k.
The theorem below requires d*2^k<=n<d*2^(k+1), including k=0. -/
def logBounds (n d k fuel : ℕ) : Option (ℕ × ℕ) :=
  match logTwo fuel, bounds (n - d * 2 ^ k) (n + d * 2 ^ k) fuel with
  | some a, some b => some (k * a.1 + b.1, k * a.2 + b.2)
  | _, _ => none

private theorem reduction_domain (n d k : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1)) :
    0 < n + d * 2 ^ k ∧ 3 * (n - d * 2 ^ k) < n + d * 2 ^ k := by
  have hm : 0 < d * 2 ^ k := Nat.mul_pos hd (by positivity)
  have hn : n < 2 * (d * 2 ^ k) := by
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hrange.2
  omega

private theorem reduction_log (n d k : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1)) :
    Real.log ((n : ℝ) / d) = (k : ℝ) * Real.log 2 +
      Real.log ((1 + ((n - d * 2 ^ k : ℕ) : ℝ) / (n + d * 2 ^ k : ℕ)) /
        (1 - ((n - d * 2 ^ k : ℕ) : ℝ) / (n + d * 2 ^ k : ℕ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < d * (2 : ℝ) ^ k := by positivity
  have hsumR : (0 : ℝ) < (n : ℝ) + d * (2 : ℝ) ^ k := by positivity
  have hid :
      (1 + ((n - d * 2 ^ k : ℕ) : ℝ) / (n + d * 2 ^ k : ℕ)) /
        (1 - ((n - d * 2 ^ k : ℕ) : ℝ) / (n + d * 2 ^ k : ℕ)) =
      (n : ℝ) / ((d : ℝ) * (2 : ℝ) ^ k) := by
    rw [Nat.cast_sub hrange.1]
    push_cast
    field_simp [hdR.ne', hsumR.ne', (show (2 : ℝ) ^ k ≠ 0 by positivity)]
    ring
  rw [hid]
  have hnR : (0 : ℝ) < n := by
    have hm : 0 < d * 2 ^ k := Nat.mul_pos hd (by positivity)
    exact_mod_cast hm.trans_le hrange.1
  rw [Real.log_div hnR.ne' hdR.ne', Real.log_div hnR.ne' hmR.ne',
    Real.log_mul hdR.ne' (by positivity), Real.log_pow]
  ring

theorem log_bounds_sound (n d k fuel : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1))
    (p : ℕ × ℕ) (hrun : logBounds n d k fuel = some p) :
    Encloses p (Real.log ((n : ℝ) / d)) := by
  cases ha : logTwo fuel with
  | none => simp [logBounds, ha] at hrun
  | some a =>
    cases hb : bounds (n - d * 2 ^ k) (n + d * 2 ^ k) fuel with
    | none => simp [logBounds, ha, hb] at hrun
    | some b =>
      have heq : (k * a.1 + b.1, k * a.2 + b.2) = p := by
        simpa [logBounds, ha, hb] using hrun
      subst p
      have h1 := logTwo_sound fuel a ha
      have hdZ := reduction_domain n d k hd hrange
      have h2 := bounds_sound _ _ fuel hdZ.1 hdZ.2 b hb
      have hid := reduction_log n d k hd hrange
      unfold Encloses at h1 h2 ⊢
      rw [hid]
      push_cast at h2 ⊢
      have hl := mul_le_mul_of_nonneg_left h1.1 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have hh := mul_le_mul_of_nonneg_left h1.2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      constructor <;> nlinarith only [hl, hh, h2.1, h2.2]

/-- Natural rational-input logarithm, including k=0 and n=d*2^k. -/
def totalLogBounds (n d k : ℕ) : ℕ × ℕ := (logBounds n d k 100).getD (0, 0)

theorem totalLogBounds_correct (n d k : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1)) :
    logBounds n d k 100 = some (totalLogBounds n d k) ∧
      Encloses (totalLogBounds n d k) (Real.log ((n : ℝ) / d)) := by
  have hz := reduction_domain n d k hd hrange
  have ha := totalLogTwo_correct.1
  have hb := (totalBounds_correct (n - d * 2 ^ k) (n + d * 2 ^ k) hz.1 hz.2).1
  have hpair : logBounds n d k 100 = some
      (k * totalLogTwo.1 + (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).1,
        k * totalLogTwo.2 + (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).2) := by
    simp only [logBounds, ha, hb]
  have hrun : logBounds n d k 100 = some (totalLogBounds n d k) :=
    getD_run _ ⟨_, hpair⟩
  exact ⟨hrun, log_bounds_sound n d k 100 hd hrange _ hrun⟩

def layerBounds (B fuel : ℕ) : Option (ℕ × ℕ) := bounds 1 (2 * B + 1) fuel

theorem layer_bounds_sound (B fuel : ℕ) (hB : 2 ≤ B) (p : ℕ × ℕ)
    (hrun : layerBounds B fuel = some p) :
    Encloses p (Real.log (1 + 1 / (B : ℝ))) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have h := bounds_sound 1 (2 * B + 1) fuel (by omega) (by omega) p hrun
  have hid : (1 + (1 : ℝ) / (2 * B + 1 : ℕ)) /
      (1 - (1 : ℝ) / (2 * B + 1 : ℕ)) = 1 + 1 / (B : ℝ) := by
    push_cast
    field_simp [hBR.ne', (show (2 : ℝ) * B + 1 ≠ 0 by positivity)]
    ring
  simpa only [Nat.cast_one, hid] using h

def totalLayerBounds (B : ℕ) : ℕ × ℕ := (layerBounds B 100).getD (0, 0)

theorem totalLayerBounds_correct (B : ℕ) (hB : 2 ≤ B) :
    layerBounds B 100 = some (totalLayerBounds B) ∧
      Encloses (totalLayerBounds B) (Real.log (1 + 1 / (B : ℝ))) := by
  have hrun : layerBounds B 100 = some (totalLayerBounds B) :=
    getD_run _ ⟨totalBounds 1 (2 * B + 1),
      (totalBounds_correct 1 (2 * B + 1) (by omega) (by omega)).1⟩
  exact ⟨hrun, layer_bounds_sound B 100 hB _ hrun⟩

private theorem totalLogTwo_pair : totalLogTwo =
    ((totalBounds 1 7).1 + (totalBounds 1 5).1,
      (totalBounds 1 7).2 + (totalBounds 1 5).2) := by
  have ha := (totalBounds_correct 1 7 (by omega) (by omega)).1
  have hb := (totalBounds_correct 1 5 (by omega) (by omega)).1
  have hp : logTwo 100 = some
      ((totalBounds 1 7).1 + (totalBounds 1 5).1,
        (totalBounds 1 7).2 + (totalBounds 1 5).2) := by
    simp only [logTwo, ha, hb]
  unfold totalLogTwo
  rw [hp]
  rfl

theorem totalLogTwo_width : totalLogTwo.1 ≤ totalLogTwo.2 ∧
    totalLogTwo.2 - totalLogTwo.1 ≤ 200 := by
  have ha := totalBounds_width 1 7 (by omega) (by omega)
  have hb := totalBounds_width 1 5 (by omega) (by omega)
  rw [totalLogTwo_pair]
  simp only [Prod.fst, Prod.snd]
  omega

private theorem totalLogBounds_pair (n d k : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1)) :
    totalLogBounds n d k =
      (k * totalLogTwo.1 + (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).1,
        k * totalLogTwo.2 + (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).2) := by
  have hz := reduction_domain n d k hd hrange
  have ha := totalLogTwo_correct.1
  have hb := (totalBounds_correct (n - d * 2 ^ k) (n + d * 2 ^ k) hz.1 hz.2).1
  have hp : logBounds n d k 100 = some
      (k * totalLogTwo.1 + (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).1,
        k * totalLogTwo.2 + (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).2) := by
    simp only [logBounds, ha, hb]
  unfold totalLogBounds
  rw [hp]
  rfl

theorem totalLogBounds_width (n d k : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1)) :
    (totalLogBounds n d k).1 ≤ (totalLogBounds n d k).2 ∧
      (totalLogBounds n d k).2 - (totalLogBounds n d k).1 ≤ 200 * k + 100 := by
  have hz := reduction_domain n d k hd hrange
  have ha := totalLogTwo_width
  have hb := totalBounds_width (n - d * 2 ^ k) (n + d * 2 ^ k) hz.1 hz.2.le
  have ha' : totalLogTwo.2 ≤ totalLogTwo.1 + 200 := by omega
  have hb' : (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).2 ≤
      (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).1 + 100 := by omega
  have hm := Nat.mul_le_mul_left k ha'
  have hmo := Nat.mul_le_mul_left k ha.1
  rw [totalLogBounds_pair n d k hd hrange]
  simp only [Prod.fst, Prod.snd]
  constructor
  · omega
  · have hsum : k * totalLogTwo.2 +
        (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).2 ≤
        k * totalLogTwo.1 +
          (totalBounds (n - d * 2 ^ k) (n + d * 2 ^ k)).1 + 200 * k + 100 := by
      nlinarith only [hm, hb']
    omega

/-- The literal finite-range budget, with the exponent witness explicit.
The input-range-to-k<=23 step is separately proved below. -/
private theorem totalLogBounds_width_of_exponent (n d k : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1)) (hk : k ≤ 23) :
    (totalLogBounds n d k).2 - (totalLogBounds n d k).1 ≤ 4700 := by
  have h := (totalLogBounds_width n d k hd hrange).2
  omega

private theorem reduction_exponent_le_23 (n d k : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1))
    (hcap : n ≤ 10000000 * d) : k ≤ 23 := by
  by_contra hn
  have hk : 24 ≤ k := by omega
  have hpow : (2 : ℕ) ^ 24 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have hm := Nat.mul_le_mul_left d hpow
  norm_num at hm
  nlinarith only [hm, hrange.1, hcap, hd]

theorem totalLogBounds_width_finite (n d k : ℕ) (hd : 0 < d)
    (hrange : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1))
    (hcap : n ≤ 10000000 * d) :
    (totalLogBounds n d k).2 - (totalLogBounds n d k).1 ≤ 4700 :=
  totalLogBounds_width_of_exponent n d k hd hrange
    (reduction_exponent_le_23 n d k hd hrange hcap)

theorem totalLayerBounds_width (B : ℕ) (hB : 2 ≤ B) :
    (totalLayerBounds B).1 ≤ (totalLayerBounds B).2 ∧
      (totalLayerBounds B).2 - (totalLayerBounds B).1 ≤ 100 := by
  change (totalBounds 1 (2 * B + 1)).1 ≤ (totalBounds 1 (2 * B + 1)).2 ∧
    (totalBounds 1 (2 * B + 1)).2 - (totalBounds 1 (2 * B + 1)).1 ≤ 100
  exact totalBounds_width 1 (2 * B + 1) (by omega) (by omega)

/-- Scaled error used by the finite owner. Order is supplied by the actual
integer theorem before the subtraction is cast. -/
theorem totalLayerBounds_error (B : ℕ) (hB : 2 ≤ B) :
    0 ≤ (upper (totalLayerBounds B) : ℝ) - Real.log (1 + 1 / (B : ℝ)) ∧
      (upper (totalLayerBounds B) : ℝ) - Real.log (1 + 1 / (B : ℝ)) ≤
        100 / (scale : ℝ) := by
  have he := (encloses_iff_rat _ _).1 (totalLayerBounds_correct B hB).2
  have hw := totalLayerBounds_width B hB
  have hi : (totalLayerBounds B).2 ≤ (totalLayerBounds B).1 + 100 := by omega
  have hiR : ((totalLayerBounds B).2 : ℝ) ≤ (totalLayerBounds B).1 + 100 := by
    exact_mod_cast hi
  have hspan : (upper (totalLayerBounds B) : ℝ) -
      (lower (totalLayerBounds B) : ℝ) ≤ 100 / (scale : ℝ) := by
    simp only [upper, lower, Rat.cast_div, Rat.cast_natCast]
    rw [← sub_div, div_le_div_iff_of_pos_right scale_pos]
    linarith only [hiR]
  exact ⟨sub_nonneg.mpr he.2, by linarith only [he.1, hspan]⟩

end D5.S3.Arith.GoldenResource.DirectedLogarithmBounds
