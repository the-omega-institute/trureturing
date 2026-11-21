/- GID: D5/S3/Arith/Abundancy/DefantC41Settlement
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/DefantC41Settlement
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.QuadraticAlgebra.Basic, mathlib/module/Mathlib.Algebra.BigOperators.Finprod, mathlib/module/Mathlib.Analysis.Real.Sqrt]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Abundancy/DefantC41Settlement.claim; result=D5.S3.Arith.Abundancy.DefantC41Settlement.result; claim=D5.S3.Arith.Abundancy.DefantC41Settlement.claim
   digest: The rational prime 3 refutes Defant's conjecture on powerful solitude in quadratic integer rings. -/

/- Formalization classification:
   proof_shape: result: content
   escape_witness: none
   admission_basis: open-problem-resolution (issue #32039)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Abundancy.DefantC41Settlement

/-- The radicands in Defant's introduction. -/
def K : Finset ℤ := {-163, -67, -43, -19, -11, -7, -3, -2, -1}

/-- The basis generator is (1 + √d)/2 when d ≡ 1 mod 4 and √d otherwise.
The parameters give its relation X² = a + bX. -/
abbrev R (d : ℤ) := QuadraticAlgebra ℤ (if d % 4 = 1 then (d - 1) / 4 else d)
  (if d % 4 = 1 then 1 else 0)

abbrev Nonzero (d : ℤ) := {z : R d // z ≠ 0}

noncomputable def absoluteValue {d : ℤ} (z : R d) : ℝ :=
  Real.sqrt ((QuadraticAlgebra.norm z : ℤ) : ℝ)

/-- The half-open argument sectors [0, π/2), [0, π/3), and [0, π),
expressed in the integral basis for the corresponding ring. -/
def A (d : ℤ) : Set (R d) :=
  {z | if d = -1 ∨ d = -3 then 0 < z.re ∧ 0 ≤ z.im
       else 0 < z.im ∨ (z.im = 0 ∧ 0 < z.re)}

/-- Defant, Definition 2.1. The weight is zero off the actual sector divisors. -/
noncomputable def delta {d : ℤ} (n : ℤ) (z : Nonzero d) : ℝ := by
  classical
  exact ∑ᶠ x : R d, if x ∣ z.val ∧ x ∈ A d then absoluteValue x ^ n else 0

/-- Defant, Definition 2.2. The conjecture uses positive natural exponents. -/
noncomputable def I {d : ℤ} (n : ℕ) (z : Nonzero d) : ℝ :=
  delta (n : ℤ) z / absoluteValue z.val ^ n

def PowerfullyFriendly {d : ℤ} (n : ℕ) (z w : Nonzero d) : Prop :=
  I n z = I n w ∧ absoluteValue z.val ≠ absoluteValue w.val

def primePower (d : ℤ) (p k : ℕ) (hp : p.Prime) : Nonzero d :=
  ⟨((p ^ k : ℕ) : R d), by
    intro h
    have hcoord := congrArg QuadraticAlgebra.re h
    rw [QuadraticAlgebra.re_natCast, QuadraticAlgebra.re_zero] at hcoord
    exact (pow_ne_zero k hp.ne_zero) (Int.natCast_eq_zero.mp hcoord)⟩

/-- Defant, Conjecture 4.1 (arXiv:1506.05416v1, p. 23).

“Let $d\!\in\! K$. If $p$ is an integer prime and $k$ is a positive integer,
then $p^k$ is $n$-powerfully solitary in $\mathcal O_{\mathbb{Q}(\sqrt{d})}$
for all positive integers $n$.”
-/
def claim : Prop :=
  ∀ (d : ℤ), d ∈ K →
    ∀ (p : ℕ) (hp : p.Prime) (k : ℕ), 0 < k →
      ∀ (n : ℕ), 0 < n →
        ∀ (z : Nonzero d), ¬ PowerfullyFriendly n (primePower d p k hp) z

open QuadraticAlgebra

private theorem norm_lower_bound {d : ℤ} (hd : d ∈ K) (z : R d) :
    z.re ^ 2 + z.im ^ 2 ≤ 2 * z.norm := by
  rw [norm_def]
  simp only [K, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num <;> nlinarith [sq_nonneg (z.re + z.im), sq_nonneg z.re, sq_nonneg z.im]

private theorem norm_pos {d : ℤ} (hd : d ∈ K) {z : R d} (hz : z ≠ 0) :
    0 < z.norm := by
  have h := norm_lower_bound hd z
  by_cases hx : z.re = 0
  · have hy : z.im ≠ 0 := fun hy => hz (QuadraticAlgebra.ext hx hy)
    nlinarith [sq_nonneg z.re, sq_pos_of_ne_zero hy]
  · nlinarith [sq_nonneg z.im, sq_pos_of_ne_zero hx]

private theorem norm_le_of_dvd {d : ℤ} (hd : d ∈ K) {u z : R d}
    (hz : z ≠ 0) (h : u ∣ z) : u.norm ≤ z.norm := by
  obtain ⟨q, rfl⟩ := h
  exact Int.le_of_dvd (norm_pos hd hz) ⟨q.norm, map_mul norm u q⟩

private theorem coordinate_bounds {x bound : ℤ} (h : x ^ 2 ≤ bound) :
    -bound ≤ x ∧ x ≤ bound := by
  have hb : 0 ≤ bound := (sq_nonneg x).trans h
  constructor
  · by_contra! hl
    have : x ≤ -bound - 1 := by omega
    nlinarith [sq_nonneg (x + 1)]
  · by_contra! hu
    have : bound + 1 ≤ x := by omega
    nlinarith [sq_nonneg (x - 1)]

/-- Multiplying by the conjugate converts divisibility into an integral
quotient test in both coordinates of the same ring. -/
private theorem dvd_iff_coordinates {d : ℤ} {u z : R d} (hu : u.norm ≠ 0) :
    u ∣ z ↔ u.norm ∣ (z * star u).re ∧ u.norm ∣ (z * star u).im := by
  let s : R d := algebraMap ℤ (R d) u.norm
  have hs : s = u * star u := algebraMap_norm_eq_mul_star u
  constructor
  · rintro ⟨q, rfl⟩
    have hmul : (u * q) * star u = s * q := by rw [hs]; ac_rfl
    rw [hmul]
    exact ⟨⟨q.re, by simp [s]⟩, ⟨q.im, by simp [s]⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let q : R d := ⟨x, y⟩
    have hmul : z * star u = s * q := by
      apply QuadraticAlgebra.ext
      · simpa [s, q] using hx
      · simpa [s, q] using hy
    have hcancel : s * z = s * (u * q) := calc
      s * z = u * (z * star u) := by rw [hs]; ac_rfl
      _ = u * (s * q) := by rw [hmul]
      _ = s * (u * q) := by ac_rfl
    refine ⟨q, QuadraticAlgebra.ext ?_ ?_⟩
    · apply mul_left_cancel₀ hu
      simpa [s] using congrArg QuadraticAlgebra.re hcancel
    · apply mul_left_cancel₀ hu
      simpa [s] using congrArg QuadraticAlgebra.im hcancel

private abbrev R11 := R (-11)

private theorem d11_mem : (-11 : ℤ) ∈ K := by decide

private def pi11 : R11 := ⟨0, 1⟩

private def three : Nonzero (-11) :=
  ⟨⟨3, 0⟩, by decide⟩

private def w : Nonzero (-11) :=
  ⟨7 * pi11 - 3, by decide⟩

private theorem norm_three : three.val.norm = 9 := by decide

private theorem norm_w : w.val.norm = 135 := by decide

private theorem norm_identity (u : R11) :
    4 * u.norm = (2 * u.re + u.im) ^ 2 + 11 * u.im ^ 2 := by
  rw [norm_def]
  change 4 * (u.re * u.re + 1 * u.re * u.im - (-3) * u.im * u.im) = _
  ring

private theorem mem_A11 (u : R11) :
    u ∈ A (-11) ↔ 0 < u.im ∨ (u.im = 0 ∧ 0 < u.re) := by
  simp [A]

private theorem sector_bounds {u : R11} (ha : u ∈ A (-11)) (hn : u.norm ≤ 135) :
    -15 ≤ u.re ∧ u.re ≤ 11 ∧ 0 ≤ u.im ∧ u.im ≤ 7 := by
  have hy : 0 ≤ u.im := by rcases (mem_A11 u).mp ha with h | ⟨h, _⟩ <;> omega
  have h := norm_identity u
  have hy' : u.im ≤ 7 := by
    by_contra! hlarge
    have : 8 ≤ u.im := by omega
    nlinarith [sq_nonneg (u.im - 8), sq_nonneg (2 * u.re + u.im)]
  have hlo : -23 ≤ 2 * u.re + u.im := by
    by_contra! hsmall
    have : 2 * u.re + u.im ≤ -24 := by omega
    nlinarith [sq_nonneg (2 * u.re + u.im + 24), sq_nonneg u.im]
  have hhi : 2 * u.re + u.im ≤ 23 := by
    by_contra! hlarge
    have : 24 ≤ 2 * u.re + u.im := by omega
    nlinarith [sq_nonneg (2 * u.re + u.im - 24), sq_nonneg u.im]
  omega

private def threeDivisors : Finset R11 :=
  {⟨1, 0⟩, ⟨3, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩}

private def wDivisors : Finset R11 :=
  {⟨1, 0⟩, ⟨-3, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨6, 1⟩, ⟨-3, 2⟩, ⟨3, 2⟩, ⟨-3, 7⟩}

private def boxElem (i : Fin 27) (j : Fin 8) : R11 :=
  ⟨(i.val : ℤ) - 15, j.val⟩

/-- The decidable predicate used for the bounded search. -/
private def divisorTest (u z : R11) : Prop :=
  (0 < u.im ∨ (u.im = 0 ∧ 0 < u.re)) ∧
    (u.norm ∣ (z * star u).re) ∧ (u.norm ∣ (z * star u).im)

private instance (u z : R11) : Decidable (divisorTest u z) := by
  unfold divisorTest
  infer_instance

private theorem divisorTest_iff (u z : R11) :
    divisorTest u z ↔ u ∣ z ∧ u ∈ A (-11) := by
  constructor
  · rintro ⟨ha, htest⟩
    have ha' := (mem_A11 u).mpr ha
    have hu : u ≠ 0 := by rintro rfl; simp [A] at ha'
    exact ⟨(dvd_iff_coordinates (norm_pos d11_mem hu).ne').mpr htest, ha'⟩
  · rintro ⟨hdvd, ha⟩
    have hu : u ≠ 0 := by rintro rfl; simp [A] at ha
    exact ⟨(mem_A11 u).mp ha, (dvd_iff_coordinates (norm_pos d11_mem hu).ne').mp hdvd⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
private theorem box_certificate :
    (∀ i j, boxElem i j ∈ threeDivisors ↔ divisorTest (boxElem i j) three.val) ∧
    (∀ i j, boxElem i j ∈ wDivisors ↔ divisorTest (boxElem i j) w.val) := by
  decide

set_option maxRecDepth 4096 in
private theorem listed_bounds :
    (∀ u ∈ threeDivisors, -15 ≤ u.re ∧ u.re ≤ 11 ∧ 0 ≤ u.im ∧ u.im ≤ 7) ∧
    (∀ u ∈ wDivisors, -15 ≤ u.re ∧ u.re ≤ 11 ∧ 0 ≤ u.im ∧ u.im ≤ 7) := by
  decide

private theorem divisors_complete (z : Nonzero (-11)) (s : Finset R11)
    (hn : z.val.norm ≤ 135)
    (hcert : ∀ i j, boxElem i j ∈ s ↔ divisorTest (boxElem i j) z.val)
    (hlisted : ∀ u ∈ s, -15 ≤ u.re ∧ u.re ≤ 11 ∧ 0 ≤ u.im ∧ u.im ≤ 7)
    (u : R11) : u ∈ s ↔ u ∣ z.val ∧ u ∈ A (-11) := by
  have h : u ∈ s ∨ (u ∣ z.val ∧ u ∈ A (-11)) →
      ∃ i j, boxElem i j = u := by
    intro hu
    obtain ⟨hxl, hxu, hyl, hyu⟩ := hu.elim (hlisted u) fun h =>
      sector_bounds h.2 ((norm_le_of_dvd d11_mem z.property h.1).trans hn)
    refine ⟨⟨(u.re + 15).toNat, by omega⟩, ⟨u.im.toNat, by omega⟩, ?_⟩
    apply QuadraticAlgebra.ext <;> simp only [boxElem] <;> omega
  constructor
  · intro hu
    obtain ⟨i, j, rfl⟩ := h (Or.inl hu)
    exact (divisorTest_iff _ _).mp ((hcert i j).mp hu)
  · intro hu
    obtain ⟨i, j, rfl⟩ := h (Or.inr hu)
    exact (hcert i j).mpr ((divisorTest_iff _ _).mpr hu)

private theorem absoluteValue_sq {d : ℤ} (hd : d ∈ K) {z : R d} (hz : z ≠ 0) :
    absoluteValue z ^ 2 = (z.norm : ℝ) := by
  exact Real.sq_sqrt (by exact_mod_cast (norm_pos hd hz).le)

private theorem delta_two_eq_sum (z : Nonzero (-11)) (s : Finset R11)
    (hs : ∀ u, u ∈ s ↔ u ∣ z.val ∧ u ∈ A (-11)) :
    delta 2 z = ((∑ u ∈ s, u.norm : ℤ) : ℝ) := by
  classical
  unfold delta
  rw [finsum_eq_sum_of_support_subset (s := s)]
  · push_cast
    apply Finset.sum_congr rfl
    intro u hu
    have h := (hs u).mp hu
    have hne : u ≠ 0 := by rintro rfl; simp [A] at h
    rw [ite_eq_left h, zpow_ofNat, absoluteValue_sq d11_mem hne]
  · intro u hu
    apply (hs u).mpr
    by_contra hn
    exact hu (ite_eq_right hn)

private theorem sum_three : (∑ u ∈ threeDivisors, u.norm : ℤ) = 16 := by decide

private theorem sum_w : (∑ u ∈ wDivisors, u.norm : ℤ) = 240 := by decide

private theorem delta_three : delta 2 three = 16 := by
  rw [delta_two_eq_sum three threeDivisors
    (divisors_complete three threeDivisors (by rw [norm_three]; decide)
      box_certificate.1 listed_bounds.1), sum_three]
  norm_num

private theorem delta_w : delta 2 w = 240 := by
  rw [delta_two_eq_sum w wDivisors
    (divisors_complete w wDivisors (by rw [norm_w])
      box_certificate.2 listed_bounds.2), sum_w]
  norm_num

private theorem equal_index : I 2 three = I 2 w := by
  change delta 2 three / absoluteValue three.val ^ 2 =
    delta 2 w / absoluteValue w.val ^ 2
  rw [delta_three, delta_w, absoluteValue_sq d11_mem three.property,
    absoluteValue_sq d11_mem w.property, norm_three, norm_w]
  norm_num

private theorem unequal_absoluteValue : absoluteValue three.val ≠ absoluteValue w.val := by
  intro h
  have hsq := congrArg (fun x : ℝ => x ^ 2) h
  rw [absoluteValue_sq d11_mem three.property, absoluteValue_sq d11_mem w.property,
    norm_three, norm_w] at hsq
  norm_num at hsq

/-- The rational prime 3 and the challenger 7π − 3 are 2-powerfully friendly
in the source ring of radicand −11. -/
theorem result : ¬ claim := by
  intro h
  have hprime : primePower (-11) 3 1 Nat.prime_three = three := by
    apply Subtype.ext
    rfl
  exact h (-11) d11_mem 3 Nat.prime_three 1 (by decide) 2 (by decide) w
    (hprime ▸ (show PowerfullyFriendly 2 three w from ⟨equal_index, unequal_absoluteValue⟩))

end D5.S3.Arith.Abundancy.DefantC41Settlement
